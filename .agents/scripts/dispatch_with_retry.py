#!/usr/bin/env python3
"""
dispatch_with_retry.py — Retry loop + websearch escalation for proof subagents.

Generates a structured prompt for the main thread to pass to task().
Handles:
  - Retry loop metadata (attempt N of M)
  - Websearch escalation when local experience is exhausted
  - Lemma decomposition recommendations

Usage:
  # First attempt — generates prompt for main theorem
  python3 dispatch_with_retry.py <file.lean> <line> [--theorem <name>] [--tag <tag>]

  # Retry — pass previous failure info + partial progress analysis
  python3 dispatch_with_retry.py <file.lean> <line> --retry <attempt> \\
    --temp-file <temp.lean> --last-error "<error>" --theorem <name>

  # Subgoal mode — generate prompt for a helper lemma (sub-subagent)
  python3 dispatch_with_retry.py <file.lean> <line> --mode subgoal \\
    --lemma-name <name> --lemma-stmt "<statement>" --theorem <parent_name>

  # Analyze partial progress from temp file
  python3 dispatch_with_retry.py --analyze <temp.lean>

Output: JSON on stdout with fields:
  - prompt: str          # The subagent prompt to pass to task()
  - meta: dict           # Metadata for experience recording
  - subgoals: list       # Lemma stubs to dispatch (from analysis)
  - websearch_query: str # If more info needed, what to search
"""

import sys
import json
import subprocess
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
MAX_RETRIES = 4  # total attempts = MAX_RETRIES + 1


def get_project_root(filepath: str) -> str:
    """Find the Lean project root (ancestor with lean-toolchain)."""
    p = Path(filepath).resolve()
    for ancestor in [p] + list(p.parents):
        if (ancestor / "lean-toolchain").exists():
            return str(ancestor)
    return str(p.parent)  # fallback

# ── Retry strategy: escalation ladder ──────────────────────────
# Attempt 0: standard prompt
# Attempt 1: include last error context
# Attempt 2: include decomposition recommendation
# Attempt 3: include websearch results (main thread fills this in)
# Attempt 4: FAIL — return summary for human intervention


def get_last_errors_for_file(filepath: str, limit: int = 3) -> list[dict]:
    """Query the experience DB for recent errors on this file."""
    result = subprocess.run(
        ["python3", str(SCRIPT_DIR / "experience.py"), "error", "list",
         "--limit", str(limit)],
        capture_output=True, text=True
    )
    # Filter by file
    try:
        lines = result.stdout.strip().splitlines()
        errors = []
        for line in lines:
            if filepath in line or Path(filepath).name in line:
                errors.append(line)
        return errors
    except Exception:
        return []


def get_recent_tips(tags: list[str] | None = None, count: int = 5) -> str:
    """Get tips from experience DB."""
    cmd = ["python3", str(SCRIPT_DIR / "experience.py"), "tip", "list", "--limit", str(count)]
    if tags:
        for t in tags:
            cmd.extend(["--tag", t])
    result = subprocess.run(cmd, capture_output=True, text=True)
    return result.stdout.strip() if result.stdout.strip() else ""


def check_experience_for_theorem(theorem: str, filepath: str) -> list[dict]:
    """Search for past errors/successes about this theorem."""
    results = []
    # Check errors
    err_result = subprocess.run(
        ["python3", str(SCRIPT_DIR / "experience.py"), "error", "search", theorem],
        capture_output=True, text=True
    )
    if err_result.stdout.strip():
        results.append({"source": "error", "text": err_result.stdout.strip()[:500]})
    # Check successes
    suc_result = subprocess.run(
        ["python3", str(SCRIPT_DIR / "experience.py"), "success", "search", theorem],
        capture_output=True, text=True
    )
    if suc_result.stdout.strip():
        results.append({"source": "success", "text": suc_result.stdout.strip()[:500]})
    return results


def generate_lemma_hints(filepath: str, line: int) -> str:
    """Scan the target theorem and suggest lemma decomposition."""
    p = Path(filepath)
    if not p.exists():
        return ""
    lines = p.read_text().splitlines()
    # Find the theorem/example/lemma at target
    target_idx = line - 1
    # Scan forward to estimate complexity
    end_idx = min(target_idx + 200, len(lines))
    body = lines[target_idx:end_idx]
    line_count = 0
    indent_level = 0
    for l in body:
        stripped = l.strip()
        if stripped.startswith("sorry"):
            break
        if stripped == "" or stripped.startswith("--"):
            continue
        line_count += 1
    if line_count > 40:
        return (f"  ⚠️  Target theorem body ~{line_count} lines — consider breaking into lemmas.\n"
                f"  Strategy: identify distinct 'have' statements that can be independent lemmas."
                f"\n  Each lemma should be ≤30 lines. Dispatch sub-subagents for each.")
    return ""


def check_relevant_tips(filepath: str, theorem: str) -> str:
    """Get tips matching the file/theorem context."""
    tags = []
    # Extract topic from filename
    fname = Path(filepath).stem.lower()
    if "measure" in fname:
        tags.append("measure")
    if "set" in fname:
        tags.append("set")
    tags.extend(["structure", "lemma-split", "large-proof"])
    return get_recent_tips(tags, count=3)


def build_retry_context(attempt: int, last_error: str, filepath: str, theorem: str) -> str:
    """Build context section based on retry attempt number."""
    parts = []
    parts.append(f"RETRY ATTEMPT: {attempt + 1} of {MAX_RETRIES + 1}")

    if attempt >= 1 and last_error:
        parts.append(f"\nLAST ATTEMPT ERROR:\n{last_error[:1000]}")

    if attempt >= 2:
        # Add lemma decomposition hints
        hints = generate_lemma_hints(filepath, 0)  # line 0 = placeholder
        if hints:
            parts.append(f"\n{hints}")

    if attempt >= 3:
        # Check experience for similar theorems
        exp = check_experience_for_theorem(theorem, filepath)
        if exp:
            parts.append(f"\nPAST EXPERIENCE FOR SIMILAR THEOREMS:")
            for e in exp:
                parts.append(f"  [{e['source']}] {e['text'][:200]}")

    return "\n".join(parts)


def generate_subagent_prompt(filepath: str, line: int, *,
                             theorem: str = "",
                             attempt: int = 0,
                             last_error: str = "",
                             websearch_results: str = "",
                             extra_tags: list[str] | None = None) -> str:
    """Generate the full prompt to pass to task()."""
    extra_tags = extra_tags or []

    # Get the base prompt from subagent_prompt.py
    tag_args = []
    for t in extra_tags:
        tag_args.extend(["--tag", t])
    cmd = ["python3", str(SCRIPT_DIR / "subagent_prompt.py"),
           filepath, str(line)]
    if theorem:
        cmd.extend(["--theorem", theorem])
    cmd.extend(tag_args)

    result = subprocess.run(cmd, capture_output=True, text=True)
    base_prompt = result.stdout.strip()

    # Build retry context
    retry_ctx = build_retry_context(attempt, last_error, filepath, theorem)

    # Check for relevant tips
    tips = check_relevant_tips(filepath, theorem)

    # Build the final prompt
    parts = [base_prompt]

    if retry_ctx:
        parts.extend([
            "",
            "=" * 70,
            "RETRY CONTEXT",
            "=" * 70,
            retry_ctx
        ])

    if tips:
        parts.extend([
            "",
            "RELEVANT TIPS FROM EXPERIENCE DB:",
            tips
        ])

    if websearch_results:
        parts.extend([
            "",
            "=" * 70,
            "WEBSEARCH RESULTS (additional mathematical context)",
            "=" * 70,
            websearch_results[:2000]
        ])

    # Add lemma decomposition hint at the end
    parts.extend([
        "",
        "=" * 70,
        "LEMMA DECOMPOSITION",
        "=" * 70,
        "If the proof is complex (>40 lines), break it into smaller lemmas.",
        "Each lemma should solve ONE subgoal. Dispatch sub-subagents for each lemma.",
        "After all lemmas are solved, assemble the main proof.",
        "",
        "Work in the temp file. Return PROOF_BLOCK only when 0 errors."
    ])

    return "\n".join(parts)


def main():
    parser = SimpleArgParser()

    # ── Analyze mode ───────────────────────────────────────────
    analyze_file: str = parser.get("--analyze") or ""
    if analyze_file:
        ap_path = SCRIPT_DIR / "analyze_partial_progress.py"
        result = subprocess.run(
            ["python3", str(ap_path), analyze_file],
            capture_output=True, text=True
        )
        print(result.stdout.strip() or result.stderr.strip())
        return

    # ── Standard / Subgoal / Retry modes ──────────────────────
    mode: str = parser.get("--mode") or "standard"
    filepath: str = parser.get(0) or ""
    line: int = parser.get_int(1) or 0
    theorem: str = parser.get("--theorem") or ""
    attempt: int = parser.get_int("--retry") or 0
    last_error: str = parser.get("--last-error") or ""
    temp_file: str = parser.get("--temp-file") or ""

    if not filepath or line == 0:
        print(__doc__)
        sys.exit(1)

    extra_tags: list = parser.get_all("--tag")

    if mode == "subgoal":
        # Generate a prompt for a helper lemma (sub-subagent dispatch)
        lemma_name: str = parser.get("--lemma-name") or "lemma"
        lemma_stmt: str = parser.get("--lemma-stmt") or ""
        prompt = _gen_subgoal_prompt(filepath, lemma_name, lemma_stmt, theorem)
        output = {
            "mode": "subgoal",
            "agent": "lean-prover",
            "prompt": prompt,
            "meta": {
                "type": "subgoal",
                "lemma_name": lemma_name,
                "parent_theorem": theorem or "unknown",
                "file": filepath,
                "line": line,
            }
        }
        print(json.dumps(output, indent=2, ensure_ascii=False))
        return

    # ── Standard main-theorem prompt ──────────────────────────
    prompt = generate_subagent_prompt(
        filepath, line,
        theorem=theorem,
        attempt=attempt,
        last_error=last_error,
        extra_tags=extra_tags
    )

    # ── Analyze partial progress (if temp file exists) ────────
    subgoals = []
    if temp_file and Path(temp_file).exists():
        ap_path = SCRIPT_DIR / "analyze_partial_progress.py"
        result = subprocess.run(
            ["python3", str(ap_path), temp_file],
            capture_output=True, text=True
        )
        try:
            analysis = json.loads(result.stdout)
            subgoals = analysis.get("subgoals_to_dispatch", [])
        except Exception:
            pass

    meta = {
        "attempt": attempt,
        "max_retries": MAX_RETRIES,
        "file": filepath,
        "line": line,
        "theorem": theorem or "auto",
        "should_retry": attempt < MAX_RETRIES,
        "needs_websearch": attempt >= 2,
        "temp_file": temp_file,
        "subgoals_found": len(subgoals),
    }

    output = {
        "mode": "standard",
        "agent": "lean-prover",
        "prompt": prompt,
        "meta": meta,
        "subgoals": subgoals,
        "websearch_query": (
            f"Exercise 1.2.10 [0,1) not countable union disjoint closed intervals measure theory Tao"
            if attempt >= 2 else ""
        )
    }

    print(json.dumps(output, indent=2, ensure_ascii=False))


def _gen_subgoal_prompt(filepath: str, lemma_name: str, lemma_stmt: str,
                        parent_theorem: str = "") -> str:
    """Generate a compact prompt for a sub-subagent to prove a helper lemma."""
    project_root = get_project_root(filepath)
    lines = [
        "=" * 70,
        "SUB-SUBAGENT: Prove ONE helper lemma",
        "=" * 70,
        "",
        f"You are a Lean 4 sub-subagent. Prove this helper lemma for theorem {parent_theorem}.",
        "",
        "RULES:",
        f"  1. Temp file: {project_root}/_temp_subgoal_{lemma_name}.lean (MUST be in project root!)",
        "  2. Work ONLY in temp file using LSP tools (lean_goal, lean_local_search, lean_diagnostic_messages)",
        "  3. Max 30 lines of proof. If stuck after 5 attempts, return STATUS=fail.",
        "  4. NEVER edit the real file.",
        "",
        "LEMMA TO PROVE:",
        lemma_stmt,
        "",
        "TEMP FILE TEMPLATE:",
        f"  import Analysis.MeasureTheory.Section_1_2_2",
        f"  open Set",
        f"  open BoundedInterval",
        "",
        f"  {lemma_stmt}",
        "",
        "RETURN FORMAT:",
        "  STATUS: success | fail",
        "  THEOREM: <lemma_name>",
        "  PROOF_BLOCK: |",
        "    <lean proof code>",
        "  NOTES: <key insight>",
        "",
        "After success, the main thread will integrate your lemma into the main proof.",
    ]
    return "\n".join(lines)


class SimpleArgParser:
    """Minimal argument parser (no deps)."""
    def __init__(self):
        self.args = sys.argv[1:]
        self.positional = []
        self.kwargs = {}
        self._parse()

    def _parse(self):
        i = 0
        while i < len(self.args):
            if self.args[i].startswith("--"):
                key = self.args[i]
                if i + 1 < len(self.args) and not self.args[i+1].startswith("--"):
                    val = self.args[i+1]
                    i += 2
                else:
                    val = True
                    i += 1
                if key not in self.kwargs:
                    self.kwargs[key] = []
                self.kwargs[key].append(str(val) if not isinstance(val, str) else val)
            else:
                self.positional.append(self.args[i])
                i += 1

    def get(self, idx_or_key, default=None):
        if isinstance(idx_or_key, int):
            return self.positional[idx_or_key] if idx_or_key < len(self.positional) else default
        vals = self.kwargs.get(idx_or_key, [])
        return vals[0] if vals else default

    def get_int(self, idx_or_key, default=None):
        val = self.get(idx_or_key)
        if val is None:
            return default
        try:
            return int(val)
        except (ValueError, TypeError):
            return default

    def get_all(self, key):
        return self.kwargs.get(key, [])


if __name__ == "__main__":
    main()
