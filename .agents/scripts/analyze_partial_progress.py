#!/usr/bin/env python3
"""
analyze_partial_progress.py — Read a temp file with partial proof progress.

Extracts:
  - Completed lemmas (no sorry, no errors) 
  - Lemma stubs (with sorry or errors)
  - The main theorem block and its current state
  - Remaining errors (from LSP diagnostics)

Output: structured JSON describing what was accomplished and what remains.

Usage:
  python3 analyze_partial_progress.py <temp-file.lean>
  python3 analyze_partial_progress.py <temp-file.lean> --with-errors
"""

import sys
import json
import re
import subprocess
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent


def find_blocks(lines: list[str]) -> list[dict]:
    """Find lemma/theorem/example blocks in the file.
    Returns list of {name, start_line, end_line, type, has_sorry, body}.
    """
    blocks = []
    i = 0
    while i < len(lines):
        line = lines[i]
        m = re.match(r'^\s*(lemma|theorem|example)\s+(\w+)?', line)
        if m:
            kw = m.group(1)
            name = m.group(2) or "(anonymous)"
            start = i
            # Scan for the end: next top-level declaration or EOF
            j = i + 1
            depth = 0
            while j < len(lines):
                next_line = lines[j]
                if next_line.strip() == "" and depth == 0:
                    pass  # blank lines within a block are OK
                elif re.match(r'^\s*(lemma|theorem|example)\s', next_line):
                    # This is a new declaration at same level
                    # But only if it's not indented more
                    if not next_line.startswith(" ") or depth == 0:
                        break
                # Track brace depth for nested blocks
                depth += next_line.count(":=") * 5  # rough heuristic
                depth = max(0, depth - next_line.count("  "))
                j += 1
            end = j - 1
            body = "\n".join(lines[start:end+1])
            has_sorry = "sorry" in body
            blocks.append({
                "name": name,
                "type": kw,
                "start_line": start + 1,  # 1-indexed
                "end_line": end + 1,
                "has_sorry": has_sorry,
                "body": body,
                "line_count": end - start + 1,
            })
            i = end + 1
        else:
            i += 1
    return blocks


def get_lsp_errors(filepath: str) -> list[dict]:
    """Run lean_diagnostic_messages via the LSP tool."""
    cmd = ["lean-lsp_lean_diagnostic_messages", filepath]
    # This would require the MCP tool — for now return empty.
    # In practice, the main thread provides this.
    return []


def classify_blocks(blocks: list[dict]) -> dict:
    """Classify blocks into completed, stub, or in-progress."""
    completed = []
    stubs = []
    for b in blocks:
        if b["has_sorry"]:
            stubs.append(b)
        else:
            completed.append(b)
    return {"completed": completed, "stubs": stubs}


def find_main_target(blocks: list[dict]) -> dict | None:
    """Find the main theorem/example block (usually the last one, or one named 'theorem')."""
    # Find the example block (if any)
    for b in blocks:
        if b["type"] == "example":
            return b
    # Find the last non-lemma block
    for b in reversed(blocks):
        if b["type"] in ("theorem", "example"):
            return b
    return blocks[-1] if blocks else None


def find_project_pitfalls(blocks: list[dict]) -> list[dict]:
    """Check blocks for known project-specific pitfalls."""
    pitfalls_path = SCRIPT_DIR.parent / "experience" / "project_pitfalls.json"
    found = []
    if not pitfalls_path.exists():
        return found
    try:
        data = json.loads(pitfalls_path.read_text())
        for pitfall in data.get("pitfalls", []):
            expected = pitfall.get("expected", "")
            for b in blocks:
                if expected in b["body"]:
                    found.append({
                        "block": b["name"],
                        "pitfall": expected,
                        "solution": pitfall.get("solution", ""),
                    })
        return found
    except Exception:
        return found


def generate_continuation_plan(blocks: list[dict], filepath: str) -> dict:
    """Generate a plan for how to continue the proof."""
    classified = classify_blocks(blocks)
    main = find_main_target(blocks)
    pitfalls = find_project_pitfalls(blocks)
    stubs = classified["stubs"]

    # For each stub lemma, recommend creating a separate subgoal
    subgoals = []
    for s in stubs:
        subgoals.append({
            "lemma_name": s["name"],
            "lines": s["line_count"],
            "type": s["type"],
            "body_preview": s["body"][:200],
            "recommendation": "dispatch sub-subagent" if s["line_count"] > 5 else "solve inline",
        })

    plan = {
        "total_blocks": len(blocks),
        "completed_lemmas": len(classified["completed"]),
        "lemma_stubs": len(stubs),
        "main_theorem_block": {
            "name": main["name"] if main else "unknown",
            "has_sorry": main["has_sorry"] if main else True,
            "line_count": main["line_count"] if main else 0,
        } if main else None,
        "subgoals_to_dispatch": subgoals,
        "pitfalls_found": pitfalls,
        "recommended_next_steps": []
    }

    # Generate recommendations
    if stubs:
        plan["recommended_next_steps"].append(
            f"Dispatch {len(stubs)} sub-subagent(s) for lemma stubs before continuing main proof"
        )
        for sg in subgoals:
            plan["recommended_next_steps"].append(
                f"  - Create _temp_subgoal_{sg['lemma_name']}.lean and dispatch sub-subagent"
            )

    if pitfalls:
        for p in pitfalls:
            plan["recommended_next_steps"].append(
                f"  - Fix known pitfall in {p['block']}: {p['solution']}"
            )

    if main and main["has_sorry"]:
        plan["recommended_next_steps"].append(
            f"After lemmas are done, continue the main proof (line {main.get('start_line', '?')})"
        )

    return plan


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)

    filepath = sys.argv[1]
    p = Path(filepath)
    if not p.exists():
        print(json.dumps({"error": f"File not found: {filepath}"}))
        sys.exit(1)

    lines = p.read_text().splitlines()
    blocks = find_blocks(lines)
    plan = generate_continuation_plan(blocks, filepath)

    # If --with-errors, read errors from stdin
    if "--with-errors" in sys.argv:
        try:
            errors_input = sys.stdin.read()
            if errors_input.strip():
                plan["lsp_errors"] = json.loads(errors_input)
        except Exception:
            plan["lsp_errors"] = []

    output = json.dumps(plan, indent=2, ensure_ascii=False)
    print(output)


if __name__ == "__main__":
    main()
