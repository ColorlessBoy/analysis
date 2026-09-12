#!/usr/bin/env python3
"""
lean_hook.py — Lean 4 workflow automation hooks.

Integrates lsp_guard + experience recording into the editing workflow.
Designed to be called before/after editing .lean files.

Usage:
  # Before editing — injects LSP reminder + relevant tips
  python3 lean_hook.py pre-edit <file.lean>

  # After editing — suggest recording + track divergence
  python3 lean_hook.py post-edit <file.lean> [--status success|error] [--errors N] [--msg "..."]

  # Check a conversation log for LSP violations
  python3 lean_hook.py session-check <log.json>

  # Record a proof result in experience DB
  python3 lean_hook.py record <file.lean> <line> \
      --type error|success --theorem <name> --msg "..." \
      [--tactic "..."] [--solution "..."] [--tags t1,t2]

  # Get relevant tips to inject into context
  python3 lean_hook.py tips [--tag <tag>] [--count N]

  # Run self-audit (meta-cognitive introspection)
  python3 lean_hook.py audit

  # Track error count divergence
  python3 lean_hook.py track <file.lean> <error_count> [--context "..."]

  # Check divergence on a file
  python3 lean_hook.py divergent <file.lean>
"""

import sys
import json
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent


def pre_edit(filepath: str):
    """Print LSP guard + top tips to inject into the prompt."""
    print(
        "🔧 LSP GUARD — You are editing a Lean file.\n"
        "  ✅ lean_goal(file, line) → see proof state\n"
        "  ✅ lean_local_search(\"name\") → find lemmas\n"
        "  ✅ lean_diagnostic_messages(file) → verify after edit\n"
        "  ❌ NEVER: lake build | grep .lean | cat .lean\n"
    )

    # Suggest top 3 most-used tips
    try:
        tips = _load_top_tips(3)
        if tips:
            print("💡 Top problem-solving tips:")
            for t in tips:
                print(f"  P{t['priority']} [{t['id']}] {t['title']}: {t['content'][:100]}")
    except Exception:
        pass


def _load_top_tips(count: int) -> list:
    db_path = SCRIPT_DIR.parent / "experience" / "db.json"
    if not db_path.exists():
        return []
    with open(db_path) as f:
        db = json.load(f)
    tips = db.get("tips", [])
    tips = sorted(tips, key=lambda t: -t.get("times_used", 0))
    return tips[:count]


def suggest_tips(tag: str = "", count: int = 5):
    """Print tips matching the given context."""
    db_path = SCRIPT_DIR.parent / "experience" / "db.json"
    if not db_path.exists():
        print("No experience database found yet.")
        return
    with open(db_path) as f:
        db = json.load(f)
    tips = db.get("tips", [])
    if tag:
        tips = [t for t in tips if tag in t.get("tags", [])]
    tips = sorted(tips, key=lambda t: (-t.get("priority", 0), -t.get("times_used", 0)))
    total = len(tips)
    tips = tips[:count]
    if not tips:
        print("No tips found.")
        return
    print(f"\n💡 TIPS ({len(tips)} of {total} total)" +
          (f" matching tag '{tag}'" if tag else "") + ":\n" + "-" * 70)
    for t in tips:
        pbar = "█" * t.get("priority", 3) + "░" * (5 - t.get("priority", 3))
        used = t.get("times_used", 0)
        print(f"  [{t['id']}] P{t.get('priority','?')} {pbar} used:{used} | {t['title'][:45]}")
        print(f"         {t['content'][:120]}")
        print()


def post_edit(filepath: str, status: str = "success", msg: str = ""):
    """Suggest recording the result."""
    exp_path = SCRIPT_DIR / "experience.py"
    if status == "error":
        print(f"💡 To record this error for future sessions:")
        print(f"  python3 {exp_path} error add \"{filepath}\" <line> <type> \"{msg}\" --solution \"<fix>\"")


def session_check(logpath: str):
    """Run lsp_guard on a conversation log."""
    import subprocess
    guard_path = SCRIPT_DIR / "lsp_guard.py"
    result = subprocess.run(
        ["python3", str(guard_path), "check", logpath],
        capture_output=True, text=True
    )
    print(result.stdout)
    if result.returncode != 0:
        print("\n⚠️  LSP violations detected. Review the report above.")
    sys.exit(result.returncode)


def record(filepath: str, line: int, record_type: str, theorem: str,
           msg: str = "", tactic: str = "", solution: str = "", tags: str = ""):
    """Record a proof attempt in the experience database."""
    import subprocess
    exp_path = SCRIPT_DIR / "experience.py"
    if record_type == "error":
        cmd = [
            "python3", str(exp_path), "error", "add",
            filepath, str(line), "type_mismatch", msg,
            "--tactic", tactic, "--solution", solution, "--tags", tags
        ]
    else:
        cmd = [
            "python3", str(exp_path), "success", "add",
            theorem, filepath, tactic, msg, "--tags", tags
        ]
    subprocess.run(cmd)


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)

    cmd = sys.argv[1]

    if cmd == "pre-edit":
        filepath = sys.argv[2] if len(sys.argv) > 2 else ""
        pre_edit(filepath)

    elif cmd == "tips":
        tag = ""
        count = 5
        i = 2
        while i < len(sys.argv):
            if sys.argv[i] == "--tag" and i + 1 < len(sys.argv):
                tag = sys.argv[i + 1]; i += 2
            elif sys.argv[i] == "--count" and i + 1 < len(sys.argv):
                count = int(sys.argv[i + 1]); i += 2
            else:
                i += 1
        suggest_tips(tag, count)

    elif cmd == "audit":
        import subprocess
        exp_path = SCRIPT_DIR / "experience.py"
        subprocess.run(["python3", str(exp_path), "audit"])

    elif cmd == "track":
        # Track error count for divergence detection
        if len(sys.argv) < 4:
            print("Usage: lean_hook.py track <file.lean> <error_count> [--context ...]")
            sys.exit(1)
        filepath = sys.argv[2]
        error_count = sys.argv[3]
        context = ""
        if len(sys.argv) > 4 and sys.argv[4] == "--context" and len(sys.argv) > 5:
            context = sys.argv[5]
        import subprocess
        exp_path = SCRIPT_DIR / "experience.py"
        cmd_args = ["python3", str(exp_path), "timeline", "add", filepath, error_count]
        if context:
            cmd_args += ["--context", context]
        subprocess.run(cmd_args)

    elif cmd == "divergent":
        if len(sys.argv) < 3:
            print("Usage: lean_hook.py divergent <file.lean>")
            sys.exit(1)
        import subprocess
        exp_path = SCRIPT_DIR / "experience.py"
        subprocess.run(["python3", str(exp_path), "divergent", sys.argv[2]])

    elif cmd == "post-edit":
        filepath = sys.argv[2] if len(sys.argv) > 2 else ""
        status = "success"
        msg = ""
        errors = None
        i = 3
        while i < len(sys.argv):
            if sys.argv[i] == "--status" and i + 1 < len(sys.argv):
                status = sys.argv[i + 1]; i += 2
            elif sys.argv[i] == "--msg" and i + 1 < len(sys.argv):
                msg = sys.argv[i + 1]; i += 2
            elif sys.argv[i] == "--errors" and i + 1 < len(sys.argv):
                errors = sys.argv[i + 1]; i += 2
            else:
                i += 1
        post_edit(filepath, status, msg)
        if errors is not None:
            import subprocess
            exp_path = SCRIPT_DIR / "experience.py"
            subprocess.run(["python3", str(exp_path), "timeline", "add", filepath, errors, "--context", status])

    elif cmd == "session-check":
        if len(sys.argv) < 3:
            print("Usage: lean_hook.py session-check <log.json>")
            sys.exit(1)
        session_check(sys.argv[2])

    elif cmd == "record":
        if len(sys.argv) < 5:
            print(__doc__)
            sys.exit(1)

        filepath, line = sys.argv[2], int(sys.argv[3])
        record_type, theorem, msg, tactic, solution, tags = "error", "", "", "", "", ""
        i = 4
        while i < len(sys.argv):
            arg = sys.argv[i]
            if arg.startswith("--"):
                key = arg[2:]
                if i + 1 < len(sys.argv) and not sys.argv[i + 1].startswith("--"):
                    val = sys.argv[i + 1]; i += 2
                    if key == "type": record_type = val
                    elif key == "theorem": theorem = val
                    elif key == "msg": msg = val
                    elif key == "tactic": tactic = val
                    elif key == "solution": solution = val
                    elif key == "tags": tags = val
                else:
                    i += 1
            else:
                i += 1

        record(filepath, line, record_type, theorem, msg, tactic, solution, tags)

    else:
        print(f"Unknown command: {cmd}")
        print("Available: pre-edit, post-edit, session-check, record, tips, audit, track, divergent")


if __name__ == "__main__":
    main()
