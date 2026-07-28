#!/usr/bin/env python3
"""Experience tracking for Lean subagents. Records successes and failures."""
import json, sys, os
from datetime import datetime

DB = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "experience", "db.json")
FAILURES = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "experience", "failures.json")

def _load(path, default=None):
    if os.path.exists(path):
        with open(path) as f: return json.load(f)
    return default or {}

def _save(path, data):
    with open(path, "w") as f: json.dump(data, f, indent=2)

def _now():
    return datetime.now().isoformat()

def cmd_success(args):
    """success add <theorem> <file> <tactics> <description>"""
    db = _load(DB, {"tips": [], "successes": [], "errors": []})
    thm, file, tactics, desc = args
    db.setdefault("successes", []).append({
        "theorem": thm, "file": file, "tactics": tactics, "description": desc,
        "time": _now()
    })
    _save(DB, db)
    print(f"Recorded success: {thm}")

def cmd_error(args):
    """error add <file> <line> <type> <message> [--solution ...]"""
    db = _load(DB, {"tips": [], "successes": [], "errors": []})
    file, line, etype, msg = args[0], args[1], args[2], args[3]
    solution = " ".join(args[4:]) if len(args) > 4 else ""
    db.setdefault("errors", []).append({
        "file": file, "line": line, "type": etype, "message": msg,
        "solution": solution, "time": _now()
    })
    _save(DB, db)
    print(f"Recorded error: {etype} at {file}:{line}")

def cmd_tip(args):
    """tip add <tag> <text>"""
    db = _load(DB, {"tips": [], "successes": [], "errors": []})
    tag, text = args
    db.setdefault("tips", []).append({
        "tag": tag, "text": text, "time": _now()
    })
    _save(DB, db)
    print(f"Added tip [{tag}]: {text[:60]}")

def cmd_tip_list(args):
    """tip list [--tag T]"""
    db = _load(DB, {"tips": []})
    tag = None
    if args and args[0] == "--tag":
        tag = args[1]
    tips = db.get("tips", [])
    if tag: tips = [t for t in tips if t.get("tag") == tag]
    for t in tips:
        print(f"[{t.get('tag','')}] {t.get('text','')}")
    if not tips: print("No tips found")

def cmd_error_search(args):
    """error search <topic>"""
    db = _load(DB, {"errors": []})
    topic = " ".join(args).lower()
    found = [e for e in db.get("errors", []) if topic in e.get("message","").lower() or topic in e.get("type","").lower()]
    for e in found:
        print(f"{e.get('file','')}:{e.get('line','')} [{e.get('type','')}] {e.get('message','')[:100]}")
        if e.get("solution"): print(f"  Solution: {e['solution'][:100]}")
    if not found: print(f"No errors matching '{topic}'")

def cmd_stats(args):
    db = _load(DB, {"tips": [], "successes": [], "errors": []})
    print(f"Tips: {len(db.get('tips',[]))}, Successes: {len(db.get('successes',[]))}, Errors: {len(db.get('errors',[]))}")

def cmd_session_start(args):
    """session start <theorem_name> <file> <goal_text>"""
    db = _load(FAILURES, {"version": 1, "sessions": []})
    session = {
        "id": len(db.get("sessions", [])),
        "theorem": args[0], "file": args[1], "goal": " ".join(args[2:])[:500],
        "start": _now(), "attempts": [], "status": "in_progress"
    }
    db.setdefault("sessions", []).append(session)
    _save(FAILURES, db)
    print(session["id"])

def cmd_session_attempt(args):
    """session attempt <id> <edit_summary> <error_before> <error_after> <diagnostics_excerpt>"""
    db = _load(FAILURES, {"version": 1, "sessions": []})
    sid = int(args[0])
    session = db["sessions"][sid]
    attempt = {
        "edit": args[1][:200], "errors_before": int(args[2]), "errors_after": int(args[3]),
        "excerpt": args[4][:300], "time": _now()
    }
    session.setdefault("attempts", []).append(attempt)
    _save(FAILURES, db)
    print(f"Attempt {len(session['attempts'])}: {attempt['errors_before']}→{attempt['errors_after']} errors") # type: ignore

def cmd_session_end(args):
    """session end <id> <success|fail> <notes>"""
    db = _load(FAILURES, {"version": 1, "sessions": []})
    sid = int(args[0])
    session = db["sessions"][sid]
    session["status"] = args[1]
    session["notes"] = " ".join(args[2:])
    session["end"] = _now()
    _save(FAILURES, db)
    print(f"Session {sid} ended: {args[1]}")

def cmd_last_failures(args):
    """last <n>"""
    db = _load(FAILURES, {"version": 1, "sessions": []})
    n = int(args[0]) if args else 5
    sessions = db.get("sessions", [])[-n:]
    for s in sessions:
        status = s.get("status", "?")
        icon = "✓" if status == "success" else "✗" if status == "fail" else "…"
        print(f"{icon} [{s.get('id')}] {s.get('theorem','')} — {status}")
        for a in s.get("attempts", [])[-3:]:
            print(f"    {a['errors_before']}→{a['errors_after']} errors: {a['edit'][:80]}")

def cmd_tips_for(args):
    """tips-for <topic>"""
    db = _load(DB, {"tips": []})
    topic = " ".join(args).lower()
    tips = [t for t in db.get("tips", []) if topic in t.get("text","").lower() or topic in t.get("tag","").lower()]
    for t in tips:
        print(f"[{t.get('tag','')}] {t.get('text','')}")
    if not tips: print("No relevant tips")

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print(__doc__); sys.exit(1)
    cmd, rest = sys.argv[1], sys.argv[2:]
    if cmd == "success" and rest and rest[0] == "add": cmd_success(rest[1:])
    elif cmd == "error" and rest and rest[0] == "add": cmd_error(rest[1:])
    elif cmd == "tip" and rest and rest[0] == "add": cmd_tip(rest[1:])
    elif cmd == "tip" and rest and rest[0] == "list": cmd_tip_list(rest[1:])
    elif cmd == "error" and rest and rest[0] == "search": cmd_error_search(rest[1:])
    elif cmd == "stats": cmd_stats(rest)
    elif cmd == "session":
        if rest[0] == "start": cmd_session_start(rest[1:])
        elif rest[0] == "attempt": cmd_session_attempt(rest[1:])
        elif rest[0] == "end": cmd_session_end(rest[1:])
    elif cmd == "last": cmd_last_failures(rest)
    elif cmd == "tips-for": cmd_tips_for(rest)
    else: print(f"Unknown: {cmd}")
