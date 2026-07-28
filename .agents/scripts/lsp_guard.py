#!/usr/bin/env python3
"""
lsp_guard.py — Lean LSP workflow compliance checker.

Checks whether the model is following LSP-first rules:
1. Using lean_diagnostic_messages instead of lake build
2. Using lean_local_search instead of grep on .lean files
3. Using Read tool instead of cat/head/tail on .lean files
4. Following the edit→verify cycle

Usage:
  python3 lsp_guard.py check <conversation_log.json>   # check a conversation
  python3 lsp_guard.py inject                           # print reminder to inject into prompt
  python3 lsp_guard.py stats <conversation_log.json>    # print LSP usage statistics
"""

import json
import re
import sys
from pathlib import Path
from datetime import datetime
from collections import defaultdict

BASH_VIOLATIONS = {
    "lake_build": {
        "pattern": r"lake\s+build",
        "msg": "lake build detected — use lean_diagnostic_messages(file) instead (0.5s vs 60s). Only lake build at cold start, new imports, or checkpoint.",
        "severity": "high",
    },
    "grep_lean": {
        "pattern": r'grep\s.*\.lean',
        "msg": "grep on .lean files — use lean_local_search('keyword') instead for lemma discovery, or the Grep tool (not bash grep) for content search.",
        "severity": "medium",
    },
    "cat_lean": {
        "pattern": r'cat\s+.*\.lean',
        "msg": "cat on .lean files — use the Read tool instead to read file contents.",
        "severity": "low",
    },
    "head_tail_lean": {
        "pattern": r'(head|tail)\s.*\.lean',
        "msg": "head/tail on .lean files — use the Read tool with offset/limit instead.",
        "severity": "low",
    },
    "lake_env_lean": {
        "pattern": r'lake\s+env\s+lean',
        "msg": "lake env lean — prefer lean_diagnostic_messages(file) for per-file checks (uses LSP cache). Use lake env lean only as file-level gate.",
        "severity": "medium",
    },
}

LSP_TOOLS = [
    "lean_goal", "lean_hover_info", "lean_local_search", "lean_leanfinder",
    "lean_leansearch", "lean_loogle", "lean_hammer_premise", "lean_state_search",
    "lean_multi_attempt", "lean_diagnostic_messages", "lean_code_actions",
    "lean_file_outline", "lean_completions", "lean_references",
    "lean_declaration_file", "lean_verify", "lean_build",
]

EXPECTED_AFTER_EDIT = [
    "lean_diagnostic_messages",
    "lean_goal",
]


def check_messages(messages: list[dict]) -> dict:
    """Analyze conversation messages for LSP compliance."""
    result = {
        "violations": [],
        "lsp_tool_counts": defaultdict(int),
        "edits_without_verify": 0,
        "total_edits": 0,
        "lsp_tools_used": 0,
        "bash_tools_used": 0,
        "score": 100,
    }

    for i, msg in enumerate(messages):
        role = msg.get("role", "")
        content = str(msg.get("content", ""))
        tool_calls = msg.get("tool_calls", []) or msg.get("tool_use", []) or []

        # Check LSP tool usage
        for tool_name in LSP_TOOLS:
            count = content.count(tool_name)
            if count > 0:
                result["lsp_tool_counts"][tool_name] += count
                result["lsp_tools_used"] += count

        # Check for bash/bad patterns
        if role == "assistant" or "tool" in str(msg).lower():
            for violation_key, violation_info in BASH_VIOLATIONS.items():
                if re.search(violation_info["pattern"], content, re.IGNORECASE):
                    result["violations"].append({
                        "type": violation_key,
                        "msg": violation_info["msg"],
                        "severity": violation_info["severity"],
                        "context": content[:200],
                    })
                    result["bash_tools_used"] += 1

        # Count edits
        if "edit" in str(tool_calls).lower() or "write" in str(tool_calls).lower():
            result["total_edits"] += 1
            # Check if next 2 messages contain diagnostic check
            verified = False
            for j in range(i + 1, min(len(messages), i + 5)):
                next_content = str(messages[j].get("content", ""))
                for expected in EXPECTED_AFTER_EDIT:
                    if expected in next_content:
                        verified = True
                        break
                if verified:
                    break
            if not verified:
                result["edits_without_verify"] += 1

    # Calculate score
    if result["violations"]:
        for v in result["violations"]:
            if v["severity"] == "high":
                result["score"] -= 15
            elif v["severity"] == "medium":
                result["score"] -= 8
            else:
                result["score"] -= 3

    if result["edits_without_verify"] > 0:
        result["score"] -= result["edits_without_verify"] * 10

    if result["lsp_tools_used"] == 0 and result["total_edits"] > 0:
        result["score"] -= 30
        result["violations"].append({
            "type": "no_lsp",
            "msg": "No LSP tools used at all despite making edits. Use lean_goal, lean_diagnostic_messages, etc.",
            "severity": "high",
        })

    result["score"] = max(0, result["score"])
    return result


def format_report(result: dict) -> str:
    """Format a human-readable compliance report."""
    lines = []
    lines.append("=" * 60)
    lines.append(f"  LSP GUARD REPORT — score: {result['score']}/100")
    lines.append("=" * 60)

    if result["violations"]:
        lines.append(f"\n🚨  VIOLATIONS ({len(result['violations'])}):")
        for v in result["violations"]:
            icon = {"high": "🔴", "medium": "🟡", "low": "🟢"}.get(v["severity"], "⚪")
            lines.append(f"  {icon} [{v['severity']}] {v['msg']}")
    else:
        lines.append("\n✅  No violations detected.")

    lines.append(f"\n📊  STATISTICS:")
    lines.append(f"  LSP tools used: {result['lsp_tools_used']}")
    lines.append(f"  Bash/shell violations: {result['bash_tools_used']}")
    lines.append(f"  Edits: {result['total_edits']}")
    lines.append(f"  Edits without verify: {result['edits_without_verify']}")

    if result["lsp_tool_counts"]:
        lines.append(f"\n🔧  LSP TOOL USAGE:")
        for tool, count in sorted(result["lsp_tool_counts"].items(), key=lambda x: -x[1]):
            lines.append(f"  {tool}: {count}")

    lines.append("=" * 60)
    return "\n".join(lines)


def get_inject_reminder() -> str:
    """Return a short prompt to inject before .lean file edits."""
    return (
        "🔧 LSP GUARD ACTIVE — Before editing .lean files:\n"
        "  1. lean_goal(file, line) to see proof state\n"
        "  2. lean_local_search / lean_state_search to find lemmas\n"
        "  3. After edit: lean_diagnostic_messages(file) to verify\n"
        "  NEVER: lake build for per-file checks | grep for lemma search | cat to read files"
    )


def main():
    if len(sys.argv) < 2:
        print("Usage: lsp_guard.py <command> [args]")
        print("  check <log.json>    — analyze conversation log")
        print("  inject              — print reminder for prompt injection")
        print("  stats <log.json>    — print LSP usage statistics only")
        sys.exit(1)

    cmd = sys.argv[1]

    if cmd == "inject":
        print(get_inject_reminder())
        return

    if cmd in ("check", "stats"):
        if len(sys.argv) < 3:
            print("Error: need a JSON log file path")
            sys.exit(1)

        log_path = Path(sys.argv[2])
        if not log_path.exists():
            print(f"Error: file not found: {log_path}")
            sys.exit(1)

        with open(log_path) as f:
            data = json.load(f)

        messages = data if isinstance(data, list) else data.get("messages", [])
        if not messages:
            print("Warning: no messages found in log. Expected format: [{\"role\":...,\"content\":...},...]")

        result = check_messages(messages)

        if cmd == "check":
            print(format_report(result))
            sys.exit(1 if result["violations"] else 0)
        elif cmd == "stats":
            print(json.dumps({
                "score": result["score"],
                "lsp_tool_counts": dict(result["lsp_tool_counts"]),
                "violations": len(result["violations"]),
                "edits": result["total_edits"],
                "edits_without_verify": result["edits_without_verify"],
            }, indent=2))


if __name__ == "__main__":
    main()
