---
description: Read-only code review of Lean proofs
argument-hint: '[target] [--scope=sorry|deps|file|changed|project] [--line=N] [--mode=batch|stuck]'
---

# Lean4 Review

Read-only review of Lean proofs for quality, style, and optimization opportunities. **Non-destructive:** files are restored after analysis.

## Usage

```
/lean4:review                              # Review changed files
/lean4:review File.lean                    # Review specific file
/lean4:review File.lean --line=89          # Review single sorry
/lean4:review File.lean --line=89 --scope=deps  # Review sorry + dependencies
/lean4:review --scope=project              # Review entire project (prompts)
/lean4:review --mode=stuck                 # Triage mode for stuck proofs
```

## Inputs

| Arg | Required | Description |
|-----|----------|-------------|
| target | No | File or directory |
| --scope | No | `sorry`, `deps`, `file`, `changed`, or `project` |
| --line | No | Line number for single-sorry scope |
| --mode | No | `batch` (full review) or `stuck` (triage, top 3 blockers) |
| --json | No | Output structured JSON |

## Scope Defaults

- No args → `--scope=changed`
- Target file → `--scope=file`
- Target + `--line` → `--scope=sorry`

## Review Modes

**Batch mode (default):**
- Full review: build status, sorry audit, axiom check, style, golfing opportunities, complexity
- Reports all findings

**Stuck mode:**
- Lightweight triage: top 3 blockers with actionable next steps
- Skips golf analysis and complexity metrics
- Output includes `next_action` classification

## Actions

1. **Build Status** — `lean_diagnostic_messages(file)` or `lake build`
2. **Sorry Audit** — `sorry_analyzer.py` with `--report-only`
3. **Axiom Check** — `check_axioms_inline.sh` with `--report-only`
4. **Style Review** — Mathlib conventions, naming, 100-char line width
5. **Golfing Opportunities** — `find_golfable.py`

## Post-Review

After review: offer to create an action plan from findings. Route to:
- `/lean4:prove` — for missing proofs
- `/lean4:refactor` — for strategy improvements
- `/lean4:golf` — for tactic-level cleanup

## Safety

- Read-only — does not modify files
- Axiom check temporarily appends `#print axioms`, then restores
- Does not create commits or apply fixes

## See Also

- `/lean4:golf` — Apply golfing optimizations
- `/lean4:refactor` — Strategy-level simplification
- `/lean4:prove` — Fill sorries discovered in review
