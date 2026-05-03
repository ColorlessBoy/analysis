---
description: Guided cycle-by-cycle theorem proving with explicit checkpoints
argument-hint: '[scope] [--planning=ask|on|off] [--deep=never|stuck|ask] [--commit=ask|auto|never]'
---

# Lean4 Prove

Guided, cycle-by-cycle theorem proving. Asks before each cycle, supports deep escalation, and checkpoints your progress.

## Usage

```
/lean4:prove                         # Start guided session
/lean4:prove File.lean               # Focus on specific file
/lean4:prove --repair-only           # Fix build errors without filling sorries
/lean4:prove --deep=stuck            # Enable deep escalation when stuck
```

## Inputs

| Arg | Required | Default | Description |
|-----|----------|---------|-------------|
| scope | No | all | Specific file or theorem |
| --repair-only | No | false | Fix build errors only, skip sorry-filling |
| --planning | No | ask | `ask`, `on`, or `off` |
| --review-source | No | internal | `internal`, `external`, `both`, or `none` |
| --review-every | No | checkpoint | `N` (sorries), `checkpoint`, or `never` |
| --checkpoint | No | true | Create checkpoint commits after each cycle |
| --deep | No | never | `never`, `ask`, `stuck`, or `always` |
| --deep-sorry-budget | No | 1 | Max sorries per deep invocation |
| --deep-time-budget | No | 10m | Advisory time budget |
| --max-deep-per-cycle | No | 1 | Max deep invocations per cycle |
| --batch-size | No | 1 | Sorries to attempt per cycle |
| --commit | No | ask | `ask`, `auto`, or `never` |
| --golf | No | prompt | `prompt`, `auto`, or `never` |

## Actions

Each cycle follows the **6-phase cycle engine** (Plan → Work → Checkpoint → Review → Replan → Continue/Stop). See the lean4 skill for full cycle-engine mechanics.

### Cycle Phases

1. **Plan** — Discover sorries via LSP (`lean_diagnostic_messages`, `lean_goal`), search mathlib with up to 3 tools, present plan for user approval.
2. **Work** — Per sorry: refresh goal → search → generate 2-3 candidates → test via `lean_multi_attempt` → validate with `lean_diagnostic_messages` → stage & commit.
3. **Checkpoint** — Stage only files from accepted fills.
4. **Review** — Runs at configured `--review-every` intervals.
5. **Replan** — Adjust plan based on progress.
6. **Continue/Stop** — Prompt user after each cycle: `[continue] / [stop] / [adjust]`. Never auto-start next cycle.

### Startup

If key preferences are not passed via flags, ask once at startup for planning preference and review source.

### Commit Behavior

Show diff and ask before each commit when `--commit=ask` (default):
- **yes** — commit, prompt again
- **yes-all** — switch to auto for session
- **no** — unstage, skip
- **never** — unstage all remaining

### Deep Mode

Bounded subroutine for stubborn sorries. Modes: `never` | `ask` | `stuck` | `always`. Statement changes NOT permitted — header fence enforced.

### Stuck Definition

A sorry is stuck when: same failure 2-3x, same build error 2x, no progress 10+ min, or empty LSP search 2x. When stuck: review → replan → user approval.

### Completion

Report filled/remaining sorries, prompt for checkpoint and golf.

## Constraints

- Max 3 candidates per sorry
- ≤80 lines diff per fill
- No statement changes (use `/lean4:formalize` for header work)
- No cross-file refactoring (fast path)
- Follow mathlib 100-char line width
- Stage only touched files (`git add <files>`), never `git add -A`

## Primitives

Use scripts from `$LEAN4_SCRIPTS`:
- `sorry_analyzer.py` — find sorries
- `check_axioms_inline.sh` — axiom check
- `smart_search.sh` — mathlib search
- `cycle_tracker.sh` — session tracking

## See Also

- `/lean4:autoprove` — Autonomous multi-cycle proving
- `/lean4:draft` — Draft skeletons
- `/lean4:formalize` — Interactive draft + prove
- `/lean4:checkpoint` — Manual save point
- `/lean4:review` — Quality check (read-only)
- `/lean4:golf` — Optimize proofs
- `/lean4:doctor` — Diagnostics
