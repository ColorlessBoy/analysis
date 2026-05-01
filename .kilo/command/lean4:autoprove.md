---
description: Autonomous multi-cycle theorem proving with explicit stop budgets
argument-hint: '[scope] [--max-cycles=N] [--max-total-runtime=DURATION] [--commit=auto|never] [--deep=never|stuck]'
---

# Lean4 Autoprove

Autonomous multi-cycle theorem proving. Runs cycles automatically with explicit stop budgets and structured summaries.

## Usage

```
/lean4:autoprove                        # Start autonomous session
/lean4:autoprove File.lean              # Focus on specific file
/lean4:autoprove --repair-only          # Fix build errors without filling sorries
/lean4:autoprove --max-cycles=10        # Limit total cycles
```

## Inputs

| Arg | Required | Default | Description |
|-----|----------|---------|-------------|
| scope | No | all | Specific file or theorem |
| --repair-only | No | false | Fix build errors only |
| --planning | No | on | `on` or `off` |
| --review-source | No | internal | `internal`, `external`, `both`, or `none` |
| --review-every | No | checkpoint | `N` (sorries), `checkpoint`, or `never` |
| --checkpoint | No | true | Create checkpoint commits after each cycle |
| --deep | No | stuck | `never`, `stuck`, or `always` |
| --deep-sorry-budget | No | 2 | Max sorries per deep invocation |
| --deep-time-budget | No | 20m | Advisory time budget |
| --max-deep-per-cycle | No | 1 | Max deep invocations per cycle |
| --max-consecutive-deep-cycles | No | 2 | Hard cap |
| --batch-size | No | 2 | Sorries to attempt per cycle |
| --commit | No | auto | `auto` or `never` |
| --golf | No | never | `prompt`, `auto`, or `never` |
| --max-cycles | No | 20 | Session stop budget |
| --max-total-runtime | No | 120m | Best-effort wall-clock budget |
| --max-stuck-cycles | No | 3 | Session stop budget |

## Actions

Same 6-phase cycle engine as `/lean4:prove` but autonomous:
1. **Plan** — LSP-first discovery, auto-plan
2. **Work** — Per sorry: search → candidates → test → validate → stage & commit
3. **Checkpoint** — Auto-stage
4. **Review** — Auto-review at intervals
5. **Replan** — Auto-replan
6. **Continue/Stop** — Auto-loop until stop condition

No questionnaire at startup. Discover state and start immediately.

## Stop Conditions

Stops when **first** of these is satisfied:
1. Completion — all sorries filled
2. Max stuck cycles — `--max-stuck-cycles` consecutive (default: 3)
3. Max cycles — `--max-cycles` reached (default: 20)
4. Max runtime — wall-clock budget reached
5. Manual user stop

## Structured Summary on Stop

```
## Autoprove Summary
Reason stopped: [completion | max-stuck | max-cycles | max-runtime | user-stop]
Metrics: sorries before/after, cycles run, stuck cycles, deep invocations, time elapsed
Handoff recommendations for remaining work.
```

## Deep Mode

Default: `stuck` (auto-escalate). `ask` coerced to `stuck` (no interactive prompting). Statement changes NOT permitted (header fence).

## Constraints

- Max 3 candidates per sorry, ≤80 lines diff
- No statement changes
- No cross-file refactoring (fast path)
- 100-char line width
- Stage only touched files

## See Also

- `/lean4:prove` — Guided cycle-by-cycle proving
- `/lean4:autoformalize` — Autonomous end-to-end formalization
- `/lean4:checkpoint` — Manual save point
- `/lean4:review` — Quality check
