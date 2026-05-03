---
description: Improve proofs for directness, clarity, performance, and brevity
argument-hint: '[target] [--dry-run] [--search=off|quick|full]'
---

# Lean4 Golf

Improve Lean proofs that already compile. Score candidates by: correctness → directness → clarity/inference burden → performance/determinism → length.

**Prerequisite:** Code must compile.

## Usage

```
/lean4:golf                     # Golf entire project
/lean4:golf File.lean           # Golf specific file
/lean4:golf File.lean:42        # Golf proof at specific line
/lean4:golf --dry-run           # Show opportunities without applying
/lean4:golf --search=full       # Include lemma replacement pass
```

## Inputs

| Arg | Required | Description |
|-----|----------|-------------|
| target | No | File or file:line |
| --dry-run | No | Preview only, no changes |
| --search | No | `off`, `quick` (default), or `full` |

## Scoring Order

1. Correctness (must still compile)
2. Directness (more direct proof shape)
3. Clarity (lower inference/search burden)
4. Performance/determinism
5. Length (tiebreaker only)

## Instant Wins (Always Apply)

| Before | After |
|--------|-------|
| `ext x; rfl` | `rfl` |
| `simp; rfl` | `simp` |
| `constructor; exact h1; exact h2` | `exact ⟨h1, h2⟩` |
| `apply f; exact h` | `exact f h` |
| `by exact t` | `t` (at declaration RHS only) |

## Safe with Verification

- Inline let bindings used ≤2 times
- Inline have blocks used once, ≤1 line

## Safety Rules

- Reverts immediately on build failure
- No naked `;` introduction
- `<;>` only for identical goals
- Length is tiebreaker, not license for heavier tactics
- Never replace `exact` with `simpa`/`rwa` unless `exact` fails
- Does not create commits (use `/lean4:checkpoint`)

## Saturation

Stop when success rate < 20% or last 3 attempts failed.

## See Also

- `/lean4:review` — Read-only analysis before golfing
- `/lean4:refactor` — Strategy-level simplification (before golf)
- `/lean4:checkpoint` — Save after golfing
