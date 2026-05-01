---
description: Leverage mathlib, extract helpers, simplify proof strategies
argument-hint: '[target] [--dry-run] [--search=off|quick|full]'
---

# Lean4 Refactor

Strategy-level proof simplification: leverage mathlib, extract helper lemmas, apply congr-lemma patterns, simplify proof structure. Operates at the **strategy** level (before `/lean4:golf` for tactic-level optimization).

## Usage

```
/lean4:refactor File.lean              # Refactor specific file
/lean4:refactor File.lean --dry-run    # Show suggestions without applying
/lean4:refactor --search=full          # Full search for mathlib replacements
```

## Inputs

| Arg | Required | Description |
|-----|----------|-------------|
| target | No | File or file:line |
| --dry-run | No | Preview only, no changes |
| --search | No | `off`, `quick` (default), or `full` |

## Actions

1. **Verify Build** — Ensure code compiles
2. **Analyze** — Identify structural patterns: repeated proofs, long proofs (>30 lines), manual instances
3. **Search Mathlib** — Find existing lemmas that can replace complex proofs
4. **Extract Helpers** — Lift repeated sub-proofs into named lemmas
5. **Apply** — Make changes with per-change verification
6. **Report** — Summary of changes

## Refactoring Strategies

- **Mathlib leverage:** Replace manual proofs with existing lemmas
- **Helper extraction:** Factor repeated patterns into lemmas
- **Congr-lemma patterns:** Use `congrArg`, `congrFun` where applicable
- **Typeclass simplification:** Reorder/merge haveI/letI blocks
- **Proof structure:** Simplify induction/cases patterns

## Constraints

- No statement changes
- No axiom changes
- Each change verified with `lean_diagnostic_messages`
- Revert on build failure

## See Also

- `/lean4:review` — Read-only analysis (no changes)
- `/lean4:golf` — Tactic-level optimization
- `/lean4:prove` — Fill remaining sorries after refactor
