---
description: Draft Lean declaration skeletons from informal claims
argument-hint: '[topic] [--mode=skeleton|attempt] [--source=PATH] [--output=chat|scratch|file]'
---

# Lean4 Draft

Draft Lean 4 declaration skeletons from informal mathematical claims. Produces sorry-stubbed statements ready for `/lean4:prove` or `/lean4:autoprove`.

## Usage

```
/lean4:draft "Every continuous function on a compact set is bounded"
/lean4:draft --mode=attempt "Zorn's lemma implies AC"
/lean4:draft --source ./paper.pdf
/lean4:draft --source ./paper.pdf "Theorem 3.2"
/lean4:draft --output=file --out=MyTheorem.lean "..."
```

## Inputs

| Arg | Required | Default | Description |
|-----|----------|---------|-------------|
| topic | No | — | Informal claim or math statement |
| --mode | No | skeleton | `skeleton` (headers only) or `attempt` (shallow proof) |
| --source | No | — | File/URL for claim extraction |
| --claim-select | No | first | `first`, `named:"..."`, `regex:"..."` |
| --output | No | chat | `chat`, `scratch`, or `file` |
| --out | No | — | Output file path (required if `--output=file`) |
| --rigor | No | sketch | `sketch` or `checked` |
| --style | No | mathlib4 | `mathlib4`, `kaggle`, `analysis`, `math4` |

## Modes

- **Skeleton (default):** Produce valid-against-mathlib headers with `:= by sorry`. No proof attempts.
- **Attempt:** Optionally attempt a shallow first proof pass after drafting.

## Output

When `--output=file --out=File.lean`, writes to disk. Otherwise displays in chat. Warning: `--output=file` will overwrite without confirmation.

## Actions

1. Parse the claim (from topic, source, or stdin)
2. Search mathlib for existing definitions/theorems (LSP: `lean_search`, `lean_loogle`, `lean_local_search`)
3. Draft declaration(s) following mathlib conventions (naming, typeclasses, binder style)
4. Review: check typeclass assumptions, noncomputable markers, decidability instances
5. Output in requested format

## See Also

- `/lean4:formalize` — Draft + guided proving
- `/lean4:autoformalize` — Autonomous end-to-end formalization
- `/lean4:prove` — Fill sorries
- `/lean4:learn` — Explore mathlib
