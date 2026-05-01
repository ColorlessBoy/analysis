---
description: Interactive formalization — drafting plus guided proving
argument-hint: '[topic] [--source=PATH] [--output=chat|scratch|file]'
---

# Lean4 Formalize

Interactive synthesis: draft Lean skeletons from informal claims, then run guided prove cycles with user interaction.

## Usage

```
/lean4:formalize "Every continuous function on a compact set is bounded"
/lean4:formalize --source ./paper.pdf
/lean4:formalize --output=file --out=Analysis.lean "..."
```

## Inputs

| Arg | Required | Default | Description |
|-----|----------|---------|-------------|
| topic | No | — | Informal claim |
| --source | No | — | File/URL for claim extraction |
| --output | No | chat | `chat`, `scratch`, or `file` |
| --out | No | — | Output file (required if `--output=file`) |
| --rigor | No | sketch | `sketch` or `checked` |
| All prove flags | No | prove defaults | Passed through to prove phase |

## Actions

1. **Draft phase** — Extract claims → search mathlib → draft skeletons → user review
2. **Prove phase** — Guided cycle-by-cycle proving on drafted skeletons
3. **Completion** — Report, prompt for checkpoint and golf

## Statement Safety

Declaration headers may be redrafted during the formalize session (this is the synthesis wrapper). Once handed off to standalone `/lean4:prove`, headers are immutable.

## See Also

- `/lean4:autoformalize` — Autonomous end-to-end formalization
- `/lean4:draft` — Draft only (no proving)
- `/lean4:prove` — Guided proving on existing skeletons
