---
description: Autonomous end-to-end formalization from informal sources
argument-hint: '[--source=PATH] [--claim-select=first|named:...|regex:...] [--out=FILE] [--max-cycles=N]'
---

# Lean4 Autoformalize

Autonomous end-to-end formalization: extract claims from a source, draft skeletons, and prove them unattended. Wraps `/lean4:draft` + `/lean4:autoprove` in one command.

## Usage

```
/lean4:autoformalize --source=./paper.pdf --claim-select=first --out=Paper.lean
/lean4:autoformalize --source=./paper.pdf "Theorem 3.2" --out=Thm3_2.lean
/lean4:autoformalize --source=./paper.pdf --claim-select=regex:"Theorem [3-5]" --max-cycles=30
```

## Inputs

| Arg | Required | Default | Description |
|-----|----------|---------|-------------|
| --source | Yes | — | File/URL for claim extraction |
| --claim-select | Yes | — | `first`, `named:"..."`, `regex:"..."` |
| topic | No | — | Single claim to formalize |
| --out | Conditional | — | Target file (required if no existing target) |
| --rigor | No | sketch | `sketch` or `checked` |
| --statement-policy | No | preserve | `preserve`, `rewrite-generated-only`, `adjacent-drafts` |
| All autoprove flags | No | autoprove defaults | `--max-cycles`, `--deep`, etc. |

## Actions

1. Extract claims from `--source`
2. Apply `--claim-select` filter to build claim queue
3. Draft skeleton for each claim
4. Run autonomous proving on each skeleton
5. On stuck: re-draft if `next_action=redraft` (subject to `--statement-policy`)
6. Report final summary

## See Also

- `/lean4:formalize` — Interactive formalization
- `/lean4:draft` — Draft only
- `/lean4:autoprove` — Autonomous proving of existing skeletons
