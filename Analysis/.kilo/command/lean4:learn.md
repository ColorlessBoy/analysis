---
description: Interactive teaching and mathlib exploration
argument-hint: '[topic] [--mode=repo|mathlib|goal|game]'
---

# Lean4 Learn

Interactive teaching and exploration. Three modes: repo orientation, mathlib exploration, and game tracks.

## Usage

```
/lean4:learn --mode=repo              # Explore project structure
/lean4:learn --mode=mathlib           # Navigate mathlib for a topic
/lean4:learn "topological groups"     # Learn about a topic in mathlib
/lean4:learn --mode=game              # Structured practice track
```

## Inputs

| Arg | Required | Description |
|-----|----------|-------------|
| topic | No | Math topic or concept to explore |
| --mode | No | `repo`, `mathlib`, `goal`, or `game` |

## Modes

- **repo** — Understand project structure, key lemmas, dependencies
- **mathlib** — Search and explore mathlib for a topic; find relevant theorems, typeclasses, tactics
- **goal** — Learn how to prove a specific goal type
- **game** — Interactive proof challenges for skill building

## Actions

1. Use LSP tools to search mathlib and inspect definitions
2. Provide structured learning with code examples
3. Explain conventions and patterns
4. Show relevant references from mathlib style guide

## See Also

- `/lean4:draft` — Apply learning to draft new proofs
- `/lean4:doctor` — Diagnostics when stuck
- [mathlib-style.md] — Mathlib conventions reference
