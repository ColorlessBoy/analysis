---
description: Save progress with a safe commit checkpoint (per-file + project build, axiom check, commit)
---

# Lean4 Checkpoint

Save point with safety checks: per-file build → project build → axiom check → commit.

## Usage

```
/lean4:checkpoint                    # Checkpoint current state
```

## Actions

1. **Per-file validation** — `lean_diagnostic_messages` on all modified files
2. **Project build** — `lake build` to ensure whole project compiles
3. **Axiom check** — Verify only standard axioms (propext, Classical.choice, Quot.sound)
4. **Commit** — If all checks pass, commit with descriptive message

## Safety

- Fails if build fails — no commit
- Fails if non-standard axioms detected — no commit
- Only stages files touched in current session
- Never `git add -A` or broad patterns

## See Also

- `/lean4:prove` — Guided proving with per-cycle checkpoints
- `/lean4:autoprove` — Autonomous proving with auto-checkpoints
- `/lean4:review` — Read-only quality check
