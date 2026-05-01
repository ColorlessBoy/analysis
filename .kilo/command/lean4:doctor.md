---
description: Diagnostics, cleanup, and migration help
---

# Lean4 Doctor

Diagnose and fix environment issues: Lean version, Lake setup, missing dependencies, build cache, migration needs.

## Usage

```
/lean4:doctor                      # Run full diagnostics
```

## Checks

1. **Lean version** — `lean --version`, check against `lean-toolchain`
2. **Lake setup** — `lake --version`, verify lakefile consistency
3. **Build cache** — Check for stale `.lake/build`, suggest `lake cache get`
4. **Environment variables** — Verify `$LEAN4_SCRIPTS`, `$LEAN4_REFS`, `$LEAN4_PLUGIN_ROOT`
5. **Python availability** — Check Python 3 for scripts
6. **LSP connectivity** — Test MCP tools (`lean_goal`, `lean_diagnostic_messages`)
7. **Mathlib cache** — Check `.lake/packages/mathlib/` exists
8. **ripgrep** — Check `rg` for local search

## Common Fixes

- **Lean version mismatch:** Update `lean-toolchain` and run `lake update`
- **Missing LSP tools:** Ensure MCP server is running
- **Missing scripts:** Set `$LEAN4_SCRIPTS` environment variable
- **Stale build cache:** Run `lake clean && lake build`
- **Cold start:** Run `lake cache get` or `lake exe cache get`

## See Also

- `/lean4:learn --mode=repo` — Explore project after fix
