## Lean 4 Workflows

Lean 4 skill loaded at `analysis/.agents/skills/lean4/SKILL.md`.
Commands available via `/lean4:*` (see `.kilo/command/`).

### Lean LSP MCP

MCP server configured in `kilo.json` via `uvx lean-lsp-mcp`.
Restart Kilo after first-run to activate the MCP server.
Tools: `lean_goal`, `lean_local_search`, `lean_diagnostic_messages`, `lean_multi_attempt`, etc.

### Environment Variables

Set these in your shell profile (`.zshrc`) or before running Kilo:

```bash
export LEAN4_PLUGIN_ROOT=/Users/penglingwei/.codex/vendor_imports/lean4-skills/plugins/lean4
export LEAN4_SCRIPTS="$LEAN4_PLUGIN_ROOT/lib/scripts"
export LEAN4_REFS="$LEAN4_PLUGIN_ROOT/skills/lean4/references"
```

These enable script-based primitives (`sorry_analyzer.py`, `check_axioms_inline.sh`, etc.) when LSP is unavailable.
