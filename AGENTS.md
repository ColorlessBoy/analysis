## Lean 4 Workflows

Lean 4 skill loaded at `~/.opencode/skills/lean4/SKILL.md`.
Commands available via `/lean4:*` (see `.kilo/command/`).

### Lean LSP MCP

MCP server configured in `opencode.json` via `uvx lean-lsp-mcp`.
Restart opencode after first-run to activate the MCP server.
Tools: `lean_goal`, `lean_local_search`, `lean_diagnostic_messages`, `lean_multi_attempt`, etc.

### LSP Guard — Automated Workflow Compliance

Scripts in `.agents/scripts/` enforce LSP-first workflow:

```bash
# Inject pre-edit reminder + top tips into prompt
python3 .agents/scripts/lean_hook.py pre-edit <file.lean>

# Check a conversation log for LSP violations
python3 .agents/scripts/lean_hook.py session-check <log.json>

# Get context-relevant problem-solving tips
python3 .agents/scripts/lean_hook.py tips [--tag <tag>] [--count N]

# Record a proof result in experience DB
python3 .agents/scripts/lean_hook.py record <file.lean> <line> \
  --type error|success --theorem <name> --msg "..." \
  [--tactic "..."] [--solution "..."] [--tags t1,t2]
```

### Experience Database — Proof Knowledge Base (CRUD)

Five collections: **errors**, **successes**, **tips**, **timeline** (divergence), **meta** (self-audit). Pre-initialized with 15 default tips.

```bash
# Error experiences (learn from failures)
python3 .agents/scripts/experience.py error add <file> <line> <type> <msg> [--tactic ...] [--solution ...] [--tags ...]
python3 .agents/scripts/experience.py error list [--tag <tag>] [--type <type>] [--limit N]
python3 .agents/scripts/experience.py error get <id>
python3 .agents/scripts/experience.py error update <id> [--solution ...] [--tags ...]
python3 .agents/scripts/experience.py error delete <id>
python3 .agents/scripts/experience.py error search <query>

# Success experiences (reusable winning patterns)
python3 .agents/scripts/experience.py success add <theorem> <file> <tactic_seq> <description> [--tags ...]
python3 .agents/scripts/experience.py success list [--tag <tag>] [--limit N]
python3 .agents/scripts/experience.py success get <id>
python3 .agents/scripts/experience.py success update <id> [--description ...] [--tactic_seq ...] [--tags ...]
python3 .agents/scripts/experience.py success delete <id>
python3 .agents/scripts/experience.py success search <query>

# Problem-solving tips (heuristics + strategies)
python3 .agents/scripts/experience.py tip add <title> <content> [--priority 1-5] [--tags ...]
python3 .agents/scripts/experience.py tip list [--tag <tag>] [--priority <N>] [--limit N]
python3 .agents/scripts/experience.py tip get <id>
python3 .agents/scripts/experience.py tip used <id>     # increment usage counter
python3 .agents/scripts/experience.py tip update <id> [--title ...] [--content ...] [--priority ...] [--tags ...]
python3 .agents/scripts/experience.py tip delete <id>
python3 .agents/scripts/experience.py tip search <query>
python3 .agents/scripts/experience.py tip top [N]       # most-used tips

# Timeline (divergence detection — error counts per file over time)
python3 .agents/scripts/experience.py timeline add <file> <error_count> [--context "..."]
python3 .agents/scripts/experience.py timeline show <file> [--limit N]
python3 .agents/scripts/experience.py divergent <file>   # check if diverging

# Meta (self-observation for skill self-audit)
python3 .agents/scripts/experience.py meta add <key> <value> [--note "..."]
python3 .agents/scripts/experience.py meta list
python3 .agents/scripts/experience.py meta increment <key> [--by N]

# Self-audit
python3 .agents/scripts/experience.py audit
python3 .agents/scripts/lean_hook.py audit

# Global
python3 .agents/scripts/experience.py stats
python3 .agents/scripts/experience.py export [--format json|markdown]
```

DB stored at `.agents/experience/db.json`. Auto-initialized with 15 tips + 6 meta keys on first use.

### Convergence Control — error divergence (50→70→90)

After each edit + `lean_diagnostic_messages`, track the error count:
```bash
python3 .agents/scripts/lean_hook.py track <file> <error_count> --context "after tactic X"
```

If errors **strictly increase** over 3+ checkpoints, the guard fires:
```
🚨 DIVERGENCE DETECTED — STOP editing
  → git stash; re-read theorem from PDF; dispatch fresh subagent
```

### Formalization Self-Doubt — when stuck, question the statement

When stuck >5 attempts or after divergence:
1. Try proving the negation — if easy, the statement is wrong
2. Compare with source book/PDF (missing hypotheses? wrong quantifier order?)
3. Try a simplified version (drop a hypothesis, fix a parameter)

```bash
python3 .agents/scripts/experience.py tip list --tag formalization-doubt
python3 .agents/scripts/experience.py meta increment total_formalization_doubts
```

### Self-Audit — is the skill itself working?

```bash
python3 .agents/scripts/lean_hook.py audit
```

Checks: LSP compliance ratio, divergence frequency, tip utilization, error/success ratio, SKILL.md integrity, per-file timeline health.

### Subagent Dispatch Protocol (MANDATORY for ≥3 sorries)

**≥3 sorries in scope → MANDATORY subagent dispatch.** Main thread = orchestration only.

**⚠️ Max 1 concurrent subagent.** The MCP server is single-connection. Parallel subagents crash it.

```
Main thread:  plan → prepare context → dispatch 1 subagent → wait → verify integration → commit → next
Subagent:     receive contract → create temp file → LSP-iterate there → return proof block → done
```

**Trust-but-verify**: Main thread always runs `lean_diagnostic_messages(real_file)` after integration. Subagent "success" reports are NOT trusted until verified.

**Diff-Not-Write**: Subagents produce proof blocks (text), not file edits. Main thread controls all file mutations.

#### Generate a subagent prompt (contract + context injected):

```bash
python3 .agents/scripts/subagent_prompt.py <file.lean> <line> \
  [--theorem <name>] [--deps <deps_file>] [--tag <tip_tag>]
```

#### Subagent contract: `.agents/scripts/subagent-contract.md`

Every proof subagent MUST receive this contract. Subagent output: PROOF_BLOCK (text) + report. Subagent NEVER edits real file.

#### Parallel dispatch rules:

- **Max 1 concurrent subagent.** No exceptions. More = MCP crash.
- **Temp file mandatory**: subagent creates `/tmp/sorry_<name>.lean`, iterates there, returns proof block
- **Proof block integration**: main thread reads proof block, pastes into real file, verifies with `lean_diagnostic_messages`
- **Per-sorry checkpoint**: after each successful integration, `git commit`
- **Trivial sorries** (`rfl`, `simp`) → solve inline, no dispatch needed

### Editor Workflow (MUST follow for .lean files)

```
1. Query prior experience:  experience.py tip list; experience.py error search <topic>
2. sorry_status.py <file>            ← locate all sorries + dependency hints
3. lean_file_outline(file)           ← understand structure
4. Group sorries by dependency; plan dispatch order
5. For each sorry:
   a. Generate subagent prompt: subagent_prompt.py <file> <line> [--tag ...]
   b. Dispatch: task(subagent_type="general", prompt=<generated prompt>)
   c. Collect report; if fail, replan or retry with fresh subagent
6. After all subagents: lean_diagnostic_messages(file) ← full-file verify
7. Record results: experience.py success add ... / experience.py error add ...
```

### NEVER Rules for .lean files

| ❌ NEVER | ✅ ALWAYS |
|----------|----------|
| `lake build` for per-file check | `lean_diagnostic_messages(file)` |
| `grep` on .lean for lemmas | `lean_local_search("name")` |
| `cat`/`head`/`tail` to read file | Read tool |
| Modify multiple theorems at once | One lemma at a time, verify each |
| ≥3 sorries solved in main thread | Dispatch subagents, one sorry each |
| Dispatch subagent without contract | Use `subagent_prompt.py` to inject contract |
| Parallel subagents (≥2) | Max 1 concurrent — MCP is single-connection |
| Subagent writes directly to real file | Temp file → verify → copy back |

### Environment Variables

Set these in your shell profile (`.zshrc`) or before running opencode:

```bash
export LEAN4_PLUGIN_ROOT=$HOME/.local/share/lean4-skills/plugins/lean4
export LEAN4_SCRIPTS="$LEAN4_PLUGIN_ROOT/lib/scripts"
export LEAN4_REFS="$LEAN4_PLUGIN_ROOT/skills/lean4/references"
```

These enable script-based primitives (`sorry_analyzer.py`, `check_axioms_inline.sh`, etc.) when LSP is unavailable.

### Kilo (Legacy)

MCP server also configured in `kilo.json` via `uvx lean-lsp-mcp` for Kilo users.