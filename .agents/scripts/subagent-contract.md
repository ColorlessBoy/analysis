# Subagent Contract — Lean 4 Proof Subagent

> The subagent's standing rules live in `.opencode/agents/lean-prover.md`
> (its agent prompt). This contract is the SHORT task brief the main thread
> includes in each dispatch. Do NOT paste the old 217-line contract into
> prompts — prompts over ~2500 chars measurably return empty.

## Task brief (inject this, nothing more)

```
Prove the sorry in this theorem. Follow your agent rules absolutely.

FILE: <real file>  (do NOT edit it)
STATEMENT:
<the exact theorem/lemma/example statement, copied verbatim>

TEMP FILE: <project-root>/_temp_<name>.lean
  - first line: <import line copied from the real file>
  - then: the STATEMENT above, with `:= by sorry` as the body
  - replace the sorry with your proof; iterate until
    lean_diagnostic_messages reports 0 errors

CONTEXT:
- Goal state: <from lean_goal, if provided by main thread>
- Key lemmas you will likely need: <names + one-line signatures, if any>

Report back: STATUS / THEOREM / TEMP_FILE / PROOF_BLOCK / NOTES.
```

## Absolute rules (summary — full text is the agent prompt)

1. Temp file only; never edit the real file. Temp file stays MINIMAL
   (imports + one theorem) so diagnostics stay small.
2. LSP loop: `lean_goal` → edit → `lean_diagnostic_messages` → fix FIRST
   error only → repeat until 0 errors.
3. No signature changes. Only the proof body after `:= by`.
4. `lean_local_search` before using any lemma name. For simple probes
   (`#check`/`#find`/`#eval`) write them in the temp file and read its LSP cache —
   faster than MCP round-trips.
5. **Warning hygiene:** final diagnostics must be 0 errors AND 0 warnings. Fix every
   warning class: docstring/comment issues (verso parser choking on `{...}`/`_`-heavy
   code — rephrase or use `{lit}` roles), `linter.unusedVariables` on unused binders
   (rename to `_`-prefixed, e.g. `_hf` — type-preserving), `linter.unusedSimpArgs` /
   `linter.unnecessarySimpa` (drop the offending arg).
6. Give-up condition: 10 failed attempts on the SAME error → STATUS=fail
   with the exact error and attempts listed. Never loop silently.

## Main-thread recovery

- SUCCESS → paste PROOF_BLOCK into real file → `lean_diagnostic_messages`
  → `git commit`.
- FAIL → read NOTES + temp file state → fix the approach (decompose the
  proof into smaller lemmas IN THE TEMP FILE first, then redispatch one
  subagent per lemma) → fresh subagent. Never resume a dead session.
