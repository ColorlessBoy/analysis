# Lean Problem Solving Skill

## Core Workflow

When solving Lean problems (filling `sorry`s), follow this strict process:

### 1. Assessment Phase
- Scan all `*.lean` files to identify which have `sorry`s
- Count sorries per file and list them
- Check for pre-existing errors/warnings in each file before making changes
- Note any imports already present (do NOT add new imports unless absolutely necessary)

### 2. Granularity
- Each **individual theorem/example** that contains `sorry` is one unit of work
- Do NOT batch entire files — work at theorem granularity to avoid context overflow
- Exception: multiple trivial `example`s that are clearly the same pattern can be batched

### 3. Execution: Subagent per Theorem — Solve → Verify

For EACH theorem containing `sorry`, use TWO subagents sequentially (NO parallelization):

#### Step A: Launch solving subagent
```lean
task(description="Solve <theorem_name>", prompt="""... detailed instructions ...""")
```
The solving subagent must:
- Read the theorem statement and inspect the goal with `lean_goal`
- Search for relevant lemmas (`lean_local_search`, `lean_loogle`, `lean_leansearch`)
- Write a proof replacing `sorry`
- Verify with `lake env lean <file>.lean 2>&1 | grep -E "error:|warning:|info:"`
- Return the verification output

#### Step B: Launch verification subagent
```lean
task(description="Verify <theorem_name>", prompt="""... verify the solution ...""")
```
The verification subagent must:
- Run `lake env lean <file>.lean 2>&1 | grep -E "error:|warning:"` and confirm ZERO output
- Check the specific theorem is no longer listed as a `sorry`
- If ANY issues found, report them (do NOT fix — let the solve step retry)

#### Step C: Fix ALL diagnostic messages
If the solve+verify cycle produces ANY of the following, fix them before moving on:
- **errors**: compilation failures (MUST fix)
- **warnings**: unused variables, unnecessary `simpa` (MUST fix)
- **suggestions**: `ring` → `ring_nf`, `simpa` → `simp` (MUST fix)

Wait for verification to pass completely before advancing to the next theorem.

### 4. No Parallelization

- Process theorems **one at a time** — do NOT launch multiple subagents concurrently
- Complete the full solve→verify cycle for theorem N before touching theorem N+1
- This prevents context mixing and ensures each proof is independently validated

### 5. What NOT to do
- Do NOT add `import` statements unless the file explicitly needs them
- Do NOT change theorem signatures, type statements, or docstrings
- Do NOT use `admit` or `axiom` instead of `sorry`
- Do NOT batch multiple unrelated proofs without verification between them
- Do NOT ignore warnings ("it's just a warning")
- Do NOT use `simpa` when `simp` suffices (creates unnecessary linter warnings)

### 6. Common Pitfalls

| Pitfall | Solution |
|---------|----------|
| Wrong lemma name | Check with `lean_run_code` first |
| `simp` can't close a goal | Use `simp; linarith` or `nlinarith` |
| `.Ioo` ambiguous | Use `Set.Ioo` explicitly |
| `Set.mem_image.mpr` not found | Use `Set.mem_image_of_mem` or `(Set.mem_image _ _ _).mpr` |
| `Set.not_mem_empty` not found | Use `simp` instead |
| `ring` fails inside `|·|` | Factor out the inner expression with `have hcalc : ... := by ring` |
| Typeclass instance missing | Use `positivity` for positivity proofs, `norm_num` for numeric |
| `rcases` can't destruct `Set.mem` | Use `simp at hy` first to expand set membership |
| Unused binder `h` | Rename to `_` |

### 7. File Cleanup Checklist

Before declaring a file done:
- [ ] Zero errors
- [ ] Zero warnings (unused variables, unnecessary simpa, etc.)
- [ ] Zero unexpected info messages
- [ ] Zero sorries
- [ ] Full `lake build` passes for the file

### 8. Multiple Files Strategy

Process files sequentially. For each file:
1. Read the entire file first to understand the dependency structure
2. Start with theorems that have no dependencies on other `sorry`s in the file
3. Work forward through the file
4. Use already-proved theorems in later proofs

The complete output of `lake env lean <file>.lean` should contain ONLY type-info outputs from intentional `#check` commands, and nothing else.
