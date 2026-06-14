# Section 5.5 Shared Knowledge

## Project-Specific Tactic Patterns

### 1. `observe` tactic (from Mathlib.Tactic)
`observe` is like `have` but auto-proves simple goals from context. Use for trivial facts:
```lean
observe hx₀ : x₀ ∈ E           -- when x₀ := hE.some, automatically uses hE.some_mem
observe claim2': E.Nonempty    -- automatically uses claim2
```

### 2. `positivity` limitations
`positivity` does NOT handle `min` expressions. For `min a b` where `a > 0` and `b > 0`:
```lean
-- DON'T: have hε : 0 < ε := by positivity  (fails for min)
-- DO:    have hε : 0 < ε := lt_min_iff.mpr ⟨by norm_num, by nlinarith⟩
```

### 3. `linarith` vs `nlinarith` on Real
- `linarith` works on `Real` for linear arithmetic
- `nlinarith` works on `Real` for nonlinear (polynomial up to degree 2)
- For min constraints, `linarith` can't see the bounds without explicit `h := min_le_left _ _` / `h := min_le_right _ _`
- Pattern for min:
```lean
set ε := min (1/2) ((x^2-2)/8)
have hε1 : ε ≤ 1/2 := min_le_left _ _
have hε2 : ε ≤ (x^2-2)/8 := min_le_right _ _
```

### 4. `isPos_iff` ↔ `>0` conversion
```lean
Real.isPos_iff x  -- x.IsPos ↔ x > 0
Real.isNeg_iff x  -- x.IsNeg ↔ x < 0
```
Usage:
```lean
have hpos : ε.IsPos := by rw [isPos_iff]; positivity
-- Or when ε is a cast rational:
have hpos : ε.IsPos := by
  dsimp [ε]
  rw [isPos_iff]
  positivity
```

### 5. `grind` for Set membership and simple logical goals
`grind` handles `upperBounds`, `upperBound_def`, `isLUB_def` etc. well:
```lean
grind [upperBound_def]
grind [isLUB_def, upperBound_def]
grind [upperBound_upper]
```

### 6. `∃!` pattern with `existsUnique_of_exists_of_unique`
```lean
apply existsUnique_of_exists_of_unique
· -- existence proof
· -- uniqueness proof (use grind)
```

### 7. Rational arithmetic: `ring` over `field_simp` when possible
```lean
-- For (m/(n+1):ℚ) = m*(1/(n+1)):
-- DON'T: field_simp  (can be overkill)
-- DO: ring
```

### 8. `qify` for ℤ ↔ ℚ × Real conversions
```lean
qify; rwa [←gt_iff_lt, gt_of_coe]
```

### 9. `∃!` choose_spec decomposition
For `h : ∃! m, P m`:
```lean
have hexists : ∃ m, P m := h.exists
choose m hm using hexists          -- gives m and hm : P m
-- or:
have hm : P ((h.exists).choose) := (h.exists).choose_spec
```

### 10. `Set.Icc`, `upperBounds` API
```lean
mem_upperBounds : M ∈ upperBounds E ↔ ∀ x ∈ E, x ≤ M
mem_lowerBounds : M ∈ lowerBounds E ↔ ∀ x ∈ E, x ≥ M
```

## Common Proof Strategies

### A. Bounding via `∃ N:ℕ, ...`
Archimedean property via `Real.le_mul`:
```lean
Real.le_mul {ε:Real} (hε: ε.IsPos) (x:Real) : ∃ M:ℕ, M > 0 ∧ M * ε > x
```

### B. Rational bounds via `Real.rat_between`
```lean
Real.rat_between {x y:Real} (hxy: x < y) : ∃ q:ℚ, x < (q:Real) ∧ (q:Real) < y
```

### C. `LIM_of_ge` and `LIM_of_le'` for sequence limits
```lean
Real.LIM_of_ge {x:Real} {a:ℕ → ℚ} (hcauchy: (a:Sequence).IsCauchy) (h: ∀ n, a n ≥ x) : LIM a ≥ x
Real.LIM_of_le' {x:Real} {a:ℕ → ℚ} (hcauchy: (a:Sequence).IsCauchy) (h: ∃ N, ∀ n ≥ N, a n ≤ x) : LIM a ≤ x
```

### D. `LIM_sub` and `LIM_add` for arithmetic
```lean
Real.LIM_sub (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) : LIM (a - b) = LIM a - LIM b
Real.LIM_add (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) : LIM (a + b) = LIM a + LIM b
```

### E. `Sequence.IsCauchy` combinators
```lean
Sequence.IsCauchy.harmonic' : (fun n ↦ 1 / (n+1) : Sequence).IsCauchy
Sequence.IsCauchy.const q   : (fun _ ↦ q : Sequence).IsCauchy
Sequence.IsCauchy.sub ha hb  : (a - b : Sequence).IsCauchy
Sequence.IsCauchy.add ha hb  : (a + b : Sequence).IsCauchy
```

### F. `|a n - a n'| ≤ 1/(N+1)` pattern
Prove by splitting into two inequalities via `abs_le`:
```lean
rw [abs_le]
split_ands
...
```

### G. `calc` for arithmetic identities
```lean
calc
  _ = x^2 - 2 * ε * x + ε * ε := by ring
  _ ≥ x^2 - 2 * ε * 2 + 0 * 0 := by gcongr
  _ = x^2 - 4 * ε := by ring
  _ > 2 := hε3
```

### H. `gcongr` for inequality composition
`gcongr` is the "generalized congruence" tactic — great for chaining inequalities with multiplication by constants.

## Environment
- `Real` is defined via formal limits of Cauchy sequences of rationals
- `ExtendedReal` has constructors: `neg_infty | real x | infty`
- `sup E` and `inf E` are defined using `ExtendedReal`
- `upperBounds`, `lowerBounds`, `IsLUB`, `IsGLB` are Mathlib concepts
