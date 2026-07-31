import Analysis.MeasureTheory.Section_1_2_2
open Set

lemma interval_halving (l r x : ℝ) (h : l ≤ x ∧ x ≤ r) : (l ≤ x ∧ x ≤ (l + r)/2) ∨ ((l + r)/2 ≤ x ∧ x ≤ r) := by
  rcases h with ⟨hx_l, hx_r⟩
  by_cases hx_mid : x ≤ (l + r)/2
  · left; exact ⟨hx_l, hx_mid⟩
  · right; exact ⟨by linarith, hx_r⟩

lemma DyadicCube.parent_union_children {d : ℕ} (n : ℤ) (a : Fin d → ℤ) :
    (DyadicCube n a).toSet = ⋃ (k : Fin d → ℤ), 
    (if ∀ i, k i = 0 ∨ k i = 1 then (DyadicCube (n+1 : ℤ) (fun i => 2*a i + k i)).toSet else ∅) := by
  ext x; constructor
  · intro hx
    have hx_mem i : (a i : ℝ) / ((2 : ℝ)^(n : ℤ)) ≤ x i ∧ x i ≤ ((a i : ℝ) + 1) / ((2 : ℝ)^(n : ℤ)) := by
      simpa [DyadicCube, Box.mem_toSet, BoundedInterval.set_Icc] using hx i
    let k : Fin d → ℤ := fun i => 
      if x i ≤ ((a i : ℝ) + (a i : ℝ) + 1) / (2 * ((2 : ℝ)^(n : ℤ))) then 0 else 1
    have hk_range i : k i = 0 ∨ k i = 1 := by
      dsimp [k]; split_ifs <;> simp
    refine Set.mem_iUnion.mpr ⟨k, ?_⟩
    split_ifs
    · simp [DyadicCube, Box.mem_toSet, BoundedInterval.set_Icc]
      intro i
      rcases hx_mem i with ⟨hx_l, hx_r⟩
      dsimp [k]; split_ifs with h
      · -- k i = 0
        have h_low : ((2*a i + 0 : ℤ) : ℝ) / ((2 : ℝ)^(n+1 : ℤ)) ≤ x i := by
          calc
            ((2*a i + 0 : ℤ) : ℝ) / ((2 : ℝ)^(n+1 : ℤ)) = ((a i : ℝ) * 2) / ((2 : ℝ)^(n : ℤ) * 2) := by
              push_cast; ring
            _ = (a i : ℝ) / ((2 : ℝ)^(n : ℤ)) := by field_simp; ring
            _ ≤ x i := hx_l
        have h_high : x i ≤ (((2*a i + 0 : ℤ) : ℝ) + 1) / ((2 : ℝ)^(n+1 : ℤ)) := by
          calc
            x i ≤ ((a i : ℝ) + 1) / ((2 : ℝ)^(n : ℤ)) := hx_r
            _ = ((a i : ℝ) + 1) * 2 / ((2 : ℝ)^(n : ℤ) * 2) := by ring
            _ = ((a i : ℝ) * 2 + 2) / ((2 : ℝ)^(n+1 : ℤ)) := by
              push_cast; ring
            _ = (((2*a i + 0 : ℤ) : ℝ) + 1) / ((2 : ℝ)^(n+1 : ℤ)) := by push_cast; ring
        exact ⟨h_low, h_high⟩
      · -- k i = 1
        have h_low : ((2*a i + 1 : ℤ) : ℝ) / ((2 : ℝ)^(n+1 : ℤ)) ≤ x i := by
          have h_not : ¬(x i ≤ ((a i : ℝ) + (a i : ℝ) + 1) / (2 * ((2 : ℝ)^(n : ℤ)))) := h
          calc
            ((2*a i + 1 : ℤ) : ℝ) / ((2 : ℝ)^(n+1 : ℤ)) = ((a i : ℝ) * 2 + 1) / ((2 : ℝ)^(n : ℤ) * 2) := by
              push_cast; ring
            _ = (((a i : ℝ) + (a i : ℝ) + 1) / ((2 : ℝ)^(n : ℤ) * 2)) := by ring
            _ ≤ x i := by
              have : (2 : ℝ)^(n+1 : ℤ) = ((2 : ℝ)^(n : ℤ) * 2) := by
                simp [pow_succ]
              nlinarith
        have h_high : x i ≤ (((2*a i + 1 : ℤ) : ℝ) + 1) / ((2 : ℝ)^(n+1 : ℤ)) := by
          calc
            x i ≤ ((a i : ℝ) + 1) / ((2 : ℝ)^(n : ℤ)) := hx_r
            _ = ((a i : ℝ) + 1) * 2 / ((2 : ℝ)^(n : ℤ) * 2) := by ring
            _ = ((a i : ℝ) * 2 + 2) / ((2 : ℝ)^(n+1 : ℤ)) := by
              push_cast; ring
            _ = (((2*a i + 1 : ℤ) : ℝ) + 1) / ((2 : ℝ)^(n+1 : ℤ)) := by push_cast; ring
        exact ⟨h_low, h_high⟩
    · exact (hk_range (fun i => False.elim ?_)).elim
  · intro hx
    rcases hx with ⟨k, hx'⟩
    split_ifs at hx' with hk_range
    · have hx_mem' i : ((2*a i + k i : ℤ) : ℝ) / ((2 : ℝ)^(n+1 : ℤ)) ≤ x i ∧
        x i ≤ (((2*a i + k i : ℤ) : ℝ) + 1) / ((2 : ℝ)^(n+1 : ℤ)) := by
        simpa [DyadicCube, Box.mem_toSet, BoundedInterval.set_Icc] using hx'.1 i
      simp [DyadicCube, Box.mem_toSet, BoundedInterval.set_Icc]
      intro i
      rcases hx_mem' i with ⟨hx_l, hx_r⟩
      have h_low : (a i : ℝ) / ((2 : ℝ)^(n : ℤ)) ≤ x i := by
        calc
          (a i : ℝ) / ((2 : ℝ)^(n : ℤ)) = ((2*a i + 0 : ℤ) : ℝ) / ((2 : ℝ)^(n+1 : ℤ)) := by
            push_cast; field_simp; ring
          _ ≤ ((2*a i + k i : ℤ) : ℝ) / ((2 : ℝ)^(n+1 : ℤ)) := by
            rcases hk_range i with (hk0 | hk1)
            · subst hk0; rfl
            · subst hk1; push_cast; nlinarith
          _ ≤ x i := hx_l
      have h_high : x i ≤ ((a i : ℝ) + 1) / ((2 : ℝ)^(n : ℤ)) := by
        calc
          x i ≤ (((2*a i + k i : ℤ) : ℝ) + 1) / ((2 : ℝ)^(n+1 : ℤ)) := hx_r
          _ = ((2*a i + k i : ℤ) : ℝ + 1) / ((2 : ℝ)^(n+1 : ℤ)) := rfl
          _ ≤ ((2*a i + 2 : ℤ) : ℝ) / ((2 : ℝ)^(n+1 : ℤ)) := by
            rcases hk_range i with (hk0 | hk1)
            · subst hk0; push_cast; nlinarith
            · subst hk1; push_cast; nlinarith
          _ = ((a i : ℝ) + 1) / ((2 : ℝ)^(n : ℤ)) := by
            push_cast; field_simp; ring
      exact ⟨h_low, h_high⟩
    · exfalso; exact Set.not_mem_empty x hx'
