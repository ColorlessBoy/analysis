import Analysis.MeasureTheory.Section_1_2_2
open Set

lemma DyadicCube.parent_union_children {d : ℕ} (n : ℕ) (a : Fin d → ℤ) :
    (DyadicCube (n : ℤ) a).toSet = ⋃ (k : Fin d → ℤ), (if ∀ i, k i = 0 ∨ k i = 1 then
      (DyadicCube (n+1 : ℤ) (fun i => 2*a i + k i)).toSet else ∅) := by
  ext x; constructor
  · intro hx
    -- x is in parent cube
    have hx_mem i : (a i : ℝ) / ((2 : ℝ)^(n : ℕ)) ≤ x i ∧ x i ≤ ((a i : ℝ) + 1) / ((2 : ℝ)^(n : ℕ)) := by
      simpa [DyadicCube, Box.mem_toSet, BoundedInterval.set_Icc, map_pow] using hx i
    -- choose k_i = 0 if x_i ≤ midpoint, 1 otherwise
    let k : Fin d → ℤ := fun i => if x i ≤ (((a i : ℝ) + (a i : ℝ) + 1) / ((2 : ℝ)^(n+1 : ℕ))) then 0 else 1
    have hk_range i : k i = 0 ∨ k i = 1 := by
      dsimp [k]; split_ifs <;> simp
    refine Set.mem_iUnion.mpr ⟨k, ?_⟩
    split_ifs
    · -- show x ∈ DyadicCube (n+1) (2a + k)
      simp [DyadicCube, Box.mem_toSet, BoundedInterval.set_Icc, map_pow]
      intro i
      rcases hx_mem i with ⟨hx_l, hx_r⟩
      dsimp [k]; split_ifs with h
      · -- k i = 0 case
        have h_low : ((2*a i + 0 : ℤ) : ℝ) / ((2 : ℝ)^(n+1 : ℕ)) ≤ x i := by
          calc
            ((2*a i + 0 : ℤ) : ℝ) / ((2 : ℝ)^(n+1 : ℕ)) = ((a i : ℝ) * 2) / ((2 : ℝ)^(n+1 : ℕ)) := by push_cast; ring
            _ = (a i : ℝ) / ((2 : ℝ)^(n : ℕ)) := by field_simp; ring
            _ ≤ x i := hx_l
        have h_high : x i ≤ (((2*a i + 0 : ℤ) : ℝ) + 1) / ((2 : ℝ)^(n+1 : ℕ)) := by
          calc
            x i ≤ ((a i : ℝ) + 1) / ((2 : ℝ)^(n : ℕ)) := hx_r
            _ = ((a i : ℝ) + 1) * 2 / ((2 : ℝ)^(n+1 : ℕ)) := by field_simp; ring
            _ = (((2*a i + 0 : ℤ) : ℝ) + 1) / ((2 : ℝ)^(n+1 : ℕ)) := by push_cast; ring
        exact ⟨h_low, h_high⟩
      · -- k i = 1 case
        have h_low : ((2*a i + 1 : ℤ) : ℝ) / ((2 : ℝ)^(n+1 : ℕ)) ≤ x i := by
          have h_not : ¬(x i ≤ (((a i : ℝ) + (a i : ℝ) + 1) / ((2 : ℝ)^(n+1 : ℕ)))) := h
          have h_mid : ((a i : ℝ) + (a i : ℝ) + 1) / ((2 : ℝ)^(n+1 : ℕ)) = ((2*a i + 1 : ℤ) : ℝ) / ((2 : ℝ)^(n+1 : ℕ)) := by
            push_cast; ring
          rw [h_mid] at h_not
          linarith
        have h_high : x i ≤ (((2*a i + 1 : ℤ) : ℝ) + 1) / ((2 : ℝ)^(n+1 : ℕ)) := by
          calc
            x i ≤ ((a i : ℝ) + 1) / ((2 : ℝ)^(n : ℕ)) := hx_r
            _ = ((a i : ℝ) + 1) * 2 / ((2 : ℝ)^(n+1 : ℕ)) := by field_simp; ring
            _ = (((2*a i + 1 : ℤ) : ℝ) + 1) / ((2 : ℝ)^(n+1 : ℕ)) := by push_cast; ring
        exact ⟨h_low, h_high⟩
    · exact (hk_range (fun i => False.elim ?_)).elim
  · intro hx
    rcases hx with ⟨k, hx'⟩
    split_ifs at hx' with hk_range
    · -- x ∈ DyadicCube (n+1) (2a + k) for some k with k_i ∈ {0,1}
      have hx_mem' i : (((2*a i + k i : ℤ) : ℝ) / ((2 : ℝ)^(n+1 : ℕ)) ≤ x i ∧
          x i ≤ (((2*a i + k i : ℤ) : ℝ) + 1) / ((2 : ℝ)^(n+1 : ℕ))) := by
        simpa [DyadicCube, Box.mem_toSet, BoundedInterval.set_Icc, map_pow] using hx'.1 i
      simp [DyadicCube, Box.mem_toSet, BoundedInterval.set_Icc, map_pow]
      intro i
      rcases hx_mem' i with ⟨hx_l, hx_r⟩
      have h_low : (a i : ℝ) / ((2 : ℝ)^(n : ℕ)) ≤ x i := by
        calc
          (a i : ℝ) / ((2 : ℝ)^(n : ℕ)) = (((2*a i : ℤ) : ℝ) + 0) / ((2 : ℝ)^(n+1 : ℕ)) := by
            push_cast; field_simp; ring
          _ ≤ ((2*a i + k i : ℤ) : ℝ) / ((2 : ℝ)^(n+1 : ℕ)) := by
            rcases hk_range i with (hk0 | hk1)
            · subst hk0; rfl
            · subst hk1; push_cast; nlinarith
          _ ≤ x i := hx_l
      have h_high : x i ≤ ((a i : ℝ) + 1) / ((2 : ℝ)^(n : ℕ)) := by
        calc
          x i ≤ (((2*a i + k i : ℤ) : ℝ) + 1) / ((2 : ℝ)^(n+1 : ℕ)) := hx_r
          _ ≤ (((2*a i + 2 : ℤ) : ℝ) + 0) / ((2 : ℝ)^(n+1 : ℕ)) := by
            rcases hk_range i with (hk0 | hk1)
            · subst hk0; push_cast; nlinarith
            · subst hk1; push_cast; nlinarith
          _ = ((a i : ℝ) + 1) / ((2 : ℝ)^(n : ℕ)) := by
            push_cast; field_simp; ring
      exact ⟨h_low, h_high⟩
    · exfalso; exact Set.not_mem_empty x hx'
