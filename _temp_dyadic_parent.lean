import Analysis.MeasureTheory.Section_1_2_2
open Set

lemma DyadicCube.parent_union_children {d : ℕ} (n : ℤ) (a : Fin d → ℤ) :
    (DyadicCube n a).toSet = ⋃ (k : Fin d → ℤ), (if ∀ i, k i = 0 ∨ k i = 1 then (DyadicCube (n+1) (fun i => 2*a i + k i)).toSet else ∅) := by
  ext x
  constructor
  · intro hx
    have hx_mem i : (a i : ℝ) / ((2 : ℝ)^(n : ℤ)) ≤ x i ∧ x i ≤ ((a i : ℝ) + 1) / ((2 : ℝ)^(n : ℤ)) := by
      simpa [DyadicCube, Box.mem_toSet, BoundedInterval.set_Icc] using hx i
    let k : Fin d → ℤ := fun i => if x i ≤ ((2 : ℝ)*(a i : ℝ) + 1) / ((2 : ℝ)^(n+1 : ℤ)) then 0 else 1
    have hk_range i : k i = 0 ∨ k i = 1 := by
      dsimp [k]; split_ifs <;> simp
    refine Set.mem_iUnion.mpr ⟨k, ?_⟩
    split_ifs with hcond
    · simp [DyadicCube, Box.mem_toSet, BoundedInterval.set_Icc]
      intro i
      have hx_low := (hx_mem i).1; have hx_high := (hx_mem i).2
      have h_low : ((2 : ℤ)*a i + k i : ℝ) / ((2 : ℝ)^(n+1 : ℤ)) ≤ x i := by
        dsimp [k]; split_ifs with h
        · -- k i = 0
          calc
            ((2 : ℤ)*a i + 0 : ℝ) / ((2 : ℝ)^(n+1 : ℤ)) = ((2 : ℝ)*(a i : ℝ)) / ((2 : ℝ)^(n+1 : ℤ)) := by push_cast; ring
            _ = (a i : ℝ) / ((2 : ℝ)^(n : ℤ)) := by
              field_simp [show (2 : ℝ)^(n : ℤ) ≠ 0 from by positivity, show (2 : ℝ)^(n+1 : ℤ) ≠ 0 from by positivity]
              ring
            _ ≤ x i := hx_low
        · -- k i = 1
          calc
            ((2 : ℤ)*a i + 1 : ℝ) / ((2 : ℝ)^(n+1 : ℤ)) = ((2 : ℝ)*(a i : ℝ) + 1) / ((2 : ℝ)^(n+1 : ℤ)) := by push_cast; ring
            _ ≤ x i := by
              have : ¬(x i ≤ ((2 : ℝ)*(a i : ℝ) + 1) / ((2 : ℝ)^(n+1 : ℤ))) := h
              linarith
      have h_high : x i ≤ (((2 : ℤ)*a i + k i : ℝ) + 1) / ((2 : ℝ)^(n+1 : ℤ)) := by
        dsimp [k]; split_ifs with h
        · -- k i = 0
          calc
            x i ≤ ((2 : ℝ)*(a i : ℝ) + 1) / ((2 : ℝ)^(n+1 : ℤ)) := h
            _ = (((2 : ℤ)*a i + 0 : ℝ) + 1) / ((2 : ℝ)^(n+1 : ℤ)) := by push_cast; ring
        · -- k i = 1
          calc
            x i ≤ ((a i : ℝ) + 1) / ((2 : ℝ)^(n : ℤ)) := hx_high
            _ = ((2 : ℝ)*(a i : ℝ) + 2) / ((2 : ℝ)^(n+1 : ℤ)) := by
              field_simp [show (2 : ℝ)^(n : ℤ) ≠ 0 from by positivity, show (2 : ℝ)^(n+1 : ℤ) ≠ 0 from by positivity]
              ring
            _ = (((2 : ℤ)*a i + 1 : ℝ) + 1) / ((2 : ℝ)^(n+1 : ℤ)) := by push_cast; ring
      exact ⟨h_low, h_high⟩
    · exact (hcond (fun i => hk_range i)).elim
  · intro hx
    rcases hx with ⟨k, hx'⟩
    split_ifs at hx' with hk_range
    · have hx_mem i : (((2 : ℤ)*a i + k i : ℝ)) / ((2 : ℝ)^(n+1 : ℤ)) ≤ x i ∧
        x i ≤ (((2 : ℤ)*a i + k i : ℝ) + 1) / ((2 : ℝ)^(n+1 : ℤ)) := by
        simpa [DyadicCube, Box.mem_toSet, BoundedInterval.set_Icc] using hx'.1 i
      simp [DyadicCube, Box.mem_toSet, BoundedInterval.set_Icc]
      intro i
      rcases hx_mem i with ⟨hx_low, hx_high⟩
      have h_low : (a i : ℝ) / ((2 : ℝ)^(n : ℤ)) ≤ x i := by
        calc
          (a i : ℝ) / ((2 : ℝ)^(n : ℤ)) = ((2 : ℝ)*(a i : ℝ)) / ((2 : ℝ)^(n+1 : ℤ)) := by
            field_simp [show (2 : ℝ)^(n : ℤ) ≠ 0 from by positivity, show (2 : ℝ)^(n+1 : ℤ) ≠ 0 from by positivity]
            ring
          _ ≤ ((2 : ℤ)*a i + k i : ℝ) / ((2 : ℝ)^(n+1 : ℤ)) := by
            rcases hk_range i with (hk0 | hk1)
            · subst hk0; simp; nlinarith
            · subst hk1; nlinarith
          _ ≤ x i := hx_low
      have h_high : x i ≤ ((a i : ℝ) + 1) / ((2 : ℝ)^(n : ℤ)) := by
        calc
          x i ≤ (((2 : ℤ)*a i + k i : ℝ) + 1) / ((2 : ℝ)^(n+1 : ℤ)) := hx_high
          _ = (((2 : ℤ)*a i : ℝ) + (k i : ℝ) + 1) / ((2 : ℝ)^(n+1 : ℤ)) := by push_cast; ring
          _ ≤ (((2 : ℤ)*a i : ℝ) + 2) / ((2 : ℝ)^(n+1 : ℤ)) := by
            rcases hk_range i with (hk0 | hk1)
            · subst hk0; nlinarith
            · subst hk1; nlinarith
          _ = ((a i : ℝ) + 1) / ((2 : ℝ)^(n : ℤ)) := by
            field_simp [show (2 : ℝ)^(n : ℤ) ≠ 0 from by positivity, show (2 : ℝ)^(n+1 : ℤ) ≠ 0 from by positivity]
            ring
      exact ⟨h_low, h_high⟩
    · exfalso; exact Set.not_mem_empty x hx'
