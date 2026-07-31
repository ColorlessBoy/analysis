import Analysis.MeasureTheory.Section_1_2_2
open Set

lemma interval_split_one_dim (a n : ℤ) (x : ℝ) : 
    ((a : ℝ) / ((2 : ℝ)^(n : ℤ)) ≤ x ∧ x ≤ ((a : ℝ) + 1) / ((2 : ℝ)^(n : ℤ))) ↔
    (((2*a : ℤ) : ℝ) / ((2 : ℝ)^(n+1 : ℤ)) ≤ x ∧ x ≤ (((2*a : ℤ) + 1 : ℤ) : ℝ) / ((2 : ℝ)^(n+1 : ℤ))) ∨
    ((((2*a : ℤ) + 1 : ℤ) : ℝ) / ((2 : ℝ)^(n+1 : ℤ)) ≤ x ∧ x ≤ (((2*a : ℤ) + 2 : ℤ) : ℝ) / ((2 : ℝ)^(n+1 : ℤ))) := by
  constructor
  · rintro ⟨h_low, h_high⟩
    by_cases h : x ≤ ((2 : ℝ)*(a : ℝ) + 1) / ((2 : ℝ)^(n+1 : ℤ))
    · left; constructor
      · calc
          ((2*a : ℤ) : ℝ) / ((2 : ℝ)^(n+1 : ℤ)) = ((2 : ℝ)*(a : ℝ)) / ((2 : ℝ)^(n+1 : ℤ)) := by push_cast; ring
          _ = (a : ℝ) / ((2 : ℝ)^(n : ℤ)) := by
            field_simp [show (2 : ℝ)^(n : ℤ) ≠ 0 from by positivity, show (2 : ℝ)^(n+1 : ℤ) ≠ 0 from by positivity]
            ring
          _ ≤ x := h_low
      · exact h
    · right; constructor
      · have : ¬(x ≤ ((2 : ℝ)*(a : ℝ) + 1) / ((2 : ℝ)^(n+1 : ℤ))) := h
        nlinarith
      · calc
          x ≤ ((a : ℝ) + 1) / ((2 : ℝ)^(n : ℤ)) := h_high
          _ = ((2*a : ℤ) + 2 : ℤ : ℝ) / ((2 : ℝ)^(n+1 : ℤ)) := by
            push_cast
            field_simp [show (2 : ℝ)^(n : ℤ) ≠ 0 from by positivity, show (2 : ℝ)^(n+1 : ℤ) ≠ 0 from by positivity]
            ring
  · intro h
    rcases h with (⟨h_low, h_high⟩ | ⟨h_low, h_high⟩)
    · constructor
      · calc
          (a : ℝ) / ((2 : ℝ)^(n : ℤ)) = ((2 : ℝ)*(a : ℝ)) / ((2 : ℝ)^(n+1 : ℤ)) := by
            field_simp [show (2 : ℝ)^(n : ℤ) ≠ 0 from by positivity, show (2 : ℝ)^(n+1 : ℤ) ≠ 0 from by positivity]
            ring
          _ = ((2*a : ℤ) : ℝ) / ((2 : ℝ)^(n+1 : ℤ)) := by push_cast; ring
          _ ≤ x := h_low
      · calc
          x ≤ (((2*a : ℤ) + 1 : ℤ) : ℝ) / ((2 : ℝ)^(n+1 : ℤ)) := h_high
          _ = ((2 : ℝ)*(a : ℝ) + 1) / ((2 : ℝ)^(n+1 : ℤ)) := by push_cast; ring
          _ ≤ ((a : ℝ) + 1) / ((2 : ℝ)^(n : ℤ)) := by
            field_simp [show (2 : ℝ)^(n : ℤ) ≠ 0 from by positivity, show (2 : ℝ)^(n+1 : ℤ) ≠ 0 from by positivity]
            nlinarith
    · constructor
      · calc
          (a : ℝ) / ((2 : ℝ)^(n : ℤ)) = ((2 : ℝ)*(a : ℝ)) / ((2 : ℝ)^(n+1 : ℤ)) := by
            field_simp [show (2 : ℝ)^(n : ℤ) ≠ 0 from by positivity, show (2 : ℝ)^(n+1 : ℤ) ≠ 0 from by positivity]
            ring
          _ = (((2*a : ℤ) : ℝ)) / ((2 : ℝ)^(n+1 : ℤ)) := by push_cast; ring
          _ ≤ (((2*a : ℤ) + 1 : ℤ) : ℝ) / ((2 : ℝ)^(n+1 : ℤ)) := by
            refine (div_le_div_right (by positivity)).mpr ?_
            push_cast; nlinarith
          _ ≤ x := h_low
      · calc
          x ≤ (((2*a : ℤ) + 2 : ℤ) : ℝ) / ((2 : ℝ)^(n+1 : ℤ)) := h_high
          _ = ((a : ℝ) + 1) / ((2 : ℝ)^(n : ℤ)) := by
            push_cast
            field_simp [show (2 : ℝ)^(n : ℤ) ≠ 0 from by positivity, show (2 : ℝ)^(n+1 : ℤ) ≠ 0 from by positivity]
            ring
