import Analysis.MeasureTheory.Section_1_2_2

open Set

example : ¬ ∃ (I : ℕ → BoundedInterval), (∀ n, IsClosed (I n).toSet) ∧ (Set.univ.PairwiseDisjoint (fun n ↦ (I n).toSet)) ∧ (⋃ n, (I n).toSet = Set.Ico (0 : ℝ) 1) := by
  intro h
  rcases h with ⟨I, h_closed, h_disj, h_union⟩
  -- If non-empty, I(n) = Icc a b
  have h_nonempty_is_Icc : ∀ n, (I n : Set ℝ) ≠ ∅ → ∃ a b, I n = Icc a b := by
    intro n hn
    rcases closed_eq_Icc_or_empty (h_closed n) with (h | h)
    · exact h
    · exact absurd h hn
  -- At most one I(n) is non-empty
  by_cases h_all_empty : ∀ n, (I n : Set ℝ) = ∅
  · -- All empty → union is empty, contradict h_union
    have h_union_empty : ⋃ n, (I n : Set ℝ) = ∅ := by
      simp [h_all_empty]
    rw [h_union_empty] at h_union
    have : Set.Ico (0 : ℝ) 1 ≠ ∅ := by
      refine Set.ne_empty_of_mem ?_
      exact ⟨by norm_num, by norm_num⟩
    exact this h_union
  · -- Some I(k) is non-empty
    push_neg at h_all_empty
    rcases h_all_empty with ⟨k, hk⟩
    rcases h_nonempty_is_Icc k hk with ⟨a, b, hk_eq⟩
    have hk_nonempty : (I k : Set ℝ) ≠ ∅ := hk
    have ha_le_b : a ≤ b := by
      by_contra! hlt
      have : (Icc a b : Set ℝ) = ∅ := by
        simp [Set.Icc_eq_empty_iff.mpr (by linarith)]
      rw [hk_eq, this] at hk
      exact hk rfl
    have h_sub : (I k : Set ℝ) ⊆ Set.Ico (0 : ℝ) 1 := by
      rw [hk_eq, BoundedInterval.coe_Icc]
      intro x ⟨hx1, hx2⟩
      have : x ∈ ⋃ n, (I n : Set ℝ) := by
        apply Set.mem_iUnion.mpr ⟨k, ?_⟩
        rw [hk_eq, BoundedInterval.coe_Icc]
        exact ⟨hx1, hx2⟩
      rw [h_union] at this
      exact this
    rcases h_sub ⟨ha_le_b, le_refl b⟩ with ⟨h_zero_le_b, hb_lt_one⟩
    -- Show that there is some x ∈ Ico 0 1 not covered by any I(n)
    sorry
