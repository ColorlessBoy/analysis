import Analysis.MeasureTheory.Section_1_2_2

open Set

lemma finite_TFAE_8_implies_0 {d : ℕ} (E : Set (EuclideanSpace' d))
    (h8 : ∀ ε > 0, ∃ (n : ℤ) (F : Finset (Box d)), (∀ B ∈ F, B.IsDyadicAtScale n) ∧
      Lebesgue_outer_measure (symmDiff (⋃ B ∈ F, B.toSet) E) ≤ ε) :
    LebesgueMeasurable E ∧ Lebesgue_measure E < ⊤ := by
  have hE_meas : LebesgueMeasurable E := by
    have h_approx : ∀ ε > 0, ∃ E' : Set (EuclideanSpace' d), LebesgueMeasurable E' ∧
        Lebesgue_outer_measure (symmDiff E' E) ≤ ε := by
      intro ε hε
      rcases h8 ε hε with ⟨n, F, hF_dyadic, h_symm⟩
      refine ⟨⋃ B ∈ F, B.toSet, ?_, h_symm⟩
      apply LebesgueMeasurable.finset_union
      intro B hB
      rcases hF_dyadic B hB with ⟨a, hB_eq⟩
      subst hB_eq
      exact (IsElementary.box (DyadicCube n a)).measurable
    exact ((LebesgueMeasurable.TFAE E).out 5 0).mp h_approx
  have hE_fin : Lebesgue_measure E < ⊤ := by
    rcases h8 1 (by norm_num : (0 : EReal) < 1) with ⟨n, F, hF_dyadic, h_symm⟩
    have hU_fin : Lebesgue_measure (⋃ B ∈ F, B.toSet) < ⊤ := by
      have h_subadd : Lebesgue_measure (⋃ B ∈ F, B.toSet) ≤ ∑ B ∈ F, Lebesgue_measure (B.toSet) := by
        clear hF_dyadic h_symm
        induction F using Finset.induction_on with
        | empty => simp
        | insert a s ha ih =>
          have h_union : (⋃ B ∈ insert a s, B.toSet) = a.toSet ∪ (⋃ B ∈ s, B.toSet) := by ext x; simp
          rw [h_union, Finset.sum_insert ha]
          have h_pair : Lebesgue_outer_measure (a.toSet ∪ (⋃ B ∈ s, B.toSet)) ≤
              Lebesgue_outer_measure (a.toSet) + Lebesgue_outer_measure (⋃ B ∈ s, B.toSet) := by
            let T : Fin 2 → Set (EuclideanSpace' d) := ![a.toSet, ⋃ B ∈ s, B.toSet]
            have h_union' : a.toSet ∪ (⋃ B ∈ s, B.toSet) = ⋃ i : Fin 2, T i := by ext x; simp [T]
            calc
              Lebesgue_outer_measure (a.toSet ∪ (⋃ B ∈ s, B.toSet)) = Lebesgue_outer_measure (⋃ i : Fin 2, T i) := by rw [h_union']
              _ ≤ ∑ i : Fin 2, Lebesgue_outer_measure (T i) := Lebesgue_outer_measure.finite_union_le T
              _ = Lebesgue_outer_measure (a.toSet) + Lebesgue_outer_measure (⋃ B ∈ s, B.toSet) := by simp [T, Fin.sum_univ_two]
          calc
            Lebesgue_measure (a.toSet ∪ (⋃ B ∈ s, B.toSet)) = Lebesgue_outer_measure (a.toSet ∪ (⋃ B ∈ s, B.toSet)) := rfl
            _ ≤ Lebesgue_outer_measure (a.toSet) + Lebesgue_outer_measure (⋃ B ∈ s, B.toSet) := h_pair
            _ = Lebesgue_measure (a.toSet) + Lebesgue_outer_measure (⋃ B ∈ s, B.toSet) := rfl
            _ = Lebesgue_measure (a.toSet) + Lebesgue_measure (⋃ B ∈ s, B.toSet) := rfl
            _ ≤ Lebesgue_measure (a.toSet) + (∑ B ∈ s, Lebesgue_measure (B.toSet)) := add_le_add_right ih (Lebesgue_measure (a.toSet))
      have h_finset_sum : (∑ B ∈ F, Lebesgue_measure (B.toSet)) < ⊤ := by
        clear hF_dyadic h_symm h_subadd
        induction F using Finset.induction_on with
        | empty => simp
        | insert a s ha ih =>
          rw [Finset.sum_insert ha]
          have ha_fin : Lebesgue_measure (a.toSet) < ⊤ := by
            have hj : JordanMeasurable (a.toSet) :=
              IsElementary.jordanMeasurable (IsElementary.box a)
            rw [Lebesgue_measure, Jordan_measurable.Lebesgue_measure hj]
            simp
          have hs_fin : (∑ B ∈ s, Lebesgue_measure (B.toSet)) < ⊤ := ih
          exact EReal.add_lt_top (ne_of_lt ha_fin) (ne_of_lt hs_fin)
      exact lt_of_le_of_lt h_subadd h_finset_sum
    have h_E_le_U : Lebesgue_outer_measure E ≤ Lebesgue_measure (⋃ B ∈ F, B.toSet) + 1 := by
      have h_sub : E ⊆ (⋃ B ∈ F, B.toSet) ∪ (symmDiff (⋃ B ∈ F, B.toSet) E) := by
        intro x hx
        by_cases hxU : x ∈ ⋃ B ∈ F, B.toSet
        · exact Set.mem_union_left _ hxU
        · have hx_symm : x ∈ symmDiff (⋃ B ∈ F, B.toSet) E := by
            rw [symmDiff_def]; exact Or.inr ⟨hx, hxU⟩
          exact Set.mem_union_right _ hx_symm
      have h_subadd : Lebesgue_outer_measure ((⋃ B ∈ F, B.toSet) ∪ (symmDiff (⋃ B ∈ F, B.toSet) E)) ≤
          Lebesgue_measure (⋃ B ∈ F, B.toSet) + Lebesgue_outer_measure (symmDiff (⋃ B ∈ F, B.toSet) E) := by
        let S' : Fin 2 → Set (EuclideanSpace' d) := ![⋃ B ∈ F, B.toSet, symmDiff (⋃ B ∈ F, B.toSet) E]
        have h_union : (⋃ B ∈ F, B.toSet) ∪ (symmDiff (⋃ B ∈ F, B.toSet) E) = ⋃ i : Fin 2, S' i := by
          ext x; simp [S']
        calc
          Lebesgue_outer_measure ((⋃ B ∈ F, B.toSet) ∪ (symmDiff (⋃ B ∈ F, B.toSet) E)) =
            Lebesgue_outer_measure (⋃ i : Fin 2, S' i) := by rw [h_union]
          _ ≤ ∑ i : Fin 2, Lebesgue_outer_measure (S' i) := Lebesgue_outer_measure.finite_union_le S'
          _ = Lebesgue_measure (⋃ B ∈ F, B.toSet) + Lebesgue_outer_measure (symmDiff (⋃ B ∈ F, B.toSet) E) := by
            simp [S', Fin.sum_univ_two, Lebesgue_measure]
      calc
        Lebesgue_outer_measure E ≤ Lebesgue_outer_measure ((⋃ B ∈ F, B.toSet) ∪ (symmDiff (⋃ B ∈ F, B.toSet) E)) :=
          Lebesgue_outer_measure.mono h_sub
        _ ≤ Lebesgue_measure (⋃ B ∈ F, B.toSet) + Lebesgue_outer_measure (symmDiff (⋃ B ∈ F, B.toSet) E) := h_subadd
        _ ≤ Lebesgue_measure (⋃ B ∈ F, B.toSet) + 1 := add_le_add_right h_symm _
    have h_E_lt_top : Lebesgue_measure E < ⊤ := by
      calc
        Lebesgue_measure E = Lebesgue_outer_measure E := rfl
        _ ≤ Lebesgue_measure (⋃ B ∈ F, B.toSet) + 1 := h_E_le_U
        _ < ⊤ := by
          refine EReal.add_lt_top (ne_of_lt hU_fin) ?_
          exact EReal.coe_ne_top (1 : ℝ)
    exact h_E_lt_top
  exact ⟨hE_meas, hE_fin⟩
