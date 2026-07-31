import Analysis.MeasureTheory.Section_1_2_2

open Set

lemma finite_TFAE_0_implies_1 {d : ℕ} (E : Set (EuclideanSpace' d))
    (h0 : LebesgueMeasurable E ∧ Lebesgue_measure E < ⊤) :
    ∀ ε > 0, ∃ U : Set (EuclideanSpace' d), IsOpen U ∧ E ⊆ U ∧ Lebesgue_measure U < ⊤ ∧ Lebesgue_outer_measure (U \ E) ≤ ε := by
  rcases h0 with ⟨hE_meas, hE_fin⟩
  intro ε hε
  by_cases hε_top : ε = ⊤
  · subst hε_top
    rcases hE_meas 1 (by norm_num : (0 : EReal) < 1) with ⟨V, hV_open, hE_sub_V, hV_diff⟩
    have h_one_pos : (0 : EReal) < 1 := by norm_num
    rcases Lebesgue_outer_measure.exists_open_superset_measure_le E 1 h_one_pos with ⟨W, hW_open, hE_sub_W, hW_le⟩
    have hW_fin : Lebesgue_measure W < ⊤ := by
      have : Lebesgue_outer_measure E < ⊤ := hE_fin
      have : Lebesgue_outer_measure E + (1 : EReal) < ⊤ := by
        have h_add : (Lebesgue_outer_measure E : EReal) + (1 : EReal) < ⊤ :=
          EReal.add_lt_top (ne_of_lt this) (EReal.coe_ne_top (1 : ℝ))
        exact h_add
      have hW_le' : Lebesgue_outer_measure W ≤ Lebesgue_outer_measure E + (1 : EReal) := hW_le
      exact lt_of_le_of_lt hW_le' this
    let U := V ∩ W
    have hU_open : IsOpen U := IsOpen.inter hV_open hW_open
    have hE_sub_U : E ⊆ U := by
      intro x hx; exact ⟨hE_sub_V hx, hE_sub_W hx⟩
    have hU_fin : Lebesgue_measure U < ⊤ := by
      have h_sub : U ⊆ W := Set.inter_subset_right
      have h_mono : Lebesgue_outer_measure U ≤ Lebesgue_outer_measure W := Lebesgue_outer_measure.mono h_sub
      exact lt_of_le_of_lt h_mono hW_fin
    have hU_diff : Lebesgue_outer_measure (U \ E) ≤ ⊤ := le_top
    exact ⟨U, hU_open, hE_sub_U, hU_fin, hU_diff⟩
  · -- ε is not ⊤, so it's either ⊥ (impossible since ε > 0) or coe r
    have hε_fin : ε ≠ ⊤ := hε_top
    have h_pos : 0 < ε := hε
    rcases hE_meas ε h_pos with ⟨V, hV_open, hE_sub_V, hV_diff⟩
    rcases Lebesgue_outer_measure.exists_open_superset_measure_le E ε h_pos with ⟨W, hW_open, hE_sub_W, hW_le⟩
    have hW_fin : Lebesgue_measure W < ⊤ := by
      have : Lebesgue_outer_measure E < ⊤ := hE_fin
      have h_add : (Lebesgue_outer_measure E : EReal) + ε < ⊤ := by
        apply EReal.add_lt_top (ne_of_lt this) hε_fin
      have hW_le' : Lebesgue_outer_measure W ≤ Lebesgue_outer_measure E + ε := hW_le
      exact lt_of_le_of_lt hW_le' h_add
    let U := V ∩ W
    have hU_open : IsOpen U := IsOpen.inter hV_open hW_open
    have hE_sub_U : E ⊆ U := by
      intro x hx; exact ⟨hE_sub_V hx, hE_sub_W hx⟩
    have hU_fin : Lebesgue_measure U < ⊤ := by
      have h_sub : U ⊆ W := Set.inter_subset_right
      have h_mono : Lebesgue_outer_measure U ≤ Lebesgue_outer_measure W := Lebesgue_outer_measure.mono h_sub
      exact lt_of_le_of_lt h_mono hW_fin
    have hU_diff : Lebesgue_outer_measure (U \ E) ≤ ε := by
      have h_sub : U \ E ⊆ V \ E := by
        intro x hx; rcases hx with ⟨⟨hxV, _⟩, hxE⟩; exact ⟨hxV, hxE⟩
      have h_mono : Lebesgue_outer_measure (U \ E) ≤ Lebesgue_outer_measure (V \ E) :=
        Lebesgue_outer_measure.mono h_sub
      exact le_trans h_mono hV_diff
    exact ⟨U, hU_open, hE_sub_U, hU_fin, hU_diff⟩
