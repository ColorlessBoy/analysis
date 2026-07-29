import Analysis.MeasureTheory.Section_1_2_1

theorem LebesgueMeasurable.finite_TFAE {d:ℕ} (E: Set (EuclideanSpace' d)) :
    [
      LebesgueMeasurable E ∧ Lebesgue_measure E < ⊤,
      (∀ ε > 0, ∃ U : Set (EuclideanSpace' d), IsOpen U ∧ E ⊆ U ∧ Lebesgue_measure U < ⊤ ∧ Lebesgue_outer_measure (U \ E) ≤ ε),
      (∀ ε > 0, ∃ U : Set (EuclideanSpace' d), IsOpen U ∧ Bornology.IsBounded U ∧ Lebesgue_outer_measure (symmDiff U E) ≤ ε),
      (∀ ε > 0, ∃ F: Set (EuclideanSpace' d), IsCompact F ∧ F ⊆ E ∧ Lebesgue_outer_measure (E \ F) ≤ ε),
      (∀ ε > 0, ∃ F: Set (EuclideanSpace' d), IsCompact F ∧ Lebesgue_outer_measure (symmDiff F E) ≤ ε),
      (∀ ε > 0, ∃ E': Set (EuclideanSpace' d), LebesgueMeasurable E' ∧ Lebesgue_measure E' < ⊤ ∧ Lebesgue_outer_measure (symmDiff E' E) ≤ ε),
      (∀ ε > 0, ∃ E': Set (EuclideanSpace' d), LebesgueMeasurable E' ∧ Bornology.IsBounded E' ∧ Lebesgue_outer_measure (symmDiff E' E) ≤ ε),
      (∀ ε > 0, ∃ E': Set (EuclideanSpace' d), IsElementary E' ∧ Lebesgue_outer_measure (symmDiff E' E) ≤ ε),
      (∀ ε > 0, ∃ (n:ℤ) (F: Finset (Box d)), (∀ B ∈ F, B.IsDyadicAtScale n) ∧ Lebesgue_outer_measure (symmDiff (⋃ B ∈ F, B.toSet) E) ≤ ε)
    ].TFAE
  := by
  apply List.tfae_of_cycle
  · -- chain: 0 → 1 → 2 → 3 → 4 → 5 → 6 → 7 → 8
    rw [List.isChain_cons_cons]
    refine ⟨?_, ?_⟩
    · -- 0 → 1
      intro h0 ε hε
      rcases h0 with ⟨h0_meas, h0_fin⟩
      obtain ⟨ε', hε'_pos, hε'_le⟩ : ∃ ε' : ℝ, 0 < ε' ∧ (ε' : EReal) ≤ ε := by
        cases ε with
        | bot => exact absurd hε (not_lt.mpr bot_le)
        | top => exact ⟨1, one_pos, le_top⟩
        | coe r => exact ⟨r, EReal.coe_pos.mp hε, le_refl _⟩
      have hε'_pos' : (0 : EReal) < (ε' : ℝ) := EReal.coe_pos.mpr hε'_pos
      rcases h0_meas ((ε' : ℝ) : EReal) hε'_pos' with ⟨U₁, hU₁_open, hE_sub_U₁, hU₁_diff⟩
      rcases Lebesgue_outer_measure.exists_open_superset_measure_le E ((ε' : ℝ) : EReal) hε'_pos'
        with ⟨V, hV_open, hE_sub_V, hV_meas⟩
      let U := U₁ ∩ V
      have hU_open : IsOpen U := IsOpen.inter hU₁_open hV_open
      have hE_sub_U : E ⊆ U := by
        intro x hx; exact ⟨hE_sub_U₁ hx, hE_sub_V hx⟩
      have hU_fin : Lebesgue_measure U < ⊤ := by
        have hU_sub_V : U ⊆ V := Set.inter_subset_right
        have hU_meas : Lebesgue_outer_measure U ≤ Lebesgue_outer_measure V :=
          Lebesgue_outer_measure.mono hU_sub_V
        have hV_fin : Lebesgue_outer_measure V < ⊤ := by
          have hV_meas' : Lebesgue_outer_measure V ≤ Lebesgue_outer_measure E + (ε' : ℝ) := hV_meas
          have hE_fin : Lebesgue_outer_measure E < ⊤ := h0_fin
          have h_add_fin : Lebesgue_outer_measure E + (ε' : ℝ) < ⊤ :=
            EReal.add_lt_top (ne_of_lt hE_fin) (by exact EReal.coe_ne_top (ε' : ℝ))
          exact lt_of_le_of_lt hV_meas' h_add_fin
        have : Lebesgue_measure U = Lebesgue_outer_measure U := rfl
        rw [this]
        exact lt_of_le_of_lt hU_meas hV_fin
      have hU_diff : Lebesgue_outer_measure (U \ E) ≤ (ε' : ℝ) := by
        have h_sub : U \ E ⊆ U₁ \ E := by
          intro x hx; rcases hx with ⟨hxU, hxE⟩; exact ⟨hxU.1, hxE⟩
        calc
          Lebesgue_outer_measure (U \ E) ≤ Lebesgue_outer_measure (U₁ \ E) :=
            Lebesgue_outer_measure.mono h_sub
          _ ≤ (ε' : ℝ) := hU₁_diff
      refine ⟨U, hU_open, hE_sub_U, hU_fin, ?_⟩
      calc
        Lebesgue_outer_measure (U \ E) ≤ (ε' : ℝ) := hU_diff
        _ ≤ ε := hε'_le
    · -- chain: 1 → 2 → 3 → 4 → 5 → 6 → 7 → 8
      rw [List.isChain_cons_cons]
      refine ⟨?_, ?_⟩
      · -- 1 → 2
        intro h1 ε hε
        obtain ⟨ε', hε'_pos, hε'_le⟩ : ∃ ε' : ℝ, 0 < ε' ∧ (ε' : EReal) ≤ ε := by
          cases ε with
          | bot => exact absurd hε (not_lt.mpr bot_le)
          | top => exact ⟨1, one_pos, le_top⟩
          | coe r => exact ⟨r, EReal.coe_pos.mp hε, le_refl _⟩
        have hε'_pos' : (0 : EReal) < (ε' / 2 : ℝ) := by
          have : (0 : ℝ) < ε' / 2 := by linarith
          exact EReal.coe_pos.mpr this
        rcases h1 ((ε' / 2 : ℝ) : EReal) hε'_pos' with ⟨U, hU_open, hE_sub_U, hU_fin, hU_diff⟩
        -- U has finite measure. Find a bounded open V such that m*(U \ V) ≤ ε'/2
        have hU_fin' : Lebesgue_outer_measure U < ⊤ := hU_fin
        -- Use the fact that closed balls are compact and have finite measure
        sorry
      · -- chain: 2 → 3 → 4 → 5 → 6 → 7 → 8
        rw [List.isChain_cons_cons]
        refine ⟨?_, ?_⟩
        · -- 2 → 3
          sorry
        · -- chain: 3 → 4 → 5 → 6 → 7 → 8
          rw [List.isChain_cons_cons]
          refine ⟨?_, ?_⟩
          · -- 3 → 4
            sorry
          · -- chain: 4 → 5 → 6 → 7 → 8
            rw [List.isChain_cons_cons]
            refine ⟨?_, ?_⟩
            · -- 4 → 5
              sorry
            · -- chain: 5 → 6 → 7 → 8
              rw [List.isChain_cons_cons]
              refine ⟨?_, ?_⟩
              · -- 5 → 6
                sorry
              · -- chain: 6 → 7 → 8
                rw [List.isChain_cons_cons]
                refine ⟨?_, ?_⟩
                · -- 6 → 7
                  sorry
                · -- chain: 7 → 8
                  rw [List.isChain_cons_cons]
                  refine ⟨?_, List.isChain_singleton _⟩
                  · -- 7 → 8
                    sorry
  · -- last: 8 → 0
    sorry
