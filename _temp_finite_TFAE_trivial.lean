import Analysis.MeasureTheory.Section_1_2_2

open Set

lemma finite_TFAE_3_implies_4 {d : ℕ} (E : Set (EuclideanSpace' d))
    (h3 : ∀ ε > 0, ∃ F : Set (EuclideanSpace' d), IsCompact F ∧ F ⊆ E ∧ Lebesgue_outer_measure (E \ F) ≤ ε) :
    ∀ ε > 0, ∃ F : Set (EuclideanSpace' d), IsCompact F ∧ Lebesgue_outer_measure (symmDiff F E) ≤ ε := by
  intro ε hε
  rcases h3 ε hε with ⟨F, hF_compact, hF_sub_E, h_diff⟩
  refine ⟨F, hF_compact, ?_⟩
  have h_symm_eq : symmDiff F E = E \ F := by
    rw [symmDiff_def]
    simp [Set.diff_eq_empty.mpr hF_sub_E]
  rw [h_symm_eq]
  exact h_diff

lemma finite_TFAE_4_implies_5 {d : ℕ} (E : Set (EuclideanSpace' d))
    (h4 : ∀ ε > 0, ∃ F : Set (EuclideanSpace' d), IsCompact F ∧ Lebesgue_outer_measure (symmDiff F E) ≤ ε) :
    ∀ ε > 0, ∃ E' : Set (EuclideanSpace' d), LebesgueMeasurable E' ∧ Lebesgue_measure E' < ⊤ ∧ Lebesgue_outer_measure (symmDiff E' E) ≤ ε := by
  intro ε hε
  rcases h4 ε hε with ⟨F, hF_compact, h_symm⟩
  refine ⟨F, hF_compact.isClosed.measurable, ?_, h_symm⟩
  have h_fin : Lebesgue_outer_measure F ≠ ⊤ := Lebesgue_outer_measure.finite_of_compact hF_compact
  rw [show Lebesgue_measure F = Lebesgue_outer_measure F from rfl]
  by_cases h_nonneg : 0 ≤ Lebesgue_outer_measure F
  · cases h : Lebesgue_outer_measure F with
    | bot => exact (not_lt.mpr h_nonneg (by rw [h]; exact EReal.bot_lt_zero)).elim
    | top => exact (h_fin h).elim
    | coe r => exact EReal.coe_lt_top r
  · exact (h_nonneg (Lebesgue_outer_measure.nonneg F)).elim
