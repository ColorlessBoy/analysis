import Analysis.MeasureTheory.Section_1_2_2
open Set
open EReal

lemma add_sub_cancel_finite' {x y : EReal} (hy_fin : y ≠ ⊤) (hy_not_bot : y ≠ ⊥) : (x + y) - y = x := by
  sorry

lemma exists_n_small_enough (d : ℕ) (δ : ℝ) (hδ_pos : 0 < δ) : ∃ n : ℕ, Real.sqrt (d : ℝ) / ((2 : ℝ)^(n : ℕ)) < δ := by
  sorry

lemma finite_TFAE_0_implies_8 {d : ℕ} (E : Set (EuclideanSpace' d))
    (h0 : LebesgueMeasurable E ∧ Lebesgue_measure E < ⊤) : ∀ ε > 0, ∃ (n : ℤ) (F : Finset (Box d)),
      (∀ B ∈ F, B.IsDyadicAtScale n) ∧ Lebesgue_outer_measure (symmDiff (⋃ B ∈ F, B.toSet) E) ≤ ε := by
  sorry
