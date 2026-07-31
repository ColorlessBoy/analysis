import Analysis.MeasureTheory.Section_1_2_2
open Set
open Real
open EReal

lemma finite_TFAE_0_implies_8 {d : ℕ} (E : Set (EuclideanSpace' d))
    (h0 : LebesgueMeasurable E ∧ Lebesgue_measure E < ⊤) :
    ∀ ε > 0, ∃ (n : ℤ) (F : Finset (Box d)), (∀ B ∈ F, B.IsDyadicAtScale n) ∧
      Lebesgue_outer_measure (symmDiff (⋃ B ∈ F, B.toSet) E) ≤ ε := by
  sorry
