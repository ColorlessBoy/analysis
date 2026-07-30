import Analysis.MeasureTheory.Section_1_2_2

open Set
open Bornology
open Box

set_option maxHeartbeats 400000

theorem LebesgueMeasurable.finite_TFAE_aux {d:ℕ} (E: Set (EuclideanSpace' d)) :
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
  -- Main proof: Use List.tfae_of_cycle with the chain 0→1→2→3→4→5→6→7→8→0
  apply List.tfae_of_cycle
  · -- Build chain 0→1→2→3→4→5→6→7→8
    rw [List.isChain_cons_cons]
    refine ⟨?_, ?_⟩
    · -- 0 → 1
      intro h0 ε hε
      rcases h0 with ⟨hE_meas, hE_fin⟩
      -- Use LebesgueMeasurable.TFAE (0)→(1) to get open superset with small outer measure
      have h_TFAE_01 : ∀ (E : Set (EuclideanSpace' d)), LebesgueMeasurable E → (∀ ε > 0, ∃ (U : Set (EuclideanSpace' d)), IsOpen U ∧ E ⊆ U ∧ Lebesgue_outer_measure (U \ E) ≤ ε) := by
        intro E hE_meas'
        have h_TFAE := (LebesgueMeasurable.TFAE E).2
        -- We know: [LebesgueMeasurable E, ...].TFAE
        -- So position 0 ↔ position 1. So hE_meas' → position 1.
        have h01 : (LebesgueMeasurable.TFAE E).1 0 1 := (List.TFAE.out (LebesgueMeasurable.TFAE E)).2
        sorry
      sorry
    · -- Chain for 1→2→3→4→5→6→7→8
      sorry
  · -- Last implication 8→0
    sorry