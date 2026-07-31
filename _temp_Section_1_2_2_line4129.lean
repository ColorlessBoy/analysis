import Analysis.MeasureTheory.Section_1_2_1
open Set
open EReal

lemma symmDiff_sub_symmDiff_union_symmDiff {α : Type*} {X Y Z : Set α} : symmDiff X Z ⊆ symmDiff X Y ∪ symmDiff Y Z := by
  intro x hx
  rw [Set.symmDiff_def] at hx
  rcases hx with (⟨hxX, hx_not_Z⟩ | ⟨hxZ, hx_not_X⟩)
  · by_cases hxY : x ∈ Y
    · apply Set.mem_union_right; rw [Set.symmDiff_def]; exact Or.inl ⟨hxY, hx_not_Z⟩
    · apply Set.mem_union_left; rw [Set.symmDiff_def]; exact Or.inl ⟨hxX, hxY⟩
  · by_cases hxY : x ∈ Y
    · apply Set.mem_union_left; rw [Set.symmDiff_def]; exact Or.inr ⟨hxY, hx_not_X⟩
    · apply Set.mem_union_right; rw [Set.symmDiff_def]; exact Or.inr ⟨hxZ, hxY⟩

lemma add_sub_cancel_finite' {x y : EReal} (hy_fin : y ≠ ⊤) (hy_not_bot : y ≠ ⊥) : (x + y) - y = x := by
  sorry

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
  sorry
