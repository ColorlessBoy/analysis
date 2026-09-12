import Analysis.MeasureTheory.Section_1_1_3

open BoundedInterval

/-! Machine-checked counterexamples to statements in `Section_1_1_3` that omit the
closed nonempty interval hypotheses built into `RiemannIntegrableOn`. -/

/-- The original `RiemannIntegrableOn.iff_darbouxIntegrable` statement is false on an
empty closed interval. -/
theorem original_iff_darbouxIntegrable_false :
    ¬ (∀ {f : ℝ → ℝ} {I : BoundedInterval},
      (∃ M, ∀ x ∈ I, |f x| ≤ M) →
      (RiemannIntegrableOn f I ↔ DarbouxIntegrableOn f I)) := by
  intro h
  let f : ℝ → ℝ := fun _ => 0
  let I : BoundedInterval := Icc 1 0
  have hb : ∃ M, ∀ x ∈ I, |f x| ≤ M := by
    refine ⟨0, ?_⟩
    intro x hx
    simp [f]
  have hd : DarbouxIntegrableOn f I := by
    refine ⟨rfl, 0, ?_⟩
    intro x hx
    simp [I, BoundedInterval.toSet] at hx
  have hr := (h hb).mpr hd
  have hn : ¬ I.toSet.Nonempty := by simp [I, BoundedInterval.toSet]
  exact hn hr.2.1

/-- The original indicator theorem is false for an empty closed interval, even for the
empty (hence Jordan measurable) set. -/
theorem original_indicator_of_elem_false :
    ¬ (∀ (I : BoundedInterval) {E : Set ℝ},
      JordanMeasurable (Real.equiv_EuclideanSpace' '' E) →
      RiemannIntegrableOn E.indicator' I) := by
  intro h
  let I : BoundedInterval := Icc 1 0
  let E : Set ℝ := ∅
  have hE : JordanMeasurable (Real.equiv_EuclideanSpace' '' E) := by
    simpa [E] using JordanMeasurable.empty 1
  have hr := h I hE
  have hn : ¬ I.toSet.Nonempty := by simp [I, BoundedInterval.toSet]
  exact hn hr.2.1

/-- The original piecewise-continuous theorem is false for an empty closed interval and
an empty partition. -/
theorem original_piecewise_continuous_false :
    ¬ (∀ {f : ℝ → ℝ} {I : BoundedInterval},
      I = Icc I.a I.b →
      ∀ T : Finset BoundedInterval,
      (T : Set BoundedInterval).PairwiseDisjoint BoundedInterval.toSet →
      I.toSet = ⋃ J ∈ T, J.toSet →
      (∀ J ∈ T, ContinuousOn f J.toSet) → RiemannIntegrableOn f I) := by
  intro h
  let f : ℝ → ℝ := fun _ => 0
  let I : BoundedInterval := Icc 1 0
  have hr := h (f := f) (I := I) rfl ∅ (by simp) (by simp [I, BoundedInterval.toSet]) (by simp)
  have hn : ¬ I.toSet.Nonempty := by simp [I, BoundedInterval.toSet]
  exact hn hr.2.1
