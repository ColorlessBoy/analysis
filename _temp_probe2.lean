import Analysis.MeasureTheory.Section_1_3_5

theorem probe1 {d:ℕ} {f : EuclideanSpace' d → ℂ} (hf: ComplexAbsolutelyIntegrable f)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (g : EuclideanSpace' d → ℂ) (E: Set (EuclideanSpace' d)), Continuous (fun x : Eᶜ => g x.val) := by
  sorry

theorem probe2 {d:ℕ} {f : EuclideanSpace' d → ℂ} (hf: ComplexAbsolutelyIntegrable f)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (g : EuclideanSpace' d → ℂ) (E: Set (EuclideanSpace' d)), Continuous (fun x : (Eᶜ : Set (EuclideanSpace' d)) => g x.val) := by
  sorry
