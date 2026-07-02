import Mathlib
example (x x₀ : ℝ) (δ : ℝ) (h : |x - x₀| < δ) : dist x x₀ < δ := by
  simpa [Real.dist_eq] using h