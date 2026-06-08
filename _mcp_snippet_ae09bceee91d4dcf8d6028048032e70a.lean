import Mathlib
open NNRat

example (q : ℚ≥0) : (q.num : ℝ) = ((q : ℚ).num : ℝ) := by
  congr
  exact q.num_div_den