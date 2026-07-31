import Analysis.MeasureTheory.Section_1_2_2
open Set

lemma DyadicCube.diam_bound {d : ℕ} (n : ℕ) (a : Fin d → ℤ) (x y : EuclideanSpace' d)
    (hx : x ∈ (DyadicCube (n : ℤ) a).toSet) (hy : y ∈ (DyadicCube (n : ℤ) a).toSet) : 
    ‖x - y‖ ≤ Real.sqrt (d : ℝ) * ((1 : ℝ) / ((2 : ℝ)^(n : ℕ))) := by
  have h_coord_diff (i : Fin d) : |x i - y i| ≤ (1 : ℝ) / ((2 : ℝ)^(n : ℕ)) := by
    have hxi : (a i : ℝ) / ((2 : ℝ)^(n : ℕ)) ≤ x i ∧ x i ≤ ((a i : ℝ) + 1) / ((2 : ℝ)^(n : ℕ)) := by
      simpa [DyadicCube, Box.mem_toSet, BoundedInterval.set_Icc, map_pow] using hx i
    have hyi : (a i : ℝ) / ((2 : ℝ)^(n : ℕ)) ≤ y i ∧ y i ≤ ((a i : ℝ) + 1) / ((2 : ℝ)^(n : ℕ)) := by
      simpa [DyadicCube, Box.mem_toSet, BoundedInterval.set_Icc, map_pow] using hy i
    rcases hxi with ⟨hx_low, hx_high⟩
    rcases hyi with ⟨hy_low, hy_high⟩
    have h_len : ((a i : ℝ) + 1) / ((2 : ℝ)^(n : ℕ)) - (a i : ℝ) / ((2 : ℝ)^(n : ℕ)) = (1 : ℝ) / ((2 : ℝ)^(n : ℕ)) := by
      field_simp [show (2 : ℝ)^(n : ℕ) ≠ 0 from by positivity]
      ring
    rw [abs_le]
    constructor <;> nlinarith

  have h_norm_sq_bound : ‖x - y‖^2 ≤ (d : ℝ) * (((1 : ℝ) / ((2 : ℝ)^(n : ℕ)))^2) := by
    calc
      ‖x - y‖^2 = ∑ i : Fin d, ((x - y) i)^2 := by
        calc
          ‖x - y‖^2 = (Real.sqrt (∑ i : Fin d, ((x - y).ofLp i)^2))^2 := by rw [EuclideanSpace'.norm_eq (x - y)]
          _ = ∑ i : Fin d, ((x - y).ofLp i)^2 := by
            have h_nonneg : 0 ≤ ∑ i : Fin d, ((x - y).ofLp i)^2 := Finset.sum_nonneg (fun i _ => pow_two_nonneg _)
            rw [Real.sq_sqrt h_nonneg]
          _ = ∑ i : Fin d, ((x - y) i)^2 := by simp
      _ ≤ ∑ i : Fin d, (((1 : ℝ) / ((2 : ℝ)^(n : ℕ)))^2) := by
        refine Finset.sum_le_sum (fun i hi => ?_)
        have h_sq : ((x - y) i)^2 ≤ ((1 : ℝ) / ((2 : ℝ)^(n : ℕ)))^2 := by
          have h_abs : |(x - y) i| ≤ (1 : ℝ) / ((2 : ℝ)^(n : ℕ)) := by simpa using h_coord_diff i
          nlinarith [abs_le.mp h_abs]
        exact h_sq
      _ = (d : ℝ) * (((1 : ℝ) / ((2 : ℝ)^(n : ℕ)))^2) := by simp

  have h_nonneg : 0 ≤ (1 : ℝ) / ((2 : ℝ)^(n : ℕ)) := by positivity
  calc
    ‖x - y‖ = Real.sqrt (‖x - y‖^2) := by rw [Real.sqrt_sq (norm_nonneg _)]
    _ ≤ Real.sqrt ((d : ℝ) * (((1 : ℝ) / ((2 : ℝ)^(n : ℕ)))^2)) := Real.sqrt_le_sqrt h_norm_sq_bound
    _ = Real.sqrt (d : ℝ) * ((1 : ℝ) / ((2 : ℝ)^(n : ℕ))) := by
      rw [Real.sqrt_mul (show 0 ≤ (d : ℝ) from by exact_mod_cast Nat.zero_le _),
        Real.sqrt_sq h_nonneg]
