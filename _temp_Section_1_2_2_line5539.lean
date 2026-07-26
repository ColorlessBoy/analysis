import Analysis.MeasureTheory.Section_1_2_1
open Set

noncomputable section

/-- Box image outer measure bound -/
lemma box_image_outer_measure_le {d:ℕ} (T: EuclideanSpace' d ≃ₗ[ℝ] EuclideanSpace' d) (B: Box d) : 
    Lebesgue_outer_measure (T '' B.toSet) ≤ ((abs (LinearMap.det (T : EuclideanSpace' d →ₗ[ℝ] EuclideanSpace' d))) * Box.volume B : ℝ) := by
  have h_bounded : Bornology.IsBounded (T '' B.toSet) := by
    apply linear_isBounded_image T
    exact (IsElementary.box B).isBounded
  have h_le_Jordan : Lebesgue_outer_measure (T '' B.toSet) ≤ (Jordan_outer_measure (T '' B.toSet) : EReal) :=
    Lebesgue_outer_measure_le_Jordan h_bounded
  have hJM : JordanMeasurable (T '' B.toSet) := JordanMeasurable.linear_of_elem T (IsElementary.box B)
  have h_outer_eq : (Jordan_outer_measure (T '' B.toSet) : EReal) = ((JordanMeasurable.linear_of_elem T (IsElementary.box B)).measure : EReal) := by
    rw [hJM.eq_outer]
  have h_measure_eq : ((JordanMeasurable.linear_of_elem T (IsElementary.box B)).measure : EReal) = 
      ((abs (LinearMap.det (T : EuclideanSpace' d →ₗ[ℝ] EuclideanSpace' d))) * (IsElementary.box B).measure : ℝ) := by
    rw [linear_of_elem_measure_eq T (IsElementary.box B)]
  have h_box_measure : (IsElementary.box B).measure = Box.volume B := IsElementary.measure_of_box B
  calc
    Lebesgue_outer_measure (T '' B.toSet) ≤ (Jordan_outer_measure (T '' B.toSet) : EReal) := h_le_Jordan
    _ = ((JordanMeasurable.linear_of_elem T (IsElementary.box B)).measure : EReal) := h_outer_eq
    _ = ((abs (LinearMap.det (T : EuclideanSpace' d →ₗ[ℝ] EuclideanSpace' d))) * (IsElementary.box B).measure : ℝ) := h_measure_eq
    _ = ((abs (LinearMap.det (T : EuclideanSpace' d →ₗ[ℝ] EuclideanSpace' d))) * Box.volume B : ℝ) := by rw [h_box_measure]

/-- Finite linear scaling lemma -/
lemma Lebesgue_outer_measure.linear_bound_finite {d:ℕ} (T: EuclideanSpace' d ≃ₗ[ℝ] EuclideanSpace' d)
    (A: Set (EuclideanSpace' d)) (r : ℝ) (hA : Lebesgue_outer_measure A ≤ (r : ℝ)) :
    Lebesgue_outer_measure (T '' A) ≤ ((abs (LinearMap.det (T : EuclideanSpace' d →ₗ[ℝ] EuclideanSpace' d))) * r : ℝ) := by
  set D := |LinearMap.det (T : EuclideanSpace' d →ₗ[ℝ] EuclideanSpace' d)| with hD_def
  have hD_pos : 0 < D := by
    rw [abs_pos]
    exact (LinearEquiv.isUnit_det' T).ne_zero
  have hD_nonneg : 0 ≤ D := le_of_lt hD_pos
  -- We use the epsilon argument: for all ε > 0, LHS ≤ D * r + ε
  apply EReal.le_of_forall_pos_le_add'
  intro ε hε
  by_cases hA_top : Lebesgue_outer_measure A = ⊤
  · -- If outer measure is ⊤, then hA gives ⊤ ≤ r, impossible since r is finite
    rw [hA_top] at hA
    have : ¬ (⊤ : EReal) ≤ (r : ℝ) := by
      have h_lt : (r : ℝ) < (⊤ : EReal) := EReal.coe_lt_top _
      exact not_le.mpr h_lt
    exact absurd hA this
  -- So Lebesgue_outer_measure A is finite (not ⊤ and ≥ 0)
  have hA_nonneg : 0 ≤ Lebesgue_outer_measure A := Lebesgue_outer_measure.nonneg A
  have hA_ne_bot : Lebesgue_outer_measure A ≠ ⊥ := by
    intro h_eq
    have h_contra : (0 : EReal) ≤ ⊥ := by simpa [h_eq] using hA_nonneg
    have : ⊥ < (0 : EReal) := EReal.bot_lt_zero
    exact not_lt.mpr h_contra this
  -- Set ε' = ε / D > 0, to find a box cover of A with total volume < outer_measure(A) + ε'
  have h_epsD_pos : (0 : ℝ) < ε / D := div_pos hε hD_pos
  have h_lt_add : Lebesgue_outer_measure A < Lebesgue_outer_measure A + (ε / D : ℝ) :=
    EReal.lt_add_of_pos_coe (x := Lebesgue_outer_measure A) (ε := ε / D) h_epsD_pos hA_ne_bot hA_top
  unfold Lebesgue_outer_measure at *
  -- h_lt_add: sInf (set for A) < sInf (set for A) + (ε / D : ℝ)
  let S_set := {V | ∃ (X : Set ℕ) (S_boxes : X → Box d), A ⊆ ⋃ n, (S_boxes n).toSet ∧ V = ∑' n, (S_boxes n).volume.toEReal}
  have h_S_nonempty : S_set.Nonempty := by
    -- There exists at least one box cover (e.g., using the whole space as one box)
    -- Use the zero-volume box for d > 0, or any box for d = 0
    sorry
  sorry

/-- For any linear isomorphism T, Lebesgue outer measure scales by at most |det T|. -/
lemma Lebesgue_outer_measure.linear_bound {d:ℕ} (T: EuclideanSpace' d ≃ₗ[ℝ] EuclideanSpace' d)
    (S: Set (EuclideanSpace' d)) : Lebesgue_outer_measure (T '' S) ≤ ((abs (LinearMap.det (T : EuclideanSpace' d →ₗ[ℝ] EuclideanSpace' d))) : ℝ) * Lebesgue_outer_measure S := by
  set D := abs (LinearMap.det (T : EuclideanSpace' d →ₗ[ℝ] EuclideanSpace' d)) with hD_def
  have hD_pos : 0 < D := by
    rw [abs_pos]
    exact (LinearEquiv.isUnit_det' T).ne_zero
  have hD_nonneg : 0 ≤ D := le_of_lt hD_pos
  apply EReal.le_of_forall_pos_le_add'
  intro ε hε
  by_cases hS_top : Lebesgue_outer_measure S = ⊤
  · rw [hS_top]
    have h_mul_top : (D : EReal) * (⊤ : EReal) = ⊤ := EReal.coe_mul_top_of_pos hD_pos
    rw [h_mul_top]
    exact le_top
  have hS_nonneg : 0 ≤ Lebesgue_outer_measure S := Lebesgue_outer_measure.nonneg S
  have hS_ne_bot : Lebesgue_outer_measure S ≠ ⊥ := by
    intro h_eq
    have h_contra : (0 : EReal) ≤ ⊥ := by simpa [h_eq] using hS_nonneg
    have : ⊥ < (0 : EReal) := EReal.bot_lt_zero
    exact not_lt.mpr h_contra this
  have h_epsD_pos : (0 : ℝ) < ε / D := div_pos hε hD_pos
  have h_lt_add : Lebesgue_outer_measure S < Lebesgue_outer_measure S + (ε / D : ℝ) :=
    EReal.lt_add_of_pos_coe (x := Lebesgue_outer_measure S) (ε := ε / D) h_epsD_pos hS_ne_bot hS_top
  -- We need to find a box cover of S with total volume < Lebesgue_outer_measure S + (ε / D)
  -- Then use box_image_outer_measure_le + union_le to bound T '' S
  unfold Lebesgue_outer_measure at *
  sorry

/-- Exercise 1.2.21 (Change of variables) -/
lemma LebesgueMeasurable.linear {d:ℕ} (T: EuclideanSpace' d ≃ₗ[ℝ] EuclideanSpace' d)
{E: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E): LebesgueMeasurable (T '' E) := by
  intro ε hε
  induction ε using EReal.rec with
  | bot =>
    exfalso
    have h_contra : (0 : EReal) < (0 : EReal) := lt_trans hε EReal.bot_lt_zero
    exact lt_irrefl (0 : EReal) h_contra
  | top =>
    refine ⟨Set.univ, isOpen_univ, ?_, ?_⟩
    · exact (Set.image_subset_range T E).trans (Set.subset_univ _)
    · exact le_top
  | coe x =>
    have hx_pos : (0 : ℝ) < x := by
      have hx_pos_EReal : (0 : EReal) < (x : EReal) := hε
      exact_mod_cast hx_pos_EReal
    set D := abs (LinearMap.det (T : EuclideanSpace' d →ₗ[ℝ] EuclideanSpace' d)) with hD_def
    have hD_pos : 0 < D := by
      rw [abs_pos]
      exact (LinearEquiv.isUnit_det' T).ne_zero
    have hD_nonneg : 0 ≤ D := le_of_lt hD_pos
    have h_eps'_real_pos : (0 : ℝ) < x / D := div_pos hx_pos hD_pos
    have h_eps'_EReal_pos : (0 : EReal) < (x / D : ℝ) := by exact_mod_cast h_eps'_real_pos
    rcases hE (x / D : ℝ) h_eps'_EReal_pos with ⟨U, hU_open, hE_sub_U, h_outer⟩
    have hTV_open : IsOpen (T '' U) := by
      have hopen : IsOpenMap (T : EuclideanSpace' d → EuclideanSpace' d) := by
        have h_cont : IsOpenMap (T.toContinuousLinearEquiv : EuclideanSpace' d → EuclideanSpace' d) :=
          ContinuousLinearEquiv.isOpenMap T.toContinuousLinearEquiv
        simpa using h_cont
      exact hopen U hU_open
    have h_sub : T '' E ⊆ T '' U := Set.image_mono hE_sub_U
    have h_diff_eq : (T '' U) \ (T '' E) = T '' (U \ E) := by
      ext x; constructor
      · intro h; rcases h with ⟨⟨y, hyU, rfl⟩, hx⟩
        refine ⟨y, ⟨hyU, ?_⟩, rfl⟩
        intro hyE; apply hx; exact ⟨y, hyE, rfl⟩
      · intro h; rcases h with ⟨y, ⟨hyU, hyE⟩, rfl⟩
        refine ⟨⟨y, hyU, rfl⟩, ?_⟩
        intro h'; rcases h' with ⟨z, hzE, hz⟩
        apply hyE; have hzy : z = y := T.injective (by
          have : T z = T y := by simpa [hz] using rfl
          exact this)
        subst hzy; exact hzE
    have h_goal_main : Lebesgue_outer_measure (T '' (U \ E)) ≤ (x : EReal) := by
      have h_bound : Lebesgue_outer_measure (T '' (U \ E)) ≤ (D : ℝ) * Lebesgue_outer_measure (U \ E) :=
        Lebesgue_outer_measure.linear_bound T (U \ E)
      have h_mul : (D : ℝ) * Lebesgue_outer_measure (U \ E) ≤ (x : EReal) := by
        have h_finite : Lebesgue_outer_measure (U \ E) ≠ ⊤ := by
          intro h_eq
          rw [h_eq] at h_outer
          have h_not_top : ¬ ((⊤ : EReal) ≤ (x / D : ℝ)) := by
            have h_lt : (x / D : ℝ) < (⊤ : EReal) := EReal.coe_lt_top _
            exact not_le.mpr h_lt
          exact h_not_top h_outer
        have h_finite_nonneg : 0 ≤ Lebesgue_outer_measure (U \ E) := Lebesgue_outer_measure.nonneg _
        have h_mul_ineq : (D : ℝ) * Lebesgue_outer_measure (U \ E) ≤ (D : ℝ) * (x / D : ℝ) :=
          mul_le_mul_of_nonneg_left h_outer (by exact_mod_cast hD_nonneg)
        have h_mul_calc : (D : ℝ) * (x / D : ℝ) = (x : EReal) := by
          calc
            (D : EReal) * (x / D : ℝ) = ((D * (x / D) : ℝ) : EReal) := by norm_cast
            _ = (x : EReal) := by
              have : (D : ℝ) * (x / D) = x := by field_simp [hD_pos.ne']
              simpa [this]
        have h_mul_calc_le : (D : ℝ) * (x / D : ℝ) ≤ (x : EReal) := le_of_eq h_mul_calc
        exact le_trans h_mul_ineq h_mul_calc_le
      exact le_trans h_bound h_mul
    refine ⟨T '' U, hTV_open, h_sub, ?_⟩
    rw [h_diff_eq]
    exact h_goal_main

end
