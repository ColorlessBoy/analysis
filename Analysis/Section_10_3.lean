import Mathlib.Tactic

/-!
# Analysis I, Section 10.3: Monotone functions and derivatives

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Relations between monotonicity and differentiability.

-/

namespace Chapter10

/-- Proposition 10.3.1 / Exercise 10.3.1 -/
theorem derivative_of_monotone (X:Set ℝ) {x₀:ℝ} (hx₀: ClusterPt x₀ (.principal (X \ {x₀})))
  {f:ℝ → ℝ} (hmono: Monotone f) (hderiv: DifferentiableWithinAt ℝ f X x₀) :
    derivWithin f X x₀ ≥ 0 := by
  have hderiv' : HasDerivWithinAt f (derivWithin f X x₀) X x₀ := hderiv.hasDerivWithinAt
  rw [hasDerivWithinAt_iff_tendsto_slope] at hderiv'
  haveI : (nhdsWithin x₀ (X \ {x₀})).NeBot := hx₀.neBot
  have h_nonneg : ∀ᶠ x in nhdsWithin x₀ (X \ {x₀}), 0 ≤ (f x - f x₀) / (x - x₀) := by
    apply Filter.eventually_of_mem self_mem_nhdsWithin
    intro x hx
    rcases hx with ⟨hxX, hx_ne⟩
    by_cases hx_lt : x < x₀
    · have hfx_le : f x ≤ f x₀ := hmono (by linarith)
      have hx_sub_neg : x - x₀ < 0 := by linarith
      have h_num_nonpos : f x - f x₀ ≤ 0 := by linarith
      exact div_nonneg_of_nonpos h_num_nonpos (by linarith)
    · have hx_gt : x₀ < x := by
        by_contra! hxge
        have : x = x₀ := le_antisymm hxge (by linarith)
        exact hx_ne this
      have hfx_ge : f x₀ ≤ f x := hmono (by linarith)
      have hx_sub_pos : 0 < x - x₀ := by linarith
      have h_num_nonneg : 0 ≤ f x - f x₀ := by linarith
      exact div_nonneg h_num_nonneg (by linarith)
  simp [slope_fun_def_field] at hderiv'
  exact ge_of_tendsto hderiv' h_nonneg

theorem derivative_of_antitone (X:Set ℝ) {x₀:ℝ} (hx₀: ClusterPt x₀ (.principal (X \ {x₀})))
  {f:ℝ → ℝ} (hmono: Antitone f) (hderiv: DifferentiableWithinAt ℝ f X x₀) :
    derivWithin f X x₀ ≤ 0 := by
  have hderiv' : HasDerivWithinAt f (derivWithin f X x₀) X x₀ := hderiv.hasDerivWithinAt
  rw [hasDerivWithinAt_iff_tendsto_slope] at hderiv'
  haveI : (nhdsWithin x₀ (X \ {x₀})).NeBot := hx₀.neBot
  have h_nonpos : ∀ᶠ x in nhdsWithin x₀ (X \ {x₀}), (f x - f x₀) / (x - x₀) ≤ 0 := by
    apply Filter.eventually_of_mem self_mem_nhdsWithin
    intro x hx
    rcases hx with ⟨hxX, hx_ne⟩
    by_cases hx_lt : x < x₀
    · have hfx_ge : f x₀ ≤ f x := hmono (by linarith)
      have hx_sub_neg : x - x₀ < 0 := by linarith
      have h_num_nonneg : 0 ≤ f x - f x₀ := by linarith
      exact div_nonpos_of_nonneg_of_nonpos h_num_nonneg (by linarith)
    · have hx_gt : x₀ < x := by
        by_contra! hxge
        have : x = x₀ := le_antisymm hxge (by linarith)
        exact hx_ne this
      have hfx_le : f x ≤ f x₀ := hmono (by linarith)
      have hx_sub_pos : 0 < x - x₀ := by linarith
      have h_num_nonpos : f x - f x₀ ≤ 0 := by linarith
      exact div_nonpos_of_nonpos_of_nonneg h_num_nonpos (by linarith)
  simp [slope_fun_def_field] at hderiv'
  exact le_of_tendsto hderiv' h_nonpos

/-- Proposition 10.3.3 / Exercise 10.3.4 -/
theorem strictMono_of_positive_derivative {a b:ℝ} {f:ℝ → ℝ}
  (hderiv: DifferentiableOn ℝ f (.Icc a b)) (hpos: ∀ x ∈ Set.Ioo a b, derivWithin f (.Icc a b) x > 0) :
    StrictMonoOn f (.Icc a b) := by
  intro x hx y hy hxy
  have hcont : ContinuousOn f (.Icc a b) := hderiv.continuousOn
  have hx' : a ≤ x := hx.1
  have hy'' : y ≤ b := hy.2
  have hsub_ic : Set.Icc x y ⊆ Set.Icc a b := Set.Icc_subset_Icc hx' hy''
  have hcont_xy : ContinuousOn f (.Icc x y) := hcont.mono hsub_ic
  have hsub_oo : Set.Ioo x y ⊆ Set.Ioo a b := Set.Ioo_subset_Ioo hx' hy''
  have hderiv_xy : DifferentiableOn ℝ f (.Ioo x y) :=
    hderiv.mono (hsub_oo.trans Set.Ioo_subset_Icc_self)
  obtain ⟨c, hc, hc_eq⟩ := exists_deriv_eq_slope f hxy hcont_xy hderiv_xy
  have ha_c : a < c := lt_of_le_of_lt hx' hc.1
  have hc_b : c < b := lt_of_lt_of_le hc.2 hy''
  have hc_ab : c ∈ Set.Ioo a b := ⟨ha_c, hc_b⟩
  have hmem_Icc_ab : Set.Icc a b ∈ nhds c :=
    Filter.mem_of_superset (isOpen_Ioo.mem_nhds hc_ab) Set.Ioo_subset_Icc_self
  have h_derivWithin_eq_deriv : derivWithin f (.Icc a b) c = deriv f c :=
    derivWithin_of_mem_nhds hmem_Icc_ab
  have hpos_val : derivWithin f (.Icc a b) c > 0 := hpos c hc_ab
  have h_deriv_pos : deriv f c > 0 := by
    rw [h_derivWithin_eq_deriv] at hpos_val
    exact hpos_val
  have h_div_pos : (f y - f x) / (y - x) > 0 := by
    rw [← hc_eq]
    exact h_deriv_pos
  have h_sub_pos : 0 < y - x := sub_pos.mpr hxy
  have h_f_sub_pos : 0 < f y - f x := by
    have h_mul_pos : 0 < ((f y - f x) / (y - x)) * (y - x) := mul_pos h_div_pos h_sub_pos
    have h_mul_eq : ((f y - f x) / (y - x)) * (y - x) = f y - f x := by
      field_simp [h_sub_pos.ne']
    rw [h_mul_eq] at h_mul_pos
    exact h_mul_pos
  linarith

theorem strictAnti_of_negative_derivative {a b:ℝ} {f:ℝ → ℝ}
  (hderiv: DifferentiableOn ℝ f (.Icc a b)) (hneg: ∀ x ∈ Set.Ioo a b, derivWithin f (.Icc a b) x < 0) :
    StrictAntiOn f (.Icc a b) := by
  intro x hx y hy hxy
  have hcont : ContinuousOn f (.Icc a b) := hderiv.continuousOn
  have hx' : a ≤ x := hx.1
  have hy'' : y ≤ b := hy.2
  have hsub_ic : Set.Icc x y ⊆ Set.Icc a b := Set.Icc_subset_Icc hx' hy''
  have hcont_xy : ContinuousOn f (.Icc x y) := hcont.mono hsub_ic
  have hsub_oo : Set.Ioo x y ⊆ Set.Ioo a b := Set.Ioo_subset_Ioo hx' hy''
  have hderiv_xy : DifferentiableOn ℝ f (.Ioo x y) :=
    hderiv.mono (hsub_oo.trans Set.Ioo_subset_Icc_self)
  obtain ⟨c, hc, hc_eq⟩ := exists_deriv_eq_slope f hxy hcont_xy hderiv_xy
  have ha_c : a < c := lt_of_le_of_lt hx' hc.1
  have hc_b : c < b := lt_of_lt_of_le hc.2 hy''
  have hc_ab : c ∈ Set.Ioo a b := ⟨ha_c, hc_b⟩
  have hmem_Icc_ab : Set.Icc a b ∈ nhds c :=
    Filter.mem_of_superset (isOpen_Ioo.mem_nhds hc_ab) Set.Ioo_subset_Icc_self
  have h_derivWithin_eq_deriv : derivWithin f (.Icc a b) c = deriv f c :=
    derivWithin_of_mem_nhds hmem_Icc_ab
  have hneg_val : derivWithin f (.Icc a b) c < 0 := hneg c hc_ab
  have h_deriv_neg : deriv f c < 0 := by
    rw [h_derivWithin_eq_deriv] at hneg_val
    exact hneg_val
  have h_div_neg : (f y - f x) / (y - x) < 0 := by
    rw [← hc_eq]
    exact h_deriv_neg
  have h_sub_pos : 0 < y - x := sub_pos.mpr hxy
  have h_f_sub_neg : f y - f x < 0 := by
    have h_mul_neg : ((f y - f x) / (y - x)) * (y - x) < 0 :=
      mul_neg_of_neg_of_pos h_div_neg h_sub_pos
    have h_mul_eq : ((f y - f x) / (y - x)) * (y - x) = f y - f x := by
      field_simp [h_sub_pos.ne']
    rw [h_mul_eq] at h_mul_neg
    exact h_mul_neg
  linarith

/-- Example 10.3.2 -/
example : ∃ f : ℝ → ℝ, Continuous f ∧ StrictMono f ∧ ¬ DifferentiableAt ℝ f 0 := by
  let f : ℝ → ℝ := fun x ↦ if 0 ≤ x then x else 2 * x
  have hcont : Continuous f := by
    unfold f
    have h_closure_nonneg : closure {x : ℝ | 0 ≤ x} = Set.Ici 0 := by
      have : {x : ℝ | 0 ≤ x} = Set.Ici 0 := by ext x; simp
      rw [this]
      exact closure_Ici (0 : ℝ)
    have h_closure_neg : closure {x : ℝ | ¬ 0 ≤ x} = Set.Iic 0 := by
      have : {x : ℝ | ¬ 0 ≤ x} = Set.Iio 0 := by ext x; simp
      rw [this]
      exact closure_Iio (0 : ℝ)
    refine continuous_if ?_ ?_ ?_
    · intro a ha
      have ha0 : a = 0 := by
        have h_frontier : frontier {x : ℝ | 0 ≤ x} = ({0} : Set ℝ) := by
          have : {x : ℝ | 0 ≤ x} = Set.Ici 0 := by ext x; simp
          rw [this]
          simp
        rw [h_frontier] at ha
        exact ha
      simp [ha0]
    · rw [h_closure_nonneg]
      exact continuous_id.continuousOn
    · rw [h_closure_neg]
      exact (continuous_const.mul continuous_id).continuousOn
  have hmono : StrictMono f := by
    intro x y hxy
    unfold f
    by_cases hx0 : 0 ≤ x
    · simp [hx0]
      by_cases hy0 : 0 ≤ y
      · simp [hy0, hxy]
      · have : y < 0 := by linarith
        linarith
    · have hx_neg : x < 0 := by linarith
      simp [hx0]
      by_cases hy0 : 0 ≤ y
      · simp [hy0]
        nlinarith
      · simp [hy0]
        nlinarith
  have hnotdiff : ¬ DifferentiableAt ℝ f 0 := by
    intro hdiff
    have hderiv : HasDerivAt f (deriv f 0) 0 := hdiff.hasDerivAt
    have htendsto : Filter.Tendsto (slope f 0) (nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ) (nhds (deriv f 0)) :=
      HasDerivAt.tendsto_slope hderiv
    have h_sub_right : Set.Ioi (0 : ℝ) ⊆ ({0} : Set ℝ)ᶜ := by
      intro x hx
      have hxpos : 0 < x := hx
      simp [hxpos.ne.symm]
    have htendsto_right : Filter.Tendsto (slope f 0) (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds (deriv f 0)) :=
      htendsto.mono_left (nhdsWithin_mono (0 : ℝ) h_sub_right)
    have h_slope_one : slope f 0 =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))] (fun _ ↦ (1 : ℝ)) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      dsimp [slope, f]
      have hxpos : 0 < x := hx
      have hx_nonneg : 0 ≤ x := hxpos.le
      simp [hx_nonneg]
      field_simp [hxpos.ne']
    have htendsto_one : Filter.Tendsto (slope f 0) (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds (1 : ℝ)) :=
      h_slope_one.tendsto
    haveI : (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))).NeBot := nhdsWithin_Ioi_neBot (le_refl (0 : ℝ))
    have h_deriv_eq_one : deriv f 0 = (1 : ℝ) :=
      tendsto_nhds_unique htendsto_right htendsto_one
    have h_sub_left : Set.Iio (0 : ℝ) ⊆ ({0} : Set ℝ)ᶜ := by
      intro x hx
      have hxneg : x < 0 := hx
      simp [hxneg.ne]
    have htendsto_left : Filter.Tendsto (slope f 0) (nhdsWithin (0 : ℝ) (Set.Iio (0 : ℝ))) (nhds (deriv f 0)) :=
      htendsto.mono_left (nhdsWithin_mono (0 : ℝ) h_sub_left)
    have h_slope_two : slope f 0 =ᶠ[nhdsWithin (0 : ℝ) (Set.Iio (0 : ℝ))] (fun _ ↦ (2 : ℝ)) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      dsimp [slope, f]
      have hxneg : x < 0 := hx
      have hx_not_nonneg : ¬ 0 ≤ x := by linarith
      simp [hx_not_nonneg]
      have hx_ne_zero : x ≠ 0 := by linarith
      field_simp [hx_ne_zero]
    have htendsto_two : Filter.Tendsto (slope f 0) (nhdsWithin (0 : ℝ) (Set.Iio (0 : ℝ))) (nhds (2 : ℝ)) :=
      h_slope_two.tendsto
    haveI : (nhdsWithin (0 : ℝ) (Set.Iio (0 : ℝ))).NeBot := nhdsWithin_Iio_neBot (le_refl (0 : ℝ))
    have h_deriv_eq_two : deriv f 0 = (2 : ℝ) :=
      tendsto_nhds_unique htendsto_left htendsto_two
    have : (1 : ℝ) ≠ 2 := by norm_num
    exact this (h_deriv_eq_one.symm ▸ h_deriv_eq_two)
  exact ⟨f, hcont, hmono, hnotdiff⟩

/-- Exercise 10.3.3 -/
example : ∃ f: ℝ → ℝ, StrictMono f ∧ Differentiable ℝ f ∧ deriv f 0 = 0 := by
  have h_odd : Odd 3 := by decide
  refine ⟨fun x : ℝ => x ^ 3, h_odd.strictMono_pow, differentiable_pow 3, ?_⟩
  rw [(hasDerivAt_pow 3 0).deriv]
  simp

/-- Exercise 10.3.5 -/
example : ∃ (X : Set ℝ) (f : ℝ → ℝ), DifferentiableOn ℝ f X ∧
  (∀ x ∈ X, derivWithin f X x > 0) ∧ ¬ StrictMonoOn f X := by
  let X : Set ℝ := Set.Ioo (0 : ℝ) 1 ∪ Set.Ioo (2 : ℝ) 3
  let f : ℝ → ℝ := Set.piecewise (Set.Ioo (0 : ℝ) 1) id (fun x => x - 100)
  have hX_open : ∀ x ∈ X, X ∈ nhds x := by
    intro x hx
    rcases hx with (hx | hx)
    · have h_open : Set.Ioo (0 : ℝ) 1 ∈ nhds x := IsOpen.mem_nhds isOpen_Ioo hx
      exact Filter.mem_of_superset h_open (Set.subset_union_left (t := Set.Ioo (2 : ℝ) 3))
    · have h_open : Set.Ioo (2 : ℝ) 3 ∈ nhds x := IsOpen.mem_nhds isOpen_Ioo hx
      exact Filter.mem_of_superset h_open (Set.subset_union_right (s := Set.Ioo (0 : ℝ) 1))
  have hdiff : DifferentiableOn ℝ f X := by
    intro x hx
    rcases hx with (hx | hx)
    · have h_open : Set.Ioo (0 : ℝ) 1 ∈ nhds x := IsOpen.mem_nhds isOpen_Ioo hx
      have hf_eq_id : f =ᶠ[nhds x] id := by
        filter_upwards [h_open] with y hy
        simp [f, hy]
      exact (differentiableAt_id.congr_of_eventuallyEq hf_eq_id).differentiableWithinAt
    · have h_open : Set.Ioo (2 : ℝ) 3 ∈ nhds x := IsOpen.mem_nhds isOpen_Ioo hx
      have hf_eq_sub : f =ᶠ[nhds x] (fun y => y - 100) := by
        filter_upwards [h_open] with y hy
        dsimp [f]
        have hy_notin : y ∉ Set.Ioo (0 : ℝ) 1 := by
          intro hy'
          have : y < 1 := hy'.2
          have : y > 2 := hy.1
          linarith
        simp [hy_notin]
      exact ((differentiableAt_id.sub (differentiableAt_const 100)).congr_of_eventuallyEq hf_eq_sub).differentiableWithinAt
  have hderiv_pos : ∀ x ∈ X, derivWithin f X x > 0 := by
    intro x hx
    have hX_mem : X ∈ nhds x := hX_open x hx
    have hderivWithin_eq : derivWithin f X x = deriv f x :=
      derivWithin_of_mem_nhds hX_mem
    rw [hderivWithin_eq]
    rcases hx with (hx | hx)
    · have h_open : Set.Ioo (0 : ℝ) 1 ∈ nhds x := IsOpen.mem_nhds isOpen_Ioo hx
      have hf_eq_id : f =ᶠ[nhds x] id := by
        filter_upwards [h_open] with y hy
        simp [f, hy]
      have hderiv_eq : deriv f x = deriv id x :=
        Filter.EventuallyEq.deriv_eq hf_eq_id
      rw [hderiv_eq, deriv_id]
      norm_num
    · have h_open : Set.Ioo (2 : ℝ) 3 ∈ nhds x := IsOpen.mem_nhds isOpen_Ioo hx
      have hf_eq_sub : f =ᶠ[nhds x] (fun y => y - 100) := by
        filter_upwards [h_open] with y hy
        dsimp [f]
        have hy_notin : y ∉ Set.Ioo (0 : ℝ) 1 := by
          intro hy'
          have : y < 1 := hy'.2
          have : y > 2 := hy.1
          linarith
        simp [hy_notin]
      have hderiv_eq : deriv f x = deriv (fun y => y - 100) x :=
        Filter.EventuallyEq.deriv_eq hf_eq_sub
      rw [hderiv_eq]
      have h_deriv : HasDerivAt (fun y : ℝ => y - 100) 1 x := by
        simpa using (hasDerivAt_id x).sub_const 100
      rw [h_deriv.deriv]
      norm_num
  have not_strict_mono : ¬ StrictMonoOn f X := by
    intro hsm
    have hx : (0.5 : ℝ) ∈ X := by
      apply Set.mem_union_left
      exact ⟨by norm_num, by norm_num⟩
    have hy : (2.5 : ℝ) ∈ X := by
      apply Set.mem_union_right (Set.Ioo (0 : ℝ) 1)
      exact ⟨by norm_num, by norm_num⟩
    have hxy : (0.5 : ℝ) < (2.5 : ℝ) := by norm_num
    have h_fx_gt_fy : f (0.5 : ℝ) > f (2.5 : ℝ) := by
      dsimp [f]
      have h1 : (0.5 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
      have h2 : (2.5 : ℝ) ∉ Set.Ioo (0 : ℝ) 1 := by
        intro h
        have : (2.5 : ℝ) < 1 := h.2
        norm_num at this
      simp [h1, h2]
      norm_num
    have h_fx_lt_fy : f (0.5 : ℝ) < f (2.5 : ℝ) := hsm hx hy hxy
    linarith
  exact ⟨X, f, hdiff, hderiv_pos, not_strict_mono⟩

end Chapter10
