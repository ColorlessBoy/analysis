import Analysis.MeasureTheory.Section_1_3_2

open UnsignedSimpleFunction.IntegralWellDef
open Filter
open scoped Topology
open scoped Pointwise

/-!
# Introduction to Measure Theory, Section 1.3.3: Unsigned Lebesgue integrals

A companion to (the introduction to) Section 1.3.3 of the book "An introduction to Measure Theory".

-/

/-- Definition 1.3.12 (Lower unsigned Lebesgue integral) -/
noncomputable def LowerUnsignedLebesgueIntegral {d:ℕ} (f: EuclideanSpace' d → EReal) : EReal :=
  sSup { R | ∃ g: EuclideanSpace' d → EReal, ∃ hg: UnsignedSimpleFunction g, ∀ x, g x ≤ f x ∧ R = hg.integ}

/-- Definition 1.3.12 (Upper unsigned Lebesgue integral) -/
noncomputable def UpperUnsignedLebesgueIntegral {d:ℕ} (f: EuclideanSpace' d → EReal) : EReal :=
  sInf { R | ∃ g: EuclideanSpace' d → EReal, ∃ hg: UnsignedSimpleFunction g, ∀ x, g x ≥ f x ∧ R = hg.integ}

theorem LowerUnsignedLebesgueIntegral.eq {d:ℕ} {f: EuclideanSpace' d → EReal} (hf : ∀ x, 0 ≤ f x) : LowerUnsignedLebesgueIntegral f =
  sSup { R | ∃ g: EuclideanSpace' d → EReal, ∃ hg: UnsignedSimpleFunction g, (AlmostAlways (fun x ↦ g x ≤ f x)) ∧ R = hg.integ} := by
  -- Both sides are suprema over sets of integrals of simple functions g bounded by f.
  -- LHS: pointwise everywhere g ≤ f; RHS: almost everywhere g ≤ f.
  -- Equality follows since the simple integral is invariant under modification on null sets.
  unfold LowerUnsignedLebesgueIntegral
  -- First, simplify the weird definition: ∀ x, g x ≤ f x ∧ R = hg.integ is equivalent to
  -- (∀ x, g x ≤ f x) ∧ R = hg.integ (since R = hg.integ is constant in x)
  congr 1
  ext R
  simp only [Set.mem_setOf_eq]
  constructor
  · intro ⟨g, hg, hcond⟩
    -- Extract the pointwise bound and the equality
    have hle : ∀ x, g x ≤ f x := fun x ↦ (hcond x).1
    have hReq : R = hg.integ := by
      -- hcond gives us R = hg.integ for any x, so pick any x
      -- EuclideanSpace' d is always nonempty
      haveI : Nonempty (EuclideanSpace' d) := inferInstance
      exact (hcond (Classical.arbitrary _)).2
    exact ⟨g, hg, AlmostAlways.ofAlways hle, hReq⟩
  · intro ⟨g, hg, hae, hReq⟩
    -- Need to find g' with g' ≤ f everywhere and same integral
    -- Let N = {x | g x > f x} be the null set where g exceeds f
    let N := {x | ¬(g x ≤ f x)}
    have hN_null : IsNull N := hae
    have hN_meas : LebesgueMeasurable N := IsNull.measurable hN_null
    -- Define g' = g * indicator(Nᶜ) = g where g ≤ f, 0 elsewhere
    let g' := fun x => g x * (EReal.indicator Nᶜ x)
    -- g' is a simple function (product of simple function with indicator of measurable set)
    have hg'_simple : UnsignedSimpleFunction g' := by
      -- This follows from the definition of simple functions as linear combinations of indicators
      -- g = ∑ c_i • indicator(E_i), so g' = ∑ c_i • indicator(E_i ∩ Nᶜ)
      obtain ⟨k, c, E, ⟨hcE, hg_eq⟩⟩ := hg
      use k, c, fun i => E i ∩ Nᶜ
      constructor
      · intro i
        constructor
        · exact LebesgueMeasurable.inter (hcE i).1 (LebesgueMeasurable.complement hN_meas)
        · exact (hcE i).2
      · -- Prove g' = ∑ c_i • indicator(E_i ∩ Nᶜ) pointwise
        funext x
        simp only [g', hg_eq, EReal.indicator, Real.EReal_fun]
        -- Use Finset.sum_fn to convert (∑ i, f i) x to ∑ i, f i x
        conv_lhs => rw [Finset.sum_fn]; simp only [Pi.smul_apply]
        conv_rhs => rw [Finset.sum_fn]; simp only [Pi.smul_apply]
        by_cases hx : x ∈ Nᶜ
        · -- x ∈ Nᶜ: multiply by 1, and E_i ∩ Nᶜ membership reduces to E_i membership
          rw [Set.indicator'_of_mem hx, EReal.coe_one, mul_one]
          apply Finset.sum_congr rfl
          intro i _
          simp only [Real.EReal_fun]
          by_cases hEi : x ∈ E i
          · rw [Set.indicator'_of_mem hEi, Set.indicator'_of_mem (Set.mem_inter hEi hx)]
          · have hnotinter : x ∉ E i ∩ Nᶜ := fun h => hEi (Set.mem_of_mem_inter_left h)
            rw [Set.indicator'_of_notMem hEi, Set.indicator'_of_notMem hnotinter]
        · -- x ∉ Nᶜ: multiply by 0, and E_i ∩ Nᶜ is empty at x
          rw [Set.indicator'_of_notMem hx, EReal.coe_zero, mul_zero]
          symm
          apply Finset.sum_eq_zero
          intro i _
          have hnotinter : x ∉ E i ∩ Nᶜ := fun h => hx (Set.mem_of_mem_inter_right h)
          simp only [Real.EReal_fun, Set.indicator'_of_notMem hnotinter, EReal.coe_zero, smul_zero]
    -- g' ≤ f everywhere
    have hg'_le_f : ∀ x, g' x ≤ f x := by
      intro x
      by_cases hx : x ∈ N
      · -- On N: g' x = g x * 0 = 0 ≤ f x (using hf)
        simp only [g', EReal.indicator, Real.EReal_fun]
        have hnotmem : x ∉ Nᶜ := by simp only [Set.mem_compl_iff, not_not]; exact hx
        rw [Set.indicator'_of_notMem hnotmem, EReal.coe_zero, mul_zero]
        exact hf x
      · -- On Nᶜ: g' x = g x * 1 = g x ≤ f x (by definition of N)
        simp only [N, Set.mem_setOf_eq] at hx
        push_neg at hx
        simp only [g', EReal.indicator, Real.EReal_fun]
        have hmem : x ∈ Nᶜ := by simp only [Set.mem_compl_iff, N, Set.mem_setOf_eq, hx, not_true_eq_false, not_false_eq_true]
        rw [Set.indicator'_of_mem hmem, EReal.coe_one, mul_one]
        exact hx
    -- g' = g almost everywhere (they differ only on N which is null)
    have hg'_ae : AlmostEverywhereEqual g' g := by
      unfold AlmostEverywhereEqual AlmostAlways IsNull
      -- {x | g' x ≠ g x} ⊆ N, and N is null
      have hsub : {x | g' x ≠ g x} ⊆ N := by
        intro x hx
        simp only [Set.mem_setOf_eq] at hx
        by_contra hxN
        -- If x ∉ N, then g' x = g x * 1 = g x
        have hmem : x ∈ Nᶜ := by simp only [Set.mem_compl_iff, N, Set.mem_setOf_eq]; exact hxN
        simp only [g', EReal.indicator, Real.EReal_fun, Set.indicator'_of_mem hmem,
                   EReal.coe_one, mul_one] at hx
        exact hx rfl
      have hle : Lebesgue_outer_measure {x | g' x ≠ g x} ≤ 0 :=
        calc Lebesgue_outer_measure {x | g' x ≠ g x}
            ≤ Lebesgue_outer_measure N := Lebesgue_outer_measure.mono hsub
          _ = 0 := hN_null
      exact le_antisymm hle (Lebesgue_outer_measure.nonneg _)
    -- By Exercise 1.3.1(iv), same integral
    have hinteg_eq : hg'_simple.integ = hg.integ :=
      UnsignedSimpleFunction.integral_eq_integral_of_aeEqual hg'_simple hg hg'_ae
    -- Now construct the witness
    use g', hg'_simple
    intro x
    constructor
    · exact hg'_le_f x
    · rw [hReq, ← hinteg_eq]

/-- Exercise 1.3.10(i) (Compatibility with the simple integral) -/
theorem LowerUnsignedLebesgueIntegral.eq_simpleIntegral {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f) :
    LowerUnsignedLebesgueIntegral f = hf.integ := by
  unfold LowerUnsignedLebesgueIntegral
  apply le_antisymm
  · apply sSup_le
    intro R hR
    rcases hR with ⟨g, hg, hg_cond⟩
    have hg_le : ∀ x, g x ≤ f x := fun x => (hg_cond x).1
    have hR_eq : R = hg.integ := (hg_cond (Classical.arbitrary _)).2
    rw [hR_eq]
    exact UnsignedSimpleFunction.integral_le_integral_of_aeLe hg hf (AlmostAlways.ofAlways hg_le)
  · exact le_sSup ⟨f, hf, fun x => ⟨le_rfl, rfl⟩⟩

/-- Exercise 1.3.10(ii) (Monotonicity) -/
theorem LowerUnsignedLebesgueIntegral.mono {d:ℕ} {f g: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) (hg: UnsignedMeasurable g)
    (hfg: AlmostAlways (fun x ↦ f x ≤ g x)) :
    LowerUnsignedLebesgueIntegral f ≤ LowerUnsignedLebesgueIntegral g := by
  rw [LowerUnsignedLebesgueIntegral.eq hf.1, LowerUnsignedLebesgueIntegral.eq hg.1]
  apply sSup_le_sSup
  intro R hR
  rcases hR with ⟨g1, hg1, hg1ae, rfl⟩
  -- g1 ≤ f a.e. and f ≤ g a.e. ⟹ g1 ≤ g a.e.
  have htrans : AlmostAlways (fun x => g1 x ≤ g x) := by
    unfold AlmostAlways at *
    have hsub : {x | ¬ g1 x ≤ g x} ⊆ {x | ¬ g1 x ≤ f x} ∪ {x | ¬ f x ≤ g x} := by
      intro x hx
      by_contra h
      have h1 : g1 x ≤ f x := by
        by_contra h1
        exact h (Or.inl h1)
      have h2 : f x ≤ g x := by
        by_contra h2
        exact h (Or.inr h2)
      exact hx (le_trans h1 h2)
    have hle : Lebesgue_outer_measure {x | ¬ g1 x ≤ g x} ≤ 0 := by
      have hle1 : Lebesgue_outer_measure {x | ¬ g1 x ≤ g x} ≤
          Lebesgue_outer_measure ({x | ¬ g1 x ≤ f x} ∪ {x | ¬ f x ≤ g x}) :=
        Lebesgue_outer_measure.mono hsub
      have hb : Lebesgue_outer_measure ({x | ¬ g1 x ≤ f x} ∪ {x | ¬ f x ≤ g x}) ≤
          Lebesgue_outer_measure {x | ¬ g1 x ≤ f x} + Lebesgue_outer_measure {x | ¬ f x ≤ g x} := by
        let E : Fin 2 → Set (EuclideanSpace' d) := ![{x | ¬ g1 x ≤ f x}, {x | ¬ f x ≤ g x}]
        have h_union : {x | ¬ g1 x ≤ f x} ∪ {x | ¬ f x ≤ g x} = ⋃ i, E i := by
          ext y
          simp [E]
        have h_sum : (∑ i : Fin 2, Lebesgue_outer_measure (E i)) =
            Lebesgue_outer_measure {x | ¬ g1 x ≤ f x} + Lebesgue_outer_measure {x | ¬ f x ≤ g x} := by
          simp [E, Fin.sum_univ_two]
        rw [h_union, ← h_sum]
        exact Lebesgue_outer_measure.finite_union_le E
      calc Lebesgue_outer_measure {x | ¬ g1 x ≤ g x}
          ≤ Lebesgue_outer_measure ({x | ¬ g1 x ≤ f x} ∪ {x | ¬ f x ≤ g x}) := hle1
        _ ≤ Lebesgue_outer_measure {x | ¬ g1 x ≤ f x} + Lebesgue_outer_measure {x | ¬ f x ≤ g x} := hb
        _ = 0 := by rw [hg1ae, hfg, add_zero]
    exact le_antisymm hle (Lebesgue_outer_measure.nonneg _)
  exact ⟨g1, hg1, htrans, rfl⟩

/-- Exercise 1.3.10(iii) (Homogeneity) -/
theorem LowerUnsignedLebesgueIntegral.hom {d:ℕ} {f: EuclideanSpace' d → EReal} (_hf: UnsignedMeasurable f) {c: ℝ} (hc: 0 ≤ c) :
    LowerUnsignedLebesgueIntegral ((c:EReal) • f) = c * LowerUnsignedLebesgueIntegral f := by
  unfold LowerUnsignedLebesgueIntegral
  have hzero_simple : UnsignedSimpleFunction (fun _ : EuclideanSpace' d => (0 : EReal)) := by
    use 0, (fun i : Fin 0 => (0 : EReal)), (fun i : Fin 0 => (∅ : Set (EuclideanSpace' d)))
    constructor
    · intro i; fin_cases i
    · ext x; simp
  have hzero_integ : hzero_simple.integ = 0 := zero_unsigned_integral hzero_simple
  apply le_antisymm
  · -- (≤): sSup(cS) ≤ c·sSup(S)
    apply sSup_le
    intro R hR
    rcases hR with ⟨g, hg, hg_cond⟩
    have hg_le : ∀ x, g x ≤ (c : EReal) • f x := fun x => (hg_cond x).1
    have hR_eq : R = hg.integ := (hg_cond (Classical.arbitrary _)).2
    rw [hR_eq]
    by_cases hc0 : c = 0
    · -- c = 0：g ≤ 0，g.integ ≤ 0 = c·sSup
      have hg0 : ∀ x, g x ≤ 0 := by
        intro x
        simpa [hc0, Pi.smul_apply, smul_eq_mul] using hg_le x
      have hg_integ_le : hg.integ ≤ 0 := by
        have hle := UnsignedSimpleFunction.integral_le_integral_of_aeLe hg hzero_simple (AlmostAlways.ofAlways hg0)
        simpa [hzero_integ] using hle
      simpa [hc0] using hg_integ_le
    · -- c > 0：g ≤ c•f ⟹ (1/c)•g ≤ f，则 g.integ ≤ c · sSup(S_f)
      have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
      have hcne : c ≠ 0 := hc0
      -- g' := (1/c) • g 简单函数
      let g' := ((1 / c : ℝ) : EReal) • g
      have hg'_simple : UnsignedSimpleFunction g' := by
        apply UnsignedSimpleFunction.smul (hg)
        exact EReal.coe_nonneg.mpr (one_div_nonneg.mpr (le_of_lt hcpos))
      have hg'_le_f : ∀ x, g' x ≤ f x := by
        intro x
        have hle := hg_le x
        -- 两边乘 1/c（正）
        have h1 : ((1 / c : ℝ) : EReal) * g x ≤ ((1 / c : ℝ) : EReal) * ((c : EReal) • f x) := by
          exact mul_le_mul_of_nonneg_left hle (EReal.coe_nonneg.mpr (one_div_nonneg.mpr (le_of_lt hcpos)))
        -- (1/c) * (c • f x) = f x（c > 0，EReal 中 1/c * c = 1）
        have h2 : ((1 / c : ℝ) : EReal) * ((c : EReal) • f x) = f x := by
          simp only [smul_eq_mul]
          rw [← mul_assoc]
          have h3 : ((1 / c : ℝ) : EReal) * (c : EReal) = 1 := by
            rw [← EReal.coe_mul]
            have h31 : (1 / c) * c = 1 := by rw [one_div, inv_mul_cancel₀ hcne]
            rw [h31, EReal.coe_one]
          rw [h3, one_mul]
        have hg'x : g' x = ((1 / c : ℝ) : EReal) * g x := rfl
        calc g' x = ((1 / c : ℝ) : EReal) * g x := hg'x
          _ ≤ ((1 / c : ℝ) : EReal) * ((c : EReal) • f x) := h1
          _ = f x := h2
      -- g.integ = c * g'.integ
      have hscale : hg.integ = (c : EReal) * hg'_simple.integ := by
        have hrev := UnsignedSimpleFunction.integral_smul hg'_simple (c := (c : EReal))
          (EReal.coe_nonneg.mpr hc)
        have hfun : (fun x => (c : EReal) • g' x) = g := by
          funext x
          simp [g', Pi.smul_apply, smul_eq_mul]
          rw [← mul_assoc]
          have h3 : (c : ℝ) * (c : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hcne
          rw [← EReal.coe_mul, h3, EReal.coe_one, one_mul]
        have hsame : (hg'_simple.smul (EReal.coe_nonneg.mpr hc)).integ = hg.integ := by
          apply UnsignedSimpleFunction.integral_eq_integral_of_aeEqual
            (hg'_simple.smul (EReal.coe_nonneg.mpr hc)) hg
          exact AlmostAlways.ofAlways (fun x => congrFun hfun x)
        exact hsame.symm.trans hrev
      -- c * g'.integ ≤ c * sSup(S_f)
      have hg'_in_set : hg'_simple.integ ∈ {R | ∃ g'' : EuclideanSpace' d → EReal, ∃ hg'' : UnsignedSimpleFunction g'', ∀ x, g'' x ≤ f x ∧ R = hg''.integ} := by
        exact ⟨g', hg'_simple, fun x => ⟨hg'_le_f x, rfl⟩⟩
      have hle_sup : hg'_simple.integ ≤ sSup {R | ∃ g'' : EuclideanSpace' d → EReal, ∃ hg'' : UnsignedSimpleFunction g'', ∀ x, g'' x ≤ f x ∧ R = hg''.integ} :=
        le_sSup hg'_in_set
      have hfinal : hg.integ ≤ (c : EReal) * sSup {R | ∃ g'' : EuclideanSpace' d → EReal, ∃ hg'' : UnsignedSimpleFunction g'', ∀ x, g'' x ≤ f x ∧ R = hg''.integ} := by
        rw [hscale]
        exact mul_le_mul_of_nonneg_left hle_sup (EReal.coe_nonneg.mpr hc)
      exact hfinal
  · -- (≥)：c·sSup(S) ≤ sSup(cS)
    by_cases hc0 : c = 0
    · -- c = 0：0 ∈ S'（零函数），故 0 ≤ sSup S'
      have hmem : (0 : EReal) ∈ {R | ∃ g : EuclideanSpace' d → EReal, ∃ hg : UnsignedSimpleFunction g, ∀ x, g x ≤ (c : EReal) • f x ∧ R = hg.integ} := by
        refine ⟨(fun _ : EuclideanSpace' d => (0 : EReal)), hzero_simple, ?_⟩
        intro x
        constructor
        · simp [hc0, smul_eq_mul]
        · exact hzero_integ.symm
      simpa [hc0] using (le_sSup hmem)
    · have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
      have hcne : c ≠ 0 := hc0
      have hc' : 0 ≤ ((1 / c : ℝ) : EReal) := EReal.coe_nonneg.mpr (one_div_nonneg.mpr (le_of_lt hcpos))
      -- 对 a ∈ S：c·a ≤ sSup(cS)（构造 c•g 简单函数）
      have hT : ∀ a ∈ {R | ∃ g : EuclideanSpace' d → EReal, ∃ hg : UnsignedSimpleFunction g, ∀ x, g x ≤ f x ∧ R = hg.integ},
          (c : EReal) * a ≤ sSup {R | ∃ g'' : EuclideanSpace' d → EReal, ∃ hg'' : UnsignedSimpleFunction g'', ∀ x, g'' x ≤ (c : EReal) • f x ∧ R = hg''.integ} := by
        intro a ha
        rcases ha with ⟨g, hg, hg_cond⟩
        have hg_le : ∀ x, g x ≤ f x := fun x => (hg_cond x).1
        have ha_eq : a = hg.integ := (hg_cond (Classical.arbitrary _)).2
        rw [ha_eq]
        have hcg_in : (c : EReal) * hg.integ ∈ {R | ∃ g'' : EuclideanSpace' d → EReal, ∃ hg'' : UnsignedSimpleFunction g'', ∀ x, g'' x ≤ (c : EReal) • f x ∧ R = hg''.integ} := by
          refine ⟨(c : EReal) • g, hg.smul (EReal.coe_nonneg.mpr hc), ?_⟩
          intro x
          constructor
          · exact mul_le_mul_of_nonneg_left (hg_le x) (EReal.coe_nonneg.mpr hc)
          · exact (UnsignedSimpleFunction.integral_smul hg (c := (c : EReal)) (EReal.coe_nonneg.mpr hc)).symm
        exact le_sSup hcg_in
      -- 反射：sSup S ≤ (1/c) · sSup S'
      have hS_le : sSup {R | ∃ g : EuclideanSpace' d → EReal, ∃ hg : UnsignedSimpleFunction g, ∀ x, g x ≤ f x ∧ R = hg.integ} ≤
          ((1 / c : ℝ) : EReal) * sSup {R | ∃ g'' : EuclideanSpace' d → EReal, ∃ hg'' : UnsignedSimpleFunction g'', ∀ x, g'' x ≤ (c : EReal) • f x ∧ R = hg''.integ} := by
        apply sSup_le
        intro a ha
        have hca := hT a ha
        calc a = ((1 / c : ℝ) : EReal) * ((c : EReal) * a) := by
              rw [← mul_assoc]
              have h31 : (1 / c) * c = 1 := by rw [one_div, inv_mul_cancel₀ hcne]
              rw [← EReal.coe_mul, h31, EReal.coe_one, one_mul]
          _ ≤ ((1 / c : ℝ) : EReal) * sSup {R | ∃ g'' : EuclideanSpace' d → EReal, ∃ hg'' : UnsignedSimpleFunction g'', ∀ x, g'' x ≤ (c : EReal) • f x ∧ R = hg''.integ} :=
              mul_le_mul_of_nonneg_left hca hc'
      calc (c : EReal) * sSup {R | ∃ g : EuclideanSpace' d → EReal, ∃ hg : UnsignedSimpleFunction g, ∀ x, g x ≤ f x ∧ R = hg.integ}
          ≤ (c : EReal) * (((1 / c : ℝ) : EReal) * sSup {R | ∃ g'' : EuclideanSpace' d → EReal, ∃ hg'' : UnsignedSimpleFunction g'', ∀ x, g'' x ≤ (c : EReal) • f x ∧ R = hg''.integ}) :=
              mul_le_mul_of_nonneg_left hS_le (EReal.coe_nonneg.mpr hc)
        _ = sSup {R | ∃ g'' : EuclideanSpace' d → EReal, ∃ hg'' : UnsignedSimpleFunction g'', ∀ x, g'' x ≤ (c : EReal) • f x ∧ R = hg''.integ} := by
          rw [← mul_assoc]
          have h32 : (c * (1 / c) : ℝ) = 1 := by rw [mul_one_div, div_self hcne]
          rw [← EReal.coe_mul, h32, EReal.coe_one, one_mul]

/-- Exercise 1.3.10(iv) (Equivalence) -/
theorem LowerUnsignedLebesgueIntegral.integral_eq_integral_of_aeEqual {d:ℕ} {f g: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) (hg: UnsignedMeasurable g)
    (heq: AlmostEverywhereEqual f g) :
    LowerUnsignedLebesgueIntegral f = LowerUnsignedLebesgueIntegral g := by
  apply le_antisymm
  · apply LowerUnsignedLebesgueIntegral.mono hf hg
    exact IsNull.subset heq (by intro x hx h; exact hx (le_of_eq h))
  · apply LowerUnsignedLebesgueIntegral.mono hg hf
    exact IsNull.subset heq (by intro x hx h; exact hx (le_of_eq h.symm))

/-- Notation bridge: element + set addition, i.e. the pointwise translation of a constant
    added to a set (this mathlib version only provides set+set addition). -/
private instance : HAdd EReal (Set EReal) (Set EReal) := ⟨fun a B => Set.image (fun b => a + b) B⟩

/-- Helper for superadditivity: adding a nonneg constant preserves the sSup of a nonneg set,
    using the monotone-continuous sSup preservation lemma plus continuity of EReal addition. -/
lemma add_sSup_nonneg {a : EReal} (ha : 0 ≤ a) {B : Set EReal} (hBne : B.Nonempty)
    (hB : B ⊆ {x | 0 ≤ x}) : a + sSup B = sSup (a + B) := by
  let f : EReal → EReal := fun x => a + x
  have hmono : Monotone f := by
    intro x y hxy
    exact add_le_add le_rfl hxy
  have hsB : 0 ≤ sSup B := by
    rcases hBne with ⟨b₀, hb₀⟩
    exact le_trans (hB hb₀) (le_sSup hb₀)
  have hcont : ContinuousAt f (sSup B) := by
    have h1 : a ≠ ⊤ ∨ sSup B ≠ ⊥ :=
      Or.inr (ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero hsB))
    have h2 : a ≠ ⊥ ∨ sSup B ≠ ⊤ :=
      Or.inl (ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero ha))
    simpa [f] using (EReal.continuousAt_add (p := (a, sSup B)) h1 h2).comp
      ((continuousAt_const (x := sSup B) (y := a)).prodMk continuousAt_id)
  have hbot : f ⊥ = ⊥ := by
    simp [f, EReal.add_bot]
  have himg : f '' B = a + B := rfl
  calc a + sSup B = f (sSup B) := rfl
    _ = sSup (f '' B) := Monotone.map_sSup_of_continuousAt hcont hmono hbot
    _ = sSup (a + B) := by rw [himg]

/-- EReal sup-additivity for nonneg nonempty sets: sSup A + sSup B ≤ sSup (A + B).
    The nonneg hypotheses are necessary — without them the claim is FALSE in EReal. -/
lemma sSup_add_le_sSup_sum {A B : Set EReal} (hA : A ⊆ {x | 0 ≤ x}) (hAne : A.Nonempty)
    (hB : B ⊆ {x | 0 ≤ x}) (hBne : B.Nonempty) :
    sSup A + sSup B ≤ sSup (A + B) := by
  have hsA : 0 ≤ sSup A := by
    rcases hAne with ⟨a₀, ha₀⟩
    exact le_trans (hA ha₀) (le_sSup ha₀)
  have hstep1 : sSup A + sSup B = sSup (sSup A + B) :=
    add_sSup_nonneg (a := sSup A) hsA hBne hB
  have hle : ∀ x ∈ sSup A + B, x ≤ sSup (A + B) := by
    intro x hx
    rcases hx with ⟨b, hb, hx_eq⟩
    have hb0 : 0 ≤ b := hB hb
    have hsing : sSup A + b ≤ sSup (b + A) := by
      rw [add_comm]
      exact le_of_eq (add_sSup_nonneg (a := b) hb0 hAne hA)
    have hsub' : b + A ⊆ A + B := by
      intro y hy
      rcases hy with ⟨a, ha, hsum⟩
      refine ⟨a, ha, b, hb, ?_⟩
      rw [← hsum]
      exact add_comm a b
    rw [← hx_eq]
    change sSup A + b ≤ sSup (A + B)
    exact le_trans hsing (sSup_le_sSup hsub')
  rw [hstep1]
  exact sSup_le hle

/-- Exercise 1.3.10(v) (Superadditivity) -/
theorem LowerUnsignedLebesgueIntegral.superadditive {d:ℕ} {f g: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) (hg: UnsignedMeasurable g) :
    LowerUnsignedLebesgueIntegral (f + g) ≥ LowerUnsignedLebesgueIntegral f + LowerUnsignedLebesgueIntegral g := by
  rw [LowerUnsignedLebesgueIntegral.eq hf.1, LowerUnsignedLebesgueIntegral.eq hg.1,
      LowerUnsignedLebesgueIntegral.eq (UnsignedMeasurable.add hf hg).1]
  let Sf : Set EReal := {R | ∃ g₁ : EuclideanSpace' d → EReal, ∃ hg₁ : UnsignedSimpleFunction g₁, AlmostAlways (fun x ↦ g₁ x ≤ f x) ∧ R = hg₁.integ}
  let Sg : Set EReal := {R | ∃ g₂ : EuclideanSpace' d → EReal, ∃ hg₂ : UnsignedSimpleFunction g₂, AlmostAlways (fun x ↦ g₂ x ≤ g x) ∧ R = hg₂.integ}
  let Sfg : Set EReal := {R | ∃ h : EuclideanSpace' d → EReal, ∃ hh : UnsignedSimpleFunction h, AlmostAlways (fun x ↦ h x ≤ (f + g) x) ∧ R = hh.integ}
  change sSup Sf + sSup Sg ≤ sSup Sfg
  let z : EuclideanSpace' d → EReal := fun _ => 0
  have hz : UnsignedSimpleFunction z := by
    use 0, (fun i : Fin 0 => (0 : EReal)), (fun i : Fin 0 => (∅ : Set (EuclideanSpace' d)))
    constructor
    · intro i; fin_cases i
    · ext x; simp [z]
  have hz_integ : hz.integ = 0 := zero_unsigned_integral hz
  have hSf_nonneg : Sf ⊆ {x | 0 ≤ x} := by
    intro R hR
    rcases hR with ⟨g₁, hg₁, _hg₁ae, rfl⟩
    have hle : hz.integ ≤ hg₁.integ :=
      UnsignedSimpleFunction.integral_le_integral_of_aeLe hz hg₁
        (AlmostAlways.ofAlways (fun x => (UnsignedSimpleFunction.unsignedMeasurable hg₁).1 x))
    simpa [hz_integ] using hle
  have hSg_nonneg : Sg ⊆ {x | 0 ≤ x} := by
    intro R hR
    rcases hR with ⟨g₂, hg₂, _hg₂ae, rfl⟩
    have hle : hz.integ ≤ hg₂.integ :=
      UnsignedSimpleFunction.integral_le_integral_of_aeLe hz hg₂
        (AlmostAlways.ofAlways (fun x => (UnsignedSimpleFunction.unsignedMeasurable hg₂).1 x))
    simpa [hz_integ] using hle
  have hSf_ne : Sf.Nonempty := ⟨0, ⟨z, hz, AlmostAlways.ofAlways (fun x => hf.1 x), hz_integ.symm⟩⟩
  have hSg_ne : Sg.Nonempty := ⟨0, ⟨z, hz, AlmostAlways.ofAlways (fun x => hg.1 x), hz_integ.symm⟩⟩
  have hsum_step : sSup Sf + sSup Sg ≤ sSup (Sf + Sg) :=
    sSup_add_le_sSup_sum hSf_nonneg hSf_ne hSg_nonneg hSg_ne
  have hsubset : Sf + Sg ⊆ Sfg := by
    intro x hx
    rcases hx with ⟨u, hu, v, hv, hsum⟩
    rcases hu with ⟨g₁, hg₁, hg₁ae, rfl⟩
    rcases hv with ⟨g₂, hg₂, hg₂ae, rfl⟩
    refine ⟨g₁ + g₂, UnsignedSimpleFunction.add hg₁ hg₂, ?_, ?_⟩
    · have hsum_ae : AlmostAlways (fun x => (g₁ + g₂) x ≤ (f + g) x) := by
        unfold AlmostAlways at *
        have hsub : {x | ¬ (g₁ + g₂) x ≤ (f + g) x} ⊆
            {x | ¬ g₁ x ≤ f x} ∪ {x | ¬ g₂ x ≤ g x} := by
          intro x hx
          by_contra h
          have h1 : g₁ x ≤ f x := by
            by_contra h1
            exact h (Or.inl h1)
          have h2 : g₂ x ≤ g x := by
            by_contra h2
            exact h (Or.inr h2)
          exact hx (add_le_add h1 h2)
        have hle : Lebesgue_outer_measure {x | ¬ (g₁ + g₂) x ≤ (f + g) x} ≤ 0 := by
          have hle1 : Lebesgue_outer_measure {x | ¬ (g₁ + g₂) x ≤ (f + g) x} ≤
              Lebesgue_outer_measure ({x | ¬ g₁ x ≤ f x} ∪ {x | ¬ g₂ x ≤ g x}) :=
            Lebesgue_outer_measure.mono hsub
          have hb : Lebesgue_outer_measure ({x | ¬ g₁ x ≤ f x} ∪ {x | ¬ g₂ x ≤ g x}) ≤
              Lebesgue_outer_measure {x | ¬ g₁ x ≤ f x} +
                Lebesgue_outer_measure {x | ¬ g₂ x ≤ g x} := by
            let E : Fin 2 → Set (EuclideanSpace' d) :=
              ![{x | ¬ g₁ x ≤ f x}, {x | ¬ g₂ x ≤ g x}]
            have h_union : {x | ¬ g₁ x ≤ f x} ∪ {x | ¬ g₂ x ≤ g x} = ⋃ i, E i := by
              ext y
              simp [E]
            have h_sum : (∑ i : Fin 2, Lebesgue_outer_measure (E i)) =
                Lebesgue_outer_measure {x | ¬ g₁ x ≤ f x} +
                  Lebesgue_outer_measure {x | ¬ g₂ x ≤ g x} := by
              simp [E, Fin.sum_univ_two]
            rw [h_union, ← h_sum]
            exact Lebesgue_outer_measure.finite_union_le E
          calc Lebesgue_outer_measure {x | ¬ (g₁ + g₂) x ≤ (f + g) x}
              ≤ Lebesgue_outer_measure ({x | ¬ g₁ x ≤ f x} ∪ {x | ¬ g₂ x ≤ g x}) := hle1
            _ ≤ Lebesgue_outer_measure {x | ¬ g₁ x ≤ f x} +
                Lebesgue_outer_measure {x | ¬ g₂ x ≤ g x} := hb
            _ = 0 := by rw [hg₁ae, hg₂ae, add_zero]
        exact le_antisymm hle (Lebesgue_outer_measure.nonneg _)
      exact hsum_ae
    · have hadd : (UnsignedSimpleFunction.add hg₁ hg₂).integ = hg₁.integ + hg₂.integ :=
        UnsignedSimpleFunction.integral_add hg₁ hg₂
      exact hsum.symm.trans hadd.symm
  exact le_trans hsum_step (sSup_le_sSup hsubset)

/-- Helper for subadditivity: adding a nonneg constant preserves the sInf of a nonneg set,
    the mirror of the sSup version via the monotone-continuous sInf preservation lemma. -/
lemma add_sInf_nonneg {a : EReal} (ha : 0 ≤ a) {B : Set EReal} (_hBne : B.Nonempty)
    (hB : B ⊆ {x | 0 ≤ x}) : a + sInf B = sInf (a + B) := by
  let f : EReal → EReal := fun x => a + x
  have hmono : Monotone f := by
    intro x y hxy
    exact add_le_add le_rfl hxy
  have hsB : 0 ≤ sInf B := by
    exact le_sInf (fun b hb => hB hb)
  have hcont : ContinuousAt f (sInf B) := by
    have h1 : a ≠ ⊤ ∨ sInf B ≠ ⊥ :=
      Or.inr (ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero hsB))
    have h2 : a ≠ ⊥ ∨ sInf B ≠ ⊤ :=
      Or.inl (ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero ha))
    simpa [f] using (EReal.continuousAt_add (p := (a, sInf B)) h1 h2).comp
      ((continuousAt_const (x := sInf B) (y := a)).prodMk continuousAt_id)
  have htop : f ⊤ = ⊤ := by
    simpa [f] using EReal.add_top_of_ne_bot (ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero ha))
  have himg : f '' B = a + B := rfl
  calc a + sInf B = f (sInf B) := rfl
    _ = sInf (f '' B) := Monotone.map_sInf_of_continuousAt hcont hmono htop
    _ = sInf (a + B) := by rw [himg]

/-- EReal inf-additivity for nonneg nonempty sets: sInf (A + B) ≤ sInf A + sInf B,
    the mirror of the sSup version using the one-sided sInf preservation lemma and
    the lower-bound characterization of sInf. -/
lemma sInf_sum_le_sInf_add {A B : Set EReal} (hA : A ⊆ {x | 0 ≤ x}) (hAne : A.Nonempty)
    (hB : B ⊆ {x | 0 ≤ x}) (hBne : B.Nonempty) :
    sInf (A + B) ≤ sInf A + sInf B := by
  have hsA : 0 ≤ sInf A := by
    exact le_sInf (fun a ha => hA ha)
  have hstep1 : sInf A + sInf B = sInf (sInf A + B) :=
    add_sInf_nonneg (a := sInf A) hsA hBne hB
  have hle : ∀ x ∈ sInf A + B, sInf (A + B) ≤ x := by
    intro x hx
    rcases hx with ⟨b, hb, hx_eq⟩
    have hb0 : 0 ≤ b := hB hb
    have hsing : sInf (A + B) ≤ b + sInf A := by
      have hsub' : b + A ⊆ A + B := by
        intro y hy
        rcases hy with ⟨a, ha, hsum⟩
        refine ⟨a, ha, b, hb, ?_⟩
        rw [← hsum]
        exact add_comm a b
      exact le_trans (sInf_le_sInf hsub')
        (le_of_eq (add_sInf_nonneg (a := b) hb0 hAne hA).symm)
    rw [← hx_eq]
    calc sInf (A + B) ≤ b + sInf A := hsing
      _ = sInf A + b := add_comm b (sInf A)
  rw [hstep1]
  exact le_sInf hle

/-- Exercise 1.3.10(vi) (Subadditivity of upper integral)-/
theorem UpperUnsignedLebesgueIntegral.subadditive {d:ℕ} {f g: EuclideanSpace' d → EReal} (_hf: UnsignedMeasurable f) (_hg: UnsignedMeasurable g) :
    UpperUnsignedLebesgueIntegral (f + g) ≤ UpperUnsignedLebesgueIntegral f + UpperUnsignedLebesgueIntegral g := by
  let Sf : Set EReal := {R | ∃ g₁ : EuclideanSpace' d → EReal, ∃ hg₁ : UnsignedSimpleFunction g₁, ∀ x, f x ≤ g₁ x ∧ R = hg₁.integ}
  let Sg : Set EReal := {R | ∃ g₂ : EuclideanSpace' d → EReal, ∃ hg₂ : UnsignedSimpleFunction g₂, ∀ x, g x ≤ g₂ x ∧ R = hg₂.integ}
  let Sfg : Set EReal := {R | ∃ h : EuclideanSpace' d → EReal, ∃ hh : UnsignedSimpleFunction h, ∀ x, (f + g) x ≤ h x ∧ R = hh.integ}
  change sInf Sfg ≤ sInf Sf + sInf Sg
  let z : EuclideanSpace' d → EReal := fun _ => 0
  have hz : UnsignedSimpleFunction z := by
    use 0, (fun i : Fin 0 => (0 : EReal)), (fun i : Fin 0 => (∅ : Set (EuclideanSpace' d)))
    constructor
    · intro i; fin_cases i
    · ext x; simp [z]
  have hz_integ : hz.integ = 0 := zero_unsigned_integral hz
  have hSf_nonneg : Sf ⊆ {x | 0 ≤ x} := by
    intro R hR
    rcases hR with ⟨g₁, hg₁, hcond₁⟩
    have hReq : R = hg₁.integ := by
      haveI : Nonempty (EuclideanSpace' d) := inferInstance
      exact (hcond₁ (Classical.arbitrary _)).2
    have hle : hz.integ ≤ hg₁.integ :=
      UnsignedSimpleFunction.integral_le_integral_of_aeLe hz hg₁
        (AlmostAlways.ofAlways (fun x => (UnsignedSimpleFunction.unsignedMeasurable hg₁).1 x))
    simpa [hz_integ, hReq] using hle
  have hSg_nonneg : Sg ⊆ {x | 0 ≤ x} := by
    intro R hR
    rcases hR with ⟨g₂, hg₂, hcond₂⟩
    have hReq : R = hg₂.integ := by
      haveI : Nonempty (EuclideanSpace' d) := inferInstance
      exact (hcond₂ (Classical.arbitrary _)).2
    have hle : hz.integ ≤ hg₂.integ :=
      UnsignedSimpleFunction.integral_le_integral_of_aeLe hz hg₂
        (AlmostAlways.ofAlways (fun x => (UnsignedSimpleFunction.unsignedMeasurable hg₂).1 x))
    simpa [hz_integ, hReq] using hle
  let t : EuclideanSpace' d → EReal := fun _ => ⊤
  have ht : UnsignedSimpleFunction t := by
    use 1, (fun i : Fin 1 => (⊤ : EReal)), (fun i : Fin 1 => (Set.univ : Set (EuclideanSpace' d)))
    constructor
    · intro i
      fin_cases i
      constructor
      · exact IsOpen.measurable isOpen_univ
      · exact le_top
    · ext x
      simp [t, EReal.indicator, Real.EReal_fun]
  have hSf_ne : Sf.Nonempty := ⟨ht.integ, ⟨t, ht, fun x => ⟨le_top, rfl⟩⟩⟩
  have hSg_ne : Sg.Nonempty := ⟨ht.integ, ⟨t, ht, fun x => ⟨le_top, rfl⟩⟩⟩
  have hsum_step : sInf (Sf + Sg) ≤ sInf Sf + sInf Sg :=
    sInf_sum_le_sInf_add hSf_nonneg hSf_ne hSg_nonneg hSg_ne
  have hsubset : Sf + Sg ⊆ Sfg := by
    intro x hx
    rcases hx with ⟨u, hu, v, hv, hsum⟩
    rcases hu with ⟨g₁, hg₁, hcond₁⟩
    rcases hv with ⟨g₂, hg₂, hcond₂⟩
    have hu_req : u = hg₁.integ := by
      haveI : Nonempty (EuclideanSpace' d) := inferInstance
      exact (hcond₁ (Classical.arbitrary _)).2
    have hv_req : v = hg₂.integ := by
      haveI : Nonempty (EuclideanSpace' d) := inferInstance
      exact (hcond₂ (Classical.arbitrary _)).2
    subst u
    subst v
    refine ⟨g₁ + g₂, UnsignedSimpleFunction.add hg₁ hg₂, ?_⟩
    intro y
    constructor
    · exact add_le_add (hcond₁ y).1 (hcond₂ y).1
    · exact hsum.symm.trans (UnsignedSimpleFunction.integral_add hg₁ hg₂).symm
  exact le_trans (sInf_le_sInf hsubset) hsum_step

/-- Indicator values are nonnegative reals lifted to EReal. -/
private lemma ind_nonneg {d : ℕ} (E₀ : Set (EuclideanSpace' d)) (x : EuclideanSpace' d) :
    0 ≤ Real.toEReal (E₀.indicator' x) := by
  by_cases hx : x ∈ E₀
  · rw [Set.indicator'_of_mem hx, EReal.coe_one]
    exact zero_le_one
  · rw [Set.indicator'_of_notMem hx, EReal.coe_zero]

/-- The indicators of a set and its complement sum to one pointwise. -/
private lemma ind_sum_eq_one {d : ℕ} (f : EuclideanSpace' d → EReal) {E₀ : Set (EuclideanSpace' d)}
    (x : EuclideanSpace' d) :
    (f * Real.toEReal ∘ E₀.indicator') x + (f * Real.toEReal ∘ E₀ᶜ.indicator') x = f x := by
  simp only [Pi.mul_apply, Function.comp_apply]
  by_cases hx : x ∈ E₀
  · rw [Set.indicator'_of_mem hx, Set.indicator'_of_notMem (by simpa using hx),
      EReal.coe_one, EReal.coe_zero, mul_one, mul_zero, add_zero]
  · rw [Set.indicator'_of_notMem hx, Set.indicator'_of_mem ((Set.mem_compl_iff E₀ x).mpr hx),
      EReal.coe_zero, EReal.coe_one, mul_zero, mul_one, zero_add]

/-- Sup of a sumset is at most the sum of the suprema. -/
private lemma sSup_sum_le_sSup_add {A B : Set EReal} :
    sSup (A + B) ≤ sSup A + sSup B := by
  apply sSup_le
  intro x hx
  rcases hx with ⟨a, ha, b, hb, rfl⟩
  exact add_le_add (le_sSup ha) (le_sSup hb)

/-- Helper 1: multiplying a simple function by the indicator of a measurable set stays simple.
    Copy the proof pattern from the eq theorem in the real file. -/
lemma simple_mul_indicator {d : ℕ} {g : EuclideanSpace' d → EReal} (hg : UnsignedSimpleFunction g)
    {E₀ : Set (EuclideanSpace' d)} (hE₀ : LebesgueMeasurable E₀) :
    UnsignedSimpleFunction (g * Real.toEReal ∘ E₀.indicator') := by
  obtain ⟨k, c, E, ⟨hcE, hg_eq⟩⟩ := hg
  use k, c, (fun i => E i ∩ E₀)
  constructor
  · intro i
    constructor
    · exact LebesgueMeasurable.inter (hcE i).1 hE₀
    · exact (hcE i).2
  · funext x
    simp only [hg_eq, EReal.indicator, Function.comp_apply, Pi.mul_apply]
    conv_lhs => rw [Finset.sum_fn]; simp only [Pi.smul_apply]
    conv_rhs => rw [Finset.sum_fn]; simp only [Pi.smul_apply]
    by_cases hx : x ∈ E₀
    · rw [Set.indicator'_of_mem hx, EReal.coe_one, mul_one]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Real.EReal_fun]
      by_cases hEi : x ∈ E i
      · rw [Set.indicator'_of_mem hEi, Set.indicator'_of_mem (Set.mem_inter hEi hx)]
      · have hnotinter : x ∉ E i ∩ E₀ := fun h => hEi (Set.mem_of_mem_inter_left h)
        rw [Set.indicator'_of_notMem hEi, Set.indicator'_of_notMem hnotinter]
    · rw [Set.indicator'_of_notMem hx, EReal.coe_zero, mul_zero]
      symm
      apply Finset.sum_eq_zero
      intro i _
      have hnotinter : x ∉ E i ∩ E₀ := fun h => hx (Set.mem_of_mem_inter_right h)
      simp only [Real.EReal_fun, Set.indicator'_of_notMem hnotinter, EReal.coe_zero, smul_zero]

/-- Helper 2: for g simple and E measurable, the integral splits across E and its complement.
    Route: pointwise g times one-E plus g times one-complement equals g, then
    integral additivity plus invariance under almost-equal functions. -/
lemma integral_split {d : ℕ} {g : EuclideanSpace' d → EReal} (hg : UnsignedSimpleFunction g)
    {E₀ : Set (EuclideanSpace' d)} (hE₀ : LebesgueMeasurable E₀) :
    hg.integ =
      (simple_mul_indicator hg hE₀).integ + (simple_mul_indicator hg (LebesgueMeasurable.complement hE₀)).integ := by
  have hsum_simple : UnsignedSimpleFunction
      (g * Real.toEReal ∘ E₀.indicator' + g * Real.toEReal ∘ E₀ᶜ.indicator') :=
    UnsignedSimpleFunction.add (simple_mul_indicator hg hE₀)
      (simple_mul_indicator hg (LebesgueMeasurable.complement hE₀))
  have hpt : ∀ x, (g * Real.toEReal ∘ E₀.indicator' + g * Real.toEReal ∘ E₀ᶜ.indicator') x = g x := by
    intro x
    simpa [Pi.add_apply] using ind_sum_eq_one g x
  have hsame : hsum_simple.integ = hg.integ :=
    UnsignedSimpleFunction.integral_eq_integral_of_aeEqual hsum_simple hg (AlmostAlways.ofAlways hpt)
  have hadd : hsum_simple.integ =
      (simple_mul_indicator hg hE₀).integ + (simple_mul_indicator hg (LebesgueMeasurable.complement hE₀)).integ :=
    UnsignedSimpleFunction.integral_add (simple_mul_indicator hg hE₀)
      (simple_mul_indicator hg (LebesgueMeasurable.complement hE₀))
  rw [← hsame, hadd]

/-- Helper 3a: if g is at most f almost everywhere, then g times the indicator is at most
    f times the indicator almost everywhere.  Null-set argument with the nonnegative indicator. -/
lemma ae_mul_indicator_le {d : ℕ} {g f : EuclideanSpace' d → EReal}
    {E₀ : Set (EuclideanSpace' d)} (hae : AlmostAlways (fun x => g x ≤ f x)) :
    AlmostAlways (fun x => (g * Real.toEReal ∘ E₀.indicator') x ≤ (f * Real.toEReal ∘ E₀.indicator') x) := by
  unfold AlmostAlways at *
  have hsub : {x | ¬ (g * Real.toEReal ∘ E₀.indicator') x ≤ (f * Real.toEReal ∘ E₀.indicator') x} ⊆
      {x | ¬ g x ≤ f x} := by
    intro x hx
    by_contra h
    have hgx : g x ≤ f x := by simpa using h
    have hle : (g * Real.toEReal ∘ E₀.indicator') x ≤ (f * Real.toEReal ∘ E₀.indicator') x := by
      simpa [Pi.mul_apply, Function.comp_apply] using
        (mul_le_mul_of_nonneg_right hgx (ind_nonneg E₀ x))
    exact hx hle
  have hle : Lebesgue_outer_measure
      {x | ¬ (g * Real.toEReal ∘ E₀.indicator') x ≤ (f * Real.toEReal ∘ E₀.indicator') x} ≤ 0 := by
    calc Lebesgue_outer_measure
          {x | ¬ (g * Real.toEReal ∘ E₀.indicator') x ≤ (f * Real.toEReal ∘ E₀.indicator') x}
        ≤ Lebesgue_outer_measure {x | ¬ g x ≤ f x} := Lebesgue_outer_measure.mono hsub
      _ = 0 := hae
  exact le_antisymm hle (Lebesgue_outer_measure.nonneg _)

/-- Helper 3b: g₁ ≤ f·1_E a.e. and g₂ ≤ f·1_Eᶜ a.e. imply g₁ + g₂ ≤ f a.e.
    Pointwise: g₁ x + g₂ x ≤ f x·1_E(x) + f x·1_Eᶜ(x) = f x.
    Null-set union argument like in the mono proof of the real file. -/
lemma ae_add_le_of_split {d : ℕ} {g₁ g₂ f : EuclideanSpace' d → EReal}
    {E₀ : Set (EuclideanSpace' d)} (h₁ : AlmostAlways (fun x => g₁ x ≤ (f * Real.toEReal ∘ E₀.indicator') x))
    (h₂ : AlmostAlways (fun x => g₂ x ≤ (f * Real.toEReal ∘ E₀ᶜ.indicator') x)) :
    AlmostAlways (fun x => g₁ x + g₂ x ≤ f x) := by
  unfold AlmostAlways at *
  have hsub : {x | ¬ g₁ x + g₂ x ≤ f x} ⊆
      {x | ¬ g₁ x ≤ (f * Real.toEReal ∘ E₀.indicator') x} ∪
        {x | ¬ g₂ x ≤ (f * Real.toEReal ∘ E₀ᶜ.indicator') x} := by
    intro x hx
    by_contra h
    have h1 : g₁ x ≤ (f * Real.toEReal ∘ E₀.indicator') x := by
      by_contra h1
      exact h (Or.inl h1)
    have h2 : g₂ x ≤ (f * Real.toEReal ∘ E₀ᶜ.indicator') x := by
      by_contra h2
      exact h (Or.inr h2)
    exact hx ((add_le_add h1 h2).trans_eq (ind_sum_eq_one f x))
  have hle : Lebesgue_outer_measure {x | ¬ g₁ x + g₂ x ≤ f x} ≤ 0 := by
    have hle1 : Lebesgue_outer_measure {x | ¬ g₁ x + g₂ x ≤ f x} ≤
        Lebesgue_outer_measure ({x | ¬ g₁ x ≤ (f * Real.toEReal ∘ E₀.indicator') x} ∪
          {x | ¬ g₂ x ≤ (f * Real.toEReal ∘ E₀ᶜ.indicator') x}) :=
      Lebesgue_outer_measure.mono hsub
    have hb : Lebesgue_outer_measure ({x | ¬ g₁ x ≤ (f * Real.toEReal ∘ E₀.indicator') x} ∪
          {x | ¬ g₂ x ≤ (f * Real.toEReal ∘ E₀ᶜ.indicator') x}) ≤
        Lebesgue_outer_measure {x | ¬ g₁ x ≤ (f * Real.toEReal ∘ E₀.indicator') x} +
          Lebesgue_outer_measure {x | ¬ g₂ x ≤ (f * Real.toEReal ∘ E₀ᶜ.indicator') x} := by
      let E : Fin 2 → Set (EuclideanSpace' d) :=
        ![{x | ¬ g₁ x ≤ (f * Real.toEReal ∘ E₀.indicator') x},
          {x | ¬ g₂ x ≤ (f * Real.toEReal ∘ E₀ᶜ.indicator') x}]
      have h_union : {x | ¬ g₁ x ≤ (f * Real.toEReal ∘ E₀.indicator') x} ∪
            {x | ¬ g₂ x ≤ (f * Real.toEReal ∘ E₀ᶜ.indicator') x} = ⋃ i, E i := by
        ext y
        simp [E]
      have h_sum : (∑ i : Fin 2, Lebesgue_outer_measure (E i)) =
          Lebesgue_outer_measure {x | ¬ g₁ x ≤ (f * Real.toEReal ∘ E₀.indicator') x} +
            Lebesgue_outer_measure {x | ¬ g₂ x ≤ (f * Real.toEReal ∘ E₀ᶜ.indicator') x} := by
        simp [E, Fin.sum_univ_two]
      rw [h_union, ← h_sum]
      exact Lebesgue_outer_measure.finite_union_le E
    calc Lebesgue_outer_measure {x | ¬ g₁ x + g₂ x ≤ f x}
        ≤ Lebesgue_outer_measure ({x | ¬ g₁ x ≤ (f * Real.toEReal ∘ E₀.indicator') x} ∪
            {x | ¬ g₂ x ≤ (f * Real.toEReal ∘ E₀ᶜ.indicator') x}) := hle1
      _ ≤ Lebesgue_outer_measure {x | ¬ g₁ x ≤ (f * Real.toEReal ∘ E₀.indicator') x} +
          Lebesgue_outer_measure {x | ¬ g₂ x ≤ (f * Real.toEReal ∘ E₀ᶜ.indicator') x} := hb
      _ = 0 := by rw [h₁, h₂, add_zero]
  exact le_antisymm hle (Lebesgue_outer_measure.nonneg _)

/-- Exercise 1.3.10(vii) (Divisibility) -/
theorem LowerUnsignedLebesgueIntegral.eq_add {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) {E: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) :
    LowerUnsignedLebesgueIntegral f = LowerUnsignedLebesgueIntegral (f * Real.toEReal ∘ E.indicator') +
      LowerUnsignedLebesgueIntegral (f * Real.toEReal ∘ Eᶜ.indicator') := by
  have hfE : ∀ x, 0 ≤ (f * Real.toEReal ∘ E.indicator') x := by
    intro x
    simpa [Pi.mul_apply, Function.comp_apply] using mul_nonneg (hf.1 x) (ind_nonneg E x)
  have hfEc : ∀ x, 0 ≤ (f * Real.toEReal ∘ Eᶜ.indicator') x := by
    intro x
    simpa [Pi.mul_apply, Function.comp_apply] using mul_nonneg (hf.1 x) (ind_nonneg Eᶜ x)
  rw [LowerUnsignedLebesgueIntegral.eq hf.1, LowerUnsignedLebesgueIntegral.eq hfE,
      LowerUnsignedLebesgueIntegral.eq hfEc]
  let Sf : Set EReal := {R | ∃ g, ∃ hg : UnsignedSimpleFunction g,
    AlmostAlways (fun x => g x ≤ f x) ∧ R = hg.integ}
  let SE : Set EReal := {R | ∃ g, ∃ hg : UnsignedSimpleFunction g,
    AlmostAlways (fun x => g x ≤ (f * Real.toEReal ∘ E.indicator') x) ∧ R = hg.integ}
  let SEc : Set EReal := {R | ∃ g, ∃ hg : UnsignedSimpleFunction g,
    AlmostAlways (fun x => g x ≤ (f * Real.toEReal ∘ Eᶜ.indicator') x) ∧ R = hg.integ}
  change sSup Sf = sSup SE + sSup SEc
  let z : EuclideanSpace' d → EReal := fun _ => 0
  have hz : UnsignedSimpleFunction z := by
    use 0, (fun i : Fin 0 => (0 : EReal)), (fun i : Fin 0 => (∅ : Set (EuclideanSpace' d)))
    constructor
    · intro i; fin_cases i
    · ext x; simp [z]
  have hz_integ : hz.integ = 0 := zero_unsigned_integral hz
  have hSE_nonneg : SE ⊆ {x | 0 ≤ x} := by
    intro R hR
    rcases hR with ⟨g, hg, _hae, rfl⟩
    have hle : hz.integ ≤ hg.integ :=
      UnsignedSimpleFunction.integral_le_integral_of_aeLe hz hg
        (AlmostAlways.ofAlways (fun x => (UnsignedSimpleFunction.unsignedMeasurable hg).1 x))
    simpa [hz_integ] using hle
  have hSEc_nonneg : SEc ⊆ {x | 0 ≤ x} := by
    intro R hR
    rcases hR with ⟨g, hg, _hae, rfl⟩
    have hle : hz.integ ≤ hg.integ :=
      UnsignedSimpleFunction.integral_le_integral_of_aeLe hz hg
        (AlmostAlways.ofAlways (fun x => (UnsignedSimpleFunction.unsignedMeasurable hg).1 x))
    simpa [hz_integ] using hle
  have hSE_ne : SE.Nonempty := ⟨0, ⟨z, hz, AlmostAlways.ofAlways hfE, hz_integ.symm⟩⟩
  have hSEc_ne : SEc.Nonempty := ⟨0, ⟨z, hz, AlmostAlways.ofAlways hfEc, hz_integ.symm⟩⟩
  have hsubset1 : Sf ⊆ SE + SEc := by
    intro R hR
    rcases hR with ⟨g, hg, hgae, rfl⟩
    refine ⟨(simple_mul_indicator hg hE).integ, ?_, (simple_mul_indicator hg (LebesgueMeasurable.complement hE)).integ, ?_, ?_⟩
    · exact ⟨g * Real.toEReal ∘ E.indicator', simple_mul_indicator hg hE,
        ae_mul_indicator_le (E₀ := E) hgae, rfl⟩
    · exact ⟨g * Real.toEReal ∘ Eᶜ.indicator', simple_mul_indicator hg (LebesgueMeasurable.complement hE),
        ae_mul_indicator_le (E₀ := Eᶜ) hgae, rfl⟩
    · exact (integral_split hg hE).symm
  have hle : sSup Sf ≤ sSup SE + sSup SEc :=
    le_trans (sSup_le_sSup hsubset1) (sSup_sum_le_sSup_add (A := SE) (B := SEc))
  have hsubset2 : SE + SEc ⊆ Sf := by
    intro x hx
    rcases hx with ⟨u, hu, v, hv, hsum⟩
    rcases hu with ⟨g₁, hg₁, hg₁ae, rfl⟩
    rcases hv with ⟨g₂, hg₂, hg₂ae, rfl⟩
    refine ⟨g₁ + g₂, UnsignedSimpleFunction.add hg₁ hg₂, ?_, ?_⟩
    · exact ae_add_le_of_split (E₀ := E) hg₁ae hg₂ae
    · exact hsum.symm.trans (UnsignedSimpleFunction.integral_add hg₁ hg₂).symm
  have hge : sSup SE + sSup SEc ≤ sSup Sf :=
    le_trans (sSup_add_le_sSup_sum hSE_nonneg hSE_ne hSEc_nonneg hSEc_ne) (sSup_le_sSup hsubset2)
  exact le_antisymm hle hge

/-- min with the constant n (as EReal) converges to the value itself. -/
lemma tendsto_min_nat {c : EReal} : Tendsto (fun n : ℕ => min c (n : ℝ)) atTop (𝓝 c) := by
  have hseq : Tendsto (fun n : ℕ => ((n : ℝ) : EReal)) atTop (𝓝 (⊤ : EReal)) := by
    exact (EReal.tendsto_coe_nhds_top_iff).2 tendsto_natCast_atTop_atTop
  have hcst : Continuous (fun x : EReal => min c x) := by
    simpa using (Continuous.min continuous_const continuous_id : Continuous (fun x : EReal => min c x))
  have hmain : Tendsto (fun n : ℕ => min c ((n : ℝ) : EReal)) atTop (𝓝 (min c (⊤ : EReal))) :=
    hcst.continuousAt.tendsto.comp hseq
  convert hmain using 1
  exact congrArg nhds (min_eq_left le_top).symm

/-- min with n times m converges to c times m for nonnegative c and m. -/
lemma tendsto_min_mul {c m : EReal} (hc : 0 ≤ c) (hm : 0 ≤ m) :
    Tendsto (fun n : ℕ => min c (n : ℝ) * m) atTop (𝓝 (c * m)) := by
  by_cases h₁ : c = 0 ∧ m = ⊤
  · rcases h₁ with ⟨hc0, hmt⟩
    subst c
    subst m
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [] with n
    simp
  · by_cases h₂ : c = ⊤ ∧ m = 0
    · rcases h₂ with ⟨hct, hm0⟩
      subst c
      subst m
      apply tendsto_nhds_of_eventually_eq
      filter_upwards [] with n
      simp
    · apply EReal.Tendsto.mul_const
      · exact tendsto_min_nat (c := c)
      · exact Or.inr ((lt_of_lt_of_le EReal.bot_lt_zero hm).ne')
      · by_cases hmt : m = ⊤
        · left
          intro hc0
          exact h₁ ⟨hc0, hmt⟩
        · exact Or.inr hmt

/-- Pointwise identity: the vertical truncation of a simple function equals the atom sum
    with min-truncated coefficients (atoms refine the representation of g). -/
lemma min_eq_sum_atomValueEReal {d : ℕ} {g : EuclideanSpace' d → EReal} (hg : UnsignedSimpleFunction g)
    (n : ℕ) :
    (fun x => min (g x) n) = ∑ n' : Fin (2^(hg.choose + hg.choose)),
      min (atomValueEReal hg.choose_spec.choose n'.val) (n : ℝ) •
        EReal.indicator (atom hg.choose_spec.choose_spec.choose hg.choose_spec.choose_spec.choose n') := by
  let k := hg.choose
  let c := hg.choose_spec.choose
  let E := hg.choose_spec.choose_spec.choose
  have hmes : ∀ i, LebesgueMeasurable (E i) ∧ c i ≥ 0 := hg.choose_spec.choose_spec.choose_spec.1
  have heq : g = ∑ i, (c i) • (EReal.indicator (E i)) := hg.choose_spec.choose_spec.choose_spec.2
  let A : Fin (2^(k+k)) → Set (EuclideanSpace' d) := atom E E
  funext x
  let n0 : Fin (2^(k+k)) := ⟨atomIndexOf E E x, atomIndexOf_lt E E x⟩
  have hx_mem : x ∈ A n0 := by
    simp only [A, atom, Set.mem_setOf_eq, n0]
    refine ⟨fun j => ?_, fun j => ?_⟩
    · rw [atomMembership_eq_testBit, atomIndexOf_testBit_E E E x j]
    · rw [atomMembership_eq_testBit, atomIndexOf_testBit_E' E E x j]
  have hunique : ∀ m : Fin (2^(k+k)), x ∈ A m → m = n0 := by
    intro m hm
    by_contra hne
    have hdisj : Disjoint (A m) (A n0) := by
      simpa [A] using atom_pairwiseDisjoint E E (by simp) (by simp) hne
    exact (Set.disjoint_left.mp hdisj) hm hx_mem
  have hgx : g x = atomValueEReal c n0.val := by
    exact (congrFun heq x).trans (by
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
        (sum_indicator_eq_atomValueEReal c E E n0 x hx_mem))
  have hrhs : (∑ n' : Fin (2^(k+k)), min (atomValueEReal c n'.val) ((n : ℝ) : EReal) * EReal.indicator (A n') x) =
      min (atomValueEReal c n0.val) ((n : ℝ) : EReal) := by
    rw [Finset.sum_eq_single n0]
    · simp only [EReal.indicator_of_mem hx_mem, mul_one]
    · intro m _ hm_ne
      have hx_notin : x ∉ A m := fun h => hm_ne (hunique m h)
      simp only [EReal.indicator_of_notMem hx_notin, mul_zero]
    · intro h; exact absurd (Finset.mem_univ n0) h
  rw [hgx]
  simpa [A, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hrhs.symm

/-- Helper 1: vertical truncation of a simple function is simple (min with a constant). -/
lemma simple_min_const {d : ℕ} {g : EuclideanSpace' d → EReal} (hg : UnsignedSimpleFunction g) (n : ℕ) :
    UnsignedSimpleFunction (fun x => min (g x) n) := by
  use 2^(hg.choose + hg.choose),
    (fun n' : Fin (2^(hg.choose + hg.choose)) => min (atomValueEReal hg.choose_spec.choose n'.val) (n : ℝ)),
    (atom hg.choose_spec.choose_spec.choose hg.choose_spec.choose_spec.choose)
  constructor
  · intro i
    constructor
    · exact atom_measurable (fun i => (hg.choose_spec.choose_spec.choose_spec.1 i).1)
        (fun j => (hg.choose_spec.choose_spec.choose_spec.1 j).1) i
    · exact le_min (atomValueEReal_nonneg (fun i => (hg.choose_spec.choose_spec.choose_spec.1 i).2) i.val)
        (EReal.coe_nonneg.mpr (Nat.cast_nonneg n))
  · exact min_eq_sum_atomValueEReal hg n

/-- Helper 2: the integral of the truncated simple function, computed on the atoms. -/
lemma integral_min_const {d : ℕ} {g : EuclideanSpace' d → EReal} (hg : UnsignedSimpleFunction g) (n : ℕ) :
    (simple_min_const hg n).integ = ∑ n' : Fin (2^(hg.choose + hg.choose)),
      min (atomValueEReal hg.choose_spec.choose n'.val) (n : ℝ) *
        Lebesgue_measure (atom hg.choose_spec.choose_spec.choose hg.choose_spec.choose_spec.choose n') := by
  rw [UnsignedSimpleFunction.integral_eq (simple_min_const hg n) (k := 2^(hg.choose + hg.choose))
    (c := fun n' : Fin (2^(hg.choose + hg.choose)) => min (atomValueEReal hg.choose_spec.choose n'.val) (n : ℝ))
    (E := atom hg.choose_spec.choose_spec.choose hg.choose_spec.choose_spec.choose)
    (hmes := fun i => atom_measurable (fun i => (hg.choose_spec.choose_spec.choose_spec.1 i).1)
        (fun j => (hg.choose_spec.choose_spec.choose_spec.1 j).1) i)
    (hnonneg := fun i => le_min (atomValueEReal_nonneg (fun j => (hg.choose_spec.choose_spec.choose_spec.1 j).2) i.val)
        (EReal.coe_nonneg.mpr (Nat.cast_nonneg n)))
    (heq := min_eq_sum_atomValueEReal hg n)]

/-- Finite sum of pointwise converging nonnegative sequences converges to the sum of limits.
    EReal addition is only continuous away from (bottom, top) and (top, bottom), which never
    occur here because every limit is nonnegative. -/
lemma tendsto_sum_of_nonneg {α : Type*} (s : Finset α) {f : α → ℕ → EReal} {a : α → EReal}
    (hf : ∀ i ∈ s, Tendsto (f i) atTop (𝓝 (a i))) (ha : ∀ i ∈ s, 0 ≤ a i) :
    Tendsto (fun n => ∑ i ∈ s, f i n) atTop (𝓝 (∑ i ∈ s, a i)) := by
  classical
  have hmain : ∀ t : Finset α, t ⊆ s →
      Tendsto (fun n => ∑ i ∈ t, f i n) atTop (𝓝 (∑ i ∈ t, a i)) := by
    intro t
    refine Finset.induction_on t ?_ ?_
    · intro _
      simp
    · intro i t' hit' ih hts
      have hfi : Tendsto (f i) atTop (𝓝 (a i)) := hf i (hts (Finset.mem_insert_self i t'))
      have hsum0 : 0 ≤ ∑ j ∈ t', a j := Finset.sum_nonneg (fun j hj => ha j (hts (Finset.mem_insert_of_mem hj)))
      have hcont : ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (a i, ∑ j ∈ t', a j) := by
        apply EReal.continuousAt_add
        · exact Or.inr ((lt_of_lt_of_le EReal.bot_lt_zero hsum0).ne')
        · exact Or.inl ((lt_of_lt_of_le EReal.bot_lt_zero (ha i (hts (Finset.mem_insert_self i t')))).ne')
      have h : Tendsto (fun n => f i n + ∑ j ∈ t', f j n) atTop (𝓝 (a i + ∑ j ∈ t', a j)) :=
        hcont.tendsto.comp (hfi.prodMk_nhds (ih ((Finset.subset_insert i t').trans hts)))
      simpa [Finset.sum_insert hit'] using h
  exact hmain s (Finset.Subset.refl s)

/-- Helper 3: the integral of the truncation converges to the integral (simple MCT). -/
lemma integral_limit {d : ℕ} {g : EuclideanSpace' d → EReal} (hg : UnsignedSimpleFunction g) :
    Tendsto (fun n : ℕ => (simple_min_const hg n).integ) atTop (𝓝 (hg.integ)) := by
  let k := hg.choose
  let c := hg.choose_spec.choose
  let E := hg.choose_spec.choose_spec.choose
  have hmes : ∀ i, LebesgueMeasurable (E i) ∧ c i ≥ 0 := hg.choose_spec.choose_spec.choose_spec.1
  have heq : g = ∑ i, (c i) • (EReal.indicator (E i)) := hg.choose_spec.choose_spec.choose_spec.2
  let A : Fin (2^(k+k)) → Set (EuclideanSpace' d) := atom E E
  have hA_mes : ∀ n, LebesgueMeasurable (A n) := by
    intro n
    simpa [A] using atom_measurable (fun i => (hmes i).1) (fun j => (hmes j).1) n
  have hsum_conv : Tendsto (fun n : ℕ =>
      ∑ n' : Fin (2^(k+k)), min (atomValueEReal c n'.val) ((n : ℝ) : EReal) * Lebesgue_measure (A n'))
      atTop (𝓝 (∑ n' : Fin (2^(k+k)), atomValueEReal c n'.val * Lebesgue_measure (A n'))) := by
    simpa using tendsto_sum_of_nonneg (s := (Finset.univ : Finset (Fin (2^(k+k)))))
      (f := fun (n' : Fin (2^(k+k))) (n : ℕ) => min (atomValueEReal c n'.val) ((n : ℝ) : EReal) * Lebesgue_measure (A n'))
      (a := fun n' : Fin (2^(k+k)) => atomValueEReal c n'.val * Lebesgue_measure (A n'))
      (hf := fun n' _ => tendsto_min_mul (atomValueEReal_nonneg (fun i => (hmes i).2) n'.val)
        (Lebesgue_outer_measure.nonneg (A n')))
      (ha := fun n' _ => mul_nonneg (atomValueEReal_nonneg (fun i => (hmes i).2) n'.val)
        (Lebesgue_outer_measure.nonneg (A n')))
  have hg_integ : hg.integ = ∑ n' : Fin (2^(k+k)), atomValueEReal c n'.val * Lebesgue_measure (A n') := by
    rw [UnsignedSimpleFunction.integral_eq hg (k := 2^(k+k))
      (c := fun n' : Fin (2^(k+k)) => atomValueEReal c n'.val) (E := A)
      (hmes := hA_mes) (hnonneg := fun n' => atomValueEReal_nonneg (fun i => (hmes i).2) n'.val)
      (heq := heq.trans (by simpa [A] using eq_sum_atomValueEReal_indicator c E E))]
  have h_n_integ : ∀ n : ℕ, (simple_min_const hg n).integ =
      ∑ n' : Fin (2^(k+k)), min (atomValueEReal c n'.val) ((n : ℝ) : EReal) * Lebesgue_measure (A n') := by
    intro n
    simpa [k, c, E, A] using integral_min_const hg n
  have hmain : Tendsto (fun n : ℕ => (simple_min_const hg n).integ) atTop
      (𝓝 (∑ n' : Fin (2^(k+k)), atomValueEReal c n'.val * Lebesgue_measure (A n'))) :=
    hsum_conv.congr (fun n => (h_n_integ n).symm)
  rw [hg_integ]
  exact hmain

/-- Exercise 1.3.10(viii) (Vertical truncation)-/
theorem LowerUnsignedLebesgueIntegral.eq_lim_vert_trunc {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) : Filter.atTop.Tendsto (fun n:ℕ ↦ LowerUnsignedLebesgueIntegral (fun x ↦ min (f x) n)) (nhds (LowerUnsignedLebesgueIntegral f)) := by
  let fn : ℕ → EuclideanSpace' d → EReal := fun n x => min (f x) n
  have hfn_meas : ∀ n, UnsignedMeasurable (fn n) := by
    intro n
    have hφ : Continuous (fun y : EReal => min y ((n : ℝ) : EReal)) := by
      simpa using (Continuous.min continuous_id continuous_const : Continuous (fun y : EReal => min y ((n : ℝ) : EReal)))
    have hφnn : ∀ x ≥ (0 : EReal), min x ((n : ℝ) : EReal) ≥ 0 := by
      intro x hx
      exact le_min hx (EReal.coe_nonneg.mpr (Nat.cast_nonneg n))
    simpa [fn] using UnsignedMeasurable.comp_cts hf hφ hφnn
  have hmono : Monotone (fun n : ℕ => LowerUnsignedLebesgueIntegral (fn n)) := by
    intro n m hnm
    apply LowerUnsignedLebesgueIntegral.mono (hfn_meas n) (hfn_meas m)
    apply AlmostAlways.ofAlways
    intro x
    exact min_le_min le_rfl (EReal.coe_le_coe_iff.mpr (by exact_mod_cast hnm))
  have hconv : Tendsto (fun n : ℕ => LowerUnsignedLebesgueIntegral (fn n)) atTop
      (𝓝 (⨆ n : ℕ, LowerUnsignedLebesgueIntegral (fn n))) :=
    tendsto_atTop_iSup hmono
  have hsup : (⨆ n : ℕ, LowerUnsignedLebesgueIntegral (fn n)) = LowerUnsignedLebesgueIntegral f := by
    apply le_antisymm
    · apply iSup_le
      intro n
      apply LowerUnsignedLebesgueIntegral.mono (hfn_meas n) hf
      apply AlmostAlways.ofAlways
      intro x
      exact min_le_left (f x) n
    · unfold LowerUnsignedLebesgueIntegral
      apply sSup_le
      intro R hR
      rcases hR with ⟨g, hg, hg_cond⟩
      have hg_le : ∀ x, g x ≤ f x := fun x => (hg_cond x).1
      have hR_eq : R = hg.integ := (hg_cond (Classical.arbitrary _)).2
      rw [hR_eq]
      have hmono_g : Monotone (fun n : ℕ => (simple_min_const hg n).integ) := by
        intro n m hnm
        apply UnsignedSimpleFunction.integral_le_integral_of_aeLe (simple_min_const hg n) (simple_min_const hg m)
        apply AlmostAlways.ofAlways
        intro x
        exact min_le_min le_rfl (EReal.coe_le_coe_iff.mpr (by exact_mod_cast hnm))
      have hconv_g : Tendsto (fun n : ℕ => (simple_min_const hg n).integ) atTop
          (𝓝 (⨆ n : ℕ, (simple_min_const hg n).integ)) :=
        tendsto_atTop_iSup hmono_g
      have hlim : hg.integ = ⨆ n : ℕ, (simple_min_const hg n).integ :=
        tendsto_nhds_unique (integral_limit hg) hconv_g
      rw [hlim]
      apply iSup_mono
      intro n
      exact le_sSup ⟨fun x => min (g x) n, simple_min_const hg n, fun x => ⟨min_le_min (hg_le x) le_rfl, rfl⟩⟩
  rw [← hsup]
  simpa [fn] using hconv

def UpperUnsignedLebesgueIntegral.eq_lim_vert_trunc : Decidable (∀ (d:ℕ) (f: EuclideanSpace' d → EReal) (hf: UnsignedMeasurable f), Filter.atTop.Tendsto (fun n:ℕ ↦ UpperUnsignedLebesgueIntegral (fun x ↦ min (f x) n)) (nhds (UpperUnsignedLebesgueIntegral f))) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  sorry

/-- The open ball centered at the origin is Lebesgue measurable. -/
def ball_measurable {d : ℕ} (n : ℕ) :
    LebesgueMeasurable (Metric.ball (0 : EuclideanSpace' d) n) :=
  IsOpen.measurable (Metric.isOpen_ball : IsOpen (Metric.ball (0 : EuclideanSpace' d) n))

/-- The measure of the open ball centered at the origin is finite. -/
lemma ball_measure_lt_top {d : ℕ} (n : ℕ) :
    Lebesgue_measure (Metric.ball (0 : EuclideanSpace' d) n) < ⊤ := by
  have hclosure_compact : IsCompact (closure (Metric.ball (0 : EuclideanSpace' d) n)) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure Metric.isBounded_ball.closure
  have hclosure_fin : Lebesgue_measure (closure (Metric.ball (0 : EuclideanSpace' d) n)) ≠ ⊤ :=
    Lebesgue_outer_measure.finite_of_compact hclosure_compact
  have hle_cl : Lebesgue_measure (Metric.ball (0 : EuclideanSpace' d) n) ≤
      Lebesgue_measure (closure (Metric.ball (0 : EuclideanSpace' d) n)) :=
    Lebesgue_outer_measure.mono subset_closure
  have hball_ne : Lebesgue_measure (Metric.ball (0 : EuclideanSpace' d) n) ≠ ⊤ := by
    intro h_eq_top
    rw [h_eq_top] at hle_cl
    exact hclosure_fin (eq_top_iff.mpr hle_cl)
  exact lt_top_iff_ne_top.mpr hball_ne

/-- Multiplying an unsigned measurable function by a ball indicator preserves measurability.
    This is a key helper for the horizontal truncation argument in Corollary 1.3.14. -/
lemma UnsignedMeasurable.mul_indicator_ball {d : ℕ} {f : EuclideanSpace' d → EReal}
    (hf : UnsignedMeasurable f) (n : ℕ) :
    UnsignedMeasurable (f * Real.toEReal ∘ (Metric.ball (0 : EuclideanSpace' d) n).indicator') := by
  constructor
  · intro x
    simp [Pi.mul_apply, Function.comp_apply]
    exact mul_nonneg (hf.1 x) (ind_nonneg (Metric.ball (0 : EuclideanSpace' d) n) x)
  · rcases hf.2 with ⟨g, hg⟩
    refine ⟨fun k => g k * Real.toEReal ∘ (Metric.ball (0 : EuclideanSpace' d) n).indicator', ?_, ?_⟩
    · intro k
      exact simple_mul_indicator (hg.1 k) (ball_measurable n)
    · intro x
      have hmul := EReal.Tendsto.mul_const (m := fun k : ℕ => g k x) (a := f x)
        (b := Real.toEReal ((Metric.ball (0 : EuclideanSpace' d) n).indicator' x))
        (hg.2 x) (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))
      simpa [Pi.mul_apply, Function.comp_apply] using hmul

/-- Helper: horizontal truncation produces functions with finite measure support. -/
lemma FiniteMeasureSupport.mul_indicator_ball {d : ℕ} {f : EuclideanSpace' d → EReal}
    (n : ℕ) : FiniteMeasureSupport (f * Real.toEReal ∘ (Metric.ball (0 : EuclideanSpace' d) n).indicator') := by
  unfold FiniteMeasureSupport
  have hsub : Support (f * Real.toEReal ∘ (Metric.ball (0 : EuclideanSpace' d) n).indicator') ⊆
      Metric.ball (0 : EuclideanSpace' d) n := by
    intro x hx
    by_contra hxball
    have hx0 : (f * Real.toEReal ∘ (Metric.ball (0 : EuclideanSpace' d) n).indicator') x = 0 := by
      simp [Pi.mul_apply, Function.comp_apply, Set.indicator'_of_notMem hxball, EReal.coe_zero, mul_zero]
    exact hx hx0
  have hle : Lebesgue_measure (Support (f * Real.toEReal ∘ (Metric.ball (0 : EuclideanSpace' d) n).indicator')) ≤
      Lebesgue_measure (Metric.ball (0 : EuclideanSpace' d) n) :=
    Lebesgue_outer_measure.mono hsub
  exact lt_of_le_of_lt hle (ball_measure_lt_top n)

/-- Helper: the measure of A ∩ ball n converges to the measure of A (balls cover space). -/
lemma measure_ball_limit {d : ℕ} {A : Set (EuclideanSpace' d)} (hA : LebesgueMeasurable A) :
    Filter.atTop.Tendsto (fun n : ℕ => Lebesgue_measure (A ∩ Metric.ball (0 : EuclideanSpace' d) n)) (nhds (Lebesgue_measure A)) := by
  have hconv := Lebesgue_measure.upward_monotone_convergence
    (E := fun n => A ∩ Metric.ball (0 : EuclideanSpace' d) n)
    (hE := fun n => LebesgueMeasurable.inter hA (ball_measurable n))
    (hmono := fun n => Set.inter_subset_inter_right A
      (Metric.ball_subset_ball (by exact_mod_cast (Nat.le_succ n))))
  have hunion : (⋃ n : ℕ, A ∩ Metric.ball (0 : EuclideanSpace' d) n) = A := by
    ext x
    constructor
    · intro hx
      rw [Set.mem_iUnion] at hx
      rcases hx with ⟨n, hxn⟩
      exact hxn.1
    · intro hx
      rcases exists_nat_gt (‖x‖) with ⟨n, hn⟩
      rw [Set.mem_iUnion]
      refine ⟨n, ⟨hx, ?_⟩⟩
      rw [Metric.mem_ball]
      simpa [dist_zero_right] using hn
  simpa [hunion] using hconv

/-- The measure of the intersection with a growing ball, multiplied by a nonnegative
    constant, converges to the constant times the full measure. -/
lemma tendsto_ball_mul {d : ℕ} {A : Set (EuclideanSpace' d)} {c : EReal} (hc : 0 ≤ c)
    (hA : LebesgueMeasurable A) :
    Tendsto (fun n : ℕ => c * Lebesgue_measure (A ∩ Metric.ball (0 : EuclideanSpace' d) n))
      atTop (𝓝 (c * Lebesgue_measure A)) := by
  by_cases h₁ : c = 0 ∧ Lebesgue_measure A = ⊤
  · rcases h₁ with ⟨hc0, hmt⟩
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [] with n
    simp [hc0, hmt]
  · by_cases h₂ : c = ⊤ ∧ Lebesgue_measure A = 0
    · rcases h₂ with ⟨hct, hm0⟩
      have hmₙ0 : ∀ n : ℕ, Lebesgue_measure (A ∩ Metric.ball (0 : EuclideanSpace' d) n) = 0 := by
        intro n
        apply le_antisymm
        · have hle : Lebesgue_measure (A ∩ Metric.ball (0 : EuclideanSpace' d) n) ≤ Lebesgue_measure A :=
            Lebesgue_outer_measure.mono (Set.inter_subset_left)
          simpa [hm0] using hle
        · exact Lebesgue_outer_measure.nonneg _
      apply tendsto_nhds_of_eventually_eq
      filter_upwards [] with n
      simp [hct, hmₙ0 n, hm0]
    · have hmn : Tendsto (fun n : ℕ =>
          Lebesgue_measure (A ∩ Metric.ball (0 : EuclideanSpace' d) n)) atTop
          (𝓝 (Lebesgue_measure A)) := measure_ball_limit hA
      have h₁' : Lebesgue_measure A ≠ 0 ∨ c ≠ ⊥ :=
        Or.inr (ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero hc))
      have h₂' : Lebesgue_measure A ≠ 0 ∨ c ≠ ⊤ := by
        by_cases hct : c = ⊤
        · left
          intro hm0
          exact h₂ ⟨hct, hm0⟩
        · exact Or.inr hct
      have hmul := EReal.Tendsto.mul_const (m := fun n : ℕ =>
          Lebesgue_measure (A ∩ Metric.ball (0 : EuclideanSpace' d) n)) (a := Lebesgue_measure A)
        (b := c) hmn h₁' h₂'
      simpa [mul_comm] using hmul

/-- The product of a simple function with a set indicator, expressed on the atoms
    intersected with the set. -/
lemma mul_indicator_eq_sum_atomValueEReal {d : ℕ} {g : EuclideanSpace' d → EReal}
    (hg : UnsignedSimpleFunction g) (E₀ : Set (EuclideanSpace' d)) :
    g * Real.toEReal ∘ E₀.indicator' = ∑ n' : Fin (2^(hg.choose + hg.choose)),
      atomValueEReal hg.choose_spec.choose n'.val •
        EReal.indicator (atom hg.choose_spec.choose_spec.choose hg.choose_spec.choose_spec.choose n' ∩ E₀) := by
  let k := hg.choose
  let c := hg.choose_spec.choose
  let E := hg.choose_spec.choose_spec.choose
  have hmes : ∀ i, LebesgueMeasurable (E i) ∧ c i ≥ 0 := hg.choose_spec.choose_spec.choose_spec.1
  have heq : g = ∑ i, (c i) • (EReal.indicator (E i)) := hg.choose_spec.choose_spec.choose_spec.2
  let A : Fin (2^(k+k)) → Set (EuclideanSpace' d) := atom E E
  funext x
  let n0 : Fin (2^(k+k)) := ⟨atomIndexOf E E x, atomIndexOf_lt E E x⟩
  have hx_mem : x ∈ A n0 := by
    simp only [A, atom, Set.mem_setOf_eq, n0]
    refine ⟨fun j => ?_, fun j => ?_⟩
    · rw [atomMembership_eq_testBit, atomIndexOf_testBit_E E E x j]
    · rw [atomMembership_eq_testBit, atomIndexOf_testBit_E' E E x j]
  have hunique : ∀ m : Fin (2^(k+k)), x ∈ A m → m = n0 := by
    intro m hm
    by_contra hne
    have hdisj : Disjoint (A m) (A n0) := by
      simpa [A] using atom_pairwiseDisjoint E E (by simp) (by simp) hne
    exact (Set.disjoint_left.mp hdisj) hm hx_mem
  have hgx : g x = atomValueEReal c n0.val := by
    exact (congrFun heq x).trans (by
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
        (sum_indicator_eq_atomValueEReal c E E n0 x hx_mem))
  by_cases hx₀ : x ∈ E₀
  · have hrhs : (∑ n' : Fin (2^(k+k)), atomValueEReal c n'.val * EReal.indicator (A n' ∩ E₀) x) =
        atomValueEReal c n0.val := by
      rw [Finset.sum_eq_single n0]
      · simp only [EReal.indicator_of_mem (Set.mem_inter hx_mem hx₀), mul_one]
      · intro m _ hm_ne
        have hx_notin : x ∉ A m ∩ E₀ := fun h => hm_ne (hunique m h.1)
        simp only [EReal.indicator_of_notMem hx_notin, mul_zero]
      · intro h; exact absurd (Finset.mem_univ n0) h
    simp only [Pi.mul_apply, Function.comp_apply, Set.indicator'_of_mem hx₀, EReal.coe_one]
    rw [hgx]
    simpa [A, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_one] using hrhs.symm
  · have hrhs : (∑ n' : Fin (2^(k+k)), atomValueEReal c n'.val * EReal.indicator (A n' ∩ E₀) x) = 0 := by
      apply Finset.sum_eq_zero
      intro n' _
      have hx_notin : x ∉ A n' ∩ E₀ := fun h => hx₀ h.2
      simp only [EReal.indicator_of_notMem hx_notin, mul_zero]
    simp only [Pi.mul_apply, Function.comp_apply, Set.indicator'_of_notMem hx₀, EReal.coe_zero]
    rw [hgx]
    simpa [A, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hrhs.symm

/-- Helper: the integral of g times the ball indicator converges to the integral of g.
    This is the simple horizontal monotone convergence result, mirroring the vertical
    one with min replaced by the ball indicator. -/
lemma ball_integral_limit {d : ℕ} {g : EuclideanSpace' d → EReal} (hg : UnsignedSimpleFunction g) :
    Tendsto (fun n : ℕ =>
      (simple_mul_indicator hg (IsOpen.measurable (Metric.isOpen_ball : IsOpen (Metric.ball (0 : EuclideanSpace' d) n)))).integ)
      atTop (𝓝 (hg.integ)) := by
  let k := hg.choose
  let c := hg.choose_spec.choose
  let E := hg.choose_spec.choose_spec.choose
  have hmes : ∀ i, LebesgueMeasurable (E i) ∧ c i ≥ 0 := hg.choose_spec.choose_spec.choose_spec.1
  have heq : g = ∑ i, (c i) • (EReal.indicator (E i)) := hg.choose_spec.choose_spec.choose_spec.2
  let A : Fin (2^(k+k)) → Set (EuclideanSpace' d) := atom E E
  let B : ℕ → Set (EuclideanSpace' d) := fun n => Metric.ball (0 : EuclideanSpace' d) n
  have hA_mes : ∀ n, LebesgueMeasurable (A n) := by
    intro n
    simpa [A] using atom_measurable (fun i => (hmes i).1) (fun j => (hmes j).1) n
  have hB_mes : ∀ n, LebesgueMeasurable (B n) := by
    intro n
    exact ball_measurable n
  have hsum_conv : Tendsto (fun n : ℕ =>
      ∑ n' : Fin (2^(k+k)), atomValueEReal c n'.val * Lebesgue_measure (A n' ∩ B n))
      atTop (𝓝 (∑ n' : Fin (2^(k+k)), atomValueEReal c n'.val * Lebesgue_measure (A n'))) := by
    simpa using tendsto_sum_of_nonneg (s := (Finset.univ : Finset (Fin (2^(k+k)))))
      (f := fun (n' : Fin (2^(k+k))) (n : ℕ) => atomValueEReal c n'.val * Lebesgue_measure (A n' ∩ B n))
      (a := fun n' : Fin (2^(k+k)) => atomValueEReal c n'.val * Lebesgue_measure (A n'))
      (hf := fun n' _ => tendsto_ball_mul (A := A n') (c := atomValueEReal c n'.val)
        (hc := atomValueEReal_nonneg (fun i => (hmes i).2) n'.val) (hA := hA_mes n'))
      (ha := fun n' _ => mul_nonneg (atomValueEReal_nonneg (fun i => (hmes i).2) n'.val)
        (Lebesgue_outer_measure.nonneg (A n')))
  have hg_integ : hg.integ = ∑ n' : Fin (2^(k+k)), atomValueEReal c n'.val * Lebesgue_measure (A n') := by
    rw [UnsignedSimpleFunction.integral_eq hg (k := 2^(k+k))
      (c := fun n' : Fin (2^(k+k)) => atomValueEReal c n'.val) (E := A)
      (hmes := hA_mes) (hnonneg := fun n' => atomValueEReal_nonneg (fun i => (hmes i).2) n'.val)
      (heq := heq.trans (by simpa [A] using eq_sum_atomValueEReal_indicator c E E))]
  have h_n_integ : ∀ n : ℕ, (simple_mul_indicator hg (hB_mes n)).integ =
      ∑ n' : Fin (2^(k+k)), atomValueEReal c n'.val * Lebesgue_measure (A n' ∩ B n) := by
    intro n
    rw [UnsignedSimpleFunction.integral_eq (simple_mul_indicator hg (hB_mes n)) (k := 2^(k+k))
      (c := fun n' : Fin (2^(k+k)) => atomValueEReal c n'.val)
      (E := fun n' : Fin (2^(k+k)) => A n' ∩ B n)
      (hmes := fun n' => LebesgueMeasurable.inter (hA_mes n') (hB_mes n))
      (hnonneg := fun n' => atomValueEReal_nonneg (fun i => (hmes i).2) n'.val)
      (heq := by simpa [A, B, k, c, E] using mul_indicator_eq_sum_atomValueEReal hg (B n))]
  have hmain : Tendsto (fun n : ℕ => (simple_mul_indicator hg (hB_mes n)).integ) atTop
      (𝓝 (∑ n' : Fin (2^(k+k)), atomValueEReal c n'.val * Lebesgue_measure (A n'))) :=
    hsum_conv.congr (fun n => (h_n_integ n).symm)
  rw [hg_integ]
  exact hmain

/-- Exercise 1.3.10(ix) (Horizontal truncation)-/
theorem LowerUnsignedLebesgueIntegral.eq_lim_horiz_trunc {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) : Filter.atTop.Tendsto (fun n:ℕ ↦ LowerUnsignedLebesgueIntegral (f * Real.toEReal ∘ (Metric.ball 0 n).indicator')) (nhds (LowerUnsignedLebesgueIntegral f)) := by
  let fn : ℕ → EuclideanSpace' d → EReal := fun n => f * Real.toEReal ∘ (Metric.ball (0 : EuclideanSpace' d) n).indicator'
  have hfn_meas : ∀ n, UnsignedMeasurable (fn n) := by
    intro n
    simpa [fn] using UnsignedMeasurable.mul_indicator_ball hf n
  have hmono : Monotone (fun n : ℕ => LowerUnsignedLebesgueIntegral (fn n)) := by
    intro n m hnm
    apply LowerUnsignedLebesgueIntegral.mono (hfn_meas n) (hfn_meas m)
    apply AlmostAlways.ofAlways
    intro x
    have hsub : Metric.ball (0 : EuclideanSpace' d) n ⊆ Metric.ball (0 : EuclideanSpace' d) m :=
      Metric.ball_subset_ball (by exact_mod_cast hnm)
    have h_ind : Real.toEReal ((Metric.ball (0 : EuclideanSpace' d) n).indicator' x) ≤
        Real.toEReal ((Metric.ball (0 : EuclideanSpace' d) m).indicator' x) := by
      by_cases hx : x ∈ Metric.ball (0 : EuclideanSpace' d) n
      · have hx' : x ∈ Metric.ball (0 : EuclideanSpace' d) m := hsub hx
        simp [Set.indicator'_of_mem hx, Set.indicator'_of_mem hx', EReal.coe_one]
      · simp only [Set.indicator'_of_notMem hx, EReal.coe_zero]
        exact ind_nonneg (Metric.ball (0 : EuclideanSpace' d) m) x
    simp [fn, Pi.mul_apply, Function.comp_apply]
    have hmain : Real.toEReal ((Metric.ball (0 : EuclideanSpace' d) n).indicator' x) * f x ≤
        Real.toEReal ((Metric.ball (0 : EuclideanSpace' d) m).indicator' x) * f x :=
      mul_le_mul_of_nonneg_right h_ind (hf.1 x)
    simpa [mul_comm] using hmain
  have hconv : Tendsto (fun n : ℕ => LowerUnsignedLebesgueIntegral (fn n)) atTop
      (𝓝 (⨆ n : ℕ, LowerUnsignedLebesgueIntegral (fn n))) :=
    tendsto_atTop_iSup hmono
  have hsup : (⨆ n : ℕ, LowerUnsignedLebesgueIntegral (fn n)) = LowerUnsignedLebesgueIntegral f := by
    apply le_antisymm
    · apply iSup_le
      intro n
      apply LowerUnsignedLebesgueIntegral.mono (hfn_meas n) hf
      apply AlmostAlways.ofAlways
      intro x
      have h_one : Real.toEReal ((Metric.ball (0 : EuclideanSpace' d) n).indicator' x) ≤ (1 : EReal) := by
        by_cases hx : x ∈ Metric.ball (0 : EuclideanSpace' d) n
        · simp [Set.indicator'_of_mem hx, EReal.coe_one]
        · simp [Set.indicator'_of_notMem hx, EReal.coe_zero]
      simp [fn, Pi.mul_apply, Function.comp_apply]
      have hmain : Real.toEReal ((Metric.ball (0 : EuclideanSpace' d) n).indicator' x) * f x ≤
          (1 : EReal) * f x :=
        mul_le_mul_of_nonneg_right h_one (hf.1 x)
      simpa [mul_comm, one_mul] using hmain
    · unfold LowerUnsignedLebesgueIntegral
      apply sSup_le
      intro R hR
      rcases hR with ⟨g, hg, hg_cond⟩
      have hg_le : ∀ x, g x ≤ f x := fun x => (hg_cond x).1
      have hR_eq : R = hg.integ := (hg_cond (Classical.arbitrary _)).2
      rw [hR_eq]
      have hmono_g : Monotone (fun n : ℕ => (simple_mul_indicator hg (ball_measurable n)).integ) := by
        intro n m hnm
        apply UnsignedSimpleFunction.integral_le_integral_of_aeLe
          (simple_mul_indicator hg (ball_measurable n)) (simple_mul_indicator hg (ball_measurable m))
        apply AlmostAlways.ofAlways
        intro x
        have hsub : Metric.ball (0 : EuclideanSpace' d) n ⊆ Metric.ball (0 : EuclideanSpace' d) m :=
          Metric.ball_subset_ball (by exact_mod_cast hnm)
        have h_ind : Real.toEReal ((Metric.ball (0 : EuclideanSpace' d) n).indicator' x) ≤
            Real.toEReal ((Metric.ball (0 : EuclideanSpace' d) m).indicator' x) := by
          by_cases hx : x ∈ Metric.ball (0 : EuclideanSpace' d) n
          · have hx' : x ∈ Metric.ball (0 : EuclideanSpace' d) m := hsub hx
            simp [Set.indicator'_of_mem hx, Set.indicator'_of_mem hx', EReal.coe_one]
          · simp only [Set.indicator'_of_notMem hx, EReal.coe_zero]
            exact ind_nonneg (Metric.ball (0 : EuclideanSpace' d) m) x
        simp [Pi.mul_apply, Function.comp_apply]
        have hmain : Real.toEReal ((Metric.ball (0 : EuclideanSpace' d) n).indicator' x) * g x ≤
            Real.toEReal ((Metric.ball (0 : EuclideanSpace' d) m).indicator' x) * g x :=
          mul_le_mul_of_nonneg_right h_ind ((UnsignedSimpleFunction.unsignedMeasurable hg).1 x)
        simpa [mul_comm] using hmain
      have hconv_g : Tendsto (fun n : ℕ => (simple_mul_indicator hg (ball_measurable n)).integ) atTop
          (𝓝 (⨆ n : ℕ, (simple_mul_indicator hg (ball_measurable n)).integ)) :=
        tendsto_atTop_iSup hmono_g
      have hlim : hg.integ = ⨆ n : ℕ, (simple_mul_indicator hg (ball_measurable n)).integ :=
        tendsto_nhds_unique (ball_integral_limit hg) hconv_g
      rw [hlim]
      apply iSup_mono
      intro n
      exact le_sSup ⟨g * Real.toEReal ∘ (Metric.ball (0 : EuclideanSpace' d) n).indicator',
        simple_mul_indicator hg (ball_measurable n),
        fun x => ⟨by
          simp [fn, Pi.mul_apply, Function.comp_apply]
          exact mul_le_mul_of_nonneg_right (hg_le x) (ind_nonneg (Metric.ball (0 : EuclideanSpace' d) n) x), rfl⟩⟩
  rw [← hsup]
  simpa [fn] using hconv

def UpperUnsignedLebesgueIntegral.eq_lim_horiz_trunc : Decidable (∀ (d:ℕ) (f: EuclideanSpace' d → EReal) (hf: UnsignedMeasurable f), Filter.atTop.Tendsto (fun n:ℕ ↦ UpperUnsignedLebesgueIntegral (f * Real.toEReal ∘ (Metric.ball 0 n).indicator')) (nhds (UpperUnsignedLebesgueIntegral f))) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  sorry

/-- Exercise 1.3.10(x) (Reflection) -/
theorem LowerUnsignedLebesgueIntegral.sum_of_reflect_eq {d:ℕ} {f g: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) (hg: UnsignedMeasurable g)
    (hfg: UnsignedSimpleFunction (f+g)) (hbound: EReal.BoundedFunction (f + g)) (hsupport: FiniteMeasureSupport (f + g)) :
    hfg.integ = LowerUnsignedLebesgueIntegral f + LowerUnsignedLebesgueIntegral g := by sorry

/-- Definition 1.3.13 (Unsigned Lebesgue integral).  For Lean purposes it is convenient to assign a "junk" value to this integral when f is not unsigned measurable. -/
noncomputable def UnsignedLebesgueIntegral {d:ℕ} (f: EuclideanSpace' d → EReal): EReal := LowerUnsignedLebesgueIntegral f

noncomputable def UnsignedMeasurable.integ {d:ℕ} (f: EuclideanSpace' d → EReal) (_: UnsignedMeasurable f) : EReal := UnsignedLebesgueIntegral f

/-- The constant function with value c is an unsigned simple function when c is nonnegative. -/
lemma const_simple {d : ℕ} (c : ℝ) (hc : 0 ≤ c) :
    UnsignedSimpleFunction (fun _ : EuclideanSpace' d => (c : EReal)) := by
  use 1, (fun _ : Fin 1 => (c : EReal)), (fun _ : Fin 1 => (Set.univ : Set (EuclideanSpace' d)))
  constructor
  · intro i
    constructor
    · simpa using isOpen_univ.measurable
    · exact EReal.coe_nonneg.mpr hc
  · ext x
    simp [smul_eq_mul, EReal.indicator_of_mem (Set.mem_univ x)]

/-- Pointwise identity: the positive part of g minus a real constant equals the atom sum
    with max-truncated coefficients (atoms refine the representation of g). -/
lemma max_eq_sum_atomValueEReal {d : ℕ} {g : EuclideanSpace' d → EReal} (hg : UnsignedSimpleFunction g)
    (c : ℝ) :
    (fun x => max (g x - (c : EReal)) 0) = ∑ n' : Fin (2^(hg.choose + hg.choose)),
      max (atomValueEReal hg.choose_spec.choose n'.val - (c : EReal)) 0 •
        EReal.indicator (atom hg.choose_spec.choose_spec.choose hg.choose_spec.choose_spec.choose n') := by
  let k := hg.choose
  let c' := hg.choose_spec.choose
  let E := hg.choose_spec.choose_spec.choose
  have hmes : ∀ i, LebesgueMeasurable (E i) ∧ c' i ≥ 0 := hg.choose_spec.choose_spec.choose_spec.1
  have heq : g = ∑ i, (c' i) • (EReal.indicator (E i)) := hg.choose_spec.choose_spec.choose_spec.2
  let A : Fin (2^(k+k)) → Set (EuclideanSpace' d) := atom E E
  funext x
  let n0 : Fin (2^(k+k)) := ⟨atomIndexOf E E x, atomIndexOf_lt E E x⟩
  have hx_mem : x ∈ A n0 := by
    simp only [A, atom, Set.mem_setOf_eq, n0]
    refine ⟨fun j => ?_, fun j => ?_⟩
    · rw [atomMembership_eq_testBit, atomIndexOf_testBit_E E E x j]
    · rw [atomMembership_eq_testBit, atomIndexOf_testBit_E' E E x j]
  have hunique : ∀ m : Fin (2^(k+k)), x ∈ A m → m = n0 := by
    intro m hm
    by_contra hne
    have hdisj : Disjoint (A m) (A n0) := by
      simpa [A] using atom_pairwiseDisjoint E E (by simp) (by simp) hne
    exact (Set.disjoint_left.mp hdisj) hm hx_mem
  have hgx : g x = atomValueEReal c' n0.val := by
    exact (congrFun heq x).trans (by
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
        (sum_indicator_eq_atomValueEReal c' E E n0 x hx_mem))
  have hrhs : (∑ n' : Fin (2^(k+k)), max (atomValueEReal c' n'.val - (c : EReal)) 0 * EReal.indicator (A n') x) =
      max (atomValueEReal c' n0.val - (c : EReal)) 0 := by
    rw [Finset.sum_eq_single n0]
    · simp only [EReal.indicator_of_mem hx_mem, mul_one]
    · intro m _ hm_ne
      have hx_notin : x ∉ A m := fun h => hm_ne (hunique m h)
      simp only [EReal.indicator_of_notMem hx_notin, mul_zero]
    · intro h; exact absurd (Finset.mem_univ n0) h
  rw [hgx]
  simpa [A, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hrhs.symm

/-- The positive part of g minus a real constant is simple, via the atom refinement
    (mirror of simple_min_const: the vertical truncation machinery). -/
lemma simple_max_sub_const {d : ℕ} {g : EuclideanSpace' d → EReal} (hg : UnsignedSimpleFunction g)
    (c : ℝ) : UnsignedSimpleFunction (fun x => max (g x - (c : EReal)) 0) := by
  use 2^(hg.choose + hg.choose),
    (fun n' : Fin (2^(hg.choose + hg.choose)) => max (atomValueEReal hg.choose_spec.choose n'.val - (c : EReal)) 0),
    (atom hg.choose_spec.choose_spec.choose hg.choose_spec.choose_spec.choose)
  constructor
  · intro i
    constructor
    · exact atom_measurable (fun i => (hg.choose_spec.choose_spec.choose_spec.1 i).1)
        (fun j => (hg.choose_spec.choose_spec.choose_spec.1 j).1) i
    · exact le_max_right _ (0 : EReal)
  · exact max_eq_sum_atomValueEReal hg c

/-- The support of an unsigned measurable function is measurable, via TFAE. -/
lemma supp_measurable {d : ℕ} {f : EuclideanSpace' d → EReal} (hf : UnsignedMeasurable f) :
    LebesgueMeasurable {x | 0 < f x} := by
  have h4 : ∀ t : EReal, LebesgueMeasurable {x | f x > t} :=
    ((UnsignedMeasurable.TFAE hf.1).out 0 4 (a := UnsignedMeasurable f)
      (b := ∀ t : EReal, LebesgueMeasurable {x | f x > t})).mp hf
  simpa using h4 (0 : EReal)

/-- The upper integral of a simple function is its simple integral. -/
lemma upperIntegral_simple {d : ℕ} {g : EuclideanSpace' d → EReal} (hg : UnsignedSimpleFunction g) :
    UpperUnsignedLebesgueIntegral g = hg.integ := by
  unfold UpperUnsignedLebesgueIntegral
  apply le_antisymm
  · apply sInf_le
    exact ⟨g, hg, fun x => ⟨le_rfl, rfl⟩⟩
  · apply le_sInf
    intro R hR
    rcases hR with ⟨h, hh, hh_cond⟩
    have hh_ge : ∀ x, g x ≤ h x := fun x => (hh_cond x).1
    have hR_eq : R = hh.integ := (hh_cond (Classical.arbitrary _)).2
    rw [hR_eq]
    exact UnsignedSimpleFunction.integral_le_integral_of_aeLe hg hh (AlmostAlways.ofAlways hh_ge)

/-- Monotonicity of the upper integral: pointwise order is preserved by the upper integral. -/
lemma upperIntegral_mono {d : ℕ} {f g : EuclideanSpace' d → EReal} (hfg : ∀ x, f x ≤ g x) :
    UpperUnsignedLebesgueIntegral f ≤ UpperUnsignedLebesgueIntegral g := by
  unfold UpperUnsignedLebesgueIntegral
  apply le_sInf
  intro R hR
  rcases hR with ⟨h, hh, hh_cond⟩
  apply sInf_le
  exact ⟨h, hh, fun x => ⟨le_trans (hfg x) (hh_cond x).1, (hh_cond x).2⟩⟩

/-- If an EReal value is bounded above by r over n+1 for every n, then it is nonpositive. -/
private lemma le_of_forall_nat_div_ereal {a : EReal} {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ n : ℕ, a ≤ (r / ((n : ℝ) + 1) : EReal)) : a ≤ 0 := by
  by_contra! hpos
  by_cases hr0 : r = 0
  · have ha0 : a ≤ 0 := by simpa [hr0] using h 0
    exact (lt_irrefl (0 : EReal)) (lt_of_lt_of_le hpos ha0)
  · obtain ⟨ε', hε'_pos, hε'_lt⟩ : ∃ ε' : ℝ, 0 < ε' ∧ (ε' : EReal) < a := by
      cases ha : a with
      | bot => rw [ha] at hpos; simp at hpos
      | top => exact ⟨1, one_pos, by
          have h1_lt_top : (1 : EReal) < ⊤ := EReal.coe_lt_top _
          simpa [ha] using h1_lt_top⟩
      | coe s =>
          have hs_pos : 0 < s := EReal.coe_pos.mp (by rw [← ha]; exact hpos)
          refine ⟨s / 2, by linarith, ?_⟩
          have : (s / 2 : ℝ) < s := by linarith
          simpa [ha] using EReal.coe_lt_coe_iff.mpr this
    have hrε_pos : 0 < r / ε' := div_pos (lt_of_le_of_ne hr (Ne.symm hr0)) hε'_pos
    have harch : ∃ N : ℕ, (N : ℝ) > r / ε' := exists_nat_gt (r / ε')
    rcases harch with ⟨N, hN⟩
    have hN1 : (N : ℝ) + 1 > r / ε' := by linarith
    have hden : 0 < (N : ℝ) + 1 := lt_trans hrε_pos hN1
    have hNr : r < ((N : ℝ) + 1) * ε' := (div_lt_iff₀ hε'_pos).mp hN1
    have h_r_lt : r / ((N : ℝ) + 1) < ε' := by
      rw [div_lt_iff₀ hden]
      nlinarith [hNr]
    have h_bound_N : a ≤ (r / ((N : ℝ) + 1) : EReal) := h N
    have h_lt_ereal : ((r / ((N : ℝ) + 1) : ℝ) : EReal) < (ε' : EReal) :=
      EReal.coe_lt_coe_iff.mpr h_r_lt
    have h_contra : a < (ε' : EReal) := lt_of_le_of_lt h_bound_N h_lt_ereal
    exact (lt_irrefl a) (lt_trans h_contra hε'_lt)

/-- Exercise 1.3.11 -/
theorem LowerUnsignedLebesgueIntegral.eq_upperIntegral {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) (hbound: EReal.BoundedFunction f) (hsupp: FiniteMeasureSupport f) :
    LowerUnsignedLebesgueIntegral f = UpperUnsignedLebesgueIntegral f := by
  apply le_antisymm
  · -- PART 1: L f ≤ U f
    unfold LowerUnsignedLebesgueIntegral UpperUnsignedLebesgueIntegral
    apply le_sInf
    intro R hR
    rcases hR with ⟨h, hh, hh_cond⟩
    apply sSup_le
    intro a ha
    rcases ha with ⟨g, hg, hg_cond⟩
    have hg_le_h : ∀ x, g x ≤ h x := fun x => le_trans (hg_cond x).1 (hh_cond x).1
    have ha_eq : a = hg.integ := (hg_cond (Classical.arbitrary _)).2
    have hR_eq : R = hh.integ := (hh_cond (Classical.arbitrary _)).2
    rw [ha_eq, hR_eq]
    exact UnsignedSimpleFunction.integral_le_integral_of_aeLe hg hh (AlmostAlways.ofAlways hg_le_h)
  · -- PART 2: U f ≤ L f
    classical
    let supp : Set (EuclideanSpace' d) := {x | 0 < f x}
    have hsupp_meas : LebesgueMeasurable supp := by
      simpa [supp] using supp_measurable hf
    have hsupp' : Lebesgue_measure supp < ⊤ := by
      unfold FiniteMeasureSupport at hsupp
      have h_eq : {x | 0 < f x} = Support f := by
        ext x
        simp only [Support, Set.mem_setOf_eq]
        constructor
        · intro hx
          exact ne_of_gt hx
        · intro hx
          exact lt_of_le_of_ne (hf.1 x) hx.symm
      simpa [supp, h_eq] using hsupp
    let μ := Lebesgue_measure supp
    have hμ_nonneg : 0 ≤ μ := by
      simpa [μ] using Lebesgue_outer_measure.nonneg (E := supp)
    have hμ_fin : μ < ⊤ := by
      simpa [μ] using hsupp'
    have hμ_fin_real : ∃ r : ℝ, 0 ≤ r ∧ μ = (r : EReal) := by
      cases hμeq : μ with
      | bot =>
          exfalso
          have hb : 0 ≤ (⊥ : EReal) := by rw [← hμeq]; exact hμ_nonneg
          exact (not_le_of_gt EReal.bot_lt_zero) hb
      | top =>
          exfalso
          rw [hμeq] at hμ_fin
          exact (lt_irrefl ⊤) hμ_fin
      | coe r =>
          have hr0 : 0 ≤ r := by
            have hco : 0 ≤ (r : EReal) := by rw [← hμeq]; exact hμ_nonneg
            exact EReal.coe_nonneg.mp hco
          exact ⟨r, hr0, rfl⟩
    rcases hμ_fin_real with ⟨r, hr0, hμ_eq⟩
    have happrox : ∃ g : ℕ → EuclideanSpace' d → EReal, (∀ n, UnsignedSimpleFunction (g n) ∧ EReal.BoundedFunction (g n)) ∧ UniformConvergesTo g f :=
      (UnsignedMeasurable.bounded_iff hf.1).1 ⟨hf, hbound⟩
    rcases happrox with ⟨g, hg_approx, hgu⟩
    let ε_nn : ℕ → NNReal := fun m => ⟨(1 : ℝ) / ((m : ℝ) + 1), by positivity⟩
    let ε : ℕ → ℝ := fun m => (ε_nn m : ℝ)
    have hε_pos : ∀ m : ℕ, 0 < ε m := by
      intro m
      dsimp [ε, ε_nn]
      positivity
    have hε_nn_pos : ∀ m : ℕ, (0 : NNReal) < ε_nn m := by
      intro m
      exact (NNReal.coe_lt_coe.mp (by dsimp [ε_nn]; positivity))
    have hε_coe : ∀ m : ℕ, (ε_nn m : EReal) = (ε m : EReal) := by
      intro m
      rfl
    have hmain : ∀ m : ℕ, UpperUnsignedLebesgueIntegral f ≤ LowerUnsignedLebesgueIntegral f + ((2 : ℝ) * (ε m : ℝ) : EReal) * μ := by
      intro m
      rcases hgu (ε_nn m) (hε_nn_pos m) with ⟨N, hN⟩
      let nₘ : ℕ := N
      have hg₀_approx : ∀ x, f x - (ε_nn m : EReal) < g nₘ x ∧ g nₘ x < f x + (ε_nn m : EReal) := hN N le_rfl
      let g₀ : EuclideanSpace' d → EReal := g nₘ
      have hg₀ : UnsignedSimpleFunction g₀ := (hg_approx nₘ).1
      let g₁ : EuclideanSpace' d → EReal := fun x => max (g₀ x - (ε m : EReal)) 0
      let g₂ : EuclideanSpace' d → EReal := fun x => (g₀ x + (ε m : EReal)) * (Real.toEReal ∘ supp.indicator') x
      have hg₁ : UnsignedSimpleFunction g₁ := by
        simpa [g₁] using simple_max_sub_const hg₀ (ε m)
      have hg₀_add_ε : UnsignedSimpleFunction (fun x => g₀ x + (ε m : EReal)) := by
        exact UnsignedSimpleFunction.add hg₀ (const_simple (ε m) (le_of_lt (hε_pos m)))
      have hg₂ : UnsignedSimpleFunction g₂ := by
        exact simple_mul_indicator hg₀_add_ε hsupp_meas
      have h2ε_supp : UnsignedSimpleFunction
          (fun x => ((2 : ℝ) * (ε m : ℝ) : EReal) * (Real.toEReal ∘ supp.indicator') x) := by
        refine ⟨1, fun _ : Fin 1 => ((2 : ℝ) * (ε m : ℝ) : EReal), fun _ : Fin 1 => supp, ?_, ?_⟩
        · intro i
          constructor
          · simpa using hsupp_meas
          · exact EReal.coe_nonneg.mpr (mul_nonneg (by norm_num) (le_of_lt (hε_pos m)))
        · ext x
          simp [smul_eq_mul, EReal.indicator, Real.EReal_fun]
      have hg₁_le_f : ∀ x, g₁ x ≤ f x := by
        intro x
        dsimp [g₁]
        have hg₀_lt_f : g₀ x < f x + (ε m : EReal) := by
          simpa [ε, ε_nn, hε_coe m] using (hg₀_approx x).2
        have hsub : g₀ x - (ε m : EReal) < f x := by
          have h' : g₀ x < (ε m : EReal) + f x := by simpa [add_comm] using hg₀_lt_f
          exact EReal.sub_lt_of_lt_add' h'
        exact max_le_iff.mpr ⟨le_of_lt hsub, hf.1 x⟩
      have hf_le_g₂ : ∀ x, f x ≤ g₂ x := by
        intro x
        by_cases hx : x ∈ supp
        · have hg₂x : g₂ x = g₀ x + (ε m : EReal) := by
            dsimp [g₂]
            simp [hx]
          have hg₀_gt : f x - (ε m : EReal) < g₀ x := by
            simpa [ε, ε_nn, hε_coe m] using (hg₀_approx x).1
          have hf_lt : f x < g₀ x + (ε m : EReal) := by
            have hstep : (f x - (ε m : EReal)) + (ε m : EReal) < g₀ x + (ε m : EReal) :=
              EReal.add_lt_add_right_coe hg₀_gt (ε m)
            simpa [EReal.sub_add_cancel] using hstep
          rw [hg₂x]
          exact le_of_lt hf_lt
        · have hf0 : f x = 0 := le_antisymm (le_of_not_gt (by simpa [supp] using hx)) (hf.1 x)
          have hg₂0 : g₂ x = 0 := by
            dsimp [g₂]
            simp [hx]
          rw [hf0, hg₂0]
      have hg₂_le : ∀ x, g₂ x ≤ g₁ x + ((2 : ℝ) * (ε m : ℝ) : EReal) * (Real.toEReal ∘ supp.indicator') x := by
        intro x
        have h2ε : ((2 : ℝ) * (ε m : ℝ) : EReal) = (ε m : EReal) + (ε m : EReal) := by
          rw [← EReal.coe_mul, ← EReal.coe_add]
          congr
          ring
        by_cases hx : x ∈ supp
        · have hg₂x : g₂ x = g₀ x + (ε m : EReal) := by
            dsimp [g₂]
            simp [hx]
          have hind : (Real.toEReal ∘ supp.indicator') x = 1 := by
            simp [hx]
          by_cases hε_le : (ε m : EReal) ≤ g₀ x
          · have hnonneg : 0 ≤ g₀ x - (ε m : EReal) := by
              exact (EReal.sub_nonneg (x := g₀ x) (y := (ε m : EReal))
                (h_top := Or.inr (EReal.coe_ne_top (ε m)))
                (h_bot := Or.inr (EReal.coe_ne_bot (ε m)))).mpr hε_le
            have hcancel : (g₀ x - (ε m : EReal)) + ((2 : ℝ) * (ε m : ℝ) : EReal) = g₀ x + (ε m : EReal) := by
              rw [h2ε, ← add_assoc]
              rw [EReal.sub_add_cancel (a := g₀ x) (b := ε m)]
            calc
              g₂ x = g₀ x + (ε m : EReal) := hg₂x
              _ ≤ (g₀ x - (ε m : EReal)) + ((2 : ℝ) * (ε m : ℝ) : EReal) := le_of_eq hcancel.symm
              _ = max (g₀ x - (ε m : EReal)) 0 + ((2 : ℝ) * (ε m : ℝ) : EReal) * (Real.toEReal ∘ supp.indicator') x := by
                rw [max_eq_left hnonneg, hind, mul_one]
          · have hmax0 : max (g₀ x - (ε m : EReal)) 0 = 0 := by
              exact max_eq_right (EReal.sub_nonpos.mpr (le_of_not_ge hε_le))
            have hg₀lt : g₀ x < (ε m : EReal) := lt_of_not_ge hε_le
            calc
              g₂ x = g₀ x + (ε m : EReal) := hg₂x
              _ ≤ ((2 : ℝ) * (ε m : ℝ) : EReal) := by
                calc
                  g₀ x + (ε m : EReal) ≤ (ε m : EReal) + (ε m : EReal) := add_le_add (le_of_lt hg₀lt) le_rfl
                  _ = ((2 : ℝ) * (ε m : ℝ) : EReal) := h2ε.symm
              _ = max (g₀ x - (ε m : EReal)) 0 + ((2 : ℝ) * (ε m : ℝ) : EReal) * (Real.toEReal ∘ supp.indicator') x := by
                rw [hmax0, hind, mul_one, zero_add]
        · have hg₂0 : g₂ x = 0 := by
            dsimp [g₂]
            simp [hx]
          have hind0 : (Real.toEReal ∘ supp.indicator') x = 0 := by
            simp [hx]
          calc
            g₂ x = 0 := hg₂0
            _ ≤ max (g₀ x - (ε m : EReal)) 0 + ((2 : ℝ) * (ε m : ℝ) : EReal) * (Real.toEReal ∘ supp.indicator') x := by
              rw [hind0, mul_zero, add_zero]
              exact le_max_right _ (0 : EReal)
      have hU_le : UpperUnsignedLebesgueIntegral f ≤ hg₂.integ := by
        rw [← upperIntegral_simple hg₂]
        exact upperIntegral_mono hf_le_g₂
      let hsum := UnsignedSimpleFunction.add hg₁ h2ε_supp
      have hg₂_integ_le : hg₂.integ ≤ hsum.integ := by
        exact UnsignedSimpleFunction.integral_le_integral_of_aeLe hg₂ hsum (AlmostAlways.ofAlways hg₂_le)
      have hsum_eq : hsum.integ = hg₁.integ + ((2 : ℝ) * (ε m : ℝ) : EReal) * μ := by
        have hadd := UnsignedSimpleFunction.integral_add hg₁ h2ε_supp
        have h2ε_integ : h2ε_supp.integ = ((2 : ℝ) * (ε m : ℝ) : EReal) * μ := by
          rw [UnsignedSimpleFunction.integral_eq h2ε_supp (k := 1)
            (c := fun _ : Fin 1 => ((2 : ℝ) * (ε m : ℝ) : EReal))
            (E := fun _ : Fin 1 => supp) (hmes := fun _ => hsupp_meas)
            (hnonneg := fun _ => EReal.coe_nonneg.mpr (mul_nonneg (by norm_num) (le_of_lt (hε_pos m))))
            (heq := by ext x; simp [smul_eq_mul, EReal.indicator, Real.EReal_fun])]
          simp [μ]
        rw [hadd, h2ε_integ]
      have hL_ge : hg₁.integ ≤ LowerUnsignedLebesgueIntegral f := by
        unfold LowerUnsignedLebesgueIntegral
        exact le_sSup ⟨g₁, hg₁, fun x => ⟨hg₁_le_f x, rfl⟩⟩
      calc
        UpperUnsignedLebesgueIntegral f ≤ hg₂.integ := hU_le
        _ ≤ hsum.integ := hg₂_integ_le
        _ = hg₁.integ + ((2 : ℝ) * (ε m : ℝ) : EReal) * μ := hsum_eq
        _ ≤ LowerUnsignedLebesgueIntegral f + ((2 : ℝ) * (ε m : ℝ) : EReal) * μ := add_le_add hL_ge le_rfl
    have hbound_r : ∀ m : ℕ, UpperUnsignedLebesgueIntegral f - LowerUnsignedLebesgueIntegral f ≤ ((2 : ℝ) * r / ((m : ℝ) + 1) : EReal) := by
      intro m
      have hcalc : ((2 : ℝ) * (ε m : ℝ) : EReal) * μ = ((2 : ℝ) * r / ((m : ℝ) + 1) : EReal) := by
        rw [hμ_eq]
        simp only [← EReal.coe_mul]
        change (((2 : ℝ) * (ε m : ℝ) * r : ℝ) : EReal) = (((2 : ℝ) * r / ((m : ℝ) + 1) : ℝ) : EReal)
        have hεm : ε m = (1 : ℝ) / ((m : ℝ) + 1) := by
          dsimp [ε, ε_nn]
        rw [hεm]
        ring_nf
      exact EReal.sub_le_of_le_add' (by simpa [hcalc] using hmain m)
    have hle0 : UpperUnsignedLebesgueIntegral f - LowerUnsignedLebesgueIntegral f ≤ 0 :=
      le_of_forall_nat_div_ereal (a := UpperUnsignedLebesgueIntegral f - LowerUnsignedLebesgueIntegral f)
        (r := 2 * r) (mul_nonneg (by norm_num) hr0) hbound_r
    exact EReal.sub_nonpos.mp hle0

def LowerUnsignedLebesgueIntegral.eq_upperIntegral_unbounded : Decidable (∀ (d:ℕ) (f: EuclideanSpace' d → EReal) (hf: UnsignedMeasurable f) (hsupp: FiniteMeasureSupport f), LowerUnsignedLebesgueIntegral f = UpperUnsignedLebesgueIntegral f) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  sorry

def LowerUnsignedLebesgueIntegral.eq_upperIntegral_infinite_supp : Decidable (∀ (d:ℕ) (f: EuclideanSpace' d → EReal) (hf: UnsignedMeasurable f) (hbound: EReal.BoundedFunction f), LowerUnsignedLebesgueIntegral f = UpperUnsignedLebesgueIntegral f) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  sorry

/-- Additivity of lower integral for finite-support functions.
    This is the key step where we can apply {name}`eq_upperIntegral` and use the sandwich argument. -/
lemma LowerUnsignedLebesgueIntegral.add_of_finiteSupport {d : ℕ}
    {f g : EuclideanSpace' d → EReal}
    (hf : UnsignedMeasurable f) (hg : UnsignedMeasurable g)
    (hfg : UnsignedMeasurable (f + g))
    (hf_supp : FiniteMeasureSupport f) (hg_supp : FiniteMeasureSupport g) :
    LowerUnsignedLebesgueIntegral (f + g) =
      LowerUnsignedLebesgueIntegral f + LowerUnsignedLebesgueIntegral g := by
  -- For finite-support functions, use vertical truncation to reduce to bounded case,
  -- then apply eq_upperIntegral to show Lower = Upper, then sandwich:
  --   Lower(f+g) ≥ Lower(f) + Lower(g)  [superadditive]
  --   Lower(f+g) = Upper(f+g) ≤ Upper(f) + Upper(g) = Lower(f) + Lower(g)  [eq_upperIntegral + subadditive]
  apply le_antisymm
  · -- ≤ direction: use vertical truncation + eq_upperIntegral + subadditive
    -- For bounded finite-support: Lower = Upper by eq_upperIntegral
    -- Then Upper(f+g) ≤ Upper(f) + Upper(g) by subadditive
    -- Take vertical truncation limit to handle unbounded case
    sorry
  · -- ≥ direction: direct from superadditivity
    exact LowerUnsignedLebesgueIntegral.superadditive hf hg

/-- Corollary 1.3.14 (Finite additivity of Lebesgue integral ). -/
theorem LowerUnsignedLebesgueIntegral.add {d:ℕ} {f g: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) (hg: UnsignedMeasurable g)
    (hfg: UnsignedMeasurable (f + g)) :
    LowerUnsignedLebesgueIntegral (f + g) = LowerUnsignedLebesgueIntegral f + LowerUnsignedLebesgueIntegral g := by
  apply le_antisymm
  · -- ≤: horizontal truncation → finite support → additivity → limit
    let f_h := fun n : ℕ ↦ f * Real.toEReal ∘ (Metric.ball (0 : EuclideanSpace' d) n).indicator'
    let g_h := fun n : ℕ ↦ g * Real.toEReal ∘ (Metric.ball (0 : EuclideanSpace' d) n).indicator'
    let fg_h := fun n : ℕ ↦ (f + g) * Real.toEReal ∘ (Metric.ball (0 : EuclideanSpace' d) n).indicator'

    have hfg_lim := eq_lim_horiz_trunc hfg

    -- (f+g) * ind = f * ind + g * ind by right_distrib for nonneg
    have heq : ∀ n, fg_h n = f_h n + g_h n := by
      intro n; funext x
      simp only [f_h, g_h, fg_h, Pi.add_apply, Pi.mul_apply]
      exact EReal.right_distrib_of_nonneg (hf.1 x) (hg.1 x)

    -- Additivity for finite-support truncations
    have heq_integ : ∀ n, LowerUnsignedLebesgueIntegral (fg_h n) =
        LowerUnsignedLebesgueIntegral (f_h n) + LowerUnsignedLebesgueIntegral (g_h n) := by
      intro n
      rw [heq n]
      apply LowerUnsignedLebesgueIntegral.add_of_finiteSupport
      · exact UnsignedMeasurable.mul_indicator_ball hf n
      · exact UnsignedMeasurable.mul_indicator_ball hg n
      · exact UnsignedMeasurable.add (UnsignedMeasurable.mul_indicator_ball hf n)
            (UnsignedMeasurable.mul_indicator_ball hg n)
      · exact FiniteMeasureSupport.mul_indicator_ball n
      · exact FiniteMeasureSupport.mul_indicator_ball n

    conv at hfg_lim => arg 1; ext n; rw [heq_integ n]

    -- Use le_of_tendsto': Lower(f_h n) + Lower(g_h n) → Lower(f+g) and each term ≤ limit
    apply le_of_tendsto' hfg_lim
    intro n
    apply add_le_add
    · -- Lower(f_h n) ≤ Lower(f) by monotonicity (f_h n ≤ f pointwise)
      apply LowerUnsignedLebesgueIntegral.mono (UnsignedMeasurable.mul_indicator_ball hf n) hf
      apply AlmostAlways.ofAlways; intro x
      simp only [Pi.mul_apply, Function.comp_apply]
      by_cases hx : x ∈ Metric.ball (0 : EuclideanSpace' d) n
      · simp [Set.indicator'_of_mem hx]
      · simp [Set.indicator'_of_notMem hx]; exact hf.1 x
    · -- Lower(g_h n) ≤ Lower(g) by monotonicity
      apply LowerUnsignedLebesgueIntegral.mono (UnsignedMeasurable.mul_indicator_ball hg n) hg
      apply AlmostAlways.ofAlways; intro x
      simp only [Pi.mul_apply, Function.comp_apply]
      by_cases hx : x ∈ Metric.ball (0 : EuclideanSpace' d) n
      · simp [Set.indicator'_of_mem hx]
      · simp [Set.indicator'_of_notMem hx]; exact hg.1 x
  · -- ≥: from superadditivity
    exact LowerUnsignedLebesgueIntegral.superadditive hf hg

/-- Exercise 1.3.12 (Upper Lebesgue integral and outer measure). -/
theorem UpperUnsignedLebesgueIntegral.eq_outer_measure_integral {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) :
    UpperUnsignedLebesgueIntegral (Real.toEReal ∘ E.indicator') = Lebesgue_outer_measure E := by sorry

theorem LowerUnsignedLebesgueIntegral.not_additive : ∃ (d:ℕ) (f g: EuclideanSpace' d → EReal) (hf: Unsigned f) (hg: Unsigned g), (LowerUnsignedLebesgueIntegral (f + g) ≠ LowerUnsignedLebesgueIntegral f + LowerUnsignedLebesgueIntegral g) := by
    sorry

theorem UpperUnsignedLebesgueIntegral.not_additive : ∃ (d:ℕ) (f g: EuclideanSpace' d → EReal) (hf: Unsigned f) (hg: Unsigned g), (UpperUnsignedLebesgueIntegral (f + g) ≠ UpperUnsignedLebesgueIntegral f + UpperUnsignedLebesgueIntegral g) := by
    sorry

/-- Exercise 1.3.13 (Area interpretation of integral). -/
theorem LowerUnsignedLebesgueIntegral.eq_area {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) :
    LowerUnsignedLebesgueIntegral f = Lebesgue_measure { p | ∃ x, ∃ t:ℝ, EuclideanSpace'.prod_equiv d 1 p = ⟨ x, t ⟩ ∧ 0 ≤ t ∧ t ≤ f x } := by sorry

/-- Exercise 1.3.14 (Uniqueness) -/
theorem UnsignedLebesgueIntegral.unique {d:ℕ} (integ: (EuclideanSpace' d → EReal) → EReal)
  (hsimple : ∀ f (hf: UnsignedSimpleFunction f), integ f = hf.integ)
  (hadd: ∀ f g (hf: UnsignedMeasurable f) (hg: UnsignedMeasurable g), integ (f + g) = integ f + integ g)
  (hvert: ∀ f (hf: UnsignedMeasurable f), Filter.atTop.Tendsto (fun n:ℕ ↦ integ (fun x ↦ min (f x) n)) (nhds (integ f)))
  (hhoriz: ∀ f (hf: UnsignedMeasurable f), Filter.atTop.Tendsto (fun n:ℕ ↦ integ (f * Real.toEReal ∘ (Metric.ball 0 n).indicator')) (nhds (integ f)))
  : ∀ f, UnsignedMeasurable f → integ f = UnsignedLebesgueIntegral f := by sorry

/-- Exercise 1.3.15 (Translation invariance). -/
theorem UnsignedLebesgueIntegral.trans {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) (a: EuclideanSpace' d) :
    UnsignedLebesgueIntegral (fun x ↦ f (x + a)) = hf.integ := by sorry

/-- Exercise 1.3.16 (Linear change of variables). -/
theorem UnsignedLebesgueIntegral.comp_linear {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) (A: EuclideanSpace' d →ₗ[ℝ] EuclideanSpace' d) (hA: A.det ≠ 0) :
    UnsignedLebesgueIntegral (fun x ↦ f (A x)) = |A.det|⁻¹ * hf.integ := by sorry

/-- Exercise 1.3.17 (Compatibility with the Riemann integral). -/
theorem RiemannIntegral.eq_UnsignedLebesgueIntegral {I: BoundedInterval} {f: ℝ → ℝ} (hf: RiemannIntegrableOn f I) :
    (riemannIntegral f I : EReal) = UnsignedLebesgueIntegral (Real.toEReal ∘ (fun x ↦ (f x) * (I.toSet.indicator' x)) ∘ EuclideanSpace'.equiv_Real) := by sorry

/-- The lower integral of a nonnegative constant times an indicator equals the constant
    times the measure of the set. -/
lemma lowerIntegral_const_indicator {d : ℕ} {c : ℝ} (hc : 0 ≤ c) {E : Set (EuclideanSpace' d)}
    (hE : LebesgueMeasurable E) :
    LowerUnsignedLebesgueIntegral (fun x => (c : EReal) * (Real.toEReal ∘ E.indicator') x) =
      (c : EReal) * Lebesgue_measure E := by
  have hg : UnsignedSimpleFunction (fun x => (c : EReal) * (Real.toEReal ∘ E.indicator') x) := by
    refine ⟨1, fun _ : Fin 1 => (c : EReal), fun _ : Fin 1 => E, ?_, ?_⟩
    · intro i
      constructor
      · simpa using hE
      · exact EReal.coe_nonneg.mpr hc
    · ext x
      simp [smul_eq_mul, EReal.indicator, Real.EReal_fun]
  rw [LowerUnsignedLebesgueIntegral.eq_simpleIntegral hg]
  rw [UnsignedSimpleFunction.integral_eq hg (k := 1) (c := fun _ : Fin 1 => (c : EReal))
    (E := fun _ : Fin 1 => E) (hmes := fun _ => hE)
    (hnonneg := fun _ => EReal.coe_nonneg.mpr hc)
    (heq := by ext x; simp [smul_eq_mul, EReal.indicator, Real.EReal_fun])]
  simp

/-- Non-strict level sets of an unsigned measurable function are measurable, via TFAE. -/
lemma level_ge_measurable {d : ℕ} {f : EuclideanSpace' d → EReal} (hf : UnsignedMeasurable f)
    (t : ℝ) : LebesgueMeasurable {x | (t : EReal) ≤ f x} := by
  have h5 : ∀ t : EReal, LebesgueMeasurable {x | f x ≥ t} :=
    ((UnsignedMeasurable.TFAE hf.1).out 0 5 (a := UnsignedMeasurable f)
      (b := ∀ t : EReal, LebesgueMeasurable {x | f x ≥ t})).mp hf
  exact h5 (t : EReal)

/-- The constant zero function is a simple unsigned function. -/
private lemma zero_simple_function {d : ℕ} :
    UnsignedSimpleFunction (fun _ : EuclideanSpace' d => (0 : EReal)) := by
  use 0, (fun i : Fin 0 => (0 : EReal)), (fun i : Fin 0 => (∅ : Set (EuclideanSpace' d)))
  constructor
  · intro i; fin_cases i
  · ext x; simp

/-- Lemma 1.3.15 (Markov's inequality) -/
theorem UnsignedLebesgueIntegral.markov_inequality {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) {t:ℝ} (ht: 0 < t) :
    Lebesgue_measure { x | f x ≥ t } ≤ hf.integ / (t:EReal) := by
  let E : Set (EuclideanSpace' d) := {x | (t : EReal) ≤ f x}
  let g : EuclideanSpace' d → EReal := fun x => (t : EReal) * (Real.toEReal ∘ E.indicator') x
  have hE : LebesgueMeasurable E := by
    dsimp [E]
    exact level_ge_measurable hf t
  have hg : UnsignedSimpleFunction g := by
    refine ⟨1, fun _ : Fin 1 => (t : EReal), fun _ : Fin 1 => E, ?_, ?_⟩
    · intro i
      constructor
      · simpa using hE
      · exact EReal.coe_nonneg.mpr (le_of_lt ht)
    · ext x
      simp [g, smul_eq_mul, EReal.indicator, Real.EReal_fun]
  have hg_le : ∀ x, g x ≤ f x := by
    intro x
    by_cases hx : (t : EReal) ≤ f x
    · have hgx : g x = (t : EReal) := by
        change (t : EReal) * EReal.indicator E x = (t : EReal)
        rw [EReal.indicator_of_mem (A := E) (x := x) hx, mul_one]
      rw [hgx]
      exact hx
    · have hgx : g x = 0 := by
        change (t : EReal) * EReal.indicator E x = 0
        rw [EReal.indicator_of_notMem (A := E) (x := x) hx, mul_zero]
      rw [hgx]
      exact hf.1 x
  have hL_eq : LowerUnsignedLebesgueIntegral g = (t : EReal) * Lebesgue_measure E := by
    simpa [g] using lowerIntegral_const_indicator (d := d) (c := t) (le_of_lt ht) hE
  have hL_le : LowerUnsignedLebesgueIntegral g ≤ hf.integ := by
    change LowerUnsignedLebesgueIntegral g ≤ LowerUnsignedLebesgueIntegral f
    rw [LowerUnsignedLebesgueIntegral.eq_simpleIntegral hg]
    unfold LowerUnsignedLebesgueIntegral
    exact le_sSup ⟨g, hg, fun x => ⟨hg_le x, rfl⟩⟩
  have hstep : (t : EReal) * Lebesgue_measure E ≤ hf.integ := by
    rw [← hL_eq]
    exact hL_le
  have htE : 0 < (t : EReal) := EReal.coe_pos.mpr ht
  have ht_ne : t ≠ 0 := ne_of_gt ht
  have hinv0 : 0 ≤ (t : EReal)⁻¹ := EReal.inv_nonneg_of_nonneg (le_of_lt htE)
  have hstep2 : Lebesgue_measure E ≤ (t : EReal)⁻¹ * hf.integ := by
    calc
      Lebesgue_measure E = (t : EReal)⁻¹ * ((t : EReal) * Lebesgue_measure E) := by
        rw [← mul_assoc]
        have h1 : (t : EReal)⁻¹ * (t : EReal) = 1 := by
          rw [← EReal.coe_inv t]
          rw [← EReal.coe_mul]
          have hrt : (t⁻¹ : ℝ) * t = 1 := inv_mul_cancel₀ ht_ne
          rw [hrt, EReal.coe_one]
        rw [h1, one_mul]
      _ ≤ (t : EReal)⁻¹ * hf.integ := mul_le_mul_of_nonneg_left hstep hinv0
  change Lebesgue_measure E ≤ hf.integ / (t : EReal)
  calc
    Lebesgue_measure E ≤ (t : EReal)⁻¹ * hf.integ := hstep2
    _ = hf.integ / (t : EReal) := by
      rw [EReal.div_eq_inv_mul]

/-- Exercise 1.3.18 (ii) -/
theorem UnsignedLebesgueIntegral.ae_finite {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) (hfin: UnsignedLebesgueIntegral f < ⊤) :
    AlmostAlways (fun x ↦ f x < ⊤) := by
  change hf.integ < ⊤ at hfin
  have hnonneg : 0 ≤ hf.integ := by
    change 0 ≤ LowerUnsignedLebesgueIntegral f
    unfold LowerUnsignedLebesgueIntegral
    have hz0 : (zero_simple_function (d := d)).integ = 0 := zero_unsigned_integral (zero_simple_function (d := d))
    exact le_sSup ⟨(fun _ : EuclideanSpace' d => (0 : EReal)), zero_simple_function (d := d),
      fun x => ⟨hf.1 x, hz0.symm⟩⟩
  have hfin_real : ∃ r : ℝ, 0 ≤ r ∧ hf.integ = (r : EReal) := by
    cases hfeq : hf.integ with
    | bot =>
        exfalso
        have hb : 0 ≤ (⊥ : EReal) := by rw [← hfeq]; exact hnonneg
        exact (not_le_of_gt EReal.bot_lt_zero) hb
    | top =>
        exfalso
        rw [hfeq] at hfin
        exact (lt_irrefl ⊤) hfin
    | coe r =>
        have hr0 : 0 ≤ r := by
          have hco : 0 ≤ (r : EReal) := by rw [← hfeq]; exact hnonneg
          exact EReal.coe_nonneg.mp hco
        exact ⟨r, hr0, rfl⟩
  rcases hfin_real with ⟨r, hr0, hr_eq⟩
  have hmarkov : ∀ n : ℕ, Lebesgue_measure {x | f x ≥ ((n : ℝ) + 1)} ≤ hf.integ / (((n : ℝ) + 1) : EReal) := by
    intro n
    exact UnsignedLebesgueIntegral.markov_inequality hf (by positivity)
  have hsub : ∀ n : ℕ, {x | f x = ⊤} ⊆ {x | f x ≥ ((n : ℝ) + 1)} := by
    intro n x hx
    have hx' : f x = ⊤ := hx
    change f x ≥ ((n : ℝ) + 1)
    rw [hx']
    exact le_top
  have hmeas_bound : ∀ n : ℕ, Lebesgue_measure {x | f x = ⊤} ≤ hf.integ / (((n : ℝ) + 1) : EReal) := by
    intro n
    calc
      Lebesgue_measure {x | f x = ⊤} ≤ Lebesgue_measure {x | f x ≥ ((n : ℝ) + 1)} :=
        Lebesgue_outer_measure.mono (hsub n)
      _ ≤ hf.integ / (((n : ℝ) + 1) : EReal) := hmarkov n
  have hbound : ∀ n : ℕ, Lebesgue_measure {x | f x = ⊤} ≤ (r / ((n : ℝ) + 1) : EReal) := by
    intro n
    calc
      Lebesgue_measure {x | f x = ⊤} ≤ hf.integ / (((n : ℝ) + 1) : EReal) := hmeas_bound n
      _ = (r / ((n : ℝ) + 1) : EReal) := by
        rw [hr_eq]
  have hμ0 : Lebesgue_measure {x | f x = ⊤} ≤ 0 := le_of_forall_nat_div_ereal hr0 hbound
  have hμ0' : Lebesgue_measure {x | f x = ⊤} = 0 := le_antisymm hμ0 (Lebesgue_outer_measure.nonneg _)
  have h_eq : {x | ¬ f x < ⊤} = {x | f x = ⊤} := by
    ext x
    constructor
    · intro hx
      cases hx' : f x with
      | bot =>
          exfalso
          apply hx
          rw [hx']
          exact lt_trans EReal.bot_lt_zero (EReal.coe_lt_top (0 : ℝ))
      | top => exact hx'
      | coe s =>
          exfalso
          apply hx
          rw [hx']
          exact EReal.coe_lt_top s
    · intro hx
      have hx' : f x = ⊤ := hx
      change ¬ f x < ⊤
      rw [hx']
      exact lt_irrefl ⊤
  unfold AlmostAlways
  change IsNull {x | ¬ f x < ⊤}
  rw [h_eq]
  change Lebesgue_outer_measure {x | f x = ⊤} = 0
  exact hμ0'

theorem UnsignedLebesgueIntegral.ae_finite_no_converse : ∃ (d:ℕ) (f: EuclideanSpace' d → EReal) (hf: UnsignedMeasurable f) (hfin: AlmostAlways (fun x ↦ f x < ⊤)), UnsignedLebesgueIntegral f = ⊤ := by sorry

/-- Exercise 1.3.18 (iii) -/
theorem UnsignedLebesgueIntegral.eq_zero_aeZero {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) :
     hf.integ = 0 ↔ AlmostAlways (fun x ↦ f x = 0) := by
  constructor
  · intro h0
    have hnull : ∀ n : ℕ, IsNull {x | f x ≥ (1 / ((n : ℝ) + 1) : ℝ)} := by
      intro n
      have ht : 0 < (1 : ℝ) / ((n : ℝ) + 1) := one_div_pos.mpr (by positivity)
      have hmarkov := UnsignedLebesgueIntegral.markov_inequality (d := d) hf ht
      have hle0 : Lebesgue_measure {x | f x ≥ (1 / ((n : ℝ) + 1) : ℝ)} ≤ 0 := by
        simpa [h0] using hmarkov
      exact le_antisymm hle0 (Lebesgue_outer_measure.nonneg _)
    have hae_ge : ∀ n : ℕ, AlmostAlways (fun x => ¬ f x ≥ (1 / ((n : ℝ) + 1) : ℝ)) := by
      intro n
      change IsNull {x | ¬ ¬ (f x ≥ (1 / ((n : ℝ) + 1) : ℝ))}
      have hset : {x | ¬ ¬ (f x ≥ (1 / ((n : ℝ) + 1) : ℝ))} =
          {x | f x ≥ (1 / ((n : ℝ) + 1) : ℝ)} := by
        ext x; simp
      rw [hset]
      exact hnull n
    have hae_all : AlmostAlways (fun x => ∀ n : ℕ, ¬ f x ≥ (1 / ((n : ℝ) + 1) : ℝ)) :=
      AlmostAlways.countable hae_ge
    have hz0 : ∀ x, (∀ n : ℕ, ¬ f x ≥ (1 / ((n : ℝ) + 1) : ℝ)) → f x = 0 := by
      intro x hx
      have hle0 : f x ≤ 0 := by
        apply le_of_forall_nat_one_div_ereal
        intro n
        exact le_of_lt (lt_of_not_ge (hx n))
      exact le_antisymm hle0 (hf.1 x)
    unfold AlmostAlways at hae_all ⊢
    change IsNull {x | ¬ f x = 0}
    apply IsNull.subset hae_all
    intro x hx hnot
    exact hx (hz0 x hnot)
  · intro hae
    change LowerUnsignedLebesgueIntegral f = 0
    have hz_meas : UnsignedMeasurable (fun _ : EuclideanSpace' d => (0 : EReal)) := by
      refine ⟨fun x => le_rfl, ⟨fun n : ℕ => (fun _ : EuclideanSpace' d => (0 : EReal)), ?_, ?_⟩⟩
      · intro n
        exact zero_simple_function
      · intro x
        exact tendsto_const_nhds
    have hL0 : LowerUnsignedLebesgueIntegral (fun _ : EuclideanSpace' d => (0 : EReal)) = 0 := by
      rw [LowerUnsignedLebesgueIntegral.eq_simpleIntegral (zero_simple_function (d := d))]
      exact zero_unsigned_integral (zero_simple_function (d := d))
    rw [LowerUnsignedLebesgueIntegral.integral_eq_integral_of_aeEqual hf hz_meas hae]
    exact hL0
