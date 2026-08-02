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

/-- Telescoping: sum over i of 1/(i+1) - 1/(i+2) equals 1 - 1/(n+1). -/
lemma sum_inv_sub {n : ℕ} :
    (∑ i : Fin n, ((1 : ℝ) / ((i.val + 1 : ℕ) : ℝ) - (1 : ℝ) / ((i.val + 2 : ℕ) : ℝ))) =
      1 - 1 / ((n + 1 : ℕ) : ℝ) := by
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ => (1 : ℝ) / ((k + 1 : ℕ) : ℝ) - (1 : ℝ) / ((k + 2 : ℕ) : ℝ)) n]
  have h := Finset.sum_range_sub' (fun k : ℕ => (1 : ℝ) / ((k + 1 : ℕ) : ℝ)) n
  rw [h]
  norm_num

/-- The preimage of the open interval (a,b) under the coordinate projection is the
    box with side (a,b). -/
lemma Ioo_preimage_eq_box' (a b : ℝ) :
    EuclideanSpace'.equiv_Real ⁻¹' Set.Ioo a b = (BoundedInterval.Ioo a b : Box 1).toSet := by
  rw [BoundedInterval.coe_of_box]
  ext x
  simp only [Set.mem_preimage, Set.mem_image]
  constructor
  · intro hx
    exact ⟨EuclideanSpace'.equiv_Real x, hx, EuclideanSpace'.equiv_Real.symm_apply_apply x⟩
  · rintro ⟨y, hy, hxy⟩
    have hyx : EuclideanSpace'.equiv_Real x = y := by
      rw [← hxy]
      exact EuclideanSpace'.equiv_Real.apply_symm_apply y
    rw [hyx]
    simpa using hy

/-- The preimage of the half-open interval from a to b under the coordinate
    projection is the box with that side. -/
lemma Ioc_preimage_eq_box' (a b : ℝ) :
    EuclideanSpace'.equiv_Real ⁻¹' Set.Ioc a b = (BoundedInterval.Ioc a b : Box 1).toSet := by
  rw [BoundedInterval.coe_of_box]
  ext x
  simp only [Set.mem_preimage, Set.mem_image]
  constructor
  · intro hx
    exact ⟨EuclideanSpace'.equiv_Real x, hx, EuclideanSpace'.equiv_Real.symm_apply_apply x⟩
  · rintro ⟨y, hy, hxy⟩
    have hyx : EuclideanSpace'.equiv_Real x = y := by
      rw [← hxy]
      exact EuclideanSpace'.equiv_Real.apply_symm_apply y
    rw [hyx]
    simpa using hy

/-- The preimage of an open interval under the coordinate projection is Lebesgue measurable. -/
lemma measurable_Ioo_preimage' (a b : ℝ) :
    LebesgueMeasurable (EuclideanSpace'.equiv_Real ⁻¹' Set.Ioo a b) := by
  rw [Ioo_preimage_eq_box' a b]
  exact Jordan_measurable.lebesgue (IsElementary.jordanMeasurable (IsElementary.box _))

/-- The preimage of a half-open interval under the coordinate projection is
    Lebesgue measurable. -/
lemma measurable_Ioc_preimage' (a b : ℝ) :
    LebesgueMeasurable (EuclideanSpace'.equiv_Real ⁻¹' Set.Ioc a b) := by
  rw [Ioc_preimage_eq_box' a b]
  exact Jordan_measurable.lebesgue (IsElementary.jordanMeasurable (IsElementary.box _))

/-- Lebesgue measure of the preimage of the open interval (a,b) is b - a. -/
lemma measure_Ioo_ab {a b : ℝ} (hab : a ≤ b) :
    Lebesgue_measure (EuclideanSpace'.equiv_Real ⁻¹' Set.Ioo a b) = ((b - a : ℝ) : EReal) := by
  let B : Box 1 := (BoundedInterval.Ioo a b : Box 1)
  have hset : EuclideanSpace'.equiv_Real ⁻¹' Set.Ioo a b = B.toSet := by
    simpa [B] using Ioo_preimage_eq_box' a b
  have hvol : |B|ᵥ = b - a := by
    rw [Box.volume_of_interval]
    simp [BoundedInterval.length, sub_nonneg.mpr hab]
  have h_elem : IsElementary B.toSet := IsElementary.box B
  rw [Lebesgue_measure, hset]
  calc
    Lebesgue_outer_measure B.toSet = ↑h_elem.measure :=
      Lebesgue_outer_measure.elementary B.toSet h_elem
    _ = (b - a : EReal) := by
      have hmeas : h_elem.measure = b - a := by
        calc
          h_elem.measure = ∑ B' ∈ ({B} : Finset (Box 1)), |B'|ᵥ :=
            h_elem.measure_eq (by simp) (by simp)
          _ = |B|ᵥ := by simp
          _ = b - a := hvol
      exact_mod_cast hmeas

/-- Lebesgue measure of the preimage of the half-open interval from a to b is
    b minus a. -/
lemma measure_Ioc_ab {a b : ℝ} (hab : a ≤ b) :
    Lebesgue_measure (EuclideanSpace'.equiv_Real ⁻¹' Set.Ioc a b) = ((b - a : ℝ) : EReal) := by
  let B : Box 1 := (BoundedInterval.Ioc a b : Box 1)
  have hset : EuclideanSpace'.equiv_Real ⁻¹' Set.Ioc a b = B.toSet := by
    simpa [B] using Ioc_preimage_eq_box' a b
  have hvol : |B|ᵥ = b - a := by
    rw [Box.volume_of_interval]
    simp [BoundedInterval.length, sub_nonneg.mpr hab]
  have h_elem : IsElementary B.toSet := IsElementary.box B
  rw [Lebesgue_measure, hset]
  calc
    Lebesgue_outer_measure B.toSet = ↑h_elem.measure :=
      Lebesgue_outer_measure.elementary B.toSet h_elem
    _ = (b - a : EReal) := by
      have hmeas : h_elem.measure = b - a := by
        calc
          h_elem.measure = ∑ B' ∈ ({B} : Finset (Box 1)), |B'|ᵥ :=
            h_elem.measure_eq (by simp) (by simp)
          _ = |B|ᵥ := by simp
          _ = b - a := hvol
      exact_mod_cast hmeas

/-- For u > 0 and r > 0: 1/sqrt(u) > r iff u < 1/r^2. -/
/- The spike counterexample for the upper integral's horizontal truncation: spike k has
    value 2^k on (2^k, 2^k + 2^{-2k}), 0 elsewhere.  U f = ⊤ but each ball truncation has
    integral ≤ 2, so the horizontal truncation limit fails for the upper integral. -/
noncomputable def f_horiz_piece (k : ℕ) : EuclideanSpace' 1 → EReal :=
  fun x => if (2 : ℝ) ^ k < EuclideanSpace'.equiv_Real x ∧
      EuclideanSpace'.equiv_Real x < (2 : ℝ) ^ k + ((2 : ℝ) ^ (2 * k : ℕ))⁻¹ then
      ((2 : ℝ) ^ k : EReal) else 0

/- The counterexample function: the sum of all spikes (at most one term is nonzero). -/
noncomputable def f_horiz : EuclideanSpace' 1 → EReal :=
  fun x => ∑' k : ℕ, f_horiz_piece k x

lemma f_horiz_piece_nonneg (k : ℕ) : ∀ x, 0 ≤ f_horiz_piece k x := by
  intro x
  unfold f_horiz_piece
  by_cases hx : (2 : ℝ) ^ k < EuclideanSpace'.equiv_Real x ∧
      EuclideanSpace'.equiv_Real x < (2 : ℝ) ^ k + ((2 : ℝ) ^ (2 * k : ℕ))⁻¹
  · rw [if_pos hx]
    rw [← EReal.coe_pow]
    exact EReal.coe_nonneg.mpr (pow_nonneg (by norm_num) k)
  · rw [if_neg hx]

lemma f_horiz_nonneg : Unsigned f_horiz := by
  intro x
  unfold f_horiz
  exact tsum_nonneg (fun k => f_horiz_piece_nonneg k x)

/- The spike intervals are pairwise disjoint. -/
lemma spikes_disjoint (j k : ℕ) (hjk : j ≠ k) :
    Set.Ioo ((2 : ℝ) ^ j) ((2 : ℝ) ^ j + ((2 : ℝ) ^ (2 * j : ℕ))⁻¹) ∩
      Set.Ioo ((2 : ℝ) ^ k) ((2 : ℝ) ^ k + ((2 : ℝ) ^ (2 * k : ℕ))⁻¹) = ∅ := by
  wlog hlt : j < k generalizing j k
  · have hkj_lt : k < j := lt_of_le_of_ne (not_lt.mp hlt) (fun h => hjk h.symm)
    have hPkj : Set.Ioo ((2 : ℝ) ^ k) ((2 : ℝ) ^ k + ((2 : ℝ) ^ (2 * k : ℕ))⁻¹) ∩
        Set.Ioo ((2 : ℝ) ^ j) ((2 : ℝ) ^ j + ((2 : ℝ) ^ (2 * j : ℕ))⁻¹) = ∅ :=
      this k j (fun h => hjk h.symm) hkj_lt
    simpa [Set.inter_comm] using hPkj
  · apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    rcases hx with ⟨hxj, hxk⟩
    have hxj_lt : x < (2 : ℝ) ^ j + ((2 : ℝ) ^ (2 * j : ℕ))⁻¹ := (Set.mem_Ioo.mp hxj).2
    have hxk_gt : (2 : ℝ) ^ k < x := (Set.mem_Ioo.mp hxk).1
    have hw_le_one : ((2 : ℝ) ^ (2 * j : ℕ))⁻¹ ≤ 1 := by
      exact (inv_le_one₀ (pow_pos (by norm_num) (2 * j))).mpr
        (one_le_pow₀ (by norm_num))
    have htwoj : (2 : ℝ) ^ j + 1 ≤ (2 : ℝ) ^ k := by
      have hjk1 : j + 1 ≤ k := Nat.succ_le_of_lt hlt
      have hpow_mono : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ k :=
        pow_le_pow_right₀ (by norm_num) hjk1
      have hsucc : (2 : ℝ) ^ j + 1 ≤ (2 : ℝ) ^ (j + 1) := by
        rw [pow_succ]
        have hone : 1 ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
        nlinarith
      exact le_trans hsucc hpow_mono
    have hle : (2 : ℝ) ^ j + ((2 : ℝ) ^ (2 * j : ℕ))⁻¹ ≤ (2 : ℝ) ^ k := by
      calc
        (2 : ℝ) ^ j + ((2 : ℝ) ^ (2 * j : ℕ))⁻¹ ≤ (2 : ℝ) ^ j + 1 := by
          exact add_le_add_right hw_le_one ((2 : ℝ) ^ j)
        _ ≤ (2 : ℝ) ^ k := htwoj
    have hxj_le : x < (2 : ℝ) ^ k := lt_of_lt_of_le hxj_lt hle
    exact (lt_irrefl x) (lt_trans hxj_le hxk_gt)

/- On the k-th spike the sum collapses to the single nonzero term. -/
lemma f_horiz_eq_piece {k : ℕ} {x : EuclideanSpace' 1}
    (hx : (2 : ℝ) ^ k < EuclideanSpace'.equiv_Real x ∧
      EuclideanSpace'.equiv_Real x < (2 : ℝ) ^ k + ((2 : ℝ) ^ (2 * k : ℕ))⁻¹) :
    f_horiz x = ((2 : ℝ) ^ k : EReal) := by
  have hzero : ∀ j : ℕ, j ≠ k → f_horiz_piece j x = 0 := by
    intro j hj
    unfold f_horiz_piece
    rw [if_neg]
    intro hcond
    have hu : EuclideanSpace'.equiv_Real x ∈
        Set.Ioo ((2 : ℝ) ^ j) ((2 : ℝ) ^ j + ((2 : ℝ) ^ (2 * j : ℕ))⁻¹) := ⟨hcond.1, hcond.2⟩
    have hu' : EuclideanSpace'.equiv_Real x ∈
        Set.Ioo ((2 : ℝ) ^ k) ((2 : ℝ) ^ k + ((2 : ℝ) ^ (2 * k : ℕ))⁻¹) := ⟨hx.1, hx.2⟩
    exact (Set.eq_empty_iff_forall_notMem.mp (spikes_disjoint j k hj) (EuclideanSpace'.equiv_Real x)) ⟨hu, hu'⟩
  change (∑' j : ℕ, f_horiz_piece j x) = ((2 : ℝ) ^ k : EReal)
  rw [tsum_eq_single k hzero]
  unfold f_horiz_piece
  rw [if_pos hx]

/- The k-th spike interval, as a subset of the space. -/
noncomputable def spike (k : ℕ) : Set (EuclideanSpace' 1) :=
  EuclideanSpace'.equiv_Real ⁻¹' Set.Ioo ((2 : ℝ) ^ k) ((2 : ℝ) ^ k + ((2 : ℝ) ^ (2 * k : ℕ))⁻¹)

/- For r ≥ 0, the level set of points with r < f_horiz x is the union of the spikes k with 2^k > r. -/
lemma f_horiz_eq_iUnion_gt (r : ℝ) (hr : 0 ≤ r) :
    {x : EuclideanSpace' 1 | (r : EReal) < f_horiz x} =
      ⋃ k : ℕ, (if (2 : ℝ) ^ k > r then spike k else ∅) := by
  ext x
  simp only [gt_iff_lt, Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · intro hx
    have hgt0 : (0 : EReal) < f_horiz x := lt_of_le_of_lt (EReal.coe_nonneg.mpr hr) hx
    have hmem : x ∈ ⋃ m : ℕ, spike m := by
      by_contra hnot
      have hz : ∀ j : ℕ, f_horiz_piece j x = 0 := by
        intro j
        unfold f_horiz_piece
        rw [if_neg]
        intro hcond
        have hxj : x ∈ ⋃ m : ℕ, spike m := by
          rw [Set.mem_iUnion]
          exact ⟨j, ⟨hcond.1, hcond.2⟩⟩
        exact hnot hxj
      have hf0 : f_horiz x = 0 := by
        unfold f_horiz
        simp [hz]
      exact (not_lt_of_ge (le_of_eq hf0)) hgt0
    rw [Set.mem_iUnion] at hmem
    rcases hmem with ⟨m, hm⟩
    have hf : f_horiz x = ((2 : ℝ) ^ m : EReal) :=
      f_horiz_eq_piece (Set.mem_Ioo.mp (Set.mem_preimage.mp hm))
    have hrm : r < (2 : ℝ) ^ m := by
      rw [hf] at hx
      have hx' : (r : EReal) < Real.toEReal ((2 : ℝ) ^ m) := by
        simpa [EReal.coe_pow] using hx
      exact EReal.coe_lt_coe_iff.mp hx'
    by_cases hkm : (2 : ℝ) ^ m > r
    · refine ⟨m, ?_⟩
      simp [hkm, hm]
    · exact False.elim ((not_lt_of_ge (le_of_not_gt hkm)) hrm)
  · intro hx
    rcases hx with ⟨k, hk⟩
    by_cases hkr : (2 : ℝ) ^ k > r
    · rw [if_pos hkr] at hk
      have hf : f_horiz x = ((2 : ℝ) ^ k : EReal) :=
        f_horiz_eq_piece (Set.mem_Ioo.mp (Set.mem_preimage.mp hk))
      rw [hf]
      rw [← EReal.coe_pow]
      exact EReal.coe_lt_coe_iff.mpr hkr
    · rw [if_neg hkr] at hk
      exact False.elim hk

/- f_horiz is unsigned measurable, via TFAE level sets. -/
lemma f_horiz_measurable : UnsignedMeasurable f_horiz := by
  have h5 : ∀ t : EReal, LebesgueMeasurable {x | f_horiz x > t} := by
    intro t
    by_cases ht : t = ⊤
    · have hset : {x | f_horiz x > t} = (∅ : Set (EuclideanSpace' 1)) := by
        ext x
        rw [ht]
        constructor
        · intro h
          change f_horiz x > ⊤ at h
          exact (not_lt_of_ge le_top) (gt_iff_lt.mp h)
        · intro h
          simp at h
      rw [hset]
      exact (isOpen_empty.measurable : LebesgueMeasurable (∅ : Set (EuclideanSpace' 1)))
    · cases t with
      | bot =>
          have hset : {x | f_horiz x > (⊥ : EReal)} = (Set.univ : Set (EuclideanSpace' 1)) := by
            ext x
            simp only [gt_iff_lt, Set.mem_univ, iff_true]
            exact lt_of_lt_of_le (EReal.bot_lt_coe (0 : ℝ)) (f_horiz_nonneg x)
          rw [hset]
          exact isOpen_univ.measurable
      | coe r =>
          by_cases hr : r < 0
          · have hset : {x | f_horiz x > (r : EReal)} = (Set.univ : Set (EuclideanSpace' 1)) := by
              ext x
              simp only [gt_iff_lt, Set.mem_univ, iff_true]
              exact lt_of_lt_of_le (EReal.coe_lt_coe_iff.mpr hr) (f_horiz_nonneg x)
            rw [hset]
            exact isOpen_univ.measurable
          · have hr0 : 0 ≤ r := le_of_not_gt hr
            have hset : {x | f_horiz x > (r : EReal)} =
                ⋃ k : ℕ, (if (2 : ℝ) ^ k > r then spike k else ∅) :=
              f_horiz_eq_iUnion_gt r hr0
            rw [hset]
            exact LebesgueMeasurable.countable_union (fun k => by
              by_cases hk : (2 : ℝ) ^ k > r
              · rw [if_pos hk]
                exact measurable_Ioo_preimage' ((2 : ℝ) ^ k) ((2 : ℝ) ^ k + ((2 : ℝ) ^ (2 * k : ℕ))⁻¹)
              · rw [if_neg hk]
                exact (isOpen_empty.measurable : LebesgueMeasurable (∅ : Set (EuclideanSpace' 1))))
      | top =>
          exact False.elim (ht rfl)
  exact ((UnsignedMeasurable.TFAE f_horiz_nonneg).out 4 0
    (a := ∀ t : EReal, LebesgueMeasurable {x | f_horiz x > t})
    (b := UnsignedMeasurable f_horiz)).mp h5

/- The upper integral of f_horiz is top: any simple g ≥ f has a top atom of positive
    measure, since f is unbounded on a positive-measure spike. -/
lemma f_horiz_upper : UpperUnsignedLebesgueIntegral f_horiz = ⊤ := by
  apply le_antisymm le_top
  unfold UpperUnsignedLebesgueIntegral
  apply le_sInf
  intro R hR
  rcases hR with ⟨g, hg, hcond⟩
  let hg' : UnsignedSimpleFunction g := hg
  rcases hg with ⟨k, c, E, hmes, heq⟩
  have hge : ∀ x, f_horiz x ≤ g x := fun x => (hcond x).1
  have hReq : R = hg'.integ := (hcond (Classical.arbitrary _)).2
  rw [hReq]
  have hE_meas : ∀ i, LebesgueMeasurable (E i) := fun i => (hmes i).1
  have hc_nonneg : ∀ i, c i ≥ 0 := fun i => (hmes i).2
  have hinteg : hg'.integ = ∑ i, c i * Lebesgue_measure (E i) :=
    UnsignedSimpleFunction.integral_eq hg' hE_meas hc_nonneg heq
  rw [hinteg]
  let C : ℝ := ∑ i, EReal.toReal (c i)
  have hcover : ∀ x, x ∈ {x : EuclideanSpace' 1 | (C : EReal) < f_horiz x} → ∃ i, x ∈ E i ∧ c i = ⊤ := by
    intro x hx
    by_contra hnot
    push_neg at hnot
    have hg_le_C : g x ≤ (C : EReal) := by
      rw [heq]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      calc
        (∑ i, c i * EReal.indicator (E i) x) ≤ (∑ i, ((c i).toReal : EReal)) := by
          apply Finset.sum_le_sum
          intro i hi
          by_cases hci : c i = ⊤
          · have hxnot : x ∉ E i := fun hxi => (hnot i hxi) hci
            rw [indicator_mul_not_mem (E i) (c i) x hxnot]
            simp [hci]
          · have hci_notbot : c i ≠ ⊥ := by
              intro hb
              have hci0 : (0 : EReal) ≤ ⊥ := by simpa [hb] using hc_nonneg i
              exact (not_le_of_gt EReal.bot_lt_zero) hci0
            by_cases hxi : x ∈ E i
            · rw [indicator_mul_mem (E i) (c i) x hxi]
              rw [EReal.coe_toReal hci hci_notbot]
            · rw [indicator_mul_not_mem (E i) (c i) x hxi]
              exact EReal.coe_nonneg.mpr (EReal.toReal_nonneg (hc_nonneg i))
        _ = (C : EReal) := by
          dsimp [C]
          exact (map_sum (⟨⟨Real.toEReal, EReal.coe_zero⟩, EReal.coe_add⟩ : ℝ →+ EReal)
            (fun i : Fin k => EReal.toReal (c i)) Finset.univ).symm
    have hgt : (C : EReal) < g x := lt_of_lt_of_le hx (hge x)
    exact (lt_irrefl (g x)) (lt_of_le_of_lt hg_le_C hgt)
  obtain ⟨m, hm⟩ : ∃ m : ℕ, C < (2 : ℝ) ^ m := by
    obtain ⟨N, hN⟩ := exists_nat_gt C
    have hNle0 : (N : ℝ) ≤ ((2 : ℕ) ^ N : ℝ) := by
      exact_mod_cast (Nat.le_of_lt (Nat.lt_two_pow_self : N < 2 ^ N))
    have hNle : (N : ℝ) ≤ (2 : ℝ) ^ N := by
      simpa [Nat.cast_pow] using hNle0
    exact ⟨N, lt_of_lt_of_le hN hNle⟩
  have hw_pos : 0 < ((2 : ℝ) ^ (2 * m : ℕ))⁻¹ := by
    exact inv_pos.mpr (pow_pos (by norm_num) (2 * m))
  have hmu_spike : Lebesgue_measure (spike m) = ((((2 : ℝ) ^ (2 * m : ℕ))⁻¹ : ℝ) : EReal) := by
    rw [show spike m = EuclideanSpace'.equiv_Real ⁻¹'
        Set.Ioo ((2 : ℝ) ^ m) ((2 : ℝ) ^ m + ((2 : ℝ) ^ (2 * m : ℕ))⁻¹) by rfl]
    simpa using (measure_Ioo_ab (le_add_of_nonneg_right (le_of_lt hw_pos)))
  have hspike_pos : (0 : EReal) < Lebesgue_measure (spike m) := by
    rw [hmu_spike]
    exact EReal.coe_pos.mpr hw_pos
  have hspike_sub : spike m ⊆ {x : EuclideanSpace' 1 | (C : EReal) < f_horiz x} := by
    intro x hx
    change (C : EReal) < f_horiz x
    have hf : f_horiz x = ((2 : ℝ) ^ m : EReal) :=
      f_horiz_eq_piece (Set.mem_Ioo.mp (Set.mem_preimage.mp hx))
    rw [hf]
    have hmE : (C : EReal) < Real.toEReal ((2 : ℝ) ^ m) := EReal.coe_lt_coe_iff.mpr hm
    simpa [EReal.coe_pow] using hmE
  have htop_atom : ∃ i₀ : Fin k, c i₀ = ⊤ ∧ 0 < Lebesgue_measure (E i₀) := by
    by_contra hnot
    push_neg at hnot
    let E' : Fin k → Set (EuclideanSpace' 1) := fun i => if c i = ⊤ then E i else ∅
    have hsub : spike m ⊆ ⋃ i : Fin k, E' i := by
      intro x hx
      rcases hcover x (hspike_sub hx) with ⟨i, hxEi, hci⟩
      rw [Set.mem_iUnion]
      exact ⟨i, by
        dsimp [E']
        rw [if_pos hci]
        exact hxEi⟩
    have hmeas0 : ∀ i, Lebesgue_measure (E' i) = 0 := by
      intro i
      by_cases hci : c i = ⊤
      · have hle : Lebesgue_measure (E i) ≤ 0 := hnot i hci
        have hz : Lebesgue_measure (E i) = 0 :=
          le_antisymm hle (Lebesgue_outer_measure.nonneg _)
        simp [E', hci, hz]
      · simp [E', hci]
    have hunion : Lebesgue_measure (⋃ i, E' i) ≤ 0 := by
      calc
        Lebesgue_measure (⋃ i, E' i) ≤ ∑ i, Lebesgue_measure (E' i) :=
          Lebesgue_outer_measure.finite_union_le E'
        _ = 0 := by simp [hmeas0]
    exact (not_lt_of_ge (le_trans (Lebesgue_outer_measure.mono hsub) hunion)) hspike_pos
  rcases htop_atom with ⟨i₀, hci₀, hmu₀⟩
  have hterm : c i₀ * Lebesgue_measure (E i₀) = ⊤ := by
    rw [hci₀, EReal.top_mul_of_pos hmu₀]
  have hprod_nonneg : ∀ i, 0 ≤ c i * Lebesgue_measure (E i) :=
    fun i => EReal.mul_nonneg (hc_nonneg i) (Lebesgue_outer_measure.nonneg _)
  have hge_top : ⊤ ≤ ∑ i, c i * Lebesgue_measure (E i) := by
    have hle := Finset.single_le_sum (fun i hi => hprod_nonneg i) (Finset.mem_univ i₀)
    rw [hterm] at hle
    exact hle
  exact hge_top

/- Algebraic helper: 2^k * (2^(2k))⁻¹ = (2⁻¹)^k. -/
lemma two_pow_mul_inv_two_mul (k : ℕ) :
    ((2 : ℝ) ^ k) * ((2 : ℝ) ^ (2 * k : ℕ))⁻¹ = ((2 : ℝ)⁻¹) ^ k := by
  rw [show 2 * k = k + k by omega]
  rw [← inv_pow, pow_add]
  rw [← mul_assoc, ← mul_pow]
  rw [mul_inv_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_pow, one_mul]

/- Geometric bound: the sum over Fin m of (2⁻¹)^i is at most 2. -/
lemma sum_pow_half_le_two (m : ℕ) : (∑ i : Fin m, ((2 : ℝ)⁻¹) ^ i.val) ≤ 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Fin.sum_univ_succ]
      have h0 : ((2 : ℝ)⁻¹) ^ (0 : Fin (m + 1)).val = 1 := by simp
      rw [h0]
      have hrew : (∑ i : Fin m, ((2 : ℝ)⁻¹) ^ i.succ.val) =
          (∑ i : Fin m, ((2 : ℝ)⁻¹) ^ i.val) * (2 : ℝ)⁻¹ := by
        calc
          (∑ i : Fin m, ((2 : ℝ)⁻¹) ^ i.succ.val) =
              (∑ i : Fin m, ((2 : ℝ)⁻¹) ^ i.val * (2 : ℝ)⁻¹) := by
                apply Finset.sum_congr rfl
                intro i hi
                simp [pow_succ]
          _ = (∑ i : Fin m, ((2 : ℝ)⁻¹) ^ i.val) * (2 : ℝ)⁻¹ := by
                exact (Finset.sum_mul (Finset.univ : Finset (Fin m))
                  (fun i : Fin m => ((2 : ℝ)⁻¹) ^ i.val) (2 : ℝ)⁻¹).symm
      rw [hrew]
      have hle : (∑ i : Fin m, ((2 : ℝ)⁻¹) ^ i.val) * (2 : ℝ)⁻¹ ≤ 2 * (2 : ℝ)⁻¹ := by
        exact mul_le_mul_of_nonneg_right ih (inv_nonneg.mpr (by norm_num))
      calc
        1 + (∑ i : Fin m, ((2 : ℝ)⁻¹) ^ i.val) * (2 : ℝ)⁻¹ ≤ 1 + 2 * (2 : ℝ)⁻¹ := by
          exact add_le_add_right hle 1
        _ = 2 := by norm_num

/- The ball truncation of f_horiz has upper integral bounded by 2 uniformly. -/
lemma f_horiz_trunc_upper_bounded : ∃ c : EReal, c < ⊤ ∧ ∀ n : ℕ, 1 ≤ n →
    UpperUnsignedLebesgueIntegral
      (f_horiz * Real.toEReal ∘ (Metric.ball (0 : EuclideanSpace' 1) n).indicator') ≤ c := by
  refine ⟨((2 : ℝ) : EReal), EReal.coe_lt_top 2, ?_⟩
  intro n hn
  let B : Set (EuclideanSpace' 1) := Metric.ball (0 : EuclideanSpace' 1) n
  let c : Fin (n + 1) → EReal := fun i => ((2 : ℝ) ^ i.val : EReal)
  let E : Fin (n + 1) → Set (EuclideanSpace' 1) := fun i => spike i.val ∩ B
  let h : EuclideanSpace' 1 → EReal := fun x => ∑ i, c i • EReal.indicator (E i) x
  have hc_nonneg : ∀ i, c i ≥ 0 := fun i => by
    dsimp [c]
    simp
  have hE_meas : ∀ i, LebesgueMeasurable (E i) := fun i =>
    LebesgueMeasurable.inter
      (measurable_Ioo_preimage' ((2 : ℝ) ^ i.val) ((2 : ℝ) ^ i.val + ((2 : ℝ) ^ (2 * i.val : ℕ))⁻¹))
      (IsOpen.measurable (Metric.isOpen_ball : IsOpen (Metric.ball (0 : EuclideanSpace' 1) n)))
  have hsimple : UnsignedSimpleFunction h := by
    refine ⟨n + 1, c, E, ?_, ?_⟩
    · intro i
      exact ⟨hE_meas i, hc_nonneg i⟩
    · ext x
      simp [h]
  have hterm_nonneg : ∀ x, ∀ j : Fin (n + 1), 0 ≤ c j • EReal.indicator (E j) x := by
    intro x j
    rw [smul_eq_mul]
    exact EReal.mul_nonneg (hc_nonneg j) (EReal.indicator_nonneg (E j) x)
  have hh_nonneg : ∀ x, 0 ≤ h x := by
    intro x
    dsimp [h]
    exact Finset.sum_nonneg (fun j hj => hterm_nonneg x j)
  have hh_ge : ∀ x, (f_horiz * Real.toEReal ∘ B.indicator') x ≤ h x := by
    intro x
    by_cases hxB : x ∈ B
    · let u : ℝ := EuclideanSpace'.equiv_Real x
      have hxball0 : dist x (0 : EuclideanSpace' 1) < (n : ℝ) := (Metric.mem_ball.mp hxB)
      have hu_abs : |u| < (n : ℝ) := by
        rw [EuclideanSpace'_dist_eq_Real_dist] at hxball0
        simpa [Real.dist_eq] using hxball0
      by_cases hspike : ∃ k : ℕ, u ∈ Set.Ioo ((2 : ℝ) ^ k) ((2 : ℝ) ^ k + ((2 : ℝ) ^ (2 * k : ℕ))⁻¹)
      · rcases hspike with ⟨k, hk⟩
        have hu_pos : 0 < u := lt_trans (pow_pos (by norm_num) k) hk.1
        have hu_lt_n : u < (n : ℝ) := lt_of_le_of_lt (le_abs_self u) hu_abs
        have hk_lt_n : k < n := by
          have h2k_lt_n : (2 : ℝ) ^ k < (n : ℝ) := lt_trans hk.1 hu_lt_n
          have hk_lt_2k : (k : ℝ) < (2 : ℝ) ^ k := by
            exact_mod_cast (Nat.lt_two_pow_self : k < 2 ^ k)
          exact_mod_cast (lt_trans hk_lt_2k h2k_lt_n)
        let i : Fin (n + 1) := ⟨k, by omega⟩
        have hf : f_horiz x = ((2 : ℝ) ^ k : EReal) := f_horiz_eq_piece hk
        have hxEi : x ∈ E i := by
          dsimp [E, B]
          exact ⟨hk, hxB⟩
        have hx_ge_c : c i ≤ h x := by
          dsimp [h]
          have htermi : c i • EReal.indicator (E i) x = c i := by
            rw [smul_eq_mul]
            rw [indicator_mul_mem (E i) (c i) x hxEi]
          have hle := Finset.single_le_sum (fun j hj => hterm_nonneg x j) (Finset.mem_univ i)
          rw [htermi] at hle
          exact hle
        have hlhs : (f_horiz * Real.toEReal ∘ B.indicator') x ≤ c i := by
          rw [show (f_horiz * Real.toEReal ∘ B.indicator') x =
              f_horiz x * Real.toEReal (B.indicator' x) by rfl]
          rw [Set.indicator'_of_mem hxB]
          rw [hf]
          dsimp [c, i]
          simp
        exact le_trans hlhs hx_ge_c
      · have hf0 : f_horiz x = 0 := by
          have hz : ∀ j : ℕ, f_horiz_piece j x = 0 := by
            intro j
            unfold f_horiz_piece
            rw [if_neg]
            intro hcond
            exact hspike ⟨j, ⟨hcond.1, hcond.2⟩⟩
          unfold f_horiz
          simp [hz]
        rw [show (f_horiz * Real.toEReal ∘ B.indicator') x =
            f_horiz x * Real.toEReal (B.indicator' x) by rfl]
        simp [hf0]
        exact hh_nonneg x
    · rw [show (f_horiz * Real.toEReal ∘ B.indicator') x =
        f_horiz x * Real.toEReal (B.indicator' x) by rfl]
      rw [Set.indicator'_of_notMem hxB]
      simp
      exact hh_nonneg x
  have hU_le : UpperUnsignedLebesgueIntegral (f_horiz * Real.toEReal ∘ B.indicator') ≤ hsimple.integ := by
    rw [← upperIntegral_simple hsimple]
    exact upperIntegral_mono hh_ge
  have hsimple_eq : h = ∑ i, (c i) • (EReal.indicator (E i)) := by
    ext x
    simp [h]
  have hinteg : hsimple.integ = ∑ i, c i * Lebesgue_measure (E i) :=
    UnsignedSimpleFunction.integral_eq hsimple hE_meas hc_nonneg hsimple_eq
  have hterm_le (i : Fin (n + 1)) :
      c i * Lebesgue_measure (E i) ≤ Real.toEReal (((2 : ℝ)⁻¹) ^ i.val) := by
    have hE_le : Lebesgue_measure (E i) ≤ Lebesgue_measure (spike i.val) :=
      Lebesgue_outer_measure.mono (by
        dsimp [E]
        intro x hx
        exact hx.1)
    have hmu : Lebesgue_measure (spike i.val) = Real.toEReal (((2 : ℝ) ^ (2 * i.val : ℕ))⁻¹) := by
      rw [show spike i.val = EuclideanSpace'.equiv_Real ⁻¹'
          Set.Ioo ((2 : ℝ) ^ i.val) ((2 : ℝ) ^ i.val + ((2 : ℝ) ^ (2 * i.val : ℕ))⁻¹) by rfl]
      simpa using (measure_Ioo_ab (le_add_of_nonneg_right
        (le_of_lt (inv_pos.mpr (pow_pos (by norm_num) (2 * i.val))))))
    have hc_mu : c i * Lebesgue_measure (spike i.val) = Real.toEReal (((2 : ℝ)⁻¹) ^ i.val) := by
      dsimp [c]
      rw [hmu]
      rw [← EReal.coe_pow]
      rw [← EReal.coe_mul]
      congr 1
      exact two_pow_mul_inv_two_mul i.val
    calc
      c i * Lebesgue_measure (E i) ≤ c i * Lebesgue_measure (spike i.val) := by
        exact mul_le_mul_of_nonneg_left hE_le (hc_nonneg i)
      _ = Real.toEReal (((2 : ℝ)⁻¹) ^ i.val) := hc_mu
  have hsum_le : (∑ i : Fin (n + 1), c i * Lebesgue_measure (E i)) ≤ (2 : EReal) := by
    calc
      (∑ i : Fin (n + 1), c i * Lebesgue_measure (E i))
          ≤ ∑ i : Fin (n + 1), Real.toEReal (((2 : ℝ)⁻¹) ^ i.val) := by
            apply Finset.sum_le_sum
            intro i hi
            exact hterm_le i
      _ = Real.toEReal (∑ i : Fin (n + 1), ((2 : ℝ)⁻¹) ^ i.val) := by
            exact (map_sum (⟨⟨Real.toEReal, EReal.coe_zero⟩, EReal.coe_add⟩ : ℝ →+ EReal)
              (fun i : Fin (n + 1) => ((2 : ℝ)⁻¹) ^ i.val) Finset.univ).symm
      _ ≤ ((2 : ℝ) : EReal) := by
            rw [EReal.coe_le_coe_iff]
            exact sum_pow_half_le_two (n + 1)
  have htotal : hsimple.integ ≤ ((2 : ℝ) : EReal) := by
    rw [hinteg]
    exact hsum_le
  exact le_trans hU_le htotal

/- The horizontal truncation limit FAILS for the upper integral: isFalse. -/
theorem eq_lim_horiz_trunc_upper_isFalse : ¬ (∀ (d:ℕ) (f: EuclideanSpace' d → EReal) (_hf: UnsignedMeasurable f),
    Filter.atTop.Tendsto (fun n:ℕ ↦ UpperUnsignedLebesgueIntegral (f * Real.toEReal ∘ (Metric.ball 0 n).indicator')) (nhds (UpperUnsignedLebesgueIntegral f))) := by
  intro h
  have hinst : Filter.atTop.Tendsto (fun n : ℕ =>
      UpperUnsignedLebesgueIntegral (f_horiz * Real.toEReal ∘ (Metric.ball (0 : EuclideanSpace' 1) n).indicator')) (nhds ⊤) := by
    simpa [f_horiz_upper] using h 1 f_horiz f_horiz_measurable
  have htop_seq : ∀ z : ℝ, ∀ᶠ n : ℕ in atTop, (z : EReal) <
      UpperUnsignedLebesgueIntegral (f_horiz * Real.toEReal ∘ (Metric.ball (0 : EuclideanSpace' 1) n).indicator') := by
    intro z
    have hmem : Set.Ioi (z : EReal) ∈ 𝓝 (⊤ : EReal) := by
      exact (EReal.mem_nhds_top_iff).mpr ⟨z, fun y hy => hy⟩
    simpa using (hinst.eventually hmem)
  rcases f_horiz_trunc_upper_bounded with ⟨c, hc_lt_top, hbounded⟩
  obtain ⟨z, hc_lt_z⟩ : ∃ z : ℝ, c < (z : EReal) := by
    cases c with
    | bot => exact ⟨0, EReal.bot_lt_coe 0⟩
    | coe r => exact ⟨r + 1, by rw [EReal.coe_lt_coe_iff]; linarith⟩
    | top => exact False.elim (not_lt_of_ge le_top hc_lt_top)
  have hev := htop_seq z
  rw [eventually_atTop] at hev
  rcases hev with ⟨N, hN⟩
  let n0 : ℕ := max N 1
  have hn0_N : N ≤ n0 := le_max_left N 1
  have hn0_ge1 : 1 ≤ n0 := le_max_right N 1
  have hs_gt : (z : EReal) < UpperUnsignedLebesgueIntegral
      (f_horiz * Real.toEReal ∘ (Metric.ball (0 : EuclideanSpace' 1) n0).indicator') :=
    hN n0 hn0_N
  have hs_le : UpperUnsignedLebesgueIntegral
      (f_horiz * Real.toEReal ∘ (Metric.ball (0 : EuclideanSpace' 1) n0).indicator') ≤ c :=
    hbounded n0 hn0_ge1
  exact (lt_irrefl (z : EReal)) (lt_trans hs_gt (lt_of_le_of_lt hs_le hc_lt_z))

def UpperUnsignedLebesgueIntegral.eq_lim_horiz_trunc : Decidable (∀ (d:ℕ) (f: EuclideanSpace' d → EReal) (_hf: UnsignedMeasurable f), Filter.atTop.Tendsto (fun n:ℕ ↦ UpperUnsignedLebesgueIntegral (f * Real.toEReal ∘ (Metric.ball 0 n).indicator')) (nhds (UpperUnsignedLebesgueIntegral f))) := by
  apply isFalse
  exact eq_lim_horiz_trunc_upper_isFalse
lemma sqrt_inv_gt_iff {r : ℝ} (hr : 0 < r) {u : ℝ} (hu : 0 < u) :
    (r : EReal) < ((1 / Real.sqrt u : ℝ) : EReal) ↔ u < 1 / r ^ 2 := by
  rw [EReal.coe_lt_coe_iff]
  rw [lt_div_iff₀ (Real.sqrt_pos.2 hu)]
  rw [mul_comm]
  rw [← lt_div_iff₀ hr]
  have hsq : (1 / r) ^ 2 = 1 / r ^ 2 := by ring
  rw [← hsq]
  exact Real.sqrt_lt (le_of_lt hu) (div_nonneg zero_le_one hr.le)

/-- f(x) = 1/sqrt(x) on (0,1), 0 elsewhere. -/
noncomputable def f_inv_sqrt : EuclideanSpace' 1 → EReal :=
  fun x => if (0 : ℝ) < EuclideanSpace'.equiv_Real x ∧ EuclideanSpace'.equiv_Real x < 1 then
    ((1 : ℝ) / Real.sqrt (EuclideanSpace'.equiv_Real x) : ℝ) else 0

/-- f is nonnegative. -/
lemma f_inv_sqrt_nonneg : Unsigned f_inv_sqrt := by
  intro x
  unfold f_inv_sqrt
  by_cases hx : (0 : ℝ) < EuclideanSpace'.equiv_Real x ∧ EuclideanSpace'.equiv_Real x < 1
  · rw [if_pos hx]
    exact EReal.coe_nonneg.mpr (div_nonneg zero_le_one (Real.sqrt_nonneg _))
  · rw [if_neg hx]

/-- f is unsigned measurable, via TFAE level sets (open intervals). -/
lemma f_inv_sqrt_measurable : UnsignedMeasurable f_inv_sqrt := by
  have h5 : ∀ t : EReal, LebesgueMeasurable {x | f_inv_sqrt x > t} := by
    intro t
    by_cases ht : t = ⊤
    · have hset : {x | f_inv_sqrt x > t} = (∅ : Set (EuclideanSpace' 1)) := by
        ext x
        rw [ht]
        constructor
        · intro h
          change f_inv_sqrt x > ⊤ at h
          exact (not_lt_of_ge le_top) (gt_iff_lt.mp h)
        · intro h
          simp at h
      rw [hset]
      exact (isOpen_empty.measurable : LebesgueMeasurable (∅ : Set (EuclideanSpace' 1)))
    · cases t with
      | bot =>
          have hset : {x | f_inv_sqrt x > (⊥ : EReal)} = (Set.univ : Set (EuclideanSpace' 1)) := by
            ext x
            simp only [gt_iff_lt, Set.mem_univ, iff_true]
            exact lt_of_lt_of_le (EReal.bot_lt_coe (0 : ℝ)) (f_inv_sqrt_nonneg x)
          rw [hset]
          exact isOpen_univ.measurable
      | coe r =>
          by_cases hr : r < 0
          · have hset : {x | f_inv_sqrt x > (r : EReal)} = (Set.univ : Set (EuclideanSpace' 1)) := by
              ext x
              simp only [gt_iff_lt, Set.mem_univ, iff_true]
              exact lt_of_lt_of_le (EReal.coe_lt_coe_iff.mpr hr) (f_inv_sqrt_nonneg x)
            rw [hset]
            exact isOpen_univ.measurable
          · have hr0 : 0 ≤ r := le_of_not_gt hr
            by_cases hrz : r = 0
            · have hset : {x | f_inv_sqrt x > (r : EReal)} = EuclideanSpace'.equiv_Real ⁻¹' Set.Ioo (0 : ℝ) 1 := by
                ext x
                rw [hrz]
                simp only [gt_iff_lt, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ioo]
                unfold f_inv_sqrt
                by_cases hx : (0 : ℝ) < EuclideanSpace'.equiv_Real x ∧ EuclideanSpace'.equiv_Real x < 1
                · rw [if_pos hx]
                  constructor
                  · intro _
                    exact hx
                  · intro _
                    exact EReal.coe_lt_coe_iff.mpr (div_pos zero_lt_one (Real.sqrt_pos.2 hx.1))
                · rw [if_neg hx]
                  constructor
                  · intro h
                    exact False.elim (lt_irrefl (0 : EReal) h)
                  · intro h
                    exact False.elim (hx h)
              rw [hset]
              exact measurable_Ioo_preimage' 0 1
            · have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hrz)
              let c : ℝ := min 1 (1 / r ^ 2)
              have hset : {x | f_inv_sqrt x > (r : EReal)} = EuclideanSpace'.equiv_Real ⁻¹' Set.Ioo (0 : ℝ) c := by
                ext x
                simp only [gt_iff_lt, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ioo]
                unfold f_inv_sqrt
                by_cases hx : (0 : ℝ) < EuclideanSpace'.equiv_Real x ∧ EuclideanSpace'.equiv_Real x < 1
                · rw [if_pos hx]
                  rw [sqrt_inv_gt_iff hrpos hx.1]
                  constructor
                  · intro h
                    exact ⟨hx.1, lt_min hx.2 h⟩
                  · intro h
                    exact lt_of_lt_of_le h.2 (min_le_right 1 (1 / r ^ 2))
                · rw [if_neg hx]
                  constructor
                  · intro h
                    exact False.elim (not_lt_of_ge (EReal.coe_le_coe_iff.mpr hrpos.le) h)
                  · intro h
                    exact False.elim (hx ⟨h.1, lt_of_lt_of_le h.2 (min_le_left 1 (1 / r ^ 2))⟩)
              rw [hset]
              exact measurable_Ioo_preimage' 0 c
      | top =>
          exact False.elim (ht rfl)
  exact ((UnsignedMeasurable.TFAE f_inv_sqrt_nonneg).out 4 0
    (a := ∀ t : EReal, LebesgueMeasurable {x | f_inv_sqrt x > t})
    (b := UnsignedMeasurable f_inv_sqrt)).mp h5

/-- The upper integral of f is top: any simple g ≥ f pointwise has a top-valued
    atom on a positive-measure set. -/
lemma f_inv_sqrt_upper : UpperUnsignedLebesgueIntegral f_inv_sqrt = ⊤ := by
  apply le_antisymm le_top
  unfold UpperUnsignedLebesgueIntegral
  apply le_sInf
  intro R hR
  rcases hR with ⟨g, hg, hcond⟩
  let hg' : UnsignedSimpleFunction g := hg
  rcases hg with ⟨k, c, E, hmes, heq⟩
  have hge : ∀ x, f_inv_sqrt x ≤ g x := fun x => (hcond x).1
  have hReq : R = hg'.integ := (hcond (Classical.arbitrary _)).2
  rw [hReq]
  have hE_meas : ∀ i, LebesgueMeasurable (E i) := fun i => (hmes i).1
  have hc_nonneg : ∀ i, c i ≥ 0 := fun i => (hmes i).2
  have hinteg : hg'.integ = ∑ i, c i * Lebesgue_measure (E i) :=
    UnsignedSimpleFunction.integral_eq hg' hE_meas hc_nonneg heq
  rw [hinteg]
  let cf : Fin k → EReal := fun i => (EReal.toReal (c i) : EReal)
  let S : EReal := ∑ i, cf i
  have hS_lt_top : S < ⊤ := by
    dsimp [S, cf]
    exact EReal_sum_lt_top_of_all (fun i => (EReal.toReal (c i) : EReal))
      (fun i => EReal.coe_lt_top (EReal.toReal (c i)))
  have hS_nonneg : 0 ≤ S := by
    dsimp [S, cf]
    exact Finset.sum_nonneg
      (fun i hi => EReal.coe_nonneg.mpr (EReal.toReal_nonneg (hc_nonneg i)))
  let M : ℝ := S.toReal + 1
  have hM_pos : 0 < M := by
    dsimp [M]
    have htr : 0 ≤ S.toReal := EReal.toReal_nonneg hS_nonneg
    linarith
  have hS_lt_M : S < (M : EReal) := by
    dsimp [M]
    calc
      S ≤ (S.toReal : EReal) := EReal.le_coe_toReal (ne_of_lt hS_lt_top)
      _ < ((S.toReal + 1 : ℝ) : EReal) := EReal.coe_lt_coe_iff.mpr (by linarith)
  let a : ℝ := min 1 (1 / M ^ 2)
  have ha_pos : 0 < a := by
    dsimp [a]
    exact lt_min zero_lt_one (div_pos zero_lt_one (sq_pos_of_pos hM_pos))
  have hcover : ∀ x, EuclideanSpace'.equiv_Real x ∈ Set.Ioo (0 : ℝ) a →
      ∃ i, x ∈ E i ∧ c i = ⊤ := by
    intro x hx
    let u : ℝ := EuclideanSpace'.equiv_Real x
    have hu0 : 0 < u := (Set.mem_Ioo.mp hx).1
    have hu1 : u < 1 := lt_of_lt_of_le (Set.mem_Ioo.mp hx).2 (min_le_left 1 (1 / M ^ 2))
    have hf_x : f_inv_sqrt x = ((1 / Real.sqrt u : ℝ) : EReal) := by
      unfold f_inv_sqrt
      rw [if_pos ⟨hu0, hu1⟩]
    have hf_gt_M : ((M : ℝ) : EReal) < f_inv_sqrt x := by
      rw [hf_x]
      rw [sqrt_inv_gt_iff hM_pos hu0]
      exact lt_of_lt_of_le (Set.mem_Ioo.mp hx).2 (min_le_right 1 (1 / M ^ 2))
    by_contra hnot
    push_neg at hnot
    have hg_le_S : g x ≤ S := by
      rw [heq]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      calc
        (∑ i, c i * EReal.indicator (E i) x) ≤ ∑ i, cf i := by
          apply Finset.sum_le_sum
          intro i hi
          dsimp [cf]
          by_cases hci : c i = ⊤
          · have hxnot : x ∉ E i := fun hxi => (hnot i hxi) hci
            rw [indicator_mul_not_mem (E i) (c i) x hxnot]
            simp [hci]
          · have hci_lt : c i < ⊤ := lt_top_iff_ne_top.mpr hci
            have hci_notbot : c i ≠ ⊥ := by
              intro hb
              have hci0 : (0 : EReal) ≤ ⊥ := by simpa [hb] using hc_nonneg i
              exact (not_le_of_gt EReal.bot_lt_zero) hci0
            by_cases hxi : x ∈ E i
            · rw [indicator_mul_mem (E i) (c i) x hxi]
              rw [EReal.coe_toReal hci hci_notbot]
            · rw [indicator_mul_not_mem (E i) (c i) x hxi]
              exact EReal.coe_nonneg.mpr (EReal.toReal_nonneg (hc_nonneg i))
        _ = S := by rfl
    have hgt : (M : EReal) < g x := lt_of_lt_of_le hf_gt_M (hge x)
    have h1 : g x < g x := by
      calc
        g x ≤ S := hg_le_S
        _ < (M : EReal) := hS_lt_M
        _ < g x := hgt
    exact (lt_irrefl (g x)) h1
  have htop_atom : ∃ i₀ : Fin k, c i₀ = ⊤ ∧ 0 < Lebesgue_measure (E i₀) := by
    by_contra hnot
    push_neg at hnot
    let E' : Fin k → Set (EuclideanSpace' 1) := fun i => if c i = ⊤ then E i else ∅
    have hsub : EuclideanSpace'.equiv_Real ⁻¹' Set.Ioo (0 : ℝ) a ⊆ ⋃ i : Fin k, E' i := by
      intro x hx
      rcases hcover x hx with ⟨i, hxEi, hci⟩
      rw [Set.mem_iUnion]
      exact ⟨i, by
        dsimp [E']
        rw [if_pos hci]
        exact hxEi⟩
    have hmeas0 : ∀ i, Lebesgue_measure (E' i) = 0 := by
      intro i
      by_cases hci : c i = ⊤
      · have hle : Lebesgue_measure (E i) ≤ 0 := hnot i hci
        have hz : Lebesgue_measure (E i) = 0 :=
          le_antisymm hle (Lebesgue_outer_measure.nonneg _)
        simp [E', hci, hz]
      · simp [E', hci]
    have hunion : Lebesgue_measure (⋃ i, E' i) ≤ 0 := by
      calc
        Lebesgue_measure (⋃ i, E' i) ≤ ∑ i, Lebesgue_measure (E' i) :=
          Lebesgue_outer_measure.finite_union_le E'
        _ = 0 := by simp [hmeas0]
    have hmu_a : Lebesgue_measure (EuclideanSpace'.equiv_Real ⁻¹' Set.Ioo (0 : ℝ) a) = ((a - 0 : ℝ) : EReal) :=
      measure_Ioo_ab (show (0 : ℝ) ≤ a from le_of_lt ha_pos)
    have hpos : (0 : EReal) < Lebesgue_measure (EuclideanSpace'.equiv_Real ⁻¹' Set.Ioo (0 : ℝ) a) := by
      rw [hmu_a]
      exact EReal.coe_pos.mpr (by simpa using ha_pos)
    exact (not_lt_of_ge (le_trans (Lebesgue_outer_measure.mono hsub) hunion)) hpos
  rcases htop_atom with ⟨i₀, hci₀, hmu₀⟩
  have hterm : c i₀ * Lebesgue_measure (E i₀) = ⊤ := by
    rw [hci₀, EReal.top_mul_of_pos hmu₀]
  have hprod_nonneg : ∀ i, 0 ≤ c i * Lebesgue_measure (E i) :=
    fun i => EReal.mul_nonneg (hc_nonneg i) (Lebesgue_outer_measure.nonneg _)
  have hge_top : ⊤ ≤ ∑ i, c i * Lebesgue_measure (E i) := by
    have hle := Finset.single_le_sum (fun i hi => hprod_nonneg i) (Finset.mem_univ i₀)
    rw [hterm] at hle
    exact hle
  exact hge_top

/-- The dyadic-grid upper bound for min(f, n): U(min(f, n)) ≤ c uniformly. -/
lemma f_inv_sqrt_trunc_upper_bounded : ∃ c : EReal, c < ⊤ ∧ ∀ n : ℕ, 1 ≤ n →
    UpperUnsignedLebesgueIntegral (fun x => min (f_inv_sqrt x) n) ≤ c := by
  refine ⟨((8 : ℝ) : EReal), EReal.coe_lt_top 8, ?_⟩
  intro n hn
  let fn : EuclideanSpace' 1 → EReal := fun x => min (f_inv_sqrt x) n
  let c : Fin (n + 1) → EReal := fun i => if i.val = 0 then ((n : ℝ) : EReal) else
    (((i.val + 1 : ℕ) : ℝ) : EReal)
  let E : Fin (n + 1) → Set (EuclideanSpace' 1) := fun i => if i.val = 0 then
      EuclideanSpace'.equiv_Real ⁻¹' Set.Ioc (0 : ℝ) (1 / (n : ℝ) ^ 2) else
      EuclideanSpace'.equiv_Real ⁻¹' Set.Ioc (1 / ((i.val + 1 : ℕ) : ℝ) ^ 2) (1 / (i.val : ℝ) ^ 2)
  let h : EuclideanSpace' 1 → EReal := fun x => ∑ i, c i • EReal.indicator (E i) x
  have hc_nonneg : ∀ i, c i ≥ 0 := by
    intro i
    by_cases hz : i.val = 0
    · dsimp [c]
      rw [if_pos hz]
      exact EReal.coe_nonneg.mpr (Nat.cast_nonneg n)
    · dsimp [c]
      rw [if_neg hz]
      exact EReal.coe_nonneg.mpr (Nat.cast_nonneg (i.val + 1))
  have hE_meas : ∀ i, LebesgueMeasurable (E i) := by
    intro i
    by_cases hz : i.val = 0
    · dsimp [E]
      rw [if_pos hz]
      exact measurable_Ioc_preimage' 0 (1 / (n : ℝ) ^ 2)
    · dsimp [E]
      rw [if_neg hz]
      exact measurable_Ioc_preimage' (1 / ((i.val + 1 : ℕ) : ℝ) ^ 2) (1 / (i.val : ℝ) ^ 2)
  have hsimple : UnsignedSimpleFunction h := by
    refine ⟨n + 1, c, E, ?_, ?_⟩
    · intro i
      exact ⟨hE_meas i, hc_nonneg i⟩
    · ext x
      simp [h]
  have hterm_nonneg : ∀ x, ∀ j : Fin (n + 1), 0 ≤ c j • EReal.indicator (E j) x := by
    intro x j
    rw [smul_eq_mul]
    exact EReal.mul_nonneg (hc_nonneg j) (EReal.indicator_nonneg (E j) x)
  have hh_nonneg : ∀ x, 0 ≤ h x := by
    intro x
    dsimp [h]
    exact Finset.sum_nonneg (fun j hj => hterm_nonneg x j)
  have hh_ge : ∀ x, fn x ≤ h x := by
    intro x
    let u : ℝ := EuclideanSpace'.equiv_Real x
    by_cases hx : (0 : ℝ) < u ∧ u < 1
    · by_cases hun : u ≤ 1 / (n : ℝ) ^ 2
      · have hxE0 : x ∈ E ⟨0, by omega⟩ := by
          dsimp [E]
          have huI : u ∈ Set.Ioc (0 : ℝ) (1 / (n : ℝ) ^ 2) := ⟨hx.1, hun⟩
          simpa [u] using huI
        have hx_ge_n : (n : EReal) ≤ h x := by
          dsimp [h]
          have hterm0 : c ⟨0, by omega⟩ • EReal.indicator (E ⟨0, by omega⟩) x = (n : EReal) := by
            rw [smul_eq_mul]
            rw [indicator_mul_mem (E ⟨0, by omega⟩) (c ⟨0, by omega⟩) x hxE0]
            dsimp [c]
          have hle := Finset.single_le_sum (fun j hj => hterm_nonneg x j) (Finset.mem_univ ⟨0, by omega⟩)
          rw [hterm0] at hle
          exact hle
        exact le_trans (min_le_right (f_inv_sqrt x) (n : EReal)) hx_ge_n
      · have hu_gt0 : 1 / (n : ℝ) ^ 2 < u := lt_of_not_ge hun
        have hn2 : 2 ≤ n := by
          by_contra hnot2
          have hn_le1 : n ≤ 1 := by omega
          have hn_eq1 : n = 1 := le_antisymm hn_le1 hn
          have : (1 : ℝ) < u := by simpa [hn_eq1] using hu_gt0
          exact (lt_irrefl (1 : ℝ)) (lt_trans this hx.2)
        let s : Finset ℕ := (Finset.range n).filter (fun j => u ≤ 1 / (j : ℝ) ^ 2)
        have hs_ne : s.Nonempty := by
          refine ⟨1, ?_⟩
          rw [Finset.mem_filter]
          constructor
          · exact Finset.mem_range.mpr (by omega)
          · simpa using hx.2.le
        let m : ℕ := s.max' hs_ne
        have hm_mem : m ∈ s := Finset.max'_mem s hs_ne
        have hm_range : m < n := (Finset.mem_range.mp (Finset.mem_filter.mp hm_mem).1)
        have hm_le : u ≤ 1 / (m : ℝ) ^ 2 := (Finset.mem_filter.mp hm_mem).2
        have hm_ge1 : 1 ≤ m := by
          by_contra hm0
          have hm_eq : m = 0 := by omega
          have : u ≤ (0 : ℝ) := by simpa [hm_eq] using hm_le
          exact (not_le_of_gt hx.1) this
        have hu_gt_next : 1 / ((m + 1 : ℕ) : ℝ) ^ 2 < u := by
          by_contra hnot
          have hu_le' : u ≤ 1 / ((m + 1 : ℕ) : ℝ) ^ 2 := le_of_not_gt hnot
          have hm1_lt : m + 1 < n := by
            by_contra hge
            have hn_le : n ≤ m + 1 := le_of_not_gt hge
            have hm1_eq_n : m + 1 = n := le_antisymm (Nat.succ_le_of_lt hm_range) hn_le
            have hu_le_n : u ≤ 1 / (n : ℝ) ^ 2 := by
              simpa [← hm1_eq_n] using hu_le'
            exact (not_le_of_gt hu_gt0) hu_le_n
          have hm1_in : m + 1 ∈ s := by
            rw [Finset.mem_filter]
            exact ⟨Finset.mem_range.mpr hm1_lt, hu_le'⟩
          have hm1_le_m : m + 1 ≤ m := Finset.le_max' s (m + 1) hm1_in
          exact (not_lt_of_ge hm1_le_m) (Nat.lt_succ_self m)
        let i : Fin (n + 1) := ⟨m, by omega⟩
        have hi_val : i.val = m := rfl
        have hxEi : x ∈ E i := by
          have hm_ne0 : m ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hm_ge1)
          dsimp [E]
          rw [if_neg (by
            intro hz
            have : 1 ≤ i.val := by simpa [hi_val] using hm_ge1
            exact (ne_of_gt this) hz)]
          · have huI : u ∈ Set.Ioc (1 / ((m + 1 : ℕ) : ℝ) ^ 2) (1 / (m : ℝ) ^ 2) :=
              ⟨hu_gt_next, hm_le⟩
            have huI' : u ∈ Set.Ioc (1 / ((i.val + 1 : ℕ) : ℝ) ^ 2) (1 / (i.val : ℝ) ^ 2) := by
              simpa [i] using huI
            simpa [u] using huI'
        have hf_x : f_inv_sqrt x = ((1 / Real.sqrt u : ℝ) : EReal) := by
          unfold f_inv_sqrt
          rw [if_pos ⟨hx.1, hx.2⟩]
        have hc_eq : c i = (((m + 1 : ℕ) : ℝ) : EReal) := by
          have hm_ne0 : m ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hm_ge1)
          dsimp [c]
          simp [hi_val, hm_ne0]
        have hf_le_c : f_inv_sqrt x ≤ c i := by
          rw [hc_eq]
          rw [hf_x]
          rw [EReal.coe_le_coe_iff]
          apply le_of_not_gt
          intro h
          have hu_lt : u < 1 / ((m + 1 : ℕ) : ℝ) ^ 2 :=
            (sqrt_inv_gt_iff (by exact_mod_cast (Nat.succ_pos m)) hx.1).mp
              (EReal.coe_lt_coe_iff.mpr h)
          exact (lt_irrefl u) (lt_trans hu_lt hu_gt_next)
        have hc_le_n : c i ≤ (n : EReal) := by
          rw [hc_eq]
          exact EReal.coe_le_coe_iff.mpr (by exact_mod_cast (Nat.succ_le_of_lt hm_range))
        have hfn : fn x = f_inv_sqrt x := by
          dsimp [fn]
          exact min_eq_left (le_trans hf_le_c hc_le_n)
        have hx_ge_c : c i ≤ h x := by
          dsimp [h]
          have htermi : c i • EReal.indicator (E i) x = c i := by
            rw [smul_eq_mul]
            rw [indicator_mul_mem (E i) (c i) x hxEi]
          have hle := Finset.single_le_sum (fun j hj => hterm_nonneg x j) (Finset.mem_univ i)
          rw [htermi] at hle
          exact hle
        exact le_trans (le_trans (le_of_eq hfn) hf_le_c) hx_ge_c
    · have hf0 : f_inv_sqrt x = 0 := by
        unfold f_inv_sqrt
        rw [if_neg (by simpa [u] using hx)]
      have hfn0 : fn x = 0 := by
        dsimp [fn]
        rw [hf0]
        exact min_eq_left (EReal.coe_nonneg.mpr (Nat.cast_nonneg n))
      exact le_trans (le_of_eq hfn0) (hh_nonneg x)
  have hU_le : UpperUnsignedLebesgueIntegral fn ≤ hsimple.integ := by
    rw [← upperIntegral_simple hsimple]
    exact upperIntegral_mono hh_ge
  have hsimple_eq : h = ∑ i, (c i) • (EReal.indicator (E i)) := by
    ext x
    simp [h]
  have hinteg : hsimple.integ = ∑ i, c i * Lebesgue_measure (E i) :=
    UnsignedSimpleFunction.integral_eq hsimple hE_meas hc_nonneg hsimple_eq
  have hterm0 : c ⟨0, by omega⟩ * Lebesgue_measure (E ⟨0, by omega⟩) ≤ ((1 / (n : ℝ) : ℝ) : EReal) := by
    have hc0 : c ⟨0, by omega⟩ = ((n : ℝ) : EReal) := by
      dsimp [c]
    have hE0 : Lebesgue_measure (E ⟨0, by omega⟩) = ((1 / (n : ℝ) ^ 2 : ℝ) : EReal) := by
      dsimp [E]
      simpa using (measure_Ioc_ab (show (0 : ℝ) ≤ 1 / (n : ℝ) ^ 2 from
        div_nonneg zero_le_one (sq_nonneg _)))
    rw [hc0, hE0, ← EReal.coe_mul]
    rw [EReal.coe_le_coe_iff]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one hn))
    field_simp [pow_two, hn0]
    norm_num
  have hterm_succ (i : Fin n) : c i.succ * Lebesgue_measure (E i.succ) =
      ((((i.val + 2 : ℕ) : ℝ) * (1 / ((i.val + 1 : ℕ) : ℝ) ^ 2 - 1 / ((i.val + 2 : ℕ) : ℝ) ^ 2) : ℝ) : EReal) := by
    have hc : c i.succ = (((i.val + 2 : ℕ) : ℝ) : EReal) := by
      dsimp [c]
    have hE : Lebesgue_measure (E i.succ) =
        ((1 / ((i.val + 1 : ℕ) : ℝ) ^ 2 - 1 / ((i.val + 2 : ℕ) : ℝ) ^ 2 : ℝ) : EReal) := by
      dsimp [E]
      have hpos : 0 < ((i.val + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.succ_pos i.val)
      have hden : ((i.val + 1 : ℕ) : ℝ) ^ 2 ≤ ((i.val + 2 : ℕ) : ℝ) ^ 2 := by
        have hi0 : 0 ≤ (i.val : ℝ) := by exact_mod_cast Nat.zero_le i.val
        push_cast
        nlinarith
      exact measure_Ioc_ab (one_div_le_one_div_of_le (sq_pos_of_pos hpos) hden)
    rw [hc, hE, ← EReal.coe_mul]
  have hterm_bound (i : Fin n) :
      (((i.val + 2 : ℕ) : ℝ) * (1 / ((i.val + 1 : ℕ) : ℝ) ^ 2 - 1 / ((i.val + 2 : ℕ) : ℝ) ^ 2) : ℝ)
        ≤ 3 * (1 / ((i.val + 1 : ℕ) : ℝ) - 1 / ((i.val + 2 : ℕ) : ℝ)) := by
    push_cast
    have hpos1 : 0 < ((i.val + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.succ_pos i.val)
    have hpos2 : 0 < ((i.val + 2 : ℕ) : ℝ) := by exact_mod_cast (Nat.succ_pos (i.val + 1))
    field_simp [hpos1.ne', hpos2.ne', pow_two]
    nlinarith
  have hbsum : (∑ i : Fin n, c i.succ * Lebesgue_measure (E i.succ)) ≤
      ((3 * (1 - 1 / ((n + 1 : ℕ) : ℝ)) : ℝ) : EReal) := by
    calc
      (∑ i : Fin n, c i.succ * Lebesgue_measure (E i.succ))
          ≤ ∑ i : Fin n, ((3 * (1 / ((i.val + 1 : ℕ) : ℝ) - 1 / ((i.val + 2 : ℕ) : ℝ)) : ℝ) : EReal) := by
            apply Finset.sum_le_sum
            intro i hi
            rw [hterm_succ i]
            rw [EReal.coe_le_coe_iff]
            exact hterm_bound i
      _ = (∑ i : Fin n, (3 * (1 / ((i.val + 1 : ℕ) : ℝ) - 1 / ((i.val + 2 : ℕ) : ℝ)) : ℝ) : EReal) := by
            rfl
      _ = ((3 * (∑ i : Fin n, (1 / ((i.val + 1 : ℕ) : ℝ) - 1 / ((i.val + 2 : ℕ) : ℝ))) : ℝ) : EReal) := by
            have hmap : (∑ i : Fin n, ((3 * (1 / ((i.val + 1 : ℕ) : ℝ) - 1 / ((i.val + 2 : ℕ) : ℝ)) : ℝ) : EReal)) =
                ((∑ i : Fin n, 3 * (1 / ((i.val + 1 : ℕ) : ℝ) - 1 / ((i.val + 2 : ℕ) : ℝ)) : ℝ) : EReal) :=
              (map_sum (⟨⟨Real.toEReal, EReal.coe_zero⟩, EReal.coe_add⟩ : ℝ →+ EReal)
                (fun i : Fin n => 3 * (1 / ((i.val + 1 : ℕ) : ℝ) - 1 / ((i.val + 2 : ℕ) : ℝ))) Finset.univ).symm
            exact hmap.trans (congrArg (fun z : ℝ => (z : EReal)) (by rw [Finset.mul_sum]))
      _ = ((3 * (1 - 1 / ((n + 1 : ℕ) : ℝ)) : ℝ) : EReal) := by
            exact congrArg (fun z : ℝ => (z : EReal)) (by rw [sum_inv_sub])
  have htotal : hsimple.integ ≤ (8 : EReal) := by
    rw [hinteg]
    rw [Fin.sum_univ_succ]
    calc
      (c ⟨0, by omega⟩ * Lebesgue_measure (E ⟨0, by omega⟩) +
          ∑ i : Fin n, c i.succ * Lebesgue_measure (E i.succ))
          ≤ ((1 / (n : ℝ) : ℝ) : EReal) + ((3 * (1 - 1 / ((n + 1 : ℕ) : ℝ)) : ℝ) : EReal) := by
            exact add_le_add hterm0 hbsum
      _ ≤ ((8 : ℝ) : EReal) := by
            have h1 : ((1 / (n : ℝ) : ℝ) : EReal) ≤ ((1 : ℝ) : EReal) := by
              rw [EReal.coe_le_coe_iff]
              exact div_le_one_of_le₀ (by exact_mod_cast hn) (by exact_mod_cast (Nat.zero_le n))
            have h2 : ((3 * (1 - 1 / ((n + 1 : ℕ) : ℝ)) : ℝ) : EReal) ≤ ((3 : ℝ) : EReal) := by
              rw [EReal.coe_le_coe_iff]
              have hle : 1 - 1 / ((n + 1 : ℕ) : ℝ) ≤ 1 :=
                sub_le_self (1 : ℝ) (by positivity)
              exact mul_le_of_le_one_right (by norm_num) hle
            have h34 : ((1 : ℝ) : EReal) + ((3 : ℝ) : EReal) ≤ ((8 : ℝ) : EReal) := by
              rw [← EReal.coe_add]
              rw [EReal.coe_le_coe_iff]
              norm_num
            exact le_trans (add_le_add h1 h2) h34
  exact le_trans hU_le htotal

/-- The target Decidable is FALSE: apply isFalse. -/
theorem eq_lim_vert_trunc_upper_isFalse : ¬ (∀ (d:ℕ) (f: EuclideanSpace' d → EReal) (_hf: UnsignedMeasurable f),
    Filter.atTop.Tendsto (fun n:ℕ ↦ UpperUnsignedLebesgueIntegral (fun x ↦ min (f x) n)) (nhds (UpperUnsignedLebesgueIntegral f))) := by
  intro h
  have hinst : Filter.atTop.Tendsto (fun n : ℕ =>
      UpperUnsignedLebesgueIntegral (fun x => min (f_inv_sqrt x) n)) (nhds ⊤) := by
    simpa [f_inv_sqrt_upper] using h 1 f_inv_sqrt f_inv_sqrt_measurable
  have htop_seq : ∀ z : ℝ, ∀ᶠ n : ℕ in atTop, (z : EReal) <
      UpperUnsignedLebesgueIntegral (fun x => min (f_inv_sqrt x) n) := by
    intro z
    have hmem : Set.Ioi (z : EReal) ∈ 𝓝 (⊤ : EReal) := by
      exact (EReal.mem_nhds_top_iff).mpr ⟨z, fun y hy => hy⟩
    simpa using (hinst.eventually hmem)
  rcases f_inv_sqrt_trunc_upper_bounded with ⟨c, hc_lt_top, hbounded⟩
  obtain ⟨z, hc_lt_z⟩ : ∃ z : ℝ, c < (z : EReal) := by
    cases c with
    | bot => exact ⟨0, EReal.bot_lt_coe 0⟩
    | coe r => exact ⟨r + 1, by rw [EReal.coe_lt_coe_iff]; linarith⟩
    | top => exact False.elim (not_lt_of_ge le_top hc_lt_top)
  have hev := htop_seq z
  rw [eventually_atTop] at hev
  rcases hev with ⟨N, hN⟩
  let n0 : ℕ := max N 1
  have hn0_N : N ≤ n0 := le_max_left N 1
  have hn0_ge1 : 1 ≤ n0 := le_max_right N 1
  have hs_gt : (z : EReal) < UpperUnsignedLebesgueIntegral (fun x => min (f_inv_sqrt x) n0) :=
    hN n0 hn0_N
  have hs_le : UpperUnsignedLebesgueIntegral (fun x => min (f_inv_sqrt x) n0) ≤ c :=
    hbounded n0 hn0_ge1
  exact (lt_irrefl (z : EReal)) (lt_trans hs_gt (lt_of_le_of_lt hs_le hc_lt_z))


def UpperUnsignedLebesgueIntegral.eq_lim_vert_trunc : Decidable (∀ (d:ℕ) (f: EuclideanSpace' d → EReal) (_hf: UnsignedMeasurable f), Filter.atTop.Tendsto (fun n:ℕ ↦ UpperUnsignedLebesgueIntegral (fun x ↦ min (f x) n)) (nhds (UpperUnsignedLebesgueIntegral f))) := by
  apply isFalse
  exact eq_lim_vert_trunc_upper_isFalse

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

/- The lower integral is at most the upper integral, unconditionally. -/
lemma upper_lower_ineq {d} {f : EuclideanSpace' d → EReal} :
    LowerUnsignedLebesgueIntegral f ≤ UpperUnsignedLebesgueIntegral f := by
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

/-- The lower integral of the zero function is zero. -/
lemma zero_lower_integral {d} :
    LowerUnsignedLebesgueIntegral (fun _ : EuclideanSpace' d => (0 : EReal)) = 0 := by
  have hz : UnsignedSimpleFunction (fun _ : EuclideanSpace' d => (0 : EReal)) := by
    use 0, (fun i : Fin 0 => (0 : EReal)), (fun i : Fin 0 => (∅ : Set (EuclideanSpace' d)))
    constructor
    · intro i; fin_cases i
    · ext x; simp
  rw [LowerUnsignedLebesgueIntegral.eq_simpleIntegral hz]
  exact zero_unsigned_integral hz

/-- The upper integral is nonnegative. -/
lemma upper_integral_nonneg {d} {g : EuclideanSpace' d → EReal} : 0 ≤ UpperUnsignedLebesgueIntegral g := by
  unfold UpperUnsignedLebesgueIntegral
  apply le_sInf
  intro R hR
  rcases hR with ⟨h, hh, hcond⟩
  have hReq : R = hh.integ := (hcond (Classical.arbitrary _)).2
  rw [hReq]
  have hz : UnsignedSimpleFunction (fun _ : EuclideanSpace' d => (0 : EReal)) := by
    use 0, (fun i : Fin 0 => (0 : EReal)), (fun i : Fin 0 => (∅ : Set (EuclideanSpace' d)))
    constructor
    · intro i; fin_cases i
    · ext x; simp
  have hle : hz.integ ≤ hh.integ :=
    UnsignedSimpleFunction.integral_le_integral_of_aeLe hz hh
      (AlmostAlways.ofAlways (fun x => (UnsignedSimpleFunction.unsignedMeasurable hh).1 x))
  simpa [zero_unsigned_integral hz] using hle

/- L f_inv_sqrt < ⊤ via the vertical truncation and the uniform upper bound on U(min(f,n)). -/
lemma f_inv_sqrt_L_lt_top : LowerUnsignedLebesgueIntegral f_inv_sqrt < ⊤ := by
  rcases f_inv_sqrt_trunc_upper_bounded with ⟨c, hc_lt_top, hbounded⟩
  have hc_nonneg : 0 ≤ c :=
    le_trans (upper_integral_nonneg (g := fun x : EuclideanSpace' 1 => min (f_inv_sqrt x) (1 : ℕ)))
      (hbounded 1 (by norm_num))
  have hconv := LowerUnsignedLebesgueIntegral.eq_lim_vert_trunc f_inv_sqrt_measurable
  have hbdd : ∀ n : ℕ, LowerUnsignedLebesgueIntegral (fun x => min (f_inv_sqrt x) n) ≤ c := by
    intro n
    by_cases hn : 1 ≤ n
    · exact le_trans (upper_lower_ineq (f := fun x => min (f_inv_sqrt x) n)) (hbounded n hn)
    · have hn0 : n = 0 := by omega
      subst n
      have hz : (fun x : EuclideanSpace' 1 => min (f_inv_sqrt x) (0 : ℕ)) =
          (fun _ : EuclideanSpace' 1 => (0 : EReal)) := by
        funext x
        simpa using (min_eq_right (f_inv_sqrt_nonneg x))
      rw [hz]
      rw [zero_lower_integral]
      exact hc_nonneg
  exact lt_of_le_of_lt (le_of_tendsto hconv (Filter.Eventually.of_forall hbdd)) hc_lt_top

/-- f_inv_sqrt has finite measure support: its support lies in the preimage of (0,1). -/
lemma f_inv_sqrt_finite_support : FiniteMeasureSupport f_inv_sqrt := by
  unfold FiniteMeasureSupport
  have hsub : Support f_inv_sqrt ⊆ EuclideanSpace'.equiv_Real ⁻¹' Set.Ioo (0 : ℝ) 1 := by
    intro x hx
    simp only [Support, Set.mem_setOf_eq, f_inv_sqrt] at hx
    by_cases hc : (0 : ℝ) < EuclideanSpace'.equiv_Real x ∧ EuclideanSpace'.equiv_Real x < 1
    · rw [if_pos hc] at hx
      exact hc
    · rw [if_neg hc] at hx
      exact False.elim (hx rfl)
  have hmu : Lebesgue_measure (EuclideanSpace'.equiv_Real ⁻¹' Set.Ioo (0 : ℝ) 1) = (1 : EReal) := by
    simpa using (measure_Ioo_ab (show (0 : ℝ) ≤ 1 from by norm_num))
  have hle : Lebesgue_measure (Support f_inv_sqrt) ≤ 1 := by
    rw [← hmu]
    simpa [Lebesgue_measure] using (Lebesgue_outer_measure.mono hsub)
  exact lt_of_le_of_lt hle (EReal.coe_lt_top 1)

/-- The boundedness hypothesis in Exercise 1.3.11 is necessary: isFalse. -/
theorem eq_upperIntegral_unbounded_isFalse :
    ¬ (∀ (d:ℕ) (f: EuclideanSpace' d → EReal) (_hf: UnsignedMeasurable f) (_hsupp: FiniteMeasureSupport f),
       LowerUnsignedLebesgueIntegral f = UpperUnsignedLebesgueIntegral f) := by
  intro h
  have heq : LowerUnsignedLebesgueIntegral f_inv_sqrt = UpperUnsignedLebesgueIntegral f_inv_sqrt :=
    h 1 f_inv_sqrt f_inv_sqrt_measurable f_inv_sqrt_finite_support
  rw [f_inv_sqrt_upper] at heq
  exact (not_lt_of_ge (le_of_eq heq.symm)) f_inv_sqrt_L_lt_top

def LowerUnsignedLebesgueIntegral.eq_upperIntegral_unbounded : Decidable (∀ (d:ℕ) (f: EuclideanSpace' d → EReal) (_hf: UnsignedMeasurable f) (_hsupp: FiniteMeasureSupport f), LowerUnsignedLebesgueIntegral f = UpperUnsignedLebesgueIntegral f) := by
  apply isFalse
  exact eq_upperIntegral_unbounded_isFalse

/-- For 0 ≤ a ≤ n, the extended absolute value of a is bounded by n. -/
lemma abs_le_of_nonneg_le {a : EReal} {n : ℕ} (h0 : 0 ≤ a) (hle : a ≤ (n : EReal)) :
    a.abs ≤ (n : NNReal) := by
  cases ha : a with
  | bot => rw [ha] at h0; simp at h0
  | top => rw [ha] at hle; exact (not_le_of_gt (EReal.coe_lt_top (n : ℝ)) hle).elim
  | coe r =>
      have hr0 : 0 ≤ r := (EReal.coe_nonneg).mp (by simpa [ha] using h0)
      have hrn : r ≤ (n : ℝ) := (EReal.coe_le_coe_iff).mp (by simpa [ha] using hle)
      rw [EReal.abs_def, abs_of_nonneg hr0]
      calc
        ENNReal.ofReal r ≤ ENNReal.ofReal (n : ℝ) := ENNReal.ofReal_le_ofReal hrn
        _ = (n : NNReal) := ENNReal.ofReal_natCast n

noncomputable def f_tail_piece (k : ℕ) : EuclideanSpace' 1 → EReal :=
  fun x => if EuclideanSpace'.equiv_Real x ∈ Set.Ioo (k : ℝ) ((k + 1 : ℕ) : ℝ) then
    (((2 : ℝ)⁻¹) ^ k : EReal) else 0

noncomputable def f_tail : EuclideanSpace' 1 → EReal :=
  fun x => ∑' k : ℕ, f_tail_piece k x

lemma f_tail_piece_nonneg (k : ℕ) : ∀ x, 0 ≤ f_tail_piece k x := by
  intro x
  unfold f_tail_piece
  by_cases hx : EuclideanSpace'.equiv_Real x ∈ Set.Ioo (k : ℝ) ((k + 1 : ℕ) : ℝ)
  · rw [if_pos hx]
    rw [← EReal.coe_pow]
    exact EReal.coe_nonneg.mpr (pow_nonneg (inv_nonneg.mpr (by norm_num)) k)
  · rw [if_neg hx]

lemma f_tail_nonneg : Unsigned f_tail := by
  intro x
  unfold f_tail
  exact tsum_nonneg (fun k => f_tail_piece_nonneg k x)

lemma tail_intervals_disjoint (j k : ℕ) (hjk : j ≠ k) :
    Set.Ioo (j : ℝ) ((j + 1 : ℕ) : ℝ) ∩ Set.Ioo (k : ℝ) ((k + 1 : ℕ) : ℝ) = ∅ := by
  wlog hlt : j < k generalizing j k
  · have hkj_lt : k < j := lt_of_le_of_ne (not_lt.mp hlt) (fun h => hjk h.symm)
    have hPkj : Set.Ioo (k : ℝ) ((k + 1 : ℕ) : ℝ) ∩ Set.Ioo (j : ℝ) ((j + 1 : ℕ) : ℝ) = ∅ :=
      this k j (fun h => hjk h.symm) hkj_lt
    simpa [Set.inter_comm] using hPkj
  · apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    rcases hx with ⟨hxj, hxk⟩
    have hxj_lt : x < ((j + 1 : ℕ) : ℝ) := (Set.mem_Ioo.mp hxj).2
    have hxk_gt : (k : ℝ) < x := (Set.mem_Ioo.mp hxk).1
    have hjk1 : j + 1 ≤ k := Nat.succ_le_of_lt hlt
    have hxj_le : x < (k : ℝ) := by
      exact lt_of_lt_of_le hxj_lt (by exact_mod_cast hjk1)
    exact (lt_irrefl x) (lt_trans hxj_le hxk_gt)

lemma f_tail_eq_piece {k : ℕ} {x : EuclideanSpace' 1}
    (hx : EuclideanSpace'.equiv_Real x ∈ Set.Ioo (k : ℝ) ((k + 1 : ℕ) : ℝ)) :
    f_tail x = (((2 : ℝ)⁻¹) ^ k : EReal) := by
  have hzero : ∀ j : ℕ, j ≠ k → f_tail_piece j x = 0 := by
    intro j hj
    unfold f_tail_piece
    rw [if_neg]
    intro hcond
    exact (Set.eq_empty_iff_forall_notMem.mp (tail_intervals_disjoint j k hj)
      (EuclideanSpace'.equiv_Real x)) ⟨hcond, hx⟩
  change (∑' j : ℕ, f_tail_piece j x) = (((2 : ℝ)⁻¹) ^ k : EReal)
  rw [tsum_eq_single k hzero]
  unfold f_tail_piece
  rw [if_pos hx]

noncomputable def tail_spike (k : ℕ) : Set (EuclideanSpace' 1) :=
  EuclideanSpace'.equiv_Real ⁻¹' Set.Ioo (k : ℝ) ((k + 1 : ℕ) : ℝ)

lemma tail_spike_meas (k : ℕ) : LebesgueMeasurable (tail_spike k) := by
  exact measurable_Ioo_preimage' (k : ℝ) ((k + 1 : ℕ) : ℝ)

lemma tail_spike_measure (k : ℕ) : Lebesgue_measure (tail_spike k) = (1 : EReal) := by
  rw [show tail_spike k = EuclideanSpace'.equiv_Real ⁻¹'
      Set.Ioo (k : ℝ) ((k + 1 : ℕ) : ℝ) by rfl]
  have hdiff : (((k + 1 : ℕ) : ℝ) - (k : ℝ)) = 1 := by
    norm_num
  simpa [hdiff] using (measure_Ioo_ab (show (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) by exact_mod_cast (Nat.le_succ k)))

lemma f_tail_eq_iUnion_gt (r : ℝ) (hr : 0 ≤ r) :
    {x : EuclideanSpace' 1 | (r : EReal) < f_tail x} =
      ⋃ k : ℕ, (if ((2 : ℝ)⁻¹) ^ k > r then tail_spike k else ∅) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · intro hx
    have hgt0 : (0 : EReal) < f_tail x := lt_of_le_of_lt (EReal.coe_nonneg.mpr hr) hx
    have hmem : x ∈ ⋃ m : ℕ, tail_spike m := by
      by_contra hnot
      have hz : ∀ j : ℕ, f_tail_piece j x = 0 := by
        intro j
        unfold f_tail_piece
        rw [if_neg]
        intro hcond
        have hxj : x ∈ ⋃ m : ℕ, tail_spike m := by
          rw [Set.mem_iUnion]
          exact ⟨j, hcond⟩
        exact hnot hxj
      have hf0 : f_tail x = 0 := by
        unfold f_tail
        simp [hz]
      exact (not_lt_of_ge (le_of_eq hf0)) hgt0
    rw [Set.mem_iUnion] at hmem
    rcases hmem with ⟨m, hm⟩
    have hf : f_tail x = (((2 : ℝ)⁻¹) ^ m : EReal) :=
      f_tail_eq_piece (Set.mem_Ioo.mp (Set.mem_preimage.mp hm))
    have hrm : r < ((2 : ℝ)⁻¹) ^ m := by
      rw [hf] at hx
      have hx' : (r : EReal) < Real.toEReal (((2 : ℝ)⁻¹) ^ m) := by
        simpa only [EReal.coe_pow] using hx
      exact EReal.coe_lt_coe_iff.mp hx'
    by_cases hkm : ((2 : ℝ)⁻¹) ^ m > r
    · refine ⟨m, ?_⟩
      rw [if_pos hkm]
      exact hm
    · exact False.elim ((not_lt_of_ge (le_of_not_gt hkm)) hrm)
  · intro hx
    rcases hx with ⟨k, hk⟩
    by_cases hkr : ((2 : ℝ)⁻¹) ^ k > r
    · rw [if_pos hkr] at hk
      have hf : f_tail x = (((2 : ℝ)⁻¹) ^ k : EReal) :=
        f_tail_eq_piece (Set.mem_Ioo.mp (Set.mem_preimage.mp hk))
      rw [hf]
      rw [← EReal.coe_pow]
      exact EReal.coe_lt_coe_iff.mpr hkr
    · rw [if_neg hkr] at hk
      exact False.elim hk

lemma f_tail_measurable : UnsignedMeasurable f_tail := by
  have h5 : ∀ t : EReal, LebesgueMeasurable {x | f_tail x > t} := by
    intro t
    by_cases ht : t = ⊤
    · have hset : {x | f_tail x > t} = (∅ : Set (EuclideanSpace' 1)) := by
        ext x
        rw [ht]
        constructor
        · intro h
          change f_tail x > ⊤ at h
          exact (not_lt_of_ge le_top) (gt_iff_lt.mp h)
        · intro h
          simp at h
      rw [hset]
      exact (isOpen_empty.measurable : LebesgueMeasurable (∅ : Set (EuclideanSpace' 1)))
    · cases t with
      | bot =>
          have hset : {x | f_tail x > (⊥ : EReal)} = (Set.univ : Set (EuclideanSpace' 1)) := by
            ext x
            simp only [gt_iff_lt, Set.mem_univ, iff_true]
            exact lt_of_lt_of_le (EReal.bot_lt_coe (0 : ℝ)) (f_tail_nonneg x)
          rw [hset]
          exact isOpen_univ.measurable
      | coe r =>
          by_cases hr : r < 0
          · have hset : {x | f_tail x > (r : EReal)} = (Set.univ : Set (EuclideanSpace' 1)) := by
              ext x
              simp only [gt_iff_lt, Set.mem_univ, iff_true]
              exact lt_of_lt_of_le (EReal.coe_lt_coe_iff.mpr hr) (f_tail_nonneg x)
            rw [hset]
            exact isOpen_univ.measurable
          · have hr0 : 0 ≤ r := le_of_not_gt hr
            have hset : {x | f_tail x > (r : EReal)} =
                ⋃ k : ℕ, (if ((2 : ℝ)⁻¹) ^ k > r then tail_spike k else ∅) :=
              f_tail_eq_iUnion_gt r hr0
            rw [hset]
            exact LebesgueMeasurable.countable_union (fun k => by
              by_cases hk : ((2 : ℝ)⁻¹) ^ k > r
              · rw [if_pos hk]
                exact tail_spike_meas k
              · rw [if_neg hk]
                exact (isOpen_empty.measurable : LebesgueMeasurable (∅ : Set (EuclideanSpace' 1))))
      | top =>
          exact False.elim (ht rfl)
  exact ((UnsignedMeasurable.TFAE f_tail_nonneg).out 4 0
    (a := ∀ t : EReal, LebesgueMeasurable {x | f_tail x > t})
    (b := UnsignedMeasurable f_tail)).mp h5

lemma f_tail_le_one : ∀ x : EuclideanSpace' 1, f_tail x ≤ (1 : EReal) := by
  intro x
  let u : ℝ := EuclideanSpace'.equiv_Real x
  by_cases hspike : ∃ k : ℕ, u ∈ Set.Ioo (k : ℝ) ((k + 1 : ℕ) : ℝ)
  · rcases hspike with ⟨k, hk⟩
    have hf : f_tail x = (((2 : ℝ)⁻¹) ^ k : EReal) := f_tail_eq_piece hk
    rw [hf]
    rw [← EReal.coe_pow]
    exact (EReal.coe_le_coe_iff.mpr
      (pow_le_one₀ (inv_nonneg.mpr (by norm_num)) (by norm_num : (2 : ℝ)⁻¹ ≤ 1)))
  · have hz : ∀ j : ℕ, f_tail_piece j x = 0 := by
      intro j
      unfold f_tail_piece
      rw [if_neg]
      intro hcond
      exact hspike ⟨j, hcond⟩
    unfold f_tail
    simp [hz]

lemma f_tail_bounded : EReal.BoundedFunction f_tail := by
  refine ⟨(1 : NNReal), ?_⟩
  intro x
  simpa using abs_le_of_nonneg_le (n := 1) (f_tail_nonneg x) (by simpa using (f_tail_le_one x))

lemma f_tail_trunc_upper_le_two : ∀ n : ℕ,
    UpperUnsignedLebesgueIntegral
      (f_tail * Real.toEReal ∘ (Metric.ball (0 : EuclideanSpace' 1) n).indicator') ≤ (2 : EReal) := by
  intro n
  let B : Set (EuclideanSpace' 1) := Metric.ball (0 : EuclideanSpace' 1) n
  let c : Fin (n + 1) → EReal := fun i => (((2 : ℝ)⁻¹) ^ i.val : EReal)
  let E : Fin (n + 1) → Set (EuclideanSpace' 1) := fun i => tail_spike i.val ∩ B
  let h : EuclideanSpace' 1 → EReal := fun x => ∑ i, c i • EReal.indicator (E i) x
  have hc_nonneg : ∀ i, c i ≥ 0 := fun i => by
    dsimp [c]
    rw [← EReal.coe_pow]
    exact EReal.coe_nonneg.mpr (pow_nonneg (inv_nonneg.mpr (by norm_num)) i.val)
  have hE_meas : ∀ i, LebesgueMeasurable (E i) := fun i =>
    LebesgueMeasurable.inter
      (tail_spike_meas i.val)
      (IsOpen.measurable (Metric.isOpen_ball : IsOpen (Metric.ball (0 : EuclideanSpace' 1) n)))
  have hsimple : UnsignedSimpleFunction h := by
    refine ⟨n + 1, c, E, ?_, ?_⟩
    · intro i
      exact ⟨hE_meas i, hc_nonneg i⟩
    · ext x
      simp [h]
  have hterm_nonneg : ∀ x, ∀ j : Fin (n + 1), 0 ≤ c j • EReal.indicator (E j) x := by
    intro x j
    rw [smul_eq_mul]
    exact EReal.mul_nonneg (hc_nonneg j) (EReal.indicator_nonneg (E j) x)
  have hh_nonneg : ∀ x, 0 ≤ h x := by
    intro x
    dsimp [h]
    exact Finset.sum_nonneg (fun j hj => hterm_nonneg x j)
  have hh_ge : ∀ x, (f_tail * Real.toEReal ∘ B.indicator') x ≤ h x := by
    intro x
    by_cases hxB : x ∈ B
    · let u : ℝ := EuclideanSpace'.equiv_Real x
      have hxball0 : dist x (0 : EuclideanSpace' 1) < (n : ℝ) := (Metric.mem_ball.mp hxB)
      have hu_abs : |u| < (n : ℝ) := by
        rw [EuclideanSpace'_dist_eq_Real_dist] at hxball0
        simpa [Real.dist_eq] using hxball0
      by_cases hspike : ∃ k : ℕ, u ∈ Set.Ioo (k : ℝ) ((k + 1 : ℕ) : ℝ)
      · rcases hspike with ⟨k, hk⟩
        have hu_lt_n : u < (n : ℝ) := lt_of_le_of_lt (le_abs_self u) hu_abs
        have hk_lt_n : k < n := by
          have hk_lt_u : (k : ℝ) < u := (Set.mem_Ioo.mp hk).1
          have hk_lt_n_r : (k : ℝ) < (n : ℝ) := lt_trans hk_lt_u hu_lt_n
          exact_mod_cast hk_lt_n_r
        let i : Fin (n + 1) := ⟨k, by omega⟩
        have hf : f_tail x = (((2 : ℝ)⁻¹) ^ k : EReal) := f_tail_eq_piece hk
        have hxEi : x ∈ E i := by
          dsimp [E, B]
          exact ⟨hk, hxB⟩
        have hx_ge_c : c i ≤ h x := by
          dsimp [h]
          have htermi : c i • EReal.indicator (E i) x = c i := by
            rw [smul_eq_mul]
            rw [indicator_mul_mem (E i) (c i) x hxEi]
          have hle := Finset.single_le_sum (fun j hj => hterm_nonneg x j) (Finset.mem_univ i)
          rw [htermi] at hle
          exact hle
        have hlhs : (f_tail * Real.toEReal ∘ B.indicator') x ≤ c i := by
          rw [show (f_tail * Real.toEReal ∘ B.indicator') x =
              f_tail x * Real.toEReal (B.indicator' x) by rfl]
          rw [Set.indicator'_of_mem hxB]
          rw [hf]
          dsimp [c, i]
          simp
        exact le_trans hlhs hx_ge_c
      · have hf0 : f_tail x = 0 := by
          have hz : ∀ j : ℕ, f_tail_piece j x = 0 := by
            intro j
            unfold f_tail_piece
            rw [if_neg]
            intro hcond
            exact hspike ⟨j, hcond⟩
          unfold f_tail
          simp [hz]
        rw [show (f_tail * Real.toEReal ∘ B.indicator') x =
            f_tail x * Real.toEReal (B.indicator' x) by rfl]
        simp [hf0]
        exact hh_nonneg x
    · rw [show (f_tail * Real.toEReal ∘ B.indicator') x =
        f_tail x * Real.toEReal (B.indicator' x) by rfl]
      rw [Set.indicator'_of_notMem hxB]
      simp
      exact hh_nonneg x
  have hU_le : UpperUnsignedLebesgueIntegral (f_tail * Real.toEReal ∘ B.indicator') ≤ hsimple.integ := by
    rw [← upperIntegral_simple hsimple]
    exact upperIntegral_mono hh_ge
  have hsimple_eq : h = ∑ i, (c i) • (EReal.indicator (E i)) := by
    ext x
    simp [h]
  have hinteg : hsimple.integ = ∑ i, c i * Lebesgue_measure (E i) :=
    UnsignedSimpleFunction.integral_eq hsimple hE_meas hc_nonneg hsimple_eq
  have hterm_le (i : Fin (n + 1)) :
      c i * Lebesgue_measure (E i) ≤ Real.toEReal (((2 : ℝ)⁻¹) ^ i.val) := by
    have hE_le : Lebesgue_measure (E i) ≤ Lebesgue_measure (tail_spike i.val) :=
      Lebesgue_outer_measure.mono (by
        dsimp [E]
        intro x hx
        exact hx.1)
    have hmu : Lebesgue_measure (tail_spike i.val) = (1 : EReal) := tail_spike_measure i.val
    have hc_mu : c i * Lebesgue_measure (tail_spike i.val) = Real.toEReal (((2 : ℝ)⁻¹) ^ i.val) := by
      dsimp [c]
      rw [hmu]
      rw [mul_one]
      rw [EReal.coe_pow]
    calc
      c i * Lebesgue_measure (E i) ≤ c i * Lebesgue_measure (tail_spike i.val) := by
        exact mul_le_mul_of_nonneg_left hE_le (hc_nonneg i)
      _ = Real.toEReal (((2 : ℝ)⁻¹) ^ i.val) := hc_mu
  have hsum_le : (∑ i : Fin (n + 1), c i * Lebesgue_measure (E i)) ≤ (2 : EReal) := by
    calc
      (∑ i : Fin (n + 1), c i * Lebesgue_measure (E i))
          ≤ ∑ i : Fin (n + 1), Real.toEReal (((2 : ℝ)⁻¹) ^ i.val) := by
            apply Finset.sum_le_sum
            intro i hi
            exact hterm_le i
      _ = Real.toEReal (∑ i : Fin (n + 1), ((2 : ℝ)⁻¹) ^ i.val) := by
            exact (map_sum (⟨⟨Real.toEReal, EReal.coe_zero⟩, EReal.coe_add⟩ : ℝ →+ EReal)
              (fun i : Fin (n + 1) => ((2 : ℝ)⁻¹) ^ i.val) Finset.univ).symm
      _ ≤ ((2 : ℝ) : EReal) := by
            rw [EReal.coe_le_coe_iff]
            exact sum_pow_half_le_two (n + 1)
  have htotal : hsimple.integ ≤ ((2 : ℝ) : EReal) := by
    rw [hinteg]
    exact hsum_le
  exact le_trans hU_le htotal

lemma f_tail_L_le_two : LowerUnsignedLebesgueIntegral f_tail ≤ (2 : EReal) := by
  exact le_of_tendsto (LowerUnsignedLebesgueIntegral.eq_lim_horiz_trunc f_tail_measurable)
    (Filter.Eventually.of_forall (fun n => le_trans
      (upper_lower_ineq (f := fun x => (f_tail * Real.toEReal ∘ (Metric.ball (0 : EuclideanSpace' 1) n).indicator') x))
      (f_tail_trunc_upper_le_two n)))


lemma tail_spike_disjoint (j k : ℕ) (hjk : j ≠ k) : Disjoint (tail_spike j) (tail_spike k) := by
  rw [Set.disjoint_iff]
  intro x hx
  have hx0 : EuclideanSpace'.equiv_Real x ∈ Set.Ioo (j : ℝ) ((j + 1 : ℕ) : ℝ) := hx.1
  have hx1 : EuclideanSpace'.equiv_Real x ∈ Set.Ioo (k : ℝ) ((k + 1 : ℕ) : ℝ) := hx.2
  exact (Set.eq_empty_iff_forall_notMem.mp (tail_intervals_disjoint j k hjk)
    (EuclideanSpace'.equiv_Real x)) ⟨hx0, hx1⟩

/- S1: for each spike k there is an atom with value >= 2^-k and measure >= 1/N on the spike. -/
lemma tail_upper_choice {k0 : ℕ} {c : Fin k0 → EReal} {E : Fin k0 → Set (EuclideanSpace' 1)}
    (hmes : ∀ i, LebesgueMeasurable (E i) ∧ c i ≥ 0)
    (hge : ∀ x, f_tail x ≤ (∑ i : Fin k0, c i • EReal.indicator (E i)) x) :
    ∀ k : ℕ, ∃ σ : Fin (2^(k0+k0)),
      ((2 : ℝ)⁻¹) ^ k ≤ atomValueEReal c σ.val ∧
      (1 / (Fintype.card (Fin (2^(k0+k0))) : ℝ) : EReal) ≤
        Lebesgue_measure (atom E E σ ∩ tail_spike k) := by
  intro k
  let A : Fin (2^(k0+k0)) → Set (EuclideanSpace' 1) := atom E E
  let N : ℝ := (Fintype.card (Fin (2^(k0+k0))) : ℝ)
  have hN_pos : 0 < N := by
    dsimp [N]
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨(0 : Fin (2 ^ (k0 + k0)))⟩)
  have hEmeas : ∀ i, LebesgueMeasurable (E i) := fun i => (hmes i).1
  have hA_meas : ∀ σ, LebesgueMeasurable (A σ) := fun σ => by
    simpa [A] using atom_measurable hEmeas hEmeas σ
  have hJ_cover : tail_spike k ⊆ ⋃ σ : Fin (2^(k0+k0)), A σ := by
    intro x hx
    have hf : f_tail x = (((2 : ℝ)⁻¹) ^ k : EReal) := f_tail_eq_piece hx
    have hpos : (0 : EReal) < f_tail x := by
      rw [hf, ← EReal.coe_pow]
      exact EReal.coe_pos.mpr (pow_pos (inv_pos.mpr (by norm_num)) k)
    have hle0 : f_tail x ≤ (∑ σ : Fin (2^(k0+k0)), atomValueEReal c σ.val • EReal.indicator (A σ)) x := by
      have hxeq : (∑ i : Fin k0, c i • EReal.indicator (E i)) x =
          (∑ σ : Fin (2^(k0+k0)), atomValueEReal c σ.val • EReal.indicator (A σ)) x := by
        exact congrFun (eq_sum_atomValueEReal_indicator c E E) x
      simpa [hxeq] using hge x
    by_contra hnot
    have hz : ∀ σ : Fin (2^(k0+k0)), EReal.indicator (A σ) x = 0 := by
      intro σ
      apply EReal.indicator_of_notMem
      intro h
      exact hnot (Set.mem_iUnion.mpr ⟨σ, h⟩)
    have hsum0 : (∑ σ : Fin (2^(k0+k0)), atomValueEReal c σ.val • EReal.indicator (A σ)) x = 0 := by
      simp [Pi.smul_apply, smul_eq_mul, hz]
    have hft_le : f_tail x ≤ 0 := by simpa [hsum0] using hle0
    exact (not_lt_of_ge hft_le) hpos
  have hJ_sub : tail_spike k ⊆ ⋃ σ : Fin (2^(k0+k0)), (A σ ∩ tail_spike k) := by
    intro x hx
    have hmem : ∃ σ : Fin (2^(k0+k0)), x ∈ A σ := Set.mem_iUnion.mp (hJ_cover hx)
    rcases hmem with ⟨σ, hσ⟩
    exact Set.mem_iUnion.mpr ⟨σ, ⟨hσ, hx⟩⟩
  have hsum_ge1 : (1 : EReal) ≤ ∑ σ : Fin (2^(k0+k0)), Lebesgue_measure (A σ ∩ tail_spike k) := by
    have hfu := Lebesgue_outer_measure.finite_union_le
      (E := fun σ : Fin (2^(k0+k0)) => A σ ∩ tail_spike k)
    calc
      1 = Lebesgue_measure (tail_spike k) := (tail_spike_measure k).symm
      _ ≤ Lebesgue_measure (⋃ σ : Fin (2^(k0+k0)), A σ ∩ tail_spike k) :=
        Lebesgue_outer_measure.mono hJ_sub
      _ ≤ ∑ σ : Fin (2^(k0+k0)), Lebesgue_measure (A σ ∩ tail_spike k) := hfu
  have hfinite : ∀ σ, Lebesgue_measure (A σ ∩ tail_spike k) ≠ ⊤ := by
    intro σ
    apply ne_of_lt
    refine lt_of_le_of_lt (Lebesgue_outer_measure.mono (Set.inter_subset_right)) ?_
    have hlt : Lebesgue_measure (tail_spike k) < ⊤ := by
      rw [tail_spike_measure k]
      exact EReal.coe_lt_top 1
    simpa [Lebesgue_measure] using hlt
  have hnotbot : ∀ σ, Lebesgue_measure (A σ ∩ tail_spike k) ≠ ⊥ := by
    intro σ
    exact ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (Lebesgue_outer_measure.nonneg _))
  let g : Fin (2^(k0+k0)) → ℝ := fun σ => (Lebesgue_measure (A σ ∩ tail_spike k)).toReal
  have hg_eq : ∀ σ, Lebesgue_measure (A σ ∩ tail_spike k) = (g σ : EReal) := fun σ =>
    (EReal.coe_toReal (hfinite σ) (hnotbot σ)).symm
  have hexists : ∃ σ : Fin (2^(k0+k0)), (1 / N : EReal) ≤ Lebesgue_measure (A σ ∩ tail_spike k) := by
    by_contra hnot
    push_neg at hnot
    have hltR : (∑ σ : Fin (2^(k0+k0)), g σ) < (∑ σ : Fin (2^(k0+k0)), 1 / N) := by
      apply Finset.sum_lt_sum_of_nonempty
      · exact Finset.univ_nonempty
      · intro σ hσ
        have hltσ : (g σ : EReal) < (1 / N : EReal) := by
          simpa [hg_eq] using hnot σ
        exact EReal.coe_lt_coe_iff.mp hltσ
    have hN_ne : N ≠ 0 := ne_of_gt hN_pos
    have hsumN : (∑ σ : Fin (2^(k0+k0)), 1 / N) = 1 := by
      rw [Finset.sum_const, nsmul_eq_mul]
      dsimp [N]
      field_simp [hN_ne]
    have hlt1 : (∑ σ : Fin (2^(k0+k0)), g σ) < 1 := by
      rw [hsumN] at hltR
      exact hltR
    have hsum_g_ge1 : 1 ≤ (∑ σ : Fin (2^(k0+k0)), g σ) := by
      have h1e : (1 : EReal) ≤ (∑ σ : Fin (2^(k0+k0)), (g σ : EReal)) := by
        simpa [hg_eq] using hsum_ge1
      have hsum_eq : (∑ σ : Fin (2^(k0+k0)), (g σ : EReal)) =
          (((∑ σ : Fin (2^(k0+k0)), g σ) : ℝ) : EReal) := by
        exact (map_sum (⟨⟨Real.toEReal, EReal.coe_zero⟩, EReal.coe_add⟩ : ℝ →+ EReal) g Finset.univ).symm
      have h2 : (1 : EReal) ≤ (((∑ σ : Fin (2^(k0+k0)), g σ) : ℝ) : EReal) := by
        rwa [hsum_eq] at h1e
      exact EReal.coe_le_coe_iff.mp h2
    exact (not_lt_of_ge hsum_g_ge1) hlt1
  rcases hexists with ⟨σ0, hσ0⟩
  have hne : (A σ0 ∩ tail_spike k).Nonempty := by
    by_contra hempty
    have hμ0 : Lebesgue_measure (A σ0 ∩ tail_spike k) = 0 := by
      have hEempty : A σ0 ∩ tail_spike k = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro x hx
        exact hempty ⟨x, hx⟩
      rw [hEempty]
      exact Lebesgue_outer_measure.of_empty (d := 1)
    have hpos0 : (0 : EReal) < Lebesgue_measure (A σ0 ∩ tail_spike k) :=
      lt_of_lt_of_le (EReal.coe_pos.mpr (one_div_pos.mpr hN_pos)) hσ0
    exact (not_lt_of_ge (le_of_eq hμ0)) hpos0
  rcases hne with ⟨x, hx⟩
  have hf : f_tail x = (((2 : ℝ)⁻¹) ^ k : EReal) := f_tail_eq_piece hx.2
  have hsum : (∑ i : Fin k0, c i • EReal.indicator (E i)) x = atomValueEReal c σ0.val := by
    have hsi := sum_indicator_eq_atomValueEReal c E E σ0 x hx.1
    simpa [Pi.smul_apply, smul_eq_mul] using hsi
  have hv : ((2 : ℝ)⁻¹) ^ k ≤ atomValueEReal c σ0.val := by
    have hle : f_tail x ≤ (∑ i : Fin k0, c i • EReal.indicator (E i)) x := hge x
    simpa [hf, hsum] using hle
  exact ⟨σ0, hv, by simpa [A, N] using hσ0⟩

/- S2+S3: finite additivity over a Finset (binary induction). -/
lemma measure_finset_sum {d : ℕ} {A : ℕ → Set (EuclideanSpace' d)}
    (hmes : ∀ k : ℕ, LebesgueMeasurable (A k))
    (hdisj : ∀ j k : ℕ, j ≠ k → Disjoint (A j) (A k)) (F : Finset ℕ) :
    (∑ k ∈ F, Lebesgue_measure (A k)) = Lebesgue_measure (⋃ k ∈ F, A k) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | insert k F hkF ih =>
      rw [Finset.sum_insert hkF]
      have hunion : (⋃ i ∈ insert k F, A i) = A k ∪ (⋃ i ∈ F, A i) := by
        ext x
        constructor
        · intro hx
          have hmem := Set.mem_iUnion.mp hx
          rcases hmem with ⟨i, hi⟩
          have hmem2 := Set.mem_iUnion.mp hi
          rcases hmem2 with ⟨hiF, hxi⟩
          by_cases hik : i = k
          · left
            simpa [hik] using hxi
          · right
            have hiF' : i ∈ F := (Finset.mem_insert.mp hiF).resolve_left hik
            exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hiF', hxi⟩⟩
        · intro hx
          rcases hx with hxk | hx
          · exact Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨by simp, hxk⟩⟩
          · have hmem := Set.mem_iUnion.mp hx
            rcases hmem with ⟨i, hi⟩
            have hmem2 := Set.mem_iUnion.mp hi
            rcases hmem2 with ⟨hiF, hxi⟩
            exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨Finset.mem_insert_of_mem hiF, hxi⟩⟩
      have hU_meas : LebesgueMeasurable (⋃ i ∈ F, A i) := by
        have hU' : (⋃ i : ℕ, if i ∈ F then A i else ∅) = (⋃ i ∈ F, A i) := by
          ext x
          simp [Set.mem_iUnion]
        rw [← hU']
        exact LebesgueMeasurable.countable_union (fun i => by
          by_cases hi : i ∈ F
          · rw [if_pos hi]
            exact hmes i
          · rw [if_neg hi]
            exact (isOpen_empty.measurable : LebesgueMeasurable (∅ : Set (EuclideanSpace' d))))
      have hdisj' : A k ∩ (⋃ i ∈ F, A i) = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro x hx
        have hmem := Set.mem_iUnion.mp hx.2
        rcases hmem with ⟨i, hi⟩
        have hmem2 := Set.mem_iUnion.mp hi
        rcases hmem2 with ⟨hiF, hxi⟩
        have hkj : k ≠ i := by
          intro hki
          exact hkF (by simpa [hki] using hiF)
        have hd : Disjoint (A k) (A i) := hdisj k i hkj
        rw [Set.disjoint_left] at hd
        exact hd hx.1 hxi
      calc
        Lebesgue_measure (A k) + ∑ x ∈ F, Lebesgue_measure (A x)
            = Lebesgue_measure (A k) + Lebesgue_measure (⋃ i ∈ F, A i) := by rw [ih]
        _ = Lebesgue_measure (A k ∪ (⋃ i ∈ F, A i)) := (Lebesgue_measure.union (hmes k) hU_meas hdisj').symm
        _ = Lebesgue_measure (⋃ i ∈ insert k F, A i) := congrArg Lebesgue_measure hunion.symm

/- S2+S3: infinite pigeonhole on the choice map, then the fiber lemma: some atom has
    positive value and infinite measure. -/
lemma tail_upper_fiber {k0 : ℕ} {c : Fin k0 → EReal} {E : Fin k0 → Set (EuclideanSpace' 1)}
    (hmes : ∀ i, LebesgueMeasurable (E i) ∧ c i ≥ 0)
    (hge : ∀ x, f_tail x ≤ (∑ i : Fin k0, c i • EReal.indicator (E i)) x) :
    ∃ σ0 : Fin (2^(k0+k0)),
      (0 : EReal) < atomValueEReal c σ0.val ∧
      Lebesgue_measure (atom E E σ0) = ⊤ := by
  let A : Fin (2^(k0+k0)) → Set (EuclideanSpace' 1) := atom E E
  let N : ℕ := Fintype.card (Fin (2^(k0+k0)))
  have hN_pos : 0 < (N : ℝ) := by
    dsimp [N]
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨(0 : Fin (2 ^ (k0 + k0)))⟩)
  let choice : ℕ → Fin (2^(k0+k0)) := fun k => (tail_upper_choice hmes hge k).choose
  have hchoice : ∀ k, ((2 : ℝ)⁻¹) ^ k ≤ atomValueEReal c (choice k).val ∧
      (1 / (N : ℝ) : EReal) ≤ Lebesgue_measure (A (choice k) ∩ tail_spike k) := by
    intro k
    have h := (tail_upper_choice hmes hge k).choose_spec
    simpa [choice, A, N] using h
  have hpig : ∃ σ0 : Fin (2^(k0+k0)), Set.Infinite {k : ℕ | choice k = σ0} := by
    by_contra hnot
    push_neg at hnot
    have hcov : (Set.univ : Set ℕ) = ⋃ σ : Fin (2^(k0+k0)), {k : ℕ | choice k = σ} := by
      ext k
      constructor
      · intro _
        rw [Set.mem_iUnion]
        exact ⟨choice k, rfl⟩
      · intro h
        trivial
    have hunion_fin : (⋃ σ : Fin (2^(k0+k0)), {k : ℕ | choice k = σ}).Finite :=
      Set.finite_iUnion hnot
    have huniv_fin : (Set.univ : Set ℕ).Finite := by
      rwa [← hcov] at hunion_fin
    exact (Set.infinite_univ : (Set.univ : Set ℕ).Infinite) huniv_fin
  rcases hpig with ⟨σ0, hS⟩
  let S : Set ℕ := {k : ℕ | choice k = σ0}
  have hS_inf : S.Infinite := hS
  have hv_pos : (0 : EReal) < atomValueEReal c σ0.val := by
    rcases hS_inf.nonempty with ⟨k0', hk0'⟩
    have hv : ((2 : ℝ)⁻¹) ^ k0' ≤ atomValueEReal c σ0.val := by
      have hk := hchoice k0'
      have hc : choice k0' = σ0 := hk0'
      simpa [hc] using hk.1
    have hposR : (0 : ℝ) < ((2 : ℝ)⁻¹) ^ k0' := pow_pos (inv_pos.mpr (by norm_num)) k0'
    have hposE : (0 : EReal) < ((2 : ℝ)⁻¹) ^ k0' := by
      rw [← EReal.coe_pow]
      exact EReal.coe_pos.mpr hposR
    exact lt_of_lt_of_le hposE hv
  have hμ_top : Lebesgue_measure (A σ0) = ⊤ := by
    have hbig : ∀ m : ℕ, ∃ F : Finset ℕ, (↑F : Set ℕ) ⊆ S ∧ m ≤ F.card := by
      intro m
      obtain ⟨t, ht1, ht2⟩ := Set.Infinite.exists_subset_card_eq hS_inf m
      exact ⟨t, ht1, by omega⟩
    have hterms : ∀ k ∈ S, (1 / (N : ℝ) : EReal) ≤ Lebesgue_measure (A σ0 ∩ tail_spike k) := by
      intro k hk
      have hk' := hchoice k
      have hc : choice k = σ0 := hk
      simpa [hc] using hk'.2
    have hA_meas0 : LebesgueMeasurable (A σ0) := by
      simpa [A] using atom_measurable (fun i => (hmes i).1) (fun i => (hmes i).1) σ0
    have hJ_meas : ∀ k : ℕ, LebesgueMeasurable (A σ0 ∩ tail_spike k) := fun k =>
      LebesgueMeasurable.inter hA_meas0 (tail_spike_meas k)
    have hJ_disj : ∀ j k : ℕ, j ≠ k → Disjoint (A σ0 ∩ tail_spike j) (A σ0 ∩ tail_spike k) := by
      intro j k hjk
      have hd := tail_spike_disjoint j k hjk
      rw [Set.disjoint_left] at hd ⊢
      intro x hx hx0
      have hxj : x ∈ tail_spike j := hx.2
      have hxk : x ∈ tail_spike k := hx0.2
      exact (hd hxj) hxk
    have hA_ge : ∀ F : Finset ℕ, (↑F : Set ℕ) ⊆ S →
        (∑ k ∈ F, Lebesgue_measure (A σ0 ∩ tail_spike k)) ≤ Lebesgue_measure (A σ0) := by
      intro F hF
      have hsum_eq : (∑ k ∈ F, Lebesgue_measure (A σ0 ∩ tail_spike k)) =
          Lebesgue_measure (⋃ k ∈ F, A σ0 ∩ tail_spike k) :=
        measure_finset_sum hJ_meas hJ_disj F
      have hsub : (⋃ k ∈ F, A σ0 ∩ tail_spike k) ⊆ A σ0 := by
        intro x hx
        have hmem := Set.mem_iUnion.mp hx
        rcases hmem with ⟨k, hk⟩
        have hmem2 := Set.mem_iUnion.mp hk
        rcases hmem2 with ⟨hkF, hxk⟩
        exact hxk.1
      calc
        (∑ k ∈ F, Lebesgue_measure (A σ0 ∩ tail_spike k))
            = Lebesgue_measure (⋃ k ∈ F, A σ0 ∩ tail_spike k) := hsum_eq
        _ ≤ Lebesgue_measure (A σ0) := Lebesgue_outer_measure.mono hsub
    have hmu_all : ∀ m : ℕ, ((m : ℝ) / (N : ℝ) : EReal) ≤ Lebesgue_measure (A σ0) := by
      intro m
      rcases hbig m with ⟨F, hF, hcard⟩
      have hle := hA_ge F hF
      have hsum_terms : (∑ k ∈ F, (((1 : ℝ) / (N : ℝ) : ℝ) : EReal)) ≤
          (∑ k ∈ F, Lebesgue_measure (A σ0 ∩ tail_spike k)) := by
        apply Finset.sum_le_sum
        intro k hk
        exact hterms k (hF hk)
      have hsumN : (∑ k ∈ F, (((1 : ℝ) / (N : ℝ) : ℝ) : EReal)) = (((F.card : ℝ) / (N : ℝ) : ℝ) : EReal) := by
        have h1 : (∑ k ∈ F, (((1 : ℝ) / (N : ℝ) : ℝ) : EReal)) =
            (((∑ k ∈ F, 1 / (N : ℝ)) : ℝ) : EReal) := by
          exact (map_sum (⟨⟨Real.toEReal, EReal.coe_zero⟩, EReal.coe_add⟩ : ℝ →+ EReal)
            (fun k : ℕ => 1 / (N : ℝ)) F).symm
        rw [h1]
        congr 1
        rw [Finset.sum_const, nsmul_eq_mul]
        field_simp
      calc
        ((m : ℝ) / (N : ℝ) : EReal) ≤ ((F.card : ℝ) / (N : ℝ) : EReal) := by
          change (((m : ℝ) / (N : ℝ) : ℝ) : EReal) ≤ (((F.card : ℝ) / (N : ℝ) : ℝ) : EReal)
          rw [EReal.coe_le_coe_iff]
          exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) (le_of_lt hN_pos)
        _ = (∑ k ∈ F, (((1 : ℝ) / (N : ℝ) : ℝ) : EReal)) := hsumN.symm
        _ ≤ (∑ k ∈ F, Lebesgue_measure (A σ0 ∩ tail_spike k)) := hsum_terms
        _ ≤ Lebesgue_measure (A σ0) := hle
    cases hμeq : Lebesgue_measure (A σ0) with
    | bot =>
        have hb : (0 : EReal) ≤ (⊥ : EReal) := by
          rw [← hμeq]
          exact Lebesgue_outer_measure.nonneg _
        exact False.elim ((not_le_of_gt EReal.bot_lt_zero) hb)
    | coe r =>
        have hle_m : ∀ m : ℕ, (m : ℝ) / (N : ℝ) ≤ r := by
          intro m
          have hc := hmu_all m
          rw [hμeq] at hc
          exact EReal.coe_le_coe_iff.mp hc
        obtain ⟨m, hm⟩ := exists_nat_gt (r * (N : ℝ))
        have hle : (m : ℝ) / (N : ℝ) ≤ r := hle_m m
        have hmul : (m : ℝ) ≤ r * (N : ℝ) := (div_le_iff₀ hN_pos).mp hle
        exact False.elim ((not_lt_of_ge hmul) hm)
    | top => rfl
  exact ⟨σ0, hv_pos, hμ_top⟩

lemma f_tail_upper_aux : UpperUnsignedLebesgueIntegral f_tail = ⊤ := by
  apply le_antisymm le_top
  unfold UpperUnsignedLebesgueIntegral
  apply le_sInf
  intro R hR
  rcases hR with ⟨g, hg, hcond⟩
  let hg' : UnsignedSimpleFunction g := hg
  rcases hg with ⟨k0, c, E, hmes, heq⟩
  have hge : ∀ x, f_tail x ≤ g x := fun x => (hcond x).1
  have hReq : R = hg'.integ := (hcond (Classical.arbitrary _)).2
  rw [hReq]
  have hE_meas : ∀ i, LebesgueMeasurable (E i) := fun i => (hmes i).1
  have hc_nonneg : ∀ i, c i ≥ 0 := fun i => (hmes i).2
  rcases tail_upper_fiber hmes (by simpa [heq] using hge) with ⟨σ0, hv_pos, hμ_top⟩
  let v : Fin (2^(k0+k0)) → EReal := fun σ => atomValueEReal c σ.val
  let A : Fin (2^(k0+k0)) → Set (EuclideanSpace' 1) := atom E E
  have hA_meas : ∀ σ, LebesgueMeasurable (A σ) := fun σ => by
    simpa [A] using atom_measurable hE_meas hE_meas σ
  have hv_nonneg : ∀ σ, v σ ≥ 0 := fun σ => atomValueEReal_nonneg hc_nonneg σ.val
  have hg_atoms : g = ∑ σ, v σ • EReal.indicator (A σ) := by
    simpa [v, A] using (heq.trans (eq_sum_atomValueEReal_indicator c E E))
  have hinteg' : hg'.integ = ∑ σ, v σ * Lebesgue_measure (A σ) :=
    UnsignedSimpleFunction.integral_eq hg' (k := 2^(k0+k0)) (c := v) (E := A)
      hA_meas hv_nonneg hg_atoms
  have hprod : v σ0 * Lebesgue_measure (A σ0) = ⊤ := by
    cases hvσ : v σ0 with
    | bot =>
        exfalso
        have hb : (0 : EReal) ≤ (⊥ : EReal) := by
          rw [← hvσ]
          exact hv_pos.le
        exact (not_le_of_gt EReal.bot_lt_zero) hb
    | coe r =>
        have hr_pos : 0 < r := by
          have hc : (0 : EReal) < (r : EReal) := by simpa [v, hvσ] using hv_pos
          exact EReal.coe_pos.mp hc
        rw [hμ_top]
        exact EReal.coe_mul_top_of_pos hr_pos
    | top =>
        rw [hμ_top]
        rfl
  have hge_top : ⊤ ≤ ∑ σ, v σ * Lebesgue_measure (A σ) := by
    have hle := Finset.single_le_sum
      (fun σ hσ => EReal.mul_nonneg (hv_nonneg σ) (Lebesgue_outer_measure.nonneg (A σ)))
      (Finset.mem_univ σ0)
    change v σ0 * Lebesgue_measure (A σ0) ≤ ∑ x, v x * Lebesgue_measure (A x) at hle
    rw [hprod] at hle
    exact hle
  rw [hinteg']
  exact hge_top

theorem eq_upperIntegral_infinite_supp_isFalse :
    ¬ (∀ (d:ℕ) (f: EuclideanSpace' d → EReal) (_hf: UnsignedMeasurable f) (_hb: EReal.BoundedFunction f),
       LowerUnsignedLebesgueIntegral f = UpperUnsignedLebesgueIntegral f) := by
  intro h
  have heq : LowerUnsignedLebesgueIntegral f_tail = UpperUnsignedLebesgueIntegral f_tail :=
    h 1 f_tail f_tail_measurable f_tail_bounded
  rw [f_tail_upper_aux] at heq
  exact (not_lt_of_ge (le_of_eq heq.symm)) (lt_of_le_of_lt f_tail_L_le_two (EReal.coe_lt_top 2))


/-- The finite-support hypothesis in Exercise 1.3.11 is necessary: isFalse. -/
def LowerUnsignedLebesgueIntegral.eq_upperIntegral_infinite_supp : Decidable (∀ (d:ℕ) (f: EuclideanSpace' d → EReal) (_hf: UnsignedMeasurable f) (_hb: EReal.BoundedFunction f), LowerUnsignedLebesgueIntegral f = UpperUnsignedLebesgueIntegral f) := by
  apply isFalse
  exact eq_upperIntegral_infinite_supp_isFalse

/-- min(f x + g x, n) ≤ min(f x, n) + min(g x, n) pointwise for nonnegative f, g. -/
lemma min_add_le {d : ℕ} {f g : EuclideanSpace' d → EReal} (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (n : ℕ) : ∀ x, min (f x + g x) n ≤ min (f x) n + min (g x) n := by
  intro x
  by_cases h1 : (n : EReal) ≤ f x
  · by_cases h2 : (n : EReal) ≤ g x
    · rw [min_eq_right h1, min_eq_right h2]
      exact le_trans (min_le_right (f x + g x) (n : EReal))
        (le_add_of_nonneg_right (by exact_mod_cast (Nat.zero_le n)))
    · rw [min_eq_right h1, min_eq_left (le_of_not_ge h2)]
      exact le_trans (min_le_right (f x + g x) (n : EReal)) (le_add_of_nonneg_right (hg0 x))
  · by_cases h2 : (n : EReal) ≤ g x
    · rw [min_eq_left (le_of_not_ge h1), min_eq_right h2]
      exact le_trans (min_le_right (f x + g x) (n : EReal)) (le_add_of_nonneg_left (hf0 x))
    · rw [min_eq_left (le_of_not_ge h1), min_eq_left (le_of_not_ge h2)]
      exact min_le_left (f x + g x) (n : EReal)

/-- The support of min(f, n) is contained in the support of f. -/
lemma supp_min_subset {d : ℕ} {f : EuclideanSpace' d → EReal} (n : ℕ) :
    Support (fun x => min (f x) n) ⊆ Support f := by
  intro x hx
  by_cases h : f x = 0
  · exfalso
    exact hx (by
      change min (f x) (n : EReal) = 0
      rw [h]
      exact min_eq_left (by exact_mod_cast (Nat.zero_le n)))
  · exact h

/-- The support of f + g is contained in the union of the supports. -/
lemma supp_add_subset {d : ℕ} {f g : EuclideanSpace' d → EReal} :
    Support (f + g) ⊆ Support f ∪ Support g := by
  intro x hx
  simp [Support] at hx ⊢
  by_contra h
  push_neg at h
  exact hx (by simp [h.1, h.2])


/-- Vertical truncation min(f, n) of a nonnegative f is bounded. -/
lemma bounded_min_const {d : ℕ} {f : EuclideanSpace' d → EReal} (hf0 : ∀ x, 0 ≤ f x) (n : ℕ) :
    EReal.BoundedFunction (fun x => min (f x) n) := by
  refine ⟨n, ?_⟩
  intro x
  apply abs_le_of_nonneg_le
  · exact le_min (hf0 x) (by exact_mod_cast (Nat.zero_le n))
  · exact min_le_right (f x) (n : EReal)

/-- The union of two finite-measure supports has finite measure. -/
lemma supp_fg_fin {d : ℕ} {f g : EuclideanSpace' d → EReal} (hf_supp : FiniteMeasureSupport f)
    (hg_supp : FiniteMeasureSupport g) : Lebesgue_measure (Support f ∪ Support g) < ⊤ := by
  have hle : Lebesgue_measure (Support f ∪ Support g) ≤
      Lebesgue_measure (Support f) + Lebesgue_measure (Support g) := by
    let E' : Fin 2 → Set (EuclideanSpace' d) := ![Support f, Support g]
    have h_union : Support f ∪ Support g = ⋃ i, E' i := by
      simp only [E']
      ext x
      simp
    have h_sum : ∑ i : Fin 2, Lebesgue_outer_measure (E' i) =
        Lebesgue_measure (Support f) + Lebesgue_measure (Support g) := by
      simp [Fin.sum_univ_two, E', Lebesgue_measure]
    rw [h_union, ← h_sum]
    exact Lebesgue_outer_measure.finite_union_le E'
  exact lt_of_le_of_lt hle (EReal.add_lt_top (ne_of_lt hf_supp) (ne_of_lt hg_supp))

/-- A nonnegative function pointwise below a bounded function is bounded. -/
lemma bounded_of_nonneg_le {d : ℕ} {f h : EuclideanSpace' d → EReal} (hf0 : ∀ x, 0 ≤ f x)
    (hle : ∀ x, f x ≤ h x) (hbound : EReal.BoundedFunction h) : EReal.BoundedFunction f := by
  rcases hbound with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro x
  have habs : (f x).abs ≤ (h x).abs := by
    rcases eq_bot_or_bot_lt (f x) with hfx_bot_eq | hfx_bot
    · exfalso
      exact (not_le_of_gt EReal.bot_lt_zero) (hfx_bot_eq ▸ hf0 x)
    rcases eq_top_or_lt_top (f x) with hfx_top_eq | hfx_lt
    · have htop : h x = ⊤ := top_le_iff.mp (hfx_top_eq ▸ hle x)
      rw [hfx_top_eq, htop]
      exact le_rfl
    · rcases eq_bot_or_bot_lt (h x) with hhx_bot_eq | hhx_bot
      · exfalso
        exact (not_le_of_gt EReal.bot_lt_zero) (le_trans (hf0 x) (hhx_bot_eq ▸ hle x))
      · rcases eq_top_or_lt_top (h x) with hhx_top_eq | hhx_lt
        · rw [hhx_top_eq]
          exact le_top
        · have hfx_eq : f x = (((f x).toReal : ℝ) : EReal) :=
            (EReal.coe_toReal hfx_lt.ne hfx_bot.ne').symm
          have hhx_eq : h x = (((h x).toReal : ℝ) : EReal) :=
            (EReal.coe_toReal hhx_lt.ne hhx_bot.ne').symm
          rw [hfx_eq, hhx_eq, EReal.abs_def, EReal.abs_def]
          have hfxr_nonneg : 0 ≤ (f x).toReal := by
            have hf0x : (0 : EReal) ≤ (((f x).toReal : ℝ) : EReal) := by
              rw [← hfx_eq]
              exact hf0 x
            exact EReal.coe_nonneg.mp hf0x
          have hfxr_le : (f x).toReal ≤ (h x).toReal := by
            have hle' : (((f x).toReal : ℝ) : EReal) ≤ (((h x).toReal : ℝ) : EReal) := by
              rw [← hfx_eq, ← hhx_eq]
              exact hle x
            exact EReal.coe_le_coe_iff.mp hle'
          have hhxr_nonneg : 0 ≤ (h x).toReal := le_trans hfxr_nonneg hfxr_le
          rw [abs_of_nonneg hfxr_nonneg, abs_of_nonneg hhxr_nonneg]
          exact ENNReal.ofReal_le_ofReal hfxr_le
  exact le_trans habs (hM x)

/-- The support of a function pointwise below another is contained in the other's support
    (for unsigned f: f x > 0 → h x ≥ f x > 0). -/
lemma supp_subset_of_le {d : ℕ} {f h : EuclideanSpace' d → EReal} (hf0 : ∀ x, 0 ≤ f x)
    (hle : ∀ x, f x ≤ h x) : Support f ⊆ Support h := by
  intro x hx
  have hfpos : 0 < f x := lt_of_le_of_ne (hf0 x) hx.symm
  have hhpos : 0 < h x := lt_of_lt_of_le hfpos (hle x)
  exact ne_of_gt hhpos

/-- Exercise 1.3.10(x) (Reflection) -/
theorem LowerUnsignedLebesgueIntegral.sum_of_reflect_eq {d:ℕ} {f g: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) (hg: UnsignedMeasurable g)
    (hfg: UnsignedSimpleFunction (f+g)) (hbound: EReal.BoundedFunction (f + g)) (hsupport: FiniteMeasureSupport (f + g)) :
    hfg.integ = LowerUnsignedLebesgueIntegral f + LowerUnsignedLebesgueIntegral g := by
  have hf_le : ∀ x, f x ≤ (f + g) x := fun x => le_add_of_nonneg_right (hg.1 x)
  have hg_le : ∀ x, g x ≤ (f + g) x := fun x => le_add_of_nonneg_left (hf.1 x)
  have hbound_f : EReal.BoundedFunction f := bounded_of_nonneg_le hf.1 hf_le hbound
  have hbound_g : EReal.BoundedFunction g := bounded_of_nonneg_le hg.1 hg_le hbound
  have hsupp_f : FiniteMeasureSupport f := by
    unfold FiniteMeasureSupport
    apply lt_of_le_of_lt _ hsupport
    exact Lebesgue_outer_measure.mono (supp_subset_of_le hf.1 hf_le)
  have hsupp_g : FiniteMeasureSupport g := by
    unfold FiniteMeasureSupport
    apply lt_of_le_of_lt _ hsupport
    exact Lebesgue_outer_measure.mono (supp_subset_of_le hg.1 hg_le)
  apply le_antisymm
  · calc
      hfg.integ = LowerUnsignedLebesgueIntegral (f + g) :=
        (LowerUnsignedLebesgueIntegral.eq_simpleIntegral hfg).symm
      _ = UpperUnsignedLebesgueIntegral (f + g) :=
        LowerUnsignedLebesgueIntegral.eq_upperIntegral (UnsignedSimpleFunction.unsignedMeasurable hfg) hbound hsupport
      _ ≤ UpperUnsignedLebesgueIntegral f + UpperUnsignedLebesgueIntegral g :=
        UpperUnsignedLebesgueIntegral.subadditive hf hg
      _ = LowerUnsignedLebesgueIntegral f + LowerUnsignedLebesgueIntegral g := by
        rw [LowerUnsignedLebesgueIntegral.eq_upperIntegral hf hbound_f hsupp_f,
            LowerUnsignedLebesgueIntegral.eq_upperIntegral hg hbound_g hsupp_g]
  · calc
      LowerUnsignedLebesgueIntegral f + LowerUnsignedLebesgueIntegral g ≤
          LowerUnsignedLebesgueIntegral (f + g) := LowerUnsignedLebesgueIntegral.superadditive hf hg
      _ = hfg.integ := LowerUnsignedLebesgueIntegral.eq_simpleIntegral hfg

/-- Additivity of lower integral for finite-support functions.
    This is the key step where we can apply {name}`eq_upperIntegral` and use the sandwich argument. -/
lemma LowerUnsignedLebesgueIntegral.add_of_finiteSupport {d : ℕ}
    {f g : EuclideanSpace' d → EReal}
    (hf : UnsignedMeasurable f) (hg : UnsignedMeasurable g)
    (hfg : UnsignedMeasurable (f + g))
    (hf_supp : FiniteMeasureSupport f) (hg_supp : FiniteMeasureSupport g) :
    LowerUnsignedLebesgueIntegral (f + g) =
      LowerUnsignedLebesgueIntegral f + LowerUnsignedLebesgueIntegral g := by
  apply le_antisymm
  · have hmono_fg := LowerUnsignedLebesgueIntegral.eq_lim_vert_trunc hfg
    have hfn_meas : ∀ n : ℕ, UnsignedMeasurable (fun x => min (f x) n) := by
      intro n
      have hφ : Continuous (fun y : EReal => min y ((n : ℝ) : EReal)) := by
        simpa using (Continuous.min continuous_id continuous_const :
          Continuous (fun y : EReal => min y ((n : ℝ) : EReal)))
      have hφnn : ∀ x ≥ (0 : EReal), min x ((n : ℝ) : EReal) ≥ 0 := by
        intro x hx
        exact le_min hx (EReal.coe_nonneg.mpr (Nat.cast_nonneg n))
      simpa using UnsignedMeasurable.comp_cts hf hφ hφnn
    have hgn_meas : ∀ n : ℕ, UnsignedMeasurable (fun x => min (g x) n) := by
      intro n
      have hφ : Continuous (fun y : EReal => min y ((n : ℝ) : EReal)) := by
        simpa using (Continuous.min continuous_id continuous_const :
          Continuous (fun y : EReal => min y ((n : ℝ) : EReal)))
      have hφnn : ∀ x ≥ (0 : EReal), min x ((n : ℝ) : EReal) ≥ 0 := by
        intro x hx
        exact le_min hx (EReal.coe_nonneg.mpr (Nat.cast_nonneg n))
      simpa using UnsignedMeasurable.comp_cts hg hφ hφnn
    have hfgn_meas : ∀ n : ℕ, UnsignedMeasurable (fun x => min ((f + g) x) n) := by
      intro n
      have hφ : Continuous (fun y : EReal => min y ((n : ℝ) : EReal)) := by
        simpa using (Continuous.min continuous_id continuous_const :
          Continuous (fun y : EReal => min y ((n : ℝ) : EReal)))
      have hφnn : ∀ x ≥ (0 : EReal), min x ((n : ℝ) : EReal) ≥ 0 := by
        intro x hx
        exact le_min hx (EReal.coe_nonneg.mpr (Nat.cast_nonneg n))
      simpa using UnsignedMeasurable.comp_cts hfg hφ hφnn
    have hbound_f : ∀ n : ℕ, EReal.BoundedFunction (fun x => min (f x) n) :=
      fun n => bounded_min_const hf.1 n
    have hbound_g : ∀ n : ℕ, EReal.BoundedFunction (fun x => min (g x) n) :=
      fun n => bounded_min_const hg.1 n
    have hbound_fg : ∀ n : ℕ, EReal.BoundedFunction (fun x => min ((f + g) x) n) :=
      fun n => bounded_min_const hfg.1 n
    have hsupp_f : ∀ n : ℕ, FiniteMeasureSupport (fun x => min (f x) n) := by
      intro n
      exact lt_of_le_of_lt (Lebesgue_outer_measure.mono (supp_min_subset (f := f) n)) hf_supp
    have hsupp_g : ∀ n : ℕ, FiniteMeasureSupport (fun x => min (g x) n) := by
      intro n
      exact lt_of_le_of_lt (Lebesgue_outer_measure.mono (supp_min_subset (f := g) n)) hg_supp
    have hsupp_fg : ∀ n : ℕ, FiniteMeasureSupport (fun x => min ((f + g) x) n) := by
      intro n
      exact lt_of_le_of_lt (Lebesgue_outer_measure.mono
        (le_trans (supp_min_subset (f := f + g) n) (supp_add_subset (f := f) (g := g))))
        (supp_fg_fin hf_supp hg_supp)
    have hle_n : ∀ n : ℕ, LowerUnsignedLebesgueIntegral (fun x => min ((f + g) x) n) ≤
        LowerUnsignedLebesgueIntegral (fun x => min (f x) n) +
          LowerUnsignedLebesgueIntegral (fun x => min (g x) n) := by
      intro n
      calc
        LowerUnsignedLebesgueIntegral (fun x => min ((f + g) x) n)
            = UpperUnsignedLebesgueIntegral (fun x => min ((f + g) x) n) :=
              LowerUnsignedLebesgueIntegral.eq_upperIntegral (hfgn_meas n) (hbound_fg n) (hsupp_fg n)
        _ ≤ UpperUnsignedLebesgueIntegral (fun x => min (f x) n + min (g x) n) :=
              upperIntegral_mono (min_add_le hf.1 hg.1 n)
        _ ≤ UpperUnsignedLebesgueIntegral (fun x => min (f x) n) +
              UpperUnsignedLebesgueIntegral (fun x => min (g x) n) :=
              UpperUnsignedLebesgueIntegral.subadditive (hfn_meas n) (hgn_meas n)
        _ = LowerUnsignedLebesgueIntegral (fun x => min (f x) n) +
              LowerUnsignedLebesgueIntegral (fun x => min (g x) n) := by
              rw [← LowerUnsignedLebesgueIntegral.eq_upperIntegral (hfn_meas n) (hbound_f n) (hsupp_f n),
                  ← LowerUnsignedLebesgueIntegral.eq_upperIntegral (hgn_meas n) (hbound_g n) (hsupp_g n)]
    have hmono_le_f : ∀ n : ℕ, LowerUnsignedLebesgueIntegral (fun x => min (f x) n) ≤
        LowerUnsignedLebesgueIntegral f := by
      intro n
      exact LowerUnsignedLebesgueIntegral.mono (hfn_meas n) hf
        (AlmostAlways.ofAlways (fun x => min_le_left (f x) (n : EReal)))
    have hmono_le_g : ∀ n : ℕ, LowerUnsignedLebesgueIntegral (fun x => min (g x) n) ≤
        LowerUnsignedLebesgueIntegral g := by
      intro n
      exact LowerUnsignedLebesgueIntegral.mono (hgn_meas n) hg
        (AlmostAlways.ofAlways (fun x => min_le_left (g x) (n : EReal)))
    have hle_n' : ∀ n : ℕ, LowerUnsignedLebesgueIntegral (fun x => min ((f + g) x) n) ≤
        LowerUnsignedLebesgueIntegral f + LowerUnsignedLebesgueIntegral g := by
      intro n
      exact le_trans (hle_n n) (add_le_add (hmono_le_f n) (hmono_le_g n))
    exact le_of_tendsto hmono_fg (Filter.Eventually.of_forall hle_n')
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
    UpperUnsignedLebesgueIntegral (Real.toEReal ∘ E.indicator') = Lebesgue_outer_measure E := by
  apply le_antisymm
  · unfold UpperUnsignedLebesgueIntegral
    calc
      sInf {R | ∃ (g : EuclideanSpace' d → EReal), ∃ hg : UnsignedSimpleFunction g, ∀ x, g x ≥ (Real.toEReal ∘ E.indicator') x ∧ R = hg.integ} ≤
          (UnsignedSimpleFunction.indicator hE).integ := by
        apply sInf_le
        refine ⟨Real.toEReal ∘ E.indicator', UnsignedSimpleFunction.indicator hE, ?_⟩
        intro x
        exact ⟨le_rfl, rfl⟩
      _ = Lebesgue_outer_measure E := by
        rw [UnsignedSimpleFunction.integral_indicator hE]
        rfl
  · unfold UpperUnsignedLebesgueIntegral
    apply le_sInf
    intro R hR
    rcases hR with ⟨g, hg, hcond⟩
    have hReq : R = hg.integ := by
      haveI : Nonempty (EuclideanSpace' d) := inferInstance
      exact (hcond (Classical.arbitrary _)).2
    rw [hReq]
    calc
      Lebesgue_outer_measure E = (UnsignedSimpleFunction.indicator hE).integ := by
        rw [UnsignedSimpleFunction.integral_indicator hE]
        rfl
      _ ≤ hg.integ :=
        UnsignedSimpleFunction.integral_le_integral_of_aeLe (UnsignedSimpleFunction.indicator hE) hg
          (AlmostAlways.ofAlways (fun x => (hcond x).1))

/- 1. For a simple g ≤ 1_A, the integral is bounded by the measure of a measurable subset of A. -/
lemma indicator_integral_le_meas {d} {A : Set (EuclideanSpace' d)} (g : EuclideanSpace' d → EReal)
    (hg : UnsignedSimpleFunction g) (hle : ∀ x, g x ≤ Real.toEReal (A.indicator' x)) :
    ∃ W : Set (EuclideanSpace' d), LebesgueMeasurable W ∧ W ⊆ A ∧ hg.integ ≤ Lebesgue_measure W := by
  let hg' : UnsignedSimpleFunction g := hg
  rcases hg with ⟨k, c, E, hmes, heq⟩
  let Aσ : Fin (2^(k+k)) → Set (EuclideanSpace' d) := atom E E
  let v : Fin (2^(k+k)) → EReal := fun σ => atomValueEReal c σ.val
  have hEmeas : ∀ i, LebesgueMeasurable (E i) := fun i => (hmes i).1
  have hc_nonneg : ∀ i, c i ≥ 0 := fun i => (hmes i).2
  have hAσ_meas : ∀ σ, LebesgueMeasurable (Aσ σ) := fun σ => by
    simpa [Aσ] using atom_measurable hEmeas hEmeas σ
  have hv_nonneg : ∀ σ, 0 ≤ v σ := fun σ => atomValueEReal_nonneg hc_nonneg σ.val
  have hg_atoms : g = ∑ σ, v σ • EReal.indicator (Aσ σ) := by
    simpa [v, Aσ] using (heq.trans (eq_sum_atomValueEReal_indicator c E E))
  have hg_integ : hg'.integ = ∑ σ, v σ * Lebesgue_measure (Aσ σ) :=
    UnsignedSimpleFunction.integral_eq hg' (k := 2^(k+k)) (c := v) (E := Aσ)
      hAσ_meas hv_nonneg hg_atoms
  have hgx_of_mem : ∀ {σ : Fin (2^(k+k))} {x : EuclideanSpace' d}, x ∈ Aσ σ → g x = v σ := by
    intro σ x hx
    have h1 : (∑ τ : Fin (2^(k+k)), v τ * EReal.indicator (Aσ τ) x) = v σ := by
      rw [Finset.sum_eq_single σ]
      · rw [EReal.indicator_of_mem hx, mul_one]
      · intro τ hτ hne
        have hxnot : x ∉ Aσ τ := by
          intro hxτ
          have hd : Disjoint (Aσ σ) (Aσ τ) :=
            atom_pairwiseDisjoint E E (Set.mem_univ σ) (Set.mem_univ τ) hne.symm
          rw [Set.disjoint_left] at hd
          exact (hd hx) hxτ
        rw [EReal.indicator_of_notMem hxnot, mul_zero]
      · intro h; exact absurd (Finset.mem_univ σ) h
    simpa [Pi.smul_apply, smul_eq_mul, h1] using (congrFun hg_atoms x)
  let W : Set (EuclideanSpace' d) := ⋃ σ : Fin (2^(k+k)), (if 0 < v σ then Aσ σ else ∅)
  have hW_meas : LebesgueMeasurable W := by
    have hfin := LebesgueMeasurable.finite_union
      (E := fun σ : Fin (2^(k+k)) => if 0 < v σ then Aσ σ else ∅)
      (fun σ => by
        by_cases hσ : 0 < v σ
        · change LebesgueMeasurable (if 0 < v σ then Aσ σ else ∅)
          rw [if_pos hσ]
          exact hAσ_meas σ
        · change LebesgueMeasurable (if 0 < v σ then Aσ σ else ∅)
          rw [if_neg hσ]
          exact (isOpen_empty.measurable : LebesgueMeasurable (∅ : Set (EuclideanSpace' d))))
    simpa [W] using hfin
  have hW_sub : W ⊆ A := by
    intro x hx
    have hmem := Set.mem_iUnion.mp hx
    rcases hmem with ⟨σ, hσ⟩
    by_cases hvσ : 0 < v σ
    · rw [if_pos hvσ] at hσ
      have hpos : (0 : EReal) < g x := by
        have hgx : g x = v σ := hgx_of_mem hσ
        rw [hgx]
        exact hvσ
      have hle1 : g x ≤ Real.toEReal (A.indicator' x) := hle x
      by_cases hxA : x ∈ A
      · exact hxA
      · have h0 : Real.toEReal (A.indicator' x) = 0 := by
          rw [Set.indicator'_of_notMem hxA]
          rfl
        have : (0 : EReal) < 0 := by simpa [h0] using (lt_of_lt_of_le hpos hle1)
        exact False.elim (lt_irrefl (0 : EReal) this)
    · rw [if_neg hvσ] at hσ
      exact False.elim hσ
  have hsum_eq : (∑ σ : Fin (2^(k+k)), v σ * Lebesgue_measure (Aσ σ)) ≤
      (∑ σ : Fin (2^(k+k)), Lebesgue_measure (if 0 < v σ then Aσ σ else ∅)) := by
    apply Finset.sum_le_sum
    intro σ hσ
    by_cases hvσ : 0 < v σ
    · rw [if_pos hvσ]
      by_cases hA : (Aσ σ).Nonempty
      · rcases hA with ⟨x, hx⟩
        have hgx : g x = v σ := hgx_of_mem hx
        have hle1 : g x ≤ Real.toEReal (A.indicator' x) := hle x
        have hle2 : Real.toEReal (A.indicator' x) ≤ (1 : EReal) := by
          by_cases hxA : x ∈ A
          · rw [Set.indicator'_of_mem hxA, EReal.coe_one]
          · rw [Set.indicator'_of_notMem hxA, EReal.coe_zero]
            exact zero_le_one
        have hv_le_1 : v σ ≤ (1 : EReal) := by
          simpa [hgx] using (le_trans hle1 hle2)
        simpa [mul_comm] using (mul_le_of_le_one_right (Lebesgue_outer_measure.nonneg (Aσ σ)) hv_le_1)
      · have hμ0 : Lebesgue_measure (Aσ σ) = 0 := by
          have hE : Aσ σ = ∅ := by
            rw [Set.eq_empty_iff_forall_notMem]
            intro x hx
            exact hA ⟨x, hx⟩
          rw [hE]
          exact Lebesgue_outer_measure.of_empty (d := d)
        simp [hμ0]
    · rw [if_neg hvσ]
      have hv0 : v σ = 0 := le_antisymm (le_of_not_gt hvσ) (hv_nonneg σ)
      rw [hv0, zero_mul]
      exact Lebesgue_outer_measure.nonneg (∅ : Set (EuclideanSpace' d))
  have hW_sum : (∑ σ : Fin (2^(k+k)), Lebesgue_measure (if 0 < v σ then Aσ σ else ∅)) =
      Lebesgue_measure W := by
    have hfin := Lebesgue_measure.finite_union
      (E := fun σ : Fin (2^(k+k)) => if 0 < v σ then Aσ σ else ∅)
      (fun σ => by
        by_cases hσ : 0 < v σ
        · change LebesgueMeasurable (if 0 < v σ then Aσ σ else ∅)
          rw [if_pos hσ]
          exact hAσ_meas σ
        · change LebesgueMeasurable (if 0 < v σ then Aσ σ else ∅)
          rw [if_neg hσ]
          exact (isOpen_empty.measurable : LebesgueMeasurable (∅ : Set (EuclideanSpace' d))))
      (by
        intro σ hσ τ hτ hne
        by_cases hvσ : 0 < v σ
        · by_cases hvτ : 0 < v τ
          · have hd : Disjoint (Aσ σ) (Aσ τ) := atom_pairwiseDisjoint E E hσ hτ hne
            change Disjoint (if 0 < v σ then Aσ σ else ∅) (if 0 < v τ then Aσ τ else ∅)
            rw [if_pos hvσ, if_pos hvτ]
            exact hd
          · change Disjoint (if 0 < v σ then Aσ σ else ∅) (if 0 < v τ then Aσ τ else ∅)
            rw [if_pos hvσ, if_neg hvτ]
            rw [Set.disjoint_iff]
            intro x hx
            exact hx.2
        · change Disjoint (if 0 < v σ then Aσ σ else ∅) (if 0 < v τ then Aσ τ else ∅)
          rw [if_neg hvσ]
          rw [Set.disjoint_iff]
          intro x hx
          exact hx.1)
    simpa [W] using hfin.symm
  refine ⟨W, hW_meas, hW_sub, ?_⟩
  rw [hg_integ]
  exact le_trans hsum_eq (le_of_eq hW_sum)

/- 3. Measurable subsets of the Vitali set have measure zero. -/
lemma vitali_meas_subset_zero (W : Set (EuclideanSpace' 1)) (hW : LebesgueMeasurable W)
    (hWV : W ⊆ Real.equiv_EuclideanSpace' '' VitaliSet) :
    Lebesgue_measure W = 0 := by
  obtain ⟨f, hf_inj, hf_mem⟩ := exists_injective_rat_enum_Icc
  let T : ℕ → Set (EuclideanSpace' 1) := fun n => W + {Real.equiv_EuclideanSpace' (f n : ℚ)}
  have hT_disj : Set.univ.PairwiseDisjoint T := by
    intro i hi j hj hij
    have hd : Disjoint
        ((Real.equiv_EuclideanSpace' '' VitaliSet) + {Real.equiv_EuclideanSpace' (f i : ℚ)})
        ((Real.equiv_EuclideanSpace' '' VitaliSet) + {Real.equiv_EuclideanSpace' (f j : ℚ)}) :=
      VitaliSet.translates_pairwise_disjoint f hf_inj hi hj hij
    change Disjoint (T i) (T j)
    rw [Set.disjoint_left] at hd ⊢
    intro z hz hz'
    have hsub1 : T i ⊆ (Real.equiv_EuclideanSpace' '' VitaliSet) + {Real.equiv_EuclideanSpace' (f i : ℚ)} := by
      intro z' hz'
      rw [Set.mem_add] at hz' ⊢
      rcases hz' with ⟨x, hx, r, hr, hz_eq⟩
      exact ⟨x, hWV hx, r, hr, hz_eq⟩
    have hsub2 : T j ⊆ (Real.equiv_EuclideanSpace' '' VitaliSet) + {Real.equiv_EuclideanSpace' (f j : ℚ)} := by
      intro z' hz'
      rw [Set.mem_add] at hz' ⊢
      rcases hz' with ⟨x, hx, r, hr, hz_eq⟩
      exact ⟨x, hWV hx, r, hr, hz_eq⟩
    exact hd (hsub1 hz) (hsub2 hz')
  have hT_meas : ∀ n, LebesgueMeasurable (T n) := fun n => by
    dsimp [T]
    exact (LebesgueMeasurable.translate W (Real.equiv_EuclideanSpace' (f n : ℚ))).mp hW
  have hT_sub : ⋃ n, T n ⊆ Real.equiv_EuclideanSpace' '' Set.Icc (-1 : ℝ) 2 := by
    intro z hz
    rw [Set.mem_iUnion] at hz
    rcases hz with ⟨n, hzn⟩
    rw [Set.mem_add] at hzn
    rcases hzn with ⟨x, hx, r, hr, hz_eq⟩
    rw [Set.mem_singleton_iff] at hr
    subst hr
    rcases (hWV hx) with ⟨v, hv, rfl⟩
    have hv_in : v ∈ Set.Icc (0 : ℝ) 1 := VitaliSet_subset_unit_interval hv
    have hq_bound : f n ∈ Set.Icc (-1 : ℚ) 1 := hf_mem n
    refine ⟨v + (f n : ℝ), ?_, ?_⟩
    · constructor
      · have h1 : (f n : ℝ) ≥ -1 := by exact_mod_cast hq_bound.1
        linarith [hv_in.1]
      · have h2 : (f n : ℝ) ≤ 1 := by exact_mod_cast hq_bound.2
        linarith [hv_in.2]
    · ext i
      fin_cases i
      have hlhs : (Real.equiv_EuclideanSpace' (v + (f n : ℝ))) ⟨0, by omega⟩ = v + (f n : ℝ) := rfl
      have hrhs : z ⟨0, by omega⟩ = (Real.equiv_EuclideanSpace' v + Real.equiv_EuclideanSpace' (f n : ℝ)) ⟨0, by omega⟩ := by
        rw [← hz_eq]
      have hrhs' : (Real.equiv_EuclideanSpace' v + Real.equiv_EuclideanSpace' (f n : ℝ)) ⟨0, by omega⟩ = v + (f n : ℝ) := rfl
      rw [hlhs, hrhs, hrhs']
  have hsum := Lebesgue_measure.countable_union hT_meas hT_disj
  have hT_eq : ∀ n, Lebesgue_measure (T n) = Lebesgue_measure W := fun n => by
    dsimp [T]
    exact Lebesgue_measure.translate _ hW
  have hle3 : Lebesgue_measure (⋃ n, T n) ≤ 3 := by
    calc
      Lebesgue_measure (⋃ n, T n) ≤ Lebesgue_measure (Real.equiv_EuclideanSpace' '' Set.Icc (-1 : ℝ) 2) :=
        Lebesgue_outer_measure.mono hT_sub
      _ = ((3 : ℝ) : EReal) := by
        rw [Lebesgue_measure.Icc_eq (-1) 2 (by norm_num)]
        norm_num
  by_cases hW0 : Lebesgue_measure W = 0
  · exact hW0
  · have hWpos : 0 < Lebesgue_measure W := lt_of_le_of_ne (Lebesgue_outer_measure.nonneg _) (Ne.symm hW0)
    have hsum_top : (∑' n : ℕ, Lebesgue_measure (T n)) = ⊤ := by
      simp only [hT_eq]
      exact EReal.tsum_const_eq_top_of_pos hWpos
    have htop : Lebesgue_measure (⋃ n, T n) = ⊤ := by
      rw [← hsum] at hsum_top
      exact hsum_top
    exact False.elim ((by decide : ¬(⊤ : EReal) ≤ 3) (by simpa [htop] using hle3))

/- 2. The lower integral of the Vitali indicator is zero. -/
lemma vitali_inner_measure_zero :
    LowerUnsignedLebesgueIntegral
      (Real.toEReal ∘ (Real.equiv_EuclideanSpace' '' VitaliSet).indicator') = 0 := by
  apply le_antisymm
  · unfold LowerUnsignedLebesgueIntegral
    apply sSup_le
    intro R hR
    rcases hR with ⟨g, hg, hcond⟩
    have hle : ∀ x, g x ≤ Real.toEReal ((Real.equiv_EuclideanSpace' '' VitaliSet).indicator' x) :=
      fun x => (hcond x).1
    have hReq : R = hg.integ := (hcond (Classical.arbitrary _)).2
    rw [hReq]
    rcases indicator_integral_le_meas g hg hle with ⟨W, hW, hWV, hleW⟩
    have hW0 : Lebesgue_measure W = 0 := vitali_meas_subset_zero W hW hWV
    exact le_trans hleW (le_of_eq hW0)
  · have hz : UnsignedSimpleFunction (fun _ : EuclideanSpace' 1 => (0 : EReal)) := by
      use 0, (fun i : Fin 0 => (0 : EReal)), (fun i : Fin 0 => (∅ : Set (EuclideanSpace' 1)))
      constructor
      · intro i; fin_cases i
      · ext x; simp
    have hz_integ : hz.integ = 0 := zero_unsigned_integral hz
    exact le_sSup ⟨(fun _ : EuclideanSpace' 1 => (0 : EReal)), hz, fun x => ⟨by
      change (0 : EReal) ≤ Real.toEReal ((Real.equiv_EuclideanSpace' '' VitaliSet).indicator' x)
      by_cases hx : x ∈ Real.equiv_EuclideanSpace' '' VitaliSet
      · rw [Set.indicator'_of_mem hx]
        exact zero_le_one
      · rw [Set.indicator'_of_notMem hx]
        exact le_rfl
    , hz_integ.symm⟩⟩

/- 4. The lower integral of the indicator of C \ V is strictly less than 1. -/
lemma complement_lower_lt_one :
    LowerUnsignedLebesgueIntegral
      (Real.toEReal ∘ (Real.equiv_EuclideanSpace' '' Set.Icc (0 : ℝ) 1 \ Real.equiv_EuclideanSpace' '' VitaliSet).indicator') < 1 := by
  let V : Set (EuclideanSpace' 1) := Real.equiv_EuclideanSpace' '' VitaliSet
  let C : Set (EuclideanSpace' 1) := Real.equiv_EuclideanSpace' '' Set.Icc (0 : ℝ) 1
  have hV_sub_C : V ⊆ C := by
    intro x hx
    rcases hx with ⟨v, hv, rfl⟩
    exact Set.mem_image_of_mem _ (VitaliSet_subset_unit_interval hv)
  have hC_meas : LebesgueMeasurable C := by
    have h_box : C = (BoundedInterval.Icc (0 : ℝ) 1 : Box 1).toSet := by
      unfold C
      have h_interval : Set.Icc (0 : ℝ) 1 = (BoundedInterval.Icc (0 : ℝ) 1).toSet := by rfl
      rw [h_interval, ← BoundedInterval.coe_of_box]
    rw [h_box]
    exact (IsElementary.measurable (IsElementary.box _))
  have hC_mu : Lebesgue_measure C = (1 : EReal) := by
    simpa [C] using (Lebesgue_measure.Icc_eq 0 1 (by norm_num))
  have hL_C : LowerUnsignedLebesgueIntegral (Real.toEReal ∘ C.indicator') = 1 := by
    rw [LowerUnsignedLebesgueIntegral.eq_simpleIntegral (UnsignedSimpleFunction.indicator hC_meas)]
    rw [UnsignedSimpleFunction.integral_indicator hC_meas]
    exact hC_mu
  have hle1 : LowerUnsignedLebesgueIntegral (Real.toEReal ∘ (C \ V).indicator') ≤ 1 := by
    unfold LowerUnsignedLebesgueIntegral
    apply sSup_le
    intro R hR
    rcases hR with ⟨g, hg, hcond⟩
    have hReq : R = hg.integ := (hcond (Classical.arbitrary _)).2
    rw [hReq]
    rw [← hL_C]
    unfold LowerUnsignedLebesgueIntegral
    exact le_sSup ⟨g, hg, fun x => ⟨by
      change g x ≤ Real.toEReal (C.indicator' x)
      have hgx : g x ≤ Real.toEReal ((C \ V).indicator' x) := (hcond x).1
      by_cases hx : x ∈ C \ V
      · have hxC : x ∈ C := hx.1
        have h1 : Real.toEReal ((C \ V).indicator' x) = Real.toEReal (C.indicator' x) := by
          rw [Set.indicator'_of_mem hx, Set.indicator'_of_mem hxC]
        simpa [h1] using hgx
      · rw [Set.indicator'_of_notMem hx] at hgx
        have hc0 : (0 : EReal) ≤ Real.toEReal (C.indicator' x) := by
          by_cases hxC : x ∈ C
          · rw [Set.indicator'_of_mem hxC]
            exact zero_le_one
          · rw [Set.indicator'_of_notMem hxC]
            exact le_rfl
        exact le_trans hgx hc0
    , rfl⟩⟩
  have hne : LowerUnsignedLebesgueIntegral (Real.toEReal ∘ (C \ V).indicator') ≠ 1 := by
    intro h1
    have hmu_le : ∀ n : ℕ, Lebesgue_outer_measure V ≤ (1 / ((n : ℝ) + 1) : EReal) := by
      intro n
      let eps : ℝ := 1 / ((n : ℝ) + 1)
      have hep : 0 < eps := by dsimp [eps]; positivity
      have hlt : ((1 - eps : ℝ) : EReal) < 1 := by
        exact EReal.coe_lt_coe_iff.mpr (by linarith)
      have hltSup : ((1 - eps : ℝ) : EReal) <
          sSup {R' | ∃ g, ∃ hg : UnsignedSimpleFunction g, ∀ x, g x ≤ Real.toEReal ((C \ V).indicator' x) ∧ R' = hg.integ} := by
        simpa [← h1, LowerUnsignedLebesgueIntegral] using hlt
      rcases (lt_sSup_iff.mp hltSup) with ⟨R, hR⟩
      rcases hR with ⟨hRmem, hltR⟩
      rcases hRmem with ⟨g, hg, hcond⟩
      have hle : ∀ x, g x ≤ Real.toEReal ((C \ V).indicator' x) := fun x => (hcond x).1
      have hReq : R = hg.integ := (hcond (Classical.arbitrary _)).2
      rw [hReq] at hltR
      rcases indicator_integral_le_meas g hg hle with ⟨W, hW, hWV, hleW⟩
      have hWbig : ((1 - eps : ℝ) : EReal) < Lebesgue_measure W := lt_of_lt_of_le hltR hleW
      have hVsub : V ⊆ C \ W := by
        intro x hx
        constructor
        · exact hV_sub_C hx
        · intro hxW
          exact (hWV hxW).2 hx
      have hsum_le : Lebesgue_measure W + Lebesgue_outer_measure V ≤ (1 : EReal) := by
        have hmuV_le : Lebesgue_outer_measure V ≤ Lebesgue_measure (C \ W) :=
          Lebesgue_outer_measure.mono hVsub
        have hW_C : W ⊆ C := by
          intro x hx
          exact (hWV hx).1
        have hunion : Lebesgue_measure C = Lebesgue_measure W + Lebesgue_measure (C \ W) := by
          have hC_eq : C = W ∪ (C \ W) := by
            ext x
            constructor
            · intro hxC
              by_cases hxW : x ∈ W
              · left; exact hxW
              · right; exact ⟨hxC, hxW⟩
            · intro hx
              simp only [Set.mem_union] at hx
              rcases hx with hxW | hx
              · exact hW_C hxW
              · exact (by simpa using hx.1 : x ∈ C)
          have hdisj : W ∩ (C \ W) = ∅ := by
            rw [Set.eq_empty_iff_forall_notMem]
            intro x hx
            exact hx.2.2 hx.1
          conv_lhs => rw [hC_eq]
          exact Lebesgue_measure.union hW (LebesgueMeasurable.inter hC_meas (LebesgueMeasurable.complement hW)) hdisj
        calc
          Lebesgue_measure W + Lebesgue_outer_measure V ≤ Lebesgue_measure W + Lebesgue_measure (C \ W) :=
            add_le_add le_rfl hmuV_le
          _ = Lebesgue_measure C := hunion.symm
          _ = 1 := hC_mu
      have hW_fin : ∃ r : ℝ, Lebesgue_measure W = (r : EReal) := by
        cases hμ : Lebesgue_measure W with
        | bot =>
            exfalso
            have : (0 : EReal) ≤ ⊥ := by rw [← hμ]; exact Lebesgue_outer_measure.nonneg _
            exact (not_le_of_gt EReal.bot_lt_zero) this
        | top =>
            exfalso
            have hle : (⊤ : EReal) ≤ 1 := by
              rw [← hμ]
              have hsub : W ⊆ Real.equiv_EuclideanSpace' '' Set.Icc (0 : ℝ) 1 := by
                intro x hx
                have hxC : x ∈ C := (hWV hx).1
                unfold C at hxC
                rcases hxC with ⟨t, ht, rfl⟩
                exact Set.mem_image_of_mem _ ht
              have hI : Lebesgue_outer_measure (Real.equiv_EuclideanSpace' '' Set.Icc (0 : ℝ) 1) = (1 : EReal) := by
                simpa [Lebesgue_measure] using (Lebesgue_measure.Icc_eq 0 1 (by norm_num))
              exact (Lebesgue_outer_measure.mono hsub).trans (le_of_eq hI)
            exact (by decide : ¬(⊤ : EReal) ≤ 1) hle
        | coe r => exact ⟨r, rfl⟩
      rcases hW_fin with ⟨r, hμW⟩
      have hV_fin_r : ∃ s : ℝ, Lebesgue_outer_measure V = (s : EReal) := by
        cases hμ : Lebesgue_outer_measure V with
        | bot =>
            exfalso
            have : (0 : EReal) ≤ ⊥ := by rw [← hμ]; exact Lebesgue_outer_measure.nonneg _
            exact (not_le_of_gt EReal.bot_lt_zero) this
        | top => exfalso; exact vitali_bounded_pos_finite.2.2 hμ
        | coe s => exact ⟨s, rfl⟩
      rcases hV_fin_r with ⟨s, hμV⟩
      have hr_big : 1 - eps < r := EReal.coe_lt_coe_iff.mp (by simpa [hμW] using hWbig)
      have hrs_le : r + s ≤ 1 := by
        have hc : ((r + s : ℝ) : EReal) ≤ (1 : EReal) := by
          simpa only [hμW, hμV, EReal.coe_add] using hsum_le
        simpa using (EReal.coe_le_coe_iff.mp hc)
      have hs_le : s ≤ eps := by
        dsimp [eps] at hr_big ⊢
        nlinarith
      rw [hμV]
      exact EReal.coe_le_coe_iff.mpr (by simpa [eps] using hs_le)
    have hV0 : Lebesgue_outer_measure V = 0 := by
      cases hμ : Lebesgue_outer_measure V with
      | bot =>
          exfalso
          have : (0 : EReal) ≤ ⊥ := by rw [← hμ]; exact Lebesgue_outer_measure.nonneg _
          exact (not_le_of_gt EReal.bot_lt_zero) this
      | top =>
          exfalso
          have h0 := hmu_le 0
          rw [hμ] at h0
          have : (⊤ : EReal) ≤ 1 := by simpa using h0
          exact (by decide : ¬(⊤ : EReal) ≤ 1) this
      | coe s =>
          have hs0 : s = 0 := by
            by_contra hs
            have hs_pos : 0 < s := by
              have hnonneg : 0 ≤ (s : EReal) := by rw [← hμ]; exact Lebesgue_outer_measure.nonneg _
              exact lt_of_le_of_ne (EReal.coe_nonneg.mp hnonneg) (Ne.symm hs)
            have harch : ∃ n : ℕ, 1 / ((n : ℝ) + 1) < s := by
              obtain ⟨N, hN⟩ := exists_nat_gt (1 / s)
              refine ⟨N, ?_⟩
              have hN' : 1 < (N : ℝ) * s := (div_lt_iff₀ hs_pos).mp hN
              have h1 : 1 < s * ((N : ℝ) + 1) := by nlinarith [hN', hs_pos]
              exact (div_lt_iff₀ (by positivity : 0 < ((N : ℝ) + 1))).mpr h1
            rcases harch with ⟨n, hn⟩
            have hle := hmu_le n
            rw [hμ] at hle
            have hc : s ≤ 1 / ((n : ℝ) + 1) := EReal.coe_le_coe_iff.mp hle
            exact (not_lt_of_ge hc) hn
          rw [hs0]
          rfl
    have hV_pos' : (0 : EReal) < Lebesgue_outer_measure V := vitali_bounded_pos_finite.2.1
    exact (not_lt_of_ge (le_of_eq hV0)) hV_pos'
  exact lt_of_le_of_ne hle1 hne

/- 5. The upper integral of an indicator is its outer measure. -/
lemma upperIntegral_indicator {d} {A : Set (EuclideanSpace' d)} :
    UpperUnsignedLebesgueIntegral (Real.toEReal ∘ A.indicator') = Lebesgue_outer_measure A := by
  apply le_antisymm
  · -- U ≤ μ*:
    apply EReal.le_of_forall_pos_le_add'
    intro ε hε
    have hεE : (0 : EReal) < (ε : EReal) := EReal.coe_pos.mpr hε
    rcases Lebesgue_outer_measure.exists_open_superset_measure_le A (ε : EReal) hεE with ⟨U, hU_open, hAU, hU_le⟩
    apply le_trans
    · apply sInf_le
      refine ⟨Real.toEReal ∘ U.indicator', UnsignedSimpleFunction.indicator (IsOpen.measurable hU_open), ?_⟩
      intro x
      constructor
      · change Real.toEReal (U.indicator' x) ≥ Real.toEReal (A.indicator' x)
        by_cases hx : x ∈ A
        · have hxU : x ∈ U := hAU hx
          rw [Set.indicator'_of_mem hx, Set.indicator'_of_mem hxU]
        · rw [Set.indicator'_of_notMem hx]
          by_cases hxU : x ∈ U
          · rw [Set.indicator'_of_mem hxU]
            exact zero_le_one
          · rw [Set.indicator'_of_notMem hxU]
      · exact (UnsignedSimpleFunction.integral_indicator (IsOpen.measurable hU_open)).symm
    · have hinteg : (UnsignedSimpleFunction.indicator (IsOpen.measurable hU_open)).integ = Lebesgue_measure U :=
        UnsignedSimpleFunction.integral_indicator (IsOpen.measurable hU_open)
      simpa [hinteg] using hU_le
  · -- μ* ≤ U:
    unfold UpperUnsignedLebesgueIntegral
    apply le_sInf
    intro R hR
    rcases hR with ⟨h, hh, hcond⟩
    have hReq : R = hh.integ := (hcond (Classical.arbitrary _)).2
    rw [hReq]
    let hh' : UnsignedSimpleFunction h := hh
    rcases hh with ⟨k, c, E, hmes, heq⟩
    let Aσ : Fin (2^(k+k)) → Set (EuclideanSpace' d) := atom E E
    let v : Fin (2^(k+k)) → EReal := fun σ => atomValueEReal c σ.val
    have hEmeas : ∀ i, LebesgueMeasurable (E i) := fun i => (hmes i).1
    have hc_nonneg : ∀ i, c i ≥ 0 := fun i => (hmes i).2
    have hAσ_meas : ∀ σ, LebesgueMeasurable (Aσ σ) := fun σ => by
      simpa [Aσ] using atom_measurable hEmeas hEmeas σ
    have hv_nonneg : ∀ σ, 0 ≤ v σ := fun σ => atomValueEReal_nonneg hc_nonneg σ.val
    have hh_atoms : h = ∑ σ, v σ • EReal.indicator (Aσ σ) := by
      simpa [v, Aσ] using (heq.trans (eq_sum_atomValueEReal_indicator c E E))
    have hh_integ : hh'.integ = ∑ σ, v σ * Lebesgue_measure (Aσ σ) :=
      UnsignedSimpleFunction.integral_eq hh' (k := 2^(k+k)) (c := v) (E := Aσ)
        hAσ_meas hv_nonneg hh_atoms
    have hcover : A ⊆ ⋃ σ : Fin (2^(k+k)), (if (1 : EReal) ≤ v σ then Aσ σ else ∅) := by
      intro x hx
      have hhge : (1 : EReal) ≤ h x := by
        have hc := (hcond x).1
        have hx1 : Real.toEReal (A.indicator' x) = 1 := by
          rw [Set.indicator'_of_mem hx]
          rfl
        simpa [hx1] using hc
      have hxmem : x ∈ ⋃ σ : Fin (2^(k+k)), Aσ σ := by
        by_contra hnot
        have hz : ∀ σ : Fin (2^(k+k)), EReal.indicator (Aσ σ) x = 0 := by
          intro σ
          apply EReal.indicator_of_notMem
          intro hσ
          exact hnot (Set.mem_iUnion.mpr ⟨σ, hσ⟩)
        have hsum0 : (∑ σ : Fin (2^(k+k)), v σ • EReal.indicator (Aσ σ)) x = 0 := by
          simp [Pi.smul_apply, smul_eq_mul, hz]
        have h0 : h x = 0 := by
          simp [hh_atoms, hsum0]
        rw [h0] at hhge
        exact (not_lt_of_ge hhge) zero_lt_one
      have hmem := Set.mem_iUnion.mp hxmem
      rcases hmem with ⟨σ, hσ⟩
      -- h x = v σ ≥ 1:
      have hvge : (1 : EReal) ≤ v σ := by
        have hxeq : (∑ τ : Fin (2^(k+k)), v τ * EReal.indicator (Aσ τ) x) = v σ := by
          rw [Finset.sum_eq_single σ]
          · rw [EReal.indicator_of_mem hσ, mul_one]
          · intro τ hτ hne
            have hxnot : x ∉ Aσ τ := by
              intro hxτ
              have hd : Disjoint (Aσ σ) (Aσ τ) :=
                atom_pairwiseDisjoint E E (Set.mem_univ σ) (Set.mem_univ τ) hne.symm
              rw [Set.disjoint_left] at hd
              exact (hd hσ) hxτ
            rw [EReal.indicator_of_notMem hxnot, mul_zero]
          · intro h; exact absurd (Finset.mem_univ σ) h
        have hxeq' : h x = v σ := by
          simpa [Pi.smul_apply, smul_eq_mul, hxeq] using (congrFun hh_atoms x)
        simpa [hxeq'] using hhge
      rw [Set.mem_iUnion]
      exact ⟨σ, by
        rw [if_pos hvge]
        exact hσ⟩
    have hmuA_le : Lebesgue_outer_measure A ≤
        (∑ σ : Fin (2^(k+k)), Lebesgue_measure (if (1 : EReal) ≤ v σ then Aσ σ else ∅)) := by
      have hsub : (⋃ σ : Fin (2^(k+k)), (if (1 : EReal) ≤ v σ then Aσ σ else ∅)) ⊆
          (⋃ σ : Fin (2^(k+k)), (if (1 : EReal) ≤ v σ then Aσ σ else ∅)) := by intro x hx; exact hx
      have hle := Lebesgue_outer_measure.finite_union_le
        (E := fun σ : Fin (2^(k+k)) => if (1 : EReal) ≤ v σ then Aσ σ else ∅)
      calc
        Lebesgue_outer_measure A ≤ Lebesgue_outer_measure (⋃ σ : Fin (2^(k+k)), (if (1 : EReal) ≤ v σ then Aσ σ else ∅)) :=
          Lebesgue_outer_measure.mono hcover
        _ ≤ ∑ σ : Fin (2^(k+k)), Lebesgue_measure (if (1 : EReal) ≤ v σ then Aσ σ else ∅) := hle
    have hterm_le : ∀ σ : Fin (2^(k+k)),
        Lebesgue_measure (if (1 : EReal) ≤ v σ then Aσ σ else ∅) ≤ v σ * Lebesgue_measure (Aσ σ) := by
      intro σ
      by_cases hvσ : (1 : EReal) ≤ v σ
      · rw [if_pos hvσ]
        simpa only [one_mul] using (mul_le_mul_of_nonneg_right hvσ (Lebesgue_outer_measure.nonneg (Aσ σ)))
      · rw [if_neg hvσ]
        have hE0 : Lebesgue_measure (∅ : Set (EuclideanSpace' d)) = 0 := by
          simpa [Lebesgue_measure] using (Lebesgue_outer_measure.of_empty (d := d))
        rw [hE0]
        exact EReal.mul_nonneg (hv_nonneg σ) (Lebesgue_outer_measure.nonneg (Aσ σ))
    calc
      Lebesgue_outer_measure A ≤ ∑ σ : Fin (2^(k+k)), Lebesgue_measure (if (1 : EReal) ≤ v σ then Aσ σ else ∅) := hmuA_le
      _ ≤ ∑ σ : Fin (2^(k+k)), v σ * Lebesgue_measure (Aσ σ) := Finset.sum_le_sum (fun σ hσ => hterm_le σ)
      _ = hh'.integ := hh_integ.symm

theorem LowerUnsignedLebesgueIntegral.not_additive : ∃ (d:ℕ) (f g: EuclideanSpace' d → EReal) (_hf: Unsigned f) (_hg: Unsigned g), (LowerUnsignedLebesgueIntegral (f + g) ≠ LowerUnsignedLebesgueIntegral f + LowerUnsignedLebesgueIntegral g) := by
  let V : Set (EuclideanSpace' 1) := Real.equiv_EuclideanSpace' '' VitaliSet
  let C : Set (EuclideanSpace' 1) := Real.equiv_EuclideanSpace' '' Set.Icc (0 : ℝ) 1
  refine ⟨1, Real.toEReal ∘ V.indicator', Real.toEReal ∘ (C \ V).indicator', ?_, ?_, ?_⟩
  · intro x
    change (0 : EReal) ≤ Real.toEReal (V.indicator' x)
    by_cases hx : x ∈ V
    · rw [Set.indicator'_of_mem hx]
      exact zero_le_one
    · rw [Set.indicator'_of_notMem hx]
      exact le_rfl
  · intro x
    change (0 : EReal) ≤ Real.toEReal ((C \ V).indicator' x)
    by_cases hx : x ∈ C \ V
    · rw [Set.indicator'_of_mem hx]
      exact zero_le_one
    · rw [Set.indicator'_of_notMem hx]
      exact le_rfl
  · have hsum : Real.toEReal ∘ V.indicator' + Real.toEReal ∘ (C \ V).indicator' =
        Real.toEReal ∘ C.indicator' := by
      funext x
      change Real.toEReal (V.indicator' x) + Real.toEReal ((C \ V).indicator' x) =
        Real.toEReal (C.indicator' x)
      by_cases hx : x ∈ V
      · have hxC : x ∈ C := by
          rcases hx with ⟨v, hv, rfl⟩
          exact Set.mem_image_of_mem _ (VitaliSet_subset_unit_interval hv)
        have hxnot : x ∉ C \ V := by
          intro hx'
          exact hx'.2 hx
        rw [Set.indicator'_of_mem hx, Set.indicator'_of_notMem hxnot, Set.indicator'_of_mem hxC]
        simp
      · by_cases hxC : x ∈ C
        · have hx' : x ∈ C \ V := ⟨hxC, hx⟩
          rw [Set.indicator'_of_notMem hx, Set.indicator'_of_mem hx', Set.indicator'_of_mem hxC]
          simp
        · rw [Set.indicator'_of_notMem hx,
            Set.indicator'_of_notMem (by intro hx'; exact hxC hx'.1),
            Set.indicator'_of_notMem hxC]
          simp
    have hC_meas : LebesgueMeasurable C := by
      have h_box : C = (BoundedInterval.Icc (0 : ℝ) 1 : Box 1).toSet := by
        unfold C
        have h_interval : Set.Icc (0 : ℝ) 1 = (BoundedInterval.Icc (0 : ℝ) 1).toSet := by rfl
        rw [h_interval, ← BoundedInterval.coe_of_box]
      rw [h_box]
      exact (IsElementary.measurable (IsElementary.box _))
    have hC_mu : Lebesgue_measure C = (1 : EReal) := by
      simpa [C] using (Lebesgue_measure.Icc_eq 0 1 (by norm_num))
    have hL_fg : LowerUnsignedLebesgueIntegral
        (Real.toEReal ∘ V.indicator' + Real.toEReal ∘ (C \ V).indicator') = 1 := by
      rw [hsum]
      rw [LowerUnsignedLebesgueIntegral.eq_simpleIntegral (UnsignedSimpleFunction.indicator hC_meas)]
      rw [UnsignedSimpleFunction.integral_indicator hC_meas]
      exact hC_mu
    have hL_f : LowerUnsignedLebesgueIntegral (Real.toEReal ∘ V.indicator') = 0 := vitali_inner_measure_zero
    have hL_g : LowerUnsignedLebesgueIntegral (Real.toEReal ∘ (C \ V).indicator') < 1 := complement_lower_lt_one
    rw [hL_fg]
    rw [hL_f]
    exact ne_of_gt (by simpa using hL_g)

theorem UpperUnsignedLebesgueIntegral.not_additive : ∃ (d:ℕ) (f g: EuclideanSpace' d → EReal) (_hf: Unsigned f) (_hg: Unsigned g), (UpperUnsignedLebesgueIntegral (f + g) ≠ UpperUnsignedLebesgueIntegral f + UpperUnsignedLebesgueIntegral g) := by
  let V : Set (EuclideanSpace' 1) := Real.equiv_EuclideanSpace' '' VitaliSet
  let C : Set (EuclideanSpace' 1) := Real.equiv_EuclideanSpace' '' Set.Icc (0 : ℝ) 1
  refine ⟨1, Real.toEReal ∘ V.indicator', Real.toEReal ∘ (C \ V).indicator', ?_, ?_, ?_⟩
  · intro x
    change (0 : EReal) ≤ Real.toEReal (V.indicator' x)
    by_cases hx : x ∈ V
    · rw [Set.indicator'_of_mem hx]
      exact zero_le_one
    · rw [Set.indicator'_of_notMem hx]
      exact le_rfl
  · intro x
    change (0 : EReal) ≤ Real.toEReal ((C \ V).indicator' x)
    by_cases hx : x ∈ C \ V
    · rw [Set.indicator'_of_mem hx]
      exact zero_le_one
    · rw [Set.indicator'_of_notMem hx]
      exact le_rfl
  · have hsum : Real.toEReal ∘ V.indicator' + Real.toEReal ∘ (C \ V).indicator' =
        Real.toEReal ∘ C.indicator' := by
      funext x
      change Real.toEReal (V.indicator' x) + Real.toEReal ((C \ V).indicator' x) =
        Real.toEReal (C.indicator' x)
      by_cases hx : x ∈ V
      · have hxC : x ∈ C := by
          rcases hx with ⟨v, hv, rfl⟩
          exact Set.mem_image_of_mem _ (VitaliSet_subset_unit_interval hv)
        have hxnot : x ∉ C \ V := by
          intro hx'
          exact hx'.2 hx
        rw [Set.indicator'_of_mem hx, Set.indicator'_of_notMem hxnot, Set.indicator'_of_mem hxC]
        simp
      · by_cases hxC : x ∈ C
        · have hx' : x ∈ C \ V := ⟨hxC, hx⟩
          rw [Set.indicator'_of_notMem hx, Set.indicator'_of_mem hx', Set.indicator'_of_mem hxC]
          simp
        · rw [Set.indicator'_of_notMem hx,
            Set.indicator'_of_notMem (by intro hx'; exact hxC hx'.1),
            Set.indicator'_of_notMem hxC]
          simp
    have hC_meas : LebesgueMeasurable C := by
      have h_box : C = (BoundedInterval.Icc (0 : ℝ) 1 : Box 1).toSet := by
        unfold C
        have h_interval : Set.Icc (0 : ℝ) 1 = (BoundedInterval.Icc (0 : ℝ) 1).toSet := by rfl
        rw [h_interval, ← BoundedInterval.coe_of_box]
      rw [h_box]
      exact (IsElementary.measurable (IsElementary.box _))
    have hC_mu : Lebesgue_measure C = (1 : EReal) := by
      simpa [C] using (Lebesgue_measure.Icc_eq 0 1 (by norm_num))
    have hU_fg : UpperUnsignedLebesgueIntegral
        (Real.toEReal ∘ V.indicator' + Real.toEReal ∘ (C \ V).indicator') = 1 := by
      rw [hsum]
      rw [upperIntegral_indicator (A := C)]
      exact hC_mu
    have hU_f : UpperUnsignedLebesgueIntegral (Real.toEReal ∘ V.indicator') = Lebesgue_outer_measure V :=
      upperIntegral_indicator (A := V)
    have hU_g : UpperUnsignedLebesgueIntegral (Real.toEReal ∘ (C \ V).indicator') = Lebesgue_outer_measure (C \ V) :=
      upperIntegral_indicator (A := C \ V)
    have hVb : Bornology.IsBounded V := vitali_bounded_pos_finite.1
    have hV_fin : Lebesgue_outer_measure V ≠ ⊤ := vitali_bounded_pos_finite.2.2
    have hinner_ne : inner_measure hVb ≠ Lebesgue_outer_measure V := by
      intro h
      exact VitaliSet.nonmeasurable ((inner_measure.eq_iff hVb).mp h)
    have hV_sub_C : V ⊆ C := by
      intro x hx
      rcases hx with ⟨v, hv, rfl⟩
      exact Set.mem_image_of_mem _ (VitaliSet_subset_unit_interval hv)
    have hB : IsElementary C := by
      have h_box : C = (BoundedInterval.Icc (0 : ℝ) 1 : Box 1).toSet := by
        unfold C
        have h_interval : Set.Icc (0 : ℝ) 1 = (BoundedInterval.Icc (0 : ℝ) 1).toSet := by rfl
        rw [h_interval, ← BoundedInterval.coe_of_box]
      rw [h_box]
      exact IsElementary.box _
    have hinner_eq : (inner_measure hVb : EReal) = Lebesgue_measure C - Lebesgue_outer_measure (C \ V) :=
      inner_measure.eq hVb hB hV_sub_C
    have hneq : Lebesgue_outer_measure V + Lebesgue_outer_measure (C \ V) ≠ 1 := by
      intro heq
      have hsub : Lebesgue_measure C - Lebesgue_outer_measure (C \ V) = Lebesgue_outer_measure V := by
        cases hμV' : Lebesgue_outer_measure V with
        | bot =>
            exfalso
            have : (0 : EReal) ≤ ⊥ := by rw [← hμV']; exact Lebesgue_outer_measure.nonneg _
            exact (not_le_of_gt EReal.bot_lt_zero) this
        | top => exfalso; exact hV_fin hμV'
        | coe s =>
            cases hμC' : Lebesgue_outer_measure (C \ V) with
            | bot =>
                exfalso
                have : (0 : EReal) ≤ ⊥ := by rw [← hμC']; exact Lebesgue_outer_measure.nonneg _
                exact (not_le_of_gt EReal.bot_lt_zero) this
            | top =>
                exfalso
                have hle : (⊤ : EReal) ≤ 1 := by
                  rw [← hμC']
                  exact (Lebesgue_outer_measure.mono (Set.diff_subset : C \ V ⊆ C)).trans (le_of_eq hC_mu)
                exact (by decide : ¬(⊤ : EReal) ≤ 1) hle
            | coe t =>
                have hst : s + t = 1 := by
                  have hc : ((s + t : ℝ) : EReal) = (1 : EReal) := by
                    simpa [hμV', hμC', EReal.coe_add] using heq
                  exact EReal.coe_eq_coe_iff.mp hc
                have ht : t = 1 - s := by linarith
                rw [hC_mu]
                change (((1 : ℝ) - t : ℝ) : EReal) = (s : EReal)
                rw [ht]
                simp
      have hinner : (inner_measure hVb : EReal) = Lebesgue_outer_measure V := by
        rw [hinner_eq]
        exact hsub
      exact hinner_ne hinner
    rw [hU_fg, hU_f, hU_g]
    exact hneq.symm



/-- Exercise 1.3.13 (Area interpretation of integral). -/
theorem LowerUnsignedLebesgueIntegral.eq_area {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) :
    LowerUnsignedLebesgueIntegral f = Lebesgue_measure { p | ∃ x, ∃ t:ℝ, EuclideanSpace'.prod_equiv d 1 p = ⟨ x, t ⟩ ∧ 0 ≤ t ∧ t ≤ f x } := by sorry

private lemma iUnion_rat_reindex {α : Type*} (F : ℚ → Set α) (e : ℕ → ℚ) (he : Function.Surjective e) :
    (⋃ q : ℚ, F q) = ⋃ n : ℕ, F (e n) := by
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · intro ⟨q, hq⟩
    obtain ⟨n, hn⟩ := he q
    exact ⟨n, by simpa [hn] using hq⟩
  · intro ⟨n, hn⟩
    exact ⟨e n, hn⟩

/-- Given b ≥ 0, b ≠ ⊤ and b + t' < a, find a rational q with q < a and b + t' < q. -/
private lemma exists_rat_btwn_sub {a b : EReal} (hb0 : 0 ≤ b) (hb_top : b ≠ ⊤) (t' : ℝ)
    (h : b + (t' : EReal) < a) : ∃ q : ℚ, a > ((q : ℝ) : EReal) ∧ b + (t' : EReal) < ((q : ℝ) : EReal) := by
  have hb_bot : b ≠ ⊥ := ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero hb0)
  have hb_eq : b = (b.toReal : EReal) := (EReal.coe_toReal hb_top hb_bot).symm
  by_cases ha_top : a = ⊤
  · obtain ⟨q, hq⟩ := exists_rat_gt (b.toReal + t')
    refine ⟨q, ?_, ?_⟩
    · rw [ha_top]
      exact EReal.coe_lt_top (q : ℝ)
    · rw [hb_eq, ← EReal.coe_add]
      exact EReal.coe_lt_coe_iff.mpr hq
  · have ha_bot : a ≠ ⊥ := by
      intro ha
      rw [ha] at h
      exact (not_lt_bot h).elim
    have ha_eq : a = (a.toReal : EReal) := (EReal.coe_toReal ha_top ha_bot).symm
    have h' : b.toReal + t' < a.toReal := by
      rw [hb_eq, ha_eq, ← EReal.coe_add] at h
      exact EReal.coe_lt_coe_iff.mp h
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (by linarith : b.toReal + t' < a.toReal)
    refine ⟨q, ?_, ?_⟩
    · rw [ha_eq]
      exact EReal.coe_lt_coe_iff.mpr hq2
    · rw [hb_eq, ← EReal.coe_add]
      exact EReal.coe_lt_coe_iff.mpr hq1

/-- Level set of (g - f) above a real threshold, for f ≥ 0, f ≠ ⊤. -/
private lemma sub_gt_set_eq {d : ℕ} {f g : EuclideanSpace' d → EReal} (hf0 : ∀ x, 0 ≤ f x)
    (hf_top : ∀ x, f x ≠ ⊤) (t' : ℝ) :
    {x | g x - f x > (t' : EReal)} =
      ⋃ (q : ℚ), ({x | g x > ((q : ℝ) : EReal)} ∩ {x | f x < (((q : ℝ) - t' : ℝ) : EReal)}) := by
  ext x
  constructor
  · intro hx
    rw [Set.mem_iUnion]
    have h_add : (t' : EReal) + f x < g x :=
      (EReal.lt_sub_iff_add_lt (a := g x) (b := f x) (c := (t' : EReal))
        (Or.inl (ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (hf0 x))))
        (Or.inl (hf_top x))).mp hx
    rcases exists_rat_btwn_sub (a := g x) (b := f x) (hf0 x) (hf_top x) t'
      (by simpa [add_comm] using h_add) with ⟨q, hgq, hfq⟩
    refine ⟨q, hgq, ?_⟩
    exact (EReal.lt_sub_iff_add_lt (a := ((q : ℝ) : EReal)) (b := (t' : EReal)) (c := f x)
      (Or.inr (hf_top x))
      (Or.inr (ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (hf0 x))))).mpr hfq
  · intro hx
    rw [Set.mem_iUnion] at hx
    rcases hx with ⟨q, hgq, hfq⟩
    change f x < (((q : ℝ) - t' : ℝ) : EReal) at hfq
    have hfq' : f x + (t' : EReal) < ((q : ℝ) : EReal) :=
      (EReal.lt_sub_iff_add_lt (a := ((q : ℝ) : EReal)) (b := (t' : EReal)) (c := f x)
        (Or.inr (hf_top x))
        (Or.inr (ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (hf0 x))))).mp hfq
    have h_add : (t' : EReal) + f x < g x := lt_trans (by simpa [add_comm] using hfq') hgq
    exact (EReal.lt_sub_iff_add_lt (a := g x) (b := f x) (c := (t' : EReal))
      (Or.inl (ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (hf0 x))))
      (Or.inl (hf_top x))).mpr h_add

/-- Corrected version of the sub measurable lemma: f additionally never takes value top. -/
lemma sub_measurable {d : ℕ} {f g : EuclideanSpace' d → EReal} (hf : UnsignedMeasurable f)
    (hg : UnsignedMeasurable g) (hf_ne_top : ∀ x, f x ≠ ⊤) (hfg : ∀ x, f x ≤ g x) :
    UnsignedMeasurable (fun x => g x - f x) := by
  have hf0 : ∀ x, 0 ≤ f x := hf.1
  have hf_ne_bot : ∀ x, f x ≠ ⊥ := fun x => ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (hf0 x))
  have h_uns : Unsigned (fun x => g x - f x) := by
    intro x
    exact (EReal.sub_nonneg (Or.inr (hf_ne_top x)) (Or.inr (hf_ne_bot x))).mpr (hfg x)
  have h4 : ∀ t : EReal, LebesgueMeasurable {x | g x - f x > t} := by
    intro t
    rcases eq_bot_or_bot_lt t with rfl | ht_bot
    · have h_eq : {x | g x - f x > ⊥} = Set.univ := by
        ext x
        constructor
        · intro hx
          trivial
        · intro hx
          exact lt_of_lt_of_le EReal.bot_lt_zero
            ((EReal.sub_nonneg (Or.inr (hf_ne_top x)) (Or.inr (hf_ne_bot x))).mpr (hfg x))
      rw [h_eq, ← Set.compl_empty]
      exact LebesgueMeasurable.empty.complement
    rcases eq_top_or_lt_top t with rfl | ht_top
    · have h_eq : {x | g x - f x > ⊤} = (∅ : Set (EuclideanSpace' d)) := by
        ext x
        constructor
        · intro hx
          change (⊤ : EReal) < g x - f x at hx
          exact (not_le_of_gt hx) (le_top : g x - f x ≤ ⊤)
        · intro hx
          exact False.elim hx
      exact h_eq ▸ LebesgueMeasurable.empty
    · induction t using EReal.rec with
      | bot => exact (not_lt.mpr le_rfl ht_bot).elim
      | top => exact (not_lt.mpr le_rfl ht_top).elim
      | coe t' =>
          have h_eq : {x | g x - f x > (t' : EReal)} =
              ⋃ q : ℚ, ({x | g x > ((q : ℝ) : EReal)} ∩ {x | f x < (((q : ℝ) - t' : ℝ) : EReal)}) :=
            sub_gt_set_eq hf0 hf_ne_top t'
          obtain ⟨e, he⟩ := exists_surjective_nat ℚ
          rw [h_eq]
          rw [iUnion_rat_reindex (fun q : ℚ => ({x | g x > ((q : ℝ) : EReal)} ∩
            {x | f x < (((q : ℝ) - t' : ℝ) : EReal)})) e he]
          apply LebesgueMeasurable.countable_union
          intro n
          apply LebesgueMeasurable.inter
          · exact (((_root_.UnsignedMeasurable.TFAE hg.1).out 0 4
              (a := _root_.UnsignedMeasurable g)
              (b := ∀ t : EReal, LebesgueMeasurable {x | g x > t})).mp hg) (((e n : ℚ) : ℝ) : EReal)
          · exact (((_root_.UnsignedMeasurable.TFAE hf.1).out 0 6
              (a := _root_.UnsignedMeasurable f)
              (b := ∀ t : EReal, LebesgueMeasurable {x | f x < t})).mp hf) ((((e n : ℚ) : ℝ) - t' : ℝ) : EReal)
  exact (((_root_.UnsignedMeasurable.TFAE h_uns).out 4 0
    (a := ∀ t : EReal, LebesgueMeasurable {x | g x - f x > t})
    (b := _root_.UnsignedMeasurable (fun x => g x - f x))).mp h4)

/-- Structural fact: for bounded nonneg v the vertical truncation sequence is eventually
    constant (min v n = v), so the hvert axiom is automatically satisfied and constrains
    integ v in no way. -/
lemma vert_eventually_const {d : ℕ} {v : EuclideanSpace' d → EReal} (hv0 : ∀ x, 0 ≤ v x)
    (hbound : EReal.BoundedFunction v) :
    ∀ᶠ n : ℕ in atTop, (fun x : EuclideanSpace' d => min (v x) (n : EReal)) = v := by
  rcases hbound with ⟨M, hM⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (M : NNReal)
  filter_upwards [eventually_ge_atTop N] with n hn
  funext x
  apply le_antisymm
  · exact min_le_left _ _
  · by_cases hvx_top : v x = ⊤
    · exfalso
      have habs : (⊤ : EReal).abs ≤ (M : NNReal) := by simpa [hvx_top] using hM x
      rw [EReal.abs_top] at habs
      exact (not_le_of_gt (ENNReal.coe_lt_top (r := (M : NNReal)))) habs
    · have hvx_bot : v x ≠ ⊥ := ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (hv0 x))
      have hvx_eq : v x = ((v x).toReal : EReal) := (EReal.coe_toReal hvx_top hvx_bot).symm
      have hr_le_M : (v x).toReal ≤ (M : ℝ) := by
        have habs : ((v x).toReal : EReal).abs ≤ (M : ENNReal) := by
          rw [← hvx_eq]
          exact hM x
        rw [EReal.abs_def] at habs
        have habs' : |(v x).toReal| ≤ (M : ℝ) := by
          rw [← ENNReal.ofReal_coe_nnreal] at habs
          exact (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ (M : ℝ))).mp habs
        exact le_trans (le_abs_self _) habs'
      have hM_le_n : (M : ℝ) ≤ (n : ℝ) := by
        have hM_le_N : (M : ℝ) ≤ (N : ℝ) := by
          exact_mod_cast (le_of_lt hN)
        exact le_trans hM_le_N (by exact_mod_cast hn)
      have hr_le_n : (v x).toReal ≤ (n : ℝ) := le_trans hr_le_M hM_le_n
      have hvx_le_n : v x ≤ (n : EReal) := by
        rw [hvx_eq]
        exact_mod_cast hr_le_n
      exact le_min le_rfl hvx_le_n

/-- Structural fact: for v with support in ball m the horizontal truncation sequence is
    eventually constant (v·1_ball_m' = v for m' ≥ m), so the hhoriz axiom is automatically
    satisfied and constrains integ v in no way. -/
lemma horiz_eventually_const_of_supp_ball {d : ℕ} {v : EuclideanSpace' d → EReal}
    (m : ℕ) (hvsupp : Support v ⊆ Metric.ball (0 : EuclideanSpace' d) m) :
    ∀ᶠ m' : ℕ in atTop,
      v * Real.toEReal ∘ (Metric.ball (0 : EuclideanSpace' d) m').indicator' = v := by
  filter_upwards [eventually_ge_atTop m] with m' hm'
  funext x
  by_cases hx : x ∈ Support v
  · have hx_ball : x ∈ Metric.ball (0 : EuclideanSpace' d) m := hvsupp hx
    have hx_ball' : x ∈ Metric.ball (0 : EuclideanSpace' d) m' :=
      Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hx_ball) (by exact_mod_cast hm'))
    simp [hx_ball']
  · have hvx0 : v x = 0 := by
      by_contra h
      exact hx (by simpa [Support] using h)
    simp [hvx0]


/-- integ is monotone on bounded functions: f ≤ g pointwise, both measurable and
    f never takes the value top, hence integ f ≤ integ g.
    Decompose g = f + (g - f); by additivity integ g = integ f + integ (g - f),
    and integ (g - f) is nonnegative by hnonneg. -/
lemma integ_mono_bounded {d : ℕ} {integ : (EuclideanSpace' d → EReal) → EReal}
  (_hsimple : ∀ f (hf: UnsignedSimpleFunction f), integ f = hf.integ)
  (hadd: ∀ f g (_hf: UnsignedMeasurable f) (_hg: UnsignedMeasurable g), integ (f + g) = integ f + integ g)
  (_hvert: ∀ f (_hf: UnsignedMeasurable f), Filter.atTop.Tendsto (fun n:ℕ ↦ integ (fun x ↦ min (f x) n)) (nhds (integ f)))
  (_hhoriz: ∀ f (_hf: UnsignedMeasurable f), Filter.atTop.Tendsto (fun n:ℕ ↦ integ (f * Real.toEReal ∘ (Metric.ball 0 n).indicator')) (nhds (integ f)))
  (hnonneg: ∀ f (_hf: UnsignedMeasurable f), 0 ≤ integ f)
  {f g : EuclideanSpace' d → EReal} (hf : UnsignedMeasurable f) (hg : UnsignedMeasurable g)
  (hf_ne_top : ∀ x, f x ≠ ⊤) (hfg : ∀ x, f x ≤ g x) : integ f ≤ integ g := by
  have hsub : UnsignedMeasurable (fun x => g x - f x) := sub_measurable hf hg hf_ne_top hfg
  have hf0 : ∀ x, 0 ≤ f x := hf.1
  have hf_ne_bot : ∀ x, f x ≠ ⊥ := fun x => ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (hf0 x))
  have hdecomp : f + (fun x => g x - f x) = g := by
    funext x
    have hcancel : (g x - f x) + f x = g x := sub_add_cancel_finite (hf_ne_top x) (hf_ne_bot x)
    simpa [add_comm] using hcancel
  have hg_eq : integ g = integ f + integ (fun x => g x - f x) := by
    calc
      integ g = integ (f + (fun x => g x - f x)) := by rw [hdecomp]
      _ = integ f + integ (fun x => g x - f x) := hadd f (fun x => g x - f x) hf hsub
  have hnonneg_sub : 0 ≤ integ (fun x => g x - f x) := hnonneg (fun x => g x - f x) hsub
  rw [hg_eq]
  exact le_add_of_nonneg_right hnonneg_sub

/-- A bounded EReal-valued function never takes the value top. -/
private lemma bounded_ne_top {v : EuclideanSpace' d → EReal} (hbound : EReal.BoundedFunction v) :
    ∀ x, v x ≠ ⊤ := by
  intro x hx_top
  rcases hbound with ⟨M, hM⟩
  have habs : (⊤ : EReal).abs ≤ (M : NNReal) := by simpa [hx_top] using hM x
  rw [EReal.abs_top] at habs
  exact (not_le_of_gt (ENNReal.coe_lt_top (r := (M : NNReal)))) habs

/-- integ agrees with the lower integral on bounded finite-support functions.
    Sandwich: by UnsignedMeasurable.bounded_iff there are simple g₀ with g₀ → v uniformly;
    g₁ := max (g₀ - ε) 0 ≤ v ≤ g₂ := (g₀ + ε) · ind, g₂ ≤ g₁ + 2ε · ind.
    integ g₁ = g₁.integ ≤ L v ≤ U v = L v ≤ g₂.integ = integ g₂ via eq_upperIntegral,
    and integ g₁ ≤ integ v ≤ integ g₂ via integ_mono_bounded; let ε → 0 to get integ v = L v. -/
lemma integ_eq_L_bounded {d : ℕ} {integ : (EuclideanSpace' d → EReal) → EReal}
  (hsimple : ∀ f (hf: UnsignedSimpleFunction f), integ f = hf.integ)
  (hadd: ∀ f g (_hf: UnsignedMeasurable f) (_hg: UnsignedMeasurable g), integ (f + g) = integ f + integ g)
  (hvert: ∀ f (_hf: UnsignedMeasurable f), Filter.atTop.Tendsto (fun n:ℕ ↦ integ (fun x ↦ min (f x) n)) (nhds (integ f)))
  (hhoriz: ∀ f (_hf: UnsignedMeasurable f), Filter.atTop.Tendsto (fun n:ℕ ↦ integ (f * Real.toEReal ∘ (Metric.ball 0 n).indicator')) (nhds (integ f)))
  (hnonneg: ∀ f (_hf: UnsignedMeasurable f), 0 ≤ integ f)
  {v : EuclideanSpace' d → EReal} (hv : UnsignedMeasurable v)
  (hbound : EReal.BoundedFunction v) (hsupp : FiniteMeasureSupport v) :
  integ v = LowerUnsignedLebesgueIntegral v := by
  have hv_ne_top : ∀ x, v x ≠ ⊤ := bounded_ne_top hbound
  apply le_antisymm
  · -- integ v ≤ L v: L v = U v, and U v = sInf over simple h ≥ v of h.integ
    rw [LowerUnsignedLebesgueIntegral.eq_upperIntegral hv hbound hsupp]
    unfold UpperUnsignedLebesgueIntegral
    apply le_sInf
    intro R hR
    rcases hR with ⟨h, hh, hcond⟩
    have hv_le_h : ∀ x, v x ≤ h x := fun x => (hcond x).1
    have hR_eq : R = hh.integ := (hcond (Classical.arbitrary _)).2
    calc
      integ v ≤ integ h :=
        integ_mono_bounded hsimple hadd hvert hhoriz hnonneg hv
          (UnsignedSimpleFunction.unsignedMeasurable hh) hv_ne_top hv_le_h
      _ = hh.integ := hsimple h hh
      _ = R := hR_eq.symm
  · -- L v ≤ integ v: L v = sSup over simple g ≤ v of g.integ
    unfold LowerUnsignedLebesgueIntegral
    apply sSup_le
    intro R hR
    rcases hR with ⟨g, hg, hcond⟩
    have hg_le_v : ∀ x, g x ≤ v x := fun x => (hcond x).1
    have hR_eq : R = hg.integ := (hcond (Classical.arbitrary _)).2
    have hg_ne_top : ∀ x, g x ≠ ⊤ := by
      intro x hgx_top
      exact hv_ne_top x (le_antisymm le_top (by simpa [hgx_top] using hg_le_v x))
    calc
      R = hg.integ := hR_eq
      _ = integ g := (hsimple g hg).symm
      _ ≤ integ v :=
        integ_mono_bounded hsimple hadd hvert hhoriz hnonneg
          (UnsignedSimpleFunction.unsignedMeasurable hg) hv hg_ne_top hg_le_v

/-- Multiplying a bounded function by a set indicator keeps it bounded, since the
    indicator takes only the values 0 and 1. -/
private lemma bounded_mul_indicator {d : ℕ} {h : EuclideanSpace' d → EReal}
    (hbound : EReal.BoundedFunction h) {E : Set (EuclideanSpace' d)} :
    EReal.BoundedFunction (h * Real.toEReal ∘ E.indicator') := by
  rcases hbound with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro x
  by_cases hx : x ∈ E
  · have hind : Real.toEReal (E.indicator' x) = (1 : EReal) := by
      simp [Set.indicator'_of_mem hx]
    simpa [Pi.mul_apply, Function.comp_apply, hind] using hM x
  · have hind : Real.toEReal (E.indicator' x) = (0 : EReal) := by
      simp [Set.indicator'_of_notMem hx]
    simp [Pi.mul_apply, Function.comp_apply, hind]

/-- Exercise 1.3.14 (Uniqueness) -/

-- NOTE: the book's statement has codomain [0, +∞] for the functional; the Lean version
-- therefore needs the explicit nonnegativity hypothesis `hnonneg` (the naive 4-axiom
-- statement without it is FALSE: on bounded finitely-supported functions both truncation
-- axioms are vacuous, and hsimple+hadd do not force nonnegativity of the values).
theorem UnsignedLebesgueIntegral.unique {d:ℕ} (integ: (EuclideanSpace' d → EReal) → EReal)
  (hsimple : ∀ f (hf: UnsignedSimpleFunction f), integ f = hf.integ)
  (hadd: ∀ f g (_hf: UnsignedMeasurable f) (_hg: UnsignedMeasurable g), integ (f + g) = integ f + integ g)
  (hvert: ∀ f (_hf: UnsignedMeasurable f), Filter.atTop.Tendsto (fun n:ℕ ↦ integ (fun x ↦ min (f x) n)) (nhds (integ f)))
  (hhoriz: ∀ f (_hf: UnsignedMeasurable f), Filter.atTop.Tendsto (fun n:ℕ ↦ integ (f * Real.toEReal ∘ (Metric.ball 0 n).indicator')) (nhds (integ f)))
  (hnonneg: ∀ f (_hf: UnsignedMeasurable f), 0 ≤ integ f)
  : ∀ f, UnsignedMeasurable f → integ f = UnsignedLebesgueIntegral f := by

  -- integ f = limₙ integ (min f n) [hvert]; for each n: min f n is bounded (bounded_min_const).
  -- integ (min f n) = limₘ integ (min f n · 1_ball m) [hhoriz on min f n]; each truncation is
  -- bounded finite-support (FiniteMeasureSupport.mul_indicator_ball), so integ = L there by
  -- integ_eq_L_bounded; L (min f n · 1_ball m) → L (min f n) [eq_lim_horiz_trunc] → L f
  -- [eq_lim_vert_trunc].  Chain with tendsto_nhds_unique.
  intro f hf
  have hfn_meas : ∀ n : ℕ, UnsignedMeasurable (fun x => min (f x) n) := by
    intro n
    have hφ : Continuous (fun y : EReal => min y ((n : ℝ) : EReal)) := by
      simpa using (Continuous.min continuous_id continuous_const : Continuous (fun y : EReal => min y ((n : ℝ) : EReal)))
    have hφnn : ∀ x ≥ (0 : EReal), min x ((n : ℝ) : EReal) ≥ 0 := by
      intro x hx
      exact le_min hx (EReal.coe_nonneg.mpr (Nat.cast_nonneg n))
    simpa using UnsignedMeasurable.comp_cts hf hφ hφnn
  have hfn_bound : ∀ n : ℕ, EReal.BoundedFunction (fun x => min (f x) n) :=
    fun n => bounded_min_const hf.1 n
  have hagree : ∀ n : ℕ,
      integ (fun x => min (f x) n) = LowerUnsignedLebesgueIntegral (fun x => min (f x) n) := by
    intro n
    apply tendsto_nhds_unique (hhoriz (fun x => min (f x) n) (hfn_meas n))
    have hconv : Tendsto (fun m : ℕ =>
        LowerUnsignedLebesgueIntegral ((fun x => min (f x) n) * Real.toEReal ∘ (Metric.ball (0 : EuclideanSpace' d) m).indicator'))
        atTop (𝓝 (LowerUnsignedLebesgueIntegral (fun x => min (f x) n))) :=
      LowerUnsignedLebesgueIntegral.eq_lim_horiz_trunc (hfn_meas n)
    exact hconv.congr (fun m => (integ_eq_L_bounded hsimple hadd hvert hhoriz hnonneg
      (hv := UnsignedMeasurable.mul_indicator_ball (hfn_meas n) m)
      (hbound := bounded_mul_indicator (hfn_bound n))
      (hsupp := FiniteMeasureSupport.mul_indicator_ball (n := m))).symm)
  apply tendsto_nhds_unique (hvert f hf)
  have hconvL : Tendsto (fun n : ℕ => LowerUnsignedLebesgueIntegral (fun x => min (f x) n))
      atTop (𝓝 (LowerUnsignedLebesgueIntegral f)) :=
    LowerUnsignedLebesgueIntegral.eq_lim_vert_trunc hf
  have h2 : Tendsto (fun n : ℕ => integ (fun x => min (f x) n))
      atTop (𝓝 (LowerUnsignedLebesgueIntegral f)) :=
    hconvL.congr (fun n => (hagree n).symm)
  simpa [UnsignedLebesgueIntegral] using h2


/-- Translating a simple function by a is still simple: translate the atoms. -/
lemma simple_translate {d : ℕ} {g : EuclideanSpace' d → EReal} (hg : UnsignedSimpleFunction g)
    (a : EuclideanSpace' d) :
    UnsignedSimpleFunction (fun x => g (x + a)) := by
  obtain ⟨k, c, E, ⟨hmes, heq⟩⟩ := hg
  use k, c, (fun i => E i + {-a})
  constructor
  · intro i
    exact ⟨(LebesgueMeasurable.translate (E i) (-a)).mp (hmes i).1, (hmes i).2⟩
  · funext x
    rw [heq]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    have hmem : x + a ∈ E i ↔ x ∈ E i + {-a} := by simp
    have hind : EReal.indicator (E i) (x + a) = EReal.indicator (E i + {-a}) x := by
      by_cases h : x + a ∈ E i
      · rw [EReal.indicator_of_mem h, EReal.indicator_of_mem (hmem.mp h)]
      · rw [EReal.indicator_of_notMem h, EReal.indicator_of_notMem (mt hmem.mpr h)]
    rw [hind]

/-- Translating a simple function preserves its integral. -/
lemma integral_translate {d : ℕ} {g : EuclideanSpace' d → EReal} (hg : UnsignedSimpleFunction g)
    (a : EuclideanSpace' d) : (simple_translate hg a).integ = hg.integ := by
  obtain ⟨k, c, E, ⟨hmes, heq⟩⟩ := hg
  have hg' : UnsignedSimpleFunction g := ⟨k, c, E, ⟨hmes, heq⟩⟩
  have hsimple : (fun x => g (x + a)) = ∑ i, (c i) • (EReal.indicator (E i + {-a})) := by
    funext x
    rw [heq]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    have hmem : x + a ∈ E i ↔ x ∈ E i + {-a} := by simp
    have hind : EReal.indicator (E i) (x + a) = EReal.indicator (E i + {-a}) x := by
      by_cases h : x + a ∈ E i
      · rw [EReal.indicator_of_mem h, EReal.indicator_of_mem (hmem.mp h)]
      · rw [EReal.indicator_of_notMem h, EReal.indicator_of_notMem (mt hmem.mpr h)]
    rw [hind]
  have h1 : (simple_translate hg' a).integ = ∑ i, c i * Lebesgue_measure (E i + {-a}) :=
    UnsignedSimpleFunction.integral_eq (simple_translate hg' a) (k := k) (c := c)
      (E := fun i => E i + {-a})
      (hmes := fun i => (LebesgueMeasurable.translate (E i) (-a)).mp (hmes i).1)
      (hnonneg := fun i => (hmes i).2) (heq := hsimple)
  have h2 : hg'.integ = ∑ i, c i * Lebesgue_measure (E i) :=
    UnsignedSimpleFunction.integral_eq hg' (k := k) (c := c) (E := E)
      (hmes := fun i => (hmes i).1) (hnonneg := fun i => (hmes i).2) (heq := heq)
  calc
    (simple_translate hg' a).integ = ∑ i, c i * Lebesgue_measure (E i + {-a}) := h1
    _ = ∑ i, c i * Lebesgue_measure (E i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Lebesgue_measure.translate (-a) (hmes i).1]
    _ = hg'.integ := h2.symm

/-- Exercise 1.3.15 (Translation invariance)-/
theorem UnsignedLebesgueIntegral.trans {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) (a: EuclideanSpace' d) :
    UnsignedLebesgueIntegral (fun x ↦ f (x + a)) = hf.integ := by
  change LowerUnsignedLebesgueIntegral (fun x => f (x + a)) = LowerUnsignedLebesgueIntegral f
  unfold LowerUnsignedLebesgueIntegral
  apply le_antisymm
  · apply sSup_le
    intro R hR
    rcases hR with ⟨g, hg, hcond⟩
    have hle : ∀ x, g x ≤ f (x + a) := fun x => (hcond x).1
    have hReq : R = hg.integ := (hcond (Classical.arbitrary _)).2
    rw [hReq]
    refine le_sSup ?_
    refine ⟨fun x => g (x + (-a)), simple_translate hg (-a), ?_⟩
    intro x
    constructor
    · calc
        g (x + (-a)) ≤ f ((x + (-a)) + a) := hle (x + (-a))
        _ = f x := by simp
    · exact (integral_translate hg (-a)).symm
  · apply sSup_le
    intro R hR
    rcases hR with ⟨g, hg, hcond⟩
    have hle : ∀ x, g x ≤ f x := fun x => (hcond x).1
    have hReq : R = hg.integ := (hcond (Classical.arbitrary _)).2
    rw [hReq]
    refine le_sSup ?_
    refine ⟨fun x => g (x + a), simple_translate hg a, ?_⟩
    intro x
    constructor
    · exact hle (x + a)
    · exact (integral_translate hg a).symm

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

/-- The measure of the preimage of (0,a) under the coordinate projection is a. -/
lemma measure_Ioo_zero {a : ℝ} (ha : 0 ≤ a) :
    Lebesgue_measure (EuclideanSpace'.equiv_Real ⁻¹' Set.Ioo (0 : ℝ) a) = (a : EReal) := by
  let B : Box 1 := (BoundedInterval.Ioo (0 : ℝ) a : Box 1)
  have hset : EuclideanSpace'.equiv_Real ⁻¹' Set.Ioo (0 : ℝ) a = B.toSet := by
    rw [BoundedInterval.coe_of_box]
    ext x
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · intro hx
      exact ⟨EuclideanSpace'.equiv_Real x, hx, EuclideanSpace'.equiv_Real.symm_apply_apply x⟩
    · rintro ⟨y, hy, hxy⟩
      have hyx : EuclideanSpace'.equiv_Real x = y := by
        rw [← hxy]
        exact EuclideanSpace'.equiv_Real.apply_symm_apply y
      rw [hyx]
      simpa using hy
  have hvol : |B|ᵥ = a := by
    rw [Box.volume_of_interval]
    simp [BoundedInterval.length, ha]
  have h_elem : IsElementary B.toSet := IsElementary.box B
  rw [Lebesgue_measure, hset]
  calc
    Lebesgue_outer_measure B.toSet = ↑h_elem.measure :=
      Lebesgue_outer_measure.elementary B.toSet h_elem
    _ = (a : EReal) := by
      have hmeas : h_elem.measure = a := by
        calc
          h_elem.measure = ∑ B' ∈ ({B} : Finset (Box 1)), |B'|ᵥ :=
            h_elem.measure_eq (by simp) (by simp)
          _ = |B|ᵥ := by simp
          _ = a := hvol
      exact_mod_cast hmeas

/-- f(x) = 1/x^2 on (0,1), 0 elsewhere: finite everywhere with infinite lower integral. -/
noncomputable def f_inv_sq : EuclideanSpace' 1 → EReal :=
  fun x => if (0 : ℝ) < EuclideanSpace'.equiv_Real x ∧ EuclideanSpace'.equiv_Real x < 1 then
    ((1 : ℝ) / (EuclideanSpace'.equiv_Real x) ^ 2 : ℝ) else 0

/-- f is nonnegative. -/
lemma f_inv_sq_nonneg : Unsigned f_inv_sq := by
  intro x
  unfold f_inv_sq
  by_cases hx : (0 : ℝ) < EuclideanSpace'.equiv_Real x ∧ EuclideanSpace'.equiv_Real x < 1
  · rw [if_pos hx]
    exact EReal.coe_nonneg.mpr (div_nonneg zero_le_one (sq_nonneg _))
  · rw [if_neg hx]

/-- f is finite everywhere. -/
lemma f_inv_sq_finite : ∀ x : EuclideanSpace' 1, f_inv_sq x < ⊤ := by
  intro x
  unfold f_inv_sq
  by_cases hx : (0 : ℝ) < EuclideanSpace'.equiv_Real x ∧ EuclideanSpace'.equiv_Real x < 1
  · rw [if_pos hx]
    exact EReal.coe_lt_top _
  · rw [if_neg hx]
    exact EReal.coe_lt_top (0 : ℝ)

/-- The preimage of (0,b) under the coordinate projection is the box with side (0,b). -/
lemma Ioo_preimage_eq_box (b : ℝ) :
    EuclideanSpace'.equiv_Real ⁻¹' Set.Ioo (0 : ℝ) b = (BoundedInterval.Ioo (0 : ℝ) b : Box 1).toSet := by
  rw [BoundedInterval.coe_of_box]
  ext x
  simp only [Set.mem_preimage, Set.mem_image]
  constructor
  · intro hx
    exact ⟨EuclideanSpace'.equiv_Real x, hx, EuclideanSpace'.equiv_Real.symm_apply_apply x⟩
  · rintro ⟨y, hy, hxy⟩
    have hyx : EuclideanSpace'.equiv_Real x = y := by
      rw [← hxy]
      exact EuclideanSpace'.equiv_Real.apply_symm_apply y
    rw [hyx]
    simpa using hy

/-- The preimage of (0,b) under the coordinate projection is Lebesgue measurable. -/
lemma measurable_Ioo_preimage (b : ℝ) :
    LebesgueMeasurable (EuclideanSpace'.equiv_Real ⁻¹' Set.Ioo (0 : ℝ) b) := by
  rw [Ioo_preimage_eq_box]
  exact Jordan_measurable.lebesgue (IsElementary.jordanMeasurable (IsElementary.box _))

/-- For u > 0 and r > 0: 1/u^2 > r iff u < sqrt(1/r). -/
lemma sq_inv_gt_iff {r : ℝ} (hr : 0 < r) {u : ℝ} (hu : 0 < u) :
    (r : EReal) < ((1 / u ^ 2 : ℝ) : EReal) ↔ u < Real.sqrt (1 / r) := by
  rw [EReal.coe_lt_coe_iff]
  rw [lt_div_iff₀ (sq_pos_of_pos hu)]
  rw [mul_comm]
  rw [← lt_div_iff₀ hr]
  exact (Real.lt_sqrt (le_of_lt hu)).symm

/-- f is unsigned measurable, via TFAE level sets. -/
lemma f_inv_sq_measurable : UnsignedMeasurable f_inv_sq := by
  have h5 : ∀ t : EReal, LebesgueMeasurable {x | f_inv_sq x > t} := by
    intro t
    by_cases ht : t = ⊤
    · have hset : {x | f_inv_sq x > t} = (∅ : Set (EuclideanSpace' 1)) := by
        ext x
        rw [ht]
        constructor
        · intro h
          change f_inv_sq x > ⊤ at h
          exact (not_lt_of_ge le_top) (gt_iff_lt.mp h)
        · intro h
          simp at h
      rw [hset]
      exact (isOpen_empty.measurable : LebesgueMeasurable (∅ : Set (EuclideanSpace' 1)))
    · cases t with
      | bot =>
          have hset : {x | f_inv_sq x > (⊥ : EReal)} = (Set.univ : Set (EuclideanSpace' 1)) := by
            ext x
            simp only [gt_iff_lt, Set.mem_univ, iff_true]
            exact lt_of_lt_of_le (EReal.bot_lt_coe (0 : ℝ)) (f_inv_sq_nonneg x)
          rw [hset]
          exact isOpen_univ.measurable
      | coe r =>
          by_cases hr : r < 0
          · have hset : {x | f_inv_sq x > (r : EReal)} = (Set.univ : Set (EuclideanSpace' 1)) := by
              ext x
              simp only [gt_iff_lt, Set.mem_univ, iff_true]
              exact lt_of_lt_of_le (EReal.coe_lt_coe_iff.mpr hr) (f_inv_sq_nonneg x)
            rw [hset]
            exact isOpen_univ.measurable
          · have hr0 : 0 ≤ r := le_of_not_gt hr
            by_cases hrz : r = 0
            · have hset : {x | f_inv_sq x > (r : EReal)} = EuclideanSpace'.equiv_Real ⁻¹' Set.Ioo (0 : ℝ) 1 := by
                ext x
                rw [hrz]
                simp only [gt_iff_lt, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ioo]
                unfold f_inv_sq
                by_cases hx : (0 : ℝ) < EuclideanSpace'.equiv_Real x ∧ EuclideanSpace'.equiv_Real x < 1
                · rw [if_pos hx]
                  constructor
                  · intro _
                    exact hx
                  · intro _
                    exact EReal.coe_lt_coe_iff.mpr (div_pos zero_lt_one (sq_pos_of_pos hx.1))
                · rw [if_neg hx]
                  constructor
                  · intro h
                    exact False.elim (lt_irrefl (0 : EReal) h)
                  · intro h
                    exact False.elim (hx h)
              rw [hset]
              exact measurable_Ioo_preimage 1
            · have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hrz)
              let c : ℝ := min 1 (Real.sqrt (1 / r))
              have hset : {x | f_inv_sq x > (r : EReal)} = EuclideanSpace'.equiv_Real ⁻¹' Set.Ioo (0 : ℝ) c := by
                ext x
                simp only [gt_iff_lt, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ioo]
                unfold f_inv_sq
                by_cases hx : (0 : ℝ) < EuclideanSpace'.equiv_Real x ∧ EuclideanSpace'.equiv_Real x < 1
                · rw [if_pos hx]
                  rw [sq_inv_gt_iff hrpos hx.1]
                  constructor
                  · intro h
                    exact ⟨hx.1, lt_min hx.2 h⟩
                  · intro h
                    exact lt_of_lt_of_le h.2 (min_le_right 1 (Real.sqrt (1 / r)))
                · rw [if_neg hx]
                  constructor
                  · intro h
                    exact False.elim (not_lt_of_ge (EReal.coe_le_coe_iff.mpr hrpos.le) h)
                  · intro h
                    exact False.elim (hx ⟨h.1, lt_of_lt_of_le h.2 (min_le_left 1 (Real.sqrt (1 / r)))⟩)
              rw [hset]
              exact measurable_Ioo_preimage c
      | top =>
          exact False.elim (ht rfl)
  exact ((UnsignedMeasurable.TFAE f_inv_sq_nonneg).out 4 0
    (a := ∀ t : EReal, LebesgueMeasurable {x | f_inv_sq x > t})
    (b := UnsignedMeasurable f_inv_sq)).mp h5

/-- The lower integral of f is top: for each M the simple function M^2 times the
    indicator of (0,1/M) lies below f and has integral M. -/
lemma f_inv_sq_integral : LowerUnsignedLebesgueIntegral f_inv_sq = ⊤ := by
  have hL_ge : ∀ M : ℕ, 1 ≤ M → ((M : ℝ) : EReal) ≤ LowerUnsignedLebesgueIntegral f_inv_sq := by
    intro M hM
    let a_M : ℝ := (M : ℝ)⁻¹
    let E : Set (EuclideanSpace' 1) := EuclideanSpace'.equiv_Real ⁻¹' Set.Ioo (0 : ℝ) a_M
    let g : EuclideanSpace' 1 → EReal :=
      fun x => (((M : ℝ) ^ 2 : ℝ) : EReal) * (Real.toEReal ∘ E.indicator') x
    have haM : 0 ≤ a_M := inv_nonneg.mpr (by exact_mod_cast (Nat.zero_le M))
    have hE_meas : LebesgueMeasurable E := by
      dsimp [E]
      exact measurable_Ioo_preimage a_M
    have hg_simple : UnsignedSimpleFunction g := by
      refine ⟨1, fun _ : Fin 1 => (((M : ℝ) ^ 2 : ℝ) : EReal), fun _ : Fin 1 => E, ?_, ?_⟩
      · intro i
        constructor
        · simpa using hE_meas
        · exact EReal.coe_nonneg.mpr (sq_nonneg _)
      · ext x
        simp [g, smul_eq_mul, EReal.indicator, Real.EReal_fun]
    have hg_le : ∀ x, g x ≤ f_inv_sq x := by
      intro x
      by_cases hx : EuclideanSpace'.equiv_Real x ∈ Set.Ioo (0 : ℝ) a_M
      · have hx1 : 0 < EuclideanSpace'.equiv_Real x := (Set.mem_Ioo.mp hx).1
        have hx2 : EuclideanSpace'.equiv_Real x < a_M := (Set.mem_Ioo.mp hx).2
        have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
        have hMpos : 0 < (M : ℝ) := lt_of_lt_of_le zero_lt_one hM1
        have haM_le_one : a_M ≤ 1 := by
          dsimp [a_M]
          exact inv_le_one_of_one_le₀ hM1
        have hx3 : EuclideanSpace'.equiv_Real x < 1 := lt_of_lt_of_le hx2 haM_le_one
        have hf_x : f_inv_sq x = (((1 : ℝ) / (EuclideanSpace'.equiv_Real x) ^ 2 : ℝ) : EReal) := by
          unfold f_inv_sq
          rw [if_pos ⟨hx1, hx3⟩]
        have hg_x : g x = (((M : ℝ) ^ 2 : ℝ) : EReal) := by
          have hgx : g x = (((M : ℝ) ^ 2 : ℝ) : EReal) * EReal.indicator E x := by
            dsimp [g]
            simp [EReal.indicator, Real.EReal_fun]
          rw [hgx]
          change (((M : ℝ) ^ 2 : ℝ) : EReal) *
            EReal.indicator (EuclideanSpace'.equiv_Real ⁻¹' Set.Ioo (0 : ℝ) a_M) x = (((M : ℝ) ^ 2 : ℝ) : EReal)
          have hx' : x ∈ EuclideanSpace'.equiv_Real ⁻¹' Set.Ioo (0 : ℝ) a_M := hx
          rw [EReal.indicator_of_mem hx', mul_one]
        have hMx : (M : ℝ) * EuclideanSpace'.equiv_Real x < 1 := by
          have h' : (M : ℝ) * EuclideanSpace'.equiv_Real x < (M : ℝ) * ((M : ℝ)⁻¹) :=
            mul_lt_mul_of_pos_left hx2 hMpos
          rwa [mul_inv_cancel₀ (ne_of_gt hMpos)] at h'
        have hsq : (M : ℝ) ^ 2 * (EuclideanSpace'.equiv_Real x) ^ 2 < 1 := by
          nlinarith [hMx, mul_pos hMpos hx1]
        have hM2_lt : (M : ℝ) ^ 2 < (1 : ℝ) / (EuclideanSpace'.equiv_Real x) ^ 2 :=
          (lt_div_iff₀ (sq_pos_of_pos hx1)).mpr hsq
        rw [hg_x, hf_x]
        exact EReal.coe_le_coe_iff.mpr (le_of_lt hM2_lt)
      · have hg_x : g x = 0 := by
          have hgx : g x = (((M : ℝ) ^ 2 : ℝ) : EReal) * EReal.indicator E x := by
            dsimp [g]
            simp [EReal.indicator, Real.EReal_fun]
          rw [hgx]
          change (((M : ℝ) ^ 2 : ℝ) : EReal) *
            EReal.indicator (EuclideanSpace'.equiv_Real ⁻¹' Set.Ioo (0 : ℝ) a_M) x = (0 : EReal)
          have hx' : x ∉ EuclideanSpace'.equiv_Real ⁻¹' Set.Ioo (0 : ℝ) a_M := hx
          rw [EReal.indicator_of_notMem hx', mul_zero]
        rw [hg_x]
        exact f_inv_sq_nonneg x
    have hL_eq : LowerUnsignedLebesgueIntegral g = (((M : ℝ) ^ 2 : ℝ) : EReal) * Lebesgue_measure E :=
      lowerIntegral_const_indicator (d := 1) (c := (M : ℝ) ^ 2) (sq_nonneg _) hE_meas
    have hinteg_le : LowerUnsignedLebesgueIntegral g ≤ LowerUnsignedLebesgueIntegral f_inv_sq := by
      rw [LowerUnsignedLebesgueIntegral.eq_simpleIntegral hg_simple]
      unfold LowerUnsignedLebesgueIntegral
      exact le_sSup ⟨g, hg_simple, fun x => ⟨hg_le x, rfl⟩⟩
    have hE_measure : Lebesgue_measure E = (a_M : EReal) := by
      dsimp [E]
      exact measure_Ioo_zero haM
    have hMne : (M : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one hM))
    calc
      ((M : ℝ) : EReal) = (((M : ℝ) ^ 2 : ℝ) : EReal) * (a_M : EReal) := by
        rw [← EReal.coe_mul]
        congr 1
        dsimp [a_M]
        rw [pow_two, mul_assoc, mul_inv_cancel₀ hMne, mul_one]
      _ = (((M : ℝ) ^ 2 : ℝ) : EReal) * Lebesgue_measure E := by rw [hE_measure]
      _ = LowerUnsignedLebesgueIntegral g := hL_eq.symm
      _ ≤ LowerUnsignedLebesgueIntegral f_inv_sq := hinteg_le
  have hL_all : ∀ r : ℝ, (r : EReal) < LowerUnsignedLebesgueIntegral f_inv_sq := by
    intro r
    by_cases hr : r < 0
    · have h0 : (0 : EReal) ≤ LowerUnsignedLebesgueIntegral f_inv_sq :=
        le_trans (by norm_num : (0 : EReal) ≤ ((1 : ℕ) : EReal)) (hL_ge 1 (by norm_num))
      exact lt_of_lt_of_le (EReal.coe_lt_coe_iff.mpr hr) h0
    · rcases exists_nat_gt r with ⟨M, hM⟩
      have hM1 : 1 ≤ M := by
        have hMpos : 0 < (M : ℝ) := lt_of_le_of_lt (le_of_not_gt hr) hM
        exact_mod_cast hMpos
      exact lt_of_lt_of_le (EReal.coe_lt_coe_iff.mpr hM) (hL_ge M hM1)
  apply le_antisymm le_top
  cases hc : LowerUnsignedLebesgueIntegral f_inv_sq with
  | bot =>
      have hbad : (0 : EReal) < (⊥ : EReal) := by simpa [hc] using hL_all 0
      exact False.elim ((not_lt_of_ge bot_le) hbad)
  | coe r =>
      have hbad : ((r + 1 : ℝ) : EReal) < (r : EReal) := by simpa [hc] using hL_all (r + 1)
      have hge : (r : EReal) ≤ ((r + 1 : ℝ) : EReal) := by
        rw [EReal.coe_le_coe_iff]
        linarith
      exact False.elim ((not_lt_of_ge hge) hbad)
  | top => rfl

theorem UnsignedLebesgueIntegral.ae_finite_no_converse : ∃ (d:ℕ) (f: EuclideanSpace' d → EReal) (_hf: UnsignedMeasurable f) (_hfin: AlmostAlways (fun x ↦ f x < ⊤)), UnsignedLebesgueIntegral f = ⊤ := by
  refine ⟨1, f_inv_sq, f_inv_sq_measurable, AlmostAlways.ofAlways f_inv_sq_finite, ?_⟩
  change LowerUnsignedLebesgueIntegral f_inv_sq = ⊤
  exact f_inv_sq_integral

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
