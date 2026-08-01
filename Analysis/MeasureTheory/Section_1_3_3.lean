import Analysis.MeasureTheory.Section_1_3_2

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

/-- Exercise 1.3.10(vii) (Divisibility) -/
theorem LowerUnsignedLebesgueIntegral.eq_add {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) {E: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) :
    LowerUnsignedLebesgueIntegral f = LowerUnsignedLebesgueIntegral (f * Real.toEReal ∘ E.indicator') +
      LowerUnsignedLebesgueIntegral (f * Real.toEReal ∘ Eᶜ.indicator') := by sorry

/-- Exercise 1.3.10(viii) (Vertical truncation). -/
theorem LowerUnsignedLebesgueIntegral.eq_lim_vert_trunc {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) : Filter.atTop.Tendsto (fun n:ℕ ↦ LowerUnsignedLebesgueIntegral (fun x ↦ min (f x) n)) (nhds (LowerUnsignedLebesgueIntegral f)) := by sorry

def UpperUnsignedLebesgueIntegral.eq_lim_vert_trunc : Decidable (∀ (d:ℕ) (f: EuclideanSpace' d → EReal) (hf: UnsignedMeasurable f), Filter.atTop.Tendsto (fun n:ℕ ↦ UpperUnsignedLebesgueIntegral (fun x ↦ min (f x) n)) (nhds (UpperUnsignedLebesgueIntegral f))) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  sorry

/-- Exercise 1.3.10(ix) (Horizontal truncation). -/
theorem LowerUnsignedLebesgueIntegral.eq_lim_horiz_trunc {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) : Filter.atTop.Tendsto (fun n:ℕ ↦ LowerUnsignedLebesgueIntegral (f * Real.toEReal ∘ (Metric.ball 0 n).indicator')) (nhds (LowerUnsignedLebesgueIntegral f)) := by sorry

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

/-- Exercise 1.3.11 -/
theorem LowerUnsignedLebesgueIntegral.eq_upperIntegral {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) (hbound: EReal.BoundedFunction f) (hsupp: FiniteMeasureSupport f) :
    LowerUnsignedLebesgueIntegral f = UpperUnsignedLebesgueIntegral f := by sorry

def LowerUnsignedLebesgueIntegral.eq_upperIntegral_unbounded : Decidable (∀ (d:ℕ) (f: EuclideanSpace' d → EReal) (hf: UnsignedMeasurable f) (hsupp: FiniteMeasureSupport f), LowerUnsignedLebesgueIntegral f = UpperUnsignedLebesgueIntegral f) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  sorry

def LowerUnsignedLebesgueIntegral.eq_upperIntegral_infinite_supp : Decidable (∀ (d:ℕ) (f: EuclideanSpace' d → EReal) (hf: UnsignedMeasurable f) (hbound: EReal.BoundedFunction f), LowerUnsignedLebesgueIntegral f = UpperUnsignedLebesgueIntegral f) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  sorry

/-- Multiplying an unsigned measurable function by a ball indicator preserves measurability.
    This is a key helper for the horizontal truncation argument in Corollary 1.3.14. -/
lemma UnsignedMeasurable.mul_indicator_ball {d : ℕ} {f : EuclideanSpace' d → EReal}
    (hf : UnsignedMeasurable f) (n : ℕ) :
    UnsignedMeasurable (f * Real.toEReal ∘ (Metric.ball (0 : EuclideanSpace' d) n).indicator') := by
  -- The indicator of a ball is measurable (balls are open, hence measurable)
  -- Multiplication of measurable functions is measurable
  -- The product of nonnegative functions is nonnegative
  constructor
  · -- Unsigned: f x * ind x ≥ 0 since f x ≥ 0 and ind x ∈ {0, 1}
    intro x
    simp only [Pi.mul_apply, Function.comp_apply]
    apply mul_nonneg (hf.1 x)
    by_cases hx : x ∈ Metric.ball (0 : EuclideanSpace' d) n
    · simp [Set.indicator'_of_mem hx]
    · simp [Set.indicator'_of_notMem hx]
  · -- Measurable: follows from closure of measurable functions under multiplication
    -- and measurability of indicator functions
    sorry

/-- Helper: horizontal truncation produces functions with finite measure support. -/
lemma FiniteMeasureSupport.mul_indicator_ball {d : ℕ} {f : EuclideanSpace' d → EReal}
    (n : ℕ) : FiniteMeasureSupport (f * Real.toEReal ∘ (Metric.ball (0 : EuclideanSpace' d) n).indicator') := by
  -- Support of f * ind is contained in ball 0 n, which has finite Lebesgue measure
  -- The key facts are:
  -- 1. If x ∉ ball 0 n, then ind x = 0, so f x * ind x = 0
  -- 2. So support ⊆ ball 0 n
  -- 3. Balls have finite Lebesgue measure
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

/-- Lemma 1.3.15 (Markov's inequality) -/
theorem UnsignedLebesgueIntegral.markov_inequality {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) {t:ℝ} (ht: 0 < t) :
    Lebesgue_measure { x | f x ≥ t } ≤ hf.integ / (t:EReal) := by
  sorry

/-- Exercise 1.3.18 (ii) -/
theorem UnsignedLebesgueIntegral.ae_finite {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) (hfin: UnsignedLebesgueIntegral f < ⊤) :
    AlmostAlways (fun x ↦ f x < ⊤) := by sorry

theorem UnsignedLebesgueIntegral.ae_finite_no_converse : ∃ (d:ℕ) (f: EuclideanSpace' d → EReal) (hf: UnsignedMeasurable f) (hfin: AlmostAlways (fun x ↦ f x < ⊤)), UnsignedLebesgueIntegral f = ⊤ := by sorry

/-- Exercise 1.3.18 (iii) -/
theorem UnsignedLebesgueIntegral.eq_zero_aeZero {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) :
     hf.integ = 0 ↔ AlmostAlways (fun x ↦ f x = 0) := by sorry
