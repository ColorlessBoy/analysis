import Analysis.MeasureTheory.Section_1_3_4
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.SpecificLimits.Normed

open Filter
open scoped Topology

/-!
# Introduction to Measure Theory, Section 1.3.5: Littlewood's three principles

A companion to (the introduction to) Section 1.3.5 of the book "An introduction to Measure Theory".

-/

/-- Helper: extract a simple function approximation from the sSup definition of the unsigned integral.
  Given an unsigned absolutely integrable f and ε > 0, there exists a simple g ≤ f pointwise
  whose integral is within ε of the integral of f. -/
private lemma unsigned_approx_from_sup {d:ℕ} {f: EuclideanSpace' d → EReal}
    (hf : UnsignedAbsolutelyIntegrable f) (ε : ℝ) (hε : 0 < ε) :
    ∃ (g : EuclideanSpace' d → EReal) (hg : UnsignedSimpleFunction g),
      (∀ x, g x ≤ f x) ∧
      UnsignedLebesgueIntegral f ≤ hg.integ + ε := by
  set L := UnsignedLebesgueIntegral f with hL_def
  have hL_lt_top : L < ⊤ := hf.2
  have hL_ne_top : L ≠ ⊤ := ne_of_lt hL_lt_top
  have hL_nonneg : (0 : EReal) ≤ L := UnsignedLebesgueIntegral.nonneg hf.1
  have hL_ne_bot : L ≠ ⊥ :=
    ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero hL_nonneg)
  -- L - ε < L (since ε > 0 and L is finite)
  have hε_ne_bot : (ε : EReal) ≠ ⊥ := EReal.coe_ne_bot ε
  have hε_ne_top : (ε : EReal) ≠ ⊤ := EReal.coe_ne_top ε
  have hL_sub_lt : L - (ε : EReal) < L := by
    rw [EReal.sub_lt_iff (Or.inl hε_ne_bot) (Or.inl hε_ne_top)]
    calc L = 0 + L := (zero_add L).symm
      _ < (ε : EReal) + L := EReal.add_lt_add_of_lt_of_le
          (EReal.coe_pos.mpr hε) le_rfl hL_ne_bot hL_ne_top
      _ = L + (ε : EReal) := add_comm _ _
  -- Extract R from the sSup definition with R > L - ε
  -- L = sSup S by definition (after unfolding)
  have hR_exists : ∃ R ∈ { R : EReal | ∃ g : EuclideanSpace' d → EReal,
      ∃ hg : UnsignedSimpleFunction g, ∀ x, g x ≤ f x ∧ R = hg.integ },
      L - (ε : EReal) < R := by
    by_contra h_all
    push_neg at h_all
    have h_le : L ≤ L - (ε : EReal) := by
      conv_lhs => rw [hL_def, UnsignedLebesgueIntegral, LowerUnsignedLebesgueIntegral]
      exact sSup_le fun R hR => h_all R hR
    exact absurd h_le (not_le.mpr hL_sub_lt)
  obtain ⟨R, hR_mem, hR_gt⟩ := hR_exists
  obtain ⟨g, hg, hcond⟩ := hR_mem
  have hg_le : ∀ x, g x ≤ f x := fun x => (hcond x).1
  have hR_eq : R = hg.integ := (hcond (0 : EuclideanSpace' d)).2
  refine ⟨g, hg, hg_le, ?_⟩
  rw [hR_eq] at hR_gt
  exact le_of_lt ((EReal.sub_lt_iff (Or.inl hε_ne_bot)
      (Or.inl hε_ne_top)).mp hR_gt)

/-- Helper: convert an unsigned simple function with finite values to a real simple function. -/
private lemma UnsignedSimpleFunction.toRealSimple {d:ℕ} {g: EuclideanSpace' d → EReal}
    (hg: UnsignedSimpleFunction g) (hfin: ∀ x, g x ≠ ⊤) :
    ∃ (h : EuclideanSpace' d → ℝ), RealSimpleFunction h ∧
      (∀ x, 0 ≤ h x) ∧ (∀ x, (h x : EReal) = g x) := by
  -- Unpack: g = ∑ i, c_i • indicator(E_i) with c_i ≥ 0, E_i measurable
  obtain ⟨k, c, E, hcond, heq⟩ := hg
  -- Define h = ∑ i, c_i.toReal • indicator'(E_i) as a real function
  set c' : Fin k → ℝ := fun i => (c i).toReal with hc'_def
  set h : EuclideanSpace' d → ℝ := fun x => ∑ i, c' i * (E i).indicator' x with hh_def
  refine ⟨h, ?_, ?_, ?_⟩
  · -- RealSimpleFunction h
    exact ⟨k, c', E, fun i => (hcond i).1, by ext x; simp [hh_def, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]⟩
  · -- h x ≥ 0 for all x
    intro x; simp only [hh_def]
    apply Finset.sum_nonneg; intro i _
    apply mul_nonneg
    · -- c'_i ≥ 0
      simp only [hc'_def]
      exact EReal.toReal_nonneg (hcond i).2
    · -- indicator' ≥ 0
      by_cases hx : x ∈ E i
      · simp [Set.indicator'_of_mem hx]
      · simp [Set.indicator'_of_notMem hx]
  · -- (h x : EReal) = g x
    intro x
    simp only [hh_def, heq, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    -- Show term-by-term that the real sum cast to EReal = the EReal sum
    -- First, prove the casting lemma for sums
    have hcoe_sum : ∀ (n : ℕ) (a : Fin n → ℝ),
        (↑(∑ i, a i) : EReal) = ∑ i, (↑(a i) : EReal) := by
      intro n a; induction n with
      | zero => simp [Finset.univ_eq_empty]
      | succ m ih =>
        rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, EReal.coe_add]
        congr 1; exact ih (fun i => a i.castSucc)
    rw [hcoe_sum]
    congr 1; ext i
    -- Need: (c'_i * indicator'(E_i)(x) : EReal) = c_i * EReal.indicator(E_i)(x)
    by_cases hx : x ∈ E i
    · -- x ∈ E i: both sides equal c_i (resp. c_i.toReal cast)
      simp only [hc'_def, Set.indicator', Set.indicator_of_mem hx, mul_one,
        EReal.indicator, Real.EReal_fun]
      -- Goal: ((c i).toReal : EReal) = c i
      have hci_ne_bot : c i ≠ ⊥ :=
        ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (hcond i).2)
      have hci_ne_top : c i ≠ ⊤ := by
        intro hci_top
        apply hfin x
        rw [heq]; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        apply eq_top_iff.mpr
        have htop : c i * EReal.indicator (E i) x = ⊤ := by
          simp [hci_top, EReal.indicator, Real.EReal_fun, Set.indicator', Set.indicator_of_mem hx]
        calc ⊤ = c i * EReal.indicator (E i) x := htop.symm
          _ ≤ ∑ j, c j * EReal.indicator (E j) x :=
            Finset.single_le_sum (f := fun j => c j * EReal.indicator (E j) x)
              (fun j _ => mul_nonneg (hcond j).2 (by
                simp only [EReal.indicator, Real.EReal_fun]
                by_cases hxj : x ∈ E j
                · simp [Set.indicator'_of_mem hxj]
                · simp [Set.indicator'_of_notMem hxj])) (Finset.mem_univ i)
      rw [show (1 : ℝ).toEReal = (1 : EReal) from rfl, mul_one]
      exact EReal.coe_toReal hci_ne_top hci_ne_bot
    · -- x ∉ E i: both sides are 0
      simp only [Set.indicator'_of_notMem hx, mul_zero, EReal.coe_zero,
        EReal.indicator, Real.EReal_fun, MulZeroClass.mul_zero]

/-- Theorem 1.3.20(i) Approximation of $L^1$ functions by simple functions (real case) -/
theorem RealAbsolutelyIntegrable.approx_by_simple {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf : RealAbsolutelyIntegrable f)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (g : EuclideanSpace' d → ℝ), RealSimpleFunction g ∧ RealAbsolutelyIntegrable g ∧
    PreL1.norm (f - g) ≤ ε := by
  -- Step 1: Get approximations for positive and negative parts
  have hε2 : 0 < ε / 2 := half_pos hε
  have hf_pos := hf.pos  -- UnsignedAbsolutelyIntegrable (EReal.pos_fun f)
  have hf_neg := hf.neg  -- UnsignedAbsolutelyIntegrable (EReal.neg_fun f)
  obtain ⟨g_pos, hg_pos, hg_pos_le, hg_pos_bound⟩ := unsigned_approx_from_sup hf_pos (ε / 2) hε2
  obtain ⟨g_neg, hg_neg, hg_neg_le, hg_neg_bound⟩ := unsigned_approx_from_sup hf_neg (ε / 2) hε2
  -- Step 2: Convert to real simple functions
  have hg_pos_fin : ∀ x, g_pos x ≠ ⊤ := fun x =>
    ne_of_lt (lt_of_le_of_lt (hg_pos_le x) (by
      simp only [EReal.pos_fun]; exact EReal.coe_lt_top _))
  have hg_neg_fin : ∀ x, g_neg x ≠ ⊤ := fun x =>
    ne_of_lt (lt_of_le_of_lt (hg_neg_le x) (by
      simp only [EReal.neg_fun]; exact EReal.coe_lt_top _))
  obtain ⟨h_pos, hh_pos_simple, hh_pos_nonneg, hh_pos_eq⟩ :=
    UnsignedSimpleFunction.toRealSimple hg_pos hg_pos_fin
  obtain ⟨h_neg, hh_neg_simple, hh_neg_nonneg, hh_neg_eq⟩ :=
    UnsignedSimpleFunction.toRealSimple hg_neg hg_neg_fin
  -- Step 3: Define g = h_pos - h_neg
  set g : EuclideanSpace' d → ℝ := h_pos - h_neg with hg_def
  have hg_simple : RealSimpleFunction g := by
    rw [show g = h_pos + (-1 : ℝ) • h_neg from by ext x; simp [hg_def, sub_eq_add_neg]]
    exact RealSimpleFunction.add hh_pos_simple (RealSimpleFunction.smul hh_neg_simple (-1))
  -- Step 4: Show h_pos and h_neg are absolutely integrable
  have habs_fun_eq_pos : EReal.abs_fun h_pos = g_pos := by
    ext x; simp only [EReal.abs_fun, Real.norm_eq_abs, abs_of_nonneg (hh_pos_nonneg x)]
    exact hh_pos_eq x
  have habs_fun_eq_neg : EReal.abs_fun h_neg = g_neg := by
    ext x; simp only [EReal.abs_fun, Real.norm_eq_abs, abs_of_nonneg (hh_neg_nonneg x)]
    exact hh_neg_eq x
  have hh_pos_ai : RealAbsolutelyIntegrable h_pos := by
    constructor
    · exact ⟨fun _ => h_pos, fun _ => hh_pos_simple, fun _ => tendsto_const_nhds⟩
    · rw [UnsignedLebesgueIntegral, habs_fun_eq_pos,
          LowerUnsignedLebesgueIntegral.eq_simpleIntegral hg_pos]
      calc hg_pos.integ ≤ UnsignedLebesgueIntegral (EReal.pos_fun f) := by
            rw [UnsignedLebesgueIntegral, LowerUnsignedLebesgueIntegral]
            exact le_sSup ⟨g_pos, hg_pos, fun x => ⟨hg_pos_le x, rfl⟩⟩
        _ < ⊤ := hf_pos.2
  have hh_neg_ai : RealAbsolutelyIntegrable h_neg := by
    constructor
    · exact ⟨fun _ => h_neg, fun _ => hh_neg_simple, fun _ => tendsto_const_nhds⟩
    · rw [UnsignedLebesgueIntegral, habs_fun_eq_neg,
          LowerUnsignedLebesgueIntegral.eq_simpleIntegral hg_neg]
      calc hg_neg.integ ≤ UnsignedLebesgueIntegral (EReal.neg_fun f) := by
            rw [UnsignedLebesgueIntegral, LowerUnsignedLebesgueIntegral]
            exact le_sSup ⟨g_neg, hg_neg, fun x => ⟨hg_neg_le x, rfl⟩⟩
        _ < ⊤ := hf_neg.2
  have hg_ai : RealAbsolutelyIntegrable g := by
    rw [hg_def]; exact RealAbsolutelyIntegrable.sub hh_pos_ai hh_neg_ai
  -- Step 5: Show the norm bound PreL1.norm (f - g) ≤ ε
  refine ⟨g, hg_simple, hg_ai, ?_⟩
  show UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) ≤ (ε : EReal)
  -- Auxiliary: h_pos, h_neg bounded by max(f,0), max(-f,0)
  have h_pos_le : ∀ x, h_pos x ≤ max (f x) 0 := fun x =>
    EReal.coe_le_coe_iff.mp (le_trans (le_of_eq (hh_pos_eq x)) (hg_pos_le x))
  have h_neg_le : ∀ x, h_neg x ≤ max (-(f x)) 0 := fun x =>
    EReal.coe_le_coe_iff.mp (le_trans (le_of_eq (hh_neg_eq x)) (hg_neg_le x))
  -- Pointwise bound: ‖(f - g) x‖ + h_pos x + h_neg x ≤ ‖f x‖
  have h_pw : ∀ x, ‖(f - g) x‖ + h_pos x + h_neg x ≤ ‖f x‖ := by
    intro x
    simp only [hg_def, Pi.sub_apply, Real.norm_eq_abs]
    rcases le_or_gt 0 (f x) with hfx | hfx
    · -- f x ≥ 0: max(-f x, 0) = 0, so h_neg x = 0
      have hb0 : h_neg x = 0 :=
        le_antisymm (by linarith [h_neg_le x, max_eq_right (neg_nonpos.mpr hfx)])
          (hh_neg_nonneg x)
      have ha_le_fx : h_pos x ≤ f x := by
        have := h_pos_le x; rwa [max_eq_left hfx] at this
      rw [hb0]; simp only [sub_zero, add_zero]
      rw [abs_of_nonneg hfx, abs_of_nonneg (sub_nonneg.mpr ha_le_fx)]
      linarith
    · -- f x < 0: max(f x, 0) = 0, so h_pos x = 0
      have ha0 : h_pos x = 0 :=
        le_antisymm (by linarith [h_pos_le x, max_eq_right (le_of_lt hfx)])
          (hh_pos_nonneg x)
      have hb_le_neg : h_neg x ≤ -(f x) := by
        have := h_neg_le x; rwa [max_eq_left (neg_nonneg.mpr (le_of_lt hfx))] at this
      rw [ha0]; simp only [zero_sub, add_zero]
      rw [abs_of_neg hfx, show f x - -h_neg x = f x + h_neg x from by ring,
          abs_of_nonpos (by linarith)]
      linarith
  -- Convert to EReal: abs_fun(f-g)(x) + (g_pos + g_neg)(x) ≤ abs_fun(f)(x)
  have h_pw_e : ∀ x, (EReal.abs_fun (f - g) + (g_pos + g_neg)) x ≤ EReal.abs_fun f x := by
    intro x
    simp only [Pi.add_apply, EReal.abs_fun]
    rw [← hh_pos_eq x, ← hh_neg_eq x, ← EReal.coe_add, ← EReal.coe_add]
    exact EReal.coe_le_coe_iff.mpr (by linarith [h_pw x])
  -- Measurability
  have hm_gp : UnsignedMeasurable g_pos := hg_pos.unsignedMeasurable
  have hm_gn : UnsignedMeasurable g_neg := hg_neg.unsignedMeasurable
  have hm_gp_gn : UnsignedMeasurable (g_pos + g_neg) := hm_gp.add hm_gn
  have hm_abs_fg : UnsignedMeasurable (EReal.abs_fun (f - g)) :=
    (RealAbsolutelyIntegrable.abs _ (hf.sub hg_ai)).1
  have hm_abs_f : UnsignedMeasurable (EReal.abs_fun f) :=
    (RealAbsolutelyIntegrable.abs _ hf).1
  have hm_sum : UnsignedMeasurable (EReal.abs_fun (f - g) + (g_pos + g_neg)) :=
    hm_abs_fg.add hm_gp_gn
  -- Monotonicity: ∫(abs_fun(f-g) + (g_pos + g_neg)) ≤ ∫(abs_fun f)
  have h_mono : UnsignedLebesgueIntegral (EReal.abs_fun (f - g) + (g_pos + g_neg)) ≤
      UnsignedLebesgueIntegral (EReal.abs_fun f) :=
    LowerUnsignedLebesgueIntegral.mono hm_sum hm_abs_f (AlmostAlways.ofAlways h_pw_e)
  -- Additivity: ∫(abs_fun(f-g) + (g_pos + g_neg)) = ∫abs_fun(f-g) + ∫(g_pos + g_neg)
  have h_add_lhs : UnsignedLebesgueIntegral (EReal.abs_fun (f - g) + (g_pos + g_neg)) =
      UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) +
      UnsignedLebesgueIntegral (g_pos + g_neg) :=
    LowerUnsignedLebesgueIntegral.add hm_abs_fg hm_gp_gn hm_sum
  -- ∫(g_pos + g_neg) = ∫g_pos + ∫g_neg
  have h_add_gp_gn : UnsignedLebesgueIntegral (g_pos + g_neg) =
      UnsignedLebesgueIntegral g_pos + UnsignedLebesgueIntegral g_neg :=
    LowerUnsignedLebesgueIntegral.add hm_gp hm_gn hm_gp_gn
  -- Simple integrals
  have h_gp_integ : UnsignedLebesgueIntegral g_pos = hg_pos.integ :=
    LowerUnsignedLebesgueIntegral.eq_simpleIntegral hg_pos
  have h_gn_integ : UnsignedLebesgueIntegral g_neg = hg_neg.integ :=
    LowerUnsignedLebesgueIntegral.eq_simpleIntegral hg_neg
  -- abs_fun f = pos_fun f + neg_fun f
  have h_abs_eq : EReal.abs_fun f = EReal.pos_fun f + EReal.neg_fun f := by
    ext x; simp only [EReal.abs_fun, EReal.pos_fun, EReal.neg_fun, Pi.add_apply,
      Real.norm_eq_abs]
    rw [show (↑|f x| : EReal) = ↑(max (f x) 0 + max (-(f x)) 0) from by
      congr 1; rcases le_or_gt 0 (f x) with hfx | hfx
      · simp [max_eq_left hfx, max_eq_right (neg_nonpos.mpr hfx), abs_of_nonneg hfx]
      · simp [max_eq_right (le_of_lt hfx), max_eq_left (neg_nonneg.mpr (le_of_lt hfx)),
              abs_of_neg hfx]]
    exact EReal.coe_add _ _
  have h_abs_add : UnsignedLebesgueIntegral (EReal.abs_fun f) =
      UnsignedLebesgueIntegral (EReal.pos_fun f) +
      UnsignedLebesgueIntegral (EReal.neg_fun f) := by
    rw [h_abs_eq]
    exact LowerUnsignedLebesgueIntegral.add hf_pos.1 hf_neg.1
      (by rw [← h_abs_eq]; exact hm_abs_f)
  -- Set C = ∫(g_pos + g_neg) = hg_pos.integ + hg_neg.integ
  set C := UnsignedLebesgueIntegral (g_pos + g_neg) with hC_def
  have hC_eq : C = hg_pos.integ + hg_neg.integ := by
    have := h_add_gp_gn; rw [h_gp_integ, h_gn_integ] at this; exact this
  have hC_lt_top : C < ⊤ := by
    rw [hC_eq]
    calc hg_pos.integ + hg_neg.integ
        ≤ UnsignedLebesgueIntegral (EReal.pos_fun f) +
          UnsignedLebesgueIntegral (EReal.neg_fun f) :=
          add_le_add
            (by rw [UnsignedLebesgueIntegral, LowerUnsignedLebesgueIntegral]
                exact le_sSup ⟨g_pos, hg_pos, fun x => ⟨hg_pos_le x, rfl⟩⟩)
            (by rw [UnsignedLebesgueIntegral, LowerUnsignedLebesgueIntegral]
                exact le_sSup ⟨g_neg, hg_neg, fun x => ⟨hg_neg_le x, rfl⟩⟩)
      _ = UnsignedLebesgueIntegral (EReal.abs_fun f) := h_abs_add.symm
      _ < ⊤ := hf.2
  have hC_ne_top : C ≠ ⊤ := ne_of_lt hC_lt_top
  have hC_nonneg : (0 : EReal) ≤ C := UnsignedLebesgueIntegral.nonneg hm_gp_gn
  have hC_ne_bot : C ≠ ⊥ := ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero hC_nonneg)
  -- Upper bound: ∫|f| ≤ C + ε
  have h_upper : UnsignedLebesgueIntegral (EReal.abs_fun f) ≤ C + (ε : EReal) := by
    rw [h_abs_add, hC_eq]
    calc UnsignedLebesgueIntegral (EReal.pos_fun f) +
          UnsignedLebesgueIntegral (EReal.neg_fun f)
        ≤ (hg_pos.integ + (ε / 2 : ℝ)) + (hg_neg.integ + (ε / 2 : ℝ)) :=
          add_le_add hg_pos_bound hg_neg_bound
      _ = hg_pos.integ + hg_neg.integ + (ε : EReal) := by
          rw [show (ε : EReal) = (↑(ε / 2) : EReal) + (↑(ε / 2) : EReal) from by
            rw [← EReal.coe_add]; congr 1; linarith]
          abel
  -- Lower bound from monotonicity + additivity
  have h_lower : UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) + C ≤
      UnsignedLebesgueIntegral (EReal.abs_fun f) := by
    calc UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) + C
        ≤ UnsignedLebesgueIntegral (EReal.abs_fun (f - g) + (g_pos + g_neg)) := by
          rw [h_add_lhs]
      _ ≤ UnsignedLebesgueIntegral (EReal.abs_fun f) := h_mono
  -- Combine and cancel C
  have h_combined : UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) + C ≤ C + (ε : EReal) :=
    le_trans h_lower h_upper
  have hC_real : C = (C.toReal : EReal) := (EReal.coe_toReal hC_ne_top hC_ne_bot).symm
  rw [hC_real] at h_combined
  rw [add_comm (↑C.toReal : EReal) (↑ε : EReal)] at h_combined
  exact (EReal.addLECancellable_coe C.toReal).add_le_add_iff_right.mp h_combined

/-- Theorem 1.3.20(i) Approximation of $L^1$ functions by simple functions (complex case) -/
theorem ComplexAbsolutelyIntegrable.approx_by_simple {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf : ComplexAbsolutelyIntegrable f)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (g : EuclideanSpace' d → ℂ), ComplexSimpleFunction g ∧ ComplexAbsolutelyIntegrable g ∧
    PreL1.norm (f - g) ≤ ε := by
  -- Approximate real and imaginary parts within ε/2
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨g_re, hg_re_simple, hg_re_ai, hg_re_norm⟩ :=
    (ComplexAbsolutelyIntegrable.re f hf).approx_by_simple (ε / 2) hε2
  obtain ⟨g_im, hg_im_simple, hg_im_ai, hg_im_norm⟩ :=
    (ComplexAbsolutelyIntegrable.im f hf).approx_by_simple (ε / 2) hε2
  -- Construct complex approximation g = ↑g_re + I • ↑g_im
  set g : EuclideanSpace' d → ℂ :=
    Real.complex_fun g_re + Complex.I • Real.complex_fun g_im with hg_def
  have hg_re_eq : Complex.re_fun g = g_re := by
    ext x; simp only [Complex.re_fun, hg_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Real.complex_fun, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im]; ring
  have hg_im_eq : Complex.im_fun g = g_im := by
    ext x; simp only [Complex.im_fun, hg_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Real.complex_fun, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re]; ring
  have hg_simple : ComplexSimpleFunction g :=
    ComplexSimpleFunction.add
      (RealSimpleFunction.toComplex g_re hg_re_simple)
      (ComplexSimpleFunction.smul (RealSimpleFunction.toComplex g_im hg_im_simple) Complex.I)
  have hg_ai : ComplexAbsolutelyIntegrable g := by
    apply (ComplexAbsolutelyIntegrable.iff g).mpr
    exact ⟨hg_re_eq ▸ hg_re_ai, hg_im_eq ▸ hg_im_ai⟩
  refine ⟨g, hg_simple, hg_ai, ?_⟩
  -- Norm bound: PreL1.norm (f - g) ≤ ε
  show UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) ≤ (ε : EReal)
  -- Re/Im of f - g
  have hfg_re : Complex.re_fun (f - g) = Complex.re_fun f - g_re := by
    ext x; simp only [Complex.re_fun, hg_def, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Real.complex_fun, Complex.sub_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im]; ring
  have hfg_im : Complex.im_fun (f - g) = Complex.im_fun f - g_im := by
    ext x; simp only [Complex.im_fun, hg_def, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Real.complex_fun, Complex.sub_im, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re]; ring
  -- Pointwise: |f-g| ≤ |Re(f-g)| + |Im(f-g)|
  have h_bound : ∀ x, EReal.abs_fun (f - g) x ≤
      (EReal.abs_fun (Complex.re_fun (f - g)) + EReal.abs_fun (Complex.im_fun (f - g))) x :=
    fun x => by
      simp only [EReal.abs_fun, Complex.re_fun, Complex.im_fun, Pi.add_apply]
      rw [← EReal.coe_add]
      exact EReal.coe_le_coe_iff.mpr (by
        calc ‖(f - g) x‖ ≤ |((f - g) x).re| + |((f - g) x).im| :=
            Complex.norm_le_abs_re_add_abs_im _
          _ = ‖((f - g) x).re‖ + ‖((f - g) x).im‖ := by rw [Real.norm_eq_abs, Real.norm_eq_abs])
  -- Measurability
  have hfg_ai := hf.sub hg_ai
  have hfg_re_ai := ComplexAbsolutelyIntegrable.re (f - g) hfg_ai
  have hfg_im_ai := ComplexAbsolutelyIntegrable.im (f - g) hfg_ai
  -- Monotonicity: ∫|f-g| ≤ ∫(|Re(f-g)| + |Im(f-g)|)
  have h_mono : UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) ≤
      UnsignedLebesgueIntegral (EReal.abs_fun (Complex.re_fun (f - g)) +
                                EReal.abs_fun (Complex.im_fun (f - g))) :=
    LowerUnsignedLebesgueIntegral.mono hfg_ai.abs.1
      (hfg_re_ai.abs.1.add hfg_im_ai.abs.1) (AlmostAlways.ofAlways h_bound)
  -- Additivity: ∫(|Re(f-g)| + |Im(f-g)|) = ∫|Re(f-g)| + ∫|Im(f-g)|
  have h_add : UnsignedLebesgueIntegral (EReal.abs_fun (Complex.re_fun (f - g)) +
      EReal.abs_fun (Complex.im_fun (f - g))) =
      UnsignedLebesgueIntegral (EReal.abs_fun (Complex.re_fun (f - g))) +
      UnsignedLebesgueIntegral (EReal.abs_fun (Complex.im_fun (f - g))) :=
    LowerUnsignedLebesgueIntegral.add hfg_re_ai.abs.1 hfg_im_ai.abs.1
      (hfg_re_ai.abs.1.add hfg_im_ai.abs.1)
  rw [h_add] at h_mono
  -- Rewrite using hfg_re, hfg_im to connect to PreL1.norm
  rw [show EReal.abs_fun (Complex.re_fun (f - g)) =
        EReal.abs_fun (Complex.re_fun f - g_re) from by rw [hfg_re],
      show EReal.abs_fun (Complex.im_fun (f - g)) =
        EReal.abs_fun (Complex.im_fun f - g_im) from by rw [hfg_im]] at h_mono
  -- Combine: ≤ ε/2 + ε/2 = ε
  calc UnsignedLebesgueIntegral (EReal.abs_fun (f - g))
      ≤ UnsignedLebesgueIntegral (EReal.abs_fun (Complex.re_fun f - g_re)) +
        UnsignedLebesgueIntegral (EReal.abs_fun (Complex.im_fun f - g_im)) := h_mono
    _ ≤ (↑(ε / 2) : EReal) + (↑(ε / 2) : EReal) := add_le_add hg_re_norm hg_im_norm
    _ = (ε : EReal) := by rw [← EReal.coe_add]; congr 1; linarith

def ComplexStepFunction {d:ℕ} (f: EuclideanSpace' d → ℂ) : Prop :=
  ∃ (S: Finset (Box d)) (c: S → ℂ), f = ∑ B, (c B • Complex.indicator (B.val.toSet))

def RealStepFunction {d:ℕ} (f: EuclideanSpace' d → ℝ) : Prop :=
  ∃ (S: Finset (Box d)) (c: S → ℝ), f = ∑ B, (c B • (B.val.toSet).indicator')

/-- Theorem 1.3.20(ii) Approximation of $L^1$ functions by step functions -/

-- Helper: indicator of an elementary set gives a step function
private lemma elementary_indicator_is_step {d:ℕ} {E : Set (EuclideanSpace' d)}
    (hE : IsElementary E) : RealStepFunction E.indicator' := by
  obtain ⟨T, hT_disj, hE_eq⟩ := hE.partition
  refine ⟨T, fun _ => 1, ?_⟩
  ext x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, one_mul]
  rw [hE_eq]
  by_cases hx : x ∈ ⋃ B ∈ T, B.toSet
  · rw [Set.indicator'_of_mem hx]
    rw [Set.mem_iUnion₂] at hx
    obtain ⟨B, hB_mem, hx_mem⟩ := hx
    have : ∑ B : T, (B.val.toSet).indicator' x = 1 := by
      rw [Finset.sum_eq_single ⟨B, hB_mem⟩]
      · exact Set.indicator'_of_mem hx_mem
      · intro ⟨B', hB'_mem⟩ _ hne
        apply Set.indicator'_of_notMem
        intro hx_B'
        have hBB' : B ≠ B' := fun h => hne (Subtype.ext h.symm)
        exact Set.disjoint_left.mp
          (hT_disj (Finset.mem_coe.mpr hB_mem) (Finset.mem_coe.mpr hB'_mem) hBB')
          hx_mem hx_B'
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [this]
  · rw [Set.indicator'_of_notMem hx]
    symm; apply Finset.sum_eq_zero
    intro ⟨B, hB_mem⟩ _
    apply Set.indicator'_of_notMem
    intro hx_mem
    exact hx (Set.mem_iUnion₂.mpr ⟨B, hB_mem, hx_mem⟩)

-- Helper: step functions are closed under scalar multiplication
private lemma RealStepFunction.smul' {d:ℕ} {f : EuclideanSpace' d → ℝ}
    (hf : RealStepFunction f) (a : ℝ) : RealStepFunction (a • f) := by
  obtain ⟨S, c, hf_eq⟩ := hf
  exact ⟨S, fun B => a * c B, by
    rw [hf_eq]; ext x
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    congr 1; ext B; rw [mul_assoc]⟩

-- Helper: step functions are closed under addition
private lemma RealStepFunction.add' {d:ℕ} {f g : EuclideanSpace' d → ℝ}
    (hf : RealStepFunction f) (hg : RealStepFunction g) : RealStepFunction (f + g) := by
  obtain ⟨S₁, c₁, hf_eq⟩ := hf
  obtain ⟨S₂, c₂, hg_eq⟩ := hg
  refine ⟨S₁ ∪ S₂, fun B =>
    (if h : B.val ∈ S₁ then c₁ ⟨B.val, h⟩ else 0) +
    (if h : B.val ∈ S₂ then c₂ ⟨B.val, h⟩ else 0), ?_⟩
  -- Rewrite f as sum over S₁ ∪ S₂ (extending c₁ by 0 outside S₁)
  have hf_union : ∀ x, (∑ B : ↥S₁, c₁ B • (B.val.toSet).indicator') x =
      (∑ B : ↥(S₁ ∪ S₂), (if h : B.val ∈ S₁ then c₁ ⟨B.val, h⟩ else 0) •
        (B.val.toSet).indicator') x := by
    intro x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    -- Embed S₁ into S₁ ∪ S₂
    set ι : ↥S₁ → ↥(S₁ ∪ S₂) :=
      fun B => ⟨B.val, Finset.mem_union_left S₂ B.prop⟩
    have hι_inj : Function.Injective ι :=
      fun ⟨a, _⟩ ⟨b, _⟩ h => Subtype.ext (Subtype.mk.inj h)
    -- The sum over S₁ ∪ S₂ restricts to S₁
    have h_zero : ∀ B : ↥(S₁ ∪ S₂), B ∉ Set.range ι →
        (if h : B.val ∈ S₁ then c₁ ⟨B.val, h⟩ else 0) * (B.val.toSet).indicator' x = 0 := by
      intro ⟨B, hB⟩ hni
      have : B ∉ S₁ := by
        intro hB₁
        exact hni ⟨⟨B, hB₁⟩, Subtype.ext rfl⟩
      simp [this]
    rw [← Finset.sum_filter_of_ne (fun B _ => not_imp_comm.mpr (h_zero B))]
    -- Show the filter equals the image of univ under ι
    have hfilter : Finset.univ.filter (fun B : ↥(S₁ ∪ S₂) => B ∈ Set.range ι) =
        Finset.univ.image ι := by
      ext ⟨B, hB⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Set.mem_range]
    rw [hfilter, Finset.sum_image (fun _ _ _ _ h => hι_inj h)]
    apply Finset.sum_congr rfl
    intro ⟨B, hB⟩ _
    simp only [ι, hB, dite_true]
  have hg_union : ∀ x, (∑ B : ↥S₂, c₂ B • (B.val.toSet).indicator') x =
      (∑ B : ↥(S₁ ∪ S₂), (if h : B.val ∈ S₂ then c₂ ⟨B.val, h⟩ else 0) •
        (B.val.toSet).indicator') x := by
    intro x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    set ι : ↥S₂ → ↥(S₁ ∪ S₂) :=
      fun B => ⟨B.val, Finset.mem_union_right S₁ B.prop⟩
    have hι_inj : Function.Injective ι :=
      fun ⟨a, _⟩ ⟨b, _⟩ h => Subtype.ext (Subtype.mk.inj h)
    have h_zero : ∀ B : ↥(S₁ ∪ S₂), B ∉ Set.range ι →
        (if h : B.val ∈ S₂ then c₂ ⟨B.val, h⟩ else 0) * (B.val.toSet).indicator' x = 0 := by
      intro ⟨B, hB⟩ hni
      have : B ∉ S₂ := by
        intro hB₂
        exact hni ⟨⟨B, hB₂⟩, Subtype.ext rfl⟩
      simp [this]
    rw [← Finset.sum_filter_of_ne (fun B _ => not_imp_comm.mpr (h_zero B))]
    have hfilter : Finset.univ.filter (fun B : ↥(S₁ ∪ S₂) => B ∈ Set.range ι) =
        Finset.univ.image ι := by
      ext ⟨B, hB⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Set.mem_range]
    rw [hfilter, Finset.sum_image (fun _ _ _ _ h => hι_inj h)]
    apply Finset.sum_congr rfl
    intro ⟨B, hB⟩ _
    simp only [ι, hB, dite_true]
  ext x
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hf_eq, hg_eq]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [show (∑ B : ↥S₁, c₁ B * (B.val.toSet).indicator' x) =
      (∑ B : ↥S₁, c₁ B • (B.val.toSet).indicator') x from by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]]
  rw [show (∑ B : ↥S₂, c₂ B * (B.val.toSet).indicator' x) =
      (∑ B : ↥S₂, c₂ B • (B.val.toSet).indicator') x from by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]]
  rw [hf_union x, hg_union x]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← add_mul, ← Finset.sum_add_distrib]

-- Helper: lift a real step function to a complex step function
private lemma RealStepFunction.toComplexStep {d:ℕ} {f : EuclideanSpace' d → ℝ}
    (hf : RealStepFunction f) : ComplexStepFunction (Real.complex_fun f) := by
  obtain ⟨S, c, hf_eq⟩ := hf
  refine ⟨S, fun B => ↑(c B), ?_⟩
  ext x
  simp only [Real.complex_fun, Complex.indicator, hf_eq]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Complex.ofReal_sum]
  congr 1; ext B
  exact Complex.ofReal_mul (c B) ((B.val.toSet).indicator' x)

-- Helper: complex step functions are closed under addition
private lemma ComplexStepFunction.add {d:ℕ} {f g : EuclideanSpace' d → ℂ}
    (hf : ComplexStepFunction f) (hg : ComplexStepFunction g) :
    ComplexStepFunction (f + g) := by
  obtain ⟨S₁, c₁, hf_eq⟩ := hf
  obtain ⟨S₂, c₂, hg_eq⟩ := hg
  refine ⟨S₁ ∪ S₂, fun B =>
    (if h : B.val ∈ S₁ then c₁ ⟨B.val, h⟩ else 0) +
    (if h : B.val ∈ S₂ then c₂ ⟨B.val, h⟩ else 0), ?_⟩
  -- Extend f-sum from S₁ to S₁ ∪ S₂
  have hf_union : ∀ x, (∑ B : ↥S₁, c₁ B • Complex.indicator (B.val.toSet)) x =
      (∑ B : ↥(S₁ ∪ S₂), (if h : B.val ∈ S₁ then c₁ ⟨B.val, h⟩ else 0) •
        Complex.indicator (B.val.toSet)) x := by
    intro x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    set ι : ↥S₁ → ↥(S₁ ∪ S₂) := fun B => ⟨B.val, Finset.mem_union_left S₂ B.prop⟩
    have hι_inj : Function.Injective ι :=
      fun ⟨a, _⟩ ⟨b, _⟩ h => Subtype.ext (Subtype.mk.inj h)
    have h_zero : ∀ B : ↥(S₁ ∪ S₂), B ∉ Set.range ι →
        (if h : B.val ∈ S₁ then c₁ ⟨B.val, h⟩ else 0) * Complex.indicator (B.val.toSet) x = 0 := by
      intro ⟨B, hB⟩ hni
      have : B ∉ S₁ := by intro hB₁; exact hni ⟨⟨B, hB₁⟩, Subtype.ext rfl⟩
      simp [this]
    rw [← Finset.sum_filter_of_ne (fun B _ => not_imp_comm.mpr (h_zero B))]
    have hfilter : Finset.univ.filter (fun B : ↥(S₁ ∪ S₂) => B ∈ Set.range ι) =
        Finset.univ.image ι := by
      ext ⟨B, hB⟩; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_image, Set.mem_range]
    rw [hfilter, Finset.sum_image (fun _ _ _ _ h => hι_inj h)]
    apply Finset.sum_congr rfl; intro ⟨B, hB⟩ _; simp only [ι, hB, dite_true]
  -- Extend g-sum from S₂ to S₁ ∪ S₂
  have hg_union : ∀ x, (∑ B : ↥S₂, c₂ B • Complex.indicator (B.val.toSet)) x =
      (∑ B : ↥(S₁ ∪ S₂), (if h : B.val ∈ S₂ then c₂ ⟨B.val, h⟩ else 0) •
        Complex.indicator (B.val.toSet)) x := by
    intro x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    set ι : ↥S₂ → ↥(S₁ ∪ S₂) := fun B => ⟨B.val, Finset.mem_union_right S₁ B.prop⟩
    have hι_inj : Function.Injective ι :=
      fun ⟨a, _⟩ ⟨b, _⟩ h => Subtype.ext (Subtype.mk.inj h)
    have h_zero : ∀ B : ↥(S₁ ∪ S₂), B ∉ Set.range ι →
        (if h : B.val ∈ S₂ then c₂ ⟨B.val, h⟩ else 0) * Complex.indicator (B.val.toSet) x = 0 := by
      intro ⟨B, hB⟩ hni
      have : B ∉ S₂ := by intro hB₂; exact hni ⟨⟨B, hB₂⟩, Subtype.ext rfl⟩
      simp [this]
    rw [← Finset.sum_filter_of_ne (fun B _ => not_imp_comm.mpr (h_zero B))]
    have hfilter : Finset.univ.filter (fun B : ↥(S₁ ∪ S₂) => B ∈ Set.range ι) =
        Finset.univ.image ι := by
      ext ⟨B, hB⟩; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_image, Set.mem_range]
    rw [hfilter, Finset.sum_image (fun _ _ _ _ h => hι_inj h)]
    apply Finset.sum_congr rfl; intro ⟨B, hB⟩ _; simp only [ι, hB, dite_true]
  ext x
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hf_eq, hg_eq]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [show (∑ B : ↥S₁, c₁ B * Complex.indicator (B.val.toSet) x) =
      (∑ B : ↥S₁, c₁ B • Complex.indicator (B.val.toSet)) x from by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]]
  rw [show (∑ B : ↥S₂, c₂ B * Complex.indicator (B.val.toSet) x) =
      (∑ B : ↥S₂, c₂ B • Complex.indicator (B.val.toSet)) x from by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]]
  rw [hf_union x, hg_union x]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← add_mul, ← Finset.sum_add_distrib]

-- Helper: complex step functions are closed under scalar multiplication
private lemma ComplexStepFunction.smul {d:ℕ} {f : EuclideanSpace' d → ℂ}
    (hf : ComplexStepFunction f) (a : ℂ) : ComplexStepFunction (a • f) := by
  obtain ⟨S, c, hf_eq⟩ := hf
  exact ⟨S, fun B => a * c B, by
    rw [hf_eq]; ext x
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    congr 1; ext B; rw [mul_assoc]⟩

-- Helper: the zero function is real absolutely integrable
private lemma RealAbsolutelyIntegrable.zero_fun {d:ℕ} :
    RealAbsolutelyIntegrable (0 : EuclideanSpace' d → ℝ) := by
  constructor
  · exact ⟨fun _ => 0, fun _ => ⟨0, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
      fun i => Fin.elim0 i, by funext x; simp [Finset.univ_eq_empty]⟩,
      fun _ => tendsto_const_nhds⟩
  · have h_zero : EReal.abs_fun (0 : EuclideanSpace' d → ℝ) = 0 := by
      funext x; simp only [EReal.abs_fun, Pi.zero_apply, norm_zero]; rfl
    rw [h_zero, UnsignedLebesgueIntegral]
    have h_simple : UnsignedSimpleFunction (0 : EuclideanSpace' d → EReal) := by
      use 0, fun i => Fin.elim0 i, fun i => Fin.elim0 i
      exact ⟨fun i => Fin.elim0 i, by funext x; simp [Finset.univ_eq_empty]⟩
    rw [LowerUnsignedLebesgueIntegral.eq_simpleIntegral h_simple]
    calc h_simple.integ = 0 := UnsignedSimpleFunction.integ_zero
      _ < ⊤ := EReal.zero_lt_top

-- Helper: PreL1.norm of zero ≤ any nonneg EReal value
private lemma PreL1.norm_zero_le {d:ℕ} {a : EReal} (ha : 0 ≤ a) :
    PreL1.norm (0 : EuclideanSpace' d → ℝ) ≤ a := by
  unfold PreL1.norm
  have h_zero : EReal.abs_fun (0 : EuclideanSpace' d → ℝ) = 0 := by
    funext x; simp only [EReal.abs_fun, Pi.zero_apply, norm_zero]; rfl
  rw [h_zero, UnsignedLebesgueIntegral]
  have h_simple : UnsignedSimpleFunction (0 : EuclideanSpace' d → EReal) := by
    use 0, fun i => Fin.elim0 i, fun i => Fin.elim0 i
    exact ⟨fun i => Fin.elim0 i, by funext x; simp [Finset.univ_eq_empty]⟩
  rw [LowerUnsignedLebesgueIntegral.eq_simpleIntegral h_simple,
    UnsignedSimpleFunction.integ_zero]
  exact ha

-- Helper: smul indicator is absolutely integrable when support has finite measure
private lemma RealAbsolutelyIntegrable.smul_indicator {d:ℕ}
    {E : Set (EuclideanSpace' d)} (hE : LebesgueMeasurable E)
    (c : ℝ) (hfin : c ≠ 0 → Lebesgue_measure E < ⊤) :
    RealAbsolutelyIntegrable (c • E.indicator') := by
  by_cases hc : c = 0
  · simp only [hc, zero_smul]; exact RealAbsolutelyIntegrable.zero_fun
  · have h_simple : RealSimpleFunction (c • E.indicator') :=
      ⟨1, fun _ => c, fun _ => E, fun _ => hE, by
        ext x; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_one]⟩
    exact h_simple.absolutelyIntegrable_iff'.mp (h_simple.absolutelyIntegrable_iff.mpr (by
      calc Lebesgue_measure (Support (c • E.indicator'))
          ≤ Lebesgue_outer_measure E := Lebesgue_outer_measure.mono (fun x hx => by
            rw [Support, Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul] at hx
            by_contra h_not
            exact hx (by rw [Set.indicator'_of_notMem h_not, mul_zero]))
        _ < ⊤ := hfin hc))

-- Helper: PreL1.norm of scalar * indicator of symmDiff
private lemma PreL1.norm_smul_indicator_symmDiff_le {d:ℕ}
    {E F : Set (EuclideanSpace' d)} (hE : LebesgueMeasurable E) (hF : LebesgueMeasurable F)
    (c : ℝ) :
    PreL1.norm (c • E.indicator' - c • F.indicator') ≤
      ↑(|c|) * Lebesgue_outer_measure (symmDiff E F) := by
  have hSD : LebesgueMeasurable (symmDiff E F) :=
    (hE.inter hF.complement).union (hF.inter hE.complement)
  have hSD_simple := UnsignedSimpleFunction.indicator hSD
  have hc_nn : (Real.toEReal |c|) ≥ 0 := by exact_mod_cast abs_nonneg c
  have h_simple := hSD_simple.smul hc_nn
  -- Pointwise: |c * indicator'_E(x) - c * indicator'_F(x)| = |c| * indicator'_{E△F}(x)
  have h_pw : EReal.abs_fun (c • E.indicator' - c • F.indicator') =
      (Real.toEReal |c|) • (Real.toEReal ∘ (symmDiff E F).indicator') := by
    funext x
    simp only [EReal.abs_fun, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Function.comp]
    by_cases hxE : x ∈ E <;> by_cases hxF : x ∈ F <;>
      simp [symmDiff_def, hxE, hxF]
  -- Compute: ∫|f| = |c| • ∫indicator(E△F) = |c| * μ(E△F)
  unfold PreL1.norm UnsignedLebesgueIntegral
  rw [h_pw, LowerUnsignedLebesgueIntegral.eq_simpleIntegral h_simple,
    UnsignedSimpleFunction.integral_smul hSD_simple hc_nn,
    UnsignedSimpleFunction.integral_indicator hSD]
  unfold Lebesgue_measure; exact le_refl _

-- Helper: triangle inequality for PreL1.norm
private lemma PreL1.norm_sub_le_add {d:ℕ} {f g h : EuclideanSpace' d → ℝ}
    (hfg_ai : RealAbsolutelyIntegrable (f - g))
    (hgh_ai : RealAbsolutelyIntegrable (g - h))
    (hfg : PreL1.norm (f - g) ≤ a) (hgh : PreL1.norm (g - h) ≤ b) :
    PreL1.norm (f - h) ≤ a + b := by
  -- Key: f - h = (f - g) + (g - h), so |f-h| ≤ |f-g| + |g-h| pointwise
  have h_eq : f - h = (f - g) + (g - h) := by ext x; simp [Pi.sub_apply]
  have hfh_ai : RealAbsolutelyIntegrable (f - h) := h_eq ▸ hfg_ai.add hgh_ai
  have h_le : ∀ x, EReal.abs_fun (f - h) x ≤
      (EReal.abs_fun (f - g) + EReal.abs_fun (g - h)) x := fun x => by
    rw [h_eq]
    simp only [EReal.abs_fun, Pi.add_apply]
    rw [← EReal.coe_add]
    exact EReal.coe_le_coe_iff.mpr (norm_add_le ((f - g) x) ((g - h) x))
  have hfg_abs := RealAbsolutelyIntegrable.abs _ hfg_ai
  have hgh_abs := RealAbsolutelyIntegrable.abs _ hgh_ai
  have hfh_abs := RealAbsolutelyIntegrable.abs _ hfh_ai
  -- Monotonicity: ∫|f-h| ≤ ∫(|f-g| + |g-h|)
  have h_mono : UnsignedLebesgueIntegral (EReal.abs_fun (f - h)) ≤
      UnsignedLebesgueIntegral (EReal.abs_fun (f - g) + EReal.abs_fun (g - h)) :=
    LowerUnsignedLebesgueIntegral.mono hfh_abs.1 (hfg_abs.1.add hgh_abs.1)
      (AlmostAlways.ofAlways h_le)
  -- Additivity: ∫(|f-g| + |g-h|) = ∫|f-g| + ∫|g-h|
  have h_add : UnsignedLebesgueIntegral (EReal.abs_fun (f - g) + EReal.abs_fun (g - h)) =
      UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) + UnsignedLebesgueIntegral (EReal.abs_fun (g - h)) :=
    LowerUnsignedLebesgueIntegral.add hfg_abs.1 hgh_abs.1 (hfg_abs.1.add hgh_abs.1)
  -- Combine
  unfold PreL1.norm at hfg hgh ⊢
  calc UnsignedLebesgueIntegral (EReal.abs_fun (f - h))
      ≤ UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) +
        UnsignedLebesgueIntegral (EReal.abs_fun (g - h)) := by rw [← h_add]; exact h_mono
    _ ≤ a + b := add_le_add hfg hgh

-- Main helper: every absolutely integrable simple function can be approximated by a step function
private lemma RealSimpleFunction.approx_by_step_aux {d:ℕ} {g : EuclideanSpace' d → ℝ}
    (hg_simple : RealSimpleFunction g) (hg_ai : RealAbsolutelyIntegrable g)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (h : EuclideanSpace' d → ℝ), RealStepFunction h ∧ RealAbsolutelyIntegrable h ∧
      PreL1.norm (g - h) ≤ δ := by
  obtain ⟨k, c, E, hE_meas, hg_eq⟩ := hg_simple
  by_cases hk : k = 0
  · subst hk
    have hg_zero : g = 0 := by rw [hg_eq]; funext x; simp [Finset.univ_eq_empty]
    refine ⟨0, ?_, RealAbsolutelyIntegrable.zero_fun, ?_⟩
    · exact ⟨∅, fun x => (Finset.notMem_empty x.1 x.2).elim, by simp⟩
    · rw [hg_zero, sub_zero]
      exact PreL1.norm_zero_le (EReal.coe_nonneg.mpr (le_of_lt hδ))
  · -- Case k ≠ 0: use disjoint representation and approximate each atom
    -- Step 1: Get disjoint representation of g
    have hg_simple' : RealSimpleFunction g := ⟨k, c, E, hE_meas, hg_eq⟩
    obtain ⟨n, v, A, hA_meas, hA_disj, hg_eq'⟩ := hg_simple'.disjoint_representation
    -- Step 2: Show Lebesgue_measure (Support g) < ⊤
    have hg_abs_int : hg_simple'.AbsolutelyIntegrable :=
      hg_simple'.absolutelyIntegrable_iff'.mpr hg_ai
    have hg_support_fin : Lebesgue_measure (Support g) < ⊤ :=
      hg_simple'.absolutelyIntegrable_iff.mp hg_abs_int
    -- Step 3: For each j with v j ≠ 0, A j ⊆ Support g, hence finite measure
    have hA_sub_support : ∀ j, v j ≠ 0 → A j ⊆ Support g := by
      intro j hvj x hx
      rw [Support, Set.mem_setOf_eq, hg_eq']
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single j]
      · exact mul_ne_zero hvj (Set.indicator'_of_mem hx ▸ one_ne_zero)
      · intro i _ hij
        rw [Set.indicator'_of_notMem]
        · ring
        · intro hxi
          exact absurd hxi (Set.disjoint_left.mp
            (hA_disj (Set.mem_univ j) (Set.mem_univ i) (Ne.symm hij)) hx)
      · intro h; exact absurd (Finset.mem_univ j) h
    have hA_fin : ∀ j, v j ≠ 0 → Lebesgue_measure (A j) < ⊤ := by
      intro j hvj
      calc Lebesgue_measure (A j)
          ≤ Lebesgue_outer_measure (Support g) := Lebesgue_outer_measure.mono (hA_sub_support j hvj)
        _ < ⊤ := hg_support_fin
    -- Handle n = 0 separately (g = 0 in this case)
    by_cases hn : n = 0
    · -- If n = 0, g = 0, so h = 0 works
      have hg_zero : g = 0 := by
        rw [hg_eq']; subst hn; funext x; simp [Finset.univ_eq_empty]
      refine ⟨0, ?_, RealAbsolutelyIntegrable.zero_fun, ?_⟩
      · exact ⟨∅, fun x => (Finset.notMem_empty x.1 x.2).elim, by simp⟩
      · rw [hg_zero, sub_zero]
        exact PreL1.norm_zero_le (EReal.coe_nonneg.mpr (le_of_lt hδ))
    -- Step 4: n ≠ 0, choose elementary approximations for each A j
    · have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      -- For each j with v j ≠ 0, use TFAE to get elementary F j with small symmDiff
      have hε_j : ∀ j : Fin n, 0 < δ / (↑n * (|v j| + 1)) := by
        intro j; apply div_pos hδ
        exact mul_pos hn_pos (by linarith [abs_nonneg (v j)])
      have hF_exists : ∀ j : Fin n, ∃ F : Set (EuclideanSpace' d),
          IsElementary F ∧
          (v j ≠ 0 → Lebesgue_outer_measure (symmDiff F (A j)) ≤
            ↑(δ / (↑n * (|v j| + 1)))) := by
        intro j
        by_cases hvj : v j = 0
        · exact ⟨∅, IsElementary.empty d, fun h => absurd hvj h⟩
        · have h_tfae := (LebesgueMeasurable.finite_TFAE (A j)).out 0 7
          have h_approx := h_tfae.mp ⟨hA_meas j, hA_fin j hvj⟩
          obtain ⟨F, hF_elem, hF_bound⟩ :=
            h_approx (↑(δ / (↑n * (|v j| + 1))))
              (EReal.coe_pos.mpr (hε_j j))
          exact ⟨F, hF_elem, fun _ => hF_bound⟩
      choose F hF_elem hF_bound using hF_exists
      -- Step 5: Define h = ∑ j : Fin n, v j • (F j).indicator'
      set h : EuclideanSpace' d → ℝ := ∑ j : Fin n, v j • (F j).indicator' with hh_def
      -- Each F j is elementary, so Lebesgue_outer_measure (F j) < ⊤
      have hF_fin : ∀ j : Fin n, Lebesgue_outer_measure (F j) < ⊤ := by
        intro j
        rw [Lebesgue_outer_measure.elementary (F j) (hF_elem j)]
        exact EReal.coe_lt_top _
      refine ⟨h, ?_, ?_, ?_⟩
      -- Step 6: h is a step function (by Finset induction)
      · rw [hh_def]; exact Finset.sum_induction _
          (fun f => RealStepFunction f)
          (fun f g hf hg => RealStepFunction.add' hf hg)
          ⟨∅, fun x => (Finset.notMem_empty x.1 x.2).elim, by simp⟩
          (fun j _ => RealStepFunction.smul'
            (elementary_indicator_is_step (hF_elem j)) (v j))
      -- Step 7: h is absolutely integrable
      · have hh_simple : RealSimpleFunction h :=
          ⟨n, v, fun j => F j,
           fun j => Jordan_measurable.lebesgue
             (IsElementary.jordanMeasurable (hF_elem j)),
           by rw [hh_def]⟩
        exact hh_simple.absolutelyIntegrable_iff'.mp
          ((hh_simple.absolutelyIntegrable_iff).mpr (by
            have h_support_sub : Support h ⊆ ⋃ j : Fin n, F j := by
              intro x hx
              rw [Support, Set.mem_setOf_eq] at hx
              rw [Set.mem_iUnion]
              by_contra h_not; push_neg at h_not; apply hx
              rw [hh_def]; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
              exact Finset.sum_eq_zero fun j _ =>
                by rw [Set.indicator'_of_notMem (h_not j)]; ring
            calc Lebesgue_measure (Support h)
                ≤ Lebesgue_outer_measure (⋃ j : Fin n, F j) :=
                  Lebesgue_outer_measure.mono h_support_sub
              _ ≤ ∑ j : Fin n, Lebesgue_outer_measure (F j) :=
                  Lebesgue_outer_measure.finite_union_le F
              _ < ⊤ := by
                  have : ∀ j : Fin n, Lebesgue_outer_measure (F j) =
                      ↑((hF_elem j).measure) :=
                    fun j => Lebesgue_outer_measure.elementary (F j) (hF_elem j)
                  simp_rw [this]
                  rw [← EReal.coe_finset_sum
                    (fun j _ => IsElementary.measure_nonneg (hF_elem j))]
                  exact EReal.coe_lt_top _))
      -- Step 8: Bound PreL1.norm (g - h) ≤ δ via induction on Finset
      · have hgh_eq : g - h = ∑ j : Fin n, (v j • (A j).indicator' - v j • (F j).indicator') := by
          rw [hg_eq', hh_def, ← Finset.sum_sub_distrib]
        suffices h_bound : ∀ (S : Finset (Fin n)),
            RealAbsolutelyIntegrable (∑ j ∈ S, (v j • (A j).indicator' - v j • (F j).indicator')) ∧
            PreL1.norm (∑ j ∈ S, (v j • (A j).indicator' - v j • (F j).indicator'))
            ≤ ∑ j ∈ S, (↑(|v j|) * Lebesgue_outer_measure (symmDiff (A j) (F j))) by
          rw [hgh_eq]
          have h1 := (h_bound Finset.univ).2
          calc PreL1.norm (∑ j : Fin n, (v j • (A j).indicator' - v j • (F j).indicator'))
              ≤ ∑ j : Fin n, (↑(|v j|) * Lebesgue_outer_measure (symmDiff (A j) (F j))) := h1
            _ ≤ ∑ j : Fin n, (↑(δ / ↑n) : EReal) := by
                apply Finset.sum_le_sum
                intro j _
                by_cases hvj : v j = 0
                · simp [hvj]
                  exact le_of_lt (div_pos hδ hn_pos)
                · have h_symmDiff := hF_bound j hvj
                  rw [symmDiff_comm] at h_symmDiff
                  calc ↑(|v j|) * Lebesgue_outer_measure (symmDiff (A j) (F j))
                      ≤ ↑(|v j|) * ↑(δ / (↑n * (|v j| + 1))) :=
                        mul_le_mul_of_nonneg_left h_symmDiff
                          (EReal.coe_nonneg.mpr (abs_nonneg _))
                    _ = ↑(|v j| * (δ / (↑n * (|v j| + 1)))) := by
                        rw [← EReal.coe_mul]
                    _ ≤ ↑(δ / ↑n) := by
                        rw [EReal.coe_le_coe_iff]
                        have hab : 0 < |v j| + 1 := by linarith [abs_nonneg (v j)]
                        calc |v j| * (δ / (↑n * (|v j| + 1)))
                            = |v j| * δ / (↑n * (|v j| + 1)) := by ring
                          _ ≤ (|v j| + 1) * δ / (↑n * (|v j| + 1)) := by
                              apply div_le_div_of_nonneg_right
                              · exact mul_le_mul_of_nonneg_right (by linarith) hδ.le
                              · exact (mul_pos hn_pos hab).le
                          _ = δ / ↑n := by
                              rw [mul_comm (|v j| + 1) δ, mul_div_mul_right _ _
                                (ne_of_gt hab)]
            _ = ↑δ := by
                rw [← EReal.coe_finset_sum (fun _ _ => le_of_lt (div_pos hδ hn_pos))]
                congr 1
                rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul,
                    mul_div_cancel₀ δ (Nat.cast_ne_zero.mpr hn)]
        -- Each term v j • (A j).indicator' - v j • (F j).indicator' is absolutely integrable
        have hterm_ai : ∀ j : Fin n, RealAbsolutelyIntegrable
            (v j • (A j).indicator' - v j • (F j).indicator') := fun j =>
          (RealAbsolutelyIntegrable.smul_indicator (hA_meas j) (v j) (hA_fin j)).sub
            (RealAbsolutelyIntegrable.smul_indicator
              (Jordan_measurable.lebesgue (IsElementary.jordanMeasurable (hF_elem j)))
              (v j) (fun _ => hF_fin j))
        -- Prove the suffices: induction on S
        intro S
        induction S using Finset.induction with
        | empty =>
          simp only [Finset.sum_empty]
          exact ⟨RealAbsolutelyIntegrable.zero_fun, PreL1.norm_zero_le le_rfl⟩
        | @insert a S haS ih =>
          rw [Finset.sum_insert haS, Finset.sum_insert haS]
          have h_single := PreL1.norm_smul_indicator_symmDiff_le (hA_meas a)
            (Jordan_measurable.lebesgue (IsElementary.jordanMeasurable (hF_elem a))) (v a)
          set f_a := v a • (A a).indicator' - v a • (F a).indicator'
          set sum_S := ∑ j ∈ S, (v j • (A j).indicator' - v j • (F j).indicator')
          have hfa_ai : RealAbsolutelyIntegrable f_a := hterm_ai a
          have hsum_ai : RealAbsolutelyIntegrable sum_S := ih.1
          -- Triangle inequality via PreL1.norm_sub_le_add
          have h_eq1 : f_a + sum_S - sum_S = f_a := by
            ext x; simp [f_a, sum_S, Pi.add_apply, Pi.sub_apply]
          have h_eq2 : sum_S - 0 = sum_S := by ext x; simp
          have h_eq3 : f_a + sum_S - 0 = f_a + sum_S := by ext x; simp
          have h_triangle : PreL1.norm (f_a + sum_S) ≤
              PreL1.norm f_a + PreL1.norm sum_S := by
            have hfg : PreL1.norm ((f_a + sum_S) - sum_S) ≤ PreL1.norm f_a := by
              rw [show (f_a + sum_S) - sum_S = f_a from h_eq1]
            have hgh : PreL1.norm (sum_S - 0) ≤ PreL1.norm sum_S := by
              rw [show sum_S - 0 = sum_S from h_eq2]
            have hfg_ai' : RealAbsolutelyIntegrable ((f_a + sum_S) - sum_S) := by
              rw [show (f_a + sum_S) - sum_S = f_a from h_eq1]; exact hfa_ai
            have hgh_ai' : RealAbsolutelyIntegrable (sum_S - 0) := by
              rw [show sum_S - 0 = sum_S from h_eq2]; exact hsum_ai
            calc PreL1.norm (f_a + sum_S)
                = PreL1.norm ((f_a + sum_S) - 0) := by congr 1; exact h_eq3.symm
              _ ≤ PreL1.norm f_a + PreL1.norm sum_S :=
                  PreL1.norm_sub_le_add hfg_ai' hgh_ai' hfg hgh
          constructor
          · exact hfa_ai.add hsum_ai
          · calc PreL1.norm (f_a + sum_S)
                ≤ PreL1.norm f_a + PreL1.norm sum_S := h_triangle
              _ ≤ (↑(|v a|) * Lebesgue_outer_measure (symmDiff (A a) (F a))) +
                  (∑ j ∈ S, (↑(|v j|) * Lebesgue_outer_measure (symmDiff (A j) (F j)))) :=
                  add_le_add h_single ih.2

theorem RealAbsolutelyIntegrable.approx_by_step {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf : RealAbsolutelyIntegrable f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (g : EuclideanSpace' d → ℝ), RealStepFunction g ∧ RealAbsolutelyIntegrable g ∧
        PreL1.norm (f - g) ≤ ε := by
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨g₁, hg₁_simple, hg₁_ai, hg₁_norm⟩ := hf.approx_by_simple (ε / 2) hε2
  obtain ⟨g₂, hg₂_step, hg₂_ai, hg₂_norm⟩ :=
    RealSimpleFunction.approx_by_step_aux hg₁_simple hg₁_ai (ε / 2) hε2
  refine ⟨g₂, hg₂_step, hg₂_ai, ?_⟩
  have h_combined := PreL1.norm_sub_le_add (hf.sub hg₁_ai) (hg₁_ai.sub hg₂_ai) hg₁_norm hg₂_norm
  calc PreL1.norm (f - g₂) ≤ ↑(ε / 2) + ↑(ε / 2) := h_combined
    _ = (ε : EReal) := by rw [← EReal.coe_add]; congr 1; linarith

theorem ComplexAbsolutelyIntegrable.approx_by_step {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf : ComplexAbsolutelyIntegrable f)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (g : EuclideanSpace' d → ℂ), ComplexStepFunction g ∧ ComplexAbsolutelyIntegrable g ∧
    PreL1.norm (f - g) ≤ ε := by
  -- Approximate real and imaginary parts within ε/2
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨g_re, hg_re_step, hg_re_ai, hg_re_norm⟩ :=
    (ComplexAbsolutelyIntegrable.re f hf).approx_by_step (ε / 2) hε2
  obtain ⟨g_im, hg_im_step, hg_im_ai, hg_im_norm⟩ :=
    (ComplexAbsolutelyIntegrable.im f hf).approx_by_step (ε / 2) hε2
  -- Construct complex approximation g = ↑g_re + I • ↑g_im
  set g : EuclideanSpace' d → ℂ :=
    Real.complex_fun g_re + Complex.I • Real.complex_fun g_im with hg_def
  have hg_re_eq : Complex.re_fun g = g_re := by
    ext x; simp only [Complex.re_fun, hg_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Real.complex_fun, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im]; ring
  have hg_im_eq : Complex.im_fun g = g_im := by
    ext x; simp only [Complex.im_fun, hg_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Real.complex_fun, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re]; ring
  -- g is a complex step function
  have hg_step : ComplexStepFunction g :=
    ComplexStepFunction.add
      (RealStepFunction.toComplexStep hg_re_step)
      (ComplexStepFunction.smul (RealStepFunction.toComplexStep hg_im_step) Complex.I)
  -- g is absolutely integrable
  have hg_ai : ComplexAbsolutelyIntegrable g := by
    apply (ComplexAbsolutelyIntegrable.iff g).mpr
    exact ⟨hg_re_eq ▸ hg_re_ai, hg_im_eq ▸ hg_im_ai⟩
  refine ⟨g, hg_step, hg_ai, ?_⟩
  -- Norm bound: PreL1.norm (f - g) ≤ ε
  show UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) ≤ (ε : EReal)
  have hfg_re : Complex.re_fun (f - g) = Complex.re_fun f - g_re := by
    ext x; simp only [Complex.re_fun, hg_def, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Real.complex_fun, Complex.sub_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im]; ring
  have hfg_im : Complex.im_fun (f - g) = Complex.im_fun f - g_im := by
    ext x; simp only [Complex.im_fun, hg_def, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Real.complex_fun, Complex.sub_im, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re]; ring
  have h_bound : ∀ x, EReal.abs_fun (f - g) x ≤
      (EReal.abs_fun (Complex.re_fun (f - g)) + EReal.abs_fun (Complex.im_fun (f - g))) x :=
    fun x => by
      simp only [EReal.abs_fun, Complex.re_fun, Complex.im_fun, Pi.add_apply]
      rw [← EReal.coe_add]
      exact EReal.coe_le_coe_iff.mpr (by
        calc ‖(f - g) x‖ ≤ |((f - g) x).re| + |((f - g) x).im| :=
            Complex.norm_le_abs_re_add_abs_im _
          _ = ‖((f - g) x).re‖ + ‖((f - g) x).im‖ := by rw [Real.norm_eq_abs, Real.norm_eq_abs])
  have hfg_ai := hf.sub hg_ai
  have hfg_re_ai := ComplexAbsolutelyIntegrable.re (f - g) hfg_ai
  have hfg_im_ai := ComplexAbsolutelyIntegrable.im (f - g) hfg_ai
  have h_mono : UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) ≤
      UnsignedLebesgueIntegral (EReal.abs_fun (Complex.re_fun (f - g)) +
                                EReal.abs_fun (Complex.im_fun (f - g))) :=
    LowerUnsignedLebesgueIntegral.mono hfg_ai.abs.1
      (hfg_re_ai.abs.1.add hfg_im_ai.abs.1) (AlmostAlways.ofAlways h_bound)
  have h_add : UnsignedLebesgueIntegral (EReal.abs_fun (Complex.re_fun (f - g)) +
      EReal.abs_fun (Complex.im_fun (f - g))) =
      UnsignedLebesgueIntegral (EReal.abs_fun (Complex.re_fun (f - g))) +
      UnsignedLebesgueIntegral (EReal.abs_fun (Complex.im_fun (f - g))) :=
    LowerUnsignedLebesgueIntegral.add hfg_re_ai.abs.1 hfg_im_ai.abs.1
      (hfg_re_ai.abs.1.add hfg_im_ai.abs.1)
  rw [h_add] at h_mono
  rw [show EReal.abs_fun (Complex.re_fun (f - g)) =
        EReal.abs_fun (Complex.re_fun f - g_re) from by rw [hfg_re],
      show EReal.abs_fun (Complex.im_fun (f - g)) =
        EReal.abs_fun (Complex.im_fun f - g_im) from by rw [hfg_im]] at h_mono
  calc UnsignedLebesgueIntegral (EReal.abs_fun (f - g))
      ≤ UnsignedLebesgueIntegral (EReal.abs_fun (Complex.re_fun f - g_re)) +
        UnsignedLebesgueIntegral (EReal.abs_fun (Complex.im_fun f - g_im)) := h_mono
    _ ≤ (↑(ε / 2) : EReal) + (↑(ε / 2) : EReal) := add_le_add hg_re_norm hg_im_norm
    _ = (ε : EReal) := by rw [← EReal.coe_add]; congr 1; linarith

def CompactlySupported {X Y:Type*} [TopologicalSpace X] [Zero Y] (f: X → Y) : Prop :=
  ∃ (K: Set X), IsCompact K ∧ ∀ x, x ∉ K → f x = 0

-- Helper: approximate a scaled box indicator by a continuous compactly supported function
private lemma Box.scaled_indicator_approx_continuous {d:ℕ} (B : Box d) (c : ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (g : EuclideanSpace' d → ℝ), Continuous g ∧ CompactlySupported g ∧
      RealAbsolutelyIntegrable g ∧ PreL1.norm (c • B.toSet.indicator' - g) ≤ δ := by
  -- Case 1: c = 0, then g = 0 works
  by_cases hc : c = 0
  · refine ⟨0, continuous_const, ⟨∅, isCompact_empty, fun x _ => rfl⟩,
      RealAbsolutelyIntegrable.zero_fun, ?_⟩
    have : c • B.toSet.indicator' - (0 : EuclideanSpace' d → ℝ) = 0 := by
      ext x; simp [hc]
    rw [this]
    exact PreL1.norm_zero_le (EReal.coe_nonneg.mpr (le_of_lt hδ))
  -- Case 2: c ≠ 0
  · -- B.toSet is elementary, hence Lebesgue measurable with finite measure
    have hB_elem : IsElementary B.toSet := IsElementary.box B
    have hB_meas : LebesgueMeasurable B.toSet :=
      Jordan_measurable.lebesgue (IsElementary.jordanMeasurable hB_elem)
    have hB_fin : Lebesgue_measure B.toSet < ⊤ := by
      unfold Lebesgue_measure
      rw [Lebesgue_outer_measure.elementary B.toSet hB_elem]
      exact EReal.coe_lt_top _
    -- Choose ε₀ = δ / (2 * |c|) > 0
    have hc_abs_pos : 0 < |c| := abs_pos.mpr hc
    set ε₀ : ℝ := δ / (2 * |c|) with hε₀_def
    have hε₀ : 0 < ε₀ := div_pos hδ (mul_pos two_pos hc_abs_pos)
    -- Get compact K ⊆ B.toSet with measure(B.toSet \ K) ≤ ε₀
    have h_tfae_03 := (LebesgueMeasurable.finite_TFAE B.toSet).out 0 3
    obtain ⟨K, hK_compact, hK_sub, hK_bound⟩ :=
      h_tfae_03.mp ⟨hB_meas, hB_fin⟩ (↑ε₀) (EReal.coe_pos.mpr hε₀)
    -- Get open U ⊇ B.toSet with measure(U \ B.toSet) ≤ ε₀ and finite measure
    have h_tfae_01 := (LebesgueMeasurable.finite_TFAE B.toSet).out 0 1
    obtain ⟨U, hU_open, hB_sub_U, hU_fin, hU_diff_bound⟩ :=
      h_tfae_01.mp ⟨hB_meas, hB_fin⟩ (↑ε₀) (EReal.coe_pos.mpr hε₀)
    -- K ⊆ U (since K ⊆ B.toSet ⊆ U)
    have hKU : K ⊆ U := hK_sub.trans hB_sub_U
    -- K and Uᶜ are disjoint
    have hKU_disj : Disjoint K Uᶜ :=
      Set.disjoint_compl_right_iff_subset.mpr hKU
    -- Apply Urysohn: get continuous φ with HasCompactSupport, φ=1 on K, φ=0 outside U
    obtain ⟨φ, hφ_one, hφ_zero, hφ_cs, hφ_range⟩ :=
      exists_continuous_one_zero_of_isCompact hK_compact hU_open.isClosed_compl hKU_disj
    -- Define g = c • φ
    set g : EuclideanSpace' d → ℝ := fun x => c * φ x with hg_def
    -- Set up notation for the difference
    set diff : EuclideanSpace' d → ℝ := c • B.toSet.indicator' - g with hdiff_def
    -- Key properties of φ
    have hφ_zero' : ∀ x, x ∉ U → φ x = 0 := by
      intro x hxU
      have := hφ_zero (show x ∈ Uᶜ from hxU)
      simp at this; exact this
    -- Pointwise bound: |diff(x)| ≤ |c| and diff = 0 outside U
    have hdiff_bound : ∀ x, ‖diff x‖ ≤ |c| := by
      intro x
      simp only [diff, hg_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      have hφ_bdd := hφ_range x
      rw [show c * B.toSet.indicator' x - c * φ x = c * (B.toSet.indicator' x - φ x) by ring]
      rw [norm_mul, Real.norm_eq_abs]
      apply mul_le_of_le_one_right (abs_nonneg c)
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · by_cases hxB : x ∈ B.toSet
        · rw [Set.indicator'_of_mem hxB]; linarith [hφ_bdd.2]
        · rw [Set.indicator'_of_notMem hxB]; linarith [hφ_bdd.2]
      · by_cases hxB : x ∈ B.toSet
        · rw [Set.indicator'_of_mem hxB]; linarith [hφ_bdd.1]
        · rw [Set.indicator'_of_notMem hxB]; linarith [hφ_bdd.1]
    have hdiff_support : ∀ x, x ∉ U → diff x = 0 := by
      intro x hxU
      simp only [diff, hg_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [Set.indicator'_of_notMem (fun h => hxU (hB_sub_U h)), mul_zero,
        hφ_zero' x hxU, mul_zero, sub_self]
    -- Measurability
    have hg_meas : RealMeasurable g :=
      (continuous_const.mul φ.continuous).RealMeasurable
    have hcB_ai : RealAbsolutelyIntegrable (c • B.toSet.indicator') :=
      RealAbsolutelyIntegrable.smul_indicator hB_meas c (fun _ => hB_fin)
    have hdiff_meas : RealMeasurable diff := RealMeasurable.sub hcB_ai.1 hg_meas
    -- Measurability of sets involved
    have hBK_meas : LebesgueMeasurable (B.toSet \ K) :=
      hB_meas.inter (hK_compact.isClosed.measurable).complement
    have hUB_meas : LebesgueMeasurable (U \ B.toSet) :=
      (IsOpen.measurable hU_open).inter hB_meas.complement
    -- Key pointwise bound: |diff(x)| ≤ |c| * (1_{B\K}(x) + 1_{U\B}(x))
    -- Also: simpler bound |diff(x)| ≤ |c| * 1_U(x) for AI proof
    have h_pw_U : ∀ x, EReal.abs_fun diff x ≤
        ((Real.toEReal |c|) • (Real.toEReal ∘ U.indicator')) x := by
      intro x
      simp only [EReal.abs_fun, Pi.smul_apply, smul_eq_mul, Function.comp]
      by_cases hxU : x ∈ U
      · rw [Set.indicator'_of_mem hxU]
        have : Real.toEReal 1 = (1 : EReal) := rfl
        rw [this, mul_one]
        exact EReal.coe_le_coe_iff.mpr (hdiff_bound x)
      · rw [hdiff_support x hxU, norm_zero, Set.indicator'_of_notMem hxU]
        have : Real.toEReal 0 = (0 : EReal) := rfl
        rw [this, mul_zero]
    -- Tighter pointwise bound (for the norm bound)
    have h_pw_tight : ∀ x, EReal.abs_fun diff x ≤
        ((Real.toEReal |c|) • ((Real.toEReal ∘ (B.toSet \ K).indicator') +
                                (Real.toEReal ∘ (U \ B.toSet).indicator'))) x := by
      intro x
      simp only [EReal.abs_fun, Pi.smul_apply, smul_eq_mul, Function.comp, Pi.add_apply]
      by_cases hxK : x ∈ K
      · -- On K: diff = 0
        have hdx : diff x = 0 := by
          simp only [diff, hg_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          have h1 := hφ_one hxK; simp only [Pi.one_apply] at h1
          rw [Set.indicator'_of_mem (hK_sub hxK), mul_one, h1, mul_one, sub_self]
        rw [hdx, norm_zero]
        apply mul_nonneg (EReal.coe_nonneg.mpr (abs_nonneg c))

        apply add_nonneg <;> exact EReal.coe_nonneg.mpr ((Set.indicator_nonneg (fun _ _ => zero_le_one) x))
      · by_cases hxB : x ∈ B.toSet
        · -- On B \ K: |diff| ≤ |c|, bound by |c| * 1
          rw [Set.indicator'_of_mem (show x ∈ B.toSet \ K from ⟨hxB, hxK⟩),
            Set.indicator'_of_notMem (show x ∉ U \ B.toSet from fun h => h.2 hxB)]
          have h0 : Real.toEReal 0 = (0 : EReal) := rfl
          have h1 : Real.toEReal 1 = (1 : EReal) := rfl
          rw [h1, h0, add_zero, mul_one]
          exact EReal.coe_le_coe_iff.mpr (hdiff_bound x)
        · by_cases hxU : x ∈ U
          · -- On U \ B: |diff| ≤ |c|, bound by |c| * 1
            rw [Set.indicator'_of_notMem (show x ∉ B.toSet \ K from fun h => hxB h.1),
              Set.indicator'_of_mem (show x ∈ U \ B.toSet from ⟨hxU, hxB⟩)]
            have h0 : Real.toEReal 0 = (0 : EReal) := rfl
            have h1 : Real.toEReal 1 = (1 : EReal) := rfl
            rw [h0, h1, zero_add, mul_one]
            exact EReal.coe_le_coe_iff.mpr (hdiff_bound x)
          · -- Outside U: diff = 0
            rw [hdiff_support x hxU, norm_zero]
            apply mul_nonneg (EReal.coe_nonneg.mpr (abs_nonneg c))
            apply add_nonneg <;> exact EReal.coe_nonneg.mpr ((Set.indicator_nonneg (fun _ _ => zero_le_one) x))
    -- Derive AI for diff (using the U bound)
    have hU_meas : LebesgueMeasurable U := IsOpen.measurable hU_open
    have hU_simple := UnsignedSimpleFunction.indicator hU_meas
    have hc_nn : (Real.toEReal |c|) ≥ 0 := by exact_mod_cast abs_nonneg c
    have hdiff_abs_meas : UnsignedMeasurable (EReal.abs_fun diff) := by
      constructor
      · intro x; simp only [EReal.abs_fun]; exact EReal.coe_nonneg.mpr (norm_nonneg _)
      · obtain ⟨g, hg_simple, hg_conv⟩ := hdiff_meas
        exact ⟨fun n => EReal.abs_fun (g n), fun n => (hg_simple n).abs, fun x => by
          simp only [EReal.abs_fun]
          exact (continuous_coe_real_ereal.comp continuous_norm).continuousAt.tendsto.comp (hg_conv x)⟩
    have hdiff_ai : RealAbsolutelyIntegrable diff := by
      constructor
      · exact hdiff_meas
      · have hbound_simple := hU_simple.smul hc_nn
        have hbound_meas := UnsignedSimpleFunction.unsignedMeasurable hbound_simple
        have h_mono := LowerUnsignedLebesgueIntegral.mono
          hdiff_abs_meas hbound_meas
          (AlmostAlways.ofAlways h_pw_U)
        have h_integ : LowerUnsignedLebesgueIntegral
            ((Real.toEReal |c|) • (Real.toEReal ∘ U.indicator')) =
            (Real.toEReal |c|) * Lebesgue_measure U := by
          rw [LowerUnsignedLebesgueIntegral.eq_simpleIntegral hbound_simple,
            UnsignedSimpleFunction.integral_smul hU_simple hc_nn,
            UnsignedSimpleFunction.integral_indicator hU_meas]
        rw [UnsignedLebesgueIntegral]
        calc LowerUnsignedLebesgueIntegral (EReal.abs_fun diff)
            ≤ LowerUnsignedLebesgueIntegral
                ((Real.toEReal |c|) • (Real.toEReal ∘ U.indicator')) := h_mono
          _ = (Real.toEReal |c|) * Lebesgue_measure U := h_integ
          _ < ⊤ := by
              apply Ne.lt_top
              exact (EReal.mul_ne_top (↑|c|) (Lebesgue_measure U)).mpr
                ⟨Or.inl (EReal.coe_ne_bot _),
                 Or.inl (le_of_lt (EReal.coe_pos.mpr hc_abs_pos)),
                 Or.inl (EReal.coe_ne_top _),
                 Or.inr (ne_of_lt hU_fin)⟩
    -- g = (c • B.toSet.indicator') - diff, so g is AI
    have hg_ai : RealAbsolutelyIntegrable g := by
      have : g = c • B.toSet.indicator' - diff := by
        ext x; simp [diff, hg_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [this]
      exact hcB_ai.sub hdiff_ai
    refine ⟨g, ?_, ?_, hg_ai, ?_⟩
    -- g is continuous
    · exact continuous_const.mul φ.continuous
    -- g is compactly supported
    · refine ⟨tsupport φ, hφ_cs, fun x hx => ?_⟩
      simp only [hg_def]
      have : φ x = 0 := by
        by_contra h
        exact hx (subset_tsupport φ (Function.mem_support.mpr h))
      rw [this, mul_zero]
    -- PreL1.norm bound: PreL1.norm diff ≤ δ
    · -- Use the tight pointwise bound
      have hBK_simple := UnsignedSimpleFunction.indicator hBK_meas
      have hUB_simple := UnsignedSimpleFunction.indicator hUB_meas
      have hsum_simple : UnsignedSimpleFunction
          ((Real.toEReal ∘ (B.toSet \ K).indicator') +
           (Real.toEReal ∘ (U \ B.toSet).indicator')) :=
        UnsignedSimpleFunction.add hBK_simple hUB_simple
      have hbound_simple := hsum_simple.smul hc_nn
      have hbound_meas2 := UnsignedSimpleFunction.unsignedMeasurable hbound_simple
      have h_mono := LowerUnsignedLebesgueIntegral.mono
        hdiff_abs_meas hbound_meas2
        (AlmostAlways.ofAlways h_pw_tight)
      have h_integ_bound : LowerUnsignedLebesgueIntegral
          ((Real.toEReal |c|) • ((Real.toEReal ∘ (B.toSet \ K).indicator') +
                                  (Real.toEReal ∘ (U \ B.toSet).indicator'))) =
          (Real.toEReal |c|) * (Lebesgue_measure (B.toSet \ K) +
                                 Lebesgue_measure (U \ B.toSet)) := by
        rw [LowerUnsignedLebesgueIntegral.eq_simpleIntegral hbound_simple,
          UnsignedSimpleFunction.integral_smul hsum_simple hc_nn]
        congr 1
        rw [← LowerUnsignedLebesgueIntegral.eq_simpleIntegral hsum_simple,
          LowerUnsignedLebesgueIntegral.add
          (UnsignedSimpleFunction.unsignedMeasurable hBK_simple)
          (UnsignedSimpleFunction.unsignedMeasurable hUB_simple)
          (UnsignedSimpleFunction.unsignedMeasurable hsum_simple),
          LowerUnsignedLebesgueIntegral.eq_simpleIntegral hBK_simple,
          LowerUnsignedLebesgueIntegral.eq_simpleIntegral hUB_simple,
          UnsignedSimpleFunction.integral_indicator hBK_meas,
          UnsignedSimpleFunction.integral_indicator hUB_meas]
      unfold PreL1.norm UnsignedLebesgueIntegral
      calc LowerUnsignedLebesgueIntegral (EReal.abs_fun diff)
          ≤ LowerUnsignedLebesgueIntegral
              ((Real.toEReal |c|) • ((Real.toEReal ∘ (B.toSet \ K).indicator') +
                                      (Real.toEReal ∘ (U \ B.toSet).indicator'))) := h_mono
        _ = (Real.toEReal |c|) * (Lebesgue_measure (B.toSet \ K) +
                                   Lebesgue_measure (U \ B.toSet)) := h_integ_bound
        _ ≤ (Real.toEReal |c|) * (↑ε₀ + ↑ε₀) := by
            apply mul_le_mul_of_nonneg_left _ hc_nn.le
            unfold Lebesgue_measure
            exact add_le_add hK_bound hU_diff_bound
        _ = ↑δ := by
            rw [← EReal.coe_add, ← EReal.coe_mul]
            congr 1
            rw [hε₀_def]
            field_simp
            ring

-- Helper: a step function can be approximated by a continuous compactly supported function
private lemma RealStepFunction.approx_by_continuous_compact_aux {d:ℕ}
    {h : EuclideanSpace' d → ℝ} (hh : RealStepFunction h) (_hh_ai : RealAbsolutelyIntegrable h)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (g : EuclideanSpace' d → ℝ), Continuous g ∧ CompactlySupported g ∧
      RealAbsolutelyIntegrable g ∧ PreL1.norm (h - g) ≤ δ := by
  obtain ⟨S, c, hh_eq⟩ := hh
  -- Handle empty finset
  by_cases hS : S = ∅
  · have hh_zero : h = 0 := by
      subst hS; rw [hh_eq]; simp [Finset.univ_eq_empty]
    refine ⟨0, continuous_const, ⟨∅, isCompact_empty, fun x _ => rfl⟩,
      RealAbsolutelyIntegrable.zero_fun, ?_⟩
    rw [hh_zero, sub_zero]
    exact PreL1.norm_zero_le (EReal.coe_nonneg.mpr (le_of_lt hδ))
  -- S is nonempty
  · have hS_nonempty : S.Nonempty := Finset.nonempty_of_ne_empty hS
    have hS_card_pos : 0 < S.card := Finset.Nonempty.card_pos hS_nonempty
    have hS_card_pos_real : 0 < (S.card : ℝ) := Nat.cast_pos.mpr hS_card_pos
    -- Budget per box
    have hδ_per : 0 < δ / S.card := div_pos hδ hS_card_pos_real
    -- For each box B ∈ S, approximate c B • B.val.toSet.indicator' by continuous g_B
    have h_approx : ∀ B : S, ∃ (g_B : EuclideanSpace' d → ℝ),
        Continuous g_B ∧ CompactlySupported g_B ∧
        RealAbsolutelyIntegrable g_B ∧
        PreL1.norm (c B • B.val.toSet.indicator' - g_B) ≤ δ / S.card :=
      fun B => Box.scaled_indicator_approx_continuous B.val (c B) (δ / S.card) hδ_per
    choose g_B hg_cont hg_cs hg_ai hg_norm using h_approx
    -- Define g = ∑ B ∈ S, g_B
    set g : EuclideanSpace' d → ℝ := fun x => ∑ B : S, g_B B x with hg_def
    -- h - g = ∑ B ∈ S, (c B • B.val.toSet.indicator' - g_B B)
    have hfg_eq : h - g = fun x => ∑ B : S, (c B • B.val.toSet.indicator' - g_B B) x := by
      ext x
      simp only [Pi.sub_apply, hg_def, hh_eq, Finset.sum_apply, Pi.smul_apply]
      rw [Finset.sum_sub_distrib]
    -- Each term is AI
    have hterm_ai : ∀ B : S,
        RealAbsolutelyIntegrable (c B • B.val.toSet.indicator' - g_B B) :=
      fun B => by
        have hB_meas : LebesgueMeasurable B.val.toSet :=
          Jordan_measurable.lebesgue (IsElementary.jordanMeasurable (IsElementary.box B.val))
        have hB_fin : Lebesgue_measure B.val.toSet < ⊤ := by
          unfold Lebesgue_measure
          rw [Lebesgue_outer_measure.elementary B.val.toSet (IsElementary.box B.val)]
          exact EReal.coe_lt_top _
        exact (RealAbsolutelyIntegrable.smul_indicator hB_meas (c B) (fun _ => hB_fin)).sub
          (hg_ai B)
    refine ⟨g, ?_, ?_, ?_, ?_⟩
    -- g is continuous
    · show Continuous g
      apply continuous_finset_sum
      intro B _
      exact hg_cont B
    -- g is compactly supported
    · obtain ⟨B₀, hB₀⟩ := hS_nonempty
      -- Each g_B has compact support K_B
      choose K hK_compact hK_support using fun B => (hg_cs B)
      refine ⟨⋃ B : S, K B, ?_, ?_⟩
      · exact isCompact_iUnion (fun B => (hK_compact B))
      · intro x hx
        rw [Set.mem_iUnion] at hx
        push_neg at hx
        simp only [hg_def]
        exact Finset.sum_eq_zero (fun B _ => hK_support B x (hx B))
    -- g is AI (sum of AI functions)
    · show RealAbsolutelyIntegrable g
      have hg_eq_sum : g = ∑ B : S, g_B B := by
        ext x; simp [hg_def]
      rw [hg_eq_sum]
      exact Finset.sum_induction _ RealAbsolutelyIntegrable
        (fun f g hf hg => hf.add hg) RealAbsolutelyIntegrable.zero_fun
        (fun B _ => hg_ai B)
    -- PreL1.norm (h - g) ≤ δ
    · -- Set up difference terms
      set diff_term : S → (EuclideanSpace' d → ℝ) :=
        fun B => c B • B.val.toSet.indicator' - g_B B with hdiff_term_def
      -- h - g = ∑ diff_term
      have hfg_eq' : h - g = ∑ B : S, diff_term B := by
        ext x
        simp only [Pi.sub_apply, hh_eq, hg_def, hdiff_term_def, Finset.sum_apply,
          Pi.smul_apply, Pi.sub_apply]
        rw [Finset.sum_sub_distrib]
      -- Prove by finset induction: AI of partial sum and norm bound
      suffices h_bound : ∀ (T : Finset S),
          RealAbsolutelyIntegrable (∑ B ∈ T, diff_term B) ∧
          PreL1.norm (∑ B ∈ T, diff_term B) ≤
          ∑ B ∈ T, PreL1.norm (diff_term B) by
        rw [hfg_eq']
        have h1 := (h_bound Finset.univ).2
        calc PreL1.norm (∑ B : S, diff_term B)
            ≤ ∑ B : S, PreL1.norm (diff_term B) := h1
          _ ≤ ∑ _B : S, (↑(δ / ↑S.card) : EReal) :=
              Finset.sum_le_sum (fun B _ => hg_norm B)
          _ = ↑δ := by
              rw [← EReal.coe_finset_sum (fun _ _ => le_of_lt hδ_per)]
              congr 1
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
                nsmul_eq_mul, mul_div_cancel₀ δ
                  (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hS_card_pos))]
      -- Prove the suffices by induction
      intro T
      induction T using Finset.induction with
      | empty =>
        simp only [Finset.sum_empty]
        exact ⟨RealAbsolutelyIntegrable.zero_fun, PreL1.norm_zero_le le_rfl⟩
      | @insert a T' haT ih =>
        rw [Finset.sum_insert haT, Finset.sum_insert haT]
        set f_a := diff_term a
        set sum_T := ∑ B ∈ T', diff_term B
        have hfa_ai : RealAbsolutelyIntegrable f_a := hterm_ai a
        have hsum_ai : RealAbsolutelyIntegrable sum_T := ih.1
        constructor
        · exact hfa_ai.add hsum_ai
        · -- Triangle inequality
          have h_eq1 : (f_a + sum_T) - sum_T = f_a := by
            ext x; simp [f_a, sum_T, Pi.add_apply, Pi.sub_apply]
          have h_eq2 : sum_T - 0 = sum_T := by ext x; simp
          have h_eq3 : (f_a + sum_T) - 0 = f_a + sum_T := by ext x; simp
          have hfg_ai' : RealAbsolutelyIntegrable ((f_a + sum_T) - sum_T) := by
            rw [h_eq1]; exact hfa_ai
          have hgh_ai' : RealAbsolutelyIntegrable (sum_T - 0) := by
            rw [h_eq2]; exact hsum_ai
          have hfg : PreL1.norm ((f_a + sum_T) - sum_T) ≤ PreL1.norm f_a := by rw [h_eq1]
          have hgh : PreL1.norm (sum_T - 0) ≤ PreL1.norm sum_T := by rw [h_eq2]
          calc PreL1.norm (f_a + sum_T)
              = PreL1.norm ((f_a + sum_T) - 0) := by congr 1; exact h_eq3.symm
            _ ≤ PreL1.norm f_a + PreL1.norm sum_T :=
                PreL1.norm_sub_le_add hfg_ai' hgh_ai' hfg hgh
            _ ≤ PreL1.norm f_a +
                ∑ B ∈ T', PreL1.norm (diff_term B) :=
                add_le_add le_rfl ih.2

/-- Theorem 1.3.20(iii) Approximation of $L^1$ functions by continuous compactly supported functions -/
theorem RealAbsolutelyIntegrable.approx_by_continuous_compact {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf : RealAbsolutelyIntegrable f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (g : EuclideanSpace' d → ℝ), Continuous g ∧ CompactlySupported g ∧
        PreL1.norm (f - g) ≤ ε := by
  -- Step 1: approximate f by step function h
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨h, hh_step, hh_ai, hh_norm⟩ := hf.approx_by_step (ε / 2) hε2
  -- Step 4: approximate step function h by continuous compactly supported g
  obtain ⟨g, hg_cont, hg_cs, hg_ai, hg_norm⟩ :=
    RealStepFunction.approx_by_continuous_compact_aux hh_step hh_ai (ε / 2) hε2
  -- Step 5: combine via triangle inequality
  refine ⟨g, hg_cont, hg_cs, ?_⟩
  have h_combined := PreL1.norm_sub_le_add (hf.sub hh_ai) (hh_ai.sub hg_ai) hh_norm hg_norm
  calc PreL1.norm (f - g) ≤ ↑(ε / 2) + ↑(ε / 2) := h_combined
    _ = (ε : EReal) := by rw [← EReal.coe_add]; congr 1; linarith

theorem ComplexAbsolutelyIntegrable.approx_by_continuous_compact {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf : ComplexAbsolutelyIntegrable f)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (g : EuclideanSpace' d → ℂ), Continuous g ∧ CompactlySupported g ∧
    PreL1.norm (f - g) ≤ ε := by
  -- Approximate real and imaginary parts within ε/2
  -- Use internal aux helpers to also get RealAbsolutelyIntegrable
  have hε2 : 0 < ε / 2 := half_pos hε
  have hε4 : 0 < ε / 2 / 2 := half_pos hε2
  -- Real part: step function approximation then continuous approximation
  obtain ⟨h_re, hh_re_step, hh_re_ai, hh_re_norm⟩ :=
    (ComplexAbsolutelyIntegrable.re f hf).approx_by_step (ε / 2 / 2) hε4
  obtain ⟨g_re, hg_re_cont, hg_re_cs, hg_re_ai, hg_re_norm'⟩ :=
    RealStepFunction.approx_by_continuous_compact_aux hh_re_step hh_re_ai (ε / 2 / 2) hε4
  have hg_re_norm : PreL1.norm (Complex.re_fun f - g_re) ≤ ↑(ε / 2) := by
    have := PreL1.norm_sub_le_add ((ComplexAbsolutelyIntegrable.re f hf).sub hh_re_ai)
      (hh_re_ai.sub hg_re_ai) hh_re_norm hg_re_norm'
    calc PreL1.norm (Complex.re_fun f - g_re)
        ≤ ↑(ε / 2 / 2) + ↑(ε / 2 / 2) := this
      _ = ↑(ε / 2) := by rw [← EReal.coe_add]; congr 1; linarith
  -- Imaginary part: step function approximation then continuous approximation
  obtain ⟨h_im, hh_im_step, hh_im_ai, hh_im_norm⟩ :=
    (ComplexAbsolutelyIntegrable.im f hf).approx_by_step (ε / 2 / 2) hε4
  obtain ⟨g_im, hg_im_cont, hg_im_cs, hg_im_ai, hg_im_norm'⟩ :=
    RealStepFunction.approx_by_continuous_compact_aux hh_im_step hh_im_ai (ε / 2 / 2) hε4
  have hg_im_norm : PreL1.norm (Complex.im_fun f - g_im) ≤ ↑(ε / 2) := by
    have := PreL1.norm_sub_le_add ((ComplexAbsolutelyIntegrable.im f hf).sub hh_im_ai)
      (hh_im_ai.sub hg_im_ai) hh_im_norm hg_im_norm'
    calc PreL1.norm (Complex.im_fun f - g_im)
        ≤ ↑(ε / 2 / 2) + ↑(ε / 2 / 2) := this
      _ = ↑(ε / 2) := by rw [← EReal.coe_add]; congr 1; linarith
  -- Construct complex approximation g = ↑g_re + I • ↑g_im
  set g : EuclideanSpace' d → ℂ :=
    Real.complex_fun g_re + Complex.I • Real.complex_fun g_im with hg_def
  have hg_re_eq : Complex.re_fun g = g_re := by
    ext x; simp only [Complex.re_fun, hg_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Real.complex_fun, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im]; ring
  have hg_im_eq : Complex.im_fun g = g_im := by
    ext x; simp only [Complex.im_fun, hg_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Real.complex_fun, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re]; ring
  -- g is continuous
  have hg_cont : Continuous g := by
    apply Continuous.add
    · exact Complex.continuous_ofReal.comp hg_re_cont
    · exact continuous_const.mul (Complex.continuous_ofReal.comp hg_im_cont)
  -- g is compactly supported
  have hg_cs : CompactlySupported g := by
    obtain ⟨K_re, hK_re_compact, hK_re_supp⟩ := hg_re_cs
    obtain ⟨K_im, hK_im_compact, hK_im_supp⟩ := hg_im_cs
    refine ⟨K_re ∪ K_im, hK_re_compact.union hK_im_compact, fun x hx => ?_⟩
    rw [Set.mem_union] at hx; push_neg at hx
    simp only [hg_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Real.complex_fun]
    rw [hK_re_supp x hx.1, hK_im_supp x hx.2]
    simp
  -- g is absolutely integrable
  have hg_ai : ComplexAbsolutelyIntegrable g := by
    apply (ComplexAbsolutelyIntegrable.iff g).mpr
    exact ⟨hg_re_eq ▸ hg_re_ai, hg_im_eq ▸ hg_im_ai⟩
  refine ⟨g, hg_cont, hg_cs, ?_⟩
  -- Norm bound: PreL1.norm (f - g) ≤ ε
  show UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) ≤ (ε : EReal)
  have hfg_re : Complex.re_fun (f - g) = Complex.re_fun f - g_re := by
    ext x; simp only [Complex.re_fun, hg_def, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Real.complex_fun, Complex.sub_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im]; ring
  have hfg_im : Complex.im_fun (f - g) = Complex.im_fun f - g_im := by
    ext x; simp only [Complex.im_fun, hg_def, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Real.complex_fun, Complex.sub_im, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re]; ring
  have h_bound : ∀ x, EReal.abs_fun (f - g) x ≤
      (EReal.abs_fun (Complex.re_fun (f - g)) + EReal.abs_fun (Complex.im_fun (f - g))) x :=
    fun x => by
      simp only [EReal.abs_fun, Complex.re_fun, Complex.im_fun, Pi.add_apply]
      rw [← EReal.coe_add]
      exact EReal.coe_le_coe_iff.mpr (by
        calc ‖(f - g) x‖ ≤ |((f - g) x).re| + |((f - g) x).im| :=
            Complex.norm_le_abs_re_add_abs_im _
          _ = ‖((f - g) x).re‖ + ‖((f - g) x).im‖ := by rw [Real.norm_eq_abs, Real.norm_eq_abs])
  have hfg_ai := hf.sub hg_ai
  have hfg_re_ai := ComplexAbsolutelyIntegrable.re (f - g) hfg_ai
  have hfg_im_ai := ComplexAbsolutelyIntegrable.im (f - g) hfg_ai
  have h_mono : UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) ≤
      UnsignedLebesgueIntegral (EReal.abs_fun (Complex.re_fun (f - g)) +
                                EReal.abs_fun (Complex.im_fun (f - g))) :=
    LowerUnsignedLebesgueIntegral.mono hfg_ai.abs.1
      (hfg_re_ai.abs.1.add hfg_im_ai.abs.1) (AlmostAlways.ofAlways h_bound)
  have h_add : UnsignedLebesgueIntegral (EReal.abs_fun (Complex.re_fun (f - g)) +
      EReal.abs_fun (Complex.im_fun (f - g))) =
      UnsignedLebesgueIntegral (EReal.abs_fun (Complex.re_fun (f - g))) +
      UnsignedLebesgueIntegral (EReal.abs_fun (Complex.im_fun (f - g))) :=
    LowerUnsignedLebesgueIntegral.add hfg_re_ai.abs.1 hfg_im_ai.abs.1
      (hfg_re_ai.abs.1.add hfg_im_ai.abs.1)
  rw [h_add] at h_mono
  rw [show EReal.abs_fun (Complex.re_fun (f - g)) =
        EReal.abs_fun (Complex.re_fun f - g_re) from by rw [hfg_re],
      show EReal.abs_fun (Complex.im_fun (f - g)) =
        EReal.abs_fun (Complex.im_fun f - g_im) from by rw [hfg_im]] at h_mono
  calc UnsignedLebesgueIntegral (EReal.abs_fun (f - g))
      ≤ UnsignedLebesgueIntegral (EReal.abs_fun (Complex.re_fun f - g_re)) +
        UnsignedLebesgueIntegral (EReal.abs_fun (Complex.im_fun f - g_im)) := h_mono
    _ ≤ (↑(ε / 2) : EReal) + (↑(ε / 2) : EReal) := add_le_add hg_re_norm hg_im_norm
    _ = (ε : EReal) := by rw [← EReal.coe_add]; congr 1; linarith

def UniformlyConvergesTo {X Y:Type*} [PseudoMetricSpace Y] (f: ℕ → X → Y) (g: X → Y) : Prop := ∀ ε>0, ∃ N, ∀ n ≥ N, ∀ x, dist (f n x) (g x) ≤ ε

def UniformlyConvergesToOn {X Y:Type*} [PseudoMetricSpace Y] (f: ℕ → X → Y) (g: X → Y) (S: Set X): Prop := UniformlyConvergesTo (fun n (x:S) ↦ f n x.val) (fun x ↦ g x.val)

/-- Definition 1.3.21 (Locally uniform convergence) -/
def LocallyUniformlyConvergesTo {X Y:Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] (f: ℕ → X → Y) (g: X → Y) : Prop :=
  ∀ (K: Set X), Bornology.IsBounded K → UniformlyConvergesToOn f g K

/-- Uniform convergence on a superset implies uniform convergence on a subset -/
private lemma UniformlyConvergesToOn.mono {X Y:Type*} [PseudoMetricSpace Y] (f: ℕ → X → Y) (g: X → Y)
    {S T : Set X} (hST : S ⊆ T) (hT : UniformlyConvergesToOn f g T) :
    UniformlyConvergesToOn f g S := by
  intro ε hε
  obtain ⟨N, hN⟩ := hT ε hε
  refine ⟨N, ?_⟩
  intro n hn x
  exact hN n hn ⟨x.val, hST x.2⟩

/-- Uniform convergence on a finite union can be combined -/
private lemma UniformlyConvergesToOn.finite_union {X Y:Type*} [PseudoMetricSpace Y] (f: ℕ → X → Y) (g: X → Y)
    {ι : Type*} (S : Finset ι) (U : ι → Set X) (hS : ∀ i ∈ S, UniformlyConvergesToOn f g (U i)) :
    UniformlyConvergesToOn f g (⋃ i : S, U i.val) := by
  intro ε hε
  have hN : ∀ i : S, ∃ N, ∀ n ≥ N, ∀ x : U i.val, dist (f n x.val) (g x.val) ≤ ε := by
    intro i
    exact hS i.val i.2 ε hε
  let N : S → ℕ := fun i => Classical.choose (hN i)
  let M : ℕ := S.attach.sup fun i => N i
  refine ⟨M, ?_⟩
  intro n hn x
  have hxmem : x.val ∈ ⋃ i : S, U i.val := x.2
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxmem
  have hNspec : ∀ m ≥ N i, ∀ y : U i.val, dist (f m y.val) (g y.val) ≤ ε :=
    Classical.choose_spec (hN i)
  have hni : N i ≤ M := by
    dsimp [M]
    exact Finset.le_sup (s := S.attach) (f := fun j => N j) (b := i) (by simp)
  exact hNspec n (le_trans hni hn) ⟨x.val, hi⟩

/-- Remark 1.3.22 -/
theorem LocallyUniformlyConvergesTo.iff {d:ℕ} {Y:Type*} [PseudoMetricSpace Y] (f: ℕ → EuclideanSpace' d → Y) (g: EuclideanSpace' d → Y) :
  LocallyUniformlyConvergesTo f g ↔
  ∀ x₀, ∃ U: Set (EuclideanSpace' d), x₀ ∈ U ∧ IsOpen U ∧ UniformlyConvergesToOn f g U := by
  constructor
  · intro hf x₀
    refine ⟨Metric.ball x₀ 1, Metric.mem_ball_self (by norm_num : (1:ℝ) > 0), Metric.isOpen_ball, ?_⟩
    exact hf (Metric.ball x₀ 1) Metric.isBounded_ball
  · intro hf K hK
    have hKcomp : IsCompact (closure K) :=
      (Metric.isCompact_iff_isClosed_bounded (α := EuclideanSpace' d)).mpr
        ⟨isClosed_closure, hK.closure⟩
    let C : Set (EuclideanSpace' d) := closure K
    let U : C → Set (EuclideanSpace' d) := fun x => Classical.choose (hf x.val)
    have hU_mem : ∀ x : C, x.val ∈ U x := by
      intro x
      exact (Classical.choose_spec (hf x.val)).1
    have hU_open : ∀ x : C, IsOpen (U x) := by
      intro x
      exact (Classical.choose_spec (hf x.val)).2.1
    have hU_conv : ∀ x : C, UniformlyConvergesToOn f g (U x) := by
      intro x
      exact (Classical.choose_spec (hf x.val)).2.2
    have hcov : C ⊆ ⋃ x : C, U x := by
      intro x hx
      exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hU_mem ⟨x, hx⟩⟩
    obtain ⟨t, ht_cov⟩ := hKcomp.elim_finite_subcover (fun x : C => U x) hU_open hcov
    have hS_conv : ∀ x ∈ t, UniformlyConvergesToOn f g (U x) := by
      intro x hx
      exact hU_conv x
    have hS_union : UniformlyConvergesToOn f g (⋃ x : t, U x.val) :=
      UniformlyConvergesToOn.finite_union f g t U (by
        intro x hx
        exact hU_conv x)
    have hK_sub : K ⊆ ⋃ x : t, U x.val := by
      intro x hx
      have hcov2 : x ∈ ⋃ j ∈ t, U j := ht_cov (subset_closure hx)
      simp only [Set.mem_iUnion] at hcov2
      obtain ⟨j, hj, hji⟩ := hcov2
      exact Set.mem_iUnion.mpr ⟨⟨j, hj⟩, hji⟩
    exact UniformlyConvergesToOn.mono f g hK_sub hS_union

def LocallyUniformlyConvergesToOn {X Y:Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] (f: ℕ → X → Y) (g: X → Y) (S: Set X): Prop :=
  LocallyUniformlyConvergesTo (fun n (x:S) ↦ f n x.val) (fun x ↦ g x.val)

/-- Example 1.3.23 -/
example : LocallyUniformlyConvergesTo (fun n (_x:EuclideanSpace' 1) ↦ _x.toReal / n) (fun _ ↦ 0) := by
  intro K hK
  rw [UniformlyConvergesToOn]
  intro ε hε
  obtain ⟨R, hKsub⟩ := (Metric.isBounded_iff_subset_closedBall (0 : EuclideanSpace' 1)).mp hK
  let R' : ℝ := max R 0
  have hsub' : K ⊆ Metric.closedBall (0 : EuclideanSpace' 1) R' := by
    intro x hx
    exact Metric.mem_closedBall.mpr (le_trans (Metric.mem_closedBall.mp (hKsub hx)) (le_max_left R 0))
  have hlim : Tendsto (fun n : ℕ => (R' : ℝ) / (n : ℝ)) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul R')
  have hεev : ∀ᶠ y in nhds (0 : ℝ), y < ε :=
    eventually_of_mem (isOpen_Iio.mem_nhds hε) (fun y hy => hy)
  have h_ev : ∀ᶠ n : ℕ in atTop, (R' : ℝ) / (n : ℝ) ≤ ε :=
    (hlim.eventually hεev).mono (fun n hn => hn.le)
  rcases (eventually_atTop.mp h_ev) with ⟨N, hN⟩
  refine ⟨max N 1, ?_⟩
  intro n hn x
  have hng : (1 : ℕ) ≤ n := le_trans (le_max_right N 1) hn
  have hnn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : (0:ℕ) < 1) hng)
  have hnN : N ≤ n := le_trans (le_max_left N 1) hn
  have hnorm : ‖x.val‖ ≤ R' := by
    have hx : x.val ∈ Metric.closedBall (0 : EuclideanSpace' 1) R' := hsub' x.2
    simpa [dist_eq_norm] using (Metric.mem_closedBall.mp hx)
  have hcoord : |x.val.toReal| ≤ ‖x.val‖ := by
    unfold EuclideanSpace'.toReal
    exact EuclideanSpace'.coord_le_norm x.val ⟨0, by simp⟩
  have hle : |x.val.toReal| ≤ R' := le_trans hcoord hnorm
  calc
    dist (x.val.toReal / (n : ℝ)) 0 = |x.val.toReal / (n : ℝ) - 0| := by rw [Real.dist_eq]
    _ = |x.val.toReal / (n : ℝ)| := by rw [sub_zero]
    _ = |x.val.toReal| / (n : ℝ) := by rw [abs_div, abs_of_nonneg hnn.le]
    _ ≤ R' / (n : ℝ) := div_le_div_of_nonneg_right hle hnn.le
    _ ≤ ε := hN n hnN

example : ¬ UniformlyConvergesTo (fun n (_x:EuclideanSpace' 1) ↦ _x.toReal / n) (fun _ ↦ 0) := by
  rw [UniformlyConvergesTo]
  push_neg
  refine ⟨1 / 2, by norm_num, ?_⟩
  intro N
  refine ⟨N + 1, by omega, ?_⟩
  let x : EuclideanSpace' 1 := (N + 1 : ℝ).toEuclideanSpace'
  refine ⟨x, ?_⟩
  have hx : x.toReal = (N + 1 : ℝ) := by
    simp [x, Real.toEuclideanSpace', Real.equiv_EuclideanSpace', EuclideanSpace'.toReal,
      EuclideanSpace'.equiv_Real]
  rw [Real.dist_eq, hx, sub_zero]
  have hne : (↑(N + 1) : ℝ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero N)
  have hcast : (↑N + 1 : ℝ) = (↑(N + 1) : ℝ) := by norm_num
  rw [hcast, div_self hne]
  norm_num

/-- Mathlib's {name}`TendstoUniformly` is equivalent to our {name}`UniformlyConvergesTo` -/
private lemma tendstoUniformly_iff_uniformlyConvergesTo {X Y:Type*} [PseudoMetricSpace Y]
    (F : ℕ → X → Y) (f : X → Y) :
    TendstoUniformly F f atTop ↔ UniformlyConvergesTo F f := by
  constructor
  · intro h ε hε
    have hball : {p : Y × Y | dist p.1 p.2 < ε} ∈ uniformity Y :=
      Metric.mem_uniformity_dist.mpr ⟨ε, hε, by intro a b hab; exact hab⟩
    rcases (eventually_atTop.mp (h {p : Y × Y | dist p.1 p.2 < ε} hball)) with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn x
    have hlt : dist (f x) (F n x) < ε := hN n hn x
    rw [dist_comm] at hlt
    exact le_of_lt hlt
  · intro h u hu
    obtain ⟨ε, hε, hsub⟩ := Metric.mem_uniformity_dist.mp hu
    obtain ⟨N, hN⟩ := h (ε / 2) (half_pos hε)
    refine (eventually_ge_atTop N).mono (fun n hn => ?_)
    intro x
    have hle : dist (F n x) (f x) ≤ ε / 2 := hN n hn x
    have hlt : dist (f x) (F n x) < ε := by
      rw [dist_comm]; exact lt_of_le_of_lt hle (half_lt_self hε)
    exact hsub hlt

/-- Mathlib's {name}`TendstoUniformlyOn` is equivalent to our {name}`UniformlyConvergesToOn` -/
private lemma tendstoUniformlyOn_iff_uniformlyConvergesToOn {X Y:Type*} [PseudoMetricSpace Y]
    (F : ℕ → X → Y) (f : X → Y) (S : Set X) :
    TendstoUniformlyOn F f atTop S ↔ UniformlyConvergesToOn F f S := by
  rw [UniformlyConvergesToOn]
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  exact tendstoUniformly_iff_uniformlyConvergesTo (F := fun n (x : S) => F n x.val) (f := fun x => f x.val)

/-- A function equal pointwise to a uniformly convergent one is uniformly convergent -/
private lemma UniformlyConvergesToOn.of_fun_eq {X Y:Type*} [PseudoMetricSpace Y]
    {F G : ℕ → X → Y} {f : X → Y} {S : Set X}
    (hF : UniformlyConvergesToOn F f S) (hFG : ∀ n x, F n x = G n x) :
    UniformlyConvergesToOn G f S := by
  intro ε hε
  obtain ⟨N, hN⟩ := hF ε hε
  refine ⟨N, ?_⟩
  intro n hn x
  have := hN n hn x
  simpa [hFG] using this

/-- The exponential Taylor series converges uniformly on any ball around 0 -/
private lemma exp_taylor_uniform_on_ball (R : ℝ) :
    UniformlyConvergesToOn
      (fun N (t : ℝ) => ∑ n ∈ Finset.range N, t^n / (n.factorial : ℝ))
      (fun t => t.exp) (Metric.ball 0 (R + 1)) := by
  let R' : ℝ := max R 0
  have hR' : 0 ≤ R' := le_max_right R 0
  have hR'1 : 0 < R' + 1 := by linarith
  have hfp' : HasFPowerSeriesOnBall NormedSpace.exp (NormedSpace.expSeries ℝ ℝ) 0 ⊤ :=
    NormedSpace.exp_hasFPowerSeriesOnBall (𝕂 := ℝ) (𝔸 := ℝ)
  have huni : TendstoUniformlyOn
      (fun (n : ℕ) (t : ℝ) => (NormedSpace.expSeries ℝ ℝ).partialSum n t)
      NormedSpace.exp atTop (Metric.ball 0 (R + 1)) := by
    have hsub : Metric.ball (0 : ℝ) (R + 1) ⊆ Metric.ball (0 : ℝ) (R' + 1) := by
      intro t ht
      rw [Metric.mem_ball] at ht ⊢
      have hlt : |t| < R + 1 := by
        simpa [Real.dist_eq, sub_zero] using ht
      have hRR' : R + 1 ≤ R' + 1 := by
        have : R ≤ R' := le_max_left R 0
        linarith
      have hlt' : |t| < R' + 1 := lt_of_lt_of_le hlt hRR'
      simpa [Real.dist_eq, sub_zero] using hlt'
    have huni' : TendstoUniformlyOn
        (fun (n : ℕ) (t : ℝ) => (NormedSpace.expSeries ℝ ℝ).partialSum n t)
        NormedSpace.exp atTop (Metric.ball 0 (R' + 1)) := by
      simpa [zero_add] using
        (hfp'.tendstoUniformlyOn (x := 0) (r := ⊤) (r' := ⟨R' + 1, by linarith⟩)
          (by exact WithTop.coe_lt_top _))
    exact huni'.mono hsub
  have huni' : UniformlyConvergesToOn
      (fun (n : ℕ) (t : ℝ) => (NormedSpace.expSeries ℝ ℝ).partialSum n t)
      NormedSpace.exp (Metric.ball 0 (R + 1)) :=
    (tendstoUniformlyOn_iff_uniformlyConvergesToOn _ _ _).mp huni
  have huni2 : UniformlyConvergesToOn
      (fun (n : ℕ) (t : ℝ) => (NormedSpace.expSeries ℝ ℝ).partialSum n t)
      (fun t => t.exp) (Metric.ball 0 (R + 1)) := by
    convert huni' using 1
    rw [Real.exp_eq_exp_ℝ]
  refine UniformlyConvergesToOn.of_fun_eq huni2 ?_
  intro N t
  rw [FormalMultilinearSeries.partialSum]
  simp_rw [NormedSpace.expSeries_apply_eq_div]

/-- Example 1.3.24 -/
example : LocallyUniformlyConvergesTo (fun N (x:EuclideanSpace' 1) ↦ ∑ n ∈ Finset.range N, x.toReal^n / n.factorial) (fun x ↦ x.toReal.exp) := by
  intro K hK
  obtain ⟨R, hKsub⟩ := (Metric.isBounded_iff_subset_closedBall (0 : EuclideanSpace' 1)).mp hK
  have hconv : UniformlyConvergesToOn
      (fun N (t : ℝ) => ∑ n ∈ Finset.range N, t^n / (n.factorial : ℝ))
      (fun t => t.exp) (Metric.ball 0 (R + 1)) := exp_taylor_uniform_on_ball R
  rw [UniformlyConvergesToOn] at hconv ⊢
  rw [UniformlyConvergesTo] at hconv ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hconv ε hε
  refine ⟨N, ?_⟩
  intro n hn x
  have hx : x.val.toReal ∈ Metric.ball (0 : ℝ) (R + 1) := by
    rw [Metric.mem_ball]
    have hnorm : ‖x.val‖ ≤ R := by
      have hxball : x.val ∈ Metric.closedBall (0 : EuclideanSpace' 1) R := hKsub x.2
      simpa [dist_eq_norm] using (Metric.mem_closedBall.mp hxball)
    have hcoord : |x.val.toReal| ≤ ‖x.val‖ := by
      unfold EuclideanSpace'.toReal
      exact EuclideanSpace'.coord_le_norm x.val ⟨0, by simp⟩
    have hle : |x.val.toReal| ≤ R := le_trans hcoord hnorm
    rw [Real.dist_eq, sub_zero]
    exact lt_of_le_of_lt hle (by linarith)
  exact hN n hn ⟨x.val.toReal, hx⟩

example : PointwiseConvergesTo (fun N (x:EuclideanSpace' 1) ↦ ∑ n ∈ Finset.range N, x.toReal^n / n.factorial) (fun x ↦ x.toReal.exp) := by
  intro x
  have htsum : (∑' n : ℕ, x.toReal ^ n / (n.factorial : ℝ)) = x.toReal.exp := by
    rw [Real.exp_eq_exp_ℝ]
    rw [NormedSpace.exp_eq_tsum_div (𝔸 := ℝ)]
  have hsum : Summable (fun n : ℕ => x.toReal ^ n / (n.factorial : ℝ)) :=
    Real.summable_pow_div_factorial x.toReal
  have hhas : HasSum (fun n : ℕ => x.toReal ^ n / (n.factorial : ℝ)) (∑' n : ℕ, x.toReal ^ n / (n.factorial : ℝ)) :=
    hsum.hasSum
  have htend : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, x.toReal ^ n / (n.factorial : ℝ)) atTop
      (nhds (∑' n : ℕ, x.toReal ^ n / (n.factorial : ℝ))) :=
    hhas.tendsto_sum_nat
  simpa [htsum] using htend

example : ¬ UniformlyConvergesTo (fun N (x:EuclideanSpace' 1) ↦ ∑ n ∈ Finset.range N, x.toReal^n / n.factorial) (fun x ↦ x.toReal.exp) := by
  rw [UniformlyConvergesTo]
  push_neg
  refine ⟨1, by norm_num, ?_⟩
  intro N
  let x : EuclideanSpace' 1 := (2 * (N + 1) : ℝ).toEuclideanSpace'
  refine ⟨N + 1, by omega, ?_⟩
  refine ⟨x, ?_⟩
  have hx : x.toReal = (2 * (N + 1) : ℝ) := by
    simp [x, Real.toEuclideanSpace', Real.equiv_EuclideanSpace', EuclideanSpace'.toReal,
      EuclideanSpace'.equiv_Real]
  let f : ℕ → ℝ := fun k => x.toReal ^ k / (k.factorial : ℝ)
  have hxnn : 0 ≤ x.toReal := by linarith
  have hf_nonneg : ∀ k, 0 ≤ f k := by
    intro k
    unfold f
    exact div_nonneg (pow_nonneg hxnn _) (by exact_mod_cast (Nat.factorial_pos k).le)
  have htsum : (∑' k : ℕ, f k) = x.toReal.exp := by
    unfold f
    rw [Real.exp_eq_exp_ℝ]
    rw [NormedSpace.exp_eq_tsum_div (𝔸 := ℝ)]
  have hsum : Summable f := by
    unfold f
    exact Real.summable_pow_div_factorial x.toReal
  have hhas : HasSum f (∑' k : ℕ, f k) := hsum.hasSum
  let P : ℝ := ∑ k ∈ Finset.range (N + 1), f k
  have hsplit : HasSum (fun k => f (k + (N + 1))) (∑' k : ℕ, f k - P) := by
    rw [hasSum_nat_add_iff]
    convert hhas using 1
    ring
  have htail_le : f (N + 1) ≤ ∑' k : ℕ, f k - P := by
    have hsum_tail : Summable (fun k => f (k + (N + 1))) := hsplit.summable
    have hle0 : ∀ j, j ≠ 0 → 0 ≤ f (j + (N + 1)) := by
      intro j hj
      exact hf_nonneg (j + (N + 1))
    have hle := Summable.le_tsum hsum_tail (i := 0) hle0
    simpa [hsplit.tsum_eq] using hle
  have hterm_ge : 2 ≤ f (N + 1) := by
    unfold f
    rw [hx]
    have hfact : (N + 1).factorial ≤ (N + 1) ^ (N + 1) := Nat.factorial_le_pow (N + 1)
    have hden_pos : 0 < ((N + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (N + 1)
    calc
      (2 : ℝ) ≤ (2 : ℝ) ^ (N + 1) := by
        have : (2 : ℝ) ^ 1 ≤ 2 ^ (N + 1) := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega)
        simpa using this
      _ = (2 * (N + 1)) ^ (N + 1) / (N + 1) ^ (N + 1) := by
        rw [mul_pow]
        field_simp [pow_ne_zero _ (by positivity : (N + 1 : ℝ) ≠ 0)]
      _ ≤ (2 * (N + 1)) ^ (N + 1) / ((N + 1).factorial : ℝ) := by
        have hnum : 0 ≤ (2 * (N + 1) : ℝ) ^ (N + 1) := by positivity
        have hc1 : 0 < (N + 1 : ℝ) ^ (N + 1) := by positivity
        have hfact' : ((N + 1).factorial : ℝ) ≤ (N + 1 : ℝ) ^ (N + 1) := by exact_mod_cast hfact
        rw [div_le_div_iff₀ hc1 hden_pos]
        exact mul_le_mul_of_nonneg_left hfact' hnum
      _ = (2 * (N + 1) : ℝ) ^ (N + 1) / ((N + 1).factorial : ℝ) := by rfl
  have hle : f (N + 1) ≤ x.toReal.exp - P := by
    have : x.toReal.exp - P = ∑' k : ℕ, f k - P := by rw [htsum]
    rw [this]
    exact htail_le
  have hbig : 2 ≤ x.toReal.exp - P := le_trans hterm_ge hle
  rw [Real.dist_eq]
  rw [show (∑ n ∈ Finset.range (N + 1), x.toReal ^ n / (n.factorial : ℝ)) = P from by
    rfl]
  rw [show |P - x.toReal.exp| = x.toReal.exp - P from by
    rw [abs_sub_comm]
    exact abs_of_nonneg (by linarith)]
  linarith

/-- Example 1.3.25 -/
example : PointwiseConvergesTo (fun n (_x:EuclideanSpace' 1) ↦ if _x.toReal > 0 then 1 / (n * _x.toReal) else 0) (fun _ ↦ 0) := by
  intro x
  by_cases hx : 0 < x.toReal
  · -- x.toReal > 0: 1/(n * x.toReal) → 0
    simp [hx]
    have hn : Tendsto (fun n : ℕ => ((n : ℝ)⁻¹)) atTop (nhds 0) := by
      simpa [div_eq_mul_inv] using (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hc : Tendsto (fun n : ℕ => x.toReal⁻¹ * (n : ℝ)⁻¹) atTop (nhds (x.toReal⁻¹ * 0)) :=
      (tendsto_const_nhds (x := x.toReal⁻¹)).mul hn
    simpa [mul_comm, mul_left_comm, mul_assoc] using hc
  · -- x.toReal ≤ 0: 0 → 0
    simp [hx]

example : ¬ LocallyUniformlyConvergesTo (fun n (_x:EuclideanSpace' 1) ↦ if _x.toReal > 0 then 1 / (n * _x.toReal) else 0) (fun _ ↦ 0) := by
  rw [LocallyUniformlyConvergesTo]
  push_neg
  -- Pick K = {x | 0 < x.toReal ∧ x.toReal ≤ 1}
  let K : Set (EuclideanSpace' 1) := {x | 0 < x.toReal ∧ x.toReal ≤ 1}
  refine ⟨K, ?_, ?_⟩
  · -- K is bounded: subset of closedBall 0 1
    rw [Metric.isBounded_iff_subset_closedBall (0 : EuclideanSpace' 1)]
    refine ⟨1, ?_⟩
    intro x hx
    have hnorm_eq : ‖x‖ = |x.toReal| := by
      rw [EuclideanSpace'.norm_eq, Fin.sum_univ_one]
      simp [EuclideanSpace'.toReal, EuclideanSpace'.equiv_Real, Real.sqrt_sq_eq_abs]
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, hnorm_eq]
    have hxabs : |x.toReal| ≤ 1 := by
      rw [abs_le]
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact hxabs
  · -- ¬ UniformlyConvergesToOn f g K
    rw [UniformlyConvergesToOn, UniformlyConvergesTo]
    push_neg
    refine ⟨1 / 2, by norm_num, ?_⟩
    intro N
    -- pick n = N+2 with x.toReal = 1/n ∈ K: f_n(x) = 1/(n * (1/n)) = 1
    refine ⟨N + 2, by omega, ?_⟩
    let n : ℕ := N + 2
    let y : EuclideanSpace' 1 := (1 / (n : ℝ)).toEuclideanSpace'
    have hxpos : 0 < y.toReal := by
      simp [y, n, Real.toEuclideanSpace', Real.equiv_EuclideanSpace', EuclideanSpace'.toReal,
        EuclideanSpace'.equiv_Real]
      positivity
    have hxle : y.toReal ≤ 1 := by
      simp [y, n, Real.toEuclideanSpace', Real.equiv_EuclideanSpace', EuclideanSpace'.toReal,
        EuclideanSpace'.equiv_Real]
      have hpos : 0 < (n : ℝ) := by positivity
      have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (Nat.le_add_left 1 (N + 1))
      field_simp [ne_of_gt hpos]
      nlinarith
    have hxmem : y ∈ K := ⟨hxpos, hxle⟩
    refine ⟨⟨y, hxmem⟩, ?_⟩
    -- dist (f n y) 0 > 1/2 where f n y = 1
    have hf : 1 / ((n : ℝ) * y.toReal) = 1 := by
      simp [y, Real.toEuclideanSpace', Real.equiv_EuclideanSpace', EuclideanSpace'.toReal,
        EuclideanSpace'.equiv_Real, n]
      have hn_eq' : (↑N + 2 : ℝ) = (n : ℝ) := by
        calc
          (↑N + 2 : ℝ) = (↑(N + 2) : ℝ) := by norm_num
          _ = (n : ℝ) := by simp [n]
      rw [hn_eq']
      exact (mul_inv_cancel₀ (show (n : ℝ) ≠ 0 from by positivity))
    rw [Real.dist_eq]
    change 1 / 2 < |(if 0 < y.toReal then 1 / (↑(N + 2) * y.toReal) else 0) - 0|
    have hg : (if 0 < y.toReal then 1 / (↑(N + 2) * y.toReal) else 0) = 1 := by
      simp [hxpos]
      have hy : y.toReal = (n : ℝ)⁻¹ := by
        simp [y, n, Real.toEuclideanSpace', Real.equiv_EuclideanSpace', EuclideanSpace'.toReal,
          EuclideanSpace'.equiv_Real, div_eq_mul_inv]
      field_simp [hy, show (n : ℝ) ≠ 0 from by positivity]
      have hn_eq : (↑(N + 2) : ℝ) = (n : ℝ) := by simp [n]
      rw [hy]
      have hn_eq' : (↑N + 2 : ℝ) = (n : ℝ) := by
        calc
          (↑N + 2 : ℝ) = (↑(N + 2) : ℝ) := by norm_num
          _ = (n : ℝ) := hn_eq
      rw [hn_eq']
      exact (inv_mul_cancel₀ (show (n : ℝ) ≠ 0 from by positivity)).symm
    rw [hg, sub_zero]
    norm_num

lemma egorov_tsum_geometric {ε : ℝ} (hε : 0 < ε) :
    (∑' m : ℕ, (ε / 2^(m+1) : EReal)) ≤ ε := by
    have hstep : ∀ m : ℕ, ε / 2^(m+1) = ε * (1 / 2 : ℝ) ^ (m+1) := by
      intro m
      rw [div_pow]
      simp [div_eq_mul_inv]
    have hgeom : (∑' m : ℕ, (1 / 2 : ℝ) ^ (m + 1)) = 1 := by
      calc
        (∑' m : ℕ, (1 / 2 : ℝ) ^ (m + 1)) = ∑' m : ℕ, (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ m := by
          apply tsum_congr
          intro m
          rw [pow_succ]
          ring
        _ = (1 / 2 : ℝ) * ∑' m : ℕ, (1 / 2 : ℝ) ^ m := by
          rw [tsum_mul_left]
        _ = (1 / 2 : ℝ) * ((1 - (1 / 2 : ℝ))⁻¹) := by
          congr 1
          exact tsum_geometric_of_abs_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
        _ = 1 := by
          norm_num
    have hreal : (∑' m : ℕ, (ε / 2^(m+1) : ℝ)) = ε := by
      calc
        (∑' m : ℕ, (ε / 2^(m+1) : ℝ)) = ∑' m : ℕ, ε * (1 / 2 : ℝ) ^ (m + 1) := by
          exact tsum_congr hstep
        _ = ε * (∑' m : ℕ, (1 / 2 : ℝ) ^ (m + 1)) := by
          rw [tsum_mul_left]
        _ = ε * 1 := by
          rw [hgeom]
        _ = ε := by
          ring
    have hnn : ∀ m : ℕ, 0 ≤ ε / 2^(m+1) := by
      intro m
      positivity
    have hsumm : Summable (fun m : ℕ => ε / 2^(m+1)) := by
      have hs : Summable (fun m : ℕ => (1 / 2 : ℝ) ^ (m + 1)) := by
        convert (Summable.mul_left (1 / 2 : ℝ) (summable_geometric_of_abs_lt_one (r := (1 / 2 : ℝ)) (by norm_num))) using 1
        ext m
        rw [pow_succ]
        ring
      simpa [hstep] using (Summable.mul_left ε hs)
    have hpoint : ∀ m : ℕ, (ε / 2^(m+1) : EReal) = (↑(ε / 2^(m+1) : ℝ) : EReal) := by
      intro m
      rw [EReal.coe_div, EReal.coe_pow]
      rfl
    calc
      (∑' m : ℕ, (ε / 2^(m+1) : EReal)) = (∑' m : ℕ, (↑(ε / 2^(m+1) : ℝ) : EReal)) := by
        exact tsum_congr hpoint
      _ = (↑(∑' m : ℕ, (ε / 2^(m+1) : ℝ)) : EReal) := by
        exact (EReal.coe_tsum_of_nonneg hnn hsumm).symm
      _ ≤ (ε : EReal) := by
        rw [hreal]

/-- Preimage of a closed set under a complex measurable function is Lebesgue measurable. -/
lemma ComplexMeasurable.preimage_closed {d:ℕ} {f : EuclideanSpace' d → ℂ} (hf : ComplexMeasurable f)
    {K : Set ℂ} (hK : IsClosed K) : LebesgueMeasurable (f ⁻¹' K) := by
  exact ((ComplexMeasurable_TFAE_helpers.ComplexMeasurable.TFAE (f := f)).out 0 5
    (a := ComplexMeasurable f)
    (b := ∀ K : Set ℂ, IsClosed K → LebesgueMeasurable (f ⁻¹' K))).mp hf K hK

/-- The "bad" set where some f(k) (k ≥ n) is still at distance ≥ 1/(m+1) from g is measurable. -/
lemma egorov_bad_set_measurable {d:ℕ} {f : ℕ → EuclideanSpace' d → ℂ} {g : EuclideanSpace' d → ℂ}
    (hf : ∀ n, ComplexMeasurable (f n)) (hg : ComplexMeasurable g) (n m : ℕ) :
    LebesgueMeasurable (⋃ j : ℕ, {x | (1 / (m + 1 : ℝ)) ≤ ‖f (n + j) x - g x‖}) := by
    have hK : IsClosed ({z : ℂ | (1 / (m + 1 : ℝ)) ≤ ‖z‖}) := by
      simpa using (IsClosed.preimage continuous_norm (isClosed_Ici (a := (1 / (m + 1 : ℝ)))))
    have hmeas : ∀ j : ℕ, LebesgueMeasurable ({x | (1 / (m + 1 : ℝ)) ≤ ‖f (n + j) x - g x‖}) := by
      intro j
      have hsub : ComplexMeasurable (f (n + j) - g) := ComplexMeasurable.sub (hf (n + j)) hg
      have hEq : ({x | (1 / (m + 1 : ℝ)) ≤ ‖f (n + j) x - g x‖}) =
          (f (n + j) - g) ⁻¹' {z : ℂ | (1 / (m + 1 : ℝ)) ≤ ‖z‖} := by
        ext x
        rfl
      rw [hEq]
      exact ComplexMeasurable.preimage_closed hsub hK
    exact LebesgueMeasurable.countable_union hmeas

/-- The intersection over n of the bad sets is null: it consists of points where convergence fails. -/
lemma egorov_bad_inter_null {d:ℕ} {f : ℕ → EuclideanSpace' d → ℂ} {g : EuclideanSpace' d → ℂ}
    (hfg : PointwiseAeConvergesTo f g) (m : ℕ) :
    IsNull (⋂ n : ℕ, (⋃ j : ℕ, {x | (1 / (m + 1 : ℝ)) ≤ ‖f (n + j) x - g x‖})) := by
    let B : Set (EuclideanSpace' d) := {x | ¬ Filter.atTop.Tendsto (fun k ↦ f k x) (nhds (g x))}
    have hB : IsNull B := by
      simpa [B, PointwiseAeConvergesTo, AlmostAlways] using hfg
    have hsub : (⋂ n : ℕ, (⋃ j : ℕ, {x | (1 / (m + 1 : ℝ)) ≤ ‖f (n + j) x - g x‖})) ⊆ B := by
      intro x hx ht
      have hε : 0 < (1 / (m + 1 : ℝ)) := by positivity
      have hN : ∃ N, ∀ k ≥ N, dist (f k x) (g x) < (1 / (m + 1 : ℝ)) :=
        (Metric.tendsto_atTop.mp ht) (1 / (m + 1 : ℝ)) hε
      rcases hN with ⟨N, hN'⟩
      have hmem : x ∈ ⋃ j : ℕ, {x | (1 / (m + 1 : ℝ)) ≤ ‖f (N + j) x - g x‖} :=
        Set.mem_iInter.mp hx N
      rcases Set.mem_iUnion.mp hmem with ⟨j, hj⟩
      have hlt : ‖f (N + j) x - g x‖ < (1 / (m + 1 : ℝ)) := by
        have hd := hN' (N + j) (Nat.le_add_right N j)
        simpa [dist_eq_norm] using hd
      exact (not_lt_of_ge hj) hlt
    exact IsNull.subset hB hsub

/-- Egorov's theorem on a set of finite measure: uniform convergence outside a small set. -/
theorem egorov_on_finite_set {d:ℕ} {f : ℕ → EuclideanSpace' d → ℂ} {g : EuclideanSpace' d → ℂ}
    (hf : ∀ n, ComplexMeasurable (f n)) (hg : ComplexMeasurable g)
    (hfg : PointwiseAeConvergesTo f g) (A : Set (EuclideanSpace' d))
    (hA : LebesgueMeasurable A) (hAf : Lebesgue_measure A < ⊤)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ E : Set (EuclideanSpace' d), LebesgueMeasurable E ∧ E ⊆ A ∧ Lebesgue_measure E ≤ ε ∧
      UniformlyConvergesToOn f g (A \ E) := by
  let B : ℕ → ℕ → Set (EuclideanSpace' d) := fun m n => A ∩ ⋃ j : ℕ, {x | (1 / (m + 1 : ℝ)) ≤ ‖f (n + j) x - g x‖}
  have hB_meas : ∀ m n, LebesgueMeasurable (B m n) := by
    intro m n
    exact LebesgueMeasurable.inter hA (egorov_bad_set_measurable hf hg n m)
  have hB_mono : ∀ m n, B m (n+1) ⊆ B m n := by
    intro m n x hx
    rcases hx with ⟨hxA, hxbad⟩
    refine ⟨hxA, ?_⟩
    rcases Set.mem_iUnion.mp hxbad with ⟨j, hj⟩
    exact Set.mem_iUnion.mpr ⟨j + 1, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hj⟩
  have hB_fin : ∀ m, ∃ n, Lebesgue_measure (B m n) < ⊤ := by
    intro m
    exact ⟨0, lt_of_le_of_lt (Lebesgue_outer_measure.mono (Set.inter_subset_left)) hAf⟩
  have hB_inter_meas : ∀ m, Lebesgue_measure (⋂ n, B m n) = 0 := by
    intro m
    have hInter_null : IsNull (⋂ n, B m n) :=
      IsNull.subset (egorov_bad_inter_null hfg m) (Set.iInter_mono (fun n => Set.inter_subset_right))
    simpa [Lebesgue_measure] using hInter_null
  have hDMC : ∀ m, Filter.atTop.Tendsto (fun n ↦ Lebesgue_measure (B m n)) (nhds 0) := by
    intro m
    simpa [hB_inter_meas m] using
      (Lebesgue_measure.downward_monotone_convergence (E := B m) (hE := hB_meas m)
        (hmono := hB_mono m) (hfin := hB_fin m))
  have hchoose : ∀ m, ∃ n, Lebesgue_measure (B m n) ≤ (ε / 2^(m+1) : EReal) := by
    intro m
    have hpos : 0 < (ε / 2^(m+1) : EReal) := by
      have hreal : 0 < (ε / 2^(m+1) : ℝ) := div_pos hε (pow_pos (by norm_num) (m + 1))
      rw [show (ε / 2^(m+1) : EReal) = (↑(ε / 2^(m+1) : ℝ) : EReal) by
        rw [EReal.coe_div, EReal.coe_pow]; rfl]
      exact EReal.coe_pos.mpr hreal
    have hev : ∀ᶠ n in Filter.atTop, Lebesgue_measure (B m n) < (ε / 2^(m+1) : EReal) := by
      simpa using (hDMC m) (isOpen_Iio.mem_nhds hpos)
    rcases Filter.eventually_atTop.mp hev with ⟨N, hN⟩
    exact ⟨N, le_of_lt (hN N le_rfl)⟩
  let n₀ : ℕ → ℕ := fun m => Classical.choose (hchoose m)
  have hB_n₀ : ∀ m, Lebesgue_measure (B m (n₀ m)) ≤ (ε / 2^(m+1) : EReal) :=
    fun m => Classical.choose_spec (hchoose m)
  let E : Set (EuclideanSpace' d) := ⋃ m : ℕ, B m (n₀ m)
  have hE_meas : LebesgueMeasurable E := LebesgueMeasurable.countable_union (fun m => hB_meas m (n₀ m))
  have hE_sub : E ⊆ A := by
    intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨m, hm⟩
    exact hm.1
  have hnonneg : ∀ m, 0 ≤ (ε / 2^(m+1) : EReal) := by
    intro m
    have hreal : 0 ≤ (ε / 2^(m+1) : ℝ) := div_nonneg (le_of_lt hε) (le_of_lt (pow_pos (by norm_num) (m + 1)))
    rw [show (ε / 2^(m+1) : EReal) = (↑(ε / 2^(m+1) : ℝ) : EReal) by
      rw [EReal.coe_div, EReal.coe_pow]; rfl]
    exact EReal.coe_nonneg.mpr hreal
  have hE_le : Lebesgue_measure E ≤ ε := by
    calc
      Lebesgue_measure E ≤ ∑' m : ℕ, Lebesgue_measure (B m (n₀ m)) :=
        Lebesgue_outer_measure.union_le (fun m => B m (n₀ m))
      _ ≤ ∑' m : ℕ, (ε / 2^(m+1) : EReal) := by
        rw [EReal.tsum_eq_ennreal_of_nonneg (f := fun m => Lebesgue_measure (B m (n₀ m)))
          (fun m => Lebesgue_outer_measure.nonneg (B m (n₀ m)))]
        rw [EReal.tsum_eq_ennreal_of_nonneg (f := fun m => (ε / 2^(m+1) : EReal)) hnonneg]
        rw [EReal.coe_ennreal_le_coe_ennreal_iff]
        apply ENNReal.tsum_le_tsum
        intro m
        exact EReal.toENNReal_le_toENNReal (hB_n₀ m)
      _ ≤ ε := egorov_tsum_geometric hε
  have hU : UniformlyConvergesToOn f g (A \ E) := by
    rw [UniformlyConvergesToOn, UniformlyConvergesTo]
    intro ε' hε'
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε'
    refine ⟨n₀ m, ?_⟩
    intro n hn x
    have hxnotB : x.val ∉ B m (n₀ m) := fun hb =>
      x.2.2 (Set.subset_iUnion (fun m' => B m' (n₀ m')) m hb)
    have hxnotBad : x.val ∉ ⋃ j : ℕ, {x | (1 / (m + 1 : ℝ)) ≤ ‖f (n₀ m + j) x - g x‖} := by
      intro hbad
      exact hxnotB ⟨x.2.1, hbad⟩
    have hlt : ‖f n x.val - g x.val‖ < 1 / (m + 1 : ℝ) := by
      by_contra hge
      have hge' : (1 / (m + 1 : ℝ)) ≤ ‖f n x.val - g x.val‖ := le_of_not_gt hge
      have hmem : x.val ∈ ⋃ j : ℕ, {x | (1 / (m + 1 : ℝ)) ≤ ‖f (n₀ m + j) x - g x‖} :=
        Set.mem_iUnion.mpr ⟨n - n₀ m, by simpa [Nat.add_sub_of_le hn] using hge'⟩
      exact hxnotBad hmem
    exact le_trans (by simpa [dist_eq_norm] using hlt.le) (le_of_lt hm)
  exact ⟨E, hE_meas, hE_sub, hE_le, hU⟩

/-- The pointwise a.e. limit of complex measurable functions is complex measurable (no boundedness needed). -/
lemma ComplexMeasurable.aeLimit_of_pointwiseAe {d:ℕ} {f : ℕ → EuclideanSpace' d → ℂ} {g : EuclideanSpace' d → ℂ}
    (hf : ∀ n, ComplexMeasurable (f n)) (hfg : PointwiseAeConvergesTo f g) : ComplexMeasurable g := by
  have hre_ae : PointwiseAeConvergesTo (fun n => Complex.re_fun (f n)) (Complex.re_fun g) := by
    apply AlmostAlways.mp hfg
    intro x hx
    exact Complex.continuous_re.continuousAt.tendsto.comp hx
  have him_ae : PointwiseAeConvergesTo (fun n => Complex.im_fun (f n)) (Complex.im_fun g) := by
    apply AlmostAlways.mp hfg
    intro x hx
    exact Complex.continuous_im.continuousAt.tendsto.comp hx
  have hre : RealMeasurable (Complex.re_fun g) := by
    apply ((RealMeasurable_TFAE_helpers.RealMeasurable.TFAE (f := Complex.re_fun g)).out 2 0
      (a := UnsignedMeasurable (EReal.pos_fun (Complex.re_fun g)) ∧
            UnsignedMeasurable (EReal.neg_fun (Complex.re_fun g)))
      (b := RealMeasurable (Complex.re_fun g))).mp
    constructor
    · apply UnsignedMeasurable.aeLimit (fun n => EReal.pos_fun (Complex.re_fun (f n)))
      · intro n
        exact RealMeasurable.measurable_pos ((ComplexMeasurable.iff.mp (hf n)).1)
      · intro x
        simp only [EReal.pos_fun]
        exact EReal.coe_nonneg.mpr (le_max_right _ _)
      · apply AlmostAlways.mp hre_ae
        intro x hx
        exact (continuous_coe_real_ereal.comp (Continuous.max continuous_id continuous_const)).continuousAt.tendsto.comp hx
    · apply UnsignedMeasurable.aeLimit (fun n => EReal.neg_fun (Complex.re_fun (f n)))
      · intro n
        exact RealMeasurable.measurable_neg ((ComplexMeasurable.iff.mp (hf n)).1)
      · intro x
        simp only [EReal.neg_fun]
        exact EReal.coe_nonneg.mpr (le_max_right _ _)
      · apply AlmostAlways.mp hre_ae
        intro x hx
        exact (continuous_coe_real_ereal.comp (Continuous.max continuous_neg continuous_const)).continuousAt.tendsto.comp hx
  have him : RealMeasurable (Complex.im_fun g) := by
    apply ((RealMeasurable_TFAE_helpers.RealMeasurable.TFAE (f := Complex.im_fun g)).out 2 0
      (a := UnsignedMeasurable (EReal.pos_fun (Complex.im_fun g)) ∧
            UnsignedMeasurable (EReal.neg_fun (Complex.im_fun g)))
      (b := RealMeasurable (Complex.im_fun g))).mp
    constructor
    · apply UnsignedMeasurable.aeLimit (fun n => EReal.pos_fun (Complex.im_fun (f n)))
      · intro n
        exact RealMeasurable.measurable_pos ((ComplexMeasurable.iff.mp (hf n)).2)
      · intro x
        simp only [EReal.pos_fun]
        exact EReal.coe_nonneg.mpr (le_max_right _ _)
      · apply AlmostAlways.mp him_ae
        intro x hx
        exact (continuous_coe_real_ereal.comp (Continuous.max continuous_id continuous_const)).continuousAt.tendsto.comp hx
    · apply UnsignedMeasurable.aeLimit (fun n => EReal.neg_fun (Complex.im_fun (f n)))
      · intro n
        exact RealMeasurable.measurable_neg ((ComplexMeasurable.iff.mp (hf n)).2)
      · intro x
        simp only [EReal.neg_fun]
        exact EReal.coe_nonneg.mpr (le_max_right _ _)
      · apply AlmostAlways.mp him_ae
        intro x hx
        exact (continuous_coe_real_ereal.comp (Continuous.max continuous_neg continuous_const)).continuousAt.tendsto.comp hx
  exact ComplexMeasurable.iff.mpr ⟨hre, him⟩

/-- The box with side from -N to N in every coordinate. -/
private def egorov_box (d : ℕ) (N : ℕ) : Box d :=
  Box.mk (fun _ : Fin d => (BoundedInterval.Icc (-(N : ℝ)) (N : ℝ) : BoundedInterval))

/-- The set of points whose coordinates all lie in -N..N. -/
private def egorov_A {d : ℕ} (N : ℕ) : Set (EuclideanSpace' d) := (egorov_box d N).toSet

/-- A box is Lebesgue measurable. -/
private lemma egorov_A_meas {d : ℕ} (N : ℕ) : LebesgueMeasurable (egorov_A (d := d) N) := by
  exact Jordan_measurable.lebesgue (IsElementary.jordanMeasurable (IsElementary.box (egorov_box d N)))

/-- A box has finite Lebesgue measure. -/
private lemma egorov_A_fin {d : ℕ} (N : ℕ) : Lebesgue_measure (egorov_A (d := d) N) < ⊤ := by
  unfold Lebesgue_measure
  rw [Lebesgue_outer_measure.elementary (egorov_A (d := d) N) (IsElementary.box (egorov_box d N))]
  exact EReal.coe_lt_top _

/-- Every bounded set is contained in some box A N. -/
private lemma egorov_bounded_subset_box {d : ℕ} (K : Set (EuclideanSpace' d)) (hK : Bornology.IsBounded K) :
    ∃ N, K ⊆ egorov_A (d := d) N := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : EuclideanSpace' d)).mp hK
  obtain ⟨N, hN⟩ := exists_nat_gt (max R 0)
  refine ⟨N, ?_⟩
  intro x hx
  have hxB : x ∈ Metric.closedBall (0 : EuclideanSpace' d) R := hR hx
  have hxR : ‖x‖ ≤ max R 0 := by
    have hd : dist x 0 ≤ R := Metric.mem_closedBall.mp hxB
    simpa [dist_eq_norm] using le_trans hd (le_max_left R 0)
  have hxN : ‖x‖ ≤ (N : ℝ) := le_trans hxR (le_of_lt hN)
  intro i
  have hcoord : |x i| ≤ ‖x‖ := EuclideanSpace'.coord_le_norm x i
  simpa [egorov_A, egorov_box, Box.mem_toSet, BoundedInterval.set_Icc] using
    (Set.mem_Icc.mpr (abs_le.mp (le_trans hcoord hxN)))

/-- The image of a bounded subset of a subspace under the coercion is bounded. -/
private lemma egorov_bounded_image {d : ℕ} {S : Set (EuclideanSpace' d)} (K : Set {x : EuclideanSpace' d // x ∈ S})
    (hK : Bornology.IsBounded K) : Bornology.IsBounded (Subtype.val '' K) := by
  by_cases hS : Nonempty {x : EuclideanSpace' d // x ∈ S}
  · rcases hS with ⟨z₀⟩
    rcases (Metric.isBounded_iff_subset_closedBall (z₀ : {x : EuclideanSpace' d // x ∈ S})).mp hK with ⟨R, hR⟩
    rw [Metric.isBounded_iff_subset_closedBall (z₀.val : EuclideanSpace' d)]
    refine ⟨R, ?_⟩
    intro y hy
    rcases hy with ⟨w, hw, rfl⟩
    have hwB : w ∈ Metric.closedBall (z₀ : {x : EuclideanSpace' d // x ∈ S}) R := hR hw
    exact Metric.mem_closedBall.mpr (by simpa [Subtype.dist_eq] using (Metric.mem_closedBall.mp hwB))
  · rw [Metric.isBounded_iff_subset_closedBall (0 : EuclideanSpace' d)]
    refine ⟨0, ?_⟩
    intro y hy
    rcases hy with ⟨w, hw, rfl⟩
    exact False.elim (hS ⟨w⟩)

/-- Theorem 1.3.26 (Egorov's theorem) -/
theorem PointwiseAeConvergesTo.locallyUniformlyConverges_outside_small {d:ℕ} {f : ℕ → EuclideanSpace' d → ℂ} {g : EuclideanSpace' d → ℂ}
  (hf: ∀ n, ComplexMeasurable (f n))
  (hfg: PointwiseAeConvergesTo f g)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (E: Set (EuclideanSpace' d)), LebesgueMeasurable E ∧
    Lebesgue_measure E ≤ ε ∧
    LocallyUniformlyConvergesToOn f g Eᶜ := by
  have hg : ComplexMeasurable g := ComplexMeasurable.aeLimit_of_pointwiseAe hf hfg
  let hchain : ∀ N : ℕ, ∃ E : Set (EuclideanSpace' d), LebesgueMeasurable E ∧ E ⊆ egorov_A (d := d) N ∧
      Lebesgue_measure E ≤ (↑(ε / 2^(N+1) : ℝ) : EReal) ∧ UniformlyConvergesToOn f g (egorov_A (d := d) N \ E) :=
    fun N => egorov_on_finite_set hf hg hfg (egorov_A (d := d) N) (egorov_A_meas N) (egorov_A_fin N)
      (ε / 2^(N+1)) (div_pos hε (pow_pos (by norm_num) (N+1)))
  let E_N : ℕ → Set (EuclideanSpace' d) := fun N => Classical.choose (hchain N)
  have hEN_spec : ∀ N, LebesgueMeasurable (E_N N) ∧ E_N N ⊆ egorov_A (d := d) N ∧
      Lebesgue_measure (E_N N) ≤ (↑(ε / 2^(N+1) : ℝ) : EReal) ∧
      UniformlyConvergesToOn f g (egorov_A (d := d) N \ E_N N) :=
    fun N => Classical.choose_spec (hchain N)
  have hEN_meas : ∀ N, LebesgueMeasurable (E_N N) := fun N => (hEN_spec N).1
  have hEN_le : ∀ N, Lebesgue_measure (E_N N) ≤ (ε / 2^(N+1) : EReal) := by
    intro N
    rw [show (ε / 2^(N+1) : EReal) = (↑(ε / 2^(N+1) : ℝ) : EReal) by
      rw [EReal.coe_div, EReal.coe_pow]; rfl]
    exact (hEN_spec N).2.2.1
  have hEN_conv : ∀ N, UniformlyConvergesTo
      (fun n (x : {x : EuclideanSpace' d // x ∈ egorov_A (d := d) N \ E_N N}) ↦ f n x.val)
      (fun x ↦ g x.val) := by
    intro N
    exact (hEN_spec N).2.2.2
  let E : Set (EuclideanSpace' d) := ⋃ N : ℕ, E_N N
  have hE_meas : LebesgueMeasurable E := LebesgueMeasurable.countable_union hEN_meas
  have hnonneg : ∀ N, 0 ≤ (ε / 2^(N+1) : EReal) := by
    intro N
    have hreal : 0 ≤ (ε / 2^(N+1) : ℝ) := div_nonneg (le_of_lt hε) (le_of_lt (pow_pos (by norm_num) (N + 1)))
    rw [show (ε / 2^(N+1) : EReal) = (↑(ε / 2^(N+1) : ℝ) : EReal) by
      rw [EReal.coe_div, EReal.coe_pow]; rfl]
    exact EReal.coe_nonneg.mpr hreal
  have hE_le : Lebesgue_measure E ≤ ε := by
    calc
      Lebesgue_measure E ≤ ∑' N : ℕ, Lebesgue_measure (E_N N) :=
        Lebesgue_outer_measure.union_le (fun N => E_N N)
      _ ≤ ∑' N : ℕ, (ε / 2^(N+1) : EReal) := by
        rw [EReal.tsum_eq_ennreal_of_nonneg (f := fun N => Lebesgue_measure (E_N N))
          (fun N => Lebesgue_outer_measure.nonneg (E_N N))]
        rw [EReal.tsum_eq_ennreal_of_nonneg (f := fun N => (ε / 2^(N+1) : EReal)) hnonneg]
        rw [EReal.coe_ennreal_le_coe_ennreal_iff]
        apply ENNReal.tsum_le_tsum
        intro N
        exact EReal.toENNReal_le_toENNReal (hEN_le N)
      _ ≤ ε := egorov_tsum_geometric hε
  have hLU : LocallyUniformlyConvergesToOn f g Eᶜ := by
    unfold LocallyUniformlyConvergesToOn LocallyUniformlyConvergesTo UniformlyConvergesToOn UniformlyConvergesTo
    intro K hK ε' hε'
    have hKimg : Bornology.IsBounded (Subtype.val '' K) := egorov_bounded_image (S := Eᶜ) K hK
    obtain ⟨N, hKN⟩ := egorov_bounded_subset_box (Subtype.val '' K) hKimg
    obtain ⟨N₀, hN₀⟩ := hEN_conv N ε' hε'
    refine ⟨N₀, ?_⟩
    intro n hn x
    have hxA : x.val.val ∈ egorov_A (d := d) N :=
      hKN ((Set.mem_image Subtype.val K x.val.val).mpr ⟨x.val, x.2, rfl⟩)
    have hxnotEN : x.val.val ∉ E_N N := fun hmem => x.val.2 (Set.subset_iUnion (fun N' => E_N N') N hmem)
    exact hN₀ n hn ⟨x.val.val, ⟨hxA, hxnotEN⟩⟩
  exact ⟨E, hE_meas, hE_le, hLU⟩

/-- The exceptional set in Egorov's theorem cannot be taken to be null -/
example : ∃ (d:ℕ) (f : ℕ → EuclideanSpace' d → ℝ) (g : EuclideanSpace' d → ℝ),
    (∀ n, RealMeasurable (f n)) ∧
    PointwiseAeConvergesTo f g ∧
    ∀ (E: Set (EuclideanSpace' d)), LebesgueMeasurable E ∧
      Lebesgue_measure E = 0 →
      ¬ LocallyUniformlyConvergesToOn f g Eᶜ := by sorry

/-- Remark 1.3.27: Local uniform convergence in Egorov's theorem cannot be upgraded to uniform convergence -/
example : ∃ (d:ℕ) (f : ℕ → EuclideanSpace' d → ℝ) (g : EuclideanSpace' d → ℝ),
    (∀ n, RealMeasurable (f n)) ∧
    PointwiseAeConvergesTo f g ∧
    ∃ (ε : ℝ) (hε : 0 < ε),
      ∀ (E: Set (EuclideanSpace' d)), LebesgueMeasurable E ∧
        Lebesgue_measure E ≤ ε →
        ¬ UniformlyConvergesToOn f g Eᶜ := by sorry

/-- But uniform convergence can be recovered on a fixed set of finite measure -/
theorem PointwiseAeConvergesTo.uniformlyConverges_outside_small {d:ℕ} {f : ℕ → EuclideanSpace' d → ℂ} {g : EuclideanSpace' d → ℂ}
  (hf: ∀ n, ComplexMeasurable (f n))
  (hfg: PointwiseAeConvergesTo f g)
  (S: Set (EuclideanSpace' d))
  (hSm: LebesgueMeasurable S)
  (hS: Lebesgue_measure S < ⊤)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (E: Set (EuclideanSpace' d)), LebesgueMeasurable E ∧ E ⊆ S ∧
    Lebesgue_measure E ≤ ε ∧
    UniformlyConvergesToOn f g (S \ E) := by
  exact egorov_on_finite_set hf (ComplexMeasurable.aeLimit_of_pointwiseAe hf hfg) hfg S hSm hS ε hε

/-- Theorem 1.3.28 (Lusin's theorem) -/
theorem ComplexAbsolutelyIntegrable.approx_by_continuous_outside_small {d:ℕ} {f : EuclideanSpace' d → ℂ}
  (hf: ComplexAbsolutelyIntegrable f)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (g : EuclideanSpace' d → ℂ) (E: Set (EuclideanSpace' d)), ContinuousOn g Eᶜ ∧ LebesgueMeasurable E ∧
      Lebesgue_measure E ≤ ε ∧
      ∀ x ∉ E, g x = f x := by sorry

/-- Lusin's theorem does not make the original function continuous outside of E -/
example : ∃ (d:ℕ) (f : EuclideanSpace' d → ℝ),
    RealMeasurable f ∧
    ∀ (E: Set (EuclideanSpace' d)), LebesgueMeasurable E → Lebesgue_measure E ≤ 1 →
      ¬ ∀ x ∈ Eᶜ, ContinuousAt f x := by sorry

def LocallyComplexAbsolutelyIntegrable {d:ℕ} (f: EuclideanSpace' d → ℂ) : Prop :=
  ∀ (S: Set (EuclideanSpace' d)), LebesgueMeasurable S ∧ Bornology.IsBounded S → ComplexAbsolutelyIntegrableOn f S

/-- Exercise 1.3.23 (Lusin's theorem only requires local absolute integrability ). -/
theorem LocallyComplexAbsolutelyIntegrable.approx_by_continuous_outside_small {d:ℕ} {f : EuclideanSpace' d → ℂ}
  (hf: LocallyComplexAbsolutelyIntegrable f)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (g : EuclideanSpace' d → ℂ) (E: Set (EuclideanSpace' d)), ContinuousOn g Eᶜ ∧ LebesgueMeasurable E ∧
      Lebesgue_measure E ≤ ε ∧
      ∀ x ∉ E, g x = f x := by sorry

theorem ComplexMeasurable.approx_by_continuous_outside_small {d:ℕ} {f : EuclideanSpace' d → ℂ}
  (hf: ComplexMeasurable f)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (g : EuclideanSpace' d → ℂ) (E: Set (EuclideanSpace' d)), ContinuousOn g Eᶜ ∧ LebesgueMeasurable E ∧
      Lebesgue_measure E ≤ ε ∧
      ∀ x ∉ E, g x = f x := by sorry

/-- Exercise 1.3.24 -/
theorem ComplexMeasurable.iff_pointwiseae_of_continuous {d:ℕ} {f : EuclideanSpace' d → ℂ} :
  ComplexMeasurable f ↔
  ∃ (g : ℕ → EuclideanSpace' d → ℂ), (∀ n, Continuous (g n)) ∧ PointwiseAeConvergesTo g f := by sorry

/-- Remark 1.3.29 -/
theorem UnsignedMeasurable.approx_by_continuous_outside_small {d:ℕ} {f : EuclideanSpace' d → EReal}
  (hf: UnsignedMeasurable f) (hfin: AlmostAlways (fun x ↦ f x < ⊤))
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (g : EuclideanSpace' d → ℝ) (E: Set (EuclideanSpace' d)), ContinuousOn g Eᶜ ∧ LebesgueMeasurable E ∧
      Lebesgue_measure E ≤ ε ∧
      ∀ x ∉ E, g x = f x := by sorry

lemma ComplexAbsolutelyIntegrable.chebyshev {d:ℕ} {f : EuclideanSpace' d → ℂ} (hf : ComplexAbsolutelyIntegrable f)
    (η : ℝ) (hη : 0 < η) :
    Lebesgue_measure {x | (η : ℝ) ≤ ‖f x‖} ≤
      ((η : ℝ)⁻¹ : EReal) * UnsignedLebesgueIntegral (EReal.abs_fun f) := by
  let E : Set (EuclideanSpace' d) := {x | (η : ℝ) ≤ ‖f x‖}
  have hE_meas : LebesgueMeasurable E := by
    have hEq : E = f ⁻¹' {z : ℂ | (η : ℝ) ≤ ‖z‖} := by
      ext x
      rfl
    rw [hEq]
    exact ComplexMeasurable.preimage_closed hf.1
      (by simpa using (IsClosed.preimage continuous_norm (isClosed_Ici (a := η))))
  have hE_simple : UnsignedSimpleFunction (EReal.indicator E) := UnsignedSimpleFunction.indicator hE_meas
  have hc : (0 : EReal) ≤ (η : EReal) := EReal.coe_nonneg.mpr (le_of_lt hη)
  have h_pw : ∀ x, ((η : EReal) • EReal.indicator E) x ≤ EReal.abs_fun f x := by
    intro x
    by_cases hx : x ∈ E
    · rw [Pi.smul_apply, smul_eq_mul, EReal.indicator_of_mem hx, mul_one]
      simp only [EReal.abs_fun]
      exact EReal.coe_le_coe_iff.mpr (by simpa [E] using hx)
    · rw [Pi.smul_apply, smul_eq_mul, EReal.indicator_of_notMem hx, mul_zero]
      simp only [EReal.abs_fun]
      exact EReal.coe_nonneg.mpr (norm_nonneg (f x))
  have hmono : LowerUnsignedLebesgueIntegral ((η : EReal) • EReal.indicator E) ≤
      UnsignedLebesgueIntegral (EReal.abs_fun f) :=
    LowerUnsignedLebesgueIntegral.mono
      (hE_simple.smul hc).unsignedMeasurable
      hf.abs.1
      (AlmostAlways.ofAlways h_pw)
  have hinteg : LowerUnsignedLebesgueIntegral ((η : EReal) • EReal.indicator E) =
      (η : EReal) * Lebesgue_measure E := by
    rw [LowerUnsignedLebesgueIntegral.eq_simpleIntegral (hE_simple.smul hc)]
    rw [UnsignedSimpleFunction.integral_smul hE_simple hc]
    exact congrArg (fun z => (η : EReal) * z) (UnsignedSimpleFunction.integral_indicator hE_meas)
  have hηm : (η : EReal) * Lebesgue_measure E ≤ UnsignedLebesgueIntegral (EReal.abs_fun f) := by
    rw [← hinteg]
    exact hmono
  have hinv : (0 : EReal) ≤ ((η : ℝ)⁻¹ : EReal) := EReal.coe_nonneg.mpr (inv_nonneg.mpr (le_of_lt hη))
  have hle' : ((η : ℝ)⁻¹ : EReal) * ((η : EReal) * Lebesgue_measure E) ≤
      ((η : ℝ)⁻¹ : EReal) * UnsignedLebesgueIntegral (EReal.abs_fun f) := by
    exact mul_le_mul_of_nonneg_left hηm hinv
  have hLHS : ((η : ℝ)⁻¹ : EReal) * ((η : EReal) * Lebesgue_measure E) = Lebesgue_measure E := by
    rw [← mul_assoc]
    have hinv_mul : ((η : ℝ)⁻¹ : EReal) * (η : EReal) = 1 := by
      rw [← EReal.coe_inv, ← EReal.coe_mul, inv_mul_cancel₀ (ne_of_gt hη), EReal.coe_one]
    rw [hinv_mul, one_mul]
  simpa [E, hLHS] using hle'

/-- Multiplying an unsigned simple function by an indicator gives an unsigned simple function. -/
lemma UnsignedSimpleFunction.mul_indicator {d:ℕ} {g : EuclideanSpace' d → EReal} (hg : UnsignedSimpleFunction g)
    {E : Set (EuclideanSpace' d)} (hE : LebesgueMeasurable E) :
    UnsignedSimpleFunction (fun x => g x * EReal.indicator E x) := by
  rcases hg with ⟨k, c, F, hcond, heq⟩
  set E' : Fin k → Set (EuclideanSpace' d) := fun i => F i ∩ E with hE'_def
  refine ⟨k, c, E', fun i => ⟨LebesgueMeasurable.inter (hcond i).1 hE, (hcond i).2⟩, ?_⟩
  ext x
  rw [heq]
  by_cases hxE : x ∈ E
  · rw [EReal.indicator_of_mem hxE, mul_one]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply congrArg (fun y : EReal => c i * y)
    by_cases hx : x ∈ F i
    · rw [EReal.indicator_of_mem hx, EReal.indicator_of_mem (by exact ⟨hx, hxE⟩)]
    · rw [EReal.indicator_of_notMem hx, EReal.indicator_of_notMem (by exact fun h => hx h.1)]
  · rw [EReal.indicator_of_notMem hxE, mul_zero]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Eq.symm
    apply Finset.sum_eq_zero
    intro i _
    rw [EReal.indicator_of_notMem (by exact fun h => hxE h.2), mul_zero]

/-- Multiplying an unsigned measurable function by an indicator gives an unsigned measurable function. -/
lemma UnsignedMeasurable.mul_indicator {d:ℕ} {f : EuclideanSpace' d → EReal} (hf : UnsignedMeasurable f)
    {E : Set (EuclideanSpace' d)} (hE : LebesgueMeasurable E) :
    UnsignedMeasurable (fun x => f x * EReal.indicator E x) := by
  constructor
  · intro x
    exact mul_nonneg (hf.1 x) (EReal.indicator_nonneg E x)
  · obtain ⟨g, hg_simple, hg_conv⟩ := hf.2
    refine ⟨fun n => fun x => g n x * EReal.indicator E x, ?_, ?_⟩
    · intro n
      exact UnsignedSimpleFunction.mul_indicator (hg_simple n) hE
    · intro x
      by_cases hxE : x ∈ E
      · simpa [EReal.indicator_of_mem hxE] using hg_conv x
      · simp [EReal.indicator_of_notMem hxE]

/-- The measure of the part of a finite-measure set outside a large ball tends to zero. -/
lemma ball_complement_measure_tendsto_zero {d:ℕ} {E : Set (EuclideanSpace' d)} (hE : LebesgueMeasurable E)
    (hEf : Lebesgue_measure E < ⊤) :
    Filter.atTop.Tendsto (fun n : ℕ =>
      Lebesgue_measure (E ∩ (Metric.ball (0 : EuclideanSpace' d) (n : ℝ))ᶜ)) (nhds 0) := by
  let B : ℕ → Set (EuclideanSpace' d) := fun n => E ∩ (Metric.ball (0 : EuclideanSpace' d) (n : ℝ))ᶜ
  have hB_meas : ∀ n, LebesgueMeasurable (B n) := by
    intro n
    dsimp [B]
    exact hE.inter ((IsOpen.measurable (Metric.isOpen_ball)).complement)
  have hB_mono : ∀ n, B (n + 1) ⊆ B n := by
    intro n x hx
    dsimp [B] at hx ⊢
    exact ⟨hx.1, fun hb => hx.2 (Metric.ball_subset_ball (by norm_num : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ)) hb)⟩
  have hB_fin : ∃ n, Lebesgue_measure (B n) < ⊤ := by
    refine ⟨0, ?_⟩
    dsimp [B]
    exact lt_of_le_of_lt (Lebesgue_outer_measure.mono (Set.inter_subset_left)) hEf
  have hconv : Tendsto (fun n => Lebesgue_measure (B n)) atTop (nhds (Lebesgue_measure (⋂ n, B n))) :=
    Lebesgue_measure.downward_monotone_convergence hB_meas hB_mono hB_fin
  have hB_inter : ⋂ n, B n = ∅ := by
    ext x
    constructor
    · intro hx
      have hx_mem : ∀ n, x ∈ B n := Set.mem_iInter.mp hx
      obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
      have hxn : x ∈ Metric.ball (0 : EuclideanSpace' d) (n : ℝ) := by
        simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hn
      exact (hx_mem n).2 hxn
    · intro hx
      simp at hx
  have hB_empty_meas : Lebesgue_measure (⋂ n, B n) = 0 := by
    simp [hB_inter]
  change Tendsto (fun n => Lebesgue_measure (B n)) atTop (nhds 0)
  simpa [hB_empty_meas] using hconv

private lemma coe_sum_eq_sum_coe {n : ℕ} (a : Fin n → ℝ) :
    (↑(∑ i, a i) : EReal) = ∑ i, (↑(a i) : EReal) := by
  induction n with
  | zero => simp [Finset.univ_eq_empty]
  | succ m ih =>
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, EReal.coe_add]
    congr 1
    exact ih (fun i => a i.castSucc)

/-- The tail measure of a finite-measure set, scaled by a nonneg scalar, tends to zero. -/
private lemma coe_mul_ball_complement_tendsto_zero {d:ℕ} {E : Set (EuclideanSpace' d)} {c : ℝ}
    (hE : LebesgueMeasurable E) (hEf : Lebesgue_measure E < ⊤) (_hc : 0 ≤ c) :
    Filter.atTop.Tendsto (fun n : ℕ =>
      (c : EReal) * Lebesgue_measure (E ∩ (Metric.ball (0 : EuclideanSpace' d) (n : ℝ))ᶜ)) (nhds 0) := by
  have h := ball_complement_measure_tendsto_zero hE hEf
  have hmul := EReal.Tendsto.mul_const
    (m := fun n : ℕ => Lebesgue_measure (E ∩ (Metric.ball (0 : EuclideanSpace' d) (n : ℝ))ᶜ))
    (a := 0) (b := (c : EReal)) h
    (Or.inr (EReal.coe_ne_bot c)) (Or.inr (EReal.coe_ne_top c))
  simpa [mul_comm] using hmul

/-- The tail integral of a real simple function equals the sum of per-atom tail measures. -/
private lemma real_simple_tail_integral_eq {d:ℕ} {g : EuclideanSpace' d → ℝ} {k : ℕ} {c : Fin k → ℝ}
    {E : Fin k → Set (EuclideanSpace' d)} (hg_eq : g = ∑ i, c i • (E i).indicator')
    (hmes : ∀ i, LebesgueMeasurable (E i)) (hc_nn : ∀ i, 0 ≤ c i) (R : ℝ) :
    UnsignedLebesgueIntegral
      (fun x => (g x : EReal) * EReal.indicator (Metric.ball (0 : EuclideanSpace' d) R)ᶜ x) =
      ∑ i, (c i : EReal) * Lebesgue_measure (E i ∩ (Metric.ball (0 : EuclideanSpace' d) R)ᶜ) := by
  let B : Set (EuclideanSpace' d) := (Metric.ball (0 : EuclideanSpace' d) R)ᶜ
  have hB_meas : LebesgueMeasurable B := (IsOpen.measurable (Metric.isOpen_ball)).complement
  have hgE_eq : (fun x => g x * B.indicator' x) = ∑ i, c i • (E i ∩ B).indicator' := by
    ext x
    rw [hg_eq]
    by_cases hx : x ∈ B
    · rw [Set.indicator'_of_mem hx, mul_one]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      by_cases hxi : x ∈ E i
      · rw [Set.indicator'_of_mem hxi, Set.indicator'_of_mem (by exact ⟨hxi, hx⟩)]
      · rw [Set.indicator'_of_notMem hxi, Set.indicator'_of_notMem (by intro h; exact hxi h.1)]
    · rw [Set.indicator'_of_notMem hx, mul_zero]
      symm
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_eq_zero (s := Finset.univ) (f := fun i => c i * (E i ∩ B).indicator' x) (by
        intro i _
        simp only
        rw [Set.indicator'_of_notMem (by intro h; exact hx h.2)]
        ring)
  have hElift : (fun x => (g x : EReal) * EReal.indicator B x) =
      ∑ i : Fin k, (c i : EReal) • EReal.indicator (E i ∩ B) := by
    ext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, EReal.indicator, Real.EReal_fun]
    rw [← EReal.coe_mul]
    simp only [← EReal.coe_mul]
    rw [← coe_sum_eq_sum_coe (fun i => c i * (E i ∩ B).indicator' x)]
    congr 1
    have hxeq := congrFun hgE_eq x
    simpa [Pi.smul_apply, smul_eq_mul] using hxeq
  have hElift_simple : UnsignedSimpleFunction (fun x => (g x : EReal) * EReal.indicator B x) :=
    ⟨k, (fun i => (c i : EReal)), (fun i => E i ∩ B),
      fun i => ⟨LebesgueMeasurable.inter (hmes i) hB_meas, EReal.coe_nonneg.mpr (hc_nn i)⟩, hElift⟩
  rw [show (fun x => (g x : EReal) * EReal.indicator (Metric.ball (0 : EuclideanSpace' d) R)ᶜ x) =
      fun x => (g x : EReal) * EReal.indicator B x from rfl]
  rw [UnsignedLebesgueIntegral, LowerUnsignedLebesgueIntegral.eq_simpleIntegral hElift_simple]
  rw [UnsignedSimpleFunction.integral_eq hElift_simple (k := k) (c := fun i => (c i : EReal))
    (E := fun i => E i ∩ B) (hmes := fun i => LebesgueMeasurable.inter (hmes i) hB_meas)
    (hnonneg := fun i => EReal.coe_nonneg.mpr (hc_nn i)) (heq := hElift)]

/-- The tail of a finite-integral nonneg-coefficient real simple function outside a large ball is small. -/
private lemma real_simple_tail_integral_small {d:ℕ} {g : EuclideanSpace' d → ℝ} {k : ℕ} {c : Fin k → ℝ}
    {E : Fin k → Set (EuclideanSpace' d)} (hg_eq : g = ∑ i, c i • (E i).indicator')
    (hmes : ∀ i, LebesgueMeasurable (E i)) (hc_nn : ∀ i, 0 ≤ c i)
    (hfin : UnsignedLebesgueIntegral (fun x => (g x : EReal)) < ⊤) (δ : ℝ) (hδ : 0 < δ) :
    ∃ R : ℝ, UnsignedLebesgueIntegral
      (fun x => (g x : EReal) * EReal.indicator (Metric.ball (0 : EuclideanSpace' d) R)ᶜ x) ≤ δ := by
  have hg_meas : UnsignedMeasurable (fun x => (g x : EReal)) := by
    constructor
    · intro x
      exact EReal.coe_nonneg.mpr (by
        rw [hg_eq]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        exact Finset.sum_nonneg (fun j _ => mul_nonneg (hc_nn j) (Set.indicator_nonneg (fun _ _ => zero_le_one) x)))
    · refine ⟨fun _ => fun x => (g x : EReal), ?_, ?_⟩
      · intro n
        refine ⟨k, (fun i => (c i : EReal)), E, fun i => ⟨hmes i, EReal.coe_nonneg.mpr (hc_nn i)⟩, ?_⟩
        ext x
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, EReal.indicator, Real.EReal_fun]
        simp only [← EReal.coe_mul]
        rw [← coe_sum_eq_sum_coe (fun i => c i * (E i).indicator' x)]
        congr 1
        simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congrFun hg_eq x
      · intro x
        exact tendsto_const_nhds
  have hthin (i : Fin k) : (c i : EReal) * Lebesgue_measure (E i) < ⊤ := by
    have h_pw : ∀ x, ((c i : EReal) * EReal.indicator (E i) x) ≤ (g x : EReal) := by
      intro x
      rw [hg_eq]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, EReal.indicator, Real.EReal_fun]
      rw [coe_sum_eq_sum_coe (fun j => c j * (E j).indicator' x)]
      simp only [← EReal.coe_mul]
      exact Finset.single_le_sum (s := Finset.univ) (a := i)
        (f := fun j => (c j : EReal) * EReal.indicator (E j) x)
        (fun j _ => mul_nonneg (EReal.coe_nonneg.mpr (hc_nn j)) (EReal.indicator_nonneg (E j) x))
        (Finset.mem_univ i)
    have hs_i : UnsignedSimpleFunction (fun x => (c i : EReal) * EReal.indicator (E i) x) :=
      ⟨1, (fun _ : Fin 1 => (c i : EReal)), (fun _ : Fin 1 => E i),
        fun j => ⟨hmes i, EReal.coe_nonneg.mpr (hc_nn i)⟩,
        by ext x; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_one]⟩
    have hmono : LowerUnsignedLebesgueIntegral (fun x => (c i : EReal) * EReal.indicator (E i) x) ≤
        UnsignedLebesgueIntegral (fun x => (g x : EReal)) :=
      LowerUnsignedLebesgueIntegral.mono (UnsignedSimpleFunction.measurable hs_i (by
        intro x
        exact mul_nonneg (EReal.coe_nonneg.mpr (hc_nn i)) (EReal.indicator_nonneg (E i) x)))
        hg_meas (AlmostAlways.ofAlways h_pw)
    calc (c i : EReal) * Lebesgue_measure (E i)
        = LowerUnsignedLebesgueIntegral (fun x => (c i : EReal) * EReal.indicator (E i) x) := by
            rw [LowerUnsignedLebesgueIntegral.eq_simpleIntegral hs_i]
            rw [UnsignedSimpleFunction.integral_eq hs_i (k := 1) (c := fun _ : Fin 1 => (c i : EReal))
              (E := fun _ : Fin 1 => E i) (hmes := fun _ => hmes i)
              (hnonneg := fun _ => EReal.coe_nonneg.mpr (hc_nn i))
              (heq := by ext x; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_one])]
            simp
      _ ≤ UnsignedLebesgueIntegral (fun x => (g x : EReal)) := hmono
      _ < ⊤ := hfin
  have hEi_fin (i : Fin k) (hci : c i ≠ 0) : Lebesgue_measure (E i) < ⊤ := by
    have hcpos : 0 < c i := lt_of_le_of_ne (hc_nn i) (Ne.symm hci)
    by_contra htop
    have hmt : Lebesgue_measure (E i) = ⊤ := by
      by_contra hne
      exact htop (lt_of_le_of_ne (le_top : Lebesgue_measure (E i) ≤ ⊤) hne)
    have hprod : (c i : EReal) * Lebesgue_measure (E i) = ⊤ := by
      rw [hmt]
      exact EReal.mul_top_of_pos (EReal.coe_pos.mpr hcpos)
    exact (lt_irrefl ⊤) (hprod ▸ hthin i)
  have hterm (i : Fin k) : Tendsto (fun n : ℕ =>
      (c i : EReal) * Lebesgue_measure (E i ∩ (Metric.ball (0 : EuclideanSpace' d) (n : ℝ))ᶜ)) atTop (nhds 0) := by
    by_cases hci : c i = 0
    · simp [hci]
    · exact coe_mul_ball_complement_tendsto_zero (hmes i) (hEi_fin i hci) (hc_nn i)
  have hterm_lt (n : ℕ) (i : Fin k) :
      (c i : EReal) * Lebesgue_measure (E i ∩ (Metric.ball (0 : EuclideanSpace' d) (n : ℝ))ᶜ) < ⊤ := by
    by_cases hci : c i = 0
    · simp [hci]
    · exact lt_of_le_of_lt
        (mul_le_mul_of_nonneg_left
          (Lebesgue_outer_measure.mono (Set.inter_subset_left)) (EReal.coe_nonneg.mpr (hc_nn i)))
        (hthin i)
  have hsum_lt_top : ∀ n : ℕ, (∑ i : Fin k,
      (c i : EReal) * Lebesgue_measure (E i ∩ (Metric.ball (0 : EuclideanSpace' d) (n : ℝ))ᶜ)) < ⊤ := by
    intro n
    have hgoal : (∑ i ∈ (Finset.univ : Finset (Fin k)),
        (c i : EReal) * Lebesgue_measure (E i ∩ (Metric.ball (0 : EuclideanSpace' d) (n : ℝ))ᶜ)) < ⊤ := by
      refine Finset.induction_on (s := Finset.univ) ?_ ?_
      · simp
      · intro i s his ih
        rw [Finset.sum_insert his]
        exact EReal.add_lt_top (ne_of_lt (hterm_lt n i)) (ne_of_lt ih)
    simpa using hgoal
  have hsum : Tendsto (fun n : ℕ => ∑ i : Fin k,
      (c i : EReal) * Lebesgue_measure (E i ∩ (Metric.ball (0 : EuclideanSpace' d) (n : ℝ))ᶜ)) atTop (nhds 0) := by
    rw [tendsto_order]
    constructor
    · intro b hb
      filter_upwards [] with n
      exact lt_of_lt_of_le hb (Finset.sum_nonneg (fun i _ =>
        mul_nonneg (EReal.coe_nonneg.mpr (hc_nn i)) (Lebesgue_outer_measure.nonneg _)))
    · intro b hb
      rcases b with _ | r
      · exact (False.elim (not_lt_of_ge (bot_le : (⊥ : EReal) ≤ 0) hb))
      · rcases r with _ | r
        · filter_upwards [] with n
          exact hsum_lt_top n
        · have hr : 0 < r := EReal.coe_pos.mp hb
          by_cases hk : k = 0
          · subst hk
            filter_upwards [] with n
            simp
            exact hb
          · have hkpos : 0 < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
            have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkpos
            have hk1pos : 0 < (k + 1 : ℝ) := by positivity
            let t : EReal := (r / (k + 1 : ℝ) : EReal)
            have ht : 0 < t := EReal.coe_pos.mpr (div_pos hr hk1pos)
            have hsmall (i : Fin k) : ∀ᶠ n : ℕ in Filter.atTop,
                (c i : EReal) * Lebesgue_measure (E i ∩ (Metric.ball (0 : EuclideanSpace' d) (n : ℝ))ᶜ) < t :=
              (hterm i).eventually (isOpen_Iio.mem_nhds ht)
            have hall : ∀ᶠ n : ℕ in Filter.atTop, ∀ i : Fin k,
                (c i : EReal) * Lebesgue_measure (E i ∩ (Metric.ball (0 : EuclideanSpace' d) (n : ℝ))ᶜ) < t :=
              Filter.eventually_all.mpr (fun i => hsmall i)
            refine hall.mono ?_
            intro n hn
            calc (∑ i : Fin k, (c i : EReal) * Lebesgue_measure (E i ∩ (Metric.ball (0 : EuclideanSpace' d) (n : ℝ))ᶜ))
                ≤ ∑ i : Fin k, t := Finset.sum_le_sum (fun i _ => le_of_lt (hn i))
              _ < (r : EReal) := by
                  have ht : t = (↑(r / (k + 1 : ℝ)) : EReal) := by rfl
                  rw [ht, ← coe_sum_eq_sum_coe (fun _ : Fin k => r / (k + 1 : ℝ))]
                  apply EReal.coe_lt_coe_iff.mpr
                  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
                  have hk1 : (k + 1 : ℝ) ≠ 0 := by positivity
                  have hk1pos : 0 < (k + 1 : ℝ) := by positivity
                  calc (k : ℝ) * (r / (k + 1 : ℝ))
                      = (k : ℝ) * r / (k + 1 : ℝ) := by rw [← mul_div_assoc]
                    _ < (k + 1 : ℝ) * r / (k + 1 : ℝ) := by
                        apply div_lt_div_of_pos_right _ hk1pos
                        nlinarith [hr]
                    _ = r := by
                        simpa [mul_comm] using (mul_div_cancel_right₀ (a := r) (b := (k + 1 : ℝ)) hk1)
  have hδe : 0 < (δ : EReal) := EReal.coe_pos.mpr hδ
  have hev : ∀ᶠ n : ℕ in Filter.atTop,
      (∑ i : Fin k, (c i : EReal) * Lebesgue_measure (E i ∩ (Metric.ball (0 : EuclideanSpace' d) (n : ℝ))ᶜ)) < (δ : EReal) :=
    hsum.eventually (isOpen_Iio.mem_nhds hδe)
  rcases Filter.eventually_atTop.mp hev with ⟨N, hN⟩
  refine ⟨(N : ℝ), ?_⟩
  rw [real_simple_tail_integral_eq hg_eq hmes hc_nn (N : ℝ)]
  exact le_of_lt (hN N le_rfl)

/-- The difference of a real measurable function and a smaller unsigned simple function is unsigned measurable. -/
lemma real_measurable_sub_unsigned {d:ℕ} {φ : EuclideanSpace' d → ℝ} {g : EuclideanSpace' d → EReal}
    (hφ : RealMeasurable φ) (hg : UnsignedSimpleFunction g) (hle : ∀ x, g x ≤ (φ x : EReal)) :
    UnsignedMeasurable (fun x => (φ x : EReal) - g x) := by
  have hfin : ∀ x, g x ≠ ⊤ := by
    intro x hgx
    have htop : (φ x : EReal) = ⊤ := le_antisymm le_top (by simpa [hgx] using hle x)
    exact (EReal.coe_ne_top (φ x)) htop
  rcases hg with ⟨k, c, E, hcond, heq⟩
  set c' : Fin k → ℝ := fun i => (c i).toReal with hc'_def
  set h : EuclideanSpace' d → ℝ := fun x => ∑ i, c' i * (E i).indicator' x with hh_def
  have hh_simple : RealSimpleFunction h := by
    exact ⟨k, c', E, fun i => (hcond i).1, by ext x; simp [hh_def, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]⟩
  have hh_eq : ∀ x, (h x : EReal) = g x := by
    intro x
    simp only [hh_def, heq, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have hcoe_sum : ∀ (n : ℕ) (a : Fin n → ℝ),
        (↑(∑ i, a i) : EReal) = ∑ i, (↑(a i) : EReal) := by
      intro n a; induction n with
      | zero => simp [Finset.univ_eq_empty]
      | succ m ih =>
        rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, EReal.coe_add]
        congr 1; exact ih (fun i => a i.castSucc)
    rw [hcoe_sum]
    congr 1; ext i
    by_cases hx : x ∈ E i
    · simp only [hc'_def, Set.indicator', Set.indicator_of_mem hx, mul_one,
        EReal.indicator, Real.EReal_fun]
      have hci_ne_bot : c i ≠ ⊥ :=
        ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (hcond i).2)
      have hci_ne_top : c i ≠ ⊤ := by
        intro hci_top
        apply hfin x
        rw [heq]; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        apply eq_top_iff.mpr
        have htop : c i * EReal.indicator (E i) x = ⊤ := by
          simp [hci_top, EReal.indicator, Real.EReal_fun, Set.indicator', Set.indicator_of_mem hx]
        calc ⊤ = c i * EReal.indicator (E i) x := htop.symm
          _ ≤ ∑ j, c j * EReal.indicator (E j) x :=
            Finset.single_le_sum (f := fun j => c j * EReal.indicator (E j) x)
              (fun j _ => mul_nonneg (hcond j).2 (by
                simp only [EReal.indicator, Real.EReal_fun]
                by_cases hxj : x ∈ E j
                · simp [Set.indicator'_of_mem hxj]
                · simp [Set.indicator'_of_notMem hxj])) (Finset.mem_univ i)
      rw [show (1 : ℝ).toEReal = (1 : EReal) from rfl, mul_one]
      exact EReal.coe_toReal hci_ne_top hci_ne_bot
    · simp only [Set.indicator'_of_notMem hx, mul_zero, EReal.coe_zero,
        EReal.indicator, Real.EReal_fun, MulZeroClass.mul_zero]
  have hh_real : RealMeasurable h := ⟨fun _ => h, fun _ => hh_simple, fun _ => tendsto_const_nhds⟩
  have hsub_real : RealMeasurable (φ - h) := RealMeasurable.sub hφ hh_real
  have hsub_nn : ∀ x, 0 ≤ (φ - h) x := fun x =>
    sub_nonneg.mpr (EReal.coe_le_coe_iff.mp (by rw [hh_eq x]; exact hle x))
  have hφminush : (fun x => (φ x : EReal) - g x) = fun x => EReal.pos_fun (φ - h) x := by
    funext x
    rw [← hh_eq x]
    simp only [EReal.pos_fun, max_eq_left (hsub_nn x)]
    simp [EReal.coe_sub]
  exact hφminush ▸ RealMeasurable.measurable_pos hsub_real

private lemma unsigned_approx_from_sup_134 {d:ℕ} {f: EuclideanSpace' d → EReal}
    (hf : UnsignedAbsolutelyIntegrable f) (ε : ℝ) (hε : 0 < ε) :
    ∃ (g : EuclideanSpace' d → EReal) (hg : UnsignedSimpleFunction g),
      (∀ x, g x ≤ f x) ∧
      UnsignedLebesgueIntegral f ≤ hg.integ + ε := by
  set L := UnsignedLebesgueIntegral f with hL_def
  have hL_lt_top : L < ⊤ := hf.2
  have hL_ne_top : L ≠ ⊤ := ne_of_lt hL_lt_top
  have hL_nonneg : (0 : EReal) ≤ L := UnsignedLebesgueIntegral.nonneg hf.1
  have hL_ne_bot : L ≠ ⊥ := ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero hL_nonneg)
  have hε_ne_bot : (ε : EReal) ≠ ⊥ := EReal.coe_ne_bot ε
  have hε_ne_top : (ε : EReal) ≠ ⊤ := EReal.coe_ne_top ε
  have hL_sub_lt : L - (ε : EReal) < L := by
    rw [EReal.sub_lt_iff (Or.inl hε_ne_bot) (Or.inl hε_ne_top)]
    calc L = 0 + L := (zero_add L).symm
      _ < (ε : EReal) + L := EReal.add_lt_add_of_lt_of_le
          (EReal.coe_pos.mpr hε) le_rfl hL_ne_bot hL_ne_top
      _ = L + (ε : EReal) := add_comm _ _
  have hR_exists : ∃ R ∈ { R : EReal | ∃ g : EuclideanSpace' d → EReal,
      ∃ hg : UnsignedSimpleFunction g, ∀ x, g x ≤ f x ∧ R = hg.integ },
      L - (ε : EReal) < R := by
    by_contra h_all
    push_neg at h_all
    have h_le : L ≤ L - (ε : EReal) := by
      conv_lhs => rw [hL_def, UnsignedLebesgueIntegral, LowerUnsignedLebesgueIntegral]
      exact sSup_le fun R hR => h_all R hR
    exact absurd h_le (not_le.mpr hL_sub_lt)
  obtain ⟨R, hR_mem, hR_gt⟩ := hR_exists
  obtain ⟨g, hg, hcond⟩ := hR_mem
  have hg_le : ∀ x, g x ≤ f x := fun x => (hcond x).1
  have hR_eq : R = hg.integ := (hcond (0 : EuclideanSpace' d)).2
  refine ⟨g, hg, hg_le, ?_⟩
  rw [hR_eq] at hR_gt
  exact le_of_lt ((EReal.sub_lt_iff (Or.inl hε_ne_bot)
      (Or.inl hε_ne_top)).mp hR_gt)

/-- Exercise 1.3.25 (a) -/
theorem ComplexAbsolutelyIntegrable.almost_bounded_support {d:ℕ} {f : EuclideanSpace' d → ℂ}
  (hf: ComplexAbsolutelyIntegrable f)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (R: ℝ), PreL1.norm (f * Complex.indicator (Metric.ball 0 R)ᶜ) ≤ ε := by
  obtain ⟨g, hg, hg_le, hg_bound⟩ := unsigned_approx_from_sup_134 hf.abs (ε / 2) (half_pos hε)
  have hfin_g : ∀ x, g x ≠ ⊤ := fun x =>
    ne_of_lt (lt_of_le_of_lt (hg_le x) (by simp only [EReal.abs_fun]; exact EReal.coe_lt_top _))
  rcases hg with ⟨k, c, E, hcond, heq⟩
  have hg : UnsignedSimpleFunction g := ⟨k, c, E, hcond, heq⟩
  have hgx_nn : ∀ x, 0 ≤ g x := by
    intro x
    rw [heq]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (hcond j).2 (EReal.indicator_nonneg (E j) x))
  have hg_meas : UnsignedMeasurable g := UnsignedSimpleFunction.measurable hg hgx_nn
  set c' : Fin k → ℝ := fun i => (c i).toReal with hc'_def
  set h : EuclideanSpace' d → ℝ := fun x => ∑ i, c' i * (E i).indicator' x with hh_def
  have hh_simple : RealSimpleFunction h :=
    ⟨k, c', E, fun i => (hcond i).1, by ext x; simp [hh_def, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]⟩
  have hh_eq : ∀ x, (h x : EReal) = g x := by
    intro x
    simp only [hh_def, heq, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [coe_sum_eq_sum_coe (fun i => c' i * (E i).indicator' x)]
    congr 1
    ext i
    by_cases hx : x ∈ E i
    · simp only [hc'_def, Set.indicator', Set.indicator_of_mem hx, mul_one,
        EReal.indicator, Real.EReal_fun]
      have hci_ne_bot : c i ≠ ⊥ := ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (hcond i).2)
      have hci_ne_top : c i ≠ ⊤ := by
        intro hci_top
        apply hfin_g x
        rw [heq]; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        apply eq_top_iff.mpr
        have htop : c i * EReal.indicator (E i) x = ⊤ := by
          simp [hci_top, EReal.indicator, Real.EReal_fun, Set.indicator', Set.indicator_of_mem hx]
        calc ⊤ = c i * EReal.indicator (E i) x := htop.symm
          _ ≤ ∑ j, c j * EReal.indicator (E j) x :=
            Finset.single_le_sum (f := fun j => c j * EReal.indicator (E j) x)
              (fun j _ => mul_nonneg (hcond j).2 (by
                simp only [EReal.indicator, Real.EReal_fun]
                by_cases hxj : x ∈ E j
                · simp [Set.indicator'_of_mem hxj]
                · simp [Set.indicator'_of_notMem hxj])) (Finset.mem_univ i)
      rw [show (1 : ℝ).toEReal = (1 : EReal) from rfl, mul_one]
      exact EReal.coe_toReal hci_ne_top hci_ne_bot
    · simp only [Set.indicator'_of_notMem hx, mul_zero, EReal.coe_zero,
        EReal.indicator, Real.EReal_fun, MulZeroClass.mul_zero]
  have hc'_nn : ∀ i, 0 ≤ c' i := fun i => by
    simp only [hc'_def]
    exact EReal.toReal_nonneg (hcond i).2
  have hh_fin : UnsignedLebesgueIntegral (fun x => (h x : EReal)) < ⊤ := by
    have hfun : (fun x => (h x : EReal)) = g := funext (fun x => hh_eq x)
    rw [hfun]
    have hmono := LowerUnsignedLebesgueIntegral.mono hg_meas hf.abs.1 (AlmostAlways.ofAlways hg_le)
    exact lt_of_le_of_lt (by simpa [UnsignedLebesgueIntegral] using hmono) hf.abs.2
  have hh_repr : h = ∑ i, c' i • (E i).indicator' := by
    ext x
    simp [hh_def, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  obtain ⟨R, hR⟩ := real_simple_tail_integral_small (g := h) (hg_eq := hh_repr)
    (hmes := fun i => (hcond i).1) (hc_nn := hc'_nn) hh_fin (ε / 2) (half_pos hε)
  have hφnorm : RealMeasurable (fun x => ‖f x‖) := by
    exact ((RealMeasurable_TFAE_helpers.RealMeasurable.TFAE (f := fun x => ‖f x‖)).out 4 0
      (a := ∀ K : Set ℝ, IsClosed K → LebesgueMeasurable ((fun x => ‖f x‖) ⁻¹' K))
      (b := RealMeasurable (fun x => ‖f x‖))).mp (by
        intro K hK
        have hKpre : IsClosed ((fun z : ℂ => ‖z‖) ⁻¹' K) := hK.preimage continuous_norm
        simpa using (ComplexMeasurable.preimage_closed hf.1 hKpre))
  have hsub_meas : UnsignedMeasurable (fun x => EReal.abs_fun f x - g x) :=
    real_measurable_sub_unsigned hφnorm hg hg_le
  have h_id : ∀ x, g x + (EReal.abs_fun f x - g x) = EReal.abs_fun f x := by
    intro x
    rw [show g x = (↑(g x).toReal : EReal) from
      (EReal.coe_toReal (hfin_g x)
        (ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (hgx_nn x)))).symm]
    rw [add_comm]
    exact (EReal.sub_add_cancel (a := EReal.abs_fun f x) (b := (g x).toReal))
  have hsum_meas : UnsignedMeasurable (fun x => g x + (EReal.abs_fun f x - g x)) :=
    hg_meas.add hsub_meas
  have hint_sum : UnsignedLebesgueIntegral (fun x => g x + (EReal.abs_fun f x - g x)) =
      UnsignedLebesgueIntegral g + UnsignedLebesgueIntegral (fun x => EReal.abs_fun f x - g x) := by
    simpa [UnsignedLebesgueIntegral] using (LowerUnsignedLebesgueIntegral.add hg_meas hsub_meas hsum_meas)
  have hint_g : UnsignedLebesgueIntegral g = hg.integ := by
    rw [UnsignedLebesgueIntegral]
    exact LowerUnsignedLebesgueIntegral.eq_simpleIntegral hg
  have hg_integ_le : hg.integ ≤ UnsignedLebesgueIntegral (EReal.abs_fun f) := by
    have hmono := LowerUnsignedLebesgueIntegral.mono hg_meas hf.abs.1 (AlmostAlways.ofAlways hg_le)
    calc hg.integ = UnsignedLebesgueIntegral g := hint_g.symm
      _ = LowerUnsignedLebesgueIntegral g := by rw [UnsignedLebesgueIntegral]
      _ ≤ LowerUnsignedLebesgueIntegral (EReal.abs_fun f) := hmono
      _ = UnsignedLebesgueIntegral (EReal.abs_fun f) := by rw [UnsignedLebesgueIntegral]
  have hg_integ_ne_top : hg.integ ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hg_integ_le hf.abs.2)
  have hg_integ_nn : 0 ≤ hg.integ := by
    simpa [hint_g] using (UnsignedLebesgueIntegral.nonneg hg_meas)
  have hg_integ_ne_bot : hg.integ ≠ ⊥ := ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero hg_integ_nn)
  have hle1 : UnsignedLebesgueIntegral (EReal.abs_fun f) =
      hg.integ + UnsignedLebesgueIntegral (fun x => EReal.abs_fun f x - g x) := by
    have hfun : (fun x => g x + (EReal.abs_fun f x - g x)) = EReal.abs_fun f := funext h_id
    conv_lhs => rw [← hfun]
    rw [hint_sum, hint_g]
  have hle2 : hg.integ + UnsignedLebesgueIntegral (fun x => EReal.abs_fun f x - g x) ≤
      hg.integ + (ε / 2 : EReal) := by
    rw [← hle1]
    simpa using hg_bound
  have hsub_bound : UnsignedLebesgueIntegral (fun x => EReal.abs_fun f x - g x) ≤ ε / 2 :=
    cancel_add_left hg_integ_ne_top hg_integ_ne_bot hle2
  have hballR_meas : LebesgueMeasurable (Metric.ball (0 : EuclideanSpace' d) R)ᶜ :=
    (IsOpen.measurable (Metric.isOpen_ball)).complement
  have hR' : UnsignedLebesgueIntegral (fun x => g x * EReal.indicator (Metric.ball 0 R)ᶜ x) ≤ ε / 2 := by
    have hfun : (fun x => (h x : EReal) * EReal.indicator (Metric.ball 0 R)ᶜ x) =
        fun x => g x * EReal.indicator (Metric.ball 0 R)ᶜ x := by
      funext x
      rw [hh_eq x]
    simpa [hfun] using hR
  have h_pw : ∀ x, EReal.abs_fun f x * EReal.indicator (Metric.ball 0 R)ᶜ x ≤
      (fun x => g x * EReal.indicator (Metric.ball 0 R)ᶜ x + (EReal.abs_fun f x - g x)) x := fun x => by
    by_cases hx : x ∈ (Metric.ball 0 R)ᶜ
    · simp [EReal.indicator_of_mem hx, mul_one, h_id x]
    · simp [EReal.indicator_of_notMem hx, mul_zero, zero_add]
      exact (EReal.sub_nonneg (Or.inl (EReal.coe_ne_top (‖f x‖)))
        (Or.inl (EReal.coe_ne_bot (‖f x‖)))).mpr (hg_le x)
  have hmono : UnsignedLebesgueIntegral (fun x => EReal.abs_fun f x * EReal.indicator (Metric.ball 0 R)ᶜ x) ≤
      UnsignedLebesgueIntegral (fun x => g x * EReal.indicator (Metric.ball 0 R)ᶜ x + (EReal.abs_fun f x - g x)) := by
    simpa [UnsignedLebesgueIntegral] using (LowerUnsignedLebesgueIntegral.mono
      (UnsignedMeasurable.mul_indicator hf.abs.1 hballR_meas)
      (UnsignedMeasurable.add (UnsignedMeasurable.mul_indicator hg_meas hballR_meas) hsub_meas)
      (AlmostAlways.ofAlways h_pw))
  have hadd : UnsignedLebesgueIntegral (fun x => g x * EReal.indicator (Metric.ball 0 R)ᶜ x + (EReal.abs_fun f x - g x)) =
      UnsignedLebesgueIntegral (fun x => g x * EReal.indicator (Metric.ball 0 R)ᶜ x) +
      UnsignedLebesgueIntegral (fun x => EReal.abs_fun f x - g x) := by
    simpa [UnsignedLebesgueIntegral] using (LowerUnsignedLebesgueIntegral.add
      (UnsignedMeasurable.mul_indicator hg_meas hballR_meas) hsub_meas
      (UnsignedMeasurable.add (UnsignedMeasurable.mul_indicator hg_meas hballR_meas) hsub_meas))
  have hmain : UnsignedLebesgueIntegral (fun x => EReal.abs_fun f x * EReal.indicator (Metric.ball 0 R)ᶜ x) ≤ (ε : EReal) := by
    calc UnsignedLebesgueIntegral (fun x => EReal.abs_fun f x * EReal.indicator (Metric.ball 0 R)ᶜ x)
        ≤ UnsignedLebesgueIntegral (fun x => g x * EReal.indicator (Metric.ball 0 R)ᶜ x + (EReal.abs_fun f x - g x)) := hmono
      _ = UnsignedLebesgueIntegral (fun x => g x * EReal.indicator (Metric.ball 0 R)ᶜ x) +
          UnsignedLebesgueIntegral (fun x => EReal.abs_fun f x - g x) := hadd
      _ ≤ (ε / 2 : EReal) + (ε / 2 : EReal) := add_le_add hR' hsub_bound
      _ = (ε : EReal) := by
          change (↑(ε / 2 : ℝ) : EReal) + (↑(ε / 2 : ℝ) : EReal) = (ε : EReal)
          rw [← EReal.coe_add]
          congr 1
          linarith
  refine ⟨R, ?_⟩
  unfold PreL1.norm
  have h_pw2 : (fun x => EReal.abs_fun (f * Complex.indicator (Metric.ball 0 R)ᶜ) x) =
      fun x => EReal.abs_fun f x * EReal.indicator (Metric.ball 0 R)ᶜ x := by
    funext x
    simp only [EReal.abs_fun, Pi.mul_apply]
    rw [norm_mul]
    by_cases hx : x ∈ (Metric.ball 0 R)ᶜ
    · rw [EReal.indicator_of_mem hx, mul_one]
      simp [Complex.indicator, Real.complex_fun, Set.indicator'_of_mem hx]
    · rw [EReal.indicator_of_notMem hx, mul_zero]
      simp [Complex.indicator, Real.complex_fun, Set.indicator'_of_notMem hx]
  rw [show EReal.abs_fun (f * Complex.indicator (Metric.ball 0 R)ᶜ) =
      fun x => EReal.abs_fun f x * EReal.indicator (Metric.ball 0 R)ᶜ x from
      funext (fun x => congrFun h_pw2 x)]
  exact hmain

/-- Exercise 1.3.25 (b) -/
def BoundedOn {X Y:Type*} [PseudoMetricSpace Y] (f: X → Y) (S: Set X) : Prop := Bornology.IsBounded (f '' S)

theorem ComplexAbsolutelyIntegrable.almost_bounded {d:ℕ} {f : EuclideanSpace' d → ℂ}
  (hf: ComplexAbsolutelyIntegrable f)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (E: Set (EuclideanSpace' d)), LebesgueMeasurable E ∧
    Lebesgue_measure E ≤ ε ∧
    BoundedOn f Eᶜ := by
  let I : EReal := UnsignedLebesgueIntegral (EReal.abs_fun f)
  have hI_lt : I < ⊤ := hf.abs.2
  have hI_nn : 0 ≤ I := UnsignedLebesgueIntegral.nonneg hf.abs.1
  have hI_ne_bot : I ≠ ⊥ := ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero hI_nn)
  have hI_ne_top : I ≠ ⊤ := ne_of_lt hI_lt
  have hI_toReal_nn : 0 ≤ I.toReal := EReal.toReal_nonneg hI_nn
  let M : ℝ := max 1 (2 * I.toReal / ε + 1)
  have hMpos : 0 < M := by
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left 1 (2 * I.toReal / ε + 1))
  have hM_ratio : M⁻¹ * I.toReal ≤ ε / 2 := by
    have hMge : 2 * I.toReal / ε + 1 ≤ M := le_max_right 1 (2 * I.toReal / ε + 1)
    have hpos : 0 < 2 * I.toReal / ε + 1 := by positivity
    have hinv : M⁻¹ ≤ (2 * I.toReal / ε + 1)⁻¹ :=
      (inv_le_inv₀ hMpos hpos).mpr hMge
    have hle : I.toReal ≤ (ε / 2) * (2 * I.toReal / ε + 1) := by
      have hcalc : (ε / 2) * (2 * I.toReal / ε + 1) = I.toReal + ε / 2 := by
        field_simp [ne_of_gt hε]
      rw [hcalc]
      nlinarith
    calc M⁻¹ * I.toReal
        ≤ (2 * I.toReal / ε + 1)⁻¹ * I.toReal := mul_le_mul_of_nonneg_right hinv hI_toReal_nn
      _ ≤ ε / 2 := by
          have hinv_nn : 0 ≤ (2 * I.toReal / ε + 1)⁻¹ := by positivity
          have hmul := mul_le_mul_of_nonneg_left hle hinv_nn
          calc (2 * I.toReal / ε + 1)⁻¹ * I.toReal
              ≤ (2 * I.toReal / ε + 1)⁻¹ * ((ε / 2) * (2 * I.toReal / ε + 1)) := hmul
            _ = ε / 2 := by
                field_simp [show 2 * I.toReal / ε + 1 ≠ 0 by positivity]
  let E : Set (EuclideanSpace' d) := {x | (M : ℝ) ≤ ‖f x‖}
  have hE_meas : LebesgueMeasurable E := by
    have hEq : E = f ⁻¹' {z : ℂ | (M : ℝ) ≤ ‖z‖} := by
      ext x
      rfl
    rw [hEq]
    exact ComplexMeasurable.preimage_closed hf.1
      (by simpa using (IsClosed.preimage continuous_norm (isClosed_Ici (a := M))))
  have hE_le : Lebesgue_measure E ≤ ε := by
    have hcheb := ComplexAbsolutelyIntegrable.chebyshev hf M hMpos
    have hI_real : I = (I.toReal : EReal) := (EReal.coe_toReal hI_ne_top hI_ne_bot).symm
    calc Lebesgue_measure E
        ≤ ((M : ℝ)⁻¹ : EReal) * I := by simpa [E] using hcheb
      _ = ((M⁻¹ * I.toReal : ℝ) : EReal) := by
          conv_lhs => rw [hI_real]
          rw [← EReal.coe_inv, ← EReal.coe_mul]
      _ ≤ (ε / 2 : EReal) := EReal.coe_le_coe_iff.mpr hM_ratio
      _ ≤ (ε : EReal) := EReal.coe_le_coe_iff.mpr (by linarith)
  have hbounded : BoundedOn f Eᶜ := by
    unfold BoundedOn
    rw [Metric.isBounded_iff_subset_closedBall (0 : ℂ)]
    refine ⟨M, ?_⟩
    intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    have hx' : ¬ (M : ℝ) ≤ ‖f x‖ := by simpa [E] using hx
    exact le_of_lt (lt_of_not_ge hx')
  exact ⟨E, hE_meas, hE_le, hbounded⟩
