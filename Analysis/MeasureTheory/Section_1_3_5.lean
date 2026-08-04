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
def egorov_box (d : ℕ) (N : ℕ) : Box d :=
  Box.mk (fun _ : Fin d => (BoundedInterval.Icc (-(N : ℝ)) (N : ℝ) : BoundedInterval))

/-- The set of points whose coordinates all lie in -N..N. -/
def egorov_A {d : ℕ} (N : ℕ) : Set (EuclideanSpace' d) := (egorov_box d N).toSet

/-- A box is Lebesgue measurable. -/
lemma egorov_A_meas {d : ℕ} (N : ℕ) : LebesgueMeasurable (egorov_A (d := d) N) := by
  exact Jordan_measurable.lebesgue (IsElementary.jordanMeasurable (IsElementary.box (egorov_box d N)))

/-- A box has finite Lebesgue measure. -/
lemma egorov_A_fin {d : ℕ} (N : ℕ) : Lebesgue_measure (egorov_A (d := d) N) < ⊤ := by
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

-- ============================================================
-- Lusin's theorem (Theorem 1.3.28) machinery
-- ============================================================

/-- Multiplying a complex simple function by the indicator of a measurable set gives a simple function. -/
private lemma ComplexSimpleFunction.mul_indicator' {d:ℕ} {s : EuclideanSpace' d → ℂ} (hs : ComplexSimpleFunction s)
    {E : Set (EuclideanSpace' d)} (hE : LebesgueMeasurable E) :
    ComplexSimpleFunction (s * Complex.indicator E) := by
  rcases hs with ⟨k, c, A, hA_meas, heq⟩
  refine ⟨k, c, fun i => A i ∩ E, fun i => LebesgueMeasurable.inter (hA_meas i) hE, ?_⟩
  ext x
  rw [heq]
  simp only [Pi.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hx : x ∈ E
  · simp [Complex.indicator, Real.complex_fun, Set.indicator'_of_mem hx, mul_one]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    by_cases hxi : x ∈ A i
    · have hmem : x ∈ A i ∩ E := Set.mem_inter hxi hx
      simp [Set.indicator'_of_mem hxi, Set.indicator'_of_mem hmem]
    · have hnot : x ∉ A i ∩ E := by
        intro h
        exact hxi h.1
      simp [Set.indicator'_of_notMem hxi, Set.indicator'_of_notMem hnot]
  · simp [Complex.indicator, Real.complex_fun, Set.indicator'_of_notMem hx, mul_zero]
    symm
    apply Finset.sum_eq_zero
    intro i _
    rw [show (A i ∩ E).indicator' x = 0 from Set.indicator'_of_notMem (by
      intro h
      have h2 : x ∈ E := h.2
      exact hx h2)]
    norm_num

/-- A complex simple function is complex measurable. -/
private lemma ComplexSimpleFunction.measurable {d:ℕ} {s : EuclideanSpace' d → ℂ} (hs : ComplexSimpleFunction s) :
    ComplexMeasurable s := by
  exact ⟨fun _ => s, fun _ => hs, fun x => tendsto_const_nhds⟩

/-- Multiplying a pointwise-converging sequence by a fixed indicator preserves pointwise convergence. -/
private lemma mul_indicator_pointwise_conv {d:ℕ} {s : ℕ → EuclideanSpace' d → ℂ} {f : EuclideanSpace' d → ℂ}
    {A : Set (EuclideanSpace' d)} (hconv : PointwiseConvergesTo s f) :
    PointwiseConvergesTo (fun m => s m * Complex.indicator A) (f * Complex.indicator A) := by
  intro x
  by_cases hx : x ∈ A
  · have hχ : Complex.indicator A x = 1 := by
      simp [Complex.indicator, Real.complex_fun, Set.indicator'_of_mem hx]
    simpa [Pi.mul_apply, hχ] using hconv x
  · have hχ : Complex.indicator A x = 0 := by
      simp [Complex.indicator, Real.complex_fun, Set.indicator'_of_notMem hx]
    simp [Pi.mul_apply, hχ]

/-- The same, but almost-always (pointwise implies pointwise ae). -/
private lemma mul_indicator_ae_conv {d:ℕ} {s : ℕ → EuclideanSpace' d → ℂ} {f : EuclideanSpace' d → ℂ}
    {A : Set (EuclideanSpace' d)} (hconv : PointwiseConvergesTo s f) :
    PointwiseAeConvergesTo (fun m => s m * Complex.indicator A) (f * Complex.indicator A) := by
  exact AlmostAlways.ofAlways (mul_indicator_pointwise_conv hconv)

/-- A uniform limit on a set of functions continuous on that set is continuous on it. -/
private lemma uniform_converges_continuousOn {X : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (F : ℕ → X → Y) (f : X → Y) (S : Set X)
    (hconv : UniformlyConvergesToOn F f S) (hcont : ∀ n, ContinuousOn (F n) S) :
    ContinuousOn f S := by
  have hT : TendstoUniformlyOn F f atTop S :=
    (tendstoUniformlyOn_iff_uniformlyConvergesToOn F f S).mpr hconv
  exact hT.continuousOn (Eventually.of_forall hcont).frequently

/-- A simple function (with finite-measure atoms) is relatively continuous on a closed
    set whose complement inside B has small measure. -/
lemma simple_continuousOn_outside_small {d:ℕ} {s : EuclideanSpace' d → ℂ} {n : ℕ}
    {v : Fin n → ℂ} {A : Fin n → Set (EuclideanSpace' d)}
    (hs_eq : s = ∑ i, v i • Complex.indicator (A i))
    (hA_meas : ∀ i, LebesgueMeasurable (A i)) (hA_disj : Set.univ.PairwiseDisjoint A)
    (hA_fin : ∀ i, v i ≠ 0 → Lebesgue_measure (A i) < ⊤)
    {B : Set (EuclideanSpace' d)} (hB : LebesgueMeasurable B) (hBf : Lebesgue_measure B < ⊤)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : Set (EuclideanSpace' d), IsClosed C ∧ LebesgueMeasurable C ∧
      Lebesgue_measure (B \ C) ≤ δ ∧ Continuous (fun x : C => s x.val) := by
  classical
  -- ε₀: the per-atom measure budget
  set ε₀ : ℝ := δ / (2 * ((n : ℝ) + 1)) with hε₀_def
  have hε₀_pos : 0 < ε₀ := by
    rw [hε₀_def]
    exact div_pos hδ (mul_pos two_pos (by positivity : 0 < (n : ℝ) + 1))
  -- Step 1: compact cores K i inside the nonzero atoms
  have hK_exists : ∀ i : Fin n, ∃ K : Set (EuclideanSpace' d), IsCompact K ∧ K ⊆ A i ∧
      (v i ≠ 0 → Lebesgue_outer_measure (A i \ K) ≤ (ε₀ : EReal)) := by
    intro i
    by_cases hv : v i = 0
    · refine ⟨∅, isCompact_empty, Set.empty_subset (A i), ?_⟩
      intro hne
      exact False.elim (hne hv)
    · have h_tfae := (LebesgueMeasurable.finite_TFAE (A i)).out 0 3
      obtain ⟨K, hKc, hKs, hKb⟩ :=
        (h_tfae.mp ⟨hA_meas i, hA_fin i hv⟩ (↑ε₀) (EReal.coe_pos.mpr hε₀_pos))
      exact ⟨K, hKc, hKs, fun _ => hKb⟩
  choose K hK_comp hK_sub hK_bound using hK_exists
  -- P i: the atom A i if v i ≠ 0, else empty
  set P : Fin n → Set (EuclideanSpace' d) := fun i => if h : v i ≠ 0 then A i else ∅ with hP_def
  -- Z: B minus all nonzero atoms (s = 0 on Z)
  set Z : Set (EuclideanSpace' d) := B \ ⋃ i, P i with hZ_def
  have hP_meas : ∀ i, LebesgueMeasurable (P i) := by
    intro i
    by_cases hv : v i = 0
    · rw [hP_def]
      simpa [hv] using LebesgueMeasurable.empty
    · rw [hP_def]
      simpa [hv] using hA_meas i
  have hUP_meas : LebesgueMeasurable (⋃ i : Fin n, P i) := by
    have hfs : LebesgueMeasurable (⋃ i ∈ (Finset.univ : Finset (Fin n)), P i) :=
      LebesgueMeasurable.finset_union (E := P) (S := Finset.univ) (fun i _ => hP_meas i)
    simpa using hfs
  have hZ_meas : LebesgueMeasurable Z := by
    rw [hZ_def]
    exact LebesgueMeasurable.inter hB (LebesgueMeasurable.complement hUP_meas)
  have hZ_fin : Lebesgue_measure Z < ⊤ := by
    rw [hZ_def]
    exact lt_of_le_of_lt (Lebesgue_outer_measure.mono Set.diff_subset) hBf
  -- Step 2: compact core L inside Z
  have hL_exists : ∃ L : Set (EuclideanSpace' d), IsCompact L ∧ L ⊆ Z ∧
      Lebesgue_outer_measure (Z \ L) ≤ (↑(δ / 2) : EReal) := by
    have h_tfae := (LebesgueMeasurable.finite_TFAE Z).out 0 3
    obtain ⟨L, hLc, hLs, hLb⟩ :=
      (h_tfae.mp ⟨hZ_meas, hZ_fin⟩ (↑(δ / 2)) (EReal.coe_pos.mpr (div_pos hδ (by norm_num))))
    exact ⟨L, hLc, hLs, hLb⟩
  obtain ⟨L, hL_comp, hL_sub, hL_bound⟩ := hL_exists
  -- Step 3: C = (⋃ i, K i) ∪ L is closed and measurable
  set C : Set (EuclideanSpace' d) := (⋃ i, K i) ∪ L with hC_def
  have hC_isClosed : IsClosed C := by
    rw [hC_def]
    exact IsCompact.isClosed (IsCompact.union (isCompact_iUnion hK_comp) hL_comp)
  have hC_meas : LebesgueMeasurable C := IsClosed.measurable hC_isClosed
  -- Step 4: s is constant v i on each K i and 0 on L
  have hs_on_K : ∀ i, ∀ x ∈ K i, s x = v i := by
    intro i x hx
    have hxAi : x ∈ A i := hK_sub i hx
    rw [hs_eq]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · simp [Complex.indicator, Real.complex_fun, Set.indicator'_of_mem hxAi]
    · intro j _ hij
      have hx_notin : x ∉ A j := by
        intro hxAj
        have hdisj := hA_disj (Set.mem_univ i) (Set.mem_univ j) (Ne.symm hij)
        exact (Set.disjoint_left.mp hdisj) hxAi hxAj
      simp [Complex.indicator, Real.complex_fun, Set.indicator'_of_notMem hx_notin]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hs_on_L : ∀ x ∈ L, s x = 0 := by
    intro x hxL
    have hx_not_P : x ∉ ⋃ i, P i := (hL_sub hxL).2
    rw [hs_eq]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hvj : v j = 0
    · simp [hvj]
    · have hx_not_Aj : x ∉ A j := by
        intro hxA
        have hx_not_Pj : x ∉ P j := by
          intro hxPj
          exact hx_not_P (Set.mem_iUnion.mpr ⟨j, hxPj⟩)
        rw [hP_def] at hx_not_Pj
        simp [hvj] at hx_not_Pj
        exact hx_not_Pj hxA
      simp [Complex.indicator, Real.complex_fun, Set.indicator'_of_notMem hx_not_Aj]
  -- Step 5: measure bound
  set G : Fin n → Set (EuclideanSpace' d) := fun i => if h : v i ≠ 0 then A i \ K i else ∅ with hG_def
  set D : Set (EuclideanSpace' d) := ⋃ i, G i with hD_def
  have hG_le : ∀ i, Lebesgue_outer_measure (G i) ≤ (ε₀ : EReal) := by
    intro i
    by_cases hv : v i = 0
    · rw [hG_def]
      simp [hv, Lebesgue_outer_measure.of_empty]
      exact hε₀_pos.le
    · rw [hG_def]
      simpa [hv] using hK_bound i hv
  have hD_le : Lebesgue_outer_measure D ≤ (↑(δ / 2) : EReal) := by
    rw [hD_def]
    calc Lebesgue_outer_measure (⋃ i, G i)
        ≤ ∑ i, Lebesgue_outer_measure (G i) := Lebesgue_outer_measure.finite_union_le G
      _ ≤ ∑ i, (ε₀ : EReal) := by
          apply Finset.sum_le_sum
          intro i _
          exact hG_le i
      _ = ((n : ℝ) * ε₀ : EReal) := by
          rw [← EReal.coe_finset_sum (fun _ _ => le_of_lt hε₀_pos)]
          congr 1
          rw [Finset.sum_const]
          rw [nsmul_eq_mul]
          norm_num
      _ ≤ (↑(δ / 2) : EReal) := by
          rw [← EReal.coe_mul]
          rw [EReal.coe_le_coe_iff]
          rw [hε₀_def]
          rw [← mul_div_assoc]
          have hden : 0 < (2 : ℝ) * ((n : ℝ) + 1) := by positivity
          have hc : (n : ℝ) + 1 ≠ 0 := ne_of_gt (by positivity)
          calc (n : ℝ) * δ / (2 * ((n : ℝ) + 1))
              ≤ ((n : ℝ) + 1) * δ / (2 * ((n : ℝ) + 1)) := by
                  apply div_le_div_of_nonneg_right
                  · exact mul_le_mul_of_nonneg_right (by linarith) hδ.le
                  · exact hden.le
            _ = δ / 2 := by
                  rw [mul_comm ((n : ℝ) + 1) δ]
                  rw [mul_div_mul_right δ 2 hc]
  have hBC_sub : B \ ((⋃ i, K i) ∪ L) ⊆ D ∪ (Z \ L) := by
    intro x hx
    rcases hx with ⟨hxB, hxC⟩
    by_cases hxU : x ∈ ⋃ i, P i
    · left
      simp only [hD_def, Set.mem_iUnion]
      rw [Set.mem_iUnion] at hxU
      rcases hxU with ⟨i, hxi⟩
      refine ⟨i, ?_⟩
      rw [hG_def]
      have hvi : v i ≠ 0 := by
        intro hv
        have hPi : P i = ∅ := by
          rw [hP_def]
          simp [hv]
        rw [hPi] at hxi
        exact hxi
      simp [hvi]
      have hPi : P i = A i := by
        rw [hP_def]
        simp [hvi]
      refine ⟨?_, ?_⟩
      · rwa [← hPi]
      · intro hxKi
        exact hxC (Or.inl (Set.mem_iUnion.mpr ⟨i, hxKi⟩))
    · right
      exact ⟨⟨hxB, hxU⟩, fun hxL => hxC (Or.inr hxL)⟩
  have hBC_bound : Lebesgue_outer_measure (B \ ((⋃ i, K i) ∪ L)) ≤ (δ : EReal) := by
    calc Lebesgue_outer_measure (B \ ((⋃ i, K i) ∪ L))
        ≤ Lebesgue_outer_measure (D ∪ (Z \ L)) := Lebesgue_outer_measure.mono hBC_sub
      _ ≤ Lebesgue_outer_measure D + Lebesgue_outer_measure (Z \ L) := by
          let S : Fin 2 → Set (EuclideanSpace' d) := ![D, Z \ L]
          have h_union : ⋃ i : Fin 2, S i = D ∪ (Z \ L) := by
            ext x; simp [S]
          calc Lebesgue_outer_measure (D ∪ (Z \ L)) = Lebesgue_outer_measure (⋃ i : Fin 2, S i) := by rw [h_union]
            _ ≤ ∑ i : Fin 2, Lebesgue_outer_measure (S i) := Lebesgue_outer_measure.finite_union_le S
            _ = Lebesgue_outer_measure D + Lebesgue_outer_measure (Z \ L) := by simp [S]
      _ ≤ (↑(δ / 2) : EReal) + (↑(δ / 2) : EReal) := add_le_add hD_le hL_bound
      _ = (δ : EReal) := by
          rw [← EReal.coe_add]
          congr 1
          ring
  -- Step 6: continuity of s on C
  have hcont : Continuous (fun x : C => s x.val) := by
    rw [continuous_iff_isClosed]
    intro t ht
    change IsClosed {x : C | s x.val ∈ t}
    have h_piece_closed : ∀ i, IsClosed {x : C | x.val ∈ K i} := by
      intro i
      exact IsClosed.preimage continuous_subtype_val (IsCompact.isClosed (hK_comp i))
    have h_L_closed : IsClosed {x : C | x.val ∈ L} :=
      IsClosed.preimage continuous_subtype_val (IsCompact.isClosed hL_comp)
    have h_eq : {x : C | s x.val ∈ t} =
        (⋃ i, {x : C | x.val ∈ K i ∧ v i ∈ t}) ∪ {x : C | x.val ∈ L ∧ (0 : ℂ) ∈ t} := by
      ext x
      constructor
      · intro hst
        have hxC : x.val ∈ (⋃ i, K i) ∪ L := by
          exact x.2
        by_cases hxK : x.val ∈ ⋃ i, K i
        · rw [Set.mem_iUnion] at hxK
          rcases hxK with ⟨i, hxi⟩
          left
          rw [Set.mem_iUnion]
          refine ⟨i, ?_⟩
          rw [Set.mem_setOf_eq]
          exact ⟨hxi, by simpa [hs_on_K i x.val hxi] using hst⟩
        · right
          have hxL : x.val ∈ L := by
            rcases hxC with hxKU | hxL
            · exact False.elim (hxK hxKU)
            · exact hxL
          rw [Set.mem_setOf_eq]
          exact ⟨hxL, by simpa [hs_on_L x.val hxL] using hst⟩
      · intro hst
        rw [Set.mem_union] at hst
        rcases hst with hstL | hstR
        · rw [Set.mem_iUnion] at hstL
          rcases hstL with ⟨i, hi⟩
          rw [Set.mem_setOf_eq] at hi
          rcases hi with ⟨hxi, hvit⟩
          simpa [hs_on_K i x.val hxi] using hvit
        · rw [Set.mem_setOf_eq] at hstR
          rcases hstR with ⟨hxL, h0t⟩
          simpa [hs_on_L x.val hxL] using h0t
    rw [h_eq]
    apply IsClosed.union
    · apply isClosed_iUnion_of_finite
      intro i
      by_cases hvit : v i ∈ t
      · convert h_piece_closed i using 1
        ext x
        simp [hvit]
      · convert (isClosed_empty : IsClosed (∅ : Set C)) using 1
        ext x
        simp [hvit]
    · by_cases h0t : (0 : ℂ) ∈ t
      · convert h_L_closed using 1
        ext x
        simp [h0t]
      · convert (isClosed_empty : IsClosed (∅ : Set C)) using 1
        ext x
        simp [h0t]
  refine ⟨C, hC_isClosed, hC_meas, ?_, hcont⟩
  change Lebesgue_outer_measure (B \ C) ≤ (δ : EReal)
  rw [hC_def]
  exact hBC_bound

/-- Lusin's theorem on a bounded measurable set: a complex measurable function is continuous on
    the complement of a small-measure subset of the set. -/
lemma box_lusin {d:ℕ} (A : Set (EuclideanSpace' d)) (hA : LebesgueMeasurable A)
    (hAf : Lebesgue_measure A < ⊤) (f : EuclideanSpace' d → ℂ) (hf : ComplexMeasurable f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ E : Set (EuclideanSpace' d), LebesgueMeasurable E ∧ E ⊆ A ∧ Lebesgue_measure E ≤ ε ∧
      Continuous (fun x : (A \ E : Set (EuclideanSpace' d)) => f x.val) := by
  classical
  let s0 : ℕ → EuclideanSpace' d → ℂ := Classical.choose hf
  have hs0_simple : ∀ n, ComplexSimpleFunction (s0 n) := (Classical.choose_spec hf).1
  have hs0_conv : PointwiseConvergesTo s0 f := (Classical.choose_spec hf).2
  set sA : ℕ → EuclideanSpace' d → ℂ := fun m => s0 m * Complex.indicator A
  set fA : EuclideanSpace' d → ℂ := f * Complex.indicator A
  -- Each sA m is complex simple, hence measurable; fA is measurable
  have hsm_simple : ∀ m, ComplexSimpleFunction (sA m) := by
    intro m
    simpa [sA] using ComplexSimpleFunction.mul_indicator' (hs0_simple m) hA
  have hsA_meas : ∀ m, ComplexMeasurable (sA m) := fun m =>
    ComplexSimpleFunction.measurable (hsm_simple m)
  have hfA_meas : ComplexMeasurable fA := by
    dsimp [fA]
    exact ComplexMeasurable.mul hf (ComplexSimpleFunction.measurable (ComplexSimpleFunction.indicator hA))
  -- sA converges pointwise (hence a.e.) to fA
  have hConvAe : PointwiseAeConvergesTo sA fA := by
    dsimp [sA, fA]
    exact mul_indicator_ae_conv hs0_conv
  -- Disjoint representation of each sA m
  have hrep : ∀ m, ∃ (n : ℕ) (v : Fin n → ℂ) (A : Fin n → Set (EuclideanSpace' d)),
      (∀ i, LebesgueMeasurable (A i)) ∧ Set.univ.PairwiseDisjoint A ∧
      sA m = ∑ i, v i • Complex.indicator (A i) := fun m =>
    (hsm_simple m).disjoint_representation
  choose nm vm Am hAm_meas hAm_disj hsm_eq using hrep
  -- On each atom the value is the coefficient; atoms with nonzero coefficient lie inside A
  have hAm_value : ∀ m i, ∀ x ∈ Am m i, sA m x = vm m i := by
    intro m i x hx
    rw [hsm_eq m]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · simp [Complex.indicator, Real.complex_fun, Set.indicator'_of_mem hx]
    · intro j _ hij
      have hdisj := hAm_disj m (Set.mem_univ i) (Set.mem_univ j) (Ne.symm hij)
      have hx_notin : x ∉ Am m j := by
        intro hxj
        exact (Set.disjoint_left.mp hdisj) hx hxj
      simp [Complex.indicator, Real.complex_fun, Set.indicator'_of_notMem hx_notin]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hAm_sub_A : ∀ m i, vm m i ≠ 0 → Am m i ⊆ A := by
    intro m i hvi x hx
    have hv_eq : sA m x = vm m i := hAm_value m i x hx
    have hsm_ne : sA m x ≠ 0 := by
      rw [hv_eq]
      exact hvi
    have hχ : Complex.indicator A x ≠ 0 := by
      intro hχ0
      have : sA m x = 0 := by
        simp [sA, hχ0]
      exact hsm_ne this
    by_contra hxnotA
    have hχ0 : Complex.indicator A x = 0 := by
      simp [Complex.indicator, Real.complex_fun, Set.indicator'_of_notMem hxnotA]
    exact hχ hχ0
  have hAm_fin : ∀ m i, vm m i ≠ 0 → Lebesgue_measure (Am m i) < ⊤ := by
    intro m i hvi
    exact lt_of_le_of_lt (Lebesgue_outer_measure.mono (hAm_sub_A m i hvi)) hAf
  -- For each m, find a closed Cm inside A on which sA m is continuous and A \ Cm is small
  have hchoose : ∀ m, ∃ C : Set (EuclideanSpace' d), IsClosed C ∧ LebesgueMeasurable C ∧
      Lebesgue_measure (A \ C) ≤ (↑(ε / 2^(m+2) : ℝ) : EReal) ∧
      Continuous (fun x : C => sA m x.val) := by
    intro m
    have hδ : 0 < (ε / 2^(m+2) : ℝ) := div_pos hε (pow_pos (by norm_num) (m + 2))
    obtain ⟨C, hCcl, hCmeas, hCb, hCcont⟩ :=
      simple_continuousOn_outside_small (s := sA m) (v := vm m) (A := Am m)
        (hs_eq := hsm_eq m) (hA_meas := hAm_meas m) (hA_disj := hAm_disj m)
        (hA_fin := hAm_fin m) (B := A) (hB := hA) (hBf := hAf)
        (δ := ε / 2^(m+2)) (hδ := hδ)
    exact ⟨C, hCcl, hCmeas, hCb, hCcont⟩
  choose Cm _hCm_closed hCm_meas hCm_bound hCm_cont using hchoose
  -- Cm' = Cm ∩ A, and D = ⋂ m Cm': measurable, D ⊆ A, finite measure
  set Cm' : ℕ → Set (EuclideanSpace' d) := fun m => Cm m ∩ A
  set D : Set (EuclideanSpace' d) := ⋂ m, Cm' m
  have hCm'_meas : ∀ m, LebesgueMeasurable (Cm' m) := fun m =>
    (hCm_meas m).inter hA
  have hD_meas : LebesgueMeasurable D := by
    dsimp [D]
    exact LebesgueMeasurable.countable_inter hCm'_meas
  have hD_sub_A : D ⊆ A := by
    intro x hx
    have hx0 : x ∈ Cm' 0 := Set.mem_iInter.mp hx 0
    exact hx0.2
  have hD_fin : Lebesgue_measure D < ⊤ :=
    lt_of_le_of_lt (Lebesgue_outer_measure.mono hD_sub_A) hAf
  -- Measure bound for A \ D
  have hACm'_eq : ∀ m, A \ Cm' m = A \ Cm m := by
    intro m
    ext x
    constructor
    · intro hx
      exact ⟨hx.1, fun hxCm => hx.2 ⟨hxCm, hx.1⟩⟩
    · intro hx
      exact ⟨hx.1, fun hxInt => hx.2 hxInt.1⟩
  have hACm'_le : ∀ m, Lebesgue_measure (A \ Cm' m) ≤ (↑(ε / 2^(m+2) : ℝ) : EReal) := by
    intro m
    rw [hACm'_eq m]
    exact hCm_bound m
  have hAD_sub : A \ D ⊆ ⋃ m, (A \ Cm' m) := by
    intro x hx
    rcases hx with ⟨hxA, hxD⟩
    rw [Set.mem_iUnion]
    have hxexists : ∃ m, x ∉ Cm' m := by
      by_contra hnone
      push_neg at hnone
      exact hxD (Set.mem_iInter.mpr hnone)
    rcases hxexists with ⟨m, hm⟩
    exact ⟨m, hxA, hm⟩
  have hterm : ∀ m : ℕ, (ε / 2^(m+2) : ℝ) = (ε / 2) / 2^(m+1) := by
    intro m
    have hp : (2 : ℝ)^(m+2) = 2 * (2 : ℝ)^(m+1) := by
      rw [pow_succ]
      ring
    rw [hp]
    rw [← div_div]
  have hconv_ereal : ∀ (X : ℝ) (k : ℕ), (X / 2^(k+1) : EReal) = (↑(X / 2^(k+1) : ℝ) : EReal) := by
    intro X k
    rw [EReal.coe_div, EReal.coe_pow]
    rfl
  have hnonneg : ∀ m, 0 ≤ (↑(ε / 2^(m+2) : ℝ) : EReal) := by
    intro m
    exact EReal.coe_nonneg.mpr (div_nonneg (le_of_lt hε) (le_of_lt (pow_pos (by norm_num) (m + 2))))
  have hnn : ∀ m, 0 ≤ Lebesgue_measure (A \ Cm' m) := fun m => Lebesgue_outer_measure.nonneg _
  have hsum_le : (∑' m : ℕ, Lebesgue_measure (A \ Cm' m)) ≤ (↑(ε / 2 : ℝ) : EReal) := by
    calc
      (∑' m : ℕ, Lebesgue_measure (A \ Cm' m)) ≤ ∑' m : ℕ, (↑(ε / 2^(m+2) : ℝ) : EReal) := by
        rw [EReal.tsum_eq_ennreal_of_nonneg (f := fun m => Lebesgue_measure (A \ Cm' m)) hnn]
        rw [EReal.tsum_eq_ennreal_of_nonneg (f := fun m => (↑(ε / 2^(m+2) : ℝ) : EReal)) hnonneg]
        rw [EReal.coe_ennreal_le_coe_ennreal_iff]
        apply ENNReal.tsum_le_tsum
        intro m
        exact EReal.toENNReal_le_toENNReal (hACm'_le m)
      _ = ∑' m : ℕ, ((ε / 2) / 2^(m+1) : EReal) := by
        apply tsum_congr
        intro m
        calc
          (↑(ε / 2^(m+2) : ℝ) : EReal) = (↑((ε / 2) / 2^(m+1) : ℝ) : EReal) := by
            congr 1
            exact hterm m
          _ = ((ε / 2) / 2^(m+1) : EReal) := (hconv_ereal (ε / 2) m).symm
      _ ≤ (↑(ε / 2 : ℝ) : EReal) := by
        have hg := egorov_tsum_geometric (half_pos hε)
        simpa using hg
  have hAD_le : Lebesgue_measure (A \ D) ≤ (↑(ε / 2 : ℝ) : EReal) := by
    calc
      Lebesgue_measure (A \ D) ≤ Lebesgue_measure (⋃ m, (A \ Cm' m)) :=
        Lebesgue_outer_measure.mono hAD_sub
      _ ≤ ∑' m : ℕ, Lebesgue_measure (A \ Cm' m) := Lebesgue_outer_measure.union_le _
      _ ≤ (↑(ε / 2 : ℝ) : EReal) := hsum_le
  -- Egorov on D: uniform convergence of sA to fA off a small E₀ ⊆ D
  obtain ⟨E₀, hE₀_meas, hE₀_sub, hE₀_le, hE₀_uni⟩ :=
    egorov_on_finite_set (f := sA) (g := fA) (hf := hsA_meas) (hg := hfA_meas)
      (hfg := hConvAe) (A := D) (hA := hD_meas) (hAf := hD_fin)
      (ε := ε / 2) (hε := half_pos hε)
  -- F = D \ E₀: sA m continuous on F, uniform limit fA continuous on F
  set F : Set (EuclideanSpace' d) := D \ E₀
  have hF_sub_D : F ⊆ D := by
    intro x hx
    exact hx.1
  have hF_sub_A : F ⊆ A := Set.Subset.trans hF_sub_D hD_sub_A
  have hF_meas : LebesgueMeasurable F := by
    dsimp [F]
    exact hD_meas.inter (LebesgueMeasurable.complement hE₀_meas)
  have hsA_contOn_D : ∀ m, ContinuousOn (sA m) D := by
    intro m
    have hcontOn_Cm : ContinuousOn (sA m) (Cm m) :=
      (continuousOn_iff_continuous_restrict (f := sA m) (s := Cm m)).mpr (hCm_cont m)
    have hcontOn_Cm' : ContinuousOn (sA m) (Cm' m) :=
      hcontOn_Cm.mono (by intro x hx; exact hx.1)
    exact hcontOn_Cm'.mono (Set.iInter_subset Cm' m)
  have hsA_contOn_F : ∀ m, ContinuousOn (sA m) F := fun m =>
    (hsA_contOn_D m).mono hF_sub_D
  have hcontOnF_fA : ContinuousOn fA F :=
    uniform_converges_continuousOn sA fA F hE₀_uni hsA_contOn_F
  have hcontF_fA : Continuous (fun x : F => fA x.val) :=
    (continuousOn_iff_continuous_restrict (f := fA) (s := F)).mp hcontOnF_fA
  -- fA agrees with f on F (since F ⊆ A)
  have hFA_eq : ∀ x : F, fA x.val = f x.val := by
    intro x
    have hxA : x.val ∈ A := hF_sub_A x.2
    dsimp [fA]
    simp [Complex.indicator, Real.complex_fun, Set.indicator'_of_mem hxA, mul_one]
  have hcontF_f : Continuous (fun x : F => f x.val) :=
    hcontF_fA.congr hFA_eq
  -- E = A \ F: measurable, inside A, small measure
  set E : Set (EuclideanSpace' d) := A \ F
  have hE_meas : LebesgueMeasurable E := by
    dsimp [E]
    exact hA.inter (LebesgueMeasurable.complement hF_meas)
  have hE_sub : E ⊆ A := by
    intro x hx
    exact hx.1
  have hE_le : Lebesgue_measure E ≤ ε := by
    have hsub : E ⊆ (A \ D) ∪ E₀ := by
      intro x hx
      dsimp [E] at hx
      have hxA : x ∈ A := hx.1
      have hxnot : x ∉ D \ E₀ := hx.2
      by_cases hxD : x ∈ D
      · right
        by_contra hxE0
        exact hxnot ⟨hxD, hxE0⟩
      · left
        exact ⟨hxA, hxD⟩
    calc
      Lebesgue_measure E ≤ Lebesgue_measure ((A \ D) ∪ E₀) := Lebesgue_outer_measure.mono hsub
      _ ≤ Lebesgue_measure (A \ D) + Lebesgue_measure E₀ := by
        let S : Fin 2 → Set (EuclideanSpace' d) := ![A \ D, E₀]
        have h_union : ⋃ i : Fin 2, S i = (A \ D) ∪ E₀ := by
          ext x; simp [S]
        calc
          Lebesgue_measure ((A \ D) ∪ E₀) = Lebesgue_measure (⋃ i : Fin 2, S i) := by rw [h_union]
          _ ≤ ∑ i : Fin 2, Lebesgue_measure (S i) := Lebesgue_outer_measure.finite_union_le S
          _ = Lebesgue_measure (A \ D) + Lebesgue_measure E₀ := by simp [S]
      _ ≤ (↑(ε / 2 : ℝ) : EReal) + (↑(ε / 2 : ℝ) : EReal) := add_le_add hAD_le hE₀_le
      _ = (ε : EReal) := by
        rw [← EReal.coe_add]
        congr 1
        norm_num
  have hAE : (A \ E : Set (EuclideanSpace' d)) = F := by
    dsimp [E]
    ext x
    constructor
    · intro hx
      by_contra hxn
      exact hx.2 ⟨hx.1, hxn⟩
    · intro hx
      exact ⟨hF_sub_A hx, fun h => h.2 hx⟩
  refine ⟨E, hE_meas, hE_sub, hE_le, ?_⟩
  rw [hAE]
  exact hcontF_f

/-- The global Lusin assembly: if f is continuous off a small set in every box of an
    exhausting nested family, then f is continuous off a small set in the whole space. -/
lemma lusin_assembly {d:ℕ} (f : EuclideanSpace' d → ℂ)
    (A : ℕ → Set (EuclideanSpace' d))
    (_hA_meas : ∀ N, LebesgueMeasurable (A N))
    (hA_int : ∀ N, A N ⊆ interior (A (N+1)))
    (hA_cover : ∀ x, ∃ N, x ∈ A N)
    (ε : ℝ) (hε : 0 < ε)
    (hbox : ∀ N, ∃ E : Set (EuclideanSpace' d), LebesgueMeasurable E ∧ E ⊆ A N ∧
      Lebesgue_measure E ≤ (↑(ε / 2^(N+1) : ℝ) : EReal) ∧
      Continuous (fun x : (A N \ E : Set (EuclideanSpace' d)) => f x.val)) :
    ∃ E : Set (EuclideanSpace' d), LebesgueMeasurable E ∧ Lebesgue_measure E ≤ ε ∧
      Continuous (fun x : (Eᶜ : Set (EuclideanSpace' d)) => f x.val) := by
  choose E_N hE_N_meas _ hE_N_le hE_N_cont using hbox
  let E : Set (EuclideanSpace' d) := ⋃ N : ℕ, E_N N
  have hE_meas : LebesgueMeasurable E := LebesgueMeasurable.countable_union (fun N => hE_N_meas N)
  have hconv_ereal : ∀ (X : ℝ) (k : ℕ), (X / 2^(k+1) : EReal) = (↑(X / 2^(k+1) : ℝ) : EReal) := by
    intro X k
    rw [EReal.coe_div, EReal.coe_pow]
    rfl
  have hnonneg : ∀ N, 0 ≤ (↑(ε / 2^(N+1) : ℝ) : EReal) := by
    intro N
    exact EReal.coe_nonneg.mpr (div_nonneg (le_of_lt hε) (le_of_lt (pow_pos (by norm_num) (N + 1))))
  have hE_le : Lebesgue_measure E ≤ (↑ε : EReal) := by
    calc
      Lebesgue_measure E ≤ ∑' N : ℕ, Lebesgue_measure (E_N N) :=
        Lebesgue_outer_measure.union_le (fun N => E_N N)
      _ ≤ ∑' N : ℕ, (↑(ε / 2^(N+1) : ℝ) : EReal) := by
        rw [EReal.tsum_eq_ennreal_of_nonneg (f := fun N => Lebesgue_measure (E_N N))
          (fun N => Lebesgue_outer_measure.nonneg (E_N N))]
        rw [EReal.tsum_eq_ennreal_of_nonneg (f := fun N => (↑(ε / 2^(N+1) : ℝ) : EReal)) hnonneg]
        rw [EReal.coe_ennreal_le_coe_ennreal_iff]
        apply ENNReal.tsum_le_tsum
        intro N
        exact EReal.toENNReal_le_toENNReal (hE_N_le N)
      _ ≤ (↑ε : EReal) := by
        have hg := egorov_tsum_geometric hε
        simpa [hconv_ereal] using hg
  have hcontOn : ContinuousOn f Eᶜ := by
    intro x hxEc
    rcases hA_cover x with ⟨N₀, hxN₀⟩
    have hxint : x ∈ interior (A (N₀ + 1)) := hA_int N₀ hxN₀
    have hxnotEN : x ∉ E_N (N₀ + 1) := fun h => hxEc (Set.subset_iUnion (fun N => E_N N) (N₀ + 1) h)
    have hcontOn_AN : ContinuousOn f (A (N₀ + 1) \ E_N (N₀ + 1)) :=
      (continuousOn_iff_continuous_restrict (f := f) (s := A (N₀ + 1) \ E_N (N₀ + 1))).mpr (hE_N_cont (N₀ + 1))
    have hxmem : x ∈ A (N₀ + 1) \ E_N (N₀ + 1) := ⟨interior_subset hxint, hxnotEN⟩
    have hcont_at : ContinuousWithinAt f (A (N₀ + 1) \ E_N (N₀ + 1)) x :=
      hcontOn_AN.continuousWithinAt hxmem
    have hA_nhds : A (N₀ + 1) ∈ nhds x := mem_interior_iff_mem_nhds.mp hxint
    have hmem : A (N₀ + 1) \ E_N (N₀ + 1) ∈ nhdsWithin x Eᶜ := by
      apply mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
      refine ⟨A (N₀ + 1), hA_nhds, ?_⟩
      intro y hy
      exact ⟨hy.1, fun h => hy.2 (Set.subset_iUnion (fun N => E_N N) (N₀ + 1) h)⟩
    exact hcont_at.mono_of_mem_nhdsWithin hmem
  have hcont : Continuous (fun x : (Eᶜ : Set (EuclideanSpace' d)) => f x.val) :=
    (continuousOn_iff_continuous_restrict (f := f) (s := Eᶜ)).mp hcontOn
  exact ⟨E, hE_meas, hE_le, hcont⟩

/-- The box A N is contained in the interior of the next box. -/
lemma egorov_A_interior {d : ℕ} (N : ℕ) : egorov_A (d := d) N ⊆ interior (egorov_A (d := d) (N+1)) := by
  intro x hx
  rw [mem_interior]
  refine ⟨Metric.ball x (1 / 2), ?_, Metric.isOpen_ball, Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2)⟩
  intro y hy
  have hxcoord : ∀ i : Fin d, x i ∈ Set.Icc (-(N : ℝ)) (N : ℝ) := by
    simpa [egorov_A, egorov_box, Box.mem_toSet, BoundedInterval.set_Icc] using hx
  have hyle : ∀ i : Fin d, |y i - x i| < 1 / 2 := by
    intro i
    have hnorm : ‖y - x‖ < 1 / 2 := by
      simpa [dist_eq_norm] using (Metric.mem_ball.mp hy)
    exact lt_of_le_of_lt (EuclideanSpace'.coord_le_norm (y - x) i) hnorm
  have hysub : ∀ i : Fin d, y i ∈ Set.Icc (-(N + 1 : ℝ)) (N + 1 : ℝ) := by
    intro i
    rcases hxcoord i with ⟨hlo, hhi⟩
    constructor
    · have hlt : -(1 / 2) < y i - x i := (abs_lt.mp (hyle i)).1
      linarith [hlo, hlt]
    · have hlt : y i - x i < 1 / 2 := (abs_lt.mp (hyle i)).2
      linarith [hhi, hlt]
  simpa [egorov_A, egorov_box, Box.mem_toSet, BoundedInterval.set_Icc] using hysub

/-- Every point lies in some box A N. -/
lemma egorov_A_cover {d : ℕ} (x : EuclideanSpace' d) : ∃ N, x ∈ egorov_A (d := d) N := by
  obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
  refine ⟨N, ?_⟩
  intro i
  have hcoord : |x i| ≤ ‖x‖ := EuclideanSpace'.coord_le_norm x i
  have hlt : |x i| < (N : ℝ) := lt_of_le_of_lt hcoord hN
  exact Set.mem_Icc.mpr (abs_le.mp (le_of_lt hlt))

/-- Theorem 1.3.28 (Lusin's theorem) -/
theorem ComplexMeasurable.approx_by_continuous_outside_small {d:ℕ} {f : EuclideanSpace' d → ℂ}
  (hf: ComplexMeasurable f)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (g : EuclideanSpace' d → ℂ) (E: Set (EuclideanSpace' d)), Continuous (fun x : (Eᶜ : Set (EuclideanSpace' d)) => g x.val) ∧ LebesgueMeasurable E ∧
      Lebesgue_measure E ≤ ε ∧
      ∀ x ∉ E, g x = f x := by
  have hbox : ∀ N : ℕ, ∃ E : Set (EuclideanSpace' d), LebesgueMeasurable E ∧ E ⊆ egorov_A (d := d) N ∧
      Lebesgue_measure E ≤ (↑(ε / 2^(N+1) : ℝ) : EReal) ∧
      Continuous (fun x : (egorov_A (d := d) N \ E : Set (EuclideanSpace' d)) => f x.val) := by
    intro N
    have hεN : 0 < ε / 2^(N+1) := div_pos hε (pow_pos (by norm_num) (N+1))
    exact box_lusin (egorov_A (d := d) N) (egorov_A_meas N) (egorov_A_fin N) f hf (ε / 2^(N+1)) hεN
  obtain ⟨E, hE_meas, hE_le, hcont⟩ :=
    lusin_assembly f egorov_A egorov_A_meas egorov_A_interior egorov_A_cover ε hε hbox
  refine ⟨f, E, hcont, hE_meas, hE_le, ?_⟩
  intro x hx
  rfl

theorem ComplexAbsolutelyIntegrable.approx_by_continuous_outside_small {d:ℕ} {f : EuclideanSpace' d → ℂ}
  (hf: ComplexAbsolutelyIntegrable f)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (g : EuclideanSpace' d → ℂ) (E: Set (EuclideanSpace' d)), Continuous (fun x : (Eᶜ : Set (EuclideanSpace' d)) => g x.val) ∧ LebesgueMeasurable E ∧
      Lebesgue_measure E ≤ ε ∧
      ∀ x ∉ E, g x = f x := by
  exact ComplexMeasurable.approx_by_continuous_outside_small hf.1 ε hε

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
  ∃ (g : EuclideanSpace' d → ℂ) (E: Set (EuclideanSpace' d)), Continuous (fun x : (Eᶜ : Set (EuclideanSpace' d)) => g x.val) ∧ LebesgueMeasurable E ∧
      Lebesgue_measure E ≤ ε ∧
      ∀ x ∉ E, g x = f x := by
  have hfmeas : ComplexMeasurable f := by
    have hseq : ∀ N : ℕ, ComplexMeasurable (fun x => f x * Complex.indicator (Metric.ball (0 : EuclideanSpace' d) (N : ℝ)) x) := by
      intro N
      have hAI : ComplexAbsolutelyIntegrableOn f (Metric.ball (0 : EuclideanSpace' d) (N : ℝ)) :=
        hf (Metric.ball (0 : EuclideanSpace' d) (N : ℝ))
          ⟨IsOpen.measurable (Metric.isOpen_ball : IsOpen (Metric.ball (0 : EuclideanSpace' d) (N : ℝ))), Metric.isBounded_ball⟩
      exact hAI.1
    exact ComplexMeasurable.aeLimit_of_pointwiseAe hseq (by
      apply AlmostAlways.ofAlways
      intro x
      obtain ⟨N₀, hN₀⟩ := exists_nat_gt ‖x‖
      have hconst : Tendsto (fun _ : ℕ => f x) atTop (nhds (f x)) := tendsto_const_nhds
      refine hconst.congr' ?_
      filter_upwards [eventually_ge_atTop N₀] with N hN
      have hxN : x ∈ Metric.ball (0 : EuclideanSpace' d) (N : ℝ) := by
        rw [Metric.mem_ball, dist_zero_right]
        exact lt_of_lt_of_le hN₀ (Nat.cast_le.mpr hN)
      simp [Complex.indicator, Real.complex_fun, Set.indicator'_of_mem hxN, mul_one])
  exact ComplexMeasurable.approx_by_continuous_outside_small hfmeas ε hε

/-- Every finite-measure measurable set is contained in an open set of barely larger measure. -/
lemma enlarge_open {d:ℕ} {E : Set (EuclideanSpace' d)} (hE : LebesgueMeasurable E)
    (hEf : Lebesgue_measure E < ⊤) (δ : ℝ) (hδ : 0 < δ) :
    ∃ O : Set (EuclideanSpace' d), IsOpen O ∧ E ⊆ O ∧ Lebesgue_measure O ≤ Lebesgue_measure E + (↑δ : EReal) := by
  classical
  have hδ_ereal : 0 < (↑δ : EReal) := EReal.coe_pos.mpr hδ
  have hTFAE := (LebesgueMeasurable.finite_TFAE E).out 0 1
  obtain ⟨U, hU_open, hE_sub_U, _hU_fin, hU_diff⟩ :=
    hTFAE.mp ⟨hE, hEf⟩ (↑δ : EReal) hδ_ereal
  refine ⟨U, hU_open, hE_sub_U, ?_⟩
  have hsub : U ⊆ E ∪ (U \ E) := by
    intro x hx
    by_cases hxE : x ∈ E
    · exact Or.inl hxE
    · exact Or.inr ⟨hx, hxE⟩
  calc
    Lebesgue_measure U ≤ Lebesgue_measure (E ∪ (U \ E)) := Lebesgue_outer_measure.mono hsub
    _ ≤ Lebesgue_measure E + Lebesgue_measure (U \ E) := by
      let S : Fin 2 → Set (EuclideanSpace' d) := ![E, U \ E]
      have h_union : ⋃ i : Fin 2, S i = E ∪ (U \ E) := by
        ext x
        simp [S]
        tauto
      calc
        Lebesgue_measure (E ∪ (U \ E)) = Lebesgue_measure (⋃ i : Fin 2, S i) := by rw [h_union]
        _ ≤ ∑ i : Fin 2, Lebesgue_measure (S i) := Lebesgue_outer_measure.finite_union_le S
        _ = Lebesgue_measure E + Lebesgue_measure (U \ E) := by simp [S]
    _ ≤ Lebesgue_measure E + (↑δ : EReal) := add_le_add le_rfl hU_diff

/-- Lusin's theorem in closed-set form: a complex measurable function is continuous on a closed
    set whose complement has small measure. -/
lemma closed_lusin {d:ℕ} (f : EuclideanSpace' d → ℂ) (hf : ComplexMeasurable f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ F : Set (EuclideanSpace' d), IsClosed F ∧ Lebesgue_measure (Fᶜ) ≤ ε ∧
      Continuous (fun x : F => f x.val) := by
  classical
  have hεN : ∀ N : ℕ, 0 < ε / 2^(N+2) := fun N => div_pos hε (pow_pos (by norm_num) (N+2))
  have hbox_orig : ∀ N : ℕ, ∃ E : Set (EuclideanSpace' d), LebesgueMeasurable E ∧ E ⊆ egorov_A (d := d) N ∧
      Lebesgue_measure E ≤ (↑(ε / 2^(N+2) : ℝ) : EReal) ∧
      Continuous (fun x : (egorov_A (d := d) N \ E : Set (EuclideanSpace' d)) => f x.val) := fun N =>
    box_lusin (egorov_A (d := d) N) (egorov_A_meas N) (egorov_A_fin N) f hf (ε / 2^(N+2)) (hεN N)
  choose E_N hE_N_meas hE_N_sub hE_N_le hE_N_cont using hbox_orig
  have hE_N_fin : ∀ N, Lebesgue_measure (E_N N) < ⊤ := fun N =>
    lt_of_le_of_lt (Lebesgue_outer_measure.mono (hE_N_sub N)) (egorov_A_fin N)
  -- enlarge each E_N to an open set O_N
  have hO : ∀ N : ℕ, ∃ O : Set (EuclideanSpace' d), IsOpen O ∧ E_N N ⊆ O ∧
      Lebesgue_measure O ≤ (↑(ε / 2^(N+1) : ℝ) : EReal) ∧
      Continuous (fun x : (egorov_A (d := d) N \ O : Set (EuclideanSpace' d)) => f x.val) := by
    intro N
    obtain ⟨O, hO_open, hE_sub_O, hO_le_E⟩ := enlarge_open (hE_N_meas N) (hE_N_fin N) (ε / 2^(N+2)) (hεN N)
    have hO_le : Lebesgue_measure O ≤ (↑(ε / 2^(N+1) : ℝ) : EReal) := by
      calc
        Lebesgue_measure O ≤ Lebesgue_measure (E_N N) + (↑(ε / 2^(N+2) : ℝ) : EReal) := hO_le_E
        _ ≤ (↑(ε / 2^(N+2) : ℝ) : EReal) + (↑(ε / 2^(N+2) : ℝ) : EReal) := add_le_add (hE_N_le N) le_rfl
        _ = (↑(ε / 2^(N+1) : ℝ) : EReal) := by
          rw [← EReal.coe_add]
          congr 1
          have hp : (2 : ℝ)^(N+2) = 2 * (2 : ℝ)^(N+1) := by
            rw [pow_succ]
            ring
          rw [hp]
          field_simp
          ring
    have hcontOn_E : ContinuousOn f (egorov_A (d := d) N \ E_N N) :=
      (continuousOn_iff_continuous_restrict (f := f) (s := egorov_A (d := d) N \ E_N N)).mpr (hE_N_cont N)
    have hsub : egorov_A (d := d) N \ O ⊆ egorov_A (d := d) N \ E_N N := by
      intro x hx
      exact ⟨hx.1, fun hxE => hx.2 (hE_sub_O hxE)⟩
    have hcontOn_O : ContinuousOn f (egorov_A (d := d) N \ O) := hcontOn_E.mono hsub
    have hcont : Continuous (fun x : (egorov_A (d := d) N \ O : Set (EuclideanSpace' d)) => f x.val) :=
      (continuousOn_iff_continuous_restrict (f := f) (s := egorov_A (d := d) N \ O)).mp hcontOn_O
    exact ⟨O, hO_open, hE_sub_O, hO_le, hcont⟩
  choose O_N hO_open hE_sub_O hO_le hO_cont using hO
  -- E := ⋃ N, O_N N is open
  let E : Set (EuclideanSpace' d) := ⋃ N : ℕ, O_N N
  have hE_open : IsOpen E := by
    dsimp [E]
    exact isOpen_iUnion (fun N => hO_open N)
  have hconv_ereal : ∀ (X : ℝ) (k : ℕ), (X / 2^(k+1) : EReal) = (↑(X / 2^(k+1) : ℝ) : EReal) := by
    intro X k
    rw [EReal.coe_div, EReal.coe_pow]
    rfl
  have hnonneg : ∀ N, 0 ≤ (↑(ε / 2^(N+1) : ℝ) : EReal) := by
    intro N
    exact EReal.coe_nonneg.mpr (div_nonneg (le_of_lt hε) (le_of_lt (pow_pos (by norm_num) (N + 1))))
  have hE_le : Lebesgue_measure E ≤ (↑ε : EReal) := by
    calc
      Lebesgue_measure E ≤ ∑' N : ℕ, Lebesgue_measure (O_N N) :=
        Lebesgue_outer_measure.union_le (fun N => O_N N)
      _ ≤ ∑' N : ℕ, (↑(ε / 2^(N+1) : ℝ) : EReal) := by
        rw [EReal.tsum_eq_ennreal_of_nonneg (f := fun N => Lebesgue_measure (O_N N))
          (fun N => Lebesgue_outer_measure.nonneg (O_N N))]
        rw [EReal.tsum_eq_ennreal_of_nonneg (f := fun N => (↑(ε / 2^(N+1) : ℝ) : EReal)) hnonneg]
        rw [EReal.coe_ennreal_le_coe_ennreal_iff]
        apply ENNReal.tsum_le_tsum
        intro N
        exact EReal.toENNReal_le_toENNReal (hO_le N)
      _ ≤ (↑ε : EReal) := by
        have hg := egorov_tsum_geometric hε
        simpa [hconv_ereal] using hg
  -- continuity of f on Eᶜ
  have hcontOn : ContinuousOn f Eᶜ := by
    intro x hxEc
    rcases egorov_A_cover x with ⟨N₀, hxN₀⟩
    have hxint : x ∈ interior (egorov_A (d := d) (N₀ + 1)) := egorov_A_interior N₀ hxN₀
    have hxnotON : x ∉ O_N (N₀ + 1) := fun h => hxEc (Set.subset_iUnion (fun N => O_N N) (N₀ + 1) h)
    have hcontOn_AN : ContinuousOn f (egorov_A (d := d) (N₀ + 1) \ O_N (N₀ + 1)) :=
      (continuousOn_iff_continuous_restrict (f := f) (s := egorov_A (d := d) (N₀ + 1) \ O_N (N₀ + 1))).mpr
        (hO_cont (N₀ + 1))
    have hxmem : x ∈ egorov_A (d := d) (N₀ + 1) \ O_N (N₀ + 1) := ⟨interior_subset hxint, hxnotON⟩
    have hcont_at : ContinuousWithinAt f (egorov_A (d := d) (N₀ + 1) \ O_N (N₀ + 1)) x :=
      hcontOn_AN.continuousWithinAt hxmem
    have hA_nhds : egorov_A (d := d) (N₀ + 1) ∈ nhds x := mem_interior_iff_mem_nhds.mp hxint
    have hmem : egorov_A (d := d) (N₀ + 1) \ O_N (N₀ + 1) ∈ nhdsWithin x Eᶜ := by
      apply mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
      refine ⟨egorov_A (d := d) (N₀ + 1), hA_nhds, ?_⟩
      intro y hy
      exact ⟨hy.1, fun h => hy.2 (Set.subset_iUnion (fun N => O_N N) (N₀ + 1) h)⟩
    exact hcont_at.mono_of_mem_nhdsWithin hmem
  have hcont : Continuous (fun x : (Eᶜ : Set (EuclideanSpace' d)) => f x.val) :=
    (continuousOn_iff_continuous_restrict (f := f) (s := Eᶜ)).mp hcontOn
  refine ⟨Eᶜ, hE_open.isClosed_compl, ?_, ?_⟩
  · simpa using hE_le
  · exact hcont

/-- Tail of the geometric series: sum over n of 1/2^(n+m+1) is at most 1/2^m. -/
private lemma tail_tsum_geometric_le (m : ℕ) :
    (∑' n : ℕ, (1 / 2^(n + m + 1) : ℝ)) ≤ (1 / 2^m : ℝ) := by
  let f : ℕ → ℝ := fun n => (1 / 2 : ℝ)^(n + 1)
  have hf_tsum : (∑' n : ℕ, f n) = 1 := by
    calc
      (∑' n : ℕ, f n) = ∑' n : ℕ, ((1 / 2 : ℝ) * (1 / 2 : ℝ)^n) := by
        apply tsum_congr
        intro n
        simp [f, pow_succ']
      _ = (1 / 2 : ℝ) * (∑' n : ℕ, (1 / 2 : ℝ)^n) := by rw [tsum_mul_left]
      _ = (1 / 2 : ℝ) * ((1 - (1 / 2 : ℝ))⁻¹) := by
        congr 1
        exact tsum_geometric_of_abs_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
      _ = 1 := by norm_num
  have hf_sum : Summable f := by
    have hg : Summable (fun n : ℕ => (1 / 2 : ℝ)^n) :=
      summable_geometric_of_abs_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
    simpa [f, pow_succ'] using (Summable.mul_left (1 / 2 : ℝ) hg)
  have htail : HasSum (fun n : ℕ => f (n + m)) (1 - ∑ i ∈ Finset.range m, f i) := by
    rw [hasSum_nat_add_iff (f := f) (k := m) (g := 1 - ∑ i ∈ Finset.range m, f i)]
    have hf_has : HasSum f (∑' n, f n) := hf_sum.hasSum
    convert hf_has using 1
    rw [hf_tsum]
    ring
  have hgeom_part : (∑ i ∈ Finset.range m, (1 / 2 : ℝ)^i) = (1 - (1 / 2 : ℝ)^m) / (1 / 2) := by
    have hg := geom_sum_mul (x := (1 / 2 : ℝ)) (n := m)
    have hx0 : (1 / 2 : ℝ) - 1 ≠ 0 := by norm_num
    calc
      (∑ i ∈ Finset.range m, (1 / 2 : ℝ)^i)
          = ((∑ i ∈ Finset.range m, (1 / 2 : ℝ)^i) * ((1 / 2 : ℝ) - 1)) / ((1 / 2 : ℝ) - 1) := by
        rw [mul_div_cancel_right₀ _ hx0]
      _ = ((1 / 2 : ℝ)^m - 1) / ((1 / 2 : ℝ) - 1) := by rw [hg]
      _ = (1 - (1 / 2 : ℝ)^m) / (1 / 2) := by
        field_simp [hx0]
        ring
  have hsum_range : (∑ i ∈ Finset.range m, f i) = 1 - (1 / 2 : ℝ)^m := by
    calc
      (∑ i ∈ Finset.range m, f i) = ∑ i ∈ Finset.range m, ((1 / 2 : ℝ) * (1 / 2 : ℝ)^i) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [f, pow_succ']
      _ = (1 / 2 : ℝ) * (∑ i ∈ Finset.range m, (1 / 2 : ℝ)^i) := by rw [Finset.mul_sum]
      _ = (1 / 2 : ℝ) * ((1 - (1 / 2 : ℝ)^m) / (1 / 2)) := by rw [hgeom_part]
      _ = 1 - (1 / 2 : ℝ)^m := by field_simp
  have hle1 : 1 - ∑ i ∈ Finset.range m, f i ≤ (1 / 2 : ℝ)^m := by
    rw [hsum_range]
    linarith
  calc
    (∑' n : ℕ, (1 / 2^(n + m + 1) : ℝ)) = ∑' n : ℕ, f (n + m) := by
      apply tsum_congr
      intro n
      simp [f]
    _ ≤ (1 / 2 : ℝ)^m := by
      rw [htail.tsum_eq]
      exact hle1
    _ = (1 / 2^m : ℝ) := by
      rw [div_pow]
      simp

/-- Borel-Cantelli: if the measures of E n decay geometrically, the limsup set is null. -/
lemma borel_cantelli_null {d:ℕ} {E : ℕ → Set (EuclideanSpace' d)}
    (_hE_meas : ∀ n, LebesgueMeasurable (E n))
    (hE : ∀ n, Lebesgue_measure (E n) ≤ (↑(1 / 2^(n+1) : ℝ) : EReal)) :
    Lebesgue_measure (⋂ m, ⋃ n ≥ m, E n) = 0 := by
  classical
  have hreindex : ∀ m, (⋃ n ≥ m, E n) = ⋃ k : ℕ, E (k + m) := by
    intro m
    ext x
    constructor
    · intro hxmem
      rw [Set.mem_iUnion] at hxmem
      rcases hxmem with ⟨n, hxinner⟩
      rw [Set.mem_iUnion] at hxinner
      rcases hxinner with ⟨hmn, hx⟩
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hmn
      rw [Set.mem_iUnion]
      refine ⟨k, ?_⟩
      simpa [hk, Nat.add_comm] using hx
    · intro hxmem
      rw [Set.mem_iUnion] at hxmem
      rcases hxmem with ⟨k, hx⟩
      rw [Set.mem_iUnion]
      refine ⟨k + m, ?_⟩
      rw [Set.mem_iUnion]
      refine ⟨by omega, ?_⟩
      exact hx
  have htail_ereal : ∀ m, (∑' k : ℕ, (↑(1 / 2^(k + m + 1) : ℝ) : EReal)) ≤ (↑(1 / 2^m : ℝ) : EReal) := by
    intro m
    have hnn : ∀ k, 0 ≤ (1 / 2^(k + m + 1) : ℝ) := by
      intro k
      positivity
    have hg_sum : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ (k + m + 1)) := by
      convert (Summable.mul_left ((1 / 2 : ℝ) ^ (m + 1))
        (summable_geometric_of_abs_lt_one (r := (1 / 2 : ℝ)) (by norm_num))) using 1
      ext k
      rw [← pow_add]
      congr 1
      omega
    have hs : Summable (fun k : ℕ => (1 / 2^(k + m + 1) : ℝ)) := by
      simpa [div_pow] using hg_sum
    have hle_real : (∑' k : ℕ, (1 / 2^(k + m + 1) : ℝ)) ≤ (1 / 2^m : ℝ) := tail_tsum_geometric_le m
    rw [← EReal.coe_tsum_of_nonneg hnn hs]
    exact_mod_cast hle_real
  have htail_le : ∀ m, Lebesgue_measure (⋃ n ≥ m, E n) ≤ (↑(1 / 2^m : ℝ) : EReal) := by
    intro m
    calc
      Lebesgue_measure (⋃ n ≥ m, E n) = Lebesgue_measure (⋃ k : ℕ, E (k + m)) := by rw [hreindex m]
      _ ≤ ∑' k : ℕ, Lebesgue_measure (E (k + m)) :=
        Lebesgue_outer_measure.union_le (fun k => E (k + m))
      _ ≤ ∑' k : ℕ, (↑(1 / 2^(k + m + 1) : ℝ) : EReal) := by
        rw [EReal.tsum_eq_ennreal_of_nonneg (f := fun k => Lebesgue_measure (E (k + m)))
          (fun k => Lebesgue_outer_measure.nonneg (E (k + m)))]
        rw [EReal.tsum_eq_ennreal_of_nonneg (f := fun k => (↑(1 / 2^(k + m + 1) : ℝ) : EReal))
          (fun k => EReal.coe_nonneg.mpr (by positivity))]
        rw [EReal.coe_ennreal_le_coe_ennreal_iff]
        apply ENNReal.tsum_le_tsum
        intro k
        exact EReal.toENNReal_le_toENNReal (hE (k + m))
      _ ≤ (↑(1 / 2^m : ℝ) : EReal) := htail_ereal m
  let a : EReal := Lebesgue_measure (⋂ m, ⋃ n ≥ m, E n)
  have ha_le : ∀ m, a ≤ (↑(1 / 2^m : ℝ) : EReal) := by
    intro m
    calc
      a ≤ Lebesgue_measure (⋃ n ≥ m, E n) := by
        exact Lebesgue_outer_measure.mono (Set.iInter_subset (fun m' => ⋃ n ≥ m', E n) m)
      _ ≤ (↑(1 / 2^m : ℝ) : EReal) := htail_le m
  have ha_nonneg : 0 ≤ a := Lebesgue_outer_measure.nonneg _
  have ha_zero : a = 0 := by
    by_contra ha_ne
    have ha_pos : 0 < a := lt_of_le_of_ne ha_nonneg (Ne.symm ha_ne)
    have ha_lt_top : a < ⊤ := lt_of_le_of_lt (ha_le 0) (EReal.coe_lt_top (1 / 2^0 : ℝ))
    have ha_ne_top : a ≠ ⊤ := ne_of_lt ha_lt_top
    have ha_ne_bot : a ≠ ⊥ := ne_of_gt (lt_trans (by norm_num : (⊥ : EReal) < 0) ha_pos)
    have ha_toReal_eq : (a.toReal : EReal) = a := EReal.coe_toReal ha_ne_top ha_ne_bot
    have ha_toReal_pos : 0 < a.toReal := by
      exact EReal.coe_pos.mp (by simpa [ha_toReal_eq] using ha_pos)
    have htend : Tendsto (fun m : ℕ => (1 / 2 : ℝ) ^ m) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num)
    have hmem : Set.Iio (a.toReal) ∈ nhds (0 : ℝ) := IsOpen.mem_nhds isOpen_Iio ha_toReal_pos
    rcases (htend.eventually hmem).exists with ⟨m, hm⟩
    have hm_coe : (↑((1 / 2 : ℝ) ^ m) : EReal) = (↑(1 / 2^m : ℝ) : EReal) := by
      congr 1
      rw [div_pow]
      simp
    have hlt : (↑(1 / 2^m : ℝ) : EReal) < a := by
      rw [← hm_coe]
      rw [← ha_toReal_eq]
      exact_mod_cast hm
    exact (lt_irrefl a) (lt_of_le_of_lt (ha_le m) hlt)
  simpa [a] using ha_zero

/-- Forward direction of Exercise 1.3.24: a measurable function is the pointwise-a.e. limit
    of continuous functions. -/
lemma iff_pointwiseae_forward {d:ℕ} {f : EuclideanSpace' d → ℂ} (hf : ComplexMeasurable f) :
    ∃ (g : ℕ → EuclideanSpace' d → ℂ), (∀ n, Continuous (g n)) ∧ PointwiseAeConvergesTo g f := by
  classical
  have hclosed : ∀ n, ∃ F : Set (EuclideanSpace' d), IsClosed F ∧
      Lebesgue_measure (Fᶜ) ≤ (1 / 2^(n+1) : ℝ) ∧ Continuous (fun x : F => f x.val) :=
    fun n => closed_lusin f hf (1 / 2^(n+1)) (by positivity)
  choose F_n hF_closed hF_le hF_cont using hclosed
  have hg : ∀ n, ∃ g : EuclideanSpace' d → ℂ, Continuous g ∧ ∀ x ∈ F_n n, g x = f x := by
    intro n
    obtain ⟨g_map, hg_res⟩ := ContinuousMap.exists_restrict_eq (hF_closed n) ⟨fun x : F_n n => f x.val, hF_cont n⟩
    refine ⟨g_map, map_continuous g_map, ?_⟩
    intro x hx
    have hxeq := congrFun (congrArg ContinuousMap.toFun hg_res) ⟨x, hx⟩
    simpa using hxeq
  choose g_n hg_cont hg_agree using hg
  refine ⟨g_n, hg_cont, ?_⟩
  unfold PointwiseAeConvergesTo AlmostAlways
  let bad : Set (EuclideanSpace' d) := ⋂ m : ℕ, ⋃ n ≥ m, (F_n n)ᶜ
  have hbad_null : IsNull bad := by
    rw [IsNull]
    exact borel_cantelli_null (fun n => (IsClosed.measurable (hF_closed n)).complement) (fun n => hF_le n)
  apply IsNull.subset hbad_null
  intro x hx
  by_contra hnotbad
  have hnotbad' : ¬ ∀ m : ℕ, ∃ n : ℕ, m ≤ n ∧ x ∉ F_n n := by
    simpa [bad] using hnotbad
  push_neg at hnotbad'
  rcases hnotbad' with ⟨m, hm⟩
  have hxagree : ∀ n, m ≤ n → g_n n x = f x := fun n hmn => hg_agree n x (hm n hmn)
  have htend : atTop.Tendsto (fun n => g_n n x) (nhds (f x)) := by
    apply Filter.Tendsto.congr' ?_ tendsto_const_nhds
    exact (eventually_ge_atTop m).mono (fun n hmn => (hxagree n hmn).symm)
  exact hx htend

/-- Backward direction of Exercise 1.3.24: a pointwise-a.e. limit of continuous functions
    is measurable. -/
lemma iff_pointwiseae_backward {d:ℕ} {f : EuclideanSpace' d → ℂ}
    (h : ∃ (g : ℕ → EuclideanSpace' d → ℂ), (∀ n, Continuous (g n)) ∧ PointwiseAeConvergesTo g f) :
    ComplexMeasurable f := by
  rcases h with ⟨g, hg_cont, hconv⟩
  exact ComplexMeasurable.aeLimit_of_pointwiseAe (fun n => Continuous.ComplexMeasurable (hg_cont n)) hconv

/-- Exercise 1.3.24 -/
theorem ComplexMeasurable.iff_pointwiseae_of_continuous {d:ℕ} {f : EuclideanSpace' d → ℂ} :
  ComplexMeasurable f ↔
  ∃ (g : ℕ → EuclideanSpace' d → ℂ), (∀ n, Continuous (g n)) ∧ PointwiseAeConvergesTo g f := by
  constructor
  · exact iff_pointwiseae_forward
  · exact iff_pointwiseae_backward

/-- An unsigned measurable EReal-valued function which is finite a.e. agrees on its
    finite part with a real measurable function. -/
lemma unsigned_measurable_to_real {d:ℕ} {f : EuclideanSpace' d → EReal}
    (hf : UnsignedMeasurable f) :
    ∃ φ : EuclideanSpace' d → ℝ, RealMeasurable φ ∧ (∀ x, f x < ⊤ → (φ x : EReal) = f x) := by
  let φ : EuclideanSpace' d → ℝ := fun x => (f x).toReal
  refine ⟨φ, ?_, ?_⟩
  · classical
    have h10 : ∀ K : Set EReal, IsClosed K → LebesgueMeasurable (f ⁻¹' K) :=
      (((UnsignedMeasurable.TFAE hf.1).out 10 0
        (a := ∀ K : Set EReal, IsClosed K → LebesgueMeasurable (f ⁻¹' K))
        (b := _root_.UnsignedMeasurable f)).mpr hf)
    apply ((RealMeasurable_TFAE_helpers.RealMeasurable.TFAE (f := φ)).out 4 0
      (a := ∀ K : Set ℝ, IsClosed K → LebesgueMeasurable (φ ⁻¹' K))
      (b := RealMeasurable φ)).mp
    intro K hK
    let C : ℕ → Set ℝ := fun n => K ∩ Set.Icc (-(n : ℝ)) (n : ℝ)
    let S : ℕ → Set EReal := fun n => {y : EReal | y.toReal ∈ C n}
    have hC_comp : ∀ n, IsCompact (C n) := by
      intro n
      exact (isCompact_Icc).inter_left hK
    have hC_closed : ∀ n, IsClosed (C n) := fun n => (hC_comp n).isClosed
    have himg_closed : ∀ n, IsClosed (Real.toEReal '' (C n)) :=
      fun n => ((hC_comp n).image continuous_coe_real_ereal).isClosed
    have hS_eq : ∀ n, S n = (Real.toEReal '' (C n)) ∪
        (if (0 : ℝ) ∈ C n then ({⊤} : Set EReal) ∪ {⊥} else ∅) := by
      intro n
      ext y
      cases y with
      | bot =>
          by_cases h0 : (0 : ℝ) ∈ C n
          · simp [S, h0, EReal.toReal_bot]
          · simp [S, h0, EReal.toReal_bot]
      | top =>
          by_cases h0 : (0 : ℝ) ∈ C n
          · simp [S, h0, EReal.toReal_top]
          · simp [S, h0, EReal.toReal_top]
      | coe r =>
          by_cases hrC : r ∈ C n
          · simp [S, hrC, EReal.toReal_coe]
          · simp [S, hrC, EReal.toReal_coe]
    have hS_closed : ∀ n, IsClosed (S n) := by
      intro n
      by_cases h0 : (0 : ℝ) ∈ C n
      · rw [hS_eq n, if_pos h0]
        exact (himg_closed n).union
          ((isClosed_singleton : IsClosed ({⊤} : Set EReal)).union (isClosed_singleton : IsClosed ({⊥} : Set EReal)))
      · rw [hS_eq n, if_neg h0]
        simpa using himg_closed n
    have hmeas : ∀ n, LebesgueMeasurable (f ⁻¹' (S n)) := fun n => h10 (S n) (hS_closed n)
    have hpre' : φ ⁻¹' K = ⋃ n : ℕ, f ⁻¹' (S n) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_iUnion]
      constructor
      · intro hxK
        simp [φ] at hxK
        obtain ⟨n, hn⟩ := exists_nat_gt |(f x).toReal|
        refine ⟨n, ?_⟩
        have hlb : -(n : ℝ) ≤ (f x).toReal := le_of_lt (abs_lt.mp hn).1
        have hub : (f x).toReal ≤ (n : ℝ) := le_of_lt (abs_lt.mp hn).2
        simp [S, C, hxK, hlb, hub]
      · rintro ⟨n, hxSn⟩
        have hxK : (f x).toReal ∈ K := by
          have hc := hxSn
          simp [S, C] at hc
          exact hc.1
        simpa [φ] using hxK
    rw [hpre']
    exact LebesgueMeasurable.countable_union hmeas
  · intro x hxlt
    have hx_ne_top : f x ≠ ⊤ := ne_of_lt hxlt
    have hx_ne_bot : f x ≠ ⊥ := ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (hf.1 x))
    simpa [φ] using (EReal.coe_toReal hx_ne_top hx_ne_bot)

/-- Remark 1.3.29 -/
theorem UnsignedMeasurable.approx_by_continuous_outside_small {d:ℕ} {f : EuclideanSpace' d → EReal}
  (hf: UnsignedMeasurable f) (hfin: AlmostAlways (fun x ↦ f x < ⊤))
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (g : EuclideanSpace' d → ℝ) (E: Set (EuclideanSpace' d)), Continuous (fun x : (Eᶜ : Set (EuclideanSpace' d)) => g x.val) ∧ LebesgueMeasurable E ∧
      Lebesgue_measure E ≤ ε ∧
      ∀ x ∉ E, g x = f x := by
  obtain ⟨φ, hφ_meas, hφ_eq⟩ := unsigned_measurable_to_real hf
  have hφ_cm : ComplexMeasurable (Real.complex_fun φ) := (RealMeasurable.iff).mp hφ_meas
  obtain ⟨g_c, E₁, hg_c_cont, hE₁_meas, hE₁_le, hg_c_eq⟩ :=
    ComplexMeasurable.approx_by_continuous_outside_small hφ_cm (ε / 2) (half_pos hε)
  let g : EuclideanSpace' d → ℝ := fun x => (g_c x).re
  let N : Set (EuclideanSpace' d) := {x | f x = ⊤}
  have hN_eq_ge : N = {x | f x ≥ ⊤} := by
    ext x
    simp [N]
    constructor
    · intro h; rw [h]
    · intro h; exact (le_antisymm h le_top).symm
  have hN_meas : LebesgueMeasurable N := by
    have h10 : ∀ K : Set EReal, IsClosed K → LebesgueMeasurable (f ⁻¹' K) :=
      (((UnsignedMeasurable.TFAE hf.1).out 10 0
        (a := ∀ K : Set EReal, IsClosed K → LebesgueMeasurable (f ⁻¹' K))
        (b := _root_.UnsignedMeasurable f)).mpr hf)
    have hN_eq' : N = f ⁻¹' ({⊤} : Set EReal) := by
      ext x
      simp [N]
    rw [hN_eq']
    exact h10 {⊤} (isClosed_singleton)
  have hN_null : Lebesgue_measure N = 0 := by
    have hfin' : IsNull {x | ¬ f x < ⊤} := by
      simpa [AlmostAlways] using hfin
    have hN_eq : N = {x | ¬ f x < ⊤} := by
      calc N = {x | f x ≥ ⊤} := hN_eq_ge
        _ = {x | ¬ f x < ⊤} := by ext x; simp [not_lt]
    rwa [hN_eq]
  let E : Set (EuclideanSpace' d) := E₁ ∪ N
  have hE_meas : LebesgueMeasurable E := hE₁_meas.union hN_meas
  have hE_le : Lebesgue_measure E ≤ ε := by
    calc
      Lebesgue_measure E = Lebesgue_measure (E₁ ∪ N) := by rfl
      _ ≤ Lebesgue_measure E₁ + Lebesgue_measure N := by
        let S : Fin 2 → Set (EuclideanSpace' d) := ![E₁, N]
        have h_union : ⋃ i : Fin 2, S i = E₁ ∪ N := by
          ext x
          simp [S]
        calc
          Lebesgue_measure (E₁ ∪ N) = Lebesgue_measure (⋃ i : Fin 2, S i) := by rw [h_union]
          _ ≤ ∑ i : Fin 2, Lebesgue_measure (S i) := Lebesgue_outer_measure.finite_union_le S
          _ = Lebesgue_measure E₁ + Lebesgue_measure N := by simp [S]
      _ ≤ (↑(ε / 2) : EReal) + (0 : EReal) := add_le_add hE₁_le (by simp [hN_null])
      _ = (↑(ε / 2) : EReal) := by simp
      _ ≤ (ε : EReal) := EReal.coe_le_coe (by linarith)
  have hg_cont : Continuous (fun x : (Eᶜ : Set (EuclideanSpace' d)) => g x.val) := by
    have hsub : Eᶜ ⊆ E₁ᶜ := by
      intro x hx
      exact fun h => hx (Or.inl h)
    have hcontOn : ContinuousOn (fun x : EuclideanSpace' d => g_c x) E₁ᶜ :=
      (continuousOn_iff_continuous_restrict (f := fun x => g_c x) (s := E₁ᶜ)).mpr hg_c_cont
    have hcontOn' : ContinuousOn (fun x : EuclideanSpace' d => g_c x) Eᶜ := hcontOn.mono hsub
    have hcontOn_g : ContinuousOn (fun x : EuclideanSpace' d => (g_c x).re) Eᶜ :=
      Continuous.comp_continuousOn Complex.continuous_re hcontOn'
    have hcont : Continuous (fun x : (Eᶜ : Set (EuclideanSpace' d)) => (g_c x.val).re) :=
      (continuousOn_iff_continuous_restrict (f := fun x => (g_c x).re) (s := Eᶜ)).mp hcontOn_g
    simpa [g] using hcont
  refine ⟨g, E, hg_cont, hE_meas, hE_le, ?_⟩
  intro x hx
  have hxE₁ : x ∉ E₁ := fun h => hx (Or.inl h)
  have hxN : x ∉ N := fun h => hx (Or.inr h)
  have hg_c_eq' : g_c x = Real.complex_fun φ x := hg_c_eq x hxE₁
  have hgre : (g_c x).re = φ x := by
    rw [hg_c_eq']
    simp [Real.complex_fun]
  have hf_lt : f x < ⊤ := by
    have hneq : f x ≠ ⊤ := by
      simpa [N] using hxN
    exact (lt_top_iff_ne_top).mpr hneq
  have hφ_eq' : (φ x : EReal) = f x := hφ_eq x hf_lt
  have hgx : (g x : EReal) = f x := by
    dsimp [g]
    rw [hgre]
    exact hφ_eq'
  exact hgx

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
