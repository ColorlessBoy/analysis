import Analysis.MeasureTheory.Section_1_3_3

open scoped Pointwise

open BoundedInterval

/-!
# Introduction to Measure Theory, Section 1.3.4: Absolute integrability

A companion to (the introduction to) Section 1.3.4 of the book "An introduction to Measure Theory".

-/

-- It is probably possible to unify the real and complex theory here using the `RCLike` class in Mathlib, but we will adopt the more pedestrian approach of duplicating definitions in the real and complex cases.

/-- Definition 1.3.17 -/

def UnsignedAbsolutelyIntegrable {d:ℕ} (f: EuclideanSpace' d → EReal) : Prop := UnsignedMeasurable f ∧ UnsignedLebesgueIntegral f < ⊤

def ComplexAbsolutelyIntegrable {d:ℕ} (f: EuclideanSpace' d → ℂ) : Prop := ComplexMeasurable f ∧ UnsignedLebesgueIntegral (EReal.abs_fun f) < ⊤

def RealAbsolutelyIntegrable {d:ℕ} (f: EuclideanSpace' d → ℝ) : Prop := RealMeasurable f ∧ UnsignedLebesgueIntegral (EReal.abs_fun f) < ⊤

lemma ComplexAbsolutelyIntegrable.abs {d:ℕ} (f: EuclideanSpace' d → ℂ) (hf: ComplexAbsolutelyIntegrable f) : UnsignedAbsolutelyIntegrable (EReal.abs_fun f) := by
  constructor
  · -- UnsignedMeasurable (EReal.abs_fun f)
    constructor
    · -- Unsigned: ∀ x, EReal.abs_fun f x ≥ 0
      intro x
      simp only [EReal.abs_fun]
      exact EReal.coe_nonneg.mpr (norm_nonneg _)
    · -- Exists approximating unsigned simple functions
      obtain ⟨g, hg_simple, hg_conv⟩ := hf.1
      use fun n => EReal.abs_fun (g n)
      constructor
      · intro n; exact (hg_simple n).abs
      · intro x
        simp only [EReal.abs_fun]
        exact (continuous_coe_real_ereal.comp continuous_norm).continuousAt.tendsto.comp (hg_conv x)
  · exact hf.2

lemma RealAbsolutelyIntegrable.abs {d:ℕ} (f: EuclideanSpace' d → ℝ) (hf: RealAbsolutelyIntegrable f) : UnsignedAbsolutelyIntegrable (EReal.abs_fun f) := by
  constructor
  · -- UnsignedMeasurable (EReal.abs_fun f)
    constructor
    · intro x
      simp only [EReal.abs_fun]
      exact EReal.coe_nonneg.mpr (norm_nonneg _)
    · obtain ⟨g, hg_simple, hg_conv⟩ := hf.1
      use fun n => EReal.abs_fun (g n)
      constructor
      · intro n; exact (hg_simple n).abs
      · intro x
        simp only [EReal.abs_fun]
        exact (continuous_coe_real_ereal.comp continuous_norm).continuousAt.tendsto.comp (hg_conv x)
  · exact hf.2



lemma RealAbsolutelyIntegrable.iff {d:ℕ} (f: EuclideanSpace' d → ℝ) : RealAbsolutelyIntegrable f ↔ ComplexAbsolutelyIntegrable (fun x ↦ (f x:ℂ)) := by
  constructor
  · intro ⟨hf_meas, hf_integ⟩
    constructor
    · exact RealMeasurable.iff.mp hf_meas
    · convert hf_integ using 2
      funext x
      simp only [EReal.abs_fun]
      congr 1
      rw [Complex.norm_real, Real.norm_eq_abs]
  · intro ⟨hf_meas, hf_integ⟩
    constructor
    · exact RealMeasurable.iff.mpr hf_meas
    · convert hf_integ using 2
      funext x
      simp only [EReal.abs_fun]
      congr 1
      rw [Complex.norm_real, Real.norm_eq_abs]

lemma ComplexAbsolutelyIntegrable.re {d:ℕ} (f: EuclideanSpace' d → ℂ) (hf: ComplexAbsolutelyIntegrable f) : RealAbsolutelyIntegrable (Complex.re_fun f) := by
  have h_re_meas : RealMeasurable (Complex.re_fun f) := ComplexMeasurable.iff.mp hf.1 |>.1
  constructor
  · exact h_re_meas
  · have h_le : ∀ x, EReal.abs_fun (Complex.re_fun f) x ≤ EReal.abs_fun f x := fun x => by
      simp only [EReal.abs_fun, Complex.re_fun]
      apply EReal.coe_le_coe_iff.mpr
      rw [Real.norm_eq_abs]
      exact Complex.abs_re_le_norm (f x)
    -- Build UnsignedMeasurable for |Re(f)| directly from RealMeasurable (re_fun f)
    have h_re_abs_meas : UnsignedMeasurable (EReal.abs_fun (Complex.re_fun f)) := by
      constructor
      · intro x; simp only [EReal.abs_fun]; exact EReal.coe_nonneg.mpr (norm_nonneg _)
      · obtain ⟨g, hg_simple, hg_conv⟩ := h_re_meas
        use fun n => EReal.abs_fun (g n)
        constructor
        · intro n; exact (hg_simple n).abs
        · intro x
          simp only [EReal.abs_fun, Complex.re_fun]
          exact (continuous_coe_real_ereal.comp continuous_norm).continuousAt.tendsto.comp (hg_conv x)
    have h_mono : UnsignedLebesgueIntegral (EReal.abs_fun (Complex.re_fun f)) ≤
                  UnsignedLebesgueIntegral (EReal.abs_fun f) := by
      apply LowerUnsignedLebesgueIntegral.mono
      · exact h_re_abs_meas
      · exact hf.abs.1
      · exact AlmostAlways.ofAlways h_le
    exact lt_of_le_of_lt h_mono hf.2

lemma ComplexAbsolutelyIntegrable.im {d:ℕ} (f: EuclideanSpace' d → ℂ) (hf: ComplexAbsolutelyIntegrable f) : RealAbsolutelyIntegrable (Complex.im_fun f) := by
  have h_im_meas : RealMeasurable (Complex.im_fun f) := ComplexMeasurable.iff.mp hf.1 |>.2
  constructor
  · exact h_im_meas
  · have h_le : ∀ x, EReal.abs_fun (Complex.im_fun f) x ≤ EReal.abs_fun f x := fun x => by
      simp only [EReal.abs_fun, Complex.im_fun]
      apply EReal.coe_le_coe_iff.mpr
      rw [Real.norm_eq_abs]
      exact Complex.abs_im_le_norm (f x)
    -- Build UnsignedMeasurable for |Im(f)| directly from RealMeasurable (im_fun f)
    have h_im_abs_meas : UnsignedMeasurable (EReal.abs_fun (Complex.im_fun f)) := by
      constructor
      · intro x; simp only [EReal.abs_fun]; exact EReal.coe_nonneg.mpr (norm_nonneg _)
      · obtain ⟨g, hg_simple, hg_conv⟩ := h_im_meas
        use fun n => EReal.abs_fun (g n)
        constructor
        · intro n; exact (hg_simple n).abs
        · intro x
          simp only [EReal.abs_fun, Complex.im_fun]
          exact (continuous_coe_real_ereal.comp continuous_norm).continuousAt.tendsto.comp (hg_conv x)
    have h_mono : UnsignedLebesgueIntegral (EReal.abs_fun (Complex.im_fun f)) ≤
                  UnsignedLebesgueIntegral (EReal.abs_fun f) := by
      apply LowerUnsignedLebesgueIntegral.mono
      · exact h_im_abs_meas
      · exact hf.abs.1
      · exact AlmostAlways.ofAlways h_le
    exact lt_of_le_of_lt h_mono hf.2

lemma ComplexAbsolutelyIntegrable.iff {d:ℕ} (f: EuclideanSpace' d → ℂ) : ComplexAbsolutelyIntegrable f ↔ RealAbsolutelyIntegrable (Complex.re_fun f) ∧ RealAbsolutelyIntegrable (Complex.im_fun f) := by
  constructor
  · intro hf
    exact ⟨ComplexAbsolutelyIntegrable.re f hf, ComplexAbsolutelyIntegrable.im f hf⟩
  · intro ⟨hre, him⟩
    constructor
    · exact ComplexMeasurable.iff.mpr ⟨hre.1, him.1⟩
    · -- Use |f| ≤ |Re(f)| + |Im(f)| to bound the integral
      have h_bound : ∀ x, EReal.abs_fun f x ≤
          (EReal.abs_fun (Complex.re_fun f) + EReal.abs_fun (Complex.im_fun f)) x := fun x => by
        simp only [EReal.abs_fun, Complex.re_fun, Complex.im_fun, Pi.add_apply]
        apply EReal.coe_le_coe_iff.mpr
        calc ‖f x‖ = Real.sqrt ((f x).re^2 + (f x).im^2) := Complex.norm_eq_sqrt_sq_add_sq (f x)
          _ ≤ |((f x).re)| + |(f x).im| := by
            have h1 : (f x).re^2 + (f x).im^2 ≤ (|(f x).re| + |(f x).im|)^2 := by
              have h_cross : 0 ≤ 2 * |(f x).re| * |(f x).im| := by positivity
              calc (f x).re^2 + (f x).im^2
                  ≤ (f x).re^2 + 2 * |(f x).re| * |(f x).im| + (f x).im^2 := by linarith
                _ = |(f x).re|^2 + 2 * |(f x).re| * |(f x).im| + |(f x).im|^2 := by rw [sq_abs, sq_abs]
                _ = (|(f x).re| + |(f x).im|)^2 := by ring
            have h2 : 0 ≤ |(f x).re| + |(f x).im| := by positivity
            calc Real.sqrt ((f x).re^2 + (f x).im^2)
                ≤ Real.sqrt ((|(f x).re| + |(f x).im|)^2) := Real.sqrt_le_sqrt h1
              _ = |(f x).re| + |(f x).im| := Real.sqrt_sq h2
          _ = ‖(f x).re‖ + ‖(f x).im‖ := by rw [Real.norm_eq_abs, Real.norm_eq_abs]
      -- Apply monotonicity and additivity of integral
      have h_mono : UnsignedLebesgueIntegral (EReal.abs_fun f) ≤
                    UnsignedLebesgueIntegral (EReal.abs_fun (Complex.re_fun f) +
                                              EReal.abs_fun (Complex.im_fun f)) := by
        apply LowerUnsignedLebesgueIntegral.mono
        · constructor
          · intro x; simp only [EReal.abs_fun]; exact EReal.coe_nonneg.mpr (norm_nonneg _)
          · obtain ⟨g, hg_simple, hg_conv⟩ := ComplexMeasurable.iff.mpr ⟨hre.1, him.1⟩
            use fun n => EReal.abs_fun (g n)
            constructor
            · intro n; exact (hg_simple n).abs
            · intro x
              simp only [EReal.abs_fun]
              exact (continuous_coe_real_ereal.comp continuous_norm).continuousAt.tendsto.comp (hg_conv x)
        · exact hre.abs.1.add him.abs.1
        · exact AlmostAlways.ofAlways h_bound
      -- UnsignedLebesgueIntegral is defined as LowerUnsignedLebesgueIntegral
      have h_add : UnsignedLebesgueIntegral (EReal.abs_fun (Complex.re_fun f) +
                                             EReal.abs_fun (Complex.im_fun f)) =
                   UnsignedLebesgueIntegral (EReal.abs_fun (Complex.re_fun f)) +
                   UnsignedLebesgueIntegral (EReal.abs_fun (Complex.im_fun f)) := by
        exact LowerUnsignedLebesgueIntegral.add hre.abs.1 him.abs.1
          (UnsignedMeasurable.add hre.abs.1 him.abs.1)
      rw [h_add] at h_mono
      calc UnsignedLebesgueIntegral (EReal.abs_fun f)
          ≤ UnsignedLebesgueIntegral (EReal.abs_fun (Complex.re_fun f)) +
            UnsignedLebesgueIntegral (EReal.abs_fun (Complex.im_fun f)) := h_mono
        _ < ⊤ := EReal.add_lt_top (lt_top_iff_ne_top.mp hre.2) (lt_top_iff_ne_top.mp him.2)

noncomputable def UnsignedAbsolutelyIntegrable.integ {d:ℕ} (f: EuclideanSpace' d → EReal) (_: UnsignedAbsolutelyIntegrable f) : ℝ := (UnsignedLebesgueIntegral f).toReal

noncomputable def ComplexAbsolutelyIntegrable.norm {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexAbsolutelyIntegrable f) : ℝ := hf.abs.integ

noncomputable def RealAbsolutelyIntegrable.norm {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealAbsolutelyIntegrable f) : ℝ := hf.abs.integ


def RealMeasurable.measurable_pos {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealMeasurable f) : UnsignedMeasurable (EReal.pos_fun f) := by
  constructor
  · -- Unsigned: ∀ x, EReal.pos_fun f x ≥ 0
    intro x
    simp only [EReal.pos_fun]
    exact EReal.coe_nonneg.mpr (le_max_right _ _)
  · -- Exists approximating unsigned simple functions
    obtain ⟨g, hg_simple, hg_conv⟩ := hf
    use fun n => EReal.pos_fun (g n)
    constructor
    · intro n; exact (hg_simple n).pos
    · intro x
      simp only [EReal.pos_fun]
      have hcont : Continuous (fun y : ℝ => (max y 0).toEReal) :=
        continuous_coe_real_ereal.comp (continuous_max.comp (continuous_id.prodMk continuous_const))
      exact hcont.continuousAt.tendsto.comp (hg_conv x)

def RealMeasurable.measurable_neg {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealMeasurable f) : UnsignedMeasurable (EReal.neg_fun f) := by
  constructor
  · -- Unsigned: ∀ x, EReal.neg_fun f x ≥ 0
    intro x
    simp only [EReal.neg_fun]
    exact EReal.coe_nonneg.mpr (le_max_right _ _)
  · -- Exists approximating unsigned simple functions
    obtain ⟨g, hg_simple, hg_conv⟩ := hf
    use fun n => EReal.neg_fun (g n)
    constructor
    · intro n; exact (hg_simple n).neg
    · intro x
      simp only [EReal.neg_fun]
      have hcont : Continuous (fun y : ℝ => (max (-y) 0).toEReal) :=
        continuous_coe_real_ereal.comp (continuous_max.comp (continuous_neg.prodMk continuous_const))
      exact hcont.continuousAt.tendsto.comp (hg_conv x)

def RealAbsolutelyIntegrable.pos {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealAbsolutelyIntegrable f) : UnsignedAbsolutelyIntegrable (EReal.pos_fun f) := by
  constructor
  · exact hf.1.measurable_pos
  · -- UnsignedLebesgueIntegral (pos_fun f) ≤ UnsignedLebesgueIntegral (abs_fun f) < ⊤
    have h_le : ∀ x, EReal.pos_fun f x ≤ EReal.abs_fun f x := fun x => by
      simp only [EReal.pos_fun, EReal.abs_fun]
      apply EReal.coe_le_coe_iff.mpr
      rw [Real.norm_eq_abs, max_le_iff]
      exact ⟨le_abs_self _, abs_nonneg _⟩
    have h_mono : UnsignedLebesgueIntegral (EReal.pos_fun f) ≤ UnsignedLebesgueIntegral (EReal.abs_fun f) := by
      apply LowerUnsignedLebesgueIntegral.mono
      · exact hf.1.measurable_pos
      · exact hf.abs.1
      · exact AlmostAlways.ofAlways h_le
    exact lt_of_le_of_lt h_mono hf.2

def RealAbsolutelyIntegrable.neg {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealAbsolutelyIntegrable f) : UnsignedAbsolutelyIntegrable (EReal.neg_fun f) := by
  constructor
  · exact hf.1.measurable_neg
  · -- UnsignedLebesgueIntegral (neg_fun f) ≤ UnsignedLebesgueIntegral (abs_fun f) < ⊤
    have h_le : ∀ x, EReal.neg_fun f x ≤ EReal.abs_fun f x := fun x => by
      simp only [EReal.neg_fun, EReal.abs_fun]
      apply EReal.coe_le_coe_iff.mpr
      rw [Real.norm_eq_abs, max_le_iff]
      exact ⟨neg_le_abs _, abs_nonneg _⟩
    have h_mono : UnsignedLebesgueIntegral (EReal.neg_fun f) ≤ UnsignedLebesgueIntegral (EReal.abs_fun f) := by
      apply LowerUnsignedLebesgueIntegral.mono
      · exact hf.1.measurable_neg
      · exact hf.abs.1
      · exact AlmostAlways.ofAlways h_le
    exact lt_of_le_of_lt h_mono hf.2

noncomputable def RealAbsolutelyIntegrable.integ {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealAbsolutelyIntegrable f) : ℝ := hf.pos.integ - hf.neg.integ

noncomputable def ComplexAbsolutelyIntegrable.integ {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexAbsolutelyIntegrable f) : ℂ := hf.re.integ + Complex.I * hf.im.integ

open Classical in
noncomputable def RealLebesgueIntegral {d:ℕ} (f: EuclideanSpace' d → ℝ) : ℝ  := if hf: RealAbsolutelyIntegrable f then hf.integ else 0

open Classical in
noncomputable def ComplexLebesgueIntegral {d:ℕ} (f: EuclideanSpace' d → ℂ) : ℂ  := if hf: ComplexAbsolutelyIntegrable f then hf.integ else 0

def RealSimpleFunction.absolutelyIntegrable_iff' {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealSimpleFunction f) : hf.AbsolutelyIntegrable ↔ RealAbsolutelyIntegrable f := by
  constructor
  · -- Forward: hf.AbsolutelyIntegrable → RealAbsolutelyIntegrable f
    intro hfi
    constructor
    · -- RealMeasurable f: use constant sequence
      exact ⟨fun _ => f, fun _ => hf, fun _ => tendsto_const_nhds⟩
    · -- UnsignedLebesgueIntegral (EReal.abs_fun f) < ⊤
      rw [UnsignedLebesgueIntegral, LowerUnsignedLebesgueIntegral.eq_simpleIntegral hf.abs]
      exact hfi
  · -- Backward: RealAbsolutelyIntegrable f → hf.AbsolutelyIntegrable
    intro ⟨_, hf_integ⟩
    rw [RealSimpleFunction.AbsolutelyIntegrable, ← LowerUnsignedLebesgueIntegral.eq_simpleIntegral hf.abs]
    exact hf_integ

def ComplexSimpleFunction.absolutelyIntegrable_iff' {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexSimpleFunction f) : hf.AbsolutelyIntegrable ↔ ComplexAbsolutelyIntegrable f := by
  constructor
  · -- Forward: hf.AbsolutelyIntegrable → ComplexAbsolutelyIntegrable f
    intro hfi
    constructor
    · -- ComplexMeasurable f: use constant sequence
      exact ⟨fun _ => f, fun _ => hf, fun _ => tendsto_const_nhds⟩
    · -- UnsignedLebesgueIntegral (EReal.abs_fun f) < ⊤
      rw [UnsignedLebesgueIntegral, LowerUnsignedLebesgueIntegral.eq_simpleIntegral hf.abs]
      exact hfi
  · -- Backward: ComplexAbsolutelyIntegrable f → hf.AbsolutelyIntegrable
    intro ⟨_, hf_integ⟩
    rw [ComplexSimpleFunction.AbsolutelyIntegrable, ← LowerUnsignedLebesgueIntegral.eq_simpleIntegral hf.abs]
    exact hf_integ

def RealSimpleFunction.AbsolutelyIntegrable.integ_eq {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealSimpleFunction f) (hfi: hf.AbsolutelyIntegrable) : hf.integ = (hf.absolutelyIntegrable_iff'.mp hfi).integ := by
  -- hf.integ = (hf.pos).integ.toReal - (hf.neg).integ.toReal
  -- (hf.absolutelyIntegrable_iff'.mp hfi).integ = (UnsignedLebesgueIntegral (pos_fun f)).toReal - (UnsignedLebesgueIntegral (neg_fun f)).toReal
  simp only [RealSimpleFunction.integ, RealAbsolutelyIntegrable.integ, UnsignedAbsolutelyIntegrable.integ]
  congr 1
  · -- (hf.pos).integ.toReal = (UnsignedLebesgueIntegral (pos_fun f)).toReal
    rw [UnsignedLebesgueIntegral, LowerUnsignedLebesgueIntegral.eq_simpleIntegral hf.pos]
  · -- (hf.neg).integ.toReal = (UnsignedLebesgueIntegral (neg_fun f)).toReal
    rw [UnsignedLebesgueIntegral, LowerUnsignedLebesgueIntegral.eq_simpleIntegral hf.neg]

def ComplexSimpleFunction.AbsolutelyIntegrable.integ_eq {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexSimpleFunction f) (hfi: hf.AbsolutelyIntegrable) : hf.integ = (hf.absolutelyIntegrable_iff'.mp hfi).integ := by
  -- Both sides are defined as re.integ + I * im.integ
  simp only [ComplexSimpleFunction.integ, ComplexAbsolutelyIntegrable.integ]
  -- The key is that the re and im of the complex absolutely integrable give the same integral as the real simple function integrals
  have hf_re : RealSimpleFunction (Complex.re_fun f) := ComplexSimpleFunction.re hf
  have hf_im : RealSimpleFunction (Complex.im_fun f) := ComplexSimpleFunction.im hf
  congr 1
  · -- hf.re.integ = (hf.absolutelyIntegrable_iff'.mp hfi).re.integ
    have hre_fi : hf_re.AbsolutelyIntegrable := by
      rw [RealSimpleFunction.AbsolutelyIntegrable]
      have h := ComplexAbsolutelyIntegrable.re f (hf.absolutelyIntegrable_iff'.mp hfi)
      rw [RealAbsolutelyIntegrable, UnsignedLebesgueIntegral, LowerUnsignedLebesgueIntegral.eq_simpleIntegral hf_re.abs] at h
      exact h.2
    have heq := RealSimpleFunction.AbsolutelyIntegrable.integ_eq hf_re hre_fi
    simp only [heq]
  · -- hf.im.integ = (hf.absolutelyIntegrable_iff'.mp hfi).im.integ
    have him_fi : hf_im.AbsolutelyIntegrable := by
      rw [RealSimpleFunction.AbsolutelyIntegrable]
      have h := ComplexAbsolutelyIntegrable.im f (hf.absolutelyIntegrable_iff'.mp hfi)
      rw [RealAbsolutelyIntegrable, UnsignedLebesgueIntegral, LowerUnsignedLebesgueIntegral.eq_simpleIntegral hf_im.abs] at h
      exact h.2
    have heq := RealSimpleFunction.AbsolutelyIntegrable.integ_eq hf_im him_fi
    simp only [heq]

theorem RealAbsolutelyIntegrable.add {d:ℕ} {f g: EuclideanSpace' d → ℝ} (hf: RealAbsolutelyIntegrable f) (hg: RealAbsolutelyIntegrable g) : RealAbsolutelyIntegrable (f + g) := by
  constructor
  · exact RealMeasurable.add hf.1 hg.1
  · -- Show ∫ |f + g| ≤ ∫ |f| + ∫ |g| < ∞
    have h_le : ∀ x, EReal.abs_fun (f + g) x ≤ (EReal.abs_fun f + EReal.abs_fun g) x := fun x => by
      simp only [EReal.abs_fun, Pi.add_apply]
      rw [← EReal.coe_add]
      exact EReal.coe_le_coe_iff.mpr (norm_add_le (f x) (g x))
    have hf_abs := RealAbsolutelyIntegrable.abs f hf
    have hg_abs := RealAbsolutelyIntegrable.abs g hg
    have hfg_abs_meas : UnsignedMeasurable (EReal.abs_fun (f + g)) := by
      constructor
      · intro x; simp only [EReal.abs_fun]; exact EReal.coe_nonneg.mpr (norm_nonneg _)
      · obtain ⟨gf, hgf_simple, hgf_conv⟩ := hf.1
        obtain ⟨gg, hgg_simple, hgg_conv⟩ := hg.1
        use fun n => EReal.abs_fun (gf n + gg n)
        constructor
        · intro n; exact (RealSimpleFunction.add (hgf_simple n) (hgg_simple n)).abs
        · intro x
          simp only [EReal.abs_fun]
          have hcont : Continuous (fun y : ℝ => ‖y‖.toEReal) :=
            continuous_coe_real_ereal.comp continuous_norm
          have hconv : Filter.Tendsto (fun n => gf n x + gg n x) Filter.atTop (nhds (f x + g x)) :=
            Filter.Tendsto.add (hgf_conv x) (hgg_conv x)
          exact hcont.continuousAt.tendsto.comp hconv
    have h_mono : UnsignedLebesgueIntegral (EReal.abs_fun (f + g)) ≤
                  UnsignedLebesgueIntegral (EReal.abs_fun f + EReal.abs_fun g) := by
      apply LowerUnsignedLebesgueIntegral.mono hfg_abs_meas (UnsignedMeasurable.add hf_abs.1 hg_abs.1)
      exact AlmostAlways.ofAlways h_le
    have h_add : UnsignedLebesgueIntegral (EReal.abs_fun f + EReal.abs_fun g) =
                 UnsignedLebesgueIntegral (EReal.abs_fun f) + UnsignedLebesgueIntegral (EReal.abs_fun g) := by
      apply LowerUnsignedLebesgueIntegral.add hf_abs.1 hg_abs.1 (UnsignedMeasurable.add hf_abs.1 hg_abs.1)
    calc UnsignedLebesgueIntegral (EReal.abs_fun (f + g))
        ≤ UnsignedLebesgueIntegral (EReal.abs_fun f) + UnsignedLebesgueIntegral (EReal.abs_fun g) := by
          rw [← h_add]; exact h_mono
      _ < ⊤ := EReal.add_lt_top hf.2.ne_top hg.2.ne_top

theorem ComplexAbsolutelyIntegrable.add {d:ℕ} {f g: EuclideanSpace' d → ℂ} (hf: ComplexAbsolutelyIntegrable f) (hg: ComplexAbsolutelyIntegrable g) : ComplexAbsolutelyIntegrable (f + g) := by
  constructor
  · exact ComplexMeasurable.add hf.1 hg.1
  · have h_le : ∀ x, EReal.abs_fun (f + g) x ≤ (EReal.abs_fun f + EReal.abs_fun g) x := fun x => by
      simp only [EReal.abs_fun, Pi.add_apply]
      rw [← EReal.coe_add]
      exact EReal.coe_le_coe_iff.mpr (norm_add_le (f x) (g x))
    have hf_abs := ComplexAbsolutelyIntegrable.abs f hf
    have hg_abs := ComplexAbsolutelyIntegrable.abs g hg
    have hfg_abs_meas : UnsignedMeasurable (EReal.abs_fun (f + g)) := by
      constructor
      · intro x; simp only [EReal.abs_fun]; exact EReal.coe_nonneg.mpr (norm_nonneg _)
      · obtain ⟨gf, hgf_simple, hgf_conv⟩ := hf.1
        obtain ⟨gg, hgg_simple, hgg_conv⟩ := hg.1
        use fun n => EReal.abs_fun (gf n + gg n)
        constructor
        · intro n; exact (ComplexSimpleFunction.add (hgf_simple n) (hgg_simple n)).abs
        · intro x
          simp only [EReal.abs_fun]
          have hcont : Continuous (fun y : ℂ => ‖y‖.toEReal) :=
            continuous_coe_real_ereal.comp continuous_norm
          have hconv : Filter.Tendsto (fun n => gf n x + gg n x) Filter.atTop (nhds (f x + g x)) :=
            Filter.Tendsto.add (hgf_conv x) (hgg_conv x)
          exact hcont.continuousAt.tendsto.comp hconv
    have h_mono : UnsignedLebesgueIntegral (EReal.abs_fun (f + g)) ≤
                  UnsignedLebesgueIntegral (EReal.abs_fun f + EReal.abs_fun g) := by
      apply LowerUnsignedLebesgueIntegral.mono hfg_abs_meas (UnsignedMeasurable.add hf_abs.1 hg_abs.1)
      exact AlmostAlways.ofAlways h_le
    have h_add : UnsignedLebesgueIntegral (EReal.abs_fun f + EReal.abs_fun g) =
                 UnsignedLebesgueIntegral (EReal.abs_fun f) + UnsignedLebesgueIntegral (EReal.abs_fun g) := by
      apply LowerUnsignedLebesgueIntegral.add hf_abs.1 hg_abs.1 (UnsignedMeasurable.add hf_abs.1 hg_abs.1)
    calc UnsignedLebesgueIntegral (EReal.abs_fun (f + g))
        ≤ UnsignedLebesgueIntegral (EReal.abs_fun f) + UnsignedLebesgueIntegral (EReal.abs_fun g) := by
          rw [← h_add]; exact h_mono
      _ < ⊤ := EReal.add_lt_top hf.2.ne_top hg.2.ne_top

theorem RealAbsolutelyIntegrable.sub {d:ℕ} {f g: EuclideanSpace' d → ℝ} (hf: RealAbsolutelyIntegrable f) (hg: RealAbsolutelyIntegrable g) : RealAbsolutelyIntegrable (f - g) := by
  constructor
  · exact RealMeasurable.sub hf.1 hg.1
  · have h_le : ∀ x, EReal.abs_fun (f - g) x ≤ (EReal.abs_fun f + EReal.abs_fun g) x := fun x => by
      simp only [EReal.abs_fun, Pi.sub_apply, Pi.add_apply]
      rw [← EReal.coe_add]
      exact EReal.coe_le_coe_iff.mpr (norm_sub_le (f x) (g x))
    have hf_abs := RealAbsolutelyIntegrable.abs f hf
    have hg_abs := RealAbsolutelyIntegrable.abs g hg
    have hfg_abs_meas : UnsignedMeasurable (EReal.abs_fun (f - g)) := by
      constructor
      · intro x; simp only [EReal.abs_fun]; exact EReal.coe_nonneg.mpr (norm_nonneg _)
      · obtain ⟨gf, hgf_simple, hgf_conv⟩ := hf.1
        obtain ⟨gg, hgg_simple, hgg_conv⟩ := hg.1
        use fun n => EReal.abs_fun (gf n - gg n)
        constructor
        · intro n
          have hsub : RealSimpleFunction (gf n - gg n) := by
            have heq : gf n - gg n = gf n + (-1 : ℝ) • gg n := by
              funext x; simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
            rw [heq]
            exact RealSimpleFunction.add (hgf_simple n) ((hgg_simple n).smul (-1))
          exact hsub.abs
        · intro x
          simp only [EReal.abs_fun]
          have hcont : Continuous (fun y : ℝ => ‖y‖.toEReal) :=
            continuous_coe_real_ereal.comp continuous_norm
          have hconv : Filter.Tendsto (fun n => gf n x - gg n x) Filter.atTop (nhds (f x - g x)) :=
            Filter.Tendsto.sub (hgf_conv x) (hgg_conv x)
          exact hcont.continuousAt.tendsto.comp hconv
    have h_mono : UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) ≤
                  UnsignedLebesgueIntegral (EReal.abs_fun f + EReal.abs_fun g) := by
      apply LowerUnsignedLebesgueIntegral.mono hfg_abs_meas (UnsignedMeasurable.add hf_abs.1 hg_abs.1)
      exact AlmostAlways.ofAlways h_le
    have h_add : UnsignedLebesgueIntegral (EReal.abs_fun f + EReal.abs_fun g) =
                 UnsignedLebesgueIntegral (EReal.abs_fun f) + UnsignedLebesgueIntegral (EReal.abs_fun g) := by
      apply LowerUnsignedLebesgueIntegral.add hf_abs.1 hg_abs.1 (UnsignedMeasurable.add hf_abs.1 hg_abs.1)
    calc UnsignedLebesgueIntegral (EReal.abs_fun (f - g))
        ≤ UnsignedLebesgueIntegral (EReal.abs_fun f) + UnsignedLebesgueIntegral (EReal.abs_fun g) := by
          rw [← h_add]; exact h_mono
      _ < ⊤ := EReal.add_lt_top hf.2.ne_top hg.2.ne_top

theorem ComplexAbsolutelyIntegrable.sub {d:ℕ} {f g: EuclideanSpace' d → ℂ} (hf: ComplexAbsolutelyIntegrable f) (hg: ComplexAbsolutelyIntegrable g) : ComplexAbsolutelyIntegrable (f - g) := by
  constructor
  · exact ComplexMeasurable.sub hf.1 hg.1
  · have h_le : ∀ x, EReal.abs_fun (f - g) x ≤ (EReal.abs_fun f + EReal.abs_fun g) x := fun x => by
      simp only [EReal.abs_fun, Pi.sub_apply, Pi.add_apply]
      rw [← EReal.coe_add]
      exact EReal.coe_le_coe_iff.mpr (norm_sub_le (f x) (g x))
    have hf_abs := ComplexAbsolutelyIntegrable.abs f hf
    have hg_abs := ComplexAbsolutelyIntegrable.abs g hg
    have hfg_abs_meas : UnsignedMeasurable (EReal.abs_fun (f - g)) := by
      constructor
      · intro x; simp only [EReal.abs_fun]; exact EReal.coe_nonneg.mpr (norm_nonneg _)
      · obtain ⟨gf, hgf_simple, hgf_conv⟩ := hf.1
        obtain ⟨gg, hgg_simple, hgg_conv⟩ := hg.1
        use fun n => EReal.abs_fun (gf n - gg n)
        constructor
        · intro n
          have hsub : ComplexSimpleFunction (gf n - gg n) := by
            have heq : gf n - gg n = gf n + (-1 : ℂ) • gg n := by
              funext x; simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
            rw [heq]
            exact ComplexSimpleFunction.add (hgf_simple n) ((hgg_simple n).smul (-1))
          exact hsub.abs
        · intro x
          simp only [EReal.abs_fun]
          have hcont : Continuous (fun y : ℂ => ‖y‖.toEReal) :=
            continuous_coe_real_ereal.comp continuous_norm
          have hconv : Filter.Tendsto (fun n => gf n x - gg n x) Filter.atTop (nhds (f x - g x)) :=
            Filter.Tendsto.sub (hgf_conv x) (hgg_conv x)
          exact hcont.continuousAt.tendsto.comp hconv
    have h_mono : UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) ≤
                  UnsignedLebesgueIntegral (EReal.abs_fun f + EReal.abs_fun g) := by
      apply LowerUnsignedLebesgueIntegral.mono hfg_abs_meas (UnsignedMeasurable.add hf_abs.1 hg_abs.1)
      exact AlmostAlways.ofAlways h_le
    have h_add : UnsignedLebesgueIntegral (EReal.abs_fun f + EReal.abs_fun g) =
                 UnsignedLebesgueIntegral (EReal.abs_fun f) + UnsignedLebesgueIntegral (EReal.abs_fun g) := by
      apply LowerUnsignedLebesgueIntegral.add hf_abs.1 hg_abs.1 (UnsignedMeasurable.add hf_abs.1 hg_abs.1)
    calc UnsignedLebesgueIntegral (EReal.abs_fun (f - g))
        ≤ UnsignedLebesgueIntegral (EReal.abs_fun f) + UnsignedLebesgueIntegral (EReal.abs_fun g) := by
          rw [← h_add]; exact h_mono
      _ < ⊤ := EReal.add_lt_top hf.2.ne_top hg.2.ne_top

theorem RealAbsolutelyIntegrable.smul {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealAbsolutelyIntegrable f) (c:ℝ) : RealAbsolutelyIntegrable (c • f) := by
  constructor
  · -- RealMeasurable (c • f)
    obtain ⟨g, hg_simple, hg_conv⟩ := hf.1
    use fun n => c • g n
    constructor
    · intro n; exact (hg_simple n).smul c
    · intro x
      have hconv : Filter.Tendsto (fun n => g n x) Filter.atTop (nhds (f x)) := hg_conv x
      have hsmul_conv : Filter.Tendsto (fun n => c • g n x) Filter.atTop (nhds (c • f x)) := by
        simp only [smul_eq_mul]
        exact hconv.const_mul c
      simp only [Pi.smul_apply]
      exact hsmul_conv
  · -- UnsignedLebesgueIntegral (EReal.abs_fun (c • f)) < ⊤
    have h_eq : ∀ x, EReal.abs_fun (c • f) x = ‖c‖.toEReal * EReal.abs_fun f x := fun x => by
      simp only [EReal.abs_fun, Pi.smul_apply, smul_eq_mul, norm_mul, Real.norm_eq_abs]
      rw [EReal.coe_mul]
    have hf_abs := RealAbsolutelyIntegrable.abs f hf
    have h_smul_eq : EReal.abs_fun (c • f) = (fun x => ‖c‖.toEReal * EReal.abs_fun f x) := by
      funext x; exact h_eq x
    rw [h_smul_eq]
    have h_scale : UnsignedLebesgueIntegral (fun x => ‖c‖.toEReal * EReal.abs_fun f x) =
                   ‖c‖.toEReal * UnsignedLebesgueIntegral (EReal.abs_fun f) := by
      have h_eq' : (fun x => ‖c‖.toEReal * EReal.abs_fun f x) = (‖c‖.toEReal : EReal) • EReal.abs_fun f := by
        funext x; simp only [Pi.smul_apply, smul_eq_mul]
      rw [h_eq', UnsignedLebesgueIntegral]
      have h_hom := LowerUnsignedLebesgueIntegral.hom hf_abs.1 (norm_nonneg c)
      exact h_hom
    rw [h_scale]
    by_cases hc : c = 0
    · simp only [hc, norm_zero]
      rw [show (0 : ℝ).toEReal = 0 by rfl, zero_mul]
      exact EReal.coe_lt_top 0
    · have hc_pos : ‖c‖ > 0 := norm_pos_iff.mpr hc
      have h_ne_top : ‖c‖.toEReal * UnsignedLebesgueIntegral (EReal.abs_fun f) ≠ ⊤ := by
        rw [EReal.mul_ne_top]
        refine ⟨?_, ?_, ?_, ?_⟩
        · left; exact EReal.coe_ne_bot ‖c‖
        · left; exact le_of_lt (EReal.coe_pos.mpr hc_pos)
        · left; exact EReal.coe_ne_top ‖c‖
        · right; exact hf.2.ne_top
      exact Ne.lt_top h_ne_top

theorem ComplexAbsolutelyIntegrable.smul {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexAbsolutelyIntegrable f) (c:ℂ) : ComplexAbsolutelyIntegrable (c • f) := by
  constructor
  · -- ComplexMeasurable (c • f)
    obtain ⟨g, hg_simple, hg_conv⟩ := hf.1
    use fun n => c • g n
    constructor
    · intro n; exact (hg_simple n).smul c
    · intro x
      have hconv : Filter.Tendsto (fun n => g n x) Filter.atTop (nhds (f x)) := hg_conv x
      have hsmul_conv : Filter.Tendsto (fun n => c • g n x) Filter.atTop (nhds (c • f x)) := by
        simp only [smul_eq_mul]
        exact hconv.const_mul c
      simp only [Pi.smul_apply]
      exact hsmul_conv
  · -- UnsignedLebesgueIntegral (EReal.abs_fun (c • f)) < ⊤
    have h_eq : ∀ x, EReal.abs_fun (c • f) x = ‖c‖.toEReal * EReal.abs_fun f x := fun x => by
      simp only [EReal.abs_fun, Pi.smul_apply, smul_eq_mul, norm_mul]
      rw [EReal.coe_mul]
    have hf_abs := ComplexAbsolutelyIntegrable.abs f hf
    have h_smul_eq : EReal.abs_fun (c • f) = (fun x => ‖c‖.toEReal * EReal.abs_fun f x) := by
      funext x; exact h_eq x
    rw [h_smul_eq]
    have h_scale : UnsignedLebesgueIntegral (fun x => ‖c‖.toEReal * EReal.abs_fun f x) =
                   ‖c‖.toEReal * UnsignedLebesgueIntegral (EReal.abs_fun f) := by
      have h_eq' : (fun x => ‖c‖.toEReal * EReal.abs_fun f x) = (‖c‖.toEReal : EReal) • EReal.abs_fun f := by
        funext x; simp only [Pi.smul_apply, smul_eq_mul]
      rw [h_eq', UnsignedLebesgueIntegral]
      have h_hom := LowerUnsignedLebesgueIntegral.hom hf_abs.1 (norm_nonneg c)
      exact h_hom
    rw [h_scale]
    by_cases hc : c = 0
    · simp only [hc, norm_zero]
      rw [show (0 : ℝ).toEReal = 0 by rfl, zero_mul]
      exact EReal.coe_lt_top 0
    · have hc_pos : ‖c‖ > 0 := norm_pos_iff.mpr hc
      have h_ne_top : ‖c‖.toEReal * UnsignedLebesgueIntegral (EReal.abs_fun f) ≠ ⊤ := by
        rw [EReal.mul_ne_top]
        refine ⟨?_, ?_, ?_, ?_⟩
        · left; exact EReal.coe_ne_bot ‖c‖
        · left; exact le_of_lt (EReal.coe_pos.mpr hc_pos)
        · left; exact EReal.coe_ne_top ‖c‖
        · right; exact hf.2.ne_top
      exact Ne.lt_top h_ne_top

theorem RealAbsolutelyIntegrable.of_neg {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealAbsolutelyIntegrable f) : RealAbsolutelyIntegrable (-f) := by
  have h : -f = (-1 : ℝ) • f := by funext x; simp [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  rw [h]
  exact hf.smul (-1)

theorem ComplexAbsolutelyIntegrable.of_neg {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexAbsolutelyIntegrable f) : ComplexAbsolutelyIntegrable (-f) := by
  have h : -f = (-1 : ℂ) • f := by funext x; simp [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  rw [h]
  exact hf.smul (-1)

theorem ComplexAbsolutelyIntegrable.conj {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexAbsolutelyIntegrable f) : ComplexAbsolutelyIntegrable (Complex.conj_fun f) := by
  constructor
  · -- ComplexMeasurable (Complex.conj_fun f)
    obtain ⟨g, hg_simple, hg_conv⟩ := hf.1
    use fun n => Complex.conj_fun (g n)
    constructor
    · intro n; exact (hg_simple n).conj
    · intro x
      simp only [Complex.conj_fun]
      have hconv : Filter.Tendsto (fun n => g n x) Filter.atTop (nhds (f x)) := hg_conv x
      exact (RCLike.continuous_conj.tendsto (f x)).comp hconv
  · -- UnsignedLebesgueIntegral (EReal.abs_fun (Complex.conj_fun f)) < ⊤
    have h_eq : EReal.abs_fun (Complex.conj_fun f) = EReal.abs_fun f := by
      funext x
      simp only [EReal.abs_fun, Complex.conj_fun, RCLike.norm_conj]
    rw [h_eq]
    exact hf.2

@[ext]
structure PreL1 (d:ℕ) where
  f : EuclideanSpace' d → ℂ
  integrable : ComplexAbsolutelyIntegrable f

noncomputable def PreL1.norm {d:ℕ} {X:Type*} [RCLike X] (f: EuclideanSpace' d → X) := UnsignedLebesgueIntegral (EReal.abs_fun f)

def ComplexAbsolutelyIntegrable.to_PreL1 {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexAbsolutelyIntegrable f) : PreL1 d := ⟨ f, hf ⟩

def PreL1.conj {d:ℕ} (F: PreL1 d) : PreL1 d := ⟨ Complex.conj_fun F.f, F.integrable.conj ⟩

lemma ComplexAbsolutelyIntegrable.zero {d:ℕ} : ComplexAbsolutelyIntegrable (0 : EuclideanSpace' d → ℂ) := by
  constructor
  · -- ComplexMeasurable 0
    use fun _ => 0
    constructor
    · intro n
      use 0, fun _ => 0, fun _ => ∅
      constructor
      · intro i; exact Fin.elim0 i
      · funext x; simp only [Pi.zero_apply, Finset.univ_eq_empty, Finset.sum_empty]
    · intro x; exact tendsto_const_nhds
  · -- UnsignedLebesgueIntegral (EReal.abs_fun 0) < ⊤
    have h_zero : EReal.abs_fun (0 : EuclideanSpace' d → ℂ) = 0 := by
      funext x; simp only [EReal.abs_fun, Pi.zero_apply, norm_zero]; rfl
    rw [h_zero, UnsignedLebesgueIntegral]
    -- Show that 0 is an unsigned simple function
    have h_simple : UnsignedSimpleFunction (0 : EuclideanSpace' d → EReal) := by
      use 0, fun i => Fin.elim0 i, fun i => Fin.elim0 i
      constructor
      · intro i; exact Fin.elim0 i
      · funext x; simp only [Pi.zero_apply, Finset.univ_eq_empty, Finset.sum_empty]
    rw [LowerUnsignedLebesgueIntegral.eq_simpleIntegral h_simple]
    -- The integral of the zero simple function is < ⊤
    -- Key: h_simple.integ ≤ ∑ i, c_i * measure(E_i) where c_i are bounded
    -- For the zero function, each term in any representation contributes 0
    simp only [UnsignedSimpleFunction.integ]
    -- The sum is over Fin (choose ...) which is some natural number
    -- Show it's < ⊤ by showing sum ≤ some finite bound
    apply lt_of_le_of_lt _ (EReal.coe_lt_top (0:ℝ))
    rw [EReal.coe_zero]
    have hcond := h_simple.choose_spec.choose_spec.choose_spec.1
    have hf_eq := h_simple.choose_spec.choose_spec.choose_spec.2
    apply Finset.sum_nonpos
    intro i _
    by_cases hci : h_simple.choose_spec.choose i = 0
    · rw [hci, zero_mul]
    · -- c i > 0, need to show E i is empty
      have hci_pos : h_simple.choose_spec.choose i > 0 := lt_of_le_of_ne (hcond i).2 (Ne.symm hci)
      have hE_empty : h_simple.choose_spec.choose_spec.choose i = ∅ := by
        by_contra hne
        have hne' := Set.nonempty_iff_ne_empty.mpr hne
        obtain ⟨x, hx⟩ := hne'
        have h1 : (0 : EuclideanSpace' d → EReal) x = 0 := rfl
        rw [hf_eq] at h1
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
        have h_nonneg : ∀ j, h_simple.choose_spec.choose j * EReal.indicator (h_simple.choose_spec.choose_spec.choose j) x ≥ 0 := fun j => by
          apply mul_nonneg (hcond j).2
          by_cases hjx : x ∈ h_simple.choose_spec.choose_spec.choose j
          · simp [EReal.indicator_of_mem hjx]
          · simp [EReal.indicator_of_notMem hjx]
        have h_all_zero : ∀ j ∈ Finset.univ, h_simple.choose_spec.choose j * EReal.indicator (h_simple.choose_spec.choose_spec.choose j) x = 0 :=
          Finset.sum_eq_zero_iff_of_nonneg (fun j _ => h_nonneg j) |>.mp h1
        have h_term_i_zero := h_all_zero i (Finset.mem_univ i)
        simp only [EReal.indicator_of_mem hx, mul_one] at h_term_i_zero
        exact (ne_of_gt hci_pos) h_term_i_zero
      rw [hE_empty, Lebesgue_measure.empty, mul_zero]

-- Helper lemma: the norm of zero is zero
lemma ComplexAbsolutelyIntegrable.norm_zero {d:ℕ} : (ComplexAbsolutelyIntegrable.zero (d:=d)).norm = 0 := by
  simp only [ComplexAbsolutelyIntegrable.norm, UnsignedAbsolutelyIntegrable.integ]
  have h_abs_zero : EReal.abs_fun (0 : EuclideanSpace' d → ℂ) = 0 := by
    funext x; simp only [EReal.abs_fun, Pi.zero_apply]; norm_cast
  have h_simple : UnsignedSimpleFunction (0 : EuclideanSpace' d → EReal) := by
    use 0, fun i => Fin.elim0 i, fun i => Fin.elim0 i
    constructor
    · intro i; exact Fin.elim0 i
    · funext x; simp only [Pi.zero_apply, Finset.univ_eq_empty, Finset.sum_empty]
  calc (UnsignedLebesgueIntegral (EReal.abs_fun 0)).toReal
      = (LowerUnsignedLebesgueIntegral (EReal.abs_fun 0)).toReal := rfl
    _ = (LowerUnsignedLebesgueIntegral 0).toReal := by rw [h_abs_zero]
    _ = h_simple.integ.toReal := by rw [LowerUnsignedLebesgueIntegral.eq_simpleIntegral h_simple]
    _ = 0 := by
        -- h_simple.integ is a sum over Fin (h_simple.choose) = Fin k for some k
        -- For the zero function, each term is 0
        simp only [UnsignedSimpleFunction.integ]
        have hcond := h_simple.choose_spec.choose_spec.choose_spec.1
        have hf_eq := h_simple.choose_spec.choose_spec.choose_spec.2
        have h_sum_zero : ∑ i, h_simple.choose_spec.choose i * Lebesgue_measure (h_simple.choose_spec.choose_spec.choose i) = 0 := by
          apply Finset.sum_eq_zero
          intro i _
          by_cases hci : h_simple.choose_spec.choose i = 0
          · rw [hci, zero_mul]
          · have hci_pos : h_simple.choose_spec.choose i > 0 := lt_of_le_of_ne (hcond i).2 (Ne.symm hci)
            have hE_empty : h_simple.choose_spec.choose_spec.choose i = ∅ := by
              by_contra hne
              have hne' := Set.nonempty_iff_ne_empty.mpr hne
              obtain ⟨x, hx⟩ := hne'
              have h1 : (0 : EuclideanSpace' d → EReal) x = 0 := rfl
              rw [hf_eq] at h1
              simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
              have h_nonneg : ∀ j, h_simple.choose_spec.choose j * EReal.indicator (h_simple.choose_spec.choose_spec.choose j) x ≥ 0 := fun j => by
                apply mul_nonneg (hcond j).2
                simp only [EReal.indicator, Real.EReal_fun]
                exact EReal.coe_nonneg.mpr (Set.indicator_nonneg (fun _ _ => zero_le_one) x)
              have h_all_zero : ∀ j ∈ Finset.univ, h_simple.choose_spec.choose j * EReal.indicator (h_simple.choose_spec.choose_spec.choose j) x = 0 :=
                Finset.sum_eq_zero_iff_of_nonneg (fun j _ => h_nonneg j) |>.mp h1
              have h_term_i_zero := h_all_zero i (Finset.mem_univ i)
              simp only [EReal.indicator_of_mem hx, mul_one] at h_term_i_zero
              exact (ne_of_gt hci_pos) h_term_i_zero
            rw [hE_empty, Lebesgue_measure.empty, mul_zero]
        simp only [h_sum_zero, EReal.toReal_zero]

instance PreL1.inst_AddZeroClass {d:ℕ} : AddZeroClass (PreL1 d) := {
  zero := ⟨ 0, ComplexAbsolutelyIntegrable.zero ⟩
  add F G := ⟨ F.f + G.f, F.integrable.add G.integrable ⟩
  zero_add := fun F => by
    apply PreL1.ext
    funext x
    -- Goal: (0 + F).f x = F.f x
    -- (0 + F).f = (⟨0, _⟩ + F).f = (0 : EuclideanSpace' d → ℂ) + F.f
    -- So goal is: (0 + F.f) x = F.f x, i.e., 0 x + F.f x = F.f x
    show (0 : EuclideanSpace' d → ℂ) x + F.f x = F.f x
    simp only [Pi.zero_apply, zero_add]
  add_zero := fun F => by
    apply PreL1.ext
    funext x
    show F.f x + (0 : EuclideanSpace' d → ℂ) x = F.f x
    simp only [Pi.zero_apply, add_zero]
}

instance PreL1.inst_addCommMonoid {d:ℕ} : AddCommMonoid (PreL1 d) := {
  add_assoc := fun F G H => by
    apply PreL1.ext
    funext x
    show (F.f + G.f) x + H.f x = F.f x + (G.f + H.f) x
    simp only [Pi.add_apply, add_assoc]
  add_comm := fun F G => by
    apply PreL1.ext
    funext x
    show F.f x + G.f x = G.f x + F.f x
    ring
  nsmul := nsmulRec
}

instance PreL1.inst_Neg {d:ℕ} : Neg (PreL1 d) := {
  neg F := ⟨ -F.f, F.integrable.of_neg ⟩
}

instance PreL1.inst_Sub {d:ℕ} : Sub (PreL1 d) := {
  sub F G := ⟨ F.f - G.f, F.integrable.sub G.integrable ⟩
}

instance PreL1.inst_module {d:ℕ} : Module ℂ (PreL1 d) := {
  smul c F := ⟨ c • F.f, F.integrable.smul c ⟩
  zero_smul := fun F => by
    apply PreL1.ext
    funext x
    show (0 : ℂ) • F.f x = (0 : EuclideanSpace' d → ℂ) x
    simp only [zero_smul, Pi.zero_apply]
  smul_zero := fun c => by
    apply PreL1.ext
    funext x
    show c • (0 : EuclideanSpace' d → ℂ) x = (0 : EuclideanSpace' d → ℂ) x
    simp only [Pi.zero_apply, smul_zero]
  one_smul := fun F => by
    apply PreL1.ext
    funext x
    show (1 : ℂ) • F.f x = F.f x
    simp only [one_smul]
  mul_smul := fun a b F => by
    apply PreL1.ext
    funext x
    show (a * b) • F.f x = a • (b • F.f x)
    simp only [mul_smul]
  smul_add := fun c F G => by
    apply PreL1.ext
    funext x
    show c • (F.f + G.f) x = (c • F.f + c • G.f) x
    simp only [Pi.add_apply, Pi.smul_apply, smul_add]
  add_smul := fun a b F => by
    apply PreL1.ext
    funext x
    show (a + b) • F.f x = (a • F.f + b • F.f) x
    simp only [Pi.add_apply, Pi.smul_apply, add_smul]
}

-- Helper: integral of the zero simple function is zero
lemma UnsignedSimpleFunction.integ_zero {d:ℕ} :
    let h_simple : UnsignedSimpleFunction (0 : EuclideanSpace' d → EReal) := by
      use 0, fun i => Fin.elim0 i, fun i => Fin.elim0 i
      exact ⟨fun i => Fin.elim0 i, by funext x; simp [Finset.univ_eq_empty]⟩
    h_simple.integ = 0 := by
  -- Use integral_eq with k=0 to compute the integral
  have h_simple : UnsignedSimpleFunction (0 : EuclideanSpace' d → EReal) := by
    use 0, fun i => Fin.elim0 i, fun i => Fin.elim0 i
    exact ⟨fun i => Fin.elim0 i, by funext x; simp [Finset.univ_eq_empty]⟩
  have heq : (0 : EuclideanSpace' d → EReal) = ∑ i : Fin 0, ((Fin.elim0 i : EReal) • (EReal.indicator (Fin.elim0 i : Set (EuclideanSpace' d)))) := by
    funext x; simp [Finset.univ_eq_empty]
  have hmes : ∀ i : Fin 0, LebesgueMeasurable (Fin.elim0 i : Set (EuclideanSpace' d)) := fun i => Fin.elim0 i
  have hnonneg : ∀ i : Fin 0, (Fin.elim0 i : EReal) ≥ 0 := fun i => Fin.elim0 i
  have h_integ := UnsignedSimpleFunction.integral_eq h_simple hmes hnonneg heq
  simp only [Finset.univ_eq_empty, Finset.sum_empty] at h_integ
  exact h_integ

-- Helper: integral of unsigned measurable function is nonnegative
lemma UnsignedLebesgueIntegral.nonneg {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) :
    0 ≤ UnsignedLebesgueIntegral f := by
  simp only [UnsignedLebesgueIntegral, LowerUnsignedLebesgueIntegral]
  apply le_csSup_of_le ⟨⊤, fun _ _ => le_top⟩ _ (le_refl 0)
  use 0
  have h_simple : UnsignedSimpleFunction (0 : EuclideanSpace' d → EReal) := by
    use 0, fun i => Fin.elim0 i, fun i => Fin.elim0 i
    exact ⟨fun i => Fin.elim0 i, by funext x; simp [Finset.univ_eq_empty]⟩
  use h_simple; intro x
  constructor
  · simp only [Pi.zero_apply]; exact hf.1 x
  · have : h_simple.integ = 0 := UnsignedSimpleFunction.integ_zero
    rw [this]

noncomputable instance PreL1.inst_seminormedAddCommGroup {d:ℕ} : SeminormedAddCommGroup (PreL1 d) := {
  norm F := F.integrable.norm
  neg F := ⟨ -F.f, F.integrable.of_neg ⟩
  zsmul := zsmulRec
  neg_add_cancel := fun F => by
    apply PreL1.ext
    funext x
    show (-F.f + F.f) x = (0 : EuclideanSpace' d → ℂ) x
    simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply, neg_add_cancel]
  dist_self := fun F => by
    -- dist F F = ‖-F + F‖ where (-F + F).f = -F.f + F.f
    -- The goal after simp has { f := -F.f, ... } + F which is syntactically different from -F + F
    -- We use convert to bridge the gap
    suffices h : ComplexAbsolutelyIntegrable.zero.norm = 0 from by
      convert h using 2
      funext x
      show (-F.f + F.f) x = (0 : EuclideanSpace' d → ℂ) x
      simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply, neg_add_cancel]
    exact ComplexAbsolutelyIntegrable.norm_zero
  dist_comm := fun F G => by
    -- dist F G = ‖-F+G‖, dist G F = ‖-G+F‖
    simp only [ComplexAbsolutelyIntegrable.norm, UnsignedAbsolutelyIntegrable.integ]
    congr 1; congr 1; funext x; simp only [EReal.abs_fun]; congr 1
    show ‖(-F.f + G.f) x‖ = ‖(-G.f + F.f) x‖
    simp only [Pi.add_apply, Pi.neg_apply]
    rw [show -F.f x + G.f x = -(F.f x - G.f x) from by ring,
        show -G.f x + F.f x = -(G.f x - F.f x) from by ring,
        norm_neg, norm_neg, norm_sub_rev]
  dist_triangle := fun F G H => by
    -- dist F H ≤ dist F G + dist G H
    -- All use ‖-X + Y‖ form. We need to avoid simp expanding things.
    -- The norm of a PreL1 P is P.integrable.norm = (UnsignedLebesgueIntegral (EReal.abs_fun P.f)).toReal
    -- dist X Y = ‖-X + Y‖ = (-X + Y).integrable.norm
    -- Let's set up abbreviations that will definitionally match the goal
    let FH : PreL1 d := -F + H
    let FG : PreL1 d := -F + G
    let GH : PreL1 d := -G + H
    -- The goal is: FH.integrable.norm ≤ FG.integrable.norm + GH.integrable.norm
    show FH.integrable.norm ≤ FG.integrable.norm + GH.integrable.norm
    simp only [ComplexAbsolutelyIntegrable.norm, UnsignedAbsolutelyIntegrable.integ]
    have h_eq : FH.f = FG.f + GH.f := by
      show (-F.f + H.f) = (-F.f + G.f) + (-G.f + H.f)
      funext x; simp only [Pi.add_apply, Pi.neg_apply]; ring
    have h_le : ∀ x, EReal.abs_fun FH.f x ≤ (EReal.abs_fun FG.f + EReal.abs_fun GH.f) x := fun x => by
      rw [h_eq]; simp only [EReal.abs_fun, Pi.add_apply]
      rw [← EReal.coe_add]
      exact EReal.coe_le_coe_iff.mpr (norm_add_le (FG.f x) (GH.f x))
    have hfg_abs := FG.integrable.abs
    have hgh_abs := GH.integrable.abs
    have hfh_abs := FH.integrable.abs
    have h_mono : UnsignedLebesgueIntegral (EReal.abs_fun FH.f) ≤
                  UnsignedLebesgueIntegral (EReal.abs_fun FG.f + EReal.abs_fun GH.f) := by
      apply LowerUnsignedLebesgueIntegral.mono hfh_abs.1 (UnsignedMeasurable.add hfg_abs.1 hgh_abs.1)
      exact AlmostAlways.ofAlways h_le
    have h_add : UnsignedLebesgueIntegral (EReal.abs_fun FG.f + EReal.abs_fun GH.f) =
                 UnsignedLebesgueIntegral (EReal.abs_fun FG.f) + UnsignedLebesgueIntegral (EReal.abs_fun GH.f) := by
      apply LowerUnsignedLebesgueIntegral.add hfg_abs.1 hgh_abs.1 (UnsignedMeasurable.add hfg_abs.1 hgh_abs.1)
    have h_ineq : UnsignedLebesgueIntegral (EReal.abs_fun FH.f) ≤
                  UnsignedLebesgueIntegral (EReal.abs_fun FG.f) + UnsignedLebesgueIntegral (EReal.abs_fun GH.f) := by
      rw [← h_add]; exact h_mono
    have h_finite_fh : UnsignedLebesgueIntegral (EReal.abs_fun FH.f) < ⊤ := hfh_abs.2
    have h_finite_fg : UnsignedLebesgueIntegral (EReal.abs_fun FG.f) < ⊤ := hfg_abs.2
    have h_finite_gh : UnsignedLebesgueIntegral (EReal.abs_fun GH.f) < ⊤ := hgh_abs.2
    have h_nonneg_fh : UnsignedLebesgueIntegral (EReal.abs_fun FH.f) ≠ ⊥ := by
      exact ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (UnsignedLebesgueIntegral.nonneg hfh_abs.1))
    have h_nonneg_fg : UnsignedLebesgueIntegral (EReal.abs_fun FG.f) ≠ ⊥ := by
      exact ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (UnsignedLebesgueIntegral.nonneg hfg_abs.1))
    have h_nonneg_gh : UnsignedLebesgueIntegral (EReal.abs_fun GH.f) ≠ ⊥ := by
      exact ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (UnsignedLebesgueIntegral.nonneg hgh_abs.1))
    have h_sum_ne_top : UnsignedLebesgueIntegral (EReal.abs_fun FG.f) + UnsignedLebesgueIntegral (EReal.abs_fun GH.f) ≠ ⊤ :=
      (EReal.add_lt_top h_finite_fg.ne_top h_finite_gh.ne_top).ne_top
    rw [← EReal.toReal_add h_finite_fg.ne_top h_nonneg_fg h_finite_gh.ne_top h_nonneg_gh]
    exact EReal.toReal_le_toReal h_ineq h_nonneg_fh h_sum_ne_top
}

instance PreL1.inst_normedSpace {d:ℕ} : NormedSpace ℂ (PreL1 d) := {
  norm_smul_le := fun a F => by
    -- Goal: ‖a • F‖ ≤ ‖a‖ * ‖F‖
    -- ‖F‖ = F.integrable.norm for PreL1
    show (a • F).integrable.norm ≤ ‖a‖ * F.integrable.norm
    simp only [ComplexAbsolutelyIntegrable.norm, UnsignedAbsolutelyIntegrable.integ]
    -- Key fact: EReal.abs_fun (a • F.f) x = ‖a‖ * EReal.abs_fun F.f x
    have h_eq : ∀ x, EReal.abs_fun (a • F).f x = ‖a‖.toEReal * EReal.abs_fun F.f x := fun x => by
      simp only [EReal.abs_fun]
      -- Show ‖(a • F).f x‖ = ‖a‖ * ‖F.f x‖
      show (‖(a • F).f x‖ : EReal) = ‖a‖.toEReal * ‖F.f x‖.toEReal
      rw [show (a • F).f x = a * F.f x from rfl, norm_mul, EReal.coe_mul]
    have hf_abs := ComplexAbsolutelyIntegrable.abs F.f F.integrable
    have h_smul_eq : EReal.abs_fun (a • F).f = (fun x => ‖a‖.toEReal * EReal.abs_fun F.f x) := by
      funext x; exact h_eq x
    rw [h_smul_eq]
    have h_scale : UnsignedLebesgueIntegral (fun x => ‖a‖.toEReal * EReal.abs_fun F.f x) =
                   ‖a‖.toEReal * UnsignedLebesgueIntegral (EReal.abs_fun F.f) := by
      have h_eq' : (fun x => ‖a‖.toEReal * EReal.abs_fun F.f x) = (‖a‖.toEReal : EReal) • EReal.abs_fun F.f := by
        funext x; simp only [Pi.smul_apply, smul_eq_mul]
      rw [h_eq', UnsignedLebesgueIntegral]
      exact LowerUnsignedLebesgueIntegral.hom hf_abs.1 (norm_nonneg a)
    rw [h_scale]
    -- Now we have: (‖a‖.toEReal * UnsignedLebesgueIntegral (EReal.abs_fun F.f)).toReal ≤ ‖a‖ * (UnsignedLebesgueIntegral (EReal.abs_fun F.f)).toReal
    -- We actually have equality
    have h_finite : UnsignedLebesgueIntegral (EReal.abs_fun F.f) < ⊤ := hf_abs.2
    have h_nonneg : 0 ≤ UnsignedLebesgueIntegral (EReal.abs_fun F.f) := UnsignedLebesgueIntegral.nonneg hf_abs.1
    have h_ne_bot : UnsignedLebesgueIntegral (EReal.abs_fun F.f) ≠ ⊥ :=
      ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero h_nonneg)
    rw [EReal.toReal_mul]
    simp only [EReal.toReal_coe, le_refl]
}

theorem PreL1.dist_eq {d:ℕ} (F G: PreL1 d) : dist F G = ‖F-G‖ :=
  dist_eq_norm F G

noncomputable abbrev L1 (d:ℕ) := SeparationQuotient (PreL1 d)

@[coe]
noncomputable def PreL1.toL1 {d:ℕ} (F: PreL1 d) : L1 d := SeparationQuotient.mk F

noncomputable instance PreL1.inst_coeL1 {d:ℕ} : Coe (PreL1 d) (L1 d) := ⟨ PreL1.toL1 ⟩

noncomputable def ComplexAbsolutelyIntegrable.toL1 {d:ℕ} {f:EuclideanSpace' d → ℂ} (hf: ComplexAbsolutelyIntegrable f) : L1 d := SeparationQuotient.mk hf.to_PreL1

theorem L1.dist_eq {d:ℕ} (f g: EuclideanSpace' d → ℂ) (hf: ComplexAbsolutelyIntegrable f) (hg: ComplexAbsolutelyIntegrable g) : dist hf.toL1 hg.toL1 = (hf.sub hg).norm := by
  simp only [ComplexAbsolutelyIntegrable.toL1]
  rw [SeparationQuotient.dist_mk, dist_eq_norm]
  simp only [ComplexAbsolutelyIntegrable.norm, UnsignedAbsolutelyIntegrable.integ, Norm.norm]; rfl

theorem L1.dist_eq_zero {d:ℕ} (f g: EuclideanSpace' d → ℂ) (hf: ComplexAbsolutelyIntegrable f) (hg: ComplexAbsolutelyIntegrable g) : dist hf.toL1 hg.toL1 = 0 ↔ AlmostEverywhereEqual f g := by
  rw [L1.dist_eq]
  simp only [ComplexAbsolutelyIntegrable.norm, UnsignedAbsolutelyIntegrable.integ]
  rw [EReal.toReal_eq_zero_iff]
  -- Eliminate ⊤ and ⊥ cases
  have h_finite : UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) < ⊤ := (hf.sub hg).2
  have h_nonneg : UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) ≥ 0 :=
    UnsignedLebesgueIntegral.nonneg (hf.sub hg).abs.1
  have h_ne_top : UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) ≠ ⊤ := ne_of_lt h_finite
  have h_ne_bot : UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) ≠ ⊥ := by
    intro h_eq_bot
    rw [h_eq_bot] at h_nonneg
    exact not_le.mpr EReal.bot_lt_zero h_nonneg
  simp only [h_ne_top, h_ne_bot, or_false]
  -- Now goal: UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) = 0 ↔ AlmostEverywhereEqual f g
  have h_meas : UnsignedMeasurable (EReal.abs_fun (f - g)) := (hf.sub hg).abs.1
  rw [show UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) = h_meas.integ from rfl]
  rw [UnsignedLebesgueIntegral.eq_zero_aeZero h_meas]
  -- Goal: AlmostAlways (fun x ↦ EReal.abs_fun (f - g) x = 0) ↔ AlmostEverywhereEqual f g
  unfold AlmostEverywhereEqual AlmostAlways
  -- Goal: IsNull {x | ¬EReal.abs_fun (f - g) x = 0} ↔ IsNull {x | ¬f x = g x}
  -- Show the sets are equal
  have h_sets_eq : {x | ¬EReal.abs_fun (f - g) x = 0} = {x | ¬f x = g x} := by
    ext x
    simp only [Set.mem_setOf_eq, EReal.abs_fun]
    -- Goal: ¬‖(f - g) x‖.toEReal = 0 ↔ ¬f x = g x
    constructor
    · intro h hfg
      apply h
      simp only [Pi.sub_apply, hfg, sub_self, norm_zero, EReal.coe_zero]
    · intro h heq
      apply h
      have h_norm_zero : ‖(f - g) x‖ = 0 := by
        have : (‖(f - g) x‖ : EReal) = 0 := heq
        exact EReal.coe_eq_zero.mp this
      exact sub_eq_zero.mp (norm_eq_zero.mp h_norm_zero)
  rw [h_sets_eq]

/-- Precomposing a real simple function with a translation gives a real simple function. -/
lemma RealSimpleFunction.translate {d:ℕ} {f : EuclideanSpace' d → ℝ} (hf : RealSimpleFunction f) (a : EuclideanSpace' d) :
    RealSimpleFunction (fun x => f (x + a)) := by
  obtain ⟨k, c, E, hmes, heq⟩ := hf
  use k, c, fun i => E i + ({(-a)} : Set (EuclideanSpace' d))
  constructor
  · intro i
    exact (LebesgueMeasurable.translate (E i) (-a)).mp (hmes i)
  · rw [heq]
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    by_cases hx : x + a ∈ E i
    · rw [Set.indicator'_of_mem hx]
      have hx' : x ∈ E i + ({(-a)} : Set (EuclideanSpace' d)) :=
        Set.mem_add.mpr ⟨x + a, hx, -a, Set.mem_singleton (-a), by abel⟩
      rw [Set.indicator'_of_mem hx']
    · rw [Set.indicator'_of_notMem hx]
      rw [Set.indicator'_of_notMem]
      intro hx'
      rcases Set.mem_add.mp hx' with ⟨e, he, t, ht, heq'⟩
      have ht' : t = -a := Set.mem_singleton_iff.mp ht
      apply hx
      rw [← heq', ht']
      rw [show (e + (-a)) + a = e from by abel]
      exact he

/-- Precomposing a complex simple function with a translation gives a complex simple function. -/
lemma ComplexSimpleFunction.translate {d:ℕ} {f : EuclideanSpace' d → ℂ} (hf : ComplexSimpleFunction f) (a : EuclideanSpace' d) :
    ComplexSimpleFunction (fun x => f (x + a)) := by
  obtain ⟨k, c, E, hmes, heq⟩ := hf
  use k, c, fun i => E i + ({(-a)} : Set (EuclideanSpace' d))
  constructor
  · intro i
    exact (LebesgueMeasurable.translate (E i) (-a)).mp (hmes i)
  · rw [heq]
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    by_cases hx : x + a ∈ E i
    · have hx' : x ∈ E i + ({(-a)} : Set (EuclideanSpace' d)) :=
        Set.mem_add.mpr ⟨x + a, hx, -a, Set.mem_singleton (-a), by abel⟩
      rw [Complex.indicator, Real.complex_fun, Set.indicator'_of_mem hx,
          Complex.indicator, Real.complex_fun, Set.indicator'_of_mem hx']
    · rw [Complex.indicator, Real.complex_fun, Set.indicator'_of_notMem hx]
      rw [Complex.indicator, Real.complex_fun, Set.indicator'_of_notMem]
      intro hx'
      rcases Set.mem_add.mp hx' with ⟨e, he, t, ht, heq'⟩
      have ht' : t = -a := Set.mem_singleton_iff.mp ht
      apply hx
      rw [← heq', ht']
      rw [show (e + (-a)) + a = e from by abel]
      exact he

/-- Real measurability is preserved under precomposition with a translation. -/
lemma RealMeasurable.translate {d:ℕ} {f : EuclideanSpace' d → ℝ} (hf : RealMeasurable f) (a : EuclideanSpace' d) :
    RealMeasurable (fun x => f (x + a)) := by
  obtain ⟨g, hg_simple, hg_conv⟩ := hf
  use fun n => fun x => g n (x + a)
  constructor
  · intro n; exact RealSimpleFunction.translate (hg_simple n) a
  · intro x
    simpa using (hg_conv (x + a))

/-- Complex measurability is preserved under precomposition with a translation. -/
lemma ComplexMeasurable.translate {d:ℕ} {f : EuclideanSpace' d → ℂ} (hf : ComplexMeasurable f) (a : EuclideanSpace' d) :
    ComplexMeasurable (fun x => f (x + a)) := by
  obtain ⟨g, hg_simple, hg_conv⟩ := hf
  use fun n => fun x => g n (x + a)
  constructor
  · intro n; exact ComplexSimpleFunction.translate (hg_simple n) a
  · intro x
    simpa using (hg_conv (x + a))

/-- Exercise 1.3.20 (Translation invariance)-/
theorem RealAbsolutelyIntegrable.trans {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealAbsolutelyIntegrable f) (a: EuclideanSpace' d) : RealAbsolutelyIntegrable (fun x ↦ f (x + a)) := by
  constructor
  · exact hf.1.translate a
  · rw [show EReal.abs_fun (fun x ↦ f (x + a)) = fun x => EReal.abs_fun f (x + a) by rfl]
    rw [UnsignedLebesgueIntegral.trans (hf.abs.1) a]
    exact hf.2

theorem RealAbsolutelyIntegrable.integ_trans {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealAbsolutelyIntegrable f) (a: EuclideanSpace' d) : (hf.trans a).integ = hf.integ  := by
  have h_pos_eq : (UnsignedLebesgueIntegral (EReal.pos_fun (fun x ↦ f (x + a)))).toReal = (UnsignedLebesgueIntegral (EReal.pos_fun f)).toReal := by
    rw [show EReal.pos_fun (fun x ↦ f (x + a)) = fun x => EReal.pos_fun f (x + a) by rfl]
    rw [UnsignedLebesgueIntegral.trans (hf.pos.1) a]
    rfl
  have h_neg_eq : (UnsignedLebesgueIntegral (EReal.neg_fun (fun x ↦ f (x + a)))).toReal = (UnsignedLebesgueIntegral (EReal.neg_fun f)).toReal := by
    rw [show EReal.neg_fun (fun x ↦ f (x + a)) = fun x => EReal.neg_fun f (x + a) by rfl]
    rw [UnsignedLebesgueIntegral.trans (hf.neg.1) a]
    rfl
  simp only [RealAbsolutelyIntegrable.integ, UnsignedAbsolutelyIntegrable.integ]
  rw [h_pos_eq, h_neg_eq]

theorem ComplexAbsolutelyIntegrable.trans {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexAbsolutelyIntegrable f) (a: EuclideanSpace' d) : ComplexAbsolutelyIntegrable (fun x ↦ f (x + a)) := by
  constructor
  · exact hf.1.translate a
  · rw [show EReal.abs_fun (fun x ↦ f (x + a)) = fun x => EReal.abs_fun f (x + a) by rfl]
    rw [UnsignedLebesgueIntegral.trans (hf.abs.1) a]
    exact hf.2

theorem ComplexAbsolutelyIntegrable.integ_trans {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexAbsolutelyIntegrable f) (a: EuclideanSpace' d) : (hf.trans a).integ = hf.integ  := by
  have hre_fun : Complex.re_fun (fun x => f (x + a)) = (fun x => Complex.re_fun f (x + a)) := rfl
  have him_fun : Complex.im_fun (fun x => f (x + a)) = (fun x => Complex.im_fun f (x + a)) := rfl
  have h_re_eq : (hf.trans a).re.integ = (hf.re.trans a).integ := by
    simp only [RealAbsolutelyIntegrable.integ, UnsignedAbsolutelyIntegrable.integ, hre_fun]
  have h_im_eq : (hf.trans a).im.integ = (hf.im.trans a).integ := by
    simp only [RealAbsolutelyIntegrable.integ, UnsignedAbsolutelyIntegrable.integ, him_fun]
  simp only [ComplexAbsolutelyIntegrable.integ]
  rw [h_re_eq, h_im_eq]
  rw [RealAbsolutelyIntegrable.integ_trans (hf := hf.re) (a := a),
      RealAbsolutelyIntegrable.integ_trans (hf := hf.im) (a := a)]

/-- Precomposing a real simple function with an invertible linear map gives a real simple function. -/
lemma RealSimpleFunction.comp_linear {d:ℕ} {f : EuclideanSpace' d → ℝ} (hf : RealSimpleFunction f)
    {A : EuclideanSpace' d →ₗ[ℝ] EuclideanSpace' d} (hA : A.det ≠ 0) :
    RealSimpleFunction (fun x => f (A x)) := by
  obtain ⟨k, c, E, hmes, heq⟩ := hf
  have hA_inj : Function.Injective A := by
    have hker : LinearMap.ker A = ⊥ := by
      by_contra hne
      exact hA ((LinearMap.det_eq_zero_iff_ker_ne_bot).mpr hne)
    exact LinearMap.ker_eq_bot.mp hker
  let T := LinearEquiv.ofInjectiveEndo A hA_inj
  have hTx : ∀ x, T x = A x := fun x => by
    simp [T]
  use k, c, fun i => T.symm '' (E i)
  constructor
  · intro i
    exact LebesgueMeasurable.linear T.symm (hmes i)
  · rw [heq]
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    by_cases hx : A x ∈ E i
    · rw [Set.indicator'_of_mem hx]
      have hx' : x ∈ T.symm '' (E i) := by
        exact (Set.mem_image T.symm (E i) x).mpr ⟨A x, hx, by
          rw [← hTx x]
          exact T.symm_apply_apply x⟩
      rw [Set.indicator'_of_mem hx']
    · rw [Set.indicator'_of_notMem hx]
      rw [Set.indicator'_of_notMem]
      intro hx'
      rcases (Set.mem_image T.symm (E i) x).mp hx' with ⟨y, hy, hy_eq⟩
      apply hx
      rw [← hTx x]
      rw [← hy_eq]
      rw [T.apply_symm_apply y]
      exact hy

/-- Precomposing a complex simple function with an invertible linear map gives a complex simple function. -/
lemma ComplexSimpleFunction.comp_linear {d:ℕ} {f : EuclideanSpace' d → ℂ} (hf : ComplexSimpleFunction f)
    {A : EuclideanSpace' d →ₗ[ℝ] EuclideanSpace' d} (hA : A.det ≠ 0) :
    ComplexSimpleFunction (fun x => f (A x)) := by
  obtain ⟨k, c, E, hmes, heq⟩ := hf
  have hA_inj : Function.Injective A := by
    have hker : LinearMap.ker A = ⊥ := by
      by_contra hne
      exact hA ((LinearMap.det_eq_zero_iff_ker_ne_bot).mpr hne)
    exact LinearMap.ker_eq_bot.mp hker
  let T := LinearEquiv.ofInjectiveEndo A hA_inj
  have hTx : ∀ x, T x = A x := fun x => by
    simp [T]
  use k, c, fun i => T.symm '' (E i)
  constructor
  · intro i
    exact LebesgueMeasurable.linear T.symm (hmes i)
  · rw [heq]
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    by_cases hx : A x ∈ E i
    · have hx' : x ∈ T.symm '' (E i) := by
        exact (Set.mem_image T.symm (E i) x).mpr ⟨A x, hx, by
          rw [← hTx x]
          exact T.symm_apply_apply x⟩
      rw [Complex.indicator, Real.complex_fun, Set.indicator'_of_mem hx,
          Complex.indicator, Real.complex_fun, Set.indicator'_of_mem hx']
    · rw [Complex.indicator, Real.complex_fun, Set.indicator'_of_notMem hx]
      rw [Complex.indicator, Real.complex_fun, Set.indicator'_of_notMem]
      intro hx'
      rcases (Set.mem_image T.symm (E i) x).mp hx' with ⟨y, hy, hy_eq⟩
      apply hx
      rw [← hTx x]
      rw [← hy_eq]
      rw [T.apply_symm_apply y]
      exact hy

/-- Real measurability is preserved under precomposition with an invertible linear map. -/
lemma RealMeasurable.comp_linear {d:ℕ} {f : EuclideanSpace' d → ℝ} (hf : RealMeasurable f)
    {A : EuclideanSpace' d →ₗ[ℝ] EuclideanSpace' d} (hA : A.det ≠ 0) :
    RealMeasurable (fun x => f (A x)) := by
  obtain ⟨g, hg_simple, hg_conv⟩ := hf
  use fun n => fun x => g n (A x)
  constructor
  · intro n; exact RealSimpleFunction.comp_linear (hg_simple n) hA
  · intro x
    simpa using (hg_conv (A x))

/-- Complex measurability is preserved under precomposition with an invertible linear map. -/
lemma ComplexMeasurable.comp_linear {d:ℕ} {f : EuclideanSpace' d → ℂ} (hf : ComplexMeasurable f)
    {A : EuclideanSpace' d →ₗ[ℝ] EuclideanSpace' d} (hA : A.det ≠ 0) :
    ComplexMeasurable (fun x => f (A x)) := by
  obtain ⟨g, hg_simple, hg_conv⟩ := hf
  use fun n => fun x => g n (A x)
  constructor
  · intro n; exact ComplexSimpleFunction.comp_linear (hg_simple n) hA
  · intro x
    simpa using (hg_conv (A x))

/-- Exercise 1.3.20 (Linear change of variables)-/
theorem RealAbsolutelyIntegrable.comp_linear {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealAbsolutelyIntegrable f) {A: EuclideanSpace' d →ₗ[ℝ] EuclideanSpace' d} (hA: A.det ≠ 0) :
    RealAbsolutelyIntegrable (fun x ↦ f (A x)) := by
  constructor
  · exact hf.1.comp_linear hA
  · rw [show EReal.abs_fun (fun x ↦ f (A x)) = fun x => EReal.abs_fun f (A x) by rfl]
    rw [UnsignedLebesgueIntegral.comp_linear (hf.abs.1) A hA]
    have hdet_pos : 0 < |A.det|⁻¹ := inv_pos.mpr (abs_pos.mpr hA)
    have h_ne_top : (|A.det|⁻¹ : ℝ).toEReal * UnsignedLebesgueIntegral (EReal.abs_fun f) ≠ ⊤ := by
      rw [EReal.mul_ne_top]
      refine ⟨?_, ?_, ?_, ?_⟩
      · left; exact EReal.coe_ne_bot (|A.det|⁻¹)
      · left; exact le_of_lt (EReal.coe_pos.mpr hdet_pos)
      · left; exact EReal.coe_ne_top (|A.det|⁻¹)
      · right; exact hf.2.ne_top
    exact Ne.lt_top h_ne_top

theorem RealAbsolutelyIntegrable.integ_comp_linear {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealAbsolutelyIntegrable f) {A: EuclideanSpace' d →ₗ[ℝ] EuclideanSpace' d} (hA: A.det ≠ 0) :
    (hf.comp_linear hA).integ = |A.det|⁻¹ * hf.integ := by
  have h_pos_eq : (UnsignedLebesgueIntegral (EReal.pos_fun (fun x ↦ f (A x)))).toReal = |A.det|⁻¹ * (UnsignedLebesgueIntegral (EReal.pos_fun f)).toReal := by
    rw [show EReal.pos_fun (fun x ↦ f (A x)) = fun x => EReal.pos_fun f (A x) by rfl]
    rw [UnsignedLebesgueIntegral.comp_linear (hf.pos.1) A hA]
    rw [EReal.toReal_mul, EReal.toReal_coe]
    rfl
  have h_neg_eq : (UnsignedLebesgueIntegral (EReal.neg_fun (fun x ↦ f (A x)))).toReal = |A.det|⁻¹ * (UnsignedLebesgueIntegral (EReal.neg_fun f)).toReal := by
    rw [show EReal.neg_fun (fun x ↦ f (A x)) = fun x => EReal.neg_fun f (A x) by rfl]
    rw [UnsignedLebesgueIntegral.comp_linear (hf.neg.1) A hA]
    rw [EReal.toReal_mul, EReal.toReal_coe]
    rfl
  simp only [RealAbsolutelyIntegrable.integ, UnsignedAbsolutelyIntegrable.integ]
  rw [h_pos_eq, h_neg_eq]
  ring

theorem ComplexAbsolutelyIntegrable.comp_linear {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexAbsolutelyIntegrable f) {A: EuclideanSpace' d →ₗ[ℝ] EuclideanSpace' d} (hA: A.det ≠ 0) :
    ComplexAbsolutelyIntegrable (fun x ↦ f (A x)) := by
  constructor
  · exact hf.1.comp_linear hA
  · rw [show EReal.abs_fun (fun x ↦ f (A x)) = fun x => EReal.abs_fun f (A x) by rfl]
    rw [UnsignedLebesgueIntegral.comp_linear (hf.abs.1) A hA]
    have hdet_pos : 0 < |A.det|⁻¹ := inv_pos.mpr (abs_pos.mpr hA)
    have h_ne_top : (|A.det|⁻¹ : ℝ).toEReal * UnsignedLebesgueIntegral (EReal.abs_fun f) ≠ ⊤ := by
      rw [EReal.mul_ne_top]
      refine ⟨?_, ?_, ?_, ?_⟩
      · left; exact EReal.coe_ne_bot (|A.det|⁻¹)
      · left; exact le_of_lt (EReal.coe_pos.mpr hdet_pos)
      · left; exact EReal.coe_ne_top (|A.det|⁻¹)
      · right; exact hf.2.ne_top
    exact Ne.lt_top h_ne_top

theorem ComplexAbsolutelyIntegrable.integ_comp_linear {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexAbsolutelyIntegrable f) {A: EuclideanSpace' d →ₗ[ℝ] EuclideanSpace' d} (hA: A.det ≠ 0) :
    (hf.comp_linear hA).integ = |A.det|⁻¹ * hf.integ := by
  have hre_fun : Complex.re_fun (fun x => f (A x)) = (fun x => Complex.re_fun f (A x)) := rfl
  have him_fun : Complex.im_fun (fun x => f (A x)) = (fun x => Complex.im_fun f (A x)) := rfl
  have h_re_eq : (hf.comp_linear hA).re.integ = (hf.re.comp_linear hA).integ := by
    simp only [RealAbsolutelyIntegrable.integ, UnsignedAbsolutelyIntegrable.integ, hre_fun]
  have h_im_eq : (hf.comp_linear hA).im.integ = (hf.im.comp_linear hA).integ := by
    simp only [RealAbsolutelyIntegrable.integ, UnsignedAbsolutelyIntegrable.integ, him_fun]
  simp only [ComplexAbsolutelyIntegrable.integ]
  rw [h_re_eq, h_im_eq]
  rw [RealAbsolutelyIntegrable.integ_comp_linear (hf := hf.re) (hA := hA),
      RealAbsolutelyIntegrable.integ_comp_linear (hf := hf.im) (hA := hA)]
  rw [Complex.ofReal_mul, Complex.ofReal_mul]
  ring

private lemma lift_image_BoundedInterval_measurable (J : BoundedInterval) :
    LebesgueMeasurable (Real.equiv_EuclideanSpace' '' (J : Set ℝ)) := by
  rw [← BoundedInterval.coe_of_box]
  exact (IsElementary.box (J : Box 1)).measurable

/-- The outer measure of the lifted image of a bounded interval equals its length. -/
private lemma lift_interval_measure_134 (J : BoundedInterval) :
    Lebesgue_outer_measure (Real.equiv_EuclideanSpace' '' (J : Set ℝ)) = (|J|ₗ : EReal) := by
  rw [← BoundedInterval.coe_of_box]
  rw [Lebesgue_outer_measure.elementary ((J : Box 1).toSet) (IsElementary.box (J : Box 1))]
  rw [IsElementary.measure_of_box]
  simp

private lemma uniform_piece_inj_134 {I : BoundedInterval} {n : ℕ} (P : TaggedPartition I n) :
    Function.Injective (fun i : Fin n => Ico (P.x i.castSucc) (P.x i.succ)) := by
  intro i j hij
  have hset : Set.Ico (P.x i.castSucc) (P.x i.succ) = Set.Ico (P.x j.castSucc) (P.x j.succ) := by
    simpa [BoundedInterval.set_Ico] using congrArg (fun K : BoundedInterval => (K : Set ℝ)) hij
  have hcast : P.x i.castSucc = P.x j.castSucc := by
    have hi : P.x i.castSucc ∈ Set.Ico (P.x i.castSucc) (P.x i.succ) :=
      ⟨le_rfl, P.x_mono Fin.castSucc_lt_succ⟩
    have h1 : P.x j.castSucc ≤ P.x i.castSucc := by
      rw [hset] at hi
      exact hi.1
    have hj : P.x j.castSucc ∈ Set.Ico (P.x j.castSucc) (P.x j.succ) :=
      ⟨le_rfl, P.x_mono Fin.castSucc_lt_succ⟩
    have h2 : P.x i.castSucc ≤ P.x j.castSucc := by
      rw [← hset] at hj
      exact hj.1
    exact le_antisymm h2 h1
  have hcij : i.castSucc = j.castSucc := P.x_mono.injective hcast
  apply Fin.ext
  simpa using congrArg Fin.val hcij

/-- The pieces of a tagged partition are pairwise disjoint (as sets). -/
private lemma uniform_pieces_disjoint_134 {I : BoundedInterval} {n : ℕ} (P : TaggedPartition I n) :
    (((Finset.image (fun i : Fin n => Ico (P.x i.castSucc) (P.x i.succ)) Finset.univ ∪
        ({Icc I.b I.b} : Finset BoundedInterval)) : Finset BoundedInterval) : Set BoundedInterval).PairwiseDisjoint
      BoundedInterval.toSet := by
  intro J hJ K hK hne
  simp only [Finset.mem_coe, Finset.mem_union, Finset.mem_image, Finset.mem_singleton] at hJ hK
  rcases hJ with (⟨i, _, rfl⟩ | rfl) <;> rcases hK with (⟨j, _, rfl⟩ | rfl)
  · -- both Ico pieces
    have hij : i ≠ j := by
      intro h_eq
      exact hne (congrArg (fun k : Fin n => Ico (P.x k.castSucc) (P.x k.succ)) h_eq)
    have hlt_or : i < j ∨ j < i := lt_or_gt_of_ne hij
    rcases hlt_or with (hlt | hlt)
    · have hmono : P.x i.succ ≤ P.x j.castSucc := by
        have hval : (i.succ : Fin (n+1)).val ≤ (j.castSucc : Fin (n+1)).val := by
          simp [Fin.val_succ]
          omega
        exact P.x_mono.monotone hval
      exact (Set.Ico_disjoint_Ico).mpr (by
        have h1 : min (P.x i.succ) (P.x j.succ) = P.x i.succ :=
          min_eq_left (le_trans hmono (le_of_lt (P.x_mono Fin.castSucc_lt_succ)))
        have h2 : max (P.x i.castSucc) (P.x j.castSucc) = P.x j.castSucc :=
          max_eq_right (le_trans (le_of_lt (P.x_mono Fin.castSucc_lt_succ)) hmono)
        rw [h1, h2]
        exact hmono)
    · have hmono : P.x j.succ ≤ P.x i.castSucc := by
        have hval : (j.succ : Fin (n+1)).val ≤ (i.castSucc : Fin (n+1)).val := by
          simp [Fin.val_succ]
          omega
        exact P.x_mono.monotone hval
      exact ((Set.Ico_disjoint_Ico).mpr (by
        have h1 : min (P.x j.succ) (P.x i.succ) = P.x j.succ :=
          min_eq_left (le_trans hmono (le_of_lt (P.x_mono Fin.castSucc_lt_succ)))
        have h2 : max (P.x j.castSucc) (P.x i.castSucc) = P.x i.castSucc :=
          max_eq_right (le_trans (le_of_lt (P.x_mono Fin.castSucc_lt_succ)) hmono)
        rw [h1, h2]
        exact hmono)).symm
  · -- Ico vs singleton {I.b}
    change Disjoint ((Ico (P.x i.castSucc) (P.x i.succ)) : Set ℝ) ((Icc I.b I.b) : Set ℝ)
    rw [Set.disjoint_iff_inter_eq_empty]
    apply Set.not_nonempty_iff_eq_empty.mp
    rintro ⟨x, hx⟩
    have h1 : x < P.x i.succ := hx.1.2
    have h2 : P.x i.succ ≤ P.x (Fin.last n) := by
      exact P.x_mono.monotone (Fin.le_last (i.succ))
    have h3 : x = I.b := by simpa [BoundedInterval.set_Icc, Set.Icc_self] using hx.2
    rw [P.x_end] at h2
    linarith
  · -- singleton vs Ico
    change Disjoint ((Icc I.b I.b) : Set ℝ) ((Ico (P.x j.castSucc) (P.x j.succ)) : Set ℝ)
    rw [Set.disjoint_iff_inter_eq_empty]
    apply Set.not_nonempty_iff_eq_empty.mp
    rintro ⟨x, hx⟩
    have h1 : x < P.x j.succ := hx.2.2
    have h2 : P.x j.succ ≤ P.x (Fin.last n) := by
      exact P.x_mono.monotone (Fin.le_last (j.succ))
    have h3 : x = I.b := by simpa [BoundedInterval.set_Icc, Set.Icc_self] using hx.1
    rw [P.x_end] at h2
    linarith
  · -- both singleton: equal
    simp at hne

/-- The half-open pieces together with the singleton point cover I. -/
private lemma uniform_pieces_cover_134 {I : BoundedInterval} {n : ℕ} (P : TaggedPartition I n)
    (hI : I = Icc I.a I.b) :
    I.toSet = ⋃ J ∈ ((Finset.image (fun i : Fin n => Ico (P.x i.castSucc) (P.x i.succ)) Finset.univ ∪
        ({Icc I.b I.b} : Finset BoundedInterval)) : Finset BoundedInterval), J.toSet := by
  ext x
  constructor
  · intro hx
    rw [hI] at hx
    have hxab : I.a ≤ x ∧ x ≤ I.b := by simpa using hx
    by_cases hx_end : x = I.b
    · subst x
      refine Set.mem_iUnion₂.mpr ⟨Icc I.b I.b, Finset.mem_union_right _ (Finset.mem_singleton_self _), ?_⟩
      simp
    · have hx_lt_Ib : x < I.b := lt_of_le_of_ne hxab.2 hx_end
      have h_exists : (Finset.filter (fun k : Fin (n+1) => x < P.x k) Finset.univ).Nonempty := by
        refine ⟨Fin.last n, ?_⟩
        simp
        rw [P.x_end]
        exact hx_lt_Ib
      let k := Finset.min' (Finset.filter (fun k : Fin (n+1) => x < P.x k) Finset.univ) h_exists
      have hk_mem : k ∈ Finset.filter (fun k : Fin (n+1) => x < P.x k) Finset.univ :=
        Finset.min'_mem _ h_exists
      have hx_lt_Pk : x < P.x k := (Finset.mem_filter.mp hk_mem).2
      have hk0 : k ≠ (0 : Fin (n+1)) := by
        intro hk0
        rw [hk0, P.x_start] at hx_lt_Pk
        linarith [hxab.1]
      have hi_pred : ∃ (i : Fin n), i.succ = k := by
        refine ⟨Fin.pred k hk0, ?_⟩
        simp
      rcases hi_pred with ⟨i, hi⟩
      have hx_lt_Pi_succ : x < P.x i.succ := by
        rw [hi]
        exact hx_lt_Pk
      have hx_ge : P.x i.castSucc ≤ x := by
        by_contra! hlt
        have hmem : (i.castSucc : Fin (n+1)) ∈ Finset.filter (fun k' : Fin (n+1) => x < P.x k') Finset.univ := by
          simp
          exact hlt
        have hk_le : k ≤ (i.castSucc : Fin (n+1)) := Finset.min'_le _ _ hmem
        have h_val' : i.val + 1 = k.val := by
          simpa [Fin.val_succ] using congrArg Fin.val hi
        have h_val : k.val = i.val + 1 := h_val'.symm
        have h_cast_val : (i.castSucc : Fin (n+1)).val = i.val := by simp
        omega
      refine Set.mem_iUnion₂.mpr ⟨Ico (P.x i.castSucc) (P.x i.succ), ?_, ?_⟩
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
      · simp [Set.mem_Ico, hx_ge, hx_lt_Pi_succ]
  · intro hx
    rcases Set.mem_iUnion₂.mp hx with ⟨J, hJ, hxJ⟩
    rw [hI]
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_singleton] at hJ
    rcases hJ with (⟨i, _, rfl⟩ | rfl)
    · constructor
      · have hmono : P.x 0 ≤ P.x i.castSucc := P.x_mono.monotone (Fin.zero_le _)
        calc I.a = P.x 0 := P.x_start.symm
          _ ≤ P.x i.castSucc := hmono
          _ ≤ x := hxJ.1
      · have hmono : P.x i.succ ≤ P.x (Fin.last n) := P.x_mono.monotone (Fin.le_last _)
        calc x ≤ P.x i.succ := le_of_lt hxJ.2
          _ ≤ P.x (Fin.last n) := hmono
          _ = I.b := P.x_end
    · have hxb : x = I.b := by simpa using hxJ
      subst x
      have hab' : I.a ≤ I.b := by
        have hmono : P.x 0 ≤ P.x (Fin.last n) := P.x_mono.monotone (Fin.zero_le _)
        rw [P.x_start, P.x_end] at hmono
        exact hmono
      exact ⟨hab', le_rfl⟩

/-- Approximate a Riemann integrable function from above and below by piecewise constant
    functions built from a fine partition, with integral bounds in terms of R and epsilon. -/
private lemma upper_lower_step_approx_134 {f : ℝ → ℝ} {I : BoundedInterval}
    (hI : I = Icc I.a I.b) (hab : I.a < I.b)
    (hbound : ∃ M, ∀ x ∈ I.toSet, |f x| ≤ M) (R : ℝ) (ε : ℝ) (hε : 0 < ε)
    (hεδ : ∀ ε > 0, ∃ δ > 0, ∀ n, ∀ P : TaggedPartition I n, P.norm ≤ δ → |P.RiemannSum f - R| ≤ ε) :
    ∃ (T : Finset BoundedInterval) (val_u val_l : BoundedInterval → ℝ)
      (hdisj : (T : Set BoundedInterval).PairwiseDisjoint BoundedInterval.toSet)
      (hcover : I.toSet = ⋃ J ∈ T, J.toSet),
      (∀ x ∈ I.toSet, (PiecewiseConstantFunction.mkPCF T val_l hdisj hcover).f x ≤ f x ∧ f x ≤ (PiecewiseConstantFunction.mkPCF T val_u hdisj hcover).f x) ∧
      (∀ x ∉ I.toSet, (PiecewiseConstantFunction.mkPCF T val_u hdisj hcover).f x = 0 ∧ (PiecewiseConstantFunction.mkPCF T val_l hdisj hcover).f x = 0) ∧
      (PiecewiseConstantFunction.mkPCF T val_u hdisj hcover).integral ≤ R + 2*ε ∧ R - 2*ε ≤ (PiecewiseConstantFunction.mkPCF T val_l hdisj hcover).integral := by
  classical
  obtain ⟨M, hM⟩ := hbound
  obtain ⟨δ, hδ_pos, hδ⟩ := hεδ ε hε
  have hdata : ∃ (N : ℕ), 0 < N ∧ ∃ P : TaggedPartition I N, P.norm ≤ δ := by
    obtain ⟨N, hN⟩ := exists_nat_gt ((I.b - I.a) / δ)
    have hN_pos : 0 < N := by
      have hpos : 0 < (I.b - I.a) / δ := div_pos (sub_pos.mpr hab) hδ_pos
      exact Nat.pos_of_ne_zero (fun hz => by rw [hz] at hN; simp at hN; linarith)
    refine ⟨N, hN_pos, ?_⟩
    refine ⟨TaggedPartition.uniform I N hN_pos hI hab, ?_⟩
    rw [TaggedPartition.uniform_norm I N hN_pos hI hab]
    have hlt : (I.b - I.a) / (N : ℝ) < δ := by
      calc (I.b - I.a) / (N : ℝ) < (I.b - I.a) / ((I.b - I.a) / δ) := by
            apply div_lt_div_of_pos_left (sub_pos.mpr hab) (div_pos (sub_pos.mpr hab) hδ_pos) hN
        _ = δ := by field_simp [ne_of_gt (sub_pos.mpr hab)]
    exact le_of_lt hlt
  rcases hdata with ⟨N, hN_pos, P, hP_norm⟩
  let T : Finset BoundedInterval :=
    Finset.image (fun i : Fin N => Ico (P.x i.castSucc) (P.x i.succ)) Finset.univ ∪ ({Icc I.b I.b} : Finset BoundedInterval)
  have hdisj : (T : Set BoundedInterval).PairwiseDisjoint BoundedInterval.toSet := by
    simpa [T] using (uniform_pieces_disjoint_134 P)
  have hcover : I.toSet = ⋃ J ∈ T, J.toSet := by
    simpa [T] using (uniform_pieces_cover_134 P hI)
  let val_u : BoundedInterval → ℝ := fun J => sSup {f y | y ∈ (J : Set ℝ)}
  let val_l : BoundedInterval → ℝ := fun J => sInf {f y | y ∈ (J : Set ℝ)}
  let u : PiecewiseConstantFunction I := PiecewiseConstantFunction.mkPCF T val_u hdisj hcover
  let l : PiecewiseConstantFunction I := PiecewiseConstantFunction.mkPCF T val_l hdisj hcover
  have hlen_pos : 0 < |I|ₗ := by
    unfold BoundedInterval.length
    rw [max_eq_left (le_of_lt (sub_pos.mpr hab))]
    exact sub_pos.mpr hab
  have hlen : |I|ₗ = I.b - I.a := by
    unfold BoundedInterval.length
    exact max_eq_left (le_of_lt (sub_pos.mpr hab))
  let κ : ℝ := ε / (2 * (N : ℝ) * |I|ₗ)
  have hκ_pos : 0 < κ := by
    dsimp [κ]
    positivity
  have hκ_len : κ * |I|ₗ = ε / (2 * (N : ℝ)) := by
    dsimp [κ]
    field_simp [ne_of_gt hlen_pos, (by norm_num : (2 : ℝ) ≠ 0), (by exact_mod_cast (ne_of_gt hN_pos) : (N : ℝ) ≠ 0)]
  have hε_2N : ε / (2 * (N : ℝ)) ≤ ε / 2 := by
    rw [div_le_div_iff₀ (mul_pos (by norm_num) (Nat.cast_pos.mpr hN_pos)) (by norm_num : (0 : ℝ) < 2)]
    nlinarith [show (1 : ℝ) ≤ N by exact_mod_cast Nat.succ_le_iff.mpr hN_pos]
  have hlen_2N : κ * |I|ₗ ≤ ε / 2 := by linarith
  have h_u_lb : ∀ x ∈ I.toSet, f x ≤ u.f x := by
    intro x hx
    have hx_mem : ∃ J' ∈ T, x ∈ (J' : Set ℝ) := by
      rw [hcover] at hx
      simpa using hx
    have hx_choose : x ∈ ((Classical.choose hx_mem : BoundedInterval) : Set ℝ) := (Classical.choose_spec hx_mem).2
    have hbdd : BddAbove {f y | y ∈ ((Classical.choose hx_mem : BoundedInterval) : Set ℝ)} := by
      refine ⟨M, ?_⟩
      intro z hz
      rcases hz with ⟨y, hy, rfl⟩
      have hyI : y ∈ I.toSet := by
        rw [hcover]
        exact Set.mem_iUnion₂.mpr ⟨Classical.choose hx_mem, (Classical.choose_spec hx_mem).1, hy⟩
      exact (abs_le.mp (hM y hyI)).2
    have hf_le : f x ≤ sSup {f y | y ∈ ((Classical.choose hx_mem : BoundedInterval) : Set ℝ)} :=
      le_csSup hbdd ⟨x, hx_choose, rfl⟩
    simpa [u, PiecewiseConstantFunction.mkPCF, hx_mem, val_u] using hf_le
  have h_l_lb : ∀ x ∈ I.toSet, l.f x ≤ f x := by
    intro x hx
    have hx_mem : ∃ J' ∈ T, x ∈ (J' : Set ℝ) := by
      rw [hcover] at hx
      simpa using hx
    have hx_choose : x ∈ ((Classical.choose hx_mem : BoundedInterval) : Set ℝ) := (Classical.choose_spec hx_mem).2
    have hbdd : BddBelow {f y | y ∈ ((Classical.choose hx_mem : BoundedInterval) : Set ℝ)} := by
      refine ⟨-M, ?_⟩
      intro z hz
      rcases hz with ⟨y, hy, rfl⟩
      have hyI : y ∈ I.toSet := by
        rw [hcover]
        exact Set.mem_iUnion₂.mpr ⟨Classical.choose hx_mem, (Classical.choose_spec hx_mem).1, hy⟩
      exact (abs_le.mp (hM y hyI)).1
    have hinf_le : sInf {f y | y ∈ ((Classical.choose hx_mem : BoundedInterval) : Set ℝ)} ≤ f x :=
      csInf_le hbdd ⟨x, hx_choose, rfl⟩
    simpa [l, PiecewiseConstantFunction.mkPCF, hx_mem, val_l] using hinf_le
  have h_u_out : ∀ x ∉ I.toSet, u.f x = 0 := by
    intro x hx
    have hnot : ¬ ∃ J' ∈ T, x ∈ (J' : Set ℝ) := by
      intro h
      rcases h with ⟨J', hJ', hx'⟩
      exact hx (by rw [hcover]; exact Set.mem_iUnion₂.mpr ⟨J', hJ', hx'⟩)
    simp [u, PiecewiseConstantFunction.mkPCF, hnot]
  have h_l_out : ∀ x ∉ I.toSet, l.f x = 0 := by
    intro x hx
    have hnot : ¬ ∃ J' ∈ T, x ∈ (J' : Set ℝ) := by
      intro h
      rcases h with ⟨J', hJ', hx'⟩
      exact hx (by rw [hcover]; exact Set.mem_iUnion₂.mpr ⟨J', hJ', hx'⟩)
    simp [l, PiecewiseConstantFunction.mkPCF, hnot]
  have hdelta_len (i : Fin N) : |Ico (P.x i.castSucc) (P.x i.succ)|ₗ = P.delta i := by
    change max (P.x i.succ - P.x i.castSucc) 0 = P.x i.succ - P.x i.castSucc
    rw [max_eq_left (sub_nonneg.mpr (le_of_lt (P.x_mono Fin.castSucc_lt_succ)))]
  have hsing_len : |Icc I.b I.b|ₗ = 0 := by
    simp [BoundedInterval.length]
  have htags_u : ∀ i : Fin N, ∃ t : ℝ, t ∈ (Ico (P.x i.castSucc) (P.x i.succ) : Set ℝ) ∧
      val_u (Ico (P.x i.castSucc) (P.x i.succ)) - κ < f t := by
    intro i
    let S := {f y | y ∈ (Ico (P.x i.castSucc) (P.x i.succ) : Set ℝ)}
    have hnonempty : S.Nonempty :=
      ⟨f (P.x i.castSucc), P.x i.castSucc, by
        simp [Set.mem_Ico, P.x_mono Fin.castSucc_lt_succ], rfl⟩
    have hbdd : BddAbove S := by
      refine ⟨M, ?_⟩
      intro z hz
      rcases hz with ⟨y, hy, rfl⟩
      have hyI : y ∈ I.toSet := by
        rw [hcover]
        exact Set.mem_iUnion₂.mpr ⟨Ico (P.x i.castSucc) (P.x i.succ), by
          dsimp [T]
          exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩), hy⟩
      exact (abs_le.mp (hM y hyI)).2
    have hlt : val_u (Ico (P.x i.castSucc) (P.x i.succ)) - κ < sSup S := by
      dsimp [val_u, S]
      linarith
    rcases exists_lt_of_lt_csSup hnonempty hlt with ⟨y, hy, hlt'⟩
    rcases hy with ⟨t, ht, rfl⟩
    exact ⟨t, ht, hlt'⟩
  have htags_l : ∀ i : Fin N, ∃ t : ℝ, t ∈ (Ico (P.x i.castSucc) (P.x i.succ) : Set ℝ) ∧
      f t < val_l (Ico (P.x i.castSucc) (P.x i.succ)) + κ := by
    intro i
    let S := {f y | y ∈ (Ico (P.x i.castSucc) (P.x i.succ) : Set ℝ)}
    have hnonempty : S.Nonempty :=
      ⟨f (P.x i.castSucc), P.x i.castSucc, by
        simp [Set.mem_Ico, P.x_mono Fin.castSucc_lt_succ], rfl⟩
    have hbdd : BddBelow S := by
      refine ⟨-M, ?_⟩
      intro z hz
      rcases hz with ⟨y, hy, rfl⟩
      have hyI : y ∈ I.toSet := by
        rw [hcover]
        exact Set.mem_iUnion₂.mpr ⟨Ico (P.x i.castSucc) (P.x i.succ), by
          dsimp [T]
          exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩), hy⟩
      exact (abs_le.mp (hM y hyI)).1
    have hlt : sInf S < val_l (Ico (P.x i.castSucc) (P.x i.succ)) + κ := by
      dsimp [val_l, S]
      linarith
    rcases exists_lt_of_csInf_lt hnonempty hlt with ⟨y, hy, hlt'⟩
    rcases hy with ⟨t, ht, rfl⟩
    exact ⟨t, ht, hlt'⟩
  let P' : TaggedPartition I N := {
    x := P.x
    x_tag := fun i => Classical.choose (htags_u i)
    x_start := P.x_start
    x_end := P.x_end
    x_mono := P.x_mono
    x_tag_between := fun i => by
      have h := (Classical.choose_spec (htags_u i)).1
      exact ⟨h.1, le_of_lt h.2⟩
  }
  let P'' : TaggedPartition I N := {
    x := P.x
    x_tag := fun i => Classical.choose (htags_l i)
    x_start := P.x_start
    x_end := P.x_end
    x_mono := P.x_mono
    x_tag_between := fun i => by
      have h := (Classical.choose_spec (htags_l i)).1
      exact ⟨h.1, le_of_lt h.2⟩
  }
  have hP'_norm : P'.norm ≤ δ := by
    have hnorm_eq : P'.norm = P.norm := by
      unfold TaggedPartition.norm P'
      exact congrArg iSup (funext (fun i => rfl))
    rw [hnorm_eq]
    exact hP_norm
  have hP''_norm : P''.norm ≤ δ := by
    have hnorm_eq : P''.norm = P.norm := by
      unfold TaggedPartition.norm P''
      exact congrArg iSup (funext (fun i => rfl))
    rw [hnorm_eq]
    exact hP_norm
  have hRS_u : |P'.RiemannSum f - R| ≤ ε := hδ N P' hP'_norm
  have hRS_l : |P''.RiemannSum f - R| ≤ ε := hδ N P'' hP''_norm
  have hsum_ge : (∑ i : Fin N, (val_u (Ico (P.x i.castSucc) (P.x i.succ)) - κ) * P.delta i) ≤
      P'.RiemannSum f := by
    rw [show P'.RiemannSum f = ∑ i : Fin N, f (P'.x_tag i) * P.delta i from rfl]
    apply Finset.sum_le_sum
    intro i hi
    have ht := (Classical.choose_spec (htags_u i)).2
    have hδnonneg : 0 ≤ P.delta i := le_of_lt (sub_pos.mpr (P.x_mono Fin.castSucc_lt_succ))
    exact mul_le_mul_of_nonneg_right (le_of_lt ht) hδnonneg
  have hsum_le : P''.RiemannSum f ≤ ∑ i : Fin N, (val_l (Ico (P.x i.castSucc) (P.x i.succ)) + κ) * P.delta i := by
    rw [show P''.RiemannSum f = ∑ i : Fin N, f (P''.x_tag i) * P.delta i from rfl]
    apply Finset.sum_le_sum
    intro i hi
    have ht := (Classical.choose_spec (htags_l i)).2
    have hδnonneg : 0 ≤ P.delta i := le_of_lt (sub_pos.mpr (P.x_mono Fin.castSucc_lt_succ))
    exact mul_le_mul_of_nonneg_right (le_of_lt ht) hδnonneg
  have hsum_calc_u : (∑ i : Fin N, (val_u (Ico (P.x i.castSucc) (P.x i.succ)) - κ) * P.delta i) =
      (∑ i : Fin N, val_u (Ico (P.x i.castSucc) (P.x i.succ)) * P.delta i) - κ * |I|ₗ := by
    simp only [sub_mul]
    rw [Finset.sum_sub_distrib]
    have hκ_sum : (∑ i : Fin N, κ * P.delta i) = κ * |I|ₗ := by
      rw [← Finset.mul_sum]
      rw [TaggedPartition.sum_delta_eq]
      rw [hlen]
    rw [hκ_sum]
  have hsum_calc_l : (∑ i : Fin N, (val_l (Ico (P.x i.castSucc) (P.x i.succ)) + κ) * P.delta i) =
      (∑ i : Fin N, val_l (Ico (P.x i.castSucc) (P.x i.succ)) * P.delta i) + κ * |I|ₗ := by
    simp only [add_mul]
    rw [Finset.sum_add_distrib]
    have hκ_sum : (∑ i : Fin N, κ * P.delta i) = κ * |I|ₗ := by
      rw [← Finset.mul_sum]
      rw [TaggedPartition.sum_delta_eq]
      rw [hlen]
    rw [hκ_sum]
  have hu_int_eq : u.integral = ∑ i : Fin N, val_u (Ico (P.x i.castSucc) (P.x i.succ)) * P.delta i := by
    rw [show u.integral = ∑ J ∈ T, val_u J * |J|ₗ from PiecewiseConstantFunction.mkPCF_integral T val_u hdisj hcover]
    have hT_eq : T = Finset.image (fun i : Fin N => Ico (P.x i.castSucc) (P.x i.succ)) Finset.univ ∪ ({Icc I.b I.b} : Finset BoundedInterval) := by
      rfl
    rw [hT_eq]
    have hsum_image : (∑ J ∈ Finset.image (fun i : Fin N => Ico (P.x i.castSucc) (P.x i.succ)) Finset.univ, val_u J * |J|ₗ)
        = ∑ i : Fin N, val_u (Ico (P.x i.castSucc) (P.x i.succ)) * P.delta i := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [hdelta_len i]
      · exact (uniform_piece_inj_134 P).injOn
    have hsing_sum : (∑ J ∈ ({Icc I.b I.b} : Finset BoundedInterval), val_u J * |J|ₗ) = 0 := by
      simp
    rw [Finset.sum_union]
    · rw [hsum_image, hsing_sum]
      simp
    · rw [Finset.disjoint_left]
      intro J hJ
      rcases Finset.mem_image.mp hJ with ⟨i, _, rfl⟩
      simp
  have hl_int_eq : l.integral = ∑ i : Fin N, val_l (Ico (P.x i.castSucc) (P.x i.succ)) * P.delta i := by
    rw [show l.integral = ∑ J ∈ T, val_l J * |J|ₗ from PiecewiseConstantFunction.mkPCF_integral T val_l hdisj hcover]
    have hT_eq : T = Finset.image (fun i : Fin N => Ico (P.x i.castSucc) (P.x i.succ)) Finset.univ ∪ ({Icc I.b I.b} : Finset BoundedInterval) := by
      rfl
    rw [hT_eq]
    have hsum_image : (∑ J ∈ Finset.image (fun i : Fin N => Ico (P.x i.castSucc) (P.x i.succ)) Finset.univ, val_l J * |J|ₗ)
        = ∑ i : Fin N, val_l (Ico (P.x i.castSucc) (P.x i.succ)) * P.delta i := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [hdelta_len i]
      · exact (uniform_piece_inj_134 P).injOn
    have hsing_sum : (∑ J ∈ ({Icc I.b I.b} : Finset BoundedInterval), val_l J * |J|ₗ) = 0 := by
      simp
    rw [Finset.sum_union]
    · rw [hsum_image, hsing_sum]
      simp
    · rw [Finset.disjoint_left]
      intro J hJ
      rcases Finset.mem_image.mp hJ with ⟨i, _, rfl⟩
      simp
  have hu_int : u.integral ≤ R + 2 * ε := by
    have hle1 : u.integral ≤ (∑ i : Fin N, (val_u (Ico (P.x i.castSucc) (P.x i.succ)) - κ) * P.delta i) + κ * |I|ₗ := by
      rw [hu_int_eq, hsum_calc_u]
      linarith
    have habs := abs_le.mp hRS_u
    calc
      u.integral ≤ (∑ i : Fin N, (val_u (Ico (P.x i.castSucc) (P.x i.succ)) - κ) * P.delta i) + κ * |I|ₗ := hle1
      _ ≤ P'.RiemannSum f + κ * |I|ₗ := by linarith
      _ ≤ R + ε + κ * |I|ₗ := by linarith
      _ ≤ R + ε + ε / 2 := by linarith [hlen_2N]
      _ ≤ R + 2 * ε := by linarith
  have hl_int : R - 2 * ε ≤ l.integral := by
    have hle1 : (∑ i : Fin N, (val_l (Ico (P.x i.castSucc) (P.x i.succ)) + κ) * P.delta i) - κ * |I|ₗ ≤ l.integral := by
      rw [hl_int_eq, hsum_calc_l]
      linarith
    have habs := abs_le.mp hRS_l
    calc
      R - 2 * ε ≤ R - ε - κ * |I|ₗ := by nlinarith [hlen_2N]
      _ ≤ P''.RiemannSum f - κ * |I|ₗ := by linarith
      _ ≤ (∑ i : Fin N, (val_l (Ico (P.x i.castSucc) (P.x i.succ)) + κ) * P.delta i) - κ * |I|ₗ := by linarith
      _ ≤ l.integral := hle1
  refine ⟨T, val_u, val_l, hdisj, hcover, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨by simpa [l] using h_l_lb x hx, by simpa [u] using h_u_lb x hx⟩
  · intro x hx
    exact ⟨by simpa [u] using h_u_out x hx, by simpa [l] using h_l_out x hx⟩
  · exact ⟨by simpa [u] using hu_int, by simpa [l] using hl_int⟩

-- ============================================================
-- Section 2: Riemann sums of piecewise constant functions are close to
-- their integral for fine partitions (the "boundary" lemma)
-- ============================================================


/-- The tag of a partition lies inside the interval. -/
lemma tag_mem_I {I : BoundedInterval} (hI : I = Icc I.a I.b) {n : ℕ} (P : TaggedPartition I n) (i : Fin n) :
    P.x_tag i ∈ I.toSet := by
  have hbtw := P.x_tag_between i
  have hmono1 : P.x 0 ≤ P.x i.castSucc := P.x_mono.monotone (Fin.zero_le _)
  have hlo : I.a ≤ P.x_tag i := by
    rw [← P.x_start]
    exact le_trans hmono1 hbtw.1
  have hmono2 : P.x i.succ ≤ P.x (Fin.last n) := P.x_mono.monotone (Fin.le_last _)
  have hhi : P.x_tag i ≤ I.b := by
    rw [← P.x_end]
    exact le_trans hbtw.2 hmono2
  have hmem : P.x_tag i ∈ (BoundedInterval.Icc I.a I.b : Set ℝ) := ⟨hlo, hhi⟩
  have hI' : I.toSet = (BoundedInterval.Icc I.a I.b : Set ℝ) := by
    rw [hI]
  rwa [hI']

/-- Every bounded interval is measurable. -/
lemma interval_measurable (J : BoundedInterval) : MeasurableSet (J : Set ℝ) := by
  cases J with
  | Ioo a b => simp
  | Icc a b => simp
  | Ioc a b => simp
  | Ico a b => simp

/-- The volume (as a real) of the i-th subinterval equals its length delta. -/
lemma subinterval_vol {I : BoundedInterval} {n : ℕ} (P : TaggedPartition I n) (i : Fin n) :
    MeasureTheory.volume.real (Set.Ico (P.x i.castSucc) (P.x i.succ)) = P.delta i := by
  have hdelta0 : 0 ≤ P.x i.succ - P.x i.castSucc :=
    sub_nonneg.mpr (le_of_lt (P.x_mono Fin.castSucc_lt_succ))
  rw [MeasureTheory.Measure.real_def, Real.volume_Ico, ENNReal.toReal_ofReal hdelta0,
    TaggedPartition.delta]

/-- The volume of the subinterval is finite. -/
lemma subinterval_vol_ne_top {I : BoundedInterval} {n : ℕ} (P : TaggedPartition I n) (i : Fin n) :
    MeasureTheory.volume (Set.Ico (P.x i.castSucc) (P.x i.succ)) ≠ ⊤ := by
  rw [Real.volume_Ico]
  exact ENNReal.ofReal_ne_top


/-- The half-open subintervals of a partition telescope. -/
lemma iUnion_Ico_partition {n : ℕ} (x : Fin (n+1) → ℝ) (hx : StrictMono x) :
    (⋃ i : Fin n, Set.Ico (x i.castSucc) (x i.succ)) = Set.Ico (x 0) (x (Fin.last n)) := by
  ext y
  constructor
  · intro hy
    rw [Set.mem_iUnion] at hy
    rcases hy with ⟨i, hi⟩
    have hmono0 : x 0 ≤ x i.castSucc := hx.monotone (Fin.zero_le _)
    have hmonol : x i.succ ≤ x (Fin.last n) := hx.monotone (Fin.le_last _)
    exact ⟨le_trans hmono0 hi.1, lt_of_lt_of_le hi.2 hmonol⟩
  · intro hy
    rw [Set.mem_Ico] at hy
    by_cases h_last : y = x (Fin.last n)
    · exfalso
      exact not_lt_of_ge (le_of_eq h_last.symm) hy.2
    · have hyl : y < x (Fin.last n) := hy.2
      have h_exists : (Finset.filter (fun k : Fin (n+1) => y < x k) Finset.univ).Nonempty := by
        refine ⟨Fin.last n, ?_⟩
        simp
        exact hyl
      let k := Finset.min' (Finset.filter (fun k : Fin (n+1) => y < x k) Finset.univ) h_exists
      have hk_mem : k ∈ Finset.filter (fun k : Fin (n+1) => y < x k) Finset.univ :=
        Finset.min'_mem _ h_exists
      have hy_lt : y < x k := (Finset.mem_filter.mp hk_mem).2
      have hk0 : k ≠ (0 : Fin (n+1)) := by
        intro hk0
        rw [hk0] at hy_lt
        linarith [hy.1]
      have hi_pred : ∃ (i : Fin n), i.succ = k := by
        refine ⟨Fin.pred k hk0, ?_⟩
        simp
      rcases hi_pred with ⟨i, hi⟩
      have hx_lt_Pi_succ : y < x i.succ := by
        rw [hi]
        exact hy_lt
      have hx_ge : x i.castSucc ≤ y := by
        by_contra! hlt
        have hmem : (i.castSucc : Fin (n+1)) ∈ Finset.filter (fun k' : Fin (n+1) => y < x k') Finset.univ := by
          simp
          exact hlt
        have hk_le : k ≤ (i.castSucc : Fin (n+1)) := Finset.min'_le _ _ hmem
        have h_val : k.val = i.val + 1 := by
          have hvi : i.succ.val = i.val + 1 := by simp
          have hkv : k.val = i.succ.val := by simp [hi]
          rw [hvi] at hkv
          exact hkv
        have h_cast : (i.castSucc : Fin (n+1)).val = i.val := by simp
        omega
      rw [Set.mem_iUnion]
      exact ⟨i, hx_ge, hx_lt_Pi_succ⟩


/-- A point belongs to at most two subintervals of a partition. -/
lemma partition_point_count_le_two {n : ℕ} (x : Fin (n+1) → ℝ) (hx : StrictMono x) (b : ℝ) :
    ((Finset.univ : Finset (Fin n)).filter (fun i => x i.castSucc ≤ b ∧ b ≤ x i.succ)).card ≤ 2 := by
  classical
  let S : Finset (Fin n) := (Finset.univ : Finset (Fin n)).filter (fun i => x i.castSucc ≤ b ∧ b ≤ x i.succ)
  change S.card ≤ 2
  by_cases hS : S.Nonempty
  · let m : ℕ := (S.min' hS).val
    have hmin : S.min' hS ∈ S := Finset.min'_mem S hS
    have hmle : ∀ i ∈ S, m ≤ i.val := by
      intro i hi
      dsimp [m]
      exact (Finset.min'_le S i hi)
    have hclose : ∀ i ∈ S, i.val ≤ m + 1 := by
      intro i hi
      by_contra! hgt
      have hlt : (S.min' hS).succ < i.castSucc := by
        rw [Fin.lt_def]
        simp
        omega
      have hmono : x (S.min' hS).succ < x i.castSucc := hx hlt
      have hb1 : b ≤ x (S.min' hS).succ := (Finset.mem_filter.mp hmin).2.2
      have hb2 : x i.castSucc ≤ b := (Finset.mem_filter.mp hi).2.1
      linarith
    have hsub : S ⊆ (Finset.univ : Finset (Fin n)).filter (fun i => i.val = m ∨ i.val = m + 1) := by
      intro i hi
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ i, by
        have hle1 : m ≤ i.val := hmle i hi
        have hle2 : i.val ≤ m + 1 := hclose i hi
        rcases eq_or_lt_of_le hle1 with (heq | hlt)
        · exact Or.inl heq.symm
        · right
          omega⟩
    have hcard1 : ((Finset.univ : Finset (Fin n)).filter (fun i => i.val = m)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      apply Fin.ext
      exact (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm
    have hcard2 : ((Finset.univ : Finset (Fin n)).filter (fun i => i.val = m + 1)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      apply Fin.ext
      exact (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm
    have hsplit : ((Finset.univ : Finset (Fin n)).filter (fun i => i.val = m ∨ i.val = m + 1)) =
        ((Finset.univ : Finset (Fin n)).filter (fun i => i.val = m)) ∪
        ((Finset.univ : Finset (Fin n)).filter (fun i => i.val = m + 1)) := by
      ext i
      simp [Finset.mem_filter, Finset.mem_union]
    have htotal : ((Finset.univ : Finset (Fin n)).filter (fun i => i.val = m ∨ i.val = m + 1)).card ≤ 2 := by
      rw [hsplit]
      exact le_trans (Finset.card_union_le _ _) (by omega)
    exact le_trans (Finset.card_le_card hsub) htotal
  · have hcard : S.card = 0 := by
      apply Finset.card_eq_zero.mpr
      by_contra hne
      exact hS (Finset.nonempty_iff_ne_empty.mpr hne)
    rw [hcard]
    norm_num

/-- The subintervals of a partition are pairwise disjoint. -/
lemma partition_subintervals_disjoint {n : ℕ} (x : Fin (n+1) → ℝ) (hx : StrictMono x) :
    ((Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint
      (fun i : Fin n => Set.Ico (x i.castSucc) (x i.succ)) := by
  intro i hi j hj hne
  apply Set.disjoint_left.mpr
  intro y hy
  rcases hy with ⟨hyi1, hyi2⟩
  intro hyj
  rcases hyj with ⟨hyj1, hyj2⟩
  have hij : i = j := by
    apply Fin.ext
    by_contra hne2
    have hlt : i.val < j.val ∨ j.val < i.val := lt_or_gt_of_ne hne2
    rcases hlt with (hlt | hlt)
    · have hmono : x i.succ ≤ x j.castSucc := hx.monotone (by
        rw [Fin.le_iff_val_le_val]
        simp
        omega)
      linarith [hyi2, hmono, hyj1]
    · have hmono : x j.succ ≤ x i.castSucc := hx.monotone (by
        rw [Fin.le_iff_val_le_val]
        simp
        omega)
      linarith [hyj2, hmono, hyi1]
  exact hne hij


/-- If a point t lies in an interval J and y does not, then one of the endpoints
    of J separates them; both points lie in the interval implies the endpoint does too. -/
lemma interval_crossing_endpoint {J : BoundedInterval} {a b t y : ℝ}
    (ht : t ∈ (J : Set ℝ)) (hy : y ∉ (J : Set ℝ))
    (hat : a ≤ t) (htb : t ≤ b) (hay : a ≤ y) (hyb : y ≤ b) :
    (a ≤ J.a ∧ J.a ≤ b) ∨ (a ≤ J.b ∧ J.b ≤ b) := by
  cases J with
  | Ioo α β =>
      simp only [BoundedInterval.set_Ioo, Set.mem_Ioo] at ht hy
      have hy' : y ≤ α ∨ β ≤ y := by
        by_contra h
        push_neg at h
        exact hy ⟨h.1, h.2⟩
      rcases hy' with (hyα | hβy)
      · left
        have h1 : a ≤ α := le_trans hay hyα
        have h2 : α ≤ b := le_trans (le_of_lt ht.1) htb
        exact ⟨h1, h2⟩
      · right
        have h1 : a ≤ β := le_trans hat (le_of_lt ht.2)
        have h2 : β ≤ b := le_trans hβy hyb
        exact ⟨h1, h2⟩
  | Icc α β =>
      simp only [BoundedInterval.set_Icc, Set.mem_Icc] at ht hy
      have hy' : y < α ∨ β < y := by
        by_contra h
        push_neg at h
        exact hy ⟨h.1, h.2⟩
      rcases hy' with (hyα | hβy)
      · left
        have h1 : a ≤ α := le_trans hay (le_of_lt hyα)
        have h2 : α ≤ b := le_trans ht.1 htb
        exact ⟨h1, h2⟩
      · right
        have h1 : a ≤ β := le_trans hat ht.2
        have h2 : β ≤ b := le_trans (le_of_lt hβy) hyb
        exact ⟨h1, h2⟩
  | Ioc α β =>
      simp only [BoundedInterval.set_Ioc, Set.mem_Ioc] at ht hy
      have hy' : y ≤ α ∨ β < y := by
        by_contra h
        push_neg at h
        exact hy ⟨h.1, h.2⟩
      rcases hy' with (hyα | hβy)
      · left
        have h1 : a ≤ α := le_trans hay hyα
        have h2 : α ≤ b := le_trans (le_of_lt ht.1) htb
        exact ⟨h1, h2⟩
      · right
        have h1 : a ≤ β := le_trans hat ht.2
        have h2 : β ≤ b := le_trans (le_of_lt hβy) hyb
        exact ⟨h1, h2⟩
  | Ico α β =>
      simp only [BoundedInterval.set_Ico, Set.mem_Ico] at ht hy
      have hy' : y < α ∨ β ≤ y := by
        by_contra h
        push_neg at h
        exact hy ⟨h.1, h.2⟩
      rcases hy' with (hyα | hβy)
      · left
        have h1 : a ≤ α := le_trans hay (le_of_lt hyα)
        have h2 : α ≤ b := le_trans ht.1 htb
        exact ⟨h1, h2⟩
      · right
        have h1 : a ≤ β := le_trans hat (le_of_lt ht.2)
        have h2 : β ≤ b := le_trans hβy hyb
        exact ⟨h1, h2⟩


private lemma cell_of_exists {I : BoundedInterval} (g : PiecewiseConstantFunction I) (x : ℝ)
    (hx : x ∈ I.toSet) : ∃ J : g.T, x ∈ (J : BoundedInterval) := by
  have h : x ∈ ⋃ J ∈ g.T, (J : Set ℝ) := by
    rw [← g.cover]
    exact hx
  rcases Set.mem_iUnion₂.mp h with ⟨J, hJ, hxJ⟩
  exact ⟨⟨J, hJ⟩, hxJ⟩

/-- The cell of a piecewise constant function containing a given point of I. -/
noncomputable def cell_of {I : BoundedInterval} (g : PiecewiseConstantFunction I) (x : ℝ)
    (hx : x ∈ I.toSet) : g.T :=
  Classical.choose (cell_of_exists g x hx)

/-- The point lies in its cell. -/
lemma cell_of_mem {I : BoundedInterval} (g : PiecewiseConstantFunction I) (x : ℝ) (hx : x ∈ I.toSet) :
    x ∈ (cell_of g x hx : BoundedInterval) :=
  Classical.choose_spec (cell_of_exists g x hx)


/-- The measure of a cell equals the sum of its intersections with the subintervals. -/
lemma cells_inter_subintervals_measure {I : BoundedInterval} {n : ℕ}
    (hI : I = Icc I.a I.b) (g : PiecewiseConstantFunction I) (P : TaggedPartition I n)
    (J : BoundedInterval) (hJ : J ∈ g.T) :
    MeasureTheory.volume.real (J : Set ℝ) =
      ∑ i : Fin n, MeasureTheory.volume.real ((J : Set ℝ) ∩ Set.Ico (P.x i.castSucc) (P.x i.succ)) := by
  classical
  let f : Fin n → Set ℝ := fun i => (J : Set ℝ) ∩ Set.Ico (P.x i.castSucc) (P.x i.succ)
  have hd0 : ((Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint
      (fun i : Fin n => Set.Ico (P.x i.castSucc) (P.x i.succ)) :=
    partition_subintervals_disjoint P.x P.x_mono
  have hd : ((Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint f := by
    exact Set.PairwiseDisjoint.mono hd0 (fun i => Set.inter_subset_right)
  have hm : ∀ b ∈ (Finset.univ : Finset (Fin n)), MeasurableSet (f b) := by
    intro b hb
    exact (interval_measurable J).inter (measurableSet_Ico : MeasurableSet (Set.Ico (P.x b.castSucc) (P.x b.succ)))
  have hfin : ∀ b ∈ (Finset.univ : Finset (Fin n)), MeasureTheory.volume (f b) ≠ ⊤ := by
    intro b hb
    exact ne_top_of_le_ne_top (subinterval_vol_ne_top P b)
      (MeasureTheory.measure_mono (Set.inter_subset_right))
  have hunion : (⋃ i : Fin n, f i) = (J : Set ℝ) \ ({I.b} : Set ℝ) := by
    ext y
    constructor
    · intro hy
      rw [Set.mem_iUnion] at hy
      rcases hy with ⟨i, hyi⟩
      rcases hyi with ⟨hyJ, hyP⟩
      have hyP' : y ∈ Set.Ico (P.x 0) (P.x (Fin.last n)) := by
        rw [← iUnion_Ico_partition P.x P.x_mono]
        exact Set.mem_iUnion.mpr ⟨i, hyP⟩
      have hyne : y ≠ I.b := by
        rw [P.x_start, P.x_end] at hyP'
        intro h
        rw [h] at hyP'
        exact (lt_irrefl _) hyP'.2
      exact ⟨hyJ, hyne⟩
    · intro hy
      rcases hy with ⟨hyJ, hyne⟩
      have hJsub : (J : Set ℝ) ⊆ Set.Icc I.a I.b := by
        intro z hz
        have hzI : z ∈ I.toSet := by
          rw [g.cover]
          exact Set.mem_iUnion₂.mpr ⟨J, hJ, hz⟩
        rwa [hI] at hzI
      have hycc := hJsub hyJ
      have hyI : y ∈ Set.Ico I.a I.b := ⟨hycc.1, lt_of_le_of_ne hycc.2 hyne⟩
      have hyP : y ∈ ⋃ i : Fin n, Set.Ico (P.x i.castSucc) (P.x i.succ) := by
        rw [iUnion_Ico_partition P.x P.x_mono, P.x_start, P.x_end]
        exact hyI
      rw [Set.mem_iUnion] at hyP
      rcases hyP with ⟨i, hyPi⟩
      exact Set.mem_iUnion.mpr ⟨i, ⟨hyJ, hyPi⟩⟩
  have hvol : MeasureTheory.volume.real (J : Set ℝ) =
      MeasureTheory.volume.real ((J : Set ℝ) \ ({I.b} : Set ℝ)) := by
    rw [MeasureTheory.Measure.real_def, MeasureTheory.Measure.real_def]
    congr 1
    have hpart : MeasureTheory.volume ((J : Set ℝ) ∩ ({I.b} : Set ℝ)) +
        MeasureTheory.volume ((J : Set ℝ) \ ({I.b} : Set ℝ)) = MeasureTheory.volume (J : Set ℝ) := by
      simpa using (MeasureTheory.measure_inter_add_diff (μ := MeasureTheory.volume)
        (J : Set ℝ) (measurableSet_singleton I.b))
    have hsing : MeasureTheory.volume ((J : Set ℝ) ∩ ({I.b} : Set ℝ)) = 0 := by
      exact MeasureTheory.measure_mono_null (Set.inter_subset_right) (Real.volume_singleton (a := I.b))
    calc
      MeasureTheory.volume (J : Set ℝ) = MeasureTheory.volume ((J : Set ℝ) ∩ ({I.b} : Set ℝ)) +
          MeasureTheory.volume ((J : Set ℝ) \ ({I.b} : Set ℝ)) := hpart.symm
      _ = MeasureTheory.volume ((J : Set ℝ) \ ({I.b} : Set ℝ)) := by rw [hsing, zero_add]
  have hsum : MeasureTheory.volume.real (⋃ i ∈ (Finset.univ : Finset (Fin n)), f i) =
      (∑ i ∈ (Finset.univ : Finset (Fin n)), MeasureTheory.volume.real (f i)) := by
    exact MeasureTheory.measureReal_biUnion_finset hd hm hfin
  calc
    MeasureTheory.volume.real (J : Set ℝ) = MeasureTheory.volume.real ((J : Set ℝ) \ ({I.b} : Set ℝ)) := hvol
    _ = MeasureTheory.volume.real (⋃ i : Fin n, f i) := by rw [hunion]
    _ = MeasureTheory.volume.real (⋃ i ∈ (Finset.univ : Finset (Fin n)), f i) := by simp
    _ = ∑ i ∈ (Finset.univ : Finset (Fin n)), MeasureTheory.volume.real (f i) := hsum
    _ = ∑ i : Fin n, MeasureTheory.volume.real (f i) := by simp
    _ = ∑ i : Fin n, MeasureTheory.volume.real ((J : Set ℝ) ∩ Set.Ico (P.x i.castSucc) (P.x i.succ)) := by
      simp [f]

/-- The measure of a subinterval equals the sum of its intersections with the cells. -/
lemma subinterval_inter_cells_measure {I : BoundedInterval} {n : ℕ}
    (hI : I = Icc I.a I.b) (g : PiecewiseConstantFunction I) (P : TaggedPartition I n) (i : Fin n) :
    MeasureTheory.volume.real (Set.Ico (P.x i.castSucc) (P.x i.succ)) =
      ∑ J ∈ g.T, MeasureTheory.volume.real (Set.Ico (P.x i.castSucc) (P.x i.succ) ∩ (J : Set ℝ)) := by
  classical
  let f : BoundedInterval → Set ℝ := fun J => Set.Ico (P.x i.castSucc) (P.x i.succ) ∩ (J : Set ℝ)
  have hd : ((g.T : Finset BoundedInterval) : Set BoundedInterval).PairwiseDisjoint f := by
    exact Set.PairwiseDisjoint.mono g.disjoint (fun J => Set.inter_subset_right)
  have hm : ∀ b ∈ g.T, MeasurableSet (f b) := by
    intro b hb
    exact (measurableSet_Ico : MeasurableSet (Set.Ico (P.x i.castSucc) (P.x i.succ))).inter (interval_measurable b)
  have hfin : ∀ b ∈ g.T, MeasureTheory.volume (f b) ≠ ⊤ := by
    intro b hb
    exact ne_top_of_le_ne_top (subinterval_vol_ne_top P i)
      (MeasureTheory.measure_mono (Set.inter_subset_left))
  have hunion : (⋃ J ∈ g.T, f J) = Set.Ico (P.x i.castSucc) (P.x i.succ) := by
    ext y
    constructor
    · intro hy
      rcases Set.mem_iUnion₂.mp hy with ⟨J, hJ, hyJ⟩
      exact hyJ.1
    · intro hy
      have hyI : y ∈ I.toSet := by
        have hlo : I.a ≤ y := by
          rw [← P.x_start]
          exact le_trans (P.x_mono.monotone (Fin.zero_le _)) hy.1
        have hhi : y ≤ I.b := by
          rw [← P.x_end]
          exact le_trans (le_of_lt hy.2) (P.x_mono.monotone (Fin.le_last _))
        rw [hI]
        exact ⟨hlo, hhi⟩
      have hycover : y ∈ ⋃ K ∈ g.T, (K : Set ℝ) := by
        rw [g.cover] at hyI
        exact hyI
      rcases Set.mem_iUnion₂.mp hycover with ⟨J, hJ, hyJ⟩
      exact Set.mem_iUnion₂.mpr ⟨J, hJ, ⟨hy, hyJ⟩⟩
  calc
    MeasureTheory.volume.real (Set.Ico (P.x i.castSucc) (P.x i.succ))
        = MeasureTheory.volume.real (⋃ J ∈ g.T, f J) := by rw [hunion]
    _ = ∑ J ∈ g.T, MeasureTheory.volume.real (f J) := by
        rw [MeasureTheory.measureReal_biUnion_finset hd hm hfin]
    _ = ∑ J ∈ g.T, MeasureTheory.volume.real (Set.Ico (P.x i.castSucc) (P.x i.succ) ∩ (J : Set ℝ)) := by
      simp [f]


/-- Convert a sum over the subtype g.T to a sum over the finset g.T. -/
lemma pcf_sum_conv {I : BoundedInterval} (g : PiecewiseConstantFunction I) (F : g.T → ℝ) :
    (∑ J : g.T, F J) = ∑ J ∈ g.T, (if hJ : J ∈ g.T then F ⟨J, hJ⟩ else 0) := by
  calc
    (∑ J : g.T, F J) = ∑ x ∈ g.T.attach, F x := by simp
    _ = ∑ x ∈ g.T.attach, (if h : (x : BoundedInterval) ∈ g.T then F ⟨(x : BoundedInterval), h⟩ else 0) := by
            apply Finset.sum_congr rfl
            intro x hx
            have hxmem : (x : BoundedInterval) ∈ g.T := x.property
            have hsub : (⟨(x : BoundedInterval), hxmem⟩ : g.T) = x := by
              apply Subtype.ext
              rfl
            simp [hxmem, hsub]
    _ = ∑ J ∈ g.T, (if hJ : J ∈ g.T then F ⟨J, hJ⟩ else 0) := by
            rw [Finset.sum_attach g.T (fun (y : BoundedInterval) => (if h : y ∈ g.T then F ⟨y, h⟩ else 0))]

/-- Stripping the membership guard in a sum over g.T. -/
lemma pcf_sum_conv' {I : BoundedInterval} (g : PiecewiseConstantFunction I) (F : BoundedInterval → ℝ) :
    (∑ J ∈ g.T, (if _hJ : J ∈ g.T then F J else 0)) = ∑ J ∈ g.T, F J := by
  apply Finset.sum_congr rfl
  intro J hJ
  rw [dif_pos hJ]

/-- The Riemann sum of a piecewise-constant function whose cell values are bounded by C over
    a fine partition is close to its integral. -/
lemma pcf_RiemannSum_close {I : BoundedInterval} {n : ℕ} (g : PiecewiseConstantFunction I)
    (hI : I = Icc I.a I.b) (C δ : ℝ) (hC : ∀ J : g.T, |g.c J| ≤ C) (hC0 : 0 ≤ C)
    (hδ0 : 0 ≤ δ) (P : TaggedPartition I n) (hPnorm : P.norm ≤ δ) :
    |P.RiemannSum g.f - g.integral| ≤ 8 * C * (g.T.card : ℝ) * δ := by
  classical
  let e : Finset ℝ := (g.T.image (fun J : BoundedInterval => J.a)) ∪ (g.T.image (fun J : BoundedInterval => J.b))
  have hecard : e.card ≤ 2 * g.T.card := by
    calc
      e.card ≤ (g.T.image (fun J : BoundedInterval => J.a)).card +
          (g.T.image (fun J : BoundedInterval => J.b)).card := Finset.card_union_le _ _
      _ ≤ g.T.card + g.T.card := by
            exact add_le_add Finset.card_image_le Finset.card_image_le
      _ = 2 * g.T.card := by omega
  let Jᵢ : Fin n → g.T := fun i => cell_of g (P.x_tag i) (tag_mem_I hI P i)
  have hPsub : ∀ i : Fin n, P.delta i ≤ δ := by
    intro i
    have hle : P.delta i ≤ P.norm := le_ciSup (Set.Finite.bddAbove (Set.finite_range P.delta)) i
    exact le_trans hle hPnorm
  let Ico_i : Fin n → Set ℝ := fun i => Set.Ico (P.x i.castSucc) (P.x i.succ)
  -- identity A: delta_i = sum over cells of the intersections
  have hA (i : Fin n) : P.delta i = ∑ J : g.T, MeasureTheory.volume.real
      (Ico_i i ∩ ((J : BoundedInterval) : Set ℝ)) := by
    rw [← subinterval_vol P i]
    rw [subinterval_inter_cells_measure hI g P i]
    rw [(pcf_sum_conv' g (fun J : BoundedInterval =>
        MeasureTheory.volume.real (Ico_i i ∩ (J : Set ℝ)))).symm]
    rw [← pcf_sum_conv g (fun J : g.T =>
        MeasureTheory.volume.real (Ico_i i ∩ ((J : BoundedInterval) : Set ℝ)))]
  -- identity B: length of a cell = sum over subintervals of intersections
  have hB (J : g.T) : |(J : BoundedInterval)|ₗ = ∑ i : Fin n, MeasureTheory.volume.real
      (((J : BoundedInterval) : Set ℝ) ∩ Ico_i i) := by
    rw [BoundedInterval.length_eq_volume]
    rw [cells_inter_subintervals_measure hI g P (J : BoundedInterval) J.property]
  -- per-index refinement
  have hpart (i : Fin n) : MeasureTheory.volume.real (Ico_i i ∩ ((Jᵢ i : BoundedInterval) : Set ℝ)) +
      MeasureTheory.volume.real (Ico_i i \ ((Jᵢ i : BoundedInterval) : Set ℝ)) =
      MeasureTheory.volume.real (Ico_i i) := by
    rw [MeasureTheory.Measure.real_def, MeasureTheory.Measure.real_def, MeasureTheory.Measure.real_def]
    have hset : (Ico_i i ∩ ((Jᵢ i : BoundedInterval) : Set ℝ)) ∪
        (Ico_i i \ ((Jᵢ i : BoundedInterval) : Set ℝ)) = Ico_i i := by
      ext y
      constructor
      · intro hy
        rcases hy with (⟨hyA, _⟩ | ⟨hyA, _⟩)
        · exact hyA
        · exact hyA
      · intro hyA
        by_cases hyB : y ∈ ((Jᵢ i : BoundedInterval) : Set ℝ)
        · left
          exact ⟨hyA, hyB⟩
        · right
          exact ⟨hyA, hyB⟩
    have hdisj : Disjoint (Ico_i i ∩ ((Jᵢ i : BoundedInterval) : Set ℝ))
        (Ico_i i \ ((Jᵢ i : BoundedInterval) : Set ℝ)) := by
      rw [Set.disjoint_iff_inter_eq_empty]
      apply Set.not_nonempty_iff_eq_empty.mp
      intro h
      rcases h with ⟨y, hy⟩
      rcases hy with ⟨⟨_, hB1⟩, ⟨_, hnotB⟩⟩
      exact hnotB hB1
    have hmeas1 : MeasurableSet (Ico_i i ∩ ((Jᵢ i : BoundedInterval) : Set ℝ)) :=
      measurableSet_Ico.inter (interval_measurable (Jᵢ i : BoundedInterval))
    have hmeas2 : MeasurableSet (Ico_i i \ ((Jᵢ i : BoundedInterval) : Set ℝ)) :=
      measurableSet_Ico.diff (interval_measurable (Jᵢ i : BoundedInterval))
    have hvol : MeasureTheory.volume (Ico_i i ∩ ((Jᵢ i : BoundedInterval) : Set ℝ)) +
        MeasureTheory.volume (Ico_i i \ ((Jᵢ i : BoundedInterval) : Set ℝ)) =
        MeasureTheory.volume (Ico_i i) := by
      rw [← MeasureTheory.measure_union hdisj hmeas2]
      rw [hset]
    have hne1 : MeasureTheory.volume (Ico_i i ∩ ((Jᵢ i : BoundedInterval) : Set ℝ)) ≠ ⊤ :=
      ne_top_of_le_ne_top (subinterval_vol_ne_top P i) (MeasureTheory.measure_mono (Set.inter_subset_left))
    have hne2 : MeasureTheory.volume (Ico_i i \ ((Jᵢ i : BoundedInterval) : Set ℝ)) ≠ ⊤ :=
      ne_top_of_le_ne_top (subinterval_vol_ne_top P i) (MeasureTheory.measure_mono (Set.diff_subset))
    rw [← ENNReal.toReal_add hne1 hne2]
    rw [← hvol]
  have hrefine (i : Fin n) :
      (∑ J : g.T, MeasureTheory.volume.real (Ico_i i ∩ ((J : BoundedInterval) : Set ℝ))) -
        MeasureTheory.volume.real (Ico_i i ∩ ((Jᵢ i : BoundedInterval) : Set ℝ)) ≤
      MeasureTheory.volume.real (Ico_i i \ ((Jᵢ i : BoundedInterval) : Set ℝ)) := by
    calc
      (∑ J : g.T, MeasureTheory.volume.real (Ico_i i ∩ ((J : BoundedInterval) : Set ℝ))) -
          MeasureTheory.volume.real (Ico_i i ∩ ((Jᵢ i : BoundedInterval) : Set ℝ))
          = P.delta i - MeasureTheory.volume.real (Ico_i i ∩ ((Jᵢ i : BoundedInterval) : Set ℝ)) := by
              rw [hA i]
      _ = MeasureTheory.volume.real (Ico_i i \ ((Jᵢ i : BoundedInterval) : Set ℝ)) := by
              rw [← subinterval_vol P i, ← hpart i]
              ring
      _ ≤ MeasureTheory.volume.real (Ico_i i \ ((Jᵢ i : BoundedInterval) : Set ℝ)) := le_rfl
  -- per-term bound
  have hterm (i : Fin n) (J : g.T) :
      |(g.c (Jᵢ i) - g.c J) * MeasureTheory.volume.real (Ico_i i ∩ ((J : BoundedInterval) : Set ℝ))| ≤
        2 * C * MeasureTheory.volume.real (Ico_i i ∩ ((J : BoundedInterval) : Set ℝ)) := by
    rw [abs_mul]
    have hx0 : 0 ≤ MeasureTheory.volume.real (Ico_i i ∩ ((J : BoundedInterval) : Set ℝ)) :=
      MeasureTheory.measureReal_nonneg
    rw [abs_of_nonneg hx0]
    have hdiff : |g.c (Jᵢ i) - g.c J| ≤ 2 * C := by
      calc |g.c (Jᵢ i) - g.c J| ≤ |g.c (Jᵢ i)| + |g.c J| := abs_sub _ _
        _ ≤ 2 * C := by nlinarith [hC (Jᵢ i), hC J]
    exact mul_le_mul_of_nonneg_right hdiff hx0
  -- the difference as a double sum
  have hcom : P.RiemannSum g.f - g.integral =
      ∑ i : Fin n, ∑ J : g.T,
        (if J = Jᵢ i then 0 else
          (g.c (Jᵢ i) - g.c J) * MeasureTheory.volume.real (Ico_i i ∩ ((J : BoundedInterval) : Set ℝ))) := by
    have hRS : P.RiemannSum g.f = ∑ i : Fin n, g.c (Jᵢ i) * P.delta i := by
      rw [show P.RiemannSum g.f = ∑ i : Fin n, g.f (P.x_tag i) * P.delta i from rfl]
      apply Finset.sum_congr rfl
      intro i hi
      have ht : P.x_tag i ∈ ((Jᵢ i : BoundedInterval) : Set ℝ) :=
        cell_of_mem g (P.x_tag i) (tag_mem_I hI P i)
      rw [g.const (Jᵢ i) (P.x_tag i) ht]
    have h1 : P.RiemannSum g.f = ∑ i : Fin n, ∑ J : g.T, g.c (Jᵢ i) *
        MeasureTheory.volume.real (Ico_i i ∩ ((J : BoundedInterval) : Set ℝ)) := by
      rw [hRS]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hA i, Finset.mul_sum]
    have h2 : g.integral = ∑ i : Fin n, ∑ J : g.T, g.c J *
        MeasureTheory.volume.real (Ico_i i ∩ ((J : BoundedInterval) : Set ℝ)) := by
      calc
        g.integral = ∑ J : g.T, g.c J * |(J : BoundedInterval)|ₗ := rfl
        _ = ∑ J : g.T, g.c J * (∑ i : Fin n, MeasureTheory.volume.real
            (((J : BoundedInterval) : Set ℝ) ∩ Ico_i i)) := by
                apply Finset.sum_congr rfl
                intro J hJ
                rw [hB J]
        _ = ∑ J : g.T, ∑ i : Fin n, g.c J * MeasureTheory.volume.real
            (((J : BoundedInterval) : Set ℝ) ∩ Ico_i i) := by
                apply Finset.sum_congr rfl
                intro J hJ
                rw [Finset.mul_sum]
        _ = ∑ i : Fin n, ∑ J : g.T, g.c J * MeasureTheory.volume.real
            (((J : BoundedInterval) : Set ℝ) ∩ Ico_i i) := by
                rw [Finset.sum_comm]
        _ = ∑ i : Fin n, ∑ J : g.T, g.c J * MeasureTheory.volume.real
            (Ico_i i ∩ ((J : BoundedInterval) : Set ℝ)) := by
                apply Finset.sum_congr rfl
                intro i hi
                apply Finset.sum_congr rfl
                intro J hJ
                rw [Set.inter_comm]
    rw [h1, h2]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro J hJ
    by_cases hJeq : J = Jᵢ i
    · simp [hJeq]
    · simp [hJeq]
      ring
  -- the counting
  have hcross (i : Fin n) (hy : (Ico_i i \ ((Jᵢ i : BoundedInterval) : Set ℝ)).Nonempty) :
      ∃ e' ∈ e, e' ∈ Set.Icc (P.x i.castSucc) (P.x i.succ) := by
    rcases hy with ⟨y, hy⟩
    have hcross := interval_crossing_endpoint (J := (Jᵢ i : BoundedInterval))
        (t := P.x_tag i) (y := y)
        (cell_of_mem g (P.x_tag i) (tag_mem_I hI P i)) hy.2
        (P.x_tag_between i).1 (P.x_tag_between i).2 hy.1.1 (le_of_lt hy.1.2)
    have hmem_a : (Jᵢ i : BoundedInterval).a ∈ e := by
      rw [Finset.mem_union]
      left
      rw [Finset.mem_image]
      exact ⟨(Jᵢ i : BoundedInterval), (Jᵢ i).property, rfl⟩
    have hmem_b : (Jᵢ i : BoundedInterval).b ∈ e := by
      rw [Finset.mem_union]
      right
      rw [Finset.mem_image]
      exact ⟨(Jᵢ i : BoundedInterval), (Jᵢ i).property, rfl⟩
    rcases hcross with (hl | hr)
    · exact ⟨(Jᵢ i : BoundedInterval).a, hmem_a, hl⟩
    · exact ⟨(Jᵢ i : BoundedInterval).b, hmem_b, hr⟩
  have hvol_le (i : Fin n) :
      MeasureTheory.volume.real (Ico_i i \ ((Jᵢ i : BoundedInterval) : Set ℝ)) ≤ δ *
        (if ∃ e' ∈ e, e' ∈ Set.Icc (P.x i.castSucc) (P.x i.succ) then (1 : ℝ) else 0) := by
    by_cases hempty : (Ico_i i \ ((Jᵢ i : BoundedInterval) : Set ℝ)) = ∅
    · have hvol0 : MeasureTheory.volume.real (Ico_i i \ ((Jᵢ i : BoundedInterval) : Set ℝ)) = 0 := by
        rw [hempty]
        rw [MeasureTheory.Measure.real_def]
        simp
      rw [hvol0]
      by_cases h : ∃ e' ∈ e, e' ∈ Set.Icc (P.x i.castSucc) (P.x i.succ)
      · rw [if_pos h]
        simpa using hδ0
      · rw [if_neg h]
        simp
    · have hvolle : MeasureTheory.volume.real (Ico_i i \ ((Jᵢ i : BoundedInterval) : Set ℝ)) ≤ δ := by
        have hmono : MeasureTheory.volume (Ico_i i \ ((Jᵢ i : BoundedInterval) : Set ℝ)) ≤
            MeasureTheory.volume (Ico_i i) := MeasureTheory.measure_mono (Set.diff_subset)
        have hto : MeasureTheory.volume.real (Ico_i i \ ((Jᵢ i : BoundedInterval) : Set ℝ)) ≤
            MeasureTheory.volume.real (Ico_i i) := by
          rw [MeasureTheory.Measure.real_def, MeasureTheory.Measure.real_def]
          exact (ENNReal.toReal_le_toReal
            (ne_top_of_le_ne_top (subinterval_vol_ne_top P i) hmono) (subinterval_vol_ne_top P i)).mpr hmono
        calc
          MeasureTheory.volume.real (Ico_i i \ ((Jᵢ i : BoundedInterval) : Set ℝ))
              ≤ MeasureTheory.volume.real (Ico_i i) := hto
          _ = P.delta i := subinterval_vol P i
          _ ≤ δ := hPsub i
      have hEx : ∃ e' ∈ e, e' ∈ Set.Icc (P.x i.castSucc) (P.x i.succ) :=
        hcross i (Set.nonempty_iff_ne_empty.mpr hempty)
      rw [if_pos hEx]
      simpa using hvolle
  have hcount : (∑ i : Fin n, MeasureTheory.volume.real
        (Ico_i i \ ((Jᵢ i : BoundedInterval) : Set ℝ))) ≤ 4 * (g.T.card : ℝ) * δ := by
    have hsum_count : (∑ i : Fin n, (if ∃ e' ∈ e, e' ∈ Set.Icc (P.x i.castSucc) (P.x i.succ) then (1 : ℝ) else 0)) ≤
        2 * (e.card : ℝ) := by
      calc
        (∑ i : Fin n, (if ∃ e' ∈ e, e' ∈ Set.Icc (P.x i.castSucc) (P.x i.succ) then (1 : ℝ) else 0))
            ≤ ∑ i : Fin n, ∑ e' ∈ e, (if e' ∈ Set.Icc (P.x i.castSucc) (P.x i.succ) then (1 : ℝ) else 0) := by
                apply Finset.sum_le_sum
                intro i hi
                by_cases h : ∃ e' ∈ e, e' ∈ Set.Icc (P.x i.castSucc) (P.x i.succ)
                · rw [if_pos h]
                  rcases h with ⟨e', he', hi'⟩
                  have hnonneg : ∀ e'' ∈ e, 0 ≤ (if e'' ∈ Set.Icc (P.x i.castSucc) (P.x i.succ) then (1 : ℝ) else 0) := by
                    intro e'' he''; by_cases h2 : e'' ∈ Set.Icc (P.x i.castSucc) (P.x i.succ) <;> simp [h2]
                  have hle1 : (if e' ∈ Set.Icc (P.x i.castSucc) (P.x i.succ) then (1 : ℝ) else 0) ≤
                      ∑ e'' ∈ e, (if e'' ∈ Set.Icc (P.x i.castSucc) (P.x i.succ) then (1 : ℝ) else 0) :=
                    Finset.single_le_sum (s := e) (a := e')
                      (f := fun x => if x ∈ Set.Icc (P.x i.castSucc) (P.x i.succ) then (1 : ℝ) else 0) hnonneg he'
                  have hval : (if e' ∈ Set.Icc (P.x i.castSucc) (P.x i.succ) then (1 : ℝ) else 0) = 1 := by simp [hi']
                  rw [hval] at hle1
                  exact hle1
                · rw [if_neg h]
                  exact Finset.sum_nonneg (by intro e'' he''; by_cases h2 : e'' ∈ Set.Icc (P.x i.castSucc) (P.x i.succ) <;> simp [h2])
        _ = ∑ e' ∈ e, ∑ i : Fin n, (if e' ∈ Set.Icc (P.x i.castSucc) (P.x i.succ) then (1 : ℝ) else 0) := by rw [Finset.sum_comm]
        _ ≤ ∑ e' ∈ e, 2 := by
                apply Finset.sum_le_sum
                intro e' he'
                rw [Finset.sum_boole]
                exact_mod_cast (partition_point_count_le_two P.x P.x_mono e')
        _ = 2 * (e.card : ℝ) := by
                rw [Finset.sum_const, nsmul_eq_mul]
                ring
    calc
      (∑ i : Fin n, MeasureTheory.volume.real (Ico_i i \ ((Jᵢ i : BoundedInterval) : Set ℝ)))
          ≤ ∑ i : Fin n, δ * (if ∃ e' ∈ e, e' ∈ Set.Icc (P.x i.castSucc) (P.x i.succ) then (1 : ℝ) else 0) := by
              apply Finset.sum_le_sum
              intro i hi
              exact hvol_le i
      _ = δ * (∑ i : Fin n, (if ∃ e' ∈ e, e' ∈ Set.Icc (P.x i.castSucc) (P.x i.succ) then (1 : ℝ) else 0)) := by
              rw [Finset.mul_sum]
      _ ≤ δ * (2 * (e.card : ℝ)) := by
              apply mul_le_mul_of_nonneg_left _ hδ0
              exact hsum_count
      _ ≤ δ * (2 * (2 * (g.T.card : ℝ))) := by
              apply mul_le_mul_of_nonneg_left _ hδ0
              have hc : (e.card : ℝ) ≤ 2 * (g.T.card : ℝ) := by exact_mod_cast hecard
              nlinarith
      _ = 4 * (g.T.card : ℝ) * δ := by ring
  -- the main bound
  have hmain : |P.RiemannSum g.f - g.integral| ≤
      2 * C * (∑ i : Fin n, MeasureTheory.volume.real
        (Ico_i i \ ((Jᵢ i : BoundedInterval) : Set ℝ))) := by
    rw [hcom]
    calc
      |∑ i : Fin n, ∑ J : g.T, (if J = Jᵢ i then 0 else
          (g.c (Jᵢ i) - g.c J) * MeasureTheory.volume.real (Ico_i i ∩ ((J : BoundedInterval) : Set ℝ)))|
          ≤ ∑ i : Fin n, ∑ J : g.T, |(if J = Jᵢ i then 0 else
              (g.c (Jᵢ i) - g.c J) * MeasureTheory.volume.real (Ico_i i ∩ ((J : BoundedInterval) : Set ℝ)))| := by
              have h1 : |∑ i : Fin n, ∑ J : g.T,
                  (if J = Jᵢ i then 0 else
                    (g.c (Jᵢ i) - g.c J) * MeasureTheory.volume.real (Ico_i i ∩ ((J : BoundedInterval) : Set ℝ)))| ≤
                  ∑ i : Fin n, |∑ J : g.T,
                    (if J = Jᵢ i then 0 else
                      (g.c (Jᵢ i) - g.c J) * MeasureTheory.volume.real (Ico_i i ∩ ((J : BoundedInterval) : Set ℝ)))| := by
                    exact Finset.abs_sum_le_sum_abs (fun i : Fin n => ∑ J : g.T,
                      (if J = Jᵢ i then 0 else
                        (g.c (Jᵢ i) - g.c J) * MeasureTheory.volume.real (Ico_i i ∩ ((J : BoundedInterval) : Set ℝ)))) Finset.univ
              refine le_trans h1 ?_
              apply Finset.sum_le_sum
              intro i hi
              exact Finset.abs_sum_le_sum_abs (fun J : g.T =>
                (if J = Jᵢ i then 0 else
                  (g.c (Jᵢ i) - g.c J) * MeasureTheory.volume.real (Ico_i i ∩ ((J : BoundedInterval) : Set ℝ)))) Finset.univ
      _ ≤ ∑ i : Fin n, ∑ J : g.T, (if J = Jᵢ i then 0 else
            2 * C * MeasureTheory.volume.real (Ico_i i ∩ ((J : BoundedInterval) : Set ℝ))) := by
              apply Finset.sum_le_sum
              intro i hi
              apply Finset.sum_le_sum
              intro J hJ
              by_cases hJeq : J = Jᵢ i
              · simp [hJeq]
              · simpa [hJeq] using hterm i J
      _ = 2 * C * ((Finset.univ : Finset (Fin n)).sum (fun k : Fin n =>
            (∑ J : g.T, MeasureTheory.volume.real (Ico_i k ∩ ((J : BoundedInterval) : Set ℝ))) -
            (MeasureTheory.volume.real (Ico_i k ∩ ((Jᵢ k : BoundedInterval) : Set ℝ))))) := by
            have hinner (i : Fin n) :
                (∑ J : g.T, (if J = Jᵢ i then 0 else
                    2 * C * MeasureTheory.volume.real (Ico_i i ∩ ((J : BoundedInterval) : Set ℝ))))
                    = 2 * C * (∑ J : g.T, (if J = Jᵢ i then 0 else
                        MeasureTheory.volume.real (Ico_i i ∩ ((J : BoundedInterval) : Set ℝ)))) := by
                  calc
                    (∑ J : g.T, (if J = Jᵢ i then 0 else
                        2 * C * MeasureTheory.volume.real (Ico_i i ∩ ((J : BoundedInterval) : Set ℝ))))
                        = (∑ J : g.T, 2 * C * (if J = Jᵢ i then 0 else
                            MeasureTheory.volume.real (Ico_i i ∩ ((J : BoundedInterval) : Set ℝ)))) := by
                            apply Finset.sum_congr rfl
                            intro J hJ
                            by_cases h : J = Jᵢ i <;> simp [h]
                    _ = 2 * C * (∑ J : g.T, (if J = Jᵢ i then 0 else
                        MeasureTheory.volume.real (Ico_i i ∩ ((J : BoundedInterval) : Set ℝ)))) := by
                            rw [Finset.mul_sum]
            have herase (i : Fin n) :
                (∑ J : g.T, (if J = Jᵢ i then 0 else
                    MeasureTheory.volume.real (Ico_i i ∩ ((J : BoundedInterval) : Set ℝ)))) =
                (∑ J : g.T, MeasureTheory.volume.real (Ico_i i ∩ ((J : BoundedInterval) : Set ℝ))) -
                MeasureTheory.volume.real (Ico_i i ∩ ((Jᵢ i : BoundedInterval) : Set ℝ)) := by
                  let x : g.T → ℝ := fun J => MeasureTheory.volume.real (Ico_i i ∩ ((J : BoundedInterval) : Set ℝ))
                  change (∑ J : g.T, (if J = Jᵢ i then 0 else x J)) = (∑ J : g.T, x J) - x (Jᵢ i)
                  calc
                    (∑ J : g.T, (if J = Jᵢ i then 0 else x J))
                        = (Finset.univ : Finset g.T).sum (fun J : g.T => (x J - (if J = Jᵢ i then x J else 0))) := by
                            apply Finset.sum_congr rfl
                            intro J hJ
                            by_cases h : J = Jᵢ i <;> simp [h]
                    _ = (∑ J : g.T, x J) - (∑ J : g.T, (if J = Jᵢ i then x J else 0)) := by rw [Finset.sum_sub_distrib]
                    _ = (∑ J : g.T, x J) - x (Jᵢ i) := by
                            rw [Finset.sum_ite_eq' Finset.univ (Jᵢ i) x]
                            simp
            calc
              (∑ i : Fin n, ∑ J : g.T, (if J = Jᵢ i then 0 else
                  2 * C * MeasureTheory.volume.real (Ico_i i ∩ ((J : BoundedInterval) : Set ℝ))))
                  = ∑ i : Fin n, 2 * C * (∑ J : g.T, (if J = Jᵢ i then 0 else
                      MeasureTheory.volume.real (Ico_i i ∩ ((J : BoundedInterval) : Set ℝ)))) := by
                      apply Finset.sum_congr rfl
                      intro i hi
                      exact hinner i
              _ = 2 * C * (∑ i : Fin n, (∑ J : g.T, (if J = Jᵢ i then 0 else
                      MeasureTheory.volume.real (Ico_i i ∩ ((J : BoundedInterval) : Set ℝ))))) := by
                      rw [Finset.mul_sum]
              _ = 2 * C * ((Finset.univ : Finset (Fin n)).sum (fun k : Fin n =>
                      (∑ J : g.T, MeasureTheory.volume.real (Ico_i k ∩ ((J : BoundedInterval) : Set ℝ))) -
                      (MeasureTheory.volume.real (Ico_i k ∩ ((Jᵢ k : BoundedInterval) : Set ℝ))))) := by
                      congr 1
                      apply Finset.sum_congr rfl
                      intro i hi
                      exact herase i
      _ ≤ 2 * C * (∑ i : Fin n, MeasureTheory.volume.real
            (Ico_i i \ ((Jᵢ i : BoundedInterval) : Set ℝ))) := by
            apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hC0)
            apply Finset.sum_le_sum
            intro i hi
            exact hrefine i
  calc
    |P.RiemannSum g.f - g.integral|
        ≤ 2 * C * (∑ i : Fin n, MeasureTheory.volume.real
            (Ico_i i \ ((Jᵢ i : BoundedInterval) : Set ℝ))) := hmain
    _ ≤ 2 * C * (4 * (g.T.card : ℝ) * δ) := by
            apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hC0)
            exact hcount
    _ = 8 * C * (g.T.card : ℝ) * δ := by ring



/-- max a (-b) - max b (-a) = a - b. -/
lemma max_sub_max_id (a b : ℝ) : max a (-b) - max b (-a) = a - b := by
  by_cases h : 0 ≤ a + b
  · rw [max_eq_left (by linarith), max_eq_left (by linarith)]
  · have h' : a + b ≤ 0 := by linarith
    rw [max_eq_right (by linarith), max_eq_right (by linarith)]
    ring

/-- |max a (-b)| ≤ M when |a| ≤ M and |b| ≤ M. -/
lemma abs_max_neg_le {a b M : ℝ} (ha : |a| ≤ M) (hb : |b| ≤ M) : |max a (-b)| ≤ M := by
  apply abs_le.mpr
  constructor
  · have ha' : -M ≤ a := (abs_le.mp ha).1
    exact le_trans ha' (le_max_left _ _)
  · apply max_le_iff.mpr
    constructor
    · exact (abs_le.mp ha).2
    · have hle : -b ≤ |b| := neg_le_abs b
      exact le_trans hle hb

/-- |f| is Riemann integrable whenever f is. -/

theorem RiemannIntegrableOn.abs {I : BoundedInterval} {f : ℝ → ℝ} (hf : RiemannIntegrableOn f I) :
    RiemannIntegrableOn (fun x => |f x|) I := by
  classical
  rcases hf with ⟨hI, hnonempty, Rf, hRf⟩
  by_cases hdeg : I.a = I.b
  · exact (RiemannIntegrable.of_zero_length (fun x => |f x|) (a := I.a) (by rw [hI, hdeg])).1
  · have hab : I.a < I.b := by
      rcases hnonempty with ⟨x, hx⟩
      rw [hI] at hx
      by_contra h
      push_neg at h
      have hle : I.a ≤ I.b := le_trans hx.1 hx.2
      exact hdeg (le_antisymm hle h)
    rcases RiemannIntegrable.bounded ⟨hI, hnonempty, Rf, hRf⟩ with ⟨M, hM⟩
    have hM0 : 0 ≤ M := by
      rcases hnonempty with ⟨x, hx⟩
      have habs := hM x hx
      linarith [abs_nonneg (f x)]
    have hεδf : ∀ ε > 0, ∃ δ > 0, ∀ n, ∀ P : TaggedPartition I n, P.norm ≤ δ → |P.RiemannSum f - Rf| ≤ ε :=
      (riemann_integral_eq_iff Rf).mp hRf
    have hcauchy : ∀ ε > 0, ∃ δ > 0, ∀ P Q : Sigma (TaggedPartition I),
        P.snd.norm ≤ δ → Q.snd.norm ≤ δ →
        |P.snd.RiemannSum (fun x => |f x|) - Q.snd.RiemannSum (fun x => |f x|)| ≤ ε := by
      intro ε hε
      let ε₁ := ε / 20
      have hε₁ : 0 < ε₁ := by positivity
      rcases upper_lower_step_approx_134 hI hab ⟨M, hM⟩ Rf ε₁ hε₁ hεδf with ⟨T, val_u, val_l, hdisj, hcover, hsq, hout, hbounds⟩
      let u : PiecewiseConstantFunction I := PiecewiseConstantFunction.mkPCF T val_u hdisj hcover
      let l : PiecewiseConstantFunction I := PiecewiseConstantFunction.mkPCF T val_l hdisj hcover
      let U : PiecewiseConstantFunction I := PiecewiseConstantFunction.mkPCF T (fun J => max (val_u J) (-(val_l J))) hdisj hcover
      let L : PiecewiseConstantFunction I := PiecewiseConstantFunction.mkPCF T (fun J => max (val_l J) (-(val_u J))) hdisj hcover
      have hUx (x : ℝ) (hx : x ∈ I.toSet) : U.f x = max (u.f x) (-(l.f x)) := by
        have hx_mem : ∃ J' ∈ T, x ∈ (J' : Set ℝ) := by
          rw [hcover] at hx
          simpa using hx
        have hx_choose : x ∈ ((Classical.choose hx_mem : BoundedInterval) : Set ℝ) := (Classical.choose_spec hx_mem).2
        have hconst := U.const ⟨Classical.choose hx_mem, (Classical.choose_spec hx_mem).1⟩ x hx_choose
        have huc := u.const ⟨Classical.choose hx_mem, (Classical.choose_spec hx_mem).1⟩ x hx_choose
        have hlc := l.const ⟨Classical.choose hx_mem, (Classical.choose_spec hx_mem).1⟩ x hx_choose
        rw [hconst, huc, hlc]
        change (fun J : BoundedInterval => max (val_u J) (-(val_l J))) (Classical.choose hx_mem) =
          max ((fun J : BoundedInterval => val_u J) (Classical.choose hx_mem))
            (-((fun J : BoundedInterval => val_l J) (Classical.choose hx_mem)))
        rfl
      have hLx (x : ℝ) (hx : x ∈ I.toSet) : L.f x = max (l.f x) (-(u.f x)) := by
        have hx_mem : ∃ J' ∈ T, x ∈ (J' : Set ℝ) := by
          rw [hcover] at hx
          simpa using hx
        have hx_choose : x ∈ ((Classical.choose hx_mem : BoundedInterval) : Set ℝ) := (Classical.choose_spec hx_mem).2
        have hconst := L.const ⟨Classical.choose hx_mem, (Classical.choose_spec hx_mem).1⟩ x hx_choose
        have huc := u.const ⟨Classical.choose hx_mem, (Classical.choose_spec hx_mem).1⟩ x hx_choose
        have hlc := l.const ⟨Classical.choose hx_mem, (Classical.choose_spec hx_mem).1⟩ x hx_choose
        rw [hconst, huc, hlc]
        change (fun J : BoundedInterval => max (val_l J) (-(val_u J))) (Classical.choose hx_mem) =
          max ((fun J : BoundedInterval => val_l J) (Classical.choose hx_mem))
            (-((fun J : BoundedInterval => val_u J) (Classical.choose hx_mem)))
        rfl
      have hLU (x : ℝ) (hx : x ∈ I.toSet) : L.f x ≤ |f x| ∧ |f x| ≤ U.f x := by
        rcases hsq x hx with ⟨hl, hu⟩
        rw [hLx x hx, hUx x hx]
        constructor
        · have hle1 : l.f x ≤ |f x| := le_trans hl (le_abs_self (f x))
          have hle2 : -(u.f x) ≤ |f x| := by
            have : -u.f x ≤ -f x := neg_le_neg hu
            exact le_trans this (neg_le_abs (f x))
          exact max_le_iff.mpr ⟨hle1, hle2⟩
        · have hle1 : f x ≤ u.f x := hu
          have hle2 : -(f x) ≤ -(l.f x) := neg_le_neg hl
          rw [abs_eq_max_neg]
          exact max_le_max hle1 hle2
      let C_U : ℝ := ∑ J : U.T, |U.c J|
      let C_L : ℝ := ∑ J : L.T, |L.c J|
      have hC_U : ∀ J : U.T, |U.c J| ≤ C_U := by
        intro J
        dsimp [C_U]
        exact Finset.single_le_sum (s := Finset.univ) (a := J) (f := fun K : U.T => |U.c K|)
          (by intro K hK; exact abs_nonneg (U.c K)) (Finset.mem_univ J)
      have hC_L : ∀ J : L.T, |L.c J| ≤ C_L := by
        intro J
        dsimp [C_L]
        exact Finset.single_le_sum (s := Finset.univ) (a := J) (f := fun K : L.T => |L.c K|)
          (by intro K hK; exact abs_nonneg (L.c K)) (Finset.mem_univ J)
      have hC0_U : 0 ≤ C_U := by
        dsimp [C_U]
        exact Finset.sum_nonneg (fun J hJ => abs_nonneg (U.c J))
      have hC0_L : 0 ≤ C_L := by
        dsimp [C_L]
        exact Finset.sum_nonneg (fun J hJ => abs_nonneg (L.c J))
      have hUL_int : U.integral - L.integral ≤ 4 * ε₁ := by
        have hU_int : U.integral = ∑ J ∈ T, (max (val_u J) (-(val_l J))) * |J|ₗ := by
          rw [PiecewiseConstantFunction.mkPCF_integral T (fun J => max (val_u J) (-(val_l J))) hdisj hcover]
        have hL_int : L.integral = ∑ J ∈ T, (max (val_l J) (-(val_u J))) * |J|ₗ := by
          rw [PiecewiseConstantFunction.mkPCF_integral T (fun J => max (val_l J) (-(val_u J))) hdisj hcover]
        have hu_int : u.integral = ∑ J ∈ T, val_u J * |J|ₗ := by
          rw [PiecewiseConstantFunction.mkPCF_integral T val_u hdisj hcover]
        have hl_int : l.integral = ∑ J ∈ T, val_l J * |J|ₗ := by
          rw [PiecewiseConstantFunction.mkPCF_integral T val_l hdisj hcover]
        have hdiff_sum : U.integral - L.integral = u.integral - l.integral := by
          rw [hU_int, hL_int, hu_int, hl_int]
          rw [← Finset.sum_sub_distrib]
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro J hJ
          rw [← sub_mul, max_sub_max_id, sub_mul]
        have hu_le' : u.integral ≤ Rf + 2 * ε₁ := hbounds.1
        have hl_ge' : Rf - 2 * ε₁ ≤ l.integral := hbounds.2
        rw [hdiff_sum]
        nlinarith
      have h_out (x : ℝ) (hx : x ∉ I.toSet) : U.f x = 0 ∧ L.f x = 0 := by
        have hx_mem : ¬ ∃ J' ∈ T, x ∈ (J' : Set ℝ) := by
          intro h
          rcases h with ⟨J', hJ', hx'⟩
          exact hx (by rw [hcover]; exact Set.mem_iUnion₂.mpr ⟨J', hJ', hx'⟩)
        constructor
        · dsimp [U]
          change (if h : ∃ J' ∈ T, x ∈ (J' : Set ℝ) then
              (fun J : BoundedInterval => max (val_u J) (-(val_l J))) (Classical.choose h) else 0) = 0
          rw [dif_neg hx_mem]
        · dsimp [L]
          change (if h : ∃ J' ∈ T, x ∈ (J' : Set ℝ) then
              (fun J : BoundedInterval => max (val_l J) (-(val_u J))) (Classical.choose h) else 0) = 0
          rw [dif_neg hx_mem]
      let δ : ℝ := ε₁ / (1 + 16 * (C_U + C_L) * (T.card : ℝ))
      have hT0 : (0 : ℝ) ≤ (T.card : ℝ) := by exact_mod_cast Nat.zero_le T.card
      have hden0 : 0 < 1 + 16 * (C_U + C_L) * (T.card : ℝ) := by
        nlinarith [hC0_U, hC0_L, hT0]
      have hδ_pos : 0 < δ := by
        dsimp [δ]
        exact div_pos hε₁ hden0
      have hδ0 : 0 ≤ δ := le_of_lt hδ_pos
      have hδ_bound : 16 * (C_U + C_L) * (T.card : ℝ) * δ ≤ ε₁ := by
        dsimp [δ]
        let x : ℝ := 16 * (C_U + C_L) * (T.card : ℝ)
        have hx0 : 0 ≤ x := by dsimp [x]; nlinarith [hC0_U, hC0_L, hT0]
        have hden : 0 < 1 + x := hden0
        calc
          x * (ε₁ / (1 + x)) = ε₁ * (x / (1 + x)) := by ring
          _ ≤ ε₁ * 1 := by
                apply mul_le_mul_of_nonneg_left _ (le_of_lt hε₁)
                rw [div_le_iff₀ hden]
                nlinarith
          _ = ε₁ := by ring
      have hUT : (U.T.card : ℝ) = (T.card : ℝ) := by dsimp [U]; rfl
      have hLT : (L.T.card : ℝ) = (T.card : ℝ) := by dsimp [L]; rfl
      refine ⟨δ, hδ_pos, ?_⟩
      intro P Q hPδ hQδ
      have hPb := pcf_RiemannSum_close U hI C_U δ hC_U hC0_U hδ0 P.snd hPδ
      have hQb := pcf_RiemannSum_close L hI C_L δ hC_L hC0_L hδ0 Q.snd hQδ
      have hPle : P.snd.RiemannSum (fun x => |f x|) ≤ P.snd.RiemannSum U.f := by
        apply Finset.sum_le_sum
        intro i hi
        have ht : P.snd.x_tag i ∈ I.toSet := tag_mem_I hI P.snd i
        have hle := (hLU (P.snd.x_tag i) ht).2
        have hδi : 0 ≤ P.snd.delta i := le_of_lt (sub_pos.mpr (P.snd.x_mono Fin.castSucc_lt_succ))
        exact mul_le_mul_of_nonneg_right hle hδi
      have hQge : Q.snd.RiemannSum L.f ≤ Q.snd.RiemannSum (fun x => |f x|) := by
        apply Finset.sum_le_sum
        intro i hi
        have ht : Q.snd.x_tag i ∈ I.toSet := tag_mem_I hI Q.snd i
        have hle := (hLU (Q.snd.x_tag i) ht).1
        have hδi : 0 ≤ Q.snd.delta i := le_of_lt (sub_pos.mpr (Q.snd.x_mono Fin.castSucc_lt_succ))
        exact mul_le_mul_of_nonneg_right hle hδi
      have hpair : ∀ (P Q : Sigma (TaggedPartition I)), P.snd.norm ≤ δ → Q.snd.norm ≤ δ →
          P.snd.RiemannSum (fun x => |f x|) - Q.snd.RiemannSum (fun x => |f x|) ≤
          U.integral - L.integral + 8 * C_U * (T.card : ℝ) * δ + 8 * C_L * (T.card : ℝ) * δ := by
        intro P' Q' hP' hQ'
        have hP'b := pcf_RiemannSum_close U hI C_U δ hC_U hC0_U hδ0 P'.snd hP'
        have hQ'b := pcf_RiemannSum_close L hI C_L δ hC_L hC0_L hδ0 Q'.snd hQ'
        have hP'le : P'.snd.RiemannSum (fun x => |f x|) ≤ P'.snd.RiemannSum U.f := by
          apply Finset.sum_le_sum
          intro i hi
          have ht : P'.snd.x_tag i ∈ I.toSet := tag_mem_I hI P'.snd i
          have hle := (hLU (P'.snd.x_tag i) ht).2
          have hδi : 0 ≤ P'.snd.delta i := le_of_lt (sub_pos.mpr (P'.snd.x_mono Fin.castSucc_lt_succ))
          exact mul_le_mul_of_nonneg_right hle hδi
        have hQ'ge : Q'.snd.RiemannSum L.f ≤ Q'.snd.RiemannSum (fun x => |f x|) := by
          apply Finset.sum_le_sum
          intro i hi
          have ht : Q'.snd.x_tag i ∈ I.toSet := tag_mem_I hI Q'.snd i
          have hle := (hLU (Q'.snd.x_tag i) ht).1
          have hδi : 0 ≤ Q'.snd.delta i := le_of_lt (sub_pos.mpr (Q'.snd.x_mono Fin.castSucc_lt_succ))
          exact mul_le_mul_of_nonneg_right hle hδi
        calc
          P'.snd.RiemannSum (fun x => |f x|) - Q'.snd.RiemannSum (fun x => |f x|)
              ≤ P'.snd.RiemannSum U.f - Q'.snd.RiemannSum L.f := by linarith
          _ ≤ (U.integral + 8 * C_U * (T.card : ℝ) * δ) - (L.integral - 8 * C_L * (T.card : ℝ) * δ) := by
                have h1 : P'.snd.RiemannSum U.f ≤ U.integral + 8 * C_U * (T.card : ℝ) * δ := by
                  rw [← hUT]
                  linarith [abs_le.mp hP'b]
                have h2 : L.integral - 8 * C_L * (T.card : ℝ) * δ ≤ Q'.snd.RiemannSum L.f := by
                  rw [← hLT]
                  linarith [abs_le.mp hQ'b]
                linarith
          _ = U.integral - L.integral + 8 * C_U * (T.card : ℝ) * δ + 8 * C_L * (T.card : ℝ) * δ := by ring
      have hmain_b : |P.snd.RiemannSum (fun x => |f x|) - Q.snd.RiemannSum (fun x => |f x|)| ≤
          U.integral - L.integral + 8 * C_U * (T.card : ℝ) * δ + 8 * C_L * (T.card : ℝ) * δ := by
        rw [abs_le]
        constructor
        · have h1 : -(P.snd.RiemannSum (fun x => |f x|) - Q.snd.RiemannSum (fun x => |f x|)) ≤
              U.integral - L.integral + 8 * C_U * (T.card : ℝ) * δ + 8 * C_L * (T.card : ℝ) * δ := by
            have hswap : -(P.snd.RiemannSum (fun x => |f x|) - Q.snd.RiemannSum (fun x => |f x|)) =
                Q.snd.RiemannSum (fun x => |f x|) - P.snd.RiemannSum (fun x => |f x|) := by ring
            rw [hswap]
            exact hpair Q P hQδ hPδ
          nlinarith
        · exact hpair P Q hPδ hQδ
      calc
        |P.snd.RiemannSum (fun x => |f x|) - Q.snd.RiemannSum (fun x => |f x|)|
            ≤ U.integral - L.integral + 8 * C_U * (T.card : ℝ) * δ + 8 * C_L * (T.card : ℝ) * δ := hmain_b
        _ ≤ 4 * ε₁ + 8 * C_U * (T.card : ℝ) * δ + 8 * C_L * (T.card : ℝ) * δ := by linarith [hUL_int]
        _ ≤ 5 * ε₁ := by
              have hδ' : 8 * C_U * (T.card : ℝ) * δ + 8 * C_L * (T.card : ℝ) * δ ≤ ε₁ := by nlinarith [hδ_bound]
              nlinarith
        _ ≤ ε := by
              dsimp [ε₁] at hε₁ ⊢
              nlinarith
    haveI : Filter.NeBot (TaggedPartition.nhds_zero I) := TaggedPartition.nhds_zero_neBot I hI hab
    have hmap_ne : Filter.NeBot (Filter.map (fun a : Sigma (TaggedPartition I) => a.snd.RiemannSum (fun x => |f x|)) (TaggedPartition.nhds_zero I)) := Filter.map_neBot
    have hcauchy_filter : Cauchy (Filter.map (fun a : Sigma (TaggedPartition I) => a.snd.RiemannSum (fun x => |f x|)) (TaggedPartition.nhds_zero I)) := by
      rw [Metric.cauchy_iff]
      constructor
      · exact hmap_ne
      · intro ε hε
        rcases hcauchy (ε / 2) (half_pos hε) with ⟨δ, hδ, hδ'⟩
        have h_ball : Metric.ball (0 : ℝ) δ ∈ nhds (0 : ℝ) := by
          rw [Metric.mem_nhds_iff]
          exact ⟨δ, hδ, fun x hx => hx⟩
        let N : Set (Sigma (TaggedPartition I)) := {P | P.snd.norm ≤ δ}
        have hN_mem : N ∈ TaggedPartition.nhds_zero I := by
          rw [TaggedPartition.nhds_zero, Filter.mem_comap]
          refine ⟨Metric.ball (0 : ℝ) δ, h_ball, ?_⟩
          intro P hP
          have hP_norm_le : P.snd.norm ≤ δ := by
            have hball : P.snd.norm ∈ Metric.ball (0 : ℝ) δ := hP
            rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hball
            exact (abs_lt.mp hball).2.le
          simpa [N] using hP_norm_le
        let t : Set ℝ := (fun a : Sigma (TaggedPartition I) => a.snd.RiemannSum (fun x => |f x|)) '' N
        have ht_mem : t ∈ Filter.map (fun a : Sigma (TaggedPartition I) => a.snd.RiemannSum (fun x => |f x|)) (TaggedPartition.nhds_zero I) := by
          rw [Filter.mem_map]
          apply Filter.mem_of_superset hN_mem
          intro P hP
          exact ⟨P, hP, rfl⟩
        refine ⟨t, ht_mem, ?_⟩
        intro x hx y hy
        rcases hx with ⟨P, hP, rfl⟩
        rcases hy with ⟨Q, hQ, rfl⟩
        rw [Real.dist_eq]
        exact lt_of_le_of_lt (hδ' P Q (by simpa [N] using hP) (by simpa [N] using hQ)) (half_lt_self hε)
    rcases (show CompleteSpace ℝ by infer_instance).complete hcauchy_filter with ⟨R, hR⟩
    exact ⟨hI, hnonempty, R, hR⟩

-- temporary placeholder for the theorems (kept as sorry until helpers are ready)

/-- The absolute value of a real measurable function is unsigned measurable. -/
lemma realMeasurable_abs_um {d : ℕ} {f : EuclideanSpace' d → ℝ} (hf : RealMeasurable f) :
    UnsignedMeasurable (EReal.abs_fun f) := by
  constructor
  · intro x
    simp only [EReal.abs_fun]
    exact EReal.coe_nonneg.mpr (norm_nonneg _)
  · obtain ⟨g, hg_simple, hg_conv⟩ := hf
    use fun n => EReal.abs_fun (g n)
    constructor
    · intro n
      exact (hg_simple n).abs
    · intro x
      simp only [EReal.abs_fun]
      exact (continuous_coe_real_ereal.comp continuous_norm).continuousAt.tendsto.comp (hg_conv x)

/-- Riemann sums are extensional in the function. -/
lemma riemann_integral_eq_of_pointwise_eq {f g : ℝ → ℝ} {I : BoundedInterval} {R : ℝ}
    (h : ∀ x, f x = g x) : riemann_integral_eq f I R ↔ riemann_integral_eq g I R := by
  unfold riemann_integral_eq
  apply Filter.tendsto_congr'
  exact Filter.univ_mem' (fun P => by
    unfold TaggedPartition.RiemannSum
    apply Finset.sum_congr rfl
    intro i hi
    rw [h (P.snd.x_tag i)])

/-- The Riemann integral is extensional in the function. -/
lemma riemannIntegral_congr {f g : ℝ → ℝ} {I : BoundedInterval} (h : ∀ x, f x = g x) :
    riemannIntegral f I = riemannIntegral g I := by
  classical
  by_cases hf : RiemannIntegrableOn f I
  · have hg : RiemannIntegrableOn g I := by
      rcases hf with ⟨hIcc, hne, R, hR⟩
      refine ⟨hIcc, hne, R, ?_⟩
      exact (riemann_integral_eq_of_pointwise_eq h).mp hR
    have hRf : riemann_integral_eq f I (riemannIntegral f I) := riemann_integral_of_integrable hf
    have hRg : riemann_integral_eq g I (riemannIntegral f I) := (riemann_integral_eq_of_pointwise_eq h).mp hRf
    exact (riemann_integral_eq_iff_of_integrable hg (riemannIntegral f I)).mp hRg
  · have hg : ¬ RiemannIntegrableOn g I := by
      intro hg
      exact hf (by
        rcases hg with ⟨hIcc, hne, R, hR⟩
        refine ⟨hIcc, hne, R, ?_⟩
        exact (riemann_integral_eq_of_pointwise_eq h).mpr hR)
    simp [riemannIntegral, hf, hg]

/-- max (f x) 0 is Riemann integrable whenever f is. -/
theorem RiemannIntegrableOn.pos {I : BoundedInterval} {f : ℝ → ℝ} (hf : RiemannIntegrableOn f I) :
    RiemannIntegrableOn (fun x => max (f x) 0) I := by
  classical
  have hf_abs : RiemannIntegrableOn (fun x => |f x|) I := RiemannIntegrableOn.abs hf
  have hsum : RiemannIntegrableOn (f + (fun x => |f x|)) I := RiemannIntegrableOn.add hf hf_abs
  have hhalf : RiemannIntegrableOn ((1 / 2 : ℝ) • (f + (fun x => |f x|))) I :=
    RiemannIntegrableOn.smul (1 / 2) hsum
  have hpt : ∀ x, ((1 / 2 : ℝ) • (f + (fun x => |f x|))) x = max (f x) 0 := by
    intro x
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    have hmax : max (f x) 0 = (f x + |f x|) / 2 := by
      by_cases h : 0 ≤ f x
      · rw [abs_of_nonneg h, max_eq_left h]
        ring
      · have h' : f x ≤ 0 := by linarith
        rw [abs_of_nonpos h', max_eq_right h']
        ring
    rw [hmax]
    ring
  rcases hhalf with ⟨hIcc, hne, R, hR⟩
  refine ⟨hIcc, hne, R, ?_⟩
  exact (riemann_integral_eq_of_pointwise_eq hpt).mp hR

/-- max (-(f x)) 0 is Riemann integrable whenever f is. -/
theorem RiemannIntegrableOn.neg {I : BoundedInterval} {f : ℝ → ℝ} (hf : RiemannIntegrableOn f I) :
    RiemannIntegrableOn (fun x => max (-(f x)) 0) I := by
  classical
  have hneg : RiemannIntegrableOn ((-1 : ℝ) • f) I := RiemannIntegrableOn.smul (-1) hf
  have hpos := RiemannIntegrableOn.pos hneg
  have hpt : ∀ x, ((-1 : ℝ) • f) x = -(f x) := by
    intro x
    simp
  rcases hpos with ⟨hIcc, hne, R, hR⟩
  refine ⟨hIcc, hne, R, ?_⟩
  have hconv : riemann_integral_eq (fun x => max (((-1 : ℝ) • f) x) 0) I R ↔
      riemann_integral_eq (fun x => max (-(f x)) 0) I R :=
    riemann_integral_eq_of_pointwise_eq (fun x => by simp [Pi.smul_apply])
  exact hconv.mp hR

/-- The integral of a scalar multiple. -/
theorem riemann_integral_smul' {I : BoundedInterval} (c : ℝ) {f : ℝ → ℝ} (h : RiemannIntegrableOn f I) :
    riemannIntegral (c • f) I = c • (riemannIntegral f I) := by
  classical
  have hRf : riemann_integral_eq f I (riemannIntegral f I) := riemann_integral_of_integrable h
  have hsmul : riemann_integral_eq (c • f) I (c • (riemannIntegral f I)) := by
    have hsums : ∀ n (P : TaggedPartition I n), P.RiemannSum (c • f) = c • P.RiemannSum f := by
      intro n P
      unfold TaggedPartition.RiemannSum
      simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
    dsimp [riemann_integral_eq, TaggedPartition.nhds_zero]
    simpa [hsums] using hRf.const_smul c
  exact ((riemann_integral_eq_iff_of_integrable (RiemannIntegrableOn.smul c h) (c • (riemannIntegral f I))).mp hsmul).symm

/-- The integral of a sum. -/
theorem riemann_integral_add' {I : BoundedInterval} {f g : ℝ → ℝ} (hf : RiemannIntegrableOn f I)
    (hg : RiemannIntegrableOn g I) :
    riemannIntegral (f + g) I = riemannIntegral f I + riemannIntegral g I := by
  classical
  have hRf : riemann_integral_eq f I (riemannIntegral f I) := riemann_integral_of_integrable hf
  have hRg : riemann_integral_eq g I (riemannIntegral g I) := riemann_integral_of_integrable hg
  have hadd : riemann_integral_eq (f + g) I (riemannIntegral f I + riemannIntegral g I) := by
    have hsums : ∀ n (P : TaggedPartition I n), P.RiemannSum (f + g) = P.RiemannSum f + P.RiemannSum g := by
      intro n P
      unfold TaggedPartition.RiemannSum
      simp [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    dsimp [riemann_integral_eq, TaggedPartition.nhds_zero]
    simpa [hsums] using hRf.add hRg
  exact ((riemann_integral_eq_iff_of_integrable (RiemannIntegrableOn.add hf hg)
    (riemannIntegral f I + riemannIntegral g I)).mp hadd).symm

theorem RiemannIntegrableOn.realAbsolutelyIntegrable {I: BoundedInterval} {f: ℝ → ℝ} (hf: RiemannIntegrableOn f I) : RealAbsolutelyIntegrable ((fun x ↦ (f x) * (I.toSet.indicator' x)) ∘ EuclideanSpace'.equiv_Real) := by
  classical
  let h : ℝ → ℝ := fun x => f x * (I.toSet.indicator' x)
  let e : EuclideanSpace' 1 → ℝ := EuclideanSpace'.equiv_Real
  let g : EuclideanSpace' 1 → ℝ := h ∘ e
  -- measurability
  have hmeas : RealMeasurable g := by
    have hRI : RealMeasurable ((fun x => if x ∈ I.toSet then f x else 0) ∘ EuclideanSpace'.equiv_Real) :=
      RealMeasurable.riemann_integrable hf
    have hpt : (fun x => if x ∈ I.toSet then f x else 0) = h := by
      funext x
      by_cases hx : x ∈ I.toSet
      · simp [h, hx]
      · simp [h, hx]
    change RealMeasurable (h ∘ e)
    rw [← hpt]
    exact hRI
  -- finiteness
  have hfin : UnsignedLebesgueIntegral (EReal.abs_fun g) < ⊤ := by
    rcases RiemannIntegrable.bounded hf with ⟨M, hM⟩
    have hM0 : 0 ≤ M := by
      rcases hf.2.1 with ⟨x, hx⟩
      linarith [hM x hx, abs_nonneg (f x)]
    let Eset : Set (EuclideanSpace' 1) := e ⁻¹' I.toSet
    have he_pre : Eset = Real.equiv_EuclideanSpace' '' (I : Set ℝ) := by
      ext x
      simp [Eset, e, Set.mem_preimage, Set.mem_image]
      constructor
      · intro hx
        refine ⟨e x, hx, ?_⟩
        exact Equiv.symm_apply_apply EuclideanSpace'.equiv_Real x
      · intro hx
        rcases hx with ⟨y, hy, hxy⟩
        have : e (Real.equiv_EuclideanSpace' y) = y := by
          simp [e]
        have hxeq : e x = y := by
          rw [← hxy]
          exact this
        change e x ∈ ↑I
        rw [hxeq]
        exact hy
    have hEmeas : LebesgueMeasurable Eset := by
      rw [he_pre]
      exact lift_image_BoundedInterval_measurable I
    have hLset : Lebesgue_measure Eset = (|I|ₗ : EReal) := by
      rw [he_pre, Lebesgue_measure]
      exact lift_interval_measure_134 I
    let T : EuclideanSpace' 1 → EReal := fun x => (M * (I.toSet.indicator' (e x))).toEReal
    have hT_simple : UnsignedSimpleFunction T := by
      refine ⟨1, fun _ => (M : EReal), fun _ => Eset, ?_, ?_⟩
      · intro i
        constructor
        · exact hEmeas
        · exact EReal.coe_nonneg.mpr hM0
      · funext x
        simp [T, Pi.smul_apply, smul_eq_mul]
        by_cases hx : e x ∈ I.toSet
        · have hxE : x ∈ Eset := hx
          simp [EReal.indicator_of_mem hxE, Set.indicator'_of_mem hx]
        · have hxE : x ∉ Eset := fun h => hx h
          simp [EReal.indicator_of_notMem hxE, Set.indicator'_of_notMem hx]
    have hT_um : UnsignedMeasurable T := by
      constructor
      · intro x
        dsimp [T]
        exact EReal.coe_nonneg.mpr (mul_nonneg hM0 (Set.indicator_nonneg (by intro a ha; norm_num) (e x)))
      · refine ⟨fun _ => T, fun _ => hT_simple, ?_⟩
        intro x
        exact tendsto_const_nhds
    have hT_eq : T = ∑ i : Fin 1, (M : EReal) • EReal.indicator Eset := by
      funext x
      simp [T, Pi.smul_apply, smul_eq_mul]
      by_cases hx : e x ∈ I.toSet
      · have hxE : x ∈ Eset := hx
        simp [EReal.indicator_of_mem hxE, Set.indicator'_of_mem hx]
      · have hxE : x ∉ Eset := fun h => hx h
        simp [EReal.indicator_of_notMem hxE, Set.indicator'_of_notMem hx]
    have hT_lt : UnsignedLebesgueIntegral T < ⊤ := by
      rw [UnsignedLebesgueIntegral, LowerUnsignedLebesgueIntegral.eq_simpleIntegral hT_simple]
      have hTi : hT_simple.integ = (M : EReal) * Lebesgue_measure Eset := by
        rw [UnsignedSimpleFunction.integral_eq hT_simple
          (c := fun _ : Fin 1 => (M : EReal)) (E := fun _ : Fin 1 => Eset)
          (hmes := fun i => hEmeas) (hnonneg := fun i => EReal.coe_nonneg.mpr hM0) (heq := hT_eq)]
        simp
      rw [hTi, hLset]
      rw [← EReal.coe_mul]
      exact EReal.coe_lt_top (M * |I|ₗ)
    have hle : ∀ x : EuclideanSpace' 1, EReal.abs_fun g x ≤ T x := by
      intro x
      rw [EReal.abs_fun, Real.norm_eq_abs]
      dsimp [T]
      apply EReal.coe_le_coe_iff.mpr
      dsimp [g, h]
      by_cases hx : e x ∈ I.toSet
      · rw [Set.indicator'_of_mem hx]
        have hb := hM (e x) hx
        simpa using hb
      · rw [Set.indicator'_of_notMem hx]
        have : |f (e x) * 0| = 0 := by simp
        rw [this]
        simp
    have hmono := LowerUnsignedLebesgueIntegral.mono (realMeasurable_abs_um hmeas) hT_um
      (AlmostAlways.ofAlways hle)
    exact lt_of_le_of_lt hmono hT_lt
  exact ⟨hmeas, hfin⟩

theorem RiemannIntegral.eq_integ {I: BoundedInterval} {f: ℝ → ℝ} (hf: RiemannIntegrableOn f I) :
    riemannIntegral f I  = hf.realAbsolutelyIntegrable.integ := by
  classical
  let p : ℝ → ℝ := fun x => max (f x) 0
  let n : ℝ → ℝ := fun x => max (-(f x)) 0
  let g : EuclideanSpace' 1 → ℝ := (fun x => f x * (I.toSet.indicator' x)) ∘ EuclideanSpace'.equiv_Real
  have hf_test : RealAbsolutelyIntegrable g := by
    simpa [g] using hf.realAbsolutelyIntegrable
  have hp : RiemannIntegrableOn p I := RiemannIntegrableOn.pos hf
  have hn : RiemannIntegrableOn n I := RiemannIntegrableOn.neg hf
  have hpos_eq : EReal.pos_fun g =
      Real.toEReal ∘ (fun x => p x * (I.toSet.indicator' x)) ∘ EuclideanSpace'.equiv_Real := by
    funext x
    simp [EReal.pos_fun, g, p]
    by_cases hx : EuclideanSpace'.equiv_Real x ∈ I.toSet
    · have hx' : x.ofLp 0 ∈ (↑I : Set ℝ) := hx
      simp [Set.indicator'_of_mem hx']
    · have hx' : x.ofLp 0 ∉ (↑I : Set ℝ) := hx
      simp [Set.indicator'_of_notMem hx']
  have hneg_eq : EReal.neg_fun g =
      Real.toEReal ∘ (fun x => n x * (I.toSet.indicator' x)) ∘ EuclideanSpace'.equiv_Real := by
    funext x
    simp [EReal.neg_fun, g, n]
    by_cases hx : EuclideanSpace'.equiv_Real x ∈ I.toSet
    · have hx' : x.ofLp 0 ∈ (↑I : Set ℝ) := hx
      simp [Set.indicator'_of_mem hx']
    · have hx' : x.ofLp 0 ∉ (↑I : Set ℝ) := hx
      simp [Set.indicator'_of_notMem hx']
  have hpos_int : UnsignedLebesgueIntegral (EReal.pos_fun g) = (riemannIntegral p I : EReal) := by
    have hA := RiemannIntegral.eq_UnsignedLebesgueIntegral hp (by
      intro x hx
      dsimp [p]
      exact le_max_right (f x) 0)
    rw [hpos_eq, hA]
  have hneg_int : UnsignedLebesgueIntegral (EReal.neg_fun g) = (riemannIntegral n I : EReal) := by
    have hA := RiemannIntegral.eq_UnsignedLebesgueIntegral hn (by
      intro x hx
      dsimp [n]
      exact le_max_right (-(f x)) 0)
    rw [hneg_eq, hA]
  have hpos_toReal : hf_test.pos.integ = riemannIntegral p I := by
    dsimp [RealAbsolutelyIntegrable.integ, UnsignedAbsolutelyIntegrable.integ]
    rw [hpos_int, EReal.toReal_coe]
  have hneg_toReal : hf_test.neg.integ = riemannIntegral n I := by
    dsimp [RealAbsolutelyIntegrable.integ, UnsignedAbsolutelyIntegrable.integ]
    rw [hneg_int, EReal.toReal_coe]
  have hfn : f = p - n := by
    funext x
    dsimp [p, n]
    by_cases hx : 0 ≤ f x
    · rw [max_eq_left hx, max_eq_right (by linarith : -(f x) ≤ 0)]
      ring
    · have hx' : f x ≤ 0 := by linarith
      rw [max_eq_right hx', max_eq_left (by linarith : 0 ≤ -(f x))]
      ring
  have hpn : p - n = p + ((-1 : ℝ) • n) := by
    funext x
    dsimp [p, n]
    rw [sub_eq_add_neg]
    simp
  have hpn_int : riemannIntegral (p - n) I = riemannIntegral p I - riemannIntegral n I := by
    rw [hpn]
    have h1 := riemann_integral_add' hp (RiemannIntegrableOn.smul (-1) hn)
    have h2 := riemann_integral_smul' (-1) hn
    rw [h1, h2]
    simp
    ring
  calc
    riemannIntegral f I = riemannIntegral (p - n) I := riemannIntegral_congr (congrFun hfn)
    _ = riemannIntegral p I - riemannIntegral n I := hpn_int
    _ = hf_test.pos.integ - hf_test.neg.integ := by rw [hpos_toReal, hneg_toReal]
    _ = hf_test.integ := by rfl
    _ = hf.realAbsolutelyIntegrable.integ := by
      have : hf.realAbsolutelyIntegrable = hf_test := Subsingleton.elim _ _
      rw [this]

/-- The unit cell of the integer lattice: the preimage of `[n, n+1)` under the real-coordinate map. -/
noncomputable abbrev cell (n : ℤ) : Set (EuclideanSpace' 1) := {x | ⌊EuclideanSpace'.equiv_Real x⌋ = n}

lemma cell_eq_box (n : ℤ) : cell n = (BoundedInterval.Ico (n : ℝ) ((n : ℝ) + 1) : Box 1).toSet := by
  ext x
  change ⌊EuclideanSpace'.equiv_Real x⌋ = n ↔ x ∈ (BoundedInterval.Ico (n : ℝ) ((n : ℝ) + 1) : Box 1).toSet
  rw [Box.mem_toSet]
  constructor
  · intro hx i
    have hi : i = ⟨0, by simp⟩ := by
      apply Fin.ext
      simp
    rw [hi]
    have hfl : ⌊EuclideanSpace'.equiv_Real x⌋ = n := hx
    rw [Int.floor_eq_iff] at hfl
    exact ⟨hfl.1, by simpa using hfl.2⟩
  · intro hx
    have hx0 : (EuclideanSpace'.equiv_Real x) ∈ Set.Ico (n : ℝ) ((n : ℝ) + 1) := by
      exact hx ⟨0, by simp⟩
    rw [Int.floor_eq_iff]
    exact ⟨hx0.1, by simpa using hx0.2⟩

lemma cell_measurable (n : ℤ) : LebesgueMeasurable (cell n) := by
  rw [cell_eq_box]
  exact (IsElementary.box (BoundedInterval.Ico (n : ℝ) ((n : ℝ) + 1) : Box 1)).measurable

lemma cell_measure (n : ℤ) : Lebesgue_measure (cell n) = 1 := by
  rw [cell_eq_box]
  unfold Lebesgue_measure
  rw [Lebesgue_outer_measure.elementary _ (IsElementary.box _)]
  rw [IsElementary.measure_of_box]
  simp only [Box.volume, BoundedInterval.length]
  norm_num

lemma cells_cover : (⋃ n : ℤ, cell n) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨⌊EuclideanSpace'.equiv_Real x⌋, rfl⟩

lemma cells_disjoint : Set.univ.PairwiseDisjoint (cell : ℤ → Set (EuclideanSpace' 1)) := by
  intro n hn m hm hne
  change Disjoint (cell n) (cell m)
  rw [Set.disjoint_left]
  intro x hxn hxm
  exact hne (hxn.symm.trans hxm)

lemma RealSimpleFunction.zero {d:ℕ} : RealSimpleFunction (0 : EuclideanSpace' d → ℝ) := by
  use 0, fun i => Fin.elim0 i, fun i => Fin.elim0 i
  constructor
  · intro i; exact Fin.elim0 i
  · funext x; simp

lemma RealSimpleFunction.sum {d:ℕ} {ι : Type*} (s : Finset ι) {f : ι → EuclideanSpace' d → ℝ}
    (hf : ∀ i ∈ s, RealSimpleFunction (f i)) : RealSimpleFunction (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
      exact RealSimpleFunction.zero
  | insert i s his ih =>
      rw [Finset.sum_insert his]
      exact RealSimpleFunction.add (hf i (Finset.mem_insert_self i s))
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

lemma ComplexSimpleFunction.zero {d:ℕ} : ComplexSimpleFunction (0 : EuclideanSpace' d → ℂ) := by
  use 0, fun i => Fin.elim0 i, fun i => Fin.elim0 i
  constructor
  · intro i; exact Fin.elim0 i
  · funext x; simp

lemma ComplexSimpleFunction.sum {d:ℕ} {ι : Type*} (s : Finset ι) {f : ι → EuclideanSpace' d → ℂ}
    (hf : ∀ i ∈ s, ComplexSimpleFunction (f i)) : ComplexSimpleFunction (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
      exact ComplexSimpleFunction.zero
  | insert i s his ih =>
      rw [Finset.sum_insert his]
      exact ComplexSimpleFunction.add (hf i (Finset.mem_insert_self i s))
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/-- A real function defined on integer steps is measurable. -/
lemma RealMeasurable.floor {a : ℤ → ℝ} : RealMeasurable (fun x => a ⌊EuclideanSpace'.equiv_Real x⌋) := by
  let g : ℕ → EuclideanSpace' 1 → ℝ := fun N => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a n • (cell n).indicator'
  use g
  constructor
  · intro N
    have h_single : ∀ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), RealSimpleFunction (a n • (cell n).indicator') := fun n hn => by
      use 1, fun _ => a n, fun _ => cell n
      constructor
      · intro i; exact cell_measurable n
      · funext x
        simp [Pi.smul_apply, smul_eq_mul]
    simpa [g] using RealSimpleFunction.sum (Finset.Icc (-(N : ℤ)) (N : ℤ)) h_single
  · intro x
    let m : ℤ := ⌊EuclideanSpace'.equiv_Real x⌋
    have h_eventual : ∀ᶠ N in Filter.atTop, g N x = a m := by
      refine Filter.eventually_atTop.mpr ?_
      refine ⟨Int.natAbs m, ?_⟩
      intro N hN
      have hmem : m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
        simp only [Finset.mem_Icc]
        have h1 : |m| ≤ (Int.natAbs m : ℤ) := by rw [Int.abs_eq_natAbs]
        have h2 : (Int.natAbs m : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
        exact abs_le.mp (le_trans h1 h2)
      have h_sum : (∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a n • (cell n).indicator' x) = a m := by
        have h_term : ∀ n, a n • (cell n).indicator' x = if n = m then a m else 0 := fun n => by
          by_cases hnm : n = m
          · subst hnm
            have hxm : x ∈ cell m := by
              show ⌊EuclideanSpace'.equiv_Real x⌋ = m
              rfl
            simp [smul_eq_mul, Set.indicator'_of_mem hxm]
          · have hx' : x ∉ cell n := by
              intro hx
              exact hnm (hx.symm.trans (by rfl : ⌊EuclideanSpace'.equiv_Real x⌋ = m))
            simp [smul_eq_mul, Set.indicator'_of_notMem hx', hnm]
        rw [Finset.sum_congr rfl (fun n hn => h_term n)]
        simp [hmem]
      simpa [g, Finset.sum_apply] using h_sum
    have h_eq : (fun N : ℕ => g N x) =ᶠ[Filter.atTop] (fun _ : ℕ => a m) := by
      exact h_eventual
    exact Filter.Tendsto.congr' h_eq.symm tendsto_const_nhds

/-- A complex function defined on integer steps is measurable. -/
lemma ComplexMeasurable.floor {a : ℤ → ℂ} : ComplexMeasurable (fun x => a ⌊EuclideanSpace'.equiv_Real x⌋) := by
  let g : ℕ → EuclideanSpace' 1 → ℂ := fun N => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a n • Complex.indicator (cell n)
  use g
  constructor
  · intro N
    have h_single : ∀ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ComplexSimpleFunction (a n • Complex.indicator (cell n)) := fun n hn => by
      use 1, fun _ => a n, fun _ => cell n
      constructor
      · intro i; exact cell_measurable n
      · funext x
        simp [Pi.smul_apply, smul_eq_mul]
    simpa [g] using ComplexSimpleFunction.sum (Finset.Icc (-(N : ℤ)) (N : ℤ)) h_single
  · intro x
    let m : ℤ := ⌊EuclideanSpace'.equiv_Real x⌋
    have h_eventual : ∀ᶠ N in Filter.atTop, g N x = a m := by
      refine Filter.eventually_atTop.mpr ?_
      refine ⟨Int.natAbs m, ?_⟩
      intro N hN
      have hmem : m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
        simp only [Finset.mem_Icc]
        have h1 : |m| ≤ (Int.natAbs m : ℤ) := by rw [Int.abs_eq_natAbs]
        have h2 : (Int.natAbs m : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
        exact abs_le.mp (le_trans h1 h2)
      have h_sum : (∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a n • Complex.indicator (cell n) x) = a m := by
        have h_term : ∀ n, a n • Complex.indicator (cell n) x = if n = m then a m else 0 := fun n => by
          by_cases hnm : n = m
          · subst hnm
            have hxm : x ∈ cell m := by
              show ⌊EuclideanSpace'.equiv_Real x⌋ = m
              rfl
            simp [smul_eq_mul, Complex.indicator, Real.complex_fun, Set.indicator'_of_mem hxm]
          · have hx' : x ∉ cell n := by
              intro hx
              exact hnm (hx.symm.trans (by rfl : ⌊EuclideanSpace'.equiv_Real x⌋ = m))
            simp [smul_eq_mul, Complex.indicator, Real.complex_fun, Set.indicator'_of_notMem hx', hnm]
        rw [Finset.sum_congr rfl (fun n hn => h_term n)]
        simp [hmem]
      simpa [g, Finset.sum_apply] using h_sum
    have h_eq : (fun N : ℕ => g N x) =ᶠ[Filter.atTop] (fun _ : ℕ => a m) := by
      exact h_eventual
    exact Filter.Tendsto.congr' h_eq.symm tendsto_const_nhds

lemma UnsignedSimpleFunction.zero {d:ℕ} : UnsignedSimpleFunction (0 : EuclideanSpace' d → EReal) := by
  use 0, fun i => Fin.elim0 i, fun i => Fin.elim0 i
  constructor
  · intro i; exact Fin.elim0 i
  · funext x; simp

lemma UnsignedSimpleFunction.sum {d:ℕ} {ι : Type*} (s : Finset ι) {f : ι → EuclideanSpace' d → EReal}
    (hf : ∀ i ∈ s, UnsignedSimpleFunction (f i)) : UnsignedSimpleFunction (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
      exact UnsignedSimpleFunction.zero
  | insert i s his ih =>
      rw [Finset.sum_insert his]
      exact UnsignedSimpleFunction.add (hf i (Finset.mem_insert_self i s))
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

lemma UnsignedSimpleFunction.measurable {d:ℕ} {f : EuclideanSpace' d → EReal} (hf : UnsignedSimpleFunction f) (huns : Unsigned f) : UnsignedMeasurable f := by
  exact ⟨huns, fun _ => f, fun _ => hf, fun _ => tendsto_const_nhds⟩

lemma UnsignedMeasurable.zero {d:ℕ} : UnsignedMeasurable (0 : EuclideanSpace' d → EReal) := by
  exact ⟨fun x => le_rfl, fun _ => 0, fun _ => UnsignedSimpleFunction.zero, fun _ => tendsto_const_nhds⟩

/-- Countable subadditivity of Lebesgue outer measure, ℤ-indexed. -/
lemma outer_measure_union_le_int {d : ℕ} (E : ℤ → Set (EuclideanSpace' d)) :
    Lebesgue_outer_measure (⋃ i : ℤ, E i) ≤ ∑' i, Lebesgue_outer_measure (E i) := by
  let f : ℕ → Set (EuclideanSpace' d) := fun j => E (Equiv.intEquivNat.symm j)
  have h_union : (⋃ i : ℤ, E i) = ⋃ j : ℕ, f j := by
    ext x
    constructor
    · intro hx
      rw [Set.mem_iUnion] at hx
      rcases hx with ⟨i, hi⟩
      rw [Set.mem_iUnion]
      exact ⟨Equiv.intEquivNat i, by simpa [f] using hi⟩
    · intro hx
      rw [Set.mem_iUnion] at hx
      rcases hx with ⟨j, hj⟩
      rw [Set.mem_iUnion]
      exact ⟨Equiv.intEquivNat.symm j, by simpa [f] using hj⟩
  calc
    Lebesgue_outer_measure (⋃ i : ℤ, E i) = Lebesgue_outer_measure (⋃ j : ℕ, f j) := by rw [h_union]
    _ ≤ ∑' j, Lebesgue_outer_measure (f j) := Lebesgue_outer_measure.union_le f
    _ = ∑' i, Lebesgue_outer_measure (E i) := by
      simpa [f] using (Equiv.intEquivNat.tsum_eq (fun j : ℕ => Lebesgue_outer_measure (E (Equiv.intEquivNat.symm j)))).symm

/-- A nonneg EReal tsum equals the coercion of the corresponding ENNReal tsum. -/
lemma EReal.tsum_eq_ennreal_of_nonneg {α : Type*} {f : α → EReal} (hf : ∀ a, 0 ≤ f a) :
    (∑' a, f a) = ((∑' a, (f a).toENNReal : ENNReal) : EReal) := by
  calc
    (∑' a, f a) = ∑' a, ((f a).toENNReal : EReal) := tsum_congr (fun a => (EReal.coe_toENNReal (hf a)).symm)
    _ = ((∑' a, (f a).toENNReal : ENNReal) : EReal) := by
      let φ : ENNReal →+ EReal := {
        toFun := (↑·)
        map_zero' := by simp
        map_add' := EReal.coe_ennreal_add
      }
      exact (Summable.map_tsum (f := fun a => (f a).toENNReal) ENNReal.summable φ continuous_coe_ennreal_ereal).symm

/-- {name}`toENNReal` commutes with tsums of nonneg EReal values. -/
lemma EReal.toENNReal_tsum_of_nonneg {α : Type*} {f : α → EReal} (hf : ∀ a, 0 ≤ f a) :
    (∑' a, f a).toENNReal = ∑' a, (f a).toENNReal := by
  rw [EReal.tsum_eq_ennreal_of_nonneg hf]
  exact EReal.toENNReal_coe

/-- {name}`toENNReal` commutes with finite sums of nonneg EReal values. -/
lemma EReal.toENNReal_sum_of_nonneg {α : Type*} (s : Finset α) {f : α → EReal}
    (hf : ∀ a ∈ s, 0 ≤ f a) : (∑ a ∈ s, f a).toENNReal = ∑ a ∈ s, (f a).toENNReal := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
      rw [Finset.sum_insert has, Finset.sum_insert has]
      rw [EReal.toENNReal_add (hf a (Finset.mem_insert_self a s))
        (Finset.sum_nonneg (fun b hb => hf b (Finset.mem_insert_of_mem hb)))]
      rw [ih (fun b hb => hf b (Finset.mem_insert_of_mem hb))]

/-- The Lebesgue measure of a set is at most the sum over all unit cells of the
    measures of its intersections with the cells (cells cover the space). -/
lemma measure_le_tsum_cells {E : Set (EuclideanSpace' 1)} :
    Lebesgue_measure E ≤ ∑' n : ℤ, Lebesgue_measure (E ∩ cell n) := by
  have h_eq : E = ⋃ n : ℤ, (E ∩ cell n) := by
    ext x
    constructor
    · intro hx
      rw [Set.mem_iUnion]
      have hx_cells : x ∈ (⋃ n : ℤ, cell n) := by rw [cells_cover]; trivial
      rw [Set.mem_iUnion] at hx_cells
      rcases hx_cells with ⟨n, hn⟩
      exact ⟨n, hx, hn⟩
    · intro hx
      rw [Set.mem_iUnion] at hx
      rcases hx with ⟨n, hn⟩
      exact hn.1
  calc
    Lebesgue_measure E = Lebesgue_outer_measure (⋃ n : ℤ, E ∩ cell n) := by
      rw [← h_eq]; rfl
    _ ≤ ∑' n, Lebesgue_outer_measure (E ∩ cell n) := outer_measure_union_le_int (fun n => E ∩ cell n)
    _ = ∑' n, Lebesgue_measure (E ∩ cell n) := by
      simp [Lebesgue_measure]

/-- For each unit cell {lit}`cell n`, the simple-function contribution restricted to that
    cell is at most {lit}`|a n|` (since the simple function is ≤ |a∘floor| pointwise, and
    on the cell the floor equals {lit}`n`). -/
lemma cell_sum_le_b {b : ℤ → ℝ} (hb : ∀ n, 0 ≤ b n) {k : ℕ} {c : Fin k → EReal} {E : Fin k → Set (EuclideanSpace' 1)}
    (hmes : ∀ i, LebesgueMeasurable (E i) ∧ c i ≥ 0)
    (hg_le : ∀ x, (∑ i, c i • EReal.indicator (E i) x) ≤ (b ⌊EuclideanSpace'.equiv_Real x⌋).toEReal) :
    ∀ n : ℤ, (∑ i, c i * Lebesgue_measure (E i ∩ cell n)) ≤ (b n).toEReal := by
  intro n
  let g_n : EuclideanSpace' 1 → EReal := fun x => ∑ i, c i * EReal.indicator (E i ∩ cell n) x
  have hg_n : UnsignedSimpleFunction g_n := by
    use k, c, fun i => E i ∩ cell n
    constructor
    · intro i
      exact ⟨LebesgueMeasurable.inter (hmes i).1 (cell_measurable n), (hmes i).2⟩
    · ext x
      simp [g_n, Pi.smul_apply, smul_eq_mul]
  have hg_n_eq : g_n = ∑ i, (c i) • (EReal.indicator (E i ∩ cell n)) := by
    ext x
    simp [g_n, Pi.smul_apply, smul_eq_mul]
  have hg_n_integ : hg_n.integ = ∑ i, c i * Lebesgue_measure (E i ∩ cell n) := by
    rw [UnsignedSimpleFunction.integral_eq hg_n (k := k) (c := c) (E := fun i => E i ∩ cell n)
      (hmes := fun i => LebesgueMeasurable.inter (hmes i).1 (cell_measurable n))
      (hnonneg := fun i => (hmes i).2) (heq := hg_n_eq)]
  let u_n : EuclideanSpace' 1 → EReal := fun x => (b n).toEReal * EReal.indicator (cell n) x
  have hu_n : UnsignedSimpleFunction u_n := by
    use 1, (fun _ : Fin 1 => (b n).toEReal), (fun _ : Fin 1 => cell n)
    constructor
    · intro i
      exact ⟨cell_measurable n, EReal.coe_nonneg.mpr (hb n)⟩
    · ext x
      simp [u_n, Pi.smul_apply, smul_eq_mul]
  have hu_n_eq : u_n = ∑ i : Fin 1, ((b n).toEReal) • (EReal.indicator (cell n)) := by
    ext x
    simp [u_n, Pi.smul_apply, smul_eq_mul]
  have hu_n_integ : hu_n.integ = (b n).toEReal := by
    rw [UnsignedSimpleFunction.integral_eq hu_n (k := 1)
      (c := fun _ : Fin 1 => (b n).toEReal) (E := fun _ : Fin 1 => cell n)
      (hmes := fun i => cell_measurable n) (hnonneg := fun i => EReal.coe_nonneg.mpr (hb n))
      (heq := hu_n_eq)]
    rw [cell_measure n]
    simp
  have h_pw : ∀ x, g_n x ≤ u_n x := by
    intro x
    by_cases hx : x ∈ cell n
    · have hx_floor : ⌊EuclideanSpace'.equiv_Real x⌋ = n := hx
      have h_ind : ∀ i, EReal.indicator (E i ∩ cell n) x = EReal.indicator (E i) x := by
        intro i
        by_cases hxi : x ∈ E i
        · have hx_inter : x ∈ E i ∩ cell n := ⟨hxi, hx⟩
          simp [EReal.indicator_of_mem hx_inter, EReal.indicator_of_mem hxi]
        · have hx_not_inter : x ∉ E i ∩ cell n := fun h => hxi h.1
          simp [EReal.indicator_of_notMem hx_not_inter, EReal.indicator_of_notMem hxi]
      calc
        g_n x = (∑ i, c i • EReal.indicator (E i)) x := by
          simp [g_n, h_ind, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        _ ≤ (b ⌊EuclideanSpace'.equiv_Real x⌋).toEReal := by
          simpa [Finset.sum_apply, Pi.smul_apply] using hg_le x
        _ = (b n).toEReal := by
          congr
        _ = u_n x := by
          simp [u_n, EReal.indicator_of_mem hx]
    · have hx_not : ∀ i, x ∉ E i ∩ cell n := fun i h => hx h.2
      have hg_n_zero : g_n x = 0 := by
        have h0 : ∀ i, c i * EReal.indicator (E i ∩ cell n) x = 0 := fun i => by
          simp [EReal.indicator_of_notMem (hx_not i)]
        simp [g_n, h0]
      have hu_n_zero : u_n x = 0 := by
        simp [u_n, EReal.indicator_of_notMem hx]
      rw [hg_n_zero, hu_n_zero]
  have h_integ_le : hg_n.integ ≤ hu_n.integ :=
    UnsignedSimpleFunction.integral_le_integral_of_aeLe hg_n hu_n (AlmostAlways.ofAlways h_pw)
  calc
    (∑ i, c i * Lebesgue_measure (E i ∩ cell n)) = hg_n.integ := hg_n_integ.symm
    _ ≤ hu_n.integ := h_integ_le
    _ = (b n).toEReal := hu_n_integ

/-- Assemble: the finite sum {lit}`∑ i, c i * measure (E i)` is bounded by
    {lit}`∑' n, b n`, using the measure-vs-cells split and the per-cell bound. All work is
    done in ENNReal where tsum manipulation is unconditional. -/
lemma sum_le_tsum_of_cells {b : ℤ → EReal} (hb : ∀ n, 0 ≤ b n)
    {k : ℕ} {c : Fin k → EReal} (hc : ∀ i, 0 ≤ c i)
    {E : Fin k → Set (EuclideanSpace' 1)}
    (hmeas : ∀ i, Lebesgue_measure (E i) ≤ ∑' n, Lebesgue_measure (E i ∩ cell n))
    (hcell : ∀ n, (∑ i, c i * Lebesgue_measure (E i ∩ cell n)) ≤ b n) :
    (∑ i, c i * Lebesgue_measure (E i)) ≤ ∑' n, b n := by
  let M : EReal := ∑ i, c i * Lebesgue_measure (E i)
  have hM_nn : 0 ≤ M := by
    dsimp [M]
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (hc i) (Lebesgue_outer_measure.nonneg (E i))
  -- per-term bound in ENNReal
  have hperterm : ∀ i, (c i * Lebesgue_measure (E i)).toENNReal ≤
      ∑' n, (c i * Lebesgue_measure (E i ∩ cell n)).toENNReal := by
    intro i
    calc
      (c i * Lebesgue_measure (E i)).toENNReal
          = (c i).toENNReal * (Lebesgue_measure (E i)).toENNReal :=
            EReal.toENNReal_mul' (Lebesgue_outer_measure.nonneg (E i))
      _ ≤ (c i).toENNReal * (∑' n, Lebesgue_measure (E i ∩ cell n)).toENNReal := by
          exact mul_le_mul_right (EReal.toENNReal_le_toENNReal (hmeas i)) (c i).toENNReal
      _ = (c i).toENNReal * (∑' n, (Lebesgue_measure (E i ∩ cell n)).toENNReal) := by
          simp [Lebesgue_measure, EReal.toENNReal_tsum_of_nonneg (fun n => Lebesgue_outer_measure.nonneg _)]
      _ = ∑' n, (c i).toENNReal * (Lebesgue_measure (E i ∩ cell n)).toENNReal := by
          rw [ENNReal.tsum_mul_left]
      _ = ∑' n, (c i * Lebesgue_measure (E i ∩ cell n)).toENNReal := by
          refine tsum_congr (fun n => ?_)
          exact (EReal.toENNReal_mul' (Lebesgue_outer_measure.nonneg _)).symm
  have hA : M.toENNReal ≤ ∑' n, (b n).toENNReal := by
    calc
      M.toENNReal = ∑ i, (c i * Lebesgue_measure (E i)).toENNReal := by
        dsimp [M]
        exact EReal.toENNReal_sum_of_nonneg Finset.univ
          (fun i hi => mul_nonneg (hc i) (Lebesgue_outer_measure.nonneg (E i)))
      _ ≤ ∑ i, (∑' n, (c i * Lebesgue_measure (E i ∩ cell n)).toENNReal) := by
          exact Finset.sum_le_sum (fun i hi => hperterm i)
      _ = ∑' n, (∑ i, (c i * Lebesgue_measure (E i ∩ cell n)).toENNReal) := by
          let γ : Fin k → ℤ → ENNReal := fun i n => (c i * Lebesgue_measure (E i ∩ cell n)).toENNReal
          calc
            ∑ i, ∑' n, γ i n = ∑' i : Fin k, ∑' n, γ i n := by simp
            _ = ∑' n, ∑' i : Fin k, γ i n := (ENNReal.tsum_comm (f := fun (n : ℤ) (i : Fin k) => γ i n)).symm
            _ = ∑' n, ∑ i, γ i n := by simp
      _ ≤ ∑' n, (b n).toENNReal := by
          exact ENNReal.tsum_le_tsum (fun n => by
            calc
              ∑ i, (c i * Lebesgue_measure (E i ∩ cell n)).toENNReal
                  = (∑ i, c i * Lebesgue_measure (E i ∩ cell n)).toENNReal := by
                    exact (EReal.toENNReal_sum_of_nonneg Finset.univ
                      (f := fun i => c i * Lebesgue_measure (E i ∩ cell n))
                      (fun i hi => mul_nonneg (hc i) (Lebesgue_outer_measure.nonneg _))).symm
              _ ≤ (b n).toENNReal := EReal.toENNReal_le_toENNReal (hcell n))
  have hT_nn : 0 ≤ ∑' n, b n := by
    apply tsum_nonneg
    exact hb
  calc
    (∑ i, c i * Lebesgue_measure (E i)) = M := rfl
    _ = (M.toENNReal : EReal) := (EReal.coe_toENNReal hM_nn).symm
    _ ≤ ((∑' n, (b n).toENNReal : ENNReal) : EReal) :=
        EReal.coe_ennreal_le_coe_ennreal_iff.mpr hA
    _ = ∑' n, b n := (EReal.tsum_eq_ennreal_of_nonneg hb).symm

/-- The Lebesgue integral of |a∘floor| is at most the tsum of |a n|. -/
 lemma floor_integral_le_tsum_b {b : ℤ → ℝ} (hb : ∀ n, 0 ≤ b n) :
     UnsignedLebesgueIntegral (fun x => (b ⌊EuclideanSpace'.equiv_Real x⌋).toEReal) ≤ ∑' n, (b n).toEReal := by
   let B : ℤ → EReal := fun n => (b n).toEReal
   rw [UnsignedLebesgueIntegral, LowerUnsignedLebesgueIntegral]
   apply sSup_le
   intro R hR
   rcases hR with ⟨g, hg, hg_le⟩
   have hR_eq' : R = hg.integ := (hg_le 0).2
   rw [hR_eq']
   have hg' : UnsignedSimpleFunction g := hg
   rcases hg' with ⟨k, c, E, hmes, heq⟩
   have hinteg : hg.integ = ∑ i, c i * Lebesgue_measure (E i) :=
     UnsignedSimpleFunction.integral_eq hg (k := k) (c := c) (E := E)
       (hmes := fun i => (hmes i).1) (hnonneg := fun i => (hmes i).2) (heq := heq)
   rw [hinteg]
   exact sum_le_tsum_of_cells (b := B)
     (fun n => EReal.coe_nonneg.mpr (hb n))
     (fun i => (hmes i).2)
     (fun i => measure_le_tsum_cells)
     (cell_sum_le_b (b := b) hb (k := k) (c := c) (E := E) hmes (fun x => by
       simpa [heq, Finset.sum_apply, Pi.smul_apply] using (hg_le x).1))

/-- A finite partial sum of |b n| is at most the integral of b∘floor. -/
lemma partial_sum_le_floor_integral_b {b : ℤ → ℝ} (hb : ∀ n, 0 ≤ b n)
    (h_f_meas : UnsignedMeasurable (fun x => (b ⌊EuclideanSpace'.equiv_Real x⌋).toEReal)) (F : Finset ℤ) :
    (∑ n ∈ F, (b n).toEReal) ≤ UnsignedLebesgueIntegral (fun x => (b ⌊EuclideanSpace'.equiv_Real x⌋).toEReal) := by
  let f : EuclideanSpace' 1 → EReal := fun x => (b ⌊EuclideanSpace'.equiv_Real x⌋).toEReal
  let term (n : ℤ) : EuclideanSpace' 1 → EReal := fun x => (b n).toEReal • EReal.indicator (cell n) x
  have h_term_simple (n : ℤ) : UnsignedSimpleFunction (term n) := by
    have h := UnsignedSimpleFunction.indicator (cell_measurable n)
    simpa [term] using h.smul (EReal.coe_nonneg.mpr (hb n))
  have h_term_meas (n : ℤ) : UnsignedMeasurable (term n) := by
    apply UnsignedSimpleFunction.measurable (h_term_simple n)
    intro x
    simp only [term]
    exact mul_nonneg (EReal.coe_nonneg.mpr (hb n)) (EReal.indicator_nonneg (cell n) x)
  have h_sum_meas (s : Finset ℤ) : UnsignedMeasurable (∑ n ∈ s, term n) := by
    classical
    induction s using Finset.induction_on with
    | empty =>
        simpa using UnsignedMeasurable.zero
    | insert n s his ih =>
        rw [Finset.sum_insert his]
        exact UnsignedMeasurable.add (h_term_meas n) ih
  have h_add_meas (n : ℤ) (s : Finset ℤ) : UnsignedMeasurable (term n + ∑ m ∈ s, term m) := by
    exact UnsignedMeasurable.add (h_term_meas n) (h_sum_meas s)
  have h_term_integ (n : ℤ) : LowerUnsignedLebesgueIntegral (term n) = (b n).toEReal := by
    have h_ind_meas : UnsignedMeasurable (EReal.indicator (cell n)) := by
      exact UnsignedSimpleFunction.measurable (UnsignedSimpleFunction.indicator (cell_measurable n)) (by intro x; exact EReal.indicator_nonneg (cell n) x)
    have h_ind_integ : LowerUnsignedLebesgueIntegral (EReal.indicator (cell n)) = 1 := by
      have h : LowerUnsignedLebesgueIntegral (Real.toEReal ∘ (cell n).indicator') = 1 := by
        rw [LowerUnsignedLebesgueIntegral.eq_simpleIntegral (UnsignedSimpleFunction.indicator (cell_measurable n))]
        rw [UnsignedSimpleFunction.integral_indicator (cell_measurable n)]
        exact cell_measure n
      simpa [EReal.indicator, Real.EReal_fun, Function.comp_apply] using h
    have h := LowerUnsignedLebesgueIntegral.hom h_ind_meas (hb n)
    simpa [term, h_ind_integ] using h
  have h_sum_integral : LowerUnsignedLebesgueIntegral (∑ n ∈ F, term n) = ∑ n ∈ F, (b n).toEReal := by
    classical
    induction F using Finset.induction_on with
    | empty =>
        simp [Finset.sum_empty]
        rw [LowerUnsignedLebesgueIntegral.eq_simpleIntegral UnsignedSimpleFunction.zero]
        have h_zero : (UnsignedSimpleFunction.zero : UnsignedSimpleFunction (0 : EuclideanSpace' 1 → EReal)).integ = 0 := by
          have heq : (0 : EuclideanSpace' 1 → EReal) = ∑ i : Fin 0, (Fin.elim0 i : EReal) • EReal.indicator (Fin.elim0 i : Set (EuclideanSpace' 1)) := by
            funext x; simp
          rw [UnsignedSimpleFunction.integral_eq UnsignedSimpleFunction.zero (k := 0) (c := fun i => Fin.elim0 i) (E := fun i => Fin.elim0 i)
            (hmes := fun i => Fin.elim0 i) (hnonneg := fun i => Fin.elim0 i) (heq := heq)]
          simp
        exact h_zero
    | insert n F' hnin ih =>
        rw [Finset.sum_insert hnin]
        rw [LowerUnsignedLebesgueIntegral.add (h_term_meas n) (h_sum_meas F') (h_add_meas n F')]
        rw [ih, h_term_integ]
        rw [Finset.sum_insert hnin]
  have h_le : ∀ x, (∑ n ∈ F, term n) x ≤ f x := by
    intro x
    let m : ℤ := ⌊EuclideanSpace'.equiv_Real x⌋
    have h_term_val : ∀ n ∈ F, term n x = if n = m then (b m).toEReal else 0 := fun n hn => by
      by_cases hnm : n = m
      · subst hnm
        have hxm : x ∈ cell m := by
          show ⌊EuclideanSpace'.equiv_Real x⌋ = m
          rfl
        simp [term, EReal.indicator_of_mem hxm]
      · have hx' : x ∉ cell n := by
          intro hx
          exact hnm (hx.symm.trans (by rfl : ⌊EuclideanSpace'.equiv_Real x⌋ = m))
        simp [term, EReal.indicator_of_notMem hx', hnm]
    have h_sum_le : (∑ n ∈ F, term n x) ≤ (b m).toEReal := by
      rw [Finset.sum_congr rfl (fun n hn => h_term_val n hn)]
      by_cases hm : m ∈ F
      · simp [hm]
      · simp [hm]
        exact hb m
    simpa [f, Finset.sum_apply] using h_sum_le
  calc (∑ n ∈ F, (b n).toEReal) = LowerUnsignedLebesgueIntegral (∑ n ∈ F, term n) := h_sum_integral.symm
    _ ≤ LowerUnsignedLebesgueIntegral f := by
        apply LowerUnsignedLebesgueIntegral.mono (h_sum_meas F) h_f_meas
        exact AlmostAlways.ofAlways h_le
    _ = UnsignedLebesgueIntegral (fun x => (b ⌊EuclideanSpace'.equiv_Real x⌋).toEReal) := by
        rw [show f = fun x => (b ⌊EuclideanSpace'.equiv_Real x⌋).toEReal from rfl]
        rfl

/-- The Lebesgue integral of b∘floor is at least the tsum of b n. -/
lemma tsum_le_floor_integral_b {b : ℤ → ℝ} (hb : ∀ n, 0 ≤ b n)
    (h_f_meas : UnsignedMeasurable (fun x => (b ⌊EuclideanSpace'.equiv_Real x⌋).toEReal)) :
    (∑' n, (b n).toEReal) ≤ UnsignedLebesgueIntegral (fun x => (b ⌊EuclideanSpace'.equiv_Real x⌋).toEReal) := by
  let e : ℕ ≃ ℤ := Equiv.intEquivNat.symm
  have h_reindex : (∑' n, (b n).toEReal) = ∑' m : ℕ, (b (e m)).toEReal := by
    exact ((Equiv.intEquivNat.symm).tsum_eq (fun n : ℤ => (b n).toEReal)).symm
  rw [h_reindex]
  apply EReal.tsum_le_of_sum_range_le_of_nonneg
  · intro m
    exact EReal.coe_nonneg.mpr (hb _)
  · intro N
    have h_img : (∑ i ∈ Finset.range N, (b (e i)).toEReal) = ∑ n ∈ Finset.image e (Finset.range N), (b n).toEReal := by
      symm
      apply Finset.sum_image
      intro x hx y hy hxy
      exact e.injective hxy
    rw [h_img]
    exact partial_sum_le_floor_integral_b hb h_f_meas (Finset.image e (Finset.range N))

/-- Exercise 1.3.21 (Absolute summability is a special case of absolute integrability)-/
theorem AbsolutelySummable.realAbsolutelyIntegrable_iff {a: ℤ → ℝ} : ∑' n, |a n|.toEReal < ⊤ ↔ RealAbsolutelyIntegrable (fun x ↦ a ⌊EuclideanSpace'.equiv_Real x⌋) := by
  have hb : ∀ n, 0 ≤ |a n| := fun n => abs_nonneg _
  have h_abs_meas : UnsignedMeasurable (fun x => (|a ⌊EuclideanSpace'.equiv_Real x⌋|).toEReal) := by
    constructor
    · intro x
      exact EReal.coe_nonneg.mpr (abs_nonneg _)
    · obtain ⟨g_seq, hg_simple, hg_conv⟩ := RealMeasurable.floor (a := a)
      use fun n => EReal.abs_fun (g_seq n)
      constructor
      · intro n; exact (hg_simple n).abs
      · intro x
        simp only [EReal.abs_fun, Real.norm_eq_abs]
        exact (continuous_coe_real_ereal.comp continuous_norm).continuousAt.tendsto.comp (hg_conv x)
  constructor
  · intro hsum
    constructor
    · exact RealMeasurable.floor
    · exact lt_of_le_of_lt (by simpa [EReal.abs_fun, Real.norm_eq_abs] using floor_integral_le_tsum_b (b := fun n => |a n|) hb) hsum
  · intro hf
    exact lt_of_le_of_lt (tsum_le_floor_integral_b (b := fun n => |a n|) hb h_abs_meas)
      (by simpa [EReal.abs_fun, Real.norm_eq_abs] using hf.2)

theorem AbsolutelySummable.complexAbsolutelyIntegrable_iff {a: ℤ → ℂ} : ∑' n, ‖a n‖.toEReal < ⊤ ↔ ComplexAbsolutelyIntegrable (fun x ↦ a ⌊EuclideanSpace'.equiv_Real x⌋) := by
  have hb : ∀ n, 0 ≤ ‖a n‖ := fun n => norm_nonneg _
  have h_abs_meas : UnsignedMeasurable (fun x => (‖a ⌊EuclideanSpace'.equiv_Real x⌋‖).toEReal) := by
    constructor
    · intro x
      exact EReal.coe_nonneg.mpr (norm_nonneg _)
    · obtain ⟨g_seq, hg_simple, hg_conv⟩ := ComplexMeasurable.floor (a := a)
      use fun n => EReal.abs_fun (g_seq n)
      constructor
      · intro n; exact (hg_simple n).abs
      · intro x
        simp only [EReal.abs_fun]
        exact (continuous_coe_real_ereal.comp continuous_norm).continuousAt.tendsto.comp (hg_conv x)
  constructor
  · intro hsum
    constructor
    · exact ComplexMeasurable.floor
    · exact lt_of_le_of_lt (by simpa [EReal.abs_fun] using floor_integral_le_tsum_b (b := fun n => ‖a n‖) hb) hsum
  · intro hf
    exact lt_of_le_of_lt (tsum_le_floor_integral_b (b := fun n => ‖a n‖) hb h_abs_meas)
      (by simpa [EReal.abs_fun] using hf.2)

/-- Lemma 1.3.19 (Triangle inequality) -/

-- Helper: |∫f| ≤ ∫|f| for real absolutely integrable functions
lemma RealAbsolutelyIntegrable.abs_integ_le {d:ℕ} {f: EuclideanSpace' d → ℝ}
    (hf: RealAbsolutelyIntegrable f) : |hf.integ| ≤ hf.abs.integ := by
  simp only [RealAbsolutelyIntegrable.integ, UnsignedAbsolutelyIntegrable.integ]
  have h_pos_nonneg := EReal.toReal_nonneg (UnsignedLebesgueIntegral.nonneg hf.pos.1)
  have h_neg_nonneg := EReal.toReal_nonneg (UnsignedLebesgueIntegral.nonneg hf.neg.1)
  -- |a - b| ≤ a + b when a, b ≥ 0
  have h_abs_ineq : |(UnsignedLebesgueIntegral (EReal.pos_fun f)).toReal -
                     (UnsignedLebesgueIntegral (EReal.neg_fun f)).toReal| ≤
                    (UnsignedLebesgueIntegral (EReal.pos_fun f)).toReal +
                    (UnsignedLebesgueIntegral (EReal.neg_fun f)).toReal := by
    rw [abs_le]; constructor <;> linarith
  -- pos_fun + neg_fun = abs_fun pointwise
  have h_eq_pointwise : ∀ x, EReal.pos_fun f x + EReal.neg_fun f x = EReal.abs_fun f x := fun x => by
    simp only [EReal.pos_fun, EReal.neg_fun, EReal.abs_fun, ← EReal.coe_add]
    congr 1; rw [max_zero_add_max_neg_zero_eq_abs_self, Real.norm_eq_abs]
  have h_sum : UnsignedLebesgueIntegral (EReal.pos_fun f) + UnsignedLebesgueIntegral (EReal.neg_fun f) =
               UnsignedLebesgueIntegral (EReal.abs_fun f) := by
    have h_eq_fun : EReal.pos_fun f + EReal.neg_fun f = EReal.abs_fun f := funext h_eq_pointwise
    rw [← h_eq_fun]; symm
    apply LowerUnsignedLebesgueIntegral.add hf.pos.1 hf.neg.1
    rw [h_eq_fun]; exact hf.abs.1
  have h_pos_ne_top := hf.pos.2.ne_top
  have h_neg_ne_top := hf.neg.2.ne_top
  have h_pos_ne_bot := ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (UnsignedLebesgueIntegral.nonneg hf.pos.1))
  have h_neg_ne_bot := ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (UnsignedLebesgueIntegral.nonneg hf.neg.1))
  calc |(UnsignedLebesgueIntegral (EReal.pos_fun f)).toReal -
        (UnsignedLebesgueIntegral (EReal.neg_fun f)).toReal|
      ≤ (UnsignedLebesgueIntegral (EReal.pos_fun f)).toReal +
        (UnsignedLebesgueIntegral (EReal.neg_fun f)).toReal := h_abs_ineq
    _ = (UnsignedLebesgueIntegral (EReal.pos_fun f) + UnsignedLebesgueIntegral (EReal.neg_fun f)).toReal := by
        rw [EReal.toReal_add h_pos_ne_top h_pos_ne_bot h_neg_ne_top h_neg_ne_bot]
    _ = (UnsignedLebesgueIntegral (EReal.abs_fun f)).toReal := by rw [h_sum]

-- Helper: ∫|Re(f)| ≤ ∫|f| for complex absolutely integrable functions
lemma ComplexAbsolutelyIntegrable.re_abs_integ_le {d:ℕ} {f: EuclideanSpace' d → ℂ}
    (hf: ComplexAbsolutelyIntegrable f) : hf.re.abs.integ ≤ hf.abs.integ := by
  simp only [UnsignedAbsolutelyIntegrable.integ]
  have h_le_pointwise : ∀ x, EReal.abs_fun (Complex.re_fun f) x ≤ EReal.abs_fun f x := fun x => by
    simp only [EReal.abs_fun, Complex.re_fun, EReal.coe_le_coe_iff, Real.norm_eq_abs]
    exact Complex.abs_re_le_norm (f x)
  have h_mono := LowerUnsignedLebesgueIntegral.mono hf.re.abs.1 hf.abs.1 (AlmostAlways.ofAlways h_le_pointwise)
  have h_re_ne_bot := ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (UnsignedLebesgueIntegral.nonneg hf.re.abs.1))
  exact EReal.toReal_le_toReal h_mono h_re_ne_bot hf.abs.2.ne_top

-- Key identity for pos/neg parts under addition
-- (f+g)⁺ + f⁻ + g⁻ = f⁺ + g⁺ + (f+g)⁻
lemma Real.pos_neg_add_identity (a b : ℝ) :
    max (a + b) 0 + max (-a) 0 + max (-b) 0 =
    max a 0 + max b 0 + max (-(a + b)) 0 := by
  rcases le_or_gt a 0 with ha | ha <;> rcases le_or_gt b 0 with hb | hb
  · have hab : a + b ≤ 0 := add_nonpos ha hb
    rw [max_eq_right hab, max_eq_right ha, max_eq_right hb,
        max_eq_left (neg_nonneg.mpr ha), max_eq_left (neg_nonneg.mpr hb),
        max_eq_left (neg_nonneg.mpr hab)]
    ring
  · rcases le_or_gt (a + b) 0 with hab | hab
    · rw [max_eq_right hab, max_eq_right ha, max_eq_left (le_of_lt hb),
          max_eq_left (neg_nonneg.mpr ha), max_eq_right (neg_nonpos.mpr (le_of_lt hb)),
          max_eq_left (neg_nonneg.mpr hab)]
      ring
    · rw [max_eq_left (le_of_lt hab), max_eq_right ha, max_eq_left (le_of_lt hb),
          max_eq_left (neg_nonneg.mpr ha), max_eq_right (neg_nonpos.mpr (le_of_lt hb)),
          max_eq_right (neg_nonpos.mpr (le_of_lt hab))]
      ring
  · rcases le_or_gt (a + b) 0 with hab | hab
    · rw [max_eq_right hab, max_eq_left (le_of_lt ha), max_eq_right hb,
          max_eq_right (neg_nonpos.mpr (le_of_lt ha)), max_eq_left (neg_nonneg.mpr hb),
          max_eq_left (neg_nonneg.mpr hab)]
      ring
    · rw [max_eq_left (le_of_lt hab), max_eq_left (le_of_lt ha), max_eq_right hb,
          max_eq_right (neg_nonpos.mpr (le_of_lt ha)), max_eq_left (neg_nonneg.mpr hb),
          max_eq_right (neg_nonpos.mpr (le_of_lt hab))]
      ring
  · have hab : 0 < a + b := add_pos ha hb
    rw [max_eq_left (le_of_lt hab), max_eq_left (le_of_lt ha), max_eq_left (le_of_lt hb),
        max_eq_right (neg_nonpos.mpr (le_of_lt ha)), max_eq_right (neg_nonpos.mpr (le_of_lt hb)),
        max_eq_right (neg_nonpos.mpr (le_of_lt hab))]
    ring

lemma EReal.pos_neg_add_identity {X: Type*} (f g : X → ℝ) :
    EReal.pos_fun (f + g) + EReal.neg_fun f + EReal.neg_fun g =
    EReal.pos_fun f + EReal.pos_fun g + EReal.neg_fun (f + g) := by
  funext x
  simp only [EReal.pos_fun, EReal.neg_fun, Pi.add_apply]
  have h := Real.pos_neg_add_identity (f x) (g x)
  simp only [← EReal.coe_add, h]

-- Key lemmas about pos_fun and neg_fun under scaling
lemma EReal.pos_fun_smul_nonneg {X: Type*} (f: X → ℝ) (c: ℝ) (hc: 0 ≤ c) :
    EReal.pos_fun (c • f) = (c : EReal) • EReal.pos_fun f := by
  funext x
  simp only [EReal.pos_fun, Pi.smul_apply, smul_eq_mul]
  congr 1
  rw [← mul_zero c, (mul_max_of_nonneg (f x) 0 hc).symm, mul_zero]

lemma EReal.neg_fun_smul_nonneg {X: Type*} (f: X → ℝ) (c: ℝ) (hc: 0 ≤ c) :
    EReal.neg_fun (c • f) = (c : EReal) • EReal.neg_fun f := by
  funext x
  simp only [EReal.neg_fun, Pi.smul_apply, smul_eq_mul]
  congr 1
  rw [show -(c * f x) = c * (-f x) from by ring]
  rw [← mul_zero c, (mul_max_of_nonneg (-f x) 0 hc).symm, mul_zero]

lemma EReal.pos_fun_smul_neg {X: Type*} (f: X → ℝ) (c: ℝ) (hc: c < 0) :
    EReal.pos_fun (c • f) = ((-c) : EReal) • EReal.neg_fun f := by
  funext x
  simp only [EReal.pos_fun, EReal.neg_fun, Pi.smul_apply, smul_eq_mul]
  have hnc : 0 ≤ -c := neg_nonneg.mpr (le_of_lt hc)
  congr 1
  rw [show c * f x = (-c) * (-f x) from by ring]
  rw [← mul_zero (-c), (mul_max_of_nonneg (-f x) 0 hnc).symm, mul_zero]

lemma EReal.neg_fun_smul_neg {X: Type*} (f: X → ℝ) (c: ℝ) (hc: c < 0) :
    EReal.neg_fun (c • f) = ((-c) : EReal) • EReal.pos_fun f := by
  funext x
  simp only [EReal.pos_fun, EReal.neg_fun, Pi.smul_apply, smul_eq_mul]
  have hnc : 0 ≤ -c := neg_nonneg.mpr (le_of_lt hc)

  congr 1
  rw [show -(c * f x) = (-c) * f x from by ring]
  rw [← mul_zero (-c), (mul_max_of_nonneg (f x) 0 hnc).symm, mul_zero]

-- Helper: scalar multiplication linearity for real integral
lemma RealAbsolutelyIntegrable.integ_smul' {d:ℕ} {f: EuclideanSpace' d → ℝ}
    (hf: RealAbsolutelyIntegrable f) (c: ℝ) : (hf.smul c).integ = c * hf.integ := by
  simp only [RealAbsolutelyIntegrable.integ, UnsignedAbsolutelyIntegrable.integ]
  by_cases hc : 0 ≤ c
  · -- Case c ≥ 0
    have h_pos : EReal.pos_fun (c • f) = (c : EReal) • EReal.pos_fun f := EReal.pos_fun_smul_nonneg f c hc
    have h_neg : EReal.neg_fun (c • f) = (c : EReal) • EReal.neg_fun f := EReal.neg_fun_smul_nonneg f c hc
    have h_pos_scale : UnsignedLebesgueIntegral (EReal.pos_fun (c • f)) = c * UnsignedLebesgueIntegral (EReal.pos_fun f) := by
      simp only [UnsignedLebesgueIntegral, h_pos]
      exact LowerUnsignedLebesgueIntegral.hom hf.pos.1 hc
    have h_neg_scale : UnsignedLebesgueIntegral (EReal.neg_fun (c • f)) = c * UnsignedLebesgueIntegral (EReal.neg_fun f) := by
      simp only [UnsignedLebesgueIntegral, h_neg]
      exact LowerUnsignedLebesgueIntegral.hom hf.neg.1 hc
    rw [h_pos_scale, h_neg_scale, EReal.toReal_mul, EReal.toReal_mul, EReal.toReal_coe]
    ring
  · -- Case c < 0
    push_neg at hc
    have h_pos : EReal.pos_fun (c • f) = ((-c) : EReal) • EReal.neg_fun f := EReal.pos_fun_smul_neg f c hc
    have h_neg : EReal.neg_fun (c • f) = ((-c) : EReal) • EReal.pos_fun f := EReal.neg_fun_smul_neg f c hc
    have hnc : 0 ≤ -c := neg_nonneg.mpr (le_of_lt hc)
    have h_pos_scale : UnsignedLebesgueIntegral (EReal.pos_fun (c • f)) = (-c) * UnsignedLebesgueIntegral (EReal.neg_fun f) := by
      simp only [UnsignedLebesgueIntegral, h_pos]
      exact LowerUnsignedLebesgueIntegral.hom hf.neg.1 hnc
    have h_neg_scale : UnsignedLebesgueIntegral (EReal.neg_fun (c • f)) = (-c) * UnsignedLebesgueIntegral (EReal.pos_fun f) := by
      simp only [UnsignedLebesgueIntegral, h_neg]
      exact LowerUnsignedLebesgueIntegral.hom hf.pos.1 hnc
    rw [h_pos_scale, h_neg_scale]
    have : (-↑c : EReal) = ↑(-c) := rfl
    simp only [EReal.toReal_mul, this, EReal.toReal_coe]
    ring

-- Helper: addition linearity for real integral
lemma RealAbsolutelyIntegrable.integ_add' {d:ℕ} {f g: EuclideanSpace' d → ℝ}
    (hf: RealAbsolutelyIntegrable f) (hg: RealAbsolutelyIntegrable g) :
    (hf.add hg).integ = hf.integ + hg.integ := by
  simp only [RealAbsolutelyIntegrable.integ, UnsignedAbsolutelyIntegrable.integ]

  have h_id := EReal.pos_neg_add_identity f g

  -- Measurability
  have hpos_fg := (hf.add hg).pos.1
  have hneg_fg := (hf.add hg).neg.1
  have hpos_f := hf.pos.1
  have hneg_f := hf.neg.1
  have hpos_g := hg.pos.1
  have hneg_g := hg.neg.1

  -- Finiteness: ne_top
  have hpos_fg_ne_top := (hf.add hg).pos.2.ne_top
  have hneg_fg_ne_top := (hf.add hg).neg.2.ne_top
  have hpos_f_ne_top := hf.pos.2.ne_top
  have hneg_f_ne_top := hf.neg.2.ne_top
  have hpos_g_ne_top := hg.pos.2.ne_top
  have hneg_g_ne_top := hg.neg.2.ne_top

  -- Nonnegativity → not bot
  have hpos_fg_ne_bot := ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (UnsignedLebesgueIntegral.nonneg hpos_fg))
  have hneg_fg_ne_bot := ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (UnsignedLebesgueIntegral.nonneg hneg_fg))
  have hpos_f_ne_bot := ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (UnsignedLebesgueIntegral.nonneg hpos_f))
  have hneg_f_ne_bot := ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (UnsignedLebesgueIntegral.nonneg hneg_f))
  have hpos_g_ne_bot := ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (UnsignedLebesgueIntegral.nonneg hpos_g))
  have hneg_g_ne_bot := ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (UnsignedLebesgueIntegral.nonneg hneg_g))

  simp only [UnsignedLebesgueIntegral] at *

  -- Apply integral additivity to the pointwise identity
  have h_lhs_add1 := LowerUnsignedLebesgueIntegral.add hpos_fg hneg_f
                       (UnsignedMeasurable.add hpos_fg hneg_f)
  have h_lhs_add2 := LowerUnsignedLebesgueIntegral.add
                       (UnsignedMeasurable.add hpos_fg hneg_f) hneg_g
                       (UnsignedMeasurable.add (UnsignedMeasurable.add hpos_fg hneg_f) hneg_g)
  have h_rhs_add1 := LowerUnsignedLebesgueIntegral.add hpos_f hpos_g
                       (UnsignedMeasurable.add hpos_f hpos_g)
  have h_rhs_add2 := LowerUnsignedLebesgueIntegral.add
                       (UnsignedMeasurable.add hpos_f hpos_g) hneg_fg
                       (UnsignedMeasurable.add (UnsignedMeasurable.add hpos_f hpos_g) hneg_fg)

  -- From the identity, integrals are equal
  have h_integ_eq : LowerUnsignedLebesgueIntegral (EReal.pos_fun (f + g)) +
                    LowerUnsignedLebesgueIntegral (EReal.neg_fun f) +
                    LowerUnsignedLebesgueIntegral (EReal.neg_fun g) =
                    LowerUnsignedLebesgueIntegral (EReal.pos_fun f) +
                    LowerUnsignedLebesgueIntegral (EReal.pos_fun g) +
                    LowerUnsignedLebesgueIntegral (EReal.neg_fun (f + g)) := by
    rw [← h_lhs_add1, ← h_lhs_add2, ← h_rhs_add1, ← h_rhs_add2, h_id]

  -- Convert to Real arithmetic
  have h1 : (LowerUnsignedLebesgueIntegral (EReal.pos_fun (f + g)) +
             LowerUnsignedLebesgueIntegral (EReal.neg_fun f) +
             LowerUnsignedLebesgueIntegral (EReal.neg_fun g)).toReal =
            (LowerUnsignedLebesgueIntegral (EReal.pos_fun f) +
             LowerUnsignedLebesgueIntegral (EReal.pos_fun g) +
             LowerUnsignedLebesgueIntegral (EReal.neg_fun (f + g))).toReal := by
    rw [h_integ_eq]

  -- Expand toReal_add using the finiteness conditions
  have hsum1_ne_top := EReal.add_ne_top hpos_fg_ne_top hneg_f_ne_top
  have hsum1_ne_bot := EReal.add_ne_bot_iff.mpr ⟨hpos_fg_ne_bot, hneg_f_ne_bot⟩
  have hsum2_ne_top := EReal.add_ne_top hpos_f_ne_top hpos_g_ne_top
  have hsum2_ne_bot := EReal.add_ne_bot_iff.mpr ⟨hpos_f_ne_bot, hpos_g_ne_bot⟩

  rw [EReal.toReal_add hsum1_ne_top hsum1_ne_bot hneg_g_ne_top hneg_g_ne_bot,
      EReal.toReal_add hpos_fg_ne_top hpos_fg_ne_bot hneg_f_ne_top hneg_f_ne_bot] at h1
  rw [EReal.toReal_add hsum2_ne_top hsum2_ne_bot hneg_fg_ne_top hneg_fg_ne_bot,
      EReal.toReal_add hpos_f_ne_top hpos_f_ne_bot hpos_g_ne_top hpos_g_ne_bot] at h1

  linarith

lemma ComplexAbsolutelyIntegrable.integ_add {d:ℕ} {f g : EuclideanSpace' d → ℂ}
    (hf : ComplexAbsolutelyIntegrable f) (hg : ComplexAbsolutelyIntegrable g) :
    (hf.add hg).integ = hf.integ + hg.integ := by
  simp only [ComplexAbsolutelyIntegrable.integ]
  have h_re_fun : Complex.re_fun (f + g) = Complex.re_fun f + Complex.re_fun g := by
    funext x
    simp only [Complex.re_fun, Pi.add_apply]
    rw [Complex.add_re]
  have h_im_fun : Complex.im_fun (f + g) = Complex.im_fun f + Complex.im_fun g := by
    funext x
    simp only [Complex.im_fun, Pi.add_apply]
    rw [Complex.add_im]
  have h_re_integ : (hf.add hg).re.integ = (hf.re.add hg.re).integ := by
    simp only [RealAbsolutelyIntegrable.integ, UnsignedAbsolutelyIntegrable.integ, h_re_fun]
  have h_im_integ : (hf.add hg).im.integ = (hf.im.add hg.im).integ := by
    simp only [RealAbsolutelyIntegrable.integ, UnsignedAbsolutelyIntegrable.integ, h_im_fun]
  rw [h_re_integ, h_im_integ]
  rw [RealAbsolutelyIntegrable.integ_add' (hf := hf.re) (hg := hg.re),
      RealAbsolutelyIntegrable.integ_add' (hf := hf.im) (hg := hg.im)]
  rw [Complex.ofReal_add, Complex.ofReal_add]
  ring

/-- Conjugation commutes with the complex Lebesgue integral. -/

-- Helper: subtraction linearity for real integral
lemma RealAbsolutelyIntegrable.integ_sub' {d:ℕ} {f g: EuclideanSpace' d → ℝ}
    (hf: RealAbsolutelyIntegrable f) (hg: RealAbsolutelyIntegrable g) :
    (hf.sub hg).integ = hf.integ - hg.integ := by
  -- f - g = f + (-1) • g pointwise
  have heq : f - g = f + (-1 : ℝ) • g := by funext x; simp [sub_eq_add_neg]
  -- The integral depends only on function values
  have h_integ_eq : (hf.sub hg).integ = (hf.add (hg.smul (-1 : ℝ))).integ := by
    simp only [RealAbsolutelyIntegrable.integ, UnsignedAbsolutelyIntegrable.integ, heq]
  rw [h_integ_eq, RealAbsolutelyIntegrable.integ_add' (hf := hf) (hg := hg.smul _),
      RealAbsolutelyIntegrable.integ_smul' (hf := hg)]
  ring

-- Helper: scalar multiplication linearity for complex integral
lemma ComplexAbsolutelyIntegrable.integ_smul {d:ℕ} {f: EuclideanSpace' d → ℂ}
    (hf: ComplexAbsolutelyIntegrable f) (c: ℂ) : (hf.smul c).integ = c * hf.integ := by
  -- Expand the definition of complex integral
  simp only [ComplexAbsolutelyIntegrable.integ]
  -- Goal: (hf.smul c).re.integ + I * (hf.smul c).im.integ =
  --       c * (hf.re.integ + I * hf.im.integ)

  -- The function equalities (pointwise)
  have h_re_fun : Complex.re_fun (c • f) = c.re • Complex.re_fun f - c.im • Complex.im_fun f := by
    funext x
    simp only [Complex.re_fun, Complex.im_fun, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Complex.mul_re]
  have h_im_fun : Complex.im_fun (c • f) = c.re • Complex.im_fun f + c.im • Complex.re_fun f := by
    funext x
    simp only [Complex.re_fun, Complex.im_fun, Pi.smul_apply, Pi.add_apply, smul_eq_mul, Complex.mul_im]

  -- Build the decomposed integrability proofs
  have h_re_decomp : RealAbsolutelyIntegrable (c.re • Complex.re_fun f - c.im • Complex.im_fun f) :=
    (hf.re.smul c.re).sub (hf.im.smul c.im)
  have h_im_decomp : RealAbsolutelyIntegrable (c.re • Complex.im_fun f + c.im • Complex.re_fun f) :=
    (hf.im.smul c.re).add (hf.re.smul c.im)

  -- The integrals of (hf.smul c).re and the decomposed form are equal
  -- because they're integrability proofs for the same function
  have h_re_integ : (hf.smul c).re.integ = h_re_decomp.integ := by
    simp only [RealAbsolutelyIntegrable.integ, UnsignedAbsolutelyIntegrable.integ, h_re_fun]
  have h_im_integ : (hf.smul c).im.integ = h_im_decomp.integ := by
    simp only [RealAbsolutelyIntegrable.integ, UnsignedAbsolutelyIntegrable.integ, h_im_fun]

  -- Use linearity of real integral for the decomposed forms
  have h_re_linear : h_re_decomp.integ = c.re * hf.re.integ - c.im * hf.im.integ := by
    rw [show h_re_decomp = (hf.re.smul c.re).sub (hf.im.smul c.im) from rfl]
    rw [RealAbsolutelyIntegrable.integ_sub' (hf := hf.re.smul c.re) (hg := hf.im.smul c.im),
        RealAbsolutelyIntegrable.integ_smul' (hf := hf.re),
        RealAbsolutelyIntegrable.integ_smul' (hf := hf.im)]
  have h_im_linear : h_im_decomp.integ = c.re * hf.im.integ + c.im * hf.re.integ := by
    rw [show h_im_decomp = (hf.im.smul c.re).add (hf.re.smul c.im) from rfl]
    rw [RealAbsolutelyIntegrable.integ_add' (hf := hf.im.smul c.re) (hg := hf.re.smul c.im),
        RealAbsolutelyIntegrable.integ_smul' (hf := hf.im),
        RealAbsolutelyIntegrable.integ_smul' (hf := hf.re)]

  rw [h_re_integ, h_im_integ, h_re_linear, h_im_linear]
  -- Need to simplify the imaginary part of (re_integ + I * im_integ)
  have h_integ_im : (↑hf.re.integ + Complex.I * ↑hf.im.integ : ℂ).im = hf.im.integ := by
    simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
               Complex.ofReal_im]; ring
  have h_integ_re : (↑hf.re.integ + Complex.I * ↑hf.im.integ : ℂ).re = hf.re.integ := by
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
               Complex.ofReal_im]; ring
  -- Now just complex algebra - compare re and im parts
  apply Complex.ext
  · -- Real parts
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
               Complex.ofReal_im, mul_zero, sub_zero, h_integ_im, h_integ_re]
    ring
  · -- Imaginary parts
    simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
               Complex.ofReal_im, mul_zero, zero_add, h_integ_im, h_integ_re]
    ring


lemma AlmostEverywhereEqual.comp {d:ℕ} {X Y : Type*} {f g : EuclideanSpace' d → X}
    (h : AlmostEverywhereEqual f g) (φ : X → Y) : AlmostEverywhereEqual (fun x => φ (f x)) (fun x => φ (g x)) := by
  unfold AlmostEverywhereEqual at *
  exact AlmostAlways.mp h (fun x hx => congrArg φ hx)

/-- A {lean}`PreL1` element whose norm-distance to another is zero has almost everywhere equal functions. -/
lemma PreL1.ae_of_dist_eq_zero {d:ℕ} {F G : PreL1 d} (h : dist F G = 0) : AlmostEverywhereEqual F.f G.f := by
  have hd : dist (SeparationQuotient.mk F : L1 d) (SeparationQuotient.mk G) = 0 := by
    rwa [SeparationQuotient.dist_mk]
  have h' := L1.dist_eq_zero F.f G.f F.integrable G.integrable
  exact (h'.mp hd)

/-- The real Lebesgue integral of two almost everywhere equal functions is equal. -/
lemma RealAbsolutelyIntegrable.integ_of_aeEqual {d:ℕ} {f g : EuclideanSpace' d → ℝ}
    (hf : RealAbsolutelyIntegrable f) (hg : RealAbsolutelyIntegrable g)
    (hae : AlmostEverywhereEqual f g) : hf.integ = hg.integ := by
  simp only [RealAbsolutelyIntegrable.integ, UnsignedAbsolutelyIntegrable.integ]
  have h_ae_pos : AlmostEverywhereEqual (EReal.pos_fun f) (EReal.pos_fun g) :=
    AlmostEverywhereEqual.comp hae (fun y : ℝ => (max y 0).toEReal)
  have h_ae_neg : AlmostEverywhereEqual (EReal.neg_fun f) (EReal.neg_fun g) :=
    AlmostEverywhereEqual.comp hae (fun y : ℝ => (max (-y) 0).toEReal)
  have h_pos_eq : UnsignedLebesgueIntegral (EReal.pos_fun f) = UnsignedLebesgueIntegral (EReal.pos_fun g) :=
    LowerUnsignedLebesgueIntegral.integral_eq_integral_of_aeEqual hf.pos.1 hg.pos.1 h_ae_pos
  have h_neg_eq : UnsignedLebesgueIntegral (EReal.neg_fun f) = UnsignedLebesgueIntegral (EReal.neg_fun g) :=
    LowerUnsignedLebesgueIntegral.integral_eq_integral_of_aeEqual hf.neg.1 hg.neg.1 h_ae_neg
  rw [h_pos_eq, h_neg_eq]

/-- The complex Lebesgue integral of two almost everywhere equal functions is equal. -/
lemma ComplexAbsolutelyIntegrable.integ_of_aeEqual {d:ℕ} {f g : EuclideanSpace' d → ℂ}
    (hf : ComplexAbsolutelyIntegrable f) (hg : ComplexAbsolutelyIntegrable g)
    (hae : AlmostEverywhereEqual f g) : hf.integ = hg.integ := by
  simp only [ComplexAbsolutelyIntegrable.integ]
  have h_ae_re : AlmostEverywhereEqual (Complex.re_fun f) (Complex.re_fun g) :=
    AlmostEverywhereEqual.comp hae Complex.re
  have h_ae_im : AlmostEverywhereEqual (Complex.im_fun f) (Complex.im_fun g) :=
    AlmostEverywhereEqual.comp hae Complex.im
  have h_re_eq : hf.re.integ = hg.re.integ :=
    RealAbsolutelyIntegrable.integ_of_aeEqual hf.re hg.re h_ae_re
  have h_im_eq : hf.im.integ = hg.im.integ :=
    RealAbsolutelyIntegrable.integ_of_aeEqual hf.im hg.im h_ae_im
  rw [h_re_eq, h_im_eq]

/-- Additivity of the complex Lebesgue integral. -/
lemma ComplexAbsolutelyIntegrable.integ_conj {d:ℕ} {f : EuclideanSpace' d → ℂ}
    (hf : ComplexAbsolutelyIntegrable f) : hf.conj.integ = starRingEnd ℂ hf.integ := by
  have h_pt_re : Complex.re_fun (Complex.conj_fun f) = Complex.re_fun f := by
    funext x
    simp [Complex.re_fun, Complex.conj_fun, Complex.conj_re]
  have h_pt_im : Complex.im_fun (Complex.conj_fun f) = (-1 : ℝ) • Complex.im_fun f := by
    funext x
    simp [Complex.im_fun, Complex.conj_fun, Complex.conj_im]
  have h_re_int : hf.conj.re.integ = hf.re.integ := by
    simp only [RealAbsolutelyIntegrable.integ, UnsignedAbsolutelyIntegrable.integ, h_pt_re]
  have h_im_int : hf.conj.im.integ = (hf.im.smul (-1 : ℝ)).integ := by
    simp only [RealAbsolutelyIntegrable.integ, UnsignedAbsolutelyIntegrable.integ, h_pt_im]
  simp only [ComplexAbsolutelyIntegrable.integ]
  rw [h_re_int, h_im_int]
  rw [RealAbsolutelyIntegrable.integ_smul' (hf := hf.im)]
  rw [map_add, map_mul]
  simp [Complex.conj_ofReal, Complex.conj_I]

/-- Exercise 1.3.19 (Integration is linear) -/
noncomputable def L1.integ {d:ℕ} : L1 d →ₗ[ℂ] ℂ := {
  toFun := Quotient.lift (fun F ↦ F.integrable.integ) (by
    intro F G h
    have hdist : dist F G = 0 := Metric.inseparable_iff.mp h
    have hae : AlmostEverywhereEqual F.f G.f := PreL1.ae_of_dist_eq_zero hdist
    exact ComplexAbsolutelyIntegrable.integ_of_aeEqual F.integrable G.integrable hae)
  map_smul' := by
    intro a F
    refine Quotient.inductionOn F ?_
    intro F'
    exact ComplexAbsolutelyIntegrable.integ_smul F'.integrable a
  map_add' := by
    intro F G
    refine Quotient.inductionOn F ?_
    intro F'
    refine Quotient.inductionOn G ?_
    intro G'
    exact ComplexAbsolutelyIntegrable.integ_add F'.integrable G'.integrable
}

noncomputable def L1.conj {d:ℕ} : L1 d → L1 d := Quotient.lift (fun F ↦ (F.conj : L1 d)) (by
  intro F G h
  have hdist : dist F G = 0 := Metric.inseparable_iff.mp h
  have hae : AlmostEverywhereEqual F.f G.f := PreL1.ae_of_dist_eq_zero hdist
  have hae_conj : AlmostEverywhereEqual (Complex.conj_fun F.f) (Complex.conj_fun G.f) :=
    AlmostEverywhereEqual.comp hae (starRingEnd ℂ)
  apply SeparationQuotient.mk_eq_mk.mpr
  rw [Metric.inseparable_iff]
  exact (L1.dist_eq_zero (f := Complex.conj_fun F.f) (g := Complex.conj_fun G.f)
      (hf := F.integrable.conj) (hg := G.integrable.conj)).mpr hae_conj)

theorem L1.integ_conj {d:ℕ} (F: L1 d) : L1.integ (L1.conj F) = starRingEnd ℂ (L1.integ F) := by
  refine Quotient.inductionOn F ?_
  intro F'
  simpa [L1.integ, L1.conj] using ComplexAbsolutelyIntegrable.integ_conj (F'.integrable)

-- Helper: |u*f| integral equals |f| integral when |u| = 1

/-- Indicator of a disjoint union is the sum of indicators. -/
lemma Complex.indicator_union {X:Type*} {E F : Set X} (hdisj : Disjoint E F) :
    Complex.indicator (E ∪ F) = Complex.indicator E + Complex.indicator F := by
  funext x
  rw [Pi.add_apply, Complex.indicator, Complex.indicator, Complex.indicator,
      Real.complex_fun, Real.complex_fun, Real.complex_fun]
  by_cases hxE : x ∈ E
  · have hxF : x ∉ F := Set.disjoint_left.mp hdisj hxE
    rw [Set.indicator'_of_mem (show x ∈ E ∪ F from Or.inl hxE), Set.indicator'_of_mem hxE,
        Set.indicator'_of_notMem hxF]
    simp
  · by_cases hxF : x ∈ F
    · rw [Set.indicator'_of_mem (show x ∈ E ∪ F from Or.inr hxF), Set.indicator'_of_notMem hxE,
        Set.indicator'_of_mem hxF]
      simp
    · rw [Set.indicator'_of_notMem (by intro h; rcases h with hE | hF; exact hxE hE; exact hxF hF),
        Set.indicator'_of_notMem hxE, Set.indicator'_of_notMem hxF]
      simp

/-- Multiplying a complex absolutely integrable function by an indicator of a measurable set
    preserves absolute integrability. -/
lemma ComplexAbsolutelyIntegrable.mul_indicator {d:ℕ} {f : EuclideanSpace' d → ℂ}
    (hf : ComplexAbsolutelyIntegrable f) {E : Set (EuclideanSpace' d)} (hE : LebesgueMeasurable E) :
    ComplexAbsolutelyIntegrable (f * Complex.indicator E) := by
  constructor
  · have h_ind_meas : ComplexMeasurable (Complex.indicator E) :=
      ⟨fun _ => Complex.indicator E, fun _ => ComplexSimpleFunction.indicator hE, fun _ => tendsto_const_nhds⟩
    exact ComplexMeasurable.mul hf.1 h_ind_meas
  · have h_le : ∀ x, EReal.abs_fun (f * Complex.indicator E) x ≤ EReal.abs_fun f x := fun x => by
      simp only [EReal.abs_fun]
      apply EReal.coe_le_coe_iff.mpr
      have hind : ‖Complex.indicator E x‖ ≤ 1 := by
        by_cases hx : x ∈ E
        · simp [Complex.indicator, Real.complex_fun, Set.indicator'_of_mem hx]
        · simp [Complex.indicator, Real.complex_fun, Set.indicator'_of_notMem hx]
      calc ‖(f * Complex.indicator E) x‖ = ‖f x * Complex.indicator E x‖ := rfl
        _ = ‖f x‖ * ‖Complex.indicator E x‖ := norm_mul (f x) (Complex.indicator E x)
        _ ≤ ‖f x‖ * 1 := mul_le_mul_of_nonneg_left hind (norm_nonneg (f x))
        _ = ‖f x‖ := by rw [mul_one]
    have h_abs_meas : UnsignedMeasurable (EReal.abs_fun (f * Complex.indicator E)) := by
      constructor
      · intro x; simp only [EReal.abs_fun]; exact EReal.coe_nonneg.mpr (norm_nonneg _)
      · obtain ⟨g, hg_simple, hg_conv⟩ := ComplexMeasurable.mul hf.1
          ⟨fun _ => Complex.indicator E, fun _ => ComplexSimpleFunction.indicator hE, fun _ => tendsto_const_nhds⟩
        use fun n => EReal.abs_fun (g n)
        constructor
        · intro n; exact (hg_simple n).abs
        · intro x
          simp only [EReal.abs_fun]
          exact (continuous_coe_real_ereal.comp continuous_norm).continuousAt.tendsto.comp (hg_conv x)
    have h_mono : UnsignedLebesgueIntegral (EReal.abs_fun (f * Complex.indicator E)) ≤
                  UnsignedLebesgueIntegral (EReal.abs_fun f) := by
      apply LowerUnsignedLebesgueIntegral.mono h_abs_meas hf.abs.1
      exact AlmostAlways.ofAlways h_le
    exact lt_of_le_of_lt h_mono hf.2

def ComplexAbsolutelyIntegrableOn {d:ℕ} (f: EuclideanSpace' d → ℂ) (E: Set (EuclideanSpace' d)) : Prop := ComplexAbsolutelyIntegrable (f * Complex.indicator E)

noncomputable def ComplexAbsolutelyIntegrableOn.integ {d:ℕ} {f: EuclideanSpace' d → ℂ} {E: Set (EuclideanSpace' d)} (hf: ComplexAbsolutelyIntegrableOn f E) : ℂ :=
  ComplexAbsolutelyIntegrable.integ hf

/-- Exercise 1.3.22 -/
theorem ComplexAbsolutelyIntegrableOn.glue {d:ℕ} {f: EuclideanSpace' d → ℂ} {E F: Set (EuclideanSpace' d)}
    (hE: LebesgueMeasurable E) (hF: LebesgueMeasurable F) (hdisj: Disjoint E F)
    (hf: ComplexAbsolutelyIntegrableOn f (E ∪ F)) :
    ∃ hE : ComplexAbsolutelyIntegrableOn f E, ∃ hF: ComplexAbsolutelyIntegrableOn f F, hf.integ = hE.integ + hF.integ := by
  let hE' : ComplexAbsolutelyIntegrableOn f E := by
    have hfun : f * Complex.indicator E = (f * Complex.indicator (E ∪ F)) * Complex.indicator E := by
      funext x
      by_cases hxE : x ∈ E
      · have hx : x ∈ E ∪ F := Or.inl hxE
        simp [Complex.indicator, Real.complex_fun, Set.indicator'_of_mem hxE, Set.indicator'_of_mem hx]
      · simp [Complex.indicator, Real.complex_fun, Set.indicator'_of_notMem hxE]
    change ComplexAbsolutelyIntegrable (f * Complex.indicator E)
    rw [hfun]
    exact hf.mul_indicator hE
  let hF' : ComplexAbsolutelyIntegrableOn f F := by
    have hfun : f * Complex.indicator F = (f * Complex.indicator (E ∪ F)) * Complex.indicator F := by
      funext x
      by_cases hxF : x ∈ F
      · have hx : x ∈ E ∪ F := Or.inr hxF
        simp [Complex.indicator, Real.complex_fun, Set.indicator'_of_mem hxF, Set.indicator'_of_mem hx]
      · simp [Complex.indicator, Real.complex_fun, Set.indicator'_of_notMem hxF]
    change ComplexAbsolutelyIntegrable (f * Complex.indicator F)
    rw [hfun]
    exact hf.mul_indicator hF
  have h_pointwise : f * Complex.indicator (E ∪ F) = f * Complex.indicator E + f * Complex.indicator F := by
    rw [Complex.indicator_union hdisj]
    funext x
    simp [Pi.mul_apply, Pi.add_apply, mul_add]
  have h_integ_eq : hf.integ = (hE'.add hF').integ := by
    simp only [ComplexAbsolutelyIntegrableOn.integ, ComplexAbsolutelyIntegrable.integ, h_pointwise]
  refine ⟨hE', hF', ?_⟩
  rw [h_integ_eq]
  exact ComplexAbsolutelyIntegrable.integ_add hE' hF'

def ComplexAbsolutelyIntegrableOn.restrict {d:ℕ} {f: EuclideanSpace' d → ℂ} {E F: Set (EuclideanSpace' d)} (hf: ComplexAbsolutelyIntegrableOn f E) (hF: LebesgueMeasurable F): ComplexAbsolutelyIntegrableOn (f * Complex.indicator F) E := by
  change ComplexAbsolutelyIntegrable ((f * Complex.indicator F) * Complex.indicator E)
  have hfun : (f * Complex.indicator F) * Complex.indicator E = (f * Complex.indicator E) * Complex.indicator F := by
    funext x
    simp only [Pi.mul_apply]
    ring
  rw [hfun]
  exact hf.mul_indicator hF

def ComplexAbsolutelyIntegrableOn.mono {d:ℕ} {f: EuclideanSpace' d → ℂ} {E F: Set (EuclideanSpace' d)} (hf: ComplexAbsolutelyIntegrableOn f E) (_hE: LebesgueMeasurable E) (hF: LebesgueMeasurable F) (hsub: F ⊆ E): ComplexAbsolutelyIntegrableOn f F := by
  change ComplexAbsolutelyIntegrable (f * Complex.indicator F)
  have hfun : f * Complex.indicator F = (f * Complex.indicator E) * Complex.indicator F := by
    funext x
    by_cases hxF : x ∈ F
    · have hxE : x ∈ E := hsub hxF
      simp [Complex.indicator, Real.complex_fun, Set.indicator'_of_mem hxF, Set.indicator'_of_mem hxE]
    · simp [Complex.indicator, Real.complex_fun, Set.indicator'_of_notMem hxF]
  rw [hfun]
  exact hf.mul_indicator hF

theorem ComplexAbsolutelyIntegrableOn.integ_restrict {d:ℕ} {f: EuclideanSpace' d → ℂ} {E F: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) (hF: LebesgueMeasurable F) (hsub: F ⊆ E) (hf: ComplexAbsolutelyIntegrableOn f E) : (hf.mono hE hF hsub).integ = (hf.restrict hF).integ:= by
  have hfun : (f * Complex.indicator F) * Complex.indicator E = f * Complex.indicator F := by
    funext x
    by_cases hxF : x ∈ F
    · have hxE : x ∈ E := hsub hxF
      simp [Complex.indicator, Real.complex_fun, Set.indicator'_of_mem hxF, Set.indicator'_of_mem hxE]
    · simp [Complex.indicator, Real.complex_fun, Set.indicator'_of_notMem hxF]
  simp only [ComplexAbsolutelyIntegrableOn.integ, ComplexAbsolutelyIntegrable.integ, hfun]

lemma ComplexAbsolutelyIntegrable.abs_smul_unit {d:ℕ} {f: EuclideanSpace' d → ℂ}
    (hf: ComplexAbsolutelyIntegrable f) (c: ℂ) (hc: ‖c‖ = 1) :
    (hf.smul c).abs.integ = hf.abs.integ := by
  simp only [UnsignedAbsolutelyIntegrable.integ]
  congr 1; congr 1
  funext x
  simp only [EReal.abs_fun, Pi.smul_apply, smul_eq_mul, norm_mul, hc, one_mul]

-- Helper: integ.re = re.integ for complex absolutely integrable functions
lemma ComplexAbsolutelyIntegrable.integ_re_eq_re_integ {d:ℕ} {f: EuclideanSpace' d → ℂ}
    (hf: ComplexAbsolutelyIntegrable f) : hf.integ.re = hf.re.integ := by
  simp only [ComplexAbsolutelyIntegrable.integ, Complex.add_re, Complex.mul_re,
             Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

-- Main theorem: ‖∫f‖ ≤ ∫|f| for complex absolutely integrable functions
theorem ComplexAbsolutelyIntegrable.abs_le {d:ℕ} {f: EuclideanSpace' d → ℂ}
    (hf: ComplexAbsolutelyIntegrable f) : ‖hf.integ‖ ≤ hf.abs.integ := by
  by_cases h : hf.integ = 0
  · -- Case: ∫f = 0
    simp [h, UnsignedAbsolutelyIntegrable.integ]
    exact EReal.toReal_nonneg (UnsignedLebesgueIntegral.nonneg hf.abs.1)
  · -- Case: ∫f ≠ 0, use rotation trick
    -- Let u = conj(∫f) / ‖∫f‖ (a unit complex number)
    let u : ℂ := starRingEnd ℂ (hf.integ) / ‖hf.integ‖
    have hu_norm : ‖u‖ = 1 := by
      simp only [u, norm_div, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs,
                 abs_of_nonneg (norm_nonneg _)]
      exact div_self (norm_ne_zero_iff.mpr h)
    -- Show u * ∫f = ‖∫f‖ (a real positive number)
    have h_mul : u * hf.integ = ‖hf.integ‖ := by
      simp only [u]
      rw [div_mul_eq_mul_div, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
      push_cast
      rw [sq, mul_div_assoc, div_self, mul_one]
      exact_mod_cast norm_ne_zero_iff.mpr h
    -- By linearity: ∫(u*f) = u * ∫f = ‖∫f‖
    have h_integ_smul : (hf.smul u).integ = u * hf.integ := hf.integ_smul u
    have h_integ_eq : (hf.smul u).integ = ‖hf.integ‖ := by rw [h_integ_smul, h_mul]
    -- So (∫(u*f)).re = ‖∫f‖ and equals (hf.smul u).re.integ
    have h_re : (hf.smul u).integ.re = ‖hf.integ‖ := by rw [h_integ_eq]; simp
    have h_re_integ : (hf.smul u).integ.re = (hf.smul u).re.integ := (hf.smul u).integ_re_eq_re_integ
    have h_norm_eq : (‖hf.integ‖ : ℝ) = (hf.smul u).re.integ := by rw [← h_re, h_re_integ]
    -- Chain of inequalities: ‖∫f‖ = ∫Re(u * f) ≤ ∫|Re(u * f)| ≤ ∫|u*f| = ∫|f|
    calc (‖hf.integ‖ : ℝ)
        = (hf.smul u).re.integ := h_norm_eq
      _ ≤ |(hf.smul u).re.integ| := le_abs_self _
      _ ≤ (hf.smul u).re.abs.integ := (hf.smul u).re.abs_integ_le
      _ ≤ (hf.smul u).abs.integ := (hf.smul u).re_abs_integ_le
      _ = hf.abs.integ := hf.abs_smul_unit u hu_norm
