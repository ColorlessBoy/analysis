import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Basic
/-!
# Analysis I, Section 10.1: Basic definitions

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- API for Mathlib's {name}`HasDerivWithinAt`, {name}`derivWithin`, and {name}`DifferentiableWithinAt`.

Note that the Mathlib conventions differ slightly from that in the text, in that
differentiability is defined even at points that are not limit points of the domain;
derivatives in such cases may not be unique, but {name}`derivWithin` still selects one such
derivative in such cases (or {lean}`0`, if no derivative exists).

-/

namespace Chapter10

variable (x₀ : ℝ)

/-- Definition 10.1.1 (Differentiability at a point).  For the Mathlib notion {name}`HasDerivWithinAt`, the
hypothesis that {name}`x₀` is a limit point is not needed. -/
theorem _root_.HasDerivWithinAt.iff (X: Set ℝ) (x₀ : ℝ) (f: ℝ → ℝ)
  (L:ℝ) :
  HasDerivWithinAt f L X x₀ ↔ (nhdsWithin x₀ (X \ {x₀})).Tendsto (fun x ↦ (f x - f x₀) / (x - x₀))
   (nhds L) :=  by
  rw [hasDerivWithinAt_iff_tendsto_slope, iff_iff_eq, slope_fun_def_field]

theorem _root_.DifferentiableWithinAt.iff (X: Set ℝ) (x₀ : ℝ) (f: ℝ → ℝ) :
  DifferentiableWithinAt ℝ f X x₀ ↔ ∃ L, HasDerivWithinAt f L X x₀ := by
  constructor
  . intro h; use derivWithin f X x₀; exact h.hasDerivWithinAt
  intro ⟨ L, h ⟩; exact h.differentiableWithinAt

theorem _root_.DifferentiableWithinAt.of_hasDeriv {X: Set ℝ} {x₀ : ℝ} {f: ℝ → ℝ} {L:ℝ}
  (hL: HasDerivWithinAt f L X x₀) : DifferentiableWithinAt ℝ f X x₀ := by
  rw [DifferentiableWithinAt.iff]; use L


theorem derivative_unique {X: Set ℝ} {x₀ : ℝ}
  (hx₀: ClusterPt x₀ (.principal (X \ {x₀}))) {f: ℝ → ℝ} {L L':ℝ}
  (hL: HasDerivWithinAt f L X x₀) (hL': HasDerivWithinAt f L' X x₀) :
  L = L' := by
    rw [_root_.HasDerivWithinAt.iff] at hL hL'
    rw [ClusterPt.eq_1] at hx₀
    solve_by_elim [tendsto_nhds_unique]

#check DifferentiableWithinAt.hasDerivWithinAt

theorem derivative_unique' (X: Set ℝ) {x₀ : ℝ}
  (hx₀: ClusterPt x₀ (.principal (X \ {x₀}))) {f: ℝ → ℝ} {L :ℝ}
  (hL: HasDerivWithinAt f L X x₀)
  (hdiff : DifferentiableWithinAt ℝ f X x₀):
  L = derivWithin f X x₀ := by
  solve_by_elim [derivative_unique, DifferentiableWithinAt.hasDerivWithinAt]


/-- Example 10.1.3 -/
example (x₀:ℝ) : HasDerivWithinAt (fun x ↦ x^2) (2 * x₀) .univ x₀ := by
  rw [hasDerivWithinAt_univ]; simpa [pow_one] using hasDerivAt_pow 2 x₀

example (x₀:ℝ) : DifferentiableWithinAt ℝ (fun x ↦ x^2) .univ x₀ := by
  apply HasDerivWithinAt.differentiableWithinAt
  rw [hasDerivWithinAt_univ]; simpa [pow_one] using hasDerivAt_pow 2 x₀

example (x₀:ℝ) : derivWithin (fun x ↦ x^2) .univ x₀ = 2 * x₀ := by
  have h : HasDerivWithinAt (fun x ↦ x^2) (2 * x₀) .univ x₀ := by
    rw [hasDerivWithinAt_univ]; simpa [pow_one] using hasDerivAt_pow 2 x₀
  have huniq : UniqueDiffWithinAt ℝ .univ x₀ := by
    exact uniqueDiffWithinAt_univ
  exact h.derivWithin huniq

/-- Remark 10.1.4 -/
example (X: Set ℝ) (x₀ : ℝ) {f g: ℝ → ℝ} (hfg: f = g):
  DifferentiableWithinAt ℝ f X x₀ ↔ DifferentiableWithinAt ℝ g X x₀ := by rw [hfg]


example (X: Set ℝ) (x₀ : ℝ) {f g: ℝ → ℝ} (L:ℝ) (hfg: f = g):
  HasDerivWithinAt f L X x₀ ↔ HasDerivWithinAt g L X x₀ := by rw [hfg]

example : ∃ (X: Set ℝ) (x₀ :ℝ) (f g: ℝ → ℝ) (L:ℝ) (_hfg: f x₀ = g x₀),
  HasDerivWithinAt f L X x₀ ∧ ¬ HasDerivWithinAt g L X x₀ := by
  refine ⟨.univ, 0, fun _ ↦ 0, fun x ↦ x, 0, by simp, ?_, ?_⟩
  · rw [hasDerivWithinAt_univ]; exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · rw [hasDerivWithinAt_univ]; intro h
    have h_id : HasDerivAt (fun (x : ℝ) ↦ x) (1 : ℝ) (0 : ℝ) :=
      (hasDerivAt_id (𝕜 := ℝ) (0 : ℝ))
    have h' : HasDerivAt (fun (x : ℝ) ↦ x) (0 : ℝ) (0 : ℝ) := h
    have h_eq : (1 : ℝ) = (0 : ℝ) := h_id.unique h'
    linarith

/-- Example 10.1.6 -/

abbrev f_10_1_6 : ℝ → ℝ := abs

example : (nhdsWithin 0 (.Ioi 0)).Tendsto (fun x ↦ (f_10_1_6 x - f_10_1_6 0) / (x - 0)) (nhds 1) := by
  have hpos : ∀ x ∈ Set.Ioi (0 : ℝ), (f_10_1_6 x - f_10_1_6 0) / (x - 0) = 1 := by
    intro x hx
    have hxpos : 0 < x := hx
    simp [f_10_1_6, abs_of_pos hxpos, abs_zero, sub_zero, hxpos.ne', div_self]
  have hmem : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
    refine mem_nhdsWithin.mpr ⟨Set.Ioo (-1 : ℝ) 1, isOpen_Ioo, ?_, ?_⟩
    · exact Set.mem_Ioo.mpr ⟨by norm_num, by norm_num⟩
    · intro x hx; exact Set.mem_Ioo.mpr ⟨hx.2, hx.1.2⟩
  have hpos' : (fun x ↦ (f_10_1_6 x - f_10_1_6 0) / (x - 0)) =ᶠ[nhdsWithin 0 (Set.Ioi 0)] (fun _ ↦ 1) := by
    refine Filter.eventually_of_mem hmem ?_
    intro x hx
    apply hpos x (Set.mem_Ioi.mpr hx.1)
  exact (Filter.Tendsto.congr' hpos'.symm tendsto_const_nhds)

example : (nhdsWithin 0 (.Iio 0)).Tendsto (fun x ↦ (f_10_1_6 x - f_10_1_6 0) / (x - 0)) (nhds (-1)) := by
  have hneg : ∀ x ∈ Set.Iio (0 : ℝ), (f_10_1_6 x - f_10_1_6 0) / (x - 0) = -1 := by
    intro x hx
    have hxneg : x < 0 := hx
    calc
      (f_10_1_6 x - f_10_1_6 0) / (x - 0) = (-x - 0) / (x - 0) := by simp [f_10_1_6, abs_of_neg hxneg, abs_zero]
      _ = -x / x := by ring
      _ = -(x / x) := by ring
      _ = -1 := by simp [hxneg.ne]
  have hmem : Set.Ioo (-1 : ℝ) 0 ∈ nhdsWithin (0 : ℝ) (Set.Iio 0) := by
    refine mem_nhdsWithin.mpr ⟨Set.Ioo (-1 : ℝ) 1, isOpen_Ioo, ?_, ?_⟩
    · exact Set.mem_Ioo.mpr ⟨by norm_num, by norm_num⟩
    · intro x hx; exact Set.mem_Ioo.mpr ⟨hx.1.1, hx.2⟩
  have hneg' : (fun x ↦ (f_10_1_6 x - f_10_1_6 0) / (x - 0)) =ᶠ[nhdsWithin 0 (Set.Iio 0)] (fun _ ↦ -1) := by
    refine Filter.eventually_of_mem hmem ?_
    intro x hx
    apply hneg x (Set.mem_Iio.mpr hx.2)
  exact (Filter.Tendsto.congr' hneg'.symm tendsto_const_nhds)

example : ¬ ∃ L, (nhdsWithin 0 (.univ \ {0})).Tendsto (fun x ↦ (f_10_1_6 x - f_10_1_6 0) / (x - 0))
   (nhds L) := by
  intro h
  rcases h with ⟨L, hL⟩
  have hIoi_sub : Set.Ioi (0 : ℝ) ⊆ Set.univ \ {0} := by
    intro x hx
    have hxpos : 0 < x := hx
    exact ⟨Set.mem_univ x, hxpos.ne'⟩
  have hIio_sub : Set.Iio (0 : ℝ) ⊆ Set.univ \ {0} := by
    intro x hx
    have hxneg : x < 0 := hx
    exact ⟨Set.mem_univ x, hxneg.ne⟩
  have hL_right : (nhdsWithin 0 (.Ioi 0)).Tendsto (fun x ↦ (f_10_1_6 x - f_10_1_6 0) / (x - 0)) (nhds L) :=
    hL.mono_left (nhdsWithin_mono 0 hIoi_sub)
  have hL_left : (nhdsWithin 0 (.Iio 0)).Tendsto (fun x ↦ (f_10_1_6 x - f_10_1_6 0) / (x - 0)) (nhds L) :=
    hL.mono_left (nhdsWithin_mono 0 hIio_sub)
  have h_right_lim : (nhdsWithin 0 (.Ioi 0)).Tendsto (fun x ↦ (f_10_1_6 x - f_10_1_6 0) / (x - 0)) (nhds 1) := by
    have hpos : ∀ x ∈ Set.Ioi (0 : ℝ), (f_10_1_6 x - f_10_1_6 0) / (x - 0) = 1 := by
      intro x hx
      have hxpos : 0 < x := hx
      simp [f_10_1_6, abs_of_pos hxpos, abs_zero, sub_zero, hxpos.ne', div_self]
    have hmem : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
      refine mem_nhdsWithin.mpr ⟨Set.Ioo (-1 : ℝ) 1, isOpen_Ioo, ?_, ?_⟩
      · exact Set.mem_Ioo.mpr ⟨by norm_num, by norm_num⟩
      · intro x hx; exact Set.mem_Ioo.mpr ⟨hx.2, hx.1.2⟩
    have hpos' : (fun x ↦ (f_10_1_6 x - f_10_1_6 0) / (x - 0)) =ᶠ[nhdsWithin 0 (Set.Ioi 0)] (fun _ ↦ 1) := by
      refine Filter.eventually_of_mem hmem ?_
      intro x hx
      apply hpos x (Set.mem_Ioi.mpr hx.1)
    exact (Filter.Tendsto.congr' hpos'.symm tendsto_const_nhds)
  have h_left_lim : (nhdsWithin 0 (.Iio 0)).Tendsto (fun x ↦ (f_10_1_6 x - f_10_1_6 0) / (x - 0)) (nhds (-1)) := by
    have hneg : ∀ x ∈ Set.Iio (0 : ℝ), (f_10_1_6 x - f_10_1_6 0) / (x - 0) = -1 := by
      intro x hx
      have hxneg : x < 0 := hx
      calc
        (f_10_1_6 x - f_10_1_6 0) / (x - 0) = (-x - 0) / (x - 0) := by simp [f_10_1_6, abs_of_neg hxneg, abs_zero]
        _ = -x / x := by ring
        _ = -(x / x) := by ring
        _ = -1 := by simp [hxneg.ne]
    have hmem : Set.Ioo (-1 : ℝ) 0 ∈ nhdsWithin (0 : ℝ) (Set.Iio 0) := by
      refine mem_nhdsWithin.mpr ⟨Set.Ioo (-1 : ℝ) 1, isOpen_Ioo, ?_, ?_⟩
      · exact Set.mem_Ioo.mpr ⟨by norm_num, by norm_num⟩
      · intro x hx; exact Set.mem_Ioo.mpr ⟨hx.1.1, hx.2⟩
    have hneg' : (fun x ↦ (f_10_1_6 x - f_10_1_6 0) / (x - 0)) =ᶠ[nhdsWithin 0 (Set.Iio 0)] (fun _ ↦ -1) := by
      refine Filter.eventually_of_mem hmem ?_
      intro x hx
      apply hneg x (Set.mem_Iio.mpr hx.2)
    exact (Filter.Tendsto.congr' hneg'.symm tendsto_const_nhds)
  have hL_eq_1 : L = 1 := tendsto_nhds_unique hL_right h_right_lim
  have hL_eq_neg1 : L = -1 := tendsto_nhds_unique hL_left h_left_lim
  linarith

example : ¬ DifferentiableWithinAt ℝ f_10_1_6 (.univ) 0 := by
  rw [DifferentiableWithinAt.iff]
  intro h; rcases h with ⟨L, hL⟩
  rw [HasDerivWithinAt.iff] at hL
  have hIoi_sub : Set.Ioi (0 : ℝ) ⊆ Set.univ \ {0} := by
    intro x hx; exact ⟨Set.mem_univ x, (Set.mem_Ioi.mp hx).ne'⟩
  have hIio_sub : Set.Iio (0 : ℝ) ⊆ Set.univ \ {0} := by
    intro x hx; exact ⟨Set.mem_univ x, (Set.mem_Iio.mp hx).ne⟩
  have hL_right : (nhdsWithin 0 (.Ioi 0)).Tendsto (fun x ↦ (f_10_1_6 x - f_10_1_6 0) / (x - 0)) (nhds L) :=
    hL.mono_left (nhdsWithin_mono 0 hIoi_sub)
  have hL_left : (nhdsWithin 0 (.Iio 0)).Tendsto (fun x ↦ (f_10_1_6 x - f_10_1_6 0) / (x - 0)) (nhds L) :=
    hL.mono_left (nhdsWithin_mono 0 hIio_sub)
  haveI : (nhdsWithin (0 : ℝ) (Set.Ioi 0)).NeBot := by
    refine nhdsWithin_neBot.mpr ?_
    intro t ht
    rcases Metric.mem_nhds_iff.mp ht with ⟨ε, hε, h⟩
    set x := ε / 2 with hx_def
    have hx_pos : 0 < x := div_pos hε (by norm_num : (0 : ℝ) < 2)
    have hx_mem_ball : dist x (0 : ℝ) < ε := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hx_pos]
      nlinarith
    exact ⟨x, h (Metric.mem_ball.mpr hx_mem_ball), Set.mem_Ioi.mpr hx_pos⟩
  haveI : (nhdsWithin (0 : ℝ) (Set.Iio 0)).NeBot := by
    refine nhdsWithin_neBot.mpr ?_
    intro t ht
    rcases Metric.mem_nhds_iff.mp ht with ⟨ε, hε, h⟩
    set x := -(ε / 2) with hx_def
    have hx_neg : x < 0 := by
      nlinarith
    have hx_mem_ball : dist x (0 : ℝ) < ε := by
      rw [Real.dist_eq, sub_zero, abs_of_neg hx_neg, neg_neg]
      nlinarith
    exact ⟨x, h (Metric.mem_ball.mpr hx_mem_ball), Set.mem_Iio.mpr hx_neg⟩
  have h_right_lim : (nhdsWithin 0 (.Ioi 0)).Tendsto (fun x ↦ (f_10_1_6 x - f_10_1_6 0) / (x - 0)) (nhds 1) := by
    have hpos : ∀ x ∈ Set.Ioi (0 : ℝ), (f_10_1_6 x - f_10_1_6 0) / (x - 0) = 1 := by
      intro x hx; have hxpos : 0 < x := hx; simp [f_10_1_6, abs_of_pos hxpos, abs_zero, sub_zero, hxpos.ne', div_self]
    have hmem : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
      refine mem_nhdsWithin.mpr ⟨Set.Ioo (-1 : ℝ) 1, isOpen_Ioo, Set.mem_Ioo.mpr ⟨by norm_num, by norm_num⟩, ?_⟩
      intro x hx; exact Set.mem_Ioo.mpr ⟨hx.2, hx.1.2⟩
    have hpos' : (fun x ↦ (f_10_1_6 x - f_10_1_6 0) / (x - 0)) =ᶠ[nhdsWithin 0 (Set.Ioi 0)] (fun _ ↦ 1) := by
      refine Filter.eventually_of_mem hmem ?_; intro x hx; apply hpos x (Set.mem_Ioi.mpr hx.1)
    exact (Filter.Tendsto.congr' hpos'.symm tendsto_const_nhds)
  have h_left_lim : (nhdsWithin 0 (.Iio 0)).Tendsto (fun x ↦ (f_10_1_6 x - f_10_1_6 0) / (x - 0)) (nhds (-1)) := by
    have hneg : ∀ x ∈ Set.Iio (0 : ℝ), (f_10_1_6 x - f_10_1_6 0) / (x - 0) = -1 := by
      intro x hx; have hxneg : x < 0 := hx
      calc
        (f_10_1_6 x - f_10_1_6 0) / (x - 0) = (-x - 0) / (x - 0) := by simp [f_10_1_6, abs_of_neg hxneg, abs_zero]
        _ = -x / x := by simp [sub_zero]
        _ = -(x / x) := by ring
        _ = -1 := by simp [hxneg.ne]
    have hmem : Set.Ioo (-1 : ℝ) 0 ∈ nhdsWithin (0 : ℝ) (Set.Iio 0) := by
      refine mem_nhdsWithin.mpr ⟨Set.Ioo (-1 : ℝ) 1, isOpen_Ioo, Set.mem_Ioo.mpr ⟨by norm_num, by norm_num⟩, ?_⟩
      intro x hx; exact Set.mem_Ioo.mpr ⟨hx.1.1, hx.2⟩
    have hneg' : (fun x ↦ (f_10_1_6 x - f_10_1_6 0) / (x - 0)) =ᶠ[nhdsWithin 0 (Set.Iio 0)] (fun _ ↦ -1) := by
      refine Filter.eventually_of_mem hmem ?_; intro x hx; apply hneg x (Set.mem_Iio.mpr hx.2)
    exact (Filter.Tendsto.congr' hneg'.symm tendsto_const_nhds)
  have hL_eq_1 : L = 1 := tendsto_nhds_unique hL_right h_right_lim
  have hL_eq_neg1 : L = -1 := tendsto_nhds_unique hL_left h_left_lim
  linarith

example : DifferentiableWithinAt ℝ f_10_1_6 (.Ioi 0) 0 := by
  rw [DifferentiableWithinAt.iff]
  refine ⟨1, ?_⟩
  rw [HasDerivWithinAt.iff]
  have h : Set.Ioi (0 : ℝ) \ {0} = Set.Ioi (0 : ℝ) := by
    ext x; constructor <;> intro hx
    · exact hx.1
    · exact ⟨hx, by
        intro hx0; have : x = 0 := hx0; subst this; simp at hx⟩
  rw [h]
  have hpos : ∀ x ∈ Set.Ioi (0 : ℝ), (f_10_1_6 x - f_10_1_6 0) / (x - 0) = 1 := by
    intro x hx; have hxpos : 0 < x := hx; simp [f_10_1_6, abs_of_pos hxpos, abs_zero, sub_zero, hxpos.ne', div_self]
  have hmem : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
    refine mem_nhdsWithin.mpr ⟨Set.Ioo (-1 : ℝ) 1, isOpen_Ioo, Set.mem_Ioo.mpr ⟨by norm_num, by norm_num⟩, ?_⟩
    intro x hx; exact Set.mem_Ioo.mpr ⟨hx.2, hx.1.2⟩
  have hpos' : (fun x ↦ (f_10_1_6 x - f_10_1_6 0) / (x - 0)) =ᶠ[nhdsWithin 0 (Set.Ioi 0)] (fun _ ↦ 1) := by
    refine Filter.eventually_of_mem hmem ?_; intro x hx; apply hpos x (Set.mem_Ioi.mpr hx.1)
  exact (Filter.Tendsto.congr' hpos'.symm tendsto_const_nhds)

example : derivWithin f_10_1_6 (.Ioi 0) 0 = 1 := by
  have h : HasDerivWithinAt f_10_1_6 1 (Set.Ioi (0 : ℝ)) (0 : ℝ) := by
    rw [HasDerivWithinAt.iff]
    have hset : Set.Ioi (0 : ℝ) \ {0} = Set.Ioi (0 : ℝ) := by
      ext x; constructor <;> intro hx
      · exact hx.1
      · exact ⟨hx, by intro hx0; have : x = 0 := hx0; subst this; simp at hx⟩
    rw [hset]
    have hpos : ∀ x ∈ Set.Ioi (0 : ℝ), (f_10_1_6 x - f_10_1_6 0) / (x - 0) = 1 := by
      intro x hx; have hxpos : 0 < x := hx; simp [f_10_1_6, abs_of_pos hxpos, abs_zero, sub_zero, hxpos.ne', div_self]
    have hmem : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
      refine mem_nhdsWithin.mpr ⟨Set.Ioo (-1 : ℝ) 1, isOpen_Ioo, Set.mem_Ioo.mpr ⟨by norm_num, by norm_num⟩, ?_⟩
      intro x hx; exact Set.mem_Ioo.mpr ⟨hx.2, hx.1.2⟩
    have hpos' : (fun x ↦ (f_10_1_6 x - f_10_1_6 0) / (x - 0)) =ᶠ[nhdsWithin 0 (Set.Ioi 0)] (fun _ ↦ 1) := by
      refine Filter.eventually_of_mem hmem ?_; intro x hx; apply hpos x (Set.mem_Ioi.mpr hx.1)
    exact (Filter.Tendsto.congr' hpos'.symm tendsto_const_nhds)
  have huniq : UniqueDiffWithinAt ℝ (Set.Ioi (0 : ℝ)) (0 : ℝ) := uniqueDiffWithinAt_Ioi 0
  exact h.derivWithin huniq

example : DifferentiableWithinAt ℝ f_10_1_6 (.Iio 0) 0 := by
  rw [DifferentiableWithinAt.iff]
  refine ⟨-1, ?_⟩
  rw [HasDerivWithinAt.iff]
  have h : Set.Iio (0 : ℝ) \ {0} = Set.Iio (0 : ℝ) := by
    ext x; constructor <;> intro hx
    · exact hx.1
    · exact ⟨hx, by intro hx0; have : x = 0 := hx0; subst this; simp at hx⟩
  rw [h]
  have hneg : ∀ x ∈ Set.Iio (0 : ℝ), (f_10_1_6 x - f_10_1_6 0) / (x - 0) = -1 := by
    intro x hx; have hxneg : x < 0 := hx
    calc
      (f_10_1_6 x - f_10_1_6 0) / (x - 0) = (-x - 0) / (x - 0) := by simp [f_10_1_6, abs_of_neg hxneg, abs_zero]
      _ = -x / x := by simp [sub_zero]
      _ = -(x / x) := by ring
      _ = -1 := by simp [hxneg.ne]
  have hmem : Set.Ioo (-1 : ℝ) 0 ∈ nhdsWithin (0 : ℝ) (Set.Iio 0) := by
    refine mem_nhdsWithin.mpr ⟨Set.Ioo (-1 : ℝ) 1, isOpen_Ioo, Set.mem_Ioo.mpr ⟨by norm_num, by norm_num⟩, ?_⟩
    intro x hx; exact Set.mem_Ioo.mpr ⟨hx.1.1, hx.2⟩
  have hneg' : (fun x ↦ (f_10_1_6 x - f_10_1_6 0) / (x - 0)) =ᶠ[nhdsWithin 0 (Set.Iio 0)] (fun _ ↦ -1) := by
    refine Filter.eventually_of_mem hmem ?_; intro x hx; apply hneg x (Set.mem_Iio.mpr hx.2)
  exact (Filter.Tendsto.congr' hneg'.symm tendsto_const_nhds)

example : derivWithin f_10_1_6 (.Iio 0) 0 = -1 := by
  have h : HasDerivWithinAt f_10_1_6 (-1) (Set.Iio (0 : ℝ)) (0 : ℝ) := by
    rw [HasDerivWithinAt.iff]
    have hset : Set.Iio (0 : ℝ) \ {0} = Set.Iio (0 : ℝ) := by
      ext x; constructor <;> intro hx
      · exact hx.1
      · exact ⟨hx, by intro hx0; have : x = 0 := hx0; subst this; simp at hx⟩
    rw [hset]
    have hneg : ∀ x ∈ Set.Iio (0 : ℝ), (f_10_1_6 x - f_10_1_6 0) / (x - 0) = -1 := by
      intro x hx; have hxneg : x < 0 := hx
      calc
        (f_10_1_6 x - f_10_1_6 0) / (x - 0) = (-x - 0) / (x - 0) := by simp [f_10_1_6, abs_of_neg hxneg, abs_zero]
        _ = -x / x := by simp [sub_zero]
        _ = -(x / x) := by ring
        _ = -1 := by simp [hxneg.ne]
    have hmem : Set.Ioo (-1 : ℝ) 0 ∈ nhdsWithin (0 : ℝ) (Set.Iio 0) := by
      refine mem_nhdsWithin.mpr ⟨Set.Ioo (-1 : ℝ) 1, isOpen_Ioo, Set.mem_Ioo.mpr ⟨by norm_num, by norm_num⟩, ?_⟩
      intro x hx; exact Set.mem_Ioo.mpr ⟨hx.1.1, hx.2⟩
    have hneg' : (fun x ↦ (f_10_1_6 x - f_10_1_6 0) / (x - 0)) =ᶠ[nhdsWithin 0 (Set.Iio 0)] (fun _ ↦ -1) := by
      refine Filter.eventually_of_mem hmem ?_; intro x hx; apply hneg x (Set.mem_Iio.mpr hx.2)
    exact (Filter.Tendsto.congr' hneg'.symm tendsto_const_nhds)
  have huniq : UniqueDiffWithinAt ℝ (Set.Iio (0 : ℝ)) (0 : ℝ) := uniqueDiffWithinAt_Iio 0
  exact h.derivWithin huniq

/-- Proposition 10.1.7 (Newton's approximation) / Exercise 10.1.2 -/
theorem _root_.HasDerivWithinAt.iff_approx_linear (X: Set ℝ) (x₀ :ℝ) (f: ℝ → ℝ) (L:ℝ) :
  HasDerivWithinAt f L X x₀ ↔
  ∀ ε > 0, ∃ δ > 0, ∀ x ∈ X, |x - x₀| < δ → |f x - f x₀ - L * (x - x₀)| ≤ ε * |x - x₀| := by
  constructor
  · -- direction (→): from derivative existence to ε-δ estimate
    intro h
    rw [HasDerivWithinAt.iff] at h
    have h' : (nhdsWithin x₀ (X \ {x₀})).Tendsto (fun x => (f x - f x₀) / (x - x₀) - L) (nhds 0) := by
      simpa using h.sub (tendsto_const_nhds (x := L))
    have h_eps_delta := Metric.tendsto_nhdsWithin_nhds.mp h'
    intro ε hε
    rcases h_eps_delta ε hε with ⟨δ, hδpos, hδ⟩
    refine ⟨δ, hδpos, ?_⟩
    intro x hx hxδ
    by_cases hx0 : x = x₀
    · subst x; simp
    · have hx_diff : x ∈ X \ {x₀} := ⟨hx, hx0⟩
      have h_div_dist := hδ hx_diff hxδ
      -- dist in ℝ is |· - ·|
      have h_div : |(f x - f x₀) / (x - x₀) - L| < ε := by
        simpa [Real.dist_eq, sub_zero] using h_div_dist
      have hx_nonzero : x - x₀ ≠ 0 := sub_ne_zero.mpr hx0
      have hpos_abs : 0 < |x - x₀| := abs_pos.mpr hx_nonzero
      have h_mul : |(f x - f x₀) / (x - x₀) - L| * |x - x₀| ≤ ε * |x - x₀| := by
        nlinarith
      have h_eq : |f x - f x₀ - L * (x - x₀)| = |(f x - f x₀) / (x - x₀) - L| * |x - x₀| := by
        calc
          |f x - f x₀ - L * (x - x₀)|
              = |(x - x₀) * ((f x - f x₀) / (x - x₀) - L)| := by
            field_simp [hx_nonzero]
          _ = |x - x₀| * |(f x - f x₀) / (x - x₀) - L| := by rw [abs_mul]
          _ = |(f x - f x₀) / (x - x₀) - L| * |x - x₀| := mul_comm _ _
      calc
        |f x - f x₀ - L * (x - x₀)| = |(f x - f x₀) / (x - x₀) - L| * |x - x₀| := h_eq
        _ ≤ ε * |x - x₀| := h_mul
  · -- direction (←): from ε-δ estimate to derivative existence
    intro h
    rw [HasDerivWithinAt.iff]
    have h_eps_delta : ∀ ε > 0, ∃ δ > 0, ∀ x ∈ X \ {x₀}, |x - x₀| < δ → |(f x - f x₀) / (x - x₀) - L| < ε := by
      intro ε hε
      rcases h (ε / 2) (by linarith) with ⟨δ, hδpos, hδ⟩
      refine ⟨δ, hδpos, ?_⟩
      intro x hx hxδ
      rcases hx with ⟨hxX, hx_ne⟩
      have hx_nonzero : x - x₀ ≠ 0 := sub_ne_zero.mpr hx_ne
      have hpos_abs : 0 < |x - x₀| := abs_pos.mpr hx_nonzero
      have h_ineq := hδ x hxX hxδ
      -- convert inequality using algebraic manipulation
      have h_eq : |(f x - f x₀) / (x - x₀) - L| = |f x - f x₀ - L * (x - x₀)| / |x - x₀| := by
        calc
          |(f x - f x₀) / (x - x₀) - L| = |(f x - f x₀ - L * (x - x₀)) / (x - x₀)| := by
            field_simp [hx_nonzero]
          _ = |f x - f x₀ - L * (x - x₀)| / |x - x₀| := by rw [abs_div]
      have h_div_ineq : |(f x - f x₀) / (x - x₀) - L| ≤ ε / 2 := by
        calc
          |(f x - f x₀) / (x - x₀) - L| = |f x - f x₀ - L * (x - x₀)| / |x - x₀| := h_eq
          _ ≤ ((ε / 2) * |x - x₀|) / |x - x₀| :=
            (div_le_div_iff_of_pos_right hpos_abs).mpr h_ineq
          _ = ε / 2 := by field_simp [hpos_abs.ne']
      calc
        |(f x - f x₀) / (x - x₀) - L| ≤ ε / 2 := h_div_ineq
        _ < ε := by linarith
    refine Metric.tendsto_nhdsWithin_nhds.mpr ?_
    intro ε hε
    rcases h_eps_delta ε hε with ⟨δ, hδpos, hδ⟩
    refine ⟨δ, hδpos, ?_⟩
    intro x hx hxδ
    have hx' : x ∈ X \ {x₀} := hx
    have h_abs : |(f x - f x₀) / (x - x₀) - L| < ε := hδ x hx' hxδ
    simpa [Real.dist_eq, sub_zero] using h_abs

/-- Proposition 10.1.10 / Exercise 10.1.3 -/
theorem _root_.ContinuousWithinAt.of_differentiableWithinAt {X: Set ℝ} {x₀ : ℝ} {f: ℝ → ℝ}
  (h: DifferentiableWithinAt ℝ f X x₀) :
  ContinuousWithinAt f X x₀ :=
  h.continuousWithinAt

/-Definition 10.1.11 (Differentiability on a domain)-/
#check DifferentiableOn.eq_1

/-- Corollary 10.1.12 -/
theorem _root_.ContinuousOn.of_differentiableOn {X: Set ℝ} {f: ℝ → ℝ}
  (h: DifferentiableOn ℝ f X) :
  ContinuousOn f X := by
  solve_by_elim [ContinuousWithinAt.of_differentiableWithinAt]

/-- Theorem 10.1.13 (a) (Differential calculus) / Exercise 10.1.4 -/
theorem _root_.HasDerivWithinAt.of_const (X: Set ℝ) (x₀ : ℝ) (c:ℝ) :
  HasDerivWithinAt (fun _ ↦ c) 0 X x₀ := by
  exact hasDerivWithinAt_const x₀ X c

/-- Theorem 10.1.13 (b) (Differential calculus) / Exercise 10.1.4 -/
theorem _root_.HasDerivWithinAt.of_id (X: Set ℝ) (x₀ : ℝ) :
  HasDerivWithinAt (fun x ↦ x) 1 X x₀ := by
  simpa using (hasDerivWithinAt_id x₀ X)

/-- Theorem 10.1.13 (c) (Sum rule) / Exercise 10.1.4 -/
theorem _root_.HasDerivWithinAt.of_add {X: Set ℝ} {x₀ f'x₀ g'x₀: ℝ}
  {f g: ℝ → ℝ} (hf: HasDerivWithinAt f f'x₀ X x₀) (hg: HasDerivWithinAt g g'x₀ X x₀) :
  HasDerivWithinAt (f + g) (f'x₀ + g'x₀) X x₀ := by
  exact hf.add hg

/-- Theorem 10.1.13 (d) (Product rule) / Exercise 10.1.4 -/
theorem _root_.HasDerivWithinAt.of_mul {X: Set ℝ} {x₀ f'x₀ g'x₀: ℝ}
  {f g: ℝ → ℝ} (hf: HasDerivWithinAt f f'x₀ X x₀) (hg: HasDerivWithinAt g g'x₀ X x₀) :
  HasDerivWithinAt (f * g) (f'x₀ * (g x₀) + (f x₀) * g'x₀) X x₀ := by
  exact hf.mul hg

/-- Theorem 10.1.13 (e) (Differential calculus) / Exercise 10.1.4 -/
theorem _root_.HasDerivWithinAt.of_smul {X: Set ℝ} {x₀ f'x₀: ℝ} (c:ℝ)
  {f: ℝ → ℝ} (hf: HasDerivWithinAt f f'x₀ X x₀) :
  HasDerivWithinAt (c • f) (c * f'x₀) X x₀ := by
  exact hf.const_smul c

/-- Theorem 10.1.13 (f) (Difference rule) / Exercise 10.1.4 -/
theorem _root_.HasDerivWithinAt.of_sub {X: Set ℝ} {x₀ f'x₀ g'x₀: ℝ}
  {f g: ℝ → ℝ} (hf: HasDerivWithinAt f f'x₀ X x₀) (hg: HasDerivWithinAt g g'x₀ X x₀) :
  HasDerivWithinAt (f - g) (f'x₀ - g'x₀) X x₀ := by
  exact hf.sub hg

/-- Theorem 10.1.13 (g) (Differential calculus) / Exercise 10.1.4 -/
theorem _root_.HasDerivWithinAt.of_inv {X: Set ℝ} {x₀ g'x₀: ℝ}
  {g: ℝ → ℝ} (hgx₀ : g x₀ ≠ 0) (hg: HasDerivWithinAt g g'x₀ X x₀) :
  HasDerivWithinAt (1/g) (-g'x₀ / (g x₀)^2) X x₀ := by
  have := hg.inv hgx₀
  simpa [div_eq_inv_mul, one_div] using this

/-- Theorem 10.1.13 (h) (Quotient rule) / Exercise 10.1.4 -/
theorem _root_.HasDerivWithinAt.of_div {X: Set ℝ} {x₀ f'x₀ g'x₀: ℝ}
  {f g: ℝ → ℝ} (hgx₀ : g x₀ ≠ 0) (hf: HasDerivWithinAt f f'x₀ X x₀)
  (hg: HasDerivWithinAt g g'x₀ X x₀) :
  HasDerivWithinAt (f / g) ((f'x₀ * (g x₀) - (f x₀) * g'x₀) / (g x₀)^2) X x₀ := by
  exact hf.div hg hgx₀

example (x₀:ℝ) (hx₀: x₀ ≠ 1): HasDerivWithinAt (fun x ↦ (x-2)/(x-1)) (1 /(x₀-1)^2) (.univ \ {1}) x₀ := by
  have h1 : HasDerivWithinAt (fun x : ℝ ↦ x - 2) 1 (Set.univ \ {1}) x₀ := by
    have h_id : HasDerivWithinAt (fun x : ℝ ↦ x) 1 (Set.univ \ {1}) x₀ := (hasDerivWithinAt_id x₀) (Set.univ \ {1})
    have h := h_id.sub (hasDerivWithinAt_const x₀ (Set.univ \ {1}) 2)
    have heq : ((fun x : ℝ ↦ x) - fun x : ℝ ↦ 2) = (fun x : ℝ ↦ x - 2) := by ext x; simp
    simpa [heq] using h
  have h2 : HasDerivWithinAt (fun x : ℝ ↦ x - 1) 1 (Set.univ \ {1}) x₀ := by
    have h_id : HasDerivWithinAt (fun x : ℝ ↦ x) 1 (Set.univ \ {1}) x₀ := (hasDerivWithinAt_id x₀) (Set.univ \ {1})
    have h := h_id.sub (hasDerivWithinAt_const x₀ (Set.univ \ {1}) 1)
    have heq : ((fun x : ℝ ↦ x) - fun x : ℝ ↦ 1) = (fun x : ℝ ↦ x - 1) := by ext x; simp
    simpa [heq] using h
  have h2_ne : (fun x : ℝ ↦ x - 1) x₀ ≠ 0 := by
    simpa [sub_ne_zero] using hx₀
  have h := h1.div h2 h2_ne
  have heq : ((fun x : ℝ ↦ x - 2) / (fun x : ℝ ↦ x - 1)) = (fun x : ℝ ↦ (x - 2) / (x - 1)) := by ext x; simp
  simpa [heq, show (2 : ℝ) - 1 = (1 : ℝ) by norm_num] using h

/-- Theorem 10.1.15 (Chain rule) / Exercise 10.1.7 -/
theorem _root_.HasDerivWithinAt.of_comp {X Y: Set ℝ} {x₀ y₀ f'x₀ g'y₀: ℝ}
  {f g: ℝ → ℝ} (hfx₀: f x₀ = y₀) (hfX : ∀ x ∈ X, f x ∈ Y)
  (hf: HasDerivWithinAt f f'x₀ X x₀) (hg: HasDerivWithinAt g g'y₀ Y y₀) :
  HasDerivWithinAt (g ∘ f) (g'y₀ * f'x₀) X x₀ := by
  have hst : Set.MapsTo f X Y := hfX
  have hg' : HasDerivWithinAt g g'y₀ Y (f x₀) := by simpa [hfx₀] using hg
  have := hg'.comp x₀ hf hst
  simpa [hfx₀] using this

/-- Exercise 10.1.5 -/
theorem _root_.HasDerivWithinAt.of_pow (n:ℕ) (x₀:ℝ) : HasDerivWithinAt (fun x ↦ x^n)
(n * x₀^((n:ℤ)-1)) .univ x₀ := by
  have h := hasDerivAt_zpow (n : ℤ) x₀ (Or.inr (Nat.cast_nonneg n))
  rw [hasDerivWithinAt_univ]
  simpa [zpow_natCast] using h

/-- Exercise 10.1.6 -/
theorem _root_.HasDerivWithinAt.of_zpow (n:ℤ) (x₀:ℝ) (hx₀: x₀ ≠ 0) :
  HasDerivWithinAt (fun x ↦ x^n) (n * x₀^(n-1)) (.univ \ {0}) x₀ := by
  have h : HasDerivAt (fun x : ℝ ↦ x ^ n) (n * x₀ ^ (n - 1)) x₀ :=
    hasDerivAt_zpow n x₀ (Or.inl hx₀)
  exact h.hasDerivWithinAt



end Chapter10
