import Mathlib.Tactic
import Mathlib.Topology.ContinuousOn
import Analysis.Section_7_3
import Analysis.Section_9_4
import Analysis.Section_9_8
import Analysis.Section_10_1
import Analysis.Section_10_2
import Analysis.Section_11_6
import Analysis.Section_11_8


/-!
# Analysis I, Section 11.9: The two fundamental theorems of calculus

I have attempted to make the translation as faithful a paraphrasing as possible of the
original text. When there is a choice between a more idiomatic Lean solution and a
more faithful translation, I have generally chosen the latter. In particular, there will
be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I
have consciously avoided doing so.

Main constructions and results of this section:
- The fundamental theorems of calculus.
-/

namespace Chapter11
open Chapter9 Chapter10 BoundedInterval

/-- Theorem 11.9.1 (First Fundamental Theorem of Calculus). -/
theorem cts_of_integ {a b:ℝ} {f:ℝ → ℝ} (hf: IntegrableOn f (Icc a b)) :
  ContinuousOn (fun x => integ f (Icc a x)) (.Icc a b) := by
  -- This proof is written to follow the structure of the original text.
  set F : ℝ → ℝ := fun x => integ f (Icc a x)
  choose M hM using hf.1
  have {x y:ℝ} (hxy: x < y) (hx: x ∈ Set.Icc a b) (hy: y ∈ Set.Icc a b) : |F y - F x| ≤ M * (y - x) := by
    simp at hx hy
    have := ((hf.join (join_Icc_Ioc hy.1 hy.2)).1.join (join_Icc_Ioc hx.1 (le_of_lt hxy))).2
    simp [F, this.2, abs_le']
    constructor
    . convert this.1.mono (g := fun _ ↦ M) (IntegrableOn.const _ _).1 _
      . simp [IntegrableOn.const, le_of_lt hxy]
      intro z hz
      specialize hM z ?_
      . simp at *; grind
      grind [abs_le']
    rw [neg_le]
    convert (IntegrableOn.const _ _).1.mono (f := fun _ ↦ -M) this.1 _
    . simp [IntegrableOn.const, le_of_lt hxy]
    intro z hz
    specialize hM z ?_
    . simp at *; grind
    grind [abs_le']
  replace {x y:ℝ} (hx: x ∈ Set.Icc a b) (hy: y ∈ Set.Icc a b) :
    |F y - F x| ≤ M * |x-y| := by
    obtain h | rfl | h := lt_trichotomy x y
    . simp [abs_of_neg (show x-y < 0 by linarith), this h hx hy]
    . simp
    . simp [abs_of_pos (show 0 < x-y by linarith), abs_sub_comm, this h hy hx]
  replace : UniformContinuousOn F (.Icc a b) := by
    simp [Metric.uniformContinuousOn_iff, Real.dist_eq, -Set.mem_Icc]
    intro ε hε
    use (ε/(max M 1)), (by positivity)
    intro x hx y hy hxy
    calc
      _ = |F y - F x| := by rw [abs_sub_comm]
      _ ≤ M * |x-y| := this hx hy
      _ ≤ (max M 1) * |x-y| := by gcongr; apply le_max_left
      _ < (max M 1) * (ε / (max M 1)) := by gcongr
      _ = _ := by field_simp
  exact ContinuousOn.ofUniformContinuousOn F this

theorem deriv_of_integ {a b:ℝ} (_hab: a < b) {f:ℝ → ℝ} (hf: IntegrableOn f (Icc a b))
  {x₀:ℝ} (hx₀ : x₀ ∈ Set.Icc a b) (hcts: ContinuousWithinAt f (Icc a b) x₀) :
  HasDerivWithinAt (fun x => integ f (Icc a x)) (f x₀) (.Icc a b) x₀ := by
  -- This proof is written to follow the structure of the original text.
  rw [HasDerivWithinAt.iff_approx_linear]
  simp [(ContinuousWithinAt.tfae _ f x₀).out 0 2] at hcts
  peel hcts with ε hε δ hδ hconv; intro y hy hyδ
  obtain hx₀y | rfl | hx₀y := lt_trichotomy x₀ y
  . have := ((hf.join (join_Icc_Ioc hy.1 hy.2)).1.join (join_Icc_Ioc hx₀.1 (le_of_lt hx₀y))).2
    simp [this.2, abs_le', abs_of_pos (show 0 < y - x₀ by linarith)]
    have h1 := this.1.mono (g := fun _ ↦ f x₀ + ε) (IntegrableOn.const _ _).1 ?_
    have h2 := (IntegrableOn.const _ _).1.mono (f := fun _ ↦ f x₀ - ε) this.1 ?_
    . simp [IntegrableOn.const, le_of_lt hx₀y] at h1 h2
      split_ands
      . convert h1 using 1; ring
      . simp [←sub_nonneg] at *; convert h2 using 1; ring
    all_goals intro z hz; simp [abs_lt] at *; specialize hconv z ?_ ?_ ?_ ?_ <;> linarith
  . simp
  . have := ((hf.join (join_Icc_Ioc hx₀.1 hx₀.2)).1.join (join_Icc_Ioc hy.1 (le_of_lt hx₀y))).2
    simp [this.2, abs_le', abs_of_neg (show y - x₀ < 0 by linarith)]
    have h1 := this.1.mono (g := fun _ ↦ f x₀ + ε) (IntegrableOn.const _ _).1 ?_
    have h2 := (IntegrableOn.const _ _).1.mono (f := fun _ ↦ f x₀ - ε) this.1 ?_
    . simp [IntegrableOn.const, le_of_lt hx₀y, BoundedInterval.length] at h1 h2
      split_ands
      . linarith
      . linarith
    all_goals intro z hz; simp [abs_lt] at *; specialize hconv z ?_ ?_ ?_ ?_ <;> linarith

/-- Example 11.9.2 -/
theorem IntegrableOn.of_f_9_8_5 : IntegrableOn f_9_8_5 (Icc 0 1) :=
  integ_of_monotone (StrictMonoOn.of_f_9_8_5.mono (by simp)).monotoneOn

noncomputable abbrev F_11_9_2 := fun x ↦ integ f_9_8_5 (Icc 0 x)

theorem ContinuousOn.of_F_11_9_2 : ContinuousOn F_11_9_2 (.Icc 0 1) := cts_of_integ IntegrableOn.of_f_9_8_5

theorem DifferentiableOn.of_F_11_9_2 {x:ℝ} (hx: ¬ ∃ r:ℚ, x = r) (hx': x ∈ Set.Icc 0 1) :
  DifferentiableWithinAt ℝ F_11_9_2 (.Icc 0 1) x := by
  have := deriv_of_integ (show 0 < 1 by norm_num) .of_f_9_8_5 hx' (ContinuousAt.of_f_9_8_5 hx).continuousWithinAt
  rw [hasDerivWithinAt_iff_hasFDerivWithinAt] at this
  exact ⟨_, this⟩

/-- Exercise 11.9.1 -/
theorem DifferentiableOn.of_F_11_9_2' {q:ℚ} (hq: (q:ℝ) ∈ Set.Ioo 0 1) : ¬ DifferentiableWithinAt ℝ F_11_9_2 (.Icc 0 1) q := by
  rcases hq with ⟨hq0, hq1⟩
  set qr := (q : ℝ)
  have hgpos : g_9_8_5 q > 0 := g_9_8_5_pos q
  set ε := g_9_8_5 q / 2 with hε
  have hεpos : 0 < ε := by linarith
  intro hdiff
  -- Jump inequality: f(qr) + g(q) ≤ f(t) for t > qr
  have h_jump (t : ℝ) (ht : qr < t) : f_9_8_5 qr + g_9_8_5 q ≤ f_9_8_5 t := by
    have hsub := f_9_8_5_sub qr t (by linarith)
    have h_summary : Summable g_9_8_5 := summable_g_9_8_5
    set S : Set ℚ := {q' : ℚ | qr ≤ (q' : ℝ) ∧ (q' : ℝ) < t} with hS
    have hqmem : q ∈ S := by
      dsimp [S]; exact ⟨le_refl qr, ht⟩
    have h_hasSum_ind_q : HasSum (Set.indicator ({q} : Set ℚ) g_9_8_5) (g_9_8_5 q) := by
      have := hasSum_single (f := Set.indicator ({q} : Set ℚ) g_9_8_5) q (by
        intro b hb
        simp [Set.indicator, Set.mem_singleton_iff, hb])
      simpa using this
    have h_hasSum_ind_S : HasSum (Set.indicator S g_9_8_5) (∑' r : ℚ, Set.indicator S g_9_8_5 r) :=
      (h_summary.indicator S).hasSum
    have h_pointwise : ∀ r : ℚ, Set.indicator ({q} : Set ℚ) g_9_8_5 r ≤ Set.indicator S g_9_8_5 r := by
      intro r
      rcases em (r = q) with (hr | hr)
      · subst r; simp [Set.indicator, hqmem]
      · have h_left : Set.indicator ({q} : Set ℚ) g_9_8_5 r = 0 := by simp [Set.indicator, hr]
        have h_right : 0 ≤ Set.indicator S g_9_8_5 r :=
          Set.indicator_nonneg (fun a _ => by positivity) r
        rw [h_left]; exact h_right
    have h_tsum_le : g_9_8_5 q ≤ ∑' r : ℚ, Set.indicator S g_9_8_5 r := by
      have := hasSum_le h_pointwise h_hasSum_ind_q h_hasSum_ind_S
      simpa [HasSum.tsum_eq h_hasSum_ind_q] using this
    have hgoal : f_9_8_5 t - (f_9_8_5 qr + g_9_8_5 q) ≥ 0 := by
      rw [sub_add_eq_sub_sub, hsub]
      linarith
    linarith
  -- Right quotient bound: for y ∈ (qr, 1], f(qr) + g(q) ≤ (F(y) - F(qr))/(y - qr)
  have h_right_quotient (y : ℝ) (hqy : qr < y) (hy1 : y ≤ 1) :
      f_9_8_5 qr + g_9_8_5 q ≤ (F_11_9_2 y - F_11_9_2 qr) / (y - qr) := by
    have hpos : 0 < y - qr := sub_pos.mpr hqy
    have h0y : 0 ≤ y := by linarith
    have hq0' : 0 ≤ qr := by linarith
    have h_join0 : (Icc 0 1 : BoundedInterval).joins (Icc 0 y) (Ioc y 1) :=
      BoundedInterval.join_Icc_Ioc h0y hy1
    have h_int_0y : IntegrableOn f_9_8_5 (Icc 0 y) :=
      (IntegrableOn.of_f_9_8_5.join h_join0).1
    have h_join_q : (Icc 0 y).joins (Icc 0 qr) (Ioc qr y) :=
      BoundedInterval.join_Icc_Ioc hq0' (by linarith)
    rcases h_int_0y.join h_join_q with ⟨h_int_0q, h_int_Ioc, h_eq⟩
    have hF_eq : F_11_9_2 y - F_11_9_2 qr = integ f_9_8_5 (Ioc qr y) := by
      dsimp [F_11_9_2]
      linarith
    rw [hF_eq]
    have h_const_int : IntegrableOn (fun _ : ℝ => f_9_8_5 qr + g_9_8_5 q) (Ioc qr y) :=
      (IntegrableOn.const (f_9_8_5 qr + g_9_8_5 q) (Ioc qr y)).1
    have h_maj : MajorizesOn f_9_8_5 (fun _ : ℝ => f_9_8_5 qr + g_9_8_5 q) (Ioc qr y) := by
      intro x hx
      rcases hx with ⟨hx1, hx2⟩
      exact h_jump x hx1
    have h_int_bound : integ (fun _ : ℝ => f_9_8_5 qr + g_9_8_5 q) (Ioc qr y) ≤ integ f_9_8_5 (Ioc qr y) :=
      IntegrableOn.mono h_const_int h_int_Ioc h_maj
    have h_const_val : integ (fun _ : ℝ => f_9_8_5 qr + g_9_8_5 q) (Ioc qr y) = (f_9_8_5 qr + g_9_8_5 q) * |Ioc qr y|ₗ :=
      (IntegrableOn.const (f_9_8_5 qr + g_9_8_5 q) (Ioc qr y)).2
    have h_len : |Ioc qr y|ₗ = y - qr := by
      rw [BoundedInterval.length, max_eq_left (sub_nonneg.mpr (by linarith))]
    have h_mul_bound : (f_9_8_5 qr + g_9_8_5 q) * (y - qr) ≤ integ f_9_8_5 (Ioc qr y) := by
      calc
        (f_9_8_5 qr + g_9_8_5 q) * (y - qr) = (f_9_8_5 qr + g_9_8_5 q) * |Ioc qr y|ₗ := by rw [h_len]
        _ = integ (fun _ : ℝ => f_9_8_5 qr + g_9_8_5 q) (Ioc qr y) := by rw [← h_const_val]
        _ ≤ integ f_9_8_5 (Ioc qr y) := h_int_bound
    field_simp [hpos.ne.symm]
    exact h_mul_bound
  -- Left quotient bound: for y ∈ [0, qr), (F(y) - F(qr))/(y - qr) ≤ f(qr)
  have h_left_quotient (y : ℝ) (hy0 : 0 ≤ y) (hyq : y < qr) :
      (F_11_9_2 y - F_11_9_2 qr) / (y - qr) ≤ f_9_8_5 qr := by
    have hneg : y - qr < 0 := by linarith
    have hpos' : 0 < qr - y := sub_pos.mpr hyq
    have hq0' : 0 ≤ qr := by linarith
    have h_join0 : (Icc 0 1 : BoundedInterval).joins (Icc 0 qr) (Ioc qr 1) :=
      BoundedInterval.join_Icc_Ioc hq0' (by linarith)
    have h_int_0qr : IntegrableOn f_9_8_5 (Icc 0 qr) :=
      (IntegrableOn.of_f_9_8_5.join h_join0).1
    have h_join_y : (Icc 0 qr).joins (Icc 0 y) (Ioc y qr) :=
      BoundedInterval.join_Icc_Ioc hy0 (by linarith)
    rcases h_int_0qr.join h_join_y with ⟨h_int_0y, h_int_Ioc, h_eq⟩
    have hF_rev : F_11_9_2 qr - F_11_9_2 y = integ f_9_8_5 (Ioc y qr) := by
      dsimp [F_11_9_2]
      linarith
    have hdiv_eq : (F_11_9_2 y - F_11_9_2 qr) / (y - qr) = (F_11_9_2 qr - F_11_9_2 y) / (qr - y) := by
      calc
        (F_11_9_2 y - F_11_9_2 qr) / (y - qr) = (-(F_11_9_2 qr - F_11_9_2 y)) / (y - qr) := by ring
        _ = -((F_11_9_2 qr - F_11_9_2 y) / (y - qr)) := by rw [neg_div]
        _ = (F_11_9_2 qr - F_11_9_2 y) / (-(y - qr)) := by rw [div_neg]
        _ = (F_11_9_2 qr - F_11_9_2 y) / (qr - y) := by ring
    rw [hdiv_eq, hF_rev]
    have h_const_int : IntegrableOn (fun _ : ℝ => f_9_8_5 qr) (Ioc y qr) :=
      (IntegrableOn.const (f_9_8_5 qr) (Ioc y qr)).1
    have h_maj : MajorizesOn (fun _ : ℝ => f_9_8_5 qr) f_9_8_5 (Ioc y qr) := by
      intro x hx
      rcases hx with ⟨hx1, hx2⟩
      have h_strict_mono : StrictMonoOn f_9_8_5 Set.univ := StrictMonoOn.of_f_9_8_5
      by_cases hx_eq : x = qr
      · subst x; rfl
      · have hx_lt : x < qr := lt_of_le_of_ne hx2 hx_eq
        have hfx_lt_fqr : f_9_8_5 x < f_9_8_5 qr :=
          h_strict_mono (Set.mem_univ x) (Set.mem_univ qr) hx_lt
        exact le_of_lt hfx_lt_fqr
    have h_int_bound : integ f_9_8_5 (Ioc y qr) ≤ integ (fun _ : ℝ => f_9_8_5 qr) (Ioc y qr) :=
      IntegrableOn.mono h_int_Ioc h_const_int h_maj
    have h_const_val : integ (fun _ : ℝ => f_9_8_5 qr) (Ioc y qr) = f_9_8_5 qr * |Ioc y qr|ₗ :=
      (IntegrableOn.const (f_9_8_5 qr) (Ioc y qr)).2
    have h_len : |Ioc y qr|ₗ = qr - y := by
      rw [BoundedInterval.length, max_eq_left (sub_nonneg.mpr (by linarith))]
    have h_mul_bound : integ f_9_8_5 (Ioc y qr) ≤ f_9_8_5 qr * (qr - y) := by
      calc
        integ f_9_8_5 (Ioc y qr) ≤ integ (fun _ : ℝ => f_9_8_5 qr) (Ioc y qr) := h_int_bound
        _ = f_9_8_5 qr * |Ioc y qr|ₗ := h_const_val
        _ = f_9_8_5 qr * (qr - y) := by rw [h_len]
    field_simp [hpos'.ne.symm]
    rw [mul_comm]
    exact h_mul_bound
  -- Main argument: get derivative, extract ε-δ, pick points on both sides, derive contradiction
  rcases (DifferentiableWithinAt.iff (.Icc 0 1) qr F_11_9_2).mp hdiff with ⟨d, hderiv⟩
  rw [HasDerivWithinAt.iff] at hderiv
  have h_tendsto := Metric.tendsto_nhds.mp hderiv
  have h_event := h_tendsto ε hεpos
  rw [eventually_nhdsWithin_iff] at h_event
  rw [Metric.eventually_nhds_iff] at h_event
  rcases h_event with ⟨δ, hδpos, hδ⟩
  -- Choose δ' small enough so that [qr-δ', qr+δ'] ⊆ [0,1] and δ' < δ
  set δ' := min (δ / 2) (min ((1 - qr) / 2) (qr / 2)) with hδ'
  have hδ'pos : 0 < δ' := by
    rw [hδ']
    apply lt_min_iff.mpr
    constructor
    · nlinarith
    · apply lt_min_iff.mpr; constructor <;> nlinarith
  have hδ'_le_δ_half : δ' ≤ δ / 2 := by rw [hδ']; exact min_le_left _ _
  have hδ'_lt_δ : δ' < δ := by nlinarith
  have hδ'_le_1mq_half : δ' ≤ (1 - qr) / 2 := by
    rw [hδ']; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ'_le_qr_half : δ' ≤ qr / 2 := by
    rw [hδ']; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hδ'_le_1mq : δ' ≤ 1 - qr := by nlinarith
  have hδ'_le_qr : δ' ≤ qr := by nlinarith
  -- Right point: x₁ = qr + δ'
  set x₁ := qr + δ' with hx₁
  have hx₁_gt_qr : qr < x₁ := by nlinarith
  have hx₁_le_1 : x₁ ≤ 1 := by nlinarith
  have hx₁_ne_qr : x₁ ≠ qr := by nlinarith
  have hx₁_dist : dist x₁ qr < δ := by
    rw [Real.dist_eq, hx₁]
    calc
      |(qr + δ') - qr| = |δ'| := by ring_nf
      _ = δ' := abs_of_pos hδ'pos
      _ < δ := hδ'_lt_δ
  have hx₁_mem : x₁ ∈ (.Icc 0 1 : Set ℝ) := by
    rw [hx₁]; simp; constructor <;> nlinarith
  have hx₁_mem_set : x₁ ∈ (.Icc 0 1 : Set ℝ) \ {qr} := by
    simp [hx₁_mem, hx₁_ne_qr]
  -- Left point: x₂ = qr - δ'
  set x₂ := qr - δ' with hx₂
  have hx₂_lt_qr : x₂ < qr := by nlinarith
  have hx₂_ge_0 : 0 ≤ x₂ := by nlinarith
  have hx₂_ne_qr : x₂ ≠ qr := by nlinarith
  have hx₂_dist : dist x₂ qr < δ := by
    rw [Real.dist_eq, hx₂]
    calc
      |(qr - δ') - qr| = |-δ'| := by ring_nf
      _ = |δ'| := abs_neg _
      _ = δ' := abs_of_pos hδ'pos
      _ < δ := hδ'_lt_δ
  have hx₂_mem : x₂ ∈ (.Icc 0 1 : Set ℝ) := by
    rw [hx₂]; simp; constructor <;> nlinarith
  have hx₂_mem_set : x₂ ∈ (.Icc 0 1 : Set ℝ) \ {qr} := by
    simp [hx₂_mem, hx₂_ne_qr]
  -- Apply the derivative bound to x₁ and x₂
  have hderiv_x₁ : dist ((F_11_9_2 x₁ - F_11_9_2 qr) / (x₁ - qr)) d < ε :=
    hδ hx₁_dist hx₁_mem_set
  have hderiv_x₂ : dist ((F_11_9_2 x₂ - F_11_9_2 qr) / (x₂ - qr)) d < ε :=
    hδ hx₂_dist hx₂_mem_set
  rw [Real.dist_eq] at hderiv_x₁ hderiv_x₂
  have hx₁_abs := abs_lt.mp hderiv_x₁
  have hx₂_abs := abs_lt.mp hderiv_x₂
  -- Apply quotient bounds
  have h_right_bound : f_9_8_5 qr + g_9_8_5 q ≤ (F_11_9_2 x₁ - F_11_9_2 qr) / (x₁ - qr) :=
    h_right_quotient x₁ hx₁_gt_qr hx₁_le_1
  have h_left_bound : (F_11_9_2 x₂ - F_11_9_2 qr) / (x₂ - qr) ≤ f_9_8_5 qr :=
    h_left_quotient x₂ hx₂_ge_0 hx₂_lt_qr
  -- Combine inequalities
  have h_d_gt : f_9_8_5 qr + g_9_8_5 q - ε < d := by
    have htemp : (F_11_9_2 x₁ - F_11_9_2 qr) / (x₁ - qr) < d + ε := by linarith
    linarith
  have h_d_lt : d < f_9_8_5 qr + ε := by
    have htemp : d - ε < (F_11_9_2 x₂ - F_11_9_2 qr) / (x₂ - qr) := by linarith
    linarith
  -- f(qr) + g(q) - ε = f(qr) + ε (since ε = g(q)/2)
  have h_eq : f_9_8_5 qr + g_9_8_5 q - ε = f_9_8_5 qr + ε := by
    dsimp [ε]; ring
  rw [h_eq] at h_d_gt
  linarith

/-- Definition 11.9.3.  We drop the requirement that x be a limit point as this makes
    the Lean arguments slightly cleaner -/
abbrev AntiderivOn (F f: ℝ → ℝ) (I: BoundedInterval) :=
  DifferentiableOn ℝ F I ∧ ∀ x ∈ I, HasDerivWithinAt F (f x) I x

theorem AntiderivOn.mono {F f: ℝ → ℝ} {I J: BoundedInterval}
  (h: AntiderivOn F f I) (hIJ: J ⊆ I) : AntiderivOn F f J :=
  ⟨ h.1.mono hIJ, by intro x hx; rw [subset_iff] at hIJ; exact (h.2 x (hIJ hx)).mono hIJ ⟩

/-- Theorem 11.9.4 (Second Fundamental Theorem of Calculus) -/
theorem integ_eq_antideriv_sub {a b:ℝ} (h:a ≤ b) {f F: ℝ → ℝ}
  (hf: IntegrableOn f (Icc a b)) (hF: AntiderivOn F f (Icc a b)) :
  integ f (Icc a b) = F b - F a := by
  -- This proof is written to follow the structure of the original text.
  obtain h | h := lt_or_eq_of_le h
  . have hF_cts : ContinuousOn F (.Icc a b) := by
      intro x hx; exact ContinuousWithinAt.of_differentiableWithinAt (hF.1 x hx)
    -- for technical reasons we need to extend F by constant outside of Icc a b
    let F' : ℝ → ℝ := fun x ↦ F (max (min x b) a)

    have hFF' {x:ℝ} (hx: x ∈ Set.Icc a b) : F' x = F x := by simp_all [F']

    have hF'_cts : ContinuousOn F' (Ioo (a-1) (b+1)) := by
      convert (hF_cts.comp_continuous (f := fun x ↦ max (min x b) a) (by fun_prop) ?_).continuousOn using 1
      intros; simp [le_of_lt h]

    have hupper (P: Partition (Icc a b)) : upper_riemann_sum f P ≥ F b - F a := by
      have := P.sum_of_α_length F'
      calc
        _ ≥ ∑ J ∈ P.intervals, F'[J]ₗ := by
          apply Finset.sum_le_sum
          intro J hJ; by_cases hJ_empty : (J:Set ℝ) = ∅
          . simp [α_length_of_empty _ hJ_empty, length_of_empty hJ_empty]
          obtain hJab | hJab := le_or_gt J.b J.a
          . push_neg at hJ_empty; choose x hx using hJ_empty
            cases J with
            | Ioo _ _ => simp at hx; linarith
            | Ioc _ _ => simp at hx; linarith
            | Ico _ _ => simp at hx; linarith
            | Icc c d =>
              simp at hx
              simp [show c = d by linarith]
              have hnhds: (Ioo (a-1) (b+1):Set ℝ) ∈ nhds d := by
                apply P.contains at hJ
                simp [subset_iff] at hJ
                rw [Set.Icc_subset_Icc_iff (by linarith)] at hJ
                apply Ioo_mem_nhds <;> linarith
              rw [α_length_of_pt, jump_of_continuous hnhds (hF'_cts _ (mem_of_mem_nhds hnhds))]
          set c := J.a
          set d := J.b
          apply P.contains at hJ
          have hJ' : Icc a b ⊆ Ioo (a-1/2) (b+1/2) := by apply Set.Icc_subset_Ioo <;> linarith
          apply ((Ioo_subset J).trans hJ).trans at hJ'
          simp [subset_iff] at hJ'
          rw [Set.Ioo_subset_Ioo_iff hJab] at hJ'
          have hJ'' : Icc a b ⊆ Ioo (a-1) (b+1) := by apply Set.Icc_subset_Ioo <;> linarith
          apply hJ.trans at hJ''
          rw [α_length_of_cts _ (le_of_lt hJab) _ hJ'' hF'_cts] <;> try linarith
          have := HasDerivWithinAt.mean_value hJab (hF'_cts.mono ?_) ?_
          . choose e he hmean using this
            have : HasDerivWithinAt F' (f e) (.Ioo c d) e := by
              apply (Ioo_subset J).trans at hJ
              simp [subset_iff] at hJ
              apply ((hF.2 e (hJ he)).mono hJ).congr (f := F)
              all_goals grind
            replace := derivative_unique ?_ this hmean
            . calc
                _ = F' d - F' c := rfl
                _ = (d - c) * f e := by
                  rw [this]; have : d-c > 0 := by linarith
                  field_simp
                _ = f e * |J|ₗ := by simp [mul_comm, length]; left; rw [max_eq_left (by linarith)]
                _ ≤ _ := by
                  gcongr; apply le_csSup
                  . rw [bddAbove_def]
                    choose M hM using hf.1; use M
                    simp [abs_le', -Set.mem_Icc] at hM ⊢
                    intro x hx; rw [subset_iff] at hJ; specialize hM x (hJ hx); tauto
                  simp; use e; simp; exact ((subset_iff _ _).mp (Ioo_subset J)) he
            rw [←mem_closure_iff_clusterPt]
            apply closure_mono (s := .Ioo e d)
            . intro _ _; simp at *; refine ⟨ ⟨ ?_, ?_ ⟩, ?_ ⟩ <;> linarith
            simp at he; rw [closure_Ioo (by linarith)]; simp; linarith
          . simp; rw [Set.Icc_subset_Ioo_iff (le_of_lt hJab)]; grind
          apply (Ioo_subset J).trans at hJ
          apply (hF.1.mono _).congr
          . intro x hx
            have : x ∈ Set.Icc a b := by specialize hJ _ hx; simpa using hJ
            grind
          grind [subset_iff]
        _ = F'[Icc a b]ₗ := P.sum_of_α_length F'
        _ = F' b - F' a := by
          apply α_length_of_cts _ _ _ _ hF'_cts <;> try linarith
          intro _ _; simp [mem_iff] at *; grind
        _ = _ := by congr 1 <;> apply hFF' <;> grind
    have hlower (P: Partition (Icc a b)) : lower_riemann_sum f P ≤ F b - F a := by
      have := P.sum_of_α_length F'
      calc
        _ ≤ ∑ J ∈ P.intervals, F'[J]ₗ := by
          apply Finset.sum_le_sum
          intro J hJ; by_cases hJ_empty : (J:Set ℝ) = ∅
          . simp [α_length_of_empty _ hJ_empty, length_of_empty hJ_empty]
          obtain hJab | hJab := le_or_gt J.b J.a
          . push_neg at hJ_empty; choose x hx using hJ_empty
            cases J with
            | Ioo _ _ => simp at hx; linarith
            | Ioc _ _ => simp at hx; linarith
            | Ico _ _ => simp at hx; linarith
            | Icc c d =>
              simp at hx
              simp [show c = d by linarith]
              have hnhds: (Ioo (a-1) (b+1):Set ℝ) ∈ nhds d := by
                apply P.contains at hJ
                simp [subset_iff] at hJ
                rw [Set.Icc_subset_Icc_iff (by linarith)] at hJ
                apply Ioo_mem_nhds <;> linarith
              rw [α_length_of_pt, jump_of_continuous hnhds (hF'_cts _ (mem_of_mem_nhds hnhds))]
          set c := J.a
          set d := J.b
          apply P.contains at hJ
          have hJ' : Icc a b ⊆ Ioo (a-1/2) (b+1/2) := by apply Set.Icc_subset_Ioo <;> linarith
          apply ((Ioo_subset J).trans hJ).trans at hJ'
          simp [subset_iff] at hJ'
          rw [Set.Ioo_subset_Ioo_iff hJab] at hJ'
          have hJ'' : Icc a b ⊆ Ioo (a-1) (b+1) := by apply Set.Icc_subset_Ioo <;> linarith
          apply hJ.trans at hJ''
          rw [α_length_of_cts _ (le_of_lt hJab) _ hJ'' hF'_cts] <;> try linarith
          have := HasDerivWithinAt.mean_value hJab (hF'_cts.mono ?_) ?_
          . choose e he hmean using this
            have : HasDerivWithinAt F' (f e) (.Ioo c d) e := by
              apply (Ioo_subset J).trans at hJ
              simp [subset_iff] at hJ
              apply ((hF.2 e (hJ he)).mono hJ).congr (f := F)
              all_goals grind
            replace := derivative_unique ?_ this hmean
            . calc
                _ ≤ f e * |J|ₗ := by
                  gcongr; apply csInf_le
                  . rw [bddBelow_def]
                    choose M hM using hf.1; use (-M)
                    simp [abs_le', -Set.mem_Icc] at hM ⊢
                    intro x hx; rw [subset_iff] at hJ; specialize hM x (hJ hx); linarith
                  simp; use e; simp; exact ((subset_iff _ _).mp (Ioo_subset J)) he
                _ = (d - c) * f e := by simp [mul_comm, length]; left; rw [max_eq_left (by linarith)]
                _ = F' d - F' c := by
                  rw [this]; have : d-c > 0 := by linarith
                  field_simp
            rw [←mem_closure_iff_clusterPt]
            apply closure_mono (s := .Ioo e d)
            . intro _ _; simp at *; refine ⟨ ⟨ ?_, ?_ ⟩, ?_ ⟩ <;> linarith
            simp at he; rw [closure_Ioo (by linarith)]; simp; linarith
          . simp; rw [Set.Icc_subset_Ioo_iff (le_of_lt hJab)]; grind
          apply (Ioo_subset J).trans at hJ
          apply (hF.1.mono _).congr
          . intro x hx
            have : x ∈ Set.Icc a b := by specialize hJ _ hx; simpa using hJ
            grind
          grind [subset_iff]
        _ = F'[Icc a b]ₗ := P.sum_of_α_length F'
        _ = F' b - F' a := by
          apply α_length_of_cts _ _ _ _ hF'_cts <;> try linarith
          intro _ _; simp [mem_iff] at *; grind
        _ = F b - F a := by congr 1 <;> apply hFF' <;> grind
    replace hupper : upper_integral f (Icc a b) ≥ F b - F a := by
      rw [upper_integ_eq_inf_upper_sum hf.1]; apply le_csInf <;> simp [Set.range_nonempty]
      grind
    replace hlower : lower_integral f (Icc a b) ≤ F b - F a := by
      rw [lower_integ_eq_sup_lower_sum hf.1]; apply csSup_le <;> simp [Set.range_nonempty]
      grind
    linarith [hf.2]
  simp [h]; exact (integ_on_subsingleton (by simp [length])).2


open Real

noncomputable abbrev F_11_9 : ℝ → ℝ := fun x ↦ if x = 0 then 0 else x^2 * sin (1 / x^3)

lemma F_11_9_differentiable : Differentiable ℝ F_11_9 := by
  intro x
  by_cases hx : x = 0
  · subst hx
    have h0 : HasDerivAt F_11_9 0 0 := by
      rw [hasDerivAt_iff_tendsto_slope]
      have h_slope_eq : slope F_11_9 0 = fun h : ℝ ↦ h * sin (1 / h^3) := by
        ext h
        dsimp [slope, F_11_9]
        by_cases hh : h = 0
        · subst hh; simp
        · simp [hh]; field_simp [hh]
      rw [h_slope_eq]
      have h_bound : ∀ h : ℝ, -|h| ≤ h * sin (1 / h^3) ∧ h * sin (1 / h^3) ≤ |h| := by
        intro h
        have h_abs_mul : |h * sin (1 / h^3)| ≤ |h| := by
          calc
            |h * sin (1 / h^3)| = |h| * |sin (1 / h^3)| := abs_mul h (sin (1 / h^3))
            _ ≤ |h| * 1 := mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg h)
            _ = |h| := mul_one _
        exact abs_le.mp h_abs_mul
      have h_tendsto_neg_abs : Filter.Tendsto (fun h : ℝ => -|h|) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
        have h_cont : Continuous (fun h : ℝ => -|h|) := by
          continuity
        simpa using h_cont.tendsto 0 |>.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
      have h_tendsto_abs : Filter.Tendsto (fun h : ℝ => |h|) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
        simpa [abs_zero] using (continuous_abs.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le h_tendsto_neg_abs h_tendsto_abs
        (fun h => (h_bound h).1) (fun h => (h_bound h).2)
    exact h0.differentiableAt
  · have h_sq_diff : DifferentiableAt ℝ (fun y : ℝ => y^2) x :=
      (differentiableAt_id).pow 2
    have h_cube_ne_zero : x^3 ≠ 0 := pow_ne_zero 3 hx
    have h_inner_diff : DifferentiableAt ℝ (fun y : ℝ => 1 / y^3) x :=
      ((differentiableAt_const 1).div ((differentiableAt_id).pow 3) h_cube_ne_zero)
    have h_sin_comp : DifferentiableAt ℝ (fun y : ℝ => sin (1 / y^3)) x :=
      h_inner_diff.sin
    have h_mul : DifferentiableAt ℝ (fun y : ℝ => y^2 * sin (1 / y^3)) x :=
      h_sq_diff.mul h_sin_comp
    have h_eq_near : F_11_9 =ᶠ[nhds x] (fun y : ℝ => y^2 * sin (1 / y^3)) := by
      filter_upwards [eventually_ne_nhds hx] with y hy
      simp [F_11_9, hy]
    exact h_mul.congr_of_eventuallyEq h_eq_near

example : ¬ BddOn (deriv F_11_9) (.Icc (-1) 1) := by
  intro hBdd
  rcases hBdd with ⟨M, hM⟩
  -- Choose n ∈ ℕ large enough (works for all M)
  -- We ensure n ≥ 1 and 2πn > max(1, (M+1)^3)
  have h_n_exists : ∃ (n : ℕ), (2 * π * (n : ℝ)) > max 1 ((M + 1)^3) ∧ (1 : ℝ) ≤ (n : ℝ) := by
    set A := max (1 / (2*π)) (((M + 1)^3) / (2*π)) with hA
    have h := exists_nat_gt A
    rcases h with ⟨n, hn⟩
    have hpos : 0 < 2*π := by positivity
    have hn_gt_A : A < (n : ℝ) := hn
    refine ⟨n, ?_, ?_⟩
    · -- 2πn > max 1 (M+1)^3
      have h1 : (1 / (2*π)) ≤ A := le_max_left _ _
      have h2 : ((M + 1)^3) / (2*π) ≤ A := le_max_right _ _
      have hn_gt_one_div : 1 / (2*π) < (n : ℝ) := by linarith
      have hn_gt_cube_div : ((M + 1)^3) / (2*π) < (n : ℝ) := by linarith
      -- From hn_gt_one_div: 1/(2π) < n ⇒ 1 < 2πn
      have h_gt_one : (1 : ℝ) < 2 * π * (n : ℝ) := by
        calc
          (1 : ℝ) = (1 / (2*π)) * (2*π) := by field_simp [ne_of_gt hpos]
          _ < (n : ℝ) * (2*π) := mul_lt_mul_of_pos_right hn_gt_one_div hpos
          _ = 2 * π * (n : ℝ) := by ring
      -- From hn_gt_cube_div: (M+1)^3/(2π) < n ⇒ (M+1)^3 < 2πn
      have h_gt_cube : (M + 1)^3 < 2 * π * (n : ℝ) := by
        calc
          (M + 1)^3 = (((M + 1)^3) / (2*π)) * (2*π) := by field_simp [ne_of_gt hpos]
          _ < (n : ℝ) * (2*π) := mul_lt_mul_of_pos_right hn_gt_cube_div hpos
          _ = 2 * π * (n : ℝ) := by ring
      exact max_lt h_gt_one h_gt_cube
    · -- 1 ≤ n
      have hA_nonneg : 0 ≤ A := by
        refine le_trans ?_ (le_max_left _ _)
        have : 0 ≤ 1 / (2*π) := div_nonneg (by norm_num) (by positivity)
        exact this
      have hn_nonneg : (0 : ℕ) < n := by
        by_contra! hzero
        have : (n : ℝ) ≤ 0 := by exact_mod_cast hzero
        linarith
      have hn_one : (1 : ℕ) ≤ n := Nat.one_le_of_lt hn_nonneg
      exact_mod_cast hn_one
  rcases h_n_exists with ⟨n, hn_gt, hn_one⟩
  have hn_gt_one : (1 : ℝ) < 2 * π * (n : ℝ) := by
    have : max 1 ((M + 1)^3) ≥ 1 := le_max_left _ _
    linarith
  have hn_gt_cube : (M + 1)^3 < 2 * π * (n : ℝ) := by
    have : max 1 ((M + 1)^3) ≥ (M + 1)^3 := le_max_right _ _
    linarith
  -- Define x := (2πn)^(-1/3)
  set x := ((2 * π * (n : ℝ)) ^ ((-1/3 : ℝ))) with hx_def
  have h_base_pos : 0 < 2 * π * (n : ℝ) := by
    positivity
  have hx_pos : 0 < x := by
    dsimp [x]
    exact Real.rpow_pos_of_pos h_base_pos _
  have hx_ne_zero : x ≠ 0 := by linarith
  have h_base_gt_one : 1 < 2 * π * (n : ℝ) := hn_gt_one
  have hx_lt_one : x < 1 := by
    dsimp [x]
    have h := Real.rpow_lt_rpow_of_neg (by norm_num : 0 < (1 : ℝ)) h_base_gt_one
      (by norm_num : (-1/3 : ℝ) < 0)
    simpa [Real.one_rpow] using h
  have hx_mem : x ∈ Set.Icc (-1 : ℝ) (1 : ℝ) := by
    refine ⟨by linarith, by linarith⟩
  -- Identity: x^3 = 1/(2πn)
  have hx_cube : x ^ 3 = 1 / (2 * π * (n : ℝ)) := by
    dsimp [x]
    have ha_nonneg : 0 ≤ 2 * π * (n : ℝ) := by linarith
    calc
      ((2 * π * (n : ℝ)) ^ ((-1/3 : ℝ))) ^ 3 = (((2 * π * (n : ℝ)) ^ ((-1/3 : ℝ))) ^ (3 : ℝ)) := by norm_num
      _ = (2 * π * (n : ℝ)) ^ (((-1/3 : ℝ) * (3 : ℝ))) := by
        rw [Real.rpow_mul ha_nonneg (-1/3) (3 : ℝ)]
      _ = (2 * π * (n : ℝ)) ^ ((-1 : ℝ)) := by ring_nf
      _ = ((2 * π * (n : ℝ))⁻¹) := by
        rw [Real.rpow_neg ha_nonneg, Real.rpow_one (2 * π * (n : ℝ))]
      _ = 1 / (2 * π * (n : ℝ)) := by simp
  have h_inv_cube : 1 / (x ^ 3) = 2 * π * (n : ℝ) := by
    rw [hx_cube]
    field_simp [ne_of_gt h_base_pos]
  -- At this x: sin(1/x^3) = 0, cos(1/x^3) = 1
  have h_sin_zero : sin (1 / (x ^ 3)) = 0 := by
    rw [h_inv_cube]
    have h := Real.sin_nat_mul_two_pi_sub 0 n
    simpa [sub_zero, mul_comm] using h
  have h_cos_one : cos (1 / (x ^ 3)) = 1 := by
    rw [h_inv_cube]
    simpa [mul_comm] using Real.cos_nat_mul_two_pi n
  -- Compute the derivative at x (x ≠ 0)
  have h_deriv_val : deriv F_11_9 x = -3 / (x ^ 2) := by
    -- First, the explicit derivative formula for y ↦ y^2 * sin(1/y^3) at x
    have h_deriv_explicit : HasDerivAt (fun (y : ℝ) => y^2 * sin (1 / y^3))
        ((2*x*sin (1/x^3)) - (3*cos (1/x^3)/x^2)) x := by
      have hx3 : x^3 ≠ 0 := pow_ne_zero 3 hx_ne_zero
      have h_sq : HasDerivAt (fun (y : ℝ) => y^2) (2*x) x := by
        simpa using hasDerivAt_pow 2 x
      have h_inv_c : HasDerivAt (fun (y : ℝ) => 1 / y^3) (-3 / x^4) x := by
        have h_pow3 : HasDerivAt (fun (y : ℝ) => y^3) (3*x^2) x := by
          simpa using hasDerivAt_pow 3 x
        have h_inv' := HasDerivAt.inv h_pow3 hx3
        have h_inv'' : HasDerivAt (fun (y : ℝ) => 1 / y^3) (-(3*x^2) / (x^3)^2) x := by
          simpa [one_div] using h_inv'
        have h_eq : (-(3*x^2) / (x^3)^2) = (-3 / x^4) := by
          field_simp [hx_ne_zero]
        simpa [h_eq] using h_inv''
      have h_sin_comp : HasDerivAt (fun (y : ℝ) => sin (1 / y^3))
          (cos (1/x^3) * (-3 / x^4)) x := by
        apply HasDerivAt.comp x (hasDerivAt_sin (1/x^3)) h_inv_c
      have h_mul := HasDerivAt.mul h_sq h_sin_comp
      have h_mul' : HasDerivAt (fun (y : ℝ) => y^2 * sin (1 / y^3))
          (2*x*sin (1/x^3) + x^2*(cos (1/x^3)*(-3/x^4))) x := by
        simpa using h_mul
      have h_eq' : (2*x*sin (1/x^3) + x^2*(cos (1/x^3)*(-3/x^4))) =
          ((2*x*sin (1/x^3)) - (3*cos (1/x^3)/x^2)) := by
        field_simp [hx_ne_zero]
        ring
      rw [h_eq'] at h_mul'
      exact h_mul'
    -- F_11_9 equals the explicit function near x ≠ 0
    have hF_eq_near : F_11_9 =ᶠ[nhds x] (fun y : ℝ => y^2 * sin (1 / y^3)) := by
      filter_upwards [eventually_ne_nhds hx_ne_zero] with y hy
      simp [F_11_9, hy]
    have h_deriv_F : HasDerivAt F_11_9
        ((2*x*sin (1/x^3)) - (3*cos (1/x^3)/x^2)) x :=
      h_deriv_explicit.congr_of_eventuallyEq hF_eq_near
    -- Now simplify using sin=0, cos=1 at our x
    rw [h_sin_zero, h_cos_one] at h_deriv_F
    rw [h_deriv_F.deriv]
    ring
  -- Compute absolute value
  have habs_deriv : |deriv F_11_9 x| = 3 / (x ^ 2) := by
    rw [h_deriv_val]
    have hpos_sq : 0 < x ^ 2 := pow_pos hx_pos 2
    rw [abs_div, abs_of_neg (by norm_num : (-3 : ℝ) < 0), abs_of_pos hpos_sq]
    ring
  -- Show 3/x^2 > M
  have h_bound : 3 / (x ^ 2) > M := by
    by_cases hMone_pos : M + 1 > 0
    · -- Standard argument when M+1 > 0
      have hx_inv_gt : 1 / x > M + 1 := by
        have h_cube_gt : (1 / x)^3 > (M + 1)^3 := by
          calc
            (1 / x)^3 = 1 / (x ^ 3) := by field_simp [hx_ne_zero]
            _ = 2 * π * (n : ℝ) := h_inv_cube
            _ > (M + 1)^3 := hn_gt_cube
        have hpos : 0 < 1 / x := div_pos (by norm_num) hx_pos
        by_contra! hle
        have ha_nonneg : 0 ≤ 1 / x := hpos.le
        have hb_nonneg : 0 ≤ M + 1 := hMone_pos.le
        have h_sq_le : (1 / x)^2 ≤ (M + 1)^2 := by
          have := mul_self_le_mul_self ha_nonneg hle
          simpa [sq] using this
        have hcube_le : (1 / x)^3 ≤ (M + 1)^3 := by
          calc
            (1 / x)^3 = (1 / x)^2 * (1 / x) := by ring
            _ ≤ (M + 1)^2 * (M + 1) :=
              mul_le_mul h_sq_le hle ha_nonneg (pow_two_nonneg (M + 1))
            _ = (M + 1)^3 := by ring
        linarith
      have hM_ineq : 3 * ((M + 1)^2) > M := by
        nlinarith
      calc
        3 / (x ^ 2) = 3 * ((1 / x)^2) := by ring
        _ > 3 * ((M + 1)^2) := by nlinarith
        _ > M := by nlinarith
    · -- M+1 ≤ 0, so M ≤ -1, then 3/x^2 > 0 ≥ M+1 ≥ M
      have hpos' : 0 < 3 / (x ^ 2) := by positivity
      linarith
  -- Get contradiction from hM
  have h_contra := hM x hx_mem
  rw [habs_deriv] at h_contra
  linarith

example : AntiderivOn F_11_9 (deriv F_11_9) (Icc (-1) 1) := by
  have hdiff := F_11_9_differentiable
  refine ⟨hdiff.differentiableOn, fun x hx => (hdiff x).hasDerivAt.hasDerivWithinAt⟩

/-- Lemma 11.9.5 / Exercise 11.9.2 -/
theorem antideriv_eq_antideriv_add_const {I:BoundedInterval} {f F G : ℝ → ℝ}
  (hfF: AntiderivOn F f I) (hfG: AntiderivOn G f I) :
   ∃ C, ∀ x ∈ (I:Set ℝ), F x = G x + C := by
  rcases hfF with ⟨hF_diff, hF_deriv⟩
  rcases hfG with ⟨hG_diff, hG_deriv⟩
  set H : ℝ → ℝ := F - G with hH
  have hH_diff : DifferentiableOn ℝ H I := hF_diff.sub hG_diff
  have hH_cont : ContinuousOn H I := hH_diff.continuousOn
  have hH_deriv : ∀ x ∈ (I : Set ℝ), HasDerivWithinAt H 0 I x := by
    intro x hx
    have hF := hF_deriv x hx
    have hG := hG_deriv x hx
    have hsub := hF.sub hG
    simpa [hH, sub_self] using hsub
  have h_ord : ((I : Set ℝ)).OrdConnected :=
    ((BoundedInterval.ordConnected_iff (I : Set ℝ)).mpr ⟨I, rfl⟩).2
  -- Lemma: every point in an open interval is a cluster point when the point is removed
  have clusterPt_Ioo {a b x : ℝ} (hx : x ∈ Set.Ioo a b) :
      ClusterPt x (.principal ((Set.Ioo a b : Set ℝ) \ {x})) := by
    rw [clusterPt_principal_iff]
    intro U hU
    rcases mem_nhds_iff.mp hU with ⟨V, hVU, hV_open, hxV⟩
    have hV_open' : IsOpen (V ∩ Set.Ioo a b) := IsOpen.inter hV_open isOpen_Ioo
    have hxV' : x ∈ V ∩ Set.Ioo a b := ⟨hxV, hx⟩
    rcases Metric.isOpen_iff.mp hV_open' x hxV' with ⟨ε, hε, hball⟩
    set d := x + ε / 2 with hd
    have hd_ball : d ∈ Metric.ball x ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> nlinarith
    have hd_V : d ∈ V := (hball hd_ball).1
    have hd_Ioo : d ∈ Set.Ioo a b := (hball hd_ball).2
    have hd_ne : d ≠ x := by nlinarith
    exact ⟨d, ⟨hVU hd_V, hd_Ioo, hd_ne⟩⟩
  -- For any x < y both in I, H x = H y (by MVT)
  have h_const_lt : ∀ {x y : ℝ}, x < y → x ∈ (I : Set ℝ) → y ∈ (I : Set ℝ) → H x = H y := by
    intro x y hlt hx hy
    have h_Icc_sub : Set.Icc x y ⊆ (I : Set ℝ) := h_ord.out hx hy
    have h_Ioo_sub : Set.Ioo x y ⊆ (I : Set ℝ) :=
      Set.Subset.trans Set.Ioo_subset_Icc_self h_Icc_sub
    have hH_cont_xy : ContinuousOn H (Set.Icc x y) := hH_cont.mono h_Icc_sub
    have hH_diff_xy : DifferentiableOn ℝ H (Set.Ioo x y) := hH_diff.mono h_Ioo_sub
    rcases HasDerivWithinAt.mean_value hlt hH_cont_xy hH_diff_xy with ⟨c, hc, hmvt⟩
    -- hmvt : HasDerivWithinAt H ((H y - H x) / (y - x)) (Set.Ioo x y) c
    have hH_deriv_c : HasDerivWithinAt H 0 (Set.Ioo x y) c := by
      have hc_I : c ∈ (I : Set ℝ) := h_Ioo_sub hc
      exact (hH_deriv c hc_I).mono h_Ioo_sub
    have h_cluster : ClusterPt c (.principal ((Set.Ioo x y : Set ℝ) \ {c})) :=
      clusterPt_Ioo hc
    have h_slope_zero : (H y - H x) / (y - x) = 0 :=
      derivative_unique h_cluster hmvt hH_deriv_c
    have hyx_ne : y - x ≠ 0 := by linarith
    rcases div_eq_zero_iff.mp h_slope_zero with (hzero | hzero)
    · linarith
    · exact absurd hzero hyx_ne
  -- For any x, y in I, H x = H y
  have h_const : ∀ x, x ∈ (I : Set ℝ) → ∀ y, y ∈ (I : Set ℝ) → H x = H y := by
    intro x hx y hy
    by_cases hxy : x ≤ y
    · by_cases hxy_lt : x < y
      · exact h_const_lt hxy_lt hx hy
      · have h_eq : x = y := le_antisymm hxy (not_lt.mp hxy_lt)
        subst h_eq; rfl
    · have hyx : y < x := by linarith
      exact (h_const_lt hyx hy hx).symm
  -- Select a reference point and set C = H x₀ = F x₀ - G x₀
  by_cases h_nonempty : (I : Set ℝ).Nonempty
  · rcases h_nonempty with ⟨x₀, hx₀⟩
    refine ⟨H x₀, ?_⟩
    intro x hx
    have h_eq : H x = H x₀ := h_const x hx x₀ hx₀
    dsimp [H] at h_eq ⊢
    linarith
  · refine ⟨0, ?_⟩
    intro x hx
    exfalso; exact h_nonempty ⟨x, hx⟩

/-
Difference-quotient bounds for the integral of a monotone function.
    For `x < y` in `[a,b]`, the increment `∫_a^y f - ∫_a^x f = ∫_x^y f`
    is squeezed between `f x * (y-x)` and `f y * (y-x)`.
-/
private lemma Exercise_11_9_3.integ_incr_bounds {a b:ℝ} {f:ℝ → ℝ}
    (hf: MonotoneOn f (Icc a b)) {x y:ℝ}
    (hx: x ∈ Set.Icc a b) (hy: y ∈ Set.Icc a b) (hxy: x < y) :
    f x * (y - x) ≤ integ f (Icc a y) - integ f (Icc a x) ∧
      integ f (Icc a y) - integ f (Icc a x) ≤ f y * (y - x) := by
        -- Apply the integrability and join the intervals.
        have h_integrable : IntegrableOn f (Icc a y) := by
          apply_rules [ integ_of_monotone, hf.mono ];
          exact Set.Icc_subset_Icc_right hy.2
        have h_join : (Icc a y).joins (Icc a x) (Ioc x y) := by
          exact BoundedInterval.join_Icc_Ioc hx.1 hxy.le
        have h_splits : integ f (Icc a y) = integ f (Icc a x) + integ f (Ioc x y) := by
          exact ( IntegrableOn.join h_join h_integrable ).2.2 ▸ rfl
        have h_length : (Ioc x y).length = y - x := by
          simp +decide [ BoundedInterval.length, hxy.le ];
        -- Apply the bounds via monotonicity.
        have h_lower_bound : f x * (y - x) ≤ integ f (Ioc x y) := by
          have h_lower_bound : ∀ t ∈ (Ioc x y : Set ℝ), f x ≤ f t := by
            exact fun t ht => hf ⟨ hx.1, hx.2 ⟩ ⟨ by linarith [ ht.1, hx.1 ], by linarith [ ht.2, hy.2 ] ⟩ ht.1.le;
          convert IntegrableOn.mono ( IntegrableOn.const ( f x ) ( Ioc x y ) |>.1 ) ( show IntegrableOn f ( Ioc x y ) from ?_ ) ( fun t ht => h_lower_bound t ht ) using 1;
          · rw [ ← h_length, ( IntegrableOn.const ( f x ) ( Ioc x y ) |>.2 ) ];
          · exact IntegrableOn.mono' ( show ( Ioc x y : Set ℝ ) ⊆ ( Icc a y : Set ℝ ) from fun t ht => ⟨ by linarith [ ht.1, hx.1 ], by linarith [ ht.2, hy.2 ] ⟩ ) h_integrable
        have h_upper_bound : integ f (Ioc x y) ≤ f y * (y - x) := by
          convert IntegrableOn.mono _ _ _ using 1;
          convert ( IntegrableOn.const ( f y ) ( Ioc x y ) ) |>.2.symm using 1;
          · rw [ h_length ];
          · exact h_integrable.mono' ( Set.Ioc_subset_Icc_self.trans ( Set.Icc_subset_Icc hx.1 le_rfl ) );
          · exact IntegrableOn.const _ _ |>.1;
          · exact fun t ht => hf ⟨ by linarith [ ht.1, hx.1 ], by linarith [ ht.2, hy.2 ] ⟩ ⟨ by linarith [ ht.1, hx.1 ], by linarith [ ht.2, hy.2 ] ⟩ ht.2;
        constructor <;> linarith

/-- Right-hand difference-quotient (slope) bounds for a monotone function:
    for {lit}`x₀ < y` in {lit}`[a,b]`, `f x₀ ≤ slope ≤ f y`. -/
private lemma Exercise_11_9_3.slope_right {a b:ℝ} {f:ℝ → ℝ}
    (hf: MonotoneOn f (Icc a b)) {x₀ y:ℝ}
    (hx₀: x₀ ∈ Set.Icc a b) (hy: y ∈ Set.Icc a b) (hxy: x₀ < y) :
    f x₀ ≤ (integ f (Icc a y) - integ f (Icc a x₀)) / (y - x₀) ∧
      (integ f (Icc a y) - integ f (Icc a x₀)) / (y - x₀) ≤ f y := by
  obtain ⟨hlo, hhi⟩ := Exercise_11_9_3.integ_incr_bounds hf hx₀ hy hxy
  have hpos : 0 < y - x₀ := by linarith
  constructor
  · rw [le_div_iff₀ hpos]; linarith
  · rw [div_le_iff₀ hpos]; linarith

/-- Left-hand difference-quotient (slope) bounds for a monotone function:
    for {lit}`y < x₀` in {lit}`[a,b]`, `f y ≤ slope ≤ f x₀`. -/
private lemma Exercise_11_9_3.slope_left {a b:ℝ} {f:ℝ → ℝ}
    (hf: MonotoneOn f (Icc a b)) {x₀ y:ℝ}
    (hx₀: x₀ ∈ Set.Icc a b) (hy: y ∈ Set.Icc a b) (hxy: y < x₀) :
    f y ≤ (integ f (Icc a y) - integ f (Icc a x₀)) / (y - x₀) ∧
      (integ f (Icc a y) - integ f (Icc a x₀)) / (y - x₀) ≤ f x₀ := by
  obtain ⟨hlo, hhi⟩ := Exercise_11_9_3.integ_incr_bounds hf hy hx₀ hxy
  have hneg : y - x₀ < 0 := by linarith
  constructor
  · rw [le_div_iff_of_neg hneg]; linarith
  · rw [div_le_iff_of_neg hneg]; linarith

/-
The hard direction of Exercise 11.9.3 at an interior point:
    if `F(x) = ∫_a^x f` is differentiable at an interior `x₀`, then the monotone
    integrand `f` is continuous at `x₀`.
-/
private lemma Exercise_11_9_3.cts_of_diff {a b x₀:ℝ} (hx₀: x₀ ∈ Set.Ioo a b)
    {f: ℝ → ℝ} (hf: MonotoneOn f (Icc a b))
    (hdiff: DifferentiableWithinAt ℝ (fun x => integ f (Icc a x)) (Icc a b) x₀) :
    ContinuousWithinAt f (Icc a b) x₀ := by
      -- Let $L := \text{derivWithin } F (\text{Icc } a b) x₀$. From `hdiff.hasDerivWithinAt` get `hL : HasDerivWithinAt F L (\text{Icc } a b) x₀`.
      obtain ⟨L, hL⟩ : ∃ L, HasDerivWithinAt (fun x => integ f (Icc a x)) L (Icc a b) x₀ := by
        exact ⟨ _, hdiff.hasDerivWithinAt ⟩;
      -- Using `hL.hasDerivAt (Icc_mem_nhds hx₀.1 hx₀.2)` get `HasDerivAt F L x₀`, and then `hasDerivAt_iff_tendsto_slope.mp` gives
      have h_slope : Filter.Tendsto (fun y => (integ f (Icc a y) - integ f (Icc a x₀)) / (y - x₀)) (nhdsWithin x₀ {x₀}ᶜ) (nhds L) := by
        convert hL.hasDerivAt ( Icc_mem_nhds hx₀.1 hx₀.2 ) |> HasDerivAt.tendsto_slope using 1;
        exact funext fun x => by rw [ slope_def_field ] ;
      -- STEP 1: `L = f x₀`.
      have hLeq : L = f x₀ := by
        refine' le_antisymm _ _;
        · -- By definition of $L$, we know that for $y$ slightly less than $x₀$, $(integ f (Icc a y) - integ f (Icc a x₀)) / (y - x₀) \leq f(x₀)$.
          have h_left : ∀ᶠ y in nhdsWithin x₀ (Set.Iio x₀), (integ f (Icc a y) - integ f (Icc a x₀)) / (y - x₀) ≤ f x₀ := by
            rw [ eventually_nhdsWithin_iff ];
            filter_upwards [ Ioo_mem_nhds hx₀.1 hx₀.2 ] with y hy hy' ; have := Exercise_11_9_3.slope_left hf ( show x₀ ∈ Set.Icc a b from ⟨ hx₀.1.le, hx₀.2.le ⟩ ) ( show y ∈ Set.Icc a b from ⟨ hy.1.le, hy.2.le ⟩ ) hy' ; aesop;
          exact le_of_tendsto ( h_slope.mono_left <| nhdsWithin_mono _ <| by simp +decide ) h_left;
        · have h_slope_right : ∀ᶠ y in nhdsWithin x₀ (Set.Ioi x₀), f x₀ ≤ (integ f (Icc a y) - integ f (Icc a x₀)) / (y - x₀) := by
            filter_upwards [ Ioo_mem_nhdsGT hx₀.2 ] with y hy using Exercise_11_9_3.slope_right hf ⟨ hx₀.1.le, hx₀.2.le ⟩ ⟨ by linarith [ hy.1, hx₀.1 ], by linarith [ hy.2, hx₀.2 ] ⟩ hy.1 |>.1;
          exact le_of_tendsto_of_tendsto tendsto_const_nhds ( h_slope.mono_left <| nhdsWithin_mono _ <| by simp +decide ) h_slope_right;
      -- STEP 2: RIGHT LIMIT `Tendsto f (𝓝[>] x₀) (𝓝 (f x₀))`, by squeeze `tendsto_of_tendsto_of_tendsto_of_le_of_le'` with lower bound `fun _ => f x₀` and upper bound `hup := fun y => 2 * slope F x₀ (2*y - x₀) - slope F x₀ y`.
      have h_right : Filter.Tendsto f (nhdsWithin x₀ (Set.Ioi x₀)) (nhds (f x₀)) := by
        have h_right : Filter.Tendsto (fun y => 2 * ((integ f (Icc a (2 * y - x₀)) - integ f (Icc a x₀)) / (2 * y - x₀ - x₀)) - ((integ f (Icc a y) - integ f (Icc a x₀)) / (y - x₀))) (nhdsWithin x₀ (Set.Ioi x₀)) (nhds (f x₀)) := by
          have h_right : Filter.Tendsto (fun y => (integ f (Icc a (2 * y - x₀)) - integ f (Icc a x₀)) / (2 * y - x₀ - x₀)) (nhdsWithin x₀ (Set.Ioi x₀)) (nhds (f x₀)) := by
            convert h_slope.comp ( show Filter.Tendsto ( fun y : ℝ => 2 * y - x₀ ) ( nhdsWithin x₀ ( Set.Ioi x₀ ) ) ( nhdsWithin x₀ { x₀ } ᶜ ) from ?_ ) using 2;
            · rw [hLeq];
            · refine' Filter.Tendsto.inf _ _ <;> norm_num;
              · exact Continuous.tendsto' ( by continuity ) _ _ ( by ring );
              · intros; linarith;
          convert Filter.Tendsto.sub ( h_right.const_mul 2 ) ( h_slope.mono_left <| nhdsWithin_mono _ _ ) using 2 <;> norm_num [ hLeq ] ; ring;
        refine' tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_right _ _;
        · filter_upwards [ Ioo_mem_nhdsGT hx₀.2 ] with y hy using hf ⟨ by linarith [ hy.1, hx₀.1 ], by linarith [ hy.2, hx₀.2 ] ⟩ ⟨ by linarith [ hy.1, hx₀.1 ], by linarith [ hy.2, hx₀.2 ] ⟩ hy.1.le;
        · filter_upwards [ Ioo_mem_nhdsGT ( show x₀ < ( x₀ + b ) / 2 by linarith [ hx₀.2 ] ) ] with y hy;
          have := Exercise_11_9_3.integ_incr_bounds hf ⟨ by linarith [ hy.1, hx₀.1 ], by linarith [ hy.2, hx₀.2 ] ⟩ ⟨ by linarith [ hy.1, hx₀.1 ], by linarith [ hy.2, hx₀.2 ] ⟩ ( show y < 2 * y - x₀ by linarith [ hy.1, hy.2 ] );
          rw [ mul_div, div_sub_div, le_div_iff₀ ] <;> nlinarith [ hy.1, hy.2 ];
      -- STEP 3: LEFT LIMIT `Tendsto f (𝓝[<] x₀) (𝓝 (f x₀))`, symmetric squeeze with lower bound `fun y => 2 * slope F x₀ (2*y - x₀) - slope F x₀ y` and upper bound `fun _ => f x₀`.
      have h_left : Filter.Tendsto f (nhdsWithin x₀ (Set.Iio x₀)) (nhds (f x₀)) := by
        -- For `y ∈ Set.Ioo ((a+x₀)/2) x₀` (so `a < 2*y - x₀ < y < x₀`), apply `Exercise_11_9_3.integ_incr_bounds hf (h2 : 2*y-x₀ ∈ Icc a b) (hy : y ∈ Icc a b) (by linarith : 2*y-x₀ < y)`, whose UPPER part reads `F y - F (2*y-x₀) ≤ f y * (y - (2*y-x₀)) = f y * (x₀ - y)`; rearrange to `2*slope F x₀ (2*y-x₀) - slope F x₀ y ≤ f y` (same algebraic identity as Step 2).
        have h_left_bound : ∀ᶠ y in nhdsWithin x₀ (Set.Iio x₀), 2 * ((integ f (Icc a (2 * y - x₀)) - integ f (Icc a x₀)) / ((2 * y - x₀) - x₀)) - ((integ f (Icc a y) - integ f (Icc a x₀)) / (y - x₀)) ≤ f y := by
          filter_upwards [ Ioo_mem_nhdsLT ( show ( a + x₀ ) / 2 < x₀ by linarith [ hx₀.1 ] ) ] with y hy;
          have := Exercise_11_9_3.integ_incr_bounds hf ( show 2 * y - x₀ ∈ Set.Icc a b from ⟨ by linarith [ hy.1, hy.2, hx₀.1, hx₀.2 ], by linarith [ hy.1, hy.2, hx₀.1, hx₀.2 ] ⟩ ) ( show y ∈ Set.Icc a b from ⟨ by linarith [ hy.1, hy.2, hx₀.1, hx₀.2 ], by linarith [ hy.1, hy.2, hx₀.1, hx₀.2 ] ⟩ ) ( by linarith [ hy.1, hy.2, hx₀.1, hx₀.2 ] : 2 * y - x₀ < y );
          rw [ mul_div, div_sub_div, div_le_iff₀ ] <;> nlinarith [ hy.1, hy.2 ];
        -- Both bounds tend to `f x₀` (const, and the `hup`-type combination via `hslope_lt` and `g` mapping `𝓝[<]x₀ → 𝓝[<]x₀`).
        have h_left_tendsto : Filter.Tendsto (fun y => 2 * ((integ f (Icc a (2 * y - x₀)) - integ f (Icc a x₀)) / ((2 * y - x₀) - x₀)) - ((integ f (Icc a y) - integ f (Icc a x₀)) / (y - x₀))) (nhdsWithin x₀ (Set.Iio x₀)) (nhds (f x₀)) := by
          have h_left_tendsto : Filter.Tendsto (fun y => ((integ f (Icc a (2 * y - x₀)) - integ f (Icc a x₀)) / ((2 * y - x₀) - x₀))) (nhdsWithin x₀ (Set.Iio x₀)) (nhds (f x₀)) := by
            convert h_slope.comp ( show Filter.Tendsto ( fun y : ℝ => 2 * y - x₀ ) ( nhdsWithin x₀ ( Set.Iio x₀ ) ) ( nhdsWithin x₀ { x₀ } ᶜ ) from ?_ ) using 2;
            · linarith;
            · refine' Filter.Tendsto.inf _ _ <;> norm_num;
              · exact Continuous.tendsto' ( by continuity ) _ _ ( by ring );
              · intros; linarith;
          convert Filter.Tendsto.sub ( h_left_tendsto.const_mul 2 ) ( h_slope.mono_left <| nhdsWithin_mono _ _ ) using 2 <;> norm_num [ hLeq ] ; ring;
        refine' tendsto_of_tendsto_of_tendsto_of_le_of_le' h_left_tendsto tendsto_const_nhds _ _;
        · exact h_left_bound;
        · filter_upwards [ Ioo_mem_nhdsLT hx₀.1 ] with y hy using hf ⟨ by linarith [ hy.1, hx₀.1 ], by linarith [ hy.2, hx₀.2 ] ⟩ ⟨ by linarith [ hy.1, hx₀.1 ], by linarith [ hy.2, hx₀.2 ] ⟩ hy.2.le;
      refine' ContinuousAt.continuousWithinAt _;
      exact continuousAt_iff_continuous_left'_right'.mpr ⟨ h_left, h_right ⟩

/-- Exercise 11.9.3 (corrected to interior points).

    The statement as originally posed allowed {lit}`x₀` to be an endpoint of {lit}`[a,b]`,
    but in that form it is FALSE: e.g. with {lit}`a = 0`, {lit}`b = 1`, {lit}`f 0 = 0` and
    {lit}`f x = 1` for `x ∈ (0,1]`, the function {lit}`f` is monotone, `F x = ∫₀ˣ f = x` is
    differentiable within {lit}`[0,1]` at {lit}`0` (with derivative {lit}`1`), yet {lit}`f` is not
    continuous within {lit}`[0,1]` at {lit}`0`. The equivalence is valid precisely at
    interior points, so we require {lit}`x₀ ∈ Ioo a b`. The original (false) statement
    is retained, commented out, below. -/
theorem Exercise_11_9_3 {a b x₀:ℝ} (hx₀: x₀ ∈ Set.Ioo a b) {f: ℝ → ℝ}
    (hf: MonotoneOn f (Icc a b)) :
    DifferentiableWithinAt ℝ (fun x => integ f (Icc a x)) (Icc a b) x₀ ↔
    ContinuousWithinAt f (Icc a b) x₀ := by
  constructor
  · intro hdiff
    exact Exercise_11_9_3.cts_of_diff hx₀ hf hdiff
  · intro hcts
    have hab : a < b := lt_trans hx₀.1 hx₀.2
    exact (deriv_of_integ hab (integ_of_monotone hf)
      (Set.Ioo_subset_Icc_self hx₀) hcts).differentiableWithinAt

/-- Exercise 11.9.3 -/
example {a b x₀:ℝ} (hab: a < b) (hx₀: x₀ ∈ Ioo a b) {f: ℝ → ℝ} (hf: MonotoneOn f (Icc a b)) :
  DifferentiableWithinAt ℝ (fun x => integ f (Icc a x)) (Icc a b) x₀ ↔
  ContinuousWithinAt f (Icc a b) x₀ := by
  have hx₀' : x₀ ∈ Set.Ioo a b := by
    simpa [BoundedInterval.set_Ioo] using hx₀
  have := hab
  exact Exercise_11_9_3 hx₀' hf

end Chapter11

/-- Exercise 11.6.5, moved to Section 11.9 -/
theorem Chapter7.Series.converges_qseries' (p:ℝ) : (mk' (m := 1) fun n ↦ 1 / (n:ℝ) ^ p : Series).converges ↔ (p>1) := by
  set s := (mk' (m := 1) fun n ↦ 1 / (n:ℝ) ^ p : Series) with hs
  constructor
  · intro hs_conv
    by_contra! hp  -- hp : p ≤ 1
    by_cases hp_pos : 0 < p
    · have h := (Series.converges_qseries p hp_pos).mp hs_conv
      linarith
    · -- p ≤ 0
      have hp_nonpos : p ≤ 0 := by linarith
      have h_no_decay : ¬ Filter.atTop.Tendsto s.seq (nhds 0) := by
        intro h_tendsto
        rw [Metric.tendsto_nhds] at h_tendsto
        have h_ball := h_tendsto (1/2) (by norm_num)
        rcases Filter.eventually_atTop.mp h_ball with ⟨N, hN⟩
        set n := max N 1 with hn
        have hn_ge_N : n ≥ N := le_max_left _ _
        have hn_ge_one : n ≥ (1 : ℤ) := le_max_right _ _
        have h_seq_ge_one : s.seq n ≥ 1 := by
          dsimp [s]
          simp [hn_ge_one]
          have hn_nonneg_int : 0 ≤ n := by omega
          have hn_nonneg_real : 0 ≤ (n : ℝ) := by exact_mod_cast hn_nonneg_int
          have hn_ge_one_real : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_one
          have hneg_nonneg : 0 ≤ -p := by linarith
          calc
            ((n : ℝ) ^ p)⁻¹ = (n : ℝ) ^ (-p) := by
              rw [← Real.rpow_neg hn_nonneg_real]
            _ ≥ (1 : ℝ) ^ (-p) :=
              Real.rpow_le_rpow (by norm_num) hn_ge_one_real hneg_nonneg
            _ = 1 := by simp
        have h_dist : dist (s.seq n) 0 < 1/2 := hN n hn_ge_N
        have h_contra : dist (s.seq n) 0 ≥ 1 := by
          rw [Real.dist_eq, sub_zero]
          have h_nonneg : 0 ≤ s.seq n := by
            dsimp [s]; simp [hn_ge_one]; positivity
          rw [abs_of_nonneg h_nonneg]
          exact h_seq_ge_one
        linarith
      exact h_no_decay (Series.decay_of_converges hs_conv)
  · intro hp
    have hp_pos : 0 < p := by linarith
    exact (Series.converges_qseries p hp_pos).mpr hp

theorem Chapter7.Series.converges_qseries'' (p:ℝ) : (mk' (m := 1) fun n ↦ 1 / (n:ℝ) ^ p : Series).absConverges ↔ (p>1) := by
  set s := (mk' (m := 1) fun n ↦ 1 / (n:ℝ) ^ p : Series) with hs
  have h_nonneg : ∀ n, |s.seq n| = s.seq n := by
    intro n
    by_cases h : (1 : ℤ) ≤ n
    · have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := by
        have : (0 : ℤ) ≤ n := by omega
        exact_mod_cast this
      have hpos : 0 ≤ 1 / (n : ℝ) ^ p :=
        div_nonneg (by norm_num) (Real.rpow_nonneg hn_nonneg p)
      dsimp [s]
      split_ifs with hcond
      · rw [abs_of_nonneg hpos]
      · exfalso; exact hcond h
    · have hzero : s.seq n = 0 := by
        dsimp [s]
        simp [h]
      simp [hzero, abs_zero]
  have h_abs_eq : s.abs = s := by
    apply Series.ext
    · rfl
    · ext n
      by_cases hn : (1 : ℤ) ≤ n
      · have hpos : 0 ≤ 1 / ((n : ℝ) ^ p) := by
          have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := by
            have : (0 : ℤ) ≤ n := by omega
            exact_mod_cast this
          exact div_nonneg (by norm_num) (Real.rpow_nonneg hn_nonneg p)
        dsimp [Series.abs, Series.mk', s]
        split_ifs with hcond
        · rw [abs_of_nonneg hpos]
        · exfalso; exact hcond hn
      · dsimp [Series.abs, Series.mk', s]
        split_ifs with hcond
        · exfalso; exact hn hcond
        · rfl
  dsimp [Series.absConverges]
  rw [h_abs_eq]
  exact converges_qseries' p
