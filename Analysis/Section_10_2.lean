import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Abs
import Analysis.Section_9_6
/-!
# Analysis I, Section 10.2: Local maxima, local minima, and derivatives

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Relation between local extrema and derivatives.
- Rolle's theorem.
- mean value theorem.

-/

open Chapter9
namespace Chapter10

/-- Definition 10.2.1 (Local maxima and minima).  Here we use Mathlib's {name}`IsLocalMaxOn` type. -/
theorem IsLocalMaxOn.iff (X:Set ℝ) (f:ℝ → ℝ) (x₀:ℝ) :
  IsLocalMaxOn f X x₀ ↔
  ∃ δ > 0, IsMaxOn f (X ∩ .Ioo (x₀ - δ) (x₀ + δ)) x₀ := by
  simp [isMaxOn_iff, IsLocalMaxOn, IsMaxFilter, nhdsWithin.eq_1, Filter.eventually_inf_principal,
        Metric.eventually_nhds_iff, Real.dist_eq, abs_sub_lt_iff]
  peel 3; constructor <;> intro h _ _ _ <;> apply h <;> grind

theorem IsLocalMinOn.iff (X:Set ℝ) (f:ℝ → ℝ) (x₀:ℝ) :
  IsLocalMinOn f X x₀ ↔
  ∃ δ > 0, IsMinOn f (X ∩ .Ioo (x₀ - δ) (x₀ + δ)) x₀ := by
  simp [isMinOn_iff, IsLocalMinOn, IsMinFilter, nhdsWithin.eq_1, Filter.eventually_inf_principal,
        Metric.eventually_nhds_iff, Real.dist_eq, abs_sub_lt_iff]
  peel 3; constructor <;> intro h _ _ _ <;> apply h <;> grind

/-- Example 10.2.3 -/
abbrev f_10_2_3 : ℝ → ℝ := fun x ↦ x^2 - x^4

example : ¬ IsMinOn f_10_2_3 .univ 0 := by
  intro h
  have : (0:ℝ)^2 - 0^4 ≤ 2^2 - 2^4 := h (by trivial : 2 ∈ Set.univ)
  norm_num at this

example : IsMinOn f_10_2_3 (.Ioo (-1) 1) 0 := by
  intro x hx
  simp [f_10_2_3]
  have h1 : 0 ≤ x^2 := sq_nonneg x
  have h2 : x^2 < 1 := by
    rw [sq_lt_one_iff_abs_lt_one]
    exact abs_lt.mpr hx
  calc x^4 = x^2 * x^2 := by ring
    _ ≤ 1 * x^2 := by nlinarith
    _ = x^2 := by ring

example : IsLocalMinOn f_10_2_3 .univ 0 := by
  rw [IsLocalMinOn.iff]
  use 1, by norm_num
  intro x ⟨_, hx⟩
  simp [f_10_2_3]
  have h2 : x^2 < 1 := by
    rw [sq_lt_one_iff_abs_lt_one]
    simp at hx
    exact abs_lt.mpr hx
  calc x^4 = x^2 * x^2 := by ring
    _ ≤ 1 * x^2 := by nlinarith [sq_nonneg x]
    _ = x^2 := by ring

/-- Example 10.2.4 -/
example : ¬ ∃ x, IsMaxOn (· : ℝ → ℝ)  ((↑· : ℤ → ℝ) '' .univ) x := by
  intro ⟨x, hx⟩
  have : ∀ n : ℤ, (n : ℝ) ≤ x := fun n => hx ⟨n, Set.mem_univ _, rfl⟩
  have h1 := this (⌊x⌋ + 1)
  have h2 : x < (⌊x⌋ + 1 : ℤ) := by
    have : x < ⌊x⌋ + 1 := Int.lt_floor_add_one x
    exact_mod_cast this
  linarith

example : ¬ ∃ x, IsMinOn (· : ℝ → ℝ)  ((↑· : ℤ → ℝ) '' .univ) x := by
  intro ⟨x, hx⟩
  have : ∀ n : ℤ, x ≤ (n : ℝ) := fun n => hx ⟨n, Set.mem_univ _, rfl⟩
  have h1 := this (⌊x⌋ - 1)
  have h2 : (⌊x⌋ - 1 : ℤ) < x := by
    have : ⌊x⌋ - 1 < x := by linarith [Int.floor_le x]
    exact_mod_cast this
  linarith

example (n:ℤ) : IsLocalMaxOn (· : ℝ → ℝ)  ((↑· : ℤ → ℝ) '' .univ) n := by
  rw [IsLocalMaxOn.iff]
  use 1, by norm_num
  intro y ⟨⟨m, _, hm⟩, hy⟩
  subst hm
  simp at hy
  have : m = n := by
    by_contra! hne
    have hmem : (m : ℝ) ∈ Set.Ioo ((n : ℝ) - 1) ((n : ℝ) + 1) := hy
    have h_abs_lt : |(m : ℝ) - (n : ℝ)| < 1 := by
      rw [abs_lt]
      constructor <;> nlinarith
    have h_dist : (1 : ℝ) ≤ |(m : ℝ) - (n : ℝ)| := by
      have h_int : (1 : ℤ) ≤ |(m : ℤ) - n| := by
        have hpos : (m : ℤ) - n ≠ 0 := sub_ne_zero.mpr hne
        have h_abs_pos : 0 < |(m : ℤ) - n| := abs_pos.mpr hpos
        omega
      have h_cast : (1 : ℝ) ≤ |((m : ℤ) - n : ℤ)| := by exact_mod_cast h_int
      simpa [Int.cast_sub, Int.cast_abs] using h_cast
    nlinarith
  simp [this]

example (n:ℤ) : IsLocalMinOn (· : ℝ → ℝ)  ((↑· : ℤ → ℝ) '' .univ) n := by
  rw [IsLocalMinOn.iff]
  use 1, by norm_num
  intro y ⟨⟨m, _, hm⟩, hy⟩
  subst hm
  simp at hy
  have : m = n := by
    by_contra! hne
    have hmem : (m : ℝ) ∈ Set.Ioo ((n : ℝ) - 1) ((n : ℝ) + 1) := hy
    have h_abs_lt : |(m : ℝ) - (n : ℝ)| < 1 := by
      rw [abs_lt]
      constructor <;> nlinarith
    have h_dist : (1 : ℝ) ≤ |(m : ℝ) - (n : ℝ)| := by
      have h_int : (1 : ℤ) ≤ |(m : ℤ) - n| := by
        have hpos : (m : ℤ) - n ≠ 0 := sub_ne_zero.mpr hne
        have h_abs_pos : 0 < |(m : ℤ) - n| := abs_pos.mpr hpos
        omega
      have h_cast : (1 : ℝ) ≤ |((m : ℤ) - n : ℤ)| := by exact_mod_cast h_int
      simpa [Int.cast_sub, Int.cast_abs] using h_cast
    nlinarith
  simp [this]

/-- Remark 10.2.5 -/
theorem IsLocalMaxOn.of_restrict {X Y:Set ℝ} (hXY: Y ⊆ X) (f:ℝ → ℝ) (x₀:ℝ)
  (h: IsLocalMaxOn f X x₀) : IsLocalMaxOn f Y x₀ := by
  rw [IsLocalMaxOn.iff] at h ⊢
  obtain ⟨δ, hδ, hmax⟩ := h
  use δ, hδ
  intro y ⟨hy1, hy2⟩
  exact hmax ⟨hXY hy1, hy2⟩

theorem IsLocalMinOn.of_restrict {X Y:Set ℝ} (hXY: Y ⊆ X) (f:ℝ → ℝ) (x₀:ℝ)
  (h: IsLocalMinOn f X x₀) : IsLocalMinOn f Y x₀ := by
  rw [IsLocalMinOn.iff] at h ⊢
  obtain ⟨δ, hδ, hmin⟩ := h
  use δ, hδ
  intro y ⟨hy1, hy2⟩
  exact hmin ⟨hXY hy1, hy2⟩

/-- Proposition 10.2.6 (Local extrema are stationary) / Exercise 10.2.1 -/
theorem IsLocalMaxOn.deriv_eq_zero {a b:ℝ} {f:ℝ → ℝ} {x₀:ℝ}
  (hx₀: x₀ ∈ Set.Ioo a b) (h: IsLocalMaxOn f (.Ioo a b) x₀) {L:ℝ}
  (hderiv: HasDerivWithinAt f L (.Ioo a b) x₀) : L = 0 := by
  have hint : Set.Ioo a b ∈ nhds x₀ := isOpen_Ioo.mem_nhds hx₀
  have hderiv' : HasDerivAt f L x₀ := HasDerivWithinAt.hasDerivAt hderiv hint
  have hmax : IsLocalMax f x₀ := IsLocalMaxOn.isLocalMax h hint
  exact IsLocalMax.hasDerivAt_eq_zero hmax hderiv'

/-- Proposition 10.2.6 (Local extrema are stationary) / Exercise 10.2.1 -/
theorem IsLocalMinOn.deriv_eq_zero {a b:ℝ} {f:ℝ → ℝ} {x₀:ℝ}
  (hx₀: x₀ ∈ Set.Ioo a b) (h: IsLocalMinOn f (.Ioo a b) x₀) {L:ℝ}
  (hderiv: HasDerivWithinAt f L (.Ioo a b) x₀) : L = 0 := by
  have hint : Set.Ioo a b ∈ nhds x₀ := isOpen_Ioo.mem_nhds hx₀
  have hderiv' : HasDerivAt f L x₀ := HasDerivWithinAt.hasDerivAt hderiv hint
  have hmin : IsLocalMin f x₀ := IsLocalMinOn.isLocalMin h hint
  exact IsLocalMin.hasDerivAt_eq_zero hmin hderiv'

theorem IsMaxOn.deriv_eq_zero_counter : ∃ (a b:ℝ) (f:ℝ → ℝ)
  (x₀:ℝ) (_hx₀: x₀ ∈ Set.Icc a b) (_h: IsMaxOn f (.Icc a b) x₀) (L:ℝ)
  (_hderiv: HasDerivWithinAt f L (.Icc a b) x₀), L ≠ 0 := by
  use 0, 1, id, 1
  refine ⟨by norm_num, ?_, 1, ?_, by norm_num⟩
  · intro y hy; simp; exact hy.2
  · simpa using hasDerivWithinAt_id (s := Set.Icc (0 : ℝ) (1 : ℝ)) (x := (1 : ℝ))

/-- Theorem 10.2.7 (Rolle's theorem) / Exercise 10.2.4 -/
theorem _root_.HasDerivWithinAt.exist_zero {a b:ℝ} (hab: a < b) {g:ℝ → ℝ}
  (hcont: ContinuousOn g (.Icc a b)) (hderiv: DifferentiableOn ℝ g (.Ioo a b))
  (hgab: g a = g b) : ∃ x ∈ Set.Ioo a b, HasDerivWithinAt g 0 (.Ioo a b) x := by
  obtain ⟨x, hx, hderiv'⟩ := exists_deriv_eq_zero hab hcont hgab
  use x, hx
  have hint : Set.Ioo a b ∈ nhds x := isOpen_Ioo.mem_nhds hx
  have hdiff : DifferentiableAt ℝ g x := (hderiv x hx).differentiableAt hint
  have : HasDerivAt g (deriv g x) x := hdiff.hasDerivAt
  rw [hderiv'] at this
  exact this.hasDerivWithinAt

/-- Corollary 10.2.9 (Mean value theorem ) / Exercise 10.2.5 -/
theorem _root_.HasDerivWithinAt.mean_value {a b:ℝ} (hab: a < b) {f:ℝ → ℝ}
  (hcont: ContinuousOn f (.Icc a b)) (hderiv: DifferentiableOn ℝ f (.Ioo a b)) :
  ∃ x ∈ Set.Ioo a b, HasDerivWithinAt f ((f b - f a) / (b - a)) (.Ioo a b) x := by
  have : ∀ x ∈ Set.Ioo a b, HasDerivAt f (deriv f x) x := by
    intro x hx
    have hint : Set.Ioo a b ∈ nhds x := isOpen_Ioo.mem_nhds hx
    exact (hderiv x hx).differentiableAt hint |>.hasDerivAt
  obtain ⟨x, hx, hderiv'⟩ := exists_hasDerivAt_eq_slope f (deriv f) hab hcont this
  use x, hx
  have hint : Set.Ioo a b ∈ nhds x := isOpen_Ioo.mem_nhds hx
  have : HasDerivAt f (deriv f x) x := (hderiv x hx).differentiableAt hint |>.hasDerivAt
  rw [hderiv'] at this
  exact this.hasDerivWithinAt

/-- Exercise 10.2.2 -/
example : ∃ f:ℝ → ℝ, ContinuousOn f (.Icc (-1) 1) ∧
  IsMaxOn f (.Icc (-1) 1) 0 ∧ ¬ DifferentiableWithinAt ℝ f (.Icc (-1) 1) 0 := by
  use fun x => -|x|
  constructor
  · exact continuous_abs.neg.continuousOn
  constructor
  · intro x _; simp
  · intro h
    have hpos : Set.Icc (-1 : ℝ) 1 ∈ nhds (0 : ℝ) := by
      refine mem_nhds_iff.mpr ⟨Set.Ioo (-1) 1, Set.Ioo_subset_Icc_self, isOpen_Ioo, ?_⟩
      exact Set.mem_Ioo.mpr ⟨by norm_num, by norm_num⟩
    have hdiff_neg_abs : DifferentiableAt ℝ (fun x : ℝ ↦ -|x|) (0 : ℝ) :=
      h.differentiableAt hpos
    have hdiff_abs : DifferentiableAt ℝ (fun x : ℝ ↦ |x|) (0 : ℝ) := by
      simpa [neg_neg] using hdiff_neg_abs.neg
    have : ¬ DifferentiableAt ℝ (fun x : ℝ ↦ |x|) (0 : ℝ) :=
      not_differentiableAt_abs_zero
    exact this hdiff_abs

/-- Exercise 10.2.3 -/
example : ∃ f:ℝ → ℝ, DifferentiableOn ℝ f (.Icc (-1) 1) ∧
  HasDerivWithinAt f 0 (.Ioo (-1) 1) 0 ∧
  ¬ IsLocalMaxOn f (.Icc (-1) 1) 0 ∧ ¬ IsLocalMinOn f (.Icc (-1) 1) 0 := by
  -- Use f(x) = x³
  use fun x => x^3
  constructor
  · apply DifferentiableOn.pow; exact differentiableOn_id
  constructor
  · have : HasDerivAt (fun (x : ℝ) => x^3) 0 (0 : ℝ) := by
      simpa using hasDerivAt_pow (3 : ℕ) (0 : ℝ)
    exact this.hasDerivWithinAt
  constructor
  · intro h
    rw [IsLocalMaxOn.iff] at h
    obtain ⟨δ, hδ, hmax⟩ := h
    have hpos : 0 < min (δ/2) (1/2) := by
      refine lt_min_iff.mpr ⟨by nlinarith, by norm_num⟩
    have hx_mem : min (δ/2) (1/2) ∈ (Set.Icc (-1 : ℝ) 1 ∩ Set.Ioo (0 - δ) (0 + δ)) := by
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · linarith
      · have : min (δ/2) (1/2) ≤ 1/2 := min_le_right _ _
        linarith
      · nlinarith
      · by_cases hcase : δ/2 ≤ 1/2
        · have hmin_val : min (δ/2) (1/2) = δ/2 := min_eq_left hcase
          rw [hmin_val]
          nlinarith
        · have hmin_val : min (δ/2) (1/2) = 1/2 := min_eq_right (by linarith)
          rw [hmin_val]
          nlinarith
    have h1 : (min (δ/2) (1/2))^3 ≤ 0^3 := hmax hx_mem
    simp at h1
    have h_cube_pos : 0 < (min (δ/2) (1/2))^3 := by positivity
    linarith
  · intro h
    rw [IsLocalMinOn.iff] at h
    obtain ⟨δ, hδ, hmin⟩ := h
    have hpos : 0 < min (δ/2) (1/2) := by
      refine lt_min_iff.mpr ⟨by nlinarith, by norm_num⟩
    have hz_mem : -(min (δ/2) (1/2)) ∈ (Set.Icc (-1 : ℝ) 1 ∩ Set.Ioo (0 - δ) (0 + δ)) := by
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · have : min (δ/2) (1/2) ≤ 1 := by
          calc
            min (δ/2) (1/2) ≤ 1/2 := min_le_right _ _
            _ ≤ 1 := by norm_num
        linarith
      · linarith
      · by_cases hcase : δ/2 ≤ 1/2
        · have hmin_val : min (δ/2) (1/2) = δ/2 := min_eq_left hcase
          rw [hmin_val]
          nlinarith
        · have hmin_val : min (δ/2) (1/2) = 1/2 := min_eq_right (by linarith)
          rw [hmin_val]
          nlinarith
      · nlinarith
    have h1 : 0^3 ≤ (-(min (δ/2) (1/2)))^3 := hmin hz_mem
    simp at h1
    have h_cube_neg : (-(min (δ/2) (1/2)))^3 < 0 := by
      have hneg : -(min (δ/2) (1/2)) < 0 := by linarith
      have hpos_cube : 0 < (min (δ/2) (1/2))^3 := by positivity
      calc
        (-(min (δ/2) (1/2)))^3 = -((min (δ/2) (1/2))^3) := by ring
        _ < 0 := by linarith
    linarith

/-- Exercise 10.2.6 -/
theorem lipschitz_bound {M a b:ℝ} (hM: M > 0) (hab: a < b) {f:ℝ → ℝ}
  (hcont: ContinuousOn f (.Icc a b))
  (hderiv: DifferentiableOn ℝ f (.Ioo a b))
  (hlip: ∀ x ∈ Set.Ioo a b, |derivWithin f (.Ioo a b) x| ≤ M)
  {x y:ℝ} (hx: x ∈ Set.Ioo a b) (hy: y ∈ Set.Ioo a b) :
  |f x - f y| ≤ M * |x - y| := by
  wlog hxy : x ≤ y
  · rw [abs_sub_comm, abs_sub_comm x y]
    exact this hM hab hcont hderiv hlip hy hx (by linarith)
  rcases eq_or_lt_of_le hxy with rfl | hxy'
  · simp
  -- Apply MVT on [x, y]
  have : ∃ c ∈ Set.Ioo x y, HasDerivWithinAt f ((f y - f x) / (y - x)) (.Ioo x y) c := by
    apply HasDerivWithinAt.mean_value hxy'
    · exact hcont.mono (Set.Icc_subset_Icc (le_of_lt hx.1) (le_of_lt hy.2))
    · exact hderiv.mono (Set.Ioo_subset_Ioo (le_of_lt hx.1) (le_of_lt hy.2))
  obtain ⟨c, hc, hderiv'⟩ := this
  have hderiv_eq : derivWithin f (.Ioo a b) c = (f y - f x) / (y - x) := by
    have hint : Set.Ioo x y ∈ nhds c := isOpen_Ioo.mem_nhds hc
    have hc' : c ∈ Set.Ioo a b := ⟨hx.1.trans hc.1, hc.2.trans hy.2⟩
    have hmem : Set.Ioo a b ∈ nhds c := isOpen_Ioo.mem_nhds hc'
    have hdiff : DifferentiableAt ℝ f c := (hderiv c hc').differentiableAt hmem
    have hderivAt_mvt : HasDerivAt f ((f y - f x) / (y - x)) c := hderiv'.hasDerivAt hint
    have hderivAt_deriv : HasDerivAt f (deriv f c) c := hdiff.hasDerivAt
    have h_derivWithin_eq_deriv : derivWithin f (.Ioo a b) c = deriv f c :=
      derivWithin_of_mem_nhds hmem
    rw [h_derivWithin_eq_deriv]
    exact hderivAt_deriv.unique hderivAt_mvt
  have hc' : c ∈ Set.Ioo a b := ⟨hx.1.trans hc.1, hc.2.trans hy.2⟩
  have hbound := hlip c hc'
  rw [hderiv_eq] at hbound
  have : |(f y - f x) / (y - x)| ≤ M := hbound
  have hne : y - x ≠ 0 := by linarith
  have hpos_abs : 0 < |y - x| := abs_pos.mpr hne
  rw [abs_div] at this
  have : |f y - f x| ≤ M * |y - x| := by
    calc
      |f y - f x| = (|f y - f x| / |y - x|) * |y - x| := by field_simp [hpos_abs.ne']
      _ ≤ M * |y - x| := mul_le_mul_of_nonneg_right this (by linarith)
  calc |f x - f y| = |f y - f x| := abs_sub_comm _ _
    _ ≤ M * |y - x| := this
    _ = M * |x - y| := by rw [abs_sub_comm]

/-- Exercise 10.2.7 -/
theorem _root_.UniformContinuousOn.of_lipschitz {f:ℝ → ℝ}
  (hcont: ContinuousOn f .univ)
  (hderiv: DifferentiableOn ℝ f .univ)
  (hlip: BddOn (deriv f) .univ) :
  UniformContinuousOn f (.univ) := by
  obtain ⟨M, hM⟩ := hlip
  -- Show that f is Lipschitz continuous with constant M
  have : ∀ x y : ℝ, |f x - f y| ≤ M * |x - y| := by
    intro x y
    by_cases h : x = y
    · simp [h]
    · sorry  -- This requires extending lipschitz_bound to the whole real line
  sorry


end Chapter10
