import Mathlib.Tactic
import Mathlib.Data.Real.Sign
import Analysis.Section_9_3
import Analysis.Section_9_4

/-!
# Analysis I, Section 9.6: The maximum principle

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Continuous functions on closed and bounded intervals are bounded.
- Continuous functions on closed and bounded intervals attain their maximum and minimum.
-/

namespace Chapter9

/-- Definition 9.6.1 -/
abbrev BddAboveOn (f:ℝ → ℝ) (X:Set ℝ) : Prop := ∃ M, ∀ x ∈ X, f x ≤ M

abbrev BddBelowOn (f:ℝ → ℝ) (X:Set ℝ) : Prop := ∃ M, ∀ x ∈ X, -M ≤ f x

abbrev BddOn (f:ℝ → ℝ) (X:Set ℝ) : Prop := ∃ M, ∀ x ∈ X, |f x| ≤ M

/-- Remark 9.6.2 -/
theorem BddOn.iff (f:ℝ → ℝ) (X:Set ℝ) : BddOn f X ↔ BddAboveOn f X ∧ BddBelowOn f X := by
  constructor
  · intro h
    rcases h with ⟨M, hM⟩
    constructor
    · use M; intro x hx; have hx' := hM x hx; rw [abs_le] at hx'; exact hx'.right
    · use M; intro x hx; have hx' := hM x hx; rw [abs_le] at hx'; exact hx'.left
  · intro ⟨⟨M1, hM1⟩, ⟨M2, hM2⟩⟩
    use max M1 M2
    intro x hx
    rw [abs_le]
    constructor
    · have hx' := hM2 x hx; have hmax : max M1 M2 ≥ M2 := le_max_right _ _; nlinarith
    · have hx' := hM1 x hx; have hmax : max M1 M2 ≥ M1 := le_max_left _ _; nlinarith

theorem BddOn.iff' (f:ℝ → ℝ) (X:Set ℝ) :  BddOn f X ↔ Bornology.IsBounded (f '' X) := by
  constructor
  · rintro ⟨M, hM⟩
    refine (Metric.isBounded_iff.mpr ?_)
    use 2*M
    rintro y ⟨x, hx, rfl⟩ z ⟨x', hx', rfl⟩
    rw [Real.dist_eq]
    calc
      |f x - f x'| ≤ |f x| + |f x'| := abs_sub _ _
      _ ≤ M + M := by nlinarith [hM x hx, hM x' hx']
      _ = 2*M := by ring
  · intro h
    rcases Metric.isBounded_iff.mp h with ⟨C, hC⟩
    by_cases hX : X.Nonempty
    · rcases hX with ⟨x₀, hx₀⟩
      have hx0_img : f x₀ ∈ f '' X := Set.mem_image_of_mem f hx₀
      use C + |f x₀|
      intro x hx
      have hx_img : f x ∈ f '' X := Set.mem_image_of_mem f hx
      have hdist : dist (f x) (f x₀) ≤ C := hC hx_img hx0_img
      rw [Real.dist_eq] at hdist
      have hx_bound : |f x| ≤ |f x - f x₀| + |f x₀| := by
        calc
          |f x| = |(f x - f x₀) + f x₀| := by ring
          _ ≤ |f x - f x₀| + |f x₀| := abs_add_le _ _
      nlinarith
    · use 0
      intro x hx; exfalso; exact hX ⟨x, hx⟩

theorem BddOn.of_bounded {f :ℝ → ℝ} {X: Set ℝ} {M:ℝ} (h: ∀ x ∈ X, |f x| ≤ M) : BddOn f X := by use M

example : Continuous (fun x:ℝ ↦ x) := by
  exact continuous_id

example : ¬ BddOn (fun x:ℝ ↦ x) .univ  := by
  intro h; rcases h with ⟨M, hM⟩
  have hM0 : |(0 : ℝ)| ≤ M := hM 0 trivial
  have hpos : |0| = (0 : ℝ) := by norm_num
  have hM_nonneg : 0 ≤ M := by
    have : |(0 : ℝ)| = 0 := abs_zero
    rw [this] at hM0; nlinarith
  have hM1 : |M + 1| ≤ M := hM (M+1) trivial
  have : |M + 1| = M + 1 := abs_of_pos (by nlinarith)
  rw [this] at hM1; nlinarith

example : BddOn (fun x:ℝ ↦ x) (.Icc 1 2) := by
  use 2
  intro x hx; rcases hx with ⟨hx1, hx2⟩
  rw [abs_le]; constructor <;> nlinarith

example : ContinuousOn (fun x:ℝ ↦ 1/x) (.Ioo 0 1) := by
  refine (continuousOn_const.div continuousOn_id ?_)
  intro x hx; exact ne_of_gt hx.1

example : ¬ BddOn (fun x:ℝ ↦ 1/x) (.Ioo 0 1) := by
  intro h; rcases h with ⟨M, hM⟩
  have hmax_pos : 0 < max M 1 := by
    have : (0 : ℝ) < 1 := by norm_num
    exact lt_of_lt_of_le this (le_max_right _ _)
  set x := 1 / (2 * max M 1) with hx
  have hx_mem : x ∈ Set.Ioo (0 : ℝ) 1 := by
    dsimp [x]
    have hpos : 2 * max M 1 > 0 := mul_pos (by norm_num : (0 : ℝ) < 2) hmax_pos
    have h_lt : 2 * max M 1 > (1 : ℝ) := by
      have hmax_ge_one : max M 1 ≥ 1 := le_max_right _ _
      nlinarith
    constructor
    · positivity
    · have hxpos : 0 < x := div_pos (by norm_num) (mul_pos (by norm_num) hmax_pos)
      have hxlt : x < 1 := by
        dsimp [x]
        have hpos' : 0 < 2 * max M 1 := mul_pos (by norm_num) hmax_pos
        apply (div_lt_one ?_).mpr ?_
        · positivity
        · have hmax_ge_one : max M 1 ≥ 1 := le_max_right _ _
          nlinarith
      exact hxlt
  have h_val : |(fun x : ℝ ↦ 1 / x) x| = 2 * max M 1 := by
    dsimp [x]
    have hpos' : 2 * max M 1 > 0 := mul_pos (by norm_num : (0 : ℝ) < 2) hmax_pos
    calc
      |1 / (1 / (2 * max M 1))| = |(2 * max M 1)| := by
        field_simp [show 2 * max M 1 ≠ 0 from by nlinarith]
      _ = 2 * max M 1 := abs_of_pos hpos'
  have h_contra := hM x hx_mem
  rw [h_val] at h_contra
  have hmax_ge_M : max M 1 ≥ M := le_max_left _ _
  have hmax_ge_one : max M 1 ≥ 1 := le_max_right _ _
  nlinarith

theorem why_7_6_3 {n: ℕ → ℕ} (hn: StrictMono n) (j:ℕ) : n j ≥ j := by
  induction' j with k ih
  · exact Nat.zero_le _
  · have hk : n k ≥ k := ih
    have hstep : n (k+1) > n k := hn (by omega)
    omega

/-- Lemma 9.6.3 -/
theorem BddOn.of_continuous_on_compact {a b:ℝ} (_h:a < b) {f:ℝ → ℝ} (hf: ContinuousOn f (.Icc a b) ) :
  BddOn f (.Icc a b) := by
  -- This proof is written to follow the structure of the original text.
  by_contra! hunbound; simp at hunbound
  set x := fun (n:ℕ) ↦ (hunbound n).choose
  have hx (n:ℕ) : a ≤ x n ∧ x n ≤ b ∧ n < |f (x n)| := by
    obtain ⟨⟨h1, h2⟩, h3⟩ := (hunbound n).choose_spec; exact ⟨h1, h2, h3⟩
  set X := Set.Icc a b
  observe hXclosed : IsClosed X
  observe hXbounded : Bornology.IsBounded X
  have haX (n:ℕ): x n ∈ X := by simp [X]; specialize hx n; grind
  have ⟨ n, hn, ⟨ L, hLX, hconv ⟩ ⟩ := ((Heine_Borel X).mp ⟨ hXclosed, hXbounded ⟩) x haX
  have why (j:ℕ) : n j ≥ j := why_7_6_3 hn j
  replace hf := hf.continuousWithinAt hLX
  rw [ContinuousWithinAt.iff] at hf
  replace hf := hf.comp (fun j ↦ haX (n j)) hconv
  apply Metric.isBounded_range_of_tendsto at hf
  rw [isBounded_def] at hf; choose M hpos hM using hf
  choose j hj using exists_nat_gt M
  replace hx := (hx (n j)).2.2
  replace hM : f (x (n j)) ∈ Set.Icc (-M) M := by grind
  simp [←abs_le] at hM
  have : n j ≥ (j:ℝ) := by simp [why j]
  linarith

/- Definition 9.6.5.  Use the Mathlib `IsMaxOn` type. -/
#check isMaxOn_iff
#check isMinOn_iff

/-- Remark 9.6.6 -/
theorem BddAboveOn.isMaxOn {f:ℝ → ℝ} {X:Set ℝ} {x₀:ℝ} (h: IsMaxOn f X x₀): BddAboveOn f X := by
  use f x₀
  intro x hx
  exact h hx

theorem BddBelowOn.isMinOn {f:ℝ → ℝ} {X:Set ℝ} {x₀:ℝ} (h: IsMinOn f X x₀): BddBelowOn f X := by
  use -f x₀
  intro x hx
  have hx' := h hx
  calc
    -(-f x₀) = f x₀ := by ring
    _ ≤ f x := hx'

/-- Proposition 9.6.7 (Maximum principle) -/
theorem IsMaxOn.of_continuous_on_compact {a b:ℝ} (h:a < b) {f:ℝ → ℝ} (hf: ContinuousOn f (.Icc a b)) :
  ∃ xmax ∈ Set.Icc a b, IsMaxOn f (.Icc a b) xmax := by
  -- This proof is written to follow the structure of the original text.
  choose M hM using BddOn.of_continuous_on_compact h hf
  set E := f '' (.Icc a b)
  have hE : E ⊆ .Icc (-M) M := by rintro _ ⟨ x, hx, rfl ⟩; simp [hM x hx, ←abs_le]
  have hnon : E ≠ ∅ := by simp [E]; contrapose! h; grind [Set.Icc_eq_empty_iff]
  set m := sSup E
  have claim1 {y:ℝ} (hy: y ∈ E) : y ≤ m := le_csSup (BddAbove.mono hE bddAbove_Icc) hy
  suffices h : ∃ xmax, xmax ∈ Set.Icc a b ∧ f xmax = m
  · rcases h with ⟨xmax, hxmax, hfxmax⟩
    refine ⟨xmax, hxmax, ?_⟩
    rw [isMaxOn_iff]
    intro y hy
    have hy' : f y ∈ f '' (.Icc a b) := Set.mem_image_of_mem f hy
    have hle : f y ≤ m := claim1 hy'
    rw [hfxmax]
    exact hle
  have claim2 (n:ℕ) : ∃ x ∈ Set.Icc a b, m - 1/(n+1:ℝ) < f x := by
    have : 1/(n+1:ℝ) > 0 := by positivity
    replace : m - 1/(n+1:ℝ) < sSup E := by linarith
    rw [←Set.nonempty_iff_ne_empty] at hnon
    apply exists_lt_of_lt_csSup hnon at this
    grind
  set x : ℕ → ℝ := fun n ↦ (claim2 n).choose
  have hx (n:ℕ) : x n ∈ Set.Icc a b := (claim2 n).choose_spec.1
  have hfx (n:ℕ) : m - 1/(n+1:ℝ) < f (x n) := (claim2 n).choose_spec.2
  observe hclosed : IsClosed (.Icc a b)
  observe hbounded : Bornology.IsBounded (.Icc a b)
  have ⟨ n, hn, ⟨ xmax, hmax, hconv⟩ ⟩ := (Heine_Borel (.Icc a b)).mp ⟨hclosed, hbounded⟩ x hx
  use xmax, hmax
  have hn_lower (j:ℕ) : n j ≥ j := why_7_6_3 hn j
  have hconv' : Filter.atTop.Tendsto (fun j ↦ f (x (n j))) (nhds (f xmax)) :=
    hconv.comp_of_continuous (hf.continuousWithinAt hmax) (fun j ↦ hx (n j))
  have hlower (j:ℕ) : m - 1/(j+1:ℝ) < f (x (n j)) := by
    apply lt_of_le_of_lt _ (hfx (n j)); gcongr; grind
  have hupper (j:ℕ) : f (x (n j)) ≤ m := by apply claim1; simp [Set.mem_image, E]; use x (n j), hx (n j)
  have hconvm : Filter.atTop.Tendsto (fun j ↦ f (x (n j))) (nhds m) := by
    apply Filter.Tendsto.squeeze (g := fun j ↦ m - 1/(j+1:ℝ)) (h := fun _ ↦ m) (f := fun j ↦ f (x (n j)))
    . convert tendsto_one_div_add_atTop_nhds_zero_nat.const_sub m (c:=0); simp
    . exact tendsto_const_nhds
    . intro _; grind
    exact hupper
  exact tendsto_nhds_unique hconv' hconvm






theorem IsMinOn.of_continuous_on_compact {a b:ℝ} (h:a < b) {f:ℝ → ℝ} (hf: ContinuousOn f (.Icc a b)) :
  ∃ xmin ∈ Set.Icc a b, IsMinOn f (.Icc a b) xmin := by
  have h_neg : ContinuousOn (-f) (.Icc a b) := hf.neg
  rcases IsMaxOn.of_continuous_on_compact h h_neg with ⟨xmin, hxmin, h_max⟩
  refine ⟨xmin, hxmin, ?_⟩
  intro y hy
  have h := h_max hy
  have h' : f xmin ≤ f y := by
    have : -(f y) ≤ -(f xmin) := h
    linarith
  exact h'

example : IsMaxOn (fun (x : ℝ) ↦ x^2) (.Icc (-2 : ℝ) 2) 2 := by
  rw [isMaxOn_iff]
  intro x hx; rcases hx with ⟨hx1, hx2⟩
  have : x^2 ≤ 2^2 := by nlinarith
  simpa

example : IsMaxOn (fun (x : ℝ) ↦ x^2) (.Icc (-2 : ℝ) 2) (-2) := by
  rw [isMaxOn_iff]
  intro x hx; rcases hx with ⟨hx1, hx2⟩
  have : x^2 ≤ (-2)^2 := by nlinarith
  simpa

theorem sSup.of_isMaxOn {f:ℝ → ℝ} {X:Set ℝ} {x₀:ℝ} (hx₀: x₀ ∈ X) (h: IsMaxOn f X x₀) :
  sSup (f '' X) = f x₀ := by
  apply IsGreatest.csSup_eq
  simp [IsGreatest, mem_upperBounds]
  refine ⟨ ⟨x₀, hx₀, rfl ⟩, h ⟩

theorem sInf.of_isMinOn {f:ℝ → ℝ} {X:Set ℝ} {x₀:ℝ} (hx₀: x₀ ∈ X) (h: IsMinOn f X x₀) :
  sInf (f '' X) = f x₀ := by
  apply IsLeast.csInf_eq
  simp [IsLeast, mem_lowerBounds]
  refine ⟨ ⟨x₀, hx₀, rfl ⟩, h ⟩

theorem sSup.of_continuous_on_compact {a b:ℝ} (h:a < b) (f:ℝ → ℝ) (hf: ContinuousOn f (.Icc a b)) : ∃ xmax ∈ Set.Icc a b, sSup (f '' .Icc a b) = f xmax := by
  choose x hx h' using IsMaxOn.of_continuous_on_compact h hf
  grind [sSup.of_isMaxOn]

theorem sInf.of_continuous_on_compact {a b:ℝ} (h:a < b) (f:ℝ → ℝ) (hf: ContinuousOn f (.Icc a b)) : ∃ xmin ∈ Set.Icc a b, sInf (f '' .Icc a b) = f xmin := by
  choose x hx h' using IsMinOn.of_continuous_on_compact h hf
  grind [sInf.of_isMinOn]

/-- Exercise 9.6.1 a) -/
example : ∃ f: ℝ → ℝ, ContinuousOn f (.Ioo 1 2) ∧ BddOn f (.Ioo 1 2) ∧
  ∃ x₀ ∈ Set.Ioo 1 2, IsMinOn f (.Ioo 1 2) x₀ ∧
  ¬ ∃ x₀ ∈ Set.Ioo 1 2, IsMaxOn f (.Ioo 1 2) x₀
  := by
  let f : ℝ → ℝ := λ x ↦ (x - 1.5)^2
  have hcont : ContinuousOn f (.Ioo 1 2) :=
    (by continuity : Continuous f).continuousOn
  have hbdd : BddOn f (.Ioo 1 2) := by
    refine ⟨0.25, λ x hx ↦ ?_⟩
    have hx1 : (1 : ℝ) < x := hx.1
    have hx2 : x < 2 := hx.2
    rw [abs_of_nonneg (pow_two_nonneg _)]
    have h_sq : (x - 1.5)^2 - 0.25 = (x - 1)*(x - 2) := by ring
    have h_nonpos : (x - 1)*(x - 2) ≤ 0 := by
      have h1 : x - 1 ≥ 0 := by linarith
      have h2 : x - 2 ≤ 0 := by linarith
      nlinarith
    rw [← sub_nonpos, h_sq]
    exact h_nonpos
  have hmin : ∃ x₀ ∈ Set.Ioo 1 2, IsMinOn f (.Ioo 1 2) x₀ := by
    have hx0_mem : (1.5 : ℝ) ∈ Set.Ioo (1 : ℝ) 2 := by
      constructor <;> norm_num
    refine ⟨1.5, hx0_mem, λ y hy ↦ ?_⟩
    have h_f15 : f (1.5 : ℝ) = 0 := by
      dsimp [f]; norm_num
    rw [h_f15]
    exact pow_two_nonneg (y - 1.5)
  have hno_max : ¬ ∃ x₀ ∈ Set.Ioo 1 2, IsMaxOn f (.Ioo 1 2) x₀ := by
    intro h
    rcases h with ⟨x₀, hx₀, h_max⟩
    have hx1 : (1 : ℝ) < x₀ := hx₀.1
    have hx2 : x₀ < 2 := hx₀.2
    by_cases hx0_le : x₀ ≤ 1.5
    · let y := (1 + x₀) / 2
      have h2 : (2 : ℝ) ≠ 0 := by norm_num
      have hy_mem : y ∈ Set.Ioo (1 : ℝ) 2 := by
        dsimp [y]
        constructor
        · field_simp [h2]; nlinarith
        · field_simp [h2]; nlinarith
      have h_lt : (y - 1.5)^2 > (x₀ - 1.5)^2 := by
        dsimp [y]
        field_simp [h2]
        nlinarith
      have h_contra := h_max hy_mem
      exact (not_lt_of_ge h_contra) h_lt
    · let y := (x₀ + 2) / 2
      have h2 : (2 : ℝ) ≠ 0 := by norm_num
      have hy_mem : y ∈ Set.Ioo (1 : ℝ) 2 := by
        dsimp [y]
        constructor
        · field_simp [h2]; nlinarith
        · field_simp [h2]; nlinarith
      have h_lt : (y - 1.5)^2 > (x₀ - 1.5)^2 := by
        dsimp [y]
        field_simp [h2]
        nlinarith
      have h_contra := h_max hy_mem
      exact (not_lt_of_ge h_contra) h_lt
  rcases hmin with ⟨x₀, hx₀, hmin_val⟩
  have hC : ∃ x₀ ∈ Set.Ioo 1 2, (IsMinOn f (.Ioo 1 2) x₀ ∧ ¬ ∃ x₀ ∈ Set.Ioo 1 2, IsMaxOn f (.Ioo 1 2) x₀) :=
    ⟨x₀, hx₀, hmin_val, hno_max⟩
  exact ⟨f, hcont, hbdd, hC⟩

/-- Exercise 9.6.1 b) -/
example : ∃ f: ℝ → ℝ, ContinuousOn f (.Ici 0) ∧ BddOn f (.Ici 0) ∧
  ∃ x₀ ∈ Set.Ici 0, IsMaxOn f (.Ici 0) x₀ ∧
  ¬ ∃ x₀ ∈ Set.Ici 0, IsMinOn f (.Ici 0) x₀
  := by
  let f : ℝ → ℝ := λ x ↦ 1/(x+1)
  have hcont : ContinuousOn f (.Ici 0) := by
    refine (continuousOn_const.div (continuousOn_id.add continuousOn_const) ?_)
    intro x hx
    have hx_nonneg : x ≥ 0 := hx
    linarith
  have hbdd : BddOn f (.Ici 0) := by
    refine ⟨1, λ x hx ↦ ?_⟩
    have hx_nonneg : x ≥ 0 := hx
    have h_nonneg_f : 0 ≤ f x := by
      dsimp [f]; positivity
    have h_bound : f x ≤ 1 := by
      dsimp [f]
      have h_denom : x + 1 ≥ 1 := by linarith
      have hx_pos : 0 < x + 1 := by linarith
      simpa using (one_div_le_one_div hx_pos (by norm_num : (0 : ℝ) < 1)).mpr h_denom
    rw [abs_of_nonneg h_nonneg_f]
    exact h_bound
  have hmax : ∃ x₀ ∈ Set.Ici 0, IsMaxOn f (.Ici 0) x₀ := by
    have h0_mem : (0 : ℝ) ∈ Set.Ici (0 : ℝ) := by norm_num
    refine ⟨0, h0_mem, λ y hy ↦ ?_⟩
    have hy_nonneg : y ≥ 0 := hy
    dsimp [f]
    have hy_denom : y + 1 ≥ 1 := by linarith
    have hy_pos : 0 < y + 1 := by linarith
    simpa using (one_div_le_one_div hy_pos (by norm_num : (0 : ℝ) < 1)).mpr hy_denom
  have hno_min : ¬ ∃ x₀ ∈ Set.Ici 0, IsMinOn f (.Ici 0) x₀ := by
    intro h
    rcases h with ⟨x₀, hx₀, h_min⟩
    have hx₀_nonneg : x₀ ≥ 0 := hx₀
    set y := x₀ + 1 with hy
    have hy_mem : y ∈ Set.Ici (0 : ℝ) := by
      dsimp [y]; exact Set.mem_Ici.mpr (by linarith)
    have h_lt : f y < f x₀ := by
      dsimp [f, y]
      have hx0_pos : 0 < x₀ + 1 := by linarith
      have hy_pos : 0 < (x₀ + 1) + 1 := by linarith
      refine (one_div_lt_one_div hy_pos hx0_pos).mpr ?_
      linarith
    have h_contra := h_min hy_mem
    exact (not_lt_of_ge h_contra) h_lt
  rcases hmax with ⟨x₀, hx₀, hmax_val⟩
  have hC : ∃ x₀ ∈ Set.Ici 0, (IsMaxOn f (.Ici 0) x₀ ∧ ¬ ∃ x₀ ∈ Set.Ici 0, IsMinOn f (.Ici 0) x₀) :=
    ⟨x₀, hx₀, hmax_val, hno_min⟩
  exact ⟨f, hcont, hbdd, hC⟩

/-- Exercise 9.6.1 c) -/
example : ∃ f: ℝ → ℝ, BddOn f (.Icc (-1) 1) ∧
  (¬ ∃ x₀ ∈ Set.Icc (-1) 1, IsMinOn f (.Icc (-1) 1) x₀) ∧
  (¬ ∃ x₀ ∈ Set.Icc (-1) 1, IsMaxOn f (.Icc (-1) 1) x₀)
  := by
  let f : ℝ → ℝ := λ x => if -1 < x ∧ x < 1 then x else 0
  have hbdd : BddOn f (.Icc (-1 : ℝ) (1 : ℝ)) := by
    refine ⟨1, λ x hx ↦ ?_⟩
    have hx1 : -1 ≤ x := hx.1; have hx2 : x ≤ 1 := hx.2
    by_cases h_int : -1 < x ∧ x < 1
    · simp [f, h_int]
      rw [abs_le]; constructor <;> linarith
    · simp [f, h_int]
  have hno_min : ¬ ∃ x₀ ∈ Set.Icc (-1 : ℝ) (1 : ℝ), IsMinOn f (Set.Icc (-1 : ℝ) (1 : ℝ)) x₀ := by
    intro h; rcases h with ⟨x₀, hx₀, h_min⟩
    have hx0_l : -1 ≤ x₀ := hx₀.1; have hx0_r : x₀ ≤ 1 := hx₀.2
    by_cases hx0_int : -1 < x₀ ∧ x₀ < 1
    · rcases hx0_int with ⟨hx0_gt, hx0_lt⟩
      let y := (x₀ + (-1)) / 2
      have h2 : (2 : ℝ) ≠ 0 := by norm_num
      have hy_mem : y ∈ Set.Icc (-1 : ℝ) (1 : ℝ) := by
        dsimp [y]
        constructor
        · field_simp [h2]; nlinarith
        · field_simp [h2]; nlinarith
      have h_fx0 : f x₀ = x₀ := by simp [f, hx0_gt, hx0_lt]
      have h_fy : f y = y := by
        have hy_gt : -1 < y := by
          dsimp [y]; field_simp [h2]; nlinarith
        have hy_lt : y < 1 := by
          dsimp [y]; field_simp [h2]; nlinarith
        simp [f, hy_gt, hy_lt]
      have h_min_val : x₀ ≤ y := by
        simpa [h_fx0, h_fy] using h_min hy_mem
      dsimp [y] at h_min_val
      field_simp [h2] at h_min_val
      nlinarith
    · have hx0_end : x₀ = -1 ∨ x₀ = 1 := by
        by_cases hx0_lt1 : x₀ < 1
        · left
          by_contra! hx0_not_eq
          have hx0_gt_neg1 : -1 < x₀ := by
            by_contra! hx0_not_gt
            have hx0_le_neg1 : x₀ ≤ -1 := hx0_not_gt
            have : x₀ = -1 := by linarith
            exact hx0_not_eq this
          exact hx0_int ⟨hx0_gt_neg1, hx0_lt1⟩
        · right; linarith
      rcases hx0_end with (hx0_end | hx0_end)
      · subst hx0_end
        have h_point_mem : (-0.5 : ℝ) ∈ Set.Icc (-1 : ℝ) (1 : ℝ) := by
          constructor <;> norm_num
        have h_min_val : f (-1 : ℝ) ≤ f (-0.5 : ℝ) := h_min h_point_mem
        simp [f] at h_min_val; norm_num at h_min_val
      · subst hx0_end
        have h_point_mem : (-0.5 : ℝ) ∈ Set.Icc (-1 : ℝ) (1 : ℝ) := by
          constructor <;> norm_num
        have h_min_val : f (1 : ℝ) ≤ f (-0.5 : ℝ) := h_min h_point_mem
        simp [f] at h_min_val; norm_num at h_min_val
  have hno_max : ¬ ∃ x₀ ∈ Set.Icc (-1 : ℝ) (1 : ℝ), IsMaxOn f (Set.Icc (-1 : ℝ) (1 : ℝ)) x₀ := by
    intro h; rcases h with ⟨x₀, hx₀, h_max⟩
    have hx0_l : -1 ≤ x₀ := hx₀.1; have hx0_r : x₀ ≤ 1 := hx₀.2
    by_cases hx0_int : -1 < x₀ ∧ x₀ < 1
    · rcases hx0_int with ⟨hx0_gt, hx0_lt⟩
      let y := (x₀ + 1) / 2
      have h2 : (2 : ℝ) ≠ 0 := by norm_num
      have hy_mem : y ∈ Set.Icc (-1 : ℝ) (1 : ℝ) := by
        dsimp [y]
        constructor
        · field_simp [h2]; nlinarith
        · field_simp [h2]; nlinarith
      have h_fx0 : f x₀ = x₀ := by simp [f, hx0_gt, hx0_lt]
      have h_fy : f y = y := by
        have hy_gt : -1 < y := by
          dsimp [y]; field_simp [h2]; nlinarith
        have hy_lt : y < 1 := by
          dsimp [y]; field_simp [h2]; nlinarith
        simp [f, hy_gt, hy_lt]
      have h_max_val : y ≤ x₀ := by
        simpa [h_fx0, h_fy] using h_max hy_mem
      dsimp [y] at h_max_val
      field_simp [h2] at h_max_val
      nlinarith
    · have hx0_end : x₀ = -1 ∨ x₀ = 1 := by
        by_cases hx0_lt1 : x₀ < 1
        · left
          by_contra! hx0_not_eq
          have hx0_gt_neg1 : -1 < x₀ := by
            by_contra! hx0_not_gt
            have hx0_le_neg1 : x₀ ≤ -1 := hx0_not_gt
            have : x₀ = -1 := by linarith
            exact hx0_not_eq this
          exact hx0_int ⟨hx0_gt_neg1, hx0_lt1⟩
        · right; linarith
      rcases hx0_end with (hx0_end | hx0_end)
      · subst hx0_end
        have h_point_mem : (0.5 : ℝ) ∈ Set.Icc (-1 : ℝ) (1 : ℝ) := by
          constructor <;> norm_num
        have h_max_val : f (0.5 : ℝ) ≤ f (-1 : ℝ) := h_max h_point_mem
        simp [f] at h_max_val; norm_num at h_max_val
      · subst hx0_end
        have h_point_mem : (0.5 : ℝ) ∈ Set.Icc (-1 : ℝ) (1 : ℝ) := by
          constructor <;> norm_num
        have h_max_val : f (0.5 : ℝ) ≤ f (1 : ℝ) := h_max h_point_mem
        simp [f] at h_max_val; norm_num at h_max_val
  refine ⟨f, ?_⟩
  refine ⟨hbdd, ?_⟩
  exact ⟨hno_min, hno_max⟩

/-- Exercise 9.6.1 d) -/
example : ∃ f: ℝ → ℝ, ¬ BddAboveOn f (.Icc (-1) 1) ∧ ¬ BddBelowOn f (.Icc (-1) 1) := by
  let f : ℝ → ℝ := λ x => if x < 0 then 1/(x+1) else 1/(x-1)
  have h_not_bdd_above : ¬ BddAboveOn f (.Icc (-1 : ℝ) (1 : ℝ)) := by
    intro h; rcases h with ⟨M, hM⟩
    have h_abs_nonneg : |M| ≥ 0 := abs_nonneg _
    have h_den_pos : |M|+2 > 0 := by linarith
    have hk : |M|+2 ≠ 0 := by linarith
    set x := -1 + 1/(|M|+2) with hx
    have hx_neg : x < 0 := by
      dsimp [x]
      have h_inv_lt_one : 1/(|M|+2) < 1 := by
        have := (one_div_lt_one_div h_den_pos (by norm_num : (0 : ℝ) < 1)).mpr (by linarith)
        simpa using this
      nlinarith
    have hx_mem : x ∈ Set.Icc (-1 : ℝ) (1 : ℝ) := by
      dsimp [x]
      have h_inv_pos : 1/(|M|+2) > 0 := div_pos (by norm_num) h_den_pos
      have h_inv_lt_one : 1/(|M|+2) < 1 := by
        have := (one_div_lt_one_div h_den_pos (by norm_num : (0 : ℝ) < 1)).mpr (by linarith)
        simpa using this
      constructor <;> nlinarith
    have h_val : f x = |M|+2 := by
      dsimp [f, x]
      have hx_neg_val : (-1 + 1/(|M|+2)) < 0 := by
        dsimp [x] at hx_neg; exact hx_neg
      rw [if_pos hx_neg_val]
      field_simp [hk]; ring
    have hfx_gt_M : f x > M := by
      rw [h_val]; have hM_le_abs : M ≤ |M| := le_abs_self M; linarith
    have h_contra := hM x hx_mem; linarith
  have h_not_bdd_below : ¬ BddBelowOn f (.Icc (-1 : ℝ) (1 : ℝ)) := by
    intro h; rcases h with ⟨M, hM⟩
    have h_abs_nonneg : |M| ≥ 0 := abs_nonneg _
    have h_den_pos : |M|+2 > 0 := by linarith
    have hk : |M|+2 ≠ 0 := by linarith
    set x := 1 - 1/(|M|+2) with hx
    have hx_nonneg : x ≥ 0 := by
      dsimp [x]
      have h_inv_le_one : 1/(|M|+2) ≤ 1 := by
        have := (one_div_le_one_div h_den_pos (by norm_num : (0 : ℝ) < 1)).mpr (by linarith)
        simpa using this
      nlinarith
    have hx_mem : x ∈ Set.Icc (-1 : ℝ) (1 : ℝ) := by
      dsimp [x]
      have h_inv_pos : 1/(|M|+2) > 0 := div_pos (by norm_num) h_den_pos
      have h_inv_le_one : 1/(|M|+2) ≤ 1 := by
        have := (one_div_le_one_div h_den_pos (by norm_num : (0 : ℝ) < 1)).mpr (by linarith)
        simpa using this
      constructor <;> nlinarith
    have h_val : f x = -((|M|+2 : ℝ)) := by
      dsimp [f, x]
      have hx_nonneg_val : ¬ (1 - 1/(|M|+2)) < 0 := by
        have : x ≥ 0 := hx_nonneg
        dsimp [x] at this; exact not_lt.mpr this
      rw [if_neg hx_nonneg_val]
      field_simp [hk]; ring
    have hfx_lt_negM : f x < -M := by
      rw [h_val]; have hM_le_abs : M ≤ |M| := le_abs_self M; linarith
    have h_contra := hM x hx_mem; linarith
  exact ⟨f, ⟨h_not_bdd_above, h_not_bdd_below⟩⟩

/-- Exercise 9.6.2 -/
theorem BddOn.add (f g : ℝ → ℝ) (X : Set ℝ) (hf : BddOn f X) (hg : BddOn g X) :
    BddOn (f + g) X := by
  rcases hf with ⟨Mf, hMf⟩
  rcases hg with ⟨Mg, hMg⟩
  use Mf + Mg
  intro x hx
  have hfx := hMf x hx
  have hgx := hMg x hx
  calc
    |(f + g) x| = |f x + g x| := rfl
    _ ≤ |f x| + |g x| := abs_add_le _ _
    _ ≤ Mf + Mg := by nlinarith

theorem BddOn.sub (f g : ℝ → ℝ) (X : Set ℝ) (hf : BddOn f X) (hg : BddOn g X) :
    BddOn (f - g) X := by
  rcases hf with ⟨Mf, hMf⟩
  rcases hg with ⟨Mg, hMg⟩
  use Mf + Mg
  intro x hx
  have hfx := hMf x hx
  have hgx := hMg x hx
  calc
    |(f - g) x| = |f x - g x| := rfl
    _ ≤ |f x| + |g x| := by
      simpa [sub_eq_add_neg, abs_neg] using abs_add_le (f x) (-g x)
    _ ≤ Mf + Mg := by nlinarith

theorem BddOn.mul (f g : ℝ → ℝ) (X : Set ℝ) (hf : BddOn f X) (hg : BddOn g X) :
    BddOn (f * g) X := by
  rcases hf with ⟨Mf, hMf⟩
  rcases hg with ⟨Mg, hMg⟩
  by_cases hX : X.Nonempty
  · rcases hX with ⟨x₀, hx₀⟩
    have hMf_nonneg : 0 ≤ Mf := by
      have h := hMf x₀ hx₀
      have h_nonneg : 0 ≤ |f x₀| := abs_nonneg _
      linarith
    have hMg_nonneg : 0 ≤ Mg := by
      have h := hMg x₀ hx₀
      have h_nonneg : 0 ≤ |g x₀| := abs_nonneg _
      linarith
    use Mf * Mg
    intro x hx
    have hfx := hMf x hx
    have hgx := hMg x hx
    calc
      |(f * g) x| = |f x * g x| := rfl
      _ = |f x| * |g x| := abs_mul _ _
      _ ≤ Mf * Mg := mul_le_mul hfx hgx (abs_nonneg _) hMf_nonneg
  · use 0
    intro x hx
    exfalso; exact hX ⟨x, hx⟩

def BddOn.div : Decidable (∀ (f g : ℝ → ℝ) (X : Set ℝ) (_ : ∀ x ∈ X, g x ≠ 0) (_ : BddOn f X)
    (_: BddOn g X), (BddOn (f / g) X)) := by
  apply isFalse
  intro h
  set X := Set.Ioo (0 : ℝ) 1 with hX
  have h_nonzero : ∀ x ∈ X, (fun x : ℝ => x) x ≠ 0 := by
    intro x hx; rcases hx with ⟨hx1, hx2⟩; nlinarith
  have hf_bdd : BddOn (fun _ : ℝ => (1 : ℝ)) X := by
    use 1; intro x hx; simp
  have hg_bdd : BddOn (fun x : ℝ => x) X := by
    use 1; intro x hx; rcases hx with ⟨hx1, hx2⟩
    rw [abs_of_nonneg (by nlinarith)]; nlinarith
  have h_div_bdd : BddOn ((fun _ : ℝ => (1 : ℝ)) / (fun x : ℝ => x)) X :=
    h (fun _ : ℝ => (1 : ℝ)) (fun x : ℝ => x) X h_nonzero hf_bdd hg_bdd
  rcases h_div_bdd with ⟨M, hM⟩
  have hM_ge_two : 2 ≤ M := by
    have hpos : (1/2 : ℝ) ∈ X := by
      dsimp [X]; constructor <;> norm_num
    have h := hM (1/2) hpos
    have h_simp : |((fun _ : ℝ => (1 : ℝ)) / (fun x : ℝ => x)) (1/2)| = 2 := by norm_num
    rw [h_simp] at h
    exact h
  set x := 1/(M+1) with hx_def
  have hx_mem : x ∈ X := by
    dsimp [X, x]
    have hpos : M+1 > 0 := by nlinarith [hM_ge_two]
    have hx_pos : 0 < 1/(M+1) := div_pos (by norm_num) hpos
    have hx_lt_one : 1/(M+1) < 1 := by
      have : 1 < M+1 := by nlinarith
      have h := (one_div_lt_one_div hpos (by norm_num : (0 : ℝ) < 1)).mpr this
      simpa using h
    exact ⟨hx_pos, hx_lt_one⟩
  have h_val : |((fun _ : ℝ => (1 : ℝ)) / (fun x : ℝ => x)) x| = M+1 := by
    dsimp
    have hpos : M+1 > 0 := by nlinarith
    have h_eq : (1 : ℝ) / (1/(M+1)) = M+1 := by
      field_simp [show M+1 ≠ 0 from by nlinarith]
    rw [h_eq, abs_of_pos hpos]
  have h_contra := hM x hx_mem
  rw [h_val] at h_contra
  nlinarith

end Chapter9
