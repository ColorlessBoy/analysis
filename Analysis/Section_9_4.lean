import Mathlib.Tactic
import Mathlib.Data.Real.Sign
import Mathlib.Topology.ContinuousOn
import Analysis.Section_9_3
/-!
# Analysis I, Section 9.4: Continuous functions

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Continuity of functions, using the Mathlib notions

-/

namespace Chapter9

/--
Definition 9.4.1.  Here we use the Mathlib definition of continuity.  The hypothesis {lean}`x₀ ∈ X` is not needed!
-/
theorem ContinuousWithinAt.iff (X:Set ℝ) (f: ℝ → ℝ)  (x₀:ℝ) :
  ContinuousWithinAt f X x₀ ↔ Convergesto X f (f x₀) x₀ := by
  rw [ContinuousWithinAt.eq_1, Convergesto.iff, nhdsWithin.eq_1]

#check ContinuousOn.eq_1
#check continuousOn_univ
#check continuousWithinAt_univ

/-- Example 9.4.2 --/
example (c x₀:ℝ) : ContinuousWithinAt (fun _ ↦ c) .univ x₀ := by
  rw [ContinuousWithinAt.iff]
  exact Convergesto.const .univ x₀ c

example (c x₀:ℝ) : ContinuousAt (fun _ ↦ c) x₀ := by
  rw [← continuousWithinAt_univ]
  rw [ContinuousWithinAt.iff]
  exact Convergesto.const .univ x₀ c

example (c:ℝ) : ContinuousOn (fun _:ℝ ↦ c) .univ := by
  rw [ContinuousOn.eq_1]
  intro x _
  rw [ContinuousWithinAt.iff]
  exact Convergesto.const .univ x c

example (c:ℝ) : Continuous (fun _:ℝ ↦ c) := by
  rw [← continuousOn_univ]
  rw [ContinuousOn.eq_1]
  intro x _
  rw [ContinuousWithinAt.iff]
  exact Convergesto.const .univ x c

/-- Example 9.4.3 --/
example : Continuous (fun x:ℝ ↦ x) := by
  exact continuous_id

/-- Example 9.4.4 --/
example {x₀:ℝ} (h: x₀ ≠ 0) : ContinuousAt Real.sign x₀ := by
  rw [← continuousWithinAt_univ, ContinuousWithinAt.iff, Convergesto.iff_conv]
  intro a ha hconv
  by_cases hx₀_pos : x₀ > 0
  · rw [Real.sign_of_pos hx₀_pos]
    have hpos : ∀ᶠ n in Filter.atTop, a n > 0 :=
      hconv.eventually ((isOpen_Ioi (a := (0 : ℝ))).mem_nhds hx₀_pos)
    have hevent : (fun _ : ℕ => (1 : ℝ)) =ᶠ[Filter.atTop] fun n => Real.sign (a n) :=
      hpos.mono fun n hn => (Real.sign_of_pos hn).symm
    exact (tendsto_const_nhds (x := (1 : ℝ))).congr' hevent
  · have hx₀_neg : x₀ < 0 := by
      by_contra! hx₀_ge
      have : x₀ = 0 := by linarith
      exact h this
    rw [Real.sign_of_neg hx₀_neg]
    have hneg : ∀ᶠ n in Filter.atTop, a n < 0 :=
      hconv.eventually ((isOpen_Iio (a := (0 : ℝ))).mem_nhds hx₀_neg)
    have hevent : (fun _ : ℕ => (-1 : ℝ)) =ᶠ[Filter.atTop] fun n => Real.sign (a n) :=
      hneg.mono fun n hn => (Real.sign_of_neg hn).symm
    exact (tendsto_const_nhds (x := (-1 : ℝ))).congr' hevent

example  :¬ ContinuousAt Real.sign 0 := by
  intro hcont
  have hconv : Convergesto Set.univ Real.sign (Real.sign 0) 0 := by
    rw [← continuousWithinAt_univ, ContinuousWithinAt.iff] at hcont
    exact hcont
  have : Real.sign (0 : ℝ) = 0 := Real.sign_zero
  rw [this] at hconv
  exact Convergesto.sign_all ⟨0, hconv⟩

/-- Example 9.4.5 --/
example (x₀:ℝ) : ¬ ContinuousAt f_9_3_21 x₀ := by
  intro hcont
  have hconv : Convergesto Set.univ f_9_3_21 (f_9_3_21 x₀) x₀ := by
    rw [← continuousWithinAt_univ, ContinuousWithinAt.iff] at hcont; exact hcont
  rw [Convergesto.iff_conv f_9_3_21 (f_9_3_21 x₀)] at hconv

  -- Construct a rational sequence a_n → x₀
  have ha_exists : ∀ n : ℕ, ∃ (q : ℚ), x₀ - (1 : ℝ) / ((n : ℝ) + 1) < (q : ℝ) ∧
    (q : ℝ) < x₀ + (1 : ℝ) / ((n : ℝ) + 1) := by
    intro n
    have h_pos : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by
      refine div_pos (by norm_num) ?_
      have : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      nlinarith
    have h_lt : x₀ - (1 : ℝ) / ((n : ℝ) + 1) < x₀ + (1 : ℝ) / ((n : ℝ) + 1) := by nlinarith
    exact exists_rat_btwn h_lt

  let a : ℕ → ℝ := λ n => ((Classical.choose (α := ℚ) (ha_exists n)) : ℝ)

  have ha_bound : ∀ n : ℕ, |a n - x₀| < 1 / ((n : ℝ) + 1) ∧
    a n ∈ (fun q : ℚ ↦ (q : ℝ)) '' Set.univ := by
    intro n
    have h_spec := Classical.choose_spec (α := ℚ) (ha_exists n)
    rcases h_spec with ⟨h_left, h_right⟩
    have h_val : a n = ((Classical.choose (α := ℚ) (ha_exists n)) : ℝ) := rfl
    refine ⟨by
      dsimp [a]
      rw [abs_lt]
      constructor <;> linarith, ⟨Classical.choose (α := ℚ) (ha_exists n), Set.mem_univ _, h_val⟩⟩

  have ha_bound' : ∀ n : ℕ, |a n - x₀| < 1 / ((n : ℝ) + 1) := fun n => (ha_bound n).1
  have ha_rational : ∀ n, a n ∈ (fun q : ℚ ↦ (q : ℝ)) '' Set.univ := fun n => (ha_bound n).2

  have ha_conv : Filter.atTop.Tendsto a (nhds x₀) := by
    have h_one_div : Filter.atTop.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) (nhds 0) := by
      have h_shift : Filter.atTop.Tendsto (fun n : ℕ => n + 1) Filter.atTop := by
        refine Filter.tendsto_atTop_atTop.mpr fun N => ⟨N, fun n hn => by omega⟩
      have h_temp : Filter.atTop.Tendsto (fun n : ℕ => 1 / (((n : ℕ) + 1 : ℕ) : ℝ)) (nhds 0) :=
        (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp h_shift
      simpa [Nat.cast_add, Nat.cast_one] using h_temp
    have h_f : Filter.atTop.Tendsto (fun (n : ℕ) => x₀ - 1 / ((n : ℝ) + 1)) (nhds x₀) := by
      simpa using (tendsto_const_nhds (x := x₀)).sub h_one_div
    have h_h : Filter.atTop.Tendsto (fun (n : ℕ) => x₀ + 1 / ((n : ℝ) + 1)) (nhds x₀) := by
      simpa using (tendsto_const_nhds (x := x₀)).add h_one_div
    have h_fg : (fun (n : ℕ) => x₀ - 1 / ((n : ℝ) + 1)) ≤ a := by
      intro n
      have h_abs := ha_bound' n
      rcases abs_lt.mp h_abs with ⟨h_neg, h_pos⟩
      linarith
    have h_gh : a ≤ (fun (n : ℕ) => x₀ + 1 / ((n : ℝ) + 1)) := by
      intro n
      have h_abs := ha_bound' n
      rcases abs_lt.mp h_abs with ⟨h_neg, h_pos⟩
      linarith
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le h_f h_h h_fg h_gh

  have ha_univ : ∀ n, a n ∈ Set.univ := λ _ => trivial

  have ha_f_one : ∀ n, f_9_3_21 (a n) = 1 := by
    intro n
    dsimp [f_9_3_21]
    rw [if_pos (ha_rational n)]

  have h_tendsto_one : Filter.atTop.Tendsto (fun n : ℕ => f_9_3_21 (a n)) (nhds 1) := by
    have h_const : (fun n : ℕ => f_9_3_21 (a n)) = fun _ : ℕ => (1 : ℝ) := by
      ext n; exact ha_f_one n
    rw [h_const]
    exact tendsto_const_nhds

  have hfx₀_is_one : f_9_3_21 x₀ = 1 :=
    tendsto_nhds_unique (hconv a ha_univ ha_conv) h_tendsto_one

  -- Construct an irrational sequence b_n → x₀
  let b : ℕ → ℝ := λ n => a n + Real.sqrt 2 / ((n : ℝ) + 1)

  have hb_nonzero : ∀ n : ℕ, (n : ℝ) + 1 ≠ 0 := by
    intro n
    positivity

  have hb_irrational : ∀ n, b n ∉ (fun q : ℚ ↦ (q : ℝ)) '' Set.univ := by
    intro n h
    have h_sqrt_rat : Real.sqrt 2 / ((n : ℝ) + 1) ∈ (fun q : ℚ ↦ (q : ℝ)) '' Set.univ := by
      rcases h with ⟨q, _, hq⟩
      rcases ha_rational n with ⟨q', _, hq'⟩
      have hq_simp : b n = (q : ℝ) := by simpa using hq.symm
      have hq'_simp : a n = (q' : ℝ) := by simpa using hq'.symm
      have h_eq : Real.sqrt 2 / ((n : ℝ) + 1) = (fun q : ℚ ↦ (q : ℝ)) (q - q') := by
        calc
          Real.sqrt 2 / ((n : ℝ) + 1) = (a n + Real.sqrt 2 / ((n : ℝ) + 1)) - a n := by ring
          _ = b n - a n := rfl
          _ = (q : ℝ) - (q' : ℝ) := by rw [hq_simp, hq'_simp]
          _ = ((q - q' : ℚ) : ℝ) := by push_cast; ring
          _ = (fun q : ℚ ↦ (q : ℝ)) (q - q') := rfl
      exact ⟨q - q', Set.mem_univ _, h_eq.symm⟩

    have h_sqrt2_rat : Real.sqrt 2 ∈ (fun q : ℚ ↦ (q : ℝ)) '' Set.univ := by
      rcases h_sqrt_rat with ⟨q'', _, hq''⟩
      have hq''_simp : Real.sqrt 2 / ((n : ℝ) + 1) = (q'' : ℝ) := by simpa using hq''.symm
      have h_mul : Real.sqrt 2 = (Real.sqrt 2 / ((n : ℝ) + 1)) * ((n : ℝ) + 1) := by
        field_simp [hb_nonzero n]
      have h_eq : Real.sqrt 2 = (fun q : ℚ ↦ (q : ℝ)) (q'' * ((n : ℚ) + 1)) := by
        calc
          Real.sqrt 2 = (Real.sqrt 2 / ((n : ℝ) + 1)) * ((n : ℝ) + 1) := h_mul
          _ = (q'' : ℝ) * ((n : ℝ) + 1) := by rw [hq''_simp]
          _ = ((q'' * ((n : ℚ) + 1) : ℚ) : ℝ) := by push_cast; ring
          _ = (fun q : ℚ ↦ (q : ℝ)) (q'' * ((n : ℚ) + 1)) := rfl
      exact ⟨q'' * ((n : ℚ) + 1), Set.mem_univ _, h_eq.symm⟩

    have h_sqrt2_rat' : Real.sqrt 2 ∈ Set.range (Rat.cast : ℚ → ℝ) := by
      simpa [Set.range] using h_sqrt2_rat
    exact irrational_sqrt_two h_sqrt2_rat'

  have hb_conv : Filter.atTop.Tendsto b (nhds x₀) := by
    have h_sqrt_conv : Filter.atTop.Tendsto (fun n : ℕ => Real.sqrt 2 / ((n : ℝ) + 1)) (nhds 0) := by
      have h_shift : Filter.atTop.Tendsto (fun n : ℕ => n + 1) Filter.atTop := by
        refine Filter.tendsto_atTop_atTop.mpr fun N => ⟨N, fun n hn => by omega⟩
      have h_temp : Filter.atTop.Tendsto (fun n : ℕ => Real.sqrt 2 / (((n : ℕ) + 1 : ℕ) : ℝ)) (nhds 0) :=
        (tendsto_const_div_atTop_nhds_zero_nat (Real.sqrt 2)).comp h_shift
      simpa [Nat.cast_add, Nat.cast_one] using h_temp
    simpa [b] using ha_conv.add h_sqrt_conv

  have hb_univ : ∀ n, b n ∈ Set.univ := λ _ => trivial

  have hb_f_zero : ∀ n, f_9_3_21 (b n) = 0 := by
    intro n
    dsimp [f_9_3_21]
    rw [if_neg (hb_irrational n)]

  have h_tendsto_zero : Filter.atTop.Tendsto (fun n : ℕ => f_9_3_21 (b n)) (nhds 0) := by
    have h_const : (fun n : ℕ => f_9_3_21 (b n)) = fun _ : ℕ => (0 : ℝ) := by
      ext n; exact hb_f_zero n
    rw [h_const]
    exact tendsto_const_nhds

  have hfx₀_is_zero : f_9_3_21 x₀ = 0 :=
    tendsto_nhds_unique (hconv b hb_univ hb_conv) h_tendsto_zero

  have : (1 : ℝ) ≠ (0 : ℝ) := by norm_num
  apply this
  calc
    (1 : ℝ) = f_9_3_21 x₀ := hfx₀_is_one.symm
    _ = 0 := hfx₀_is_zero

/-- Example 9.4.6 --/
noncomputable abbrev f_9_4_6 (x:ℝ) : ℝ := if x ≥ 0 then 1 else 0

example {x₀:ℝ} (h: x₀ ≠ 0) : ContinuousAt f_9_4_6 x₀ := by
  rw [← continuousWithinAt_univ, ContinuousWithinAt.iff, Convergesto.iff_conv]
  intro a ha hconv
  by_cases hx₀_pos : x₀ > 0
  · have hpos : ∀ᶠ n in Filter.atTop, a n > 0 :=
      hconv.eventually ((isOpen_Ioi (a := (0 : ℝ))).mem_nhds hx₀_pos)
    have hevent : (fun _ : ℕ => (1 : ℝ)) =ᶠ[Filter.atTop] fun n => f_9_4_6 (a n) :=
      hpos.mono fun n hn => by
        dsimp [f_9_4_6]
        rw [if_pos (show a n ≥ 0 from by linarith)]
    have hfx₀ : f_9_4_6 x₀ = 1 := by
      dsimp [f_9_4_6]
      rw [if_pos (show x₀ ≥ 0 from by linarith)]
    rw [hfx₀]
    exact (tendsto_const_nhds (x := (1 : ℝ))).congr' hevent
  · have hx₀_neg : x₀ < 0 := by
      by_contra! hx₀_ge
      have : x₀ = 0 := by linarith
      exact h this
    have hneg : ∀ᶠ n in Filter.atTop, a n < 0 :=
      hconv.eventually ((isOpen_Iio (a := (0 : ℝ))).mem_nhds hx₀_neg)
    have hevent : (fun _ : ℕ => (0 : ℝ)) =ᶠ[Filter.atTop] fun n => f_9_4_6 (a n) :=
      hneg.mono fun n hn => by
        dsimp [f_9_4_6]
        rw [if_neg (show ¬ a n ≥ 0 from by linarith)]
    have hfx₀ : f_9_4_6 x₀ = 0 := by
      dsimp [f_9_4_6]
      rw [if_neg (show ¬ x₀ ≥ 0 from by linarith)]
    rw [hfx₀]
    exact (tendsto_const_nhds (x := (0 : ℝ))).congr' hevent

example : ¬ ContinuousAt f_9_4_6 0 := by
  intro hcont
  have hconv : Convergesto Set.univ f_9_4_6 (f_9_4_6 0) 0 :=
    (ContinuousWithinAt.iff Set.univ f_9_4_6 0).mp ((continuousWithinAt_univ f_9_4_6 0).mpr hcont)
  have hseq := (Convergesto.iff_conv f_9_4_6 (f_9_4_6 0)).mp hconv
  have hf0 : f_9_4_6 0 = 1 := by
    dsimp [f_9_4_6]
    simp
  let b : ℕ → ℝ := λ n => -1 / ((n : ℝ) + 1)
  have hb_univ : ∀ n, b n ∈ Set.univ := λ _ => trivial
  have hb_conv : Filter.atTop.Tendsto b (nhds (0 : ℝ)) := by
    dsimp [b]
    have h_eq : (fun n : ℕ => -1 / ((n : ℝ) + 1)) = ((fun n : ℕ => -1 / (n : ℝ)) ∘ (fun n : ℕ => n + 1)) := by
      ext n; simp
    rw [h_eq]
    exact ((tendsto_const_div_atTop_nhds_zero_nat (-1 : ℝ)).comp (Filter.tendsto_add_atTop_nat 1))
  have hfb : ∀ n, f_9_4_6 (b n) = 0 := by
    intro n
    dsimp [f_9_4_6, b]
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
      linarith
    have hneg : -1 / ((n : ℝ) + 1) < 0 :=
      div_neg_of_neg_of_pos (by norm_num) hpos
    rw [if_neg (by linarith : ¬ -1 / ((n : ℝ) + 1) ≥ (0 : ℝ))]
  have hfb_tendsto : Filter.atTop.Tendsto (fun n ↦ f_9_4_6 (b n)) (nhds (f_9_4_6 0)) :=
    hseq b hb_univ hb_conv
  have hzero_tendsto_one : Filter.atTop.Tendsto (fun n : ℕ ↦ (0 : ℝ)) (nhds (1 : ℝ)) := by
    convert hfb_tendsto
    · simp [hfb]
    · simp [hf0]
  have hzero_tendsto_zero : Filter.atTop.Tendsto (fun n : ℕ ↦ (0 : ℝ)) (nhds (0 : ℝ)) :=
    tendsto_const_nhds
  have h01 : (1 : ℝ) = (0 : ℝ) :=
    tendsto_nhds_unique (a := 1) (b := 0) hzero_tendsto_one hzero_tendsto_zero
  linarith

example : ContinuousWithinAt f_9_4_6 (.Ici 0) 0 := by
  rw [ContinuousWithinAt.iff]
  have hf0 : f_9_4_6 0 = 1 := by
    dsimp [f_9_4_6]
    simp
  rw [hf0]
  rw [Convergesto.iff_conv]
  intro a ha hconv
  have ha_pos : ∀ n, a n ≥ 0 := ha
  have hfa : ∀ n, f_9_4_6 (a n) = 1 := by
    intro n
    dsimp [f_9_4_6]
    rw [if_pos (ha_pos n)]
  simp [hfa]

/-- Proposition 9.4.7 / Exercise 9.4.1. -/
theorem ContinuousWithinAt.tfae (X:Set ℝ) (f: ℝ → ℝ) (x₀:ℝ) :
  [
    ContinuousWithinAt f X x₀,
    ∀ a:ℕ → ℝ, (∀ n, a n ∈ X) → Filter.atTop.Tendsto a (nhds x₀) → Filter.atTop.Tendsto (fun n ↦ f (a n)) (nhds (f x₀)),
    ∀ ε > 0, ∃ δ > 0, ∀ x ∈ X, |x-x₀| < δ → |f x - f x₀| < ε,
    ∀ ε > 0, ∃ δ > 0, ∀ x ∈ X, |x-x₀| ≤ δ → |f x - f x₀| ≤ ε
  ].TFAE := by
  tfae_have 2 → 1 := by
    intro h
    rw [ContinuousWithinAt.iff, Convergesto.iff_conv f (f x₀)]
    exact h

  tfae_have 1 → 2 := by
    intro h
    have hconv := (ContinuousWithinAt.iff X f x₀).mp h
    exact (Convergesto.iff_conv f (f x₀)).mp hconv

  tfae_have 1 → 3 := by
    intro h
    rcases (ContinuousWithinAt.iff X f x₀).mp h with hconv
    unfold Convergesto at hconv
    intro ε hε
    rcases hconv ε hε with ⟨δ, hδpos, h⟩
    refine ⟨δ, hδpos, ?_⟩
    intro x hx hxlt
    apply h x
    refine ⟨hx, ?_⟩
    rw [Set.mem_Ioo]
    rcases abs_lt.mp hxlt with ⟨hlt1, hlt2⟩
    constructor <;> nlinarith

  tfae_have 3 → 4 := by
    intro h ε hε
    rcases h ε hε with ⟨δ, hδpos, h⟩
    refine ⟨δ/2, by nlinarith, ?_⟩
    intro x hx hxle
    have hxlt : |x - x₀| < δ := by
      nlinarith
    have hlt : |f x - f x₀| < ε := h x hx hxlt
    exact le_of_lt hlt

  tfae_have 4 → 1 := by
    intro h
    rw [ContinuousWithinAt.iff]
    unfold Convergesto
    intro ε hε
    rcases h (ε/2) (by nlinarith) with ⟨δ, hδpos, h⟩
    unfold Real.CloseNear
    refine ⟨δ, hδpos, ?_⟩
    unfold Real.CloseFn
    intro x hx
    rcases hx with ⟨hxX, hxI⟩
    rw [Set.mem_Ioo] at hxI
    rcases hxI with ⟨hxleft, hxright⟩
    have hxlt : |x - x₀| < δ := by
      rw [abs_lt]
      constructor <;> nlinarith
    have hxle : |x - x₀| ≤ δ := le_of_lt hxlt
    have hfx : |f x - f x₀| ≤ ε/2 := h x hxX hxle
    nlinarith

  tfae_finish

/-- Remark 9.4.8 --/
theorem _root_.Filter.Tendsto.comp_of_continuous {X:Set ℝ} {f: ℝ → ℝ} {x₀:ℝ}
  (h_cont: ContinuousWithinAt f X x₀) {a: ℕ → ℝ} (ha: ∀ n, a n ∈ X)
  (hconv: Filter.atTop.Tendsto a (nhds x₀)):
  Filter.atTop.Tendsto (fun n ↦ f (a n)) (nhds (f x₀)) := by
  have := (ContinuousWithinAt.tfae X f x₀).out 0 1
  grind

/- Proposition 9.4.9 -/
theorem ContinuousWithinAt.add {X:Set ℝ} (f g: ℝ → ℝ) {x₀:ℝ}
  (hf: ContinuousWithinAt f X x₀) (hg: ContinuousWithinAt g X x₀) :
  ContinuousWithinAt (f + g) X x₀ := by
  rw [iff] at hf hg ⊢; convert hf.add hg using 1


theorem ContinuousWithinAt.sub {X:Set ℝ} (f g: ℝ → ℝ) {x₀:ℝ}
  (hf: ContinuousWithinAt f X x₀) (hg: ContinuousWithinAt g X x₀) :
  ContinuousWithinAt (f - g) X x₀ := by
  rw [iff] at hf hg ⊢; convert hf.sub hg using 1

theorem ContinuousWithinAt.max {X:Set ℝ} (f g: ℝ → ℝ) {x₀:ℝ}
  (hf: ContinuousWithinAt f X x₀) (hg: ContinuousWithinAt g X x₀) :
  ContinuousWithinAt (max f g) X x₀ := by
  rw [iff] at hf hg ⊢; convert hf.max hg using 1


theorem ContinuousWithinAt.min {X:Set ℝ} (f g: ℝ → ℝ) {x₀:ℝ}
  (hf: ContinuousWithinAt f X x₀) (hg: ContinuousWithinAt g X x₀) :
  ContinuousWithinAt (min f g) X x₀ := by
  rw [iff] at hf hg ⊢; convert hf.min hg using 1


theorem ContinuousWithinAt.mul' {X:Set ℝ} (f g: ℝ → ℝ) {x₀:ℝ}
  (hf: ContinuousWithinAt f X x₀) (hg: ContinuousWithinAt g X x₀) :
  ContinuousWithinAt (f * g) X x₀ := by
  rw [iff] at hf hg ⊢; convert hf.mul hg using 1

theorem ContinuousWithinAt.div' {X:Set ℝ} (f g: ℝ → ℝ) {x₀:ℝ} (hM: g x₀ ≠ 0)
  (hf: ContinuousWithinAt f X x₀) (hg: ContinuousWithinAt g X x₀) :
  ContinuousWithinAt (f / g) X x₀ := by
  rw [iff] at hf hg ⊢; convert hf.div hM hg using 1

/-- Proposition 9.4.10 / Exercise 9.4.3  -/
theorem Continuous.exp {a:ℝ} (ha: a>0) : Continuous (fun x:ℝ ↦ a ^ x) := by
  exact Real.continuous_const_rpow ha.ne'

/-- Proposition 9.4.11 / Exercise 9.4.4 -/
theorem Continuous.exp' (p:ℝ) : ContinuousOn (fun x:ℝ ↦ x ^ p) (.Ioi 0) := by
  intro x hx
  apply (Real.continuousAt_rpow_const x p (Or.inl (ne_of_gt hx))).continuousWithinAt

/-- Proposition 9.4.12 -/
theorem Continuous.abs : Continuous (fun x:ℝ ↦ |x|) := by
  exact continuous_abs

/-- Proposition 9.4.13 / Exercise 9.4.5 -/
theorem ContinuousWithinAt.comp {X Y: Set ℝ} {f g:ℝ → ℝ} (hf: ∀ x ∈ X, f x ∈ Y) (x₀:ℝ)
  (hf_cont: ContinuousWithinAt f X x₀) (hg_cont: ContinuousWithinAt g Y (f x₀)):
  ContinuousWithinAt (g ∘ f) X x₀ :=
    hg_cont.comp hf_cont hf

/-- Example 9.4.14 -/
example : Continuous (fun x:ℝ ↦ 3*x + 1) := by
  continuity

example : Continuous (fun x:ℝ ↦ (5:ℝ)^x) := by
  exact Continuous.exp (by norm_num : (5 : ℝ) > 0)

example : Continuous (fun x:ℝ ↦ (5:ℝ)^(3*x+1)) := by
  have h_exp : Continuous (fun x : ℝ ↦ (5 : ℝ) ^ x) := Continuous.exp (by norm_num : (5 : ℝ) > 0)
  have h_lin : Continuous (fun x : ℝ ↦ 3*x + 1) := by continuity
  exact h_exp.comp h_lin

example : Continuous (fun x:ℝ ↦ |x^2-8*x+8|^(Real.sqrt 2) / (x^2 + 1)) := by
  have h_sqrt2_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have h_pow_cont : Continuous (fun x : ℝ ↦ |x^2 - 8*x + 8| ^ (Real.sqrt 2)) :=
    (Real.continuous_rpow_const h_sqrt2_nonneg).comp
      (continuous_abs.comp (by continuity : Continuous (fun x : ℝ ↦ x^2 - 8*x + 8)))
  have h_denom_cont : Continuous (fun x : ℝ ↦ x^2 + 1) := by continuity
  have h_denom_ne_zero : ∀ x : ℝ, x^2 + 1 ≠ 0 := by
    intro x
    nlinarith [sq_nonneg x]
  exact h_pow_cont.div h_denom_cont h_denom_ne_zero

/-- Exercise 9.4.6 -/
theorem ContinuousOn.restrict {X Y:Set ℝ} {f: ℝ → ℝ} (hY: Y ⊆ X) (hf: ContinuousOn f X) : ContinuousOn f Y := by
  rw [ContinuousOn.eq_1] at hf ⊢
  intro x hx
  exact (hf x (hY hx)).mono hY

/-- Exercise 9.4.7 -/
theorem Continuous.polynomial {n:ℕ} (c: Fin n → ℝ) : Continuous (fun x:ℝ ↦ ∑ i, c i * x ^ (i:ℕ)) := by
  continuity
