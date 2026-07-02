import Mathlib.Tactic
import Mathlib.Data.Real.Sign
import Analysis.Section_9_1

set_option doc.verso.suggestions false

/-!
# Analysis I, Section 9.3: Limiting values of functions

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Limits of continuous functions
- Connection with Mathilb's filter convergence concepts
- Limit laws for functions

Technical point: in the text, the functions `f` studied are defined only on subsets `X` of {lean}`ℝ`, and
left undefined elsewhere.  However, in Lean, this then creates some fiddly conversions when trying
to restrict `f` to various subsets of `X` (which, technically, are not precisely subsets of {lean}`ℝ`,
though they can be coerced to such).  To avoid this issue we will deviate from the text by having
our functions defined on all of {lean}`ℝ` (with the understanding that they are assigned "junk" values
outside of the domain `X` of interest).
-/

/-- Definition 9.3.1
Note the books uses ≤ instead of <, but < matches mathlib's definition of neighborhood.
-/
abbrev Real.CloseFn (ε:ℝ) (X:Set ℝ) (f: ℝ → ℝ) (L:ℝ) : Prop :=
  ∀ x ∈ X, |f x - L| < ε

/-- Definition 9.3.3 -/
abbrev Real.CloseNear (ε:ℝ) (X:Set ℝ) (f: ℝ → ℝ) (L:ℝ) (x₀:ℝ) : Prop :=
  ∃ δ > 0, ε.CloseFn (X ∩ .Ioo (x₀-δ) (x₀+δ)) f L

namespace Chapter9

/-- Example 9.3.2
Slight change from the book to accomodate the change to {lean}`Real.CloseFn`
-/
example : (5.1:ℝ).CloseFn (.Icc 1 3) (fun x ↦ x^2) 4 := by
  intro x hx
  rcases hx with ⟨hx1, hx2⟩
  have hx_sq_bound : x^2 ≤ 9 := by nlinarith
  have hx_sq_lower : 1 ≤ x^2 := by nlinarith
  have : |x^2 - 4| ≤ 5 := by
    rw [abs_le]
    constructor <;> nlinarith
  nlinarith

/-- Example 9.3.2
Slight change from the book to accomodate the change to {lean}`Real.CloseFn`
-/
example : (0.42:ℝ).CloseFn (.Icc 1.9 2.1) (fun x ↦ x^2) 4 := by
  intro x hx; rcases hx with ⟨hx1, hx2⟩
  have hx_sq_lower : 1.9^2 ≤ x^2 := by nlinarith
  have hx_sq_upper : x^2 ≤ 2.1^2 := by nlinarith
  have : |x^2 - 4| ≤ 0.41 := by
    rw [abs_le]; constructor <;> nlinarith
  nlinarith

/-- Example 9.3.4 -/
example: ¬(0.1:ℝ).CloseFn (.Icc 1 3) (fun x ↦ x^2) 4 := by
  intro h
  have h3 := h 3 (by norm_num)
  norm_num at h3

/-- Example 9.3.4 -/
example: (0.1:ℝ).CloseNear (.Icc 1 3) (fun x ↦ x^2) 4 2 := by
  refine ⟨0.01, by norm_num, ?_⟩
  intro x hx; rcases hx with ⟨⟨hx1, hx2⟩, hx3⟩
  rcases hx3 with ⟨hx3l, hx3r⟩
  have hx_sq_lower : x^2 > 3.9601 := by nlinarith
  have hx_sq_upper : x^2 < 4.0401 := by nlinarith
  have : |x^2 - 4| < 0.0401 := by
    rw [abs_lt]; constructor <;> nlinarith
  nlinarith

/-- Example 9.3.5 -/
example: ¬(0.1:ℝ).CloseFn (.Icc 1 3) (fun x ↦ x^2) 9 := by
  intro h
  have h1 := h 1 (by norm_num)
  norm_num at h1

/-- Example 9.3.5 -/
example: (0.1:ℝ).CloseNear (.Icc 1 3) (fun x ↦ x^2) 9 3 := by
  refine ⟨0.01, by norm_num, ?_⟩
  intro x hx; rcases hx with ⟨⟨hx1, hx2⟩, hx3⟩
  rcases hx3 with ⟨hx3l, hx3r⟩
  have hx_sq_lower : x^2 > 8.9401 := by nlinarith
  have hx_sq_upper : x^2 < 9.0601 := by nlinarith
  have : |x^2 - 9| < 0.0601 := by
    rw [abs_lt]; constructor <;> nlinarith
  nlinarith

/-- Definition 9.3.6 (Convergence of functions at a point)-/
abbrev Convergesto (X:Set ℝ) (f: ℝ → ℝ) (L:ℝ) (x₀:ℝ) : Prop := ∀ ε > (0:ℝ), ε.CloseNear X f L x₀

/-- Connection with Mathlib filter convergence concepts -/
theorem Convergesto.iff (X:Set ℝ) (f: ℝ → ℝ) (L:ℝ) (x₀:ℝ) :
  Convergesto X f L x₀ ↔ (nhdsWithin x₀ X).Tendsto f (nhds L) := by
  unfold Convergesto Real.CloseNear Real.CloseFn nhdsWithin
  rw [LinearOrderedAddCommGroup.tendsto_nhds]
  peel with ε hε
  rw [Filter.eventually_inf_principal]
  simp [Filter.Eventually, mem_nhds_iff_exists_Ioo_subset]
  constructor
  . intro ⟨ δ, _, _ ⟩; use x₀-δ, x₀+δ, by grind
    intro _; simp; grind
  intro ⟨ l, u, ⟨ _, _ ⟩, h ⟩
  have h1 : 0 < x₀ - l := by linarith
  have h2 : 0 < u - x₀ := by linarith
  set δ := min (x₀ - l) (u - x₀)
  observe hδ1 : δ ≤ x₀ - l
  observe hδ2 : δ ≤ u - x₀
  use δ, (by positivity); intro x hxX _ _
  specialize h (show x ∈ .Ioo l u by simp; grind)
  simpa [hxX] using h

/-- Example 9.3.8 -/
example: Convergesto (.Icc 1 3) (fun x ↦ x^2) 4 2 := by
  intro ε hε
  have h_eps_pos : 0 < ε / 5 := by nlinarith
  refine ⟨ε/5, h_eps_pos, ?_⟩
  intro x hx
  rcases hx with ⟨⟨hx1, hx2⟩, hx3⟩
  rcases hx3 with ⟨hx3l, hx3r⟩
  have hx_lt_ε5 : |x - 2| < ε/5 := by
    rw [abs_lt]; constructor <;> nlinarith
  have hx_plus_2_nonneg : 0 ≤ x + 2 := by nlinarith
  have hx_plus_2_le_5 : x + 2 ≤ 5 := by nlinarith
  have hx_sq_diff_eq : |x^2 - 4| = |x - 2| * (x + 2) := by
    calc
      |x^2 - 4| = |(x - 2) * (x + 2)| := by ring_nf
      _ = |x - 2| * |x + 2| := abs_mul _ _
      _ = |x - 2| * (x + 2) := by rw [abs_of_nonneg hx_plus_2_nonneg]
  rw [hx_sq_diff_eq]
  calc
    |x - 2| * (x + 2) < (ε/5) * (x + 2) :=
      mul_lt_mul_of_pos_right hx_lt_ε5 (by nlinarith)
    _ ≤ (ε/5) * 5 := mul_le_mul_of_nonneg_left hx_plus_2_le_5 (by nlinarith)
    _ = ε := by ring

/-- Proposition 9.3.9 / Exercise 9.3.1 -/
theorem Convergesto.iff_conv {E:Set ℝ} (f: ℝ → ℝ) (L:ℝ) {x₀:ℝ} :
  Convergesto E f L x₀ ↔ ∀ a:ℕ → ℝ, (∀ n:ℕ, a n ∈ E) →
  Filter.atTop.Tendsto a (nhds x₀) →
  Filter.atTop.Tendsto (fun n ↦ f (a n)) (nhds L) := by
  rw [Convergesto.iff]
  constructor
  · intro h a ha hconv
    have hseq : Filter.atTop.Tendsto a (nhdsWithin x₀ E) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨hconv, ?_⟩
      rw [Filter.eventually_atTop]
      refine ⟨0, λ n hn => ha n⟩
    exact h.comp hseq
  · intro h
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    by_contra! h_not
    have h_choice : ∀ n : ℕ, ∃ x : ℝ, x ∈ E ∧ dist x x₀ < ((1 : ℝ) / (n+1 : ℝ)) ∧ ε ≤ dist (f x) L := by
      intro n
      have hpos : (0 : ℝ) < 1 / (n+1 : ℝ) := by positivity
      exact h_not (1 / (n+1 : ℝ)) hpos
    let a : ℕ → ℝ := λ n => (Classical.choose (h_choice n))
    have ha : ∀ n, a n ∈ E := λ n => (Classical.choose_spec (h_choice n)).1
    have hdist : ∀ n, dist (a n) x₀ < ((1 : ℝ) / (n+1 : ℝ)) := λ n => (Classical.choose_spec (h_choice n)).2.1
    have hf_dist : ∀ n, ε ≤ dist (f (a n)) L := λ n => (Classical.choose_spec (h_choice n)).2.2
    have hconv_a : Filter.atTop.Tendsto a (nhds x₀) := by
      rw [Metric.tendsto_atTop]
      intro δ hδ
      have hN : ∃ N : ℕ, (1 : ℝ) / (N+1 : ℝ) < δ := by
        exact exists_nat_one_div_lt hδ
      rcases hN with ⟨N, hN⟩
      refine ⟨N, λ n hn => ?_⟩
      calc
        dist (a n) x₀ < (1 : ℝ) / (n+1 : ℝ) := hdist n
        _ ≤ (1 : ℝ) / (N+1 : ℝ) := by
          refine (one_div_le_one_div ?_ ?_).mpr ?_
          · positivity
          · positivity
          · have h' : (N : ℕ) + 1 ≤ (n : ℕ) + 1 := Nat.add_le_add_right hn 1
            exact_mod_cast h'
        _ < δ := hN
    have hf_conv : Filter.atTop.Tendsto (fun n ↦ f (a n)) (nhds L) := h a ha hconv_a
    rw [Metric.tendsto_atTop] at hf_conv
    rcases hf_conv ε hε with ⟨N, hN⟩
    have hN' : ε ≤ dist (f (a N)) L := hf_dist N
    have hN'' : dist (f (a N)) L < ε := hN N (le_refl N)
    linarith

theorem Convergesto.comp {E:Set ℝ} {f: ℝ → ℝ} {L:ℝ} {x₀:ℝ} (hf: Convergesto E f L x₀) {a:ℕ → ℝ}
  (ha: ∀ n:ℕ, a n ∈ E) (hconv: Filter.atTop.Tendsto a (nhds x₀)) :
  Filter.atTop.Tendsto (fun n ↦ f (a n)) (nhds L) := by
  rw [iff_conv f L] at hf; solve_by_elim

-- Remark 9.3.11 is not quite true in Lean: the hypothesis `AdherentPt x₀ E` is safely removed
-- from most theorems (with the exception of Convergesto.uniq).

/-- Corollary 9.3.13 -/
theorem Convergesto.uniq {E:Set ℝ} {f: ℝ → ℝ} {L L':ℝ} {x₀:ℝ} (h: AdherentPt x₀ E)
  (hf: Convergesto E f L x₀) (hf': Convergesto E f L' x₀) : L = L' := by
  -- This proof is written to follow the structure of the original text.
  let ⟨ a, ha, hconv ⟩ := (limit_of_AdherentPt _ _).mp h
  exact tendsto_nhds_unique (hf.comp ha hconv) (hf'.comp ha hconv)

/-- Proposition 9.3.14 (Limit laws for functions) -/
theorem Convergesto.add {E:Set ℝ} {f g: ℝ → ℝ} {L M:ℝ} {x₀:ℝ}
  (hf: Convergesto E f L x₀) (hg: Convergesto E g M x₀) :
  Convergesto E (f + g) (L + M) x₀ := by
    -- This proof is written to follow the structure of the original text.
    rw [iff_conv _ _] at hf hg ⊢
    intro a ha hconv; specialize hf a ha hconv; specialize hg a ha hconv
    convert hf.add hg using 1

/-- Proposition 9.3.14 (Limit laws for functions) / Exercise 9.3.2 -/
theorem Convergesto.sub {E:Set ℝ} {f g: ℝ → ℝ} {L M:ℝ} {x₀:ℝ}
  (hf: Convergesto E f L x₀) (hg: Convergesto E g M x₀) :
  Convergesto E (f - g) (L - M) x₀ := by
    rw [iff_conv _ _] at hf hg ⊢
    intro a ha hconv; specialize hf a ha hconv; specialize hg a ha hconv
    convert hf.sub hg using 1

/-- Proposition 9.3.14 (Limit laws for functions) / Exercise 9.3.2 -/
theorem Convergesto.max {E:Set ℝ} {f g: ℝ → ℝ} {L M:ℝ} {x₀:ℝ}
  (hf: Convergesto E f L x₀) (hg: Convergesto E g M x₀) :
  Convergesto E (max f g) (max L M) x₀ := by
    rw [iff_conv _ _] at hf hg ⊢
    intro a ha hconv; specialize hf a ha hconv; specialize hg a ha hconv
    simpa using hf.max hg

/-- Proposition 9.3.14 (Limit laws for functions) / Exercise 9.3.2 -/
theorem Convergesto.min {E:Set ℝ} {f g: ℝ → ℝ} {L M:ℝ} {x₀:ℝ}
  (hf: Convergesto E f L x₀) (hg: Convergesto E g M x₀) :
  Convergesto E (min f g) (min L M) x₀ := by
    rw [iff_conv _ _] at hf hg ⊢
    intro a ha hconv; specialize hf a ha hconv; specialize hg a ha hconv
    simpa using hf.min hg

/-- Proposition 9.3.14 (Limit laws for functions) / Exercise 9.3.2 -/
theorem Convergesto.smul {E:Set ℝ} {f: ℝ → ℝ} {L:ℝ} {x₀:ℝ}
  (hf: Convergesto E f L x₀) (c:ℝ) :
  Convergesto E (c • f) (c * L) x₀ := by
    rw [iff_conv _ _] at hf ⊢
    intro a ha hconv; specialize hf a ha hconv
    simpa [Pi.smul_apply, smul_eq_mul] using hf.const_mul c

/-- Proposition 9.3.14 (Limit laws for functions) / Exercise 9.3.2 -/
theorem Convergesto.mul {E:Set ℝ} {f g: ℝ → ℝ} {L M:ℝ} {x₀:ℝ}
  (hf: Convergesto E f L x₀) (hg: Convergesto E g M x₀) :
  Convergesto E (f * g) (L * M) x₀ := by
    rw [iff_conv _ _] at hf hg ⊢
    intro a ha hconv; specialize hf a ha hconv; specialize hg a ha hconv
    simpa [Pi.mul_apply] using hf.mul hg

/-- Proposition 9.3.14 (Limit laws for functions) / Exercise 9.3.2.  The hypothesis in the book that g is non-vanishing on E can be dropped. -/
theorem Convergesto.div {E:Set ℝ} {f g: ℝ → ℝ} {L M:ℝ} {x₀:ℝ} (hM: M ≠ 0)
  (hf: Convergesto E f L x₀) (hg: Convergesto E g M x₀) :
  Convergesto E (f / g) (L / M) x₀ := by
    rw [iff_conv _ _] at hf hg ⊢
    intro a ha hconv; specialize hf a ha hconv; specialize hg a ha hconv
    simpa [Pi.div_apply] using hf.div hg hM

theorem Convergesto.const (E:Set ℝ) (x₀:ℝ) (c:ℝ)
  : Convergesto E (fun _ ↦ c) c x₀ := by
    rw [iff_conv _ _]
    intro a ha hconv; simp

theorem Convergesto.id (E:Set ℝ) (x₀:ℝ)
  : Convergesto E (fun x ↦ x) x₀ x₀ := by
    rw [iff_conv _ _]
    intro a ha hconv; simpa using hconv

theorem Convergesto.sq (E:Set ℝ) (x₀:ℝ)
  : Convergesto E (fun x ↦ x^2) (x₀^2) x₀ := by
    rw [iff_conv _ _]
    intro a ha hconv
    simpa using hconv.pow 2

theorem Convergesto.linear (E:Set ℝ) (x₀:ℝ) (c:ℝ)
  : Convergesto E (fun x ↦ c * x) (c * x₀) x₀ := by
    simpa using (Convergesto.const E x₀ c).mul (Convergesto.id E x₀)

theorem Convergesto.quadratic (E:Set ℝ) (x₀:ℝ) (c d:ℝ)
  : Convergesto E (fun x ↦ x^2 + c * x + d) (x₀^2 + c * x₀ + d) x₀ := by
    simpa [add_assoc] using
      (Convergesto.sq E x₀).add ((Convergesto.linear E x₀ c).add (Convergesto.const E x₀ d))

theorem Convergesto.restrict {X Y:Set ℝ} {f: ℝ → ℝ} {L:ℝ} {x₀:ℝ} (hf: Convergesto X f L x₀) (hY: Y ⊆ X) : Convergesto Y f L x₀ := by
  rw [iff_conv _ _] at hf ⊢
  intro a ha hconv
  apply hf a (by
    intro n; exact hY (ha n))
  exact hconv

theorem Real.sign_def (x:ℝ) : Real.sign x = if x < 0 then -1 else if x > 0 then 1 else 0 := rfl

/-- Example 9.3.16 -/
theorem Convergesto.sign_right : Convergesto (.Ioi 0) Real.sign 1 0 := by
  rw [iff_conv _ _]
  intro a ha hconv
  have hpos : ∀ n, a n > 0 := ha
  have hsign : ∀ n, Real.sign (a n) = 1 := by
    intro n
    have hpos_n : a n > 0 := hpos n
    have h_not_neg : ¬ a n < 0 := by linarith
    rw [Real.sign_def, if_neg h_not_neg, if_pos hpos_n]
  simp [hsign]

/-- Example 9.3.16 -/
theorem Convergesto.sign_left : Convergesto (.Iio 0) Real.sign (-1) 0 := by
  rw [iff_conv _ _]
  intro a ha hconv
  have hneg : ∀ n, a n < 0 := ha
  have hsign : ∀ n, Real.sign (a n) = -1 := by
    intro n
    rw [Real.sign_def, if_pos (hneg n)]
  simp [hsign]

/-- Example 9.3.16 -/
theorem Convergesto.sign_all : ¬ ∃ L, Convergesto Set.univ Real.sign L 0 := by
  intro h; rcases h with ⟨L, hL⟩
  have h_adv_right : AdherentPt 0 (.Ioi 0) := by
    intro ε hε
    have h_pos : ε/2 > 0 := by nlinarith
    refine ⟨ε/2, h_pos, ?_⟩
    calc
      |0 - (ε/2)| = |ε/2| := by
        have : 0 - (ε/2) = -(ε/2) := by ring
        rw [this, abs_neg]
      _ = ε/2 := abs_of_pos h_pos
      _ ≤ ε := by nlinarith
  have h_adv_left : AdherentPt 0 (.Iio 0) := by
    intro ε hε
    have h_pos : ε/2 > 0 := by nlinarith
    have h_neg : -ε/2 < 0 := by nlinarith
    refine ⟨-ε/2, h_neg, ?_⟩
    calc
      |0 - (-ε/2)| = |ε/2| := by
        have : 0 - (-ε/2) = ε/2 := by ring
        rw [this]
      _ = ε/2 := abs_of_pos h_pos
      _ ≤ ε := by nlinarith
  have hL_right : Convergesto (.Ioi 0) Real.sign L 0 :=
    hL.restrict (Set.subset_univ _)
  have hL_left : Convergesto (.Iio 0) Real.sign L 0 :=
    hL.restrict (Set.subset_univ _)
  have h_eq1 : L = 1 := Convergesto.uniq h_adv_right hL_right Convergesto.sign_right
  have h_eq2 : L = -1 := Convergesto.uniq h_adv_left hL_left Convergesto.sign_left
  linarith

noncomputable abbrev f_9_3_17 : ℝ → ℝ := fun x ↦ if x = 0 then 1 else 0

theorem Convergesto.f_9_3_17_remove : Convergesto (Set.univ \ {0}) f_9_3_17 0 0 := by
  rw [iff_conv _ _]
  intro a ha hconv
  have ha_ne_0 (n : ℕ) : a n ≠ 0 := by
    have : a n ∈ Set.univ \ {0} := ha n
    exact this.2
  have h_f (n : ℕ) : f_9_3_17 (a n) = 0 := by
    simp [f_9_3_17, ha_ne_0 n]
  simp [h_f]

theorem Convergesto.f_9_3_17_all : ¬ ∃ L, Convergesto Set.univ f_9_3_17 L 0 := by
  intro h; rcases h with ⟨L, hL⟩
  have h_remove : Convergesto (Set.univ \ {0}) f_9_3_17 0 0 := Convergesto.f_9_3_17_remove
  have hL_remove : Convergesto (Set.univ \ {0}) f_9_3_17 L 0 :=
    hL.restrict (by simp)
  have h_adv : AdherentPt 0 (Set.univ \ {0}) := by
    intro ε hε
    have h_pos : ε/2 > 0 := by nlinarith
    have h_ne : ε/2 ≠ 0 := by nlinarith
    refine ⟨ε/2, ⟨trivial, h_ne⟩, ?_⟩
    calc
      |0 - (ε/2)| = |ε/2| := by
        have : 0 - (ε/2) = -(ε/2) := by ring
        rw [this, abs_neg]
      _ = ε/2 := abs_of_pos h_pos
      _ ≤ ε := by nlinarith
  have h_eq : L = 0 := Convergesto.uniq h_adv hL_remove h_remove
  rw [h_eq] at hL
  have h_eps : (0 : ℝ) < 1/2 := by norm_num
  rcases hL (1/2) h_eps with ⟨δ, hδ, h⟩
  have h0_mem : (0 : ℝ) ∈ Set.univ ∩ Set.Ioo (0-δ) (0+δ) := by
    refine ⟨trivial, ?_⟩
    constructor <;> nlinarith
  have h_contra : |f_9_3_17 (0 : ℝ) - 0| < 1/2 := h 0 h0_mem
  simp [f_9_3_17] at h_contra
  norm_num at h_contra

/-- Proposition 9.3.18 / Exercise 9.3.3 -/
theorem Convergesto.local {E:Set ℝ} {f: ℝ → ℝ} {L:ℝ} {x₀:ℝ} {δ:ℝ} (hδ: δ > 0) :
  Convergesto E f L x₀ ↔ Convergesto (E ∩ Set.Ioo (x₀-δ) (x₀+δ)) f L x₀ := by
  have hx₀ : x₀ ∈ Set.Ioo (x₀-δ) (x₀+δ) := by
    constructor <;> nlinarith
  have h_open : IsOpen (Set.Ioo (x₀-δ) (x₀+δ)) := isOpen_Ioo
  have h_eq : E ∩ Set.Ioo (x₀-δ) (x₀+δ) = (E ∩ Set.Ioo (x₀-δ) (x₀+δ)) ∩ Set.Ioo (x₀-δ) (x₀+δ) := by
    simp
  rw [Convergesto.iff, Convergesto.iff, nhdsWithin_eq_nhdsWithin hx₀ h_open h_eq]

/-- Example 9.3.19.  The point of this example is somewhat blunted by the ability to remove the hypothesis that {lit}`g` is non-zero from the relevant part of Proposition 9.3.14 -/
example : Convergesto Set.univ (fun x ↦ (x+2)/(x+1)) (4/3:ℝ) 2 := by
  have h_id : Convergesto Set.univ (fun x : ℝ ↦ x) 2 2 := Convergesto.id Set.univ 2
  have h_two : Convergesto Set.univ (fun _ : ℝ ↦ (2 : ℝ)) 2 2 := Convergesto.const Set.univ 2 2
  have h_one : Convergesto Set.univ (fun _ : ℝ ↦ (1 : ℝ)) 1 2 := Convergesto.const Set.univ 2 1
  have h_num_temp := h_id.add h_two
  have h_denom_temp := h_id.add h_one
  have h_num : Convergesto Set.univ (fun x : ℝ ↦ x + 2) (4 : ℝ) 2 := by
    simpa [show (fun x : ℝ ↦ x + 2) = (fun x : ℝ ↦ x) + (fun _ : ℝ ↦ (2 : ℝ)) by ext x; simp,
      show (2 : ℝ) + 2 = (4 : ℝ) by norm_num] using h_num_temp
  have h_denom : Convergesto Set.univ (fun x : ℝ ↦ x + 1) (3 : ℝ) 2 := by
    simpa [show (fun x : ℝ ↦ x + 1) = (fun x : ℝ ↦ x) + (fun _ : ℝ ↦ (1 : ℝ)) by ext x; simp,
      show (2 : ℝ) + 1 = (3 : ℝ) by norm_num] using h_denom_temp
  have h_denom_ne_zero : (3 : ℝ) ≠ 0 := by norm_num
  have h_div := h_num.div h_denom_ne_zero h_denom
  simpa using h_div

/-- Example 9.3.20 -/
example : Convergesto (Set.univ \ {1}) (fun x ↦ (x^2-1)/(x-1)) 2 1 := by
  rw [Convergesto.iff_conv (fun x ↦ (x^2-1)/(x-1)) 2]
  intro a ha hconv
  have ha_ne_one (n : ℕ) : a n ≠ 1 := by
    have : a n ∈ Set.univ \ {1} := ha n
    exact this.2
  have h_simp (n : ℕ) : (a n ^ 2 - 1) / (a n - 1) = a n + 1 := by
    have h_denom_ne_zero : a n - 1 ≠ 0 := sub_ne_zero.mpr (ha_ne_one n)
    field_simp [h_denom_ne_zero]
    ring
  have h_simp_seq : (fun n : ℕ ↦ (a n ^ 2 - 1) / (a n - 1)) = (fun n : ℕ ↦ a n + 1) := by
    ext n; exact h_simp n
  rw [h_simp_seq]
  simpa [show (1 : ℝ) + 1 = (2 : ℝ) by norm_num] using hconv.add (tendsto_const_nhds (x := (1 : ℝ)))

open Classical in
/-- Example 9.3.21 -/
noncomputable abbrev f_9_3_21 : ℝ → ℝ := fun x ↦ if x ∈ (fun q:ℚ ↦ (q:ℝ)) '' .univ then 1 else 0

example : Filter.atTop.Tendsto (fun (n:ℕ) ↦ f_9_3_21 (1/n:ℝ)) (nhds 1) := by
  have h (n : ℕ) : f_9_3_21 (1/((n:ℝ))) = 1 := by
    dsimp [f_9_3_21]
    have h_rational : (1 : ℝ)/((n : ℝ)) ∈ (fun q : ℚ ↦ (q : ℝ)) '' Set.univ := by
      refine ⟨(1 : ℚ)/((n : ℚ)), trivial, ?_⟩
      push_cast; ring
    rw [if_pos h_rational]
  have : (fun (n : ℕ) ↦ f_9_3_21 (1/((n:ℝ)))) = fun _ : ℕ ↦ (1 : ℝ) := by
    ext n; exact h n
  rw [this]; exact tendsto_const_nhds

example : Filter.atTop.Tendsto (fun (n:ℕ) ↦ f_9_3_21 ((Real.sqrt 2)/n:ℝ)) (nhds 0) := by
  have h_eventually : (fun (n : ℕ) ↦ f_9_3_21 ((Real.sqrt 2)/((n:ℝ)))) =ᶠ[Filter.atTop] fun _ : ℕ ↦ (0 : ℝ) := by
    refine Filter.eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
    have hn_nonzero : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn)
    dsimp [f_9_3_21]
    have h_not_rational : (Real.sqrt 2)/((n:ℝ)) ∉ (fun q : ℚ ↦ (q : ℝ)) '' Set.univ := by
      intro h; rcases h with ⟨q, _, hq⟩
      have h_sqrt2_rational : (Real.sqrt 2 : ℝ) ∈ (fun q : ℚ ↦ (q : ℝ)) '' Set.univ := by
        refine ⟨(q : ℚ) * (n : ℚ), trivial, ?_⟩
        push_cast
        field_simp [hn_nonzero] at hq ⊢
        nlinarith
      apply irrational_sqrt_two
      simpa using h_sqrt2_rational
    rw [if_neg h_not_rational]
  have h_symm : (fun _ : ℕ ↦ (0 : ℝ)) =ᶠ[Filter.atTop] (fun (n : ℕ) ↦ f_9_3_21 ((Real.sqrt 2)/((n:ℝ)))) :=
    h_eventually.symm
  exact (tendsto_const_nhds (x := (0 : ℝ))).congr' h_symm

example : ¬ ∃ L, Convergesto Set.univ f_9_3_21 L 0 := by
  rintro ⟨L, hL⟩
  rw [Convergesto.iff_conv f_9_3_21 L] at hL
  have h1 : Filter.atTop.Tendsto (fun (n : ℕ) ↦ f_9_3_21 (1/((n:ℝ)))) (nhds 1) := by
    have h (n : ℕ) : f_9_3_21 (1/((n:ℝ))) = 1 := by
      dsimp [f_9_3_21]
      have h_rational : (1 : ℝ)/((n : ℝ)) ∈ (fun q : ℚ ↦ (q : ℝ)) '' Set.univ := by
        refine ⟨(1 : ℚ)/((n : ℚ)), trivial, ?_⟩
        push_cast; ring
      rw [if_pos h_rational]
    have : (fun (n : ℕ) ↦ f_9_3_21 (1/((n:ℝ)))) = fun _ : ℕ ↦ (1 : ℝ) := by
      ext n; exact h n
    rw [this]; exact tendsto_const_nhds
  have h2 : Filter.atTop.Tendsto (fun (n : ℕ) ↦ f_9_3_21 ((Real.sqrt 2)/((n:ℝ)))) (nhds 0) := by
    have h_eventually : (fun (n : ℕ) ↦ f_9_3_21 ((Real.sqrt 2)/((n:ℝ)))) =ᶠ[Filter.atTop] fun _ : ℕ ↦ (0 : ℝ) := by
      refine Filter.eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
      have hn_nonzero : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn)
      dsimp [f_9_3_21]
      have h_not_rational : (Real.sqrt 2)/((n:ℝ)) ∉ (fun q : ℚ ↦ (q : ℝ)) '' Set.univ := by
        intro h; rcases h with ⟨q, _, hq⟩
        have h_sqrt2_rational : (Real.sqrt 2 : ℝ) ∈ (fun q : ℚ ↦ (q : ℝ)) '' Set.univ := by
          refine ⟨q * (n : ℚ), trivial, ?_⟩
          push_cast
          field_simp [hn_nonzero] at hq ⊢
          nlinarith
        apply irrational_sqrt_two
        simpa using h_sqrt2_rational
      rw [if_neg h_not_rational]
    have h_symm : (fun _ : ℕ ↦ (0 : ℝ)) =ᶠ[Filter.atTop] (fun (n : ℕ) ↦ f_9_3_21 ((Real.sqrt 2)/((n:ℝ)))) :=
      h_eventually.symm
    exact (tendsto_const_nhds (x := (0 : ℝ))).congr' h_symm
  have hL1 : Filter.atTop.Tendsto (fun (n : ℕ) ↦ f_9_3_21 (1/((n:ℝ)))) (nhds L) :=
    hL (fun n : ℕ ↦ 1/((n:ℝ))) (by intro n; trivial) (by
      simpa using tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  have hL2 : Filter.atTop.Tendsto (fun (n : ℕ) ↦ f_9_3_21 ((Real.sqrt 2)/((n:ℝ)))) (nhds L) :=
    hL (fun n : ℕ ↦ (Real.sqrt 2)/((n:ℝ))) (by intro n; trivial) (by
      simpa using tendsto_const_div_atTop_nhds_zero_nat (Real.sqrt 2))
  have LL1 : L = 1 := tendsto_nhds_unique hL1 h1
  have LL0 : L = 0 := tendsto_nhds_unique hL2 h2
  linarith

/- Exercise 9.3.4: State a definition of limit superior and limit inferior for functions, and prove an analogue of Proposition 9.3.9 for those definitions. -/

/-- Exercise 9.3.5 (Continuous version of squeeze test) -/
theorem Convergesto.squeeze {E:Set ℝ} {f g h: ℝ → ℝ} {L:ℝ} {x₀:ℝ}
  (hfg: ∀ x ∈ E, f x ≤ g x) (hgh: ∀ x ∈ E, g x ≤ h x)
  (hf: Convergesto E f L x₀) (hh: Convergesto E h L x₀) :
  Convergesto E g L x₀ := by
  rw [Convergesto.iff_conv g L]
  intro a ha hconv
  have hf_seq : Filter.atTop.Tendsto (f ∘ a) (nhds L) :=
    (Convergesto.iff_conv f L |>.mp hf) a ha hconv
  have hh_seq : Filter.atTop.Tendsto (h ∘ a) (nhds L) :=
    (Convergesto.iff_conv h L |>.mp hh) a ha hconv
  have hfg_seq : ∀ n, f (a n) ≤ g (a n) := by
    intro n; exact hfg (a n) (ha n)
  have hgh_seq : ∀ n, g (a n) ≤ h (a n) := by
    intro n; exact hgh (a n) (ha n)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hf_seq hh_seq hfg_seq hgh_seq


end Chapter9
