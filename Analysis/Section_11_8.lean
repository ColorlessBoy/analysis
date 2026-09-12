import Mathlib.Tactic
import Mathlib.Topology.Instances.Irrational
import Analysis.Section_11_6

set_option doc.verso.suggestions false

/-!
# Analysis I, Section 11.8: The Riemann-Stieltjes integral

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Definition of `α_length`.
- The piecewise constant Riemann-Stieltjes integral.
- The full Riemann-Stieltjes integral.

{open Set}

Technical notes:
- In Lean it is more convenient to make definitions such as `α_length` and the Riemann-Stieltjes
  integral totally defined, thus assigning "junk" values to the cases where the definition is
  not intended to be applied. For the definition of `α_length`, the definition is intended to be
  applied in contexts where left and right limits exist, and the function is extended by
  constants to the left and right of its intended domain of definition; for instance, if a
  function `x` `f` is defined on {lean}`Icc 0 1`, then it is intended that `f x = f 1` for all `x ≥ 1`
  and `f x = f 0` for all `x ≤ 0`; in particular, at a right endpoint, the value of a function
  is intended to agree with its right limit, and similarly for the left endpoint, although we
  do not enforce this in our definition of `α_length`. (For functions defined on open intervals,
  the extension is immaterial.)
- The notion of `α_length` and piecewise constant Riemann-Stieltjes integral is intended for
  situations where left and right limits exist, such as for monotone functions or continuous
  functions, though technically they make sense without these hypotheses. The full Riemann-Stieltjes
  integral is intended for functions that are of bounded variation, though we shall restrict
  attention to the special case of monotone increasing functions for the most part.
-/

namespace Chapter11

open BoundedInterval Chapter9

/-- Left and right limits. A junk value is assigned if the limit does not exist. -/
noncomputable abbrev right_lim (f: ℝ → ℝ) (x₀:ℝ) : ℝ := Filter.lim ((nhdsWithin x₀ (.Ioi x₀)).map f)

noncomputable abbrev left_lim (f: ℝ → ℝ) (x₀:ℝ) : ℝ := Filter.lim ((nhdsWithin x₀ (.Iio x₀)).map f)

theorem right_lim_def {f: ℝ → ℝ} {x₀ L:ℝ} (h: Convergesto (.Ioi x₀) f L x₀) :
  right_lim f x₀ = L := by
  show Filter.lim _ = L
  apply lim_eq; rwa [Convergesto.iff, Filter.Tendsto.eq_1] at h

theorem left_lim_def {f: ℝ → ℝ} {x₀ L:ℝ} (h: Convergesto (.Iio x₀) f L x₀) :
  left_lim f x₀ = L := by
  show Filter.lim _ = L
  apply lim_eq; rwa [Convergesto.iff, Filter.Tendsto.eq_1] at h

noncomputable abbrev jump (f: ℝ → ℝ) (x₀:ℝ) : ℝ :=
  right_lim f x₀ - left_lim f x₀

/-- Right limits exist for continuous functions -/
theorem right_lim_of_continuous {X:Set ℝ} {f: ℝ → ℝ} {x₀:ℝ}
  (h : ∃ ε>0, .Ico x₀ (x₀+ε) ⊆ X) (hf: ContinuousWithinAt f X x₀) :
  right_lim f x₀ = f x₀ := by
  choose ε hε hX using h
  apply right_lim_def
  rw [ContinuousWithinAt.eq_1] at hf
  replace hf : (nhdsWithin x₀ (.Ioo x₀ (x₀ + ε))).Tendsto f  (nhds (f x₀)) :=
    tendsto_nhdsWithin_mono_left (Set.Ioo_subset_Ico_self.trans hX) hf
  rw [Convergesto.iff]
  convert hf using 1
  have h1 : .Ioo x₀ (x₀ + ε) ∈ nhdsWithin x₀ (.Ioi x₀) := by
    convert inter_mem_nhdsWithin (t := .Ioo (x₀-ε) (x₀+ε)) _ _
    . grind
    apply Ioo_mem_nhds <;> linarith
  rw [←nhdsWithin_inter_of_mem h1]; congr 1; simp [Set.Ioo_subset_Ioi_self]

/-- Left limits exist for continuous functions -/
theorem left_lim_of_continuous {X:Set ℝ} {f: ℝ → ℝ} {x₀:ℝ}
  (h : ∃ ε>0, .Ioc (x₀-ε) x₀ ⊆ X) (hf: ContinuousWithinAt f X x₀) :
  left_lim f x₀ = f x₀ := by
  choose ε hε hX using h
  apply left_lim_def
  rw [ContinuousWithinAt.eq_1] at hf
  replace hf : (nhdsWithin x₀ (.Ioo (x₀ - ε) x₀)).Tendsto f (nhds (f x₀)) :=
    tendsto_nhdsWithin_mono_left (Set.Ioo_subset_Ioc_self.trans hX) hf
  rw [Convergesto.iff]
  convert hf using 1
  have h1 : .Ioo (x₀-ε) x₀ ∈ nhdsWithin x₀ (.Iio x₀) := by
    convert inter_mem_nhdsWithin (t := .Ioo (x₀-ε) (x₀+ε)) _ _
    . grind
    apply Ioo_mem_nhds <;> linarith
  rw [←nhdsWithin_inter_of_mem h1]
  congr 1; simp [Set.Ioo_subset_Iio_self]

/-- No jump for continuous functions -/
theorem jump_of_continuous {X:Set ℝ} {f: ℝ → ℝ} {x₀:ℝ}
  (h : X ∈ nhds x₀) (hf: ContinuousWithinAt f X x₀) :
  jump f x₀ = 0 := by
  rw [mem_nhds_iff_exists_Ioo_subset] at h
  choose l u hx₀ hX using h; simp at hx₀
  have hl : ∃ ε>0, .Ioc (x₀-ε) x₀ ⊆ X :=
    ⟨ x₀-l, by linarith, Set.Subset.trans (by intro x ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩) hX ⟩
  have hu : ∃ ε>0, .Ico x₀ (x₀+ε) ⊆ X :=
    ⟨ u-x₀, by linarith, Set.Subset.trans (by intro x ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩) hX ⟩
  simp [jump, left_lim_of_continuous hl hf, right_lim_of_continuous hu hf]

/-- Right limits exist for monotone functions -/
theorem right_lim_of_monotone {f: ℝ → ℝ} (x₀:ℝ) (hf: Monotone f) :
  Convergesto (.Ioi x₀) f (sInf (f '' .Ioi x₀)) x₀ := by
  rw [Convergesto.iff]
  apply (hf.monotoneOn _).tendsto_nhdsGT
  rw [bddBelow_def]; use f x₀; intro y hy; simp at hy; obtain ⟨ x, hx, rfl ⟩ := hy; apply hf; grind

theorem right_lim_of_monotone' {f: ℝ → ℝ} (x₀:ℝ) (hf: Monotone f) :
  right_lim f x₀ = sInf (f '' .Ioi x₀) := right_lim_def (right_lim_of_monotone x₀ hf)

/-- Left limits exist for monotone functions -/
theorem left_lim_of_monotone {f: ℝ → ℝ} (x₀:ℝ) (hf: Monotone f) :
  Convergesto (.Iio x₀) f (sSup (f '' .Iio x₀)) x₀ := by
  rw [Convergesto.iff]
  apply (hf.monotoneOn _).tendsto_nhdsLT
  rw [bddAbove_def]; use f x₀; intro y hy; simp at hy; obtain ⟨ x, hx, rfl ⟩ := hy; apply hf; grind

theorem left_lim_of_monotone' {f: ℝ → ℝ} (x₀:ℝ) (hf: Monotone f) :
  left_lim f x₀ = sSup (f '' .Iio x₀) := left_lim_def (left_lim_of_monotone x₀ hf)

theorem jump_of_monotone {f: ℝ → ℝ} (x₀:ℝ) (hf: Monotone f) :
  0 ≤ jump f x₀  := by
  simp [jump, left_lim_of_monotone' x₀ hf, right_lim_of_monotone' x₀ hf]
  apply csSup_le (by simp); intro a ha
  apply le_csInf (by simp); intro b hb; simp at ha hb
  obtain ⟨ x, hx, rfl ⟩ := ha; obtain ⟨ y, hy, rfl ⟩ := hb
  apply hf; grind

theorem right_lim_le_left_lim_of_monotone {f:ℝ → ℝ} {a b:ℝ} (hab: a < b)
  (hf: Monotone f) :
  right_lim f a ≤ left_lim f b := by
  rw [left_lim_of_monotone' b hf, right_lim_of_monotone' a hf]
  calc
    _ ≤ f ((a+b)/2) := by
      apply csInf_le
      . rw [bddBelow_def]; use f a; intro y hy; simp at hy; obtain ⟨ x, hx, rfl ⟩ := hy; apply hf; grind
      simp; use (a+b)/2; simp; linarith
    _ ≤ _ := by
      apply le_csSup
      . rw [bddAbove_def]; use f b; intro y hy; simp at hy; obtain ⟨ x, hx, rfl ⟩ := hy; apply hf; grind
      simp; use (a+b)/2; simp; linarith

/-- Definition 11.8.1 -/
noncomputable abbrev α_length (α: ℝ → ℝ) (I: BoundedInterval) : ℝ := match I with
| Icc a b => if a ≤ b then (right_lim α b) - (left_lim α a) else 0
| Ico a b => if a ≤ b then (left_lim α b) - (left_lim α a) else 0
| Ioc a b => if a ≤ b then (right_lim α b) - (right_lim α a) else 0
| Ioo a b => if a < b then (left_lim α b) - (right_lim α a) else 0

syntax:max term "[" term "]ₗ" : term
macro_rules | `($α[$I]ₗ) => `(α_length $α $I)

theorem α_length_of_empty (α: ℝ → ℝ) {I: BoundedInterval} (hI: (I:Set ℝ) = ∅) : α[I]ₗ = 0 :=
  match I with
  | Icc _ _ => by simp [Set.Icc_eq_empty_iff] at *; simp [*]
  | Ico a b => by simp [Set.Ico_eq_empty_iff] at *; intro h; have := le_antisymm hI h; subst this; simp
  | Ioc a b => by simp [Set.Ioc_eq_empty_iff] at *; intro h; have := le_antisymm hI h; subst this; simp
  | Ioo _ _ => by simp [Set.Ioo_eq_empty_iff] at *; simp [*]

@[simp]
theorem α_length_of_pt {α: ℝ → ℝ} (a:ℝ) : α[Icc a a]ₗ = jump α a := by simp [α_length, jump]

theorem α_length_of_cts {α:ℝ → ℝ} {I: BoundedInterval} {a b: ℝ}
  (haa: a < I.a) (hab: I.a ≤ I.b) (hbb: I.b < b)
  (hI : I ⊆ Ioo a b) (hα: ContinuousOn α (Ioo a b)) :
  α[I]ₗ = α I.b - α I.a := by
  have ha_left : left_lim α I.a = α I.a := by
    apply left_lim_of_continuous _ (hα.continuousWithinAt (by simp; grind))
    exact ⟨ I.a - a, by grind, by intro _; simp; grind ⟩
  have ha_right : right_lim α I.a = α I.a := by
    apply right_lim_of_continuous _ (hα.continuousWithinAt (by simp; grind))
    exact ⟨ b - I.a, by grind, by intro _; simp; grind ⟩
  have hb_left : left_lim α I.b = α I.b := by
    apply left_lim_of_continuous _ (hα.continuousWithinAt (by simp; grind))
    exact ⟨ I.b - a, by grind, by intro _; simp; grind ⟩
  have hb_right : right_lim α I.b = α I.b := by
    apply right_lim_of_continuous _ (hα.continuousWithinAt (by simp; grind))
    exact ⟨ b - I.b, by grind, by intro _; simp; grind ⟩
  cases I with
  | Icc _ _ => grind
  | Ico _ _ => grind
  | Ioc _ _ => grind
  | Ioo _ _ => simp [α_length, ha_right, hb_left]; intro h; have := le_antisymm h (by linarith); subst this; simp

/-- Example 11.8.2 -/
example : (fun x ↦ x^2)[Icc 2 3]ₗ = 5 := by
  have hright : right_lim (fun x ↦ x^2) 3 = (fun x ↦ x^2) 3 :=
    right_lim_of_continuous ⟨1, by norm_num, Set.subset_univ _⟩
      ((continuous_id.pow 2).continuousWithinAt)
  have hleft : left_lim (fun x ↦ x^2) 2 = (fun x ↦ x^2) 2 :=
    left_lim_of_continuous ⟨1, by norm_num, Set.subset_univ _⟩
      ((continuous_id.pow 2).continuousWithinAt)
  simp [α_length, hright, hleft]
  norm_num

example : (fun x ↦ x^2)[Icc 2 2]ₗ = 0 := by
  have hjump : jump (fun x ↦ x^2) 2 = 0 :=
    jump_of_continuous (isOpen_univ.mem_nhds (Set.mem_univ 2)) ((continuous_id.pow 2).continuousWithinAt)
  rw [α_length_of_pt, hjump]

example : (fun x ↦ x^2)[Ioo 2 2]ₗ = 0 := by
  simp [α_length]

/-- Example 11.8.3 -/
@[simp]
theorem α_len_of_id (I: BoundedInterval) : (fun x ↦ x)[I]ₗ = |I|ₗ := by
  have hright (x : ℝ) : right_lim (fun x ↦ x) x = (fun x ↦ x) x :=
    right_lim_of_continuous ⟨1, by norm_num, Set.subset_univ _⟩ continuousWithinAt_id
  have hleft (x : ℝ) : left_lim (fun x ↦ x) x = (fun x ↦ x) x :=
    left_lim_of_continuous ⟨1, by norm_num, Set.subset_univ _⟩ continuousWithinAt_id
  cases I with
  | Icc a b =>
    simp [α_length, hright, hleft, BoundedInterval.length, BoundedInterval.a, BoundedInterval.b]
    by_cases h : a ≤ b
    · simp [h]
    · simp [h, show b ≤ a from by linarith]
  | Ico a b =>
    simp [α_length, hleft, BoundedInterval.length, BoundedInterval.a, BoundedInterval.b]
    by_cases h : a ≤ b
    · simp [h]
    · simp [h, show b ≤ a from by linarith]
  | Ioc a b =>
    simp [α_length, hright, BoundedInterval.length, BoundedInterval.a, BoundedInterval.b]
    by_cases h : a ≤ b
    · simp [h]
    · simp [h, show b ≤ a from by linarith]
  | Ioo a b =>
    simp [α_length, hright, hleft, BoundedInterval.length, BoundedInterval.a, BoundedInterval.b]
    by_cases h : a < b
    · simp [h, show a ≤ b from by linarith]
    · simp [h, show b ≤ a from by linarith]

/-- An improved version of {name}`BoundedInterval.joins` that also controls {name}`α_length`. -/
abbrev BoundedInterval.joins' (K I J: BoundedInterval) : Prop :=  K.joins I J ∧ ∀ α:ℝ → ℝ, α[K]ₗ = α[I]ₗ + α[J]ₗ

theorem BoundedInterval.join_Icc_Ioc' {a b c:ℝ} (hab: a ≤ b) (hbc: b ≤ c) : (Icc a c).joins' (Icc a b) (Ioc b c) := ⟨ join_Icc_Ioc hab hbc,
  by simp [α_length, show a ≤ b by grind, show b ≤ c by grind, show a ≤ c by grind] ⟩


theorem BoundedInterval.join_Icc_Ioo' {a b c:ℝ} (hab: a ≤ b) (hbc: b < c) : (Ico a c).joins' (Icc a b) (Ioo b c) := ⟨ join_Icc_Ioo hab hbc,
  by simp [α_length, show a ≤ b by grind, show b < c by grind, show a ≤ c by grind] ⟩

theorem BoundedInterval.join_Ioc_Ioc' {a b c:ℝ} (hab: a ≤ b) (hbc: b ≤ c) : (Ioc a c).joins' (Ioc a b) (Ioc b c) := ⟨ join_Ioc_Ioc hab hbc,
  by simp [α_length, show a ≤ b by grind, show b ≤ c by grind, show a ≤ c by grind] ⟩

theorem BoundedInterval.join_Ioc_Ioo' {a b c:ℝ} (hab: a ≤ b) (hbc: b < c) : (Ioo a c).joins' (Ioc a b) (Ioo b c) := ⟨ join_Ioc_Ioo hab hbc,
  by simp [α_length, show a ≤ b by grind, show b < c by grind, show a < c by grind] ⟩

theorem BoundedInterval.join_Ico_Icc' {a b c:ℝ} (hab: a ≤ b) (hbc: b ≤ c) : (Icc a c).joins' (Ico a b) (Icc b c) := ⟨ join_Ico_Icc hab hbc,
  by simp [α_length, show a ≤ b by grind, show b ≤ c by grind, show a ≤ c by grind] ⟩

theorem BoundedInterval.join_Ico_Ico' {a b c:ℝ} (hab: a ≤ b) (hbc: b ≤ c) : (Ico a c).joins' (Ico a b) (Ico b c) := ⟨ join_Ico_Ico hab hbc,
  by simp [α_length, show a ≤ b by grind, show b ≤ c by grind, show a ≤ c by grind] ⟩

theorem BoundedInterval.join_Ioo_Icc' {a b c:ℝ} (hab: a < b) (hbc: b ≤ c) : (Ioc a c).joins' (Ioo a b) (Icc b c) := ⟨ join_Ioo_Icc hab hbc,
  by simp [α_length, show a < b by grind, show b ≤ c by grind, show a ≤ c by grind] ⟩

theorem BoundedInterval.join_Ioo_Ico' {a b c:ℝ} (hab: a < b) (hbc: b ≤ c) : (Ioo a c).joins' (Ioo a b) (Ico b c) := ⟨ join_Ioo_Ico hab hbc,
  by simp [α_length, show a < b by grind, show b ≤ c by grind, show a < c by grind] ⟩

lemma set_singleton_imp_Icc {I : BoundedInterval} {x : ℝ} (h : (I : Set ℝ) = {x}) : I = Icc x x := by
  have hx_mem : x ∈ (I : Set ℝ) := by rw [h]; simp
  induction I with
  | Icc a b =>
    have hx : x ∈ Set.Icc a b := by simpa using hx_mem
    rcases hx with ⟨ha_x, hx_b⟩
    have hb_le_a : b ≤ a := by
      by_contra! h_lt
      have ha_mem : a ∈ (Icc a b : Set ℝ) := by
        have : a ∈ Set.Icc a b := ⟨by nlinarith, by nlinarith⟩
        simpa using this
      have hb_mem : b ∈ (Icc a b : Set ℝ) := by
        have : b ∈ Set.Icc a b := ⟨by nlinarith, by nlinarith⟩
        simpa using this
      have ha_x' : a = x := by
        rw [h] at ha_mem; simp at ha_mem; exact ha_mem
      have hb_x' : b = x := by
        rw [h] at hb_mem; simp at hb_mem; exact hb_mem
      nlinarith
    have ha_eq_x : a = x := by nlinarith
    have hb_eq_x : b = x := by nlinarith
    subst ha_eq_x; subst hb_eq_x; rfl
  | Ico a b =>
    have hx : x ∈ Set.Ico a b := by simpa using hx_mem
    rcases hx with ⟨ha_x, hx_lt_b⟩
    by_cases ha_lt_x : a < x
    · have hy : (a + x) / 2 ∈ (Ico a b : Set ℝ) := by
        have : (a + x) / 2 ∈ Set.Ico a b := by
          constructor <;> nlinarith
        simpa using this
      rw [h] at hy; simp at hy; nlinarith
    · have ha_eq_x : a = x := by nlinarith
      have h_temp : (Ico x b : Set ℝ) = {x} := by
        simpa [ha_eq_x] using h
      have hy : (x + b) / 2 ∈ (Ico x b : Set ℝ) := by
        have : (x + b) / 2 ∈ Set.Ico x b := by
          constructor <;> nlinarith
        simpa using this
      rw [h_temp] at hy; simp at hy; nlinarith
  | Ioc a b =>
    have hx : x ∈ Set.Ioc a b := by simpa using hx_mem
    rcases hx with ⟨ha_lt_x, hx_b⟩
    by_cases hx_lt_b : x < b
    · have hy : (x + b) / 2 ∈ (Ioc a b : Set ℝ) := by
        have : (x + b) / 2 ∈ Set.Ioc a b := by
          constructor <;> nlinarith
        simpa using this
      rw [h] at hy; simp at hy; nlinarith
    · have hx_eq_b : x = b := by nlinarith
      have h_temp : (Ioc a x : Set ℝ) = {x} := by
        simpa [hx_eq_b] using h
      have hy : (a + x) / 2 ∈ (Ioc a x : Set ℝ) := by
        have : (a + x) / 2 ∈ Set.Ioc a x := by
          constructor <;> nlinarith
        simpa using this
      rw [h_temp] at hy; simp at hy; nlinarith
  | Ioo a b =>
    have hx : x ∈ Set.Ioo a b := by simpa using hx_mem
    rcases hx with ⟨ha_lt_x, hx_lt_b⟩
    have hy : (a + x) / 2 ∈ (Ioo a b : Set ℝ) := by
      have : (a + x) / 2 ∈ Set.Ioo a b := by
        constructor <;> nlinarith
      simpa using this
    rw [h] at hy; simp at hy; nlinarith

/-- Theorem 11.8.4 / Exercise 11.8.1 -/
theorem Partition.sum_of_α_length  {I: BoundedInterval} (P: Partition I) (α: ℝ → ℝ) :
  ∑ J ∈ P.intervals, α[J]ₗ = α[I]ₗ := by
  generalize hcard: P.intervals.card = n
  revert I; induction' n with n hn <;> intro I P hcard
  . rw [Finset.card_eq_zero] at hcard
    have : (I:Set ℝ) = ∅ := by
      by_contra! hne
      rcases hne with ⟨x, hx⟩
      rcases P.exists_unique x hx with ⟨J, ⟨hJmem, _⟩, _⟩
      have hP_empty : P.intervals = ∅ := hcard
      have hJmem' : J ∈ P.intervals := hJmem
      rw [hP_empty] at hJmem'
      simp at hJmem'
    have h_len : α[I]ₗ = 0 := α_length_of_empty α this
    simp [hcard, h_len]
  by_cases h : Subsingleton (I:Set ℝ)
  . have hJ_subs (J: BoundedInterval) (hJ: J ∈ P) : Subsingleton (J:Set ℝ) := by
      apply Subsingleton.intro
      intro a b
      apply Subtype.ext
      have haJ : a.val ∈ (J : Set ℝ) := a.property
      have hbJ : b.val ∈ (J : Set ℝ) := b.property
      have haI : a.val ∈ (I : Set ℝ) := (P.contains J hJ a.val) haJ
      have hbI : b.val ∈ (I : Set ℝ) := (P.contains J hJ b.val) hbJ
      have h_eq : (⟨a.val, haI⟩ : (I : Set ℝ)) = (⟨b.val, hbI⟩ : (I : Set ℝ)) :=
        Subsingleton.elim _ _
      injection h_eq
    by_cases hne : (I:Set ℝ).Nonempty
    · rcases hne with ⟨x, hx⟩
      have hI_set : (I : Set ℝ) = {x} := by
        have hI_subs : Set.Subsingleton (I : Set ℝ) := by
          simpa [Set.subsingleton_coe] using h
        exact hI_subs.eq_singleton_of_mem hx
      rcases P.exists_unique x hx with ⟨J, ⟨hJmem, hxJ⟩, huniq⟩
      have h_rest_zero : ∑ K ∈ P.intervals.erase J, α[K]ₗ = 0 := by
        refine Finset.sum_eq_zero ?_
        intro K hKmem_erase
        have hKmem : K ∈ P.intervals := (Finset.mem_erase.mp hKmem_erase).2
        have hKneJ : K ≠ J := (Finset.mem_erase.mp hKmem_erase).1
        have hx_not_K : x ∉ (K : Set ℝ) := by
          intro hxK; apply hKneJ; exact huniq K ⟨hKmem, hxK⟩
        have hK_sub_I : (K : Set ℝ) ⊆ (I : Set ℝ) := λ y hy => (P.contains K hKmem y) hy
        rw [hI_set] at hK_sub_I
        have hK_empty : (K : Set ℝ) = ∅ :=
          Set.not_nonempty_iff_eq_empty.mp (by
            intro hneK; rcases hneK with ⟨y, hy⟩
            have hy_singleton : y ∈ ({x} : Set ℝ) := hK_sub_I hy
            simp at hy_singleton; subst hy_singleton
            exact hx_not_K hy)
        exact α_length_of_empty α hK_empty
      have hα_J_eq_α_I : α[J]ₗ = α[I]ₗ := by
        have hJ_set : (J : Set ℝ) = {x} := by
          have hJ_subs_set : Set.Subsingleton (J : Set ℝ) := by
            simpa [Set.subsingleton_coe] using hJ_subs J hJmem
          exact hJ_subs_set.eq_singleton_of_mem hxJ
        have hJ_eq : J = Icc x x := set_singleton_imp_Icc hJ_set
        have hI_eq : I = Icc x x := set_singleton_imp_Icc hI_set
        rw [hJ_eq, hI_eq]
      calc
        ∑ K ∈ P.intervals, α[K]ₗ = α[J]ₗ + ∑ K ∈ P.intervals.erase J, α[K]ₗ := by
          rw [Finset.add_sum_erase P.intervals (λ K => α[K]ₗ) hJmem]
        _ = α[J]ₗ := by simp [h_rest_zero]
        _ = α[I]ₗ := hα_J_eq_α_I
    · have hempty : (I : Set ℝ) = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      have h_all_zero : ∀ K ∈ P.intervals, α[K]ₗ = 0 := by
        intro K hKmem
        have hK_sub_I : (K : Set ℝ) ⊆ (I : Set ℝ) := λ y hy => (P.contains K hKmem y) hy
        rw [hempty] at hK_sub_I
        have hK_empty : (K : Set ℝ) = ∅ :=
          Set.not_nonempty_iff_eq_empty.mp (by
            intro hneK; rcases hneK with ⟨y, hy⟩
            have hy_empty : y ∈ (∅ : Set ℝ) := hK_sub_I hy
            simp at hy_empty)
        exact α_length_of_empty α hK_empty
      simp [α_length_of_empty α hempty, Finset.sum_eq_zero h_all_zero]
  simp [length_of_subsingleton, length, -Set.subsingleton_coe] at h
  have : ∃ K L : BoundedInterval, K ∈ P ∧ I.joins' L K := by
    by_cases hI' : I.b ∈ I
    . choose K hK hbK using (P.exists_unique I.b hI').exists
      observe hKI : K ⊆ I
      by_cases hsub : Subsingleton (K:Set ℝ)
      . simp_all [mem_iff]
        apply hsub.eq_singleton_of_mem at hbK
        have : K = Icc (I.b) (I.b) := by
          have hK_set_eq : (K : Set ℝ) = {I.b} := hbK
          have hmem : I.b ∈ (K : Set ℝ) := by
            simp [hK_set_eq]
          cases K with
          | Ioo a b =>
            rcases Set.mem_Ioo.mp hmem with ⟨ha_lt_Ib, hIb_lt_b⟩
            have ha_lt_b : a < b := lt_trans ha_lt_Ib hIb_lt_b
            have hsub_set : (Ioo a b : Set ℝ).Subsingleton := by
              simpa using hsub
            have hx : (2*a + b)/3 ∈ (Ioo a b : Set ℝ) := by
              apply Set.mem_Ioo.mpr; constructor <;> nlinarith
            have hy : (a + 2*b)/3 ∈ (Ioo a b : Set ℝ) := by
              apply Set.mem_Ioo.mpr; constructor <;> nlinarith
            have h_val_eq : (2*a + b)/3 = (a + 2*b)/3 :=
              hsub_set hx hy
            have hneq : (2*a + b)/3 ≠ (a + 2*b)/3 := by nlinarith
            exfalso; exact hneq h_val_eq
          | Icc a b =>
            have ha_le_Ib : a ≤ I.b := (Set.mem_Icc.mp hmem).1
            have hIb_le_b : I.b ≤ b := (Set.mem_Icc.mp hmem).2
            have hsub_set : (Icc a b : Set ℝ).Subsingleton := by
              simpa using hsub
            have hb_le_a : b ≤ a := by
              have : (Set.Icc a b).Subsingleton := by simpa using hsub_set
              rw [Set.subsingleton_Icc_iff] at this
              exact this
            have ha_eq_Ib : a = I.b := by nlinarith
            have hb_eq_Ib : b = I.b := by nlinarith
            simp [ha_eq_Ib, hb_eq_Ib]
          | Ioc a b =>
            rcases Set.mem_Ioc.mp hmem with ⟨ha_lt_Ib, hIb_le_b⟩
            have ha_lt_b : a < b := lt_of_lt_of_le ha_lt_Ib hIb_le_b
            have hsub_set : (Ioc a b : Set ℝ).Subsingleton := by
              simpa using hsub
            have hx : (2*a + b)/3 ∈ (Ioc a b : Set ℝ) := by
              apply Set.mem_Ioc.mpr; constructor <;> nlinarith
            have hy : (a + 2*b)/3 ∈ (Ioc a b : Set ℝ) := by
              apply Set.mem_Ioc.mpr; constructor <;> nlinarith
            have h_val_eq : (2*a + b)/3 = (a + 2*b)/3 :=
              hsub_set hx hy
            have hneq : (2*a + b)/3 ≠ (a + 2*b)/3 := by nlinarith
            exfalso; exact hneq h_val_eq
          | Ico a b =>
            rcases Set.mem_Ico.mp hmem with ⟨ha_le_Ib, hIb_lt_b⟩
            have ha_lt_b : a < b := lt_of_le_of_lt ha_le_Ib hIb_lt_b
            have hsub_set : (Ico a b : Set ℝ).Subsingleton := by
              simpa using hsub
            have hx : (2*a + b)/3 ∈ (Ico a b : Set ℝ) := by
              apply Set.mem_Ico.mpr; constructor <;> nlinarith
            have hy : (a + 2*b)/3 ∈ (Ico a b : Set ℝ) := by
              apply Set.mem_Ico.mpr; constructor <;> nlinarith
            have h_val_eq : (2*a + b)/3 = (a + 2*b)/3 :=
              hsub_set hx hy
            have hneq : (2*a + b)/3 ≠ (a + 2*b)/3 := by nlinarith
            exfalso; exact hneq h_val_eq
        subst this
        cases I with
        | Ioo _ _ => simp at hI'
        | Icc a b => use (Icc b b), hK, Ico a b; exact join_Ico_Icc' (by order) (by order)
        | Ioc a b => use (Icc b b), hK, Ioo a b; exact join_Ioo_Icc' (by order) (by order)
        | Ico _ _ => simp at hI'
      simp [length_of_subsingleton, -Set.subsingleton_coe] at hsub
      have hKI' := (K.Ioo_subset.trans hKI).trans I.subset_Icc
      simp only [subset_iff] at hKI'
      have hKb : K.b = I.b := by
        rw [le_antisymm_iff]; split_ands
        . apply csSup_le_csSup bddAbove_Icc (by simp [hsub]) at hKI'
          simp_all [csSup_Ioo hsub, csSup_Icc (le_of_lt h)]
        have := K.subset_Icc _ hbK; simp [mem_iff] at this; exact this.2
      have hKA : I.a ≤ K.a := by
        apply csInf_le_csInf bddBelow_Icc (by simp [hsub]) at hKI'
        simp_all [csInf_Icc (le_of_lt h), csInf_Ioo]
      cases I with
      | Ioo _ _ => simp [mem_iff] at hI'
      | Icc a₁ b₁ =>
        use K; cases K with
        | Ioo _ _ => simp [mem_iff, subset_iff] at *; grind
        | Icc c₂ b₂ => use Ico a₁ c₂, hK; simp_all; apply join_Ico_Icc' <;> order
        | Ioc c₂ b₂ => use Icc a₁ c₂, hK; simp_all; apply join_Icc_Ioc' <;> order
        | Ico _ _ => simp [mem_iff] at *; grind
      | Ioc a₁ b₁ =>
        use K; cases K with
        | Ioo _ _ => simp_all [mem_iff]
        | Icc c₂ b₂ =>
          use Ioo a₁ c₂, hK
          simp_all [subset_iff]
          have : c₂ ∈ Set.Icc c₂ b₁ := by grind
          apply hKI at this; apply join_Ioo_Icc' <;> grind
        | Ioc c₂ b₂ => use Ioc a₁ c₂, hK; simp_all; apply join_Ioc_Ioc' <;> order
        | Ico _ _ => simp [mem_iff, subset_iff] at *; grind
      | Ico _ _ => simp [mem_iff] at hI'
    choose c hc hK using P.exist_right h hI'
    cases I with
    | Ioo a₁ b₁ =>
      obtain hK | hK := hK <;> simp_all [mem_iff]
      . use Ioo c b₁, hK, Ioc a₁ c; apply join_Ioc_Ioo' <;> tauto
      use Ico c b₁, hK, Ioo a₁ c
      apply P.contains at hK; simp [subset_iff] at hK
      have : c ∈ Set.Ico c b₁ := by grind
      apply join_Ioo_Ico' <;> grind
    | Icc _ _ => simp [mem_iff] at hI' h; order
    | Ioc _ _ => simp [mem_iff] at hI' h; order
    | Ico a₁ b₁ =>
      obtain hK | hK := hK <;> simp_all [mem_iff]
      . use Ioo c b₁, hK, Icc a₁ c; apply join_Icc_Ioo' <;> grind
      use Ico c b₁, hK, Ico a₁ c; apply join_Ico_Ico' <;> grind
  obtain ⟨ K, L, hK, ⟨⟨ h1, h2, h3 ⟩, h_α ⟩ ⟩ := this
  have : ∃ P' : Partition L, P'.intervals = P.intervals.erase K := by
    refine ⟨{
      intervals := P.intervals.erase K
      exists_unique := by
        intro x hxL
        have hxI : x ∈ (I : Set ℝ) := by
          rw [h2]
          exact Set.mem_union_left (K : Set ℝ) hxL
        rcases P.exists_unique x hxI with ⟨J, ⟨hJmem, hxJ⟩, huniq⟩
        have hx_not_K : x ∉ (K : Set ℝ) := by
          intro hxK
          have : x ∈ (L : Set ℝ) ∩ (K : Set ℝ) := Set.mem_inter hxL hxK
          rw [h1] at this
          simp at this
        have hJ_ne_K : J ≠ K := by
          intro h_eq
          subst h_eq
          apply hx_not_K
          simpa [mem_iff] using hxJ
        have hJ_mem_erase : J ∈ P.intervals.erase K :=
          Finset.mem_erase.mpr ⟨hJ_ne_K, hJmem⟩
        refine ⟨J, ⟨hJ_mem_erase, hxJ⟩, ?_⟩
        intro J' ⟨hJ'_mem_erase, hxJ'⟩
        have hJ'_mem : J' ∈ P.intervals := (Finset.mem_erase.mp hJ'_mem_erase).2
        exact huniq J' ⟨hJ'_mem, hxJ'⟩
      contains := by
        intro J hJ_erase
        have hJmem : J ∈ P.intervals := (Finset.mem_erase.mp hJ_erase).2
        have hJ_ne_K : J ≠ K := (Finset.mem_erase.mp hJ_erase).1
        intro x hxJ
        have hxI : x ∈ (I : Set ℝ) := (P.contains J hJmem) x hxJ
        rw [h2] at hxI
        rcases hxI with (hxL | hxK)
        · simpa [mem_iff] using hxL
        · exfalso
          have hxI' : x ∈ (I : Set ℝ) := by
            rw [h2]
            exact Set.mem_union_right (L : Set ℝ) hxK
          rcases P.exists_unique x hxI' with ⟨J', ⟨hJ'mem, hxJ'⟩, huniq⟩
          have hJ_eq_K : J = K :=
            (huniq J ⟨hJmem, hxJ⟩).trans (huniq K ⟨hK, by
              simpa [mem_iff] using hxK⟩).symm
          exact hJ_ne_K hJ_eq_K
    }, rfl⟩
  choose P' hP' using this
  rw [h_α α, ←Finset.add_sum_erase _ _ hK, ←hP', add_comm]; congr
  apply hn; simp [hP', Finset.card_erase_of_mem hK, hcard]

/-- Definition 11.8.5 (Piecewise constant RS integral)-/
noncomputable abbrev PiecewiseConstantWith.RS_integ (f:ℝ → ℝ) {I: BoundedInterval} (P: Partition I) (α: ℝ → ℝ)   :
  ℝ := ∑ J ∈ P.intervals, constant_value_on f (J:Set ℝ) * α[J]ₗ

/-- Example 11.8.6 -/
noncomputable abbrev f_11_8_6 (x:ℝ) : ℝ := if x < 2 then 4 else 2

noncomputable abbrev P_11_8_6 : Partition (Icc 1 3) :=
  (⊥: Partition (Ico 1 2)).join (⊥ : Partition (Icc 2 3))
  (join_Ico_Icc (by norm_num) (by norm_num) )

theorem f_11_8_6_RS_integ : PiecewiseConstantWith.RS_integ f_11_8_6 P_11_8_6 (fun x ↦ x^2) = 22 := by
  have h_intervals : P_11_8_6.intervals = {Ico 1 2, Icc 2 3} := by
    rw [P_11_8_6, Partition.intervals_of_join, Partition.intervals_of_bot, Partition.intervals_of_bot]
    simp
  have h_const_Ico : constant_value_on f_11_8_6 (Ico 1 2 : Set ℝ) = 4 := by
    apply ConstantOn.const_eq ⟨1.5, by norm_num⟩
    intro x hx; rcases hx with ⟨hx1, hx2⟩; simp [f_11_8_6, hx2]
  have h_const_Icc : constant_value_on f_11_8_6 (Icc 2 3 : Set ℝ) = 2 := by
    apply ConstantOn.const_eq ⟨2.5, by norm_num⟩
    intro x hx; rcases hx with ⟨hx1, hx2⟩; simp [f_11_8_6, hx1]
  have h_α_Ico : (fun x ↦ x^2)[Ico 1 2]ₗ = 3 := by
    have hleft2 : left_lim (fun x ↦ x^2) 2 = (fun x ↦ x^2) 2 :=
      left_lim_of_continuous ⟨1, by norm_num, Set.subset_univ _⟩
        ((continuous_id.pow 2).continuousWithinAt)
    have hleft1 : left_lim (fun x ↦ x^2) 1 = (fun x ↦ x^2) 1 :=
      left_lim_of_continuous ⟨1, by norm_num, Set.subset_univ _⟩
        ((continuous_id.pow 2).continuousWithinAt)
    simp [α_length, hleft2, hleft1]
    norm_num
  have h_α_Icc : (fun x ↦ x^2)[Icc 2 3]ₗ = 5 := by
    have hright : right_lim (fun x ↦ x^2) 3 = (fun x ↦ x^2) 3 :=
      right_lim_of_continuous ⟨1, by norm_num, Set.subset_univ _⟩
        ((continuous_id.pow 2).continuousWithinAt)
    have hleft : left_lim (fun x ↦ x^2) 2 = (fun x ↦ x^2) 2 :=
      left_lim_of_continuous ⟨1, by norm_num, Set.subset_univ _⟩
        ((continuous_id.pow 2).continuousWithinAt)
    simp [α_length, hright, hleft]
    norm_num
  rw [PiecewiseConstantWith.RS_integ, h_intervals]
  have h_not_mem : (Ico 1 2 : BoundedInterval) ∉ ({Icc 2 3} : Finset BoundedInterval) := by
    simp
  rw [Finset.sum_insert h_not_mem, Finset.sum_singleton]
  unfold constant_value_on at *
  unfold constant_value at *
  rw [h_const_Ico, h_const_Icc, h_α_Ico, h_α_Icc]
  norm_num

/-- Example 11.8.7 -/
theorem PiecewiseConstantWith.RS_integ_eq_integ {f:ℝ → ℝ} {I: BoundedInterval} (P: Partition I) :RS_integ f P (fun x ↦ x) = integ f P := by
  simp [PiecewiseConstantWith.RS_integ, PiecewiseConstantWith.integ, α_len_of_id]

/-- If two intervals in a partition intersect, they are equal. -/
lemma Partition.eq_of_mem_inter {I : BoundedInterval} (P : Partition I) {J K : BoundedInterval}
  (hJ : J ∈ P.intervals) (hK : K ∈ P.intervals) {x : ℝ} (hxJ : x ∈ J) (hxK : x ∈ K) : J = K := by
  have hxI : x ∈ I := (P.contains J hJ) x hxJ
  rcases P.exists_unique x hxI with ⟨L, ⟨hL, hxL⟩, huniq⟩
  have hJ_eq_L : J = L := huniq J ⟨hJ, hxJ⟩
  have hK_eq_L : K = L := huniq K ⟨hK, hxK⟩
  rw [hJ_eq_L, hK_eq_L]

/-- If P ≤ Q, the RS integral with respect to Q equals the RS integral with respect to P. -/
lemma RS_integ_eq_of_refinement {f : ℝ → ℝ} {I : BoundedInterval} {P Q : Partition I}
  (hP : PiecewiseConstantWith f P) (hPQ : P ≤ Q) (α : ℝ → ℝ) :
  PiecewiseConstantWith.RS_integ f Q α = PiecewiseConstantWith.RS_integ f P α := by
  classical
    let nonempty_set (J : BoundedInterval) : Prop := Set.Nonempty (J : Set ℝ)
    let Q_intervals_K (K : BoundedInterval) : Finset BoundedInterval :=
      (Q.intervals).filter (λ J => J ⊆ K ∧ nonempty_set J)
    have h_nonempty_contrib_eq : ∑ J ∈ (Q.intervals).filter nonempty_set,
      constant_value_on f (J : Set ℝ) * α[J]ₗ = PiecewiseConstantWith.RS_integ f Q α := by
      rw [PiecewiseConstantWith.RS_integ]
      have h_filter_subset : (Q.intervals).filter nonempty_set ⊆ Q.intervals := Finset.filter_subset _ _
      apply Finset.sum_subset h_filter_subset
      intro x hx hx'
      have hx_not_nonempty : ¬nonempty_set x := by
        intro hx_nonempty
        apply hx'
        exact Finset.mem_filter.mpr ⟨hx, hx_nonempty⟩
      have hx_empty : (x : Set ℝ) = ∅ := Set.not_nonempty_iff_eq_empty.mp hx_not_nonempty
      have hx_alpha : α[x]ₗ = 0 := α_length_of_empty α hx_empty
      simp [hx_alpha]
    have h_sum_K (K : BoundedInterval) (hK : K ∈ P.intervals) :
      ∑ J ∈ Q_intervals_K K, α[J]ₗ = α[K]ₗ := by
      let Q_K : Partition K :=
      { intervals := Q_intervals_K K
        exists_unique := by
          intro x hx
          have hxI : x ∈ I := (P.contains K hK) x hx
          rcases Q.exists_unique x hxI with ⟨J, ⟨hJmem, hxJ⟩, huniq⟩
          have hJK : J ⊆ K := by
            rcases hPQ J hJmem with ⟨K', hK', hJK'⟩
            have hxK' : x ∈ K' := hJK' x hxJ
            have h_eq : K' = K := Partition.eq_of_mem_inter P hK' hK hxK' hx
            subst h_eq; exact hJK'
          have hJ_nonempty : nonempty_set J := ⟨x, hxJ⟩
          have hJmem' : J ∈ Q_intervals_K K := by
            simp [Q_intervals_K, nonempty_set, hJmem, hJK, hJ_nonempty]
          refine ⟨J, ⟨hJmem', hxJ⟩, ?_⟩
          intro J' ⟨hJ'mem', hxJ'⟩
          have hJ'_filter : J' ∈ (Q.intervals).filter (λ J' => J' ⊆ K ∧ nonempty_set J') := by
            simpa [Q_intervals_K] using hJ'mem'
          rcases Finset.mem_filter.mp hJ'_filter with ⟨hJ'mem, hJ'cond⟩
          exact huniq J' ⟨hJ'mem, hxJ'⟩
        contains := by
          intro J hJ
          have hJ_filter : J ∈ (Q.intervals).filter (λ J => J ⊆ K ∧ nonempty_set J) := by
            simpa [Q_intervals_K] using hJ
          rcases Finset.mem_filter.mp hJ_filter with ⟨hJmem, hJcond⟩
          exact hJcond.1
      }
      calc
        ∑ J ∈ Q_intervals_K K, α[J]ₗ = ∑ J ∈ Q_K.intervals, α[J]ₗ := rfl
        _ = α[K]ₗ := Partition.sum_of_α_length Q_K α
    have h_bUnion : Finset.biUnion P.intervals Q_intervals_K = (Q.intervals).filter nonempty_set := by
      ext J
      constructor
      · intro hJ
        rcases Finset.mem_biUnion.mp hJ with ⟨K, hK, hJ'⟩
        have hJ_filter : J ∈ (Q.intervals).filter (λ J => J ⊆ K ∧ nonempty_set J) := by
          simpa [Q_intervals_K] using hJ'
        rcases Finset.mem_filter.mp hJ_filter with ⟨hJmem, ⟨hJK, hJ_nonempty⟩⟩
        simp [hJmem, hJ_nonempty, nonempty_set]
      · intro hJ
        rcases Finset.mem_filter.mp hJ with ⟨hJmem, hJ_nonempty⟩
        rcases hPQ J hJmem with ⟨K, hK, hJK⟩
        apply Finset.mem_biUnion.mpr
        refine ⟨K, hK, ?_⟩
        simp [Q_intervals_K, nonempty_set, hJmem, hJK, hJ_nonempty]
    have h_disjoint : ∀ K₁ ∈ P.intervals, ∀ K₂ ∈ P.intervals, K₁ ≠ K₂ → Disjoint (Q_intervals_K K₁) (Q_intervals_K K₂) := by
      intro K₁ hK₁ K₂ hK₂ hne
      rw [Finset.disjoint_iff_inter_eq_empty]
      ext J
      constructor
      · intro hJ
        rcases Finset.mem_inter.mp hJ with ⟨hJ₁, hJ₂⟩
        have hJ₁_filter : J ∈ (Q.intervals).filter (λ J' => J' ⊆ K₁ ∧ nonempty_set J') := by
          simpa [Q_intervals_K] using hJ₁
        have hJ₂_filter : J ∈ (Q.intervals).filter (λ J' => J' ⊆ K₂ ∧ nonempty_set J') := by
          simpa [Q_intervals_K] using hJ₂
        rcases Finset.mem_filter.mp hJ₁_filter with ⟨hJmem₁, ⟨hJK₁, hJ_nonempty₁⟩⟩
        rcases Finset.mem_filter.mp hJ₂_filter with ⟨hJmem₂, ⟨hJK₂, hJ_nonempty₂⟩⟩
        rcases hJ_nonempty₁ with ⟨x, hx⟩
        exfalso
        exact hne (Partition.eq_of_mem_inter P hK₁ hK₂ (hJK₁ x hx) (hJK₂ x hx))
      · intro hJ
        exfalso
        simp at hJ
    calc
      PiecewiseConstantWith.RS_integ f Q α = ∑ J ∈ (Q.intervals).filter nonempty_set,
        constant_value_on f (J : Set ℝ) * α[J]ₗ := by symm; exact h_nonempty_contrib_eq
      _ = ∑ J ∈ Finset.biUnion P.intervals Q_intervals_K, constant_value_on f (J : Set ℝ) * α[J]ₗ := by rw [h_bUnion]
      _ = ∑ K ∈ P.intervals, ∑ J ∈ Q_intervals_K K, constant_value_on f (J : Set ℝ) * α[J]ₗ := by
        rw [Finset.sum_biUnion h_disjoint]
      _ = ∑ K ∈ P.intervals, ∑ J ∈ Q_intervals_K K, constant_value_on f (K : Set ℝ) * α[J]ₗ := by
        refine Finset.sum_congr rfl (λ K hK => ?_)
        refine Finset.sum_congr rfl (λ J hJ => ?_)
        have hJ_filter : J ∈ (Q.intervals).filter (λ J => J ⊆ K ∧ nonempty_set J) := by
          simpa [Q_intervals_K] using hJ
        rcases Finset.mem_filter.mp hJ_filter with ⟨hJmem, ⟨hJK, hJ_nonempty⟩⟩
        rcases hJ_nonempty with ⟨x, hx⟩
        have h_const_J : ConstantOn f (J : Set ℝ) := by
          rcases hP K hK with ⟨c, hc⟩
          refine ⟨c, λ y => hc ⟨y.val, hJK y.val y.property⟩⟩
        have h_val_eq : constant_value_on f (J : Set ℝ) = constant_value_on f (K : Set ℝ) := by
          calc
            constant_value_on f (J : Set ℝ) = f x := (ConstantOn.eq h_const_J hx).symm
            _ = constant_value_on f (K : Set ℝ) := ConstantOn.eq (hP K hK) (hJK x hx)
        simp [h_val_eq]
      _ = ∑ K ∈ P.intervals, constant_value_on f (K : Set ℝ) * (∑ J ∈ Q_intervals_K K, α[J]ₗ) := by
        simp [Finset.mul_sum]
      _ = ∑ K ∈ P.intervals, constant_value_on f (K : Set ℝ) * α[K]ₗ := by
        refine Finset.sum_congr rfl (λ K hK => ?_)
        rw [h_sum_K K hK]
      _ = PiecewiseConstantWith.RS_integ f P α := rfl

lemma PiecewiseConstantWith.sup {f : ℝ → ℝ} {I : BoundedInterval} {P P' : Partition I}
  (hP : PiecewiseConstantWith f P) (_hP' : PiecewiseConstantWith f P') : PiecewiseConstantWith f (P ⊔ P') := by
  intro K hK
  have hK_sup : K ∈ Finset.image₂ (fun J K' => J ∩ K') P.intervals P'.intervals := hK
  rcases Finset.mem_image₂.mp hK_sup with ⟨J, hJ, J', hJ', rfl⟩
  rcases hP J hJ with ⟨c, hc⟩
  refine ⟨c, λ x => ?_⟩
  have hxJ : (x : ℝ) ∈ (J : Set ℝ) := by
    have hx_inter : (x : ℝ) ∈ ((J : Set ℝ) ∩ (J' : Set ℝ)) := by
      simpa [BoundedInterval.inter_eq J J'] using x.property
    exact hx_inter.1
  exact hc ⟨x, hxJ⟩

/-- Analogue of Proposition 11.2.13 -/
theorem PiecewiseConstantWith.RS_integ_eq {f:ℝ → ℝ} {I: BoundedInterval} {P P': Partition I}
  (hP: PiecewiseConstantWith f P) (hP': PiecewiseConstantWith f P') (α:ℝ → ℝ): RS_integ f P α = RS_integ f P' α := by
  have hmax := BoundedInterval.le_max P P'
  have hPQ : P ≤ P ⊔ P' := hmax.1
  have hP'Q : P' ≤ P ⊔ P' := hmax.2
  have hQ : PiecewiseConstantWith f (P ⊔ P') := PiecewiseConstantWith.sup hP hP'
  calc
    RS_integ f P α = PiecewiseConstantWith.RS_integ f P α := rfl
    _ = PiecewiseConstantWith.RS_integ f (P ⊔ P') α := (RS_integ_eq_of_refinement hP hPQ α).symm
    _ = PiecewiseConstantWith.RS_integ f P' α := RS_integ_eq_of_refinement hP' hP'Q α
    _ = RS_integ f P' α := rfl

open Classical in
noncomputable abbrev PiecewiseConstantOn.RS_integ (f:ℝ → ℝ) (I: BoundedInterval) (α:ℝ → ℝ):
  ℝ := if h: PiecewiseConstantOn f I then PiecewiseConstantWith.RS_integ f h.choose α else 0

theorem PiecewiseConstantOn.RS_integ_def {f:ℝ → ℝ} {I: BoundedInterval} {P: Partition I}
  (h: PiecewiseConstantWith f P) (α:ℝ → ℝ) : RS_integ f I α = PiecewiseConstantWith.RS_integ f P α := by
  have h' : PiecewiseConstantOn f I := by use P
  simp [RS_integ, h']; exact PiecewiseConstantWith.RS_integ_eq h'.choose_spec h α

/-- {name}`α_length` non-negative when α monotone -/
theorem α_length_nonneg_of_monotone {α:ℝ → ℝ}  (hα: Monotone α) (I: BoundedInterval):
  0 ≤ α[I]ₗ := by
  cases I with
  | Icc a b =>
    simp [α_length]
    split
    · by_cases hlt : a < b
      · have h1 : left_lim α a ≤ right_lim α a := by
          have := jump_of_monotone a hα; linarith
        have h2 : right_lim α a ≤ left_lim α b := right_lim_le_left_lim_of_monotone hlt hα
        have h3 : left_lim α b ≤ right_lim α b := by
          have := jump_of_monotone b hα; linarith
        linarith
      · have heq : a = b := by linarith
        subst heq
        have hpos : 0 ≤ jump α a := jump_of_monotone a hα
        simp [jump] at hpos
        linarith
    · rfl
  | Ico a b =>
    simp [α_length]
    split
    · by_cases hlt : a < b
      · have h_left : left_lim α a ≤ left_lim α b := by
          have h1 : left_lim α a ≤ right_lim α a := by
            have := jump_of_monotone a hα; linarith
          have h2 : right_lim α a ≤ left_lim α b := right_lim_le_left_lim_of_monotone hlt hα
          linarith
        linarith
      · have heq : a = b := by linarith
        subst heq; linarith
    · rfl
  | Ioc a b =>
    simp [α_length]
    split
    · by_cases hlt : a < b
      · have h_right : right_lim α a ≤ right_lim α b := by
          have h1 : right_lim α a ≤ left_lim α b := right_lim_le_left_lim_of_monotone hlt hα
          have h2 : left_lim α b ≤ right_lim α b := by
            have := jump_of_monotone b hα; linarith
          linarith
        linarith
      · have heq : a = b := by linarith
        subst heq; linarith
    · rfl
  | Ioo a b =>
    simp [α_length]
    split
    · have hchain : right_lim α a ≤ left_lim α b := right_lim_le_left_lim_of_monotone (by assumption) hα
      linarith
    · rfl

/-- Analogue of Theorem 11.2.16 (a) (Laws of integration) / Exercise 11.8.3 -/
theorem PiecewiseConstantOn.RS_integ_add {f g: ℝ → ℝ} {I: BoundedInterval}
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) {α:ℝ → ℝ} (hα: Monotone α):
  RS_integ (f + g) I α = RS_integ f I α + RS_integ g I α := by
  let _ := hα
  rcases hf with ⟨P, hP⟩
  rcases hg with ⟨Q, hQ⟩
  set R := P ⊔ Q with hR
  have hfR : PiecewiseConstantWith f R :=
    PiecewiseConstantWith.mono (BoundedInterval.le_max P Q).1 hP
  have hgR : PiecewiseConstantWith g R :=
    PiecewiseConstantWith.mono (BoundedInterval.le_max P Q).2 hQ
  have hfgR : PiecewiseConstantWith (f + g) R := by
    intro J hJ
    have hfJ := hfR J hJ
    have hgJ := hgR J hJ
    rcases hfJ with ⟨c, hc⟩
    rcases hgJ with ⟨d, hd⟩
    refine ⟨c + d, λ x => ?_⟩
    simp [hc x, hd x]
  have hval (J : BoundedInterval) (hJ : J ∈ R.intervals) :
    constant_value_on (f + g) (J : Set ℝ) * α[J]ₗ
    = constant_value_on f (J : Set ℝ) * α[J]ₗ + constant_value_on g (J : Set ℝ) * α[J]ₗ := by
    have hfJ : ConstantOn f (J : Set ℝ) := hfR J hJ
    have hgJ : ConstantOn g (J : Set ℝ) := hgR J hJ
    by_cases hJ_nonempty : (J : Set ℝ).Nonempty
    · rcases hJ_nonempty with ⟨x, hx⟩
      have hfx : f x = constant_value_on f (J : Set ℝ) := hfJ.eq hx
      have hgx : g x = constant_value_on g (J : Set ℝ) := hgJ.eq hx
      have hfgJ : ConstantOn (f + g) (J : Set ℝ) := by
        rcases hfJ with ⟨c, hc⟩
        rcases hgJ with ⟨d, hd⟩
        refine ⟨c + d, λ y => ?_⟩
        simp [hc y, hd y]
      have hfgx : (f + g) x = constant_value_on (f + g) (J : Set ℝ) := hfgJ.eq hx
      calc
        constant_value_on (f + g) (J : Set ℝ) * α[J]ₗ = ((f + g) x) * α[J]ₗ := by rw [hfgx]
        _ = (f x + g x) * α[J]ₗ := rfl
        _ = f x * α[J]ₗ + g x * α[J]ₗ := by ring
        _ = constant_value_on f (J : Set ℝ) * α[J]ₗ + constant_value_on g (J : Set ℝ) * α[J]ₗ := by rw [hfx, hgx]
    · have hJ_empty : (J : Set ℝ) = ∅ := Set.not_nonempty_iff_eq_empty.mp hJ_nonempty
      have h_len : α[J]ₗ = 0 := α_length_of_empty α hJ_empty
      simp [h_len]
  calc
    RS_integ (f + g) I α = PiecewiseConstantWith.RS_integ (f + g) R α := by
      rw [PiecewiseConstantOn.RS_integ_def hfgR α]
    _ = ∑ J ∈ R.intervals, constant_value_on (f + g) (J : Set ℝ) * α[J]ₗ := rfl
    _ = ∑ J ∈ R.intervals, (constant_value_on f (J : Set ℝ) * α[J]ₗ + constant_value_on g (J : Set ℝ) * α[J]ₗ) := by
      refine Finset.sum_congr rfl (λ J hJ => ?_)
      rw [hval J hJ]
    _ = (∑ J ∈ R.intervals, constant_value_on f (J : Set ℝ) * α[J]ₗ) +
        (∑ J ∈ R.intervals, constant_value_on g (J : Set ℝ) * α[J]ₗ) := by
      simp [Finset.sum_add_distrib]
    _ = PiecewiseConstantWith.RS_integ f R α + PiecewiseConstantWith.RS_integ g R α := rfl
    _ = RS_integ f I α + RS_integ g I α := by
      rw [PiecewiseConstantOn.RS_integ_def hfR α, PiecewiseConstantOn.RS_integ_def hgR α]

/-- Analogue of Theorem 11.2.16 (b) (Laws of integration) / Exercise 11.8.3 -/
theorem PiecewiseConstantOn.RS_integ_smul {f: ℝ → ℝ} {I: BoundedInterval} (c:ℝ)
  (hf: PiecewiseConstantOn f I) {α:ℝ → ℝ} (hα: Monotone α) :
  RS_integ (c • f) I α = c * RS_integ f I α
   := by
  let _ := hα
  rcases hf with ⟨P, hP⟩
  have hcP : PiecewiseConstantWith (c • f) P := by
    intro J hJ
    rcases hP J hJ with ⟨d, hd⟩
    refine ⟨c * d, λ x => ?_⟩
    simp [hd x]
  have hval (J : BoundedInterval) (hJ : J ∈ P.intervals) :
    constant_value_on (c • f) (J : Set ℝ) * α[J]ₗ = c * (constant_value_on f (J : Set ℝ) * α[J]ₗ) := by
    have hfJ : ConstantOn f (J : Set ℝ) := hP J hJ
    by_cases hJ_nonempty : (J : Set ℝ).Nonempty
    · rcases hJ_nonempty with ⟨x, hx⟩
      have hfx : f x = constant_value_on f (J : Set ℝ) := hfJ.eq hx
      have hcfJ : ConstantOn (c • f) (J : Set ℝ) := by
        rcases hfJ with ⟨d, hd⟩
        refine ⟨c * d, λ y => ?_⟩
        simp [hd y]
      have hcfx : (c • f) x = constant_value_on (c • f) (J : Set ℝ) := hcfJ.eq hx
      calc
        constant_value_on (c • f) (J : Set ℝ) * α[J]ₗ = ((c • f) x) * α[J]ₗ := by rw [hcfx]
        _ = (c * f x) * α[J]ₗ := rfl
        _ = c * (f x * α[J]ₗ) := by ring
        _ = c * (constant_value_on f (J : Set ℝ) * α[J]ₗ) := by rw [hfx]
    · have hJ_empty : (J : Set ℝ) = ∅ := Set.not_nonempty_iff_eq_empty.mp hJ_nonempty
      have hlen : α[J]ₗ = 0 := α_length_of_empty α hJ_empty
      simp [hlen]
  calc
    RS_integ (c • f) I α = PiecewiseConstantWith.RS_integ (c • f) P α := by
      rw [PiecewiseConstantOn.RS_integ_def hcP α]
    _ = ∑ J ∈ P.intervals, constant_value_on (c • f) (J : Set ℝ) * α[J]ₗ := rfl
    _ = ∑ J ∈ P.intervals, c * (constant_value_on f (J : Set ℝ) * α[J]ₗ) := by
      refine Finset.sum_congr rfl (λ J hJ => ?_)
      rw [hval J hJ]
    _ = c * (∑ J ∈ P.intervals, constant_value_on f (J : Set ℝ) * α[J]ₗ) := by simp [Finset.mul_sum]
    _ = c * PiecewiseConstantWith.RS_integ f P α := rfl
    _ = c * RS_integ f I α := by rw [PiecewiseConstantOn.RS_integ_def hP α]

/-- Theorem 11.8.8 (c) (Laws of RS integration) / Exercise 11.8.3 -/
theorem PiecewiseConstantOn.RS_integ_sub {f g: ℝ → ℝ} {I: BoundedInterval}
  {α:ℝ → ℝ} (hα: Monotone α)
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) :
  RS_integ (f - g) I α = RS_integ f I α - RS_integ g I α := by
  have h_neg_g : PiecewiseConstantOn ((-1 : ℝ) • g) I :=
    PiecewiseConstantOn.smul (-1) hg
  have h_eq : f - g = f + ((-1 : ℝ) • g) := by
    ext x; simp [sub_eq_add_neg]
  rw [h_eq]
  rw [RS_integ_add hf h_neg_g hα, RS_integ_smul (-1) hg hα]
  ring

/-- Theorem 11.8.8 (d) (Laws of RS integration) / Exercise 11.8.3 -/
theorem PiecewiseConstantOn.RS_integ_of_nonneg {f: ℝ → ℝ} {I: BoundedInterval}
  {α:ℝ → ℝ} (hα: Monotone α)
  (h: ∀ x ∈ I, 0 ≤ f x) (hf: PiecewiseConstantOn f I) :
  0 ≤ RS_integ f I α := by
  rcases hf with ⟨P, hP⟩
  have h_nonneg_sum : 0 ≤ ∑ J ∈ P.intervals, constant_value_on f (J : Set ℝ) * α[J]ₗ := by
    refine Finset.sum_nonneg (λ J hJ => ?_)
    have hfJ : ConstantOn f (J : Set ℝ) := hP J hJ
    by_cases hJ_nonempty : (J : Set ℝ).Nonempty
    · rcases hJ_nonempty with ⟨x, hx⟩
      have hJI : (J : Set ℝ) ⊆ (I : Set ℝ) := P.contains J hJ
      have hxI : x ∈ (I : Set ℝ) := hJI hx
      have h_fx : f x = constant_value_on f (J : Set ℝ) := hfJ.eq hx
      have h_nonneg_val : 0 ≤ constant_value_on f (J : Set ℝ) := by
        rw [← h_fx]; exact h x hxI
      have h_nonneg_α : 0 ≤ α[J]ₗ := α_length_nonneg_of_monotone hα J
      nlinarith
    · have hJ_empty : (J : Set ℝ) = ∅ := Set.not_nonempty_iff_eq_empty.mp hJ_nonempty
      have hlen : α[J]ₗ = 0 := α_length_of_empty α hJ_empty
      simp [hlen]
  rw [PiecewiseConstantOn.RS_integ_def hP α, PiecewiseConstantWith.RS_integ]
  exact h_nonneg_sum

/-- Theorem 11.8.8 (e) (Laws of RS integration) / Exercise 11.8.3 -/
theorem PiecewiseConstantOn.RS_integ_mono {f g: ℝ → ℝ} {I: BoundedInterval}
  {α:ℝ → ℝ} (hα: Monotone α)
  (h: ∀ x ∈ I, f x ≤ g x) (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) :
  RS_integ f I α ≤ RS_integ g I α := by
  have h_nonneg : ∀ x ∈ I, 0 ≤ (g - f) x := by
    intro x hx; simp; linarith [h x hx]
  have h_sub : PiecewiseConstantOn (g - f) I :=
    PiecewiseConstantOn.sub hg hf
  have h_nonneg_integ : 0 ≤ RS_integ (g - f) I α :=
    RS_integ_of_nonneg hα h_nonneg h_sub
  have h_eq : RS_integ (g - f) I α = RS_integ g I α - RS_integ f I α :=
    RS_integ_sub hα hg hf
  linarith

/-- Theorem 11.8.8 (f) (Laws of RS integration) / Exercise 11.8.3 -/
theorem PiecewiseConstantOn.RS_integ_const (c: ℝ) (I: BoundedInterval) {α:ℝ → ℝ} (hα: Monotone α) :
  RS_integ (fun _ ↦ c) I α = c * α[I]ₗ := by
  let _ := hα
  have hc : ConstantOn (fun _ : ℝ ↦ c) (I : Set ℝ) := ConstantOn.of_const' c I
  have hc_bot : PiecewiseConstantWith (fun _ : ℝ ↦ c) (⊥ : Partition I) := by
    intro J hJ
    have hJ_mem : J ∈ (⊥ : Partition I).intervals := hJ
    rw [Partition.intervals_of_bot] at hJ_mem
    have hJ_eq : J = I := by simpa [Finset.mem_singleton] using hJ_mem
    subst hJ_eq; exact hc
  calc
    RS_integ (fun _ : ℝ ↦ c) I α = PiecewiseConstantWith.RS_integ (fun _ : ℝ ↦ c) (⊥ : Partition I) α := by
      rw [PiecewiseConstantOn.RS_integ_def hc_bot α]
    _ = constant_value_on (fun _ : ℝ ↦ c) (I : Set ℝ) * α[I]ₗ := by
      simp [PiecewiseConstantWith.RS_integ, Partition.intervals_of_bot]
    _ = c * α[I]ₗ := by
      by_cases hI_nonempty : (I : Set ℝ).Nonempty
      · rcases hI_nonempty with ⟨x, hx⟩
        have hval : constant_value_on (fun _ : ℝ ↦ c) (I : Set ℝ) = c := (hc.eq hx).symm
        rw [hval]
      · have hI_empty : (I : Set ℝ) = ∅ := Set.not_nonempty_iff_eq_empty.mp hI_nonempty
        have hlen : α[I]ₗ = 0 := α_length_of_empty α hI_empty
        simp [hlen]

/-- Theorem 11.8.8 (f') (Laws of RS integration) / Exercise 11.8.3 -/
theorem PiecewiseConstantOn.RS_integ_const' {f:ℝ → ℝ} {I: BoundedInterval}
  {α:ℝ → ℝ} (hα: Monotone α) (h: ConstantOn f I) :
  RS_integ f I α = (constant_value_on f I) * α[I]ₗ := by
  let _ := hα
  have hf_bot : PiecewiseConstantWith f (⊥ : Partition I) := by
    intro J hJ
    have hJ_mem : J ∈ (⊥ : Partition I).intervals := hJ
    rw [Partition.intervals_of_bot] at hJ_mem
    have hJ_eq : J = I := by simpa [Finset.mem_singleton] using hJ_mem
    subst hJ_eq; exact h
  calc
    RS_integ f I α = PiecewiseConstantWith.RS_integ f (⊥ : Partition I) α := by
      rw [PiecewiseConstantOn.RS_integ_def hf_bot α]
    _ = constant_value_on f (I : Set ℝ) * α[I]ₗ := by
      simp [PiecewiseConstantWith.RS_integ, Partition.intervals_of_bot]
    _ = (constant_value_on f I) * α[I]ₗ := rfl

open Classical in
/-- Theorem 11.8.8 (g) (Laws of RS integration) / Exercise 11.8.3 -/
theorem PiecewiseConstantOn.RS_of_extend {I J: BoundedInterval} (hIJ: I ⊆ J)
  {f: ℝ → ℝ} (h: PiecewiseConstantOn f I) {α:ℝ → ℝ} (hα: Monotone α):
  PiecewiseConstantOn (fun x ↦ if x ∈ I then f x else 0) J :=
  let _ := hα; PiecewiseConstantOn.of_extend hIJ h

open Classical in
/-- Theorem 11.8.8 (g') (Laws of RS integration) / Exercise 11.8.3 -/
theorem PiecewiseConstantOn.RS_integ_of_extend {I J: BoundedInterval} (hIJ: I ⊆ J)
  {f: ℝ → ℝ} (h: PiecewiseConstantOn f I) {α:ℝ → ℝ} (hα: Monotone α):
  RS_integ (fun x ↦ if x ∈ I then f x else 0) J α = RS_integ f I α := by
  let _ := hα
  rcases h with ⟨P, hP⟩
  set g := fun x ↦ if x ∈ I then f x else 0 with hg_def
  have hg_on_P : PiecewiseConstantWith g P := by
    intro K hK
    rcases hP K hK with ⟨c, hc⟩
    refine ⟨c, λ x => ?_⟩
    have hxI : x.1 ∈ I := (P.contains K hK) x.1 x.2
    simp [hg_def, hxI, hc x]
  by_cases hI_empty : (I : Set ℝ) = ∅
  · have hg_zero : g = (fun _ : ℝ => 0) := by
      ext x; simp [hg_def, hI_empty, BoundedInterval.mem_iff]
    rw [hg_zero]
    have hzero : PiecewiseConstantWith (fun _ : ℝ => 0) (⊥ : Partition J) := by
      intro K hK
      have hK_eq_J : K = J := by
        have hmem : K ∈ (⊥ : Partition J).intervals := hK
        simp [Partition.intervals_of_bot] at hmem
        simpa using hmem
      subst hK_eq_J; exact ConstantOn.of_const (c := 0) (by simp)
    have hf_zero : RS_integ f I α = 0 := by
      rw [PiecewiseConstantOn.RS_integ_def hP α, PiecewiseConstantWith.RS_integ]
      refine Finset.sum_eq_zero (λ K hK => ?_)
      have hK_sub_I : (K : Set ℝ) ⊆ (I : Set ℝ) := P.contains K hK
      have hK_empty : (K : Set ℝ) = ∅ :=
        Set.subset_eq_empty hK_sub_I hI_empty
      simp [hK_empty, α_length_of_empty α hK_empty]
    calc
      RS_integ (fun _ : ℝ => 0) J α = PiecewiseConstantWith.RS_integ (fun _ : ℝ => 0) (⊥ : Partition J) α := by
        rw [PiecewiseConstantOn.RS_integ_def hzero α]
      _ = constant_value_on (fun _ : ℝ => 0) (J : Set ℝ) * α[J]ₗ := by
        simp [PiecewiseConstantWith.RS_integ, Partition.intervals_of_bot]
      _ = 0 := by
        by_cases hJ_nonempty : (J : Set ℝ).Nonempty
        · rcases hJ_nonempty with ⟨x, hx⟩
          have hJ_const : ConstantOn (fun _ : ℝ => 0) (J : Set ℝ) := by
            refine ⟨0, λ x => ?_⟩; simp
          have hconst : constant_value_on (fun _ : ℝ => 0) (J : Set ℝ) = 0 := by
            have h_eq := hJ_const.eq hx
            simp at h_eq
            exact h_eq.symm
          simp [hconst]
        · have hJ_empty : (J : Set ℝ) = ∅ := Set.not_nonempty_iff_eq_empty.mp hJ_nonempty
          have hlen : α[J]ₗ = 0 := α_length_of_empty α hJ_empty
          simp [hlen]
      _ = RS_integ f I α := by rw [hf_zero]
  have h_nonempty : (I : Set ℝ).Nonempty := Set.nonempty_iff_ne_empty.mpr hI_empty
  rcases h_nonempty with ⟨x0, hx0⟩
  have hJ_props : Bornology.IsBounded (J : Set ℝ) ∧ (J : Set ℝ).OrdConnected :=
    (BoundedInterval.ordConnected_iff (J : Set ℝ)).mpr ⟨J, rfl⟩
  have hI_props : Bornology.IsBounded (I : Set ℝ) ∧ (I : Set ℝ).OrdConnected :=
    (BoundedInterval.ordConnected_iff (I : Set ℝ)).mpr ⟨I, rfl⟩
  let leftGapSet : Set ℝ := ((J : Set ℝ) ∩ {x | x ≤ I.a}) \ (I : Set ℝ)
  let rightGapSet : Set ℝ := ((J : Set ℝ) ∩ {x | I.b ≤ x}) \ (I : Set ℝ)
  have hL_set_ord : leftGapSet.OrdConnected := by
    by_cases hI_a_mem : I.a ∈ (I : Set ℝ)
    · have h_eq : leftGapSet = ((J : Set ℝ) ∩ Set.Iio I.a) := by
        ext x; constructor
        · rintro ⟨⟨hxJ, hxle⟩, hxnot⟩
          simp at hxle; refine ⟨hxJ, ?_⟩
          simp
          by_contra! h
          have hx_eq : x = I.a := le_antisymm hxle h
          subst hx_eq; exact hxnot hI_a_mem
        · rintro ⟨hxJ, hxlt⟩; simp at hxlt
          refine ⟨⟨hxJ, le_of_lt hxlt⟩, λ hxI => ?_⟩
          have hx_Icc : x ∈ (Icc I.a I.b : Set ℝ) := (BoundedInterval.subset_Icc I) x hxI
          have : I.a ≤ x := by simp at hx_Icc; exact hx_Icc.1
          linarith
      rw [h_eq]; exact hJ_props.2.inter Set.ordConnected_Iio
    · have h_eq : leftGapSet = ((J : Set ℝ) ∩ Set.Iic I.a) := by
        ext x; constructor
        · rintro ⟨⟨hxJ, hxle⟩, _⟩; simp at hxle; exact ⟨hxJ, hxle⟩
        · rintro ⟨hxJ, hxle⟩; simp at hxle
          refine ⟨⟨hxJ, hxle⟩, λ hxI => ?_⟩
          have hx_Icc : x ∈ (Icc I.a I.b : Set ℝ) := (BoundedInterval.subset_Icc I) x hxI
          have hI_a_le_x : I.a ≤ x := by simp at hx_Icc; exact hx_Icc.1
          by_cases hx_ltIa : I.a < x
          · exact not_lt.mpr hxle hx_ltIa
          · have hx_eq : x = I.a := le_antisymm hxle hI_a_le_x
            subst hx_eq; exact hI_a_mem hxI
      rw [h_eq]; exact hJ_props.2.inter Set.ordConnected_Iic
  have hR_set_ord : rightGapSet.OrdConnected := by
    by_cases hI_b_mem : I.b ∈ (I : Set ℝ)
    · have h_eq : rightGapSet = ((J : Set ℝ) ∩ Set.Ioi I.b) := by
        ext x; constructor
        · rintro ⟨⟨hxJ, hxle⟩, hxnot⟩
          simp at hxle; refine ⟨hxJ, ?_⟩
          simp
          by_contra! h
          have hx_eq : x = I.b := le_antisymm h hxle
          subst hx_eq; exact hxnot hI_b_mem
        · rintro ⟨hxJ, hxlt⟩; simp at hxlt
          refine ⟨⟨hxJ, le_of_lt hxlt⟩, λ hxI => ?_⟩
          have hx_Icc : x ∈ (Icc I.a I.b : Set ℝ) := (BoundedInterval.subset_Icc I) x hxI
          have : x ≤ I.b := by simp at hx_Icc; exact hx_Icc.2
          linarith
      rw [h_eq]; exact hJ_props.2.inter Set.ordConnected_Ioi
    · have h_eq : rightGapSet = ((J : Set ℝ) ∩ Set.Ici I.b) := by
        ext x; constructor
        · rintro ⟨⟨hxJ, hxle⟩, _⟩; simp at hxle; exact ⟨hxJ, hxle⟩
        · rintro ⟨hxJ, hxle⟩; simp at hxle
          refine ⟨⟨hxJ, hxle⟩, λ hxI => ?_⟩
          have hx_Icc : x ∈ (Icc I.a I.b : Set ℝ) := (BoundedInterval.subset_Icc I) x hxI
          have hx_le_Ib : x ≤ I.b := by simp at hx_Icc; exact hx_Icc.2
          by_cases hx_gtIb : I.b < x
          · exfalso; linarith
          · have hx_eq : x = I.b := le_antisymm hx_le_Ib hxle
            subst hx_eq; exact hI_b_mem hxI
      rw [h_eq]; exact hJ_props.2.inter Set.ordConnected_Ici
  have hL_set_bdd : Bornology.IsBounded leftGapSet :=
    hJ_props.1.subset (by intro x hx; exact hx.1.1)
  have hR_set_bdd : Bornology.IsBounded rightGapSet :=
    hJ_props.1.subset (by intro x hx; exact hx.1.1)
  rcases (BoundedInterval.ordConnected_iff leftGapSet).mp ⟨hL_set_bdd, hL_set_ord⟩ with ⟨L, hL⟩
  obtain ⟨R_b, hR⟩ := (BoundedInterval.ordConnected_iff rightGapSet).mp ⟨hR_set_bdd, hR_set_ord⟩
  set R := R_b with hRdef
  have hL_sub_J : (L : Set ℝ) ⊆ (J : Set ℝ) := by
    intro x hx; rw [← hL] at hx; exact hx.1.1
  have hR_sub_J : (R : Set ℝ) ⊆ (J : Set ℝ) := by
    intro x hx; rw [← hR] at hx; exact hx.1.1
  have hL_not_I : (L : Set ℝ) ∩ (I : Set ℝ) = ∅ := by
    apply Set.not_nonempty_iff_eq_empty.mp
    intro h; rcases h with ⟨x, hxL, hxI⟩
    rw [← hL] at hxL; exact hxL.2 hxI
  have hR_not_I : (R : Set ℝ) ∩ (I : Set ℝ) = ∅ := by
    apply Set.not_nonempty_iff_eq_empty.mp
    intro h; rcases h with ⟨x, hxR, hxI⟩
    rw [← hR] at hxR; exact hxR.2 hxI
  have hLR_disjoint : (L : Set ℝ) ∩ (R : Set ℝ) = ∅ := by
    apply Set.not_nonempty_iff_eq_empty.mp
    intro h; rcases h with ⟨x, hxL, hxR⟩
    rw [← hL] at hxL; rw [← hR] at hxR
    have hx_le_Ia : x ≤ I.a := hxL.1.2
    have hx_Ib_le : I.b ≤ x := hxR.1.2
    have hI_a_le_Ib : I.a ≤ I.b := by
      have : x0 ∈ (Icc I.a I.b : Set ℝ) := (BoundedInterval.subset_Icc I) x0 hx0
      simp at this; exact le_trans this.1 this.2
    have hI_b_le_Ia : I.b ≤ I.a := le_trans hx_Ib_le hx_le_Ia
    have h_eq : I.a = I.b := le_antisymm hI_a_le_Ib hI_b_le_Ia
    have hx_eq : x = I.a := by nlinarith
    subst hx_eq
    have hI_a_mem : I.a ∈ (I : Set ℝ) := by
      match I with
      | Icc a b =>
        have h_ab : a = b := by simpa using h_eq
        subst h_ab; simp
      | Ioo a b =>
        have h_ab : a = b := by simpa using h_eq
        subst h_ab; exfalso; exact hI_empty (by simp)
      | Ioc a b =>
        have h_ab : a = b := by simpa using h_eq
        subst h_ab; exfalso; exact hI_empty (by simp)
      | Ico a b =>
        have h_ab : a = b := by simpa using h_eq
        subst h_ab; exfalso; exact hI_empty (by simp)
    exact hxL.2 hI_a_mem
  let intervals_J : Finset BoundedInterval := P.intervals ∪ {L, R}
  let P_J : Partition J := {
    intervals := intervals_J
    exists_unique := by
      intro x hx
      by_cases hxI : x ∈ (I : Set ℝ)
      · rcases P.exists_unique x hxI with ⟨K, ⟨hKmem, hxK⟩, huniq⟩
        refine ⟨K, ⟨Finset.mem_union_left _ hKmem, hxK⟩, λ K' hK' => ?_⟩
        rcases hK' with ⟨hK'mem, hxK'⟩
        rcases Finset.mem_union.mp hK'mem with (hK'P | hK'LR)
        · exact huniq K' ⟨hK'P, hxK'⟩
        · rcases Finset.mem_insert.mp hK'LR with (hK'L | hK'R)
          · subst hK'L; exfalso; exact Set.not_nonempty_iff_eq_empty.mpr hL_not_I ⟨x, hxK', hxI⟩
          · have hK'_eq_R : K' = R := Finset.mem_singleton.mp hK'R
            subst hK'_eq_R; exfalso; exact Set.not_nonempty_iff_eq_empty.mpr hR_not_I ⟨x, hxK', hxI⟩
      · by_cases hxL : x ∈ (L : Set ℝ)
        · refine ⟨L, ⟨Finset.mem_union_right _ (by simp), hxL⟩, λ K' hK' => ?_⟩
          rcases hK' with ⟨hK'mem, hxK'⟩
          rcases Finset.mem_union.mp hK'mem with (hK'P | hK'LR)
          · have hK'_sub_I : (K' : Set ℝ) ⊆ (I : Set ℝ) := P.contains K' hK'P
            exact (hxI (hK'_sub_I hxK')).elim
          · rcases Finset.mem_insert.mp hK'LR with (hK'L | hK'R)
            · subst hK'L; rfl
            · have hK'_eq_R : K' = R := Finset.mem_singleton.mp hK'R
              subst hK'_eq_R; exfalso; exact Set.not_nonempty_iff_eq_empty.mpr hLR_disjoint ⟨x, hxL, hxK'⟩
        · by_cases hxR : x ∈ (R : Set ℝ)
          · refine ⟨R, ⟨Finset.mem_union_right _ (by simp [Finset.mem_insert]), hxR⟩, λ K' hK' => ?_⟩
            rcases hK' with ⟨hK'mem, hxK'⟩
            rcases Finset.mem_union.mp hK'mem with (hK'P | hK'LR)
            · have hK'_sub_I : (K' : Set ℝ) ⊆ (I : Set ℝ) := P.contains K' hK'P
              exact (hxI (hK'_sub_I hxK')).elim
            · rcases Finset.mem_insert.mp hK'LR with (hK'L | hK'R)
              · subst hK'L; exfalso; exact Set.not_nonempty_iff_eq_empty.mpr hLR_disjoint ⟨x, hxK', hxR⟩
              · have hK'_eq_R : K' = R := Finset.mem_singleton.mp hK'R; subst hK'_eq_R; rfl
          · have hxI' : x ∈ (I : Set ℝ) := by
              have hx_gtIa : I.a < x := by
                by_contra! h; rw [← hL] at hxL; apply hxL; refine ⟨⟨hx, h⟩, hxI⟩
              have hx_ltIb : x < I.b := by
                by_contra! h; rw [← hR] at hxR; apply hxR; refine ⟨⟨hx, h⟩, hxI⟩
              have hxI' : x ∈ (I : Set ℝ) :=
                (BoundedInterval.Ioo_subset I) x (by
                  simpa using Set.mem_Ioo.mpr ⟨hx_gtIa, hx_ltIb⟩)
              exact hxI'
            exact (hxI hxI').elim
    contains := by
      intro K hK
      rcases Finset.mem_union.mp hK with (hKP | hKLR)
      · exact Set.Subset.trans (P.contains K hKP) hIJ
      · rcases Finset.mem_insert.mp hKLR with (hKL | hKR)
        · subst hKL; exact hL_sub_J
        · have hK_eq_R : K = R := Finset.mem_singleton.mp hKR
          subst hK_eq_R; exact hR_sub_J
  }
  have hg_on_P_J : PiecewiseConstantWith g P_J := by
    intro K' hK'
    rcases Finset.mem_union.mp hK' with (hKP | hKLR)
    · exact hg_on_P K' hKP
    · rcases Finset.mem_insert.mp hKLR with (hKL | hKR)
      · rw [hKL]
        refine ⟨0, λ x => ?_⟩
        have hxL_val : x.val ∈ leftGapSet := by
          simp [hL]
        have hx_not_I : x.val ∉ (I : Set ℝ) := hxL_val.2
        dsimp [g]
        split_ifs with hxI
        · exfalso; exact hx_not_I hxI
        · rfl
      · have hK'_eq_R : K' = R := Finset.mem_singleton.mp hKR
        rw [hK'_eq_R]
        refine ⟨0, λ x => ?_⟩
        have hxR_val : x.val ∈ rightGapSet := by
          simp [hR]
        have hx_not_I : x.val ∉ (I : Set ℝ) := hxR_val.2
        dsimp [g]
        split_ifs with hxI
        · exfalso; exact hx_not_I hxI
        · rfl
  have h1 : RS_integ g J α = PiecewiseConstantWith.RS_integ g P_J α := by
    rw [PiecewiseConstantOn.RS_integ_def hg_on_P_J α]

  have h_T_zero (K : BoundedInterval) (hK : K ∈ ({L, R} : Finset BoundedInterval)) :
    constant_value_on g (K : Set ℝ) * α[K]ₗ = 0 := by
    rcases Finset.mem_insert.mp hK with (hKL | hKR)
    · subst K
      rcases Set.eq_empty_or_nonempty (L : Set ℝ) with (hL_empty | hL_nonempty)
      · rw [hL_empty, α_length_of_empty α hL_empty]; simp
      · rcases hL_nonempty with ⟨x, hx⟩
        have h_zero_on_L : ∀ x ∈ (L : Set ℝ), g x = 0 := by
          intro x' hx'
          have hx'_leftGap : x' ∈ leftGapSet := by
            rw [hL]; exact hx'
          have hx'_not_I : x' ∉ (I : Set ℝ) := hx'_leftGap.2
          dsimp [g]; simp [BoundedInterval.mem_iff, hx'_not_I]
        have hgL_const : ConstantOn g (L : Set ℝ) := ⟨0, λ y => h_zero_on_L y.1 y.2⟩
        have h_val : constant_value_on g (L : Set ℝ) = 0 := by
          calc
            constant_value_on g (L : Set ℝ) = g x := (hgL_const.eq hx).symm
            _ = 0 := h_zero_on_L x hx
        simp [h_val]
    · have hK_eq_R : K = R := Finset.mem_singleton.mp hKR
      subst hK_eq_R
      rcases Set.eq_empty_or_nonempty (R : Set ℝ) with (hR_empty | hR_nonempty)
      · have hlen : α[R]ₗ = 0 := α_length_of_empty α hR_empty
        rw [hR_empty, hlen, mul_zero]
      · rcases hR_nonempty with ⟨x, hx⟩
        have h_zero_on_R : ∀ x ∈ (R : Set ℝ), g x = 0 := by
          intro x' hx'
          have hx'_rightGap : x' ∈ rightGapSet := by
            rw [hR]; exact hx'
          have hx'_not_I : x' ∉ (I : Set ℝ) := hx'_rightGap.2
          have hx'I_not : x' ∉ (I : Set ℝ) := hx'_not_I
          dsimp [g]
          by_cases hx'I : x' ∈ I
          · exfalso; exact hx'I_not hx'I
          · simp [hx'I]
        have hgR_const : ConstantOn g (R : Set ℝ) := ⟨0, λ y => h_zero_on_R y.1 y.2⟩
        have h_val : constant_value_on g (R : Set ℝ) = 0 := by
          calc
            constant_value_on g (R : Set ℝ) = g x := (hgR_const.eq hx).symm
            _ = 0 := h_zero_on_R x hx
        rw [h_val, zero_mul]

  have h2 : PiecewiseConstantWith.RS_integ g P_J α = (∑ K ∈ P.intervals, constant_value_on g (K : Set ℝ) * α[K]ₗ) +
      (∑ K ∈ {L, R}, constant_value_on g (K : Set ℝ) * α[K]ₗ) := by
    have : PiecewiseConstantWith.RS_integ g P_J α = ∑ K ∈ (P.intervals ∪ {L,R}), constant_value_on g (K : Set ℝ) * α[K]ₗ := by
      dsimp [PiecewiseConstantWith.RS_integ, P_J, intervals_J]
    rw [this]
    have h_sdiff_sum : ∑ K ∈ ({L, R} \ P.intervals), constant_value_on g (K : Set ℝ) * α[K]ₗ =
        ∑ K ∈ {L, R}, constant_value_on g (K : Set ℝ) * α[K]ₗ := by
      refine Finset.sum_subset (λ x hx => ?_) (λ x hx hx_not => ?_)
      · rcases Finset.mem_sdiff.mp hx with ⟨hxLR, _⟩; exact hxLR
      · exact h_T_zero x hx
    have h_sub : P.intervals ⊆ P.intervals ∪ {L, R} := by
      intro x hx; exact Finset.mem_union_left {L, R} hx
    have h_sdiff_eq : (P.intervals ∪ {L, R}) \ P.intervals = ({L, R} : Finset BoundedInterval) \ P.intervals := by
      apply Finset.Subset.antisymm
      · intro x hx; rcases Finset.mem_sdiff.mp hx with ⟨hx_union, hx_not⟩
        refine Finset.mem_sdiff.mpr ⟨?_, hx_not⟩
        rcases Finset.mem_union.mp hx_union with (hx_P | hx_LR)
        · exfalso; exact hx_not hx_P
        · exact hx_LR
      · intro x hx; rcases Finset.mem_sdiff.mp hx with ⟨hx_LR, hx_not⟩
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ hx_LR, hx_not⟩
    have h_temp : (∑ K ∈ ((P.intervals ∪ {L, R}) \ P.intervals), constant_value_on g (K : Set ℝ) * α[K]ₗ) +
        (∑ K ∈ P.intervals, constant_value_on g (K : Set ℝ) * α[K]ₗ) =
        ∑ K ∈ (P.intervals ∪ {L, R}), (constant_value_on g (K : Set ℝ) * α[K]ₗ) :=
      Finset.sum_sdiff h_sub
    rw [h_sdiff_eq] at h_temp
    have h_goal : ∑ K ∈ (P.intervals ∪ {L,R}), constant_value_on g (K : Set ℝ) * α[K]ₗ =
        (∑ K ∈ P.intervals, constant_value_on g (K : Set ℝ) * α[K]ₗ) +
        (∑ K ∈ {L,R}, constant_value_on g (K : Set ℝ) * α[K]ₗ) := by
      calc
        ∑ K ∈ (P.intervals ∪ {L,R}), constant_value_on g (K : Set ℝ) * α[K]ₗ
            = (∑ K ∈ ({L,R} \ P.intervals), constant_value_on g (K : Set ℝ) * α[K]ₗ) +
              (∑ K ∈ P.intervals, constant_value_on g (K : Set ℝ) * α[K]ₗ) := by
          rw [← h_temp, add_comm]
        _ = (∑ K ∈ P.intervals, constant_value_on g (K : Set ℝ) * α[K]ₗ) +
            (∑ K ∈ ({L,R} \ P.intervals), constant_value_on g (K : Set ℝ) * α[K]ₗ) := by rw [add_comm]
        _ = (∑ K ∈ P.intervals, constant_value_on g (K : Set ℝ) * α[K]ₗ) +
            (∑ K ∈ {L,R}, constant_value_on g (K : Set ℝ) * α[K]ₗ) := by rw [h_sdiff_sum]
    exact h_goal

  have h3 : (∑ K ∈ P.intervals, constant_value_on g (K : Set ℝ) * α[K]ₗ) + (∑ K ∈ {L, R}, constant_value_on g (K : Set ℝ) * α[K]ₗ) =
      (∑ K ∈ P.intervals, constant_value_on f (K : Set ℝ) * α[K]ₗ) + 0 := by
    congr 1
    · refine Finset.sum_congr rfl (λ K hK => ?_)
      have hK_sub_I : (K : Set ℝ) ⊆ (I : Set ℝ) := P.contains K hK
      rcases Set.eq_empty_or_nonempty (K : Set ℝ) with (h_empty | h_nonempty)
      · simp [h_empty, α_length_of_empty α h_empty]
      · rcases h_nonempty with ⟨x, hx⟩
        have hxI : x ∈ (I : Set ℝ) := hK_sub_I hx
        have hgK : ConstantOn g (K : Set ℝ) := hg_on_P K hK
        have hfK : ConstantOn f (K : Set ℝ) := hP K hK
        have hgx : g x = f x := by
          dsimp [g]; simp [BoundedInterval.mem_iff, hxI]
        have hg_val : constant_value_on g (K : Set ℝ) = g x := (hgK.eq hx).symm
        have hf_val : constant_value_on f (K : Set ℝ) = f x := (hfK.eq hx).symm
        simp [hg_val, hf_val, hgx]
    · apply Finset.sum_eq_zero; intro K hK
      rcases Finset.mem_insert.mp hK with (hKL | hKR)
      · subst K; exact h_T_zero L (by simp)
      · have hK_eq_R : K = R := Finset.mem_singleton.mp hKR
        subst hK_eq_R; exact h_T_zero R (by simp)

  have h4 : (∑ K ∈ P.intervals, constant_value_on f (K : Set ℝ) * α[K]ₗ) + 0 = PiecewiseConstantWith.RS_integ f P α := by
    simp [PiecewiseConstantWith.RS_integ]

  have h5 : PiecewiseConstantWith.RS_integ f P α = RS_integ f I α := by
    rw [PiecewiseConstantOn.RS_integ_def hP α]

  calc
    RS_integ g J α = PiecewiseConstantWith.RS_integ g P_J α := h1
    _ = (∑ K ∈ P.intervals, constant_value_on g (K : Set ℝ) * α[K]ₗ) + (∑ K ∈ {L, R}, constant_value_on g (K : Set ℝ) * α[K]ₗ) := h2
    _ = (∑ K ∈ P.intervals, constant_value_on f (K : Set ℝ) * α[K]ₗ) + 0 := h3
    _ = PiecewiseConstantWith.RS_integ f P α := h4
    _ = RS_integ f I α := h5

open Classical in
/-- Theorem 11.8.8 (h) (Laws of RS integration) / Exercise 11.8.8 -/
theorem PiecewiseConstantOn.RS_integ_of_join {I J K: BoundedInterval} (hIJK: K.joins' I J)
  {f: ℝ → ℝ} (h: PiecewiseConstantOn f K) {α:ℝ → ℝ} (hα: Monotone α):
  RS_integ f K α = RS_integ f I α + RS_integ f J α := by
  let _ := hα
  rcases (PiecewiseConstantOn.of_join hIJK.1 f).mp h with ⟨hI, hJ⟩
  rcases hI with ⟨P_I, hP_I⟩
  rcases hJ with ⟨P_J, hP_J⟩
  have hP_join : PiecewiseConstantWith f (P_I.join P_J hIJK.1) := by
    intro L hL
    have hL_int : L ∈ (P_I.join P_J hIJK.1).intervals := hL
    have hL' : L ∈ (P_I.intervals ∪ P_J.intervals) := by
      simpa [Partition.intervals_of_join] using hL_int
    rcases Finset.mem_union.mp hL' with (hL_I | hL_J)
    · exact hP_I L hL_I
    · exact hP_J L hL_J
  let T : BoundedInterval → ℝ := λ L => constant_value_on f (L : Set ℝ) * α[L]ₗ
  have hzero_inter : ∀ L ∈ P_I.intervals ∩ P_J.intervals, T L = 0 := by
    intro L hL
    rcases Finset.mem_inter.mp hL with ⟨hL_I, hL_J⟩
    have hL_sub_I : (L : Set ℝ) ⊆ (I : Set ℝ) := by
      rw [← BoundedInterval.subset_iff]; exact P_I.contains L hL_I
    have hL_sub_J : (L : Set ℝ) ⊆ (J : Set ℝ) := by
      rw [← BoundedInterval.subset_iff]; exact P_J.contains L hL_J
    have hL_empty : (L : Set ℝ) = ∅ := by
      by_contra! h_ne
      have h_nonempty : (L : Set ℝ).Nonempty := by
        rcases h_ne with ⟨x, hx⟩; exact ⟨x, hx⟩
      rcases h_nonempty with ⟨x, hx⟩
      have hxI : x ∈ (I : Set ℝ) := hL_sub_I hx
      have hxJ : x ∈ (J : Set ℝ) := hL_sub_J hx
      have h_disjoint : (I : Set ℝ) ∩ (J : Set ℝ) = ∅ := hIJK.1.1
      exact Set.not_nonempty_iff_eq_empty.mpr h_disjoint ⟨x, hxI, hxJ⟩
    simp [T, α_length_of_empty α hL_empty]
  have h_disjoint : Disjoint P_I.intervals (P_J.intervals \ P_I.intervals) :=
    Finset.disjoint_sdiff (s := P_I.intervals) (t := P_J.intervals)
  have h_union_eq : P_I.intervals ∪ P_J.intervals = P_I.intervals ∪ (P_J.intervals \ P_I.intervals) := by
    ext x; simp
  have h_sub : (P_I.intervals ∩ P_J.intervals) ⊆ P_J.intervals :=
    λ x hx => (Finset.mem_inter.mp hx).2
  have h_sdiff_eq : P_J.intervals \ P_I.intervals = P_J.intervals \ (P_I.intervals ∩ P_J.intervals) := by
    ext x; simp
  have hA : ∑ L ∈ (P_J.intervals \ (P_I.intervals ∩ P_J.intervals)), T L = (∑ L ∈ P_J.intervals, T L) - (∑ L ∈ (P_I.intervals ∩ P_J.intervals), T L) := by
    have h := Finset.sum_sdiff (f := T) h_sub
    apply eq_sub_of_add_eq
    simpa [add_comm] using h
  have h_sdiff_sum : (∑ L ∈ (P_J.intervals \ P_I.intervals), T L : ℝ) = (∑ L ∈ P_J.intervals, T L) - (∑ L ∈ (P_I.intervals ∩ P_J.intervals), T L) := by
    calc
      ∑ L ∈ (P_J.intervals \ P_I.intervals), T L
          = ∑ L ∈ (P_J.intervals \ (P_I.intervals ∩ P_J.intervals)), T L := by rw [h_sdiff_eq]
      _ = (∑ L ∈ P_J.intervals, T L) - (∑ L ∈ (P_I.intervals ∩ P_J.intervals), T L) := hA
  have h_union_sum : (∑ L ∈ (P_I.intervals ∪ P_J.intervals), T L) = (∑ L ∈ P_I.intervals, T L) + (∑ L ∈ P_J.intervals, T L) := by
    calc
      (∑ L ∈ (P_I.intervals ∪ P_J.intervals), T L)
          = (∑ L ∈ (P_I.intervals ∪ (P_J.intervals \ P_I.intervals)), T L) := by rw [h_union_eq]
      _ = (∑ L ∈ P_I.intervals, T L) + (∑ L ∈ (P_J.intervals \ P_I.intervals), T L) := by
        rw [Finset.sum_union h_disjoint]
      _ = (∑ L ∈ P_I.intervals, T L) + (∑ L ∈ P_J.intervals, T L - ∑ L ∈ (P_I.intervals ∩ P_J.intervals), T L) := by rw [h_sdiff_sum]
      _ = (∑ L ∈ P_I.intervals, T L) + (∑ L ∈ P_J.intervals, T L - 0) := by
        have h_inter_sum : ∑ L ∈ (P_I.intervals ∩ P_J.intervals), T L = 0 := by
          apply Finset.sum_eq_zero; intro L hL; exact hzero_inter L hL
        rw [h_inter_sum]
      _ = (∑ L ∈ P_I.intervals, T L) + (∑ L ∈ P_J.intervals, T L) := by ring
  calc
    RS_integ f K α = PiecewiseConstantWith.RS_integ f (P_I.join P_J hIJK.1) α := by
      rw [PiecewiseConstantOn.RS_integ_def hP_join α]
    _ = ∑ L ∈ (P_I.join P_J hIJK.1).intervals, constant_value_on f (L : Set ℝ) * α[L]ₗ := rfl
    _ = ∑ L ∈ (P_I.intervals ∪ P_J.intervals), constant_value_on f (L : Set ℝ) * α[L]ₗ := by
      simp
    _ = (∑ L ∈ P_I.intervals, constant_value_on f (L : Set ℝ) * α[L]ₗ) +
        (∑ L ∈ P_J.intervals, constant_value_on f (L : Set ℝ) * α[L]ₗ) := h_union_sum
    _ = PiecewiseConstantWith.RS_integ f P_I α + PiecewiseConstantWith.RS_integ f P_J α := rfl
    _ = RS_integ f I α + RS_integ f J α := by
      rw [PiecewiseConstantOn.RS_integ_def hP_I α, PiecewiseConstantOn.RS_integ_def hP_J α]

/-- Analogue of Definition 11.3.2 (Upper and lower Riemann integrals ). -/
noncomputable abbrev upper_RS_integral (f:ℝ → ℝ) (I: BoundedInterval) (α: ℝ → ℝ): ℝ :=
  sInf ((PiecewiseConstantOn.RS_integ · I α) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I})

noncomputable abbrev lower_RS_integral (f:ℝ → ℝ) (I: BoundedInterval) (α: ℝ → ℝ): ℝ :=
  sSup ((PiecewiseConstantOn.RS_integ · I α) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I})

lemma RS_integral_bound_upper_of_bounded {f:ℝ → ℝ} {M:ℝ} {I: BoundedInterval}
  (h: ∀ x ∈ (I:Set ℝ), |f x| ≤ M) {α:ℝ → ℝ} (hα:Monotone α)
  : M * α[I]ₗ ∈ (PiecewiseConstantOn.RS_integ · I α) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I} := by
  simp; refine ⟨ fun _ ↦ M, ⟨ ⟨ ?_, ?_ ⟩, PiecewiseConstantOn.RS_integ_const M I hα ⟩ ⟩
  . grind [abs_le']
  exact (ConstantOn.of_const (c := M) (by simp)).piecewiseConstantOn


lemma RS_integral_bound_lower_of_bounded {f:ℝ → ℝ} {M:ℝ} {I: BoundedInterval} (h: ∀ x ∈ (I:Set ℝ), |f x| ≤ M) {α:ℝ → ℝ} (hα:Monotone α)
  : -M * α[I]ₗ ∈ (PiecewiseConstantOn.RS_integ · I α) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I} := by
  simp; refine ⟨ fun _ ↦ -M, ⟨ ⟨ ?_, ?_ ⟩, by convert PiecewiseConstantOn.RS_integ_const _ _ hα using 1; simp ⟩ ⟩
  . grind [abs_le']
  exact (ConstantOn.of_const (c := -M) (by simp)).piecewiseConstantOn


lemma RS_integral_bound_upper_nonempty {f:ℝ → ℝ} {I: BoundedInterval} (h: BddOn f I)
  {α:ℝ → ℝ} (hα: Monotone α) :
  ((PiecewiseConstantOn.RS_integ · I α) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I}).Nonempty := by
  choose M h using h; exact Set.nonempty_of_mem (RS_integral_bound_upper_of_bounded h hα)

lemma RS_integral_bound_lower_nonempty {f:ℝ → ℝ} {I: BoundedInterval} (h: BddOn f I)
  {α:ℝ → ℝ} (hα: Monotone α) :
  ((PiecewiseConstantOn.RS_integ · I α) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I}).Nonempty := by
  choose M h using h; exact Set.nonempty_of_mem (RS_integral_bound_lower_of_bounded h hα)

lemma RS_integral_bound_lower_le_upper {f:ℝ → ℝ} {I: BoundedInterval} {a b:ℝ}
  {α:ℝ → ℝ} (hα: Monotone α)
  (ha: a ∈ (PiecewiseConstantOn.RS_integ · I α) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I})
  (hb: b ∈ (PiecewiseConstantOn.RS_integ · I α) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I})
  : b ≤ a:= by
    have ⟨ g, ⟨ ⟨ hmaj, hgp⟩, hgi ⟩ ⟩ := ha
    have ⟨ h, ⟨ ⟨ hmin, hhp⟩, hhi ⟩ ⟩ := hb
    rw [←hgi, ←hhi]; apply hhp.RS_integ_mono hα _ hgp; intro _ hx; linarith [hmin _ hx, hmaj _ hx]

lemma RS_integral_bound_below {f:ℝ → ℝ} {I: BoundedInterval} (h: BddOn f I)
  {α:ℝ → ℝ} (hα: Monotone α) :
  BddBelow ((PiecewiseConstantOn.RS_integ · I α) ''
    {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I}) := by
    rw [bddBelow_def]; use (RS_integral_bound_lower_nonempty h hα).some
    intro a ha; exact RS_integral_bound_lower_le_upper hα ha (RS_integral_bound_lower_nonempty h hα).some_mem

lemma RS_integral_bound_above {f:ℝ → ℝ} {I: BoundedInterval} (h: BddOn f I)
  {α:ℝ → ℝ} (hα: Monotone α):
  BddAbove ((PiecewiseConstantOn.RS_integ · I α) ''
    {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I}) := by
    rw [bddAbove_def]; use (RS_integral_bound_upper_nonempty h hα).some
    intro b hb; exact RS_integral_bound_lower_le_upper hα (RS_integral_bound_upper_nonempty h hα).some_mem hb

lemma le_lower_RS_integral {f:ℝ → ℝ} {I: BoundedInterval} {M:ℝ} (h: ∀ x ∈ (I:Set ℝ), |f x| ≤ M)
  {α:ℝ → ℝ} (hα: Monotone α) :
  -M * α[I]ₗ ≤ lower_RS_integral f I α :=
  le_csSup (RS_integral_bound_above (BddOn.of_bounded h) hα) (RS_integral_bound_lower_of_bounded h hα)

lemma lower_RS_integral_le_upper {f:ℝ → ℝ} {I: BoundedInterval} (h: BddOn f I)
  {α:ℝ → ℝ} (hα: Monotone α) :
  lower_RS_integral f I α ≤ upper_RS_integral f I α := by
  apply csSup_le (RS_integral_bound_lower_nonempty h hα)
  intros
  apply le_csInf (RS_integral_bound_upper_nonempty h hα)
  intros; solve_by_elim [RS_integral_bound_lower_le_upper]

lemma RS_upper_integral_le {f:ℝ → ℝ} {I: BoundedInterval} {M:ℝ} (h: ∀ x ∈ (I:Set ℝ), |f x| ≤ M)
  {α:ℝ → ℝ} (hα: Monotone α) :
  upper_RS_integral f I α ≤ M * α[I]ₗ :=
  csInf_le (RS_integral_bound_below (.of_bounded h) hα) (RS_integral_bound_upper_of_bounded h hα)

lemma upper_RS_integral_le_integ {f g:ℝ → ℝ} {I: BoundedInterval} (hf: BddOn f I)
  (hfg: MajorizesOn g f I) (hg: PiecewiseConstantOn g I)
  {α:ℝ → ℝ} (hα: Monotone α) :
  upper_RS_integral f I α ≤ PiecewiseConstantOn.RS_integ g I α :=
  csInf_le (RS_integral_bound_below hf hα) ⟨ g, by simpa [hg] ⟩

lemma integ_le_lower_RS_integral {f h:ℝ → ℝ} {I: BoundedInterval} (hf: BddOn f I)
  (hfh: MinorizesOn h f I) (hg: PiecewiseConstantOn h I)
  {α:ℝ → ℝ} (hα: Monotone α) :
  PiecewiseConstantOn.RS_integ h I α ≤ lower_RS_integral f I α :=
  le_csSup (RS_integral_bound_above hf hα) ⟨ h, by simpa [hg] ⟩

lemma lt_of_gt_upper_RS_integral {f:ℝ → ℝ} {I: BoundedInterval} (hf: BddOn f I)
  {α: ℝ → ℝ} (hα: Monotone α) {X:ℝ} (hX: upper_RS_integral f I α < X ) :
  ∃ g, MajorizesOn g f I ∧ PiecewiseConstantOn g I ∧ PiecewiseConstantOn.RS_integ g I α < X := by
  have ⟨ Y, hY, hYX ⟩ := exists_lt_of_csInf_lt (RS_integral_bound_upper_nonempty hf hα) hX
  simp at hY; have ⟨ g, ⟨ hmaj, hgp ⟩, hgi ⟩ := hY; exact ⟨ g, hmaj, hgp, by rwa [hgi] ⟩

lemma gt_of_lt_lower_RS_integral {f:ℝ → ℝ} {I: BoundedInterval} (hf: BddOn f I)
  {α:ℝ → ℝ} (hα: Monotone α) {X:ℝ} (hX: X < lower_RS_integral f I α) :
  ∃ h, MinorizesOn h f I ∧ PiecewiseConstantOn h I ∧ X < PiecewiseConstantOn.RS_integ h I α := by
  have ⟨ Y, hY, hYX ⟩ := exists_lt_of_lt_csSup (RS_integral_bound_lower_nonempty hf hα) hX
  simp at hY; have ⟨ h, ⟨ hmin, hhp ⟩, hhi ⟩ := hY; exact ⟨ h, hmin, hhp, by rwa [hhi] ⟩

/-- Analogue of Definition 11.3.4 -/
noncomputable abbrev RS_integ (f:ℝ → ℝ) (I: BoundedInterval) (α:ℝ → ℝ) : ℝ := upper_RS_integral f I α

noncomputable abbrev RS_IntegrableOn (f:ℝ → ℝ) (I: BoundedInterval) (α: ℝ → ℝ) : Prop :=
  BddOn f I ∧ lower_RS_integral f I α = upper_RS_integral f I α

/-- Analogue of various components of Lemma 11.3.3 -/
theorem upper_RS_integral_eq_upper_integral (f:ℝ → ℝ) (I: BoundedInterval) :
  upper_RS_integral f I (fun x ↦ x) = upper_integral f I := by
  simp [upper_RS_integral, upper_integral, PiecewiseConstantOn.RS_integ, PiecewiseConstantOn.integ,
    PiecewiseConstantWith.RS_integ, PiecewiseConstantWith.integ, α_len_of_id]

theorem lower_RS_integral_eq_lower_integral (f:ℝ → ℝ) (I: BoundedInterval) :
  lower_RS_integral f I (fun x ↦ x) = lower_integral f I := by
  simp [lower_RS_integral, lower_integral, PiecewiseConstantOn.RS_integ, PiecewiseConstantOn.integ,
    PiecewiseConstantWith.RS_integ, PiecewiseConstantWith.integ, α_len_of_id]

theorem RS_integ_eq_integ (f:ℝ → ℝ) (I: BoundedInterval) :
  RS_integ f I (fun x ↦ x) = integ f I := by
  simp [RS_integ, integ, upper_RS_integral_eq_upper_integral]

theorem RS_IntegrableOn_iff_IntegrableOn (f:ℝ → ℝ) (I: BoundedInterval) :
  RS_IntegrableOn f I (fun x ↦ x) ↔ IntegrableOn f I := by
  simp [RS_IntegrableOn, IntegrableOn, lower_RS_integral_eq_lower_integral,
    upper_RS_integral_eq_upper_integral]

/-- Exercise 11.8.4 -/
theorem RS_integ_of_uniform_cts {I: BoundedInterval} {f:ℝ → ℝ} (hf: UniformContinuousOn f I)
  {α:ℝ → ℝ} (hα: Monotone α):
  RS_IntegrableOn f I α := by
  -- This proof is written to follow the structure of the original text.
  have hfbound : BddOn f I := by
    rw [BddOn.iff']; exact hf.of_bounded subset_rfl (Bornology.IsBounded.of_boundedInterval I)
  have hlower_le_upper : lower_RS_integral f I α ≤ upper_RS_integral f I α :=
    lower_RS_integral_le_upper hfbound hα
  refine ⟨hfbound, ?_⟩
  by_cases hzero : α[I]ₗ = 0
  · rcases hfbound with ⟨M, hM⟩
    have hupper : upper_RS_integral f I α ≤ 0 := by
      calc
        upper_RS_integral f I α ≤ M * α[I]ₗ := RS_upper_integral_le hM hα
        _ = M * 0 := by rw [hzero]
        _ = 0 := by ring
    have hlower : 0 ≤ lower_RS_integral f I α := by
      calc
        0 = -M * 0 := by ring
        _ = -M * α[I]ₗ := by rw [hzero]
        _ ≤ lower_RS_integral f I α := le_lower_RS_integral hM hα
    linarith
  · have hpos : 0 < α[I]ₗ := by
      have h_nonneg : 0 ≤ α[I]ₗ := α_length_nonneg_of_monotone hα I
      exact lt_of_le_of_ne h_nonneg (Ne.symm hzero)
    by_cases hsing : |I|ₗ = 0
    · have hsub : Subsingleton (I : Set ℝ) :=
        (BoundedInterval.length_of_subsingleton.mpr hsing)
      haveI : Subsingleton (I : Set ℝ) := hsub
      have h_const : ConstantOn f (I : Set ℝ) := ConstantOn.of_subsingleton
      have h_pc : PiecewiseConstantOn f I := h_const.piecewiseConstantOn
      have h_maj : MajorizesOn f f I := λ x hx => le_rfl
      have h_min : MinorizesOn f f I := λ x hx => le_rfl
      have h_upper_le_RS : upper_RS_integral f I α ≤ PiecewiseConstantOn.RS_integ f I α :=
        upper_RS_integral_le_integ hfbound h_maj h_pc hα
      have h_RS_le_lower : PiecewiseConstantOn.RS_integ f I α ≤ lower_RS_integral f I α :=
        integ_le_lower_RS_integral hfbound h_min h_pc hα
      have h_eq : lower_RS_integral f I α = upper_RS_integral f I α := by
        apply le_antisymm hlower_le_upper
        calc
          upper_RS_integral f I α ≤ PiecewiseConstantOn.RS_integ f I α := h_upper_le_RS
          _ ≤ lower_RS_integral f I α := h_RS_le_lower
      exact h_eq
    · simp [length] at hsing
      set a := I.a
      set b := I.b
      have hsing' : 0 < b - a := by linarith
      have (ε : ℝ) (hε : ε > 0) : upper_RS_integral f I α - lower_RS_integral f I α ≤ ε * α[I]ₗ := by
        rw [UniformContinuousOn.iff] at hf
        choose δ hδ hf_unif using hf ε hε
        simp [Real.Close, Real.dist_eq] at hf_unif
        choose N hN using exists_nat_gt ((b - a) / δ)
        have hNpos : 0 < N := by
          have : 0 < (b - a) / δ := by positivity
          rify; order
        have hN' : (b - a) / N < δ := by rwa [div_lt_comm₀] <;> positivity
        have hpart : ∃ P : Partition I, P.intervals.card = N ∧ ∀ J ∈ P.intervals, |J|ₗ = (b - a) / N := by
          have hI_len_pos : 0 < |I|ₗ := by
            have hsub_nonneg : 0 ≤ I.b - I.a := by linarith
            have : |I|ₗ = I.b - I.a := by
              rw [length, max_eq_left hsub_nonneg]
            rw [this]
            linarith
          have h_lemma : ∀ (I' : BoundedInterval) (n : ℕ), 0 < n → (0 < |I'|ₗ) →
            ∃ P : Partition I', P.intervals.card = n ∧ ∀ J ∈ P.intervals, |J|ₗ = (|I'|ₗ) / n := by
            intro I' n hnpos hlenpos
            induction' n with k ih generalizing I'
            · exact absurd hnpos (lt_irrefl _)
            · by_cases hk0 : k = 0
              · subst hk0
                refine ⟨⊥, by simp, ?_⟩
                intro J hJ; simp at hJ; subst hJ
                simp [length]
              · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
                have ha_lt_b : I'.a < I'.b := by
                  by_contra! hle
                  have : |I'|ₗ = 0 := by
                    simp [length, hle]
                  linarith
                set Δ := (|I'|ₗ) / ((k + 1 : ℕ) : ℝ) with hΔ
                have hΔpos : 0 < Δ := by positivity
                have hlen_eq : |I'|ₗ = I'.b - I'.a := by
                  simp [length, ha_lt_b.le]
                have ha_aΔ_lt : I'.a < I'.a + Δ := by nlinarith
                have ha_aΔ_le : I'.a ≤ I'.a + Δ := by nlinarith
                have haΔ_b : I'.a + Δ ≤ I'.b := by
                  have hΔ_le : Δ ≤ |I'|ₗ := by
                    rw [hΔ]
                    refine div_le_self (by positivity) ?_
                    exact_mod_cast (show 1 ≤ (k + 1 : ℕ) from by omega)
                  nlinarith
                have haΔ_lt_b : I'.a + Δ < I'.b := by
                  have hΔ_lt : Δ < |I'|ₗ := by
                    rw [hΔ]
                    have hkp1_gt_1 : (1 : ℝ) < ((k + 1 : ℕ) : ℝ) := by
                      exact_mod_cast (show 1 < k + 1 from by omega)
                    have hkp1_pos : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
                    have h_one_div_lt_one : (1 : ℝ) / ((k + 1 : ℕ) : ℝ) < 1 :=
                      (div_lt_one hkp1_pos).mpr hkp1_gt_1
                    calc
                      |I'|ₗ / ((k + 1 : ℕ) : ℝ) = |I'|ₗ * ((1 : ℝ) / ((k + 1 : ℕ) : ℝ)) := by ring
                      _ < |I'|ₗ * 1 := by nlinarith
                      _ = |I'|ₗ := by simp
                  nlinarith
                let I_left : BoundedInterval := match I' with
                  | Icc _ _ => Ico I'.a (I'.a + Δ)
                  | Ico _ _ => Ico I'.a (I'.a + Δ)
                  | Ioc _ _ => Ioc I'.a (I'.a + Δ)
                  | Ioo _ _ => Ioo I'.a (I'.a + Δ)
                let I_right : BoundedInterval := match I' with
                  | Icc _ _ => Icc (I'.a + Δ) I'.b
                  | Ico _ _ => Ico (I'.a + Δ) I'.b
                  | Ioc _ _ => Ioc (I'.a + Δ) I'.b
                  | Ioo _ _ => Ico (I'.a + Δ) I'.b
                have hI_left_len : |I_left|ₗ = Δ := by
                  dsimp [I_left]
                  cases I' <;> simp [length, hΔpos.le]
                have hI_right_a : I_right.a = I'.a + Δ := by
                  dsimp [I_right]; cases I' <;> rfl
                have hI_right_b : I_right.b = I'.b := by
                  dsimp [I_right]; cases I' <;> rfl
                have hI_right_len : |I_right|ₗ = k * Δ := by
                  rw [length, hI_right_a, hI_right_b]
                  have hsub : I'.b - (I'.a + Δ) = k * Δ := by
                    calc
                      I'.b - (I'.a + Δ) = (I'.b - I'.a) - Δ := by ring
                      _ = |I'|ₗ - Δ := by rw [hlen_eq]
                      _ = |I'|ₗ - (|I'|ₗ / ((k + 1 : ℕ) : ℝ)) := by rw [hΔ]
                      _ = (|I'|ₗ * (((k + 1 : ℕ) : ℝ) - 1)) / ((k + 1 : ℕ) : ℝ) := by
                        field_simp
                      _ = (|I'|ₗ * (k : ℝ)) / ((k + 1 : ℕ) : ℝ) := by push_cast; ring
                      _ = (|I'|ₗ / ((k + 1 : ℕ) : ℝ)) * (k : ℝ) := by ring
                      _ = Δ * (k : ℝ) := by rw [hΔ]
                      _ = k * Δ := mul_comm _ _
                  rw [hsub]
                  have hpos' : 0 < k * Δ := by positivity
                  simp [hpos'.le]
                have hI_right_len_pos : 0 < |I_right|ₗ := by
                  rw [hI_right_len]; positivity
                have hjoin : I'.joins I_left I_right := by
                  dsimp [I_left, I_right]
                  cases I' with
                  | Icc a b => exact BoundedInterval.join_Ico_Icc ha_aΔ_le haΔ_b
                  | Ico a b => exact BoundedInterval.join_Ico_Ico ha_aΔ_le haΔ_b
                  | Ioc a b => exact BoundedInterval.join_Ioc_Ioc ha_aΔ_le haΔ_b
                  | Ioo a b => exact BoundedInterval.join_Ioo_Ico ha_aΔ_lt haΔ_b
                have h_inter_empty : (I_left : Set ℝ) ∩ (I_right : Set ℝ) = ∅ := hjoin.1
                let P_left : Partition I_left := ⊥
                have hcard_left : P_left.intervals.card = 1 := by
                  simp [P_left]
                have hlen_left_all : ∀ J ∈ P_left.intervals, |J|ₗ = (|I'|ₗ) / ((k + 1 : ℕ) : ℝ) := by
                  intro J hJ
                  have hJ_eq : J = I_left := by
                    have : P_left.intervals = {I_left} := by simp [P_left]
                    simpa [this] using hJ
                  subst hJ_eq; rw [← hΔ]; exact hI_left_len
                have h_right_spec : ∃ P : Partition I_right, P.intervals.card = k ∧
                  ∀ J ∈ P.intervals, |J|ₗ = (|I_right|ₗ) / k :=
                  ih I_right hkpos hI_right_len_pos
                rcases h_right_spec with ⟨P_right, hcard_right, hlen_right⟩
                have hlen_right_all : ∀ J ∈ P_right.intervals, |J|ₗ = (|I'|ₗ) / ((k + 1 : ℕ) : ℝ) := by
                  intro J hJ
                  rw [hlen_right J hJ, hI_right_len]
                  calc
                    (k * Δ) / (k : ℝ) = Δ := by
                      field_simp [show (k : ℝ) ≠ 0 from by exact_mod_cast hkpos.ne.symm]
                    _ = (|I'|ₗ) / ((k + 1 : ℕ) : ℝ) := by rw [hΔ]
                have h_not_mem : I_left ∉ P_right.intervals := by
                  intro hmem
                  have hsub : I_left ⊆ I_right := P_right.contains I_left hmem
                  have h_empty : (I_left : Set ℝ) = ∅ := by
                    have hsub' : (I_left : Set ℝ) ⊆ (I_right : Set ℝ) := hsub
                    have h_eq : (I_left : Set ℝ) = (I_left : Set ℝ) ∩ (I_right : Set ℝ) :=
                      (Set.inter_eq_left.mpr hsub').symm
                    calc
                      (I_left : Set ℝ) = (I_left : Set ℝ) ∩ (I_right : Set ℝ) := h_eq
                      _ = ∅ := h_inter_empty
                  have hlen0 : |I_left|ₗ = 0 := BoundedInterval.length_of_empty h_empty
                  rw [hI_left_len] at hlen0
                  linarith
                have hcard_total : (P_left.join P_right hjoin).intervals.card = k + 1 := by
                  rw [Partition.intervals_of_join]
                  have hcard_union : (P_left.intervals ∪ P_right.intervals).card = 1 + k := by
                    have hcard_singleton : P_left.intervals = {I_left} := by simp [P_left]
                    rw [hcard_singleton]
                    by_cases hmem : I_left ∈ P_right.intervals
                    · exact absurd hmem h_not_mem
                    · simp [hcard_right, hmem, add_comm]
                  simpa [add_comm] using hcard_union
                refine ⟨P_left.join P_right hjoin, hcard_total, ?_⟩
                intro J hJ
                rw [Partition.intervals_of_join] at hJ
                rcases Finset.mem_union.mp hJ with (hJ_left | hJ_right)
                · exact hlen_left_all J hJ_left
                · exact hlen_right_all J hJ_right
          rcases h_lemma I N hNpos hI_len_pos with ⟨P, hcard, hlen⟩
          have hI_len_eq : |I|ₗ = b - a := by
            have : 0 ≤ b - a := by linarith
            rw [length, max_eq_left this]
          refine ⟨P, hcard, ?_⟩
          intro J hJ
          rw [hlen J hJ, hI_len_eq]
        rcases hpart with ⟨P, hcard, hlength⟩
        classical
          -- Construct g (takes sup on each partition interval) that majorizes f
          let g : ℝ → ℝ := λ x ↦
            if hxI : x ∈ (I : Set ℝ) then
              sSup (f '' (((P.exists_unique x hxI).choose) : Set ℝ))
            else 0
          have hg_majorizes : MajorizesOn g f I := by
            intro x hx
            rcases P.exists_unique x hx with ⟨J, ⟨hJ_mem, hxJ⟩, huniq⟩
            have h_fx_img : f x ∈ f '' (J : Set ℝ) := ⟨x, hxJ, rfl⟩
            have h_bdd_above : BddAbove (f '' (J : Set ℝ)) := by
              rcases hfbound with ⟨M, hM⟩
              refine ⟨M, λ y hy => ?_⟩
              rcases hy with ⟨x', hx', rfl⟩
              have hx'I : x' ∈ (I : Set ℝ) := (P.contains J hJ_mem) x' hx'
              have h_abs : |f x'| ≤ M := hM x' hx'I
              nlinarith [abs_le.mp h_abs]
            have h_fx_le_sup : f x ≤ sSup (f '' (J : Set ℝ)) := le_csSup h_bdd_above h_fx_img
            dsimp [g]
            rw [dif_pos hx]
            have hJ_eq : (P.exists_unique x hx).choose = J :=
              huniq ((P.exists_unique x hx).choose) ((P.exists_unique x hx).choose_spec).1
            rw [hJ_eq]
            exact h_fx_le_sup
          have hg_pwc : PiecewiseConstantWith g P := by
            intro J hJ
            apply ConstantOn.of_const
            intro x hx
            have hxI : x ∈ (I : Set ℝ) := (P.contains J hJ) x hx
            rcases P.exists_unique x hxI with ⟨J', ⟨hJ'_mem, hxJ'⟩, huniq⟩
            have hJ'_eq : J' = J := (huniq J ⟨hJ, hx⟩).symm
            dsimp [g]
            rw [dif_pos hxI]
            have hJ_eq : (P.exists_unique x hxI).choose = J' :=
              huniq ((P.exists_unique x hxI).choose) ((P.exists_unique x hxI).choose_spec).1
            rw [hJ_eq, hJ'_eq]
          have hg_pwc_on : PiecewiseConstantOn g I := ⟨P, hg_pwc⟩
          have hg_integ_eq : PiecewiseConstantWith.RS_integ g P α = ∑ J ∈ P.intervals, (sSup (f '' (J : Set ℝ))) * α[J]ₗ := by
            dsimp [PiecewiseConstantWith.RS_integ]
            refine Finset.sum_congr rfl (λ J hJ => ?_)
            by_cases hJ_nonempty : (J : Set ℝ).Nonempty
            · have h_const_val : constant_value_on g (J : Set ℝ) = sSup (f '' (J : Set ℝ)) := by
                apply ConstantOn.const_eq hJ_nonempty
                intro x hx
                have hxI : x ∈ (I : Set ℝ) := (P.contains J hJ) x hx
                rcases P.exists_unique x hxI with ⟨J', ⟨hJ'_mem, hxJ'⟩, huniq⟩
                have hJ'_eq : J' = J := (huniq J ⟨hJ, hx⟩).symm
                dsimp [g]
                rw [dif_pos hxI]
                have hJ_eq : (P.exists_unique x hxI).choose = J' :=
                  huniq ((P.exists_unique x hxI).choose) ((P.exists_unique x hxI).choose_spec).1
                rw [hJ_eq, hJ'_eq]
              simp [h_const_val]
            · have hJ_empty : (J : Set ℝ) = ∅ := Set.not_nonempty_iff_eq_empty.mp hJ_nonempty
              have hlen_α : α[J]ₗ = 0 := α_length_of_empty α hJ_empty
              simp [hlen_α]
          have h_upper_bound : upper_RS_integral f I α ≤ ∑ J ∈ P.intervals, (sSup (f '' (J : Set ℝ))) * α[J]ₗ := by
            calc
              upper_RS_integral f I α ≤ PiecewiseConstantOn.RS_integ g I α :=
                upper_RS_integral_le_integ hfbound hg_majorizes hg_pwc_on hα
              _ = PiecewiseConstantWith.RS_integ g P α := by
                rw [PiecewiseConstantOn.RS_integ_def hg_pwc α]
              _ = ∑ J ∈ P.intervals, (sSup (f '' (J : Set ℝ))) * α[J]ₗ := hg_integ_eq
          -- Construct h (takes inf on each partition interval) that minorizes f
          let h : ℝ → ℝ := λ x ↦
            if hxI : x ∈ (I : Set ℝ) then
              sInf (f '' (((P.exists_unique x hxI).choose) : Set ℝ))
            else 0
          have hh_minorizes : MinorizesOn h f I := by
            intro x hx
            rcases P.exists_unique x hx with ⟨J, ⟨hJ_mem, hxJ⟩, huniq⟩
            have h_fx_img : f x ∈ f '' (J : Set ℝ) := ⟨x, hxJ, rfl⟩
            have h_bdd_below : BddBelow (f '' (J : Set ℝ)) := by
              rcases hfbound with ⟨M, hM⟩
              refine ⟨-M, λ y hy => ?_⟩
              rcases hy with ⟨x', hx', rfl⟩
              have hx'I : x' ∈ (I : Set ℝ) := (P.contains J hJ_mem) x' hx'
              have h_abs : |f x'| ≤ M := hM x' hx'I
              nlinarith [abs_le.mp h_abs]
            have h_inf_le_fx : sInf (f '' (J : Set ℝ)) ≤ f x := csInf_le h_bdd_below h_fx_img
            dsimp [h]
            rw [dif_pos hx]
            have hJ_eq : (P.exists_unique x hx).choose = J :=
              huniq ((P.exists_unique x hx).choose) ((P.exists_unique x hx).choose_spec).1
            rw [hJ_eq]
            exact h_inf_le_fx
          have hh_pwc : PiecewiseConstantWith h P := by
            intro J hJ
            apply ConstantOn.of_const
            intro x hx
            have hxI : x ∈ (I : Set ℝ) := (P.contains J hJ) x hx
            rcases P.exists_unique x hxI with ⟨J', ⟨hJ'_mem, hxJ'⟩, huniq⟩
            have hJ'_eq : J' = J := (huniq J ⟨hJ, hx⟩).symm
            dsimp [h]
            rw [dif_pos hxI]
            have hJ_eq : (P.exists_unique x hxI).choose = J' :=
              huniq ((P.exists_unique x hxI).choose) ((P.exists_unique x hxI).choose_spec).1
            rw [hJ_eq, hJ'_eq]
          have hh_pwc_on : PiecewiseConstantOn h I := ⟨P, hh_pwc⟩
          have hh_integ_eq : PiecewiseConstantWith.RS_integ h P α = ∑ J ∈ P.intervals, (sInf (f '' (J : Set ℝ))) * α[J]ₗ := by
            dsimp [PiecewiseConstantWith.RS_integ]
            refine Finset.sum_congr rfl (λ J hJ => ?_)
            by_cases hJ_nonempty : (J : Set ℝ).Nonempty
            · have h_const_val : constant_value_on h (J : Set ℝ) = sInf (f '' (J : Set ℝ)) := by
                apply ConstantOn.const_eq hJ_nonempty
                intro x hx
                have hxI : x ∈ (I : Set ℝ) := (P.contains J hJ) x hx
                rcases P.exists_unique x hxI with ⟨J', ⟨hJ'_mem, hxJ'⟩, huniq⟩
                have hJ'_eq : J' = J := (huniq J ⟨hJ, hx⟩).symm
                dsimp [h]
                rw [dif_pos hxI]
                have hJ_eq : (P.exists_unique x hxI).choose = J' :=
                  huniq ((P.exists_unique x hxI).choose) ((P.exists_unique x hxI).choose_spec).1
                rw [hJ_eq, hJ'_eq]
              simp [h_const_val]
            · have hJ_empty : (J : Set ℝ) = ∅ := Set.not_nonempty_iff_eq_empty.mp hJ_nonempty
              have hlen_α : α[J]ₗ = 0 := α_length_of_empty α hJ_empty
              simp [hlen_α]
          have h_lower_bound : ∑ J ∈ P.intervals, (sInf (f '' (J : Set ℝ))) * α[J]ₗ ≤ lower_RS_integral f I α := by
            calc
              ∑ J ∈ P.intervals, (sInf (f '' (J : Set ℝ))) * α[J]ₗ = PiecewiseConstantWith.RS_integ h P α := by
                symm; exact hh_integ_eq
              _ = PiecewiseConstantOn.RS_integ h I α := by
                rw [PiecewiseConstantOn.RS_integ_def hh_pwc α]
              _ ≤ lower_RS_integral f I α := integ_le_lower_RS_integral hfbound hh_minorizes hh_pwc_on hα
        have h_osc_est : ∀ J ∈ P.intervals, sSup (f '' (J : Set ℝ)) - sInf (f '' (J : Set ℝ)) ≤ ε := by
          intro J hJ
          have h_lenJ : |J|ₗ = (b - a) / N := hlength J hJ
          have h_lt_δ : |J|ₗ < δ := by
            rw [h_lenJ]; exact hN'
          have h_sub_interval : ∀ x, x ∈ J → ∀ y, y ∈ J → |f x - f y| ≤ ε := by
            intro x hx y hy
            have hxI : x ∈ (I : Set ℝ) := (P.contains J hJ) x hx
            have hyI : y ∈ (I : Set ℝ) := (P.contains J hJ) y hy
            have hdist : |x - y| < δ := by
              have : |x - y| ≤ |J|ₗ := BoundedInterval.dist_le_length hx hy
              exact lt_of_le_of_lt this h_lt_δ
            exact hf_unif y hyI x hxI (by exact hdist.le)
          have hJ_nonempty : (J : Set ℝ).Nonempty := by
            by_contra! h
            have hlen0 : |J|ₗ = 0 := BoundedInterval.length_of_empty h
            rw [hlength J hJ] at hlen0
            have : 0 < (b - a) / N := by positivity
            linarith
          rcases hJ_nonempty with ⟨y0, hy0⟩
          have h_sup_le : sSup (f '' (J : Set ℝ)) ≤ sInf (f '' (J : Set ℝ)) + ε := by
            have h_ineq : ∀ x, x ∈ J → ∀ y, y ∈ J → f x ≤ f y + ε := by
              intro x hx y hy
              have h_diff : |f x - f y| ≤ ε := h_sub_interval x hx y hy
              nlinarith [abs_le.mp h_diff]
            apply csSup_le (⟨f y0, y0, hy0, rfl⟩ : (f '' (J : Set ℝ)).Nonempty)
            intro b hb
            rcases hb with ⟨z, hz, rfl⟩
            have h_fz_minus_ε : f z - ε ≤ sInf (f '' (J : Set ℝ)) := by
              refine le_csInf (⟨f y0, y0, hy0, rfl⟩ : (f '' (J : Set ℝ)).Nonempty) ?_
              intro b hb
              rcases hb with ⟨w, hw, rfl⟩
              have h_diff_wz : |f w - f z| ≤ ε := h_sub_interval w hw z hz
              nlinarith [abs_le.mp h_diff_wz]
            nlinarith
          linarith
        calc
          upper_RS_integral f I α - lower_RS_integral f I α
              ≤ (∑ J ∈ P.intervals, (sSup (f '' (J : Set ℝ))) * α[J]ₗ) -
                (∑ J ∈ P.intervals, (sInf (f '' (J : Set ℝ))) * α[J]ₗ) := by
                linarith
          _ = ∑ J ∈ P.intervals, ((sSup (f '' (J : Set ℝ))) * α[J]ₗ - (sInf (f '' (J : Set ℝ))) * α[J]ₗ) := by
            rw [Finset.sum_sub_distrib]
          _ = ∑ J ∈ P.intervals, ((sSup (f '' (J : Set ℝ))) - sInf (f '' (J : Set ℝ))) * α[J]ₗ := by
            refine Finset.sum_congr rfl (λ J hJ => ?_)
            ring
          _ ≤ ∑ J ∈ P.intervals, (ε * α[J]ₗ) := by
            refine Finset.sum_le_sum (λ J hJ => ?_)
            have h_α_nonneg : 0 ≤ α[J]ₗ := α_length_nonneg_of_monotone hα J
            have h_diff := h_osc_est J hJ
            nlinarith
          _ = ε * (∑ J ∈ P.intervals, α[J]ₗ) := by
            rw [← Finset.mul_sum]
          _ = ε * α[I]ₗ := by rw [Partition.sum_of_α_length P α]
      have lower_le_upper : 0 ≤ upper_RS_integral f I α - lower_RS_integral f I α := by
        linarith [lower_RS_integral_le_upper hfbound hα]
      obtain h | h := le_iff_lt_or_eq.mp lower_le_upper
      · set ε := (upper_RS_integral f I α - lower_RS_integral f I α) / (2 * α[I]ₗ) with hε
        have hεpos : 0 < ε := by
          refine div_pos (by linarith) (by nlinarith)
        have hbound' : upper_RS_integral f I α - lower_RS_integral f I α ≤
          ε * α[I]ₗ := this ε hεpos
        rw [hε] at hbound'
        have : 0 < 2 * α[I]ₗ := by nlinarith
        field_simp at hbound'
        nlinarith
      · linarith

/-- Exercise 11.8.5 -/
theorem RS_integ_with_sign (f:ℝ → ℝ) (hf: ContinuousOn f (.Icc (-1) 1)) :
    RS_IntegrableOn f (Icc (-1) 1) Real.sign ∧ RS_integ f (Icc (-1) 1) Real.sign = 2 * f 0 := by
  have h_sign_mono : Monotone Real.sign := by
    intro x y hxy
    by_cases hx0 : x < 0
    · have hx_sign : Real.sign x = -1 := by
        rw [Real.sign_def, if_pos hx0]
      rw [hx_sign]
      by_cases hy0 : y < 0
      · rw [Real.sign_def, if_pos hy0]
      · by_cases hy0' : y > 0
        · simp [Real.sign_def, hy0, hy0']
        · have hy0_eq : y = 0 := by linarith
          subst hy0_eq; simp
    · have hx_nonneg : x ≥ 0 := by linarith
      by_cases hx_pos : x > 0
      · have hx_sign : Real.sign x = 1 := by
          rw [Real.sign_def, if_neg (by linarith), if_pos hx_pos]
        rw [hx_sign]
        have hy_pos : y > 0 := by linarith
        have hy_sign : Real.sign y = 1 := by
          rw [Real.sign_def, if_neg (by linarith), if_pos hy_pos]
        rw [hy_sign]
      · have hx0_eq : x = 0 := by linarith
        subst hx0_eq
        rcases lt_or_eq_of_le hxy with (hy_pos | hy_eq)
        · have hy_not_neg : ¬ y < 0 := by linarith
          simp [Real.sign_def, hy_not_neg, hy_pos]
        · subst hy_eq; simp
  have hbdd : BddOn f (Icc (-1) 1) :=
    BddOn.of_continuous_on_compact (by norm_num : (-1 : ℝ) < 1) hf
  have h_unif : UniformContinuousOn f (Icc (-1) 1) :=
    UniformContinuousOn.of_continuousOn hf
  have hint : RS_IntegrableOn f (Icc (-1) 1) Real.sign :=
    RS_integ_of_uniform_cts h_unif h_sign_mono
  have h_int_eq : lower_RS_integral f (Icc (-1) 1) Real.sign =
    upper_RS_integral f (Icc (-1) 1) Real.sign := hint.2
  -- α-length computations for Real.sign
  have h_sign_right_lim_0 : right_lim Real.sign 0 = 1 :=
    right_lim_def Convergesto.sign_right
  have h_sign_left_lim_0 : left_lim Real.sign 0 = -1 :=
    left_lim_def Convergesto.sign_left
  have h_sign_conv_right_1 : Convergesto (.Ioi 1) Real.sign 1 1 := by
    rw [Convergesto.iff_conv]
    intro a ha hconv
    have hpos : ∀ n, a n > 1 := ha
    have hsign : ∀ n, Real.sign (a n) = 1 := by
      intro n
      have hpos0 : a n > 0 := by
        have : (1 : ℝ) > 0 := by norm_num
        exact lt_trans this (hpos n)
      have h_not_neg : ¬ a n < 0 := by linarith
      rw [Real.sign_def, if_neg h_not_neg, if_pos hpos0]
    have : (fun n : ℕ => Real.sign (a n)) = fun _ : ℕ => (1 : ℝ) := by
      ext n; exact hsign n
    rw [this]
    exact tendsto_const_nhds
  have h_sign_conv_left_m1 : Convergesto (.Iio (-1)) Real.sign (-1) (-1) := by
    rw [Convergesto.iff_conv]
    intro a ha hconv
    have hneg : ∀ n, a n < -1 := ha
    have hsign : ∀ n, Real.sign (a n) = -1 := by
      intro n
      have hneg0 : a n < 0 := lt_trans (hneg n) (by norm_num : (-1 : ℝ) < 0)
      rw [Real.sign_def, if_pos hneg0]
    have : (fun n : ℕ => Real.sign (a n)) = fun _ : ℕ => (-1 : ℝ) := by
      ext n; exact hsign n
    rw [this]
    exact tendsto_const_nhds
  have h_sign_right_lim_1 : right_lim Real.sign 1 = 1 :=
    right_lim_def h_sign_conv_right_1
  have h_sign_left_lim_m1 : left_lim Real.sign (-1) = -1 :=
    left_lim_def h_sign_conv_left_m1
  have h_α_Ico : Real.sign[Ico (-1) 0]ₗ = 0 := by
    simp [α_length, show (-1 : ℝ) ≤ 0 by norm_num, h_sign_left_lim_0, h_sign_left_lim_m1]
  have h_α_Icc : Real.sign[Icc (0 : ℝ) 0]ₗ = 2 := by
    rw [α_length_of_pt, jump, h_sign_right_lim_0, h_sign_left_lim_0]
    ring
  have h_α_Ioc : Real.sign[Ioc (0 : ℝ) 1]ₗ = 0 := by
    simp [α_length, show (0 : ℝ) ≤ 1 by norm_num, h_sign_right_lim_1, h_sign_right_lim_0]
  -- Build PC majorant g and minorant h
  obtain ⟨M, hM⟩ := hbdd
  let g : ℝ → ℝ := λ x =>
    if hx : x < 0 then M
    else if hx' : x ≤ 0 then f 0
    else M
  let h : ℝ → ℝ := λ x =>
    if hx : x < 0 then -M
    else if hx' : x ≤ 0 then f 0
    else -M
  have hg_maj : MajorizesOn g f (Icc (-1) 1) := by
    intro x hx
    have ⟨hx1, hx2⟩ := hx
    dsimp [g]
    by_cases hx_lt0 : x < 0
    · simp [hx_lt0]
      have hfxM : |f x| ≤ M := hM x ⟨hx1, hx2⟩
      linarith [abs_le.mp hfxM]
    · simp [hx_lt0]
      by_cases hx_le0 : x ≤ 0
      · simp [hx_le0]
        have hx0 : x = 0 := by linarith
        subst hx0; rfl
      · simp [hx_le0]
        have hfxM : |f x| ≤ M := hM x ⟨hx1, hx2⟩
        linarith [abs_le.mp hfxM]
  have hh_min : MinorizesOn h f (Icc (-1) 1) := by
    intro x hx
    have ⟨hx1, hx2⟩ := hx
    dsimp [h]
    by_cases hx_lt0 : x < 0
    · simp [hx_lt0]
      have hfxM : |f x| ≤ M := hM x ⟨hx1, hx2⟩
      linarith [abs_le.mp hfxM]
    · simp [hx_lt0]
      by_cases hx_le0 : x ≤ 0
      · simp [hx_le0]
        have hx0 : x = 0 := by linarith
        subst hx0; rfl
      · simp [hx_le0]
        have hfxM : |f x| ≤ M := hM x ⟨hx1, hx2⟩
        linarith [abs_le.mp hfxM]
  let P : Partition (Icc (-1 : ℝ) 1) :=
    ((⊥ : Partition (Ico (-1 : ℝ) 0)).join (⊥ : Partition (Icc (0 : ℝ) 0))
      (join_Ico_Icc (by norm_num) (by norm_num))).join
      (⊥ : Partition (Ioc (0 : ℝ) 1))
      (join_Icc_Ioc (by norm_num) (by norm_num))
  have hg_pc : PiecewiseConstantWith g P := by
    intro J hJ
    rcases Finset.mem_union.mp hJ with (hJ' | hJ')
    · rcases Finset.mem_union.mp hJ' with (hJ_Ico | hJ_Icc)
      · have hJ_eq : J = Ico (-1 : ℝ) 0 := by
          simpa [Partition.intervals_of_bot] using hJ_Ico
        subst hJ_eq
        refine ConstantOn.of_const (c := M) ?_
        intro x hx
        rcases hx with ⟨hx_low, hx_lt0⟩
        dsimp [g]
        simp [hx_lt0]
      · have hJ_eq : J = Icc (0 : ℝ) 0 := by
          simpa [Partition.intervals_of_bot] using hJ_Icc
        subst hJ_eq
        refine ConstantOn.of_const (c := f 0) ?_
        intro x hx
        rcases hx with ⟨hx_low, hx_high⟩
        dsimp [g]
        have hx0 : x = 0 := by linarith
        subst hx0; simp
    · have hJ_eq : J = Ioc (0 : ℝ) 1 := by
        simpa [Partition.intervals_of_bot] using hJ'
      subst hJ_eq
      refine ConstantOn.of_const (c := M) ?_
      intro x hx
      rcases hx with ⟨hx_gt0, hx_high⟩
      dsimp [g]
      have hx_not_lt0 : ¬ x < 0 := by linarith
      have hx_not_le0 : ¬ x ≤ 0 := by linarith
      simp [hx_not_lt0, hx_not_le0]
  have hg_pc_on : PiecewiseConstantOn g (Icc (-1) 1) := ⟨P, hg_pc⟩
  have hh_pc : PiecewiseConstantWith h P := by
    intro J hJ
    rcases Finset.mem_union.mp hJ with (hJ' | hJ')
    · rcases Finset.mem_union.mp hJ' with (hJ_Ico | hJ_Icc)
      · have hJ_eq : J = Ico (-1 : ℝ) 0 := by
          simpa [Partition.intervals_of_bot] using hJ_Ico
        subst hJ_eq
        refine ConstantOn.of_const (c := -M) ?_
        intro x hx
        rcases hx with ⟨hx_low, hx_lt0⟩
        dsimp [h]
        simp [hx_lt0]
      · have hJ_eq : J = Icc (0 : ℝ) 0 := by
          simpa [Partition.intervals_of_bot] using hJ_Icc
        subst hJ_eq
        refine ConstantOn.of_const (c := f 0) ?_
        intro x hx
        rcases hx with ⟨hx_low, hx_high⟩
        dsimp [h]
        have hx0 : x = 0 := by linarith
        subst hx0; simp
    · have hJ_eq : J = Ioc (0 : ℝ) 1 := by
        simpa [Partition.intervals_of_bot] using hJ'
      subst hJ_eq
      refine ConstantOn.of_const (c := -M) ?_
      intro x hx
      rcases hx with ⟨hx_gt0, hx_high⟩
      dsimp [h]
      have hx_not_lt0 : ¬ x < 0 := by linarith
      have hx_not_le0 : ¬ x ≤ 0 := by linarith
      simp [hx_not_lt0, hx_not_le0]
  have hh_pc_on : PiecewiseConstantOn h (Icc (-1) 1) := ⟨P, hh_pc⟩
  have h_intervals : P.intervals = {Ico (-1 : ℝ) 0, Icc (0 : ℝ) 0, Ioc (0 : ℝ) 1} := by
    let inner := (⊥ : Partition (Ico (-1 : ℝ) 0)).join (⊥ : Partition (Icc (0 : ℝ) 0))
      (join_Ico_Icc (by norm_num) (by norm_num))
    calc
      P.intervals = (inner.join (⊥ : Partition (Ioc (0 : ℝ) 1)) (join_Icc_Ioc (by norm_num) (by norm_num))).intervals := rfl
      _ = inner.intervals ∪ (⊥ : Partition (Ioc (0 : ℝ) 1)).intervals := by rw [Partition.intervals_of_join]
      _ = (((⊥ : Partition (Ico (-1 : ℝ) 0)).intervals ∪ (⊥ : Partition (Icc (0 : ℝ) 0)).intervals) : Finset BoundedInterval) ∪
        (⊥ : Partition (Ioc (0 : ℝ) 1)).intervals := by
        rw [Partition.intervals_of_join]
      _ = ({Ico (-1 : ℝ) 0} : Finset BoundedInterval) ∪ {Icc (0 : ℝ) 0} ∪ {Ioc (0 : ℝ) 1} := by
        simp [Partition.intervals_of_bot]
      _ = {Ico (-1 : ℝ) 0, Icc (0 : ℝ) 0, Ioc (0 : ℝ) 1} := by simp
  have h_g_integ : PiecewiseConstantWith.RS_integ g P Real.sign = 2 * f 0 := by
    rw [PiecewiseConstantWith.RS_integ, h_intervals]
    have h_not_mem1 : Ico (-1 : ℝ) 0 ∉ ({Icc (0 : ℝ) 0, Ioc (0 : ℝ) 1} : Finset BoundedInterval) := by simp
    have h_not_mem2 : Icc (0 : ℝ) 0 ∉ ({Ioc (0 : ℝ) 1} : Finset BoundedInterval) := by simp
    rw [Finset.sum_insert h_not_mem1, Finset.sum_insert h_not_mem2, Finset.sum_singleton]
    rw [h_α_Ico, h_α_Icc, h_α_Ioc]
    have h_nonempty : (Icc (0 : ℝ) 0 : Set ℝ).Nonempty := by
      use 0; simp
    have h_const_val : constant_value_on g (Icc (0 : ℝ) 0 : Set ℝ) = f 0 := by
      apply ConstantOn.const_eq h_nonempty
      intro x hx
      dsimp [g]
      have hx0 : x = 0 := by
        simpa [Set.mem_Icc] using hx
      subst hx0; simp
    rw [h_const_val]
    simp
    ring_nf
  have h_h_integ : PiecewiseConstantWith.RS_integ h P Real.sign = 2 * f 0 := by
    rw [PiecewiseConstantWith.RS_integ, h_intervals]
    have h_not_mem1 : Ico (-1 : ℝ) 0 ∉ ({Icc (0 : ℝ) 0, Ioc (0 : ℝ) 1} : Finset BoundedInterval) := by simp
    have h_not_mem2 : Icc (0 : ℝ) 0 ∉ ({Ioc (0 : ℝ) 1} : Finset BoundedInterval) := by simp
    rw [Finset.sum_insert h_not_mem1, Finset.sum_insert h_not_mem2, Finset.sum_singleton]
    rw [h_α_Ico, h_α_Icc, h_α_Ioc]
    have h_nonempty : (Icc (0 : ℝ) 0 : Set ℝ).Nonempty := by
      use 0; simp
    have h_const_val : constant_value_on h (Icc (0 : ℝ) 0 : Set ℝ) = f 0 := by
      apply ConstantOn.const_eq h_nonempty
      intro x hx
      dsimp [h]
      have hx0 : x = 0 := by
        simpa [Set.mem_Icc] using hx
      subst hx0; simp
    rw [h_const_val]
    simp
    ring_nf
  have h_g_integ_on : PiecewiseConstantOn.RS_integ g (Icc (-1) 1) Real.sign = 2 * f 0 := by
    rw [PiecewiseConstantOn.RS_integ_def hg_pc, h_g_integ]
  have h_h_integ_on : PiecewiseConstantOn.RS_integ h (Icc (-1) 1) Real.sign = 2 * f 0 := by
    rw [PiecewiseConstantOn.RS_integ_def hh_pc, h_h_integ]
  have h_upper_le : upper_RS_integral f (Icc (-1) 1) Real.sign ≤ 2 * f 0 := by
    calc
      upper_RS_integral f (Icc (-1) 1) Real.sign ≤ PiecewiseConstantOn.RS_integ g (Icc (-1) 1) Real.sign :=
        upper_RS_integral_le_integ hint.1 hg_maj hg_pc_on h_sign_mono
      _ = 2 * f 0 := h_g_integ_on
  have h_lower_ge : 2 * f 0 ≤ lower_RS_integral f (Icc (-1) 1) Real.sign := by
    calc
      2 * f 0 = PiecewiseConstantOn.RS_integ h (Icc (-1) 1) Real.sign := by symm; exact h_h_integ_on
      _ ≤ lower_RS_integral f (Icc (-1) 1) Real.sign :=
        integ_le_lower_RS_integral hint.1 hh_min hh_pc_on h_sign_mono
  have h_integ_eq : RS_integ f (Icc (-1) 1) Real.sign = 2 * f 0 := by
    dsimp [RS_integ]
    have h_upper_eq : upper_RS_integral f (Icc (-1) 1) Real.sign = 2 * f 0 := by
      apply le_antisymm h_upper_le
      calc
        2 * f 0 ≤ lower_RS_integral f (Icc (-1) 1) Real.sign := h_lower_ge
        _ = upper_RS_integral f (Icc (-1) 1) Real.sign := h_int_eq
    exact h_upper_eq
  exact ⟨hint, h_integ_eq⟩

/-- Analogue of Lemma 11.3.7 -/
theorem RS_integ_of_piecewise_const {f:ℝ → ℝ} {I: BoundedInterval} (hf: PiecewiseConstantOn f I)
  {α: ℝ → ℝ} (hα: Monotone α):
  RS_IntegrableOn f I α ∧ RS_integ f I α = PiecewiseConstantOn.RS_integ f I α := by
  have hmaj : MajorizesOn f f I := λ x hx ↦ le_rfl
  have hmin : MinorizesOn f f I := λ x hx ↦ le_rfl
  have hbdd : BddOn f I := by
    rcases hf with ⟨P, hP⟩
    by_cases hI_nonempty : (I : Set ℝ).Nonempty
    · rcases hI_nonempty with ⟨x0, hx0⟩
      rcases P.exists_unique x0 hx0 with ⟨J0, ⟨hJ0mem, _⟩, _⟩
      have h_intervals_nonempty : P.intervals.Nonempty := ⟨J0, hJ0mem⟩
      let vals : Finset ℝ := Finset.image (λ (J : BoundedInterval) => constant_value_on f (J : Set ℝ)) P.intervals
      have h_vals_nonempty : vals.Nonempty := by
        have h_val0 : constant_value_on f (J0 : Set ℝ) ∈ vals :=
          Finset.mem_image.mpr ⟨J0, hJ0mem, rfl⟩
        exact ⟨constant_value_on f (J0 : Set ℝ), h_val0⟩
      use Finset.sup' vals h_vals_nonempty (λ v => |v|)
      intro x hx
      rcases P.exists_unique x hx with ⟨J, ⟨hJmem, hxJ⟩, _⟩
      have h_const : ConstantOn f (J : Set ℝ) := hP J hJmem
      have hfx_eq : f x = constant_value_on f (J : Set ℝ) := h_const.eq hxJ
      rw [hfx_eq]
      have h_val_mem : constant_value_on f (J : Set ℝ) ∈ vals :=
        Finset.mem_image.mpr ⟨J, hJmem, rfl⟩
      exact Finset.le_sup' (λ v : ℝ => |v|) h_val_mem
    · use 0; intro x hx; exfalso; exact hI_nonempty ⟨x, hx⟩
  set RS_integ_val := PiecewiseConstantOn.RS_integ f I α with hRS_integ_val
  have hmem_upper : RS_integ_val ∈ (PiecewiseConstantOn.RS_integ · I α) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I} := by
    refine ⟨f, ⟨hmaj, hf⟩, rfl⟩
  have hmem_lower : RS_integ_val ∈ (PiecewiseConstantOn.RS_integ · I α) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I} := by
    refine ⟨f, ⟨hmin, hf⟩, rfl⟩
  have h_upper_integ_le : upper_RS_integral f I α ≤ RS_integ_val :=
    csInf_le (RS_integral_bound_below hbdd hα) hmem_upper
  have h_lower_integ_ge : RS_integ_val ≤ lower_RS_integral f I α :=
    le_csSup (RS_integral_bound_above hbdd hα) hmem_lower
  have h_lower_le_upper : lower_RS_integral f I α ≤ upper_RS_integral f I α :=
    lower_RS_integral_le_upper hbdd hα
  have h_eq : lower_RS_integral f I α = upper_RS_integral f I α := by
    apply le_antisymm h_lower_le_upper
    calc
      upper_RS_integral f I α ≤ RS_integ_val := h_upper_integ_le
      _ ≤ lower_RS_integral f I α := h_lower_integ_ge
  have h_upper_integ_eq : upper_RS_integral f I α = RS_integ_val :=
    le_antisymm h_upper_integ_le (calc
      RS_integ_val ≤ lower_RS_integral f I α := h_lower_integ_ge
      _ = upper_RS_integral f I α := h_eq)
  have h_RS_integ_eq : RS_integ f I α = RS_integ_val := by
    dsimp [RS_integ, RS_integ_val]
    exact h_upper_integ_eq
  exact ⟨⟨hbdd, h_eq⟩, h_RS_integ_eq⟩

end Chapter11
