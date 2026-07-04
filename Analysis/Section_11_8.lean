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

/-- Theorem 11.8.4 / Exercise 11.8.1 -/
theorem Partition.sum_of_α_length  {I: BoundedInterval} (P: Partition I) (α: ℝ → ℝ) :
  ∑ J ∈ P.intervals, α[J]ₗ = α[I]ₗ := by
  revert α
  generalize hcard: P.intervals.card = n
  revert I; induction' n with n hn <;> intro I P hcard α
  . rw [Finset.card_eq_zero] at hcard
    have hI_empty : (I:Set ℝ) = ∅ := by
      by_contra! hne
      rcases hne with ⟨x, hx⟩
      rcases P.exists_unique x hx with ⟨J, ⟨hJmem, _⟩, _⟩
      have hP_empty : P.intervals = ∅ := hcard
      have hJmem' : J ∈ P.intervals := hJmem
      rw [hP_empty] at hJmem'; simp at hJmem'
    simp [α_length_of_empty α hI_empty]
  -- Inductive step. Check if I is subsingleton.
  by_cases hsub : Subsingleton (I:Set ℝ)
  · by_cases h_empty : (I : Set ℝ) = ∅
    · have h_empty_all : ∀ J ∈ P.intervals, (J : Set ℝ) = ∅ := by
        intro J hJ; apply Set.not_nonempty_iff_eq_empty.mp; intro hne
        rcases hne with ⟨x, hx⟩
        have hxI : x ∈ (I : Set ℝ) := P.contains J hJ x hx
        rw [h_empty] at hxI; exact hxI
      simp [α_length_of_empty α h_empty, Finset.sum_eq_zero (λ J hJ => by
        simp [α_length_of_empty α (h_empty_all J hJ)])]
    · have h_nonempty : (I : Set ℝ).Nonempty := Set.nonempty_iff_ne_empty.mpr h_empty
      rcases h_nonempty with ⟨a, ha⟩
      rcases (P.exists_unique a ha).exists with ⟨J₀, hJ₀_mem, haJ₀⟩
      have h_J_empty (J : BoundedInterval) (hJ : J ∈ P.intervals) (hJ_ne : J ≠ J₀) : (J : Set ℝ) = ∅ := by
        by_contra! hne
        have h_nonempty' : (J : Set ℝ).Nonempty := by
          by_contra! h_empty'
          apply hne
          exact Set.not_nonempty_iff_eq_empty.mpr h_empty'
        rcases h_nonempty' with ⟨x, hx⟩
        have hxI : x ∈ (I : Set ℝ) := P.contains J hJ x hx
        have ha_subtype : a ∈ (I : Set ℝ) := ha
        have hx_eq_a : x = a := congr_arg Subtype.val (Subsingleton.elim (h := hsub) ⟨x, hxI⟩ ⟨a, ha_subtype⟩)
        have hxJ₀ : x ∈ (J₀ : Set ℝ) := by rw [hx_eq_a]; exact haJ₀
        have huniq := (P.exists_unique x hxI).unique ⟨hJ, hx⟩ ⟨hJ₀_mem, hxJ₀⟩
        exact hJ_ne huniq
      have hJ₀_sub_a : (J₀ : Set ℝ) ⊆ {a} := by
        intro x hx
        have hxI : x ∈ (I : Set ℝ) := P.contains J₀ hJ₀_mem x hx
        have ha_subtype : a ∈ (I : Set ℝ) := ha
        have hx_eq_a : x = a := congr_arg Subtype.val (Subsingleton.elim (h := hsub) ⟨x, hxI⟩ ⟨a, ha_subtype⟩)
        simp [hx_eq_a]
      have ha_sub_J₀ : {a} ⊆ (J₀ : Set ℝ) := by simp [haJ₀]
      have hJ₀_set : (J₀ : Set ℝ) = {a} := Set.Subset.antisymm hJ₀_sub_a ha_sub_J₀
      have hJ₀_eq_Icc : J₀ = Icc a a := by
        have ha_mem_J₀ : a ∈ (J₀ : Set ℝ) := haJ₀
        match J₀ with
        | Icc b c =>
          have hmem : b ≤ a ∧ a ≤ c := Set.mem_Icc.mp ha_mem_J₀
          have hsub_set : Subsingleton (Set.Icc b c) := by
            intro x y hx hy; have : x = a ∧ y = a := by
              have : (Icc b c : Set ℝ) = {a} := hJ₀_set
              rw [this] at hx hy; simp at hx hy; exact ⟨hx, hy⟩
            rcases this with ⟨hx_a, hy_a⟩; rw [hx_a, hy_a]
          rw [Set.subsingleton_Icc_iff] at hsub_set
          have hb_eq_a : b = a := le_antisymm (by nlinarith) hmem.1
          have hc_eq_a : c = a := le_antisymm hmem.2 (by nlinarith)
          simp [hb_eq_a, hc_eq_a]
        | Ico b c =>
          have hmem : b ≤ a ∧ a < c := Set.mem_Ico.mp ha_mem_J₀
          rcases exists_between hmem.2 with ⟨x, hx1, hx2⟩
          have hx_mem : x ∈ (Ico b c : Set ℝ) := ⟨by nlinarith, hx2⟩
          have : (Ico b c : Set ℝ) = {a} := hJ₀_set
          rw [this] at hx_mem; simp at hx_mem; nlinarith
        | Ioc b c =>
          have hmem : b < a ∧ a ≤ c := Set.mem_Ioc.mp ha_mem_J₀
          rcases exists_between hmem.1 with ⟨x, hx1, hx2⟩
          have hx_mem : x ∈ (Ioc b c : Set ℝ) := ⟨hx1, by nlinarith⟩
          have : (Ioc b c : Set ℝ) = {a} := hJ₀_set
          rw [this] at hx_mem; simp at hx_mem; nlinarith
        | Ioo b c =>
          have hmem : b < a ∧ a < c := Set.mem_Ioo.mp ha_mem_J₀
          rcases exists_between hmem.1 with ⟨x, hx1, hx2⟩
          have hx_mem : x ∈ (Ioo b c : Set ℝ) := ⟨hx1, by nlinarith⟩
          have : (Ioo b c : Set ℝ) = {a} := hJ₀_set
          rw [this] at hx_mem; simp at hx_mem; nlinarith
      have hI_eq_Icc : I = Icc a a := by
        match I with
        | Icc b c =>
          have hmem : b ≤ a ∧ a ≤ c := Set.mem_Icc.mp ha
          have hsubI : Subsingleton (Set.Icc b c) := hsub
          rw [Set.subsingleton_Icc_iff] at hsubI
          have hb_eq_a : b = a := le_antisymm (by nlinarith) hmem.1
          have hc_eq_a : c = a := le_antisymm hmem.2 (by nlinarith)
          simp [hb_eq_a, hc_eq_a]
        | Ico b c =>
          have ha_mem : a ∈ (Ico b c : Set ℝ) := ha
          have hmem : b ≤ a ∧ a < c := Set.mem_Ico.mp ha_mem
          rcases exists_between hmem.2 with ⟨x, hx1, hx2⟩
          have hx_mem : x ∈ (Ico b c : Set ℝ) := ⟨by nlinarith, hx2⟩
          have : (Ico b c : Set ℝ) = {a} := by
            apply Set.Subset.antisymm
            · intro x' hx'
              have hx_eq_a : x' = a := congr_arg Subtype.val (Subsingleton.elim (h := hsub) ⟨x', hx'⟩ ⟨a, ha_mem⟩)
              simp [hx_eq_a]
            · simp [ha_mem]
          rw [this] at hx_mem; simp at hx_mem; nlinarith
        | Ioc b c =>
          have ha_mem : a ∈ (Ioc b c : Set ℝ) := ha
          have hmem : b < a ∧ a ≤ c := Set.mem_Ioc.mp ha_mem
          rcases exists_between hmem.1 with ⟨x, hx1, hx2⟩
          have hx_mem : x ∈ (Ioc b c : Set ℝ) := ⟨hx1, by nlinarith⟩
          have : (Ioc b c : Set ℝ) = {a} := by
            apply Set.Subset.antisymm
            · intro x' hx'
              have hx_eq_a : x' = a := congr_arg Subtype.val (Subsingleton.elim (h := hsub) ⟨x', hx'⟩ ⟨a, ha_mem⟩)
              simp [hx_eq_a]
            · simp [ha_mem]
          rw [this] at hx_mem; simp at hx_mem; nlinarith
        | Ioo b c =>
          have ha_mem : a ∈ (Ioo b c : Set ℝ) := ha
          have hmem : b < a ∧ a < c := Set.mem_Ioo.mp ha_mem
          rcases exists_between hmem.1 with ⟨x, hx1, hx2⟩
          have hx_mem : x ∈ (Ioo b c : Set ℝ) := ⟨hx1, by nlinarith⟩
          have : (Ioo b c : Set ℝ) = {a} := by
            apply Set.Subset.antisymm
            · intro x' hx'
              have hx_eq_a : x' = a := congr_arg Subtype.val (Subsingleton.elim (h := hsub) ⟨x', hx'⟩ ⟨a, ha_mem⟩)
              simp [hx_eq_a]
            · simp [ha_mem]
          rw [this] at hx_mem; simp at hx_mem; nlinarith
      calc
        ∑ J ∈ P.intervals, α[J]ₗ = α[J₀]ₗ + ∑ J ∈ P.intervals.erase J₀, α[J]ₗ := by
          rw [Finset.add_sum_erase _ _ hJ₀_mem]
        _ = α[J₀]ₗ := by
          have : ∑ J ∈ P.intervals.erase J₀, α[J]ₗ = 0 := by
            refine Finset.sum_eq_zero (λ J hJ => ?_)
            have hJ_mem : J ∈ P.intervals := Finset.mem_of_mem_erase hJ
            have hJ_ne : J ≠ J₀ := Finset.ne_of_mem_erase hJ
            have hJ_empty : (J : Set ℝ) = ∅ := h_J_empty J hJ_mem hJ_ne
            simp [α_length_of_empty α hJ_empty]
          simp [this]
        _ = α[Icc a a]ₗ := by rw [hJ₀_eq_Icc]
        _ = α[I]ₗ := by rw [hI_eq_Icc]
  · -- I is NOT subsingleton, so I.a < I.b. Follow the structure of Partition.sum_of_length.
    simp [BoundedInterval.length_of_subsingleton, BoundedInterval.length, -Set.subsingleton_coe] at hsub
    have hex : ∃ K L : BoundedInterval, K ∈ P ∧ I.joins' L K := by
      by_cases hI' : I.b ∈ I
      . choose K hK hbK using (P.exists_unique I.b hI').exists
        have hKI : K ⊆ I := P.contains K hK
        by_cases hsubK : Subsingleton (K:Set ℝ)
        . simp_all [mem_iff]
          have hK_sub_a : (K : Set ℝ) ⊆ {I.b} := by
            intro x hx
            have hx_eq_Ib : x = I.b := hsubK hx hbK
            simp [hx_eq_Ib]
          have ha_sub_K : {I.b} ⊆ (K : Set ℝ) := by simp [hbK]
          have hK_point : (K : Set ℝ) = {I.b} := Set.Subset.antisymm hK_sub_a ha_sub_K
          have hK_Icc : K = Icc (I.b) (I.b) := by
            have hmem' : I.b ∈ (K : Set ℝ) := hbK
            cases K with
            | Ioo a b =>
              rcases Set.mem_Ioo.mp hmem' with ⟨ha_lt_Ib, hIb_lt_b⟩
              have ha_lt_b : a < b := lt_trans ha_lt_Ib hIb_lt_b
              have hsub_set : (Ioo a b : Set ℝ).Subsingleton := hsubK
              have hx : (2*a + b)/3 ∈ (Ioo a b : Set ℝ) := by
                apply Set.mem_Ioo.mpr; constructor <;> nlinarith
              have hy : (a + 2*b)/3 ∈ (Ioo a b : Set ℝ) := by
                apply Set.mem_Ioo.mpr; constructor <;> nlinarith
              have h_val_eq : (2*a + b)/3 = (a + 2*b)/3 := hsub_set hx hy
              nlinarith
            | Icc a b =>
              have ha_le_Ib : a ≤ I.b := (Set.mem_Icc.mp hmem').1
              have hIb_le_b : I.b ≤ b := (Set.mem_Icc.mp hmem').2
              have hsub_set : (Icc a b : Set ℝ).Subsingleton := hsubK
              have hsubIcc : Subsingleton (Set.Icc a b) := by simpa using hsub_set
              rw [Set.subsingleton_Icc_iff] at hsubIcc
              have ha_eq_Ib : a = I.b := by nlinarith
              have hb_eq_Ib : b = I.b := by nlinarith
              simp [ha_eq_Ib, hb_eq_Ib]
            | Ioc a b =>
              rcases Set.mem_Ioc.mp hmem' with ⟨ha_lt_Ib, hIb_le_b⟩
              have ha_lt_b : a < b := lt_of_lt_of_le ha_lt_Ib hIb_le_b
              have hsub_set : (Ioc a b : Set ℝ).Subsingleton := hsubK
              have hx : (2*a + b)/3 ∈ (Ioc a b : Set ℝ) := by
                apply Set.mem_Ioc.mpr; constructor <;> nlinarith
              have hy : (a + 2*b)/3 ∈ (Ioc a b : Set ℝ) := by
                apply Set.mem_Ioc.mpr; constructor <;> nlinarith
              have h_val_eq : (2*a + b)/3 = (a + 2*b)/3 := hsub_set hx hy
              nlinarith
            | Ico a b =>
              rcases Set.mem_Ico.mp hmem' with ⟨ha_le_Ib, hIb_lt_b⟩
              have ha_lt_b : a < b := lt_of_le_of_lt ha_le_Ib hIb_lt_b
              have hsub_set : (Ico a b : Set ℝ).Subsingleton := hsubK
              have hx : (2*a + b)/3 ∈ (Ico a b : Set ℝ) := by
                apply Set.mem_Ico.mpr; constructor <;> nlinarith
              have hy : (a + 2*b)/3 ∈ (Ico a b : Set ℝ) := by
                apply Set.mem_Ico.mpr; constructor <;> nlinarith
              have h_val_eq : (2*a + b)/3 = (a + 2*b)/3 := hsub_set hx hy
              nlinarith
          rw [hK_Icc]
          cases I with
          | Ioo _ _ => simp at hI'
          | Icc a b => refine ⟨Icc b b, Ico a b, hK, join_Ico_Icc' (by order) (by order)⟩
          | Ioc a b => refine ⟨Icc b b, Ioo a b, hK, join_Ioo_Icc' (by order) (by order)⟩
          | Ico _ _ => simp at hI'
        . simp [BoundedInterval.length_of_subsingleton, -Set.subsingleton_coe] at hsubK
          have hKI' := (K.Ioo_subset.trans hKI).trans I.subset_Icc
          simp only [subset_iff] at hKI'
          have hKb : K.b = I.b := by
            rw [le_antisymm_iff]; constructor
            · apply csSup_le_csSup bddAbove_Icc (by simp [hsubK]) at hKI'
              simp_all [csSup_Ioo hsubK, csSup_Icc (le_of_lt hsub)]
            · have := K.subset_Icc _ hbK; simp [mem_iff] at this; exact this.2
          have hKA : I.a ≤ K.a := by
            apply csInf_le_csInf bddBelow_Icc (by simp [hsubK]) at hKI'
            simp_all [csInf_Icc (le_of_lt hsub), csInf_Ioo]
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
              have hbK_simp : b₁ ∈ (Icc c₂ b₂ : Set ℝ) := by
                -- hbK : I.b ∈ K. After case splits, I.b = b₁ and K = Icc c₂ b₂.
                -- `simp` should handle this.
                simpa using hbK
              use Ioo a₁ c₂, hK
              simp_all [subset_iff]
              have hc₂_le_b₁ : c₂ ≤ b₁ := by
                have hmem_iff : b₁ ∈ (Icc c₂ b₂ : Set ℝ) := hbK_simp
                simp [mem_iff] at hmem_iff
                exact hmem_iff.1
              have hmem_c₂ : c₂ ∈ K.Ioo_subset := by
                rw [BoundedInterval.Ioo_subset]
                refine Set.mem_Ioo.mpr ⟨?_, hc₂_le_b₁.trans ?_⟩
                · have hK_a_lt_K_b : K.a < K.b := by
                    by_contra! hge
                    apply hsubK
                    rw [Set.subsingleton_Icc_iff]
                    exact hge
                  have hK_a_le_c₂ : K.a ≤ c₂ := by
                    have : K.a = c₂ := rfl
                    rw [this]
                  nlinarith
                · exact hKb.symm.le
              have hmem_Icc : c₂ ∈ Set.Icc a₁ b₁ := hKI' hmem_c₂
              grind [join_Ioo_Icc']
            | Ioc c₂ b₂ => use Ioc a₁ c₂, hK; simp_all; apply join_Ioc_Ioc' <;> order
            | Ico _ _ => simp [mem_iff, subset_iff] at *; grind
          | Ico _ _ => simp [mem_iff] at hI'
      . choose c hc hK using P.exist_right hsub hI'
        cases I with
        | Ioo a₁ b₁ =>
          obtain hK | hK := hK <;> simp_all [mem_iff]
          . use Ioo c b₁, hK, Ioc a₁ c; apply join_Ioc_Ioo' <;> tauto
          . use Ico c b₁, hK, Ioo a₁ c
            apply P.contains at hK; simp [subset_iff] at hK
            have : c ∈ Set.Ico c b₁ := by grind
            grind [join_Ioo_Ico']
        | Icc _ _ => simp [mem_iff] at hI' hsub; order
        | Ioc _ _ => simp [mem_iff] at hI' hsub; order
        | Ico a₁ b₁ =>
          obtain hK | hK := hK <;> simp_all [mem_iff]
          . use Ioo c b₁, hK, Icc a₁ c; grind [join_Icc_Ioo']
          . use Ico c b₁, hK, Ico a₁ c; grind [join_Ico_Ico']
    obtain ⟨ K, L, hK, ⟨ hJoins, hα_add ⟩ ⟩ := hex
    have : ∃ P' : Partition L, P'.intervals = P.intervals.erase K := by
      refine ⟨{
        intervals := P.intervals.erase K
        exists_unique := by
          intro x hxL
          have hxI : x ∈ (I : Set ℝ) := by
            rw [hJoins.2.1]
            exact Set.mem_union_left (K : Set ℝ) hxL
          rcases P.exists_unique x hxI with ⟨J, ⟨hJmem, hxJ⟩, huniq⟩
          have hx_not_K : x ∉ (K : Set ℝ) := by
            intro hxK; have : x ∈ (L : Set ℝ) ∩ (K : Set ℝ) := Set.mem_inter hxL hxK
            rw [hJoins.1] at this; simp at this
          have hJ_ne_K : J ≠ K := by
            intro h_eq; subst h_eq; apply hx_not_K; simpa [mem_iff] using hxJ
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
          rw [hJoins.2.1] at hxI
          rcases hxI with (hxL | hxK)
          · simpa [mem_iff] using hxL
          · exfalso
            have hxI' : x ∈ (I : Set ℝ) := by
              rw [hJoins.2.1]; exact Set.mem_union_right (L : Set ℝ) hxK
            rcases P.exists_unique x hxI' with ⟨J', ⟨hJ'mem, hxJ'⟩, huniq⟩
            have hJ_eq_K : J = K :=
              (huniq J ⟨hJmem, hxJ⟩).trans (huniq K ⟨hK, by
                simpa [mem_iff] using hxK⟩).symm
            exact hJ_ne_K hJ_eq_K
      }, rfl⟩
    choose P' hP' using this
    rw [hα_add α, ←Finset.add_sum_erase _ _ hK, ←hP', add_comm]; congr
    apply hn; simp [hP', Finset.card_erase_of_mem hK, hcard]

/-- Definition 11.8.5 (Piecewise constant RS integral). -/
noncomputable abbrev PiecewiseConstantWith.RS_integ (f:ℝ → ℝ) {I: BoundedInterval} (P: Partition I) (α: ℝ → ℝ)   :
  ℝ := ∑ J ∈ P.intervals, constant_value_on f (J:Set ℝ) * α[J]ₗ

/-- Example 11.8.6 -/
noncomputable abbrev f_11_8_6 (x:ℝ) : ℝ := if x < 2 then 4 else 2

noncomputable abbrev P_11_8_6 : Partition (Icc 1 3) :=
  (⊥: Partition (Ico 1 2)).join (⊥ : Partition (Icc 2 3))
  (join_Ico_Icc (by norm_num) (by norm_num) )

theorem f_11_8_6_RS_integ : PiecewiseConstantWith.RS_integ f_11_8_6 P_11_8_6 (fun x ↦ x^2) = 22 := by
  have h_intervals : P_11_8_6.intervals = {Ico 1 2, Icc 2 3} := by
    unfold P_11_8_6
    simp [Partition.intervals_of_join, Partition.intervals_of_bot]
  rw [PiecewiseConstantWith.RS_integ, h_intervals]
  have hIco : (fun x ↦ x^2)[Ico 1 2]ₗ = 3 := by
    have hleft2 : left_lim (fun x ↦ x^2) 2 = (fun x ↦ x^2) 2 :=
      left_lim_of_continuous ⟨1, by norm_num, Set.subset_univ _⟩ ((continuous_id.pow 2).continuousWithinAt)
    have hleft1 : left_lim (fun x ↦ x^2) 1 = (fun x ↦ x^2) 1 :=
      left_lim_of_continuous ⟨1, by norm_num, Set.subset_univ _⟩ ((continuous_id.pow 2).continuousWithinAt)
    simp [α_length, hleft2, hleft1]; norm_num
  have hIcc : (fun x ↦ x^2)[Icc 2 3]ₗ = 5 := by
    have hright : right_lim (fun x ↦ x^2) 3 = (fun x ↦ x^2) 3 :=
      right_lim_of_continuous ⟨1, by norm_num, Set.subset_univ _⟩ ((continuous_id.pow 2).continuousWithinAt)
    have hleft : left_lim (fun x ↦ x^2) 2 = (fun x ↦ x^2) 2 :=
      left_lim_of_continuous ⟨1, by norm_num, Set.subset_univ _⟩ ((continuous_id.pow 2).continuousWithinAt)
    simp [α_length, hright, hleft]; norm_num
  have hconst_Ico : constant_value_on f_11_8_6 (Ico 1 2 : Set ℝ) = 4 := by
    have h_nonempty : (Ico 1 2 : Set ℝ).Nonempty := by
      use 1.5; norm_num
    apply ConstantOn.const_eq h_nonempty
    intro x hx; rcases Set.mem_Ico.mp hx with ⟨hx1, hx2⟩
    simp [f_11_8_6, hx2]
  have hconst_Icc : constant_value_on f_11_8_6 (Icc 2 3 : Set ℝ) = 2 := by
    have h_nonempty : (Icc 2 3 : Set ℝ).Nonempty := by
      use 2; norm_num
    apply ConstantOn.const_eq h_nonempty
    intro x hx; rcases Set.mem_Icc.mp hx with ⟨hx1, hx2⟩
    simp [f_11_8_6, hx1]
  rw [Finset.sum_insert (by simp), Finset.sum_singleton]
  rw [hconst_Ico, hconst_Icc, hIco, hIcc]
  norm_num

/-- Example 11.8.7 -/
theorem PiecewiseConstantWith.RS_integ_eq_integ {f:ℝ → ℝ} {I: BoundedInterval} (P: Partition I) :RS_integ f P (fun x ↦ x) = integ f P := by
  simp [RS_integ, integ, α_len_of_id]

/-- Analogue of Proposition 11.2.13 -/
theorem PiecewiseConstantWith.RS_integ_eq {f:ℝ → ℝ} {I: BoundedInterval} {P P': Partition I}
  (hP: PiecewiseConstantWith f P) (hP': PiecewiseConstantWith f P') (α:ℝ → ℝ): RS_integ f P α = RS_integ f P' α := by
  sorry

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
  sorry

/-- Analogue of Theorem 11.2.16 (a) (Laws of integration) / Exercise 11.8.3 -/
theorem PiecewiseConstantOn.RS_integ_add {f g: ℝ → ℝ} {I: BoundedInterval}
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) {α:ℝ → ℝ} (hα: Monotone α):
  RS_integ (f + g) I α = RS_integ f I α + RS_integ g I α := by
  sorry

/-- Analogue of Theorem 11.2.16 (b) (Laws of integration) / Exercise 11.8.3 -/
theorem PiecewiseConstantOn.RS_integ_smul {f: ℝ → ℝ} {I: BoundedInterval} (c:ℝ)
  (hf: PiecewiseConstantOn f I) {α:ℝ → ℝ} (hα: Monotone α) :
  RS_integ (c • f) I α = c * RS_integ f I α
   := by
  sorry

/-- Theorem 11.8.8 (c) (Laws of RS integration) / Exercise 11.8.3 -/
theorem PiecewiseConstantOn.RS_integ_sub {f g: ℝ → ℝ} {I: BoundedInterval}
  {α:ℝ → ℝ} (hα: Monotone α)
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) :
  RS_integ (f - g) I α = RS_integ f I α - RS_integ g I α := by
  sorry

/-- Theorem 11.8.8 (d) (Laws of RS integration) / Exercise 11.8.3 -/
theorem PiecewiseConstantOn.RS_integ_of_nonneg {f: ℝ → ℝ} {I: BoundedInterval}
  {α:ℝ → ℝ} (hα: Monotone α)
  (h: ∀ x ∈ I, 0 ≤ f x) (hf: PiecewiseConstantOn f I) :
  0 ≤ RS_integ f I α := by
  sorry

/-- Theorem 11.8.8 (e) (Laws of RS integration) / Exercise 11.8.3 -/
theorem PiecewiseConstantOn.RS_integ_mono {f g: ℝ → ℝ} {I: BoundedInterval}
  {α:ℝ → ℝ} (hα: Monotone α)
  (h: ∀ x ∈ I, f x ≤ g x) (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) :
  RS_integ f I α ≤ RS_integ g I α := by
  sorry

/-- Theorem 11.8.8 (f) (Laws of RS integration) / Exercise 11.8.3 -/
theorem PiecewiseConstantOn.RS_integ_const (c: ℝ) (I: BoundedInterval) {α:ℝ → ℝ} (hα: Monotone α) :
  RS_integ (fun _ ↦ c) I α = c * α[I]ₗ := by
  sorry

/-- Theorem 11.8.8 (f') (Laws of RS integration) / Exercise 11.8.3 -/
theorem PiecewiseConstantOn.RS_integ_const' {f:ℝ → ℝ} {I: BoundedInterval}
  {α:ℝ → ℝ} (hα: Monotone α) (h: ConstantOn f I) :
  RS_integ f I α = (constant_value_on f I) * α[I]ₗ := by
  sorry

open Classical in
/-- Theorem 11.8.8 (g) (Laws of RS integration) / Exercise 11.8.3 -/
theorem PiecewiseConstantOn.RS_of_extend {I J: BoundedInterval} (hIJ: I ⊆ J)
  {f: ℝ → ℝ} (h: PiecewiseConstantOn f I) {α:ℝ → ℝ} (hα: Monotone α):
  PiecewiseConstantOn (fun x ↦ if x ∈ I then f x else 0) J := by
  sorry

open Classical in
/-- Theorem 11.8.8 (g') (Laws of RS integration) / Exercise 11.8.3 -/
theorem PiecewiseConstantOn.RS_integ_of_extend {I J: BoundedInterval} (hIJ: I ⊆ J)
  {f: ℝ → ℝ} (h: PiecewiseConstantOn f I) {α:ℝ → ℝ} (hα: Monotone α):
  RS_integ (fun x ↦ if x ∈ I then f x else 0) J α = RS_integ f I α := by
  sorry

/-- Theorem 11.8.8 (h) (Laws of RS integration) / Exercise 11.8.3 -/
theorem PiecewiseConstantOn.RS_integ_of_join {I J K: BoundedInterval} (hIJK: K.joins' I J)
  {f: ℝ → ℝ} (h: PiecewiseConstantOn f K) {α:ℝ → ℝ} (hα: Monotone α):
  RS_integ f K α = RS_integ f I α + RS_integ f J α := by
  sorry

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
  sorry

theorem lower_RS_integral_eq_lower_integral (f:ℝ → ℝ) (I: BoundedInterval) :
  lower_RS_integral f I (fun x ↦ x) = lower_integral f I := by
  sorry

theorem RS_integ_eq_integ (f:ℝ → ℝ) (I: BoundedInterval) :
  RS_integ f I (fun x ↦ x) = integ f I := by
  sorry

theorem RS_IntegrableOn_iff_IntegrableOn (f:ℝ → ℝ) (I: BoundedInterval) :
  RS_IntegrableOn f I (fun x ↦ x) ↔ IntegrableOn f I := by
  sorry

/-- Exercise 11.8.4 -/
theorem RS_integ_of_uniform_cts {I: BoundedInterval} {f:ℝ → ℝ} (hf: UniformContinuousOn f I)
 {α:ℝ → ℝ} (hα: Monotone α):
  RS_IntegrableOn f I α := by
  sorry

/-- Exercise 11.8.5 -/
theorem RS_integ_with_sign (f:ℝ → ℝ) (hf: ContinuousOn f (.Icc (-1) 1)) : RS_IntegrableOn f (Icc (-1) 1) Real.sign ∧ RS_integ f (Icc (-1) 1) Real.sign = 2 * f 0 := by
  sorry

/-- Analogue of Lemma 11.3.7 -/
theorem RS_integ_of_piecewise_const {f:ℝ → ℝ} {I: BoundedInterval} (hf: PiecewiseConstantOn f I)
  {α: ℝ → ℝ} (hα: Monotone α):
  RS_IntegrableOn f I α ∧ RS_integ f I α = PiecewiseConstantOn.RS_integ f I α := by
  sorry

end Chapter11
