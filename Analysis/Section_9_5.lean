import Mathlib.Tactic
import Mathlib.Data.Real.Sign
import Analysis.Section_9_3
import Analysis.Section_9_4

/-!
# Analysis I, Section 9.5: Left and right limits

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Left and right limits.
-/

namespace Chapter9

/-- Definition 9.5.1.  We give left and right limits the "junk" value of 0 if the limit does not exist. -/
abbrev RightLimitExists (X: Set ℝ) (f: ℝ → ℝ) (x₀:ℝ) : Prop := ∃ L, (nhdsWithin x₀ (X ∩ .Ioi x₀)).Tendsto f (nhds L)

open Classical in
noncomputable abbrev right_limit (X: Set ℝ) (f: ℝ → ℝ) (x₀:ℝ) : ℝ := if h : RightLimitExists X f x₀ then h.choose else 0

abbrev LeftLimitExists (X: Set ℝ) (f: ℝ → ℝ) (x₀:ℝ) : Prop := ∃ L, (nhdsWithin x₀ (X ∩ .Iio x₀)).Tendsto f (nhds L)

open Classical in
noncomputable abbrev left_limit (X: Set ℝ) (f: ℝ → ℝ) (x₀:ℝ) : ℝ := if h: LeftLimitExists X f x₀ then h.choose else 0

theorem right_limit.eq {X: Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} {L:ℝ} (had: AdherentPt x₀ (X ∩ .Ioi x₀))
  (h: (nhdsWithin x₀ (X ∩ .Ioi x₀)).Tendsto f (nhds L)) : RightLimitExists X f x₀ ∧ right_limit X f x₀ = L := by
  have h' : RightLimitExists X f x₀ := by use L
  simp [right_limit, h']
  have hne : (nhdsWithin x₀ (X ∩ .Ioi x₀)).NeBot := by
    rwa [←mem_closure_iff_nhdsWithin_neBot, closure_def']
  exact tendsto_nhds_unique h'.choose_spec h

theorem left_limit.eq {X: Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} {L:ℝ} (had: AdherentPt x₀ (X ∩ .Iio x₀))
  (h: (nhdsWithin x₀ (X ∩ .Iio x₀)).Tendsto f (nhds L)) : LeftLimitExists X f x₀ ∧ left_limit X f x₀ = L := by
  have h' : LeftLimitExists X f x₀ := by use L
  simp [left_limit, h']
  have hne : (nhdsWithin x₀ (X ∩ .Iio x₀)).NeBot := by
    rwa [←mem_closure_iff_nhdsWithin_neBot, closure_def']
  exact tendsto_nhds_unique h'.choose_spec h

theorem right_limit.eq' {X: Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} (h: RightLimitExists X f x₀) :
  (nhdsWithin x₀ (X ∩ .Ioi x₀)).Tendsto f (nhds (right_limit X f x₀)) := by
  simp [right_limit, h]; exact h.choose_spec

theorem left_limit.eq' {X: Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} (h: LeftLimitExists X f x₀) :
  (nhdsWithin x₀ (X ∩ .Iio x₀)).Tendsto f (nhds (left_limit X f x₀)) := by
  simp [left_limit, h]; exact h.choose_spec

/-- Example 9.5.2.  The second part of this example is no longer operative as we assign "junk" values to our functions instead of leaving them undefined. -/
example : right_limit .univ Real.sign 0 = 1 := by
  have h_adv : AdherentPt 0 (.univ ∩ .Ioi 0) := by
    have h : AdherentPt 0 (.Ioi (0 : ℝ)) := by
      intro ε hε
      have h_pos : ε/2 > 0 := by nlinarith
      refine ⟨ε/2, h_pos, ?_⟩
      calc
        |0 - (ε/2)| = |ε/2| := by
          have : 0 - (ε/2) = -(ε/2) := by ring
          rw [this, abs_neg]
        _ = ε/2 := abs_of_pos h_pos
        _ ≤ ε := by nlinarith
    simpa using h
  have h_conv : (nhdsWithin 0 (.univ ∩ .Ioi 0)).Tendsto Real.sign (nhds 1) := by
    have := Convergesto.sign_right
    rw [Convergesto.iff] at this
    simpa using this
  exact (right_limit.eq h_adv h_conv).2

example : left_limit .univ Real.sign 0 = -1 := by
  have h_adv : AdherentPt 0 (.univ ∩ .Iio 0) := by
    have h : AdherentPt 0 (.Iio (0 : ℝ)) := by
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
    simpa using h
  have h_conv : (nhdsWithin 0 (.univ ∩ .Iio 0)).Tendsto Real.sign (nhds (-1)) := by
    have := Convergesto.sign_left
    rw [Convergesto.iff] at this
    simpa using this
  exact (left_limit.eq h_adv h_conv).2

theorem right_limit.conv {X: Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} (had: AdherentPt x₀ (X ∩ .Ioi x₀))
  (h: RightLimitExists X f x₀)
  (a:ℕ → ℝ) (ha: ∀ n, a n ∈ X ∩ .Ioi x₀)
  (hconv: Filter.atTop.Tendsto a (nhds x₀)) :
  Filter.atTop.Tendsto (fun n ↦ f (a n)) (nhds (right_limit X f x₀)) := by
  choose L hL using h
  apply Convergesto.comp _ ha hconv
  rwa [Convergesto.iff, (eq had hL).2]

theorem left_limit.conv {X: Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} (had: AdherentPt x₀ (X ∩ .Iio x₀))
  (h: LeftLimitExists X f x₀)
  (a:ℕ → ℝ) (ha: ∀ n, a n ∈ X ∩ .Iio x₀)
  (hconv: Filter.atTop.Tendsto a (nhds x₀)) :
  Filter.atTop.Tendsto (fun n ↦ f (a n)) (nhds (left_limit X f x₀)) := by
  choose L hL using h
  apply Convergesto.comp _ ha hconv
  rwa [Convergesto.iff, (eq had hL).2]

/-- Proposition 9.5.3 -/
theorem ContinuousAt.iff_eq_left_right_limit {X: Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} (h: x₀ ∈ X)
  (had_left: AdherentPt x₀ (X ∩ .Iio x₀)) (had_right: AdherentPt x₀ (X ∩ .Ioi x₀)) :
  ContinuousWithinAt f X x₀ ↔ (RightLimitExists X f x₀ ∧ right_limit X f x₀ = f x₀) ∧ (LeftLimitExists X f x₀ ∧ left_limit X f x₀ = f x₀) := by
  -- This proof is written to follow the structure of the original text.
  constructor
  · intro hcont
    rw [ContinuousWithinAt.iff] at hcont
    have hconv : (nhdsWithin x₀ X).Tendsto f (nhds (f x₀)) := by
      rwa [Convergesto.iff] at hcont
    have h_sub_right : X ∩ .Ioi x₀ ⊆ X := fun x hx => hx.1
    have h_sub_left : X ∩ .Iio x₀ ⊆ X := fun x hx => hx.1
    have hconv_right : (nhdsWithin x₀ (X ∩ .Ioi x₀)).Tendsto f (nhds (f x₀)) :=
      hconv.mono_left (nhdsWithin_mono x₀ h_sub_right)
    have hconv_left : (nhdsWithin x₀ (X ∩ .Iio x₀)).Tendsto f (nhds (f x₀)) :=
      hconv.mono_left (nhdsWithin_mono x₀ h_sub_left)
    have h_right := right_limit.eq had_right hconv_right
    have h_left := left_limit.eq had_left hconv_left
    exact ⟨h_right, h_left⟩
  intro ⟨ ⟨ hre, hright⟩, ⟨ hle, lheft ⟩ ⟩
  set L := f x₀
  have := (ContinuousWithinAt.tfae X f x₀).out 0 2
  rw [this]
  intro ε hε
  apply right_limit.eq' at hre
  apply left_limit.eq' at hle
  rw [hright, ←Convergesto.iff] at hre
  rw [lheft, ←Convergesto.iff] at hle
  simp [Convergesto, Real.CloseNear, Real.CloseFn] at hre hle
  choose δ_plus hδ_plus hre using hre ε hε
  choose δ_minus hδ_minus hle using hle ε hε
  use min δ_plus δ_minus, (by positivity)
  intro x hx hxx₀
  obtain hlt | rfl | hgt := lt_trichotomy x x₀
  · have hx_lt_minus : |x - x₀| < δ_minus :=
      hxx₀.trans_le (min_le_right _ _)
    have hx_in_Ioo : x ∈ Set.Ioo (x₀ - δ_minus) (x₀ + δ_minus) := by
      rcases abs_lt.mp hx_lt_minus with ⟨hxl, hxr⟩
      exact Set.mem_Ioo.mpr ⟨by nlinarith, by nlinarith⟩
    apply hle x hx hlt hx_in_Ioo.1 hx_in_Ioo.2
  · simpa
  · have hx_lt_plus : |x - x₀| < δ_plus :=
      hxx₀.trans_le (min_le_left _ _)
    have hx_in_Ioo : x ∈ Set.Ioo (x₀ - δ_plus) (x₀ + δ_plus) := by
      rcases abs_lt.mp hx_lt_plus with ⟨hxl, hxr⟩
      exact Set.mem_Ioo.mpr ⟨by nlinarith, by nlinarith⟩
    apply hre x hx hgt hx_in_Ioo.1 hx_in_Ioo.2

abbrev HasJumpDiscontinuity (X: Set ℝ) (f: ℝ → ℝ) (x₀:ℝ) : Prop :=
  RightLimitExists X f x₀ ∧ LeftLimitExists X f x₀ ∧ right_limit X f x₀ ≠ left_limit X f x₀

example : HasJumpDiscontinuity .univ Real.sign 0 := by
  have h_adv_right : AdherentPt 0 (.univ ∩ .Ioi 0) := by
    have h : AdherentPt 0 (.Ioi (0 : ℝ)) := by
      intro ε hε
      have h_pos : ε/2 > 0 := by nlinarith
      refine ⟨ε/2, h_pos, ?_⟩
      calc
        |0 - (ε/2)| = |ε/2| := by
          have : 0 - (ε/2) = -(ε/2) := by ring
          rw [this, abs_neg]
        _ = ε/2 := abs_of_pos h_pos
        _ ≤ ε := by nlinarith
    simpa using h
  have h_adv_left : AdherentPt 0 (.univ ∩ .Iio 0) := by
    have h : AdherentPt 0 (.Iio (0 : ℝ)) := by
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
    simpa using h
  have h_right_conv : (nhdsWithin 0 (.univ ∩ .Ioi 0)).Tendsto Real.sign (nhds 1) := by
    have := Convergesto.sign_right
    rw [Convergesto.iff] at this
    simpa using this
  have h_left_conv : (nhdsWithin 0 (.univ ∩ .Iio 0)).Tendsto Real.sign (nhds (-1)) := by
    have := Convergesto.sign_left
    rw [Convergesto.iff] at this
    simpa using this
  have h_right_val : right_limit .univ Real.sign 0 = 1 := (right_limit.eq h_adv_right h_right_conv).2
  have h_left_val : left_limit .univ Real.sign 0 = -1 := (left_limit.eq h_adv_left h_left_conv).2
  refine ⟨⟨1, h_right_conv⟩, ⟨-1, h_left_conv⟩, ?_⟩
  rw [h_right_val, h_left_val]
  norm_num

abbrev HasRemovableDiscontinuity (X: Set ℝ) (f: ℝ → ℝ) (x₀:ℝ) : Prop :=
  RightLimitExists X f x₀ ∧ LeftLimitExists X f x₀ ∧ right_limit X f x₀ = left_limit X f x₀
  ∧ right_limit X f x₀ ≠ f x₀

example : HasRemovableDiscontinuity .univ f_9_3_17 0 := by
  have h_adv_right : AdherentPt 0 (.univ ∩ .Ioi 0) := by
    have h : AdherentPt 0 (.Ioi (0 : ℝ)) := by
      intro ε hε
      have h_pos : ε/2 > 0 := by nlinarith
      refine ⟨ε/2, h_pos, ?_⟩
      calc
        |0 - (ε/2)| = |ε/2| := by
          have : 0 - (ε/2) = -(ε/2) := by ring
          rw [this, abs_neg]
        _ = ε/2 := abs_of_pos h_pos
        _ ≤ ε := by nlinarith
    simpa using h
  have h_adv_left : AdherentPt 0 (.univ ∩ .Iio 0) := by
    have h : AdherentPt 0 (.Iio (0 : ℝ)) := by
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
    simpa using h
  have h_right_conv : (nhdsWithin 0 (.univ ∩ .Ioi 0)).Tendsto f_9_3_17 (nhds 0) := by
    rw [← Convergesto.iff]
    apply Convergesto.f_9_3_17_remove.restrict
    intro x hx
    rcases hx with ⟨hx_univ, hx_Ioi⟩
    have hx_pos : x > 0 := hx_Ioi
    have hx_ne_zero : x ≠ 0 := by linarith
    exact ⟨hx_univ, hx_ne_zero⟩
  have h_left_conv : (nhdsWithin 0 (.univ ∩ .Iio 0)).Tendsto f_9_3_17 (nhds 0) := by
    rw [← Convergesto.iff]
    apply Convergesto.f_9_3_17_remove.restrict
    intro x hx
    rcases hx with ⟨hx_univ, hx_Iio⟩
    have hx_neg : x < 0 := hx_Iio
    have hx_ne_zero : x ≠ 0 := by linarith
    exact ⟨hx_univ, hx_ne_zero⟩
  have h_right_val : right_limit .univ f_9_3_17 0 = 0 := (right_limit.eq h_adv_right h_right_conv).2
  have h_left_val : left_limit .univ f_9_3_17 0 = 0 := (left_limit.eq h_adv_left h_left_conv).2
  refine ⟨⟨0, h_right_conv⟩, ⟨0, h_left_conv⟩, ?_, ?_⟩
  · rw [h_right_val, h_left_val]
  · rw [h_right_val]
    dsimp [f_9_3_17]
    norm_num

private lemma no_right_limit_one_div_at_zero : ¬ RightLimitExists Set.univ (fun x : ℝ ↦ 1/x) 0 := by
  intro h
  rcases h with ⟨L, hL⟩
  rcases Metric.tendsto_nhdsWithin_nhds.mp hL 1 (by norm_num) with ⟨δ, hδ, h⟩
  set t := min (δ/2) (1 / (|L| + 1)) with ht
  have ht_pos : t > 0 := by
    refine lt_min_iff.mpr ⟨by nlinarith, ?_⟩
    positivity
  have hx_mem : t ∈ Set.univ ∩ Set.Ioi 0 := ⟨trivial, ht_pos⟩
  have hx_dist : dist t 0 < δ := by
    rw [Real.dist_eq, sub_zero]
    rw [abs_of_pos ht_pos]
    have ht_le_δ2 : t ≤ δ/2 := min_le_left _ _
    nlinarith
  have h_contra := h (x := t) hx_mem hx_dist
  rw [Real.dist_eq] at h_contra
  have h_one_div_t_large : 1/t ≥ |L| + 1 := by
    have ht_small : t ≤ 1 / (|L| + 1) := min_le_right _ _
    have ha_pos : 0 < 1 / (|L| + 1) := by positivity
    calc
      |L| + 1 = 1 / (1 / (|L| + 1)) := by
        field_simp [show |L| + 1 ≠ 0 from by nlinarith [abs_nonneg L]]
      _ ≤ 1/t := (one_div_le_one_div ha_pos ht_pos).mpr ht_small
  have h_bound : |1/t - L| ≥ 1 := by
    have h_rev : |1/t| - |L| ≤ |1/t - L| := abs_sub_abs_le_abs_sub (1/t) L
    have h_abs_one_div : |1/t| = 1/t := abs_of_pos (by positivity)
    rw [h_abs_one_div] at h_rev
    nlinarith
  linarith

example : ¬ HasRemovableDiscontinuity .univ (fun x ↦ 1/x) 0 := by
  intro h
  rcases h with ⟨h_right, _, _, _⟩
  exact no_right_limit_one_div_at_zero h_right

example : ¬ HasJumpDiscontinuity .univ (fun x ↦ 1/x) 0 := by
  intro h
  rcases h with ⟨h_right, _, _⟩
  exact no_right_limit_one_div_at_zero h_right

/- Exercise 9.5.1: Write down a definition of what it would mean for a limit of a function to be `+∞` or `-∞`, apply to `fun x ↦ 1/x`, and state and prove a version of Proposition 9.3.9. -/


end Chapter9
