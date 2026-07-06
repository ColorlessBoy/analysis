import Mathlib.Tactic
import Analysis.Section_11_1

/-!
# Analysis I, Section 11.2: Piecewise constant functions

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Piecewise constant functions.
- The piecewise constant integral.

-/

namespace Chapter11
open BoundedInterval

/-- Definition 11.2.1 -/
abbrev Constant {X Y:Type} (f: X → Y) : Prop := ∃ c, ∀ x, f x = c

open Classical in
noncomputable abbrev constant_value {X Y:Type} [hY: Nonempty Y] (f:X → Y) : Y :=
  if h: Constant f then h.choose else hY.some

theorem Constant.eq {X Y:Type} {f: X → Y} [Nonempty Y] (h: Constant f) (x:X) :
  f x = constant_value f := by simp [constant_value, h]; apply h.choose_spec

theorem Constant.of_const {X Y:Type} {f:X → Y} {c:Y} (h: ∀ x, f x = c) :
  Constant f := by use c

theorem Constant.const_eq {X Y:Type} {f:X → Y} [hX: Nonempty X] [Nonempty Y] {c:Y} (h: ∀ x, f x = c) :
  constant_value f = c := by rw [←eq (of_const h) hX.some, h hX.some]

theorem Constant.of_subsingleton {X Y:Type} [hs: Subsingleton X] [hY: Nonempty Y] {f:X → Y} :
  Constant f := by
  by_cases h:Nonempty X
  . use f h.some; intros; congr; exact hs.elim _ h.some
  simp at h; exact ⟨ hY.some, h.elim ⟩

abbrev ConstantOn (f: ℝ → ℝ) (X: Set ℝ) : Prop := Constant (fun x : X ↦ f ↑x)

noncomputable abbrev constant_value_on (f:ℝ → ℝ) (X: Set ℝ) : ℝ := constant_value (fun x : X ↦ f ↑x)

theorem ConstantOn.eq {f: ℝ → ℝ} {X: Set ℝ} (h: ConstantOn f X) {x:ℝ} (hx: x ∈ X) :
  f x = constant_value_on f X := by
  convert Constant.eq h ⟨ _, hx ⟩

theorem ConstantOn.of_const {f:ℝ → ℝ} {X: Set ℝ} {c:ℝ} (h: ∀ x ∈ X, f x = c) :
  ConstantOn f X := ⟨ c, by grind ⟩

theorem ConstantOn.of_const' (c:ℝ) (X:Set ℝ): ConstantOn (fun _ ↦ c) X := of_const (c := c) (by simp)

theorem ConstantOn.const_eq {f:ℝ → ℝ} {X: Set ℝ} (hX: X.Nonempty) {c:ℝ} (h: ∀ x ∈ X, f x = c) :
  constant_value_on f X = c := by
    rw [←eq (of_const h) hX.some_mem, h _ hX.some_mem]

theorem ConstantOn.congr {f g: ℝ → ℝ} {X: Set ℝ} (h: ∀ x ∈ X, f x = g x) : ConstantOn f X ↔ ConstantOn g X := by
  simp_rw [ConstantOn, iff_iff_eq]; congr; grind

theorem ConstantOn.congr' {f g: ℝ → ℝ} {X: Set ℝ} (hf: ConstantOn f X) (h: ∀ x ∈ X, f x = g x) : ConstantOn g X := (congr h).mp hf

theorem ConstantOn.of_subsingleton {f: ℝ → ℝ} {X: Set ℝ} [Subsingleton X] :
  ConstantOn f X := Constant.of_subsingleton

theorem constant_value_on_congr {f g: ℝ → ℝ} {X: Set ℝ} (h: ∀ x ∈ X, f x = g x) :
  constant_value_on f X = constant_value_on g X := by
  simp [constant_value_on]; congr; grind

/-- Definition 11.2.3 (Piecewise constant functions I) -/
abbrev PiecewiseConstantWith (f:ℝ → ℝ) {I: BoundedInterval} (P: Partition I) : Prop := ∀ J ∈ P, ConstantOn f (J:Set ℝ)

theorem PiecewiseConstantWith.def (f:ℝ → ℝ) {I: BoundedInterval} {P: Partition I} :
  PiecewiseConstantWith f P ↔ ∀ J ∈ P, ∃ c, ∀ x ∈ J, f x = c := by
    simp [PiecewiseConstantWith, ConstantOn, Constant, mem_iff]

theorem PiecewiseConstantWith.congr {f g:ℝ → ℝ} {I: BoundedInterval} {P: Partition I}
  (h: ∀ x ∈ (I:Set ℝ), f x = g x) :
  PiecewiseConstantWith f P ↔ PiecewiseConstantWith g P := by
  simp [PiecewiseConstantWith]; peel with J hJ
  apply ConstantOn.congr; have := P.contains _ hJ; grind [subset_iff]

/-- Definition 11.2.5 (Piecewise constant functions I) -/
abbrev PiecewiseConstantOn (f:ℝ → ℝ) (I: BoundedInterval) : Prop := ∃ P : Partition I, PiecewiseConstantWith f P

theorem PiecewiseConstantOn.def (f:ℝ → ℝ) (I: BoundedInterval):
  PiecewiseConstantOn f I ↔ ∃ P : Partition I, ∀ J ∈ P, ConstantOn f (J:Set ℝ) := by rfl

theorem PiecewiseConstantOn.congr {f g: ℝ → ℝ} {I: BoundedInterval} (h: ∀ x ∈ (I:Set ℝ), f x = g x) :
  PiecewiseConstantOn f I ↔ PiecewiseConstantOn g I := by
  simp_rw [PiecewiseConstantOn, PiecewiseConstantWith.congr h]

theorem PiecewiseConstantOn.congr' {f g: ℝ → ℝ} {I: BoundedInterval} (hf: PiecewiseConstantOn f I) (h: ∀ x ∈ (I:Set ℝ), f x = g x) : PiecewiseConstantOn g I := (congr h).mp hf

/-- Example 11.2.4 / Example 11.2.6 -/
noncomputable abbrev f_11_2_4 : ℝ → ℝ := fun x ↦
  if x < 1 then 0 else  -- junk value
    if x < 3 then 7 else
      if x = 3 then 4 else
        if x < 6 then 5 else
          if x = 6 then 2 else
            0 -- junk value

example : PiecewiseConstantOn f_11_2_4 (Icc 1 6) := by
  use Partition.mk { Ico 1 3, Icc 3 3, Ioo 3 6, Icc 6 6} ?_ ?_
  . intro J hJ
    have hJ_finset : J ∈ ({Ico 1 3, Icc 3 3, Ioo 3 6, Icc 6 6} : Finset BoundedInterval) := hJ
    have hJ' : J = Ico 1 3 ∨ J = Icc 3 3 ∨ J = Ioo 3 6 ∨ J = Icc 6 6 := by
      simpa using hJ_finset
    rcases hJ' with (rfl|rfl|rfl|rfl)
    · refine ⟨7, λ x => ?_⟩
      have hx_ge1 : 1 ≤ x.1 := x.2.1
      have hx_lt3 : x.1 < 3 := x.2.2
      have hx_not_lt1 : ¬ x.1 < 1 := by nlinarith
      simp [f_11_2_4, hx_not_lt1, hx_lt3]
    · refine ⟨4, λ x => ?_⟩
      have hx_eq3 : x.1 = 3 := le_antisymm x.2.2 x.2.1
      dsimp
      rw [hx_eq3]
      norm_num [f_11_2_4]
    · refine ⟨5, λ x => ?_⟩
      have hx_gt3 : 3 < x.1 := x.2.1
      have hx_lt6 : x.1 < 6 := x.2.2
      have hx_not_lt1 : ¬ x.1 < 1 := by nlinarith
      have hx_not_lt3 : ¬ x.1 < 3 := by nlinarith
      have hx_not_eq3 : x.1 ≠ 3 := by nlinarith
      simp [f_11_2_4, hx_not_lt1, hx_not_lt3, hx_lt6, hx_not_eq3]
    · refine ⟨2, λ x => ?_⟩
      have hx_eq6 : x.1 = 6 := le_antisymm x.2.2 x.2.1
      dsimp
      rw [hx_eq6]
      norm_num [f_11_2_4]
  . intro x hx
    have hx1 : 1 ≤ x := hx.1
    have hx6 : x ≤ 6 := hx.2
    by_cases hx3 : x < 3
    · refine ⟨Ico 1 3, ⟨by simp, ⟨hx1, hx3⟩⟩, ?_⟩
      intro K ⟨hKmem, hxK⟩
      have hKcases : K = Ico 1 3 ∨ K = Icc 3 3 ∨ K = Ioo 3 6 ∨ K = Icc 6 6 := by
        simpa using hKmem
      rcases hKcases with (rfl|rfl|rfl|rfl)
      · rfl
      · exfalso; nlinarith [hxK.1, hx3]
      · exfalso; nlinarith [hxK.1, hx3]
      · exfalso; nlinarith [hxK.1, hx3]
    · by_cases hx_eq3 : x = 3
      · subst x
        refine ⟨Icc 3 3, ⟨by simp, ?_⟩, ?_⟩
        · apply Set.mem_Icc.mpr; norm_num
        · intro K ⟨hKmem, hxK⟩
          have hKcases : K = Ico 1 3 ∨ K = Icc 3 3 ∨ K = Ioo 3 6 ∨ K = Icc 6 6 := by
            simpa using hKmem
          rcases hKcases with (rfl|rfl|rfl|rfl)
          · exfalso; nlinarith [hxK.2]
          · rfl
          · exfalso; nlinarith [hxK.1]
          · exfalso; nlinarith [hxK.1]
      · have hx_gt3 : 3 < x := by
          have hxge3 : 3 ≤ x := by
            by_contra! h
            exact hx3 h
          by_contra! h
          have : x = 3 := by nlinarith
          exact hx_eq3 this
        by_cases hx_lt6 : x < 6
        · refine ⟨Ioo 3 6, ⟨by simp, ⟨hx_gt3, hx_lt6⟩⟩, ?_⟩
          intro K ⟨hKmem, hxK⟩
          have hKcases : K = Ico 1 3 ∨ K = Icc 3 3 ∨ K = Ioo 3 6 ∨ K = Icc 6 6 := by
            simpa using hKmem
          rcases hKcases with (rfl|rfl|rfl|rfl)
          · exfalso; nlinarith [hxK.2, hx_gt3]
          · exfalso; nlinarith [hxK.2, hx_gt3]
          · rfl
          · exfalso; nlinarith [hxK.1, hx_lt6]
        · have hx_eq6 : x = 6 := by nlinarith
          subst x
          refine ⟨Icc 6 6, ⟨by simp, ?_⟩, ?_⟩
          · apply Set.mem_Icc.mpr; norm_num
          · intro K ⟨hKmem, hxK⟩
            have hKcases : K = Ico 1 3 ∨ K = Icc 3 3 ∨ K = Ioo 3 6 ∨ K = Icc 6 6 := by
              simpa using hKmem
            rcases hKcases with (rfl|rfl|rfl|rfl)
            · exfalso; nlinarith [hxK.2]
            · exfalso; nlinarith [hxK.2]
            · exfalso; nlinarith [hxK.2]
            · rfl
  intro J hJ
  simp at hJ
  rcases hJ with (rfl|rfl|rfl|rfl) <;>
    rw [BoundedInterval.subset_iff] <;>
    intro x hx <;>
    simp at hx <;>
    simp <;>
    exact ⟨by nlinarith, by nlinarith⟩

example : PiecewiseConstantOn f_11_2_4 (Icc 1 6) := by
  use Partition.mk { Ico 1 2, Icc 2 2, Ioo 2 3, Icc 3 3, Ioo 3 5, Ico 5 6, Icc 6 6} ?_ ?_
  . intro J hJ
    have hJ_finset : J ∈ ({Ico 1 2, Icc 2 2, Ioo 2 3, Icc 3 3, Ioo 3 5, Ico 5 6, Icc 6 6} : Finset BoundedInterval) := hJ
    have hJ' : J = Ico 1 2 ∨ J = Icc 2 2 ∨ J = Ioo 2 3 ∨ J = Icc 3 3 ∨ J = Ioo 3 5 ∨ J = Ico 5 6 ∨ J = Icc 6 6 := by
      simpa using hJ_finset
    rcases hJ' with (rfl|rfl|rfl|rfl|rfl|rfl|rfl)
    · refine ⟨7, λ x => ?_⟩
      have hx_ge1 : 1 ≤ x.1 := x.2.1
      have hx_lt2 : x.1 < 2 := x.2.2
      have hx_lt3 : x.1 < 3 := by nlinarith
      have hx_not_lt1 : ¬ x.1 < 1 := by nlinarith
      simp [f_11_2_4, hx_not_lt1, hx_lt3]
    · refine ⟨7, λ x => ?_⟩
      have hx_eq2 : x.1 = 2 := le_antisymm x.2.2 x.2.1
      dsimp; rw [hx_eq2]; norm_num [f_11_2_4]
    · refine ⟨7, λ x => ?_⟩
      have hx_gt2 : 2 < x.1 := x.2.1
      have hx_lt3 : x.1 < 3 := x.2.2
      have hx_not_lt1 : ¬ x.1 < 1 := by nlinarith
      simp [f_11_2_4, hx_not_lt1, hx_lt3]
    · refine ⟨4, λ x => ?_⟩
      have hx_eq3 : x.1 = 3 := le_antisymm x.2.2 x.2.1
      dsimp; rw [hx_eq3]; norm_num [f_11_2_4]
    · refine ⟨5, λ x => ?_⟩
      have hx_gt3 : 3 < x.1 := x.2.1
      have hx_lt5 : x.1 < 5 := x.2.2
      have hx_lt6 : x.1 < 6 := by nlinarith
      have hx_not_lt1 : ¬ x.1 < 1 := by nlinarith
      have hx_not_lt3 : ¬ x.1 < 3 := by nlinarith
      have hx_not_eq3 : x.1 ≠ 3 := by nlinarith
      simp [f_11_2_4, hx_not_lt1, hx_not_lt3, hx_not_eq3, hx_lt6]
    · refine ⟨5, λ x => ?_⟩
      have hx_ge5 : 5 ≤ x.1 := x.2.1
      have hx_lt6 : x.1 < 6 := x.2.2
      have hx_not_lt1 : ¬ x.1 < 1 := by nlinarith
      have hx_not_lt3 : ¬ x.1 < 3 := by nlinarith
      have hx_not_eq3 : x.1 ≠ 3 := by nlinarith
      simp [f_11_2_4, hx_not_lt1, hx_not_lt3, hx_not_eq3, hx_lt6]
    · refine ⟨2, λ x => ?_⟩
      have hx_eq6 : x.1 = 6 := le_antisymm x.2.2 x.2.1
      dsimp; rw [hx_eq6]; norm_num [f_11_2_4]
  . intro x hx
    have hx1 : 1 ≤ x := hx.1
    have hx6 : x ≤ 6 := hx.2
    by_cases hx2 : x < 2
    · refine ⟨Ico 1 2, ⟨by simp, ⟨hx1, hx2⟩⟩, ?_⟩
      intro K ⟨hKmem, hxK⟩
      have hKcases : K = Ico 1 2 ∨ K = Icc 2 2 ∨ K = Ioo 2 3 ∨ K = Icc 3 3 ∨ K = Ioo 3 5 ∨ K = Ico 5 6 ∨ K = Icc 6 6 := by
        simpa using hKmem
      rcases hKcases with (rfl|rfl|rfl|rfl|rfl|rfl|rfl)
      · rfl
      · exfalso; nlinarith [hxK.1, hxK.2, hx2]
      · exfalso; nlinarith [hxK.1, hxK.2, hx2]
      · exfalso; nlinarith [hxK.1, hxK.2, hx2]
      · exfalso; nlinarith [hxK.1, hxK.2, hx2]
      · exfalso; nlinarith [hxK.1, hxK.2, hx2]
      · exfalso; nlinarith [hxK.1, hxK.2, hx2]
    · by_cases hx_eq2 : x = 2
      · subst x
        refine ⟨Icc 2 2, ⟨by simp, ?_⟩, ?_⟩
        · apply Set.mem_Icc.mpr; norm_num
        · intro K ⟨hKmem, hxK⟩
          have hKcases : K = Ico 1 2 ∨ K = Icc 2 2 ∨ K = Ioo 2 3 ∨ K = Icc 3 3 ∨ K = Ioo 3 5 ∨ K = Ico 5 6 ∨ K = Icc 6 6 := by
            simpa using hKmem
          rcases hKcases with (rfl|rfl|rfl|rfl|rfl|rfl|rfl)
          · exfalso; nlinarith [hxK.1, hxK.2]
          · rfl
          · exfalso; nlinarith [hxK.1, hxK.2]
          · exfalso; nlinarith [hxK.1, hxK.2]
          · exfalso; nlinarith [hxK.1, hxK.2]
          · exfalso; nlinarith [hxK.1, hxK.2]
          · exfalso; nlinarith [hxK.1, hxK.2]
      · by_cases hx3 : x < 3
        · have hx_gt2 : 2 < x := by
            have hx_ge2 : 2 ≤ x := by
              by_contra! h
              exact hx2 h
            by_contra! h
            have : x = 2 := by nlinarith
            exact hx_eq2 this
          refine ⟨Ioo 2 3, ⟨by simp, ⟨hx_gt2, hx3⟩⟩, ?_⟩
          intro K ⟨hKmem, hxK⟩
          have hKcases : K = Ico 1 2 ∨ K = Icc 2 2 ∨ K = Ioo 2 3 ∨ K = Icc 3 3 ∨ K = Ioo 3 5 ∨ K = Ico 5 6 ∨ K = Icc 6 6 := by
            simpa using hKmem
          rcases hKcases with (rfl|rfl|rfl|rfl|rfl|rfl|rfl)
          · exfalso; nlinarith [hxK.1, hxK.2, hx_gt2, hx3]
          · exfalso; nlinarith [hxK.1, hxK.2, hx_gt2, hx3]
          · rfl
          · exfalso; nlinarith [hxK.1, hxK.2, hx_gt2, hx3]
          · exfalso; nlinarith [hxK.1, hxK.2, hx_gt2, hx3]
          · exfalso; nlinarith [hxK.1, hxK.2, hx_gt2, hx3]
          · exfalso; nlinarith [hxK.1, hxK.2, hx_gt2, hx3]
        · by_cases hx_eq3 : x = 3
          · subst x
            refine ⟨Icc 3 3, ⟨by simp, ?_⟩, ?_⟩
            · apply Set.mem_Icc.mpr; norm_num
            · intro K ⟨hKmem, hxK⟩
              have hKcases : K = Ico 1 2 ∨ K = Icc 2 2 ∨ K = Ioo 2 3 ∨ K = Icc 3 3 ∨ K = Ioo 3 5 ∨ K = Ico 5 6 ∨ K = Icc 6 6 := by
                simpa using hKmem
              rcases hKcases with (rfl|rfl|rfl|rfl|rfl|rfl|rfl)
              · exfalso; nlinarith [hxK.1, hxK.2]
              · exfalso; nlinarith [hxK.1, hxK.2]
              · exfalso; nlinarith [hxK.1, hxK.2]
              · rfl
              · exfalso; nlinarith [hxK.1, hxK.2]
              · exfalso; nlinarith [hxK.1, hxK.2]
              · exfalso; nlinarith [hxK.1, hxK.2]
          · have hx_gt3 : 3 < x := by
              have hx_ge3 : 3 ≤ x := by
                by_contra! h
                exact hx3 h
              by_contra! h
              have : x = 3 := by nlinarith
              exact hx_eq3 this
            by_cases hx5 : x < 5
            · refine ⟨Ioo 3 5, ⟨by simp, ⟨hx_gt3, hx5⟩⟩, ?_⟩
              intro K ⟨hKmem, hxK⟩
              have hKcases : K = Ico 1 2 ∨ K = Icc 2 2 ∨ K = Ioo 2 3 ∨ K = Icc 3 3 ∨ K = Ioo 3 5 ∨ K = Ico 5 6 ∨ K = Icc 6 6 := by
                simpa using hKmem
              rcases hKcases with (rfl|rfl|rfl|rfl|rfl|rfl|rfl)
              · exfalso; nlinarith [hxK.1, hxK.2, hx_gt3, hx5]
              · exfalso; nlinarith [hxK.1, hxK.2, hx_gt3, hx5]
              · exfalso; nlinarith [hxK.1, hxK.2, hx_gt3, hx5]
              · exfalso; nlinarith [hxK.1, hxK.2, hx_gt3, hx5]
              · rfl
              · exfalso; nlinarith [hxK.1, hxK.2, hx_gt3, hx5]
              · exfalso; nlinarith [hxK.1, hxK.2, hx_gt3, hx5]
            · by_cases hx_eq6 : x = 6
              · subst x
                refine ⟨Icc 6 6, ⟨by simp, ?_⟩, ?_⟩
                · apply Set.mem_Icc.mpr; norm_num
                · intro K ⟨hKmem, hxK⟩
                  have hKcases : K = Ico 1 2 ∨ K = Icc 2 2 ∨ K = Ioo 2 3 ∨ K = Icc 3 3 ∨ K = Ioo 3 5 ∨ K = Ico 5 6 ∨ K = Icc 6 6 := by
                    simpa using hKmem
                  rcases hKcases with (rfl|rfl|rfl|rfl|rfl|rfl|rfl)
                  · exfalso; nlinarith [hxK.1, hxK.2]
                  · exfalso; nlinarith [hxK.1, hxK.2]
                  · exfalso; nlinarith [hxK.1, hxK.2]
                  · exfalso; nlinarith [hxK.1, hxK.2]
                  · exfalso; nlinarith [hxK.1, hxK.2]
                  · exfalso; nlinarith [hxK.1, hxK.2]
                  · rfl
              · have hx_ge5 : 5 ≤ x := by
                  by_contra! h
                  have hx_lt5 : x < 5 := h
                  nlinarith
                have hx_lt6 : x < 6 := by
                  by_contra! h
                  have : x = 6 := by nlinarith
                  exact hx_eq6 this
                refine ⟨Ico 5 6, ⟨by simp, ⟨hx_ge5, hx_lt6⟩⟩, ?_⟩
                intro K ⟨hKmem, hxK⟩
                have hKcases : K = Ico 1 2 ∨ K = Icc 2 2 ∨ K = Ioo 2 3 ∨ K = Icc 3 3 ∨ K = Ioo 3 5 ∨ K = Ico 5 6 ∨ K = Icc 6 6 := by
                  simpa using hKmem
                rcases hKcases with (rfl|rfl|rfl|rfl|rfl|rfl|rfl)
                · exfalso; nlinarith [hxK.1, hxK.2, hx_ge5, hx_lt6]
                · exfalso; nlinarith [hxK.1, hxK.2, hx_ge5, hx_lt6]
                · exfalso; nlinarith [hxK.1, hxK.2, hx_ge5, hx_lt6]
                · exfalso; nlinarith [hxK.1, hxK.2, hx_ge5, hx_lt6]
                · exfalso; nlinarith [hxK.1, hxK.2, hx_ge5, hx_lt6]
                · rfl
                · exfalso; nlinarith [hxK.1, hxK.2, hx_ge5, hx_lt6]
  intro J hJ
  simp at hJ
  rcases hJ with (rfl|rfl|rfl|rfl|rfl|rfl|rfl) <;>
    rw [BoundedInterval.subset_iff] <;>
    intro x hx <;>
    simp at hx <;>
    simp <;>
    exact ⟨by nlinarith, by nlinarith⟩

/-- Example 11.2.6 -/
theorem ConstantOn.piecewiseConstantOn {f:ℝ → ℝ} {I: BoundedInterval} (h: ConstantOn f (I:Set ℝ)) :
  PiecewiseConstantOn f I := by
  use ⊥
  intro J hJ
  have hJ_intervals : J ∈ (⊥ : Partition I).intervals := hJ
  rw [Partition.intervals_of_bot] at hJ_intervals
  simp at hJ_intervals
  subst hJ_intervals
  exact h

/-- Lemma 11.2.7 / Exercise 11.2.1 -/
theorem PiecewiseConstantWith.mono {f:ℝ → ℝ} {I: BoundedInterval} {P P': Partition I} (hPP': P ≤ P')
  (hP: PiecewiseConstantWith f P) : PiecewiseConstantWith f P' := by
  intro J hJ
  rcases hPP' J hJ with ⟨K, hK, hJK⟩
  rcases hP K hK with ⟨c, hc⟩
  refine ⟨c, λ x => ?_⟩
  apply hc ⟨x.1, hJK x.1 x.2⟩

/-- Lemma 11.2.8 / Exercise 11.2.2 (add). -/
theorem PiecewiseConstantOn.add {f g: ℝ → ℝ} {I: BoundedInterval}
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) : PiecewiseConstantOn (f + g) I := by
  rcases hf with ⟨P, hP⟩
  rcases hg with ⟨Q, hQ⟩
  use P ⊔ Q
  intro J hJ
  have hPf : PiecewiseConstantWith f (P ⊔ Q) :=
    PiecewiseConstantWith.mono (BoundedInterval.le_max P Q).1 hP
  have hQg : PiecewiseConstantWith g (P ⊔ Q) :=
    PiecewiseConstantWith.mono (BoundedInterval.le_max P Q).2 hQ
  rcases hPf J hJ with ⟨c, hc⟩
  rcases hQg J hJ with ⟨d, hd⟩
  refine ⟨c + d, λ x => ?_⟩
  simp [hc x, hd x]

/-- Lemma 11.2.8 / Exercise 11.2.2 (sub). -/
theorem PiecewiseConstantOn.sub {f g: ℝ → ℝ} {I: BoundedInterval}
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) : PiecewiseConstantOn (f - g) I := by
  rcases hf with ⟨P, hP⟩
  rcases hg with ⟨Q, hQ⟩
  use P ⊔ Q
  intro J hJ
  have hPf : PiecewiseConstantWith f (P ⊔ Q) :=
    PiecewiseConstantWith.mono (BoundedInterval.le_max P Q).1 hP
  have hQg : PiecewiseConstantWith g (P ⊔ Q) :=
    PiecewiseConstantWith.mono (BoundedInterval.le_max P Q).2 hQ
  rcases hPf J hJ with ⟨c, hc⟩
  rcases hQg J hJ with ⟨d, hd⟩
  refine ⟨c - d, λ x => ?_⟩
  simp [hc x, hd x]

/-- Lemma 11.2.8 / Exercise 11.2.2 (max). -/
theorem PiecewiseConstantOn.max {f g: ℝ → ℝ} {I: BoundedInterval}
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) : PiecewiseConstantOn (max f g) I := by
  rcases hf with ⟨P, hP⟩
  rcases hg with ⟨Q, hQ⟩
  use P ⊔ Q
  intro J hJ
  have hPf : PiecewiseConstantWith f (P ⊔ Q) :=
    PiecewiseConstantWith.mono (BoundedInterval.le_max P Q).1 hP
  have hQg : PiecewiseConstantWith g (P ⊔ Q) :=
    PiecewiseConstantWith.mono (BoundedInterval.le_max P Q).2 hQ
  rcases hPf J hJ with ⟨c, hc⟩
  rcases hQg J hJ with ⟨d, hd⟩
  refine ⟨Max.max (c : ℝ) (d : ℝ), λ x => ?_⟩
  have hc' : f x.1 = c := hc x
  have hd' : g x.1 = d := hd x
  calc
    (Max.max f g) x.1 = Max.max (f x.1) (g x.1) := rfl
    _ = Max.max (c : ℝ) (d : ℝ) := by simp [hc', hd']

/-- Lemma 11.2.8 / Exercise 11.2.2 (min). -/
theorem PiecewiseConstantOn.min {f g: ℝ → ℝ} {I: BoundedInterval}
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) : PiecewiseConstantOn (min f g) I := by
  rcases hf with ⟨P, hP⟩
  rcases hg with ⟨Q, hQ⟩
  use P ⊔ Q
  intro J hJ
  have hPf : PiecewiseConstantWith f (P ⊔ Q) :=
    PiecewiseConstantWith.mono (BoundedInterval.le_max P Q).1 hP
  have hQg : PiecewiseConstantWith g (P ⊔ Q) :=
    PiecewiseConstantWith.mono (BoundedInterval.le_max P Q).2 hQ
  rcases hPf J hJ with ⟨c, hc⟩
  rcases hQg J hJ with ⟨d, hd⟩
  refine ⟨Min.min (c : ℝ) (d : ℝ), λ x => ?_⟩
  have hc' : f x.1 = c := hc x
  have hd' : g x.1 = d := hd x
  calc
    (Min.min f g) x.1 = Min.min (f x.1) (g x.1) := rfl
    _ = Min.min (c : ℝ) (d : ℝ) := by simp [hc', hd']

/-- Lemma 11.2.8 / Exercise 11.2.2 (mul). -/
theorem PiecewiseConstantOn.mul {f g: ℝ → ℝ} {I: BoundedInterval}
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) : PiecewiseConstantOn (f * g) I := by
  rcases hf with ⟨P, hP⟩
  rcases hg with ⟨Q, hQ⟩
  use P ⊔ Q
  intro J hJ
  have hPf : PiecewiseConstantWith f (P ⊔ Q) :=
    PiecewiseConstantWith.mono (BoundedInterval.le_max P Q).1 hP
  have hQg : PiecewiseConstantWith g (P ⊔ Q) :=
    PiecewiseConstantWith.mono (BoundedInterval.le_max P Q).2 hQ
  rcases hPf J hJ with ⟨c, hc⟩
  rcases hQg J hJ with ⟨d, hd⟩
  refine ⟨c * d, λ x => ?_⟩
  simp [hc x, hd x]

/-- Lemma 11.2.8 / Exercise 11.2.2 (smul). -/
theorem PiecewiseConstantOn.smul {f: ℝ → ℝ} {I: BoundedInterval}
  (c:ℝ) (hf: PiecewiseConstantOn f I) : PiecewiseConstantOn (c • f) I := by
  rcases hf with ⟨P, hP⟩
  use P
  intro J hJ
  rcases hP J hJ with ⟨d, hd⟩
  refine ⟨c * d, λ x => ?_⟩
  simp [hd x]

/-- Lemma 11.2.8 / Exercise 11.2.2 (div). -/
theorem PiecewiseConstantOn.div {f g: ℝ → ℝ} {I: BoundedInterval}
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) (_hg_ne : ∀ x ∈ I.toSet, g x ≠ 0) :
  PiecewiseConstantOn (f / g) I := by
  rcases hf with ⟨P, hP⟩
  rcases hg with ⟨Q, hQ⟩
  use P ⊔ Q
  intro J hJ
  have hPf : PiecewiseConstantWith f (P ⊔ Q) :=
    PiecewiseConstantWith.mono (BoundedInterval.le_max P Q).1 hP
  have hQg : PiecewiseConstantWith g (P ⊔ Q) :=
    PiecewiseConstantWith.mono (BoundedInterval.le_max P Q).2 hQ
  rcases hPf J hJ with ⟨c, hc⟩
  rcases hQg J hJ with ⟨d, hd⟩
  refine ⟨c / d, λ x => ?_⟩
  simp [hc x, hd x]

/-- Definition 11.2.9 (Piecewise constant integral I). -/
noncomputable abbrev PiecewiseConstantWith.integ (f:ℝ → ℝ) {I: BoundedInterval} (P: Partition I)  :
  ℝ := ∑ J ∈ P.intervals, constant_value_on f (J:Set ℝ) * |J|ₗ

theorem PiecewiseConstantWith.integ_congr {f g:ℝ → ℝ} {I: BoundedInterval} {P: Partition I}
  (h: ∀ x ∈ (I:Set ℝ), f x = g x) : integ f P = integ g P := by
  apply Finset.sum_congr rfl; intro J hJ; congr 1; apply constant_value_on_congr
  have := P.contains _ hJ; grind [subset_iff]

/-- Example 11.2.12 -/
noncomputable abbrev f_11_2_12 : ℝ → ℝ := fun x ↦
    if x < 3 then 2 else
      if x = 3 then 4 else
        6

noncomputable abbrev P_11_2_12 : Partition (Icc 1 4) :=
  ((⊥: Partition (Ico 1 3)).join (⊥ : Partition (Icc 3 3))
  (join_Ico_Icc (by norm_num) (by norm_num) )).join
  (⊥: Partition (Ioc 3 4))
  (join_Icc_Ioc (by norm_num) (by norm_num))

example : PiecewiseConstantWith f_11_2_12 P_11_2_12 := by
  have h_intervals : P_11_2_12.intervals = {Ico 1 3, Icc 3 3, Ioc 3 4} := by
    rw [P_11_2_12, Partition.intervals_of_join, Partition.intervals_of_join,
      Partition.intervals_of_bot, Partition.intervals_of_bot, Partition.intervals_of_bot]
    simp
  intro J hJ
  have hJ_intervals : J ∈ P_11_2_12.intervals := hJ
  rw [h_intervals] at hJ_intervals
  simp at hJ_intervals
  rcases hJ_intervals with (rfl|rfl|rfl)
  · refine ⟨2, λ x => ?_⟩
    rcases x.2 with ⟨hx1, hx2⟩
    simp [f_11_2_12, hx2]
  · refine ⟨4, λ x => ?_⟩
    rcases x.2 with ⟨hx1, hx2⟩
    have hx_eq3 : x.1 = 3 := le_antisymm hx2 hx1
    dsimp; rw [hx_eq3]; norm_num [f_11_2_12]
  · refine ⟨6, λ x => ?_⟩
    rcases x.2 with ⟨hx1, hx2⟩
    have hx_not_lt3 : ¬ x.1 < 3 := by nlinarith
    have hx_ne3 : x.1 ≠ 3 := by nlinarith
    simp [f_11_2_12, hx_not_lt3, hx_ne3]

example : PiecewiseConstantWith.integ f_11_2_12 P_11_2_12 = 10 := by
  have h_intervals : P_11_2_12.intervals = {Ico 1 3, Icc 3 3, Ioc 3 4} := by
    rw [P_11_2_12, Partition.intervals_of_join, Partition.intervals_of_join,
      Partition.intervals_of_bot, Partition.intervals_of_bot, Partition.intervals_of_bot]
    simp
  have hIco_val : constant_value_on f_11_2_12 (Ico 1 3 : Set ℝ) = 2 := by
    apply ConstantOn.const_eq ⟨2, by norm_num⟩
    intro x hx; rcases hx with ⟨hx1, hx2⟩; simp [f_11_2_12, hx2]
  have hIcc_val : constant_value_on f_11_2_12 (Icc 3 3 : Set ℝ) = 4 := by
    apply ConstantOn.const_eq ⟨3, by norm_num⟩
    intro x hx; rcases hx with ⟨hx1, hx2⟩; have hx_eq3 : x = 3 := le_antisymm hx2 hx1; simp [f_11_2_12, hx_eq3]
  have hIoc_val : constant_value_on f_11_2_12 (Ioc 3 4 : Set ℝ) = 6 := by
    apply ConstantOn.const_eq ⟨3.5, by norm_num⟩
    intro x hx; rcases hx with ⟨hx1, hx2⟩; dsimp [f_11_2_12]; split_ifs with hlt heq
    · exfalso; nlinarith
    · exfalso; nlinarith
    · rfl
  calc
    PiecewiseConstantWith.integ f_11_2_12 P_11_2_12
        = ∑ J ∈ P_11_2_12.intervals, constant_value_on f_11_2_12 (J : Set ℝ) * |J|ₗ := rfl
    _ = ∑ J ∈ ({Ico 1 3, Icc 3 3, Ioc 3 4} : Finset BoundedInterval), constant_value_on f_11_2_12 (J : Set ℝ) * |J|ₗ := by
      rw [h_intervals]
    _ = (constant_value_on f_11_2_12 (Ico 1 3 : Set ℝ) * |Ico 1 3|ₗ
        + constant_value_on f_11_2_12 (Icc 3 3 : Set ℝ) * |Icc 3 3|ₗ
        + constant_value_on f_11_2_12 (Ioc 3 4 : Set ℝ) * |Ioc 3 4|ₗ) := by
      simp (dsimp := false) [Finset.sum_insert, Finset.sum_singleton]; rfl
    _ = (2 * |Ico 1 3|ₗ + 4 * |Icc 3 3|ₗ + 6 * |Ioc 3 4|ₗ) := by
      unfold constant_value_on at *
      unfold constant_value at *
      rw [hIco_val, hIcc_val, hIoc_val]
    _ = (2 * 2 + 4 * 0 + 6 * 1) := by
      norm_num [BoundedInterval.length, BoundedInterval.a, BoundedInterval.b]
    _ = 10 := by norm_num

noncomputable abbrev P_11_2_12' : Partition (Icc 1 4) :=
  ((((⊥: Partition (Ico 1 2)).join (⊥ : Partition (Ico 2 3))
  (join_Ico_Ico (by norm_num) (by norm_num) )).join
  (⊥: Partition (Icc 3 3))
  (join_Ico_Icc (by norm_num) (by norm_num))).join
  (⊥: Partition (Ioc 3 4))
  (join_Icc_Ioc (by norm_num) (by norm_num))).add_empty

example : PiecewiseConstantWith f_11_2_12 P_11_2_12' := by
  have h_intervals : P_11_2_12'.intervals = {Ico 1 2, Ico 2 3, Icc 3 3, Ioc 3 4, ∅} := by
    rw [P_11_2_12', Partition.intervals_of_add_empty, Partition.intervals_of_join, Partition.intervals_of_join,
      Partition.intervals_of_join, Partition.intervals_of_bot, Partition.intervals_of_bot,
      Partition.intervals_of_bot, Partition.intervals_of_bot]
    simp
  intro J hJ
  have hJ_intervals : J ∈ P_11_2_12'.intervals := hJ
  rw [h_intervals] at hJ_intervals
  simp at hJ_intervals
  rcases hJ_intervals with (rfl|rfl|rfl|rfl|rfl)
  · refine ⟨2, λ x => ?_⟩
    rcases x.2 with ⟨hx1, hx2⟩
    have hx_lt3 : x.1 < 3 := by nlinarith
    simp [f_11_2_12, hx_lt3]
  · refine ⟨2, λ x => ?_⟩
    rcases x.2 with ⟨hx1, hx2⟩
    simp [f_11_2_12, hx2]
  · refine ⟨4, λ x => ?_⟩
    rcases x.2 with ⟨hx1, hx2⟩
    have hx_eq3 : x.1 = 3 := le_antisymm hx2 hx1
    dsimp; rw [hx_eq3]; norm_num [f_11_2_12]
  · refine ⟨6, λ x => ?_⟩
    rcases x.2 with ⟨hx1, hx2⟩
    have hx_not_lt3 : ¬ x.1 < 3 := by nlinarith
    have hx_ne3 : x.1 ≠ 3 := by nlinarith
    simp [f_11_2_12, hx_not_lt3, hx_ne3]
  · apply ConstantOn.of_const (c := 0)
    intro x hx; simp at hx

example : PiecewiseConstantWith.integ f_11_2_12 P_11_2_12' = 10 := by
  have h_intervals : P_11_2_12'.intervals = {Ico 1 2, Ico 2 3, Icc 3 3, Ioc 3 4, ∅} := by
    rw [P_11_2_12', Partition.intervals_of_add_empty, Partition.intervals_of_join, Partition.intervals_of_join,
      Partition.intervals_of_join, Partition.intervals_of_bot, Partition.intervals_of_bot,
      Partition.intervals_of_bot, Partition.intervals_of_bot]
    simp
  have hIco12_val : constant_value_on f_11_2_12 (Ico 1 2 : Set ℝ) = 2 := by
    apply ConstantOn.const_eq ⟨1.5, by norm_num⟩
    intro x hx; rcases hx with ⟨hx1, hx2⟩; dsimp [f_11_2_12]; split_ifs with h h'
    · simp
    · exfalso; nlinarith
    · exfalso; nlinarith
  have hIco23_val : constant_value_on f_11_2_12 (Ico 2 3 : Set ℝ) = 2 := by
    apply ConstantOn.const_eq ⟨2.5, by norm_num⟩
    intro x hx; rcases hx with ⟨hx1, hx2⟩; simp [f_11_2_12, hx2]
  have hIcc33_val : constant_value_on f_11_2_12 (Icc 3 3 : Set ℝ) = 4 := by
    apply ConstantOn.const_eq ⟨3, by norm_num⟩
    intro x hx; rcases hx with ⟨hx1, hx2⟩; have hx_eq3 : x = 3 := le_antisymm hx2 hx1; simp [f_11_2_12, hx_eq3]
  have hIoc34_val : constant_value_on f_11_2_12 (Ioc 3 4 : Set ℝ) = 6 := by
    apply ConstantOn.const_eq ⟨3.5, by norm_num⟩
    intro x hx; rcases hx with ⟨hx1, hx2⟩; dsimp [f_11_2_12]; split_ifs with hlt heq
    · exfalso; nlinarith
    · exfalso; nlinarith
    · rfl
  calc
    PiecewiseConstantWith.integ f_11_2_12 P_11_2_12'
        = ∑ J ∈ P_11_2_12'.intervals, constant_value_on f_11_2_12 (J : Set ℝ) * |J|ₗ := rfl
    _ = ∑ J ∈ ({Ico 1 2, Ico 2 3, Icc 3 3, Ioc 3 4, ∅} : Finset BoundedInterval),
        constant_value_on f_11_2_12 (J : Set ℝ) * |J|ₗ := by rw [h_intervals]
    _ = (constant_value_on f_11_2_12 (Ico 1 2 : Set ℝ) * |Ico 1 2|ₗ
        + (constant_value_on f_11_2_12 (Ico 2 3 : Set ℝ) * |Ico 2 3|ₗ
        + (constant_value_on f_11_2_12 (Icc 3 3 : Set ℝ) * |Icc 3 3|ₗ
        + (constant_value_on f_11_2_12 (Ioc 3 4 : Set ℝ) * |Ioc 3 4|ₗ
        + constant_value_on f_11_2_12 (∅ : Set ℝ) * |∅|ₗ)))) := by
      simp; rfl
    _ = (2 * |Ico 1 2|ₗ + 2 * |Ico 2 3|ₗ + 4 * |Icc 3 3|ₗ + 6 * |Ioc 3 4|ₗ + 2 * |∅|ₗ) := by
      unfold constant_value_on at *
      rw [hIco12_val, hIco23_val, hIcc33_val, hIoc34_val]
      simp [BoundedInterval.length, BoundedInterval.a, BoundedInterval.b, add_assoc]
    _ = (2 * 1 + 2 * 1 + 4 * 0 + 6 * 1 + 2 * 0) := by
      norm_num [BoundedInterval.length, BoundedInterval.a, BoundedInterval.b]
    _ = 10 := by norm_num

/-- Proposition 11.2.13 (Piecewise constant integral is independent of partition) / Exercise 11.2.3 -/
theorem PiecewiseConstantWith.integ_eq {f:ℝ → ℝ} {I: BoundedInterval} {P P': Partition I}
  (hP: PiecewiseConstantWith f P) (hP': PiecewiseConstantWith f P') : integ f P = integ f P' := by
  sorry

open Classical in
/-- Definition 11.2.14 (Piecewise constant integral II)  -/
noncomputable abbrev PiecewiseConstantOn.integ (f:ℝ → ℝ) (I: BoundedInterval) :
  ℝ := if h: PiecewiseConstantOn f I then PiecewiseConstantWith.integ f h.choose else 0

noncomputable abbrev PiecewiseConstantOn.integ' {f:ℝ → ℝ} {I: BoundedInterval} (_:PiecewiseConstantOn f I) := integ f I

theorem PiecewiseConstantOn.integ_def {f:ℝ → ℝ} {I: BoundedInterval} {P: Partition I}
  (h: PiecewiseConstantWith f P) : integ f I = PiecewiseConstantWith.integ f P := by
  have h' : PiecewiseConstantOn f I := by use P
  simp [integ, h']; exact PiecewiseConstantWith.integ_eq h'.choose_spec h

theorem PiecewiseConstantOn.integ_congr {f g:ℝ → ℝ} {I: BoundedInterval}
  (h: ∀ x ∈ (I:Set ℝ), f x = g x) : integ f I = integ g I := by
  by_cases hf : PiecewiseConstantOn f I
  <;> (have hg := hf; rw [congr h] at hg; simp [integ, hf, hg])
  rw [PiecewiseConstantWith.integ_congr h, ←integ_def hg.choose_spec, ←integ_def]
  rw [←PiecewiseConstantWith.congr h]; exact hf.choose_spec

/-- Example 11.2.15 -/
example : PiecewiseConstantOn.integ f_11_2_12 (Icc 1 4) = 10 := by
  sorry

/-- Theorem 11.2.16 (a) (Laws of integration) / Exercise 11.2.4 -/
theorem PiecewiseConstantOn.integ_add {f g: ℝ → ℝ} {I: BoundedInterval}
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) :
  integ (f + g) I = integ f I + integ g I := by
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
    constant_value_on (f + g) (J : Set ℝ) * |J|ₗ
    = constant_value_on f (J : Set ℝ) * |J|ₗ + constant_value_on g (J : Set ℝ) * |J|ₗ := by
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
        constant_value_on (f + g) (J : Set ℝ) * |J|ₗ = ((f + g) x) * |J|ₗ := by rw [hfgx]
        _ = (f x + g x) * |J|ₗ := rfl
        _ = f x * |J|ₗ + g x * |J|ₗ := by ring
        _ = constant_value_on f (J : Set ℝ) * |J|ₗ + constant_value_on g (J : Set ℝ) * |J|ₗ := by rw [hfx, hgx]
    · have hJ_empty : (J : Set ℝ) = ∅ := Set.not_nonempty_iff_eq_empty.mp hJ_nonempty
      have hlen : |J|ₗ = 0 := BoundedInterval.length_of_empty hJ_empty
      simp [hlen]
  calc
    integ (f + g) I = PiecewiseConstantWith.integ (f + g) R := by
      rw [PiecewiseConstantOn.integ_def hfgR]
    _ = ∑ J ∈ R.intervals, constant_value_on (f + g) (J : Set ℝ) * |J|ₗ := rfl
    _ = ∑ J ∈ R.intervals, (constant_value_on f (J : Set ℝ) * |J|ₗ + constant_value_on g (J : Set ℝ) * |J|ₗ) := by
      refine Finset.sum_congr rfl (λ J hJ => ?_)
      rw [hval J hJ]
    _ = (∑ J ∈ R.intervals, constant_value_on f (J : Set ℝ) * |J|ₗ) +
        (∑ J ∈ R.intervals, constant_value_on g (J : Set ℝ) * |J|ₗ) := by
      simp [Finset.sum_add_distrib]
    _ = PiecewiseConstantWith.integ f R + PiecewiseConstantWith.integ g R := rfl
    _ = integ f I + integ g I := by
      rw [PiecewiseConstantOn.integ_def hfR, PiecewiseConstantOn.integ_def hgR]

/-- Theorem 11.2.16 (b) (Laws of integration) / Exercise 11.2.4 -/
theorem PiecewiseConstantOn.integ_smul {f: ℝ → ℝ} {I: BoundedInterval} (c:ℝ) (hf: PiecewiseConstantOn f I) :
  integ (c • f) I = c * integ f I := by
  rcases hf with ⟨P, hP⟩
  have hcP : PiecewiseConstantWith (c • f) P := by
    intro J hJ
    rcases hP J hJ with ⟨d, hd⟩
    refine ⟨c * d, λ x => ?_⟩
    simp [hd x]
  have hval (J : BoundedInterval) (hJ : J ∈ P.intervals) :
    constant_value_on (c • f) (J : Set ℝ) * |J|ₗ = c * (constant_value_on f (J : Set ℝ) * |J|ₗ) := by
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
        constant_value_on (c • f) (J : Set ℝ) * |J|ₗ = ((c • f) x) * |J|ₗ := by rw [hcfx]
        _ = (c * f x) * |J|ₗ := rfl
        _ = c * (f x * |J|ₗ) := by ring
        _ = c * (constant_value_on f (J : Set ℝ) * |J|ₗ) := by rw [hfx]
    · have hJ_empty : (J : Set ℝ) = ∅ := Set.not_nonempty_iff_eq_empty.mp hJ_nonempty
      have hlen : |J|ₗ = 0 := BoundedInterval.length_of_empty hJ_empty
      simp [hlen]
  calc
    integ (c • f) I = PiecewiseConstantWith.integ (c • f) P := by
      rw [PiecewiseConstantOn.integ_def hcP]
    _ = ∑ J ∈ P.intervals, constant_value_on (c • f) (J : Set ℝ) * |J|ₗ := rfl
    _ = ∑ J ∈ P.intervals, c * (constant_value_on f (J : Set ℝ) * |J|ₗ) := by
      refine Finset.sum_congr rfl (λ J hJ => ?_)
      rw [hval J hJ]
    _ = c * (∑ J ∈ P.intervals, constant_value_on f (J : Set ℝ) * |J|ₗ) := by simp [Finset.mul_sum]
    _ = c * PiecewiseConstantWith.integ f P := rfl
    _ = c * integ f I := by rw [PiecewiseConstantOn.integ_def hP]

/-- Theorem 11.2.16 (c) (Laws of integration) / Exercise 11.2.4 -/
theorem PiecewiseConstantOn.integ_sub {f g: ℝ → ℝ} {I: BoundedInterval}
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) :
  integ (f - g) I = integ f I - integ g I := by
  calc
    integ (f - g) I = integ (f + ((-1 : ℝ) • g)) I := by
      simp [sub_eq_add_neg]
    _ = integ f I + integ ((-1 : ℝ) • g) I := PiecewiseConstantOn.integ_add hf (PiecewiseConstantOn.smul (-1) hg)
    _ = integ f I + ((-1 : ℝ) * integ g I) := by rw [PiecewiseConstantOn.integ_smul (-1) hg]
    _ = integ f I - integ g I := by ring

/-- Theorem 11.2.16 (d) (Laws of integration) / Exercise 11.2.4 -/
theorem PiecewiseConstantOn.integ_of_nonneg {f: ℝ → ℝ} {I: BoundedInterval} (h: ∀ x ∈ I, 0 ≤ f x)
  (hf: PiecewiseConstantOn f I) :
  0 ≤ integ f I := by
  rcases hf with ⟨P, hP⟩
  have h_nonneg_sum : 0 ≤ ∑ J ∈ P.intervals, constant_value_on f (J : Set ℝ) * |J|ₗ := by
    refine Finset.sum_nonneg (λ J hJ => ?_)
    have hfJ : ConstantOn f (J : Set ℝ) := hP J hJ
    by_cases hJ_nonempty : (J : Set ℝ).Nonempty
    · rcases hJ_nonempty with ⟨x, hx⟩
      have hJI : (J : Set ℝ) ⊆ (I : Set ℝ) := P.contains J hJ
      have hxI : x ∈ (I : Set ℝ) := hJI hx
      have h_fx : f x = constant_value_on f (J : Set ℝ) := hfJ.eq hx
      have h_nonneg_val : 0 ≤ constant_value_on f (J : Set ℝ) := by
        rw [← h_fx]; exact h x hxI
      have h_len_nonneg : 0 ≤ |J|ₗ := BoundedInterval.length_nonneg J
      nlinarith
    · have hJ_empty : (J : Set ℝ) = ∅ := Set.not_nonempty_iff_eq_empty.mp hJ_nonempty
      have hlen : |J|ₗ = 0 := BoundedInterval.length_of_empty hJ_empty
      simp [hlen]
  calc
    0 ≤ ∑ J ∈ P.intervals, constant_value_on f (J : Set ℝ) * |J|ₗ := h_nonneg_sum
    _ = PiecewiseConstantWith.integ f P := rfl
    _ = integ f I := by rw [PiecewiseConstantOn.integ_def hP]

/-- Theorem 11.2.16 (e) (Laws of integration) / Exercise 11.2.4 -/
theorem PiecewiseConstantOn.integ_mono {f g: ℝ → ℝ} {I: BoundedInterval} (h: ∀ x ∈ I, f x ≤ g x)
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) :
  integ f I ≤ integ g I := by
  have h_nonneg : ∀ x ∈ I, 0 ≤ (g - f) x := by
    intro x hx; simp; linarith [h x hx]
  have h_nonneg_int : 0 ≤ integ (g - f) I :=
    integ_of_nonneg h_nonneg (hg.sub hf)
  have h_sub : integ (g - f) I = integ g I - integ f I := PiecewiseConstantOn.integ_sub hg hf
  linarith


/-- Theorem 11.2.16 (f) (Laws of integration) / Exercise 11.2.4 -/
theorem PiecewiseConstantOn.integ_const (c: ℝ) (I: BoundedInterval) :
  integ (fun _ ↦ c) I = c * |I|ₗ := by
  have hc : ConstantOn (fun _ : ℝ ↦ c) (I : Set ℝ) := ConstantOn.of_const' c I
  have hc_bot : PiecewiseConstantWith (fun _ : ℝ ↦ c) (⊥ : Partition I) := by
    intro J hJ
    have hJ_mem : J ∈ (⊥ : Partition I).intervals := hJ
    rw [Partition.intervals_of_bot] at hJ_mem
    have hJ_eq : J = I := by simpa [Finset.mem_singleton] using hJ_mem
    subst hJ_eq; exact hc
  calc
    integ (fun _ : ℝ ↦ c) I = PiecewiseConstantWith.integ (fun _ : ℝ ↦ c) (⊥ : Partition I) := by
      rw [PiecewiseConstantOn.integ_def hc_bot]
    _ = constant_value_on (fun _ : ℝ ↦ c) (I : Set ℝ) * |I|ₗ := by
      simp [PiecewiseConstantWith.integ, Partition.intervals_of_bot]
    _ = c * |I|ₗ := by
      by_cases hI_nonempty : (I : Set ℝ).Nonempty
      · rcases hI_nonempty with ⟨x, hx⟩
        have hval : constant_value_on (fun _ : ℝ ↦ c) (I : Set ℝ) = c := (hc.eq hx).symm
        rw [hval]
      · have hI_empty : (I : Set ℝ) = ∅ := Set.not_nonempty_iff_eq_empty.mp hI_nonempty
        have hlen : |I|ₗ = 0 := BoundedInterval.length_of_empty hI_empty
        simp [hlen]

/-- Theorem 11.2.16 (f') (Laws of integration) / Exercise 11.2.4 -/
theorem PiecewiseConstantOn.integ_const' {f:ℝ → ℝ} {I: BoundedInterval} (h: ConstantOn f I) :
  integ f I = (constant_value_on f I) * |I|ₗ := by
  have h_bot : PiecewiseConstantWith f (⊥ : Partition I) := by
    intro J hJ
    have hJ_mem : J ∈ (⊥ : Partition I).intervals := hJ
    rw [Partition.intervals_of_bot] at hJ_mem
    have hJ_eq : J = I := by simpa [Finset.mem_singleton] using hJ_mem
    subst hJ_eq; exact h
  calc
    integ f I = PiecewiseConstantWith.integ f (⊥ : Partition I) := by
      rw [PiecewiseConstantOn.integ_def h_bot]
    _ = constant_value_on f (I : Set ℝ) * |I|ₗ := by
      simp [PiecewiseConstantWith.integ, Partition.intervals_of_bot]

open Classical in
/-- Theorem 11.2.16 (g) (Laws of integration) / Exercise 11.2.4 -/
theorem PiecewiseConstantOn.of_extend {I J: BoundedInterval} (hIJ: I ⊆ J)
  {f: ℝ → ℝ} (h: PiecewiseConstantOn f I) :
  PiecewiseConstantOn (fun x ↦ if x ∈ I then f x else 0) J := by
  rcases h with ⟨P, hP⟩
  have hg_on_P : PiecewiseConstantWith (fun x ↦ if x ∈ I then f x else 0) P := by
    intro K hK
    rcases hP K hK with ⟨c, hc⟩
    refine ⟨c, λ x => ?_⟩
    have hxI : x.1 ∈ I := (P.contains K hK) x.1 x.2
    simp [hxI, hc x]
  by_cases hI_empty : (I : Set ℝ) = ∅
  · have hzero : (fun x ↦ if x ∈ I then f x else 0) = (fun _ : ℝ ↦ 0) := by
      ext x; simp [hI_empty, BoundedInterval.mem_iff]
    rw [hzero]
    refine ⟨⊥, λ K hK => ?_⟩
    have hK_mem : K ∈ (⊥ : Partition J).intervals := hK
    have : (⊥ : Partition J).intervals = {J} := by simp
    have hK_eq : K = J := by simpa [this] using hK_mem
    rw [hK_eq]
    exact ConstantOn.of_const (c := 0) (by simp)
  have h_nonempty : (I : Set ℝ).Nonempty := Set.nonempty_iff_ne_empty.mpr hI_empty
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
          simp at hxle
          refine ⟨hxJ, ?_⟩
          by_contra! h
          have hI_a_le_x : I.a ≤ x := not_lt.mp h
          have hx_eq : x = I.a := le_antisymm hxle hI_a_le_x
          subst hx_eq; exact hxnot hI_a_mem
        · rintro ⟨hxJ, hxlt⟩
          simp at hxlt
          have hxle_Ia : x ≤ I.a := le_of_lt hxlt
          refine ⟨⟨hxJ, hxle_Ia⟩, λ hxI => ?_⟩
          have hx_in_Icc : x ∈ (Icc I.a I.b : Set ℝ) := (BoundedInterval.subset_Icc I) x hxI
          have hI_a_le_x : I.a ≤ x := by
            simp at hx_in_Icc; exact hx_in_Icc.1
          exact not_lt.mpr hI_a_le_x hxlt
      rw [h_eq]
      exact hJ_props.2.inter (Set.ordConnected_Iio (a := I.a))
    · have h_eq : leftGapSet = ((J : Set ℝ) ∩ Set.Iic I.a) := by
        ext x; constructor
        · rintro ⟨⟨hxJ, hxle⟩, _⟩; simp at hxle; exact ⟨hxJ, hxle⟩
        · rintro ⟨hxJ, hxle⟩
          simp at hxle
          refine ⟨⟨hxJ, hxle⟩, λ hxI => ?_⟩
          have hx_in_Icc : x ∈ (Icc I.a I.b : Set ℝ) := (BoundedInterval.subset_Icc I) x hxI
          simp at hx_in_Icc
          have hI_a_le_x : I.a ≤ x := hx_in_Icc.1
          by_cases hx_ltIa : I.a < x
          · exfalso; exact not_lt.mpr hxle hx_ltIa
          · have hx_eq : x = I.a := le_antisymm hxle hI_a_le_x
            subst hx_eq; exact hI_a_mem hxI
      rw [h_eq]
      exact hJ_props.2.inter (Set.ordConnected_Iic (a := I.a))
  have hR_set_ord : rightGapSet.OrdConnected := by
    by_cases hI_b_mem : I.b ∈ (I : Set ℝ)
    · have h_eq : rightGapSet = ((J : Set ℝ) ∩ Set.Ioi I.b) := by
        ext x; constructor
        · rintro ⟨⟨hxJ, hxle⟩, hxnot⟩
          simp at hxle
          refine ⟨hxJ, ?_⟩
          by_contra! h
          have hx_le_Ib : x ≤ I.b := not_lt.mp h
          have hx_eq : x = I.b := le_antisymm hx_le_Ib hxle
          subst hx_eq; exact hxnot hI_b_mem
        · rintro ⟨hxJ, hxlt⟩
          simp at hxlt
          have hxge_Ib : I.b ≤ x := le_of_lt hxlt
          refine ⟨⟨hxJ, hxge_Ib⟩, λ hxI => ?_⟩
          have hx_in_Icc : x ∈ (Icc I.a I.b : Set ℝ) := (BoundedInterval.subset_Icc I) x hxI
          simp at hx_in_Icc
          have hx_le_Ib : x ≤ I.b := hx_in_Icc.2
          exfalso; exact not_lt.mpr hx_le_Ib hxlt
      rw [h_eq]
      exact hJ_props.2.inter (Set.ordConnected_Ioi (a := I.b))
    · have h_eq : rightGapSet = ((J : Set ℝ) ∩ Set.Ici I.b) := by
        ext x; constructor
        · rintro ⟨⟨hxJ, hxle⟩, _⟩; simp at hxle; exact ⟨hxJ, hxle⟩
        · rintro ⟨hxJ, hxle⟩
          simp at hxle
          refine ⟨⟨hxJ, hxle⟩, λ hxI => ?_⟩
          have hx_in_Icc : x ∈ (Icc I.a I.b : Set ℝ) := (BoundedInterval.subset_Icc I) x hxI
          simp at hx_in_Icc
          have hx_eq : x = I.b := le_antisymm hx_in_Icc.2 hxle
          subst hx_eq; exact hI_b_mem hxI
      rw [h_eq]
      exact hJ_props.2.inter (Set.ordConnected_Ici (a := I.b))
  have hL_set_bdd : Bornology.IsBounded leftGapSet :=
    hJ_props.1.subset (by intro x hx; exact hx.1.1)
  have hR_set_bdd : Bornology.IsBounded rightGapSet :=
    hJ_props.1.subset (by intro x hx; exact hx.1.1)
  rcases (BoundedInterval.ordConnected_iff leftGapSet).mp ⟨hL_set_bdd, hL_set_ord⟩ with ⟨L, hL⟩
  rcases (BoundedInterval.ordConnected_iff rightGapSet).mp ⟨hR_set_bdd, hR_set_ord⟩ with ⟨R, hR⟩
  have hL_sub_J : (L : Set ℝ) ⊆ (J : Set ℝ) := by
    intro x hx; rw [← hL] at hx; exact hx.1.1
  have hR_sub_J : (R : Set ℝ) ⊆ (J : Set ℝ) := by
    intro x hx; rw [← hR] at hx; exact hx.1.1
  have hL_not_I : (L : Set ℝ) ∩ (I : Set ℝ) = ∅ := by
    apply Set.not_nonempty_iff_eq_empty.mp
    intro h_nonempty; rcases h_nonempty with ⟨x, hxL, hxI⟩
    rw [← hL] at hxL; exact hxL.2 hxI
  have hR_not_I : (R : Set ℝ) ∩ (I : Set ℝ) = ∅ := by
    apply Set.not_nonempty_iff_eq_empty.mp
    intro h_nonempty; rcases h_nonempty with ⟨x, hxR, hxI⟩
    rw [← hR] at hxR; exact hxR.2 hxI
  have hLR_disjoint : (L : Set ℝ) ∩ (R : Set ℝ) = ∅ := by
    apply Set.not_nonempty_iff_eq_empty.mp
    intro hLR_nonempty; rcases hLR_nonempty with ⟨x, hxL, hxR⟩
    rw [← hL] at hxL; rw [← hR] at hxR
    have hx_le_Ia : x ≤ I.a := hxL.1.2
    have hx_Ib_le : I.b ≤ x := hxR.1.2
    have hI_a_le_Ib : I.a ≤ I.b := by
      rcases h_nonempty with ⟨y, hy⟩
      have hy_in_Icc : y ∈ (Icc I.a I.b : Set ℝ) := (BoundedInterval.subset_Icc I) y hy
      simp at hy_in_Icc
      have hI_a_le_y : I.a ≤ y := hy_in_Icc.1
      have hy_le_Ib : y ≤ I.b := hy_in_Icc.2
      exact le_trans hI_a_le_y hy_le_Ib
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
          · subst hK'L
            exfalso; exact Set.not_nonempty_iff_eq_empty.mpr hL_not_I ⟨x, hxK', hxI⟩
          · have hK'_eq_R : K' = R := Finset.mem_singleton.mp hK'R
            subst hK'_eq_R
            exfalso; exact Set.not_nonempty_iff_eq_empty.mpr hR_not_I ⟨x, hxK', hxI⟩
      · by_cases hxL : x ∈ (L : Set ℝ)
        · refine ⟨L, ⟨Finset.mem_union_right _ (by simp), hxL⟩, λ K' hK' => ?_⟩
          rcases hK' with ⟨hK'mem, hxK'⟩
          rcases Finset.mem_union.mp hK'mem with (hK'P | hK'LR)
          · have hK'_sub_I : (K' : Set ℝ) ⊆ (I : Set ℝ) := P.contains K' hK'P
            exact (hxI (hK'_sub_I hxK')).elim
          · rcases Finset.mem_insert.mp hK'LR with (hK'L | hK'R)
            · subst hK'L; rfl
            · have hK'_eq_R : K' = R := Finset.mem_singleton.mp hK'R
              subst hK'_eq_R
              exfalso; exact Set.not_nonempty_iff_eq_empty.mpr hLR_disjoint ⟨x, hxL, hxK'⟩
        · by_cases hxR : x ∈ (R : Set ℝ)
          · refine ⟨R, ⟨Finset.mem_union_right _ (by simp [Finset.mem_insert]), hxR⟩, λ K' hK' => ?_⟩
            rcases hK' with ⟨hK'mem, hxK'⟩
            rcases Finset.mem_union.mp hK'mem with (hK'P | hK'LR)
            · have hK'_sub_I : (K' : Set ℝ) ⊆ (I : Set ℝ) := P.contains K' hK'P
              exact (hxI (hK'_sub_I hxK')).elim
            · rcases Finset.mem_insert.mp hK'LR with (hK'L | hK'R)
              · subst hK'L
                exfalso; exact Set.not_nonempty_iff_eq_empty.mpr hLR_disjoint ⟨x, hxK', hxR⟩
              · have hK'_eq_R : K' = R := Finset.mem_singleton.mp hK'R; subst hK'_eq_R; rfl
          · have hxI' : x ∈ (I : Set ℝ) := by
              have hx_gtIa : I.a < x := by
                by_contra! h
                rw [← hL] at hxL
                apply hxL; refine ⟨⟨hx, h⟩, hxI⟩
              have hx_ltIb : x < I.b := by
                by_contra! h
                rw [← hR] at hxR
                apply hxR; refine ⟨⟨hx, h⟩, hxI⟩
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
        · subst hKL; rw [BoundedInterval.subset_iff]; exact hL_sub_J
        · have hK_eq_R : K = R := Finset.mem_singleton.mp hKR
          subst hK_eq_R; rw [BoundedInterval.subset_iff]; exact hR_sub_J
  }
  refine ⟨P_J, λ K hK => ?_⟩
  rcases Finset.mem_union.mp hK with (hKP | hKLR)
  · exact hg_on_P K hKP
  · rcases Finset.mem_insert.mp hKLR with (hKL | hKR)
    · subst hKL
      apply ConstantOn.of_const (c := 0)
      intro x hx
      rw [← hL] at hx
      have hx_not_I : x ∉ (I : Set ℝ) := hx.2
      split_ifs with hxI
      · exfalso; exact hx_not_I hxI
      · rfl
    · have hK_eq_R : K = R := Finset.mem_singleton.mp hKR
      subst hK_eq_R
      apply ConstantOn.of_const (c := 0)
      intro x hx
      rw [← hR] at hx
      have hx_not_I : x ∉ (I : Set ℝ) := hx.2
      split_ifs with hxI
      · exfalso; exact hx_not_I hxI
      · rfl

open Classical in
/-- Theorem 11.2.16 (g') (Laws of integration) / Exercise 11.2.4 -/
theorem PiecewiseConstantOn.integ_of_extend {I J: BoundedInterval} (hIJ: I ⊆ J)
  {f: ℝ → ℝ} (h: PiecewiseConstantOn f I) :
  integ (fun x ↦ if x ∈ I then f x else 0) J = integ f I := by
  -- Proof omitted due to complexity
  sorry

/-- Theorem 11.2.16 (h) (Laws of integration) / Exercise 11.2.4 -/
theorem PiecewiseConstantOn.of_join {I J K: BoundedInterval} (hIJK: K.joins I J)
  (f: ℝ → ℝ) : PiecewiseConstantOn f K ↔ PiecewiseConstantOn f I ∧ PiecewiseConstantOn f J := by
  constructor
  · intro h
    rcases h with ⟨P, hP⟩
    have h_disjoint : (I : Set ℝ) ∩ (J : Set ℝ) = ∅ := hIJK.1
    have h_union : (K : Set ℝ) = (I : Set ℝ) ∪ (J : Set ℝ) := hIJK.2.1
    have hP_I : PiecewiseConstantOn f I := by
      let P_I : Partition I := {
        intervals := Finset.image (fun (L : BoundedInterval) => L ∩ I) P.intervals
        exists_unique := λ x hx => by
          have hxK : x ∈ K := by
            simpa [h_union, BoundedInterval.mem_iff] using Or.inl (hx : x ∈ (I : Set ℝ))
          rcases P.exists_unique x (by simpa [BoundedInterval.mem_iff] using hxK) with ⟨L, ⟨hLmem, hxL⟩, huniq⟩
          refine ⟨L ∩ I, ⟨Finset.mem_image.mpr ⟨L, hLmem, rfl⟩, ?_⟩, ?_⟩
          · simpa [BoundedInterval.mem_inter] using And.intro hxL hx
          · intro K' hK'
            rcases hK' with ⟨hK'mem, hxK'⟩
            rcases Finset.mem_image.mp hK'mem with ⟨L', hL'mem, hK'_eq⟩
            subst hK'_eq
            have hxL' : x ∈ (L' : Set ℝ) := by
              have : x ∈ ((L' : Set ℝ) ∩ (I : Set ℝ)) := by
                simpa [BoundedInterval.inter_eq] using hxK'
              exact this.1
            have hL'_eq_L : L' = L := huniq L' ⟨hL'mem, by simpa [BoundedInterval.mem_iff] using hxL'⟩
            subst hL'_eq_L; rfl
        contains := λ L' hL' => by
          rcases Finset.mem_image.mp hL' with ⟨L, hLmem, hL'_eq⟩
          subst hL'_eq
          rw [BoundedInterval.subset_iff, BoundedInterval.inter_eq]
          apply Set.inter_subset_right
      }
      have hP_I' : PiecewiseConstantWith f P_I := by
        intro L' hL'
        rcases Finset.mem_image.mp hL' with ⟨L, hLmem, hL'_eq⟩
        subst hL'_eq
        rcases hP L hLmem with ⟨c, hc⟩
        refine ⟨c, λ x => ?_⟩
        apply hc ⟨x, ?_⟩
        have : x.1 ∈ ((L : Set ℝ) ∩ (I : Set ℝ)) := by
          simpa [BoundedInterval.inter_eq] using x.2
        exact this.1
      exact ⟨P_I, hP_I'⟩
    have hP_J : PiecewiseConstantOn f J := by
      let P_J : Partition J := {
        intervals := Finset.image (fun (L : BoundedInterval) => L ∩ J) P.intervals
        exists_unique := λ x hx => by
          have hxK : x ∈ K := by
            simpa [h_union, BoundedInterval.mem_iff] using Or.inr (hx : x ∈ (J : Set ℝ))
          rcases P.exists_unique x (by simpa [BoundedInterval.mem_iff] using hxK) with ⟨L, ⟨hLmem, hxL⟩, huniq⟩
          refine ⟨L ∩ J, ⟨Finset.mem_image.mpr ⟨L, hLmem, rfl⟩, ?_⟩, ?_⟩
          · simpa [BoundedInterval.mem_inter] using And.intro hxL hx
          · intro K' hK'
            rcases hK' with ⟨hK'mem, hxK'⟩
            rcases Finset.mem_image.mp hK'mem with ⟨L', hL'mem, hK'_eq⟩
            subst hK'_eq
            have hxL' : x ∈ (L' : Set ℝ) := by
              have : x ∈ ((L' : Set ℝ) ∩ (J : Set ℝ)) := by
                simpa [BoundedInterval.inter_eq] using hxK'
              exact this.1
            have hL'_eq_L : L' = L := huniq L' ⟨hL'mem, by simpa [BoundedInterval.mem_iff] using hxL'⟩
            subst hL'_eq_L; rfl
        contains := λ L' hL' => by
          rcases Finset.mem_image.mp hL' with ⟨L, hLmem, hL'_eq⟩
          subst hL'_eq
          rw [BoundedInterval.subset_iff, BoundedInterval.inter_eq]
          apply Set.inter_subset_right
      }
      have hP_J' : PiecewiseConstantWith f P_J := by
        intro L' hL'
        rcases Finset.mem_image.mp hL' with ⟨L, hLmem, hL'_eq⟩
        subst hL'_eq
        rcases hP L hLmem with ⟨c, hc⟩
        refine ⟨c, λ x => ?_⟩
        apply hc ⟨x, ?_⟩
        have : x.1 ∈ ((L : Set ℝ) ∩ (J : Set ℝ)) := by
          simpa [BoundedInterval.inter_eq] using x.2
        exact this.1
      exact ⟨P_J, hP_J'⟩
    exact ⟨hP_I, hP_J⟩
  · intro ⟨hI, hJ⟩
    rcases hI with ⟨P_I, hP_I⟩
    rcases hJ with ⟨P_J, hP_J⟩
    refine ⟨P_I.join P_J hIJK, λ L hL => ?_⟩
    have hL_int : L ∈ (P_I.join P_J hIJK).intervals := hL
    have hL' : L ∈ (P_I.intervals ∪ P_J.intervals) := by
      simpa [Partition.intervals_of_join] using hL_int
    rcases Finset.mem_union.mp hL' with (hL_I | hL_J)
    · exact hP_I L hL_I
    · exact hP_J L hL_J

/-- Theorem 11.2.16 (h') (Laws of integration) / Exercise 11.2.4 -/
theorem PiecewiseConstantOn.integ_of_join {I J K: BoundedInterval} (hIJK: K.joins I J)
  {f: ℝ → ℝ} (h: PiecewiseConstantOn f K) :
  integ f K = integ f I + integ f J := by
  rcases (PiecewiseConstantOn.of_join hIJK f).mp h with ⟨hI, hJ⟩
  rcases hI with ⟨P_I, hP_I⟩
  rcases hJ with ⟨P_J, hP_J⟩
  have hP_join : PiecewiseConstantWith f (P_I.join P_J hIJK) := by
    intro L hL
    have hL_int : L ∈ (P_I.join P_J hIJK).intervals := hL
    have hL' : L ∈ (P_I.intervals ∪ P_J.intervals) := by
      simpa [Partition.intervals_of_join] using hL_int
    rcases Finset.mem_union.mp hL' with (hL_I | hL_J)
    · exact hP_I L hL_I
    · exact hP_J L hL_J
  have h_union_sum : (∑ L ∈ (P_I.intervals ∪ P_J.intervals), constant_value_on f (L : Set ℝ) * |L|ₗ)
      = (∑ L ∈ P_I.intervals, constant_value_on f (L : Set ℝ) * |L|ₗ)
      + (∑ L ∈ P_J.intervals, constant_value_on f (L : Set ℝ) * |L|ₗ) := by
    let T : BoundedInterval → ℝ := λ L => constant_value_on f (L : Set ℝ) * |L|ₗ
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
        have h_disjoint : (I : Set ℝ) ∩ (J : Set ℝ) = ∅ := hIJK.1
        exact Set.not_nonempty_iff_eq_empty.mpr h_disjoint ⟨x, hxI, hxJ⟩
      simp [T, BoundedInterval.length_of_empty hL_empty]
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
    integ f K = PiecewiseConstantWith.integ f (P_I.join P_J hIJK) := by
      rw [PiecewiseConstantOn.integ_def hP_join]
    _ = ∑ L ∈ (P_I.join P_J hIJK).intervals, constant_value_on f (L : Set ℝ) * |L|ₗ := rfl
    _ = ∑ L ∈ (P_I.intervals ∪ P_J.intervals), constant_value_on f (L : Set ℝ) * |L|ₗ := by simp
    _ = (∑ L ∈ P_I.intervals, constant_value_on f (L : Set ℝ) * |L|ₗ)
      + (∑ L ∈ P_J.intervals, constant_value_on f (L : Set ℝ) * |L|ₗ) := h_union_sum
    _ = PiecewiseConstantWith.integ f P_I + PiecewiseConstantWith.integ f P_J := rfl
    _ = integ f I + integ f J := by
      rw [PiecewiseConstantOn.integ_def hP_I, PiecewiseConstantOn.integ_def hP_J]

end Chapter11
