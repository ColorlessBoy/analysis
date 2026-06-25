import Mathlib.Tactic
import Analysis.Section_8_4

set_option doc.verso.suggestions false

/-!
# Analysis I, Section 8.5: Ordered sets

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Review of {name}`PartialOrder`, {name}`LinearOrder`, and {name}`WellFoundedLT`, with some API.
- Strong induction.
- Zorn's lemma.

-/

namespace Chapter8

/-- Definition 8.5.1 - Here we just review the Mathlib {name}`PartialOrder` class. -/

example {X:Type} [PartialOrder X] (x:X) : x ≤ x := le_refl x
example {X:Type} [PartialOrder X] {x y:X} (h₁: x ≤ y) (h₂: y ≤ x) : x = y := antisymm h₁ h₂
example {X:Type} [PartialOrder X] {x y z:X} (h₁: x ≤ y) (h₂: y ≤ z) : x ≤ z := le_trans h₁ h₂
example {X:Type} [PartialOrder X] (x y:X) : x < y ↔ x ≤ y ∧ x ≠ y := lt_iff_le_and_ne

@[implicit_reducible] def PartialOrder.mk {X:Type} [LE X]
  (hrefl: ∀ x:X, x ≤ x)
  (hantisymm: ∀ x y:X, x ≤ y → y ≤ x → x = y)
  (htrans: ∀ x y z:X, x ≤ y → y ≤ z → x ≤ z) : PartialOrder X :=
{
  le := (· ≤ ·)
  le_refl := hrefl
  le_antisymm := hantisymm
  le_trans := htrans
}

example {X:Type} : PartialOrder (Set X) := by infer_instance
example {X:Type} (A B: Set X) : A ≤ B ↔ A ⊆ B := by rfl

/-- Definition 8.5.3.  Here we just review the Mathlib {name}`LinearOrder` class. -/
example {X:Type} [LinearOrder X] : PartialOrder X := by infer_instance
def IsTotal (X:Type) [PartialOrder X] : Prop := ∀ x y:X, x ≤ y ∨ y ≤ x
example {X:Type} [LinearOrder X] : IsTotal X := le_total

open Classical in
@[implicit_reducible] noncomputable def LinearOrder.mk {X:Type} [PartialOrder X]
  (htotal: IsTotal X) : LinearOrder X :=
{
   le_total := htotal
   toDecidableLE := decRel LE.le
}

/- Examples 8.5.4 -/
example : LinearOrder ℕ := by infer_instance
example : LinearOrder ℚ := by infer_instance
noncomputable example : LinearOrder ℝ := by infer_instance
noncomputable example : LinearOrder EReal := by infer_instance


theorem IsTotal.subtype {X:Type} [PartialOrder X] {A: Set X} (hA: IsTotal X) : IsTotal A := by
  intro ⟨ x, hx ⟩ ⟨ y, hy ⟩
  specialize hA x y; simp_all

@[implicit_reducible] noncomputable def LinearOrder.subtype {X:Type} [LinearOrder X] (A: Set X) : LinearOrder A :=
LinearOrder.mk (IsTotal.subtype le_total)

theorem IsTotal.subset {X:Type} [PartialOrder X] {A B: Set X} (hA: IsTotal A) (hAB: B ⊆ A) : IsTotal B := by
  intro ⟨ x, hx ⟩ ⟨ y, hy ⟩
  specialize hA ⟨ x, hAB hx ⟩ ⟨ y, hAB hy ⟩; simp_all

abbrev X_8_5_4 : Set (Set ℕ) := { {1,2}, {2}, {2,3}, {2,3,4}, {5} }
example : ¬ IsTotal X_8_5_4 := by
  intro htotal
  let x : X_8_5_4 := ⟨{1,2}, by simp [X_8_5_4]⟩
  let y : X_8_5_4 := ⟨{2,3}, by simp [X_8_5_4]⟩
  have h := htotal x y
  rcases h with (hxy | hyx)
  · have hmem : (1 : ℕ) ∈ ({2,3} : Set ℕ) := hxy (by dsimp [x]; simp)
    simp at hmem
  · have hmem : (3 : ℕ) ∈ ({1,2} : Set ℕ) := hyx (by dsimp [y]; simp)
    simp at hmem

/-- Definition 8.5.5 (Maximal and minimal elements).  Here we use Mathlib's {name}`IsMax` and {name}`IsMin`. -/
theorem IsMax.iff {X:Type} [PartialOrder X] (x:X) :
  IsMax x ↔ ¬ ∃ y, x < y := by rw [isMax_iff_forall_not_lt]; grind

theorem IsMin.iff {X:Type} [PartialOrder X] (x:X) :
  IsMin x ↔ ¬ ∃ y, x > y := by rw [isMin_iff_forall_not_lt]; grind

/-- Examples 8.5.6 -/
example : IsMin (⟨ {2}, by aesop ⟩ : X_8_5_4) := by
  intro y hy
  rcases y with ⟨A, hA⟩
  have hcases : A = {1,2} ∨ A = {2} ∨ A = {2,3} ∨ A = {2,3,4} ∨ A = {5} := by
    simpa [X_8_5_4] using hA
  have hsub : A ⊆ {2} := hy
  rcases hcases with (rfl|rfl|rfl|rfl|rfl)
  · have hmem : (1 : ℕ) ∈ ({1,2} : Set ℕ) := by simp
    have hnotmem : (1 : ℕ) ∉ ({2} : Set ℕ) := by simp
    exact absurd (hsub hmem) hnotmem
  · simp
  · have hmem : (3 : ℕ) ∈ ({2,3} : Set ℕ) := by simp
    have hnotmem : (3 : ℕ) ∉ ({2} : Set ℕ) := by simp
    exact absurd (hsub hmem) hnotmem
  · have hmem : (3 : ℕ) ∈ ({2,3,4} : Set ℕ) := by simp
    have hnotmem : (3 : ℕ) ∉ ({2} : Set ℕ) := by simp
    exact absurd (hsub hmem) hnotmem
  · have hmem : (5 : ℕ) ∈ ({5} : Set ℕ) := by simp
    have hnotmem : (5 : ℕ) ∉ ({2} : Set ℕ) := by simp
    exact absurd (hsub hmem) hnotmem
example : IsMax (⟨ {1,2}, by aesop ⟩ : X_8_5_4) := by
  intro y hy
  rcases y with ⟨A, hA⟩
  have hcases : A = {1,2} ∨ A = {2} ∨ A = {2,3} ∨ A = {2,3,4} ∨ A = {5} := by
    simpa [X_8_5_4] using hA
  have hsub : ({1,2} : Set ℕ) ⊆ A := hy
  rcases hcases with (rfl|rfl|rfl|rfl|rfl)
  · simp
  · have hmem : (1 : ℕ) ∈ ({1,2} : Set ℕ) := by simp
    have hnotmem : (1 : ℕ) ∉ ({2} : Set ℕ) := by simp
    exact absurd (hsub hmem) hnotmem
  · have hmem : (1 : ℕ) ∈ ({1,2} : Set ℕ) := by simp
    have hnotmem : (1 : ℕ) ∉ ({2,3} : Set ℕ) := by simp
    exact absurd (hsub hmem) hnotmem
  · have hmem : (1 : ℕ) ∈ ({1,2} : Set ℕ) := by simp
    have hnotmem : (1 : ℕ) ∉ ({2,3,4} : Set ℕ) := by simp
    exact absurd (hsub hmem) hnotmem
  · have hmem : (1 : ℕ) ∈ ({1,2} : Set ℕ) := by simp
    have hnotmem : (1 : ℕ) ∉ ({5} : Set ℕ) := by simp
    exact absurd (hsub hmem) hnotmem
example : IsMax (⟨ {2,3,4}, by aesop ⟩ : X_8_5_4) := by
  intro y hy
  rcases y with ⟨A, hA⟩
  have hcases : A = {1,2} ∨ A = {2} ∨ A = {2,3} ∨ A = {2,3,4} ∨ A = {5} := by
    simpa [X_8_5_4] using hA
  have hsub : ({2,3,4} : Set ℕ) ⊆ A := hy
  rcases hcases with (rfl|rfl|rfl|rfl|rfl)
  · have hmem : (3 : ℕ) ∈ ({2,3,4} : Set ℕ) := by simp
    have hnotmem : (3 : ℕ) ∉ ({1,2} : Set ℕ) := by simp
    exact absurd (hsub hmem) hnotmem
  · have hmem : (3 : ℕ) ∈ ({2,3,4} : Set ℕ) := by simp
    have hnotmem : (3 : ℕ) ∉ ({2} : Set ℕ) := by simp
    exact absurd (hsub hmem) hnotmem
  · have hmem : (4 : ℕ) ∈ ({2,3,4} : Set ℕ) := by simp
    have hnotmem : (4 : ℕ) ∉ ({2,3} : Set ℕ) := by simp
    exact absurd (hsub hmem) hnotmem
  · simp
  · have hmem : (2 : ℕ) ∈ ({2,3,4} : Set ℕ) := by simp
    have hnotmem : (2 : ℕ) ∉ ({5} : Set ℕ) := by simp
    exact absurd (hsub hmem) hnotmem
example : IsMin (⟨ {5}, by aesop ⟩ : X_8_5_4) ∧ IsMax (⟨ {5}, by aesop ⟩ : X_8_5_4) := by
  constructor
  · intro y hy
    rcases y with ⟨A, hA⟩
    have hcases : A = {1,2} ∨ A = {2} ∨ A = {2,3} ∨ A = {2,3,4} ∨ A = {5} := by
      simpa [X_8_5_4] using hA
    have hsub : A ⊆ {5} := hy
    rcases hcases with (rfl|rfl|rfl|rfl|rfl)
    · have hmem : (1 : ℕ) ∈ ({1,2} : Set ℕ) := by simp
      have hnotmem : (1 : ℕ) ∉ ({5} : Set ℕ) := by simp
      exact absurd (hsub hmem) hnotmem
    · have hmem : (2 : ℕ) ∈ ({2} : Set ℕ) := by simp
      have hnotmem : (2 : ℕ) ∉ ({5} : Set ℕ) := by simp
      exact absurd (hsub hmem) hnotmem
    · have hmem : (2 : ℕ) ∈ ({2,3} : Set ℕ) := by simp
      have hnotmem : (2 : ℕ) ∉ ({5} : Set ℕ) := by simp
      exact absurd (hsub hmem) hnotmem
    · have hmem : (2 : ℕ) ∈ ({2,3,4} : Set ℕ) := by simp
      have hnotmem : (2 : ℕ) ∉ ({5} : Set ℕ) := by simp
      exact absurd (hsub hmem) hnotmem
    · simp
  · intro y hy
    rcases y with ⟨A, hA⟩
    have hcases : A = {1,2} ∨ A = {2} ∨ A = {2,3} ∨ A = {2,3,4} ∨ A = {5} := by
      simpa [X_8_5_4] using hA
    have hsub : ({5} : Set ℕ) ⊆ A := hy
    rcases hcases with (rfl|rfl|rfl|rfl|rfl)
    · have hmem : (5 : ℕ) ∈ ({5} : Set ℕ) := by simp
      have hnotmem : (5 : ℕ) ∉ ({1,2} : Set ℕ) := by simp
      exact absurd (hsub hmem) hnotmem
    · have hmem : (5 : ℕ) ∈ ({5} : Set ℕ) := by simp
      have hnotmem : (5 : ℕ) ∉ ({2} : Set ℕ) := by simp
      exact absurd (hsub hmem) hnotmem
    · have hmem : (5 : ℕ) ∈ ({5} : Set ℕ) := by simp
      have hnotmem : (5 : ℕ) ∉ ({2,3} : Set ℕ) := by simp
      exact absurd (hsub hmem) hnotmem
    · have hmem : (5 : ℕ) ∈ ({5} : Set ℕ) := by simp
      have hnotmem : (5 : ℕ) ∉ ({2,3,4} : Set ℕ) := by simp
      exact absurd (hsub hmem) hnotmem
    · simp
example : ¬ IsMin (⟨ {2,3}, by aesop ⟩ : X_8_5_4) ∧ ¬ IsMax (⟨ {2,3}, by aesop ⟩ : X_8_5_4) := by
  constructor
  · rw [IsMin.iff]
    push_neg
    refine ⟨⟨{2}, by aesop⟩, ?_⟩
    have : ({2} : Set ℕ) ⊆ ({2,3} : Set ℕ) := by simp
    have : ({2} : Set ℕ) ≠ ({2,3} : Set ℕ) := by
      intro h; have : (3 : ℕ) ∈ ({2} : Set ℕ) := by
        have hmem : (3 : ℕ) ∈ ({2,3} : Set ℕ) := by simp
        simp [h, hmem]
      simp at this
    exact ⟨by simp, by simp⟩
  · rw [IsMax.iff]
    push_neg
    refine ⟨⟨{2,3,4}, by aesop⟩, ?_⟩
    have : ({2,3} : Set ℕ) ⊆ ({2,3,4} : Set ℕ) := by simp
    have : ({2,3} : Set ℕ) ≠ ({2,3,4} : Set ℕ) := by
      intro h; have : (4 : ℕ) ∈ ({2,3} : Set ℕ) := by
        have hmem : (4 : ℕ) ∈ ({2,3,4} : Set ℕ) := by simp
        simp [h, hmem]
      simp at this
    exact ⟨by simp, by simp⟩

/-- Example 8.5.7 -/
example : IsMin (0:ℕ) := by
  intro b hb
  have h : b = 0 := Nat.eq_zero_of_le_zero hb
  subst h
  exact le_refl 0
example (n:ℕ) : ¬ IsMax n := by
  rw [IsMax.iff]
  push_neg
  exact ⟨n+1, Nat.lt_succ_self n⟩
example (n:ℤ): ¬ IsMin n ∧ ¬ IsMax n := by
  constructor
  · rw [IsMin.iff]
    push_neg
    exact ⟨n-1, sub_lt_self n (by norm_num)⟩
  · rw [IsMax.iff]
    push_neg
    exact ⟨n+1, lt_add_of_pos_right n (by norm_num)⟩

/-- Definition 8.5.8.  We use `[LinearOrder X] [WellFoundedLT X]` to describe well-ordered sets. -/
theorem WellFoundedLT.iff (X:Type) [LinearOrder X] :
  WellFoundedLT X ↔ ∀ A:Set X, A.Nonempty → ∃ x:A, IsMin x := by
  unfold WellFoundedLT IsMin
  rw [isWellFounded_iff, WellFounded.wellFounded_iff_has_min]
  peel with A hA; constructor
  . intro ⟨ x, hxA, h ⟩; use ⟨ x, hxA ⟩; intro ⟨ y, hy ⟩ this; specialize h y hy
    simp at *; order
  intro ⟨ ⟨ x, hx ⟩, h ⟩; refine ⟨ _, hx, ?_ ⟩; intro y hy; specialize h (b := ⟨ _, hy ⟩)
  simp at h; contrapose! h; simp [h]; order

theorem WellFoundedLT.iff' {X:Type} [PartialOrder X] (h: IsTotal X) :
  WellFoundedLT X ↔ ∀ A:Set X, A.Nonempty → ∃ x:A, IsMin x := @iff X (LinearOrder.mk h)

/-- Example 8.5.9 -/
example : WellFoundedLT ℕ := by
  rw [WellFoundedLT.iff]
  intro A hA; use ⟨ _, (Nat.min_spec hA).1 ⟩
  simp [IsMin]; grind [Nat.min_spec]

/-- Exercise 8.1.2 -/
example : ¬ WellFoundedLT ℤ := by
  rw [WellFoundedLT.iff ℤ]
  push_neg
  refine ⟨Set.univ, Set.univ_nonempty, ?_⟩
  intro x
  rw [IsMin.iff]
  push_neg
  refine ⟨⟨x.val - 1, trivial⟩, ?_⟩
  have h : (x.val : ℤ) - 1 < (x.val : ℤ) := by omega
  simpa
example : ¬ WellFoundedLT ℚ := by
  rw [WellFoundedLT.iff ℚ]
  push_neg
  refine ⟨Set.univ, Set.univ_nonempty, ?_⟩
  intro x
  rw [IsMin.iff]
  push_neg
  refine ⟨⟨x.val - 1, trivial⟩, ?_⟩
  have hx : x.val - 1 < x.val := by linarith
  exact Subtype.mk_lt_mk.mpr hx
example : ¬ WellFoundedLT ℝ := by
  rw [WellFoundedLT.iff ℝ]
  push_neg
  refine ⟨Set.univ, Set.univ_nonempty, ?_⟩
  intro x
  rw [IsMin.iff]
  push_neg
  refine ⟨⟨x.val - 1, trivial⟩, ?_⟩
  have hx : x.val - 1 < x.val := by linarith
  exact Subtype.mk_lt_mk.mpr hx

/-- Exercise 8.5.8 -/
theorem IsMax.ofFinite {X:Type} [LinearOrder X] [Finite X] [Nonempty X] : ∃ x:X, IsMax x := by
  have hne : (Finset.univ : Finset X).Nonempty := Finset.univ_nonempty
  let m := (Finset.univ : Finset X).max' hne
  refine ⟨m, ?_⟩
  intro y hy
  exact Finset.le_max' (Finset.univ : Finset X) y (Finset.mem_univ y)

theorem IsMin.ofFinite {X:Type} [LinearOrder X] [Finite X] [Nonempty X] : ∃ x:X, IsMin x := by
  have hne : (Finset.univ : Finset X).Nonempty := Finset.univ_nonempty
  let m := (Finset.univ : Finset X).min' hne
  refine ⟨m, ?_⟩
  intro y hy
  exact Finset.min'_le (Finset.univ : Finset X) y (Finset.mem_univ y)

/-- Exercise 8.5.8 -/
theorem WellFoundedLT.ofFinite {X:Type} [LinearOrder X] [Finite X] : WellFoundedLT X := by
  rw [WellFoundedLT.iff]
  intro A hA
  have hne : Nonempty A := by
    rcases hA with ⟨a, ha⟩
    exact ⟨⟨a, ha⟩⟩
  exact IsMin.ofFinite

example {X:Type} [LinearOrder X] [WellFoundedLT X] (A: Set X) : WellFoundedLT A := by
  rw [WellFoundedLT.iff A]
  have h_wf : ∀ A' : Set X, A'.Nonempty → ∃ x : A', IsMin x :=
    ((WellFoundedLT.iff X).mp ‹_›)
  intro B hB_nonempty
  let B' : Set X := {x : X | ∃ (a : A), a ∈ B ∧ a.val = x}
  have hB'_nonempty : B'.Nonempty := by
    rcases hB_nonempty with ⟨b, hb⟩
    exact ⟨b.val, b, hb, rfl⟩
  rcases h_wf B' hB'_nonempty with ⟨⟨x₀, hx₀_B'⟩, hx₀_min⟩
  have hx₀_B'_copy := hx₀_B'
  rcases hx₀_B' with ⟨a, ha_B, ha_val⟩
  use ⟨a, ha_B⟩
  intro b' hb'_le
  have hb'_val_val_le_x₀ : b'.val.val ≤ x₀ := by
    have h1 : b'.val ≤ a := (Subtype.coe_le_coe (p := B)).mpr hb'_le
    have h2 : b'.val.val ≤ a.val := (Subtype.coe_le_coe (p := A)).mpr h1
    rw [ha_val] at h2
    exact h2
  have hb'_val_val_mem_B' : b'.val.val ∈ B' := ⟨b'.val, b'.property, rfl⟩
  have h_c_le : (⟨b'.val.val, hb'_val_val_mem_B'⟩ : Subtype B') ≤ ⟨x₀, hx₀_B'_copy⟩ := by
    simpa [Subtype.mk_le_mk] using hb'_val_val_le_x₀
  have hle := hx₀_min (b := ⟨b'.val.val, hb'_val_val_mem_B'⟩) h_c_le
  have hx₀_le : x₀ ≤ b'.val.val := by
    simpa [Subtype.mk_le_mk] using hle
  apply (Subtype.coe_le_coe (p := B)).mp
  apply (Subtype.coe_le_coe (p := A)).mp
  simpa [ha_val] using hx₀_le

theorem WellFoundedLT.subset {X:Type} [PartialOrder X] {A B: Set X} (hA: IsTotal A) [hwell: WellFoundedLT A] (hAB: B ⊆ A) : WellFoundedLT B := by
  set hAlin : LinearOrder A := LinearOrder.mk hA
  set hBlin : LinearOrder B := LinearOrder.mk (hA.subset hAB)
  rw [iff' hA] at hwell; rw [iff' (hA.subset hAB)]; intro C hC
  have ⟨ ⟨ ⟨ x, hx ⟩, hx' ⟩, hmin ⟩ := hwell ((B.embeddingOfSubset _ hAB) '' C) (by aesop)
  simp at hx'; choose y hy hyC this using hx'; use ⟨ _, hyC ⟩
  simp_all [IsMin, Set.embeddingOfSubset]
  intro a ha_B ha_C
  apply hmin _ (hAB ha_B) <;> trivial

/-- Proposition 8.5.10 / Exercise 8.5.10 -/
theorem WellFoundedLT.strong_induction {X:Type} [LinearOrder X] [WellFoundedLT X] {P:X → Prop}
  (h: ∀ n, (∀ m < n, P m) → P n) : ∀ n, P n := by
  refine WellFounded.induction (r := (· < ·)) (C := P) (h := ?_) ?_
  · exact wellFounded_lt
  · exact h

/-- Definition 8.5.12 (Upper bounds and strict upper bounds) -/
abbrev IsUpperBound {X:Type} [PartialOrder X] (A:Set X) (x:X) : Prop :=
  ∀ y ∈ A, y ≤ x

/-- Connection with Mathlib's {name}`upperBounds` -/
theorem IsUpperBound.iff {X:Type} [PartialOrder X] (A:Set X) (x:X) :
  IsUpperBound A x ↔ x ∈ upperBounds A := by simp [IsUpperBound, upperBounds]

abbrev IsStrictUpperBound {X:Type} [PartialOrder X] (A:Set X) (x:X) : Prop :=
  IsUpperBound A x ∧ x ∉ A

theorem IsStrictUpperBound.iff {X:Type} [PartialOrder X] (A:Set X) (x:X) :
  IsStrictUpperBound A x ↔ ∀ y ∈ A, y < x := by
  constructor
  · rintro ⟨hub, hxnotin⟩ y hy
    rw [lt_iff_le_not_ge]
    have hle : y ≤ x := hub y hy
    refine ⟨hle, ?_⟩
    intro hge
    apply hxnotin
    have heq : x = y := le_antisymm hge hle
    rw [heq]
    exact hy
  · intro h
    have hub : ∀ y ∈ A, y ≤ x := by
      intro y hy
      have hlt := h y hy
      rw [lt_iff_le_not_ge] at hlt
      exact hlt.1
    have hxnotin : x ∉ A := by
      intro hx
      have hxx : x < x := h x hx
      exact lt_irrefl x hxx
    exact And.intro hub hxnotin

theorem IsStrictUpperBound.iff' {X:Type} [PartialOrder X] (A:Set X) (x:X) :
  IsStrictUpperBound A x ↔ x ∈ upperBounds A \ A := by
  simp [IsStrictUpperBound, IsUpperBound.iff]

example : IsUpperBound (.Icc 1 2: Set ℝ) 2 := by
  simp [IsUpperBound, Set.mem_Icc]

example : ¬ IsStrictUpperBound (.Icc 1 2: Set ℝ) 2 := by
  simp [IsStrictUpperBound]

example : IsStrictUpperBound (.Icc 1 2: Set ℝ) 3 := by
  rw [IsStrictUpperBound.iff]
  intro y hy
  rcases hy with ⟨h1, h2⟩
  linarith

/-- A convenient way to simplify the notion of having {name}`x₀` as a minimal element.-/
theorem IsMin.iff_lowerbound {X:Type} [PartialOrder X] {Y: Set X} (hY: IsTotal Y) (x₀ : X) : (∃ hx₀ : x₀ ∈ Y, IsMin (⟨ x₀, hx₀ ⟩:Y)) ↔ x₀ ∈ Y ∧ ∀ x ∈ Y, x₀ ≤ x := by
  constructor
  . rintro ⟨ hx₀, hmin ⟩; simp [IsMin, hx₀] at *
    peel hmin with x hx _; specialize hY ⟨ _, hx ⟩ ⟨ _, hx₀ ⟩; aesop
  intro h; use h.1; simp [IsMin]; aesop

theorem IsMin.iff_lowerbound' {X:Type} [PartialOrder X] {Y: Set X} (hY: IsTotal Y) : (∃ x₀ : Y, IsMin x₀) ↔ ∃ x₀, x₀ ∈ Y ∧ ∀ x ∈ Y, x₀ ≤ x := by
  constructor
  . intro ⟨ ⟨ x₀, hx₀ ⟩, hmin ⟩
    have : ∃ (hx₀ : x₀ ∈ Y), IsMin (⟨ _, hx₀ ⟩:Y) := by use hx₀
    rw [iff_lowerbound hY x₀] at this; use x₀
  intro ⟨ x₀, hx₀, hmin ⟩; choose hx₀ _ using (iff_lowerbound hY x₀).mpr ⟨ hx₀, hmin ⟩; use ⟨ _, hx₀ ⟩

/-- Exercise 8.5.11 -/
example {X:Type} [PartialOrder X] {Y Y':Set X} (hY: IsTotal Y) (hY': IsTotal Y') (hY_well: WellFoundedLT Y) (hY'_well: WellFoundedLT Y') (hYY': IsTotal (Y ∪ Y': Set X)) : WellFoundedLT (Y ∪ Y': Set X) := by
  rw [WellFoundedLT.iff' hYY']
  intro A hAne
  have hA_total : IsTotal A := by
    intro ⟨x, hx⟩ ⟨y, hy⟩; exact hYY' x y
  rw [IsMin.iff_lowerbound' hA_total]
  -- goal: ∃ a₀, a₀ ∈ A ∧ ∀ x ∈ A, a₀ ≤ x
  -- embed Y and Y' into the union
  let f : Y → (Y ∪ Y' : Set X) := λ y => ⟨y.1, Or.inl y.2⟩
  let g : Y' → (Y ∪ Y' : Set X) := λ y' => ⟨y'.1, Or.inr y'.2⟩
  -- preimages of A under these embeddings
  let A_Y : Set Y := {y | f y ∈ A}
  let A_Y' : Set Y' := {y' | g y' ∈ A}
  have hY_wf := (WellFoundedLT.iff' hY).mp hY_well
  have hY'_wf := (WellFoundedLT.iff' hY').mp hY'_well
  have hAY_total : IsTotal A_Y := by
    intro x y; exact hY x y
  have hAY'_total : IsTotal A_Y' := by
    intro x y; exact hY' x y
  -- get minima for both preimages (if nonempty)
  by_cases hAYne : A_Y.Nonempty
  · rcases hY_wf A_Y hAYne with ⟨y₀, hy₀_min⟩
    rcases ((IsMin.iff_lowerbound' hAY_total).mp ⟨y₀, hy₀_min⟩) with ⟨y₀v, hy₀v_AY, hy₀v_le⟩
    by_cases hAY'ne' : A_Y'.Nonempty
    · -- both nonempty: compare the two minima
      rcases hY'_wf A_Y' hAY'ne' with ⟨y'₀, hy'₀_min⟩
      rcases ((IsMin.iff_lowerbound' hAY'_total).mp ⟨y'₀, hy'₀_min⟩) with ⟨y'₀v, hy'₀v_AY', hy'₀v_le⟩
      have hcmp := hYY' (f y₀v) (g y'₀v)
      rcases hcmp with (hle | hle)
      · -- f y₀v ≤ g y'₀v, candidate is f y₀v
        have hmem : f y₀v ∈ A := hy₀v_AY
        refine ⟨f y₀v, hmem, ?_⟩
        intro x hx
        have hx_mem : (x : X) ∈ Y ∪ Y' := x.property
        rcases hx_mem with (hxY | hxY')
        · -- x is from Y: f ⟨(x : X), hxY⟩ = x, and ⟨(x : X), hxY⟩ ∈ A_Y
          have hx_AY : ⟨(x : X), hxY⟩ ∈ A_Y := by
            simpa [A_Y, f] using hx
          have hy₀v_le_xY : (y₀v : Y) ≤ ⟨(x : X), hxY⟩ := hy₀v_le _ hx_AY
          simpa [f] using hy₀v_le_xY
        · -- x is from Y': g ⟨(x : X), hxY'⟩ = x, and ⟨(x : X), hxY'⟩ ∈ A_Y'
          have hx_AY' : ⟨(x : X), hxY'⟩ ∈ A_Y' := by
            simpa [A_Y', g] using hx
          have hy'₀v_le_xY' : (y'₀v : Y') ≤ ⟨(x : X), hxY'⟩ := hy'₀v_le _ hx_AY'
          have h_gy0_le_x : g y'₀v ≤ x := by simpa [g] using hy'₀v_le_xY'
          exact le_trans hle h_gy0_le_x
      · -- g y'₀v ≤ f y₀v, candidate is g y'₀v
        have hmem : g y'₀v ∈ A := hy'₀v_AY'
        refine ⟨g y'₀v, hmem, ?_⟩
        intro x hx
        have hx_mem : (x : X) ∈ Y ∪ Y' := x.property
        rcases hx_mem with (hxY | hxY')
        · have hx_AY : ⟨(x : X), hxY⟩ ∈ A_Y := by
            simpa [A_Y, f] using hx
          have hy₀v_le_xY : (y₀v : Y) ≤ ⟨(x : X), hxY⟩ := hy₀v_le _ hx_AY
          have h_fy0_le_x : f y₀v ≤ x := by simpa [f] using hy₀v_le_xY
          exact le_trans hle h_fy0_le_x
        · have hx_AY' : ⟨(x : X), hxY'⟩ ∈ A_Y' := by
            simpa [A_Y', g] using hx
          have hy'₀v_le_xY' : (y'₀v : Y') ≤ ⟨(x : X), hxY'⟩ := hy'₀v_le _ hx_AY'
          simpa [g] using hy'₀v_le_xY'
    · -- A_Y' empty, so all elements of A come from Y
      have hmem : f y₀v ∈ A := hy₀v_AY
      refine ⟨f y₀v, hmem, ?_⟩
      intro x hx
      have hx_mem : (x : X) ∈ Y ∪ Y' := x.property
      rcases hx_mem with (hxY | hxY')
      · have hx_AY : ⟨(x : X), hxY⟩ ∈ A_Y := by
          simpa [A_Y, f] using hx
        have hy₀v_le_xY : (y₀v : Y) ≤ ⟨(x : X), hxY⟩ := hy₀v_le _ hx_AY
        simpa [f] using hy₀v_le_xY
      · -- x is from Y', but A_Y' is empty, contradiction
        have : ⟨(x : X), hxY'⟩ ∈ A_Y' := by
          simpa [A_Y', g] using hx
        exfalso
        exact hAY'ne' ⟨⟨(x : X), hxY'⟩, this⟩
  · -- A_Y empty, so all elements of A come from Y'
    have hAY'ne : A_Y'.Nonempty := by
      rcases hAne with ⟨a₀, ha₀⟩
      have hmem : (a₀ : X) ∈ Y ∨ (a₀ : X) ∈ Y' := a₀.property
      rcases hmem with (h | h)
      · have : ⟨(a₀ : X), h⟩ ∈ A_Y := by simp [A_Y, f, ha₀]
        exfalso
        exact hAYne ⟨⟨(a₀ : X), h⟩, this⟩
      · exact ⟨⟨(a₀ : X), h⟩, by simp [A_Y', g, ha₀]⟩
    rcases hY'_wf A_Y' hAY'ne with ⟨y'₀, hy'₀_min⟩
    rcases ((IsMin.iff_lowerbound' hAY'_total).mp ⟨y'₀, hy'₀_min⟩) with ⟨y'₀v, hy'₀v_AY', hy'₀v_le⟩
    have hmem : g y'₀v ∈ A := hy'₀v_AY'
    refine ⟨g y'₀v, hmem, ?_⟩
    intro x hx
    have hx_mem : (x : X) ∈ Y ∪ Y' := x.property
    rcases hx_mem with (hxY | hxY')
    · -- x is from Y, but A_Y is empty, contradiction
      have : ⟨(x : X), hxY⟩ ∈ A_Y := by
        simpa [A_Y, f] using hx
      exfalso
      exact hAYne ⟨⟨(x : X), hxY⟩, this⟩
    · have hx_AY' : ⟨(x : X), hxY'⟩ ∈ A_Y' := by
        simpa [A_Y', g] using hx
      have hy'₀v_le_xY' : (y'₀v : Y') ≤ ⟨(x : X), hxY'⟩ := hy'₀v_le _ hx_AY'
      simpa [g] using hy'₀v_le_xY'

/-- Lemma 8.5.14-/
theorem WellFoundedLT.partialOrder {X:Type} [PartialOrder X] (x₀ : X) : ∃ Y : Set X, IsTotal Y ∧ WellFoundedLT Y ∧ (∃ hx₀ : x₀ ∈ Y, IsMin (⟨ x₀, hx₀ ⟩: Y)) ∧ ¬ ∃ x, IsStrictUpperBound Y x := by
  -- This proof is based on the original text with some technical simplifications.

  -- The class of well-ordered subsets `Y` of `X` that contain `x₀` as a minimal element is not named in the text,
  -- but it is convenient to give it a name (`Ω₀`) for the formalization.  Here we use `IsMin.iff_lowerbound` to
  -- simplify the notion of minimality.
  let Ω₀ := { Y : Set X | IsTotal Y ∧ WellFoundedLT Y ∧ x₀ ∈ Y ∧ ∀ x ∈ Y, x₀ ≤ x}
  suffices : ∃ Y ∈ Ω₀, ¬ ∃ x, IsStrictUpperBound Y x
  . have ⟨ Y, ⟨ hY, hY'⟩, hstrict ⟩ := this; use Y, hY
    rw [IsMin.iff_lowerbound hY x₀]; tauto
  by_contra! hs
  let s : Ω₀ → X := fun Y ↦ (hs Y Y.property).choose
  replace hs (Y:Ω₀) : IsStrictUpperBound Y (s Y) := (hs Y Y.property).choose_spec

  have hpt: {x₀} ∈ Ω₀ := by
    have htotal : IsTotal ({x₀}: Set X) := by simp [IsTotal]
    let _lin : LinearOrder ({x₀}: Set X) := LinearOrder.mk htotal
    simp [Ω₀, htotal]; apply WellFoundedLT.ofFinite
  let pt : Ω₀ := ⟨ _, hpt ⟩

  -- The operation of sending a set `Y` in `Ω₀` to the smaller set `{y ∈ Y.val | y < x}`, which is also
  -- in `Ω₀` if `x ∈ Y.val \ {x₀}`, is not named explicitly in the text, but we give it a name `F` for
  -- the formalization.
  have hF {Y:Set X} (hY: Y ∈ Ω₀) {x:X} (hxy : x ∈ Y \ {x₀}) : {y ∈ Y | y < x} ∈ Ω₀ := by
    simp [Ω₀, IsTotal] at hY ⊢; choose _ hmin using hY.2.2; simp_all
    split_ands
    . convert WellFoundedLT.subset (hwell := hY.2) (B := {y ∈ Y | y < x}) _ _
      . intro ⟨ _, _ ⟩ ⟨ _, _ ⟩; simp; solve_by_elim [hY.1]
      intro _; simp; tauto
    have := hmin _ hxy.1; contrapose! hxy; order
  classical
  let F : Ω₀ → X → Ω₀ := fun Y x ↦ if hxy : x ∈ Y.val \ {x₀} then ⟨ {y ∈ (Y:Set X) | y < x}, hF Y.property hxy ⟩ else pt
  replace hF {Y : Ω₀} {x : X} (hxy : x ∈ (Y:Set X) \ {x₀}) : F Y x = { y ∈ (Y:Set X) | y < x } := by
    simp_all [F]

  -- The set `Ω` captures the notion of a `good set`.
  set Ω := { Y : Ω₀ | ∀ x ∈ (Y:Set X) \ {x₀}, x = s (F Y x) }
  have hΩ : pt ∈ Ω := by
    simp [Ω, pt]

  -- Exercise 8.5.13
  -- Exercise 8.5.13: if x ∈ Y' \ Y for good sets Y, Y', then x is a strict upper bound of Y.
  -- Proof via the standard "agreement set" (tower comparison) argument.
  have ex_8_5_13 {Y Y':Ω} (x:X) (h: x ∈ (Y':Set X) \ Y) : IsStrictUpperBound Y x := by
    rcases h with ⟨hx_in_Y', hx_not_Y⟩
    have hY_omega0 : (Y : Set X) ∈ Ω₀ := Y.val.property
    rcases hY_omega0 with ⟨hY_total, hY_wf, hY_x₀, hY_min⟩
    have hY'_omega0 : (Y' : Set X) ∈ Ω₀ := Y'.val.property
    rcases hY'_omega0 with ⟨hY'_total, hY'_wf, hY'_x₀, hY'_min⟩
    have hY_Omega : ∀ z ∈ (Y : Set X) \ {x₀}, z = s (F Y z) := Y.property
    have hY'_Omega : ∀ z ∈ (Y' : Set X) \ {x₀}, z = s (F Y' z) := Y'.property
    have hx_ne_x₀ : x ≠ x₀ := by
      intro hx_eq; apply hx_not_Y; rw [hx_eq]; exact hY_x₀
    -- Define the "agreement set": elements where initial segments in Y and Y' agree
    let agree (z : X) : Prop := z ∈ (Y : Set X) ∧ z ∈ (Y' : Set X) ∧ (F Y z : Set X) = (F Y' z : Set X)
    have hx₀_agree : agree x₀ := by
      dsimp [agree]
      refine ⟨hY_x₀, hY'_x₀, ?_⟩
      have h_pt_Y : (F Y x₀ : Set X) = {x₀} := by
        dsimp [F, pt]; by_cases h : x₀ ∈ (Y : Set X) \ {x₀}
        · exfalso; exact h.2 rfl
        · simp [h]
      have h_pt_Y' : (F Y' x₀ : Set X) = {x₀} := by
        dsimp [F, pt]; by_cases h : x₀ ∈ (Y' : Set X) \ {x₀}
        · exfalso; exact h.2 rfl
        · simp [h]
      rw [h_pt_Y, h_pt_Y']
    -- Lemma: agree is downward-closed in Y
    have agree_dc_Y : ∀ {a b : X}, agree a → b ∈ (Y : Set X) → b < a → agree b := by
      intro a b ha_agree hbY hb_lt_a
      rcases ha_agree with ⟨haY, haY', hFa⟩
      have ha_ne_x₀ : a ≠ x₀ := by
        intro h_eq; rw [h_eq] at hb_lt_a
        have hx₀_le_b : x₀ ≤ b := hY_min b hbY
        rw [lt_iff_le_not_ge] at hb_lt_a; exact hb_lt_a.2 hx₀_le_b
      have ha_minus_Y : a ∈ (Y : Set X) \ {x₀} := ⟨haY, ha_ne_x₀⟩
      have ha_minus_Y' : a ∈ (Y' : Set X) \ {x₀} := ⟨haY', ha_ne_x₀⟩
      have hFa_Y : (F Y a : Set X) = {z ∈ (Y : Set X) | z < a} := by
        simpa [F] using hF (Y := (Y : Ω₀)) ha_minus_Y
      have hFa_Y' : (F Y' a : Set X) = {z ∈ (Y' : Set X) | z < a} := by
        simpa [F] using hF (Y := (Y' : Ω₀)) ha_minus_Y'
      rw [hFa_Y, hFa_Y'] at hFa
      -- Now hFa: {z ∈ Y | z < a} = {z ∈ Y' | z < a}
      have hb_in_both : b ∈ {z ∈ (Y : Set X) | z < a} := ⟨hbY, hb_lt_a⟩
      rw [hFa] at hb_in_both
      rcases hb_in_both with ⟨hbY', hb_lt_a'⟩
      -- b ∈ Y' and b < a. Now prove F Y b = F Y' b
      by_cases hb_eq_x₀ : b = x₀
      · subst hb_eq_x₀; exact hx₀_agree
      · have hb_minus_Y : b ∈ (Y : Set X) \ {x₀} := ⟨hbY, hb_eq_x₀⟩
        have hb_minus_Y' : b ∈ (Y' : Set X) \ {x₀} := ⟨hbY', hb_eq_x₀⟩
        have hFb_Y : (F Y b : Set X) = {z ∈ (Y : Set X) | z < b} := by
          simpa [F] using hF (Y := (Y : Ω₀)) hb_minus_Y
        have hFb_Y' : (F Y' b : Set X) = {z ∈ (Y' : Set X) | z < b} := by
          simpa [F] using hF (Y := (Y' : Ω₀)) hb_minus_Y'
        refine ⟨hbY, hbY', ?_⟩
        rw [hFb_Y, hFb_Y']
        ext z; constructor
        · rintro ⟨hzY, hz_lt_b⟩
          have hz_lt_a : z < a := lt_trans hz_lt_b hb_lt_a
          have hzY' : z ∈ (Y' : Set X) := by
            have : z ∈ {z ∈ (Y : Set X) | z < a} := ⟨hzY, hz_lt_a⟩
            -- Using hFa: {z ∈ Y | z < a} = {z ∈ Y' | z < a}
            have := hFa.symm ▸ this
            exact this.1
          exact ⟨hzY', hz_lt_b⟩
        · rintro ⟨hzY', hz_lt_b⟩
          have hz_lt_a : z < a := lt_trans hz_lt_b hb_lt_a
          have hzY : z ∈ (Y : Set X) := by
            have : z ∈ {z ∈ (Y' : Set X) | z < a} := ⟨hzY', hz_lt_a⟩
            have := hFa ▸ this
            exact this.1
          exact ⟨hzY, hz_lt_b⟩
    -- Lemma: agree is downward-closed in Y'
    have agree_dc_Y' : ∀ {a b : X}, agree a → b ∈ (Y' : Set X) → b < a → agree b := by
      intro a b ha_agree hbY' hb_lt_a
      rcases ha_agree with ⟨haY, haY', hFa⟩
      have ha_ne_x₀ : a ≠ x₀ := by
        intro h_eq; rw [h_eq] at hb_lt_a
        have hx₀_le_b : x₀ ≤ b := hY'_min b hbY'
        rw [lt_iff_le_not_ge] at hb_lt_a; exact hb_lt_a.2 hx₀_le_b
      have ha_minus_Y : a ∈ (Y : Set X) \ {x₀} := ⟨haY, ha_ne_x₀⟩
      have ha_minus_Y' : a ∈ (Y' : Set X) \ {x₀} := ⟨haY', ha_ne_x₀⟩
      have hFa_Y : (F Y a : Set X) = {z ∈ (Y : Set X) | z < a} := by
        simpa [F] using hF (Y := (Y : Ω₀)) ha_minus_Y
      have hFa_Y' : (F Y' a : Set X) = {z ∈ (Y' : Set X) | z < a} := by
        simpa [F] using hF (Y := (Y' : Ω₀)) ha_minus_Y'
      rw [hFa_Y, hFa_Y'] at hFa
      have hbY : b ∈ (Y : Set X) := by
        have : b ∈ {z ∈ (Y' : Set X) | z < a} := ⟨hbY', hb_lt_a⟩
        have := hFa ▸ this
        exact this.1
      -- b ∈ Y. Now reuse agree_dc_Y (which has the same conclusion)
      let ha_full : agree a := ⟨haY, haY', by rw [hFa_Y, hFa_Y']; exact hFa⟩
      exact agree_dc_Y ha_full hbY hb_lt_a
    -- The key structural result: either (Y:SetX) ⊆ agree_set or (Y':SetX) ⊆ agree_set
    -- More precisely: either ∀ z ∈ Y, agree z, or ∀ z ∈ Y', agree z
    have h_tower_compare : (∀ z ∈ (Y : Set X), agree z) ∨ (∀ z ∈ (Y' : Set X), agree z) := by
      by_cases hY_all : ∀ z ∈ (Y : Set X), agree z
      · left; exact hY_all
      · right
        push_neg at hY_all
        rcases hY_all with ⟨y, hyY, hy_not_agree⟩
        -- Take minimal y in Y with ¬ agree
        have h_nonempty : Set.Nonempty {z : (Y : Set X) | ¬ agree (z : X)} := ⟨⟨y, hyY⟩, hy_not_agree⟩
        obtain ⟨y_min, hy_min_mem, hy_min_min⟩ := hY_wf.wf.has_min {z : (Y : Set X) | ¬ agree (z : X)} h_nonempty
        have hy_min_Y : (y_min : X) ∈ (Y : Set X) := y_min.property
        have hy_min_not_agree : ¬ agree (y_min : X) := hy_min_mem
        have h_all_lt_agree : ∀ (z : (Y : Set X)), z < y_min → agree (z : X) := by
          intro z hz_lt
          by_contra! hz_not
          have hz_mem : z ∈ {z : (Y : Set X) | ¬ agree (z : X)} := hz_not
          exact hy_min_min z hz_mem hz_lt
        -- y_min ≠ x₀ (since x₀ agrees)
        have hy_min_ne_x₀ : (y_min : X) ≠ x₀ := by
          intro h_eq; rw [h_eq] at hy_min_not_agree; exact hy_min_not_agree hx₀_agree
        -- Now take minimal y' in Y' with ¬ agree (if any)
        by_cases hY'_all : ∀ z ∈ (Y' : Set X), agree z
        · exact hY'_all
        · push_neg at hY'_all
          rcases hY'_all with ⟨y', hy'Y', hy'_not_agree⟩
          have h_nonempty' : Set.Nonempty {z : (Y' : Set X) | ¬ agree (z : X)} := ⟨⟨y', hy'Y'⟩, hy'_not_agree⟩
          obtain ⟨y'_min, hy'_min_mem, hy'_min_min⟩ := hY'_wf.wf.has_min {z : (Y' : Set X) | ¬ agree (z : X)} h_nonempty'
          have hy'_min_Y' : (y'_min : X) ∈ (Y' : Set X) := y'_min.property
          have hy'_min_not_agree : ¬ agree (y'_min : X) := hy'_min_mem
          have h_all_lt_agree' : ∀ (z : (Y' : Set X)), z < y'_min → agree (z : X) := by
            intro z hz_lt
            by_contra! hz_not
            have hz_mem : z ∈ {z : (Y' : Set X) | ¬ agree (z : X)} := hz_not
            exact hy'_min_min z hz_mem hz_lt
          have hy'_min_ne_x₀ : (y'_min : X) ≠ x₀ := by
            intro h_eq; rw [h_eq] at hy'_min_not_agree; exact hy'_min_not_agree hx₀_agree
          -- Now derive a contradiction: y_min = y'_min ∈ agree
          -- Both are ≠ x₀, so both satisfy the Ω condition
          have hy_min_mem_minus : (y_min : X) ∈ (Y : Set X) \ {x₀} := ⟨hy_min_Y, hy_min_ne_x₀⟩
          have hy'_min_mem_minus : (y'_min : X) ∈ (Y' : Set X) \ {x₀} := ⟨hy'_min_Y', hy'_min_ne_x₀⟩
          have hy_min_eq_s : (y_min : X) = s (F Y y_min) := hY_Omega (y_min : X) hy_min_mem_minus
          have hy'_min_eq_s : (y'_min : X) = s (F Y' y'_min) := hY'_Omega (y'_min : X) hy'_min_mem_minus
          -- Key claim: F Y y_min = F Y' y'_min
          -- Both equal the set {z | agree z}
          have hFY_eq_set : (F Y y_min : Set X) = {z | agree z} := by
            have hFY_Y : (F Y y_min : Set X) = {z ∈ (Y : Set X) | z < (y_min : X)} := by
              simpa [F] using hF (Y := (Y : Ω₀)) hy_min_mem_minus
            rw [hFY_Y]
            ext z; constructor
            · rintro ⟨hzY, hz_lt⟩
              exact h_all_lt_agree ⟨z, hzY⟩ (by simpa using hz_lt)
            · intro hz_agree
              have hzY := hz_agree.1
              have hzY' := hz_agree.2.1
              have hFz := hz_agree.2.2
              -- Need z < y_min. Compare z and y_min in Y (total)
              have hz_cmp := hY_total ⟨z, hzY⟩ ⟨y_min, hy_min_Y⟩
              rcases hz_cmp with (hz_le | hy_min_le)
              · -- z ≤ y_min in Y order, hence in X order
                have hz_le_X : z ≤ (y_min : X) := by simpa using hz_le
                by_cases hz_eq : z = (y_min : X)
                · -- z = y_min, but then y_min would agree, contradiction
                  exfalso; exact hy_min_not_agree (hz_eq.symm ▸ hz_agree)
                · -- z < y_min
                  have hz_lt_ymin : z < (y_min : X) := lt_of_le_of_ne hz_le_X hz_eq
                  exact ⟨hzY, hz_lt_ymin⟩
              · -- y_min ≤ z in Y order. If equality, y_min agrees (contradiction).
                -- If strict: y_min < z, then since z agrees, by agree_dc_Y, y_min agrees. Contradiction.
                have hy_min_le_X : (y_min : X) ≤ z := by simpa using hy_min_le
                by_cases hy_eq : (y_min : X) = z
                · exfalso; exact hy_min_not_agree (hy_eq ▸ hz_agree)
                · -- y_min < z
                  have hy_min_lt_z : (y_min : X) < z := lt_of_le_of_ne hy_min_le_X hy_eq
                  -- Since z agrees (z ∈ Y, z ∈ Y', F Y z = F Y' z), 
                  -- and y_min ∈ Y, y_min < z, by agree_dc_Y, y_min agrees. Contradiction.
                  have hy_min_agree : agree (y_min : X) :=
                    agree_dc_Y hz_agree hy_min_Y hy_min_lt_z
                  exfalso; exact hy_min_not_agree hy_min_agree
          have hFY'_eq_set : (F Y' y'_min : Set X) = {z | agree z} := by
            have hFY'_Y' : (F Y' y'_min : Set X) = {z ∈ (Y' : Set X) | z < (y'_min : X)} := by
              simpa [F] using hF (Y := (Y' : Ω₀)) hy'_min_mem_minus
            rw [hFY'_Y']
            ext z; constructor
            · rintro ⟨hzY', hz_lt⟩
              exact h_all_lt_agree' ⟨z, hzY'⟩ (by simpa using hz_lt)
            · intro hz_agree
              have hzY := hz_agree.1
              have hzY' := hz_agree.2.1
              have hFz := hz_agree.2.2
              have hz_cmp := hY'_total ⟨z, hzY'⟩ ⟨y'_min, hy'_min_Y'⟩
              rcases hz_cmp with (hz_le | hy'_min_le)
              · have hz_le_X : z ≤ (y'_min : X) := by simpa using hz_le
                by_cases hz_eq : z = (y'_min : X)
                · exfalso; exact hy'_min_not_agree (hz_eq.symm ▸ hz_agree)
                · have hz_lt_y'min : z < (y'_min : X) := lt_of_le_of_ne hz_le_X hz_eq
                  exact ⟨hzY', hz_lt_y'min⟩
              · have hy'_min_le_X : (y'_min : X) ≤ z := by simpa using hy'_min_le
                by_cases hy'_eq : (y'_min : X) = z
                · exfalso; exact hy'_min_not_agree (hy'_eq ▸ hz_agree)
                · have hy'_min_lt_z : (y'_min : X) < z := lt_of_le_of_ne hy'_min_le_X hy'_eq
                  have hy'_min_agree : agree (y'_min : X) :=
                    agree_dc_Y' hz_agree hy'_min_Y' hy'_min_lt_z
                  exfalso; exact hy'_min_not_agree hy'_min_agree
          -- Now: (F Y y_min : Set X) = {z | agree z} = (F Y' y'_min : Set X)
          -- Apply s to both sides, use Ω condition
          -- Need equality at Ω₀ level, not just Set X level
          have hFY_eq_val : F Y y_min = F Y' y'_min := by
            apply Subtype.val_injective
            rw [hFY_eq_set, ← hFY'_eq_set]
          -- hFY_eq_val : F Y y_min = F Y' y'_min (in Ω₀)
          have hy_eq_y' : (y_min : X) = (y'_min : X) := by
            calc
              (y_min : X) = s (F Y y_min) := hy_min_eq_s
              _ = s (F Y' y'_min) := by rw [hFY_eq_val]
              _ = (y'_min : X) := by rw [← hy'_min_eq_s]
          -- Now y_min = y'_min as X elements, so agree y_min holds
          have hy_min_agree : agree (y_min : X) := by
            refine ⟨hy_min_Y, ?_, ?_⟩
            · -- y_min ∈ Y' because y_min = y'_min ∈ Y'
              rw [hy_eq_y']; exact hy'_min_Y'
            · -- F Y y_min = F Y' y_min
              calc
                (F Y y_min : Set X) = {z | agree z} := hFY_eq_set
                _ = (F Y' y'_min : Set X) := by rw [hFY'_eq_set]
                _ = (F Y' y_min : Set X) := by rw [hy_eq_y']
          exfalso; exact hy_min_not_agree hy_min_agree
    -- Use the tower comparison to prove the goal
    rcases h_tower_compare with (hY_agree | hY'_agree)
    · -- All elements of Y agree → Y ⊆ Y' and initial segments match
      refine ⟨?_, hx_not_Y⟩
      intro y hy
      have hy_agree := hY_agree y hy
      rcases hy_agree with ⟨hyY, hyY', hF_eq⟩
      -- y ∈ Y and y ∈ Y'. Need y ≤ x
      -- Since y, x ∈ Y' and Y' is total, y and x are comparable
      have h_cmp := hY'_total ⟨y, hyY'⟩ ⟨x, hx_in_Y'⟩
      rcases h_cmp with (hle | hle)
      · simpa using hle
      · -- x ≤ y in Y'. If x = y, then x ∈ Y, contradiction. If x < y, then x ∈ F Y' y = F Y y ⊆ Y, contradiction.
        by_cases h_eq : (x : X) = y
        · rw [h_eq] at hx_not_Y; exact absurd hy hx_not_Y
        · have hx_lt_y : (x : X) < y := by
            have : (⟨x, hx_in_Y'⟩ : (Y' : Set X)) < (⟨y, hyY'⟩ : (Y' : Set X)) :=
              lt_of_le_of_ne hle (by intro heq; apply h_eq; simpa using heq)
            simpa using this
          -- Now x < y in Y' and y ∈ Y. Since y ∈ Y and F Y y = F Y' y:
          -- x ∈ F Y' y = F Y y ⊆ Y, contradiction
          have hx_FY'y : x ∈ (F Y' y : Set X) := by
            have hy_ne_x₀ : y ≠ x₀ := by
              intro hy_eq; rw [hy_eq] at hx_lt_y
              have hx₀_le_x : x₀ ≤ x := hY'_min x hx_in_Y'
              rw [lt_iff_le_not_ge] at hx_lt_y; exact hx_lt_y.2 hx₀_le_x
            have hy_minus : y ∈ (Y' : Set X) \ {x₀} := ⟨hyY', hy_ne_x₀⟩
            have hFy : (F Y' y : Set X) = {z ∈ (Y' : Set X) | z < y} := by
              simpa [F] using hF (Y := (Y' : Ω₀)) hy_minus
            rw [hFy]
            exact ⟨hx_in_Y', hx_lt_y⟩
          rw [← hF_eq] at hx_FY'y
          have hFy_Y : (F Y y : Set X) = {z ∈ (Y : Set X) | z < y} := by
            have hy_minus_Y : y ∈ (Y : Set X) \ {x₀} := by
              refine ⟨hy, ?_⟩
              intro hy_eq_x₀; rw [hy_eq_x₀] at hx_lt_y
              have hx₀_le_x : x₀ ≤ x := hY'_min x hx_in_Y'
              rw [lt_iff_le_not_ge] at hx_lt_y; exact hx_lt_y.2 hx₀_le_x
            simpa [F] using hF (Y := (Y : Ω₀)) hy_minus_Y
          rw [hFy_Y] at hx_FY'y
          rcases hx_FY'y with ⟨hxY, _⟩
          exfalso; exact hx_not_Y hxY
    · -- All elements of Y' agree → Y' ⊆ Y, but x ∈ Y' \ Y, contradiction
      have hx_agree := hY'_agree x hx_in_Y'
      rcases hx_agree with ⟨hxY, _, _⟩
      exfalso; exact hx_not_Y hxY

  have : IsTotal Ω := by
    unfold IsTotal; by_contra!; obtain ⟨ ⟨ ⟨ Y, hY1 ⟩, hY2 ⟩, ⟨ ⟨ Y', hY'1⟩, hY'2 ⟩, h1, h2 ⟩ := this
    simp_all [Set.not_subset]
    choose x₁ hx₁ hx₁' using h1; choose x₂ hx₂ hx₂' using h2
    observe h1 : IsStrictUpperBound Y x₂
    observe h2 : IsStrictUpperBound Y' x₁
    simp [IsStrictUpperBound.iff] at h1 h2
    specialize h1 _ hx₁; specialize h2 _ hx₂; order
  set Y_infty : Set X := ⋃ Y:Ω, Y
  have hmem : x₀ ∈ Y_infty := by simp [Y_infty]; use pt; grind
  have hmin {x:X} (hx: x ∈ Y_infty) : x₀ ≤ x := by
    simp [Y_infty] at hx
    rcases hx with ⟨Y, ⟨hYΩ₀, hYΩ⟩, hxY⟩
    simp [Ω₀] at hYΩ₀
    exact hYΩ₀.2.2.2 x hxY
  have htotal : IsTotal Y_infty := by
    intro ⟨ x, hx ⟩ ⟨ x', hx'⟩; simp [Y_infty] at hx hx'
    obtain ⟨ Y, ⟨ hYΩ₀, hYΩ ⟩, hxY ⟩ := hx; obtain ⟨ Y', ⟨ hY'Ω₀, hY'Ω ⟩, hxY' ⟩ := hx'
    specialize this ⟨ _, hYΩ ⟩ ⟨ _, hY'Ω ⟩; simp [Ω₀] at this ⊢ hYΩ₀ hY'Ω₀
    obtain this | this := this
    . replace hY'Ω₀ := hY'Ω₀.1 ⟨ _, this hxY ⟩ ⟨ _, hxY' ⟩; simpa using hY'Ω₀
    replace hYΩ₀ := hYΩ₀.1 ⟨ _, hxY ⟩ ⟨ _, this hxY' ⟩; simpa using hYΩ₀
  have hwell : WellFoundedLT Y_infty := by
    rw [iff' htotal]; intro A ⟨ ⟨a, ha⟩, haA ⟩
    simp [Y_infty] at ha; obtain ⟨ Y, ⟨hYΩ₀, hYΩ⟩, haY ⟩ := ha
    simp [Ω₀, iff' hYΩ₀.1] at hYΩ₀
    choose b hb hbY hbmin using hYΩ₀.2.1 {x:Y | ∃ x':A, (x:X) = x'} (by use ⟨ _, haY ⟩; simp [ha, haA])
    simp at hbY; choose hbY_infty hbA using hbY
    refine ((IsMin.iff_lowerbound' (IsTotal.subtype htotal)).mpr ?_)
    refine ⟨⟨b, hbY_infty⟩, hbA, ?_⟩
    intro ⟨x, hx⟩ hxA
    -- Goal: ⟨b, hbY_infty⟩ ≤ ⟨x, hx⟩  (in Subtype Y_infty), i.e., b ≤ x
    simp [Y_infty] at hx ⊢
    -- hx : ∃ (Y' : Ω), x ∈ Y', goal: b ≤ x
    obtain ⟨ Y', ⟨ hY'Ω₀, hY'Ω ⟩, hxY' ⟩ := hx
    -- hYΩ₀ was simplified at line 856; now simplify hY'Ω₀ too
    simp [Ω₀] at hY'Ω₀
    have hYΩ₀_setMem : Y ∈ Ω₀ := by
      have h_wf : WellFoundedLT (↑Y : Set X) := (iff' hYΩ₀.1).mpr (by
        intro A' hne
        rcases hYΩ₀.2.1 A' hne with ⟨a, hbA', hbY_A', hmin⟩
        exact ⟨⟨⟨a, hbA'⟩, hbY_A'⟩, hmin⟩)
      simpa [Ω₀] using ⟨hYΩ₀.1, h_wf, hYΩ₀.2.2.1, hYΩ₀.2.2.2⟩
    have hY'Ω₀_setMem : Y' ∈ Ω₀ := by
      simpa [Ω₀] using ⟨hY'Ω₀.1, hY'Ω₀.2.1, hY'Ω₀.2.2.1, hY'Ω₀.2.2.2⟩
    have hcmp := this ⟨⟨Y, hYΩ₀_setMem⟩, hYΩ⟩ ⟨⟨Y', hY'Ω₀_setMem⟩, hY'Ω⟩
    rcases hcmp with (h_sub | h_sub)
    · -- Y ⊆ Y'
      have hbY' : b ∈ Y' := h_sub hb
      have hY'_total : IsTotal (↑Y' : Set X) := hY'Ω₀.1
      have h_cmp := hY'_total ⟨b, hbY'⟩ ⟨x, hxY'⟩
      rcases h_cmp with (hle | hle)
      · simpa using hle
      · have hleX : x ≤ b := by simpa using hle
        by_cases h_eq : x = b
        · subst h_eq; exact le_refl _
        · have h_lt : x < b := lt_of_le_of_ne hleX h_eq
          by_cases hxY : x ∈ Y
          · -- x ∈ Y, use hbmin for contradiction
            have hY_total : IsTotal (↑Y : Set X) := hYΩ₀.1
            have h_cmp' := hY_total ⟨b, hb⟩ ⟨x, hxY⟩
            rcases h_cmp' with (hleY | hleY)
            · have hleX' : b ≤ x := by simpa using hleY
              exfalso
              exact lt_irrefl x (lt_of_lt_of_le h_lt hleX')
            · have hx_mem_S : ⟨x, hxY⟩ ∈ {x' : Subtype Y | ∃ (x'' : A), (x' : X) = (x'' : X)} := by
                refine ⟨⟨⟨x, hx⟩, hxA⟩, ?_⟩; rfl
              have hS_le : (⟨⟨x, hxY⟩, hx_mem_S⟩ : Subtype (fun x' : Subtype Y => ∃ (x'' : A), (x' : X) = (x'' : X))) ≤
                (⟨⟨b, hb⟩, hbY⟩ : Subtype (fun x' : Subtype Y => ∃ (x'' : A), (x' : X) = (x'' : X))) := by
                simpa using hleY
              have h_eq_to := hbmin hS_le
              simpa using h_eq_to
          · -- x ∉ Y, so x ∈ Y' \ Y; use ex_8_5_13
            have hxY'Y : x ∈ (Y' : Set X) \ Y := ⟨hxY', hxY⟩
            have h_strict_ub := ex_8_5_13 (Y := ⟨⟨Y, hYΩ₀_setMem⟩, hYΩ⟩) (Y' := ⟨⟨Y', hY'Ω₀_setMem⟩, hY'Ω⟩) x hxY'Y
            rw [IsStrictUpperBound.iff] at h_strict_ub
            have h_b_lt_x : b < x := h_strict_ub b hb
            exfalso
            exact lt_irrefl x (lt_trans h_lt h_b_lt_x)
    · -- Y' ⊆ Y
      have hxY : x ∈ Y := h_sub hxY'
      have hY_total : IsTotal (↑Y : Set X) := hYΩ₀.1
      have h_cmp' := hY_total ⟨b, hb⟩ ⟨x, hxY⟩
      rcases h_cmp' with (hleY | hleY)
      · simpa using hleY
      · have hx_mem_S : ⟨x, hxY⟩ ∈ {x' : Subtype Y | ∃ (x'' : A), (x' : X) = (x'' : X)} := by
          refine ⟨⟨⟨x, hx⟩, hxA⟩, ?_⟩; rfl
        have hS_le : (⟨⟨x, hxY⟩, hx_mem_S⟩ : Subtype (fun x' : Subtype Y => ∃ (x'' : A), (x' : X) = (x'' : X))) ≤
          (⟨⟨b, hb⟩, hbY⟩ : Subtype (fun x' : Subtype Y => ∃ (x'' : A), (x' : X) = (x'' : X))) := by
          simpa using hleY
        have h_eq_to := hbmin hS_le
        simpa using h_eq_to
  have hY_inftyΩ₀ : Y_infty ∈ Ω₀ := by
    simp [Ω₀, htotal, hwell, hmem]; intro x hxY; exact hmin hxY
  set sY_infty : X := s ⟨ _, hY_inftyΩ₀ ⟩
  have h_strict_ub : IsStrictUpperBound Y_infty sY_infty := hs ⟨_, hY_inftyΩ₀⟩
  rw [IsStrictUpperBound.iff] at h_strict_ub
  have hYs_total : IsTotal (Y_infty ∪ {sY_infty} : Set X) := by
    intro ⟨x, hx⟩ ⟨y, hy⟩
    simp at hx hy
    rcases hx with (hx_s | hxY)
    · subst hx_s
      rcases hy with (hy_s | hyY)
      · subst hy_s; left; exact le_refl _
      · right; exact (h_strict_ub y hyY).le
    · rcases hy with (hy_s | hyY)
      · subst hy_s; left; exact (h_strict_ub x hxY).le
      · have h_cmp := htotal ⟨x, hxY⟩ ⟨y, hyY⟩
        simpa using h_cmp
  have hYs_well : WellFoundedLT (Y_infty ∪ {sY_infty} : Set X) := by
    rw [WellFoundedLT.iff' hYs_total]
    intro A hA_nonempty
    have hwell' := (WellFoundedLT.iff' htotal).mp hwell
    let ι (y : Subtype Y_infty) : (Y_infty ∪ {sY_infty} : Set X) := ⟨(y : X), Or.inl y.2⟩
    by_cases h_in_Y : ∃ y : Subtype Y_infty, ι y ∈ A
    · rcases h_in_Y with ⟨y, hyA⟩
      let B : Set (Subtype Y_infty) := { z | ι z ∈ A }
      have hB_nonempty : B.Nonempty := ⟨y, hyA⟩
      rcases hwell' B hB_nonempty with ⟨⟨b, hbB⟩, hb_min⟩
      have hbA : ι b ∈ A := hbB
      have hB_total : IsTotal (B : Set (Subtype Y_infty)) := IsTotal.subtype htotal
      have hb_le_all : ∀ (x : Subtype Y_infty), x ∈ B → (b : X) ≤ (x : X) := by
        intro x hxB
        have h_cmp := hB_total ⟨b, hbB⟩ ⟨x, hxB⟩
        rcases h_cmp with (hle | hle)
        · exact hle
        · by_cases h_eq : (x : X) = (b : X)
          · rw [h_eq]
          · have h_lt : (x : X) < (b : X) := lt_of_le_of_ne hle h_eq
            have h_contra : ∃ (z : B), (⟨b, hbB⟩ : B) > z := by
              refine ⟨⟨x, hxB⟩, ?_⟩
              simpa using h_lt
            have hb_min' := (IsMin.iff _).mp hb_min
            exact absurd h_contra hb_min'
      have h_min_le_all : ∀ (x : A), (⟨ι b, hbA⟩ : A) ≤ x := by
        intro ⟨c_s, hcA_s⟩
        have hc_union : (c_s : X) ∈ Y_infty ∪ {sY_infty} := c_s.2
        rcases hc_union with (hcY | hc_s)
        · have hcB : ⟨(c_s : X), hcY⟩ ∈ B := by
            dsimp [B]
            have h_ι_eq : ι ⟨(c_s : X), hcY⟩ = c_s := Subtype.ext rfl
            rw [h_ι_eq]
            exact hcA_s
          have hle_X : (b : X) ≤ (c_s : X) := hb_le_all ⟨(c_s : X), hcY⟩ hcB
          exact hle_X
        · have hc_val_s : (c_s : X) = sY_infty := by
            simpa [Set.mem_singleton_iff] using hc_s
          have hle_X : (b : X) ≤ sY_infty := (h_strict_ub (b : X) b.2).le
          apply Subtype.mk_le_mk.mpr
          apply Subtype.mk_le_mk.mpr
          rw [hc_val_s]
          exact hle_X
      have h_min : IsMin (⟨ι b, hbA⟩ : A) := by
        intro x hx_le
        exact h_min_le_all x
      refine ⟨⟨ι b, hbA⟩, h_min⟩
    · rcases hA_nonempty with ⟨a_s, haA_s⟩
      have ha_val_s : (a_s : X) = sY_infty := by
        have ha_union : (a_s : X) ∈ Y_infty ∪ {sY_infty} := a_s.2
        rcases ha_union with (haY | ha_s')
        · exfalso; apply h_in_Y
          exact ⟨⟨(a_s : X), haY⟩, by
            have h_ι_eq : ι ⟨(a_s : X), haY⟩ = a_s := Subtype.ext rfl
            rw [h_ι_eq]
            exact haA_s⟩
        · simpa [Set.mem_singleton_iff] using ha_s'
      have h_all_val_s : ∀ (x : A), (a_s : X) = (x.val : X) := by
        intro ⟨c_s, hcA_s⟩
        have hc_union : (c_s : X) ∈ Y_infty ∪ {sY_infty} := c_s.2
        rcases hc_union with (hcY | hc_s')
        · exfalso; apply h_in_Y
          exact ⟨⟨(c_s : X), hcY⟩, by
            have h_ι_eq : ι ⟨(c_s : X), hcY⟩ = c_s := Subtype.ext rfl
            rw [h_ι_eq]
            exact hcA_s⟩
        · have hc_val_s : (c_s : X) = sY_infty := by
            simpa [Set.mem_singleton_iff] using hc_s'
          rw [ha_val_s, hc_val_s]
      have h_min_le_all : ∀ (x : A), (⟨a_s, haA_s⟩ : A) ≤ x := by
        intro x
        have h_val_eq : (a_s : X) = (x.val : X) := h_all_val_s x
        have h_eq : (⟨a_s, haA_s⟩ : A) = x := by
          apply Subtype.ext
          apply Subtype.ext
          exact h_val_eq
        rw [h_eq]
      have h_min : IsMin (⟨a_s, haA_s⟩ : A) := by
        intro x hx_le
        exact h_min_le_all x
      refine ⟨⟨a_s, haA_s⟩, h_min⟩
  have hYs_mem : x₀ ∈ Y_infty ∪ {sY_infty} := Or.inl hmem
  have hYs_min : ∀ x ∈ Y_infty ∪ {sY_infty}, x₀ ≤ x := by
    intro x hx
    rcases hx with (hxY | hx_s)
    · exact hmin hxY
    · subst hx_s
      exact (h_strict_ub x₀ hmem).le
  have hYs_Ω₀ : (Y_infty ∪ {sY_infty}) ∈ Ω₀ := by
    simpa [-Set.union_singleton, Ω₀, hYs_total, hYs_well, hYs_mem]
  specialize hs ⟨ _, hY_inftyΩ₀ ⟩
  simp [IsStrictUpperBound.iff] at hs
  have hYs_Ω : ⟨ _, hYs_Ω₀ ⟩ ∈ Ω := by
    simp [Ω, -Set.mem_insert_iff, -and_imp]
    intro x hx hxx₀
    rcases hx with rfl | hx
    . unfold sY_infty; congr 1
      symm; apply Subtype.val_injective; convert hF _
      . ext; simp; constructor
        . grind
        rintro ⟨ _ | _, _ ⟩
        . order
        assumption
      simp; specialize hs (y := x₀) (by simp [hmem]); order
    have hx' := hx; simp [Y_infty] at hx'; obtain ⟨ Y, ⟨hYΩ₀, hYΩ⟩, hxY ⟩ := hx'
    have hYΩ' := hYΩ; simp [Ω] at hYΩ
    convert hYΩ _ hxY hxx₀ using 2
    apply Subtype.val_injective
    rw [hF, hF]
    . ext y; simp [Y_infty]; intro hyx; constructor
      . rintro (rfl | ⟨ Y', ⟨hY'Ω₀, hY'Ω⟩, hyY' ⟩)
        . specialize hs _ hx; order
        by_contra!
        specialize ex_8_5_13 (Y := ⟨_, hYΩ'⟩) (Y' := ⟨_, hY'Ω⟩) y (by grind)
        rw [IsStrictUpperBound.iff] at ex_8_5_13
        specialize ex_8_5_13 x (by simp [hxY]); order
      grind
    all_goals simp [hxY, hx, hxx₀]
  have hs_mem : sY_infty ∈ Y_infty := Set.mem_iUnion_of_mem ⟨ _, hYs_Ω ⟩ (by simp)
  specialize hs _ hs_mem; order


/-- Lemma 8.5.15 (Zorn's lemma) / Exercise 8.5.14 -/
theorem Zorns_lemma {X:Type} [PartialOrder X] [Nonempty X]
  (hchain: ∀ Y:Set X, IsTotal Y ∧ Y.Nonempty → ∃ x, IsUpperBound Y x) : ∃ x:X, IsMax x := by
  let ⟨a⟩ := ‹Nonempty X›
  rcases WellFoundedLT.partialOrder a with ⟨Y, hYtotal, hYwf, hmin_ex, hno_strict_ub⟩
  rcases hmin_ex with ⟨haY, hamin⟩
  have hYnonempty : Y.Nonempty := ⟨a, haY⟩
  rcases hchain Y ⟨hYtotal, hYnonempty⟩ with ⟨u, hu_ub⟩
  refine ⟨u, ?_⟩
  rw [IsMax.iff]
  intro h_lt
  rcases h_lt with ⟨v, huv⟩
  have hv_ub : IsUpperBound Y v := by
    intro y hy
    exact le_trans (hu_ub y hy) (le_of_lt huv)
  have hv_notin : v ∉ Y := by
    intro hvY
    have hv_le_u : v ≤ u := hu_ub v hvY
    have : u < u := lt_of_lt_of_le huv hv_le_u
    exact lt_irrefl u this
  have hv_strict_ub : IsStrictUpperBound Y v := ⟨hv_ub, hv_notin⟩
  apply hno_strict_ub
  exact ⟨v, hv_strict_ub⟩

/-- Exercise 8.5.1 -/
def empty_set_partial_order [h₀: LE Empty] : Decidable (∃ h : PartialOrder Empty, h.le = h₀.le) := by
  apply isTrue
  haveI : Preorder Empty := {
    le := h₀.le
    le_refl := λ x => x.elim
    le_trans := λ x => x.elim
    lt_iff_le_not_ge := λ x => x.elim
  }
  refine ⟨{ le_antisymm := λ x => x.elim }, ?_⟩
  ext x; exact x.elim

def empty_set_linear_order [h₀: LE Empty] : Decidable (∃ h : LinearOrder Empty, h.le = h₀.le) := by
  apply isTrue
  haveI : Preorder Empty := {
    le := h₀.le
    le_refl := λ x => x.elim
    le_trans := λ x => x.elim
    lt_iff_le_not_ge := λ x => x.elim
  }
  refine ⟨{
    le_antisymm := λ x => x.elim
    le_total := λ x => x.elim
    toDecidableLE := λ x => x.elim
    toDecidableEq := λ x => x.elim
    toDecidableLT := λ x => x.elim
    min := λ x => x.elim
    max := λ x => x.elim
    compare := λ x => x.elim
    min_def := λ x => x.elim
    max_def := λ x => x.elim
    compare_eq_compareOfLessAndEq := λ x => x.elim
  }, ?_⟩
  ext x; exact x.elim

def empty_set_well_order [h₀: LT Empty]: Decidable (Nonempty (WellFoundedLT Empty)) := by
  have hwf : WellFounded (α := Empty) (· < ·) := WellFounded.intro (λ x => x.elim)
  have hwflt : WellFoundedLT Empty := IsWellFounded.mk hwf
  apply isTrue
  exact ⟨hwflt⟩

/-- Exercise 8.5.2 -/
example : ∃ (X:Type) (_ : LE X), (∀ x:X, x ≤ x) ∧ (∀ x y:X, x ≤ y → y ≤ x → x = y) ∧ ¬ (∀ x y z:X, x ≤ y → y ≤ z → x ≤ z) := by
  refine ⟨Fin 3, ⟨λ a b : Fin 3 =>
    a = b ∨ (a = (0 : Fin 3) ∧ b = (1 : Fin 3)) ∨ (a = (1 : Fin 3) ∧ b = (2 : Fin 3))⟩, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro x; exact Or.inl rfl
  · intro x y hxy hyx
    rcases hxy with (h | h | h)
    · exact h
    · rcases h with ⟨hx0, hy1⟩
      rcases hyx with (h' | h' | h')
      · exact h'.symm
      · rcases h' with ⟨hy0, hx1⟩; exfalso; exact (by decide : (1 : Fin 3) ≠ (0 : Fin 3)) (hy1.symm.trans hy0)
      · rcases h' with ⟨hy1', hx2⟩; exfalso; exact (by decide : (0 : Fin 3) ≠ (2 : Fin 3)) (hx0.symm.trans hx2)
    · rcases h with ⟨hx1, hy2⟩
      rcases hyx with (h' | h' | h')
      · exact h'.symm
      · rcases h' with ⟨hy0, hx1'⟩; exfalso; exact (by decide : (0 : Fin 3) ≠ (2 : Fin 3)) (hy0.symm.trans hy2)
      · rcases h' with ⟨hy1', hx2⟩; exfalso; exact (by decide : (1 : Fin 3) ≠ (2 : Fin 3)) (hy1'.symm.trans hy2)
  · intro h_trans
    have h01 : (0 : Fin 3) = (1 : Fin 3) ∨ ((0 : Fin 3) = (0 : Fin 3) ∧ (1 : Fin 3) = (1 : Fin 3)) ∨ ((0 : Fin 3) = (1 : Fin 3) ∧ (1 : Fin 3) = (2 : Fin 3)) :=
      Or.inr (Or.inl ⟨rfl, rfl⟩)
    have h12 : (1 : Fin 3) = (2 : Fin 3) ∨ ((1 : Fin 3) = (0 : Fin 3) ∧ (2 : Fin 3) = (1 : Fin 3)) ∨ ((1 : Fin 3) = (1 : Fin 3) ∧ (2 : Fin 3) = (2 : Fin 3)) :=
      Or.inr (Or.inr ⟨rfl, rfl⟩)
    have h02 := h_trans 0 1 2 h01 h12
    rcases h02 with (h | h | h)
    · exact (by decide : (0 : Fin 3) ≠ (2 : Fin 3)) h
    · rcases h with ⟨_, hneq⟩; exact (by decide : (1 : Fin 3) ≠ (2 : Fin 3)) hneq.symm
    · rcases h with ⟨h01', _⟩; exact (by decide : (0 : Fin 3) ≠ (1 : Fin 3)) h01'

example : ∃ (X:Type) (_ : LE X), (∀ x:X, x ≤ x) ∧ (∀ x y z:X, x ≤ y → y ≤ z → x ≤ z) ∧ ¬ (∀ x y:X, x ≤ y → y ≤ x → x = y) := by
  refine ⟨Fin 2, ⟨λ _ _ : Fin 2 => True⟩, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro x; trivial
  · intro x y z _ _; trivial
  · intro h_anti
    have h_eq : (0 : Fin 2) = (1 : Fin 2) := h_anti 0 1 trivial trivial
    exact (by decide : (0 : Fin 2) ≠ (1 : Fin 2)) h_eq

example : ∃ (X:Type) (_ : LE X), (∀ x y:X, x ≤ y → y ≤ x → x = y) ∧ (∀ x y z:X, x ≤ y → y ≤ z → x ≤ z) ∧ ¬ (∀ x:X, x ≤ x) := by
  refine ⟨Fin 1, ⟨λ _ _ : Fin 1 => False⟩, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy hyx; exact hxy.elim
  · intro x y z hxy hyz; exact hxy.elim
  · intro h_refl; exact h_refl 0

/-- Exercise 8.5.3: The divisibility ordering on PNat. -/
@[reducible] def PNat.divOrder : PartialOrder PNat where
  le x y := ∃ n : PNat, y = n * x
  lt x y := (∃ n : PNat, y = n * x) ∧ ¬∃ n : PNat, x = n * y
  le_refl := fun x => ⟨1, by simp⟩
  le_antisymm := by
    intro x y ⟨n, hn⟩ ⟨m, hm⟩
    have h1 : (y : ℕ) = (n : ℕ) * (x : ℕ) := by exact_mod_cast hn
    have h2 : (x : ℕ) = (m : ℕ) * (y : ℕ) := by exact_mod_cast hm
    have hnm : (n : ℕ) * (m : ℕ) = 1 := by
      have h3 : (y : ℕ) = ((n : ℕ) * (m : ℕ)) * (y : ℕ) := by
        calc
          (y : ℕ) = (n : ℕ) * (x : ℕ) := h1
          _ = (n : ℕ) * ((m : ℕ) * (y : ℕ)) := by rw [h2]
          _ = ((n : ℕ) * (m : ℕ)) * (y : ℕ) := by ring
      have hy_pos : 0 < (y : ℕ) := y.property
      nlinarith
    have hn1 : (n : ℕ) = 1 := by
      have hndiv : (n : ℕ) ∣ 1 := by
        rw [← hnm]
        exact ⟨(m : ℕ), rfl⟩
      exact Nat.eq_one_of_dvd_one hndiv
    apply PNat.eq
    calc
      (x : ℕ) = 1 * (x : ℕ) := by simp
      _ = (n : ℕ) * (x : ℕ) := by rw [hn1]
      _ = (y : ℕ) := h1.symm
  le_trans := by
    intro x y z ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨m * n, ?_⟩
    calc
      z = m * y := hm
      _ = m * (n * x) := by rw [hn]
      _ = (m * n) * x := by ring
  lt_iff_le_not_ge := fun _ _ ↦ Iff.rfl

theorem PNat.divOrder_exists :
    ∃ (h₀ : PartialOrder PNat), h₀.le = (fun x y ↦ ∃ n, y = n * x) :=
  ⟨PNat.divOrder, rfl⟩

theorem PNat.divOrder_not_linear :
    ¬∃ (h₀ : LinearOrder PNat), h₀.le = (fun x y ↦ ∃ n, y = n * x) := by
  intro h
  rcases h with ⟨h_lin, h_le⟩
  have h_total : ∀ x y : PNat, (∃ n : PNat, y = n * x) ∨ (∃ n : PNat, x = n * y) := by
    intro x y
    have htotal := h_lin.le_total x y
    simpa [h_le] using htotal
  rcases h_total 2 3 with (⟨n, hn⟩ | ⟨n, hn⟩)
  · -- 3 = n * 2
    have hn' : (3 : ℕ) = (n : ℕ) * (2 : ℕ) := by exact_mod_cast hn
    omega
  · -- 2 = n * 3
    have hn' : (2 : ℕ) = (n : ℕ) * (3 : ℕ) := by exact_mod_cast hn
    omega

/-- Exercise 8.5.4 -/
example : ¬ ∃ x : {x:ℝ| x > 0}, IsMin x := by
  rintro ⟨x, hmin⟩
  have hxpos : x.val > 0 := x.property
  have hhalf_pos : x.val / 2 > 0 := by linarith
  have hhalf_lt : x.val / 2 < x.val := by linarith
  have : IsMin x := hmin
  rw [IsMin.iff] at this
  push_neg at this
  have hle := this ⟨x.val / 2, hhalf_pos⟩
  have hle' : x.val ≤ x.val / 2 := Subtype.mk_le_mk.mp hle
  linarith

/-- Exercise 8.5.5 -/
example {X Y:Type} [PartialOrder Y] (f:X → Y) : ∃ h₀: PartialOrder X, h₀.le = (fun x y ↦ f x < f y ∨ x = y) := by
  let h₀ : PartialOrder X := {
    le := λ x y => f x < f y ∨ x = y
    lt := λ x y => f x < f y
    le_refl := λ x => Or.inr rfl
    le_antisymm := by
      intro x y h₁ h₂
      rcases h₁ with (hlt | heq)
      · rcases h₂ with (hlt' | heq')
        · exact (lt_asymm hlt hlt').elim
        · exact heq'.symm
      · exact heq
    le_trans := by
      intro x y z h₁ h₂
      rcases h₁ with (hlt | heq)
      · rcases h₂ with (hlt' | heq')
        · exact Or.inl (lt_trans hlt hlt')
        · exact Or.inl (heq' ▸ hlt)
      · exact heq ▸ h₂
    lt_iff_le_not_ge := by
      intro x y
      constructor
      · intro hlt
        constructor
        · exact Or.inl hlt
        · intro h
          rcases h with (hlt' | heq)
          · exact lt_asymm hlt hlt'
          · rw [heq] at hlt
            exact lt_irrefl (f x) hlt
      · intro ⟨h₁, h₂⟩
        rcases h₁ with (hlt | heq)
        · exact hlt
        · exfalso
          apply h₂
          exact Or.inr heq.symm
  }
  refine ⟨h₀, rfl⟩

def Ex_8_5_5_b : Decidable (∀ (X Y:Type) (_ : LinearOrder Y) (f:X → Y), ∃ h₀: LinearOrder X, h₀.le = (fun x y ↦ f x < f y ∨ x = y)) := by
  apply isFalse
  intro H
  specialize H (Fin 2) ℕ (by infer_instance) (λ _ => 0)
  rcases H with ⟨h_lin, h_le⟩
  have h_total : h_lin.le (0 : Fin 2) 1 ∨ h_lin.le (1 : Fin 2) 0 := h_lin.le_total 0 1
  rcases h_total with (hle | hle)
  · rw [h_le] at hle
    simp at hle
  · rw [h_le] at hle
    simp at hle

-- Final part of Exercise 8.5.5; if the answer to the previous part is "no", modify the hypotheses to make it true.

/-- Exercise 8.5.6 -/
abbrev OrderIdeals (X: Type) [PartialOrder X] : Set (Set X) := .Iic '' (.univ : Set X)

noncomputable def OrderIdeals.iso {X: Type} [PartialOrder X] : X ≃o OrderIdeals X :=
  let f : X → OrderIdeals X := λ x => ⟨.Iic x, by simp [OrderIdeals]⟩
  have h_inj : Function.Injective f := by
    intro a b h
    have h_eq : Set.Iic a = Set.Iic b := by
      simpa [f] using congr_arg Subtype.val h
    apply le_antisymm
    · have ha : a ∈ Set.Iic a := le_refl a; rw [h_eq] at ha; exact ha
    · have hb : b ∈ Set.Iic b := le_refl b; rw [← h_eq] at hb; exact hb
  have h_surj : Function.Surjective f := by
    intro S
    rcases S.property with ⟨x, _, hx⟩
    use x
    ext; dsimp [f]; simp [hx]
  {
    toFun := f
    invFun := λ S =>
      have hS : ∃ x, Set.Iic x = S.val := by
        simpa [OrderIdeals, Set.mem_image] using S.property
      Classical.choose hS
    left_inv := λ x => by
      have hS : ∃ y, Set.Iic y = Set.Iic x := ⟨x, rfl⟩
      apply h_inj
      dsimp [f]
      have h_choose : Set.Iic (Classical.choose hS) = Set.Iic x := Classical.choose_spec hS
      ext; simp [h_choose]
    right_inv := λ S => by
      have hS : ∃ x, Set.Iic x = S.val := by
        simpa [OrderIdeals, Set.mem_image] using S.property
      have h_choose : Set.Iic (Classical.choose hS) = S.val := Classical.choose_spec hS
      ext; dsimp [f]; simp [h_choose]
    map_rel_iff' := λ {a b} => by
      simp [f, Subtype.mk_le_mk, Set.subset_def, Set.mem_Iic]
      exact ⟨λ h => h a (le_refl a), λ h c hc => le_trans hc h⟩
  }

/-- Exercise 8.5.7 -/
example {Y:Type} [LinearOrder Y] {x y:Y} (hx: IsMin x) (hy: IsMin y) : x = y := by
  rcases le_total x y with (h | h)
  · have hy' := hy h; exact le_antisymm h hy'
  · have hx' := hx h; exact le_antisymm hx' h

example {Y:Type} [LinearOrder Y] {x y:Y} (hx: IsMax x) (hy: IsMax y) : x = y := by
  rcases le_total x y with (h | h)
  · have hx' := hx h; exact le_antisymm h hx'
  · have hy' := hy h; exact le_antisymm hy' h

/-- Exercise 8.5.9 -/
example {X:Type} [LinearOrder X] (hmin: ∀ Y: Set X, Y.Nonempty → ∃ x:Y, IsMin x) (hmax: ∀ Y: Set X, Y.Nonempty → ∃ x:Y, IsMax x) : Finite X := by
  by_contra! hFin
  have hInfinite : Infinite X := hFin
  haveI : Nonempty X := inferInstance
  have hwf : WellFounded (· < · : X → X → Prop) := by
    have : WellFoundedLT X := (WellFoundedLT.iff X).mpr hmin
    exact wellFounded_lt
  -- For any Finset s, find the maximum element of X \ s
  have h_max_of_compl (s : Finset X) : ∃ m : X, m ∉ s ∧ ∀ x, x ∉ s → x ≤ m := by
    have h_nonempty : {x | x ∉ (s : Set X)}.Nonempty := by
      rcases Finset.exists_notMem s with ⟨a, ha⟩
      exact ⟨a, ha⟩
    rcases hmax {x | x ∉ (s : Set X)} h_nonempty with ⟨x', hx'⟩
    refine ⟨x'.val, x'.property, λ z hz => ?_⟩
    rcases le_total x'.val z with (hle | hle)
    · have hx'_le_hz' : x' ≤ (⟨z, hz⟩ : {x | x ∉ (s : Set X)}) := Subtype.mk_le_mk.mpr hle
      have hz'_le_x' : (⟨z, hz⟩ : {x | x ∉ (s : Set X)}) ≤ x' := hx' hx'_le_hz'
      exact Subtype.mk_le_mk.mp hz'_le_x'
    · exact hle
  -- Extract the max-of-complement as a function with its properties
  let max_compl (s : Finset X) : X := Classical.choose (h_max_of_compl s)
  have max_compl_not_mem (s : Finset X) : max_compl s ∉ s :=
    (Classical.choose_spec (h_max_of_compl s)).1
  have max_compl_is_max (s : Finset X) : ∀ x, x ∉ s → x ≤ max_compl s :=
    (Classical.choose_spec (h_max_of_compl s)).2
  -- Build a decreasing sequence: s_n = {f 0, ..., f (n-1)}, f n = max of (s n)ᶜ
  let s : ℕ → Finset X :=
    Nat.rec (∅ : Finset X) (fun _ prev => prev ∪ {max_compl prev})
  let f : ℕ → X := fun n => max_compl (s n)
  have hs_succ (n : ℕ) : s (n+1) = s n ∪ {f n} := by
    simp [s, f, max_compl]
  have hf_succ_lt (n : ℕ) : f (n+1) < f n := by
    have h_not_mem_succ : f (n+1) ∉ s (n+1) := max_compl_not_mem (s (n+1))
    rw [hs_succ n] at h_not_mem_succ
    have h_not_mem_s : f (n+1) ∉ s n := by
      intro h; apply h_not_mem_succ; exact Finset.mem_union_left _ h
    have h_ne : f (n+1) ≠ f n := by
      intro heq; apply h_not_mem_succ
      rw [heq]; exact Finset.mem_union_right _ (Finset.mem_singleton.mpr rfl)
    have hle : f (n+1) ≤ f n := max_compl_is_max (s n) (f (n+1)) h_not_mem_s
    exact lt_of_le_of_ne hle h_ne
  -- The infinite decreasing chain contradicts well-foundedness of <
  rcases WellFounded.wellFounded_iff_has_min.mp hwf (Set.range f) (Set.range_nonempty _) with
    ⟨a, ha, ha_min⟩
  rcases ha with ⟨k, rfl⟩
  apply ha_min (f (k+1)) ⟨k+1, rfl⟩ (hf_succ_lt k)


/-- Exercise 8.5.12.  Here we make a copy of Mathlib's {name}`Lex` wrapper for lexicographical orderings.  This wrapper is needed
because products `X × Y` of ordered sets are given the default instance of the product partial order instead of
the lexicographical one. -/
def Lex' (α : Type) := α

instance Lex'.partialOrder {X Y: Type} [PartialOrder X] [PartialOrder Y] : PartialOrder (Lex' (X × Y)) := {
  le := fun ⟨ x, y ⟩ ⟨ x', y' ⟩ ↦ (x < x') ∨ (x = x' ∧ y ≤ y')
  le_refl := by rintro ⟨x, y⟩; exact Or.inr ⟨rfl, le_refl y⟩
  le_antisymm := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ (h | ⟨hx, hy⟩) (h' | ⟨hx', hy'⟩)
    · exact (lt_asymm h h').elim
    · rw [hx'] at h; exact (lt_irrefl _ h).elim
    · rw [hx] at h'; exact (lt_irrefl _ h').elim
    · subst hx
      have : y = y' := le_antisymm hy hy'
      subst this; rfl
  le_trans := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ ⟨x'', y''⟩ (h1 | ⟨hx, hy⟩) (h2 | ⟨hx', hy'⟩)
    · exact Or.inl (lt_trans h1 h2)
    · subst hx'; exact Or.inl h1
    · subst hx; exact Or.inl h2
    · subst hx; subst hx'; exact Or.inr ⟨rfl, le_trans hy hy'⟩
}

instance Lex'.linearOrder {X Y:Type} [LinearOrder X] [LinearOrder Y] : LinearOrder (Lex' (X × Y)) :=
  { Lex'.partialOrder with
    le_total := by
      rintro ⟨x, y⟩ ⟨x', y'⟩
      rcases lt_trichotomy x x' with (h | h | h)
      · exact Or.inl (Or.inl h)
      · rw [h]
        rcases le_total y y' with (h' | h')
        · exact Or.inl (Or.inr ⟨rfl, h'⟩)
        · exact Or.inr (Or.inr ⟨rfl, h'⟩)
      · exact Or.inr (Or.inl h)
    toDecidableLE := λ a b => show Decidable ((a.1 < b.1) ∨ (a.1 = b.1 ∧ a.2 ≤ b.2)) from inferInstance
    toDecidableEq := inferInstanceAs (DecidableEq (X × Y))
    toDecidableLT := λ a b => show Decidable (((a.1 < b.1) ∨ (a.1 = b.1 ∧ a.2 ≤ b.2)) ∧ ¬((b.1 < a.1) ∨ (b.1 = a.1 ∧ b.2 ≤ a.2))) from inferInstance
  }

lemma Lex'.lt_iff {X Y: Type} [LinearOrder X] [LinearOrder Y] (a b : Lex' (X × Y)) :
    a < b ↔ (a.1 < b.1) ∨ (a.1 = b.1 ∧ a.2 < b.2) := by
  rcases a with ⟨x, y⟩
  rcases b with ⟨x', y'⟩
  simp
  constructor
  · intro hlt
    rcases hlt with ⟨hle, hnle⟩
    rcases hle with (hlt_x | ⟨hx, hle_y⟩)
    · exact Or.inl hlt_x
    · have h_notle : ¬ y' ≤ y := by
        intro hle'
        apply hnle
        exact Or.inr ⟨hx.symm, hle'⟩
      have hlt_y : y < y' := lt_of_not_ge h_notle
      exact Or.inr ⟨hx, hlt_y⟩
  · intro h
    rcases h with (hlt_x | ⟨hx, hlt_y⟩)
    · refine ⟨Or.inl hlt_x, ?_⟩
      intro hle'
      rcases hle' with (hlt_x' | ⟨hx', hle_y⟩)
      · exact lt_asymm hlt_x hlt_x'
      · rw [hx'] at hlt_x; exact lt_irrefl _ hlt_x
    · refine ⟨Or.inr ⟨hx, le_of_lt hlt_y⟩, ?_⟩
      intro hle'
      rcases hle' with (hlt_x' | ⟨hx', hle_y⟩)
      · rw [hx] at hlt_x'; exact lt_irrefl _ hlt_x'
      · have : y < y := lt_of_lt_of_le hlt_y hle_y
        exact lt_irrefl _ this

instance Lex'.WellFoundedLT {X Y:Type} [LinearOrder X] [WellFoundedLT X] [LinearOrder Y] [WellFoundedLT Y]:
  WellFoundedLT (Lex' (X × Y)) := by
  have hwf : WellFounded (Prod.Lex ((· < ·) : X → X → Prop) ((· < ·) : Y → Y → Prop)) :=
    WellFounded.prod_lex (wellFounded_lt (α := X)) (wellFounded_lt (α := Y))
  have h_eq : (fun (a b : Lex' (X × Y)) => a < b) = (fun (a b : Lex' (X × Y)) => Prod.Lex (· < ·) (· < ·) a b) := by
    ext a b
    rw [Lex'.lt_iff, Prod.lex_iff]
  have hwf' : WellFounded (fun (a b : Lex' (X × Y)) => a < b) := by
    rw [h_eq]
    exact hwf
  exact ⟨hwf'⟩


/-- Exercise 8.5.15 -/
theorem inj_trichotomy {X Y : Type}
    (h : ¬∃ f : X → Y, Function.Injective f) :
    ∃ g : Y → X, Function.Injective g := by
  have h_no_emb : ¬ Nonempty (X ↪ Y) := by
    rintro ⟨f⟩
    apply h
    exact ⟨f, f.injective⟩
  have h_no_le : ¬ Cardinal.mk X ≤ Cardinal.mk Y := by
    rw [Cardinal.le_def]
    exact h_no_emb
  rcases le_total (Cardinal.mk X) (Cardinal.mk Y) with (hle | hle)
  · exact absurd hle h_no_le
  · rw [Cardinal.le_def] at hle
    rcases hle with ⟨f⟩
    exact ⟨f, f.injective⟩

/-- Exercise 8.5.16: The set of partial orderings on X, ordered by "coarser than",
is itself a partial order. -/
instance PartialOrder.coarserOrder (X : Type) : PartialOrder (PartialOrder X) where
  le p1 p2 := ∀ x y : X, p1.le x y → p2.le x y
  le_refl := by simp
  le_trans p1 p2 p3 h12 h23 := fun x y h => h23 x y (h12 x y h)
  le_antisymm p1 p2 h12 h21 := by ext x y; exact ⟨h12 x y, h21 x y⟩

/-- The divisibility ordering on PNat is coarser than the usual ordering. -/
example : PNat.divOrder ≤ (inferInstance : PartialOrder PNat) := by
  intro x y h
  obtain ⟨n, rfl⟩ := h
  show x ≤ n * x
  exact Nat.le_mul_of_pos_left x n.pos

/-- The discrete ordering (x ≤ y ↔ x = y) is the unique minimal element. -/
@[reducible] def PartialOrder.discrete (X : Type) : PartialOrder X where
  le x y := x = y
  le_refl := fun _ ↦ rfl
  le_antisymm := fun _ _ h _ ↦ h
  le_trans := fun _ _ _ h1 h2 ↦ h1.trans h2

theorem PartialOrder.discrete_isBot (X : Type) (p : PartialOrder X) :
    PartialOrder.discrete X ≤ p := by
  intro x y h_eq
  -- h_eq : (discrete X).le x y, i.e. x = y
  cases h_eq
  exact p.le_refl x

theorem PartialOrder.discrete_isMin (X : Type) :
    @IsMin (PartialOrder X) (coarserOrder X).toPreorder.toLE
      (PartialOrder.discrete X) := by
  intro q hq x y h_eq
  cases h_eq
  exact q.le_refl x

theorem PartialOrder.discrete_unique_min (X : Type) (p : PartialOrder X)
    (h : @IsMin (PartialOrder X) (coarserOrder X).toPreorder.toLE p) :
    p = discrete X := by
  have h_disc_le_p : discrete X ≤ p := discrete_isBot X p
  have h_p_le_disc : p ≤ discrete X := h h_disc_le_p
  exact le_antisymm h_p_le_disc h_disc_le_p

/-- A partial ordering is maximal in the coarser order iff it is total. -/
theorem PartialOrder.isMax_iff_isTotal (X : Type) (p : PartialOrder X) :
    @IsMax (PartialOrder X) (coarserOrder X).toPreorder.toLE p ↔
    @IsTotal X p := by
  constructor
  · intro h_max x y
    by_cases hxy : p.le x y
    · exact Or.inl hxy
    · by_cases hyx : p.le y x
      · exact Or.inr hyx
      · let le_q (a b : X) : Prop := p.le a b ∨ (p.le a x ∧ p.le y b)
        let q : PartialOrder X := {
          le := le_q
          lt := λ a b => le_q a b ∧ ¬ le_q b a
          le_refl := λ a => Or.inl (p.le_refl a)
          le_trans := by
            intro a b c h_ab h_bc
            rcases h_ab with (h_ab_p | ⟨h_ax, h_yb⟩)
            · rcases h_bc with (h_bc_p | ⟨h_bx, h_yc⟩)
              · exact Or.inl (p.le_trans a b c h_ab_p h_bc_p)
              · exact Or.inr ⟨p.le_trans a b x h_ab_p h_bx, h_yc⟩
            · rcases h_bc with (h_bc_p | ⟨h_bx, h_yc⟩)
              · exact Or.inr ⟨h_ax, p.le_trans y b c h_yb h_bc_p⟩
              · exfalso
                exact hyx (p.le_trans y b x h_yb h_bx)
          le_antisymm := by
            intro a b h_ab h_ba
            rcases h_ab with (h_ab_p | ⟨h_ax, h_yb⟩)
            · rcases h_ba with (h_ba_p | ⟨h_bx, h_ya⟩)
              · exact p.le_antisymm a b h_ab_p h_ba_p
              · exfalso
                exact hyx (p.le_trans y b x (p.le_trans y a b h_ya h_ab_p) h_bx)
            · rcases h_ba with (h_ba_p | ⟨h_bx, h_ya⟩)
              · exfalso
                exact hyx (p.le_trans y b x h_yb (p.le_trans b a x h_ba_p h_ax))
              · exfalso
                exact hyx (p.le_trans y b x h_yb h_bx)
          lt_iff_le_not_ge := λ a b => Iff.rfl
        }
        have h_p_le_q : p ≤ q := λ a b h => Or.inl h
        have h_max' : q ≤ p := h_max h_p_le_q
        have h_qxy : le_q x y := Or.inr ⟨p.le_refl x, p.le_refl y⟩
        have h_pxy : p.le x y := h_max' x y h_qxy
        exfalso; exact hxy h_pxy
  · intro h_total q hq x y hqxy
    by_contra! h_not
    have h_total_xy : p.le x y ∨ p.le y x := h_total x y
    rcases h_total_xy with (hpxy | hpyx)
    · exact h_not hpxy
    · have hqyx : q.le y x := hq y x hpyx
      have h_eq : x = y := q.le_antisymm x y hqxy hqyx
      rcases h_eq with rfl
      exact h_not (p.le_refl x)

/-- Any partial ordering extends to a total ordering (by Zorn's lemma). -/
theorem PartialOrder.extends_to_total (X : Type) (p : PartialOrder X) :
    ∃ q : PartialOrder X, p ≤ q ∧ @IsTotal X q := by
  let S := {q : PartialOrder X // p ≤ q}
  have hS_nonempty : Nonempty S := ⟨⟨p, le_refl p⟩⟩
  haveI : Nonempty S := hS_nonempty
  have h_chain : ∀ (C : Set S), IsTotal C ∧ C.Nonempty → ∃ ub : S, IsUpperBound C ub := by
    intro C ⟨hC_total, hC_ne⟩
    rcases hC_ne with ⟨q0, hq0⟩
    let ub_val : PartialOrder X := {
      le a b := ∃ q ∈ C, q.val.le a b
      lt := λ a b => (∃ q ∈ C, q.val.le a b) ∧ ¬(∃ q ∈ C, q.val.le b a)
      le_refl := λ a => ⟨q0, hq0, q0.val.le_refl a⟩
      le_trans := by
        intro a b c ⟨q1, hq1, h_ab⟩ ⟨q2, hq2, h_bc⟩
        have h_chain_or : q1.val ≤ q2.val ∨ q2.val ≤ q1.val := by
          have h := hC_total (⟨q1, hq1⟩ : C) (⟨q2, hq2⟩ : C)
          simpa [S] using h
        rcases h_chain_or with (h_le | h_le)
        · have h_ab_q2 : q2.val.le a b := h_le a b h_ab
          have h_bc_q2 : q2.val.le b c := h_bc
          exact ⟨q2, hq2, q2.val.le_trans a b c h_ab_q2 h_bc_q2⟩
        · have h_bc_q1 : q1.val.le b c := h_le b c h_bc
          have h_ab_q1 : q1.val.le a b := h_ab
          exact ⟨q1, hq1, q1.val.le_trans a b c h_ab_q1 h_bc_q1⟩
      le_antisymm := by
        intro a b ⟨q1, hq1, h_ab⟩ ⟨q2, hq2, h_ba⟩
        have h_chain_or : q1.val ≤ q2.val ∨ q2.val ≤ q1.val := by
          have h := hC_total (⟨q1, hq1⟩ : C) (⟨q2, hq2⟩ : C)
          simpa [S] using h
        rcases h_chain_or with (h_le | h_le)
        · have h_ab_q2 : q2.val.le a b := h_le a b h_ab
          exact q2.val.le_antisymm a b h_ab_q2 h_ba
        · have h_ba_q1 : q1.val.le b a := h_le b a h_ba
          exact q1.val.le_antisymm a b h_ab h_ba_q1
      lt_iff_le_not_ge := λ a b => Iff.rfl
    }
    have h_p_le_ub : p ≤ ub_val := by
      intro a b h_pab
      have h_q0ab : q0.val.le a b := q0.property a b h_pab
      exact ⟨q0, hq0, h_q0ab⟩
    let hub : S := ⟨ub_val, h_p_le_ub⟩
    have h_ub_upper : IsUpperBound C hub := by
      intro q hqC
      have h_val_le : q.val ≤ ub_val := by
        intro a b h_qab
        exact ⟨q, hqC, h_qab⟩
      cases q; rename_i q_val q_prop
      apply Subtype.mk_le_mk.mpr
      simpa using h_val_le
    refine ⟨hub, h_ub_upper⟩
  rcases Zorns_lemma h_chain with ⟨⟨q, hq⟩, hq_max⟩
  refine ⟨q, hq, ?_⟩
  have h_max_q : @IsMax (PartialOrder X) (coarserOrder X).toPreorder.toLE q := by
    intro r hr
    have h_pr : p ≤ r := le_trans hq hr
    have h_q_le_rS : (⟨q, hq⟩ : S) ≤ (⟨r, h_pr⟩ : S) := hr
    have h_rS_le_q : (⟨r, h_pr⟩ : S) ≤ (⟨q, hq⟩ : S) := hq_max h_q_le_rS
    simpa using h_rS_le_q
  exact ((isMax_iff_isTotal X q).mp h_max_q)

/-- Exercise 8.5.17: Use Zorn's lemma to reprove Exercise 8.4.2 -/
theorem exists_set_singleton_intersect' {I U : Type} {X : I → Set U}
    (h : Set.PairwiseDisjoint .univ X) (hne : ∀ α, Nonempty (X α)) :
    ∃ Y : Set U, ∀ α, Nat.card (Y ∩ X α : Set U) = 1 := by
  let Ωset := { Y : Set U | ∀ α, (Y ∩ X α).Subsingleton }
  let Ω : Type := Subtype (· ∈ Ωset)
  haveI : Nonempty Ω := ⟨⟨∅, λ α x hx _ => hx.1.elim⟩⟩
  have h_chain : ∀ (C : Set Ω), IsTotal C ∧ C.Nonempty → ∃ ub : Ω, IsUpperBound C ub := by
    intro C ⟨hC_total, hC_ne⟩
    let ub_val : Set U := ⋃₀ (Subtype.val '' C)
    have hub_subsingleton : ∀ α, (ub_val ∩ X α).Subsingleton := by
      intro α x hx y hy
      rcases hx with ⟨hx_ub, hx_X⟩
      rcases hy with ⟨hy_ub, hy_X⟩
      rw [Set.mem_sUnion] at hx_ub hy_ub
      rcases hx_ub with ⟨Sx, hSx_mem, hxSx⟩
      rcases hy_ub with ⟨Sy, hSy_mem, hySy⟩
      rw [Set.mem_image] at hSx_mem hSy_mem
      rcases hSx_mem with ⟨⟨Yx, hYx_prop⟩, hYxC, hSx_eq⟩
      rcases hSy_mem with ⟨⟨Yy, hYy_prop⟩, hYyC, hSy_eq⟩
      subst hSx_eq hSy_eq
      have h_compare := hC_total (⟨⟨Yx, hYx_prop⟩, hYxC⟩ : C) (⟨⟨Yy, hYy_prop⟩, hYyC⟩ : C)
      rcases h_compare with (h_le | h_le)
      · have hxYy : x ∈ Yy := h_le hxSx
        exact hYy_prop α ⟨hxYy, hx_X⟩ ⟨hySy, hy_X⟩
      · have hyYx : y ∈ Yx := h_le hySy
        exact hYx_prop α ⟨hxSx, hx_X⟩ ⟨hyYx, hy_X⟩
    have hub_mem_Ωset : ub_val ∈ Ωset := hub_subsingleton
    let hub : Ω := ⟨ub_val, hub_mem_Ωset⟩
    have h_ub_upper : IsUpperBound C hub := by
      intro S hSC x hxS
      rcases S with ⟨S_val, hS_mem⟩
      apply Set.mem_sUnion.mpr
      refine ⟨S_val, Set.mem_image_of_mem Subtype.val hSC, hxS⟩
    refine ⟨hub, h_ub_upper⟩
  rcases Zorns_lemma (X := Ω) h_chain with ⟨⟨Y, hY⟩, hY_max⟩
  use Y
  intro α
  have h_subsingleton : (Y ∩ X α).Subsingleton := hY α
  have h_nonempty : (Y ∩ X α).Nonempty := by
    by_contra h_empty
    rcases hne α with ⟨a, ha⟩
    have ha_notin_Y : a ∉ Y := by
      intro haY
      apply h_empty
      exact ⟨a, haY, ha⟩
    let Y' : Set U := Y ∪ {a}
    have h_empty_eq : Y ∩ X α = ∅ := Set.not_nonempty_iff_eq_empty.mp h_empty
    have hY'_subsingleton : ∀ β, (Y' ∩ X β).Subsingleton := by
      intro β
      by_cases hαβ : α = β
      · subst hαβ
        have hY'_Xα_eq : Y' ∩ X α = ({a} : Set U) := by
          ext z; constructor
          · rintro ⟨hzY', hzXα⟩
            rcases hzY' with (hzY | hz_a)
            · have : z ∈ Y ∩ X α := ⟨hzY, hzXα⟩
              rw [h_empty_eq] at this
              exact this.elim
            · simpa using hz_a
          · intro hz
            have hz_eq_a : z = a := by simpa using hz
            subst hz_eq_a
            exact ⟨Or.inr (by simp), ha⟩
        rw [hY'_Xα_eq]
        intro x hx y hy
        have hx_a : x = a := by simpa using hx
        have hy_a : y = a := by simpa using hy
        rw [hx_a, hy_a]
      · have h_disjoint : Disjoint (X α) (X β) := h (Set.mem_univ α) (Set.mem_univ β) hαβ
        rw [Set.disjoint_iff_inter_eq_empty] at h_disjoint
        have ha_notin_Xβ : a ∉ X β := by
          intro haXβ
          have ha_inter : a ∈ X α ∩ X β := ⟨ha, haXβ⟩
          rw [h_disjoint] at ha_inter
          exact ha_inter.elim
        have hY'_Xβ_eq : Y' ∩ X β = Y ∩ X β := by
          ext z; constructor
          · rintro ⟨hzY', hzXβ⟩
            rcases hzY' with (hzY | hz_a)
            · exact ⟨hzY, hzXβ⟩
            · exfalso
              apply ha_notin_Xβ
              have hz_eq_a : z = a := by simpa using hz_a
              rwa [hz_eq_a] at hzXβ
          · rintro ⟨hzY, hzXβ⟩
            exact ⟨Or.inl hzY, hzXβ⟩
        rw [hY'_Xβ_eq]
        exact hY β
    have hY_sub_Y' : Y ⊆ Y' := by
      intro z hz; exact Or.inl hz
    have hY'_le_Y : Y' ⊆ Y := by
      have hY_max' : ∀ (b : Ω), (⟨Y, hY⟩ : Ω) ≤ b → b ≤ (⟨Y, hY⟩ : Ω) := hY_max
      have hY_le_Y'_Ω : (⟨Y, hY⟩ : Ω) ≤ (⟨Y', hY'_subsingleton⟩ : Ω) := by
        simpa using hY_sub_Y'
      have htemp := hY_max' (⟨Y', hY'_subsingleton⟩ : Ω) hY_le_Y'_Ω
      exact htemp
    have haY' : a ∈ Y' := Set.mem_union_right Y (by simp)
    exact ha_notin_Y (hY'_le_Y haY')
  rcases Set.Subsingleton.eq_empty_or_singleton h_subsingleton with (h_empty' | ⟨a, ha_eq⟩)
  · exact absurd h_empty' h_nonempty.ne_empty
  · rw [ha_eq]
    simp

/-- Exercise 8.5.18 -/
theorem hausdorff_of_zorns_lemma {X : Type} [PartialOrder X] :
    ∃ M : Set X, Maximal (fun (S : Set X) => IsTotal S) M := by
  let Ωset := { S : Set X | IsTotal S }
  let Ω : Type := Subtype (· ∈ Ωset)
  haveI : Nonempty Ω := ⟨⟨∅, λ x y => by exfalso; exact x.property⟩⟩
  have h_chain : ∀ (C : Set Ω), IsTotal C ∧ C.Nonempty → ∃ ub : Ω, IsUpperBound C ub := by
    intro C ⟨hC_total, hC_ne⟩
    let ub_val : Set X := ⋃₀ (Subtype.val '' C)
    have hub_total : IsTotal ub_val := by
      intro x y
      have hx_sUnion := (by
        simpa [ub_val] using x.property : x.val ∈ ⋃₀ (Subtype.val '' C))
      have hy_sUnion := (by
        simpa [ub_val] using y.property : y.val ∈ ⋃₀ (Subtype.val '' C))
      rcases (Set.mem_sUnion.mp hx_sUnion) with ⟨Sx, hSx_mem, hxSx⟩
      rcases (Set.mem_sUnion.mp hy_sUnion) with ⟨Sy, hSy_mem, hySy⟩
      rw [Set.mem_image] at hSx_mem hSy_mem
      rcases hSx_mem with ⟨⟨Sx', hSx'_total⟩, hSx'C, hSx_eq⟩
      rcases hSy_mem with ⟨⟨Sy', hSy'_total⟩, hSy'C, hSy_eq⟩
      have hxSx' : x.val ∈ Sx' := by rwa [← hSx_eq] at hxSx
      have hySy' : y.val ∈ Sy' := by rwa [← hSy_eq] at hySy
      have h_compare := hC_total (⟨⟨Sx', hSx'_total⟩, hSx'C⟩ : C) (⟨⟨Sy', hSy'_total⟩, hSy'C⟩ : C)
      rcases h_compare with (h_le | h_le)
      · have hxSy' : x.val ∈ Sy' := h_le hxSx'
        have h := hSy'_total ⟨x.val, hxSy'⟩ ⟨y.val, hySy'⟩
        simpa using h
      · have hySx' : y.val ∈ Sx' := h_le hySy'
        have h := hSx'_total ⟨x.val, hxSx'⟩ ⟨y.val, hySx'⟩
        simpa using h
    have hub_mem_Ωset : ub_val ∈ Ωset := hub_total
    let hub : Ω := ⟨ub_val, hub_mem_Ωset⟩
    have h_ub_upper : IsUpperBound C hub := by
      intro S hSC x hxS
      rcases S with ⟨S_val, hS_mem⟩
      apply Set.mem_sUnion.mpr
      refine ⟨S_val, Set.mem_image_of_mem Subtype.val hSC, hxS⟩
    refine ⟨hub, h_ub_upper⟩
  rcases Zorns_lemma (X := Ω) h_chain with ⟨⟨M, hM_total⟩, hM_max⟩
  refine ⟨M, hM_total, λ S hS_total hM_sub_S => ?_⟩
  have hM_max' : ∀ (b : Ω), (⟨M, hM_total⟩ : Ω) ≤ b → b ≤ (⟨M, hM_total⟩ : Ω) := hM_max
  have hS_le_M : (⟨S, hS_total⟩ : Ω) ≤ (⟨M, hM_total⟩ : Ω) :=
    hM_max' (⟨S, hS_total⟩ : Ω) (by simpa using hM_sub_S)
  simpa using hS_le_M

theorem zorns_lemma_of_hausdorff {X : Type} [PartialOrder X] [Nonempty X]
    (hhausdorff : ∃ M : Set X, Maximal (fun (S : Set X) => IsTotal S) M)
    (hchain : ∀ Y : Set X, IsTotal Y ∧ Y.Nonempty → ∃ x, IsUpperBound Y x) :
    ∃ x : X, IsMax x := by
  rcases hhausdorff with ⟨M, hM_max⟩
  have hM_total : IsTotal M := hM_max.1
  have hM_maximal : ∀ S : Set X, IsTotal S → M ⊆ S → S ⊆ M :=
    λ S hS_total hM_sub_S => hM_max.2 hS_total hM_sub_S
  have hM_nonempty : M.Nonempty := by
    by_contra h_empty
    rcases ‹Nonempty X› with ⟨a⟩
    have h_sing_total : IsTotal ({a} : Set X) := by
      intro x y
      have hx_a : x.val = a := x.property
      have hy_a : y.val = a := y.property
      have h_eq : x = y := Subtype.ext (hx_a.trans hy_a.symm)
      rw [h_eq]
      exact Or.inl (le_refl y)
    have h_empty_sub : M ⊆ ({a} : Set X) := by
      have hM_empty : M = ∅ := Set.not_nonempty_iff_eq_empty.mp h_empty
      rw [hM_empty]
      exact Set.empty_subset _
    have h_sing_sub_M : ({a} : Set X) ⊆ M :=
      hM_maximal ({a} : Set X) h_sing_total h_empty_sub
    have haM : a ∈ M := h_sing_sub_M (by simp)
    have hM_empty : M = ∅ := Set.not_nonempty_iff_eq_empty.mp h_empty
    rw [hM_empty] at haM
    exact haM.elim
  rcases hchain M ⟨hM_total, hM_nonempty⟩ with ⟨x, hx_ub⟩
  have hx_in_M : x ∈ M := by
    by_contra hx_not_M
    have h_ext_total : IsTotal (M ∪ {x} : Set X) := by
      intro a b
      rcases a.property with (haM | ha_eq_x)
      · rcases b.property with (hbM | hb_eq_x)
        · have h := hM_total ⟨a.val, haM⟩ ⟨b.val, hbM⟩
          simpa using h
        · have hb_val_eq_x : b.val = x := by simpa using hb_eq_x
          have hle' : a.val ≤ b.val := by
            rw [hb_val_eq_x]
            exact hx_ub a.val haM
          exact Or.inl hle'
      · have ha_val_eq_x : a.val = x := by simpa using ha_eq_x
        rcases b.property with (hbM | hb_eq_x)
        · have hle' : b.val ≤ a.val := by
            rw [ha_val_eq_x]
            exact hx_ub b.val hbM
          exact Or.inr hle'
        · have hb_val_eq_x : b.val = x := by simpa using hb_eq_x
          have h_eq : a.val = b.val := by rw [ha_val_eq_x, hb_val_eq_x]
          have hle' : a.val ≤ b.val := by rw [h_eq]
          exact Or.inl hle'
    have hM_sub_ext : M ⊆ M ∪ {x} := by
      intro z hz; exact Or.inl hz
    have h_ext_sub_M : M ∪ {x} ⊆ M :=
      hM_maximal (M ∪ {x}) h_ext_total hM_sub_ext
    have hx_ext : x ∈ M ∪ {x} := Set.mem_union_right M (by simp)
    exact hx_not_M (h_ext_sub_M hx_ext)
  use x
  intro y hx_le_y
  have hy_ub : IsUpperBound M y := by
    intro m hm
    exact le_trans (hx_ub m hm) hx_le_y
  have hy_in_M : y ∈ M := by
    by_contra hy_not_M
    have h_ext_total : IsTotal (M ∪ {y} : Set X) := by
      intro a b
      rcases a.property with (haM | ha_eq_y)
      · rcases b.property with (hbM | hb_eq_y)
        · have h := hM_total ⟨a.val, haM⟩ ⟨b.val, hbM⟩
          simpa using h
        · have hb_val_eq_y : b.val = y := by simpa using hb_eq_y
          have hle' : a.val ≤ b.val := by
            rw [hb_val_eq_y]
            exact hy_ub a.val haM
          exact Or.inl hle'
      · have ha_val_eq_y : a.val = y := by simpa using ha_eq_y
        rcases b.property with (hbM | hb_eq_y)
        · have hle' : b.val ≤ a.val := by
            rw [ha_val_eq_y]
            exact hy_ub b.val hbM
          exact Or.inr hle'
        · have hb_val_eq_y : b.val = y := by simpa using hb_eq_y
          have h_eq : a.val = b.val := by rw [ha_val_eq_y, hb_val_eq_y]
          have hle' : a.val ≤ b.val := by rw [h_eq]
          exact Or.inl hle'
    have hM_sub_ext : M ⊆ M ∪ {y} := by
      intro z hz; exact Or.inl hz
    have h_ext_sub_M : M ∪ {y} ⊆ M :=
      hM_maximal (M ∪ {y}) h_ext_total hM_sub_ext
    have hy_ext : y ∈ M ∪ {y} := Set.mem_union_right M (by simp)
    exact hy_not_M (h_ext_sub_M hy_ext)
  exact hx_ub y hy_in_M

/-- Exercise 8.5.19: A well-ordered subset of X: a subset with a linear order and
well-foundedness. -/
structure WellOrderedSubset (X : Type) where
  carrier : Set X
  ord : LinearOrder carrier
  wf : @WellFoundedLT carrier ord.toLT

/-- (W, ≤) is an initial segment of (W', ≤') if W ⊆ W', the orderings agree on W,
and W = \{y ∈ W' : y <' x\} for some x ∈ W'. -/
def WellOrderedSubset.IsInitialSegment {X : Type}
    (W W' : WellOrderedSubset X) : Prop :=
  ∃ x : W'.carrier,
    W.carrier = Subtype.val '' {z : W'.carrier | W'.ord.lt z x} ∧
    ∀ (a b : W.carrier) (ha : a.1 ∈ W'.carrier) (hb : b.1 ∈ W'.carrier),
      W.ord.le a b ↔ W'.ord.le ⟨a, ha⟩ ⟨b, hb⟩

theorem WellOrderedSubset.IsInitialSegment.subset {X : Type}
    {W W' : WellOrderedSubset X} (h : W.IsInitialSegment W') :
    W.carrier ⊂ W'.carrier := by
  letI : LinearOrder W'.carrier := W'.ord
  rcases h with ⟨x, hW_eq, h_ord⟩
  have h_sub : W.carrier ⊆ W'.carrier := by
    rw [hW_eq]
    rintro y ⟨z, hz, rfl⟩
    exact z.2
  refine ⟨h_sub, ?_⟩
  intro h_eq
  have hx_in_W : x.val ∈ W.carrier := h_eq x.2
  rw [hW_eq] at hx_in_W
  rcases hx_in_W with ⟨z, hz, hz_eq⟩
  have hz_eq_x : z = x := Subtype.ext hz_eq
  rw [hz_eq_x] at hz
  exact lt_irrefl x hz

/-- The ordering on well-ordered subsets: equal or initial segment. -/
instance WellOrderedSubset.instPartialOrder (X : Type) :
    PartialOrder (WellOrderedSubset X) where
  le W W' := W = W' ∨ W.IsInitialSegment W'
  le_refl := fun W ↦ Or.inl rfl
  le_antisymm := by
    intro W W' h1 h2
    rcases h1 with rfl | h1
    · rfl
    rcases h2 with rfl | h2
    · rfl
    exact (h1.subset.asymm h2.subset).elim
  le_trans := by
    intro W W' W'' h1 h2
    letI : LinearOrder W'.carrier := W'.ord
    letI : LinearOrder W''.carrier := W''.ord
    rcases h1 with (rfl | h1)
    · exact h2
    rcases h2 with (rfl | h2)
    · exact Or.inr h1
    rcases h1 with ⟨x, hW_eq, h_ord⟩
    rcases h2 with ⟨y, hW'_eq, h_ord'⟩
    have hx_val_mem : x.val ∈ W'.carrier := x.2
    have hx_val_image : x.val ∈ (Subtype.val '' {w : W''.carrier | W''.ord.lt w y}) :=
      hW'_eq ▸ hx_val_mem
    rcases hx_val_image with ⟨z, hz_lt_y, hz_val⟩
    have mem_W' (a : W.carrier) : a.1 ∈ W'.carrier := by
      have hmem' : a.1 ∈ (Subtype.val '' {z : W'.carrier | W'.ord.lt z x}) := hW_eq ▸ a.2
      rcases hmem' with ⟨u, _, hu_val⟩
      rw [← hu_val]
      exact u.2
    have mem_W'' (a : W.carrier) : a.1 ∈ W''.carrier := by
      have hmem' : a.1 ∈ (Subtype.val '' {w : W''.carrier | W''.ord.lt w y}) :=
        hW'_eq ▸ mem_W' a
      rcases hmem' with ⟨w, _, hw_val⟩
      rw [← hw_val]
      exact w.2
    have lt_equiv_W' (a b : W'.carrier) (ha : a.1 ∈ W''.carrier) (hb : b.1 ∈ W''.carrier) :
        W'.ord.lt a b ↔ W''.ord.lt (⟨a, ha⟩ : W''.carrier) (⟨b, hb⟩ : W''.carrier) := by
      constructor
      · intro hlt
        have hle : W'.ord.le a b := le_of_lt hlt
        have hne : a ≠ b := ne_of_lt hlt
        have hle' : W''.ord.le (⟨a, ha⟩ : W''.carrier) (⟨b, hb⟩ : W''.carrier) :=
          (h_ord' a b ha hb).mp hle
        have hne' : (⟨a, ha⟩ : W''.carrier) ≠ (⟨b, hb⟩ : W''.carrier) := by
          intro heq
          apply hne
          exact Subtype.ext (by
            have := congrArg Subtype.val heq
            simpa using this)
        exact lt_of_le_of_ne hle' hne'
      · intro hlt
        have hle : W''.ord.le (⟨a, ha⟩ : W''.carrier) (⟨b, hb⟩ : W''.carrier) := le_of_lt hlt
        have hne : (⟨a, ha⟩ : W''.carrier) ≠ (⟨b, hb⟩ : W''.carrier) := ne_of_lt hlt
        have hle' : W'.ord.le a b := (h_ord' a b ha hb).mpr hle
        have hne' : a ≠ b := by
          intro heq
          apply hne
          subst heq
          apply Subtype.ext rfl
        exact lt_of_le_of_ne hle' hne'
    have h_ord_comp (a b : W.carrier) (ha : a.1 ∈ W''.carrier) (hb : b.1 ∈ W''.carrier) :
        W.ord.le a b ↔ W''.ord.le (⟨a.val, ha⟩ : W''.carrier) (⟨b.val, hb⟩ : W''.carrier) := by
      let ha' : a.1 ∈ W'.carrier := mem_W' a
      let hb' : b.1 ∈ W'.carrier := mem_W' b
      have h1_eq := h_ord a b ha' hb'
      have h2_eq := h_ord' ⟨a.val, ha'⟩ ⟨b.val, hb'⟩ ha hb
      have ha_sub_eq : (⟨(⟨a.val, ha'⟩ : W'.carrier), ha⟩ : W''.carrier) = ⟨a.val, ha⟩ := Subtype.ext rfl
      have hb_sub_eq : (⟨(⟨b.val, hb'⟩ : W'.carrier), hb⟩ : W''.carrier) = ⟨b.val, hb⟩ := Subtype.ext rfl
      rw [ha_sub_eq, hb_sub_eq] at h2_eq
      exact ⟨λ h => h2_eq.mp (h1_eq.mp h), λ h => h1_eq.mpr (h2_eq.mpr h)⟩
    refine Or.inr ?_
    use z
    constructor
    · rw [hW_eq]
      ext a
      constructor
      · rintro ⟨u, hu_lt_x, rfl⟩
        have hu_val_mem' : u.val ∈ (Subtype.val '' {w : W''.carrier | W''.ord.lt w y}) :=
          hW'_eq ▸ u.2
        rw [Set.mem_image] at hu_val_mem'
        rcases hu_val_mem' with ⟨w, hw_lt_y, hw_val⟩
        have hw_mem : u.val ∈ W''.carrier := by
          rw [← hw_val]; exact w.2
        have hx_mem : x.val ∈ W''.carrier := by
          rw [← hz_val]; exact z.2
        have hw_as_subtype : (⟨u.val, hw_mem⟩ : W''.carrier) = w := Subtype.ext hw_val.symm
        have hz_as_subtype : (⟨x.val, hx_mem⟩ : W''.carrier) = z := Subtype.ext hz_val.symm
        have h_lt' : W''.ord.lt (⟨u.val, hw_mem⟩ : W''.carrier) (⟨x.val, hx_mem⟩ : W''.carrier) :=
          (lt_equiv_W' u x hw_mem hx_mem).mp hu_lt_x
        rw [hw_as_subtype, hz_as_subtype] at h_lt'
        rw [Set.mem_image]
        exact ⟨w, ⟨h_lt', hw_val⟩⟩
      · rintro ⟨w, hw_lt_z, rfl⟩
        have hw_lt_y : W''.ord.lt w y := lt_trans hw_lt_z hz_lt_y
        have hw_val_mem : w.val ∈ W'.carrier := by
          rw [hW'_eq]
          rw [Set.mem_image]
          exact ⟨w, hw_lt_y, rfl⟩
        let u : W'.carrier := ⟨w.val, hw_val_mem⟩
        have hw_mem_W'' : u.val ∈ W''.carrier := by
          dsimp [u]; exact w.2
        have hx_mem_W'' : x.val ∈ W''.carrier := by
          rw [← hz_val]; exact z.2
        have h_eq_u : (⟨u.val, hw_mem_W''⟩ : W''.carrier) = w := Subtype.ext rfl
        have h_eq_x : (⟨x.val, hx_mem_W''⟩ : W''.carrier) = z := Subtype.ext hz_val.symm
        have h_lt : W''.ord.lt (⟨u.val, hw_mem_W''⟩ : W''.carrier) (⟨x.val, hx_mem_W''⟩ : W''.carrier) := by
          rw [h_eq_u, h_eq_x]
          exact hw_lt_z
        have hu_lt_x : W'.ord.lt u x := (lt_equiv_W' u x hw_mem_W'' hx_mem_W'').mpr h_lt
        use u
        exact ⟨hu_lt_x, rfl⟩
    · exact h_ord_comp

/-- The empty well-ordered subset. -/
def WellOrderedSubset.empty (X : Type) : WellOrderedSubset X where
  carrier := ∅
  ord := { PartialOrder.discrete (∅ : Set X) with
    le_total := fun ⟨_, h⟩ ↦ h.elim
    toDecidableLE := fun ⟨_, h⟩ ↦ h.elim }
  wf := ⟨⟨fun ⟨_, h⟩ ↦ h.elim⟩⟩

theorem WellOrderedSubset.empty_isMin (X : Type) :
    @IsMin (WellOrderedSubset X) (instPartialOrder X).toPreorder.toLE
      (empty X) := by
  intro W hW
  rcases hW with (rfl | h_init)
  · rfl
  rcases h_init with ⟨x, hW_eq, h_ord⟩
  exact x.2.elim

/-- The maximal elements are precisely the well-orderings of all of X. -/
theorem WellOrderedSubset.isMax_iff_full (X : Type) (W : WellOrderedSubset X) :
    @IsMax (WellOrderedSubset X) (instPartialOrder X).toPreorder.toLE W ↔
    W.carrier = Set.univ := by
  constructor
  · intro h_max
    by_contra! h_not_full
    have h_exists : ∃ x : X, x ∉ W.carrier := by
      by_contra! hall
      apply h_not_full
      ext x; simp [hall x]
    rcases h_exists with ⟨x, hx⟩
    -- If x ∉ W.carrier, extend W by placing x as the new maximum element,
    -- constructing a well-ordered subset W' that strictly extends W as an
    -- initial segment, contradicting maximality.
    let ord_carrier : LinearOrder (W.carrier) := W.ord
    let wf_carrier : @WellFoundedLT (W.carrier) ord_carrier.toLT := W.wf
    let carrier' : Set X := W.carrier ∪ {x}
    classical
    let e : carrier' ≃ WithTop (W.carrier) := {
      toFun := λ a =>
        if ha : (a.val : X) ∈ W.carrier then
          (⟨a.val, ha⟩ : W.carrier)
        else
          (⊤ : WithTop (W.carrier))
      invFun := λ t => match t with
        | ⊤ => ⟨x, Or.inr rfl⟩
        | (w : W.carrier) => ⟨w.val, Or.inl w.property⟩
      left_inv := λ a => by
        dsimp
        by_cases ha : (a.val : X) ∈ W.carrier
        · simp [ha]
        · have hx' : a.val = x := by
            rcases a.property with (h | h)
            · exact (ha h).elim
            · exact h
          simp [ha]
          apply Subtype.ext
          simp [hx']
      right_inv := λ t => by
        dsimp
        match t with
        | ⊤ => simp [hx]
        | (w : W.carrier) => simp
    }
    letI ord_carrier' : LinearOrder carrier' := LinearOrder.lift' e (e.injective)
    let ord_top : LinearOrder (WithTop (W.carrier)) := @WithTop.linearOrder (W.carrier) ord_carrier
    have wf_top : @WellFounded (WithTop (W.carrier)) ord_top.toLT.lt :=
      (@WithTop.instWellFoundedLT (W.carrier) ord_carrier.toLT wf_carrier).wf
    haveI wf_carrier' : @WellFoundedLT carrier' ord_carrier'.toLT := by
      constructor
      have h := @InvImage.wf carrier' (WithTop (W.carrier)) ord_top.toLT.lt e wf_top
      simpa using h
    let W' : WellOrderedSubset X := {
      carrier := carrier'
      ord := ord_carrier'
      wf := wf_carrier'
    }
    have hW_le_W' : W ≤ W' := by
      refine Or.inr ?_
      let x_val : W'.carrier := ⟨x, Or.inr rfl⟩
      refine ⟨x_val, ?_, ?_⟩
      · -- W.carrier = Subtype.val '' {z : W'.carrier | W'.ord.lt z x_val}
        ext a; constructor
        · intro haW
          have ha' : a ∈ carrier' := Or.inl haW
          refine ⟨⟨a, ha'⟩, ?_, rfl⟩
          dsimp [W', ord_carrier']
          show e (⟨a, ha'⟩) < e x_val
          have hleft : e (⟨a, ha'⟩) = ((⟨a, haW⟩ : W.carrier) : WithTop (W.carrier)) := by
            dsimp [e]; simp [haW]
          have hright : e x_val = (⊤ : WithTop (W.carrier)) := by
            dsimp [e, x_val]; simp [hx]
          rw [hleft, hright]
          exact WithTop.coe_lt_top (⟨a, haW⟩ : W.carrier)
        · intro h
          rcases h with ⟨z, hz_lt, rfl⟩
          by_cases hzW : z.val ∈ W.carrier
          · exact hzW
          · have heqz : e z = (⊤ : WithTop (W.carrier)) := by
              dsimp [e]
              simp [hzW]
            have heqx : e x_val = (⊤ : WithTop (W.carrier)) := by
              dsimp [e, x_val]
              simp [hx]
            dsimp [W', ord_carrier'] at hz_lt
            have h_lt_top : e z < e x_val := hz_lt
            rw [heqz, heqx] at h_lt_top
            exfalso
            exact lt_irrefl _ h_lt_top
      · -- Order agreement
        intro a b ha' hb'
        have haW : (a.val : X) ∈ W.carrier := a.property
        have hbW : (b.val : X) ∈ W.carrier := b.property
        dsimp [W', ord_carrier']
        have hle_def : ∀ (u v : carrier'), (u ≤ v) = (e u ≤ e v) := by
          intro u v; rfl
        rw [hle_def (⟨a.val, ha'⟩) (⟨b.val, hb'⟩)]
        constructor
        · intro h
          have ha_eq' : e (⟨a.val, ha'⟩) = ((⟨a.val, haW⟩ : W.carrier) : WithTop (W.carrier)) := by
            dsimp [e]; simp [haW]
          have hb_eq' : e (⟨b.val, hb'⟩) = ((⟨b.val, hbW⟩ : W.carrier) : WithTop (W.carrier)) := by
            dsimp [e]; simp [hbW]
          have ha_sub_eq : (⟨a.val, haW⟩ : W.carrier) = a := Subtype.ext rfl
          have hb_sub_eq : (⟨b.val, hbW⟩ : W.carrier) = b := Subtype.ext rfl
          rw [ha_eq', hb_eq']
          rw [WithTop.coe_le_coe]
          rw [ha_sub_eq, hb_sub_eq]
          exact h
        · intro h
          have ha_eq' : e (⟨a.val, ha'⟩) = ((⟨a.val, haW⟩ : W.carrier) : WithTop (W.carrier)) := by
            dsimp [e]; simp [haW]
          have hb_eq' : e (⟨b.val, hb'⟩) = ((⟨b.val, hbW⟩ : W.carrier) : WithTop (W.carrier)) := by
            dsimp [e]; simp [hbW]
          have ha_sub_eq : (⟨a.val, haW⟩ : W.carrier) = a := Subtype.ext rfl
          have hb_sub_eq : (⟨b.val, hbW⟩ : W.carrier) = b := Subtype.ext rfl
          rw [ha_eq', hb_eq'] at h
          rw [WithTop.coe_le_coe] at h
          rw [ha_sub_eq, hb_sub_eq] at h
          exact h
    have hW_ne_W' : W ≠ W' := by
      intro heq
      have hx_in_W' : x ∈ W'.carrier := by
        dsimp [W', carrier']; simp
      have h_carrier_eq : W.carrier = W'.carrier := by
        simpa [W'] using congrArg (λ ws : WellOrderedSubset X => ws.carrier) heq
      rw [← h_carrier_eq] at hx_in_W'
      exact hx hx_in_W'
    have h_lt : W < W' := by
      rw [lt_iff_le_and_ne]
      exact ⟨hW_le_W', hW_ne_W'⟩
    have h_not_max : ¬ IsMax W := by
      rw [isMax_iff_forall_not_lt]
      exact λ h => h W' h_lt
    exact h_not_max h_max
  · intro h_full W' hW'
    rcases hW' with (rfl | h_init)
    · exact Or.inl rfl
    have h_sub : W.carrier ⊂ W'.carrier := h_init.subset
    rw [h_full] at h_sub
    exfalso
    exact h_sub.2 (Set.subset_univ W'.carrier)

/-- The well-ordering principle: every set has a well-ordering. -/
theorem well_ordering_principle (X : Type) :
    ∃ (l : LinearOrder X), @WellFoundedLT X l.toLT :=
  exists_wellOrder X

theorem axiom_of_choice_of_well_ordering
    (hwo : ∀ T : Type, ∃ (l : LinearOrder T), @WellFoundedLT T l.toLT)
    {I : Type} {X : I → Type} (hne : ∀ i, Nonempty (X i)) :
    Nonempty (∀ i, X i) := by
  let T := Σ i, X i
  rcases hwo T with ⟨l, hwf⟩
  letI : LinearOrder T := l
  letI : WellFoundedLT T := hwf
  have h_wf_min : ∀ (A : Set T), A.Nonempty → ∃ x : A, IsMin x :=
    (WellFoundedLT.iff T).mp (by infer_instance)
  have h_choice : ∀ i, X i := by
    intro i
    let S_i : Set T := {t | t.1 = i}
    have hS_nonempty : S_i.Nonempty := by
      rcases hne i with ⟨xi⟩
      refine ⟨⟨i, xi⟩, ?_⟩
      rfl
    let h_min_exists := h_wf_min S_i hS_nonempty
    let t_min : S_i := h_min_exists.choose
    have h_min : IsMin t_min := h_min_exists.choose_spec
    have hi : (t_min.val : T).1 = i := t_min.property
    -- t_min.val.2 : X (t_min.val.1) = X i (by hi)
    exact hi ▸ (t_min.val : T).2
  exact ⟨h_choice⟩

/-- Exercise 8.5.20 -/
theorem maximal_disjoint_subcollection {X : Type} (Ω : Set (Set X)) (hne : ∅ ∉ Ω) :
    ∃ Ω' ⊆ Ω, Ω'.Pairwise Disjoint ∧
      (∀ C ∈ Ω, ∃ A ∈ Ω', (C ∩ A).Nonempty) := by
  let 𝒟 := { D : Set (Set X) | D ⊆ Ω ∧ D.Pairwise Disjoint }
  haveI : Nonempty 𝒟 := ⟨⟨∅, Set.empty_subset Ω, by intro a ha; exact ha.elim⟩⟩
  have h_chain : ∀ (C : Set 𝒟), IsTotal C ∧ C.Nonempty → ∃ ub : 𝒟, IsUpperBound C ub := by
    intro C ⟨hC_total, hC_ne⟩
    let ub_val : Set (Set X) := ⋃₀ (Subtype.val '' C)
    have hub_sub : ub_val ⊆ Ω := by
      intro A hA
      rw [Set.mem_sUnion] at hA
      rcases hA with ⟨B, hB_mem, hAB⟩
      rw [Set.mem_image] at hB_mem
      rcases hB_mem with ⟨⟨D, hD_sub, _⟩, _, rfl⟩
      exact hD_sub hAB
    have hub_disjoint : ub_val.Pairwise Disjoint := by
      intro A hA B hB h_ne
      rw [Set.mem_sUnion] at hA hB
      rcases hA with ⟨DA, hDA_mem, hA_DA⟩
      rcases hB with ⟨DB, hDB_mem, hB_DB⟩
      rw [Set.mem_image] at hDA_mem hDB_mem
      rcases hDA_mem with ⟨⟨DA', ⟨hDA'_sub, hDA'_disj⟩⟩, hDA'C, rfl⟩
      rcases hDB_mem with ⟨⟨DB', ⟨hDB'_sub, hDB'_disj⟩⟩, hDB'C, rfl⟩
      have h_compare := hC_total (⟨⟨DA', ⟨hDA'_sub, hDA'_disj⟩⟩, hDA'C⟩ : C)
                                (⟨⟨DB', ⟨hDB'_sub, hDB'_disj⟩⟩, hDB'C⟩ : C)
      rcases h_compare with (h_le | h_le)
      · have hA_db' : A ∈ DB' := h_le hA_DA
        exact hDB'_disj hA_db' hB_DB h_ne
      · have hB_da' : B ∈ DA' := h_le hB_DB
        exact hDA'_disj hA_DA hB_da' h_ne
    have hub_mem : ub_val ∈ 𝒟 := ⟨hub_sub, hub_disjoint⟩
    let hub : 𝒟 := ⟨ub_val, hub_mem⟩
    have h_ub_upper : IsUpperBound C hub := by
      intro D hDC A hAD
      rcases D with ⟨D_val, ⟨_, _⟩⟩
      apply Set.mem_sUnion.mpr
      refine ⟨D_val, Set.mem_image_of_mem Subtype.val hDC, hAD⟩
    refine ⟨hub, h_ub_upper⟩
  rcases Zorns_lemma (X := 𝒟) h_chain with ⟨⟨Ω_max, ⟨hΩ_sub, hΩ_disjoint⟩⟩, hΩ_max⟩
  refine ⟨Ω_max, hΩ_sub, hΩ_disjoint, ?_⟩
  intro C hC_Ω
  by_contra! h_no_intersect
  -- h_no_intersect: ∀ A ∈ Ω_max, C ∩ A = ∅
  have hC_disjoint_all : ∀ A ∈ Ω_max, C ∩ A = ∅ := h_no_intersect
  have hC_nonempty : (C : Set X).Nonempty := by
    by_contra h_empty
    have hC_empty : C = ∅ := Set.not_nonempty_iff_eq_empty.mp h_empty
    rw [hC_empty] at hC_Ω
    exact hne hC_Ω
  have hC_not_mem_Ω_max : C ∉ Ω_max := by
    intro hC_mem
    have hC_self_empty : C ∩ C = ∅ := hC_disjoint_all C hC_mem
    rcases hC_nonempty with ⟨x, hx⟩
    have hx_inter : x ∈ C ∩ C := ⟨hx, hx⟩
    rw [hC_self_empty] at hx_inter
    exact hx_inter.elim
  let Ω_max' : Set (Set X) := Set.insert C Ω_max
  have hΩ_max'_sub : Ω_max' ⊆ Ω := by
    intro S hS
    rcases Set.mem_insert_iff.mp hS with (rfl | hS)
    · exact hC_Ω
    · exact hΩ_sub hS
  have hΩ_max'_disjoint : Ω_max'.Pairwise Disjoint := by
    intro A hA' B hB' h_ne
    rcases Set.mem_insert_iff.mp hA' with (rfl | hA_in_Ω)
    · rcases Set.mem_insert_iff.mp hB' with (rfl | hB_in_Ω)
      · exfalso; exact h_ne rfl
      · rw [Set.disjoint_iff_inter_eq_empty]
        exact hC_disjoint_all B hB_in_Ω
    · rcases Set.mem_insert_iff.mp hB' with (rfl | hB_in_Ω)
      · rw [Set.disjoint_iff_inter_eq_empty, Set.inter_comm]
        exact hC_disjoint_all A hA_in_Ω
      · exact hΩ_disjoint hA_in_Ω hB_in_Ω h_ne
  have hΩ_max'_mem_𝒟 : Ω_max' ∈ 𝒟 := ⟨hΩ_max'_sub, hΩ_max'_disjoint⟩
  have hΩ_max_le_Ω_max' : (⟨Ω_max, ⟨hΩ_sub, hΩ_disjoint⟩⟩ : 𝒟) ≤ (⟨Ω_max', hΩ_max'_mem_𝒟⟩ : 𝒟) := by
    intro A hA
    apply Set.mem_insert_of_mem C
    exact hA
  have hΩ_max'_le_Ω_max : (⟨Ω_max', hΩ_max'_mem_𝒟⟩ : 𝒟) ≤ (⟨Ω_max, ⟨hΩ_sub, hΩ_disjoint⟩⟩ : 𝒟) :=
    hΩ_max hΩ_max_le_Ω_max'
  have hC_in_Ω_max : C ∈ Ω_max :=
    hΩ_max'_le_Ω_max (Set.mem_insert C Ω_max)
  exact hC_not_mem_Ω_max hC_in_Ω_max

/-- The maximal disjoint subcollection property implies Exercise 8.4.2, hence is
equivalent to the axiom of choice. -/
theorem exists_set_singleton_intersect_of_maximal_disjoint
    (hmds : ∀ (X : Type) (Ω : Set (Set X)), ∅ ∉ Ω →
      ∃ Ω' ⊆ Ω, Ω'.Pairwise Disjoint ∧
        (∀ C ∈ Ω, ∃ A ∈ Ω', (C ∩ A).Nonempty))
    {I U : Type} {X : I → Set U}
    (h : Set.PairwiseDisjoint .univ X) (hne : ∀ α, Nonempty (X α)) :
    ∃ Y : Set U, ∀ α, Nat.card (Y ∩ X α : Set U) = 1 := by
  -- The family {X α | α : I} consists of nonempty pairwise disjoint sets.
  -- Applying hmds to this family gives Ω' = Set.range X (since pairwise disjointness
  -- forces every member to be in Ω'). Then picking one element from each X α yields Y.
  have h_range_nonempty : ∅ ∉ Set.range X := by
    intro h
    rcases h with ⟨α, h_eq⟩
    rcases hne α with ⟨x⟩
    -- h_eq : X α = ∅, so x.val ∈ X α = ∅, contradiction
    have hx_empty : x.val ∈ (∅ : Set U) := h_eq ▸ x.property
    simp at hx_empty
  rcases hmds U (Set.range X) h_range_nonempty with ⟨Ω', hΩ'_sub_range, hΩ'_disjoint, hΩ'_cover⟩
  -- For each α, X α ∈ Set.range X, so by hΩ'_cover there is A ∈ Ω' with (X α ∩ A).Nonempty.
  -- Since the X α are pairwise disjoint, A must be X α itself. Hence X α ∈ Ω' for all α.
  have hX_mem_Ω' : ∀ α, X α ∈ Ω' := by
    intro α
    have hX_range : X α ∈ Set.range X := ⟨α, rfl⟩
    rcases hΩ'_cover (X α) hX_range with ⟨A, hA, h_inter⟩
    rcases hΩ'_sub_range hA with ⟨β, rfl⟩
    -- A = X β, and (X α ∩ X β).Nonempty
    by_cases hαβ : α = β
    · subst hαβ; exact hA
    · -- α ≠ β, so Disjoint (X α) (X β) by h
      have h_disjoint : Disjoint (X α) (X β) := h (Set.mem_univ α) (Set.mem_univ β) hαβ
      rw [Set.disjoint_iff_inter_eq_empty] at h_disjoint
      rw [h_disjoint] at h_inter
      exact (Set.not_nonempty_empty h_inter).elim
  -- Choose one element from each X α
  classical
    let s : ∀ α, X α := λ α => (hne α).some
    let y : I → U := λ α => (s α).val
    have hy_mem : ∀ α, y α ∈ X α := λ α => (s α).property
  let Y : Set U := Set.range y
  refine ⟨Y, ?_⟩
  intro α
  have h_eq : Y ∩ (X α : Set U) = {y α} := by
    apply Set.Subset.antisymm
    · intro u hu
      rcases hu with ⟨huY, huXα⟩
      rcases huY with ⟨β, rfl⟩
      -- u = y β, and y β ∈ X α
      by_cases hαβ : α = β
      · subst hαβ; exact Set.mem_singleton _
      · have h_disjoint : Disjoint (X α) (X β) := h (Set.mem_univ α) (Set.mem_univ β) hαβ
        rw [Set.disjoint_iff_inter_eq_empty] at h_disjoint
        have hyβ_Xβ : y β ∈ X β := hy_mem β
        have h_inter : y β ∈ X α ∩ X β := ⟨huXα, hyβ_Xβ⟩
        rw [h_disjoint] at h_inter
        exact h_inter.elim
    · intro u hu
      rcases Set.mem_singleton_iff.mp hu with rfl
      exact ⟨⟨α, rfl⟩, hy_mem α⟩
  rw [h_eq]
  simp

end Chapter8
