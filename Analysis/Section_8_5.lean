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
#check (inferInstance : LinearOrder ℕ)
#check (inferInstance : LinearOrder ℚ)
#check (inferInstance : LinearOrder ℝ)
#check (inferInstance : LinearOrder EReal)


theorem IsTotal.subtype {X:Type} [PartialOrder X] {A: Set X} (hA: IsTotal X) : IsTotal A := by
  intro ⟨ x, hx ⟩ ⟨ y, hy ⟩
  specialize hA x y; simp_all

@[implicit_reducible] noncomputable def LinearOrder.subtype {X:Type} [LinearOrder X] (A: Set X) : LinearOrder A :=
LinearOrder.mk (IsTotal.subtype (by
  intro x y; exact le_total x y))

theorem IsTotal.subset {X:Type} [PartialOrder X] {A B: Set X} (hA: IsTotal A) (hAB: B ⊆ A) : IsTotal B := by
  intro ⟨ x, hx ⟩ ⟨ y, hy ⟩
  specialize hA ⟨ x, hAB hx ⟩ ⟨ y, hAB hy ⟩; simp_all

abbrev X_8_5_4 : Set (Set ℕ) := { {1,2}, {2}, {2,3}, {2,3,4}, {5} }
example : ¬ IsTotal X_8_5_4 := by
  intro h
  have h := h (⟨ {2}, by simp [X_8_5_4] ⟩ : X_8_5_4) (⟨ {5}, by simp [X_8_5_4] ⟩ : X_8_5_4)
  simp at h

/-- Definition 8.5.5 (Maximal and minimal elements).  Here we use Mathlib's {name}`IsMax` and {name}`IsMin`. -/
theorem IsMax.iff {X:Type} [PartialOrder X] (x:X) :
  IsMax x ↔ ¬ ∃ y, x < y := by rw [isMax_iff_forall_not_lt]; grind

theorem IsMin.iff {X:Type} [PartialOrder X] (x:X) :
  IsMin x ↔ ¬ ∃ y, x > y := by rw [isMin_iff_forall_not_lt]; grind

/-- Examples 8.5.6 -/
example : IsMin (⟨ {2}, by aesop ⟩ : X_8_5_4) := by
  rw [IsMin.iff]; intro h; rcases h with ⟨⟨b, hbX⟩, hb⟩
  simp [X_8_5_4] at hbX; rcases hbX with rfl|rfl|rfl|rfl|rfl
  · have hsub : ({1,2} : Set ℕ) ⊆ ({2} : Set ℕ) := by simpa using le_of_lt hb
    exact (Set.not_subset.mpr ⟨1, by simp, by simp⟩) hsub
  · apply (ne_of_lt hb); apply Subtype.eq; rfl
  · have hsub : ({2,3} : Set ℕ) ⊆ ({2} : Set ℕ) := by simpa using le_of_lt hb
    exact (Set.not_subset.mpr ⟨3, by simp, by simp⟩) hsub
  · have hsub : ({2,3,4} : Set ℕ) ⊆ ({2} : Set ℕ) := by simpa using le_of_lt hb
    exact (Set.not_subset.mpr ⟨4, by simp, by simp⟩) hsub
  · have hsub : ({5} : Set ℕ) ⊆ ({2} : Set ℕ) := by simpa using le_of_lt hb
    exact (Set.not_subset.mpr ⟨5, by simp, by simp⟩) hsub
example : IsMax (⟨ {1,2}, by aesop ⟩ : X_8_5_4) := by
  rw [IsMax.iff]; intro h; rcases h with ⟨⟨b, hbX⟩, hb⟩
  simp [X_8_5_4] at hbX; rcases hbX with rfl|rfl|rfl|rfl|rfl
  · apply (ne_of_lt hb); apply Subtype.eq; rfl
  · have hsub : ({1,2} : Set ℕ) ⊆ ({2} : Set ℕ) := by simpa using le_of_lt hb
    exact (Set.not_subset.mpr ⟨1, by simp, by simp⟩) hsub
  · have hsub : ({1,2} : Set ℕ) ⊆ ({2,3} : Set ℕ) := by simpa using le_of_lt hb
    exact (Set.not_subset.mpr ⟨1, by simp, by simp⟩) hsub
  · have hsub : ({1,2} : Set ℕ) ⊆ ({2,3,4} : Set ℕ) := by simpa using le_of_lt hb
    exact (Set.not_subset.mpr ⟨1, by simp, by simp⟩) hsub
  · have hsub : ({1,2} : Set ℕ) ⊆ ({5} : Set ℕ) := by simpa using le_of_lt hb
    exact (Set.not_subset.mpr ⟨1, by simp, by simp⟩) hsub
example : IsMax (⟨ {2,3,4}, by aesop ⟩ : X_8_5_4) := by
  rw [IsMax.iff]; intro h; rcases h with ⟨⟨b, hbX⟩, hb⟩
  simp [X_8_5_4] at hbX; rcases hbX with rfl|rfl|rfl|rfl|rfl
  · have hsub : ({2,3,4} : Set ℕ) ⊆ ({1,2} : Set ℕ) := by simpa using le_of_lt hb
    exact (Set.not_subset.mpr ⟨3, by simp, by simp⟩) hsub
  · have hsub : ({2,3,4} : Set ℕ) ⊆ ({2} : Set ℕ) := by simpa using le_of_lt hb
    exact (Set.not_subset.mpr ⟨3, by simp, by simp⟩) hsub
  · have hsub : ({2,3,4} : Set ℕ) ⊆ ({2,3} : Set ℕ) := by simpa using le_of_lt hb
    exact (Set.not_subset.mpr ⟨4, by simp, by simp⟩) hsub
  · apply (ne_of_lt hb); apply Subtype.eq; rfl
  · have hsub : ({2,3,4} : Set ℕ) ⊆ ({5} : Set ℕ) := by simpa using le_of_lt hb
    exact (Set.not_subset.mpr ⟨3, by simp, by simp⟩) hsub
example : IsMin (⟨ {5}, by aesop ⟩ : X_8_5_4) ∧ IsMax (⟨ {5}, by aesop ⟩ : X_8_5_4) := by
  constructor
  · rw [IsMin.iff]; intro h; rcases h with ⟨⟨b, hbX⟩, hb⟩
    simp [X_8_5_4] at hbX; rcases hbX with rfl|rfl|rfl|rfl|rfl
    · have hsub : ({5} : Set ℕ) ⊆ ({1,2} : Set ℕ) := by simpa using le_of_lt hb
      exact (Set.not_subset.mpr ⟨5, by simp, by simp⟩) hsub
    · have hsub : ({5} : Set ℕ) ⊆ ({2} : Set ℕ) := by simpa using le_of_lt hb
      exact (Set.not_subset.mpr ⟨5, by simp, by simp⟩) hsub
    · have hsub : ({5} : Set ℕ) ⊆ ({2,3} : Set ℕ) := by simpa using le_of_lt hb
      exact (Set.not_subset.mpr ⟨5, by simp, by simp⟩) hsub
    · have hsub : ({5} : Set ℕ) ⊆ ({2,3,4} : Set ℕ) := by simpa using le_of_lt hb
      exact (Set.not_subset.mpr ⟨5, by simp, by simp⟩) hsub
    · apply (ne_of_lt hb); apply Subtype.eq; rfl
  · rw [IsMax.iff]; intro h; rcases h with ⟨⟨b, hbX⟩, hb⟩
    simp [X_8_5_4] at hbX; rcases hbX with rfl|rfl|rfl|rfl|rfl
    · have hsub : ({1,2} : Set ℕ) ⊆ ({5} : Set ℕ) := by simpa using le_of_lt hb
      exact (Set.not_subset.mpr ⟨1, by simp, by simp⟩) hsub
    · have hsub : ({2} : Set ℕ) ⊆ ({5} : Set ℕ) := by simpa using le_of_lt hb
      exact (Set.not_subset.mpr ⟨2, by simp, by simp⟩) hsub
    · have hsub : ({2,3} : Set ℕ) ⊆ ({5} : Set ℕ) := by simpa using le_of_lt hb
      exact (Set.not_subset.mpr ⟨3, by simp, by simp⟩) hsub
    · have hsub : ({2,3,4} : Set ℕ) ⊆ ({5} : Set ℕ) := by simpa using le_of_lt hb
      exact (Set.not_subset.mpr ⟨3, by simp, by simp⟩) hsub
    · apply (ne_of_lt hb); apply Subtype.eq; rfl
example : ¬ IsMin (⟨ {2,3}, by aesop ⟩ : X_8_5_4) ∧ ¬ IsMax (⟨ {2,3}, by aesop ⟩ : X_8_5_4) := by
  constructor
  · rw [IsMin.iff, not_not]; refine ⟨⟨{2}, by aesop⟩, ?_⟩
    have h : ({2} : Set ℕ) < ({2,3} : Set ℕ) := by
      refine lt_of_le_of_ne ?_ ?_
      · intro x hx; simp at hx; simp [hx]
      · intro h; have : 3 ∈ ({2} : Set ℕ) := by simpa [h] using (by simp : 3 ∈ ({2,3} : Set ℕ))
        simp at this
    simpa
  · rw [IsMax.iff, not_not]; refine ⟨⟨{2,3,4}, by aesop⟩, ?_⟩
    have h : ({2,3} : Set ℕ) < ({2,3,4} : Set ℕ) := by
      refine lt_of_le_of_ne ?_ ?_
      · intro x hx
        simp at hx
        rcases hx with (rfl|rfl)
        · show (2 : ℕ) ∈ ({2,3,4} : Set ℕ); simp
        · show (3 : ℕ) ∈ ({2,3,4} : Set ℕ); simp
      · intro h; have : 4 ∈ ({2,3} : Set ℕ) := by simpa [h] using (by simp : 4 ∈ ({2,3,4} : Set ℕ))
        simp at this
    simpa

/-- Example 8.5.7 -/
example : IsMin (0:ℕ) := by
  rw [IsMin.iff]
  intro h
  rcases h with ⟨y, hy⟩
  have hy' : (0:ℕ) ≤ y := Nat.zero_le _
  linarith

example (n:ℕ) : ¬ IsMax n := by
  rw [IsMax.iff]
  refine ⟨n+1, ?_⟩
  omega

example (n:ℤ): ¬ IsMin n ∧ ¬ IsMax n := by
  constructor
  · rw [IsMin.iff]
    intro h
    apply h
    refine ⟨n-1, ?_⟩
    omega
  · rw [IsMax.iff]
    intro h
    apply h
    refine ⟨n+1, ?_⟩
    omega

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
  intro h
  have hwf := h.wf
  have huniv_nonempty : (Set.univ : Set ℤ).Nonempty := Set.univ_nonempty
  let m := WellFounded.min hwf (Set.univ : Set ℤ) huniv_nonempty
  have h_lt_mem : m - 1 ∈ (Set.univ : Set ℤ) := by simp
  have h_lt : m - 1 < m := by omega
  exact (WellFounded.not_lt_min hwf (Set.univ : Set ℤ) h_lt_mem) h_lt

example : ¬ WellFoundedLT ℚ := by
  intro h
  have hwf := h.wf
  have huniv_nonempty : (Set.univ : Set ℚ).Nonempty := Set.univ_nonempty
  let m := WellFounded.min hwf (Set.univ : Set ℚ) huniv_nonempty
  have h_lt_mem : m - 1 ∈ (Set.univ : Set ℚ) := by simp
  have h_lt : m - 1 < m := by linarith
  exact (WellFounded.not_lt_min hwf (Set.univ : Set ℚ) h_lt_mem) h_lt

example : ¬ WellFoundedLT ℝ := by
  intro h
  have hwf := h.wf
  have huniv_nonempty : (Set.univ : Set ℝ).Nonempty := Set.univ_nonempty
  let m := WellFounded.min hwf (Set.univ : Set ℝ) huniv_nonempty
  have h_lt_mem : m - 1 ∈ (Set.univ : Set ℝ) := by simp
  have h_lt : m - 1 < m := by linarith
  exact (WellFounded.not_lt_min hwf (Set.univ : Set ℝ) h_lt_mem) h_lt

/-- Exercise 8.5.8 -/
theorem IsMax.ofFinite {X:Type} [LinearOrder X] [Finite X] [Nonempty X] : ∃ x:X, IsMax x := by
  haveI : Fintype X := Fintype.ofFinite _
  have hne : (Finset.univ : Finset X).Nonempty := Finset.univ_nonempty
  set m := Finset.max' Finset.univ hne with hm
  refine ⟨m, ?_⟩
  rw [IsMax.iff]
  intro h
  rcases h with ⟨y, hy⟩
  have hy' : y ∈ Finset.univ := Finset.mem_univ y
  have hmax : y ≤ m := Finset.le_max' (Finset.univ : Finset X) y hy'
  have : ¬ m < y := not_lt.mpr hmax
  exact this hy

theorem IsMin.ofFinite {X:Type} [LinearOrder X] [Finite X] [Nonempty X] : ∃ x:X, IsMin x := by
  haveI : Fintype X := Fintype.ofFinite _
  have hne : (Finset.univ : Finset X).Nonempty := Finset.univ_nonempty
  set m := Finset.min' Finset.univ hne with hm
  refine ⟨m, ?_⟩
  rw [IsMin.iff]
  intro h
  rcases h with ⟨y, hy⟩
  have hy' : y ∈ Finset.univ := Finset.mem_univ y
  have hmin : m ≤ y := Finset.min'_le (Finset.univ : Finset X) y hy'
  have : ¬ m > y := not_lt.mpr hmin
  exact this hy

/-- Exercise 8.5.8 -/
theorem WellFoundedLT.ofFinite {X:Type} [LinearOrder X] [Finite X] : WellFoundedLT X := by
  rw [WellFoundedLT.iff]
  intro A hA
  haveI : Finite A := Finite.Set.subset A (Set.Subset.refl A)
  have hneA : Nonempty A := by rcases hA with ⟨x, hx⟩; exact ⟨⟨x, hx⟩⟩
  haveI : Nonempty A := hneA
  exact IsMin.ofFinite (X := A)

example {X:Type} [LinearOrder X] [WellFoundedLT X] (A: Set X) : WellFoundedLT A := by
  rw [WellFoundedLT.iff (X := A)]
  intro C hC
  have hC' : (Subtype.val '' (C : Set A)).Nonempty := by
    rcases hC with ⟨x, hx⟩
    refine ⟨x.val, x, hx, rfl⟩
  rcases (WellFoundedLT.iff (X := X)).mp inferInstance (Subtype.val '' (C : Set A)) hC' with ⟨x', hx'_min⟩
  rcases x'.property with ⟨a, ha, ha_eq⟩
  let c : C := ⟨a, ha⟩
  refine ⟨c, ?_⟩
  rw [IsMin.iff]
  intro h
  rcases h with ⟨d, hd⟩
  have hd_val_lt : (d.val : X) < (c.val : X) := by simpa using hd
  have hmem : (d.val : X) ∈ Subtype.val '' (C : Set A) := ⟨d.val, d.property, rfl⟩
  let y' : (Subtype.val '' (C : Set A)) := ⟨(d.val : X), hmem⟩
  have hy'_lt : y' < x' := by
    dsimp [y']
    refine Subtype.mk_lt_mk.mpr ?_
    calc
      (d.val : X) < (c.val : X) := hd_val_lt
      _ = (a.val : X) := rfl
      _ = x'.val := ha_eq
  exact (IsMin.iff (x := x')).mp hx'_min ⟨y', hy'_lt⟩

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
  sorry

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
  · rintro ⟨hUB, hxA⟩ y hy
    have hyx := hUB y hy
    refine lt_of_le_of_ne hyx ?_
    intro h; exact hxA (h ▸ hy)
  · intro h
    refine ⟨fun y hy => le_of_lt (h y hy), ?_⟩
    intro hxA; apply lt_irrefl x (h x hxA)

theorem IsStrictUpperBound.iff' {X:Type} [PartialOrder X] (A:Set X) (x:X) :
  IsStrictUpperBound A x ↔ x ∈ upperBounds A \ A := by
  simp [IsStrictUpperBound, IsUpperBound.iff]

example : IsUpperBound (.Icc 1 2: Set ℝ) 2 := by
  intro y hy; rcases hy with ⟨hy1, hy2⟩; exact hy2

example : ¬ IsStrictUpperBound (.Icc 1 2: Set ℝ) 2 := by
  intro h; apply h.2; norm_num

example : IsStrictUpperBound (.Icc 1 2: Set ℝ) 3 := by
  refine ⟨?_, ?_⟩
  · intro y hy; rcases hy with ⟨hy1, hy2⟩; linarith
  · norm_num

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
  have hY_min (B : Set X) (hB_sub : B ⊆ Y) (hB_ne : B.Nonempty) : ∃ m ∈ B, ∀ x ∈ B, m ≤ x := by
    let s : Set (Subtype Y) := {y | (y : X) ∈ B}
    have hs_ne : s.Nonempty := by
      rcases hB_ne with ⟨b, hb⟩
      exact ⟨⟨b, hB_sub hb⟩, hb⟩
    rcases hY_well.wf.has_min s hs_ne with ⟨⟨m, hmY⟩, hm_s, hmmin⟩
    refine ⟨m, hm_s, ?_⟩
    intro x hx
    have hx_s : (⟨x, hB_sub hx⟩ : Subtype Y) ∈ s := hx
    rcases hY (⟨m, hmY⟩ : Subtype Y) (⟨x, hB_sub hx⟩ : Subtype Y) with (hmx | hxm)
    · simpa using hmx
    · by_cases h_eq : (⟨x, hB_sub hx⟩ : Subtype Y) = (⟨m, hmY⟩ : Subtype Y)
      · have hx_eq_m : x = m := congrArg Subtype.val h_eq
        subst hx_eq_m; exact le_refl _
      · exact (hmmin (⟨x, hB_sub hx⟩ : Subtype Y) hx_s (by
          have h_lt : (⟨x, hB_sub hx⟩ : Subtype Y) < (⟨m, hmY⟩ : Subtype Y) := lt_of_le_of_ne hxm h_eq
          simpa using h_lt)).elim
  have hY'_min (B : Set X) (hB_sub : B ⊆ Y') (hB_ne : B.Nonempty) : ∃ m ∈ B, ∀ x ∈ B, m ≤ x := by
    let s : Set (Subtype Y') := {y | (y : X) ∈ B}
    have hs_ne : s.Nonempty := by
      rcases hB_ne with ⟨b, hb⟩
      exact ⟨⟨b, hB_sub hb⟩, hb⟩
    rcases hY'_well.wf.has_min s hs_ne with ⟨⟨m, hmY'⟩, hm_s, hmmin⟩
    refine ⟨m, hm_s, ?_⟩
    intro x hx
    have hx_s : (⟨x, hB_sub hx⟩ : Subtype Y') ∈ s := hx
    rcases hY' (⟨m, hmY'⟩ : Subtype Y') (⟨x, hB_sub hx⟩ : Subtype Y') with (hmx | hxm)
    · simpa using hmx
    · by_cases h_eq : (⟨x, hB_sub hx⟩ : Subtype Y') = (⟨m, hmY'⟩ : Subtype Y')
      · have hx_eq_m : x = m := congrArg Subtype.val h_eq
        subst hx_eq_m; exact le_refl _
      · exact (hmmin (⟨x, hB_sub hx⟩ : Subtype Y') hx_s (by
          have h_lt : (⟨x, hB_sub hx⟩ : Subtype Y') < (⟨m, hmY'⟩ : Subtype Y') := lt_of_le_of_ne hxm h_eq
          simpa using h_lt)).elim
  rw [WellFoundedLT.iff' hYY']
  intro A hA
  rcases hA with ⟨a, haA⟩
  let A_X : Set X := {x | ∃ hx : x ∈ (Y ∪ Y' : Set X), (⟨x, hx⟩ : (Y ∪ Y' : Set X)) ∈ A}
  have hA_X_ne : A_X.Nonempty := by
    rcases a with ⟨x, hx⟩
    exact ⟨x, hx, haA⟩
  by_cases hAY : (A_X ∩ Y).Nonempty
  · rcases hY_min (A_X ∩ Y) (by intro x hx; exact hx.2) hAY with ⟨m, hm, hmmin⟩
    have hm_AX : m ∈ A_X := hm.1
    rcases hm_AX with ⟨hm_union, hmA⟩
    have hmA' : ((⟨m, Or.inl hm.2⟩ : U) : U) ∈ A := by simpa using hmA
    by_cases hAY' : (A_X ∩ Y').Nonempty
    · rcases hY'_min (A_X ∩ Y') (by intro x hx; exact hx.2) hAY' with ⟨m', hm', hm'min⟩
      have hm'_AX : m' ∈ A_X := hm'.1
      rcases hm'_AX with ⟨hm'_union, hm'A⟩
      have hm'A' : ((⟨m', Or.inr hm'.2⟩ : U) : U) ∈ A := by simpa using hm'A
      have h_total := hYY'.total (⟨m, Or.inl hm.2⟩ : (Y ∪ Y' : Set X)) (⟨m', Or.inr hm'.2⟩ : (Y ∪ Y' : Set X))
      rcases h_total with (h | h)
      · refine ⟨⟨(⟨m, Or.inl hm.2⟩ : (Y ∪ Y' : Set X)), hmA'⟩, λ y hlt => ?_⟩
        rcases y with ⟨⟨b, hb_union⟩, hb⟩
        have hb_AX : b ∈ A_X := ⟨hb_union, hb⟩
        rcases hb_union with (hbY | hbY')
        · have hmle_b : m ≤ b := hmmin b ⟨hb_AX, hbY⟩
          simpa using hmle_b
        · have hm'le_b : m' ≤ b := hm'min b ⟨hb_AX, hbY'⟩
          have hmle_m' : m ≤ m' := h
          simpa using le_trans hmle_m' hm'le_b
      · refine ⟨⟨(⟨m', Or.inr hm'.2⟩ : (Y ∪ Y' : Set X)), hm'A'⟩, λ y hlt => ?_⟩
        rcases y with ⟨⟨b, hb_union⟩, hb⟩
        have hb_AX : b ∈ A_X := ⟨hb_union, hb⟩
        rcases hb_union with (hbY | hbY')
        · have hmle_b : m ≤ b := hmmin b ⟨hb_AX, hbY⟩
          have hm'le_m : m' ≤ m := h
          simpa using le_trans hm'le_m hmle_b
        · have hm'le_b : m' ≤ b := hm'min b ⟨hb_AX, hbY'⟩
          simpa using hm'le_b
    · refine ⟨⟨(⟨m, Or.inl hm.2⟩ : (Y ∪ Y' : Set X)), hmA'⟩, λ y hlt => ?_⟩
      rcases y with ⟨⟨b, hb_union⟩, hb⟩
      have hb_AX : b ∈ A_X := ⟨hb_union, hb⟩
      rcases hb_union with (hbY | hbY')
      · have hmle_b : m ≤ b := hmmin b ⟨hb_AX, hbY⟩
        simpa using hmle_b
      · exfalso; exact hAY' ⟨b, ⟨hb_AX, hbY'⟩⟩
  · have hA_X_sub_Y' : A_X ⊆ Y' := by
      intro x hx_AX
      have hx_AX_copy : x ∈ A_X := hx_AX
      rcases hx_AX with ⟨hx_union, hx_mem_A⟩
      rcases hx_union with (hxY | hxY')
      · exfalso; exact hAY ⟨x, ⟨hx_AX_copy, hxY⟩⟩
      · exact hxY'
    rcases hY'_min A_X hA_X_sub_Y' hA_X_ne with ⟨m, hm_AX, hmmin⟩
    have hm_AX_copy : m ∈ A_X := hm_AX
    rcases hm_AX with ⟨hm_union, hmA⟩
    have hmY' : m ∈ Y' := by
      rcases hm_union with (hmY | hmY')
      · exfalso; exact hAY ⟨m, ⟨hm_AX_copy, hmY⟩⟩
      · exact hmY'
    have hmA' : (⟨m, Or.inr hmY'⟩ : (Y ∪ Y' : Set X)) ∈ A := by simpa using hmA
    refine ⟨⟨(⟨m, Or.inr hmY'⟩ : (Y ∪ Y' : Set X)), hmA'⟩, λ y hlt => ?_⟩
    rcases y with ⟨⟨b, hb_union⟩, hb⟩
    have hb_AX : b ∈ A_X := ⟨hb_union, hb⟩
    have hmle_b : m ≤ b := hmmin b hb_AX
    simpa using hmle_b

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
    have hsub : (pt : Set X) \ {x₀} = (∅ : Set X) := by
      ext x; simp
    simp [Ω, hsub]

  -- Exercise 8.5.13
  have ex_8_5_13 {Y Y':Ω} (x:X) (h: x ∈ (Y':Set X) \ Y) : IsStrictUpperBound Y x := by
    sorry

  -- Exercise 8.5.13
  have ex_8_5_13 {Y Y':Ω} (x:X) (h: x ∈ (Y':Set X) \ Y) : IsStrictUpperBound Y x := by
    sorry

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
    obtain ⟨Y, hYΩ, hxY⟩ := hx
    exact Y.val.property.2.2.2 x hxY
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
    rw [IsMin.iff_lowerbound' (IsTotal.subtype htotal)]
    use ⟨ _, hbY_infty ⟩, hbA; intro ⟨ x, hx ⟩ hxA
    simp [Y_infty] at hx ⊢; obtain ⟨ Y', ⟨ hY'Ω₀, hY'Ω ⟩, hxY' ⟩ := hx
    sorry
  have hY_inftyΩ₀ : Y_infty ∈ Ω₀ := by
    simp [Ω₀, htotal, hwell, hmem, hmin]
  set sY_infty : X := s ⟨ _, hY_inftyΩ₀ ⟩
  have hYs_total : IsTotal (Y_infty ∪ {sY_infty} : Set X) := by
    intro x y
    rcases x with ⟨x, hx⟩
    rcases y with ⟨y, hy⟩
    simp at hx hy
    rcases hx with (hx | rfl)
    · rcases hy with (hy | rfl)
      · have htot := htotal ⟨x, hx⟩ ⟨y, hy⟩
        simpa using htot
      · have hlt : x < sY_infty := hs hx
        exact Or.inl (le_of_lt hlt)
    · rcases hy with (hy | rfl)
      · have hlt : y < sY_infty := hs hy
        exact Or.inr (le_of_lt hlt)
      · exact Or.inl (le_refl _)
  have hYs_well : WellFoundedLT (Y_infty ∪ {sY_infty} : Set X) := by
    have hs_infty' : ∀ y ∈ Y_infty, y < sY_infty := by
      have hsi : IsStrictUpperBound Y_infty sY_infty := hs ⟨ _, hY_inftyΩ₀ ⟩
      simpa [IsStrictUpperBound.iff] using hsi
    rw [WellFoundedLT.iff' hYs_total]
    intro A hA
    rcases hA with ⟨a, ha⟩
    by_cases hA_inf_nonempty : ∃ (y : Subtype (Y_infty : Set X)), (⟨y.val, Or.inl y.property⟩ : (Y_infty ∪ {sY_infty} : Set X)) ∈ A
    · let A_inf : Set (Subtype (Y_infty : Set X)) :=
        {y | (⟨y.val, Or.inl y.property⟩ : (Y_infty ∪ {sY_infty} : Set X)) ∈ A}
      have hAinf_nonempty : A_inf.Nonempty := hA_inf_nonempty
      rcases ((WellFoundedLT.iff' htotal).mp hwell) A_inf hAinf_nonempty with ⟨⟨m, hm⟩, hmmin⟩
      have hmA : (⟨m.val, Or.inl m.property⟩ : (Y_infty ∪ {sY_infty} : Set X)) ∈ A := hm
      refine ⟨⟨⟨m.val, Or.inl m.property⟩, hmA⟩, ?_⟩
      intro ⟨⟨b, hb⟩, hbA⟩
      rcases hb with (hbY | rfl)
      · have hb_inf : (⟨b, hbY⟩ : Subtype (Y_infty : Set X)) ∈ A_inf := hbA
        have hmle : (⟨m.val, m.property⟩ : Subtype (Y_infty : Set X)) ≤ (⟨b, hbY⟩ : Subtype (Y_infty : Set X)) := hmmin ⟨⟨b, hbY⟩, hb_inf⟩
        simpa using hmle
      · have hlt : m.val < sY_infty := hs_infty' m.val m.property
        exact hlt
    · have : a.val = sY_infty := by
        have ha_mem : a.val ∈ Y_infty ∪ {sY_infty} := a.property
        simp at ha_mem
        rcases ha_mem with (h | h)
        · exfalso; exact hA_inf_nonempty ⟨⟨a.val, h⟩, ha⟩
        · exact h
      subst this
      refine ⟨a, ?_⟩
      intro ⟨⟨b, hb⟩, hbA⟩
      rcases hb with (hbY | rfl)
      · exfalso; exact hA_inf_nonempty ⟨⟨b, hbY⟩, hbA⟩
      · exact lt_irrefl _
  have hYs_mem : x₀ ∈ Y_infty ∪ {sY_infty} := by
    left; exact hmem
  have hYs_min : ∀ x ∈ Y_infty ∪ {sY_infty}, x₀ ≤ x := by
    intro x hx
    rcases hx with (hx | hx)
    · exact hmin hx
    · simp at hx; subst hx
      exact le_of_lt (hs hmem)
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
  sorry

/-- Exercise 8.5.1 -/
def empty_set_partial_order [h₀: LE Empty] : Decidable (∃ h : PartialOrder Empty, h.le = h₀.le) := by
  sorry

def empty_set_linear_order [h₀: LE Empty] : Decidable (∃ h : LinearOrder Empty, h.le = h₀.le) := by
  sorry

def empty_set_well_order [h₀: LT Empty]: Decidable (Nonempty (WellFoundedLT Empty)) := by
  sorry

/-- Exercise 8.5.2 -/
example : ∃ (X:Type) (h₀: LE X), (∀ x:X, x ≤ x) ∧ (∀ x y:X, x ≤ y → y ≤ x → x = y) ∧ ¬ (∀ x y z:X, x ≤ y → y ≤ z → x ≤ z) := by
  let X := Fin 3
  let le_rel : X → X → Prop := λ a b => a = b ∨ (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2)
  have h01 : (0 : X) ≠ 1 := by decide
  have h02 : (0 : X) ≠ 2 := by decide
  have h12 : (1 : X) ≠ 2 := by decide
  refine ⟨X, ⟨le_rel⟩, ?_, ?_, ?_⟩
  · intro x; exact Or.inl rfl
  · intro x y h h'
    rcases h with (h_eq|⟨hx0, hy1⟩|⟨hx1, hy2⟩)
    · exact h_eq
    · rcases h' with (h_eq'|⟨hy0, hx1'⟩|⟨hy1', hx2'⟩)
      · exact h_eq'.symm
      · exfalso; exact h01.symm (hy1.symm.trans hy0)
      · exfalso; exact h02 (hx0.symm.trans hx2')
    · rcases h' with (h_eq'|⟨hy0', hx1'⟩|⟨hy1', hx2'⟩)
      · exact h_eq'.symm
      · exfalso; exact h02 (hy0'.symm.trans hy2)
      · exfalso; exact h12.symm (hy2.symm.trans hy1')
  · intro h
    have h01' : le_rel (0 : X) (1 : X) := Or.inr (Or.inl ⟨rfl, rfl⟩)
    have h12' : le_rel (1 : X) (2 : X) := Or.inr (Or.inr ⟨rfl, rfl⟩)
    have h02' : le_rel (0 : X) (2 : X) := h 0 1 2 h01' h12'
    rcases h02' with (h_eq|⟨_, h21⟩|⟨h1', _⟩)
    · exact h02 h_eq
    · exact h12.symm h21
    · exact h01 h1'

example : ∃ (X:Type) (h₀: LE X), (∀ x:X, x ≤ x) ∧ (∀ x y z:X, x ≤ y → y ≤ z → x ≤ z) ∧ ¬ (∀ x y:X, x ≤ y → y ≤ x → x = y) := by
  let X := Fin 2
  let le_rel : X → X → Prop := λ a b => a = b ∨ (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0)
  have h01 : (0 : X) ≠ 1 := by decide
  refine ⟨X, ⟨le_rel⟩, ?_, ?_, ?_⟩
  · intro x; exact Or.inl rfl
  · intro x y z h h'
    rcases h with (h_eq|⟨hx0, hy1⟩|⟨hx1, hy0⟩)
    · exact h_eq ▸ h'
    · rcases h' with (h_eq'|⟨hy0', hz1⟩|⟨hy1', hz0⟩)
      · exact h_eq' ▸ (Or.inr (Or.inl ⟨hx0, hy1⟩))
      · exfalso; exact h01.symm (hy1.symm.trans hy0')
      · exact Or.inl (hx0.trans hz0.symm)
    · rcases h' with (h_eq'|⟨hy0', hz1⟩|⟨hy1', hz0⟩)
      · exact h_eq' ▸ (Or.inr (Or.inr ⟨hx1, hy0⟩))
      · exact Or.inl (hx1.trans hz1.symm)
      · exfalso; exact h01 (hy0.symm.trans hy1')
  · intro h
    have h01' : le_rel (0 : X) (1 : X) := Or.inr (Or.inl ⟨rfl, rfl⟩)
    have h10' : le_rel (1 : X) (0 : X) := Or.inr (Or.inr ⟨rfl, rfl⟩)
    have h_eq : (0 : X) = (1 : X) := h 0 1 h01' h10'
    exact h01 h_eq

example : ∃ (X:Type) (h₀: LE X), (∀ x y:X, x ≤ y → y ≤ x → x = y) ∧ (∀ x y z:X, x ≤ y → y ≤ z → x ≤ z) ∧ ¬ (∀ x:X, x ≤ x) := by
  let X := Fin 1
  let le_rel : X → X → Prop := λ _ _ => False
  refine ⟨X, ⟨le_rel⟩, ?_, ?_, ?_⟩
  · intro x y h h'
    exact False.elim h
  · intro x y z h h'
    exact False.elim h
  · intro h
    exact h 0

/-- Exercise 8.5.3: The divisibility ordering on PNat. -/
@[reducible] def PNat.divOrder : PartialOrder PNat where
  le x y := ∃ n : PNat, y = n * x
  lt x y := (∃ n : PNat, y = n * x) ∧ ¬∃ n : PNat, x = n * y
  le_refl := by
    intro x
    exact ⟨1, by simp⟩
  le_antisymm := by
    intro x y h1 h2
    rcases h1 with ⟨n, hn⟩
    rcases h2 with ⟨m, hm⟩
    have h_dvd1 : (x : ℕ) ∣ (y : ℕ) := by
      have h_val : (y : ℕ) = (n : ℕ) * (x : ℕ) := by exact_mod_cast hn
      rw [h_val]
      exact ⟨(n : ℕ), by ring⟩
    have h_dvd2 : (y : ℕ) ∣ (x : ℕ) := by
      have h_val : (x : ℕ) = (m : ℕ) * (y : ℕ) := by exact_mod_cast hm
      rw [h_val]
      exact ⟨(m : ℕ), by ring⟩
    exact PNat.eq (Nat.dvd_antisymm h_dvd1 h_dvd2)
  le_trans := by
    intro x y z h1 h2
    rcases h1 with ⟨n, hn⟩
    rcases h2 with ⟨m, hm⟩
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
  rcases h with ⟨h₀, h₀_eq⟩
  have h_total : ∀ x y : PNat, h₀.le x y ∨ h₀.le y x := h₀.le_total
  have h23 : h₀.le (2 : PNat) (3 : PNat) ∨ h₀.le (3 : PNat) (2 : PNat) := h_total 2 3
  rcases h23 with (h23 | h32)
  · have hdiv : ∃ n : PNat, (3 : PNat) = n * (2 : PNat) := by
      simpa [h₀_eq] using h23
    rcases hdiv with ⟨n, hn⟩
    have h_val : (3 : ℕ) = (n : ℕ) * (2 : ℕ) := by exact_mod_cast hn
    omega
  · have hdiv : ∃ n : PNat, (2 : PNat) = n * (3 : PNat) := by
      simpa [h₀_eq] using h32
    rcases hdiv with ⟨n, hn⟩
    have h_val : (2 : ℕ) = (n : ℕ) * (3 : ℕ) := by exact_mod_cast hn
    omega

/-- Exercise 8.5.4 -/
example : ¬ ∃ x : {x:ℝ| x > 0}, IsMin x := by
  intro h
  rcases h with ⟨⟨x, hx⟩, hxmin⟩
  have hx2 : x/2 > 0 := by
    have : x > 0 := hx
    nlinarith
  have hxpos : x > 0 := hx
  have hx2_le_x : x/2 ≤ x := by
    nlinarith [hxpos]
  have hle_sub : (⟨x/2, hx2⟩ : {x : ℝ | x > 0}) ≤ (⟨x, hx⟩ : {x : ℝ | x > 0}) :=
    Subtype.coe_le_coe.mp hx2_le_x
  have hle : (⟨x, hx⟩ : {x : ℝ | x > 0}) ≤ (⟨x/2, hx2⟩ : {x : ℝ | x > 0}) := hxmin hle_sub
  have hle' : x ≤ x/2 := hle
  nlinarith

/-- Exercise 8.5.5 -/
example {X Y:Type} [PartialOrder Y] (f:X → Y) : ∃ h₀: PartialOrder X, h₀.le = (fun x y ↦ f x < f y ∨ x = y) := by
  refine ⟨{
    le := fun x y => f x < f y ∨ x = y
    le_refl := fun x => Or.inr rfl
    le_antisymm := by
      intro x y hxy hyx
      rcases hxy with (hlt | rfl)
      · rcases hyx with (hlt' | rfl)
        · exact (lt_asymm hlt hlt').elim
        · rfl
      · rfl
    le_trans := by
      intro x y z hxy hyz
      rcases hxy with (hlt | rfl)
      · rcases hyz with (hlt' | rfl)
        · exact Or.inl (lt_trans hlt hlt')
        · exact Or.inl hlt
      · exact hyz
  }, rfl⟩

def Ex_8_5_5_b : Decidable (∀ (X Y:Type) (h: LinearOrder Y) (f:X → Y), ∃ h₀: LinearOrder X, h₀.le = (fun x y ↦ f x < f y ∨ x = y)) := by
  apply isFalse
  intro h
  let X := Fin 2
  let Y := Fin 1
  have hY : LinearOrder Y := inferInstance
  let f : X → Y := fun _ => 0
  have hX := h X Y hY f
  rcases hX with ⟨h₀, h₀_eq⟩
  have h_total : h₀.le (0 : X) (1 : X) ∨ h₀.le (1 : X) (0 : X) := h₀.le_total _ _
  rcases h_total with (h01 | h10)
  · have h01_eq : h₀.le (0 : X) (1 : X) = ((0 : Fin 1) < (0 : Fin 1) ∨ (0 : Fin 2) = (1 : Fin 2)) := by
      have := congrArg (fun g => g (0 : X) (1 : X)) h₀_eq
      beta_reduce at this
      simpa [f] using this
    have h01' : ((0 : Fin 1) < (0 : Fin 1) ∨ (0 : Fin 2) = (1 : Fin 2)) := h01_eq ▸ h01
    have : ¬((0 : Fin 1) < (0 : Fin 1)) := by decide
    have : (0 : Fin 2) ≠ (1 : Fin 2) := by decide
    simp at h01'
  · have h10_eq : h₀.le (1 : X) (0 : X) = ((0 : Fin 1) < (0 : Fin 1) ∨ (1 : Fin 2) = (0 : Fin 2)) := by
      have := congrArg (fun g => g (1 : X) (0 : X)) h₀_eq
      beta_reduce at this
      simpa [f] using this
    have h10' : ((0 : Fin 1) < (0 : Fin 1) ∨ (1 : Fin 2) = (0 : Fin 2)) := h10_eq ▸ h10
    have : ¬((0 : Fin 1) < (0 : Fin 1)) := by decide
    have : (1 : Fin 2) ≠ (0 : Fin 2) := by decide
    simp at h10'

-- Final part of Exercise 8.5.5; if the answer to the previous part is "no", modify the hypotheses to make it true.

/-- Exercise 8.5.6 -/
abbrev OrderIdeals (X: Type) [PartialOrder X] : Set (Set X) := .Iic '' (.univ : Set X)

def OrderIdeals.iso {X: Type} [PartialOrder X] : X ≃o OrderIdeals X := {
  toFun x := ⟨ .Iic x, by simp ⟩
  invFun := λ I =>
    have hI : I.1 ∈ .Iic '' (.univ : Set X) := I.2
    (hI.choose)
  left_inv := λ x => by
    dsimp [toFun, invFun]
    have hI : (.Iic x ∈ .Iic '' (.univ : Set X)) := by simp
    have hspec := hI.choose_spec
    rcases hspec with ⟨y, _, hy⟩
    have hxy : x ≤ y := by
      have hx : x ∈ .Iic x := le_refl x
      have hx' : x ∈ .Iic y := by simpa [hy] using hx
      exact hx'
    have hyx : y ≤ x := by
      have hy' : y ∈ .Iic y := le_refl y
      have hy'' : y ∈ .Iic x := by simpa [hy] using hy'
      exact hy''
    exact le_antisymm hxy hyx
  right_inv := by
    intro I
    ext y; simp
    have hI : I.1 ∈ .Iic '' (.univ : Set X) := I.2
    rcases hI with ⟨x, _, hx⟩
    simp [hx]
  map_rel_iff' := by
    intro a b
    simp
    constructor
    · intro h; apply h; rfl
    · intro h x hx; exact le_trans hx h
  }

/-- Exercise 8.5.7 -/
example {Y:Type} [PartialOrder Y] {x y:Y} (hx: IsMin x) (hy: IsMin y) : x = y := by
  have hxy : x ≤ y := hx y
  have hyx : y ≤ x := hy x
  exact le_antisymm hxy hyx

example {Y:Type} [PartialOrder Y] {x y:Y} (hx: IsMax x) (hy: IsMax y) : x = y := by
  have hyx : y ≤ x := hx y
  have hxy : x ≤ y := hy x
  exact le_antisymm hxy hyx

/-- Exercise 8.5.9 -/
example {X:Type} [LinearOrder X] (hmin: ∀ Y: Set X, Y.Nonempty → ∃ x:Y, IsMin x) (hmax: ∀ Y: Set X, Y.Nonempty → ∃ x:Y, IsMax x) : Finite X := by sorry


/-- Exercise 8.5.12.  Here we make a copy of Mathlib's {name}`Lex` wrapper for lexicographical orderings.  This wrapper is needed
because products `X × Y` of ordered sets are given the default instance of the product partial order instead of
the lexicographical one. -/
def Lex' (α : Type) := α

instance Lex'.partialOrder {X Y: Type} [PartialOrder X] [PartialOrder Y] : PartialOrder (Lex' (X × Y)) := {
  le := fun ⟨ x, y ⟩ ⟨ x', y' ⟩ ↦ (x < x') ∨ (x = x' ∧ y ≤ y')
  le_refl := by
    intro ⟨x, y⟩
    right; exact ⟨rfl, le_refl y⟩
  le_antisymm := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ (h | ⟨hx, hy⟩) (h' | ⟨hx', hy'⟩)
    · exact (lt_asymm h h').elim
    · exact (lt_irrefl x' (hx'.symm ▸ h)).elim
    · exact (lt_irrefl x (hx.symm ▸ h')).elim
    · have hy_eq : y = y' := le_antisymm hy hy'
      simp [hx, hy_eq]
  le_trans := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ ⟨x'', y''⟩ (h | ⟨hx, hy⟩) (h' | ⟨hx', hy'⟩)
    · exact Or.inl (lt_trans h h')
    · exact Or.inl (hx' ▸ h)
    · exact Or.inl (hx ▸ h')
    · exact Or.inr ⟨hx.trans hx', le_trans hy hy'⟩
}

instance Lex'.linearOrder {X Y:Type} [LinearOrder X] [LinearOrder Y] : LinearOrder (Lex' (X × Y)) :=
  { (by infer_instance : PartialOrder (Lex' (X × Y))) with
    le_total := by
      rintro ⟨x, y⟩ ⟨x', y'⟩
      by_cases hx_lt : x < x'
      · left; exact Or.inl hx_lt
      · by_cases hx'_lt : x' < x
        · right; exact Or.inl hx'_lt
        · have hx_eq : x = x' := le_antisymm (not_lt.mp hx'_lt) (not_lt.mp hx_lt)
          rcases le_total y y' with (hy | hy)
          · left; exact Or.inr ⟨hx_eq, hy⟩
          · right; exact Or.inr ⟨hx_eq.symm, hy⟩
    toDecidableLE := by
      intro a b
      apply decidable_of_iff ((a.1 < b.1) ∨ (a.1 = b.1 ∧ a.2 ≤ b.2))
      rfl
  }

instance Lex'.WellFoundedLT {X Y:Type} [LinearOrder X] [WellFoundedLT X] [LinearOrder Y] [WellFoundedLT Y]:
    WellFoundedLT (Lex' (X × Y)) := by
  have hX_wf : WellFounded (· < · : X → X → Prop) := IsWellFounded.wf
  have hY_wf : WellFounded (· < · : Y → Y → Prop) := IsWellFounded.wf
  have h_wf_lex : WellFounded (Prod.Lex (· < · : X → X → Prop) (· < · : Y → Y → Prop)) :=
    WellFounded.prod_lex hX_wf hY_wf
  have h_rel_eq : (· < · : Lex' (X × Y) → Lex' (X × Y) → Prop) =
      Prod.Lex (· < · : X → X → Prop) (· < · : Y → Y → Prop) := by
    ext a b
    rcases a with ⟨x, y⟩; rcases b with ⟨x', y'⟩
    constructor
    · intro h
      rcases h with ⟨hle, hnle⟩
      rcases hle with (hx_lt | ⟨hx_eq, hy_le⟩)
      · apply Prod.Lex.left; exact hx_lt
      · subst hx_eq
        have hy_lt : y < y' := by
          by_contra! h
          apply hnle
          exact Or.inr ⟨rfl, h⟩
        apply Prod.Lex.right; exact hy_lt
    · intro h
      cases h
      case left hx_lt =>
        refine ⟨Or.inl hx_lt, ?_⟩
        intro h'
        rcases h' with (hx'_lt | ⟨hx'_eq, _⟩)
        · exact lt_asymm hx_lt hx'_lt
        · exact lt_irrefl _ (hx'_eq ▸ hx_lt)
      case right hy_lt =>
        refine ⟨Or.inr ⟨rfl, le_of_lt hy_lt⟩, ?_⟩
        intro h'
        rcases h' with (hx'_lt | ⟨_, hy'_le⟩)
        · exact lt_irrefl _ hx'_lt
        · exact lt_irrefl _ (lt_of_lt_of_le hy_lt hy'_le)
  have h_wf : WellFounded (· < · : Lex' (X × Y) → Lex' (X × Y) → Prop) := by
    rw [h_rel_eq]
    exact h_wf_lex
  exact ⟨h_wf⟩


/-- Exercise 8.5.15 -/
theorem inj_trichotomy {X Y : Type}
    (h : ¬∃ f : X → Y, Function.Injective f) :
    ∃ g : Y → X, Function.Injective g := by sorry

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
  intro x y h
  -- h : (discrete X).le x y, i.e., x = y
  -- need p.le x y, which is p.le x x (since x = y), which holds by le_refl
  have h_eq : x = y := h
  subst h_eq
  exact le_refl x

theorem PartialOrder.discrete_isMin (X : Type) :
    @IsMin (PartialOrder X) (coarserOrder X).toPreorder.toLE
      (PartialOrder.discrete X) := by
  intro p h
  exact discrete_isBot X p

theorem PartialOrder.discrete_unique_min (X : Type) (p : PartialOrder X)
    (h : @IsMin (PartialOrder X) (coarserOrder X).toPreorder.toLE p) :
    p = discrete X := by
  have h_discrete_le_p : discrete X ≤ p := discrete_isBot X p
  have h_p_le_discrete : p ≤ discrete X := h h_discrete_le_p
  exact le_antisymm h_p_le_discrete h_discrete_le_p

/-- A partial ordering is maximal in the coarser order iff it is total. -/
theorem PartialOrder.isMax_iff_isTotal (X : Type) (p : PartialOrder X) :
    @IsMax (PartialOrder X) (coarserOrder X).toPreorder.toLE p ↔
    @IsTotal X p := by sorry

/-- Any partial ordering extends to a total ordering (by Zorn's lemma). -/
theorem PartialOrder.extends_to_total (X : Type) (p : PartialOrder X) :
    ∃ q : PartialOrder X, p ≤ q ∧ @IsTotal X q := by sorry

/-- Exercise 8.5.17: Use Zorn's lemma to reprove Exercise 8.4.2 -/
theorem exists_set_singleton_intersect' {I U : Type} {X : I → Set U}
    (h : Set.PairwiseDisjoint .univ X) (hne : ∀ α, Nonempty (X α)) :
    ∃ Y : Set U, ∀ α, Nat.card (Y ∩ X α : Set U) = 1 := by sorry

/-- Exercise 8.5.18 -/
theorem hausdorff_of_zorns_lemma {X : Type} [PartialOrder X] :
    ∃ M : Set X, Maximal (fun (S : Set X) => IsTotal S) M := by sorry

theorem zorns_lemma_of_hausdorff {X : Type} [PartialOrder X] [Nonempty X]
    (hhausdorff : ∃ M : Set X, Maximal (fun (S : Set X) => IsTotal S) M)
    (hchain : ∀ Y : Set X, IsTotal Y ∧ Y.Nonempty → ∃ x, IsUpperBound Y x) :
    ∃ x : X, IsMax x := by sorry

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
    W.carrier ⊂ W'.carrier := by sorry

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
  le_trans := by sorry

/-- The empty well-ordered subset. -/
def WellOrderedSubset.empty (X : Type) : WellOrderedSubset X where
  carrier := ∅
  ord := { PartialOrder.discrete (∅ : Set X) with
    le_total := fun ⟨_, h⟩ ↦ h.elim
    toDecidableLE := fun ⟨_, h⟩ ↦ h.elim }
  wf := ⟨⟨fun ⟨_, h⟩ ↦ h.elim⟩⟩

theorem WellOrderedSubset.empty_isMin (X : Type) :
    @IsMin (WellOrderedSubset X) (instPartialOrder X).toPreorder.toLE
      (empty X) := by sorry

/-- The maximal elements are precisely the well-orderings of all of X. -/
theorem WellOrderedSubset.isMax_iff_full (X : Type) (W : WellOrderedSubset X) :
    @IsMax (WellOrderedSubset X) (instPartialOrder X).toPreorder.toLE W ↔
    W.carrier = Set.univ := by sorry

/-- The well-ordering principle: every set has a well-ordering. -/
theorem well_ordering_principle (X : Type) :
    ∃ (l : LinearOrder X), @WellFoundedLT X l.toLT := by sorry

/-- Well-ordering principle implies axiom of choice. Well-order the disjoint union
`Σ i, X i`, then pick the minimum of each fiber. -/
theorem axiom_of_choice_of_well_ordering
    (hwo : ∀ T : Type, ∃ (l : LinearOrder T), @WellFoundedLT T l.toLT)
    {I : Type} {X : I → Type} (hne : ∀ i, Nonempty (X i)) :
    Nonempty (∀ i, X i) := by sorry

/-- Exercise 8.5.20 -/
theorem maximal_disjoint_subcollection {X : Type} (Ω : Set (Set X)) (hne : ∅ ∉ Ω) :
    ∃ Ω' ⊆ Ω, Ω'.Pairwise Disjoint ∧
      (∀ C ∈ Ω, ∃ A ∈ Ω', (C ∩ A).Nonempty) := by sorry

/-- The maximal disjoint subcollection property implies Exercise 8.4.2, hence is
equivalent to the axiom of choice. -/
theorem exists_set_singleton_intersect_of_maximal_disjoint
    (hmds : ∀ (X : Type) (Ω : Set (Set X)), ∅ ∉ Ω →
      ∃ Ω' ⊆ Ω, Ω'.Pairwise Disjoint ∧
        (∀ C ∈ Ω, ∃ A ∈ Ω', (C ∩ A).Nonempty))
    {I U : Type} {X : I → Set U}
    (h : Set.PairwiseDisjoint .univ X) (hne : ∀ α, Nonempty (X α)) :
    ∃ Y : Set U, ∀ α, Nat.card (Y ∩ X α : Set U) = 1 := by sorry

end Chapter8
