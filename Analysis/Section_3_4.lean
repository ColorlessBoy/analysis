import Mathlib.Tactic
import Analysis.Section_3_1

/-!
# Analysis I, Section 3.4: Images and inverse images

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Images and inverse images of (Mathlib) functions, within the framework of Section 3.1 set
  theory. (The Section 3.3 functions are now deprecated and will not be used further.)
- Connection with Mathlib's image {syntax term}`f '' S` and preimage {syntax term}`f ⁻¹' S` notions.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter3

export SetTheory (Set Object nat)

variable [SetTheory]

/-- Definition 3.4.1.  Interestingly, the definition does not require {lean}`S` to be a subset of {lean}`X`. -/
abbrev SetTheory.Set.image {X Y:Set} (f:X → Y) (S: Set) : Set :=
  X.replace (P := fun x y ↦ f x = y ∧ x.val ∈ S) (by intro x y z ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩; rw [← h1, ← h3]) -- simp_all

/-- Definition 3.4.1 -/
theorem SetTheory.Set.mem_image {X Y:Set} (f:X → Y) (S: Set) (y:Object) :
  y ∈ image f S ↔ ∃ x:X, x.val ∈ S ∧ f x = y := by
  rw [replacement_axiom]
  constructor
  · intro ⟨x, hx⟩; use x; exact ⟨hx.2, hx.1⟩
  intro ⟨x, hx⟩; use x; exact ⟨hx.2, hx.1⟩
  -- grind [replacement_axiom]

#print SetTheory.Set.mem_image

/-- Alternate definition of image using axiom of specification -/
theorem SetTheory.Set.image_eq_specify {X Y:Set} (f:X → Y) (S: Set) :
  image f S = Y.specify (fun y ↦ ∃ x:X, x.val ∈ S ∧ f x = y) := by
  apply SetTheory.Set.ext
  intro y
  rw [specification_axiom'', mem_image]
  constructor
  · intro ⟨x,⟨h1,h2⟩⟩
    have : y ∈ Y := by rw [← h2]; exact (f x).property
    use this
    use x
    apply And.intro h1
    rw [← Subtype.val_inj, h2]
  intro ⟨hy,x, h1,h2⟩
  use x
  apply And.intro h1
  exact Subtype.val_inj.mpr h2

/--
  Connection with Mathlib's notion of image.  Note the need to utilize the {name}`Subtype.val` coercion
  to make everything type consistent.
-/
theorem SetTheory.Set.image_eq_image {X Y:Set} (f:X → Y) (S: Set):
    (image f S: _root_.Set Object) = Subtype.val '' (f '' {x | x.val ∈ S}) := by
  ext; simp; grind

theorem SetTheory.Set.image_in_codomain {X Y:Set} (f:X → Y) (S: Set) :
    image f S ⊆ Y := by intro _ h; rw [mem_image] at h; grind

/-- Example 3.4.2 -/
abbrev f_3_4_2 : nat → nat := fun n ↦ (2*n:ℕ)

theorem SetTheory.Set.image_f_3_4_2 : image f_3_4_2 {1,2,3} = {2,4,6} := by
  ext; simp only [mem_image, mem_triple, f_3_4_2]
  constructor
  · rintro ⟨_, (_ | _ | _), rfl⟩ <;> simp_all
  rintro (_ | _ | _); map_tacs [use 1; use 2; use 3]
  all_goals simp_all

/-- Example 3.4.3 is written using Mathlib's notion of image. -/
example : (fun n:ℤ ↦ n^2) '' {-1,0,1,2} = {0,1,4} := by aesop

theorem SetTheory.Set.mem_image_of_eval {X Y:Set} (f:X → Y) (S: Set) (x:X) :
    x.val ∈ S → (f x).val ∈ image f S := by
    rw [mem_image]; intro h; use x

theorem SetTheory.Set.mem_image_of_eval_counter :
    ∃ (X Y:Set) (f:X → Y) (S: Set) (x:X), ¬((f x).val ∈ image f S → x.val ∈ S) := by
    use Nat, Nat, (fun n => (n - 1 :ℕ)), {0}, 1
    rw [mem_singleton]
    intro h
    have : (1 : Nat).val ≠ 0 := by simp
    apply this
    apply h
    rw [nat_equiv_coe_of_coe'', _root_.Nat.sub_self, Object.ofnat_eq, mem_image]
    use 0
    rw [mem_singleton]
    constructor
    · rfl
    rw [nat_equiv_coe_of_coe'' 0, Object.ofnat_eq, _root_.Nat.zero_sub]

/--
  Definition 3.4.4 (inverse images).
  Again, it is not required that {lean}`U` be a subset of {lean}`Y`.
-/
abbrev SetTheory.Set.preimage {X Y:Set} (f:X → Y) (U: Set) : Set := X.specify (P := fun x ↦ (f x).val ∈ U)

@[simp]
theorem SetTheory.Set.mem_preimage {X Y:Set} (f:X → Y) (U: Set) (x:X) :
    x.val ∈ preimage f U ↔ (f x).val ∈ U := by rw [specification_axiom']

/--
  A version of {name}`mem_preimage` that does not require {lean}`x` to be of type {lean}`X`.
-/
theorem SetTheory.Set.mem_preimage' {X Y:Set} (f:X → Y) (U: Set) (x:Object) :
    x ∈ preimage f U ↔ ∃ x': X, x'.val = x ∧ (f x').val ∈ U := by
  constructor
  . intro h
    have hx := specification_axiom h
    use ⟨ x, hx ⟩
    have := mem_preimage f U ⟨ _, hx ⟩
    apply And.intro (Eq.refl x)
    apply (mem_preimage _ _ _).mp h -- simp_all
  . rintro ⟨ x', rfl, hfx' ⟩; rwa [mem_preimage]

#print SetTheory.Set.mem_preimage'

/-- Connection with Mathlib's notion of preimage. -/
theorem SetTheory.Set.preimage_eq {X Y:Set} (f:X → Y) (U: Set) :
    ((preimage f U): _root_.Set Object) = Subtype.val '' (f⁻¹' {y | y.val ∈ U}) := by
  ext; simp

theorem SetTheory.Set.preimage_in_domain {X Y:Set} (f:X → Y) (U: Set) :
    (preimage f U) ⊆ X := by intro x hx; rw [mem_preimage'] at hx; obtain ⟨x', hx'⟩ := hx; rw [← hx'.1]; exact x'.property

/-- Example 3.4.6 -/
theorem SetTheory.Set.preimage_f_3_4_2 : preimage f_3_4_2 {2,4,6} = {1,2,3} := by
  ext; simp only [mem_preimage', mem_triple, f_3_4_2]; constructor
  · rintro ⟨x, rfl, (_ | _ | _)⟩ <;> simp_all <;> omega
  rintro (rfl | rfl | rfl); map_tacs [use 1; use 2; use 3]
  all_goals simp

theorem SetTheory.Set.image_preimage_f_3_4_2 :
    image f_3_4_2 (preimage f_3_4_2 {1,2,3}) ≠ {1,2,3} := by
    have : preimage f_3_4_2 {1,2,3} = {1} := by
      ext; simp only [mem_preimage', mem_triple, f_3_4_2]; constructor
      · rintro ⟨x, rfl, (_ | _ | _)⟩ <;> simp_all ; omega
      rw [mem_singleton]; intro h; use 1; simp; rw [h]; simp
    rw [this]
    have : image f_3_4_2 {1} = {2} := by
      ext; simp only [mem_image, f_3_4_2]; constructor
      · rintro ⟨x, hx, (_ | _ | _)⟩ ; simp_all
      rw [mem_singleton]; intro h; use 1; simp; rw [h]; simp
    rw [this]
    intro h
    rw [Set.ext_iff] at h
    have := h 1
    simp at this

/-- Example 3.4.7 (using the Mathlib notion of preimage) -/
example : (fun n:ℤ ↦ n^2) ⁻¹' {0,1,4} = {-2,-1,0,1,2} := by
  ext; refine ⟨ ?_, by aesop ⟩; rintro (_ | _ | h)
  on_goal 3 => have : 2 ^ 2 = (4:ℤ) := (by norm_num); rw [←h, sq_eq_sq_iff_eq_or_eq_neg] at this
  all_goals aesop

example : (fun n:ℤ ↦ n^2) ⁻¹' ((fun n:ℤ ↦ n^2) '' {-1,0,1,2}) ≠ {-1,0,1,2} := by
  intro h
  have : (-2:ℤ) ∈ (fun n:ℤ ↦ n^2) ⁻¹' ((fun n:ℤ ↦ n^2) '' {-1,0,1,2}) := by simp
  rw [h] at this
  simp_all

instance SetTheory.Set.inst_pow : Pow Set Set where
  pow := pow

@[coe]
def SetTheory.Set.coe_of_fun {X Y:Set} (f: X → Y) : Object := function_to_object X Y f

/-- This coercion has to be a {name}`CoeOut` rather than a
{name}`Coe` because the input type {lean}`X → Y` contains
parameters not present in the output type {name}`Object` -/
instance SetTheory.Set.inst_coe_of_fun {X Y:Set} : CoeOut (X → Y) Object where
  coe := coe_of_fun

@[simp]
theorem SetTheory.Set.coe_of_fun_inj {X Y:Set} (f g:X → Y) : (f:Object) = (g:Object) ↔ f = g := by
  simp [coe_of_fun]

/-- Axiom 3.11 (Power set axiom) --/
@[simp]
theorem SetTheory.Set.powerset_axiom {X Y:Set} (F:Object) :
    F ∈ (X ^ Y) ↔ ∃ f: Y → X, f = F := SetTheory.powerset_axiom X Y F

/-- Example 3.4.9 -/
abbrev f_3_4_9_a : ({4,7}:Set) → ({0,1}:Set) := fun x ↦ ⟨ 0, by simp ⟩

open Classical in
noncomputable abbrev f_3_4_9_b : ({4,7}:Set) → ({0,1}:Set) :=
  fun x ↦ if x.val = 4 then ⟨ 0, by simp ⟩ else ⟨ 1, by simp ⟩

open Classical in
noncomputable abbrev f_3_4_9_c : ({4,7}:Set) → ({0,1}:Set) :=
  fun x ↦ if x.val = 4 then ⟨ 1, by simp ⟩ else ⟨ 0, by simp ⟩

abbrev f_3_4_9_d : ({4,7}:Set) → ({0,1}:Set) := fun x ↦ ⟨ 1, by simp ⟩

theorem SetTheory.Set.example_3_4_9 (F:Object) :
    F ∈ ({0,1}:Set) ^ ({4,7}:Set) ↔ F = f_3_4_9_a
    ∨ F = f_3_4_9_b ∨ F = f_3_4_9_c ∨ F = f_3_4_9_d := by
  rw [powerset_axiom]
  refine ⟨?_, by aesop ⟩
  rintro ⟨f, rfl⟩
  have h1 := (f ⟨4, by simp⟩).property
  have h2 := (f ⟨7, by simp⟩).property
  simp [coe_of_fun_inj] at *
  obtain _ | _ := h1 <;> obtain _ | _ := h2
  map_tacs [left; (right;left); (right;right;left); (right;right;right)]
  all_goals ext ⟨_, hx⟩; simp at hx; grind

/-- Exercise 3.4.6 (i). One needs to provide a suitable definition of the power set here. -/
def SetTheory.Set.powerset (X:Set) : Set :=
  (({0,1} ^ X): Set).replace (P := fun F S ↦ ∃ f: X → ({(0:Object),1}:Set), F.val = f ∧ S = X.specify (fun x ↦ f x = ⟨1, by simp⟩)
) (by
  intro F S1 S2 ⟨h1, h2⟩
  obtain ⟨f1, hf1, hS1⟩ := h1
  obtain ⟨f2, hf2, hS2⟩ := h2
  rw [hS1, hS2, coe_eq_iff, Set.ext_iff]
  intro x
  rw [SetTheory.Set.specification_axiom'', SetTheory.Set.specification_axiom'']
  rw [hf1] at hf2
  have := (coe_of_fun_inj _ _).mp hf2
  constructor
  · rintro ⟨h, hx⟩; use h; rw [← hx, this]
  rintro ⟨h, hx⟩; use h; rw [← hx, ← this]
)

open Classical in
/-- Exercise 3.4.6 (i) -/
@[simp]
theorem SetTheory.Set.mem_powerset {X:Set} (x:Object) :
    x ∈ powerset X ↔ ∃ Y:Set, x = Y ∧ Y ⊆ X := by
    unfold powerset
    rw [replacement_axiom]
    constructor
    · rintro ⟨Y, FY, ⟨h1, h2⟩⟩
      use (X.specify fun x ↦ FY x = ⟨1, by simp⟩)
      apply And.intro h2
      apply specify_subset
    rintro ⟨Y, hx, hYX⟩
    -- X : Set
    -- x : Object
    -- Y : Set
    -- hx : x = set_to_object Y
    -- hYX : Y ⊆ X
    -- |- ∃ (x_1 : ({0, 1} ^ X).toSubtype) (f : X.toSubtype → {0, 1}.toSubtype), ↑x_1 = ↑f ∧ x = set_to_object (X.specify fun x ↦ f x = ⟨1, ⋯⟩)
    have : ∃ f: X → ({(0:Object),1}:Set), ∀ x:X, f x = ⟨1, by simp⟩ ↔ x.val ∈ Y := by
      use fun x ↦ if x.val ∈ Y then ⟨ 1, by simp ⟩ else ⟨ 0, by simp ⟩
      intro x
      by_cases h : x.val ∈ Y
      . simp [h]
      simp [h]
    obtain ⟨f, hf⟩ := this
    -- X : Set
    -- x : Object
    -- Y : Set
    -- hx : x = set_to_object Y
    -- hYX : Y ⊆ X
    -- f : X.toSubtype → {0, 1}.toSubtype
    -- hf : ∀ (x : X.toSubtype), f x = ⟨1, ⋯⟩ ↔ ↑x ∈ Y
    -- |- ∃ (x_1 : ({0, 1} ^ X).toSubtype) (f : X.toSubtype → {0, 1}.toSubtype), ↑x_1 = ↑f ∧ x = set_to_object (X.specify fun x ↦ f x = ⟨1, ⋯⟩)
    use ⟨f, by simp⟩ -- why `simp` works? because `{0, 1} ^ X` is `X.toSubtype → {0, 1}.toSubtype` by definition.
    use f
    apply And.intro rfl
    rw [hx, coe_eq_iff, Set.ext_iff]
    intro x
    rw [specification_axiom'']
    constructor
    · intro h
      have h1 := hYX x h
      use h1
      have := hf ⟨x, h1⟩
      rw [this]
      exact h
    rintro ⟨h1, h2⟩
    have := hf ⟨x, h1⟩
    rw [← this]
    exact h2

/-- Lemma 3.4.10 -/
theorem SetTheory.Set.exists_powerset (X:Set) :
   ∃ (Z: Set), ∀ x, x ∈ Z ↔ ∃ Y:Set, x = Y ∧ Y ⊆ X := by
  use powerset X; apply mem_powerset

/- As noted in errata, Exercise 3.4.6 (ii) is replaced by Exercise 3.5.11. -/

/-- Remark 3.4.11 -/
theorem SetTheory.Set.powerset_of_triple (a b c x:Object) :
    x ∈ powerset {a,b,c}
    ↔ x = (∅:Set)
    ∨ x = ({a}:Set)
    ∨ x = ({b}:Set)
    ∨ x = ({c}:Set)
    ∨ x = ({a,b}:Set)
    ∨ x = ({a,c}:Set)
    ∨ x = ({b,c}:Set)
    ∨ x = ({a,b,c}:Set) := by
  simp only [mem_powerset, subset_def, mem_triple]
  refine ⟨ ?_, by aesop ⟩
  rintro ⟨Y, rfl, hY⟩; by_cases a ∈ Y <;> by_cases b ∈ Y <;> by_cases c ∈ Y
  on_goal 8 => left
  on_goal 4 => right; left
  on_goal 6 => right; right; left
  on_goal 7 => right; right; right; left
  on_goal 2 => right; right; right; right; left
  on_goal 3 => right; right; right; right; right; left
  on_goal 5 => right; right; right; right; right; right; left
  on_goal 1 => right; right; right; right; right; right; right
  all_goals congr; ext; simp; grind

/-- Axiom 3.12 (Union) -/
theorem SetTheory.Set.union_axiom (A: Set) (x:Object) :
    x ∈ union A ↔ ∃ (S:Set), x ∈ S ∧ (S:Object) ∈ A := SetTheory.union_axiom A x

/-- Example 3.4.12 -/
theorem SetTheory.Set.example_3_4_12 :
    union { (({2,3}:Set):Object), (({3,4}:Set):Object), (({4,5}:Set):Object) } = {2,3,4,5} := by
  ext x
  rw [union_axiom]
  constructor
  · rintro ⟨S, ⟨h1, h2⟩⟩
    rw [mem_triple, coe_eq_iff, coe_eq_iff, coe_eq_iff] at h2
    obtain h | h | h := h2 <;> simp_all;
    · rw [← or_assoc]; left; exact h1
    · right; rw [← or_assoc]; left; exact h1
  aesop

/-- Connection with Mathlib union -/
theorem SetTheory.Set.union_eq (A: Set) :
    (union A : _root_.Set Object) =
    ⋃₀ { S : _root_.Set Object | ∃ S':Set, S = S' ∧ (S':Object) ∈ A } := by
  ext; simp [union_axiom, Set.mem_sUnion]; aesop

/-- Indexed union -/
abbrev SetTheory.Set.iUnion (I: Set) (A: I → Set) : Set :=
  union (I.replace (P := fun α S ↦ S = A α) (by intro _ _ _ ⟨h1, h2⟩; exact h1.trans h2.symm))

theorem SetTheory.Set.mem_iUnion {I:Set} (A: I → Set) (x:Object) :
    x ∈ iUnion I A ↔ ∃ α:I, x ∈ A α := by
  rw [union_axiom]; constructor
  . simp_all [replacement_axiom]
  simp_all [replacement_axiom]

open Classical in
noncomputable abbrev SetTheory.Set.index_example : ({1,2,3}:Set) → Set :=
  fun i ↦ if i.val = 1 then {2,3} else if i.val = 2 then {3,4} else {4,5}

theorem SetTheory.Set.iUnion_example : iUnion {1,2,3} index_example = {2,3,4,5} := by
  apply ext; intros; simp [mem_iUnion, index_example, Insert.insert]
  refine ⟨ by aesop, ?_ ⟩; rintro (_ | _ | _); map_tacs [use 1; use 2; use 3]
  all_goals aesop

/-- Connection with Mathlib indexed union -/
theorem SetTheory.Set.iUnion_eq (I: Set) (A: I → Set) :
    (iUnion I A : _root_.Set Object) = ⋃ α, (A α: _root_.Set Object) := by
  ext; simp [mem_iUnion]

theorem SetTheory.Set.iUnion_of_empty (A: (∅:Set) → Set) : iUnion (∅:Set) A = ∅ := by
  rw [Set.ext_iff]
  intro x
  constructor
  · rw [mem_iUnion]; rintro ⟨y, hy⟩; exfalso; apply not_mem_empty y y.property
  intro h; exfalso; apply not_mem_empty x h

/-- Indexed intersection -/
noncomputable abbrev SetTheory.Set.nonempty_choose {I:Set} (hI: I ≠ ∅) : I :=
  ⟨(nonempty_def hI).choose, (nonempty_def hI).choose_spec⟩

abbrev SetTheory.Set.iInter' (I:Set) (β:I) (A: I → Set) : Set :=
  (A β).specify (P := fun x ↦ ∀ α:I, x.val ∈ A α)

noncomputable abbrev SetTheory.Set.iInter (I: Set) (hI: I ≠ ∅) (A: I → Set) : Set :=
  iInter' I (nonempty_choose hI) A

theorem SetTheory.Set.mem_iInter {I:Set} (hI: I ≠ ∅) (A: I → Set) (x:Object) :
    x ∈ iInter I hI A ↔ ∀ α:I, x ∈ A α := by
  rw [Set.specification_axiom'']
  constructor
  · rintro ⟨h1, h2⟩; exact h2
  intro h
  use h (nonempty_choose hI)

/-- Exercise 3.4.1 -/
theorem SetTheory.Set.preimage_eq_image_of_inv {X Y V:Set} (f:X → Y) (f_inv: Y → X)
  (hf: Function.LeftInverse f_inv f ∧ Function.RightInverse f_inv f) (_: V ⊆ Y) :
    image f_inv V = preimage f V := by
    rw [Set.ext_iff]
    intro x
    rw [mem_image, specification_axiom'']
    constructor
    · rintro ⟨y, hy, hx⟩
      have hy2 := hf.2 y
      have h1 := (f_inv y).property
      rw [hx] at h1
      use h1
      have h2 : f_inv y = ⟨x, h1⟩ := by
        rw [← Subtype.val_inj]
        exact hx
      have h3: (f ⟨x, h1⟩).val = y.val := by
        rw [Subtype.val_inj, ← hy2, h2]
      rw [h3]
      exact hy
    rintro ⟨h1, h2⟩
    use (f ⟨x, h1⟩)
    apply And.intro h2
    have h3 : f_inv (f ⟨x, h1⟩) = ⟨x, h1⟩ := by apply hf.left
    apply Subtype.val_inj.mpr h3

/- Exercise 3.4.2.  State and prove an assertion connecting `preimage f (image f S)` and `S`. -/
theorem SetTheory.Set.preimage_of_image {X Y:Set} (f:X → Y) (S: Set) (hS: S ⊆ X) : S ⊆ preimage f (image f S) := by
  intro x hx
  rw [specification_axiom'']
  have hx2 := hS x hx
  use hx2
  rw [mem_image]
  use ⟨x, hx2⟩

/- Exercise 3.4.2.  State and prove an assertion connecting `image f (preimage f U)` and `U`.
Interestingly, it is not needed for U to be a subset of Y. -/
theorem SetTheory.Set.image_of_preimage {X Y:Set} (f:X → Y) (U: Set) : image f (preimage f U) ⊆ U := by
  intro y hy
  rw [mem_image] at hy
  obtain ⟨x, hx', hx''⟩ := hy
  rw [← hx'']
  rw [specification_axiom''] at hx'
  obtain ⟨h1, h2⟩ := hx'
  exact h2

/- Exercise 3.4.2.  State and prove an assertion connecting `preimage f (image f (preimage f U))` and `preimage f U`.
Interestingly, it is not needed for U to be a subset of Y.-/
theorem SetTheory.Set.preimage_of_image_of_preimage {X Y:Set} (f:X → Y) (U: Set) : preimage f (image f (preimage f U)) = preimage f U := by
  rw [Set.ext_iff]
  intro x
  rw [specification_axiom'', specification_axiom'']
  constructor
  · rintro ⟨h1, h2⟩
    use h1
    apply image_of_preimage f
    exact h2
  rintro ⟨h1, h2⟩
  use h1
  rw [mem_image]
  use ⟨x, h1⟩
  rw [mem_preimage]
  exact ⟨h2, rfl⟩

/--
  Exercise 3.4.3.
-/
theorem SetTheory.Set.image_of_inter {X Y:Set} (f:X → Y) (A B: Set) :
    image f (A ∩ B) ⊆ (image f A) ∩ (image f B) := by
    intro y hy
    rw [mem_image] at hy
    obtain ⟨x, hx', hx''⟩ := hy
    rw [mem_inter] at hx'
    rw [mem_inter, mem_image, mem_image]
    constructor
    · use x; exact ⟨hx'.1, hx''⟩
    use x; exact ⟨hx'.2, hx''⟩

theorem SetTheory.Set.image_of_diff {X Y:Set} (f:X → Y) (A B: Set) :
    (image f A) \ (image f B) ⊆ image f (A \ B) := by
    intro y
    rw [mem_sdiff, mem_image, mem_image, mem_image, not_exists]
    rintro ⟨⟨x, h1, h2⟩, h3⟩
    use x
    rw [mem_sdiff]
    have h4 := h3 x
    rw [and_comm, not_and] at h4
    have h5 := h4 h2
    exact ⟨⟨h1, h5⟩, h2⟩

theorem SetTheory.Set.image_of_union {X Y:Set} (f:X → Y) (A B: Set) :
    image f (A ∪ B) = (image f A) ∪ (image f B) := by
    rw [Set.ext_iff]
    intro y
    rw [mem_image, mem_union]
    constructor
    -- ⊢ (∃ x_1, ↑x_1 ∈ A ∪ B ∧ ↑(f x_1) = x) → x ∈ image f A ∨ x ∈ image f B
    · rintro ⟨x1, h1, h2⟩
      rw [mem_image, mem_image]
      rw [mem_union] at h1
      apply Or.imp _ _ h1
      · intro h3; use x1
      intro h3; use x1
    rw [mem_image, mem_image]
    intro h
    rcases h with h | h
    · obtain ⟨x, h1, h2⟩ := h
      use x
      rw [mem_union]
      exact ⟨Or.inl h1, h2⟩
    obtain ⟨x, h1, h2⟩ := h
    use x
    rw [mem_union]
    exact ⟨Or.inr h1, h2⟩

def SetTheory.Set.image_of_inter' : Decidable (∀ X Y:Set, ∀ f:X → Y, ∀ A B: Set, image f (A ∩ B) = (image f A) ∩ (image f B)) := by
  -- The first line of this construction should be either `apply isTrue` or `apply isFalse`
  apply isFalse
  intro h
  have h1 := h {0,1} {0} (fun n => ⟨0, by simp⟩) {0} {1}
  rw [Set.ext_iff] at h1
  have h2 := h1 (0:Object)
  simp at h2

def SetTheory.Set.image_of_diff' : Decidable (∀ X Y:Set, ∀ f:X → Y, ∀ A B: Set, image f (A \ B) = (image f A) \ (image f B)) := by
  -- The first line of this construction should be either `apply isTrue` or `apply isFalse`
  apply isFalse
  intro h
  have h1 := h {0, 1} {0} (fun n => ⟨0, by simp⟩) {0, 1} {1}
  rw [Set.ext_iff] at h1
  have h2 := h1 (0: Object)
  simp at h2

/-- Exercise 3.4.4 -/
theorem SetTheory.Set.preimage_of_inter {X Y:Set} (f:X → Y) (A B: Set) :
    preimage f (A ∩ B) = (preimage f A) ∩ (preimage f B) := by
    rw [Set.ext_iff]
    intro x
    rw [mem_inter, specification_axiom'', specification_axiom'', specification_axiom'']
    constructor
    · rintro ⟨hx, hAB⟩
      rw [mem_inter] at hAB
      constructor
      · use hx; exact hAB.1
      use hx; exact hAB.2
    rintro ⟨⟨h1, h2⟩,⟨h3,h4⟩⟩
    use h1; rw [mem_inter]; exact ⟨h2, h4⟩

theorem SetTheory.Set.preimage_of_union {X Y:Set} (f:X → Y) (A B: Set) :
    preimage f (A ∪ B) = (preimage f A) ∪ (preimage f B) := by
    rw [Set.ext_iff]
    intro x
    rw [mem_union, specification_axiom'', specification_axiom'', specification_axiom'']
    constructor
    · rintro ⟨hx, hAB⟩
      rw [mem_union] at hAB
      rcases hAB with hAB | hAB
      · left; use hx
      right; use hx
    intro h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · use h1; rw [mem_union]; left; exact h2
    use h1; rw [mem_union]; right; exact h2

theorem SetTheory.Set.preimage_of_diff {X Y:Set} (f:X → Y) (A B: Set) :
    preimage f (A \ B) = (preimage f A) \ (preimage f B)  := by
    rw [Set.ext_iff]
    intro x
    rw [mem_sdiff, specification_axiom'', specification_axiom'', specification_axiom'']
    constructor
    · rintro ⟨hx, hAB⟩
      rw [mem_sdiff] at hAB
      constructor
      · use hx; exact hAB.1
      rintro ⟨h2, h3⟩
      exact hAB.2 h3
    rintro ⟨⟨h1, h2⟩, h3⟩
    use h1; rw [mem_sdiff]; apply And.intro h2
    contrapose! h3
    use h1

/-- Exercise 3.4.5 -/
theorem SetTheory.Set.image_preimage_of_surj {X Y:Set} (f:X → Y) :
    (∀ S, S ⊆ Y → image f (preimage f S) = S) ↔ Function.Surjective f := by
    constructor
    · intro h y
      let S := ({y.val}: Set)
      have : S ⊆ Y := by intro x; rw [mem_singleton]; intro h; rw [h]; exact y.property
      have := h _ this
      have : y.val ∈ image f (preimage f S) := by rw [this,mem_singleton]
      rw [mem_image] at this
      obtain ⟨x, hx, hx'⟩ := this
      use x; rw [← Subtype.val_inj]; exact hx'
    intro h1 S h2
    apply subset_antisymm
    apply image_of_preimage f
    intro y hy
    rw [mem_image]
    obtain ⟨x, hx⟩ := h1 ⟨y,h2 y hy⟩
    use x
    constructor
    · rw [mem_preimage, hx]; exact hy
    exact Subtype.val_inj.mpr hx

/-- Exercise 3.4.5 -/
theorem SetTheory.Set.preimage_image_of_inj {X Y:Set} (f:X → Y) :
    (∀ S, S ⊆ X → preimage f (image f S) = S) ↔ Function.Injective f := by
    constructor
    · intro h x y hxy
      let S := ({x.val}: Set)
      have : S ⊆ X := by intro z; rw [mem_singleton]; intro h; rw [h]; exact x.property
      have h1 := h _ this
      rw [Set.ext_iff] at h1
      have h2 := h1 y
      rw [mem_preimage, mem_image, mem_singleton, Eq.comm] at h2
      apply Subtype.val_inj.mp
      apply h2.mp
      use x
      rw [mem_singleton]
      apply And.intro rfl
      apply Subtype.val_inj.mpr hxy
    intro h1 S hS
    rw [Set.ext_iff]
    intro y
    rw [specification_axiom'']
    constructor
    · rintro ⟨h2, h3⟩; rw [mem_image] at h3; obtain ⟨x, hx, hx'⟩ := h3
      have h4 := h1 (Subtype.val_inj.mp hx')
      rw [← Subtype.val_inj] at h4
      rw [h4] at hx
      exact hx
    intro h1; use (hS y h1); rw [mem_image]; use  ⟨y, hS y h1⟩

/-- Helper lemma for Exercise 3.4.7. -/
@[simp]
lemma SetTheory.Set.mem_powerset' {S S' : Set} : (S': Object) ∈ S.powerset ↔ S' ⊆ S := by
  simp [mem_powerset]

/-- Another helper lemma for Exercise 3.4.7. -/
lemma SetTheory.Set.mem_union_powerset_replace_iff {S : Set} {P : S.powerset → Object → Prop} {hP : _} {x : Object} :
    x ∈ union (S.powerset.replace (P := P) hP) ↔
    ∃ (S' : S.powerset) (U : Set), P S' U ∧ x ∈ U := by
  grind [union_axiom, replacement_axiom]

noncomputable def SetTheory.Set.partial_functions_inner (Y : Set) (S' : Set) : Set :=
  let Q (T : Y.powerset) (U : Object) : Prop :=
    ∃ T' : Set, (T' : Object) = T.val ∧ U = (T' ^ S' : Set)
  have hQ : ∀ (T : Y.powerset) (U U' : Object), Q T U ∧ Q T U' → U = U' := by
    intro T U U' ⟨⟨T1, hT1, hU1⟩, ⟨T2, hT2, hU2⟩⟩
    have h1 : (T1 : Object) = (T2 : Object) := by rw [hT1, hT2]
    have h2 : T1 = T2 := Set.coe_eq h1
    subst h2; simp_all
  union (Y.powerset.replace hQ)

lemma SetTheory.Set.mem_partial_functions_inner {Y S' : Set} {F : Object} :
    F ∈ partial_functions_inner Y S' ↔
    ∃ Y' : Set, Y' ⊆ Y ∧ ∃ f : S' → Y', F = f := by
  unfold SetTheory.Set.partial_functions_inner;
  rw [mem_union_powerset_replace_iff]
  -- simp [mem_union_powerset_replace_iff] at *;
  constructor
  · rintro ⟨Y', U, ⟨⟨T', h1, h2⟩, h3⟩⟩
    use T'
    constructor
    · have := Y'.property
      rw [← h1, mem_powerset'] at this; exact this
    apply coe_eq at h2
    rw [h2, powerset_axiom] at h3
    obtain ⟨f, hf⟩ := h3
    use f
    rw [hf]
  rintro ⟨Y', hY', ⟨f, hf⟩⟩
  use ⟨Y', by rw [mem_powerset']; exact hY'⟩, Y'^S'
  constructor
  · use Y'
  rw [powerset_axiom]
  use f
  rw [hf]

/-- Exercise 3.4.7 -/
theorem SetTheory.Set.partial_functions {X Y:Set} :
    ∃ Z:Set, ∀ F:Object, F ∈ Z ↔ ∃ X' Y':Set, X' ⊆ X ∧ Y' ⊆ Y ∧ ∃ f: X' → Y', F = f := by
  -- Z = ⋃_{X' ⊆ X} (⋃_{Y' ⊆ Y} Y'^X')
  let P (S : X.powerset) (U : Object) : Prop :=
    ∃ S' : Set, (S' : Object) = S.val ∧ U = partial_functions_inner Y S'
  have hP : ∀ (S : X.powerset) (U U' : Object), P S U ∧ P S U' → U = U' := by
    intro S U U' ⟨⟨S1, hS1, hU1⟩, ⟨S2, hS2, hU2⟩⟩
    have h1 : (S1 : Object) = (S2 : Object) := by rw [hS1, hS2]
    have h2 : S1 = S2 := Set.coe_eq h1
    subst h2; simp_all
  use union (X.powerset.replace hP)
  intro F
  rw [mem_union_powerset_replace_iff]
  constructor
  · -- F ∈ Z → partial function
    rintro ⟨S, U, ⟨S', hS', hU⟩, hF⟩
    have hU' : U = partial_functions_inner Y S' := Set.coe_eq hU
    rw [hU', mem_partial_functions_inner] at hF
    obtain ⟨Y', hY', f, hf⟩ := hF
    refine ⟨S', Y', ?_, hY', f, hf⟩
    have := S.property
    rw [← hS'] at this
    exact mem_powerset'.mp this
  · -- partial function → F ∈ Z
    rintro ⟨X', Y', h1, h2, f, hf⟩
    use ⟨X', mem_powerset'.mpr h1⟩, partial_functions_inner Y X'
    constructor
    · exact ⟨X', rfl, rfl⟩
    · rw [mem_partial_functions_inner]
      exact ⟨Y', h2, f, hf⟩

/--
  Exercise 3.4.8.  The point of this exercise is to prove it without using the
  pairwise union operation {kw (of := «term_∪_»)}`∪`.
-/
theorem SetTheory.Set.union_pair_exists (X Y:Set) : ∃ Z:Set, ∀ x, x ∈ Z ↔ (x ∈ X ∨ x ∈ Y) := by
  sorry

/-- Exercise 3.4.9 -/
theorem SetTheory.Set.iInter'_insensitive {I:Set} (β β':I) (A: I → Set) :
    iInter' I β A = iInter' I β' A := by sorry

/-- Exercise 3.4.10 -/
theorem SetTheory.Set.union_iUnion {I J:Set} (A: (I ∪ J:Set) → Set) :
    iUnion I (fun α ↦ A ⟨ α.val, by simp [α.property]⟩)
    ∪ iUnion J (fun α ↦ A ⟨ α.val, by simp [α.property]⟩)
    = iUnion (I ∪ J) A := by sorry

/-- Exercise 3.4.10 -/
theorem SetTheory.Set.union_of_nonempty {I J:Set} (hI: I ≠ ∅) (hJ: J ≠ ∅) : I ∪ J ≠ ∅ := by sorry

/-- Exercise 3.4.10 -/
theorem SetTheory.Set.inter_iInter {I J:Set} (hI: I ≠ ∅) (hJ: J ≠ ∅) (A: (I ∪ J:Set) → Set) :
    iInter I hI (fun α ↦ A ⟨ α.val, by simp [α.property]⟩)
    ∩ iInter J hJ (fun α ↦ A ⟨ α.val, by simp [α.property]⟩)
    = iInter (I ∪ J) (union_of_nonempty hI hJ) A := by sorry

/-- Exercise 3.4.11 -/
theorem SetTheory.Set.compl_iUnion {X I: Set} (hI: I ≠ ∅) (A: I → Set) :
    X \ iUnion I A = iInter I hI (fun α ↦ X \ A α) := by sorry

/-- Exercise 3.4.11 -/
theorem SetTheory.Set.compl_iInter {X I: Set} (hI: I ≠ ∅) (A: I → Set) :
    X \ iInter I hI A = iUnion I (fun α ↦ X \ A α) := by sorry

end Chapter3
