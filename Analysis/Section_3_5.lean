import Mathlib.Tactic
import Analysis.Section_3_1
import Analysis.Section_3_2
import Analysis.Section_3_4

/-!
# Analysis I, Section 3.5: Cartesian products

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Ordered pairs and n-tuples.
- Cartesian products and n-fold products.
- Finite choice.
- Connections with Mathlib counterparts such as {name}`Set.pi` and {name}`Set.prod`.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

--/

namespace Chapter3

export SetTheory (Set Object nat)

variable [SetTheory]

open SetTheory.Set

/-- Definition 3.5.1 (Ordered pair).  One could also have used {lean}`Object × Object` to
define {name}`OrderedPair` here. -/
@[ext]
structure OrderedPair where
  fst: Object
  snd: Object

/-- Definition 3.5.1 (Ordered pair) -/
@[simp]
theorem OrderedPair.eq (x y x' y' : Object) :
    (⟨ x, y ⟩ : OrderedPair) = (⟨ x', y' ⟩ : OrderedPair) ↔ x = x' ∧ y = y' := by
    rw [OrderedPair.ext_iff]


/-- Helper lemma for Exercise 3.5.1 -/
lemma SetTheory.Set.pair_eq_singleton_iff {a b c: Object} : {a, b} = ({c}: Set) ↔
    a = c ∧ b = c := by
  constructor
  . intro h
    constructor
    · rw [← mem_singleton, ← h, mem_pair]; left; rfl
    rw [← mem_singleton, ← h, mem_pair]; right; rfl
  rintro ⟨h1, h2⟩
  rw [h1, h2, pair_self]

/-- Exercise 3.5.1, first part -/
def OrderedPair.toObject : OrderedPair ↪ Object where
  toFun p := ({ (({p.fst}:Set):Object), (({p.fst, p.snd}:Set):Object) }:Set)
  inj' := by
    intro x y h
    rw [OrderedPair.ext_iff]
    have hxy := SetTheory.Set.coe_eq h
    rcases SetTheory.Set.pair_eq_pair hxy with hxy | hxy
    · rw [coe_eq_iff, coe_eq_iff] at hxy
      have hfst : x.fst = y.fst := by rw [← mem_singleton, ← hxy.1, mem_singleton]
      apply And.intro hfst
      rcases SetTheory.Set.pair_eq_pair hxy.2 with hs | hs
      · exact hs.2
      rw [hs.2, ← hfst, hs.1]
    · rw [coe_eq_iff, coe_eq_iff, pair_eq_singleton_iff, Eq.comm, pair_eq_singleton_iff] at hxy
      obtain ⟨⟨h1, h2⟩,⟨h3, h4⟩⟩ := hxy
      apply And.intro h3
      rw [h4, h2, h3]

instance OrderedPair.inst_coeObject : Coe OrderedPair Object where
  coe := toObject

/--
  A technical operation, turning a object $`x` and a set $`Y` to a set $`{x} × Y`, needed to define
  the full Cartesian product
-/
abbrev SetTheory.Set.slice (x:Object) (Y:Set) : Set :=
  Y.replace (P := fun y z ↦ z = (⟨x, y⟩:OrderedPair)) (by grind)

@[simp]
theorem SetTheory.Set.mem_slice (x z:Object) (Y:Set) :
    z ∈ (SetTheory.Set.slice x Y) ↔ ∃ y:Y, z = (⟨x, y⟩:OrderedPair) := replacement_axiom _ _

/-- Definition 3.5.4 (Cartesian product) -/
abbrev SetTheory.Set.cartesian (X Y:Set) : Set :=
  union (X.replace (P := fun x z ↦ z = slice x Y) (by intro _ _ _ ⟨h1, h2⟩; exact h1.trans h2.symm))

/-- This instance enables the ×ˢ notation for Cartesian product. -/
instance SetTheory.Set.inst_SProd : SProd Set Set Set where
  sprod := cartesian

example (X Y:Set) : X ×ˢ Y = SetTheory.Set.cartesian X Y := rfl

@[simp]
theorem SetTheory.Set.mem_cartesian (z:Object) (X Y:Set) :
    z ∈ X ×ˢ Y ↔ ∃ x:X, ∃ y:Y, z = (⟨x, y⟩:OrderedPair) := by
  simp only [SProd.sprod, union_axiom]; constructor
  . intro ⟨ S, hz, hS ⟩; rw [replacement_axiom] at hS; obtain ⟨ x, hx ⟩ := hS
    use x; rw [coe_eq_iff] at hx; rw [hx, mem_slice] at hz; exact hz
  rintro ⟨ x, y, rfl ⟩; use slice x Y; refine ⟨ by simp, ?_ ⟩
  rw [replacement_axiom]; use x

noncomputable abbrev SetTheory.Set.fst {X Y:Set} (z:X ×ˢ Y) : X :=
  ((mem_cartesian _ _ _).mp z.property).choose

noncomputable abbrev SetTheory.Set.snd {X Y:Set} (z:X ×ˢ Y) : Y :=
  (exists_comm.mp ((mem_cartesian _ _ _).mp z.property)).choose

theorem SetTheory.Set.pair_eq_fst_snd {X Y:Set} (z:X ×ˢ Y) :
    z.val = (⟨ fst z, snd z ⟩:OrderedPair) := by
  have := (mem_cartesian _ _ _).mp z.property
  obtain ⟨ y, hy: z.val = (⟨ fst z, y ⟩:OrderedPair)⟩ := this.choose_spec
  obtain ⟨ x, hx: z.val = (⟨ x, snd z ⟩:OrderedPair)⟩ := (exists_comm.mp this).choose_spec
  rw [hx, EmbeddingLike.apply_eq_iff_eq, OrderedPair.eq] at hy
  rw [hx, EmbeddingLike.apply_eq_iff_eq, OrderedPair.eq]
  exact And.intro hy.1 rfl

/-- This equips an {name}`OrderedPair` with proofs that $`x ∈ X` and $`y ∈ Y`. -/
def SetTheory.Set.mk_cartesian {X Y:Set} (x:X) (y:Y) : X ×ˢ Y :=
  ⟨(⟨ x, y ⟩:OrderedPair), by rw [mem_cartesian]; use x, y⟩

@[simp]
theorem SetTheory.Set.fst_of_mk_cartesian {X Y:Set} (x:X) (y:Y) :
    fst (mk_cartesian x y) = x := by
  let z := mk_cartesian x y; have := (mem_cartesian _ _ _).mp z.property
  obtain ⟨ y', hy: z.val = (⟨ fst z, y' ⟩:OrderedPair) ⟩ := this.choose_spec
  simp [z, mk_cartesian, Subtype.val_inj] at *; rw [←hy.1]

@[simp]
theorem SetTheory.Set.snd_of_mk_cartesian {X Y:Set} (x:X) (y:Y) :
    snd (mk_cartesian x y) = y := by
  let z := mk_cartesian x y; have := (mem_cartesian _ _ _).mp z.property
  obtain ⟨ x', hx: z.val = (⟨ x', snd z ⟩:OrderedPair) ⟩ := (exists_comm.mp this).choose_spec
  simp [z, mk_cartesian, Subtype.val_inj] at *; rw [←hx.2]

@[simp]
theorem SetTheory.Set.mk_cartesian_fst_snd_eq {X Y: Set} (z: X ×ˢ Y) :
    (mk_cartesian (fst z) (snd z)) = z := by
  rw [mk_cartesian, Subtype.mk.injEq, pair_eq_fst_snd]

/--
  {given -show}`x : X, y : Y`
  Connections with the Mathlib set product, which consists of Lean pairs like {lean}`(x, y)`
  equipped with a proof that {name}`x` is in the left set, and {name}`y` is in the right set.
  Lean pairs like {lean}`(x, y)` are similar to our {name}`OrderedPair`, but more general.
-/
noncomputable abbrev SetTheory.Set.prod_equiv_prod (X Y:Set) :
    ((X ×ˢ Y):_root_.Set Object) ≃ (X:_root_.Set Object) ×ˢ (Y:_root_.Set Object) where
  toFun z := ⟨(fst z, snd z), by simp⟩
  invFun z := mk_cartesian ⟨z.val.1, z.prop.1⟩ ⟨z.val.2, z.prop.2⟩
  left_inv _ := by simp
  right_inv _ := by simp

/-- Example 3.5.5 -/
example : ({1, 2}: Set) ×ˢ ({3, 4, 5}: Set) = ({
  ((mk_cartesian (1: Nat) (3: Nat)): Object),
  ((mk_cartesian (1: Nat) (4: Nat)): Object),
  ((mk_cartesian (1: Nat) (5: Nat)): Object),
  ((mk_cartesian (2: Nat) (3: Nat)): Object),
  ((mk_cartesian (2: Nat) (4: Nat)): Object),
  ((mk_cartesian (2: Nat) (5: Nat)): Object)
}: Set) := by ext; aesop

/-- Example 3.5.5 / Exercise 3.6.5. There is a bijection between {lean}`X ×ˢ Y` and {lean}`Y ×ˢ X`. -/
noncomputable abbrev SetTheory.Set.prod_commutator (X Y:Set) : X ×ˢ Y ≃ Y ×ˢ X where
  toFun z := ⟨mk_cartesian (snd z) (fst z), by rw [mk_cartesian, mem_cartesian]; use snd z, fst z⟩
  invFun z := mk_cartesian (snd z) (fst z)
  left_inv := by intro x; simp
  right_inv := by intro x; simp

/-- Example 3.5.5. A function of two variables can be thought of as a function of a pair. -/
noncomputable abbrev SetTheory.Set.curry_equiv {X Y Z:Set} : (X → Y → Z) ≃ (X ×ˢ Y → Z) where
  toFun f z := f (fst z) (snd z)
  invFun f x y := f (mk_cartesian x y)
  left_inv _ := by ext; simp
  right_inv _ := by simp

/-- Definition 3.5.6.  The indexing set {name}`I` plays the role of $`{ i : 1 ≤ i ≤ n }` in the text.
    See Exercise 3.5.10 below for some connections betweeen this concept and the preceding notion
    of Cartesian product and ordered pair.  -/
abbrev SetTheory.Set.tuple {I:Set} {X: I → Set} (x: ∀ i, X i) : Object :=
  ((fun i ↦ ⟨ x i, by rw [mem_iUnion]; use i; exact (x i).property ⟩):I → iUnion I X)

/-- Definition 3.5.6 -/
abbrev SetTheory.Set.iProd {I: Set} (X: I → Set) : Set :=
  ((iUnion I X)^I).specify (fun t ↦ ∃ x : ∀ i, X i, t = tuple x)

/-- Definition 3.5.6 -/
theorem SetTheory.Set.mem_iProd {I: Set} {X: I → Set} (t:Object) :
    t ∈ iProd X ↔ ∃ x: ∀ i, X i, t = tuple x := by
  simp only [iProd, specification_axiom'']; constructor
  . intro ⟨ ht, x, h ⟩; use x
  intro ⟨ x, hx ⟩
  have h : t ∈ (I.iUnion X)^I := by rw [hx, powerset_axiom]; simp
  use h, x

theorem SetTheory.Set.tuple_mem_iProd {I: Set} {X: I → Set} (x: ∀ i, X i) :
    tuple x ∈ iProd X := by rw [mem_iProd]; use x

@[simp]
theorem SetTheory.Set.tuple_inj {I:Set} {X: I → Set} (x y: ∀ i, X i) :
    tuple x = tuple y ↔ x = y := by
    rw [coe_of_fun_inj]
    constructor
    · intro h
      apply funext
      intro i
      have := congr_fun h i
      rw [← Subtype.val_inj] at this
      rw [← Subtype.val_inj]
      exact this
    intro h
    rw [h]

/-- Example 3.5.8. There is a bijection between {lean}`(X ×ˢ Y) ×ˢ Z` and {lean}`X ×ˢ (Y ×ˢ Z)`. -/
noncomputable abbrev SetTheory.Set.prod_associator (X Y Z:Set) : (X ×ˢ Y) ×ˢ Z ≃ X ×ˢ (Y ×ˢ Z) where
  toFun p := mk_cartesian (fst (fst p)) (mk_cartesian (snd (fst p)) (snd p))
  invFun p := mk_cartesian (mk_cartesian (fst p) (fst (snd p))) (snd (snd p))
  left_inv _ := by simp
  right_inv _ := by simp

/--
  Example 3.5.10. I suspect most of the equivalences will require classical reasoning and only be
  defined non-computably, but would be happy to learn of counterexamples.
-/
noncomputable abbrev SetTheory.Set.singleton_iProd_equiv (i:Object) (X:Set) :
    iProd (fun _:({i}:Set) ↦ X) ≃ X where
  toFun t := ((mem_iProd _).mp t.property).choose ⟨i, by simp⟩
  invFun x := ⟨tuple (fun j : ({i}:Set) ↦ x), by apply tuple_mem_iProd⟩
  left_inv := by
    intro t
    ext
    have h := (mem_iProd _).mp t.property
    rw [h.choose_spec, tuple_inj]
    ext j
    have hj : j = ⟨i, by simp⟩ := by
      apply Subtype.ext
      exact (mem_singleton j.val i).mp j.property
    rw [hj]
  right_inv := by
    intro x
    simp only
    have h := (mem_iProd _).mp (tuple_mem_iProd (fun j : ({i}:Set) ↦ x))
    have hspec := h.choose_spec
    rw [tuple_inj] at hspec
    rw [← hspec]

/-- Example 3.5.10 -/
abbrev SetTheory.Set.empty_iProd_equiv (X: (∅:Set) → Set) : iProd X ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨tuple (fun i : (∅:Set) ↦ False.elim (not_mem_empty i.val i.property)), by apply tuple_mem_iProd⟩
  left_inv := by
    intro t
    ext
    have h := (mem_iProd _).mp t.property
    simp only
    rw [h.choose_spec, tuple_inj]
    ext i
    exfalso
    exact not_mem_empty i.val i.property
  right_inv := by
    intro x
    cases x
    rfl

/-- Example 3.5.10 -/
noncomputable abbrev SetTheory.Set.iProd_of_const_equiv (I:Set) (X: Set) :
    iProd (fun _ :I ↦ X) ≃ (I → X) where
  toFun t := ((mem_iProd t.val).mp t.property).choose
  invFun x := ⟨tuple (fun i : I ↦ x i), by apply tuple_mem_iProd⟩
  left_inv := by
    intro t
    ext
    have h := (mem_iProd t.val).mp t.property
    rw [h.choose_spec, tuple_inj]
  right_inv := by
    intro x
    simp only
    apply funext
    intro i
    have h := (mem_iProd _).mp (tuple_mem_iProd (fun i : I ↦ x i))
    have hspec := h.choose_spec
    rw [tuple_inj] at hspec
    rw [← hspec]

/-- Helper for iProd_equiv_prod -/
noncomputable def SetTheory.Set.iProd_equiv_prod_aux (X: ({0,1}:Set) → Set)
    (x0 : X ⟨0, by simp⟩) (x1 : X ⟨1, by simp⟩)
    (i : ({0,1}:Set)) : X i := by
  -- 不需要 classical，因为 Nat 有 DecidableEq 实例
  if hi : i.val = 0 then
    have : i = ⟨0, by simp⟩ := Subtype.ext hi
    subst this; exact x0
  else
    have hi1 : i.val = 1 := by
      have hp := i.property
      rw [mem_insert, mem_singleton] at hp
      rcases hp with hp | hp
      · contradiction
      · exact hp
    have : i = ⟨1, by simp⟩ := Subtype.ext hi1
    subst this; exact x1

/-- Example 3.5.10 -/
noncomputable abbrev SetTheory.Set.iProd_equiv_prod (X: ({0,1}:Set) → Set) :
    iProd X ≃ (X ⟨ 0, by simp ⟩) ×ˢ (X ⟨ 1, by simp ⟩) where
  toFun t :=  by have h := ((mem_iProd t.val).mp t.property).choose; apply mk_cartesian (h ⟨0, by simp⟩) (h ⟨1, by simp⟩)
  invFun x := ⟨tuple (iProd_equiv_prod_aux X (fst x) (snd x)), by apply tuple_mem_iProd⟩
  left_inv := by
    intro t
    rw [Subtype.ext_iff]
    have h := (mem_iProd t.val).mp t.property
    have hspec := h.choose_spec
    rw [h.choose_spec, tuple_inj]
    funext i
    have hi := (mem_pair _ _ _).mp i.property
    rcases hi with hi | hi
    · have : i = ⟨0, (mem_pair 0 0 1).mpr (Or.inl rfl)⟩ := Subtype.ext hi
      subst this; unfold iProd_equiv_prod_aux
      rw [dif_pos rfl, fst_of_mk_cartesian]
    have : i = ⟨1, by simp⟩ := Subtype.ext hi
    subst this; unfold iProd_equiv_prod_aux;
    rw [dif_neg (by intro h; rw [h, ofNat_inj'] at hi; apply Nat.succ_ne_zero 0; apply Eq.symm; exact hi), snd_of_mk_cartesian]
  right_inv := by
    intro x
    dsimp only
    have h := (mem_iProd _).mp (tuple_mem_iProd (iProd_equiv_prod_aux X (fst x) (snd x)))
    have hspec := h.choose_spec
    rw [tuple_inj] at hspec
    simp only [← hspec, iProd_equiv_prod_aux]
    split_ifs with h1 h2
    · have : (1:Object) ≠ 0 := by simp
      exact absurd h2 this
    · exact mk_cartesian_fst_snd_eq x
    · exact absurd (by trivial : True) h1
    · exact absurd (by trivial : True) h1

/-- Example 3.5.10 -/
noncomputable def SetTheory.Set.iProd_equiv_prod_triple_aux (X: ({0,1,2}:Set) → Set)
    (x0 : X ⟨0, by simp⟩) (x1 : X ⟨1, by simp⟩) (x2 : X ⟨2, by simp⟩)
    (i : ({0,1,2}:Set)) : X i := by
  if hi0 : i.val = 0 then
    have : i = ⟨0, by simp⟩ := Subtype.ext hi0
    subst this; exact x0
  else if hi1 : i.val = 1 then
    have : i = ⟨1, by simp⟩ := Subtype.ext hi1
    subst this; exact x1
  else
    have hi2 : i.val = 2 := by
      have h := i.property
      rw [mem_insert, mem_insert, mem_singleton] at h
      rcases h with h | h | h
      all_goals simp_all
    have : i = ⟨2, by simp⟩ := Subtype.ext hi2
    subst this; exact x2

def SetTheory.Set.index0 : ({0,1,2}:Set) := ⟨0, by simp⟩
def SetTheory.Set.index1 : ({0,1,2}:Set) := ⟨1, by simp⟩
def SetTheory.Set.index2 : ({0,1,2}:Set) := ⟨2, by simp⟩

@[simp]
theorem SetTheory.Set.iProd_equiv_prod_triple_aux_index0 (X: ({0,1,2}:Set) → Set)
    (x0 : X index0) (x1 : X index1) (x2 : X index2) :
    iProd_equiv_prod_triple_aux X x0 x1 x2 index0 = x0 := by
  simp only [iProd_equiv_prod_triple_aux, index0]
  simp

@[simp]
theorem SetTheory.Set.iProd_equiv_prod_triple_aux_index1 (X: ({0,1,2}:Set) → Set)
    (x0 : X index0) (x1 : X index1) (x2 : X index2) :
    iProd_equiv_prod_triple_aux X x0 x1 x2 index1 = x1 := by
  simp only [iProd_equiv_prod_triple_aux, index1]
  simp

@[simp]
theorem SetTheory.Set.iProd_equiv_prod_triple_aux_index2 (X: ({0,1,2}:Set) → Set)
    (x0 : X index0) (x1 : X index1) (x2 : X index2) :
    iProd_equiv_prod_triple_aux X x0 x1 x2 index2 = x2 := by
  simp only [iProd_equiv_prod_triple_aux, index2]
  simp

/-- Example 3.5.10 -/
noncomputable abbrev SetTheory.Set.iProd_equiv_prod_triple (X: ({0,1,2}:Set) → Set) :
    iProd X ≃ (X index0) ×ˢ (X index1) ×ˢ (X index2) where
  toFun t := mk_cartesian (((mem_iProd t.val).mp t.property).choose index0)
      (mk_cartesian (((mem_iProd t.val).mp t.property).choose index1)
        (((mem_iProd t.val).mp t.property).choose index2))
  invFun x := ⟨tuple (iProd_equiv_prod_triple_aux X (fst x) (fst (snd x)) (snd (snd x))), by apply tuple_mem_iProd⟩
  left_inv := by
    intro t
    ext
    dsimp only
    set f := ((mem_iProd t.val).mp t.property).choose
    have hspec : t.val = tuple f := ((mem_iProd t.val).mp t.property).choose_spec
    rw [hspec, tuple_inj]
    ext i
    -- Enter inside the coercion and simplify
    conv =>
      lhs
      arg 1  -- enter the argument of the coercion
      simp only [fst_of_mk_cartesian, snd_of_mk_cartesian]
    by_cases hi0 : i.val = 0
    · have hi : i = index0 := Subtype.ext hi0
      rw [hi, iProd_equiv_prod_triple_aux_index0]
      show (fst (mk_cartesian (f index0) (mk_cartesian (f index1) (f index2)))).val = (f index0).val
      rw [fst_of_mk_cartesian]
    · by_cases hi1 : i.val = 1
      · have hi : i = index1 := Subtype.ext hi1
        rw [hi, iProd_equiv_prod_triple_aux_index1]
        show (fst (snd (mk_cartesian (f index0) (mk_cartesian (f index1) (f index2))))).val = (f index1).val
        rw [snd_of_mk_cartesian, fst_of_mk_cartesian]
      · have hi2 : i.val = 2 := by
          have hp := i.property
          rw [mem_insert, mem_insert, mem_singleton] at hp
          rcases hp with hp | hp | hp
          all_goals simp_all
        have hi : i = index2 := Subtype.ext hi2
        rw [hi, iProd_equiv_prod_triple_aux_index2]
        show (snd (snd (mk_cartesian (f index0) (mk_cartesian (f index1) (f index2))))).val = (f index2).val
        rw [snd_of_mk_cartesian, snd_of_mk_cartesian]
  right_inv := by
    intro x
    simp only
    have h := (mem_iProd _).mp (tuple_mem_iProd (iProd_equiv_prod_triple_aux X (fst x) (fst (snd x)) (snd (snd x))))
    have hspec := h.choose_spec
    rw [tuple_inj] at hspec
    rw [← hspec]
    simp only [iProd_equiv_prod_triple_aux_index0, iProd_equiv_prod_triple_aux_index1, iProd_equiv_prod_triple_aux_index2]
    -- Need to show mk_cartesian (fst x) (mk_cartesian (fst (snd x)) (snd (snd x))) = x
    calc mk_cartesian (fst x) (mk_cartesian (fst (snd x)) (snd (snd x)))
        = mk_cartesian (fst x) (snd x) := by
            apply congr_arg
            exact mk_cartesian_fst_snd_eq (snd x)
        _ = x := mk_cartesian_fst_snd_eq x

/-- Connections with Mathlib's {name}`Set.pi` -/
noncomputable abbrev SetTheory.Set.iProd_equiv_pi (I:Set) (X: I → Set) :
    iProd X ≃ Set.pi .univ (fun i:I ↦ ((X i):_root_.Set Object)) where
  toFun t := ⟨fun i ↦ ((mem_iProd _).mp t.property).choose i, by simp⟩
  invFun x :=
    ⟨tuple fun i ↦ ⟨x.val i, by have := x.property i; simpa⟩, by apply tuple_mem_iProd⟩
  left_inv t := by ext; rw [((mem_iProd _).mp t.property).choose_spec, tuple_inj]
  right_inv x := by
    ext; dsimp
    generalize_proofs _ h
    rw [←(tuple_inj _ _).mp h.choose_spec]


/-
remark: there are also additional relations between these equivalences, but this begins to drift
into the field of higher order category theory, which we will not pursue here.
-/

/--
  Here we set up some an analogue of Mathlib {lean}`Fin n` types within the Chapter 3 Set Theory,
  with rudimentary API.
-/
abbrev SetTheory.Set.Fin (n:ℕ) : Set := nat.specify (fun m ↦ (m:ℕ) < n)

theorem SetTheory.Set.mem_Fin (n:ℕ) (x:Object) : x ∈ Fin n ↔ ∃ m, m < n ∧ x = m := by
  rw [specification_axiom'']; constructor
  . intro ⟨ h1, h2 ⟩; use ↑(⟨ x, h1 ⟩:nat); simp [h2]
  intro ⟨ m, hm, h ⟩
  use (by rw [h, ←Object.ofnat_eq]; exact (m:nat).property)
  grind [Object.ofnat_eq''']

abbrev SetTheory.Set.Fin_mk (n m:ℕ) (h: m < n): Fin n := ⟨ m, by rw [mem_Fin]; use m ⟩

theorem SetTheory.Set.mem_Fin' {n:ℕ} (x:Fin n) : ∃ m, ∃ h : m < n, x = Fin_mk n m h := by
  choose m hm this using (mem_Fin _ _).mp x.property; use m, hm
  simp [Fin_mk, ←Subtype.val_inj, this]

@[coe]
noncomputable abbrev SetTheory.Set.Fin.toNat {n:ℕ} (i: Fin n) : ℕ := (mem_Fin' i).choose

noncomputable instance SetTheory.Set.Fin.inst_coeNat {n:ℕ} : CoeOut (Fin n) ℕ where
  coe := toNat

theorem SetTheory.Set.Fin.toNat_spec {n:ℕ} (i: Fin n) :
    ∃ h : i < n, i = Fin_mk n i h := (mem_Fin' i).choose_spec

theorem SetTheory.Set.Fin.toNat_lt {n:ℕ} (i: Fin n) : i < n := (toNat_spec i).choose

@[simp]
theorem SetTheory.Set.Fin.coe_toNat {n:ℕ} (i: Fin n) : ((i:ℕ):Object) = (i:Object) := by
  set j := (i:ℕ); obtain ⟨ h, h':i = Fin_mk n j h ⟩ := toNat_spec i; rw [h']

@[simp low]
lemma SetTheory.Set.Fin.coe_inj {n:ℕ} {i j: Fin n} : i = j ↔ (i:ℕ) = (j:ℕ) := by
  constructor
  · simp_all
  obtain ⟨_, hi⟩ := toNat_spec i
  obtain ⟨_, hj⟩ := toNat_spec j
  grind

@[simp]
theorem SetTheory.Set.Fin.coe_eq_iff {n:ℕ} (i: Fin n) {j:ℕ} : (i:Object) = (j:Object) ↔ i = j := by
  constructor
  · intro h
    rw [Subtype.coe_eq_iff] at h
    obtain ⟨_, rfl⟩ := h
    simp [←Object.natCast_inj]
  aesop

@[simp]
theorem SetTheory.Set.Fin.coe_eq_iff' {n m:ℕ} (i: Fin n) (hi : ↑i ∈ Fin m) : ((⟨i, hi⟩ : Fin m):ℕ) = (i:ℕ) := by
  obtain ⟨val, property⟩ := i
  simp only [toNat, Subtype.mk.injEq, exists_prop]
  generalize_proofs h1 h2
  suffices : (h1.choose: Object) = h2.choose
  · aesop
  have := h1.choose_spec
  have := h2.choose_spec
  grind

@[simp]
theorem SetTheory.Set.Fin.toNat_mk {n:ℕ} (m:ℕ) (h: m < n) : (Fin_mk n m h : ℕ) = m := by
  have := coe_toNat (Fin_mk n m h)
  rwa [Object.natCast_inj] at this

abbrev SetTheory.Set.Fin_embed (n N:ℕ) (h: n ≤ N) (i: Fin n) : Fin N := ⟨ i.val, by
  have := i.property; rw [mem_Fin] at *; grind
⟩

/-- Connections with Mathlib's {lean}`Fin n` -/
noncomputable abbrev SetTheory.Set.Fin.Fin_equiv_Fin (n:ℕ) : Fin n ≃ _root_.Fin n where
  toFun m := _root_.Fin.mk m (toNat_lt m)
  invFun m := Fin_mk n m.val m.isLt
  left_inv m := (toNat_spec m).2.symm
  right_inv m := by simp

/-- Lemma 3.5.11 (finite choice) -/
theorem SetTheory.Set.finite_choice {n:ℕ} {X: Fin n → Set} (h: ∀ i, X i ≠ ∅) : iProd X ≠ ∅ := by
  -- This proof broadly follows the one in the text
  -- (although it is more convenient to induct from 0 rather than 1)
  induction' n with n hn
  . have : Fin 0 = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      grind [specification_axiom'']
    have empty (i:Fin 0) : X i := False.elim (by rw [this] at i; exact not_mem_empty i i.property)
    apply nonempty_of_inhabited (x := tuple empty); rw [mem_iProd]; use empty
  set X' : Fin n → Set := fun i ↦ X (Fin_embed n (n+1) (by linarith) i)
  have hX' (i: Fin n) : X' i ≠ ∅ := h _
  choose x'_obj hx' using nonempty_def (hn hX')
  rw [mem_iProd] at hx'; obtain ⟨ x', rfl ⟩ := hx'
  set last : Fin (n+1) := Fin_mk (n+1) n (by linarith)
  choose a ha using nonempty_def (h last)
  have x : ∀ i, X i := fun i =>
    if h : i = n then
      have : i = last := by ext; simpa [←Fin.coe_toNat, last]
      ⟨a, by grind⟩
    else
      have : i < n := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Fin.toNat_lt i)) h
      let i' := Fin_mk n i this
      have : X i = X' i' := by simp [X', i', Fin_embed]
      ⟨x' i', by grind⟩
  exact nonempty_of_inhabited (tuple_mem_iProd x)

/-- Exercise 3.5.1, second part (requires axiom of regularity) -/
def OrderedPair.toObject' : OrderedPair ↪ Object where
  toFun p := ({ p.fst, (({p.fst, p.snd}:Set):Object) }:Set)
  inj' := by
    intro x y h
    rw [OrderedPair.ext_iff]
    -- 分析 pair 相等的两种情况
    have hxy := SetTheory.Set.coe_eq h
    rcases SetTheory.Set.pair_eq_pair hxy with hxy | hxy
    · -- 情况1：x.fst = y.fst 且 {x.fst, x.snd} = {y.fst, y.snd}
      have hfst : x.fst = y.fst := hxy.1
      apply And.intro hfst
      have hpair := SetTheory.Set.coe_eq hxy.2
      rcases SetTheory.Set.pair_eq_pair hpair with hs | hs
      · -- 子情况A：x.fst = y.fst 且 x.snd = y.snd
        exact hs.2
      -- 子情况B：x.fst = y.snd 且 x.snd = y.fst
      -- 从 hfst : x.fst = y.fst 和 hs.1 : x.fst = y.snd，得 y.fst = y.snd
      -- 从 hs.2 : x.snd = y.fst 和 y.fst = y.snd，得 x.snd = y.snd
      exact hs.2.trans (hfst.symm.trans hs.1)
    · -- 情况2：x.fst = {y.fst, y.snd} 且 {x.fst, x.snd} = y.fst
      -- 这个情况违反 not_mem_mem
      -- 定义 X := {y.fst, y.snd}，Y := {x.fst, x.snd}
      -- 则 x.fst = X，y.fst = Y
      -- y.fst ∈ X（因为 y.fst ∈ {y.fst, y.snd} = X），即 Y ∈ X
      -- x.fst ∈ Y（因为 x.fst ∈ {x.fst, x.snd} = Y），即 X ∈ Y
      -- 这违反了 not_mem_mem X Y
      set X : Set := {y.fst, y.snd}
      set Y : Set := {x.fst, x.snd}
      have hxX : (x.fst:Object) = X := hxy.1
      have hyY : (y.fst:Object) = Y := hxy.2.symm
      have h1 : (y.fst:Object) ∈ X := by
        rw [mem_pair]
        left; rfl
      have h2 : (x.fst:Object) ∈ Y := by
        rw [mem_pair]
        left; rfl
      have h3 : (Y:Object) ∈ X := by
        rw [hyY] at h1; exact h1
      have h4 : (X:Object) ∈ Y := by
        rw [hxX] at h2; exact h2
      have hcontr := not_mem_mem X Y
      rw [← not_and_or] at hcontr
      exact False.elim (hcontr ⟨h4, h3⟩)

/-- An alternate definition of a tuple, used in Exercise 3.5.2 -/
structure SetTheory.Set.Tuple (n:ℕ) where
  X: Set
  x: Fin n → X
  surj: Function.Surjective x

/--
  Custom extensionality lemma for Exercise 3.5.2.
  Placing {attr}`@[ext]` on the structure would generate a lemma requiring proof of {lit}`t.x = t'.x`,
  but these functions have different types when {lean}`t.X ≠ t'.X`. This lemma handles that part.
-/
@[ext]
lemma SetTheory.Set.Tuple.ext {n:ℕ} {t t':Tuple n}
    (hX : t.X = t'.X)
    (hx : ∀ n : Fin n, ((t.x n):Object) = ((t'.x n):Object)) :
    t = t' := by
  have ⟨_, _, _⟩ := t; have ⟨_, _, _⟩ := t'; subst hX; congr; ext; grind

/-- Exercise 3.5.2 -/
theorem SetTheory.Set.Tuple.eq {n:ℕ} (t t':Tuple n) :
    t = t' ↔ ∀ n : Fin n, ((t.x n):Object) = ((t'.x n):Object) := by
  constructor
  · intro h n
    rw [h]
  intro h
  apply Tuple.ext _ h
  ext a
  constructor
  · intro ha
    obtain ⟨i, hi⟩ := t.surj ⟨a, ha⟩
    have hxi : (t.x i : Object) = a := congrArg Subtype.val hi
    rw [← hxi, h i]
    exact (t'.x i).property
  · intro ha
    obtain ⟨i, hi⟩ := t'.surj ⟨a, ha⟩
    have hxi : (t'.x i : Object) = a := congrArg Subtype.val hi
    rw [← hxi, ← h i]
    exact (t.x i).property

noncomputable def SetTheory.Set.iProd_equiv_tuples_aux {n:ℕ} {X: Fin n → Set} (f: ∀ i, X i) : Tuple n where
  X := (iUnion (Fin n) X).specify (fun y ↦ ∃ i : Fin n, (f i : Object) = y.val)
  x i := ⟨(f i : Object), by
    rw [specification_axiom'']
    exact ⟨by rw [mem_iUnion]; exact ⟨i, (f i).property⟩, i, rfl⟩⟩
  surj := by
    intro y
    obtain ⟨_, i, hi⟩ := (specification_axiom'' (fun y ↦ ∃ i : Fin n, (f i : Object) = y.val) y.val).mp y.property
    use i; exact Subtype.ext hi

@[simp]
theorem SetTheory.Set.iProd_equiv_tuples_aux_x_val {n:ℕ} {X: Fin n → Set} (f: ∀ i, X i) (i : Fin n) :
    ((iProd_equiv_tuples_aux f).x i : Object) = (f i : Object) := rfl

noncomputable abbrev SetTheory.Set.iProd_equiv_tuples (n:ℕ) (X: Fin n → Set) :
    iProd X ≃ { t:Tuple n // ∀ i, (t.x i:Object) ∈ X i } where
  toFun t := by
    have h := (mem_iProd t.val).mp t.property
    exact ⟨iProd_equiv_tuples_aux h.choose, fun i ↦ (h.choose i).property⟩
  invFun t := by
    have hx (i : Fin n) : X i := ⟨(t.val.x i : Object), t.property i⟩
    exact ⟨tuple (fun i ↦ hx i), tuple_mem_iProd (fun i ↦ hx i)⟩
  left_inv := by
    intro t
    ext
    have h := (mem_iProd t.val).mp t.property
    have hf : t.val = tuple h.choose := h.choose_spec
    show (tuple fun i ↦ ⟨↑((iProd_equiv_tuples_aux h.choose).x i), _⟩) = ↑t
    have key : (fun i ↦ (⟨↑((iProd_equiv_tuples_aux h.choose).x i),
        (h.choose i).property⟩ : X i)) = h.choose := by ext i; rfl
    rw [key, ← hf]
  right_inv := by
    intro t
    apply Subtype.ext
    apply (Tuple.eq _ _).mpr
    intro i
    simp only [iProd_equiv_tuples_aux_x_val]
    generalize_proofs h1 h2
    have key : h2.choose = fun i ↦ (⟨(t.val.x i : Object), h1 i⟩ : X i) :=
      (tuple_inj _ _).mp h2.choose_spec.symm
    simp [key]

/--
  Exercise 3.5.3. The spirit here is to avoid direct rewrites (which make all of these claims
  trivial), and instead use {name}`OrderedPair.eq` or {name}`SetTheory.Set.tuple_inj`
-/
theorem OrderedPair.refl (p: OrderedPair) : p = p := by sorry

theorem OrderedPair.symm (p q: OrderedPair) : p = q ↔ q = p := by sorry

theorem OrderedPair.trans {p q r: OrderedPair} (hpq: p=q) (hqr: q=r) : p=r := by sorry

theorem SetTheory.Set.tuple_refl {I:Set} {X: I → Set} (a: ∀ i, X i) :
    tuple a = tuple a := by sorry

theorem SetTheory.Set.tuple_symm {I:Set} {X: I → Set} (a b: ∀ i, X i) :
    tuple a = tuple b ↔ tuple b = tuple a := by sorry

theorem SetTheory.Set.tuple_trans {I:Set} {X: I → Set} {a b c: ∀ i, X i}
  (hab: tuple a = tuple b) (hbc : tuple b = tuple c) :
    tuple a = tuple c := by sorry

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.prod_union (A B C:Set) : A ×ˢ (B ∪ C) = (A ×ˢ B) ∪ (A ×ˢ C) := by sorry

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.prod_inter (A B C:Set) : A ×ˢ (B ∩ C) = (A ×ˢ B) ∩ (A ×ˢ C) := by sorry

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.prod_diff (A B C:Set) : A ×ˢ (B \ C) = (A ×ˢ B) \ (A ×ˢ C) := by sorry

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.union_prod (A B C:Set) : (A ∪ B) ×ˢ C = (A ×ˢ C) ∪ (B ×ˢ C) := by sorry

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.inter_prod (A B C:Set) : (A ∩ B) ×ˢ C = (A ×ˢ C) ∩ (B ×ˢ C) := by sorry

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.diff_prod (A B C:Set) : (A \ B) ×ˢ C = (A ×ˢ C) \ (B ×ˢ C) := by sorry

/-- Exercise 3.5.5 -/
theorem SetTheory.Set.inter_of_prod (A B C D:Set) :
    (A ×ˢ B) ∩ (C ×ˢ D) = (A ∩ C) ×ˢ (B ∩ D) := by sorry

/- Exercise 3.5.5 -/
def SetTheory.Set.union_of_prod :
  Decidable (∀ (A B C D:Set), (A ×ˢ B) ∪ (C ×ˢ D) = (A ∪ C) ×ˢ (B ∪ D)) := by
  -- the first line of this construction should be `apply isTrue` or `apply isFalse`.
  sorry

/- Exercise 3.5.5 -/
def SetTheory.Set.diff_of_prod :
  Decidable (∀ (A B C D:Set), (A ×ˢ B) \ (C ×ˢ D) = (A \ C) ×ˢ (B \ D)) := by
  -- the first line of this construction should be `apply isTrue` or `apply isFalse`.
  sorry

/--
  Exercise 3.5.6.
-/
theorem SetTheory.Set.prod_subset_prod {A B C D:Set}
  (hA: A ≠ ∅) (hB: B ≠ ∅) (hC: C ≠ ∅) (hD: D ≠ ∅) :
    A ×ˢ B ⊆ C ×ˢ D ↔ A ⊆ C ∧ B ⊆ D := by sorry

def SetTheory.Set.prod_subset_prod' :
  Decidable (∀ (A B C D:Set), A ×ˢ B ⊆ C ×ˢ D ↔ A ⊆ C ∧ B ⊆ D) := by
  -- the first line of this construction should be `apply isTrue` or `apply isFalse`.
  sorry

/-- Exercise 3.5.7 -/
theorem SetTheory.Set.direct_sum {X Y Z:Set} (f: Z → X) (g: Z → Y) :
    ∃! h: Z → X ×ˢ Y, fst ∘ h = f ∧ snd ∘ h = g := by sorry

/-- Exercise 3.5.8 -/
@[simp]
theorem SetTheory.Set.iProd_empty_iff {n:ℕ} {X: Fin n → Set} :
    iProd X = ∅ ↔ ∃ i, X i = ∅ := by sorry

/-- Exercise 3.5.9-/
theorem SetTheory.Set.iUnion_inter_iUnion {I J: Set} (A: I → Set) (B: J → Set) :
    (iUnion I A) ∩ (iUnion J B) = iUnion (I ×ˢ J) (fun p ↦ (A (fst p)) ∩ (B (snd p))) := by sorry

abbrev SetTheory.Set.graph {X Y:Set} (f: X → Y) : Set :=
  (X ×ˢ Y).specify (fun p ↦ (f (fst p) = snd p))

/-- Exercise 3.5.10 -/
theorem SetTheory.Set.graph_inj {X Y:Set} (f f': X → Y) :
    graph f = graph f' ↔ f = f' := by sorry

theorem SetTheory.Set.is_graph {X Y G:Set} (hG: G ⊆ X ×ˢ Y)
  (hvert: ∀ x:X, ∃! y:Y, ((⟨x,y⟩:OrderedPair):Object) ∈ G) :
    ∃! f: X → Y, G = graph f := by sorry

/--
  Exercise 3.5.11. This trivially follows from {name}`SetTheory.Set.powerset_axiom`, but the
  exercise is to derive it from {name}`SetTheory.Set.exists_powerset` instead.
-/
theorem SetTheory.Set.powerset_axiom' (X Y:Set) :
    ∃! S:Set, ∀(F:Object), F ∈ S ↔ ∃ f: Y → X, f = F := sorry

/-- Exercise 3.5.12, with errata from web site incorporated -/
theorem SetTheory.Set.recursion (X: Set) (f: nat → X → X) (c:X) :
    ∃! a: nat → X, a 0 = c ∧ ∀ n, a (n + 1:ℕ) = f n (a n) := by sorry

/-- Exercise 3.5.13 -/
theorem SetTheory.Set.nat_unique (nat':Set) (zero:nat') (succ:nat' → nat')
  (succ_ne: ∀ n:nat', succ n ≠ zero) (succ_of_ne: ∀ n m:nat', n ≠ m → succ n ≠ succ m)
  (ind: ∀ P: nat' → Prop, P zero → (∀ n, P n → P (succ n)) → ∀ n, P n) :
    ∃! f : nat → nat', Function.Bijective f ∧ f 0 = zero
    ∧ ∀ (n:nat) (n':nat'), f n = n' ↔ f (n+1:ℕ) = succ n' := by
  have nat_coe_eq {m:nat} {n} : (m:ℕ) = n → m = n := by aesop
  have nat_coe_eq_zero {m:nat} : (m:ℕ) = 0 → m = 0 := nat_coe_eq
  obtain ⟨f, hf⟩ := recursion nat' sorry sorry
  apply existsUnique_of_exists_of_unique
  · use f
    constructor
    · constructor
      · intro x1 x2 heq
        induction' hx1: (x1:ℕ) with i ih generalizing x1 x2
        · sorry
        sorry
      sorry
    sorry
  sorry


end Chapter3
