import Mathlib.Tactic
import Analysis.Section_3_5

/-!
# Analysis I, Section 3.6: Cardinality of sets

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.


Main constructions and results of this section:

- Cardinality of a set
- Finite and infinite sets
- Connections with Mathlib equivalents

After this section, these notions will be deprecated in favor of their Mathlib equivalents.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter3

export SetTheory (Set Object nat)

variable [SetTheory]

/-- Definition 3.6.1 (Equal cardinality) -/
abbrev SetTheory.Set.EqualCard (X Y:Set) : Prop := ∃ f : X → Y, Function.Bijective f

/-- Example 3.6.2 -/
theorem SetTheory.Set.Example_3_6_2 : EqualCard {0,1,2} {3,4,5} := by
  use open Classical in fun x ↦
    ⟨if x.val = 0 then 3 else if x.val = 1 then 4 else 5, by aesop⟩
  constructor
  · intro; aesop
  intro y
  have : y = (3: Object) ∨ y = (4: Object) ∨ y = (5: Object) := by
    have := y.property
    aesop
  rcases this with (_ | _ | _)
  · use ⟨0, by simp⟩; aesop
  · use ⟨1, by simp⟩; aesop
  · use ⟨2, by simp⟩; aesop

/-- Example 3.6.3 -/
theorem SetTheory.Set.Example_3_6_3 : EqualCard nat (nat.specify (fun x ↦ Even (x:ℕ))) := by
  -- The bijection is n ↦ 2n from nat to the even naturals.
  let f : nat.toSubtype → (nat.specify (fun x ↦ Even (x:ℕ))).toSubtype := fun x =>
    let n : ℕ := nat_equiv.symm x
    let two_n_nat : nat.toSubtype := nat_equiv (2 * n)
    ⟨two_n_nat.val, by
      rw [specification_axiom'']
      refine ⟨two_n_nat.property, ?_⟩
      show Even (nat_equiv.symm ⟨two_n_nat.val, two_n_nat.property⟩)
      simp [two_n_nat]⟩
  use f
  constructor
  · -- injective
    intro x1 x2 h
    have hval : (f x1).val = (f x2).val := congrArg Subtype.val h
    simp only [f] at hval
    have hval2 : nat_equiv (2 * nat_equiv.symm x1) = nat_equiv (2 * nat_equiv.symm x2) :=
      Subtype.val_injective hval
    have hval3 : 2 * nat_equiv.symm x1 = 2 * nat_equiv.symm x2 := nat_equiv.injective hval2
    have hval4 : nat_equiv.symm x1 = nat_equiv.symm x2 := by omega
    exact nat_equiv.symm.injective hval4
  · -- surjective
    intro y
    have hy_spec := y.property
    rw [specification_axiom''] at hy_spec
    obtain ⟨hy_mem, hy_even⟩ := hy_spec
    obtain ⟨k, hk⟩ := hy_even
    use nat_equiv k
    apply Subtype.ext
    simp only [f, Equiv.symm_apply_apply]
    have : nat_equiv (k + k) = ⟨y.val, hy_mem⟩ := by
      apply nat_equiv.symm.injective; simp [hk]
    rw [show 2 * k = k + k from by ring]
    exact congrArg Subtype.val this

@[refl]
theorem SetTheory.Set.EqualCard.refl (X:Set) : EqualCard X X := by
  use fun x : X => x
  constructor
  · intro a b h; exact h
  intro x; use x

@[symm]
theorem SetTheory.Set.EqualCard.symm {X Y:Set} (h: EqualCard X Y) : EqualCard Y X := by
  obtain ⟨f, ⟨h1, h2⟩⟩ := h
  let g := fun (y : Y) => (h2 y).choose
  use g
  constructor
  · intro y1 y2 h
    have h3 := (h2 y1).choose_spec
    have h4 := (h2 y2).choose_spec
    unfold g at h
    rw [h] at h3
    rw [h3] at h4
    exact h4
  intro x; use f x
  unfold g
  apply h1
  exact (h2 (f x)).choose_spec

@[trans]
theorem SetTheory.Set.EqualCard.trans {X Y Z:Set} (h1: EqualCard X Y) (h2: EqualCard Y Z) : EqualCard X Z := by
  obtain ⟨f, ⟨hf1, hf2⟩⟩ := h1
  obtain ⟨g, ⟨hg1, hg2⟩⟩ := h2
  let h := fun (x : X) => g (f x)
  use h
  constructor
  · intro x1 x2 h'; apply hf1; apply hg1; exact h'
  intro z
  obtain ⟨y', hy'⟩ := hg2 z
  obtain ⟨x', hx'⟩ := hf2 y'
  use x'; unfold h
  rw [hx', hy']

/-- Proposition 3.6.4 / Exercise 3.6.1 -/
instance SetTheory.Set.EqualCard.inst_setoid : Setoid SetTheory.Set := ⟨ EqualCard, {refl, symm, trans} ⟩

/-- Definition 3.6.5 -/
abbrev SetTheory.Set.has_card (X:Set) (n:ℕ) : Prop := X ≈ Fin n

theorem SetTheory.Set.has_card_iff (X:Set) (n:ℕ) :
    X.has_card n ↔ ∃ f: X → Fin n, Function.Bijective f := by
  simp [has_card, HasEquiv.Equiv, instHasEquivOfSetoid, Setoid.r, EqualCard]

/-- Remark 3.6.6 -/
theorem SetTheory.Set.Remark_3_6_6 (n:ℕ) :
    (nat.specify (fun x ↦ 1 ≤ (x:ℕ) ∧ (x:ℕ) ≤ n)).has_card n := by
  simp [SetTheory.Set.has_card_iff]
  use fun x => Fin_mk _ (((⟨x.val, by apply ((specification_axiom'' _ _).mp x.property).choose⟩:nat) : ℕ) - 1) (by
    have hx := x.property; rw [specification_axiom''] at hx; obtain ⟨hx1, hx2⟩ := hx; omega)
  constructor
  · intro x1 x2 h;
    simp at h
    have ⟨h1, ⟨h2, h3⟩⟩ := (specification_axiom'' _ x1).mp (x1.property)
    have ⟨h1', ⟨h2', h3'⟩⟩ := (specification_axiom'' _ x2).mp (x2.property)
    rw [Nat.sub_eq_iff_eq_add h2, Nat.sub_add_cancel h2'] at h
    apply nat_equiv.symm.injective at h
    rw [← Subtype.val_inj, Subtype.val_inj (a := x1)] at h
    exact h
  · intro y
    let m := (y : ℕ) + 1
    have hm1 : 1 ≤ m := by omega
    have hm2 : m ≤ n := by have := Fin.toNat_lt y; omega
    have hm : (nat_equiv m : Object) ∈ nat.specify (fun x ↦ 1 ≤ nat_equiv.symm x ∧ nat_equiv.symm x ≤ n) := by
      rw [specification_axiom'']
      exact ⟨(nat_equiv m).property, by simp; exact ⟨hm1, hm2⟩⟩
    use ⟨nat_equiv m, hm⟩
    simp
    omega

/-- Example 3.6.7 -/
theorem SetTheory.Set.Example_3_6_7a (a:Object) : ({a}:Set).has_card 1 := by
  rw [has_card_iff]
  use fun _ ↦ Fin_mk _ 0 (by simp)
  constructor
  · intro x1 x2 hf; aesop
  intro y
  use ⟨a, by simp⟩
  have := Fin.toNat_lt y
  simp_all

theorem SetTheory.Set.Example_3_6_7b {a b c d:Object} (hab: a ≠ b) (hac: a ≠ c) (had: a ≠ d)
    (hbc: b ≠ c) (hbd: b ≠ d) (hcd: c ≠ d) : ({a,b,c,d}:Set).has_card 4 := by
  rw [has_card_iff]
  use open Classical in fun x ↦ Fin_mk _ (
    if x.val = a then 0 else if x.val = b then 1 else if x.val = c then 2 else 3
  ) (by aesop)
  constructor
  · intro x1 x2 hf; aesop
  intro y
  have : y = (0:ℕ) ∨ y = (1:ℕ) ∨ y = (2:ℕ) ∨ y = (3:ℕ) := by
    have := Fin.toNat_lt y
    omega
  rcases this with (_ | _ | _ | _)
  · use ⟨a, by aesop⟩; aesop
  · use ⟨b, by aesop⟩; aesop
  · use ⟨c, by aesop⟩; aesop
  · use ⟨d, by aesop⟩; aesop

/-- Lemma 3.6.9 -/
theorem SetTheory.Set.pos_card_nonempty {n:ℕ} (h: n ≥ 1) {X:Set} (hX: X.has_card n) : X ≠ ∅ := by
  -- This proof is written to follow the structure of the original text.
  by_contra! this
  have hnon : Fin n ≠ ∅ := by
    apply nonempty_of_inhabited (x := 0); rw [mem_Fin]; use 0, (by omega); rfl
  rw [has_card_iff] at hX
  choose f hf using hX
  choose m hm using (Set.nonempty_def hnon)
  have x := (hf.2 ⟨m ,hm⟩).choose
  exact nonempty_of_inhabited x.property this
  -- obtain a contradiction from the fact that `f` is a bijection from the empty set to a
  -- non-empty set.

/-- Exercise 3.6.2a -/
theorem SetTheory.Set.has_card_zero {X:Set} : X.has_card 0 ↔ X = ∅ := by
  constructor
  · intro hX
    rw [has_card_iff] at hX
    obtain ⟨f, hf⟩ := hX
    -- If X were nonempty, f would map an element to Fin 0, which is empty
    by_contra hne
    obtain ⟨x, hx⟩ := Set.nonempty_def hne
    let y := f ⟨x, hx⟩
    have hy := y.property
    rw [specification_axiom''] at hy
    obtain ⟨hy1, hy2⟩ := hy
    exact Nat.not_lt_zero _ hy2
  · intro hX
    rw [hX]
    rw [has_card_iff]
    by_contra h
    push_neg at h
    let f := fun (x : (∅:Set)) => (⟨x, by exfalso; exact not_mem_empty _ (x.property)⟩ : Fin 0)
    apply h f
    constructor
    · intro x; exfalso; exact not_mem_empty _ (x.property)
    intro y; have hy := y.property; rw [specification_axiom''] at hy
    obtain ⟨z, hz⟩ := hy
    exfalso
    exact Nat.not_lt_zero _ hz

/-- Lemma 3.6.9 -/
theorem SetTheory.Set.card_erase {n:ℕ} (h: n ≥ 1) {X:Set} (hX: X.has_card n) (x:X) :
    (X \ {x.val}).has_card (n-1) := by
  -- This proof has been rewritten from the original text to try to make it friendlier to
  -- formalize in Lean.
  rw [has_card_iff] at hX; choose f hf using hX
  set X' : Set := X \ {x.val}
  set ι : X' → X := fun ⟨y, hy⟩ ↦ ⟨ y, by aesop ⟩
  observe hι : ∀ x:X', (ι x:Object) = x
  choose m₀ hm₀ hm₀f using (mem_Fin _ _).mp (f x).property
  set g : X' → Fin (n-1) := fun x' ↦
    let := Fin.toNat_lt (f (ι x'))
    let : (f (ι x'):ℕ) ≠ m₀ := by
      by_contra!; simp [←this, Subtype.val_inj, hf.1.eq_iff, ι] at hm₀f
      have := x'.property; aesop
    if h' : f (ι x') < m₀ then Fin_mk _ (f (ι x')) (by omega)
    else Fin_mk _ (f (ι x') - 1) (by omega)
  have hg_def (x':X') : if (f (ι x'):ℕ) < m₀ then (g x':ℕ) = f (ι x') else (g x':ℕ) = f (ι x') - 1 := by
    split_ifs with h' <;> simp [g,h']
  have hg : Function.Bijective g := by
    constructor
    · intro x1 x2 h;
      by_cases h1 : f (ι x1) < m₀
      by_cases h2 : f (ι x2) < m₀
      · unfold g at h
        simp [dif_pos h1, dif_pos h2] at h
        apply Subtype.val_inj.mp at h
        apply hf.1 at h
        apply Subtype.val_inj.mpr at h
        rw [hι, hι x2, Subtype.val_inj] at h
        exact h
      · unfold g at h
        simp [dif_pos h1, dif_neg h2] at h
        rw [h] at h1
        have : f (ι x2) = m₀ := by omega
        simp [← this] at hm₀f
        apply Subtype.val_inj.mp at hm₀f
        apply hf.1 at hm₀f
        apply Subtype.val_inj.mpr at hm₀f
        rw [hι] at hm₀f
        have hx2 := x2.property
        rw [mem_sdiff, mem_singleton] at hx2
        exfalso
        apply hx2.2
        rw [hm₀f]
      by_cases h2 : f (ι x2) < m₀
      · unfold g at h
        simp [dif_neg h1, dif_pos h2] at h
        have : (f (ι x1) : ℕ) - 1 = f (ι x2) := by
          rw [← Fin.coe_toNat] at h; exact Object.natCast_inj _ _ |>.mp h
        rw [← this] at h2
        have : f (ι x1) = m₀ := by omega
        simp [← this] at hm₀f
        apply Subtype.val_inj.mp at hm₀f
        apply hf.1 at hm₀f
        apply Subtype.val_inj.mpr at hm₀f
        rw [hι] at hm₀f
        have hx1 := x1.property
        rw [mem_sdiff, mem_singleton] at hx1
        exfalso
        apply hx1.2
        rw [hm₀f]
      · unfold g at h
        simp [dif_neg h1, dif_neg h2] at h
        have hm₀f_nat : (f x : ℕ) = m₀ := Object.natCast_inj _ _ |>.mp (by simpa using hm₀f)
        have hne : ι x1 ≠ x := by intro h; have := x1.property; aesop
        have hne' : f (ι x1) ≠ f x := fun h => hne (hf.1 h)
        have hne2 : (f (ι x1) : ℕ) ≠ m₀ := by
          intro h; apply hne'; exact Fin.coe_inj.mpr (h.trans hm₀f_nat.symm)
        have h3 : ((f (ι x1)) : ℕ) > 0 := by omega
        have hne3 : ι x2 ≠ x := by intro h; have := x2.property; aesop
        have hne4 : f (ι x2) ≠ f x := fun h => hne3 (hf.1 h)
        have hne5 : (f (ι x2) : ℕ) ≠ m₀ := by
          intro h; apply hne4; exact Fin.coe_inj.mpr (h.trans hm₀f_nat.symm)
        have h4 : ((f (ι x2)) : ℕ) > 0 := by omega
        have h5 : (f (ι x1) : ℕ) = (f (ι x2) : ℕ) := by omega
        rw [← Fin.coe_inj] at h5
        apply hf.1 at h5
        rw [← Subtype.val_inj, hι, hι x2, Subtype.val_inj] at h5
        exact h5
    intro y
    set k := (y : ℕ)
    have hk : k < n - 1 := Fin.toNat_lt y
    have hm₀f_nat : (f x : ℕ) = m₀ := Object.natCast_inj _ _ |>.mp (by simpa using hm₀f)
    by_cases hk_lt : k < m₀
    · have hk_fin : k < n := by omega
      obtain ⟨w, hw⟩ := hf.2 (Fin_mk n k hk_fin)
      have hwk : (f w : ℕ) = k := by rw [hw, Fin.toNat_mk]
      by_cases hw_eq : (w:Object) = x
      · exfalso
        have : w = x := Subtype.val_inj.mp hw_eq
        rw [this] at hwk; omega
      use ⟨w, by rw [mem_sdiff, mem_singleton]; exact ⟨w.property, hw_eq⟩⟩
      have hgi := hg_def ⟨w, by rw [mem_sdiff, mem_singleton]; exact ⟨w.property, hw_eq⟩⟩
      simp [hwk, hk_lt] at hgi
      exact Fin.coe_inj.mpr hgi
    · have hk1 : k + 1 < n := by omega
      obtain ⟨w, hw⟩ := hf.2 (Fin_mk n (k + 1) hk1)
      have hwk : (f w : ℕ) = k + 1 := by rw [hw, Fin.toNat_mk]
      by_cases hw_eq : (w:Object) = x
      · exfalso
        have : w = x := Subtype.val_inj.mp hw_eq
        rw [this] at hwk; omega
      use ⟨w, by rw [mem_sdiff, mem_singleton]; exact ⟨w.property, hw_eq⟩⟩
      have hgi := hg_def ⟨w, by rw [mem_sdiff, mem_singleton]; exact ⟨w.property, hw_eq⟩⟩
      simp [hwk, show ¬(k + 1) < m₀ by omega] at hgi
      exact Fin.coe_inj.mpr hgi
  use g

/-- Proposition 3.6.8 (Uniqueness of cardinality) -/
theorem SetTheory.Set.card_uniq {X:Set} {n m:ℕ} (h1: X.has_card n) (h2: X.has_card m) : n = m := by
  -- This proof is written to follow the structure of the original text.
  revert X m; induction' n with n hn
  . intro _ _ h1 h2; rw [has_card_zero] at h1; contrapose! h1
    apply pos_card_nonempty _ h2; omega
  intro X m h1 h2
  have : X ≠ ∅ := pos_card_nonempty (by omega) h1
  choose x hx using nonempty_def this
  have : m ≠ 0 := by contrapose! this; simpa [has_card_zero, this] using h2
  specialize hn (card_erase ?_ h1 ⟨ _, hx ⟩) (card_erase ?_ h2 ⟨ _, hx ⟩) <;> omega

lemma SetTheory.Set.Example_3_6_8_a: ({0,1,2}:Set).has_card 3 := by
  rw [has_card_iff]
  have : ({0, 1, 2}: Set) = SetTheory.Set.Fin 3 := by
    ext x
    simp only [mem_insert, mem_singleton, mem_Fin]
    constructor
    · aesop
    rintro ⟨x, ⟨_, rfl⟩⟩
    simp only [nat_coe_eq_iff]
    omega
  rw [this]
  use id
  exact Function.bijective_id

lemma SetTheory.Set.Example_3_6_8_b: ({3,4}:Set).has_card 2 := by
  rw [has_card_iff]
  use open Classical in fun x ↦ Fin_mk _ (if x = (3:Object) then 0 else 1) (by aesop)
  constructor
  · intro x1 x2
    aesop
  intro y
  have := Fin.toNat_lt y
  have : y = (0:ℕ) ∨ y = (1:ℕ) := by omega
  aesop

lemma SetTheory.Set.Example_3_6_8_c : ¬({0,1,2}:Set) ≈ ({3,4}:Set) := by
  by_contra h
  have h1 : Fin 3 ≈ Fin 2 := (Example_3_6_8_a.symm.trans h).trans Example_3_6_8_b
  have h2 : Fin 3 ≈ Fin 3 := by rfl
  have := card_uniq h1 h2
  contradiction

abbrev SetTheory.Set.finite (X:Set) : Prop := ∃ n:ℕ, X.has_card n

abbrev SetTheory.Set.infinite (X:Set) : Prop := ¬ finite X

/-- Exercise 3.6.3, phrased using Mathlib natural numbers -/
theorem SetTheory.Set.bounded_on_finite {n:ℕ} (f: Fin n → nat) : ∃ M, ∀ i, (f i:ℕ) ≤ M := by
  by_cases hn : n = 0
  . subst hn; have : Fin 0 = ∅ := by rw [SetTheory.Set.Fin, SetTheory.Set.specify, eq_empty_iff_forall_notMem]; grind [SetTheory.Set.specification_axiom'']
    use 0; intro x;
    have ⟨n, hn, _⟩ := mem_Fin _ _ |>.mp x.property
    exfalso; exact Nat.not_lt_zero _ hn
  let e := SetTheory.Set.Fin.Fin_equiv_Fin n
  let g (i : _root_.Fin n) : ℕ := (f (e.invFun i) : ℕ)
  let L := List.ofFn g
  have hL : L.length = n := List.length_ofFn
  have hL' : 0 < L.length := Nat.zero_lt_of_ne_zero (by aesop)
  let M := L.maximum_of_length_pos hL'
  use M
  intro i
  let j := e.toFun i
  have hij : j.1 < n := j.2
  have hij' : j.1 < L.length := by rw [hL]; exact hij
  calc (f i : ℕ) = (f (e.invFun j) : ℕ) := by rw [e.left_inv]
    _ = g j := rfl
    _ = L.get ⟨j.1, hij'⟩ := (List.get_ofFn g ⟨j.1, hij'⟩).symm
    _ ≤ M := List.le_maximum_of_length_pos_of_mem (List.get_mem L ⟨j.1, hij'⟩) hL'

/-- Theorem 3.6.12 -/
theorem SetTheory.Set.nat_infinite : infinite nat := by
  -- This proof is written to follow the structure of the original text.
  by_contra this; choose n hn using this
  simp [has_card] at hn; symm at hn; simp [HasEquiv.Equiv] at hn
  choose f hf using hn; choose M hM using bounded_on_finite f
  replace hf := hf.surjective ↑(M+1); contrapose! hf
  peel hM with hi; contrapose! hi
  apply_fun nat_equiv.symm at hi; simp_all

open Classical in
/-- It is convenient for Lean purposes to give infinite sets the "junk" cardinality of zero. -/
noncomputable def SetTheory.Set.card (X:Set) : ℕ := if h:X.finite then h.choose else 0

theorem SetTheory.Set.has_card_card {X:Set} (hX: X.finite) : X.has_card (SetTheory.Set.card X) := by
  simp [card, hX, hX.choose_spec]

theorem SetTheory.Set.has_card_to_card {X:Set} {n: ℕ}: X.has_card n → X.card = n := by
  intro h; simp [card, card_uniq (⟨ n, h ⟩:X.finite).choose_spec h]; aesop

theorem SetTheory.Set.card_to_has_card {X:Set} {n: ℕ} (hn: n ≠ 0): X.card = n → X.has_card n
  := by grind [card, has_card_card]

theorem SetTheory.Set.card_fin_eq (n:ℕ): (Fin n).has_card n := (has_card_iff _ _).mp ⟨ id, Function.bijective_id ⟩

theorem SetTheory.Set.Fin_card (n:ℕ): (Fin n).card = n := has_card_to_card (card_fin_eq n)

theorem SetTheory.Set.Fin_finite (n:ℕ): (Fin n).finite := ⟨n, card_fin_eq n⟩

theorem SetTheory.Set.EquivCard_to_has_card_eq {X Y:Set} {n: ℕ} (h: X ≈ Y): X.has_card n ↔ Y.has_card n := by
  choose f hf using h; let e := Equiv.ofBijective f hf
  constructor <;> (intro h'; rw [has_card_iff] at *; choose g hg using h')
  . use e.symm.trans (.ofBijective _ hg); apply Equiv.bijective
  . use e.trans (.ofBijective _ hg); apply Equiv.bijective

theorem SetTheory.Set.EquivCard_to_card_eq {X Y:Set} (h: X ≈ Y): X.card = Y.card := by
  by_cases hX: X.finite <;> by_cases hY: Y.finite <;> try rw [finite] at hX hY
  . choose nX hXn using hX; choose nY hYn using hY
    simp [has_card_to_card hXn, has_card_to_card hYn, EquivCard_to_has_card_eq h] at *
    solve_by_elim [card_uniq]
  . choose nX hXn using hX; rw [EquivCard_to_has_card_eq h] at hXn; tauto
  . choose nY hYn using hY; rw [←EquivCard_to_has_card_eq h] at hYn; tauto
  simp [card, hX, hY]

/-- Exercise 3.6.2 -/
theorem SetTheory.Set.empty_iff_card_eq_zero {X:Set} : X = ∅ ↔ X.finite ∧ X.card = 0 := by
  constructor
  · intro h; rw [h]
    constructor
    · use 0; simp [has_card_zero]
    apply has_card_to_card; rw [has_card_zero]
  intro ⟨h1, h2⟩
  rw [card, dif_pos h1] at h2
  have h3 := h1.choose_spec
  rw [h2] at h3
  exact has_card_zero.mp h3

lemma SetTheory.Set.empty_of_card_eq_zero {X:Set} (hX : X.finite) : X.card = 0 → X = ∅ := by
  intro h
  rw [empty_iff_card_eq_zero]
  exact ⟨hX, h⟩

lemma SetTheory.Set.finite_of_empty {X:Set} : X = ∅ → X.finite := by
  intro h
  rw [empty_iff_card_eq_zero] at h
  exact h.1

lemma SetTheory.Set.card_eq_zero_of_empty {X:Set} : X = ∅ → X.card = 0 := by
  intro h
  rw [empty_iff_card_eq_zero] at h
  exact h.2

@[simp]
lemma SetTheory.Set.empty_finite : (∅: Set).finite := finite_of_empty rfl

@[simp]
lemma SetTheory.Set.empty_card_eq_zero : (∅: Set).card = 0 := card_eq_zero_of_empty rfl

/-- Proposition 3.6.14 (a) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_insert {X:Set} (hX: X.finite) {x:Object} (hx: x ∉ X) :
    (X ∪ {x}).finite ∧ (X ∪ {x}).card = X.card + 1 := by
  have hXn := has_card_card hX
  set n := X.card
  rw [has_card_iff] at hXn
  obtain ⟨f, hf⟩ := hXn
  classical
  have hXux : (X ∪ {x}).has_card (n + 1) := by
    rw [has_card_iff]
    set g : ↥(X ∪ {x}) → ↥(Fin (n + 1)) := fun y =>
      if hy : (y : Object) ∈ X then
        Fin_mk (n + 1) ((f ⟨(y : Object), hy⟩) : ℕ) (by have := Fin.toNat_lt (f ⟨(y : Object), hy⟩); omega)
      else
        Fin_mk (n + 1) n (by omega)
    use g
    constructor
    · -- injective
      intro y1 y2 hg
      unfold g at hg; split_ifs at hg
      · -- both in X
        have h1 := Fin.coe_inj.mp hg; simp only [Fin.toNat_mk] at h1
        have h2 := hf.1 (Fin.coe_inj.mpr h1)
        have h3 : (y1 : Object) = (y2 : Object) := congrArg (fun z : X => (z : Object)) h2
        exact Subtype.ext h3
      · -- y1 in X, y2 not in X
        have h1 := Fin.coe_inj.mp hg; simp only [Fin.toNat_mk] at h1
        have : (f ⟨(y1 : Object), ‹(y1 : Object) ∈ X›⟩ : ℕ) < n := Fin.toNat_lt _
        omega
      · -- y1 not in X, y2 in X
        have h1 := Fin.coe_inj.mp hg; simp only [Fin.toNat_mk] at h1
        have : (f ⟨(y2 : Object), ‹(y2 : Object) ∈ X›⟩ : ℕ) < n := Fin.toNat_lt _
        omega
      · -- both not in X
        have ey1 : (y1 : Object) = x := by
          have h := y1.property; rw [mem_union] at h
          rcases h with (h | h); · exact absurd h ‹¬(y1 : Object) ∈ X›
          rw [mem_singleton] at h; exact h
        have ey2 : (y2 : Object) = x := by
          have h := y2.property; rw [mem_union] at h
          rcases h with (h | h); · exact absurd h ‹¬(y2 : Object) ∈ X›
          rw [mem_singleton] at h; exact h
        exact Subtype.ext (ey1.trans ey2.symm)
    · -- surjective
      intro k
      by_cases hk : (k : ℕ) < n
      · -- k < n: find preimage in X
        obtain ⟨w, hw⟩ := hf.2 (Fin_mk n (k : ℕ) hk)
        use ⟨(w : Object), by rw [mem_union]; left; exact w.property⟩
        unfold g; split_ifs
        · -- (w : Object) ∈ X
          apply Fin.coe_inj.mpr; simp only [Fin.toNat_mk]
          have : (f w : ℕ) = (k : ℕ) := by rw [hw]; simp only [Fin.toNat_mk]
          exact this
        · -- (w : Object) ∉ X, contradiction since w : X
          have : (w : Object) ∈ X := w.property
          contradiction
      · -- k = n: x is the preimage
        use ⟨x, by rw [mem_union]; right; rw [mem_singleton]⟩
        unfold g; split_ifs
        · -- x ∈ X, contradiction since hx : x ∉ X
          contradiction
        · -- x ∉ X
          apply Fin.coe_inj.mpr; simp only [Fin.toNat_mk]
          have hlt : (k : ℕ) < n + 1 := Fin.toNat_lt k
          omega
  exact ⟨⟨n + 1, hXux⟩, has_card_to_card hXux⟩

/-- Proposition 3.6.14 (b) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_union {X Y:Set} (hX: X.finite) (hY: Y.finite) :
    (X ∪ Y).finite ∧ (X ∪ Y).card ≤ X.card + Y.card := by
  have hXn := has_card_card hX
  have hYn := has_card_card hY
  set n := X.card with hn
  set m := Y.card with hm
  -- Prove by induction on k: for any Y' with has_card k, (X ∪ Y').finite ∧ card ≤ n + k
  have h_main : ∀ (k : ℕ), ∀ (Y' : Set), Y'.has_card k → ((X ∪ Y').finite ∧ (X ∪ Y').card ≤ n + k) := by
    intro k
    induction' k with k ih
    · -- k = 0, so Y' is empty
      intro Y' hY'0
      have hY'_empty : Y' = ∅ := has_card_zero.mp hY'0
      rw [hY'_empty, union_empty, hn]
      exact ⟨hX, le_rfl⟩
    · -- k = k.succ
      intro Y' hY'Sk
      have hk_pos : k.succ ≥ 1 := by omega
      have hY'_nonempty : Y' ≠ ∅ := pos_card_nonempty hk_pos hY'Sk
      rcases Set.nonempty_def hY'_nonempty with ⟨y, hy⟩
      set Y'' := Y' \ {y} with hY''
      have hY''_card : Y''.has_card k := by
        have h_card := card_erase hk_pos hY'Sk ⟨y, hy⟩
        have h_sub : k.succ - 1 = k := by omega
        simpa [hY'', h_sub] using h_card
      have h_induction := ih Y'' hY''_card
      rcases h_induction with ⟨h_fin, h_card⟩
      by_cases hy_in : y ∈ X ∪ Y''
      · -- y already in X ∪ Y'', so X ∪ Y' = X ∪ Y''
        have h_union_eq : X ∪ Y' = X ∪ Y'' := by
          apply Set.ext; intro z
          constructor
          · intro hz
            rw [mem_union] at hz ⊢
            rcases hz with (hzX | hzY')
            · exact Or.inl hzX
            · by_cases hzy : z = y
              · subst z; rw [mem_union] at hy_in; exact hy_in
              · right; rw [hY'', mem_sdiff]; exact ⟨hzY', by simpa [mem_singleton]⟩
          · intro hz
            rw [mem_union] at hz ⊢
            rcases hz with (hzX | hzY'')
            · exact Or.inl hzX
            · right; rw [hY'', mem_sdiff] at hzY''; exact hzY''.1
        rw [h_union_eq]
        have : n + k ≤ n + k.succ := by omega
        exact ⟨h_fin, le_trans h_card this⟩
      · -- y ∉ X ∪ Y'', apply card_insert
        have h_singleton_subset : ({y} : Set) ⊆ Y' := by
          intro z hz; rw [mem_singleton] at hz; subst hz; exact hy
        have h_singleton_union_sdiff : ({y} : Set) ∪ Y'' = Y' := by
          rw [hY'']
          exact union_compl h_singleton_subset
        have h_union_eq : X ∪ Y' = (X ∪ Y'') ∪ {y} := by
          rw [h_singleton_union_sdiff.symm, ← union_assoc, union_comm X {y}, union_assoc, union_comm]
        have h_card_insert := card_insert h_fin hy_in
        rcases h_card_insert with ⟨h_fin', h_card'⟩
        rw [h_union_eq]
        rw [h_card']
        have h_bound : (X ∪ Y'').card + 1 ≤ n + (k + 1) := by omega
        exact ⟨h_fin', h_bound⟩
  exact h_main m Y hYn

/-- Proposition 3.6.14 (b) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_union_disjoint {X Y:Set} (hX: X.finite) (hY: Y.finite)
  (hdisj: Disjoint X Y) : (X ∪ Y).card = X.card + Y.card := by
  have hXn := has_card_card hX
  have hYn := has_card_card hY
  have h_disj_empty : X ∩ Y = ∅ := by
    rw [← SetTheory.Set.disjoint_iff]
    exact hdisj
  set n := X.card with hn
  set m := Y.card with hm
  have h_main : ∀ (k : ℕ), ∀ (Y' : Set), Y'.has_card k → (Disjoint X Y') → (X ∪ Y').card = n + k := by
    intro k
    induction' k with k ih
    · intro Y' hY'0 hdisj'
      have hY'_empty : Y' = ∅ := has_card_zero.mp hY'0
      rw [hY'_empty, union_empty, hn]; ring
    · intro Y' hY'Sk hdisj'
      have hk_pos : k.succ ≥ 1 := by omega
      have hY'_nonempty : Y' ≠ ∅ := pos_card_nonempty hk_pos hY'Sk
      rcases Set.nonempty_def hY'_nonempty with ⟨y, hy⟩
      set Y'' := Y' \ {y} with hY''
      have hY''_card : Y''.has_card k := by
        have h_card := card_erase hk_pos hY'Sk ⟨y, hy⟩
        have h_sub : k.succ - 1 = k := by omega
        simpa [hY'', h_sub] using h_card
      have h_disj'_empty : X ∩ Y' = ∅ := by
        rw [← SetTheory.Set.disjoint_iff]; exact hdisj'
      have h_disj'' : Disjoint X Y'' := by
        rw [SetTheory.Set.disjoint_iff, eq_empty_iff_forall_notMem]
        intro z hz
        rw [mem_inter] at hz
        rcases hz with ⟨hzX, hzY''⟩
        rw [hY'', mem_sdiff] at hzY''
        have hzY' : z ∈ Y' := hzY''.1
        have : z ∈ X ∩ Y' := by rw [mem_inter]; exact ⟨hzX, hzY'⟩
        rw [h_disj'_empty] at this
        exact not_mem_empty z this
      have h_induction := ih Y'' hY''_card h_disj''
      have hy_notin_XUY'' : y ∉ X ∪ Y'' := by
        rw [mem_union]
        intro h
        rcases h with (hyX | hyY'')
        · have : y ∈ X ∩ Y' := by rw [mem_inter]; exact ⟨hyX, hy⟩
          rw [h_disj'_empty] at this
          exact not_mem_empty y this
        · rw [hY'', mem_sdiff] at hyY''
          rcases hyY'' with ⟨_, hy_notin_singleton⟩
          rw [mem_singleton] at hy_notin_singleton
          exact hy_notin_singleton rfl
      have h_card_insert := card_insert (by
        have h := card_union hX (⟨k, hY''_card⟩ : Y''.finite)
        exact h.1) hy_notin_XUY''
      rcases h_card_insert with ⟨_, h_card_eq⟩
      have h_singleton_subset : ({y} : Set) ⊆ Y' := by
        intro z hz
        rw [mem_singleton] at hz
        rw [hz]
        exact hy
      have h_union_eq : X ∪ Y' = (X ∪ Y'') ∪ {y} := by
        calc
          X ∪ Y' = X ∪ (Y'' ∪ {y}) := by
            rw [← union_compl h_singleton_subset, hY'', union_comm {y} Y'']
          _ = (X ∪ Y'') ∪ {y} := by rw [← union_assoc]
      rw [h_union_eq, h_card_eq, h_induction]
      ring
  exact h_main m Y hYn hdisj

/-- Proposition 3.6.14 (c) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_subset {X Y:Set} (hX: X.finite) (hY: Y ⊆ X) :
    Y.finite ∧ Y.card ≤ X.card := by
  have hXc := has_card_card hX
  have h_main : ∀ (k : ℕ), ∀ (X' : Set), X'.has_card k →
      (∀ (Y' : Set), Y' ⊆ X' → (Y'.finite ∧ Y'.card ≤ X'.card)) := by
    intro k
    induction' k with k ih
    · intro X' hX'0 Y' hY'X'
      have hX'_empty : X' = ∅ := has_card_zero.mp hX'0
      rw [hX'_empty] at hY'X'
      have hY'_empty : Y' = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro y hy
        exact not_mem_empty y (hY'X' y hy)
      rw [hX'_empty, hY'_empty]
      exact ⟨empty_finite, le_rfl⟩
    · intro X' hX'Sk Y' hY'X'
      by_cases hY'_empty : Y' = ∅
      · rw [hY'_empty]
        simp
      · rcases Set.nonempty_def hY'_empty with ⟨y, hy⟩
        have hyX' : y ∈ X' := hY'X' y hy
        set Y'' := Y' \ {y} with hY''
        set X'' := X' \ {y} with hX''
        have hk_pos : k.succ ≥ 1 := by omega
        have hX''_card : X''.has_card k := by
          have h := card_erase hk_pos hX'Sk ⟨y, hyX'⟩
          have h_sub : k.succ - 1 = k := by omega
          simpa [hX'', h_sub] using h
        have hY''_sub_X'' : Y'' ⊆ X'' := by
          intro z hz
          rw [hY'', mem_sdiff] at hz
          rcases hz with ⟨hzY', hz_not_singleton⟩
          rw [hX'', mem_sdiff]
          exact ⟨hY'X' z hzY', hz_not_singleton⟩
        have h_induction := ih X'' hX''_card Y'' hY''_sub_X''
        rcases h_induction with ⟨hY''_fin, h_card_ineq⟩
        have hy_notin_Y'' : y ∉ Y'' := by
          rw [hY'', mem_sdiff]
          intro h
          rcases h with ⟨_, h_not⟩
          rw [mem_singleton] at h_not
          exact h_not rfl
        have hy_notin_X'' : y ∉ X'' := by
          rw [hX'', mem_sdiff]
          intro h
          rcases h with ⟨_, h_not⟩
          rw [mem_singleton] at h_not
          exact h_not rfl
        have hX''_finite : X''.finite := ⟨k, hX''_card⟩
        have h_card_insert_Y := card_insert hY''_fin hy_notin_Y''
        have h_card_insert_X := card_insert hX''_finite hy_notin_X''
        rcases h_card_insert_Y with ⟨hY_fin, hY_card_eq⟩
        rcases h_card_insert_X with ⟨hX_fin, hX_card_eq⟩
        have h_singleton_subset_Y : ({y} : Set) ⊆ Y' := by
          intro z hz
          rw [mem_singleton] at hz
          subst z
          exact hy
        have h_singleton_subset_X : ({y} : Set) ⊆ X' := by
          intro z hz
          rw [mem_singleton] at hz
          subst z
          exact hyX'
        have hY_eq : Y' = Y'' ∪ {y} :=
          calc
            Y' = ({y} : Set) ∪ (Y' \ {y}) := (union_compl h_singleton_subset_Y).symm
            _ = ({y} : Set) ∪ Y'' := by rw [hY'']
            _ = Y'' ∪ {y} := by rw [union_comm]
        have hX_eq : X' = X'' ∪ {y} :=
          calc
            X' = ({y} : Set) ∪ (X' \ {y}) := (union_compl h_singleton_subset_X).symm
            _ = ({y} : Set) ∪ X'' := by rw [hX'']
            _ = X'' ∪ {y} := by rw [union_comm]
        rw [hY_eq, hX_eq, hY_card_eq, hX_card_eq]
        have h_card_le : Y''.card + 1 ≤ X''.card + 1 := by omega
        exact ⟨hY_fin, h_card_le⟩
  exact h_main X.card X hXc Y hY

/-- Proposition 3.6.14 (c) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_ssubset {X Y:Set} (hX: X.finite) (hY: Y ⊂ X) :
    Y.card < X.card := by
  rcases hY with ⟨hY_sub, hY_ne⟩
  have hXc := has_card_card hX
  have h_exists : ∃ x, x ∈ X ∧ x ∉ Y := by
    by_contra h_all
    push_neg at h_all
    have h_eq : X = Y := Set.ext (fun z => ⟨h_all z, hY_sub z⟩)
    exact hY_ne h_eq.symm
  rcases h_exists with ⟨x, hxX, hx_notY⟩
  have hX_card_pos : X.card ≥ 1 := by
    by_contra h
    have h0 : X.card = 0 := by omega
    have h_has0 : X.has_card 0 := by simpa [h0] using hXc
    have hX_empty : X = ∅ := has_card_zero.mp h_has0
    have : x ∉ X := by rw [hX_empty]; exact not_mem_empty x
    exact this hxX
  have h_erase : (X \ {x}).has_card (X.card - 1) := by
    simpa using card_erase hX_card_pos hXc ⟨x, hxX⟩
  have h_erase_fin : (X \ {x}).finite := ⟨X.card - 1, h_erase⟩
  have hY_sub_erase : Y ⊆ X \ {x} := by
    intro z hz
    rw [mem_sdiff]
    have hzX : z ∈ X := hY_sub z hz
    have hz_not_x : z ∉ ({x} : Set) := by
      intro hzx
      rw [mem_singleton] at hzx
      rw [hzx] at hz
      exact hx_notY hz
    exact ⟨hzX, hz_not_x⟩
  have h_card_erase_subset := card_subset h_erase_fin hY_sub_erase
  rcases h_card_erase_subset with ⟨_, hY_card_le_erase⟩
  have h_erase_card : (X \ {x}).card = X.card - 1 := by
    apply has_card_to_card h_erase
  rw [h_erase_card] at hY_card_le_erase
  omega

/-- Proposition 3.6.14 (d) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_image {X Y:Set} (hX: X.finite) (f: X → Y) :
    (image f X).finite ∧ (image f X).card ≤ X.card := by
  have hXc := has_card_card hX
  have h_main : ∀ (k : ℕ) (S : Set), S ⊆ X → S.has_card k →
      ((image f S).finite ∧ (image f S).card ≤ k) := by
    intro k S hS_sub hSk
    induction' k with k ih generalizing S
    · have hS_empty : S = ∅ := has_card_zero.mp hSk
      subst hS_empty
      have himg_empty : image f (∅ : Set) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro y hy; rw [mem_image] at hy; rcases hy with ⟨x, hx, _⟩
        exact not_mem_empty _ hx
      rw [himg_empty]; simp
    · have hpos : k.succ ≥ 1 := by omega
      have hne : S ≠ ∅ := pos_card_nonempty hpos hSk
      rcases Set.nonempty_def hne with ⟨x, hx⟩
      set S' := S \ {x} with hS'
      have hS'_sub : S' ⊆ X := by
        intro z hz; rw [hS', mem_sdiff] at hz; exact hS_sub _ hz.1
      have hS'_card : S'.has_card k := by
        have h := card_erase hpos hSk ⟨x, hx⟩
        have hsub : k.succ - 1 = k := by omega
        simpa [hS', hsub] using h
      have h_induction := ih S' hS'_sub hS'_card
      rcases h_induction with ⟨h_fin_S', h_card_S'⟩
      have himg_singleton_eq : image f {x} = {(f ⟨x, hS_sub x hx⟩).val} := by
        apply Set.ext; intro y; constructor
        · rw [mem_image]; rintro ⟨x', mem_sing, h⟩
          rw [mem_singleton] at mem_sing
          have hx'_eq : x' = ⟨x, hS_sub x hx⟩ := Subtype.val_inj.mp mem_sing
          subst hx'_eq; subst h; simp
        · intro hy; simp at hy; subst hy; rw [mem_image]
          use ⟨x, hS_sub x hx⟩; simp
      have himg_singleton_fin : (image f {x}).finite := by
        rw [himg_singleton_eq]; exact ⟨1, Example_3_6_7a _⟩
      have himg_singleton_card : (image f {x}).card ≤ 1 := by
        rw [himg_singleton_eq]
        rw [has_card_to_card (Example_3_6_7a _)]
      have h_singleton_subset : ({x} : Set) ⊆ S := by
        intro z hz; rw [mem_singleton] at hz; subst z; exact hx
      have h_union_eq : S = S' ∪ {x} :=
        calc
          S = ({x} : Set) ∪ (S \ {x}) := (union_compl h_singleton_subset).symm
          _ = ({x} : Set) ∪ S' := by rw [hS']
          _ = S' ∪ {x} := by rw [union_comm]
      rw [h_union_eq]
      have himg_union : image f (S' ∪ {x}) = image f S' ∪ image f {x} := image_of_union f S' {x}
      rw [himg_union]
      have h_union := card_union h_fin_S' himg_singleton_fin
      rcases h_union with ⟨h_fin_union, h_card_union⟩
      have h_card_total : (image f S').card + (image f {x}).card ≤ k.succ := by omega
      exact ⟨h_fin_union, le_trans h_card_union h_card_total⟩
  apply h_main X.card X (by intro _ h; exact h) hXc

/-- Proposition 3.6.14 (d) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_image_inj {X Y:Set} (_: X.finite) {f: X → Y}
  (hf: Function.Injective f) : (image f X).card = X.card := by
  have h_eq_card : X ≈ image f X := by
    let g : X → image f X := fun x => ⟨f x, by rw [mem_image]; use x; exact ⟨x.property, rfl⟩⟩
    use g
    constructor
    · intro a b h
      apply hf
      apply Subtype.val_inj.mp
      simpa [g] using congrArg Subtype.val h
    · intro y
      rcases (mem_image f X y.val).mp y.property with ⟨x, hx, h⟩
      use x
      apply Subtype.val_inj.mp
      simpa [g] using h
  exact (EquivCard_to_card_eq h_eq_card).symm

/-- Proposition 3.6.14 (e) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_prod {X Y:Set} (hX: X.finite) (hY: Y.finite) :
    (X ×ˢ Y).finite ∧ (X ×ˢ Y).card = X.card * Y.card := by
  have hXc := has_card_card hX
  have hYc := has_card_card hY
  have hempty_prod : (∅ : Set) ×ˢ Y = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro z hz; rw [mem_cartesian] at hz
    rcases hz with ⟨x, y, h⟩; exact not_mem_empty _ x.property
  have h_singleton_info (S : Set) (hS_sub : S ⊆ X) (x : Object) (hx : x ∈ S) :
      (({x} : Set) ×ˢ Y).finite ∧ (({x} : Set) ×ˢ Y).card = Y.card := by
    rcases (has_card_iff Y Y.card).mp hYc with ⟨φ, hφ⟩
    let e := Equiv.ofBijective φ hφ
    have h_has_card : (({x} : Set) ×ˢ Y).has_card Y.card := by
      rw [has_card_iff]
      let f : (({x} : Set) ×ˢ Y) → Fin Y.card := fun p => e (snd p)
      use f
      constructor
      · intro a b h
        have h_snd : snd a = snd b := e.bijective.injective h
        have h_fst : fst a = fst b := by
          have h_val_a : (fst a).val = x := by
            have hmem := (fst a).property; rwa [mem_singleton] at hmem
          have h_val_b : (fst b).val = x := by
            have hmem := (fst b).property; rwa [mem_singleton] at hmem
          apply Subtype.val_inj.mp; rw [h_val_a, h_val_b]
        calc
          a = mk_cartesian (fst a) (snd a) := (mk_cartesian_fst_snd_eq a).symm
          _ = mk_cartesian (fst b) (snd b) := by rw [h_fst, h_snd]
          _ = b := mk_cartesian_fst_snd_eq b
      · intro i
        let y := e.symm i
        let p : (({x} : Set) ×ˢ Y) := mk_cartesian (X := {x}) (Y := Y) (⟨x, by simp⟩) y
        use p
        calc
          f p = e (snd p) := rfl
          _ = e (snd (mk_cartesian (X := {x}) (Y := Y) (⟨x, by simp⟩) y)) := rfl
          _ = e y := by simp
          _ = e (e.symm i) := rfl
          _ = i := by simp
    exact ⟨⟨Y.card, h_has_card⟩, has_card_to_card h_has_card⟩
  have h_main : ∀ (k : ℕ) (S : Set), S ⊆ X → S.has_card k →
      ((S ×ˢ Y).finite ∧ (S ×ˢ Y).card = k * Y.card) := by
    intro k S hS_sub hSk
    induction' k with k ih generalizing S
    · have hS_empty : S = ∅ := has_card_zero.mp hSk
      subst hS_empty; rw [hempty_prod]; simp
    · have hpos : k.succ ≥ 1 := by omega
      have hne : S ≠ ∅ := pos_card_nonempty hpos hSk
      rcases Set.nonempty_def hne with ⟨x, hx⟩
      set S' := S \ {x} with hS'
      have hS'_sub : S' ⊆ X := by
        intro z hz; rw [hS', mem_sdiff] at hz; exact hS_sub _ hz.1
      have hS'_card : S'.has_card k := by
        have h := card_erase hpos hSk ⟨x, hx⟩
        have hsub : k.succ - 1 = k := by omega
        simpa [hS', hsub] using h
      have h_induction := ih S' hS'_sub hS'_card
      rcases h_induction with ⟨h_fin_prod_S', h_card_prod_S'⟩
      have h_singleton_info := h_singleton_info S hS_sub x hx
      rcases h_singleton_info with ⟨h_fin_singleton, h_card_singleton⟩
      have h_disj : Disjoint (S' ×ˢ Y) (({x} : Set) ×ˢ Y) := by
        rw [disjoint_iff]
        calc
          (S' ×ˢ Y) ∩ (({x} : Set) ×ˢ Y) = (S' ∩ {x}) ×ˢ (Y ∩ Y) := inter_of_prod S' Y {x} Y
          _ = (S' ∩ {x}) ×ˢ Y := by simp
          _ = ∅ ×ˢ Y := by
            rw [hS']
            have : (S \ {x}) ∩ {x} = ∅ := by
              apply eq_empty_iff_forall_notMem.mpr
              intro z hz; rw [mem_inter, mem_sdiff, mem_singleton] at hz
              rcases hz with ⟨⟨_, hz_not⟩, hz_eq⟩; exact hz_not hz_eq
            rw [this]
          _ = ∅ := hempty_prod
      have h_singleton_subset : ({x} : Set) ⊆ S := by
        intro z hz; rw [mem_singleton] at hz; subst z; exact hx
      have h_union_eq : S = S' ∪ {x} :=
        calc
          S = ({x} : Set) ∪ (S \ {x}) := (union_compl h_singleton_subset).symm
          _ = ({x} : Set) ∪ S' := by rw [hS']
          _ = S' ∪ {x} := by rw [union_comm]
      rw [h_union_eq]
      rw [union_prod S' {x} Y]
      have h_card_union := card_union_disjoint h_fin_prod_S' h_fin_singleton h_disj
      rw [h_card_prod_S', h_card_singleton] at h_card_union
      have h_card_total : k * Y.card + Y.card = (k + 1) * Y.card := by ring
      rw [h_card_total] at h_card_union
      exact ⟨by
        have := card_union h_fin_prod_S' h_fin_singleton
        exact this.1, h_card_union⟩
  exact h_main X.card X (by intro _ h; exact h) hXc

noncomputable def SetTheory.Set.pow_fun_equiv {A B : Set} : ↑(A ^ B) ≃ (B → A) where
  toFun F := ((powerset_axiom (F := F.val)).mp F.property).choose
  invFun f := ⟨(f : Object), by
    rw [powerset_axiom]
    exact ⟨f, rfl⟩⟩
  left_inv F := by
    ext
    have h := (powerset_axiom (F := F.val)).mp F.property
    simpa using h.choose_spec
  right_inv f := by
    have h := (powerset_axiom (X := A) (Y := B) (F := (f : Object))).mp (by
      rw [powerset_axiom (X := A) (Y := B)]
      exact ⟨f, rfl⟩)
    exact (coe_of_fun_inj _ _).mp h.choose_spec

lemma SetTheory.Set.pow_fun_eq_iff {A B : Set} (x y : ↑(A ^ B)) : x = y ↔ pow_fun_equiv x = pow_fun_equiv y := by
  rw [←pow_fun_equiv.apply_eq_iff_eq]

/-- Proposition 3.6.14 (f) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_pow {X Y:Set} (hY: Y.finite) (hX: X.finite) :
    (Y ^ X).finite ∧ (Y ^ X).card = Y.card ^ X.card := by sorry

/-- Exercise 3.6.5. You might find {name}`SetTheory.Set.prod_commutator` useful. -/
theorem SetTheory.Set.prod_EqualCard_prod (A B:Set) :
    EqualCard (A ×ˢ B) (B ×ˢ A) := by
  let e := prod_commutator (X := A) (Y := B)
  use e; exact e.bijective

noncomputable abbrev SetTheory.Set.pow_fun_equiv' (A B : Set) : ↑(A ^ B) ≃ (B → A) :=
  pow_fun_equiv (A:=A) (B:=B)

/-- Exercise 3.6.6. You may find {name}`SetTheory.Set.curry_equiv` useful. -/
theorem SetTheory.Set.pow_pow_EqualCard_pow_prod (A B C:Set) :
    EqualCard ((A ^ B) ^ C) (A ^ (B ×ˢ C)) := by
  let e := calc
    ↑((A ^ B) ^ C) ≃ (C → ↑(A ^ B)) := pow_fun_equiv
    _ ≃ (C → (B → A)) := {
      toFun := fun g c => pow_fun_equiv (g c)
      invFun := fun g c => (pow_fun_equiv (A := A) (B := B)).symm (g c)
      left_inv := by intro g; ext c; simp
      right_inv := by intro g; ext c; simp
    }
    _ ≃ (C ×ˢ B → A) := curry_equiv
    _ ≃ (B ×ˢ C → A) := {
      toFun := fun g bc => g (prod_commutator (X := B) (Y := C) bc)
      invFun := fun g cb => g ((prod_commutator (X := B) (Y := C)).symm cb)
      left_inv := by intro g; ext cb; simp
      right_inv := by intro g; ext bc; simp
    }
    _ ≃ ↑(A ^ (B ×ˢ C)) := (pow_fun_equiv (A := A) (B := B ×ˢ C)).symm
  use e; exact e.bijective

set_option linter.unusedSectionVars false
theorem SetTheory.Set.pow_pow_eq_pow_mul (a b c:ℕ): (a^b)^c = a^(b*c) := by
  induction' c with c ih
  · simp
  · rw [Nat.pow_succ, ih, mul_add, pow_add, mul_one]

theorem SetTheory.Set.pow_prod_pow_EqualCard_pow_union (A B C:Set) (hd: Disjoint B C) :
    EqualCard ((A ^ B) ×ˢ (A ^ C)) (A ^ (B ∪ C)) := by sorry

theorem SetTheory.Set.pow_mul_pow_eq_pow_add (a b c:ℕ): (a^b) * a^c = a^(b+c) := by
  rw [pow_add]

/-- Exercise 3.6.7 -/
theorem SetTheory.Set.injection_iff_card_le {A B:Set} (hA: A.finite) (hB: B.finite) :
    (∃ f:A → B, Function.Injective f) ↔ A.card ≤ B.card := by
  constructor
  · rintro ⟨f, hf⟩
    have h_card_image := card_image_inj hA hf
    have h_image_subset : image f A ⊆ B := by
      intro y hy; rw [mem_image] at hy; rcases hy with ⟨x, hx, h⟩; rw [← h]; exact (f x).property
    have h_card_subset := card_subset hB h_image_subset
    rcases h_card_subset with ⟨_, h_le⟩
    rw [h_card_image] at h_le; exact h_le
  · intro h
    have hAc := has_card_card hA
    have hBc := has_card_card hB
    rcases (has_card_iff A A.card).mp hAc with ⟨φA, hφA⟩
    rcases (has_card_iff B B.card).mp hBc with ⟨φB, hφB⟩
    let eA := Equiv.ofBijective φA hφA
    let eB := Equiv.ofBijective φB hφB
    let emb : ↥(Fin A.card) → ↥(Fin B.card) := Fin_embed A.card B.card h
    have hemb_inj : Function.Injective emb := by
      intro x y heq; apply Subtype.val_inj.mp; simpa [Fin_embed] using congrArg Subtype.val heq
    let f : A → B := eB.symm ∘ emb ∘ eA
    use f
    intro x y h
    apply eA.injective
    apply hemb_inj
    apply eB.symm.injective
    simpa [f] using h

/-- Exercise 3.6.8 -/
theorem SetTheory.Set.surjection_from_injection {A B:Set} (hA: A ≠ ∅) (f: A → B)
  (hf: Function.Injective f) : ∃ g:B → A, Function.Surjective g := by
  rcases Set.nonempty_def hA with ⟨a0, ha0⟩
  classical
    let g : B → A := fun b =>
      if h : b.val ∈ image f A then
        ((mem_image f A b.val).mp h).choose
      else
        ⟨a0, ha0⟩
  use g
  intro a
  use f a
  dsimp [g]
  have hmem : (f a).val ∈ image f A := by
    rw [mem_image]; use a; exact ⟨a.property, rfl⟩
  rw [dif_pos hmem]
  have h_pre := (mem_image f A (f a).val).mp hmem
  have h_val_eq : (f h_pre.choose).val = (f a).val := by
    simpa using h_pre.choose_spec.2
  have h_f_eq : f h_pre.choose = f a := Subtype.val_inj.mp h_val_eq
  exact hf h_f_eq

/-- Exercise 3.6.9 -/
theorem SetTheory.Set.card_union_add_card_inter {A B:Set} (hA: A.finite) (hB: B.finite) :
    A.card + B.card = (A ∪ B).card + (A ∩ B).card := by
  have hBA_fin : (B \ A).finite := by
    have := card_subset hB (show (B \ A) ⊆ B from by intro x h; rw [mem_sdiff] at h; exact h.1)
    exact this.1
  have hAB_fin : (A ∩ B).finite := by
    have := card_subset hA (show (A ∩ B) ⊆ A from by intro x h; rw [mem_inter] at h; exact h.1)
    exact this.1
  have h_disj1 : Disjoint A (B \ A) := by
    rw [disjoint_iff, eq_empty_iff_forall_notMem]
    intro x hx; rw [mem_inter] at hx; rcases hx with ⟨hxA, hxBA⟩
    rw [mem_sdiff] at hxBA; exact hxBA.2 hxA
  have h_union1 : A ∪ (B \ A) = A ∪ B := by
    apply Set.ext; intro x; rw [mem_union, mem_union, mem_sdiff]; tauto
  have h_card1 := card_union_disjoint hA hBA_fin h_disj1
  have h_disj2 : Disjoint (B \ A) (A ∩ B) := by
    rw [disjoint_iff, eq_empty_iff_forall_notMem]
    intro x hx; rw [mem_inter] at hx; rcases hx with ⟨hxBA, hxAB⟩
    rw [mem_sdiff] at hxBA; rcases hxBA with ⟨hxB, hxnA⟩
    rw [mem_inter] at hxAB; exact hxnA hxAB.1
  have h_union2 : (B \ A) ∪ (A ∩ B) = B := by
    apply Set.ext; intro x; rw [mem_union, mem_inter, mem_sdiff]; tauto
  have h_card2 := card_union_disjoint hBA_fin hAB_fin h_disj2
  have h_card1' : (A ∪ B).card = A.card + (B \ A).card := by
    simpa [h_union1] using h_card1
  have h_card2' : B.card = (B \ A).card + (A ∩ B).card := by
    simpa [h_union2] using h_card2
  rw [h_card2', h_card1']
  omega

/-- Exercise 3.6.10 -/
theorem SetTheory.Set.pigeonhole_principle {n:ℕ} {A: Fin n → Set}
  (hA: ∀ i, (A i).finite) (hAcard: (iUnion _ A).card > n) : ∃ i, (A i).card ≥ 2 := by sorry

/-- Exercise 3.6.11 -/
theorem SetTheory.Set.two_to_two_iff {X Y:Set} (f: X → Y): Function.Injective f ↔
    ∀ S ⊆ X, S.card = 2 → (image f S).card = 2 := by sorry

/-- Connections with Mathlib's {name}`Finite` -/
theorem SetTheory.Set.finite_iff_finite {X:Set} : X.finite ↔ Finite X := by
  constructor
  · rintro ⟨n, hn⟩
    rcases (has_card_iff X n).mp hn with ⟨f, hf⟩
    have eq : X ≃ _root_.Fin n := (Equiv.ofBijective f hf).trans (Fin.Fin_equiv_Fin n)
    exact Finite.of_equiv _ eq.symm
  · intro hFin
    rcases Finite.exists_equiv_fin X with ⟨n, h⟩
    use n
    let e : X ≃ _root_.Fin n := Classical.choice h
    have eq : X ≃ Fin n := e.trans (Fin.Fin_equiv_Fin n).symm
    rw [has_card_iff]
    use eq; exact eq.bijective

/-- Connections with Mathlib's {name}`Set.Finite` -/
theorem SetTheory.Set.finite_iff_set_finite {X:Set} :
    X.finite ↔ (X :_root_.Set Object).Finite := by
  rw [finite_iff_finite]
  rfl

/-- Exercise 3.6.12 -/
def SetTheory.Set.Permutations (n: ℕ): Set := (Fin n ^ Fin n).specify (fun F ↦
    Function.Bijective (pow_fun_equiv F))

/-- Exercise 3.6.12 (i), first part -/
theorem SetTheory.Set.Permutations_finite (n: ℕ): (Permutations n).finite := by
  have h_fin_pow : (Fin n ^ Fin n).finite := by
    rw [finite_iff_finite]
    have h_equiv : ↑(Fin n ^ Fin n) ≃ (_root_.Fin n → _root_.Fin n) :=
      (pow_fun_equiv (A := Fin n) (B := Fin n)).trans
      { toFun := fun f x => Fin.Fin_equiv_Fin n (f ((Fin.Fin_equiv_Fin n).symm x))
        invFun := fun g x => (Fin.Fin_equiv_Fin n).symm (g (Fin.Fin_equiv_Fin n x))
        left_inv := by
          intro f; ext x
          have hx_spec := Fin.toNat_spec x
          rcases hx_spec with ⟨hx_lt, hx_eq⟩
          rw [hx_eq]
          simp [Fin.Fin_equiv_Fin, Fin.toNat_mk]
        right_inv := by
          intro g; ext x
          simp [Fin.Fin_equiv_Fin] }
    exact Finite.of_equiv _ h_equiv.symm
  have h_sub : Permutations n ⊆ Fin n ^ Fin n := by
    intro x hx
    rw [Permutations] at hx
    exact ((specification_axiom'' (x := x) (A := Fin n ^ Fin n)
      (P := fun F => Function.Bijective (pow_fun_equiv F))).mp hx).choose
  exact (card_subset h_fin_pow h_sub).1

/- To continue Exercise 3.6.12 (i), we'll first develop some theory about `Permutations` and `Fin`. -/

noncomputable def SetTheory.Set.Permutations_toFun {n: ℕ} (p: Permutations n) : (Fin n) → (Fin n) := by
  have := p.property
  simp only [Permutations, specification_axiom'', powerset_axiom] at this
  exact this.choose.choose

theorem SetTheory.Set.Permutations_bijective {n: ℕ} (p: Permutations n) :
    Function.Bijective (Permutations_toFun p) := by
  have hp_mem : p.val ∈ Permutations n := p.property
  rcases ((specification_axiom'' (x := p.val) (A := Fin n ^ Fin n)
    (P := fun F => Function.Bijective (pow_fun_equiv F))).mp hp_mem) with ⟨h_pow_mem, h_bijective⟩
  have h_val : (Permutations_toFun p : Object) = p.val := by
    unfold Permutations_toFun
    have h := p.property
    simp only [Permutations, specification_axiom'', powerset_axiom] at h
    have h_inner := h.choose.choose_spec
    simpa using h_inner
  have h_fun_eq : Permutations_toFun p = pow_fun_equiv ⟨p.val, h_pow_mem⟩ := by
    apply (coe_of_fun_inj _ _).mp
    rw [h_val]
    have hpow := (powerset_axiom (F := p.val)).mp h_pow_mem
    simpa [pow_fun_equiv] using hpow.choose_spec.symm
  rw [h_fun_eq]; exact h_bijective

theorem SetTheory.Set.Permutations_inj {n: ℕ} (p1 p2: Permutations n) :
    Permutations_toFun p1 = Permutations_toFun p2 ↔ p1 = p2 := by
  constructor
  · intro h
    apply Subtype.val_inj.mp
    have hp1 := p1.property
    have hp2 := p2.property
    simp only [Permutations, specification_axiom'', powerset_axiom] at hp1 hp2
    calc
      p1.val = (Permutations_toFun p1 : Object) := by
        unfold Permutations_toFun; symm; simpa using hp1.choose.choose_spec
      _ = (Permutations_toFun p2 : Object) := by rw [h]
      _ = p2.val := by
        unfold Permutations_toFun; simpa using hp2.choose.choose_spec
  · intro h; subst h; rfl

/-- This connects our concept of a permutation with Mathlib's {name}`Equiv` between {lean}`Fin n` and {lean}`Fin n`. -/
noncomputable def SetTheory.Set.perm_equiv_equiv {n : ℕ} : Permutations n ≃ (Fin n ≃ Fin n) :=
  let toF : Permutations n → (Fin n ≃ Fin n) := fun p =>
    Equiv.ofBijective (Permutations_toFun p) (Permutations_bijective p)
  let invF : (Fin n ≃ Fin n) → Permutations n := fun e =>
    have h_mem : ((e : Fin n → Fin n) : Object) ∈ Fin n ^ Fin n := by
      rw [powerset_axiom]; exact ⟨e, rfl⟩
    have h_bijective : Function.Bijective (pow_fun_equiv ⟨(e : Object), h_mem⟩) := by
      have h_eq : pow_fun_equiv ⟨(e : Object), h_mem⟩ = (e : Fin n → Fin n) := by
        apply (coe_of_fun_inj _ _).mp
        have hpow := (powerset_axiom (F := (e : Object))).mp h_mem
        simp [pow_fun_equiv]
      rw [h_eq]; exact e.bijective
    ⟨(e : Object), by
      rw [Permutations, specification_axiom'']
      exact ⟨h_mem, h_bijective⟩⟩
  {
    toFun := toF
    invFun := invF
    left_inv := by
      intro p
      have h_val : (Permutations_toFun p : Object) = p.val := by
        unfold Permutations_toFun
        have h := p.property
        simp only [Permutations, specification_axiom'', powerset_axiom] at h
        have h_inner := h.choose.choose_spec
        simpa using h_inner
      apply Subtype.val_inj.mp
      calc
        (invF (toF p)).val = ((toF p : Fin n → Fin n) : Object) := rfl
        _ = (Permutations_toFun p : Object) := rfl
        _ = p.val := h_val
    right_inv := by
      intro e
      ext x
      let p : Permutations n := invF e
      have h_fun : Permutations_toFun p = (e : Fin n → Fin n) := by
        apply (coe_of_fun_inj _ _).mp
        have h_perm_val : (Permutations_toFun p : Object) = p.val := by
          unfold Permutations_toFun
          have h := p.property
          simp only [Permutations, specification_axiom'', powerset_axiom] at h
          have h_inner := h.choose.choose_spec
          simpa using h_inner
        have hp_val : p.val = (e : Object) := rfl
        rw [h_perm_val, hp_val]
      have h_eq : (toF (invF e)) x = e x := by
        calc
          (toF (invF e)) x = (toF p) x := rfl
          _ = (Equiv.ofBijective (Permutations_toFun p) (Permutations_bijective p)) x := rfl
          _ = (Permutations_toFun p) x := rfl
          _ = (e : Fin n → Fin n) x := by rw [h_fun]
          _ = e x := rfl
      simpa using congrArg Subtype.val h_eq
  }

/- Exercise 3.6.12 involves a lot of moving between `Fin n` and `Fin (n + 1)` so let's add some conveniences. -/

/-- Any {lean}`Fin n` can be cast to {lean}`Fin (n + 1)`. Compare to Mathlib {name}`Fin.castSucc`. -/
def SetTheory.Set.Fin.castSucc {n} (x : Fin n) : Fin (n + 1) :=
  Fin_embed _ _ (by omega) x

@[simp]
lemma SetTheory.Set.Fin.castSucc_inj {n} {x y : Fin n} : castSucc x = castSucc y ↔ x = y := by
  constructor
  · intro h
    apply Subtype.val_inj.mp
    simpa [castSucc] using congrArg Subtype.val h
  · intro h; subst h; rfl

@[simp]
theorem SetTheory.Set.Fin.castSucc_ne {n} (x : Fin n) : castSucc x ≠ n := by
  have hx := Fin.toNat_lt x
  have hcast : (castSucc x : ℕ) = (x : ℕ) := by simp [castSucc, Fin_embed]
  rw [hcast]
  omega

/-- Any {lean}`Fin (n + 1)` except {lean}`n` can be cast to {lean}`Fin n`. Compare to Mathlib {name}`Fin.castPred`. -/
noncomputable def SetTheory.Set.Fin.castPred {n} (x : Fin (n + 1)) (h : (x : ℕ) ≠ n) : Fin n :=
  Fin_mk _ (x : ℕ) (by have := Fin.toNat_lt x; omega)

@[simp]
theorem SetTheory.Set.Fin.castSucc_castPred {n} (x : Fin (n + 1)) (h : (x : ℕ) ≠ n) :
    castSucc (castPred x h) = x := by
  apply Subtype.val_inj.mp; simp [castSucc, castPred, Fin_embed]

@[simp]
theorem SetTheory.Set.Fin.castPred_castSucc {n} (x : Fin n) (h : ((castSucc x : Fin (n + 1)) : ℕ) ≠ n) :
    castPred (castSucc x) h = x := by
  apply Subtype.val_inj.mp; simp [castSucc, castPred, Fin_embed]

/-- Any natural {lean}`n` can be cast to {lean}`Fin (n + 1)`. Compare to Mathlib {name}`Fin.last`. -/
def SetTheory.Set.Fin.last (n : ℕ) : Fin (n + 1) := Fin_mk _ n (by omega)

/-- Now is a good time to prove this result, which will be useful for completing Exercise 3.6.12 (i). -/
theorem SetTheory.Set.card_iUnion_card_disjoint {n m: ℕ} {S : Fin n → Set}
    (hSc : ∀ i, (S i).has_card m)
    (hSd : Pairwise fun i j => Disjoint (S i) (S j)) :
    ((Fin n).iUnion S).finite ∧ ((Fin n).iUnion S).card = n * m := by
  revert S; induction' n with n ih
  · intro S hSc hSd
    have h_empty : (Fin 0).iUnion S = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx; rw [mem_iUnion] at hx; rcases hx with ⟨i, hi⟩
      have h := Fin.toNat_lt i; omega
    rw [h_empty]; simp
  · intro S hSc hSd
    set S' : Fin n → Set := fun i => S (Fin.castSucc i) with hS'
    have hSc' : ∀ i, (S' i).has_card m := by intro i; simp [hS', hSc]
    have hSd' : Pairwise fun (i j : Fin n) => Disjoint (S' i) (S' j) := by
      intro i j h_ne
      dsimp [S']
      apply hSd
      intro h_eq; apply h_ne; exact (Fin.castSucc_inj.mp h_eq)
    rcases ih hSc' hSd' with ⟨h_fin_iUnion, h_card_iUnion⟩
    have h_last_fin : (S (Fin.last n)).finite := ⟨m, hSc (Fin.last n)⟩
    have h_last_card : (S (Fin.last n)).card = m := has_card_to_card (hSc (Fin.last n))
    have h_disj_mem : ∀ i : Fin n, Disjoint (S' i) (S (Fin.last n)) := by
      intro i
      have h_ne : Fin.castSucc i ≠ Fin.last n := by
        intro h_eq
        have h_val := (Fin.coe_inj (n := n.succ)).mp h_eq
        have h_cast_val : (Fin.castSucc i : ℕ) = (i : ℕ) := by simp [Fin.castSucc, Fin_embed]
        have h_last_val : (Fin.last n : ℕ) = n := by simp [Fin.last]
        rw [h_cast_val, h_last_val] at h_val
        have hi_lt_n : (i : ℕ) < n := Fin.toNat_lt i
        omega
      apply hSd; exact h_ne
    have h_disj : Disjoint ((Fin n).iUnion S') (S (Fin.last n)) := by
      rw [disjoint_iff, eq_empty_iff_forall_notMem]
      intro x hx; rw [mem_inter] at hx; rcases hx with ⟨hx_union, hx_last⟩
      rw [mem_iUnion] at hx_union; rcases hx_union with ⟨i, hi⟩
      have hd := h_disj_mem i
      rw [disjoint_iff] at hd
      have hx_inter : x ∈ S' i ∩ S (Fin.last n) := by rw [mem_inter]; exact ⟨hi, hx_last⟩
      rw [hd] at hx_inter
      exact not_mem_empty _ hx_inter
    have h_union_eq : (Fin n.succ).iUnion S = ((Fin n).iUnion S') ∪ S (Fin.last n) := by
      apply SetTheory.Set.ext; intro x
      rw [mem_iUnion, mem_union, mem_iUnion]
      refine ⟨by
        rintro ⟨i, hi⟩
        by_cases hi_last : i = Fin.last n
        · subst i; right; exact hi
        · have hi_ne_n : (i : ℕ) ≠ n := by
            intro h_eq; apply hi_last
            apply (Fin.coe_inj (n := n.succ)).mpr
            have h_last_val : (Fin.last n : ℕ) = n := by simp [Fin.last]
            rw [h_last_val, h_eq]
          let j : Fin n := Fin.castPred i hi_ne_n
          have hi_eq : Fin.castSucc j = i := Fin.castSucc_castPred i hi_ne_n
          left; use j; dsimp [S']; rw [hi_eq]; exact hi
      , by
        intro h; rcases h with (⟨i, hi⟩ | h)
        · use Fin.castSucc i
        · use Fin.last n
      ⟩
    rw [h_union_eq]
    have h_card_union := card_union_disjoint h_fin_iUnion h_last_fin h_disj
    rw [h_card_iUnion, h_last_card] at h_card_union
    have h_card_total : n * m + m = n.succ * m := by
      rw [Nat.succ_mul]
    rw [h_card_total] at h_card_union
    have h_fin_union : (((Fin n).iUnion S') ∪ S (Fin.last n)).finite := by
      have h := card_union h_fin_iUnion h_last_fin
      exact h.1
    exact ⟨h_fin_union, h_card_union⟩

/- Finally, we'll set up a way to shrink `Fin (n + 1)` into `Fin n` (or expand the latter) by making a hole. -/

/--
  If some {lean}`x : Fin (n+1)` is never equal to {name}`i`, we can shrink it into {lean}`Fin n` by shifting all {lean}`(x : ℕ) > i` down by one.
  Compare to Mathlib {name}`Fin.predAbove`.
-/
noncomputable def SetTheory.Set.Fin.predAbove {n} (i : Fin (n + 1)) (x : Fin (n + 1)) (h : x ≠ i) : Fin n :=
  if hx : (x:ℕ) < i then
    Fin_mk _ (x:ℕ) (by
      have hx_bound := Fin.toNat_lt x
      have hi_bound := Fin.toNat_lt i
      by_cases h_eq : (x : ℕ) = n
      · have : (i : ℕ) = n := by omega
        have heq : x = i := (Fin.coe_inj (n := n + 1)).mpr (by simp [h_eq, this])
        exact absurd heq h
      · omega)
  else
    Fin_mk _ ((x:ℕ) - 1) (by
      have hx_bound := Fin.toNat_lt x
      have hn_pos : n ≥ 1 := by
        by_contra! hle
        have hn0 : n = 0 := by omega
        subst hn0
        have hi0 : (i : ℕ) = 0 := by have hi := Fin.toNat_lt i; omega
        have hx0 : (x : ℕ) = 0 := by omega
        have heqx : x = i := (Fin.coe_inj (n := 1)).mpr (by simp [hi0, hx0])
        exact h heqx
      omega)

/--
  We can expand {lean}`x : Fin n` into {lean}`Fin (n + 1)` by shifting all {lean}`(x : ℕ) ≥ i` up by one.
  The output is never {name}`i`, so it forms an inverse to the shrinking done by {name}`predAbove`.
  Compare to Mathlib {name}`Fin.succAbove`.
-/
noncomputable def SetTheory.Set.Fin.succAbove {n} (i : Fin (n + 1)) (x : Fin n) : Fin (n + 1) :=
  if (x:ℕ) < i then
    Fin_embed _ _ (by omega) x
  else
    Fin_mk _ ((x:ℕ) + 1) (by
      have hx := Fin.toNat_lt x
      omega)

@[simp]
theorem SetTheory.Set.Fin.succAbove_ne {n} (i : Fin (n + 1)) (x : Fin n) : succAbove i x ≠ i := by
  dsimp [succAbove]
  split_ifs with h_lt
  · intro h_eq
    have h_val := (Fin.coe_inj (n := n + 1)).mp h_eq
    simp [Fin_embed] at h_val
    omega
  · intro h_eq
    have h_val := (Fin.coe_inj (n := n + 1)).mp h_eq
    simp at h_val
    omega

@[simp]
theorem SetTheory.Set.Fin.succAbove_predAbove {n} (i : Fin (n + 1)) (x : Fin (n + 1)) (h : x ≠ i) :
    (succAbove i) (predAbove i x h) = x := by
  apply (Fin.coe_inj (n := n + 1)).mpr
  by_cases h1 : (x : ℕ) < i
  · have h_pred_val : (predAbove i x h : ℕ) = (x : ℕ) := by
      simp [predAbove, h1, Fin.toNat_mk]
    have h_cond : (predAbove i x h : ℕ) < i := by rw [h_pred_val]; exact h1
    calc
      (succAbove i (predAbove i x h) : ℕ) = (predAbove i x h : ℕ) := by
        have h_eq : succAbove i (predAbove i x h) = Fin_embed n (n+1) (by omega) (predAbove i x h) := by
          delta succAbove; rw [if_pos h_cond]
        rw [h_eq]; simp [Fin_embed]
      _ = (x : ℕ) := h_pred_val
  · have h_pred_val : (predAbove i x h : ℕ) = (x : ℕ) - 1 := by
      simp [predAbove, h1, Fin.toNat_mk]
    by_cases h2 : (x : ℕ) - 1 < i
    · have hi_eq_x : (i : ℕ) = (x : ℕ) := by omega
      have heq : x = i := (Fin.coe_inj (n := n + 1)).mpr hi_eq_x.symm
      exact absurd heq h
    · have h_cond : ¬ ((predAbove i x h : ℕ) < i) := by rw [h_pred_val]; exact h2
      have hx_pos : (x : ℕ) ≥ 1 := by
        by_contra! hle
        have hx0 : (x : ℕ) = 0 := by omega
        have hi0 : (i : ℕ) = 0 := by omega
        have heq' : x = i := (Fin.coe_inj (n := n + 1)).mpr (by rw [hx0, hi0])
        exact h heq'
      calc
        (succAbove i (predAbove i x h) : ℕ) = ((predAbove i x h : ℕ) + 1) := by
          have h_eq : succAbove i (predAbove i x h) =
              Fin_mk (n + 1) (((predAbove i x h) : ℕ) + 1) (by
                have hx := Fin.toNat_lt (predAbove i x h); omega) := by
            delta succAbove; rw [if_neg h_cond]
          rw [h_eq]; simp [Fin.toNat_mk]
        _ = ((x : ℕ) - 1) + 1 := by rw [h_pred_val]
        _ = (x : ℕ) := by omega

@[simp]
theorem SetTheory.Set.Fin.predAbove_succAbove {n} (i : Fin (n + 1)) (x : Fin n) :
    (predAbove i) (succAbove i x) (succAbove_ne i x) = x := by
  apply (Fin.coe_inj (n := n)).mpr
  by_cases h1 : (x : ℕ) < i
  · have h_succ_val : (succAbove i x : ℕ) = (x : ℕ) := by
      simp [succAbove, h1, Fin_embed]
    have h_cond : (succAbove i x : ℕ) < i := by rw [h_succ_val]; exact h1
    calc
      (predAbove i (succAbove i x) (succAbove_ne i x) : ℕ) = (succAbove i x : ℕ) := by
        have h_eq : predAbove i (succAbove i x) (succAbove_ne i x) =
            Fin_mk n ((succAbove i x : ℕ)) (by rw [h_succ_val]; exact Fin.toNat_lt x) := by
          by_cases htemp : (succAbove i x : ℕ) < i
          · simp [predAbove, htemp]
          · exfalso; exact htemp h_cond
        rw [h_eq]; simp [Fin.toNat_mk]
      _ = (x : ℕ) := h_succ_val
  · have h_succ_val : (succAbove i x : ℕ) = (x : ℕ) + 1 := by
      simp [succAbove, h1, Fin.toNat_mk]
    have h_cond : ¬ ((succAbove i x : ℕ) < i) := by rw [h_succ_val]; omega
    calc
      (predAbove i (succAbove i x) (succAbove_ne i x) : ℕ) = ((succAbove i x : ℕ) - 1) := by
        have h_eq : predAbove i (succAbove i x) (succAbove_ne i x) =
            Fin_mk n (((succAbove i x : ℕ)) - 1) (by
              rw [h_succ_val]; have hx := Fin.toNat_lt x; omega) := by
          by_cases htemp : (succAbove i x : ℕ) < i
          · exfalso; exact h_cond htemp
          · simp [predAbove, htemp]
        rw [h_eq]; simp [Fin.toNat_mk]
      _ = ((x : ℕ) + 1) - 1 := by rw [h_succ_val]
      _ = (x : ℕ) := by omega

/-- Exercise 3.6.12 (i), second part -/
theorem SetTheory.Set.Permutations_ih (n: ℕ):
    (Permutations (n + 1)).card = (n + 1) * (Permutations n).card := by
  let S i := (Permutations (n + 1)).specify (fun p ↦ perm_equiv_equiv p (Fin.last n) = i)

  have hSe : ∀ i, S i ≈ Permutations n := by
    intro i
    -- Hint: you might find `perm_equiv_equiv`, `Fin.succAbove`, and `Fin.predAbove` useful.
    have equiv : S i ≃ Permutations n := sorry
    use equiv, equiv.injective, equiv.surjective

  -- Hint: you might find `card_iUnion_card_disjoint` and `Permutations_finite` useful.
  sorry

/-- Exercise 3.6.12 (ii) -/
theorem SetTheory.Set.Permutations_card (n: ℕ):
    (Permutations n).card = n.factorial := by sorry

/-- Connections with Mathlib's {name}`Nat.card` -/
theorem SetTheory.Set.card_eq_nat_card {X:Set} : X.card = Nat.card X := by
  by_cases hf : X.finite
  · by_cases hz : X.card = 0
    · rw [hz]; symm
      have : X = ∅ := empty_of_card_eq_zero hf hz
      rw [this, Nat.card_eq_zero, isEmpty_iff]
      aesop
    symm
    have hc := has_card_card hf
    obtain ⟨f, hf⟩ := hc
    apply Nat.card_eq_of_equiv_fin
    exact (Equiv.ofBijective f hf).trans (Fin.Fin_equiv_Fin X.card)
  simp only [card, hf, ↓reduceDIte]; symm
  rw [Nat.card_eq_zero, ←not_finite_iff_infinite]
  right
  rwa [finite_iff_set_finite] at hf

/-- Connections with Mathlib's {name}`Set.ncard` -/
theorem SetTheory.Set.card_eq_ncard {X:Set} : X.card = (X: _root_.Set Object).ncard := by
  rw [card_eq_nat_card]
  rfl

end Chapter3
