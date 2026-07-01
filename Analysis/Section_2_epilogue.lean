import Mathlib.Tactic
import Analysis.Section_2_3

/-!
# Analysis I, Chapter 2 epilogue: Isomorphism with the Mathlib natural numbers

In this (technical) epilogue, we show that the "Chapter 2" natural numbers {name}`Chapter2.Nat` are
isomorphic in various senses to the standard natural numbers {lean}`ℕ`.

After this epilogue, {name}`Chapter2.Nat` will be deprecated, and we will instead use the standard
natural numbers {lean}`ℕ` throughout.  In particular, one should use the full Mathlib API for {lean}`ℕ` for
all subsequent chapters, in lieu of the {name}`Chapter2.Nat` API.

Filling the sorries here requires both the {name}`Chapter2.Nat` API and the Mathlib API for the standard
natural numbers {lean}`ℕ`.  As such, they are excellent exercises to prepare you for the aforementioned
transition.

In second half of this section we also give a fully axiomatic treatment of the natural numbers
via the Peano axioms. The treatment in the preceding three sections was only partially axiomatic,
because we used a specific construction {name}`Chapter2.Nat` of the natural numbers that was an inductive
type, and used that inductive type to construct a recursor.  Here, we give some exercises to show
how one can accomplish the same tasks directly from the Peano axioms, without knowing the specific
implementation of the natural numbers.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

/-- Converting a Chapter 2 natural number to a Mathlib natural number. -/
abbrev Chapter2.Nat.toNat (n : Chapter2.Nat) : ℕ := match n with
  | zero => 0
  | succ n' => n'.toNat + 1

lemma Chapter2.Nat.zero_toNat : (0 : Chapter2.Nat).toNat = 0 := rfl

lemma Chapter2.Nat.succ_toNat (n : Chapter2.Nat) : (n++).toNat = n.toNat + 1 := rfl

/-- The conversion is a bijection. Here we use the existing capability (from Section 2.1) to map
the Mathlib natural numbers to the Chapter 2 natural numbers. -/
abbrev Chapter2.Nat.equivNat : Chapter2.Nat ≃ ℕ where
  toFun := toNat
  invFun n := (n:Chapter2.Nat)
  left_inv n := by
    induction' n with n hn; rfl
    simp [hn]
    rw [succ_eq_add_one]
  right_inv n := by
    induction' n with n hn; rfl
    simp [←succ_eq_add_one, hn]

/-- The conversion preserves addition. -/
abbrev Chapter2.Nat.map_add : ∀ (n m : Nat), (n + m).toNat = n.toNat + m.toNat := by
  intro n m
  induction' n with n hn
  · rw [show zero = 0 from rfl, zero_add, _root_.Nat.zero_add]
  · rw [succ_add, succ_toNat, hn, succ_toNat, _root_.Nat.succ_add]

/-- The conversion preserves multiplication. -/
abbrev Chapter2.Nat.map_mul : ∀ (n m : Nat), (n * m).toNat = n.toNat * m.toNat := by
  intro n m
  induction' n with n hn
  · rw [show zero = (0 : Nat) from rfl, zero_mul, zero_toNat, _root_.Nat.zero_mul]
  · rw [succ_mul, map_add, hn, succ_toNat, _root_.Nat.succ_mul]

/-- The conversion preserves order. -/
abbrev Chapter2.Nat.map_le_map_iff : ∀ {n m : Nat}, n.toNat ≤ m.toNat ↔ n ≤ m := by
  intro n m
  constructor
  · intro h
    rcases _root_.Nat.le.dest h with ⟨k, hk⟩
    have h_inj : Function.Injective (toNat : Nat → ℕ) := equivNat.injective
    have h_eq : (n + (k : Nat)).toNat = m.toNat := by
      calc
        (n + (k : Nat)).toNat = n.toNat + ((k : Nat).toNat) := map_add _ _
        _ = n.toNat + k := by
          simpa using congrArg (fun x => n.toNat + x) (equivNat.right_inv k)
        _ = m.toNat := by rw [← hk]
    have h_eq' : n + (k : Nat) = m := h_inj h_eq
    rw [← h_eq']
    exact ⟨k, rfl⟩
  · intro h
    rcases h with ⟨a, h⟩
    rw [h, map_add]
    exact _root_.Nat.le_add_right _ _

abbrev Chapter2.Nat.equivNat_ordered_ring : Chapter2.Nat ≃+*o ℕ where
  toEquiv := equivNat
  map_add' := map_add
  map_mul' := map_mul
  map_le_map_iff' := map_le_map_iff

/-- The conversion preserves exponentiation. -/
lemma Chapter2.Nat.pow_eq_pow (n m : Chapter2.Nat) :
    n.toNat ^ m.toNat = (n^m).toNat := by
  induction' m with m ih
  · simp
  · rw [succ_toNat, _root_.Nat.pow_succ, pow_succ, map_mul, ih]


/-- The Peano axioms for an abstract type {name}`Nat` -/
@[ext]
structure PeanoAxioms where
  Nat : Type
  zero : Nat -- Axiom 2.1
  succ : Nat → Nat -- Axiom 2.2
  succ_ne : ∀ n : Nat, succ n ≠ zero -- Axiom 2.3
  succ_cancel : ∀ {n m : Nat}, succ n = succ m → n = m -- Axiom 2.4
  induction : ∀ (P : Nat → Prop),
    P zero → (∀ n : Nat, P n → P (succ n)) → ∀ n : Nat, P n -- Axiom 2.5

namespace PeanoAxioms

/-- The Chapter 2 natural numbers obey the Peano axioms. -/
def Chapter2_Nat : PeanoAxioms where
  Nat := Chapter2.Nat
  zero := Chapter2.Nat.zero
  succ := Chapter2.Nat.succ
  succ_ne := Chapter2.Nat.succ_ne
  succ_cancel := Chapter2.Nat.succ_cancel
  induction := Chapter2.Nat.induction

/-- The Mathlib natural numbers obey the Peano axioms. -/
def Mathlib_Nat : PeanoAxioms where
  Nat := ℕ
  zero := 0
  succ := Nat.succ
  succ_ne := Nat.succ_ne_zero
  succ_cancel := Nat.succ_inj.mp
  induction _ := Nat.rec

/-- One can map the Mathlib natural numbers into any other structure obeying the Peano axioms. -/
abbrev natCast (P : PeanoAxioms) : ℕ → P.Nat := fun n ↦ match n with
  | Nat.zero => P.zero
  | Nat.succ n => P.succ (natCast P n)

/-- One can start the proof here with {syntax tactic}`unfold Function.Injective`, although it is not strictly necessary. -/
theorem natCast_injective (P : PeanoAxioms) : Function.Injective P.natCast := by
  intro x y h
  induction' x with x ih generalizing y
  · cases' y with y
    · rfl
    · exfalso
      apply P.succ_ne (P.natCast y)
      simpa [natCast] using h.symm
  · cases' y with y
    · exfalso
      apply P.succ_ne (P.natCast x)
      simpa [natCast] using h
    · apply congrArg Nat.succ
      apply ih
      apply P.succ_cancel
      simpa [natCast] using h

/-- One can start the proof here with {syntax tactic}`unfold Function.Surjective`, although it is not strictly necessary. -/
theorem natCast_surjective (P : PeanoAxioms) : Function.Surjective P.natCast := by
  intro p
  have h := P.induction (λ q => ∃ n : ℕ, P.natCast n = q) ⟨0, rfl⟩ (by
    intro q hq
    rcases hq with ⟨n, hn⟩
    exact ⟨Nat.succ n, by simp [natCast, hn]⟩) p
  exact h

/-- The notion of an equivalence between two structures obeying the Peano axioms.
    The symbol {kw (of := «term_≃_»)}`≃` is an alias for Mathlib's {name}`Equiv` class; for instance {lean}`P.Nat ≃ Q.Nat` is
    an alias for {lean}`_root_.Equiv P.Nat Q.Nat`. -/
class Equiv (P Q : PeanoAxioms) where
  equiv : P.Nat ≃ Q.Nat
  equiv_zero : equiv P.zero = Q.zero
  equiv_succ : ∀ n : P.Nat, equiv (P.succ n) = Q.succ (equiv n)

/-- This exercise will require application of Mathlib's API for the {name}`Equiv` class.
    Some of this API can be invoked automatically via the {tactic}`simp` tactic. -/
abbrev Equiv.symm {P Q: PeanoAxioms} (equiv : Equiv P Q) : Equiv Q P where
  equiv := equiv.equiv.symm
  equiv_zero := by
    calc
      equiv.equiv.symm Q.zero = equiv.equiv.symm (equiv.equiv P.zero) := by rw [equiv.equiv_zero]
      _ = P.zero := by simp
  equiv_succ n := by
    have h := congrArg equiv.equiv.symm (equiv.equiv_succ (equiv.equiv.symm n))
    simpa using h.symm

/-- This exercise will require application of Mathlib's API for the {name}`Equiv` class.
    Some of this API can be invoked automatically via the {tactic}`simp` tactic. -/
abbrev Equiv.trans {P Q R: PeanoAxioms} (equiv1 : Equiv P Q) (equiv2 : Equiv Q R) : Equiv P R where
  equiv := equiv1.equiv.trans equiv2.equiv
  equiv_zero := by
    simp [equiv1.equiv_zero, equiv2.equiv_zero]
  equiv_succ n := by
    simp [equiv1.equiv_succ n, equiv2.equiv_succ (equiv1.equiv n)]

/-- Useful Mathlib tools for inverting bijections include {name}`Function.surjInv` and {name}`Function.invFun`. -/
noncomputable abbrev Equiv.fromNat (P : PeanoAxioms) : Equiv Mathlib_Nat P where
  equiv := Equiv.ofBijective P.natCast ⟨natCast_injective P, natCast_surjective P⟩
  equiv_zero := by
    rw [Equiv.ofBijective_apply]; rfl
  equiv_succ n := by
    rw [Equiv.ofBijective_apply]; rfl

/-- The task here is to establish that any two structures obeying the Peano axioms are equivalent. -/
noncomputable abbrev Equiv.mk' (P Q : PeanoAxioms) : Equiv P Q :=
  (Equiv.symm (Equiv.fromNat P)).trans (Equiv.fromNat Q)

/-- There is only one equivalence between any two structures obeying the Peano axioms. -/
theorem Equiv.uniq {P Q : PeanoAxioms} (equiv1 equiv2 : PeanoAxioms.Equiv P Q) :
    equiv1 = equiv2 := by
  obtain ⟨equiv1, equiv_zero1, equiv_succ1⟩ := equiv1
  obtain ⟨equiv2, equiv_zero2, equiv_succ2⟩ := equiv2
  congr
  ext n
  apply P.induction (λ n => equiv1 n = equiv2 n)
  · rw [equiv_zero1, equiv_zero2]
  · intro n ih
    rw [equiv_succ1 n, equiv_succ2 n, ih]

/-- A sample result: recursion is well-defined on any structure obeying the Peano axioms-/
theorem Nat.recurse_uniq {P : PeanoAxioms} (f: P.Nat → P.Nat → P.Nat) (c: P.Nat) :
    ∃! (a: P.Nat → P.Nat), a P.zero = c ∧ ∀ n, a (P.succ n) = f n (a n) := by
  let E : ℕ ≃ P.Nat := (Equiv.fromNat P).equiv
  let a' : ℕ → P.Nat := Nat.rec c (λ k ih => f (E k) ih)
  have ha'_zero : a' 0 = c := rfl
  have ha'_succ : ∀ k : ℕ, a' (k.succ) = f (E k) (a' k) := λ k => rfl
  let a : P.Nat → P.Nat := a' ∘ E.symm
  have hE0 : E (0 : ℕ) = P.zero := by
    simpa [Mathlib_Nat] using (Equiv.fromNat P).equiv_zero
  have ha_zero : a P.zero = c := by
    dsimp [a]
    calc
      a' (E.symm P.zero) = a' (E.symm (E 0)) := by rw [hE0]
      _ = a' 0 := by simp
      _ = c := ha'_zero
  have ha_succ : ∀ n : P.Nat, a (P.succ n) = f n (a n) := by
    intro n
    dsimp [a]
    have h_succ' : E ((E.symm n).succ) = P.succ n := by
      have h_temp := (Equiv.fromNat P).equiv_succ (E.symm n)
      calc
        E ((E.symm n).succ) = (Equiv.fromNat P).equiv ((E.symm n).succ) := rfl
        _ = (Equiv.fromNat P).equiv (Mathlib_Nat.succ (E.symm n)) := by simp [Mathlib_Nat]
        _ = P.succ ((Equiv.fromNat P).equiv (E.symm n)) := h_temp
        _ = P.succ (E (E.symm n)) := rfl
        _ = P.succ n := by simp
    have h_succ : E.symm (P.succ n) = (E.symm n).succ := by
      apply E.injective
      calc
        E (E.symm (P.succ n)) = P.succ n := by simp
        _ = E ((E.symm n).succ) := by rw [h_succ']
    calc
      a' (E.symm (P.succ n)) = a' ((E.symm n).succ) := by rw [h_succ]
      _ = f (E (E.symm n)) (a' (E.symm n)) := ha'_succ (E.symm n)
      _ = f n (a' (E.symm n)) := by simp
      _ = f n (a n) := rfl
  have huniq : ∀ b : P.Nat → P.Nat,
      (b P.zero = c ∧ ∀ n, b (P.succ n) = f n (b n)) → b = a := by
    intro b ⟨hb_zero, hb_succ⟩
    ext n
    apply P.induction (λ n => b n = a n)
    · rw [hb_zero, ha_zero]
    · intro n ih
      rw [hb_succ n, ha_succ n, ih]
  exact ⟨a, ⟨ha_zero, ha_succ⟩, huniq⟩

end PeanoAxioms
