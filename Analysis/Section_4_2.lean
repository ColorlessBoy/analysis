import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms

set_option doc.verso.suggestions false

/-!
# Analysis I, Section 4.2

This file is a translation of Section 4.2 of Analysis I to Lean 4.
All numbering refers to the original text.

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of the "Section 4.2" rationals, `Section_4_2.Rat`, as formal quotients `a // b` of
  integers `a b:ℤ`, up to equivalence.  (This is a quotient of a scaffolding type
  `Section_4_2.PreRat`, which consists of formal quotients without any equivalence imposed.)

- Field operations and order on these rationals, as well as an embedding of {lean}`ℕ` and {lean}`ℤ`.

- Equivalence with the Mathlib rationals {name}`_root_.Rat` (or {lean}`ℚ`), which we will use going forward.

Note: here (and in the sequel) we use Mathlib's natural numbers {lean}`ℕ` and integers {lean}`ℤ` rather than
the Chapter 2 natural numbers and Section 4.1 integers.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Section_4_2

structure PreRat where
  numerator : ℤ
  denominator : ℤ
  nonzero : denominator ≠ 0

/-- Exercise 4.2.1 -/
instance PreRat.instSetoid : Setoid PreRat where
  r a b := a.numerator * b.denominator = b.numerator * a.denominator
  iseqv := {
    refl := by intro; rfl
    symm := by intro x y h; simpa [eq_comm] using h
    trans := by
      intro x y z h1 h2
      have hden : y.denominator ≠ 0 := y.nonzero
      apply mul_right_cancel₀ hden
      calc
        x.numerator * z.denominator * y.denominator
            = x.numerator * y.denominator * z.denominator := by ring
        _ = y.numerator * x.denominator * z.denominator := by rw [h1]
        _ = y.numerator * z.denominator * x.denominator := by ring
        _ = z.numerator * y.denominator * x.denominator := by rw [h2]
        _ = z.numerator * x.denominator * y.denominator := by ring
    }

@[simp]
theorem PreRat.eq (a b c d:ℤ) (hb: b ≠ 0) (hd: d ≠ 0) :
    (⟨ a,b,hb ⟩: PreRat) ≈ ⟨ c,d,hd ⟩ ↔ a * d = c * b := by rfl

abbrev Rat := Quotient PreRat.instSetoid

/-- We give division a "junk" value of 0//1 if the denominator is zero -/
abbrev Rat.formalDiv (a b:ℤ) : Rat :=
  Quotient.mk PreRat.instSetoid (if h:b ≠ 0 then ⟨ a,b,h ⟩ else ⟨ 0, 1, by decide ⟩)

infix:100 " // " => Rat.formalDiv

/-- Definition 4.2.1 (Rationals) -/
theorem Rat.eq (a c:ℤ) {b d:ℤ} (hb: b ≠ 0) (hd: d ≠ 0): a // b = c // d ↔ a * d = c * b := by
  simp [formalDiv, hb, hd, Quotient.eq, PreRat.instSetoid]

/-- Definition 4.2.1 (Rationals) -/
theorem Rat.eq_diff (n:Rat) : ∃ a b, b ≠ 0 ∧ n = a // b := by
  apply Quotient.ind _ n; intro ⟨ a, b, h ⟩
  refine ⟨ a, b, h, ?_ ⟩
  simp [formalDiv, h]

/--
  Decidability of equality. Hint: modify the proof of {lean}`DecidableEq Int` from the previous
  section. However, because formal division handles the case of zero denominator separately, it
  may be more convenient to avoid that operation and work directly with the {name}`Quotient` API.

-/
instance Rat.decidableEq : DecidableEq Rat := by
  intro a b
  have : ∀ (n:PreRat) (m: PreRat),
      Decidable (Quotient.mk PreRat.instSetoid n = Quotient.mk PreRat.instSetoid m) := by
    intro ⟨ a,b,h1 ⟩ ⟨ c,d,h2 ⟩
    exact decidable_of_iff (a * d = c * b) ((PreRat.eq a b c d h1 h2).symm.trans (Quotient.eq).symm)
  exact Quotient.recOnSubsingleton₂ a b this

/-- Lemma 4.2.3 (Addition well-defined) -/
instance Rat.add_inst : Add Rat where
  add := Quotient.lift₂ (fun ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ ↦ (a*d+b*c) // (b*d)) (by
    intro ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ ⟨ a', b', h1' ⟩ ⟨ c', d', h2' ⟩ h3 h4
    simp_all [Quotient.eq]
    linear_combination d * d' * h3 + b * b' * h4
  )

/-- Definition 4.2.2 (Addition of rationals) -/
theorem Rat.add_eq (a c:ℤ) {b d:ℤ} (hb: b ≠ 0) (hd: d ≠ 0) :
    (a // b) + (c // d) = (a*d + b*c) // (b*d) := by
  convert Quotient.lift₂_mk _ _ _ _ <;> simp [hb, hd]

/-- Lemma 4.2.3 (Multiplication well-defined) -/
instance Rat.mul_inst : Mul Rat where
  mul := Quotient.lift₂ (fun ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ ↦ (a*c) // (b*d)) (by
    intro ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ ⟨ a', b', h1' ⟩ ⟨ c', d', h2' ⟩ h3 h4
    simp_all [Quotient.eq]
    calc
      a*c*(b'*d') = a*b'*(c*d') := by ring
      _ = a'*b*(c*d') := by rw [h3]
      _ = a'*b*(c'*d) := by rw [h4]
      _ = a'*c'*(b*d) := by ring
  )

/-- Definition 4.2.2 (Multiplication of rationals) -/
theorem Rat.mul_eq (a c:ℤ) {b d:ℤ} (hb: b ≠ 0) (hd: d ≠ 0) :
    (a // b) * (c // d) = (a*c) // (b*d) := by
  convert Quotient.lift₂_mk _ _ _ _ <;> simp [hb, hd]

/-- Lemma 4.2.3 (Negation well-defined) -/
instance Rat.neg_inst : Neg Rat where
  neg := Quotient.lift (fun ⟨ a, b, h1 ⟩ ↦ (-a) // b) (by
    intro ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ h3
    simp_all [Quotient.eq]
  )

/-- Definition 4.2.2 (Negation of rationals) -/
theorem Rat.neg_eq (a:ℤ) {b:ℤ} (hb: b ≠ 0) : - (a // b) = (-a) // b := by
  convert Quotient.lift_mk _ _ _ <;> simp [hb]

/-- Embedding the integers in the rationals -/
instance Rat.instIntCast : IntCast Rat where
  intCast a := a // 1

instance Rat.instNatCast : NatCast Rat where
  natCast n := (n:ℤ) // 1

instance Rat.instOfNat {n:ℕ} : OfNat Rat n where
  ofNat := (n:ℤ) // 1

theorem Rat.coe_Int_eq (a:ℤ) : (a:Rat) = a // 1 := rfl

theorem Rat.coe_Nat_eq (n:ℕ) : (n:Rat) = n // 1 := rfl

theorem Rat.of_Nat_eq (n:ℕ) : (ofNat(n):Rat) = (ofNat(n):Nat) // 1 := rfl

/-- natCast distributes over successor -/
theorem Rat.natCast_succ (n: ℕ) : ((n + 1: ℕ): Rat) = (n: Rat) + 1 := by
  have : 1 = 1 // 1 := rfl
  rw [Rat.coe_Nat_eq, Rat.coe_Nat_eq, this, add_eq, eq] <;> simp

/-- intCast distributes over addition -/
lemma Rat.intCast_add (a b:ℤ) : (a:Rat) + (b:Rat) = (a+b:ℤ) := by
  rw [coe_Int_eq, coe_Int_eq, coe_Int_eq, add_eq a b (by norm_num) (by norm_num)]
  rw [eq _ _ (by norm_num : (1:ℤ)*1 ≠ 0) (by norm_num : (1:ℤ) ≠ 0)]
  ring

/-- intCast distributes over multiplication -/
lemma Rat.intCast_mul (a b:ℤ) : (a:Rat) * (b:Rat) = (a*b:ℤ) := by
  rw [coe_Int_eq, coe_Int_eq, coe_Int_eq, mul_eq a b (by norm_num) (by norm_num)]
  rw [eq _ _ (by norm_num : (1:ℤ)*1 ≠ 0) (by norm_num : (1:ℤ) ≠ 0)]
  ring

/-- intCast commutes with negation -/
lemma Rat.intCast_neg (a:ℤ) : - (a:Rat) = (-a:ℤ) := rfl

theorem Rat.coe_Int_inj : Function.Injective (fun n:ℤ ↦ (n:Rat)) := by
  intro a b h
  have h1 : (1:ℤ) ≠ 0 := by norm_num
  simp at h
  rw [coe_Int_eq, coe_Int_eq, eq, mul_one, mul_one] at h
  exact h
  omega
  omega

/--
  Whereas the book leaves the inverse of 0 undefined, it is more convenient in Lean to assign a
  "junk" value to this inverse; we arbitrarily choose this junk value to be 0.
-/
instance Rat.instInv : Inv Rat where
  inv := Quotient.lift (fun ⟨ a, b, h1 ⟩ ↦ b // a) (by
    intro ⟨ a, b, h1 ⟩ ⟨ a', b', h1' ⟩ h
    by_cases ha : a = 0
    · subst ha
      have ha' : a' = 0 := by
        have h0 : 0 = a' * b := by simpa using h
        rcases eq_zero_or_eq_zero_of_mul_eq_zero h0.symm with (haz | hbz)
        · exact haz
        · exact absurd hbz h1
      subst ha'
      simp [formalDiv]
    · by_cases ha' : a' = 0
      · subst ha'
        have h0 : a * b' = 0 := by simpa using h
        rcases eq_zero_or_eq_zero_of_mul_eq_zero h0 with (haz | hb'z)
        · exact absurd haz ha
        · exact absurd hb'z h1'
      · simp [ha, ha', formalDiv]
        apply Quotient.sound
        simpa [PreRat.instSetoid] using calc
          b * a' = a' * b := mul_comm _ _
          _ = a * b' := by rw [← h]
          _ = b' * a := mul_comm _ _
  )

lemma Rat.inv_eq (a:ℤ) {b:ℤ} (hb: b ≠ 0) : (a // b)⁻¹ = b // a := by
  convert Quotient.lift_mk _ _ _ <;> simp [hb]

@[simp]
theorem Rat.inv_zero : (0:Rat)⁻¹ = 0 := rfl

/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.addGroup_inst : AddGroup Rat :=
AddGroup.ofLeftAxioms (by
  -- this proof is written to follow the structure of the original text.
  intro x y z
  obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
  obtain ⟨ c, d, hd, rfl ⟩ := eq_diff y
  obtain ⟨ e, f, hf, rfl ⟩ := eq_diff z
  have hbd : b*d ≠ 0 := Int.mul_ne_zero hb hd     -- can also use `observe hbd : b*d ≠ 0` here
  have hdf : d*f ≠ 0 := Int.mul_ne_zero hd hf     -- can also use `observe hdf : d*f ≠ 0` here
  have hbdf : b*d*f ≠ 0 := Int.mul_ne_zero hbd hf -- can also use `observe hbdf : b*d*f ≠ 0` here
  rw [add_eq _ _ hb hd, add_eq _ _ hbd hf, add_eq _ _ hd hf,
      add_eq _ _ hb hdf, ←mul_assoc b, eq _ _ hbdf hbdf]
  ring
)
 (by
    intro x
    obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
    calc
      (0:Rat) + (a // b) = ((0:ℤ) // 1) + (a // b) := rfl
      _ = (0 * b + 1 * a) // (1 * b) := by rw [add_eq 0 a (by norm_num) hb]
      _ = a // b := by
        rw [eq (0 * b + 1 * a) a (Int.mul_ne_zero (by norm_num : (1:ℤ) ≠ 0) hb) hb]
        simp)
  (by
    intro x
    obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
    calc
      (-(a // b)) + (a // b) = ((-a) // b) + (a // b) := by rw [neg_eq a hb]
      _ = ((-a) * b + b * a) // (b * b) := by rw [add_eq (-a) a hb hb]
      _ = 0 // (b * b) := by
        have hbb : b * b ≠ 0 := Int.mul_ne_zero hb hb
        rw [eq ((-a) * b + b * a) 0 hbb hbb]
        ring
      _ = (0:Rat) := by
        have hbb : b * b ≠ 0 := Int.mul_ne_zero hb hb
        have h1 : (1:ℤ) ≠ 0 := by norm_num
        calc
          0 // (b * b) = (0:ℤ) // 1 := (eq 0 0 hbb h1).mpr (by simp)
          _ = (0:Rat) := (coe_Int_eq 0).symm)

/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.instAddCommGroup : AddCommGroup Rat where
  add_comm := by
    intro x y
    obtain ⟨ a1, b1, hb1, rfl ⟩ := eq_diff x
    obtain ⟨ a2, b2, hb2, rfl ⟩ := eq_diff y
    have hbd : b1*b2 ≠ 0 := Int.mul_ne_zero hb1 hb2     -- can also use `observe hbd : b1*b2 ≠ 0` here
    rw [add_eq _ _ hb1 hb2, add_eq _ _ hb2 hb1, mul_comm b2 b1, mul_comm b2, mul_comm b1, add_comm]

/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.instCommMonoid : CommMonoid Rat where
  mul_comm := by
    intro x y
    obtain ⟨ a1, b1, hb1, rfl ⟩ := eq_diff x
    obtain ⟨ a2, b2, hb2, rfl ⟩ := eq_diff y
    have hbd : b1*b2 ≠ 0 := Int.mul_ne_zero hb1 hb2
    rw [mul_eq _ _ hb1 hb2, mul_eq _ _ hb2 hb1, mul_comm a1 a2, mul_comm b1 b2]
  mul_assoc := by
    intro x y z
    obtain ⟨ a1, b1, hb1, rfl ⟩ := eq_diff x
    obtain ⟨ a2, b2, hb2, rfl ⟩ := eq_diff y
    obtain ⟨ a3, b3, hb3, rfl ⟩ := eq_diff z
    have hb12 : b1*b2 ≠ 0 := Int.mul_ne_zero hb1 hb2
    have hb23 : b2*b3 ≠ 0 := Int.mul_ne_zero hb2 hb3
    have hb123 : (b1*b2)*b3 ≠ 0 := Int.mul_ne_zero hb12 hb3
    have hb1_23 : b1*(b2*b3) ≠ 0 := Int.mul_ne_zero hb1 hb23
    rw [mul_eq _ _ hb1 hb2, mul_eq _ _ hb12 hb3, mul_eq _ _ hb2 hb3, mul_eq _ _ hb1 hb23]
    rw [eq ((a1*a2)*a3) (a1*(a2*a3)) hb123 hb1_23]
    ring
  one_mul := by
    intro x
    obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
    have h1 : (1:ℤ) ≠ 0 := by norm_num
    have h1b : (1:ℤ)*b ≠ 0 := Int.mul_ne_zero h1 hb
    calc
      1 * (a // b) = ((1:ℤ) // 1) * (a // b) := rfl
      _ = (1*a) // (1*b) := by rw [mul_eq 1 a h1 hb]
      _ = a // b := by
        rw [eq (1*a) a h1b hb]
        simp
  mul_one := by
    intro x
    obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
    have h1 : (1:ℤ) ≠ 0 := by norm_num
    have hb1 : b*(1:ℤ) ≠ 0 := Int.mul_ne_zero hb h1
    calc
      (a // b) * 1 = (a // b) * ((1:ℤ) // 1) := rfl
      _ = (a*1) // (b*1) := by rw [mul_eq a 1 hb h1]
      _ = a // b := by
        rw [eq (a*1) a hb1 hb]
        simp

/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.instCommRing : CommRing Rat where
  left_distrib := by
    intro x y z
    obtain ⟨ a1, b1, hb1, rfl ⟩ := eq_diff x
    obtain ⟨ a2, b2, hb2, rfl ⟩ := eq_diff y
    obtain ⟨ a3, b3, hb3, rfl ⟩ := eq_diff z
    have hb12 : b1*b2 ≠ 0 := Int.mul_ne_zero hb1 hb2
    have hb13 : b1*b3 ≠ 0 := Int.mul_ne_zero hb1 hb3
    have hb23 : b2*b3 ≠ 0 := Int.mul_ne_zero hb2 hb3
    have hb123 : b1*(b2*b3) ≠ 0 := Int.mul_ne_zero hb1 hb23
    have hb12_13 : (b1*b2)*(b1*b3) ≠ 0 := Int.mul_ne_zero hb12 hb13
    rw [add_eq a2 a3 hb2 hb3, mul_eq a1 (a2*b3 + b2*a3) hb1 hb23,
      mul_eq a1 a2 hb1 hb2, mul_eq a1 a3 hb1 hb3, add_eq (a1*a2) (a1*a3) hb12 hb13]
    rw [eq (a1*(a2*b3 + b2*a3)) ((a1*a2)*(b1*b3) + (b1*b2)*(a1*a3)) hb123 hb12_13]
    ring
  right_distrib := by
    intro x y z
    obtain ⟨ a1, b1, hb1, rfl ⟩ := eq_diff x
    obtain ⟨ a2, b2, hb2, rfl ⟩ := eq_diff y
    obtain ⟨ a3, b3, hb3, rfl ⟩ := eq_diff z
    have hb12 : b1*b2 ≠ 0 := Int.mul_ne_zero hb1 hb2
    have hb13 : b1*b3 ≠ 0 := Int.mul_ne_zero hb1 hb3
    have hb23 : b2*b3 ≠ 0 := Int.mul_ne_zero hb2 hb3
    have hb123 : (b1*b2)*b3 ≠ 0 := Int.mul_ne_zero hb12 hb3
    have hb13_23 : (b1*b3)*(b2*b3) ≠ 0 := Int.mul_ne_zero hb13 hb23
    rw [add_eq a1 a2 hb1 hb2, mul_eq (a1*b2 + b1*a2) a3 hb12 hb3,
      mul_eq a1 a3 hb1 hb3, mul_eq a2 a3 hb2 hb3, add_eq (a1*a3) (a2*a3) hb13 hb23]
    rw [eq ((a1*b2 + b1*a2)*a3) ((a1*a3)*(b2*b3) + (b1*b3)*(a2*a3)) hb123 hb13_23]
    ring
  zero_mul := by
    intro x
    obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
    have h1 : (1:ℤ) ≠ 0 := by norm_num
    have h1b : (1:ℤ)*b ≠ 0 := Int.mul_ne_zero h1 hb
    calc
      0 * (a // b) = ((0:ℤ) // 1) * (a // b) := rfl
      _ = (0*a) // (1*b) := by rw [mul_eq 0 a h1 hb]
      _ = 0 // (1*b) := by simp
      _ = (0:ℤ) // 1 := (eq 0 0 h1b h1).mpr (by simp)
      _ = (0 : Rat) := (coe_Int_eq 0).symm
  mul_zero := by
    intro x
    obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
    have h1 : (1:ℤ) ≠ 0 := by norm_num
    have hb1 : b*(1:ℤ) ≠ 0 := Int.mul_ne_zero hb h1
    calc
      (a // b) * 0 = (a // b) * ((0:ℤ) // 1) := rfl
      _ = (a*0) // (b*1) := by rw [mul_eq a 0 hb h1]
      _ = 0 // (b*1) := by simp
      _ = (0:ℤ) // 1 := (eq 0 0 hb1 h1).mpr (by simp)
      _ = (0 : Rat) := (coe_Int_eq 0).symm
  mul_assoc := mul_assoc
  natCast_succ := natCast_succ

instance Rat.instRatCast : RatCast Rat where
  ratCast q := q.num // q.den

theorem Rat.ratCast_inj : Function.Injective (fun n:ℚ ↦ (n:Rat)) := by
  intro n m h
  have hnz : (n.den : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr n.den_nz
  have hmz : (m.den : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr m.den_nz
  have h' : n.num // (n.den : ℤ) = m.num // (m.den : ℤ) := by
    simpa [Rat.instRatCast] using h
  rw [Rat.eq _ _ hnz hmz] at h'
  exact (Rat.eq_iff_mul_eq_mul (p := n) (q := m)).mpr h'

theorem Rat.coe_Rat_eq (a:ℤ) {b:ℤ} (hb: b ≠ 0) : (a/b:ℚ) = a // b := by
  set q := (a/b:ℚ)
  set num :ℤ := q.num
  set den :ℤ := (q.den:ℤ)
  have hden : den ≠ 0 := by simp [den, q.den_nz]
  change num // den = a // b
  rw [eq _ _ hden hb]
  qify
  have hq : num / den = q := Rat.num_div_den q
  rwa [div_eq_div_iff] at hq <;> simp [hden, hb]

/-- Default definition of division -/
instance Rat.instDivInvMonoid : DivInvMonoid Rat where

theorem Rat.div_eq (q r:Rat) : q/r = q * r⁻¹ := by rfl

instance Rat.instNNRatCast : NNRatCast Rat where
  nnratCast := fun q => ((q : ℚ) : Rat)

lemma Rat.nnratCast_def' (q : ℚ≥0) : (q : Rat) = (q.num : Rat) / (q.den : Rat) := by
  calc
    (q : Rat) = ((q : ℚ) : Rat) := rfl
    _ = ((q : ℚ).num : Rat) / ((q : ℚ).den : Rat) := by
      have h1 : (1 : ℤ) ≠ 0 := by norm_num
      have hden : ((q : ℚ).den : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (q : ℚ).den_nz
      calc
        ((q : ℚ) : Rat) = (q : ℚ).num // (q : ℚ).den := rfl
        _ = ((q : ℚ).num * 1) // (1 * (q : ℚ).den) := by simp
        _ = ((q : ℚ).num // 1) * (1 // (q : ℚ).den) := by
          rw [Rat.mul_eq ((q : ℚ).num : ℤ) 1 h1 hden]
        _ = ((q : ℚ).num : Rat) * (((q : ℚ).den : Rat)⁻¹) := by
          simp [Rat.coe_Int_eq, Rat.coe_Nat_eq, Rat.inv_eq ((q : ℚ).den : ℤ) h1]
        _ = ((q : ℚ).num : Rat) / ((q : ℚ).den : Rat) := rfl
    _ = (q.num : Rat) / (q.den : Rat) := by
      simp [NNRat.num_coe, NNRat.den_coe]

/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.instField : Field Rat where
  exists_pair_ne := by
    have h1 : (1 : ℤ) ≠ 0 := by norm_num
    refine ⟨0, 1, ?_⟩
    intro h
    have := ((Rat.eq (0 : ℤ) (1 : ℤ) h1 h1).mp h)
    norm_num at this
  mul_inv_cancel := by
    intro x hx0
    obtain ⟨a, b, hb, rfl⟩ := Rat.eq_diff x
    have ha : a ≠ 0 := by
      intro hazero
      apply hx0
      have hzero : (0 : Rat) = (0 : ℤ) // 1 := rfl
      rw [hzero, Rat.eq a 0 hb (by norm_num : (1 : ℤ) ≠ 0)]
      simp [hazero]
    have h1 : (1 : ℤ) ≠ 0 := by norm_num
    have hab : a*b ≠ 0 := mul_ne_zero ha hb
    calc
      (a // b) * ((a // b)⁻¹) = (a // b) * (b // a) := by rw [Rat.inv_eq a hb]
      _ = (a*b) // (b*a) := by rw [Rat.mul_eq a b hb ha]
      _ = (a*b) // (a*b) := by rw [mul_comm b a]
      _ = (1 : ℤ) // 1 := by
        rw [Rat.eq (a*b) 1 hab h1]
        simp
      _ = (1 : Rat) := rfl
  inv_zero := rfl
  ratCast_def := by
    intro q
    have h1 : (1 : ℤ) ≠ 0 := by norm_num
    have hden : (q.den : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
    calc
      (q : Rat) = q.num // q.den := rfl
      _ = (q.num * 1) // (1 * q.den) := by simp
      _ = (q.num // 1) * (1 // q.den) := by rw [Rat.mul_eq q.num 1 h1 hden]
      _ = (q.num : Rat) * ((q.den : Rat)⁻¹) := by
        simp [Rat.coe_Int_eq, Rat.coe_Nat_eq, Rat.inv_eq (q.den : ℤ) h1]
      _ = (q.num : Rat) / (q.den : Rat) := rfl
  nnratCast_def := Rat.nnratCast_def'
  qsmul := (fun a x => (a : Rat) * x)
  qsmul_def := by
    intro a x
    rfl
  nnqsmul := (fun a x => ((a : ℚ) : Rat) * x)
  nnqsmul_def := by
    intro a x
    rfl

example : (3//4) / (5//6) = 9 // 10 := by
  calc
    (3//4) / (5//6) = (3//4) * ((5//6)⁻¹) := rfl
    _ = (3//4) * (6//5) := by rw [Rat.inv_eq (5 : ℤ) (by norm_num : (6 : ℤ) ≠ 0)]
    _ = (3*6) // (4*5) := by
      rw [Rat.mul_eq (3 : ℤ) (6 : ℤ) (by norm_num : (4 : ℤ) ≠ 0) (by norm_num : (5 : ℤ) ≠ 0)]
    _ = 18 // 20 := by norm_num
    _ = 9 // 10 := by
      rw [Rat.eq (18 : ℤ) (9 : ℤ) (by norm_num : (20 : ℤ) ≠ 0) (by norm_num : (10 : ℤ) ≠ 0)]
      norm_num

/-- Definition of subtraction -/
theorem Rat.sub_eq (a b:Rat) : a - b = a + (-b) := by rfl

def Rat.coe_int_hom : ℤ →+* Rat where
  toFun n := (n:Rat)
  map_zero' := rfl
  map_one' := rfl
  map_add' := by sorry
  map_mul' := by sorry

/-- Definition 4.2.6 (positivity) -/
def Rat.isPos (q:Rat) : Prop := ∃ a b:ℤ, a > 0 ∧ b > 0 ∧ q = a/b

/-- Definition 4.2.6 (negativity) -/
def Rat.isNeg (q:Rat) : Prop := ∃ r:Rat, r.isPos ∧ q = -r

/-- Lemma 4.2.7 (trichotomy of rationals) / Exercise 4.2.4 -/
theorem Rat.trichotomous (x:Rat) : x = 0 ∨ x.isPos ∨ x.isNeg := by sorry

/-- Lemma 4.2.7 (trichotomy of rationals) / Exercise 4.2.4 -/
theorem Rat.not_zero_and_pos (x:Rat) : ¬(x = 0 ∧ x.isPos) := by sorry

/-- Lemma 4.2.7 (trichotomy of rationals) / Exercise 4.2.4 -/
theorem Rat.not_zero_and_neg (x:Rat) : ¬(x = 0 ∧ x.isNeg) := by sorry

/-- Lemma 4.2.7 (trichotomy of rationals) / Exercise 4.2.4 -/
theorem Rat.not_pos_and_neg (x:Rat) : ¬(x.isPos ∧ x.isNeg) := by sorry

/-- Definition 4.2.8 (Ordering of the rationals) -/
instance Rat.instLT : LT Rat where
  lt x y := (x-y).isNeg

/-- Definition 4.2.8 (Ordering of the rationals) -/
instance Rat.instLE : LE Rat where
  le x y := (x < y) ∨ (x = y)

theorem Rat.lt_iff (x y:Rat) : x < y ↔ (x-y).isNeg := by rfl
theorem Rat.le_iff (x y:Rat) : x ≤ y ↔ (x < y) ∨ (x = y) := by rfl

theorem Rat.gt_iff (x y:Rat) : x > y ↔ (x-y).isPos := by sorry
theorem Rat.ge_iff (x y:Rat) : x ≥ y ↔ (x > y) ∨ (x = y) := by sorry

/-- Proposition 4.2.9(a) (order trichotomy) / Exercise 4.2.5 -/
theorem Rat.trichotomous' (x y:Rat) : x > y ∨ x < y ∨ x = y := by sorry

/-- Proposition 4.2.9(a) (order trichotomy) / Exercise 4.2.5 -/
theorem Rat.not_gt_and_lt (x y:Rat) : ¬ (x > y ∧ x < y):= by sorry

/-- Proposition 4.2.9(a) (order trichotomy) / Exercise 4.2.5 -/
theorem Rat.not_gt_and_eq (x y:Rat) : ¬ (x > y ∧ x = y):= by sorry

/-- Proposition 4.2.9(a) (order trichotomy) / Exercise 4.2.5 -/
theorem Rat.not_lt_and_eq (x y:Rat) : ¬ (x < y ∧ x = y):= by sorry

/-- Proposition 4.2.9(b) (order is anti-symmetric) / Exercise 4.2.5 -/
theorem Rat.antisymm (x y:Rat) : x < y ↔ y > x := by sorry

/-- Proposition 4.2.9(c) (order is transitive) / Exercise 4.2.5 -/
theorem Rat.lt_trans {x y z:Rat} (hxy: x < y) (hyz: y < z) : x < z := by sorry

/-- Proposition 4.2.9(d) (addition preserves order) / Exercise 4.2.5 -/
theorem Rat.add_lt_add_right {x y:Rat} (z:Rat) (hxy: x < y) : x + z < y + z := by sorry

/-- Proposition 4.2.9(e) (positive multiplication preserves order) / Exercise 4.2.5 -/
theorem Rat.mul_lt_mul_right {x y z:Rat} (hxy: x < y) (hz: z.isPos) : x * z < y * z := by sorry

/-- (Not from textbook) Establish the decidability of this order. -/
instance Rat.decidableRel : DecidableRel (· ≤ · : Rat → Rat → Prop) := by
  intro n m
  have : ∀ (n:PreRat) (m: PreRat),
      Decidable (Quotient.mk PreRat.instSetoid n ≤ Quotient.mk PreRat.instSetoid m) := by
    intro ⟨ a,b,hb ⟩ ⟨ c,d,hd ⟩
    -- at this point, the goal is morally `Decidable(a//b ≤ c//d)`, but there are technical
    -- issues due to the junk value of formal division when the denominator vanishes.
    -- It may be more convenient to avoid formal division and work directly with `Quotient.mk`.
    cases (0:ℤ).decLe (b*d) with
      | isTrue hbd =>
        cases (a * d).decLe (b * c) with
          | isTrue h =>
            apply isTrue
            sorry
          | isFalse h =>
            apply isFalse
            sorry
      | isFalse hbd =>
        cases (b * c).decLe (a * d) with
          | isTrue h =>
            apply isTrue
            sorry
          | isFalse h =>
            apply isFalse
            sorry
  exact Quotient.recOnSubsingleton₂ n m this

/-- (Not from textbook) Rat has the structure of a linear ordering. -/
instance Rat.instLinearOrder : LinearOrder Rat where
  le_refl := sorry
  le_trans := sorry
  lt_iff_le_not_ge := sorry
  le_antisymm := sorry
  le_total := sorry
  toDecidableLE := decidableRel

/-- (Not from textbook) Rat has the structure of a strict ordered ring. -/
instance Rat.instIsStrictOrderedRing : IsStrictOrderedRing Rat where
  add_le_add_left := by sorry
  add_le_add_right := by sorry
  mul_lt_mul_of_pos_left := by sorry
  mul_lt_mul_of_pos_right := by sorry
  le_of_add_le_add_left := by sorry
  zero_le_one := by sorry

/-- Exercise 4.2.6 -/
theorem Rat.mul_lt_mul_right_of_neg (x y z:Rat) (hxy: x < y) (hz: z.isNeg) : x * z > y * z := by
  sorry


/--
  Not in textbook: create an equivalence between Rat and ℚ. This requires some familiarity with
  the API for Mathlib's version of the rationals.
-/
abbrev Rat.equivRat : Rat ≃ ℚ where
  toFun := Quotient.lift (fun ⟨ a, b, h ⟩ ↦ a / b) (by
    sorry)
  invFun := fun n: ℚ ↦ (n:Rat)
  left_inv n := sorry
  right_inv n := sorry

/-- Not in textbook: equivalence preserves order -/
abbrev Rat.equivRat_order : Rat ≃o ℚ where
  toEquiv := equivRat
  map_rel_iff' := by sorry

/-- Not in textbook: equivalence preserves ring operations -/
abbrev Rat.equivRat_ring : Rat ≃+* ℚ where
  toEquiv := equivRat
  map_add' := by sorry
  map_mul' := by sorry

/--
  (Not from textbook) The textbook rationals are isomorphic (as a field) to the Mathlib rationals.
-/
def Rat.equivRat_ring_symm : ℚ ≃+* Rat := Rat.equivRat_ring.symm

end Section_4_2
