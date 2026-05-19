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
  map_add' := by
    intro n m
    rw [← intCast_add n m]
  map_mul' := by
    intro n m
    rw [← intCast_mul n m]

/-- Definition 4.2.6 (positivity) -/
def Rat.isPos (q:Rat) : Prop := ∃ a b:ℤ, a > 0 ∧ b > 0 ∧ q = a/b

/-- Definition 4.2.6 (negativity) -/
def Rat.isNeg (q:Rat) : Prop := ∃ r:Rat, r.isPos ∧ q = -r

lemma Rat.div_eq_formalDiv (a : ℤ) {b : ℤ} (hb : b ≠ 0) : (a : Rat) / (b : Rat) = a // b := by
  calc
    (a : Rat) / (b : Rat) = (a : Rat) * ((b : Rat)⁻¹) := rfl
    _ = (a // 1) * ((b // 1)⁻¹) := by simp [coe_Int_eq]
    _ = (a // 1) * (1 // b) := by rw [inv_eq (b : ℤ) (by norm_num : (1 : ℤ) ≠ 0)]
    _ = (a*1) // (1*b) := by rw [mul_eq (a : ℤ) 1 (by norm_num : (1 : ℤ) ≠ 0) hb]
    _ = a // b := by simp

/-- Lemma 4.2.7 (trichotomy of rationals) / Exercise 4.2.4 -/
theorem Rat.trichotomous (x:Rat) : x = 0 ∨ x.isPos ∨ x.isNeg := by
  obtain ⟨a, b, hb, rfl⟩ := Rat.eq_diff x
  by_cases ha0 : a = 0
  · left
    apply (Rat.eq a 0 hb (by norm_num : (1 : ℤ) ≠ 0)).mpr
    simp [ha0]
  · have ha0' : a ≠ 0 := ha0
    by_cases ha_pos : a > 0
    · by_cases hb_pos : b > 0
      · right; left
        refine ⟨a, b, ha_pos, hb_pos, ?_⟩
        symm; exact Rat.div_eq_formalDiv a hb
      · have hb_neg : b < 0 := by omega
        right; right
        have hnegb_pos : -b > 0 := by omega
        refine ⟨a // (-b), ?_, ?_⟩
        · refine ⟨a, -b, ha_pos, hnegb_pos, ?_⟩
          symm; exact Rat.div_eq_formalDiv a (by omega : -b ≠ 0)
        · calc
            a // b = (-a) // (-b) := by
              rw [Rat.eq a (-a) hb (by omega : -b ≠ 0)]
              ring
            _ = -(a // (-b)) := by rw [← Rat.neg_eq a (by omega : -b ≠ 0)]
    · have ha_neg : a < 0 := by omega
      by_cases hb_pos : b > 0
      · right; right
        have hneg_a_pos : -a > 0 := by omega
        refine ⟨(-a) // b, ?_, ?_⟩
        · refine ⟨-a, b, hneg_a_pos, hb_pos, ?_⟩
          symm; exact Rat.div_eq_formalDiv (-a) hb
        · have hneg : -((-a) // b) = a // b := by
            calc
              -((-a) // b) = (-(-a)) // b := Rat.neg_eq (-a) hb
              _ = a // b := by simp
          symm; exact hneg
      · have hb_neg : b < 0 := by omega
        right; left
        have hneg_a_pos : -a > 0 := by omega
        have hneg_b_pos : -b > 0 := by omega
        refine ⟨-a, -b, hneg_a_pos, hneg_b_pos, ?_⟩
        calc
          a // b = (-a) // (-b) := by
            rw [Rat.eq a (-a) hb (by omega : -b ≠ 0)]
            ring
          _ = (-a : Rat) / (-b : Rat) := by
            symm; exact Rat.div_eq_formalDiv (-a) (by omega : -b ≠ 0)

/-- Lemma 4.2.7 (trichotomy of rationals) / Exercise 4.2.4 -/
theorem Rat.not_zero_and_pos (x:Rat) : ¬(x = 0 ∧ x.isPos) := by
  rintro ⟨hx, ⟨a, b, ha, hb, h⟩⟩
  have hb_ne : b ≠ 0 := by omega
  have h_eq : a // b = (0 : Rat) := by
    calc
      a // b = (a : Rat) / (b : Rat) := by symm; exact Rat.div_eq_formalDiv a hb_ne
      _ = x := by symm; exact h
      _ = 0 := hx
  have hzero : a * (1 : ℤ) = (0 : ℤ) * b :=
    ((Rat.eq a 0 hb_ne (by norm_num : (1 : ℤ) ≠ 0)).mp h_eq)
  simp at hzero
  omega

/-- Lemma 4.2.7 (trichotomy of rationals) / Exercise 4.2.4 -/
theorem Rat.not_zero_and_neg (x:Rat) : ¬(x = 0 ∧ x.isNeg) := by
  rintro ⟨hx, ⟨r, hr, hx'⟩⟩
  have hzero : r = 0 := by
    calc
      r = -(-r) := by simp
      _ = -x := by rw [hx']
      _ = -(0 : Rat) := by rw [hx]
      _ = 0 := by simp
  exact not_zero_and_pos r ⟨hzero, hr⟩

/-- Lemma 4.2.7 (trichotomy of rationals) / Exercise 4.2.4 -/
theorem Rat.not_pos_and_neg (x:Rat) : ¬(x.isPos ∧ x.isNeg) := by
  rintro ⟨hpos, hneg⟩
  rcases hpos with ⟨a, b, ha, hb, hx⟩
  rcases hneg with ⟨r, hr, hx'⟩
  have hb_ne : b ≠ 0 := by omega
  have h_eq : a // b = -r := by
    calc
      a // b = (a : Rat) / (b : Rat) := by symm; exact Rat.div_eq_formalDiv a hb_ne
      _ = x := hx.symm
      _ = -r := hx'
  rcases hr with ⟨c, d, hc, hd, hr_eq⟩
  have hd_ne : d ≠ 0 := by omega
  have h_eq2 : r = c // d := by
    calc
      r = (c : Rat) / (d : Rat) := hr_eq
      _ = c // d := Rat.div_eq_formalDiv c hd_ne
  have h_sum : a // b + c // d = 0 := by
    calc
      a // b + c // d = (-r) + r := by rw [h_eq, h_eq2]
      _ = 0 := by simp
  rw [add_eq a c hb_ne hd_ne] at h_sum
  have hbd_ne : b*d ≠ 0 := mul_ne_zero hb_ne hd_ne
  have hzero : (a*d + b*c) * (1 : ℤ) = (0 : ℤ) * (b*d) :=
    ((Rat.eq (a*d + b*c) 0 hbd_ne (by norm_num : (1 : ℤ) ≠ 0)).mp h_sum)
  simp at hzero
  have hpos_sum : a*d + b*c > 0 := by nlinarith
  nlinarith

/-- Definition 4.2.8 (Ordering of the rationals) -/
instance Rat.instLT : LT Rat where
  lt x y := (x-y).isNeg

/-- Definition 4.2.8 (Ordering of the rationals) -/
instance Rat.instLE : LE Rat where
  le x y := (x < y) ∨ (x = y)

theorem Rat.lt_iff (x y:Rat) : x < y ↔ (x-y).isNeg := by rfl
theorem Rat.le_iff (x y:Rat) : x ≤ y ↔ (x < y) ∨ (x = y) := by rfl

lemma Rat.pos_to_neg (x y: Rat) : (x - y).isPos ↔ (y - x).isNeg := by
    constructor
    · rintro ⟨a, b, ha, hb, h⟩
      have hb_ne : b ≠ 0 := by omega
      refine ⟨a // b, ⟨a, b, ha, hb, (Rat.div_eq_formalDiv a hb_ne).symm⟩, ?_⟩
      calc
        y - x = -(x - y) := (neg_sub x y).symm
        _ = -((a : Rat) / b) := by rw [h]
        _ = -(a // b) := by rw [Rat.div_eq_formalDiv a hb_ne]
    · rintro ⟨r, ⟨ra, rb, ⟨hr1, hr2, hr3⟩⟩, h⟩
      refine ⟨ra, rb, hr1, hr2, ?_⟩
      calc
        x - y = -(y - x) := (neg_sub y x).symm
        _ = -(-r) := by rw [h]
        _ = r := by simp
        _ = ra / rb := hr3

lemma Rat.add_pos_pos (r s: Rat) (hr: r.isPos) (hs: s.isPos) : (r+s).isPos := by
  rcases hr with ⟨a, b, ha, hb, hr_eq⟩
  rcases hs with ⟨c, d, hc, hd, hs_eq⟩
  have hb_ne : b ≠ 0 := by omega
  have hd_ne : d ≠ 0 := by omega
  have hbd_ne : b*d ≠ 0 := mul_ne_zero hb_ne hd_ne
  refine ⟨a*d + b*c, b*d, by nlinarith, by nlinarith, ?_⟩
  rw [hr_eq, hs_eq, Rat.div_eq_formalDiv a hb_ne, Rat.div_eq_formalDiv c hd_ne,
    Rat.add_eq a c hb_ne hd_ne, ← Rat.div_eq_formalDiv (a*d + b*c) hbd_ne]

lemma Rat.mul_pos_pos (r s: Rat) (hr: r.isPos) (hs: s.isPos) : (r*s).isPos := by
  rcases hr with ⟨a, b, ha, hb, hr_eq⟩
  rcases hs with ⟨c, d, hc, hd, hs_eq⟩
  have hb_ne : b ≠ 0 := by omega
  have hd_ne : d ≠ 0 := by omega
  have hbd_ne : b*d ≠ 0 := mul_ne_zero hb_ne hd_ne
  refine ⟨a*c, b*d, by nlinarith, by nlinarith, ?_⟩
  rw [hr_eq, hs_eq, Rat.div_eq_formalDiv a hb_ne, Rat.div_eq_formalDiv c hd_ne,
    Rat.mul_eq a c hb_ne hd_ne, ← Rat.div_eq_formalDiv (a*c) hbd_ne]

lemma Rat.neg_pos (r: Rat) (hr: r.isPos) : (-r).isNeg := ⟨r, hr, rfl⟩

theorem Rat.gt_iff (x y:Rat) : x > y ↔ (x-y).isPos := by
  rw [Rat.pos_to_neg]
  rfl

theorem Rat.ge_iff (x y:Rat) : x ≥ y ↔ (x > y) ∨ (x = y) := by
  have : x ≥ y ↔ (y - x).isNeg ∨ (y = x) := by rfl
  rw [this]
  rw [eq_comm, gt_iff, pos_to_neg]

/-- Proposition 4.2.9(a) (order trichotomy) / Exercise 4.2.5 -/
theorem Rat.trichotomous' (x y:Rat) : x > y ∨ x < y ∨ x = y := by
  rw [gt_iff, lt_iff]
  rcases Rat.trichotomous (x-y) with h | h | h
  · refine Or.inr (Or.inr ?_)
    exact eq_of_sub_eq_zero h
  exact Or.inl h
  exact Or.inr (Or.inl h)

/-- Proposition 4.2.9(a) (order trichotomy) / Exercise 4.2.5 -/
theorem Rat.not_gt_and_lt (x y:Rat) : ¬ (x > y ∧ x < y) := by
  rintro ⟨hgt, hlt⟩
  rw [gt_iff] at hgt
  exact not_pos_and_neg (x-y) ⟨hgt, hlt⟩

/-- Proposition 4.2.9(a) (order trichotomy) / Exercise 4.2.5 -/
theorem Rat.not_gt_and_eq (x y:Rat) : ¬ (x > y ∧ x = y) := by
  rintro ⟨hgt, heq⟩
  rw [gt_iff] at hgt
  have hzero : x - y = 0 := by rw [heq, sub_self]
  exact not_zero_and_pos (x-y) ⟨hzero, hgt⟩

/-- Proposition 4.2.9(a) (order trichotomy) / Exercise 4.2.5 -/
theorem Rat.not_lt_and_eq (x y:Rat) : ¬ (x < y ∧ x = y) := by
  rintro ⟨hlt, heq⟩
  have hzero : x - y = 0 := by rw [heq, sub_self]
  exact not_zero_and_neg (x-y) ⟨hzero, hlt⟩

/-- Proposition 4.2.9(b) (order is anti-symmetric) / Exercise 4.2.5 -/
theorem Rat.antisymm (x y:Rat) : x < y ↔ y > x := Iff.rfl

/-- Proposition 4.2.9(c) (order is transitive) / Exercise 4.2.5 -/
theorem Rat.lt_trans {x y z:Rat} (hxy: x < y) (hyz: y < z) : x < z := by
  rw [lt_iff] at hxy hyz ⊢
  rcases hxy with ⟨r, hr, hxy'⟩
  rcases hyz with ⟨s, hs, hyz'⟩
  use r + s
  refine ⟨add_pos_pos r s hr hs, ?_⟩
  calc
    x - z = (x - y) + (y - z) := (sub_add_sub_cancel x y z).symm
    _ = -r + -s := by rw [hxy', hyz']
    _ = -(r + s) := by ring

/-- Proposition 4.2.9(d) (addition preserves order) / Exercise 4.2.5 -/
theorem Rat.add_lt_add_right {x y:Rat} (z:Rat) (hxy: x < y) : x + z < y + z := by
  rw [lt_iff] at hxy ⊢
  have : x + z - (y + z) = x - y := by ring
  rw [this]
  exact hxy

/-- Proposition 4.2.9(e) (positive multiplication preserves order) / Exercise 4.2.5 -/
theorem Rat.mul_lt_mul_right {x y z:Rat} (hxy: x < y) (hz: z.isPos) : x * z < y * z := by
  rw [lt_iff] at hxy ⊢
  rcases hxy with ⟨r, hr, hxy'⟩
  use r * z
  refine ⟨mul_pos_pos r z hr hz, ?_⟩
  calc
    x * z - y * z = (x - y) * z := by ring
    _ = (-r) * z := by rw [hxy']
    _ = -(r * z) := by ring

/-- (Not from textbook) Establish the decidability of this order. -/
instance Rat.decidableRel : DecidableRel (· ≤ · : Rat → Rat → Prop) := by
  intro n m
  have hconv : ∀ (a b : ℤ) (h : b ≠ 0),
      (Quotient.mk PreRat.instSetoid ⟨a, b, h⟩ : Rat) = a // b := by
    intro a b h; simp [formalDiv, h]

  have : ∀ (n:PreRat) (m: PreRat),
      Decidable (Quotient.mk PreRat.instSetoid n ≤ Quotient.mk PreRat.instSetoid m) := by
    intro ⟨ a,b,hb ⟩ ⟨ c,d,hd ⟩
    have hsub : a // b - c // d = (a*d - b*c) // (b*d) := by
      calc
        a // b - c // d = a // b + (-(c // d)) := rfl
        _ = a // b + (-c) // d := by rw [neg_eq c hd]
        _ = (a*d + b*(-c)) // (b*d) := by rw [add_eq a (-c) hb hd]
        _ = (a*d - b*c) // (b*d) := by ring_nf
    cases (0:ℤ).decLe (b*d) with
    | isTrue hbd0 =>
      have hbd_pos : b*d > 0 := by
        have hne : b*d ≠ 0 := mul_ne_zero hb hd
        omega
      exact decidable_of_iff (a*d ≤ b*c) (by
        constructor
        · intro h
          rcases lt_or_eq_of_le h with (hlt | heq)
          · refine Or.inl ?_
            simp [hconv a b hb, hconv c d hd, lt_iff, hsub]
            use (b*c - a*d) // (b*d)
            refine ⟨⟨b*c - a*d, b*d, by omega, hbd_pos, ?_⟩, ?_⟩
            · symm; exact Rat.div_eq_formalDiv (b*c - a*d) hbd_pos.ne.symm
            · calc
                (a*d - b*c) // (b*d) = (-(b*c - a*d)) // (b*d) := by ring_nf
                _ = -((b*c - a*d) // (b*d)) := by rw [neg_eq (b*c - a*d) hbd_pos.ne.symm]
          · refine Or.inr (by
            simp [hconv a b hb, hconv c d hd, Rat.eq a c hb hd]
            calc
              a*d = b*c := heq
              _ = c*b := mul_comm b c)
        · intro hle
          rcases hle with (hlt | heq)
          · simp [hconv a b hb, hconv c d hd, lt_iff] at hlt
            rcases hlt with ⟨r, hr, hlt'⟩
            rw [hsub] at hlt'
            by_contra! hgt
            have num_pos : a*d - b*c > 0 := by omega
            have hpos : ((a*d - b*c) // (b*d)).isPos :=
              ⟨a*d - b*c, b*d, num_pos, hbd_pos,
                (Rat.div_eq_formalDiv (a*d - b*c) hbd_pos.ne.symm).symm⟩
            have hneg : ((a*d - b*c) // (b*d)).isNeg := ⟨r, hr, hlt'⟩
            exact not_pos_and_neg ((a*d - b*c) // (b*d)) ⟨hpos, hneg⟩
          · simp [hconv a b hb, hconv c d hd] at heq
            have h_eq : a*d = c*b := (Rat.eq a c hb hd).mp heq
            have : a*d = b*c := by simpa [mul_comm] using h_eq
            omega
      )
    | isFalse hbd0 =>
      have hbd_neg : b*d < 0 := by omega
      have hden_pos : -(b*d) > 0 := by omega
      exact decidable_of_iff (b*c ≤ a*d) (by
        constructor
        · intro h
          rcases lt_or_eq_of_le h with (hlt | heq)
          · refine Or.inl ?_
            simp [hconv a b hb, hconv c d hd, lt_iff, hsub]
            use (a*d - b*c) // (-(b*d))
            refine ⟨⟨a*d - b*c, -(b*d), by omega, hden_pos, ?_⟩, ?_⟩
            · symm; exact Rat.div_eq_formalDiv (a*d - b*c) hden_pos.ne.symm
            · calc
                (a*d - b*c) // (b*d) = (-(a*d - b*c)) // (-(b*d)) := by
                  rw [Rat.eq (a*d - b*c) (-(a*d - b*c)) hbd_neg.ne hden_pos.ne.symm]
                  ring
                _ = -((a*d - b*c) // (-(b*d))) := by
                  rw [neg_eq (a*d - b*c) hden_pos.ne.symm]
          · refine Or.inr (by
            simp [hconv a b hb, hconv c d hd, Rat.eq a c hb hd]
            calc
              a*d = b*c := heq.symm
              _ = c*b := mul_comm b c)
        · intro hle
          rcases hle with (hlt | heq)
          · simp [hconv a b hb, hconv c d hd, lt_iff] at hlt
            rcases hlt with ⟨r, hr, hlt'⟩
            rw [hsub] at hlt'
            by_contra! hgt
            have h_eq_raw : (a*d - b*c) // (b*d) = (-(a*d - b*c) : Rat) / (-(b*d) : Rat) := by
              calc
                (a*d - b*c) // (b*d) = (-(a*d - b*c)) // (-(b*d)) := by
                  rw [Rat.eq (a*d - b*c) (-(a*d - b*c)) hbd_neg.ne hden_pos.ne.symm]
                  ring_nf
                _ = (-(a*d - b*c) : Rat) / (-(b*d) : Rat) := by
                  simpa using (Rat.div_eq_formalDiv (-(a*d - b*c)) hden_pos.ne.symm).symm
            have hpos : ((a*d - b*c) // (b*d)).isPos :=
              ⟨-(a*d - b*c), -(b*d), by omega, hden_pos, by simpa using h_eq_raw⟩
            have hneg : ((a*d - b*c) // (b*d)).isNeg := ⟨r, hr, hlt'⟩
            exact not_pos_and_neg ((a*d - b*c) // (b*d)) ⟨hpos, hneg⟩
          · simp [hconv a b hb, hconv c d hd] at heq
            have h_eq : a*d = c*b := (Rat.eq a c hb hd).mp heq
            have : a*d = b*c := by simpa [mul_comm] using h_eq
            omega
      )
  exact Quotient.recOnSubsingleton₂ n m this

/-- (Not from textbook) Rat has the structure of a linear ordering. -/
instance Rat.instLinearOrder : LinearOrder Rat where
  le_refl := fun a => Or.inr rfl
  le_trans := by
    intro a b c h h'
    rcases h with (hlt | heq)
    · rcases h' with (hlt' | heq')
      · exact Or.inl (lt_trans hlt hlt')
      · rw [heq'] at hlt; exact Or.inl hlt
    · rw [heq]; exact h'
  lt_iff_le_not_ge := by
    intro a b
    constructor
    · intro hlt
      constructor
      · exact Or.inl hlt
      · intro hge
        rcases hge with (hgt' | heq')
        · exact Rat.not_gt_and_lt b a ⟨(Rat.antisymm _ _).mp hlt, hgt'⟩
        · have : (0 : Rat).isNeg := by
            have h_self : b < b := by
              rw [heq'.symm] at hlt
              exact hlt
            rw [lt_iff] at h_self
            simpa [sub_self] using h_self
          exact not_zero_and_neg 0 ⟨rfl, this⟩
    · rintro ⟨hle, hnge⟩
      rcases hle with (hlt | heq)
      · exact hlt
      · exfalso
        apply hnge
        exact Or.inr heq.symm
  le_antisymm := by
    intro a b h h'
    rcases h with (hlt | heq)
    · rcases h' with (hlt' | heq')
      · exact absurd ⟨(Rat.antisymm _ _).mp hlt, hlt'⟩ (Rat.not_gt_and_lt b a)
      · exact heq'.symm
    · exact heq
  le_total := by
    intro a b
    rcases Rat.trichotomous' a b with (hgt | hlt | heq)
    · exact Or.inr (Or.inl hgt)
    · exact Or.inl (Or.inl hlt)
    · exact Or.inl (Or.inr heq)
  toDecidableLE := decidableRel

lemma Rat.zero_lt_iff_isPos (x : Rat) : 0 < x ↔ x.isPos := by
  constructor
  · intro h
    rw [lt_iff] at h
    rcases h with ⟨r, hr, h_eq⟩
    have hx_eq_r : x = r := neg_injective (by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h_eq)
    rw [hx_eq_r]
    exact hr
  · intro h
    rw [lt_iff]
    refine ⟨x, h, ?_⟩
    simp

/-- (Not from textbook) Rat has the structure of a strict ordered ring. -/
instance Rat.instIsStrictOrderedRing : IsStrictOrderedRing Rat where
  add_le_add_left := by
    intro a b h c
    rcases h with (hlt | heq)
    · exact Or.inl (add_lt_add_right c hlt)
    · rw [heq]
  add_le_add_right := by
    intro a b h c
    rcases h with (hlt | heq)
    · have h_ac_bc : a + c < b + c := add_lt_add_right c hlt
      have : a + c ≤ b + c := Or.inl h_ac_bc
      simpa [add_comm] using this
    · rw [heq]
  mul_lt_mul_of_pos_left := by
    intro a ha b c hbc
    have ha_pos : a.isPos := (zero_lt_iff_isPos a).mp ha
    -- need a * b < a * c, have b < c
    simpa [mul_comm] using mul_lt_mul_right hbc ha_pos
  mul_lt_mul_of_pos_right := by
    intro c hc a b hab
    have hc_pos : c.isPos := (zero_lt_iff_isPos c).mp hc
    exact mul_lt_mul_right hab hc_pos
  le_of_add_le_add_left := by
    intro a b c h
    rcases h with (hlt | heq)
    · rw [lt_iff] at hlt
      have : (a + b) - (a + c) = b - c := by ring
      rw [this] at hlt
      exact Or.inl (by rw [lt_iff]; exact hlt)
    · exact Or.inr (add_left_cancel heq)
  zero_le_one := by
    refine Or.inl ?_
    rw [zero_lt_iff_isPos]
    refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
    calc
      (1 : Rat) = 1 // 1 := rfl
      _ = (1 : ℤ) / (1 : ℤ) := (Rat.div_eq_formalDiv 1 (by norm_num : (1 : ℤ) ≠ 0)).symm

/-- Exercise 4.2.6 -/
theorem Rat.mul_lt_mul_right_of_neg (x y z:Rat) (hxy: x < y) (hz: z.isNeg) : x * z > y * z := by
  rw [gt_iff]
  rw [lt_iff] at hxy
  rcases hxy with ⟨s, hs_pos, hxy_eq⟩
  rcases hz with ⟨r, hr_pos, hz_eq⟩
  have : x * z - y * z = s * r := by
    calc
      x * z - y * z = (x - y) * z := by ring
      _ = (-s) * z := by rw [hxy_eq]
      _ = (-s) * (-r) := by rw [hz_eq]
      _ = s * r := by ring
  rw [this]
  exact mul_pos_pos s r hs_pos hr_pos


/--
  Not in textbook: create an equivalence between Rat and ℚ. This requires some familiarity with
  the API for Mathlib's version of the rationals.
-/
abbrev Rat.equivRat : Rat ≃ ℚ where
  toFun := Quotient.lift (fun ⟨ a, b, h ⟩ ↦ a / b) (by
    intro ⟨a, b, hb⟩ ⟨c, d, hd⟩ h
    simp [PreRat.eq a b c d hb hd] at h
    have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb
    have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd
    apply (div_eq_div_iff hb' hd').mpr
    exact_mod_cast h)
  invFun := fun n: ℚ ↦ (n:Rat)
  left_inv n := by
    apply Quotient.ind _ n
    intro ⟨a, b, hb⟩
    simpa [formalDiv, hb] using Rat.coe_Rat_eq a hb
  right_inv n := by
    dsimp
    have hcast : (↑n : Rat) = n.num // (n.den : ℤ) := rfl
    rw [hcast]
    simp [formalDiv]
    simpa using (Rat.num_div_den n)

/-- Not in textbook: equivalence preserves order -/
abbrev Rat.equivRat_order : Rat ≃o ℚ where
  toEquiv := equivRat
  map_rel_iff' := by sorry

/-- Not in textbook: equivalence preserves ring operations -/
abbrev Rat.equivRat_ring : Rat ≃+* ℚ where
  toEquiv := equivRat
  map_add' x y := by
    refine Quotient.ind₂ (motive := λ x y : Rat => equivRat (x + y) = equivRat x + equivRat y) ?_ x y
    intro ⟨a, b, hb⟩ ⟨c, d, hd⟩
    have ha_rep : (⟦{ numerator := a, denominator := b, nonzero := hb }⟧ : Rat) = a // b := by
      simp [formalDiv, hb]
    have hc_rep : (⟦{ numerator := c, denominator := d, nonzero := hd }⟧ : Rat) = c // d := by
      simp [formalDiv, hd]
    rw [ha_rep, hc_rep]
    rw [Rat.add_eq a c hb hd]
    have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb
    have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd
    have hbd : b*d ≠ 0 := mul_ne_zero hb hd
    delta equivRat
    simp [formalDiv, hb, hd, hbd]
    field_simp [hb', hd']
  map_mul' x y := by
    refine Quotient.ind₂ (motive := λ x y : Rat => equivRat (x * y) = equivRat x * equivRat y) ?_ x y
    intro ⟨a, b, hb⟩ ⟨c, d, hd⟩
    have ha_rep : (⟦{ numerator := a, denominator := b, nonzero := hb }⟧ : Rat) = a // b := by
      simp [formalDiv, hb]
    have hc_rep : (⟦{ numerator := c, denominator := d, nonzero := hd }⟧ : Rat) = c // d := by
      simp [formalDiv, hd]
    rw [ha_rep, hc_rep]
    rw [Rat.mul_eq a c hb hd]
    have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb
    have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd
    have hbd : b*d ≠ 0 := mul_ne_zero hb hd
    delta equivRat
    simp [formalDiv, hb, hd, hbd]
    field_simp [hb', hd']

/--
  (Not from textbook) The textbook rationals are isomorphic (as a field) to the Mathlib rationals.
-/
def Rat.equivRat_ring_symm : ℚ ≃+* Rat := Rat.equivRat_ring.symm

end Section_4_2
