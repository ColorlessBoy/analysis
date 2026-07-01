import Mathlib.Tactic
import Analysis.Section_2_2

/-!
# Analysis I, Section 2.3: Multiplication

This file is a translation of Section 2.3 of Analysis I to Lean 4. All numbering refers to the
original text.

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of multiplication and exponentiation for the "Chapter 2" natural numbers,
  {name}`Chapter2.Nat`.

Note: at the end of this chapter, the {name}`Chapter2.Nat` class will be deprecated in favor of the
standard Mathlib class {name}`_root_.Nat`, or {lean}`ℕ`.  However, we will develop the properties of
{name}`Chapter2.Nat` "by hand" for pedagogical purposes.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter2

/-- Definition 2.3.1 (Multiplication of natural numbers) -/
abbrev Nat.mul (n m : Nat) : Nat := Nat.recurse (fun _ prod ↦ prod + m) 0 n

/-- This instance allows for the {kw (of := «term_*_»)}`*` notation to be used for natural number multiplication. -/
instance Nat.instMul : Mul Nat where
  mul := mul

/-- Definition 2.3.1 (Multiplication of natural numbers)
Compare with Mathlib's {name}`Nat.zero_mul` -/
theorem Nat.zero_mul (m: Nat) : 0 * m = 0 := recurse_zero (fun _ prod ↦ prod+m) _

/-- Definition 2.3.1 (Multiplication of natural numbers)
Compare with Mathlib's {name}`Nat.succ_mul` -/
theorem Nat.succ_mul (n m: Nat) : (n++) * m = n * m + m := recurse_succ (fun _ prod ↦ prod+m) _ _

theorem Nat.one_mul' (m: Nat) : 1 * m = 0 + m := by
  rw [←zero_succ, succ_mul, zero_mul]

/-- Compare with Mathlib's {name}`Nat.one_mul` -/
theorem Nat.one_mul (m: Nat) : 1 * m = m := by
  rw [one_mul', zero_add]

theorem Nat.two_mul (m: Nat) : 2 * m = 0 + m + m := by
  rw [←one_succ, succ_mul, one_mul']

/-- This lemma will be useful to prove Lemma 2.3.2.
Compare with Mathlib's {name}`Nat.mul_zero` -/
lemma Nat.mul_zero (n: Nat) : n * 0 = 0 := by
  revert n; apply induction
  · exact zero_mul 0
  intro n ih
  rw [succ_mul, ih, zero_add]

/-- This lemma will be useful to prove Lemma 2.3.2.
Compare with Mathlib's {name}`Nat.mul_succ` -/
lemma Nat.mul_succ (n m:Nat) : n * m++ = n * m + n := by
  revert n; apply induction
  · rw [zero_mul, zero_mul, zero_add]
  intro n ih
  calc
    (n++) * (m++) = n * (m++) + (m++) := by rw [succ_mul]
    _ = (n * m + n) + (m++) := by rw [ih]
    _ = n * m + (n + (m++)) := by rw [add_assoc]
    _ = n * m + ((n + m)++) := by rw [add_succ]
    _ = n * m + ((m + n)++) := by rw [add_comm n m]
    _ = n * m + (m + (n++)) := by rw [←add_succ m n]
    _ = (n * m + m) + (n++) := by rw [←add_assoc]
    _ = (n++) * m + (n++) := by rw [succ_mul]

/-- Lemma 2.3.2 (Multiplication is commutative) / Exercise 2.3.1
Compare with Mathlib's {name}`Nat.mul_comm` -/
lemma Nat.mul_comm (n m: Nat) : n * m = m * n := by
  revert n; apply induction
  · rw [zero_mul, mul_zero]
  intro n ih
  rw [succ_mul, mul_succ, ih]

/-- Compare with Mathlib's {name}`Nat.mul_one` -/
theorem Nat.mul_one (m: Nat) : m * 1 = m := by
  rw [mul_comm, one_mul]

/-- This lemma will be useful to prove Lemma 2.3.3.
Compare with Mathlib's {name}`Nat.mul_pos` -/
lemma Nat.pos_mul_pos {n m: Nat} (h₁: n.IsPos) (h₂: m.IsPos) : (n * m).IsPos := by
  induction n with
  | zero => exfalso; exact h₁ rfl
  | succ n ih =>
    rw [succ_mul]
    exact add_pos_right (n * m) h₂

/-- Lemma 2.3.3 (Positive natural numbers have no zero divisors) / Exercise 2.3.2.
    Compare with Mathlib's {name}`Nat.mul_eq_zero`.  -/
lemma Nat.mul_eq_zero (n m: Nat) : n * m = 0 ↔ n = 0 ∨ m = 0 := by
  constructor
  · intro h
    by_contra hnm
    have hn0 : n ≠ 0 := by intro hn; apply hnm; left; exact hn
    have hm0 : m ≠ 0 := by intro hm; apply hnm; right; exact hm
    have hpos : (n * m).IsPos := pos_mul_pos (by rwa [isPos_iff]) (by rwa [isPos_iff])
    rw [isPos_iff] at hpos
    exact hpos h
  · intro h
    rcases h with (hn | hm)
    · rw [hn, zero_mul]
    · rw [hm, mul_zero]

/-- Proposition 2.3.4 (Distributive law)
Compare with Mathlib's {name}`Nat.mul_add` -/
theorem Nat.mul_add (a b c: Nat) : a * (b + c) = a * b + a * c := by
  -- This proof is written to follow the structure of the original text.
  revert c; apply induction
  . rw [add_zero]
    rw [mul_zero, add_zero]
  intro c habc
  rw [add_succ, mul_succ]
  rw [mul_succ, ←add_assoc, ←habc]

/-- Proposition 2.3.4 (Distributive law)
Compare with Mathlib's {name}`Nat.add_mul`  -/
theorem Nat.add_mul (a b c: Nat) : (a + b)*c = a*c + b*c := by
  simp only [mul_comm, mul_add]

/-- Proposition 2.3.5 (Multiplication is associative) / Exercise 2.3.3
Compare with Mathlib's {name}`Nat.mul_assoc` -/
theorem Nat.mul_assoc (a b c: Nat) : (a * b) * c = a * (b * c) := by
  revert a; apply induction
  · rw [zero_mul, zero_mul, zero_mul]
  intro a ih
  rw [succ_mul, add_mul, ih, succ_mul]

/-- (Not from textbook)  {name}`Nat` is a commutative semiring.
    This allows tactics such as {tactic}`ring` to apply to the Chapter 2 natural numbers. -/
instance Nat.instCommSemiring : CommSemiring Nat where
  left_distrib := mul_add
  right_distrib := add_mul
  zero_mul := zero_mul
  mul_zero := mul_zero
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  mul_comm := mul_comm

/-- This illustration of the {tactic}`ring` tactic is not from the
    textbook. -/
example (a b c d:ℕ) : (a+b)*1*(c+d) = d*b+a*c+c*b+a*d+0 := by ring


/-- Proposition 2.3.6 (Multiplication preserves order)
Compare with Mathlib's {name}`Nat.mul_lt_mul_of_pos_right` -/
theorem Nat.mul_lt_mul_of_pos_right {a b c: Nat} (h: a < b) (hc: c.IsPos) : a * c < b * c := by
  -- This proof is written to follow the structure of the original text.
  rw [lt_iff_add_pos] at h
  choose d hdpos hd using h
  replace hd := congr($hd * c)
  rw [add_mul] at hd
  have hdcpos : (d * c).IsPos := pos_mul_pos hdpos hc
  rw [lt_iff_add_pos]
  use d*c

/-- Proposition 2.3.6 (Multiplication preserves order) -/
theorem Nat.mul_gt_mul_of_pos_right {a b c: Nat} (h: a > b) (hc: c.IsPos) :
    a * c > b * c := mul_lt_mul_of_pos_right h hc

/-- Proposition 2.3.6 (Multiplication preserves order)
Compare with Mathlib's {name}`Nat.mul_lt_mul_of_pos_left` -/
theorem Nat.mul_lt_mul_of_pos_left {a b c: Nat} (h: a < b) (hc: c.IsPos) : c * a < c * b := by
  simp [mul_comm]
  exact mul_lt_mul_of_pos_right h hc

/-- Proposition 2.3.6 (Multiplication preserves order) -/
theorem Nat.mul_gt_mul_of_pos_left {a b c: Nat} (h: a > b) (hc: c.IsPos) :
    c * a > c * b := mul_lt_mul_of_pos_left h hc

/-- Corollary 2.3.7 (Cancellation law)
Compare with Mathlib's {name}`Nat.mul_right_cancel` -/
lemma Nat.mul_cancel_right {a b c: Nat} (h: a * c = b * c) (hc: c.IsPos) : a = b := by
  -- This proof is written to follow the structure of the original text.
  have := trichotomous a b
  obtain hlt | rfl | hgt := this
  . replace hlt := mul_lt_mul_of_pos_right hlt hc
    apply ne_of_lt at hlt
    contradiction
  . rfl
  replace hgt := mul_gt_mul_of_pos_right hgt hc
  apply ne_of_gt at hgt
  contradiction

/-- (Not from textbook) {name}`Nat` is an ordered semiring.
This allows tactics such as {tactic}`gcongr` to apply to the Chapter 2 natural numbers. -/
instance Nat.isOrderedRing : IsOrderedRing Nat where
  zero_le_one := zero_le 1
  mul_le_mul_of_nonneg_left := by
    intro a ha b c hbc
    by_cases ha0 : a = 0
    · rw [ha0, zero_mul, zero_mul]
    · have hapos : a.IsPos := by rw [isPos_iff]; exact ha0
      rcases (le_iff_lt_or_eq b c).mp hbc with (hlt | heq)
      · have hlt' := mul_lt_mul_of_pos_left hlt hapos
        exact le_of_lt hlt'
      · rw [heq]
  mul_le_mul_of_nonneg_right := by
    intro c hc a b hab
    by_cases hc0 : c = 0
    · rw [hc0, mul_zero, mul_zero]
    · have hcpos : c.IsPos := by rw [isPos_iff]; exact hc0
      rcases (le_iff_lt_or_eq a b).mp hab with (hlt | heq)
      · have hlt' := mul_lt_mul_of_pos_right hlt hcpos
        exact le_of_lt hlt'
      · rw [heq]

/-- This illustration of the {tactic}`gcongr` tactic is not from the
    textbook. -/
example (a b c d:Nat) (hab: a ≤ b) : c*a*d ≤ c*b*d := by
  gcongr
  . exact d.zero_le
  exact c.zero_le

/-- Proposition 2.3.9 (Euclid's division lemma) / Exercise 2.3.5
Compare with Mathlib's {name}`Nat.mod_eq_iff` -/
theorem Nat.exists_div_mod (n:Nat) {q: Nat} (hq: q.IsPos) :
    ∃ m r: Nat, 0 ≤ r ∧ r < q ∧ n = m * q + r := by
  induction n with
  | zero =>
    refine ⟨0, 0, zero_le 0, ?_, ?_⟩
    · rw [lt_iff_add_pos]
      refine ⟨q, hq, ?_⟩
      rw [zero_add]
    · rw [zero_mul, add_zero]; rfl
  | succ n ih =>
    rcases ih with ⟨m, r, hr_nonneg, hr_lt, hn⟩
    have h_rpp_le_q : r++ ≤ q := (lt_iff_succ_le r q).mp hr_lt
    rcases (le_iff_lt_or_eq _ _).mp h_rpp_le_q with (h_lt | h_eq)
    · refine ⟨m, r++, zero_le (r++), h_lt, ?_⟩
      rw [hn, add_succ]
    · refine ⟨m++, 0, zero_le 0, ?_, ?_⟩
      · rw [lt_iff_add_pos]
        refine ⟨q, hq, ?_⟩
        rw [zero_add]
      · rw [hn, ←add_succ, h_eq, ←succ_mul, add_zero]

/-- Definition 2.3.11 (Exponentiation for natural numbers) -/
abbrev Nat.pow (m n: Nat) : Nat := Nat.recurse (fun _ prod ↦ prod * m) 1 n

instance Nat.instPow : HomogeneousPow Nat where
  pow := Nat.pow

/-- Definition 2.3.11 (Exponentiation for natural numbers)
Compare with Mathlib's {name}`Nat.pow_zero` -/
@[simp]
theorem Nat.pow_zero (m: Nat) : m ^ (0:Nat) = 1 := recurse_zero (fun _ prod ↦ prod * m) _

/-- Definition 2.3.11 (Exponentiation for natural numbers) -/
@[simp]
theorem Nat.zero_pow_zero : (0:Nat) ^ 0 = 1 := recurse_zero (fun _ prod ↦ prod * 0) _

/-- Definition 2.3.11 (Exponentiation for natural numbers)
Compare with Mathlib's {name}`Nat.pow_succ` -/
theorem Nat.pow_succ (m n: Nat) : (m:Nat) ^ n++ = m^n * m :=
  recurse_succ (fun _ prod ↦ prod * m) _ _

/-- Compare with Mathlib's {name}`Nat.pow_one` -/
@[simp]
theorem Nat.pow_one (m: Nat) : m ^ (1:Nat) = m := by
  rw [←zero_succ, pow_succ]; simp

/-- Exercise 2.3.4-/
theorem Nat.sq_add_eq (a b: Nat) :
    (a + b) ^ (2 : Nat) = a ^ (2 : Nat) + 2 * a * b + b ^ (2 : Nat) := by
  have ha_sq : a ^ (2 : Nat) = a * a := by
    calc
      a ^ (2 : Nat) = a ^ (1++) := rfl
      _ = a ^ (1 : Nat) * a := by rw [pow_succ]
      _ = a * a := by rw [pow_one]
  have hb_sq : b ^ (2 : Nat) = b * b := by
    calc
      b ^ (2 : Nat) = b ^ (1++) := rfl
      _ = b ^ (1 : Nat) * b := by rw [pow_succ]
      _ = b * b := by rw [pow_one]
  calc
    (a + b) ^ (2 : Nat) = (a + b) * (a + b) := by
      calc
        (a + b) ^ (2 : Nat) = (a + b) ^ (1++) := rfl
        _ = (a + b) ^ (1 : Nat) * (a + b) := by rw [pow_succ]
        _ = (a + b) * (a + b) := by rw [pow_one]
    _ = (a + b) * a + (a + b) * b := by rw [mul_add]
    _ = (a * a + b * a) + (a * b + b * b) := by rw [add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      abel
    _ = a * a + (a * b + a * b) + b * b := by rw [mul_comm b a]
    _ = a * a + 2 * (a * b) + b * b := by
      calc
        a * a + (a * b + a * b) + b * b
            = a * a + (0 + a * b + a * b) + b * b := by rw [zero_add]
        _ = a * a + 2 * (a * b) + b * b := by rw [two_mul]
    _ = a * a + (2 * a) * b + b * b := by rw [←mul_assoc 2 a b]
    _ = a ^ (2 : Nat) + 2 * a * b + b ^ (2 : Nat) := by rw [ha_sq, hb_sq]

end Chapter2
