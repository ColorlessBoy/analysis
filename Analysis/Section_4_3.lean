import Mathlib.Tactic

/-!
# Analysis I, Section 4.3: Absolute value and exponentiation

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Basic properties of absolute value and exponentiation on the rational numbers (here we use the
  Mathlib rational numbers {lean}`ℚ` rather than the Section 4.2 rational numbers).

Note: We define a custom absolute value as an {name}`abs` inside the {lit}`Section_4_3` namespace.
This shadows Mathlib's {name}`abs` and prevents accidental use of Mathlib's absolute value lemmas.
A bridge theorem {name}`abs_eq_abs` shows our {name}`abs` agrees with Mathlib's {syntax term}`|·|` — needed only for
`Rat.Close` (defined outside using Mathlib's {syntax term}`|·|`).  The spirit of the exercises is to use the
API provided in this section, as well as more basic Mathlib API for the rational numbers that does
not reference either absolute value or exponentiation.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/


/--
  This definition needs to be made outside of the Section 4.3 namespace for technical reasons.
-/
def Rat.Close (ε : ℚ) (x y:ℚ) := |x-y| ≤ ε


namespace Section_4_3

/-- Definition 4.3.1 (Absolute value) -/
abbrev abs (x:ℚ) : ℚ := if x > 0 then x else (if x < 0 then -x else 0)

theorem abs_of_pos {x: ℚ} (hx: 0 < x) : abs x = x := by grind

/-- Definition 4.3.1 (Absolute value) -/
theorem abs_of_neg {x: ℚ} (hx: x < 0) : abs x = -x := by grind

/-- Definition 4.3.1 (Absolute value) -/
theorem abs_of_zero : abs 0 = 0 := rfl

/--
  (Not from textbook) Our custom {name}`abs` agrees with
  Mathlib's absolute value (written {name}`_root_.abs` or {syntax term}`|·|` outside the namespace).
  The bridge {name}`abs_eq_abs` is only needed to connect {name}`Rat.Close` (outside) with our theorems.
  All proofs inside the namespace use only our custom {name}`abs` and its lemmas.
-/
theorem abs_eq_abs (x: ℚ) : abs x = _root_.abs x := by
  by_cases hx : 0 < x
  · rw [abs_of_pos hx, _root_.abs_of_nonneg (by linarith)]
  · by_cases hx' : x < 0
    · rw [abs_of_neg hx', _root_.abs_of_nonpos (by linarith)]
    · have hx0 : x = 0 := by linarith
      rw [hx0, abs_of_zero, _root_.abs_zero]

abbrev dist (x y : ℚ) := abs (x - y)

/--
  Definition 4.2 (Distance).
  We avoid the Mathlib notion of distance here because it is real-valued.
-/
theorem dist_eq (x y: ℚ) : dist x y = abs (x - y) := rfl

/-- Proposition 4.3.3(a) / Exercise 4.3.1 -/
theorem abs_nonneg (x: ℚ) : abs (x) ≥ 0 := by
  by_cases hx : 0 < x
  · rw [abs_of_pos hx]; linarith
  · by_cases hx' : x < 0
    · rw [abs_of_neg hx']; linarith
    · have hx0 : x = 0 := by linarith
      rw [hx0, abs_of_zero]

/-- Proposition 4.3.3(a) / Exercise 4.3.1 -/
theorem abs_eq_zero_iff (x: ℚ) : abs (x) = 0 ↔ x = 0 := by
  constructor
  · intro h
    by_cases hx : 0 < x
    · rw [abs_of_pos hx] at h; exact h
    · by_cases hx' : x < 0
      · rw [abs_of_neg hx'] at h; linarith
      · linarith
  · intro h; subst h; exact abs_of_zero

/-- Proposition 4.3.3(c) / Exercise 4.3.1 -/
theorem abs_le_iff (x y:ℚ) : -y ≤ x ∧ x ≤ y ↔ abs (x) ≤ y := by
  constructor
  · intro ⟨h1, h2⟩
    by_cases hx : 0 < x
    · rw [abs_of_pos hx]; exact h2
    · by_cases hx' : x < 0
      · rw [abs_of_neg hx']; linarith
      · have hx0 : x = 0 := by linarith
        rw [hx0, abs_of_zero]; linarith
  · intro h
    constructor
    · by_cases hx : 0 < x
      · rw [abs_of_pos hx] at h; linarith
      · by_cases hx' : x < 0
        · rw [abs_of_neg hx'] at h; linarith
        · have hx0 : x = 0 := by linarith
          subst hx0; rw [abs_of_zero] at h; linarith
    · by_cases hx : 0 < x
      · rw [abs_of_pos hx] at h; exact h
      · by_cases hx' : x < 0
        · rw [abs_of_neg hx'] at h; linarith
        · have hx0 : x = 0 := by linarith
          subst hx0; rw [abs_of_zero] at h; linarith

/-- Proposition 4.3.3(c) / Exercise 4.3.1 -/
theorem le_abs (x:ℚ) : -abs x ≤ x ∧ x ≤ abs x :=
  (abs_le_iff x (abs x)).mpr (le_refl _)

/-- Proposition 4.3.3(b) / Exercise 4.3.1 -/
theorem abs_add (x y:ℚ) : abs (x + y) ≤ abs (x) + abs (y) := by
  have hx := le_abs x
  have hy := le_abs y
  have hsum : -(abs (x) + abs (y)) ≤ x + y ∧ x + y ≤ abs (x) + abs (y) := by
    constructor <;> linarith
  exact (abs_le_iff (x + y) (abs (x) + abs (y))).mp hsum

/-- Proposition 4.3.3(d) / Exercise 4.3.1 -/
theorem abs_mul (x y:ℚ) : abs (x * y) = abs (x) * abs (y) := by sorry

/-- Proposition 4.3.3(d) / Exercise 4.3.1 -/
theorem abs_neg (x:ℚ) : abs (-x) = abs (x) := by sorry

/-- Proposition 4.3.3(e) / Exercise 4.3.1 -/
theorem dist_nonneg (x y:ℚ) : dist x y ≥ 0 := by sorry

/-- Proposition 4.3.3(e) / Exercise 4.3.1 -/
theorem dist_eq_zero_iff (x y:ℚ) : dist x y = 0 ↔ x = y := by
  sorry

/-- Proposition 4.3.3(f) / Exercise 4.3.1 -/
theorem dist_symm (x y:ℚ) : dist x y = dist y x := by sorry

/-- Proposition 4.3.3(f) / Exercise 4.3.1 -/
theorem dist_le (x y z:ℚ) : dist x z ≤ dist x y + dist y z := by sorry

/--
  Definition 4.3.4 (eps-closeness).  In the text the notion is undefined for ε zero or negative,
  but it is more convenient in Lean to assign a "junk" definition in this case.  But this also
  allows some relaxations of hypotheses in the lemmas that follow.
-/
theorem close_iff (ε x y:ℚ): ε.Close x y ↔ abs (x - y) ≤ ε := by
  have h := abs_eq_abs (x - y)
  rw [h]
  rfl

/-- Examples 4.3.6 -/
example : (0.1:ℚ).Close (0.99:ℚ) (1.01:ℚ) := by sorry

/-- Examples 4.3.6 -/
example : ¬ (0.01:ℚ).Close (0.99:ℚ) (1.01:ℚ) := by sorry

/-- Examples 4.3.6 -/
example (ε : ℚ) (hε : ε > 0) : ε.Close 2 2 := by sorry

theorem close_refl (x:ℚ) : (0:ℚ).Close x x := by sorry

/-- Proposition 4.3.7(a) / Exercise 4.3.2 -/
theorem eq_if_close (x y:ℚ) : x = y ↔ ∀ ε:ℚ, ε > 0 → ε.Close x y := by sorry

/-- Proposition 4.3.7(b) / Exercise 4.3.2 -/
theorem close_symm (ε x y:ℚ) : ε.Close x y ↔ ε.Close y x := by sorry

/-- Proposition 4.3.7(c) / Exercise 4.3.2 -/
theorem close_trans {ε δ x y z:ℚ} (hxy: ε.Close x y) (hyz: δ.Close y z) :
    (ε + δ).Close x z := by sorry

/-- Proposition 4.3.7(d) / Exercise 4.3.2 -/
theorem add_close {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε + δ).Close (x+z) (y+w) := by sorry

/-- Proposition 4.3.7(d) / Exercise 4.3.2 -/
theorem sub_close {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε + δ).Close (x-z) (y-w) := by sorry

/-- Proposition 4.3.7(e) / Exercise 4.3.2, slightly strengthened -/
theorem close_mono {ε ε' x y:ℚ} (hxy: ε.Close x y) (hε: ε' ≥  ε) :
    ε'.Close x y := by sorry

/-- Proposition 4.3.7(f) / Exercise 4.3.2 -/
theorem close_between {ε x y z w:ℚ} (hxy: ε.Close x y) (hxz: ε.Close x z)
  (hbetween: (y ≤ w ∧ w ≤ z) ∨ (z ≤ w ∧ w ≤ y)) : ε.Close x w := by sorry

/-- Proposition 4.3.7(g) / Exercise 4.3.2 -/
theorem close_mul_right {ε x y z:ℚ} (hxy: ε.Close x y) :
    (ε*abs (z)).Close (x * z) (y * z) := by sorry

/-- Proposition 4.3.7(h) / Exercise 4.3.2 -/
theorem close_mul_mul {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε*abs (z) + δ*abs (x) + ε*δ).Close (x * z) (y * w) := by
  -- The proof is written to follow the structure of the original text, though
  -- non-negativity of ε and δ are implied and don't need to be provided as
  -- explicit hypotheses.
  have hε : ε ≥ 0 := le_trans (_root_.abs_nonneg (x - y)) hxy
  set a := y-x
  have ha : y = x + a := by grind
  have haε: abs a ≤ ε := by rwa [close_symm, close_iff] at hxy
  set b := w-z
  have hb : w = z + b := by grind
  have hbδ: abs b ≤ δ := by rwa [close_symm, close_iff] at hzw
  have h_yw : y*w = x*z + a*z + x*b + a*b := by grind
  rw [close_symm, close_iff]
  have h_diff : y*w - x*z = a*z + b*x + a*b := by
    nlinarith
  rw [h_diff]
  calc
    abs (a*z + b*x + a*b) ≤ abs (a*z + b*x) + abs (a*b) := abs_add _ _
    _ ≤ abs (a*z) + abs (b*x) + abs (a*b) := by
      have h := abs_add (a*z) (b*x)
      linarith
    _ = abs a * abs z + abs b * abs x + abs a * abs b := by rw [abs_mul, abs_mul, abs_mul]
    _ ≤ ε*abs z + δ*abs x + ε*δ := by
      nlinarith [haε, hbδ, abs_nonneg z, abs_nonneg x, abs_nonneg a, abs_nonneg b, hε]

/-- This variant of Proposition 4.3.7(h) was not in the textbook, but can be useful
in some later exercises. -/
theorem close_mul_mul' {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε*abs (z) + δ*abs (y)).Close (x * z) (y * w) := by
    sorry

/-- Definition 4.3.9 (exponentiation).  Here we use the Mathlib definition.-/
lemma pow_zero (x:ℚ) : x^0 = 1 := _root_.pow_zero x

example : (0:ℚ)^0 = 1 := pow_zero 0

/-- Definition 4.3.9 (exponentiation).  Here we use the Mathlib definition.-/
lemma pow_succ (x:ℚ) (n:ℕ) : x^(n+1) = x^n * x := _root_.pow_succ x n

/-- Proposition 4.3.10(a) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_add (x:ℚ) (m n:ℕ) : x^n * x^m = x^(n+m) := by sorry

/-- Proposition 4.3.10(a) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_mul (x:ℚ) (m n:ℕ) : (x^n)^m = x^(n*m) := by sorry

/-- Proposition 4.3.10(a) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem mul_pow (x y:ℚ) (n:ℕ) : (x*y)^n = x^n * y^n := by sorry

/-- Proposition 4.3.10(b) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_eq_zero (x:ℚ) (n:ℕ) (hn : 0 < n) : x^n = 0 ↔ x = 0 := by sorry

/-- Proposition 4.3.10(c) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_nonneg {x:ℚ} (n:ℕ) (hx: x ≥ 0) : x^n ≥ 0 := by sorry

/-- Proposition 4.3.10(c) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_pos {x:ℚ} (n:ℕ) (hx: x > 0) : x^n > 0 := by sorry

/-- Proposition 4.3.10(c) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_ge_pow (x y:ℚ) (n:ℕ) (hxy: x ≥ y) (hy: y ≥ 0) : x^n ≥ y^n := by sorry

/-- Proposition 4.3.10(c) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_gt_pow (x y:ℚ) (n:ℕ) (hxy: x > y) (hy: y ≥ 0) (hn: n > 0) : x^n > y^n := by sorry

/-- Proposition 4.3.10(d) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_abs (x:ℚ) (n:ℕ) : abs (x)^n = abs (x^n) := by sorry

/--
  Definition 4.3.11 (Exponentiation to a negative number).
  Here we use the Mathlib notion of integer exponentiation
-/
theorem zpow_neg (x:ℚ) (n:ℕ) : x^(-(n:ℤ)) = 1/(x^n) := by simp

example (x:ℚ): x^(-3:ℤ) = 1/(x^3) := zpow_neg x 3

example (x:ℚ): x^(-3:ℤ) = 1/(x*x*x) := by convert zpow_neg x 3; ring

theorem pow_eq_zpow (x:ℚ) (n:ℕ): x^(n:ℤ) = x^n := zpow_natCast x n

/-- Proposition 4.3.12(a) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_add (x:ℚ) (n m:ℤ) (hx: x ≠ 0): x^n * x^m = x^(n+m) := by sorry

/-- Proposition 4.3.12(a) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_mul (x:ℚ) (n m:ℤ) : (x^n)^m = x^(n*m) := by sorry

/-- Proposition 4.3.12(a) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem mul_zpow (x y:ℚ) (n:ℤ) : (x*y)^n = x^n * y^n := by sorry

/-- Proposition 4.3.12(b) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_pos {x:ℚ} (n:ℤ) (hx: x > 0) : x^n > 0 := by sorry

/-- Proposition 4.3.12(b) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_ge_zpow {x y:ℚ} {n:ℤ} (hxy: x ≥ y) (hy: y > 0) (hn: n > 0): x^n ≥ y^n := by sorry

theorem zpow_ge_zpow_ofneg {x y:ℚ} {n:ℤ} (hxy: x ≥ y) (hy: y > 0) (hn: n < 0) : x^n ≤ y^n := by
  sorry

/-- Proposition 4.3.12(c) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_inj {x y:ℚ} {n:ℤ} (hx: x > 0) (hy : y > 0) (hn: n ≠ 0) (hxy: x^n = y^n) : x = y := by
  sorry

/-- Proposition 4.3.12(d) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_abs (x:ℚ) (n:ℤ) : abs (x)^n = abs (x^n) := by sorry

/-- Exercise 4.3.5 -/
theorem two_pow_geq (N:ℕ) : 2^N ≥ N := by sorry
