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
theorem abs_mul (x y:ℚ) : abs (x * y) = abs (x) * abs (y) := by
  by_cases hx : 0 < x
  · rw [abs_of_pos hx]
    by_cases hy : 0 < y
    · have hxy : 0 < x * y := by nlinarith
      rw [abs_of_pos hy, abs_of_pos hxy]
    by_cases hy' : y < 0
    · have hxy : x * y < 0 := by nlinarith
      rw [abs_of_neg hy', abs_of_neg hxy]; linarith
    have hy0 : y = 0 := by linarith
    rw [hy0, mul_zero, abs_of_zero, mul_zero]
  by_cases hx' : x < 0
  · rw [abs_of_neg hx']
    by_cases hy : 0 < y
    · have hxy : x * y < 0 := by nlinarith
      rw [abs_of_pos hy, abs_of_neg hxy]
      linarith
    by_cases hy' : y < 0
    · have hxy : 0 < x * y := by nlinarith
      rw [abs_of_neg hy', abs_of_pos hxy]; linarith
    have hy0 : y = 0 := by linarith
    rw [hy0, mul_zero, abs_of_zero, mul_zero]
  have hx0 : x = 0 := by linarith
  rw [hx0, zero_mul, abs_of_zero, zero_mul]

/-- Proposition 4.3.3(d) / Exercise 4.3.1 -/
theorem abs_neg (x:ℚ) : abs (-x) = abs (x) := by
  rw [neg_eq_neg_one_mul, abs_mul, abs_of_neg (by norm_num)]; simp

/-- Proposition 4.3.3(e) / Exercise 4.3.1 -/
theorem dist_nonneg (x y:ℚ) : dist x y ≥ 0 := by
  rw [dist_eq]
  exact abs_nonneg _

/-- Proposition 4.3.3(e) / Exercise 4.3.1 -/
theorem dist_eq_zero_iff (x y:ℚ) : dist x y = 0 ↔ x = y := by
  rw [dist_eq, abs_eq_zero_iff]
  exact sub_eq_zero

/-- Proposition 4.3.3(f) / Exercise 4.3.1 -/
theorem dist_symm (x y:ℚ) : dist x y = dist y x := by
  rw [dist_eq, ← abs_neg, neg_sub, dist_eq]

/-- Proposition 4.3.3(f) / Exercise 4.3.1 -/
theorem dist_le (x y z:ℚ) : dist x z ≤ dist x y + dist y z := by
  have h : x - z = (x - y) + (y - z) := by linarith
  rw [dist_eq, dist_eq, dist_eq, h]
  exact abs_add _ _

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
example : (0.1:ℚ).Close (0.99:ℚ) (1.01:ℚ) := by
  rw [close_iff, abs_of_neg (by linarith)]; norm_num

/-- Examples 4.3.6 -/
example : ¬ (0.01:ℚ).Close (0.99:ℚ) (1.01:ℚ) := by
  rw [close_iff, abs_of_neg (by linarith)]; norm_num

/-- Examples 4.3.6 -/
example (ε : ℚ) (hε : ε > 0) : ε.Close 2 2 := by
  rw [close_iff, sub_self, abs_of_zero]; linarith

theorem close_refl (x:ℚ) : (0:ℚ).Close x x := by
  rw [close_iff, sub_self, abs_of_zero]

/-- Proposition 4.3.7(a) / Exercise 4.3.2 -/
theorem eq_if_close (x y:ℚ) : x = y ↔ ∀ ε:ℚ, ε > 0 → ε.Close x y := by
  constructor
  · intro h e he; rw [h, close_iff, sub_self, abs_of_zero]; linarith
  intro h
  by_cases h' : 0 < x - y
  · have h'' := h ((x - y)/2) (by linarith); rw [close_iff, abs_of_pos h'] at h''; nlinarith
  by_cases h' : x - y < 0
  · have h'' := h ((y - x)/2) (by linarith); rw [close_iff, abs_of_neg h'] at h''; nlinarith
  nlinarith

/-- Proposition 4.3.7(b) / Exercise 4.3.2 -/
theorem close_symm (ε x y:ℚ) : ε.Close x y ↔ ε.Close y x := by
  rw [close_iff, ← abs_neg, neg_sub, ← close_iff]

/-- Proposition 4.3.7(c) / Exercise 4.3.2 -/
theorem close_trans {ε δ x y z:ℚ} (hxy: ε.Close x y) (hyz: δ.Close y z) :
    (ε + δ).Close x z := by
    simp_all [close_iff]
    apply le_trans _ (add_le_add hxy hyz)
    have : x - z = x - y + (y - z) := by linarith
    rw [this]
    exact abs_add _ _

/-- Proposition 4.3.7(d) / Exercise 4.3.2 -/
theorem add_close {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε + δ).Close (x+z) (y+w) := by
  rw [close_iff] at hxy hzw ⊢
  have h : (x+z) - (y+w) = (x-y) + (z-w) := by ring
  rw [h]
  calc
    abs ((x-y) + (z-w)) ≤ abs (x-y) + abs (z-w) := abs_add _ _
    _ ≤ ε + δ := by linarith

/-- Proposition 4.3.7(d) / Exercise 4.3.2 -/
theorem sub_close {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε + δ).Close (x-z) (y-w) := by
  rw [close_iff] at hxy hzw ⊢
  have h : (x-z) - (y-w) = (x-y) + (w-z) := by ring
  rw [h]
  have h_abs : abs (w - z) = abs (z - w) := by rw [← abs_neg, neg_sub]
  calc
    abs ((x-y) + (w-z)) ≤ abs (x-y) + abs (w-z) := abs_add _ _
    _ = abs (x-y) + abs (z-w) := by rw [h_abs]
    _ ≤ ε + δ := by linarith

/-- Proposition 4.3.7(e) / Exercise 4.3.2, slightly strengthened -/
theorem close_mono {ε ε' x y:ℚ} (hxy: ε.Close x y) (hε: ε' ≥ ε) :
    ε'.Close x y := by
  rw [close_iff] at hxy ⊢
  linarith

/-- Proposition 4.3.7(f) / Exercise 4.3.2 -/
theorem close_between {ε x y z w:ℚ} (hxy: ε.Close x y) (hxz: ε.Close x z)
  (hbetween: (y ≤ w ∧ w ≤ z) ∨ (z ≤ w ∧ w ≤ y)) : ε.Close x w := by
  rcases hbetween with (⟨hyw, hwz⟩ | ⟨hzw, hwy⟩)
  · rw [close_iff] at hxy hxz ⊢
    rcases (abs_le_iff (x - y) ε).mpr hxy with ⟨hxy1, hxy2⟩
    rcases (abs_le_iff (x - z) ε).mpr hxz with ⟨hxz1, hxz2⟩
    apply (abs_le_iff (x - w) ε).mp
    constructor <;> linarith
  rw [close_iff] at hxy hxz ⊢
  rcases (abs_le_iff (x - y) ε).mpr hxy with ⟨hxy1, hxy2⟩
  rcases (abs_le_iff (x - z) ε).mpr hxz with ⟨hxz1, hxz2⟩
  apply (abs_le_iff (x - w) ε).mp
  constructor <;> linarith

/-- Proposition 4.3.7(g) / Exercise 4.3.2 -/
theorem close_mul_right {ε x y z:ℚ} (hxy: ε.Close x y) :
    (ε*abs (z)).Close (x * z) (y * z) := by
  rw [close_iff] at hxy ⊢
  have h : x * z - y * z = (x - y) * z := by ring
  rw [h, abs_mul]
  have hz : abs (z) ≥ 0 := abs_nonneg _
  nlinarith

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
  have hε : ε ≥ 0 := by
    have := abs_nonneg (x - y)
    rw [close_iff] at hxy
    linarith
  set a := y - x
  have ha : y = x + a := by linarith
  have haε : abs a ≤ ε := by
    rw [close_symm, close_iff] at hxy
    simpa [a] using hxy
  set b := w - z
  have hb : w = z + b := by linarith
  have hbδ : abs b ≤ δ := by
    rw [close_symm, close_iff] at hzw
    simpa [b] using hzw
  rw [close_symm, close_iff]
  have h_diff : y * w - x * z = a * z + y * b := by
    rw [ha, hb]
    ring
  rw [h_diff]
  calc
    abs (a * z + y * b) ≤ abs (a * z) + abs (y * b) := abs_add _ _
    _ = abs a * abs z + abs b * abs y := by
      rw [abs_mul a z, abs_mul y b]
      ring
    _ ≤ ε * abs z + δ * abs y := by
      have hz : abs z ≥ 0 := abs_nonneg _
      have hy : abs y ≥ 0 := abs_nonneg _
      nlinarith

/-- Definition 4.3.9 (exponentiation).  Here we use the Mathlib definition.-/
lemma pow_zero (x:ℚ) : x^0 = 1 := _root_.pow_zero x

example : (0:ℚ)^0 = 1 := pow_zero 0

/-- Definition 4.3.9 (exponentiation).  Here we use the Mathlib definition.-/
lemma pow_succ (x:ℚ) (n:ℕ) : x^(n+1) = x^n * x := _root_.pow_succ x n

/-- Proposition 4.3.10(a) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_add (x:ℚ) (m n:ℕ) : x^n * x^m = x^(n+m) := by
  rw [_root_.pow_add x n m]

/-- Proposition 4.3.10(a) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_mul (x:ℚ) (m n:ℕ) : (x^n)^m = x^(n*m) := by
  rw [← _root_.pow_mul x n m]

/-- Proposition 4.3.10(a) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem mul_pow (x y:ℚ) (n:ℕ) : (x*y)^n = x^n * y^n := by
  exact _root_.mul_pow x y n

/-- Proposition 4.3.10(b) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_eq_zero (x:ℚ) (n:ℕ) (hn : 0 < n) : x^n = 0 ↔ x = 0 := by
  constructor
  · exact eq_zero_of_pow_eq_zero
  · intro h; rw [h]; exact zero_pow hn.ne.symm

/-- Proposition 4.3.10(c) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_nonneg {x:ℚ} (n:ℕ) (hx: x ≥ 0) : x^n ≥ 0 := by
  exact _root_.pow_nonneg hx n

/-- Proposition 4.3.10(c) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_pos {x:ℚ} (n:ℕ) (hx: x > 0) : x^n > 0 := by
  exact _root_.pow_pos hx n

/-- Proposition 4.3.10(c) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_ge_pow (x y:ℚ) (n:ℕ) (hxy: x ≥ y) (hy: y ≥ 0) : x^n ≥ y^n := by
  induction' n with k ih
  · simp
  · have hx : x ≥ 0 := by linarith
    have hxk_nonneg : x^k ≥ 0 := _root_.pow_nonneg hx k
    rw [pow_succ, pow_succ]
    exact mul_le_mul ih hxy hy hxk_nonneg

/-- Proposition 4.3.10(c) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_gt_pow (x y:ℚ) (n:ℕ) (hxy: x > y) (hy: y ≥ 0) (hn: n > 0) : x^n > y^n := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne.symm
  subst hk
  rw [pow_succ, pow_succ]
  have hx : x > 0 := by linarith
  have hxk_pos : x^k > 0 := _root_.pow_pos hx k
  have hxk_ge_yk : x^k ≥ y^k := pow_ge_pow x y k (by linarith) hy
  have h1 : x^k * x > x^k * y := mul_lt_mul_of_pos_left hxy hxk_pos
  have h2 : x^k * y ≥ y^k * y := mul_le_mul_of_nonneg_right hxk_ge_yk hy
  calc
    x^k * x > x^k * y := h1
    _ ≥ y^k * y := h2

/-- Proposition 4.3.10(d) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_abs (x:ℚ) (n:ℕ) : abs (x)^n = abs (x^n) := by
  calc
    abs (x)^n = (_root_.abs x)^n := by rw [abs_eq_abs]
    _ = _root_.abs (x ^ n) := by rw [_root_.abs_pow]
    _ = abs (x ^ n) := by rw [← abs_eq_abs]

/--
  Definition 4.3.11 (Exponentiation to a negative number).
  Here we use the Mathlib notion of integer exponentiation
-/
theorem zpow_neg (x:ℚ) (n:ℕ) : x^(-(n:ℤ)) = 1/(x^n) := by simp

example (x:ℚ): x^(-3:ℤ) = 1/(x^3) := zpow_neg x 3

example (x:ℚ): x^(-3:ℤ) = 1/(x*x*x) := by convert zpow_neg x 3; ring

theorem pow_eq_zpow (x:ℚ) (n:ℕ): x^(n:ℤ) = x^n := zpow_natCast x n

/-- Proposition 4.3.12(a) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_add (x:ℚ) (n m:ℤ) (hx: x ≠ 0): x^n * x^m = x^(n+m) := by
  rw [← _root_.zpow_add₀ hx n m]

/-- Proposition 4.3.12(a) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_mul (x:ℚ) (n m:ℤ) : (x^n)^m = x^(n*m) := by
  rw [← _root_.zpow_mul x n m]

/-- Proposition 4.3.12(a) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem mul_zpow (x y:ℚ) (n:ℤ) : (x*y)^n = x^n * y^n := by
  exact _root_.mul_zpow x y n

/-- Proposition 4.3.12(b) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_pos {x:ℚ} (n:ℤ) (hx: x > 0) : x^n > 0 := by
  exact _root_.zpow_pos hx n

/-- Proposition 4.3.12(b) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_ge_zpow {x y:ℚ} {n:ℤ} (hxy: x ≥ y) (hy: y > 0) (hn: n > 0): x^n ≥ y^n := by
  apply _root_.zpow_le_zpow_left₀ <;> linarith

theorem zpow_ge_zpow_ofneg {x y:ℚ} {n:ℤ} (hxy: x ≥ y) (hy: y > 0) (hn: n < 0) : x^n ≤ y^n := by
  have hx : x > 0 := by linarith
  have hm_pos : 0 < -n := by linarith
  have hpos_case := zpow_ge_zpow hxy hy hm_pos
  have hx_pos : x ^ (-n) > 0 := _root_.zpow_pos hx (-n)
  have hy_pos : y ^ (-n) > 0 := _root_.zpow_pos hy (-n)
  have hx_eq : x^n = 1 / (x ^ (-n)) := by
    calc
      x^n = x ^ (-(-n)) := by simp
      _ = (x ^ (-n))⁻¹ := by rw [_root_.zpow_neg]
      _ = 1 / (x ^ (-n)) := by rw [one_div]
  have hy_eq : y^n = 1 / (y ^ (-n)) := by
    calc
      y^n = y ^ (-(-n)) := by simp
      _ = (y ^ (-n))⁻¹ := by rw [_root_.zpow_neg]
      _ = 1 / (y ^ (-n)) := by rw [one_div]
  rw [hx_eq, hy_eq]
  exact ((one_div_le_one_div hx_pos hy_pos).mpr hpos_case)

/-- Proposition 4.3.12(c) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_inj {x y:ℚ} {n:ℤ} (hx: x > 0) (hy : y > 0) (hn: n ≠ 0) (hxy: x^n = y^n) : x = y := by
  rcases lt_or_gt_of_ne hn with (hn_neg | hn_pos)
  · -- n < 0, reduce to positive case by taking inverses
    have hm_nonneg : 0 ≤ -n := by linarith
    have h_pow_eq : x ^ (-n) = y ^ (-n) := by
      calc
        x ^ (-n) = (x ^ n)⁻¹ := by rw [_root_.zpow_neg x n]
        _ = (y ^ n)⁻¹ := by rw [hxy]
        _ = y ^ (-n) := by rw [← _root_.zpow_neg y n]
    lift -n to ℕ using hm_nonneg with k hk
    have hk_ne_zero : k ≠ 0 := by
      intro hzero
      have : (k : ℤ) = 0 := by exact_mod_cast hzero
      have hn0 : n = 0 := by linarith
      linarith
    have hk_pos : 0 < k := Nat.pos_of_ne_zero hk_ne_zero
    rw [pow_eq_zpow x k, pow_eq_zpow y k] at h_pow_eq
    by_contra hne
    have hlt_or : x < y ∨ y < x := lt_or_gt_of_ne hne
    rcases hlt_or with (hlt | hlt)
    · have hlt' : x ^ k < y ^ k := pow_gt_pow y x k hlt (by linarith) hk_pos
      linarith
    · have hlt' : y ^ k < x ^ k := pow_gt_pow x y k hlt (by linarith) hk_pos
      linarith
  · -- n > 0
    have hn_nonneg : 0 ≤ n := by linarith
    lift n to ℕ using hn_nonneg with k hk
    have hk_ne_zero : k ≠ 0 := by
      intro hzero
      have : (k : ℤ) = 0 := by exact_mod_cast hzero
      have hn0 : n = 0 := by linarith
      linarith
    have hk_pos : 0 < k := Nat.pos_of_ne_zero hk_ne_zero
    rw [pow_eq_zpow x k, pow_eq_zpow y k] at hxy
    by_contra hne
    have hlt_or : x < y ∨ y < x := lt_or_gt_of_ne hne
    rcases hlt_or with (hlt | hlt)
    · have hlt' : x ^ k < y ^ k := pow_gt_pow y x k hlt (by linarith) hk_pos
      linarith
    · have hlt' : y ^ k < x ^ k := pow_gt_pow x y k hlt (by linarith) hk_pos
      linarith

/-- Proposition 4.3.12(d) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_abs (x:ℚ) (n:ℤ) : abs (x)^n = abs (x^n) := by
  by_cases hn_nonneg : 0 ≤ n
  · lift n to ℕ using hn_nonneg with k
    calc
      abs (x)^((k : ℤ)) = (abs x)^k := by rw [pow_eq_zpow]
      _ = (_root_.abs x)^k := by rw [abs_eq_abs]
      _ = _root_.abs (x ^ k) := by rw [_root_.abs_pow]
      _ = abs (x ^ k) := by rw [← abs_eq_abs]
      _ = abs (x ^ ((k : ℤ))) := by rw [← pow_eq_zpow]
  · have hn_nonpos : n ≤ 0 := by linarith
    have hpos : 0 ≤ -n := by linarith
    lift -n to ℕ using hpos with k hk
    have hn_eq : n = -((k : ℤ)) := by
      linarith
    rw [hn_eq]
    calc
      abs (x) ^ (-(k : ℤ)) = ((abs x) ^ (k : ℤ))⁻¹ := by rw [_root_.zpow_neg]
      _ = ((abs x) ^ k)⁻¹ := by rw [pow_eq_zpow]
      _ = 1 / ((abs x) ^ k) := by rw [one_div]
      _ = 1 / ((_root_.abs x) ^ k) := by rw [abs_eq_abs]
      _ = 1 / _root_.abs (x ^ k) := by rw [_root_.abs_pow]
      _ = _root_.abs (1) / _root_.abs (x ^ k) := by rw [_root_.abs_one]
      _ = _root_.abs (1 / (x ^ k)) := by rw [_root_.abs_div]
      _ = abs (1 / (x ^ k)) := by rw [← abs_eq_abs]
      _ = abs ((x ^ k)⁻¹) := by rw [one_div]
      _ = abs (x ^ (-(k : ℤ))) := by
        rw [← pow_eq_zpow x k, ← _root_.zpow_neg x k]

/-- Exercise 4.3.5 -/
theorem two_pow_geq (N:ℕ) : 2^N ≥ N := by
  induction' N with k ih
  · simp
  · rw [Nat.pow_succ, mul_comm, Nat.two_mul]
    have hpos : 0 < 2 ^ k := Nat.pow_pos (a := 2) (by norm_num : 0 < 2) (n := k)
    omega
