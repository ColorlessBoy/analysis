import Mathlib.Tactic
import Analysis.Section_5_5


/-!
# Analysis I, Section 5.6: Real exponentiation, part I

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Exponentiating reals to natural numbers and integers.
- nth roots.
- Raising a real to a rational number.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter5

/-- Upgrade {name}`Real` to {name}`CommGroupWithZero` using the existing inverse on {name}`Real`.
This is enough to unlock e.g. {name}`zpow_neg`, {name}`zpow_add₀`, {name}`zpow_mul`,
{name}`mul_zpow`, which are needed for the proofs below. -/
noncomputable instance Real.instCommGroupWithZero : CommGroupWithZero Real where
  __ := (inferInstance : DivInvMonoid Real)
  __ := (inferInstance : CommMonoid Real)
  exists_pair_ne := ⟨0, 1, by norm_num⟩
  mul_inv_cancel := fun _ h => Real.self_mul_inv h
  inv_zero := Real.inv_zero
  zero_mul := zero_mul
  mul_zero := mul_zero

/-- Definition 5.6.1 (Exponentiating a real by a natural number). Here we use the
    Mathlib definition coming from {name}`Monoid`. -/

lemma Real.pow_zero (x: Real) : x ^ 0 = 1 := rfl

lemma Real.pow_succ (x: Real) (n:ℕ) : x ^ (n+1) = (x ^ n) * x := rfl

lemma Real.pow_of_coe (q: ℚ) (n:ℕ) : (q:Real) ^ n = (q ^ n:ℚ) := by
  induction n with
  | zero => simp
  | succ k ih => rw [_root_.pow_succ, _root_.pow_succ, ih, Real.ratCast_mul]

/- The claims below can be handled easily by existing Mathlib API (as `Real` already is known
to be a `Field`), but the spirit of the exercises is to adapt the proofs of
Proposition 4.3.10 that you previously established. -/

/-- Analogue of Proposition 4.3.10(a) -/
theorem Real.pow_add (x:Real) (m n:ℕ) : x^n * x^m = x^(n+m) := by
  rw [_root_.pow_add x n m]

/-- Analogue of Proposition 4.3.10(a) -/
theorem Real.pow_mul (x:Real) (m n:ℕ) : (x^n)^m = x^(n*m) := by
  rw [← _root_.pow_mul x n m]

/-- Analogue of Proposition 4.3.10(a) -/
theorem Real.mul_pow (x y:Real) (n:ℕ) : (x*y)^n = x^n * y^n := by
  exact _root_.mul_pow x y n

/-- Analogue of Proposition 4.3.10(b) -/
theorem Real.pow_eq_zero (x:Real) (n:ℕ) (hn : 0 < n) : x^n = 0 ↔ x = 0 := by
  constructor
  · exact pow_eq_zero_iff hn.ne.symm |>.mp
  · intro h; rw [h]; exact zero_pow hn.ne.symm

/-- Analogue of Proposition 4.3.10(c) -/
theorem Real.pow_nonneg {x:Real} (n:ℕ) (hx: x ≥ 0) : x^n ≥ 0 := by
  exact _root_.pow_nonneg hx n

/-- Analogue of Proposition 4.3.10(c) -/
theorem Real.pow_pos {x:Real} (n:ℕ) (hx: x > 0) : x^n > 0 := by
  exact _root_.pow_pos hx n

/-- Analogue of Proposition 4.3.10(c) -/
theorem Real.pow_ge_pow (x y:Real) (n:ℕ) (hxy: x ≥ y) (hy: y ≥ 0) : x^n ≥ y^n := by
  induction' n with k ih
  · simp
  · have hx : x ≥ 0 := by linarith
    have hxk_nonneg : x^k ≥ 0 := _root_.pow_nonneg hx k
    rw [_root_.pow_succ, _root_.pow_succ]
    exact mul_le_mul ih hxy hy hxk_nonneg

/-- Analogue of Proposition 4.3.10(c) -/
theorem Real.pow_gt_pow (x y:Real) (n:ℕ) (hxy: x > y) (hy: y ≥ 0) (hn: n > 0) : x^n > y^n := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne.symm
  subst hk
  rw [_root_.pow_succ, _root_.pow_succ]
  have hx : x > 0 := by linarith
  have hxk_pos : x^k > 0 := _root_.pow_pos hx k
  have hxk_ge_yk : x^k ≥ y^k := Real.pow_ge_pow x y k (by linarith) hy
  calc
    x^k * x > x^k * y := mul_lt_mul_of_pos_left hxy hxk_pos
    _ ≥ y^k * y := mul_le_mul_of_nonneg_right hxk_ge_yk hy

/-- Analogue of Proposition 4.3.10(d) -/
theorem Real.pow_abs (x:Real) (n:ℕ) : |x|^n = |x^n| := by
  exact (abs_pow x n).symm

/-- Definition 5.6.2 (Exponentiating a real by an integer). Here we use the Mathlib definition coming from {name}`DivInvMonoid`. -/
lemma Real.pow_eq_pow (x: Real) (n:ℕ): x ^ (n:ℤ) = x ^ n := by rfl

@[simp]
lemma Real.zpow_zero (x: Real) : x ^ (0:ℤ) = 1 := by rfl

lemma Real.zpow_neg {x:Real} (n:ℕ) : x^(-n:ℤ) = 1 / (x^n) := by simp

/-- Analogue of Proposition 4.3.12(a) -/
theorem Real.zpow_add (x:Real) (n m:ℤ) (hx: x ≠ 0): x^n * x^m = x^(n+m) := by
  rw [← _root_.zpow_add₀ hx n m]

/-- Analogue of Proposition 4.3.12(a) -/
theorem Real.zpow_mul (x:Real) (n m:ℤ) : (x^n)^m = x^(n*m) := by
  rw [← _root_.zpow_mul x n m]

/-- Analogue of Proposition 4.3.12(a) -/
theorem Real.mul_zpow (x y:Real) (n:ℤ) : (x*y)^n = x^n * y^n := by
  exact _root_.mul_zpow x y n

/-- Analogue of Proposition 4.3.12(b) -/
theorem Real.zpow_pos {x:Real} (n:ℤ) (hx: x > 0) : x^n > 0 := by
  exact _root_.zpow_pos hx n

/-- Analogue of Proposition 4.3.12(b) -/
theorem Real.zpow_ge_zpow {x y:Real} {n:ℤ} (hxy: x ≥ y) (hy: y > 0) (hn: n > 0): x^n ≥ y^n := by
  apply _root_.zpow_le_zpow_left₀ <;> linarith

theorem Real.zpow_ge_zpow_ofneg {x y:Real} {n:ℤ} (hxy: x ≥ y) (hy: y > 0) (hn: n < 0) : x^n ≤ y^n := by
  have hx : x > 0 := by linarith
  have hm_pos : 0 < -n := by linarith
  have hpos_case := zpow_ge_zpow hxy hy hm_pos
  have hx_pos : x ^ (-n) > 0 := _root_.zpow_pos hx (-n)
  have hy_pos : y ^ (-n) > 0 := _root_.zpow_pos hy (-n)
  have hx_eq : x^n = (x ^ (-n))⁻¹ := by
    rw [show n = -(-n) from neg_neg n |>.symm, _root_.zpow_neg, neg_neg]
  have hy_eq : y^n = (y ^ (-n))⁻¹ := by
    rw [show n = -(-n) from neg_neg n |>.symm, _root_.zpow_neg, neg_neg]
  rw [hx_eq, hy_eq]
  -- Now show (x^(-n))⁻¹ ≤ (y^(-n))⁻¹
  have hxy' : y ^ (-n) ≤ x ^ (-n) := hpos_case
  have h1 : (x ^ (-n))⁻¹ * (x ^ (-n)) = 1 := inv_mul_cancel₀ hx_pos.ne'
  have h2 : (y ^ (-n))⁻¹ * (y ^ (-n)) = 1 := inv_mul_cancel₀ hy_pos.ne'
  have hinvx_pos : (x ^ (-n))⁻¹ > 0 := inv_pos.mpr hx_pos
  have hinvy_pos : (y ^ (-n))⁻¹ > 0 := inv_pos.mpr hy_pos
  -- (x^(-n))⁻¹ * y^(-n) ≤ (x^(-n))⁻¹ * x^(-n) = 1 = (y^(-n))⁻¹ * y^(-n)
  have step1 : (x^(-n))⁻¹ * y^(-n) ≤ (x^(-n))⁻¹ * x^(-n) :=
    mul_le_mul_of_nonneg_left hxy' hinvx_pos.le
  rw [h1] at step1
  -- step1 : (x^(-n))⁻¹ * y^(-n) ≤ 1
  -- want: (x^(-n))⁻¹ ≤ (y^(-n))⁻¹
  have hk : (x^(-n))⁻¹ * y^(-n) ≤ (y^(-n))⁻¹ * y^(-n) := by rw [h2]; exact step1
  exact le_of_mul_le_mul_right hk hy_pos

/-- Analogue of Proposition 4.3.12(c) -/
theorem Real.zpow_inj {x y:Real} {n:ℤ} (hx: x > 0) (hy : y > 0) (hn: n ≠ 0) (hxy: x^n = y^n) : x = y := by
  rcases lt_or_gt_of_ne hn with (hn_neg | hn_pos)
  · -- n < 0, reduce to positive case by taking inverses
    have hm_nonneg : 0 ≤ -n := by linarith
    have h_pow_eq : x ^ (-n) = y ^ (-n) := by
      rw [_root_.zpow_neg x n, _root_.zpow_neg y n, hxy]
    lift -n to ℕ using hm_nonneg with k hk
    have hk_pos : 0 < k := by
      have : (0:ℤ) < k := by linarith
      exact_mod_cast this
    rw [zpow_natCast x k, zpow_natCast y k] at h_pow_eq
    by_contra hne
    rcases lt_or_gt_of_ne hne with (hlt | hlt)
    · have hlt' : x ^ k < y ^ k := pow_gt_pow y x k hlt (by linarith) hk_pos
      linarith
    · have hlt' : y ^ k < x ^ k := pow_gt_pow x y k hlt (by linarith) hk_pos
      linarith
  · -- n > 0
    have hn_nonneg : 0 ≤ n := by linarith
    lift n to ℕ using hn_nonneg with k
    have hk_pos : 0 < k := by exact_mod_cast hn_pos
    rw [zpow_natCast x k, zpow_natCast y k] at hxy
    by_contra hne
    rcases lt_or_gt_of_ne hne with (hlt | hlt)
    · have hlt' : x ^ k < y ^ k := pow_gt_pow y x k hlt (by linarith) hk_pos
      linarith
    · have hlt' : y ^ k < x ^ k := pow_gt_pow x y k hlt (by linarith) hk_pos
      linarith

/-- Analogue of Proposition 4.3.12(d) -/
theorem Real.zpow_abs (x:Real) (n:ℤ) : |x|^n = |x^n| := by
  by_cases hn_nonneg : 0 ≤ n
  · lift n to ℕ using hn_nonneg with k
    rw [zpow_natCast, zpow_natCast, abs_pow]
  · have hpos : 0 ≤ -n := by linarith
    lift -n to ℕ using hpos with k hk
    have hn_eq : n = -((k : ℤ)) := by linarith
    rw [hn_eq, _root_.zpow_neg, _root_.zpow_neg, zpow_natCast, zpow_natCast]
    rw [show |x|^k = |x^k| from pow_abs x k]
    -- Goal: (|x^k|)⁻¹ = |(x^k)⁻¹|
    set y := x^k
    rcases eq_or_ne y 0 with hy | hy
    · rw [hy]; simp
    · have h_abs_ne : |y| ≠ 0 := abs_ne_zero.mpr hy
      have h_inv_ne : y⁻¹ ≠ 0 := by
        intro hh
        have : y * y⁻¹ = 0 := by rw [hh]; ring
        rw [Real.self_mul_inv hy] at this; norm_num at this
      have h1 : |y|⁻¹ * |y| = 1 := inv_mul_cancel₀ h_abs_ne
      have h2 : |y⁻¹| * |y| = 1 := by
        rw [← abs_mul, inv_mul_cancel₀ hy, abs_one]
      have := h1.trans h2.symm
      exact mul_right_cancel₀ h_abs_ne this

/-- Definition 5.6.2. We permit "junk values" when {lean}`x` is negative or {lean}`n` vanishes. -/
noncomputable abbrev Real.root (x:Real) (n:ℕ) : Real := sSup { y:Real | y ≥ 0 ∧ y^n ≤ x }

noncomputable abbrev Real.sqrt (x:Real) := x.root 2

/-- Local Archimedean helper: every real number is dominated by some natural number. -/
private theorem Real.exists_nat_gt' (x : Real) : ∃ n : ℕ, x < (n:Real) := by
  rcases lt_trichotomy x 1 with h | h | h
  · exact ⟨1, by norm_cast⟩
  · exact ⟨2, by rw [h]; norm_cast⟩
  · have h1pos : (1:Real).IsPos := by rw [Real.isPos_iff]; norm_num
    obtain ⟨M, _, hM⟩ := Real.le_mul h1pos x
    refine ⟨M, ?_⟩
    rw [show ((M:ℕ):Real) = (M:ℕ) * (1:Real) from by ring]; linarith

/-- Lemma 5.6.5 (Existence of n^th roots) -/
theorem Real.rootset_nonempty {x:Real} (hx: x ≥ 0) (n:ℕ) (hn: n ≥ 1) : { y:Real | y ≥ 0 ∧ y^n ≤ x }.Nonempty := by
  use 0
  refine ⟨le_refl _, ?_⟩
  rw [zero_pow (by omega : n ≠ 0)]; exact hx

theorem Real.rootset_bddAbove {x:Real} (n:ℕ) (hn: n ≥ 1) : BddAbove { y:Real | y ≥ 0 ∧ y^n ≤ x } := by
  -- This proof is written to follow the structure of the original text.
  rw [_root_.bddAbove_def]
  obtain h | h := le_or_gt x 1
  . use 1; intro y hy; simp at hy
    by_contra! hy'
    replace hy' : 1 < y^n := by
      have : (1:Real)^n < y^n := pow_gt_pow y 1 n hy' (by norm_num) hn
      simpa using this
    linarith
  use x; intro y hy; simp at hy
  by_contra! hy'
  replace hy' : x < y^n := by
    have hx_pos : x > 0 := by linarith
    have hxn : x^n ≥ x := by
      -- x ≥ 1 hence x^n ≥ x^1 = x
      rcases Nat.lt_or_ge n 1 with hn1 | hn1
      · omega
      · -- n ≥ 1, so x^n = x * x^(n-1) ≥ x * 1 = x
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn1
        rw [add_comm, _root_.pow_add, _root_.pow_one]
        have hxk : x^k ≥ 1 := by
          have h1n : (1:Real)^k ≤ x^k := pow_ge_pow x 1 k (by linarith) (by norm_num)
          simpa using h1n
        nlinarith
    have hyn_gt_xn : x^n < y^n := pow_gt_pow y x n hy' (by linarith) hn
    linarith
  linarith

/-- Lemma 5.6.6 (c) / Exercise 5.6.1 -/
theorem Real.root_nonneg {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) : x.root n ≥ 0 := by
  -- 0 ∈ { y | y ≥ 0 ∧ y^n ≤ x }, so sSup ≥ 0.
  have h0_mem : (0:Real) ∈ { y:Real | y ≥ 0 ∧ y^n ≤ x } := by
    refine ⟨le_refl _, ?_⟩
    rw [zero_pow (by omega : n ≠ 0)]; exact hx
  have h_lub := ExtendedReal.sSup_of_bounded ⟨0, h0_mem⟩ (rootset_bddAbove n hn)
  exact h_lub.1 h0_mem

theorem Real.pow_of_root {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) :
  (x.root n)^n = x := by
  set S := { y:Real | y ≥ 0 ∧ y^n ≤ x } with hS_def
  set α := x.root n with hα_def
  have hS_nonempty := rootset_nonempty hx n hn
  have hS_bdd := rootset_bddAbove (x := x) n hn
  have h_lub : IsLUB S α := ExtendedReal.sSup_of_bounded hS_nonempty hS_bdd
  have hα_nonneg : α ≥ 0 := root_nonneg hx hn
  have hn_pos : (n:Real) > 0 := by exact_mod_cast hn
  rcases lt_trichotomy (α^n) x with h_lt | h_eq | h_gt
  · exfalso
    -- find ε > 0 with (α+ε)^n < x, contradicting α as upper bound
    set δ := x - α^n with hδ_def
    have hδ_pos : δ > 0 := by linarith
    set C := (n:Real) * (α+1)^(n-1) with hC_def
    have h_aplus1_pos : (α+1:Real) > 0 := by linarith
    have hC_pos : C > 0 := mul_pos hn_pos (_root_.pow_pos h_aplus1_pos _)
    have hδ_isPos : δ.IsPos := (Real.isPos_iff _).mpr hδ_pos
    obtain ⟨M, hMpos, hMC⟩ := Real.le_mul hδ_isPos C
    have hM_real_pos : (M:Real) > 0 := by exact_mod_cast hMpos
    have hM_ne : (M:Real) ≠ 0 := hM_real_pos.ne'
    set ε := (1:Real) / M with hε_def
    have hε_pos : ε > 0 := by rw [hε_def]; positivity
    have hε_M : ε * (M:Real) = 1 := by
      rw [hε_def]; exact one_div_mul_cancel hM_ne
    have hε_le_1 : ε ≤ 1 := by
      have h_M_ge_1 : (M:Real) ≥ 1 := by exact_mod_cast hMpos
      have : ε * (M:Real) ≤ 1 * (M:Real) := by rw [hε_M, one_mul]; linarith
      exact le_of_mul_le_mul_right (by linarith) hM_real_pos
    have h_apl_nonneg : α + ε ≥ 0 := by linarith
    have h_bound := abs_pow_sub_pow_le (α+ε) α n
    have h_eps_abs : |ε| = ε := _root_.abs_of_pos hε_pos
    have h_max : max |α+ε| |α| = α + ε := by
      rw [abs_of_nonneg h_apl_nonneg, abs_of_nonneg hα_nonneg]
      exact max_eq_left (by linarith)
    have h_diff_eq : ((α + ε) - α : Real) = ε := by ring
    rw [h_diff_eq, h_eps_abs, h_max] at h_bound
    have h_diff : (α+ε)^n - α^n ≤ ε * (n:Real) * (α+ε)^(n-1) := by
      calc (α+ε)^n - α^n ≤ |(α+ε)^n - α^n| := le_abs_self _
        _ ≤ ε * (n:Real) * (α+ε)^(n-1) := h_bound
    have h_pow_le : (α+ε)^(n-1) ≤ (α+1)^(n-1) :=
      pow_ge_pow (α+1) (α+ε) (n-1) (by linarith) h_apl_nonneg
    have h_eps_n_nn : ε * (n:Real) ≥ 0 := mul_nonneg hε_pos.le hn_pos.le
    have h_chain : ε * (n:Real) * (α+ε)^(n-1) ≤ ε * (n:Real) * (α+1)^(n-1) :=
      mul_le_mul_of_nonneg_left h_pow_le h_eps_n_nn
    have h_eps_C_M : ε * C * (M:Real) < δ * (M:Real) := by
      have heq : ε * C * (M:Real) = C := by
        have : ε * C * (M:Real) = ε * (M:Real) * C := by ring
        rw [this, hε_M, one_mul]
      rw [heq]; linarith
    have h_eps_C : ε * C < δ :=
      lt_of_mul_lt_mul_right h_eps_C_M hM_real_pos.le
    have h_combined : (α+ε)^n - α^n < δ := by
      calc (α+ε)^n - α^n ≤ ε * (n:Real) * (α+ε)^(n-1) := h_diff
      _ ≤ ε * (n:Real) * (α+1)^(n-1) := h_chain
      _ = ε * C := by rw [hC_def]; ring
      _ < δ := h_eps_C
    have h_aeps_lt_x : (α+ε)^n < x := by linarith
    have h_aeps_in_S : (α+ε) ∈ S := ⟨h_apl_nonneg, le_of_lt h_aeps_lt_x⟩
    have h_aeps_le : α + ε ≤ α := h_lub.1 h_aeps_in_S
    linarith
  · exact h_eq
  · exfalso
    -- find ε > 0 with (α-ε)^n > x, contradicting α as least upper bound
    have hα_pos : α > 0 := by
      by_contra h_le
      push_neg at h_le
      have hα_zero : α = 0 := le_antisymm h_le hα_nonneg
      rw [hα_zero, zero_pow (by omega : n ≠ 0)] at h_gt
      linarith
    set δ := α^n - x with hδ_def
    have hδ_pos : δ > 0 := by linarith
    set C := (n:Real) * α^(n-1) with hC_def
    have hC_pos : C > 0 := mul_pos hn_pos (_root_.pow_pos hα_pos _)
    have hδ_isPos : δ.IsPos := (Real.isPos_iff _).mpr hδ_pos
    obtain ⟨M, hMpos, hMC⟩ := Real.le_mul hδ_isPos C
    have hM_real_pos : (M:Real) > 0 := by exact_mod_cast hMpos
    have hM_ne : (M:Real) ≠ 0 := hM_real_pos.ne'
    have h_invM_pos : (1:Real)/(M:Real) > 0 := by positivity
    have hα_half_pos : α/2 > 0 := by positivity
    have hα_half_lt : α/2 < α := by
      have h2 : 2 * (α/2) = α := by field_simp
      nlinarith
    set ε := min (α/2) (1/(M:Real)) with hε_def
    have hε_pos : ε > 0 := lt_min hα_half_pos h_invM_pos
    have hε_le_α2 : ε ≤ α/2 := min_le_left _ _
    have hε_le_M : ε ≤ 1/(M:Real) := min_le_right _ _
    have hε_lt_α : ε < α := lt_of_le_of_lt hε_le_α2 hα_half_lt
    have h_amε_nonneg : α - ε ≥ 0 := by linarith
    have h_bound := abs_pow_sub_pow_le α (α-ε) n
    have h_diff_eq : (α - (α - ε):Real) = ε := by ring
    have h_eps_abs : |ε| = ε := _root_.abs_of_pos hε_pos
    have h_max : max |α| |α-ε| = α := by
      rw [abs_of_nonneg hα_nonneg, abs_of_nonneg h_amε_nonneg]
      exact max_eq_left (by linarith)
    rw [h_diff_eq, h_eps_abs, h_max] at h_bound
    have h_diff_le : α^n - (α-ε)^n ≤ ε * (n:Real) * α^(n-1) := by
      calc α^n - (α-ε)^n ≤ |α^n - (α-ε)^n| := le_abs_self _
        _ ≤ ε * (n:Real) * α^(n-1) := h_bound
    have h_invM_C_M : (1/(M:Real)) * C * (M:Real) < δ * (M:Real) := by
      have heq : (1/(M:Real)) * C * (M:Real) = C := by
        have : (1/(M:Real)) * C * (M:Real) = (1/(M:Real)) * (M:Real) * C := by ring
        rw [this, one_div_mul_cancel hM_ne, one_mul]
      rw [heq]; linarith
    have h_invM_C : (1/(M:Real)) * C < δ :=
      lt_of_mul_lt_mul_right h_invM_C_M hM_real_pos.le
    have h_eps_C_lt : ε * C < δ :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_right hε_le_M hC_pos.le) h_invM_C
    have h_amε_pow_gt : (α - ε)^n > x := by
      have h1 : α^n - (α-ε)^n ≤ ε * C := by
        calc α^n - (α-ε)^n ≤ ε * (n:Real) * α^(n-1) := h_diff_le
        _ = ε * C := by rw [hC_def]; ring
      linarith
    have h_amε_ub : α - ε ∈ upperBounds S := by
      intro y hy
      obtain ⟨hy_nn, hy_pow⟩ := hy
      by_contra h_not
      push_neg at h_not
      have hy_pow_lt : y^n > x := by
        have : (α - ε)^n < y^n := pow_gt_pow y (α-ε) n h_not h_amε_nonneg hn
        linarith
      linarith
    have hα_le : α ≤ α - ε := h_lub.2 h_amε_ub
    linarith

/-- Lemma 5.6.6 (ab) / Exercise 5.6.1 -/
theorem Real.eq_root_iff_pow_eq {x y:Real} (hx: x ≥ 0) (hy: y ≥ 0) {n:ℕ} (hn: n ≥ 1) :
  y = x.root n ↔ y^n = x := by
  constructor
  · intro h; rw [h]; exact pow_of_root hx hn
  · intro h
    have hroot_nn : x.root n ≥ 0 := root_nonneg hx hn
    have h1 : (x.root n)^n = x := pow_of_root hx hn
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : y^n < (x.root n)^n := pow_gt_pow (x.root n) y n hlt hy hn
      linarith
    · have : (x.root n)^n < y^n := pow_gt_pow y (x.root n) n hgt hroot_nn hn
      linarith

/-- Lemma 5.6.6 (c) / Exercise 5.6.1 -/
theorem Real.root_pos {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) : x.root n > 0 ↔ x > 0 := by
  constructor
  · intro h
    have heq := pow_of_root hx hn
    rw [← heq]
    exact pow_pos n h
  · intro hxpos
    have hr_nn := root_nonneg hx hn
    rcases eq_or_lt_of_le hr_nn with h | h
    · exfalso
      have heq := pow_of_root hx hn
      rw [← h, zero_pow (by omega : n ≠ 0)] at heq
      linarith
    · exact h

theorem Real.root_of_pow {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) :
  (x^n).root n = x := by
  have hxpow_nn : x^n ≥ 0 := pow_nonneg n hx
  exact ((eq_root_iff_pow_eq hxpow_nn hx hn).mpr rfl).symm

/-- Lemma 5.6.6 (d) / Exercise 5.6.1 -/
theorem Real.root_mono {x y:Real} (hx: x ≥ 0) (hy: y ≥ 0) {n:ℕ} (hn: n ≥ 1) :
  x > y ↔ x.root n > y.root n := by
  have hxr_nn := root_nonneg hx hn
  have hyr_nn := root_nonneg hy hn
  constructor
  · intro hxy
    by_contra h_not
    push_neg at h_not
    have h1 : (x.root n)^n ≤ (y.root n)^n := pow_ge_pow (y.root n) (x.root n) n h_not hxr_nn
    rw [pow_of_root hx hn, pow_of_root hy hn] at h1
    linarith
  · intro h_root
    have h1 : (y.root n)^n < (x.root n)^n :=
      pow_gt_pow (x.root n) (y.root n) n h_root hyr_nn hn
    rw [pow_of_root hx hn, pow_of_root hy hn] at h1
    exact h1

/-- Lemma 5.6.6 (e) / Exercise 5.6.1 -/
theorem Real.root_of_one {k: ℕ} (hk: k ≥ 1): (1:Real).root k = 1 := by
  have h1nn : (1:Real) ≥ 0 := by norm_num
  exact ((eq_root_iff_pow_eq h1nn h1nn hk).mpr (one_pow k)).symm

theorem Real.root_one {x:Real} (hx: x > 0): x.root 1 = x := by
  have hxnn : x ≥ 0 := hx.le
  exact ((eq_root_iff_pow_eq hxnn hxnn (le_refl 1)).mpr (pow_one x)).symm

/-- Lemma 5.6.6 (e) / Exercise 5.6.1 -/
theorem Real.root_mono_of_gt_one {x : Real} (hx: x > 1) {k l: ℕ} (hkl: k > l) (hl: l ≥ 1) :
  x.root k < x.root l := by
  have hxnn : x ≥ 0 := by linarith
  have hk : k ≥ 1 := by linarith
  set r_k := x.root k with hr_k_def
  set r_l := x.root l with hr_l_def
  have h_rk_pow : r_k^k = x := pow_of_root hxnn hk
  have h_rl_pow : r_l^l = x := pow_of_root hxnn hl
  have h_rk_nn : r_k ≥ 0 := root_nonneg hxnn hk
  have h_rl_nn : r_l ≥ 0 := root_nonneg hxnn hl
  have h_rl_gt_1 : r_l > 1 := by
    by_contra h_not
    push_neg at h_not
    have : r_l^l ≤ (1:Real)^l := pow_ge_pow 1 r_l l h_not h_rl_nn
    rw [one_pow] at this
    linarith
  by_contra h_not
  push_neg at h_not
  have h1 : r_l^k ≤ r_k^k := pow_ge_pow r_k r_l k h_not h_rl_nn
  have h2 : r_l^l < r_l^k := by
    obtain ⟨d, hd_eq, hd_pos⟩ : ∃ d:ℕ, k = l + d ∧ d > 0 := ⟨k - l, by omega, by omega⟩
    rw [hd_eq, _root_.pow_add]
    have h_rl_pos : r_l > 0 := by linarith
    have h_rlpow_pos : r_l^l > 0 := _root_.pow_pos h_rl_pos l
    have h_rl_d_gt_1 : r_l^d > 1 := by
      have hh : (1:Real)^d < r_l^d := pow_gt_pow r_l 1 d h_rl_gt_1 (by norm_num) hd_pos
      simpa using hh
    have hh : r_l^l * 1 < r_l^l * r_l^d :=
      mul_lt_mul_of_pos_left h_rl_d_gt_1 h_rlpow_pos
    simpa using hh
  linarith

/-- Lemma 5.6.6 (e) / Exercise 5.6.1 -/
theorem Real.root_mono_of_lt_one {x : Real} (hx0: 0 < x) (hx: x < 1) {k l: ℕ} (hkl: k > l) (hl: l ≥ 1) :
  x.root k > x.root l := by
  have hxnn : x ≥ 0 := hx0.le
  have hk : k ≥ 1 := by linarith
  set r_k := x.root k with hr_k_def
  set r_l := x.root l with hr_l_def
  have h_rk_pow : r_k^k = x := pow_of_root hxnn hk
  have h_rl_pow : r_l^l = x := pow_of_root hxnn hl
  have h_rk_pos : r_k > 0 := (root_pos hxnn hk).mpr hx0
  have h_rl_pos : r_l > 0 := (root_pos hxnn hl).mpr hx0
  have h_rl_lt_1 : r_l < 1 := by
    by_contra h_not
    push_neg at h_not
    have : (1:Real)^l ≤ r_l^l := pow_ge_pow r_l 1 l h_not (by norm_num)
    rw [one_pow] at this
    linarith
  by_contra h_not
  push_neg at h_not
  have h1 : r_k^k ≤ r_l^k := pow_ge_pow r_l r_k k h_not h_rk_pos.le
  have h2 : r_l^k < r_l^l := by
    obtain ⟨d, hd_eq, hd_pos⟩ : ∃ d:ℕ, k = l + d ∧ d > 0 := ⟨k - l, by omega, by omega⟩
    rw [hd_eq, _root_.pow_add]
    have h_rlpow_pos : r_l^l > 0 := _root_.pow_pos h_rl_pos l
    have h_rl_d_lt_1 : r_l^d < 1 := by
      have hh : r_l^d < (1:Real)^d := pow_gt_pow 1 r_l d h_rl_lt_1 h_rl_pos.le hd_pos
      simpa using hh
    have hh : r_l^l * r_l^d < r_l^l * 1 :=
      mul_lt_mul_of_pos_left h_rl_d_lt_1 h_rlpow_pos
    simpa using hh
  linarith

/-- Lemma 5.6.6 (f) / Exercise 5.6.1 -/
theorem Real.root_mul {x y:Real} (hx: x ≥ 0) (hy: y ≥ 0) {n:ℕ} (hn: n ≥ 1) :
  (x*y).root n = (x.root n) * (y.root n) := by
  have hxy_nn : x * y ≥ 0 := mul_nonneg hx hy
  have hxr_nn := root_nonneg hx hn
  have hyr_nn := root_nonneg hy hn
  have h_prod_nn : (x.root n) * (y.root n) ≥ 0 := mul_nonneg hxr_nn hyr_nn
  symm
  rw [eq_root_iff_pow_eq hxy_nn h_prod_nn hn, Real.mul_pow,
      pow_of_root hx hn, pow_of_root hy hn]

/-- Lemma 5.6.6 (g) / Exercise 5.6.1 -/
theorem Real.root_root {x:Real} (hx: x ≥ 0) {n m:ℕ} (hn: n ≥ 1) (hm: m ≥ 1):
  (x.root n).root m = x.root (n*m) := by
  have hr_nn := root_nonneg hx hn
  have hrr_nn := root_nonneg hr_nn hm
  have hnm : n*m ≥ 1 := by
    have : 1*1 ≤ n*m := Nat.mul_le_mul hn hm
    simpa using this
  rw [eq_root_iff_pow_eq hx hrr_nn hnm]
  calc ((x.root n).root m)^(n*m)
      = ((x.root n).root m)^(m*n) := by rw [Nat.mul_comm]
    _ = (((x.root n).root m)^m)^n := by rw [← Real.pow_mul]
    _ = (x.root n)^n := by rw [pow_of_root hr_nn hm]
    _ = x := pow_of_root hx hn

theorem Real.pow_cancel {y z:Real} (hy: y > 0) (hz: z > 0) {n:ℕ} (hn: n ≥ 1)
  (h: y^n = z^n) : y = z := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have : y^n < z^n := pow_gt_pow z y n hlt (by linarith) hn
    linarith
  · have : z^n < y^n := pow_gt_pow y z n hlt (by linarith) hn
    linarith

example : ¬(∀ (y:Real) (z:Real) (n:ℕ) (_: n ≥ 1) (_: y^n = z^n), y = z) := by
  simp; refine ⟨ (-3), 3, 2, ?_, ?_, ?_ ⟩ <;> norm_num

/-- Definition 5.6.7 -/
noncomputable abbrev Real.ratPow (x:Real) (q:ℚ) : Real := (x.root q.den)^(q.num)

noncomputable instance Real.instRatPow : Pow Real ℚ where
  pow x q := x.ratPow q

theorem Rat.eq_quot (q:ℚ) : ∃ a:ℤ, ∃ b:ℕ, b > 0 ∧ q = a / b := by
  use q.num, q.den; have := q.den_nz
  refine ⟨ by omega, (Rat.num_div_den q).symm ⟩

/-- Lemma 5.6.8 -/
theorem Real.pow_root_eq_pow_root {a a':ℤ} {b b':ℕ} (hb: b > 0) (hb' : b' > 0)
  (hq : (a/b:ℚ) = (a'/b':ℚ)) {x:Real} (hx: x > 0) :
    (x.root b')^(a') = (x.root b)^(a) := by
  -- This proof is written to follow the structure of the original text.
  wlog ha: a > 0 generalizing a b a' b'
  . simp at ha
    obtain ha | ha := le_iff_lt_or_eq.mp ha
    . replace hq : ((-a:ℤ)/b:ℚ) = ((-a':ℤ)/b':ℚ) := by
        push_cast at *; ring_nf at *; simp [hq]
      specialize this hb hb' hq (by linarith)
      simpa [zpow_neg] using this
    have : a' = 0 := by
      subst ha
      simp at hq
      -- hq : 0 = a' / b'
      have hb'_pos : (0:ℚ) < (b':ℚ) := by exact_mod_cast hb'
      have : (a':ℚ) = 0 := by
        have : (0:ℚ) * (b':ℚ) = (a':ℚ) / (b':ℚ) * (b':ℚ) := by rw [← hq]
        rw [div_mul_cancel₀ _ hb'_pos.ne'] at this
        linarith
      exact_mod_cast this
    simp_all
  have : a' > 0 := by
    have hb_pos : (0:ℚ) < (b:ℚ) := by exact_mod_cast hb
    have hb'_pos : (0:ℚ) < (b':ℚ) := by exact_mod_cast hb'
    have ha' : (a':ℚ) / (b':ℚ) > 0 := by
      rw [← hq]
      exact div_pos (by exact_mod_cast ha) hb_pos
    have : (a':ℚ) > 0 := by
      rcases lt_trichotomy (a':ℚ) 0 with hlt | heq | hgt
      · exact absurd ha' (by
          have : (a':ℚ) / (b':ℚ) < 0 := div_neg_of_neg_of_pos hlt hb'_pos
          linarith)
      · rw [heq, zero_div] at ha'; linarith
      · exact hgt
    exact_mod_cast this
  field_simp at hq
  lift a to ℕ using by order
  lift a' to ℕ using by order
  norm_cast at *
  set y := x.root (a*b')
  have h1 : y = (x.root b').root a := by rw [root_root, mul_comm] <;> linarith
  have h2 : y = (x.root b).root a' := by rw [root_root, ←hq] <;> linarith
  have h3 : y^a = x.root b' := by rw [h1]; apply pow_of_root (root_nonneg _ _) <;> linarith
  have h4 : y^a' = x.root b := by rw [h2]; apply pow_of_root (root_nonneg _ _) <;> linarith
  rw [←h3, pow_mul, mul_comm, ←pow_mul, h4]

theorem Real.ratPow_def {x:Real} (hx: x > 0) (a:ℤ) {b:ℕ} (hb: b > 0) : x^(a/b:ℚ) = (x.root b)^a := by
  set q := (a/b:ℚ)
  convert pow_root_eq_pow_root hb _ _ hx
  . have := q.den_nz; omega
  rw [Rat.num_div_den q]

theorem Real.ratPow_eq_root {x:Real} (hx: x > 0) {n:ℕ} (hn: n ≥ 1) : x^(1/n:ℚ) = x.root n := by
  have hnz : n > 0 := hn
  rw [show ((1:ℚ)/(n:ℚ)) = ((1:ℤ):ℚ)/((n:ℕ):ℚ) from by push_cast; ring]
  rw [Real.ratPow_def hx 1 hnz, _root_.zpow_one]

theorem Real.ratPow_eq_pow {x:Real} (hx: x > 0) (n:ℤ) : x^(n:ℚ) = x^n := by
  rw [show ((n:ℚ)) = (n:ℚ)/((1:ℕ):ℚ) from by push_cast; ring]
  rw [Real.ratPow_def hx n (by norm_num : (1:ℕ) > 0), Real.root_one hx]

/-- Lemma 5.6.9(a) / Exercise 5.6.2 -/
theorem Real.ratPow_pos {x:Real} (hx: x > 0) (q:ℚ) : x^q > 0 := by
  have hden : q.den > 0 := q.pos
  have hxnn : x ≥ 0 := hx.le
  have hroot_pos : x.root q.den > 0 := (root_pos hxnn hden).mpr hx
  show x.ratPow q > 0
  unfold Real.ratPow
  exact _root_.zpow_pos hroot_pos q.num

/-- Lemma 5.6.9(b) / Exercise 5.6.2 -/
theorem Real.ratPow_add {x:Real} (hx: x > 0) (q r:ℚ) : x^(q+r) = x^q * x^r := by
  set a := q.num
  set b := q.den
  set a' := r.num
  set b' := r.den
  have hb : b > 0 := q.pos
  have hb' : b' > 0 := r.pos
  have hbb' : b * b' > 0 := Nat.mul_pos hb hb'
  have hb_ne : (b:ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  have hb'_ne : (b':ℚ) ≠ 0 := by exact_mod_cast hb'.ne'
  have hq_eq : q = ((a * b':ℤ) : ℚ) / ((b * b':ℕ) : ℚ) := by
    have hq0 : q = (a:ℚ) / (b:ℚ) := (Rat.num_div_den q).symm
    rw [hq0]; push_cast; field_simp
  have hr_eq : r = ((a' * b:ℤ) : ℚ) / ((b * b':ℕ) : ℚ) := by
    have hr0 : r = (a':ℚ) / (b':ℚ) := (Rat.num_div_den r).symm
    rw [hr0]; push_cast; field_simp
  have hqr_eq : q + r = ((a * b' + a' * b:ℤ) : ℚ) / ((b * b':ℕ) : ℚ) := by
    rw [hq_eq, hr_eq]; push_cast; field_simp
  rw [show x^q = x^(((a * b':ℤ) : ℚ) / ((b * b':ℕ) : ℚ)) from by rw [← hq_eq],
      show x^r = x^(((a' * b:ℤ) : ℚ) / ((b * b':ℕ) : ℚ)) from by rw [← hr_eq],
      show x^(q+r) = x^(((a * b' + a' * b:ℤ) : ℚ) / ((b * b':ℕ) : ℚ)) from by rw [← hqr_eq]]
  rw [Real.ratPow_def hx _ hbb', Real.ratPow_def hx _ hbb', Real.ratPow_def hx _ hbb']
  rw [← _root_.zpow_add₀ ((root_pos hx.le hbb').mpr hx).ne']

/-- Lemma 5.6.9(b) / Exercise 5.6.2 -/
theorem Real.ratPow_ratPow {x:Real} (hx: x > 0) (q r:ℚ) : (x^q)^r = x^(q*r) := by
  set a := q.num
  set b := q.den
  set a' := r.num
  set b' := r.den
  have hb : b > 0 := q.pos
  have hb' : b' > 0 := r.pos
  have hbb' : b * b' > 0 := Nat.mul_pos hb hb'
  have hb_ne : (b:ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  have hb'_ne : (b':ℚ) ≠ 0 := by exact_mod_cast hb'.ne'
  have hxq_pos : x^q > 0 := ratPow_pos hx q
  have hroot_b_pos : x.root b > 0 := (root_pos hx.le hb).mpr hx
  have hroot_bb'_pos : x.root (b*b') > 0 := (root_pos hx.le hbb').mpr hx
  have hroot_b_nn : x.root b ≥ 0 := root_nonneg hx.le hb
  have hroot_bb'_nn : x.root (b*b') ≥ 0 := root_nonneg hx.le hbb'
  have h_xq : x^q = (x.root b)^a := by
    rw [show q = ((a:ℤ):ℚ)/((b:ℕ):ℚ) from by
      have := (Rat.num_div_den q).symm; exact this]
    exact Real.ratPow_def hx a hb
  have h_xqr : (x^q)^r = ((x^q).root b')^a' := by
    rw [show r = ((a':ℤ):ℚ)/((b':ℕ):ℚ) from by
      have := (Rat.num_div_den r).symm; exact this]
    exact Real.ratPow_def hxq_pos a' hb'
  have h_qr_eq : q * r = ((a * a':ℤ):ℚ)/((b*b':ℕ):ℚ) := by
    have hq0 : q = (a:ℚ)/(b:ℚ) := (Rat.num_div_den q).symm
    have hr0 : r = (a':ℚ)/(b':ℚ) := (Rat.num_div_den r).symm
    rw [hq0, hr0]; push_cast; field_simp
  have h_xqr_target : x^(q*r) = (x.root (b*b'))^(a*a') := by
    rw [h_qr_eq]; exact Real.ratPow_def hx (a*a') hbb'
  -- ((x.root b)^a).root b' = (x.root (b*b'))^a
  have h_root_eq : ((x.root b)^a).root b' = (x.root (b*b'))^a := by
    have hroot_b_a_pos : ((x.root b)^a:Real) > 0 := _root_.zpow_pos hroot_b_pos a
    have hroot_bb_a_pos : ((x.root (b*b'))^a:Real) > 0 := _root_.zpow_pos hroot_bb'_pos a
    symm
    rw [eq_root_iff_pow_eq hroot_b_a_pos.le hroot_bb_a_pos.le hb']
    have h_root_split : x.root (b*b') = (x.root b).root b' := by rw [root_root hx.le hb hb']
    calc ((x.root (b*b'))^a)^(b':ℕ)
        = (x.root (b*b'))^(a * (b':ℤ)) := by
          rw [← zpow_natCast ((x.root (b*b'))^a) b', ← _root_.zpow_mul]
      _ = (x.root (b*b'))^((b':ℤ) * a) := by ring_nf
      _ = ((x.root (b*b'))^(b':ℤ))^a := by rw [_root_.zpow_mul]
      _ = ((x.root (b*b'))^(b':ℕ))^a := by rw [zpow_natCast]
      _ = ((x.root b).root b' ^ (b':ℕ))^a := by rw [h_root_split]
      _ = (x.root b)^a := by rw [pow_of_root hroot_b_nn hb']
  rw [h_xqr, h_xq, h_root_eq, h_xqr_target]
  exact (_root_.zpow_mul (x.root (b*b')) a a').symm

/-- Lemma 5.6.9(c) / Exercise 5.6.2 -/
theorem Real.ratPow_neg {x:Real} (hx: x > 0) (q:ℚ) : x^(-q) = 1 / x^q := by
  set a := q.num
  set b := q.den
  have hb : b > 0 := q.pos
  have hroot_pos : x.root b > 0 := (root_pos hx.le hb).mpr hx
  have h_xq : x^q = (x.root b)^a := by
    rw [show q = ((a:ℤ):ℚ)/((b:ℕ):ℚ) from by
      have := (Rat.num_div_den q).symm; exact this]
    exact Real.ratPow_def hx a hb
  have h_xnq : x^(-q) = (x.root b)^(-a) := by
    rw [show -q = ((-a:ℤ):ℚ)/((b:ℕ):ℚ) from by
      have hq0 : q = (a:ℚ)/(b:ℚ) := (Rat.num_div_den q).symm
      rw [hq0]; push_cast; ring]
    exact Real.ratPow_def hx (-a) hb
  rw [h_xq, h_xnq, _root_.zpow_neg, one_div]

/-- Lemma 5.6.9(d) / Exercise 5.6.2 -/
theorem Real.ratPow_mono {x y:Real} (hx: x > 0) (hy: y > 0) {q:ℚ} (h: q > 0) : x > y ↔ x^q > y^q := by
  set a := q.num
  set b := q.den
  have hb : b > 0 := q.pos
  have ha : a > 0 := Rat.num_pos.mpr h
  have hq_eq : q = ((a:ℤ):ℚ)/((b:ℕ):ℚ) := by
    have := (Rat.num_div_den q).symm; exact this
  have h_xq : x^q = (x.root b)^a := by rw [hq_eq]; exact Real.ratPow_def hx a hb
  have h_yq : y^q = (y.root b)^a := by rw [hq_eq]; exact Real.ratPow_def hy a hb
  have hxr_pos : x.root b > 0 := (root_pos hx.le hb).mpr hx
  have hyr_pos : y.root b > 0 := (root_pos hy.le hb).mpr hy
  rw [h_xq, h_yq]
  constructor
  · intro hxy
    have hroot_lt : y.root b < x.root b := (root_mono hx.le hy.le hb).mp hxy
    exact zpow_lt_zpow_left₀ ha hyr_pos.le hroot_lt
  · intro hpow
    by_contra hne
    push_neg at hne
    rcases eq_or_lt_of_le hne with heq | hlt
    · rw [heq] at hpow; linarith
    · have hroot_le : x.root b ≤ y.root b := (root_mono hy.le hx.le hb).mp hlt |>.le
      have : (x.root b)^a ≤ (y.root b)^a := zpow_le_zpow_left₀ ha.le hxr_pos.le hroot_le
      linarith

/-- Lemma 5.6.9(e) / Exercise 5.6.2 -/
theorem Real.ratPow_mono_of_gt_one {x:Real} (hx: x > 1) {q r:ℚ} : x^q > x^r ↔ q > r := by
  have hx_pos : x > 0 := by linarith
  have h_one_pos : (1:Real) > 0 := by norm_num
  -- helper: 1^s = 1 for any s:ℚ
  have h_one_ratPow : ∀ s:ℚ, (1:Real)^s = 1 := by
    intro s
    show (1:Real).ratPow s = 1
    unfold Real.ratPow
    rw [Real.root_of_one s.pos, one_zpow]
  -- helper: x^s > 0 for any s
  have h_pos : ∀ s:ℚ, x^s > 0 := fun s => ratPow_pos hx_pos s
  -- helper: x^0 = 1
  have h_zero : x^(0:ℚ) = 1 := by
    have h := ratPow_add hx_pos 0 0
    rw [zero_add] at h
    have hxq_pos := h_pos 0
    -- h : x^0 = x^0 * x^0; cancel x^0 from x^0 * 1 = x^0 = x^0 * x^0
    have h' : x^(0:ℚ) * 1 = x^(0:ℚ) * x^(0:ℚ) := by rw [mul_one]; exact h
    exact (mul_left_cancel₀ hxq_pos.ne' h').symm
  -- helper: x^s > 1 ↔ s > 0
  have h_aux : ∀ s:ℚ, x^s > 1 ↔ s > 0 := by
    intro s
    constructor
    · intro hs
      by_contra h_not
      push_neg at h_not
      rcases eq_or_lt_of_le h_not with heq | hlt
      · rw [heq, h_zero] at hs; linarith
      · -- s < 0, so -s > 0; x^(-s) > 1; and x^(-s) * x^s = x^0 = 1
        have hns : -s > 0 := by linarith
        have h1 : x^(-s) > 1 := by
          have := (ratPow_mono hx_pos h_one_pos hns).mp hx
          rw [h_one_ratPow (-s)] at this; exact this
        have hprod : x^(-s) * x^s = 1 := by
          rw [← ratPow_add hx_pos (-s) s, neg_add_cancel, h_zero]
        have hxs_pos : x^s > 0 := h_pos s
        have hxns_pos : x^(-s) > 0 := h_pos (-s)
        -- x^(-s) * x^s = 1, x^(-s) > 1, x^s > 1, so product > 1, contradiction
        have : x^(-s) * x^s > 1 * 1 := by
          exact mul_lt_mul' h1.le hs (by linarith) (by linarith)
        rw [hprod] at this; linarith
    · intro hs
      have := (ratPow_mono hx_pos h_one_pos hs).mp hx
      rw [h_one_ratPow s] at this; exact this
  -- main proof: use x^q = x^(q-r) * x^r
  have h_split : ∀ s:ℚ, x^q = x^(q-s) * x^s := by
    intro s
    rw [← ratPow_add hx_pos (q-s) s, sub_add_cancel]
  constructor
  · intro hqr
    have hxr_pos := h_pos r
    have hxqr_pos := h_pos (q-r)
    have h_eq : x^q = x^(q-r) * x^r := h_split r
    -- hqr : x^q > x^r, h_eq : x^q = x^(q-r) * x^r, so x^(q-r) * x^r > x^r = 1 * x^r
    have : x^(q-r) * x^r > 1 * x^r := by rw [one_mul]; rw [h_eq] at hqr; exact hqr
    have hgt1 : x^(q-r) > 1 := lt_of_mul_lt_mul_right this hxr_pos.le
    have := (h_aux (q-r)).mp hgt1
    linarith
  · intro hqr
    have hs : q - r > 0 := by linarith
    have h1 : x^(q-r) > 1 := (h_aux (q-r)).mpr hs
    have hxr_pos := h_pos r
    have h_eq : x^q = x^(q-r) * x^r := h_split r
    rw [h_eq]
    have := mul_lt_mul_of_pos_right h1 hxr_pos
    linarith

/-- Lemma 5.6.9(e) / Exercise 5.6.2 -/
theorem Real.ratPow_mono_of_lt_one {x:Real} (hx0: 0 < x) (hx: x < 1) {q r:ℚ} : x^q > x^r ↔ q < r := by
  have h_one_pos : (1:Real) > 0 := by norm_num
  -- helper: 1^s = 1 for any s:ℚ
  have h_one_ratPow : ∀ s:ℚ, (1:Real)^s = 1 := by
    intro s
    show (1:Real).ratPow s = 1
    unfold Real.ratPow
    rw [Real.root_of_one s.pos, one_zpow]
  have h_pos : ∀ s:ℚ, x^s > 0 := fun s => ratPow_pos hx0 s
  have h_zero : x^(0:ℚ) = 1 := by
    have h := ratPow_add hx0 0 0
    rw [zero_add] at h
    have hxq_pos := h_pos 0
    have h' : x^(0:ℚ) * 1 = x^(0:ℚ) * x^(0:ℚ) := by rw [mul_one]; exact h
    exact (mul_left_cancel₀ hxq_pos.ne' h').symm
  -- helper: x^s < 1 ↔ s > 0
  have h_aux : ∀ s:ℚ, x^s < 1 ↔ s > 0 := by
    intro s
    constructor
    · intro hs
      by_contra h_not
      push_neg at h_not
      rcases eq_or_lt_of_le h_not with heq | hlt
      · rw [heq, h_zero] at hs; linarith
      · -- s < 0
        have hns : -s > 0 := by linarith
        have h1 : x^(-s) < 1 := by
          have := (ratPow_mono h_one_pos hx0 hns).mp hx
          rw [h_one_ratPow (-s)] at this; exact this
        have hprod : x^(-s) * x^s = 1 := by
          rw [← ratPow_add hx0 (-s) s, neg_add_cancel, h_zero]
        have hxs_pos : x^s > 0 := h_pos s
        have hxns_pos : x^(-s) > 0 := h_pos (-s)
        have : x^(-s) * x^s < 1 * 1 := by
          exact mul_lt_mul' h1.le hs (by linarith) (by linarith)
        rw [hprod] at this; linarith
    · intro hs
      have := (ratPow_mono h_one_pos hx0 hs).mp hx
      rw [h_one_ratPow s] at this; exact this
  have h_split : ∀ s:ℚ, x^q = x^(q-s) * x^s := by
    intro s
    rw [← ratPow_add hx0 (q-s) s, sub_add_cancel]
  constructor
  · intro hqr
    have hxr_pos := h_pos r
    have h_eq : x^q = x^(q-r) * x^r := h_split r
    -- x^q > x^r → x^(q-r) * x^r > x^r = 1 * x^r → x^(q-r) > 1 → q - r < 0 → q < r
    rw [h_eq] at hqr
    have h2 : x^(q-r) * x^r > 1 * x^r := by rw [one_mul]; exact hqr
    have hgt1 : x^(q-r) > 1 := lt_of_mul_lt_mul_right h2 hxr_pos.le
    -- Now hgt1 : x^(q-r) > 1; we want q - r < 0
    by_contra h_not
    push_neg at h_not
    rcases eq_or_lt_of_le h_not with heq | hlt
    · rw [show q - r = 0 from by linarith, h_zero] at hgt1; linarith
    · have hpos : q - r > 0 := by linarith
      have := (h_aux (q-r)).mpr hpos
      linarith
  · intro hqr
    have hs : q - r < 0 := by linarith
    have hns : -(q - r) > 0 := by linarith
    have h_neg_lt : x^(-(q-r)) < 1 := (h_aux (-(q-r))).mpr hns
    -- x^(q-r) > 1: since x^(-(q-r)) * x^(q-r) = 1 and x^(-(q-r)) < 1
    have hprod : x^(-(q-r)) * x^(q-r) = 1 := by
      rw [← ratPow_add hx0 (-(q-r)) (q-r), neg_add_cancel, h_zero]
    have hxs_pos : x^(q-r) > 0 := h_pos (q-r)
    have hxns_pos : x^(-(q-r)) > 0 := h_pos (-(q-r))
    have h_xqr_gt_1 : x^(q-r) > 1 := by
      by_contra h_not
      push_neg at h_not
      rcases eq_or_lt_of_le h_not with heq | hlt
      · rw [heq, mul_one] at hprod; linarith
      · have : x^(-(q-r)) * x^(q-r) < 1 * 1 := mul_lt_mul' h_neg_lt.le hlt (by linarith) (by linarith)
        rw [hprod] at this; linarith
    have hxr_pos := h_pos r
    have h_eq : x^q = x^(q-r) * x^r := h_split r
    rw [h_eq]
    have := mul_lt_mul_of_pos_right h_xqr_gt_1 hxr_pos
    linarith

/-- Lemma 5.6.9(f) / Exercise 5.6.2 -/
theorem Real.ratPow_mul {x y:Real} (hx: x > 0) (hy: y > 0) (q:ℚ) : (x*y)^q = x^q * y^q := by
  set a := q.num
  set b := q.den
  have hb : b > 0 := q.pos
  have hxy_pos : x * y > 0 := mul_pos hx hy
  have hq_eq : q = ((a:ℤ):ℚ)/((b:ℕ):ℚ) := by
    have := (Rat.num_div_den q).symm; exact this
  have h_xq : x^q = (x.root b)^a := by rw [hq_eq]; exact Real.ratPow_def hx a hb
  have h_yq : y^q = (y.root b)^a := by rw [hq_eq]; exact Real.ratPow_def hy a hb
  have h_xyq : (x*y)^q = ((x*y).root b)^a := by rw [hq_eq]; exact Real.ratPow_def hxy_pos a hb
  rw [h_xq, h_yq, h_xyq, Real.root_mul hx.le hy.le hb, _root_.mul_zpow]

/-- Exercise 5.6.3 -/
theorem Real.pow_even (x:Real) {n:ℕ} (hn: Even n) : x^n ≥ 0 := by
  obtain ⟨k, rfl⟩ := hn
  rw [show k + k = 2 * k from by ring, _root_.pow_mul]
  exact Real.pow_nonneg k (sq_nonneg x)

/-- Helper: ratPow is monotone (≤ form) for positive base and positive q. -/
private theorem Real.ratPow_le_ratPow {x y:Real} (hx: x > 0) (hy: y > 0) {q:ℚ} (hq: q > 0)
  (hxy: x ≤ y) : x^q ≤ y^q := by
  rcases eq_or_lt_of_le hxy with heq | hlt
  · rw [heq]
  · exact ((Real.ratPow_mono hy hx hq).mp hlt).le

/-- Exercise 5.6.5 -/
theorem Real.max_ratPow {x y:Real} (hx: x > 0) (hy: y > 0) {q:ℚ} (hq: q > 0) :
  max (x^q) (y^q) = (max x y)^q := by
  rcases le_total x y with hxy | hxy
  · rw [max_eq_right hxy, max_eq_right (Real.ratPow_le_ratPow hx hy hq hxy)]
  · rw [max_eq_left hxy, max_eq_left (Real.ratPow_le_ratPow hy hx hq hxy)]

/-- Exercise 5.6.5 -/
theorem Real.min_ratPow {x y:Real} (hx: x > 0) (hy: y > 0) {q:ℚ} (hq: q > 0) :
  min (x^q) (y^q) = (min x y)^q := by
  rcases le_total x y with hxy | hxy
  · rw [min_eq_left hxy, min_eq_left (Real.ratPow_le_ratPow hx hy hq hxy)]
  · rw [min_eq_right hxy, min_eq_right (Real.ratPow_le_ratPow hy hx hq hxy)]

/-- Final part of Exercise 5.6.5: versions for negative {lit}`q`. For {lit}`q < 0`, the
exponentiation reverses order: larger base gives smaller power. So {lit}`max`/{lit}`min`
swap roles. -/
theorem Real.max_ratPow_neg {x y:Real} (hx: x > 0) (hy: y > 0) {q:ℚ} (hq: q < 0) :
  max (x^q) (y^q) = (min x y)^q := by
  have hnq : -q > 0 := by linarith
  have hx_neg_pos : x^(-q) > 0 := Real.ratPow_pos hx (-q)
  have hy_neg_pos : y^(-q) > 0 := Real.ratPow_pos hy (-q)
  have hxq_eq : x^q = 1 / x^(-q) := by
    have h := Real.ratPow_neg hx (-q)
    rw [neg_neg] at h; exact h
  have hyq_eq : y^q = 1 / y^(-q) := by
    have h := Real.ratPow_neg hy (-q)
    rw [neg_neg] at h; exact h
  rcases le_total x y with hxy | hxy
  · rw [min_eq_left hxy]
    rw [hxq_eq, hyq_eq]
    have h1 : y^(-q) ≥ x^(-q) := Real.ratPow_le_ratPow hx hy hnq hxy
    have hinv_le : (y^(-q))⁻¹ ≤ (x^(-q))⁻¹ := by
      have h2 : (x^(-q))⁻¹ * x^(-q) = 1 := inv_mul_cancel₀ hx_neg_pos.ne'
      have h3 : (y^(-q))⁻¹ * x^(-q) ≤ (y^(-q))⁻¹ * y^(-q) :=
        mul_le_mul_of_nonneg_left h1 (inv_pos.mpr hy_neg_pos).le
      rw [inv_mul_cancel₀ hy_neg_pos.ne'] at h3
      have h4 : (y^(-q))⁻¹ * x^(-q) ≤ (x^(-q))⁻¹ * x^(-q) := by rw [h2]; exact h3
      exact le_of_mul_le_mul_right h4 hx_neg_pos
    have : x^q = (x^(-q))⁻¹ := by rw [hxq_eq, one_div]
    rw [one_div, one_div]
    rw [hxq_eq, one_div] at this
    exact max_eq_left hinv_le
  · rw [min_eq_right hxy]
    rw [hxq_eq, hyq_eq]
    have h1 : x^(-q) ≥ y^(-q) := Real.ratPow_le_ratPow hy hx hnq hxy
    have hinv_le : (x^(-q))⁻¹ ≤ (y^(-q))⁻¹ := by
      have h2 : (y^(-q))⁻¹ * y^(-q) = 1 := inv_mul_cancel₀ hy_neg_pos.ne'
      have h3 : (x^(-q))⁻¹ * y^(-q) ≤ (x^(-q))⁻¹ * x^(-q) :=
        mul_le_mul_of_nonneg_left h1 (inv_pos.mpr hx_neg_pos).le
      rw [inv_mul_cancel₀ hx_neg_pos.ne'] at h3
      have h4 : (x^(-q))⁻¹ * y^(-q) ≤ (y^(-q))⁻¹ * y^(-q) := by rw [h2]; exact h3
      exact le_of_mul_le_mul_right h4 hy_neg_pos
    rw [one_div, one_div]
    exact max_eq_right hinv_le

theorem Real.min_ratPow_neg {x y:Real} (hx: x > 0) (hy: y > 0) {q:ℚ} (hq: q < 0) :
  min (x^q) (y^q) = (max x y)^q := by
  have hnq : -q > 0 := by linarith
  have hx_neg_pos : x^(-q) > 0 := Real.ratPow_pos hx (-q)
  have hy_neg_pos : y^(-q) > 0 := Real.ratPow_pos hy (-q)
  have hxq_eq : x^q = 1 / x^(-q) := by
    have h := Real.ratPow_neg hx (-q)
    rw [neg_neg] at h; exact h
  have hyq_eq : y^q = 1 / y^(-q) := by
    have h := Real.ratPow_neg hy (-q)
    rw [neg_neg] at h; exact h
  rcases le_total x y with hxy | hxy
  · rw [max_eq_right hxy]
    rw [hxq_eq, hyq_eq]
    have h1 : y^(-q) ≥ x^(-q) := Real.ratPow_le_ratPow hx hy hnq hxy
    have hinv_le : (y^(-q))⁻¹ ≤ (x^(-q))⁻¹ := by
      have h2 : (x^(-q))⁻¹ * x^(-q) = 1 := inv_mul_cancel₀ hx_neg_pos.ne'
      have h3 : (y^(-q))⁻¹ * x^(-q) ≤ (y^(-q))⁻¹ * y^(-q) :=
        mul_le_mul_of_nonneg_left h1 (inv_pos.mpr hy_neg_pos).le
      rw [inv_mul_cancel₀ hy_neg_pos.ne'] at h3
      have h4 : (y^(-q))⁻¹ * x^(-q) ≤ (x^(-q))⁻¹ * x^(-q) := by rw [h2]; exact h3
      exact le_of_mul_le_mul_right h4 hx_neg_pos
    rw [one_div, one_div]
    exact min_eq_right hinv_le
  · rw [max_eq_left hxy]
    rw [hxq_eq, hyq_eq]
    have h1 : x^(-q) ≥ y^(-q) := Real.ratPow_le_ratPow hy hx hnq hxy
    have hinv_le : (x^(-q))⁻¹ ≤ (y^(-q))⁻¹ := by
      have h2 : (y^(-q))⁻¹ * y^(-q) = 1 := inv_mul_cancel₀ hy_neg_pos.ne'
      have h3 : (x^(-q))⁻¹ * y^(-q) ≤ (x^(-q))⁻¹ * x^(-q) :=
        mul_le_mul_of_nonneg_left h1 (inv_pos.mpr hx_neg_pos).le
      rw [inv_mul_cancel₀ hx_neg_pos.ne'] at h3
      have h4 : (x^(-q))⁻¹ * y^(-q) ≤ (y^(-q))⁻¹ * y^(-q) := by rw [h2]; exact h3
      exact le_of_mul_le_mul_right h4 hy_neg_pos
    rw [one_div, one_div]
    exact min_eq_left hinv_le

-- Final part of Exercise 5.6.5: state and prove versions of the above lemmas covering the case of negative q.

end Chapter5
