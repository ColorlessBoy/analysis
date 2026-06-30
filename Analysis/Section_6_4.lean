import Mathlib.Tactic
import Analysis.Section_6_3

/-!
# Analysis I, Section 6.4: Limsup, liminf, and limit points

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Lim sup and lim inf of sequences
- Limit points of sequences
- Comparison and squeeze tests
- Completeness of the reals

-/

abbrev Real.Adherent (ε:ℝ) (a:Chapter6.Sequence) (x:ℝ) := ∃ n ≥ a.m, ε.Close (a n) x

abbrev Real.ContinuallyAdherent (ε:ℝ) (a:Chapter6.Sequence) (x:ℝ) :=
  ∀ N ≥ a.m, ε.Adherent (a.from N) x

namespace Chapter6

open EReal

abbrev Sequence.LimitPoint (a:Sequence) (x:ℝ) : Prop :=
  ∀ ε > (0:ℝ), ε.ContinuallyAdherent a x

theorem Sequence.limit_point_def (a:Sequence) (x:ℝ) :
  a.LimitPoint x ↔ ∀ ε > 0, ∀ N ≥ a.m, ∃ n ≥ N, |a n - x| ≤ ε := by
    unfold LimitPoint Real.ContinuallyAdherent Real.Adherent
    simp [Real.Close, Real.dist_eq]
    constructor
    · intro h ε hε N hN
      rcases h ε hε N hN with ⟨n, ⟨hn₁, hn₂⟩, hclose⟩
      exact ⟨n, hn₂, by simpa [hn₁, hn₂] using hclose⟩
    · intro h ε hε N hN
      rcases h ε hε N hN with ⟨n, hn, hclose⟩
      have hn₁ : a.m ≤ n := le_trans hN hn
      exact ⟨n, ⟨hn₁, hn⟩, by simpa [hn₁, hn] using hclose⟩

noncomputable abbrev Example_6_4_3 : Sequence := (fun (n:ℕ) ↦ 1 - (10:ℝ)^(-(n:ℤ)-1))

/-- Example 6.4.3 -/
example : (0.1:ℝ).Adherent Example_6_4_3 0.8 := by
  unfold Real.Adherent
  refine ⟨0, by simp, ?_⟩
  unfold Real.Close
  rw [Real.dist_eq]
  norm_num [Example_6_4_3]

/-- Example 6.4.3 -/
example : ¬ (0.1:ℝ).ContinuallyAdherent Example_6_4_3 0.8 := by
  unfold Real.ContinuallyAdherent
  intro h
  have hN := h 1 (by unfold Example_6_4_3; simp)
  unfold Real.Adherent at hN
  rcases hN with ⟨n, hn, hclose⟩
  have hn' : n ≥ (1:ℤ) := hn
  have h_eval : (Example_6_4_3.from 1) n = Example_6_4_3 n :=
    Sequence.from_eval _ hn'
  rw [h_eval] at hclose
  rw [Real.Close, Real.dist_eq] at hclose
  have h_formula : Example_6_4_3 n = 1 - (10:ℝ)^(-(n:ℤ)-1) := by
    dsimp [Example_6_4_3]; simp [show (n:ℤ) ≥ 0 from by omega]
  rw [h_formula] at hclose
  have h_exp : (-(n:ℤ)-1 : ℤ) ≤ (-(1:ℤ)-1 : ℤ) := by omega
  have h_pow_bound : (10:ℝ)^(-(n:ℤ)-1 : ℤ) ≤ (10:ℝ)^(-(1:ℤ)-1 : ℤ) :=
    (zpow_le_zpow_iff_right₀ (a := (10:ℝ)) (by norm_num : 1 < (10:ℝ))).mpr h_exp
  have h_val : (10:ℝ)^(-(1:ℤ)-1 : ℤ) = (0.01:ℝ) := by norm_num
  have h_bound : (10:ℝ)^(-(n:ℤ)-1 : ℤ) ≤ (0.01:ℝ) :=
    calc
      (10:ℝ)^(-(n:ℤ)-1 : ℤ) ≤ (10:ℝ)^(-(1:ℤ)-1 : ℤ) := h_pow_bound
      _ = (0.01:ℝ) := h_val
  have h_nonneg : 0 ≤ 1 - (10:ℝ)^(-(n:ℤ)-1) - 0.8 := by
    nlinarith
  rw [abs_of_nonneg h_nonneg] at hclose
  have h_contra : 0.1 ≤ (10:ℝ)^(-(n:ℤ)-1 : ℤ) := by
    nlinarith
  nlinarith

/-- Example 6.4.3 -/
example : (0.1:ℝ).ContinuallyAdherent Example_6_4_3 1 := by
  unfold Real.ContinuallyAdherent Real.Adherent
  intro N hN
  dsimp [Example_6_4_3] at hN
  have hm : (Example_6_4_3.from N).m = N := by
    dsimp [Example_6_4_3, Sequence.from, Sequence.mk']
    rw [max_eq_right hN]
  refine ⟨N, by rw [hm], ?_⟩
  unfold Real.Close
  rw [Real.dist_eq]
  have h_eval : (Example_6_4_3.from N) N = Example_6_4_3 N :=
    Sequence.from_eval _ (by omega)
  rw [h_eval]
  have h_formula : Example_6_4_3 N = 1 - (10:ℝ)^(-(N:ℤ)-1) := by
    dsimp [Example_6_4_3]; simp [hN]
  rw [h_formula]
  have h_diff : |(1 - (10:ℝ)^(-(N:ℤ)-1)) - 1| = |-(10:ℝ)^(-(N:ℤ)-1)| := by
    simp
  rw [h_diff]
  rw [abs_neg]
  have h_nonneg : 0 ≤ (10:ℝ)^(-(N:ℤ)-1 : ℤ) := by positivity
  rw [abs_of_nonneg h_nonneg]
  have h_pow_exponent : (-(N:ℤ)-1 : ℤ) ≤ (-(0:ℤ)-1 : ℤ) := by omega
  have h_pow : (10:ℝ)^(-(N:ℤ)-1 : ℤ) ≤ (10:ℝ)^(-(0:ℤ)-1 : ℤ) :=
    zpow_le_zpow_right₀ (a := (10:ℝ)) (by norm_num : (1:ℝ) ≤ 10) h_pow_exponent
  have h_val : (10:ℝ)^(-(0:ℤ)-1 : ℤ) = 0.1 := by norm_num
  calc
    (10:ℝ)^(-(N:ℤ)-1 : ℤ) ≤ (10:ℝ)^(-(0:ℤ)-1 : ℤ) := h_pow
    _ = 0.1 := h_val

/-- Example 6.4.3 -/
example : Example_6_4_3.LimitPoint 1 := by
  rw [Sequence.limit_point_def]
  intro ε hε N hN
  have hlt : (1/10 : ℝ) < 1 := by norm_num
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε hlt
  set n := max N (k : ℤ) with hn_def
  have hn : n ≥ N := le_max_left _ _
  have hkz : (k : ℤ) ≤ n := le_max_right _ _
  refine ⟨n, hn, ?_⟩
  have h_expr : Example_6_4_3 n = 1 - (10 : ℝ) ^ (-(n : ℤ) - 1) := by
    dsimp [Example_6_4_3]
    have h0 : (N : ℤ) ≥ 0 := by
      -- hN : N ≥ Example_6_4_3.m, and Example_6_4_3.m = 0
      simpa [Example_6_4_3] using hN
    have hn_nonneg : (n : ℤ) ≥ 0 := le_trans h0 hn
    simp [hn_nonneg]
  rw [h_expr]
  have h_diff : |(1 - (10 : ℝ) ^ (-(n : ℤ) - 1)) - 1| = |-(10 : ℝ) ^ (-(n : ℤ) - 1)| := by
    simp
  rw [h_diff, abs_neg]
  have h_nonneg : 0 ≤ (10 : ℝ) ^ (-(n : ℤ) - 1 : ℤ) := by positivity
  rw [abs_of_nonneg h_nonneg]
  have h_exp : (-(n : ℤ) - 1 : ℤ) ≤ (-(k : ℤ) - 1 : ℤ) := by omega
  have h_pow_le' : (10 : ℝ) ^ (-(n : ℤ) - 1 : ℤ) ≤
    (10 : ℝ) ^ (-(k : ℤ) - 1 : ℤ) :=
    zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ (10 : ℝ)) h_exp
  have hexp : (-(k : ℤ) - 1 : ℤ) = (-1 : ℤ) + (-(k : ℤ)) := by ring
  have h_pow_eq : (10 : ℝ) ^ (-(k : ℤ) - 1 : ℤ) = (1/10 : ℝ) ^ (k+1 : ℕ) := by
    calc
      (10 : ℝ) ^ (-(k : ℤ) - 1 : ℤ) = (10 : ℝ) ^ ((-1 : ℤ) + (-(k : ℤ))) := by rw [hexp]
      _ = (10 : ℝ) ^ (-1 : ℤ) * (10 : ℝ) ^ (-(k : ℤ)) := by
        rw [zpow_add₀ (show (10 : ℝ) ≠ 0 from by norm_num)]
      _ = (1/10 : ℝ) * (10 : ℝ) ^ (-(k : ℤ)) := by norm_num
      _ = (1/10 : ℝ) * ((10 : ℝ) ^ (k : ℤ))⁻¹ := by rw [zpow_neg]
      _ = (1/10 : ℝ) * ((10 : ℝ)⁻¹ ^ (k : ℤ)) := by rw [inv_zpow]
      _ = (1/10 : ℝ) * ((1/10 : ℝ) ^ (k : ℤ)) := by norm_num
      _ = (1/10 : ℝ) * ((1/10 : ℝ) ^ (k : ℕ)) := by simp
      _ = (1/10 : ℝ) ^ (k+1 : ℕ) := by simp [pow_succ, mul_comm]
  have h_pow_dec : (1/10 : ℝ) ^ (k+1 : ℕ) ≤ (1/10 : ℝ) ^ (k : ℕ) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  calc
    (10 : ℝ) ^ (-(n : ℤ) - 1 : ℤ) ≤ (10 : ℝ) ^ (-(k : ℤ) - 1 : ℤ) := h_pow_le'
    _ = (1/10 : ℝ) ^ (k+1 : ℕ) := h_pow_eq
    _ ≤ (1/10 : ℝ) ^ (k : ℕ) := h_pow_dec
    _ ≤ ε := by linarith

noncomputable abbrev Example_6_4_4 : Sequence :=
  (fun (n:ℕ) ↦ (-1:ℝ)^n * (1 + (10:ℝ)^(-(n:ℤ)-1)))

/-- Example 6.4.4 -/
example : (0.1:ℝ).Adherent Example_6_4_4 1 := by
  use 0
  unfold Real.Close
  rw [Real.dist_eq]
  norm_num [Example_6_4_4]

/-- Example 6.4.4 -/
example : (0.1:ℝ).ContinuallyAdherent Example_6_4_4 1 := by
  unfold Real.ContinuallyAdherent Real.Adherent
  intro N hN
  have hNpos : (N : ℤ) ≥ 0 := by
    simpa [Example_6_4_4] using hN
  have hm : (Example_6_4_4.from N).m = N := by
    dsimp [Example_6_4_4, Sequence.from, Sequence.mk']
    rw [max_eq_right hNpos]
  refine ⟨2*N, by rw [hm]; nlinarith, ?_⟩
  unfold Real.Close
  rw [Real.dist_eq]
  have h_eval : (Example_6_4_4.from N) (2*N) = Example_6_4_4 (2*N) :=
    Sequence.from_eval _ (show (2*N : ℤ) ≥ N from by nlinarith)
  rw [h_eval]
  have h_nonneg : (2*N : ℤ) ≥ 0 := by nlinarith
  have h_parity : (-1 : ℝ)^((2*N : ℤ).toNat : ℕ) = 1 := by
    have hn : (2*N : ℤ).toNat = 2*(Int.toNat N) := by omega
    simp [hn]
  have h_formula : Example_6_4_4 (2*N) = 1 + (10:ℝ)^(-(2*N : ℤ)-1) := by
    dsimp [Example_6_4_4]
    simp [h_nonneg, h_parity]
  rw [h_formula]
  have h_diff : |(1 + (10:ℝ)^(-(2*N : ℤ)-1)) - 1| = |(10:ℝ)^(-(2*N : ℤ)-1)| := by
    simp
  rw [h_diff]
  have h_nonneg_pow : 0 ≤ (10:ℝ)^(-(2*N : ℤ)-1 : ℤ) := by positivity
  rw [abs_of_nonneg h_nonneg_pow]
  have h_exp : (-(2*N : ℤ)-1 : ℤ) ≤ (-(0 : ℤ)-1 : ℤ) := by omega
  have h_pow : (10:ℝ)^(-(2*N : ℤ)-1 : ℤ) ≤ (10:ℝ)^(-(0 : ℤ)-1 : ℤ) :=
    zpow_le_zpow_right₀ (a := (10:ℝ)) (by norm_num : (1:ℝ) ≤ 10) h_exp
  have h_val : (10:ℝ)^(-(0 : ℤ)-1 : ℤ) = 0.1 := by norm_num
  calc
    (10:ℝ)^(-(2*N : ℤ)-1 : ℤ) ≤ (10:ℝ)^(-(0 : ℤ)-1 : ℤ) := h_pow
    _ = 0.1 := h_val

/-- Example 6.4.4 -/
example : Example_6_4_4.LimitPoint 1 := by
  rw [Sequence.limit_point_def]
  intro ε hε N hN
  have hlt : (1/10 : ℝ) < 1 := by norm_num
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε hlt
  set n := 2*max N (k : ℤ) with hn_def
  have hN_nonneg : (0 : ℤ) ≤ N := by
    simpa [Example_6_4_4] using hN
  have hn_nonneg : n ≥ 0 := by
    dsimp [n]
    omega
  have hnN : n ≥ N := by
    have hN_max : N ≤ max N (k : ℤ) := le_max_left _ _
    calc
      n = 2 * max N (k : ℤ) := rfl
      _ ≥ max N (k : ℤ) := by
        have : max N (k : ℤ) ≥ 0 := le_trans hN_nonneg hN_max
        omega
      _ ≥ N := hN_max
  refine ⟨n, hnN, ?_⟩
  · have h_parity : (-1 : ℝ)^(n.toNat : ℕ) = 1 := by
      have hn_even : n.toNat = 2*((max N (k : ℤ)).toNat) := by
        dsimp [n]; omega
      simp [hn_even]
    have h_expr : Example_6_4_4 n = 1 + (10 : ℝ)^(-(n : ℤ) - 1) := by
      dsimp [Example_6_4_4]
      simp [hn_nonneg, h_parity]
    rw [h_expr]
    have h_diff : |(1 + (10 : ℝ)^(-(n : ℤ) - 1)) - 1| = |(10 : ℝ)^(-(n : ℤ) - 1)| := by
      simp
    rw [h_diff]
    have h_nonneg_pow : 0 ≤ (10 : ℝ)^(-(n : ℤ) - 1 : ℤ) := by positivity
    rw [abs_of_nonneg h_nonneg_pow]
    have hkz : (k : ℤ) ≤ n := by
      have hk_max : (k : ℤ) ≤ max N (k : ℤ) := le_max_right _ _
      calc
        (k : ℤ) ≤ max N (k : ℤ) := hk_max
        _ ≤ 2*max N (k : ℤ) := by
          have : max N (k : ℤ) ≥ 0 := le_trans hN_nonneg (le_max_left _ _)
          omega
        _ = n := rfl.symm
    have h_exp : (-(n : ℤ) - 1 : ℤ) ≤ (-(k : ℤ) - 1 : ℤ) := by omega
    have h_pow_le' : (10 : ℝ)^(-(n : ℤ) - 1 : ℤ) ≤ (10 : ℝ)^(-(k : ℤ) - 1 : ℤ) :=
      zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ (10 : ℝ)) h_exp
    have hexp : (-(k : ℤ) - 1 : ℤ) = (-1 : ℤ) + (-(k : ℤ)) := by ring
    have h_pow_eq : (10 : ℝ)^(-(k : ℤ) - 1 : ℤ) = (1/10 : ℝ)^(k+1 : ℕ) := by
      calc
        (10 : ℝ)^(-(k : ℤ) - 1 : ℤ) = (10 : ℝ)^((-1 : ℤ) + (-(k : ℤ))) := by rw [hexp]
        _ = (10 : ℝ)^(-1 : ℤ) * (10 : ℝ)^(-(k : ℤ)) := by
          rw [zpow_add₀ (show (10 : ℝ) ≠ 0 from by norm_num)]
        _ = (1/10 : ℝ) * (10 : ℝ)^(-(k : ℤ)) := by norm_num
        _ = (1/10 : ℝ) * ((10 : ℝ)^(k : ℤ))⁻¹ := by rw [zpow_neg]
        _ = (1/10 : ℝ) * ((10 : ℝ)⁻¹ ^ (k : ℤ)) := by rw [inv_zpow]
        _ = (1/10 : ℝ) * ((1/10 : ℝ)^(k : ℤ)) := by norm_num
        _ = (1/10 : ℝ) * ((1/10 : ℝ)^(k : ℕ)) := by simp
        _ = (1/10 : ℝ)^(k+1 : ℕ) := by simp [pow_succ, mul_comm]
    have h_pow_dec : (1/10 : ℝ)^(k+1 : ℕ) ≤ (1/10 : ℝ)^(k : ℕ) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    calc
      (10 : ℝ)^(-(n : ℤ) - 1 : ℤ) ≤ (10 : ℝ)^(-(k : ℤ) - 1 : ℤ) := h_pow_le'
      _ = (1/10 : ℝ)^(k+1 : ℕ) := h_pow_eq
      _ ≤ (1/10 : ℝ)^(k : ℕ) := h_pow_dec
      _ ≤ ε := by linarith

/-- Example 6.4.4 -/
example : Example_6_4_4.LimitPoint (-1) := by
  rw [Sequence.limit_point_def]
  intro ε hε N hN
  have hlt : (1/10 : ℝ) < 1 := by norm_num
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε hlt
  set n := 2*max N (k : ℤ) + 1 with hn_def
  have hN_nonneg : (0 : ℤ) ≤ N := by
    simpa [Example_6_4_4] using hN
  have hn_nonneg : n ≥ 0 := by
    dsimp [n]
    omega
  have hnN : n ≥ N := by
    have hN_max : N ≤ max N (k : ℤ) := le_max_left _ _
    calc
      n = 2 * max N (k : ℤ) + 1 := rfl
      _ ≥ 2 * max N (k : ℤ) := by omega
      _ ≥ max N (k : ℤ) := by
        have : max N (k : ℤ) ≥ 0 := le_trans hN_nonneg hN_max
        omega
      _ ≥ N := hN_max
  refine ⟨n, hnN, ?_⟩
  have h_parity : (-1 : ℝ)^(n.toNat : ℕ) = -1 := by
    have hn_odd : n.toNat = 2*((max N (k : ℤ)).toNat) + 1 := by
      dsimp [n]; omega
    calc
      (-1 : ℝ)^(n.toNat : ℕ) = (-1 : ℝ)^(2*((max N (k : ℤ)).toNat) + 1 : ℕ) := by rw [hn_odd]
      _ = ((-1 : ℝ)^(2*((max N (k : ℤ)).toNat) : ℕ)) * (-1 : ℝ) := by rw [pow_succ]
      _ = 1 * (-1 : ℝ) := by simp
      _ = -1 := by simp
  have h_expr : Example_6_4_4 n = -(1 + (10 : ℝ)^(-(n : ℤ) - 1)) := by
    dsimp [Example_6_4_4]
    simp [hn_nonneg, h_parity]
  rw [h_expr]
  have h_diff : |(-(1 + (10 : ℝ)^(-(n : ℤ) - 1)) - (-1))| = |(10 : ℝ)^(-(n : ℤ) - 1)| := by
    simp
  rw [h_diff]
  have h_nonneg_pow : 0 ≤ (10 : ℝ)^(-(n : ℤ) - 1 : ℤ) := by positivity
  rw [abs_of_nonneg h_nonneg_pow]
  have hkz : (k : ℤ) ≤ n := by
    have hk_max : (k : ℤ) ≤ max N (k : ℤ) := le_max_right _ _
    calc
      (k : ℤ) ≤ max N (k : ℤ) := hk_max
      _ ≤ 2*max N (k : ℤ) := by
        have : max N (k : ℤ) ≥ 0 := le_trans hN_nonneg (le_max_left _ _)
        omega
      _ ≤ 2*max N (k : ℤ) + 1 := by omega
      _ = n := rfl.symm
  have h_exp : (-(n : ℤ) - 1 : ℤ) ≤ (-(k : ℤ) - 1 : ℤ) := by omega
  have h_pow_le' : (10 : ℝ)^(-(n : ℤ) - 1 : ℤ) ≤ (10 : ℝ)^(-(k : ℤ) - 1 : ℤ) :=
    zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ (10 : ℝ)) h_exp
  have hexp : (-(k : ℤ) - 1 : ℤ) = (-1 : ℤ) + (-(k : ℤ)) := by ring
  have h_pow_eq : (10 : ℝ)^(-(k : ℤ) - 1 : ℤ) = (1/10 : ℝ)^(k+1 : ℕ) := by
    calc
      (10 : ℝ)^(-(k : ℤ) - 1 : ℤ) = (10 : ℝ)^((-1 : ℤ) + (-(k : ℤ))) := by rw [hexp]
      _ = (10 : ℝ)^(-1 : ℤ) * (10 : ℝ)^(-(k : ℤ)) := by
        rw [zpow_add₀ (show (10 : ℝ) ≠ 0 from by norm_num)]
      _ = (1/10 : ℝ) * (10 : ℝ)^(-(k : ℤ)) := by norm_num
      _ = (1/10 : ℝ) * ((10 : ℝ)^(k : ℤ))⁻¹ := by rw [zpow_neg]
      _ = (1/10 : ℝ) * ((10 : ℝ)⁻¹ ^ (k : ℤ)) := by rw [inv_zpow]
      _ = (1/10 : ℝ) * ((1/10 : ℝ)^(k : ℤ)) := by norm_num
      _ = (1/10 : ℝ) * ((1/10 : ℝ)^(k : ℕ)) := by simp
      _ = (1/10 : ℝ)^(k+1 : ℕ) := by simp [pow_succ, mul_comm]
  have h_pow_dec : (1/10 : ℝ)^(k+1 : ℕ) ≤ (1/10 : ℝ)^(k : ℕ) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  calc
    (10 : ℝ)^(-(n : ℤ) - 1 : ℤ) ≤ (10 : ℝ)^(-(k : ℤ) - 1 : ℤ) := h_pow_le'
    _ = (1/10 : ℝ)^(k+1 : ℕ) := h_pow_eq
    _ ≤ (1/10 : ℝ)^(k : ℕ) := h_pow_dec
    _ ≤ ε := by linarith

/-- Example 6.4.4 -/
example : ¬ Example_6_4_4.LimitPoint 0 := by
  rw [Sequence.limit_point_def]
  intro h
  have h_lim := h 0.5 (by norm_num : (0 : ℝ) < 0.5) (0 : ℤ) (by
    unfold Example_6_4_4; simp)
  rcases h_lim with ⟨n, hn, hclose⟩
  have hn_nonneg : (0 : ℤ) ≤ n := hn
  have h_val : |Example_6_4_4 n| = 1 + (10 : ℝ)^(-(n : ℤ) - 1) := by
    have h_expr : Example_6_4_4 n = (-1 : ℝ)^(n.toNat : ℕ) * (1 + (10 : ℝ)^(-(n : ℤ) - 1)) := by
      dsimp [Example_6_4_4]; simp [hn_nonneg]
    rw [h_expr]
    calc
      |(-1 : ℝ)^(n.toNat : ℕ) * (1 + (10 : ℝ)^(-(n : ℤ) - 1))| =
        |(-1 : ℝ)^(n.toNat : ℕ)| * |1 + (10 : ℝ)^(-(n : ℤ) - 1)| := by rw [_root_.abs_mul]
      _ = 1 * |1 + (10 : ℝ)^(-(n : ℤ) - 1)| := by simp
      _ = |1 + (10 : ℝ)^(-(n : ℤ) - 1)| := by simp
      _ = 1 + (10 : ℝ)^(-(n : ℤ) - 1) := by
        have hpos : 0 < (10 : ℝ)^(-(n : ℤ) - 1 : ℤ) := by positivity
        rw [abs_of_pos (by nlinarith)]
  have : |Example_6_4_4 n - 0| = |Example_6_4_4 n| := by simp
  rw [this] at hclose
  rw [h_val] at hclose
  have h_gt : 1 + (10 : ℝ)^(-(n : ℤ) - 1) > (0.5 : ℝ) := by
    have hpos : 0 < (10 : ℝ)^(-(n : ℤ) - 1 : ℤ) := by positivity
    nlinarith
  nlinarith

/-- Proposition 6.4.5 / Exercise 6.4.1 -/
theorem Sequence.limit_point_of_limit {a:Sequence} {x:ℝ} (h: a.TendsTo x) : a.LimitPoint x := by
  rw [Sequence.limit_point_def]
  have hTends := (Sequence.tendsTo_iff a x).mp h
  intro ε hε N hN
  rcases hTends ε hε with ⟨N₀, hN₀⟩
  refine ⟨max N N₀, le_max_left _ _, ?_⟩
  exact hN₀ (max N N₀) (le_max_right _ _)

/--
  A technical issue uncovered by the formalization: the upper and lower sequences of a real
  sequence take values in the extended reals rather than the reals, so the definitions need to be
  adjusted accordingly.
-/
noncomputable abbrev Sequence.upperseq (a:Sequence) : ℤ → EReal := fun N ↦ (a.from N).sup

noncomputable abbrev Sequence.limsup (a:Sequence) : EReal :=
  sInf { x | ∃ N ≥ a.m, x = a.upperseq N }

noncomputable abbrev Sequence.lowerseq (a:Sequence) : ℤ → EReal := fun N ↦ (a.from N).inf

noncomputable abbrev Sequence.liminf (a:Sequence) : EReal :=
  sSup { x | ∃ N ≥ a.m, x = a.lowerseq N }

noncomputable abbrev Example_6_4_7 : Sequence := (fun (n:ℕ) ↦ (-1:ℝ)^n * (1 + (10:ℝ)^(-(n:ℤ)-1)))

lemma le_pow_ten {k n : ℤ} (hk : k ≥ n) : (10 : ℝ)^(-(k : ℤ)-1) ≤ (10 : ℝ)^(-(n : ℤ)-1) := by
  have h_exp : (-(k : ℤ)-1 : ℤ) ≤ (-(n : ℤ)-1 : ℤ) := by omega
  exact (zpow_le_zpow_iff_right₀ (a := (10:ℝ)) (by norm_num : 1 < (10:ℝ))).mpr h_exp

lemma neg_one_pow_even (n : ℕ) (h : Even n) : ((-1 : ℝ) ^ n) = 1 := by
  rcases h with ⟨k, hk⟩
  calc
    (-1 : ℝ) ^ n = (-1 : ℝ) ^ (k + k) := by rw [hk]
    _ = ((-1 : ℝ) ^ k) * ((-1 : ℝ) ^ k) := by rw [pow_add]
    _ = ((-1 : ℝ) ^ k) ^ 2 := by ring
    _ = (-1 : ℝ) ^ (k*2) := by rw [pow_mul]
    _ = (-1 : ℝ) ^ (2*k) := by ring
    _ = ((-1 : ℝ) ^ 2) ^ k := by rw [pow_mul]
    _ = 1 ^ k := by norm_num
    _ = 1 := by simp

lemma neg_one_pow_odd (n : ℕ) (h : ¬ Even n) : ((-1 : ℝ) ^ n) = -1 := by
  have h_mod : n % 2 = 1 := by
    have h_mod2 := Nat.mod_two_eq_zero_or_one n
    rcases h_mod2 with h0 | h1
    · exfalso; exact h (by rw [Nat.even_iff]; exact h0)
    · exact h1
  have h_pow2 : ((-1 : ℝ) ^ 2) = 1 := by norm_num
  calc
    (-1 : ℝ) ^ n = (-1 : ℝ) ^ (2*(n / 2) + n % 2) := by rw [Nat.div_add_mod n 2]
    _ = (-1 : ℝ) ^ (2*(n / 2)) * (-1 : ℝ) ^ (n % 2) := by rw [pow_add]
    _ = ((-1 : ℝ) ^ 2) ^ (n / 2) * (-1 : ℝ) ^ (n % 2) := by rw [← pow_mul, mul_comm]
    _ = 1 ^ (n / 2) * (-1 : ℝ) ^ (n % 2) := by rw [h_pow2]
    _ = (-1 : ℝ) ^ (n % 2) := by simp
    _ = (-1 : ℝ) ^ 1 := by rw [h_mod]
    _ = -1 := by simp

lemma upperseq_formula (n:ℕ) :
    Example_6_4_7.upperseq n = (if Even n then (1 + (10:ℝ)^(-(n:ℤ)-1) : ℝ) else (1 + (10:ℝ)^(-(n:ℤ)-2) : ℝ)) := by
  unfold Sequence.upperseq
  by_cases h : Even n
  · have h_sup : (Example_6_4_7.from (n : ℤ)).sup = (1 + (10 : ℝ)^(-(n : ℤ)-1) : ℝ) := by
      have hm : (Example_6_4_7.from (n : ℤ)).m = (n : ℤ) := by simp
      have hn_nonneg : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast (Nat.zero_le n)
      have h_val_n : (Example_6_4_7.from (n : ℤ)) (n : ℤ) = (1 + (10 : ℝ)^(-(n : ℤ)-1) : ℝ) := by
        simp [hn_nonneg, neg_one_pow_even n h]
      apply le_antisymm
      · apply Sequence.sup_le_upper
        intro k hk
        have hk' : k ≥ (n : ℤ) := by simpa [hm] using hk
        have hk_nonneg : k ≥ 0 := by omega
        have h_val_k : (Example_6_4_7.from (n : ℤ)) k = Example_6_4_7 k := Sequence.from_eval _ hk'
        rw [h_val_k]
        have h_expr : Example_6_4_7 k = ((-1 : ℝ) ^ (k.toNat : ℕ)) * (1 + (10 : ℝ)^(-(k : ℤ)-1)) := by
          simp [hk_nonneg]
        rw [h_expr]
        rcases neg_one_pow_eq_or ℝ (k.toNat : ℕ) with hneg | hneg
        · rw [hneg, one_mul]
          have h_bound : (1 : ℝ) + (10 : ℝ)^(-(k : ℤ)-1) ≤ (1 : ℝ) + (10 : ℝ)^(-(n : ℤ)-1) := by
            nlinarith [le_pow_ten hk']
          exact_mod_cast h_bound
        · rw [hneg]
          have h_bound : ((-1 : ℝ) * (1 + (10 : ℝ)^(-(k : ℤ)-1)) : ℝ) ≤ (1 : ℝ) + (10 : ℝ)^(-(n : ℤ)-1) := by
            have h_eq : (-1 : ℝ) * (1 + (10 : ℝ)^(-(k : ℤ)-1)) = -(1 + (10 : ℝ)^(-(k : ℤ)-1)) := by ring
            rw [h_eq]
            have hz_nonneg : 0 ≤ (10 : ℝ)^(-(k : ℤ)-1) := zpow_nonneg (by norm_num : (0 : ℝ) ≤ 10) _
            have hz_nonneg' : 0 ≤ (10 : ℝ)^(-(n : ℤ)-1) := zpow_nonneg (by norm_num : (0 : ℝ) ≤ 10) _
            nlinarith
          exact_mod_cast h_bound
      · have h_sup_ge : ((1 + (10 : ℝ)^(-(n : ℤ)-1) : ℝ) : EReal) ≤ (Example_6_4_7.from (n : ℤ)).sup := by
          calc
            ((1 + (10 : ℝ)^(-(n : ℤ)-1) : ℝ) : EReal) = (Example_6_4_7.from (n : ℤ)) (n : ℤ) := by
              exact_mod_cast h_val_n.symm
            _ ≤ (Example_6_4_7.from (n : ℤ)).sup := Sequence.le_sup (by simp)
        exact h_sup_ge
    simp [h, h_sup]
  · have h_sup : (Example_6_4_7.from (n : ℤ)).sup = (1 + (10 : ℝ)^(-(n : ℤ)-2) : ℝ) := by
      have hm : (Example_6_4_7.from (n : ℤ)).m = (n : ℤ) := by simp
      have hn_nonneg' : (0 : ℤ) ≤ (n : ℤ) + 1 := by omega
      have h_next_even : Even (n+1) := by
        rcases Nat.even_or_odd n with (h_even | h_odd)
        · exfalso; exact h h_even
        · exact h_odd.add_one
      have h_val_np1 : (Example_6_4_7.from (n : ℤ)) ((n : ℤ) + 1) = (1 + (10 : ℝ)^(-(n : ℤ)-2) : ℝ) := by
        simp [hn_nonneg', neg_one_pow_even (n+1) h_next_even]
        ring
      apply le_antisymm
      · apply Sequence.sup_le_upper
        intro k hk
        have hk' : k ≥ (n : ℤ) := by simpa [hm] using hk
        have hk_nonneg : k ≥ 0 := by omega
        have h_val_k : (Example_6_4_7.from (n : ℤ)) k = Example_6_4_7 k := Sequence.from_eval _ hk'
        rw [h_val_k]
        have h_expr : Example_6_4_7 k = ((-1 : ℝ) ^ (k.toNat : ℕ)) * (1 + (10 : ℝ)^(-(k : ℤ)-1)) := by
          simp [hk_nonneg]
        rw [h_expr]
        rcases neg_one_pow_eq_or ℝ (k.toNat : ℕ) with hneg | hneg
        · rw [hneg, one_mul]
          by_cases hk_gt : k > (n : ℤ)
          · have hkp1 : k ≥ (n : ℤ) + 1 := by omega
            have h_bound : (1 : ℝ) + (10 : ℝ)^(-(k : ℤ)-1) ≤ (1 : ℝ) + (10 : ℝ)^(-(n : ℤ)-2) := by
              have hle : (10 : ℝ)^(-(k : ℤ)-1) ≤ (10 : ℝ)^(-((n : ℤ)+1)-1) := le_pow_ten hkp1
              have h_exp : -((n : ℤ)+1)-1 = -(n : ℤ)-2 := by ring
              calc
                (1 : ℝ) + (10 : ℝ)^(-(k : ℤ)-1) ≤ (1 : ℝ) + (10 : ℝ)^(-((n : ℤ)+1)-1) := by nlinarith
                _ = (1 : ℝ) + (10 : ℝ)^(-(n : ℤ)-2) := by rw [h_exp]
            exact_mod_cast h_bound
          · have hk_eq : k = (n : ℤ) := by omega
            subst hk_eq
            have : ((-1 : ℝ) ^ ((n : ℤ).toNat : ℕ)) = -1 := by
              simp [neg_one_pow_odd n h]
            rw [this] at hneg
            norm_num at hneg
        · rw [hneg]
          have h_bound : ((-1 : ℝ) * (1 + (10 : ℝ)^(-(k : ℤ)-1)) : ℝ) ≤ (1 : ℝ) + (10 : ℝ)^(-(n : ℤ)-2) := by
            have h_eq : (-1 : ℝ) * (1 + (10 : ℝ)^(-(k : ℤ)-1)) = -(1 + (10 : ℝ)^(-(k : ℤ)-1)) := by ring
            rw [h_eq]
            have hz_nonneg : 0 ≤ (10 : ℝ)^(-(k : ℤ)-1) := zpow_nonneg (by norm_num : (0 : ℝ) ≤ 10) _
            have hz_nonneg' : 0 ≤ (10 : ℝ)^(-(n : ℤ)-2) := zpow_nonneg (by norm_num : (0 : ℝ) ≤ 10) _
            nlinarith
          exact_mod_cast h_bound
      · have h_sup_ge : ((1 + (10 : ℝ)^(-(n : ℤ)-2) : ℝ) : EReal) ≤ (Example_6_4_7.from (n : ℤ)).sup := by
          calc
            ((1 + (10 : ℝ)^(-(n : ℤ)-2) : ℝ) : EReal) = (Example_6_4_7.from (n : ℤ)) ((n : ℤ) + 1) := by
              exact_mod_cast h_val_np1.symm
            _ ≤ (Example_6_4_7.from (n : ℤ)).sup := Sequence.le_sup (by simp)
        exact h_sup_ge
    simp [h, h_sup]

example : Example_6_4_7.limsup = 1 := by
  unfold Sequence.limsup
  have hm : Example_6_4_7.m = (0 : ℤ) := by
    unfold Example_6_4_7; simp
  rw [hm]
  let S := {x | ∃ N ≥ (0 : ℤ), x = Example_6_4_7.upperseq N}
  have h_nonempty : S.Nonempty := by
    refine ⟨Example_6_4_7.upperseq (0 : ℤ), ?_⟩
    refine ⟨(0 : ℤ), le_refl _, rfl⟩
  have h_ge_one : ∀ a ∈ S, (1 : EReal) ≤ a := by
    intro a ha
    rcases ha with ⟨N, hN, rfl⟩
    have h_nonneg : N ≥ 0 := hN
    have hN_cast : (N.toNat : ℤ) = N := Int.toNat_of_nonneg h_nonneg
    have h_upp_eq : Example_6_4_7.upperseq N = Example_6_4_7.upperseq (N.toNat : ℕ) := by
      simp [hN_cast]
    rw [h_upp_eq, upperseq_formula (N.toNat : ℕ)]
    rw [hN_cast]
    have h_val : (1 : ℝ) ≤ (if Even (N.toNat : ℕ) then (1 : ℝ) + (10 : ℝ)^(-(N : ℤ)-1) else (1 : ℝ) + (10 : ℝ)^(-(N : ℤ)-2)) := by
      have h_nonneg_pow1 : 0 ≤ (10 : ℝ)^(-(N : ℤ)-1) := zpow_nonneg (by norm_num : (0 : ℝ) ≤ 10) _
      have h_nonneg_pow2 : 0 ≤ (10 : ℝ)^(-(N : ℤ)-2) := zpow_nonneg (by norm_num : (0 : ℝ) ≤ 10) _
      split <;> nlinarith
    exact_mod_cast h_val
  have h_gt_exists : ∀ (w : EReal), (1 : EReal) < w → ∃ a ∈ S, a < w := by
    intro w hw
    rcases w with (w|w)
    · exfalso; exact not_lt_bot hw
    · rcases w with (w|w)
      · -- w = ⊤
        have h_upp_lt_top : Example_6_4_7.upperseq (0 : ℤ) < ⊤ := by
          have h := upperseq_formula 0
          calc
            Example_6_4_7.upperseq (0 : ℤ) = ((1 : ℝ) + (10 : ℝ)^(-(0 : ℤ)-1) : ℝ) := by
              simpa using h
            _ = ((11/10 : ℝ) : EReal) := by norm_num
            _ < ⊤ := by simp
        refine ⟨Example_6_4_7.upperseq (0 : ℤ), ?_, h_upp_lt_top⟩
        refine ⟨(0 : ℤ), le_refl _, rfl⟩
      · -- w = (c : ℝ) where c > 1
        have hc : (1 : ℝ) < w := by exact_mod_cast (show (1 : EReal) < (w : EReal) from hw)
        have h_ε_pos : 0 < w - 1 := by linarith
        rcases exists_pow_lt_of_lt_one h_ε_pos (by norm_num : (1/10 : ℝ) < 1) with ⟨k, hk⟩
        have h_expr : (10 : ℝ)^(-(k : ℤ)-1) < w - 1 := by
          have h_eq : (10 : ℝ)^(-(k : ℤ)-1) = ((1/10 : ℝ) ^ (k+1 : ℕ)) := by
            calc
              (10 : ℝ)^(-(k : ℤ)-1) = (10 : ℝ)^(-(k+1 : ℤ)) := by
                rw [show -(k : ℤ) - 1 = -(k+1 : ℤ) by omega]
              _ = ((10 : ℝ)⁻¹)^(k+1 : ℤ) := by simp
              _ = ((10 : ℝ)⁻¹)^(k+1 : ℕ) := by
                simpa using (zpow_natCast ((10 : ℝ)⁻¹) (k+1))
              _ = ((1/10 : ℝ) ^ (k+1 : ℕ)) := by norm_num
          rw [h_eq]
          have h_lt_pow : ((1/10 : ℝ) ^ (k+1 : ℕ)) < ((1/10 : ℝ) ^ (k : ℕ)) := by
            have h_pow : (10 : ℝ) ^ (k : ℕ) < (10 : ℝ) ^ (k+1 : ℕ) :=
              pow_lt_pow_right₀ (by norm_num : 1 < (10 : ℝ)) (by omega : k < k+1)
            have h_pos_k : 0 < (10 : ℝ) ^ (k : ℕ) := pow_pos (by norm_num : 0 < (10 : ℝ)) _
            have h_pos_k1 : 0 < (10 : ℝ) ^ (k+1 : ℕ) := pow_pos (by norm_num : 0 < (10 : ℝ)) _
            calc
              (1/10 : ℝ) ^ (k+1 : ℕ) = ((10 : ℝ) ^ (k+1 : ℕ))⁻¹ := by
                simp [div_eq_inv_mul]
              _ < ((10 : ℝ) ^ (k : ℕ))⁻¹ := by
                simpa using (one_div_lt_one_div h_pos_k1 h_pos_k).mpr h_pow
              _ = (1/10 : ℝ) ^ (k : ℕ) := by simp [div_eq_inv_mul]
          have h_pow_lt_ε : ((1/10 : ℝ) ^ (k : ℕ)) < w - 1 := hk
          exact lt_trans h_lt_pow h_pow_lt_ε
        have h_upp_lt : Example_6_4_7.upperseq (k : ℕ) < (w : EReal) := by
          rw [upperseq_formula k]
          have h_val : (if Even (k : ℕ) then (1 : ℝ) + (10 : ℝ)^(-(k : ℤ)-1) else (1 : ℝ) + (10 : ℝ)^(-(k : ℤ)-2)) < w := by
            split
            · nlinarith
            · have h_expr2 : (10 : ℝ)^(-(k : ℤ)-2) ≤ (10 : ℝ)^(-(k : ℤ)-1) := by
                have h_exp : (-(k : ℤ)-2 : ℤ) ≤ (-(k : ℤ)-1 : ℤ) := by omega
                have h_one_lt_ten : 1 < (10 : ℝ) := by norm_num
                have h_le := (zpow_le_zpow_iff_right₀ (a := (10 : ℝ)) h_one_lt_ten).mpr h_exp
                exact h_le
              nlinarith
          exact_mod_cast h_val
        refine ⟨Example_6_4_7.upperseq (k : ℕ), ?_, h_upp_lt⟩
        refine ⟨(k : ℤ), ?_, rfl⟩
        exact_mod_cast (Nat.zero_le k)
  exact csInf_eq_of_forall_ge_of_forall_gt_exists_lt h_nonempty h_ge_one h_gt_exists

lemma lowerseq_formula (n:ℕ) :
    Example_6_4_7.lowerseq n = (if Even n then -(1 + (10:ℝ)^(-(n:ℤ)-2) : ℝ) else -(1 + (10:ℝ)^(-(n:ℤ)-1) : ℝ)) := by
  unfold Sequence.lowerseq
  by_cases h : Even n
  · have hm : (Example_6_4_7.from (n : ℤ)).m = (n : ℤ) := by simp
    have hn_nonneg' : (0 : ℤ) ≤ (n : ℤ) + 1 := by omega
    have h_next_odd : ¬ Even (n+1) := by
      rcases h with ⟨k, hk⟩
      intro h_even
      rcases h_even with ⟨m, hm'⟩
      omega
    have h_val_np1 : (Example_6_4_7.from (n : ℤ)) ((n : ℤ) + 1) = (-(1 + (10 : ℝ)^(-(n : ℤ)-2) : ℝ) : ℝ) := by
      calc
        (Example_6_4_7.from (n : ℤ)) ((n : ℤ) + 1) = Example_6_4_7 ((n : ℤ) + 1) :=
          Sequence.from_eval _ (by omega)
        _ = ((-1 : ℝ) ^ (n+1 : ℕ)) * (1 + (10 : ℝ)^(-((n : ℤ) + 1 : ℤ)-1)) := by
          simp [hn_nonneg']
        _ = (-1 : ℝ) * (1 + (10 : ℝ)^(-(n : ℤ)-2 : ℤ)) := by
          simp [neg_one_pow_odd (n+1) h_next_odd]
          ring
        _ = -(1 + (10 : ℝ)^(-(n : ℤ)-2) : ℝ) := by ring
    have h_inf : (Example_6_4_7.from (n : ℤ)).inf = (-(1 + (10 : ℝ)^(-(n : ℤ)-2) : ℝ) : EReal) := by
      apply le_antisymm
      · have hk : (n : ℤ) + 1 ≥ (Example_6_4_7.from (n : ℤ)).m := by rw [hm]; omega
        have h_ge_inf := Sequence.ge_inf (a := Example_6_4_7.from (n : ℤ)) hk
        calc
          (Example_6_4_7.from (n : ℤ)).inf ≤ (Example_6_4_7.from (n : ℤ)) ((n : ℤ) + 1) := h_ge_inf
          _ = (-(1 + (10 : ℝ)^(-(n : ℤ)-2) : ℝ) : EReal) := by exact_mod_cast h_val_np1
      · apply Sequence.inf_ge_lower
        intro k hk
        have hk' : k ≥ (n : ℤ) := by simpa [hm] using hk
        have hk_nonneg : k ≥ 0 := by omega
        have h_val_k : (Example_6_4_7.from (n : ℤ)) k = Example_6_4_7 k := Sequence.from_eval _ hk'
        rw [h_val_k]
        have h_expr : Example_6_4_7 k = ((-1 : ℝ) ^ (k.toNat : ℕ)) * (1 + (10 : ℝ)^(-(k : ℤ)-1)) := by
          simp [hk_nonneg]
        rw [h_expr]
        rcases neg_one_pow_eq_or ℝ (k.toNat : ℕ) with hneg | hneg
        · rw [hneg, one_mul]
          have h_ineq : (1 : ℝ) + (10 : ℝ)^(-(k : ℤ)-1) ≥ -(1 + (10 : ℝ)^(-(n : ℤ)-2) : ℝ) := by
            have hz_nonneg : 0 ≤ (10 : ℝ)^(-(k : ℤ)-1) := zpow_nonneg (by norm_num : (0 : ℝ) ≤ 10) _
            have hz_nonneg' : 0 ≤ (10 : ℝ)^(-(n : ℤ)-2) := zpow_nonneg (by norm_num : (0 : ℝ) ≤ 10) _
            nlinarith
          exact_mod_cast h_ineq
        · have h_bound : (10 : ℝ)^(-(k : ℤ)-1) ≤ (10 : ℝ)^(-(n : ℤ)-2) := by
            have hkp1 : k ≥ (n : ℤ) + 1 := by
              by_contra! hc
              have hk_eq_n : k = (n : ℤ) := by omega
              subst hk_eq_n
              have h_pow_n : ((-1 : ℝ) ^ ((n : ℤ).toNat : ℕ)) = 1 := by
                simpa using neg_one_pow_even n h
              have h_pow_n_neg : ((-1 : ℝ) ^ ((n : ℤ).toNat : ℕ)) = -1 := by
                simpa using hneg
              rw [h_pow_n] at h_pow_n_neg
              norm_num at h_pow_n_neg
            have h_exp : (-(k : ℤ)-1 : ℤ) ≤ (-(n : ℤ)-2 : ℤ) := by omega
            exact (zpow_le_zpow_iff_right₀ (a := (10:ℝ)) (by norm_num : 1 < (10:ℝ))).mpr h_exp
          have h_mul_eq : (-1 : ℝ) * (1 + (10 : ℝ)^(-(k : ℤ)-1)) = -(1 + (10 : ℝ)^(-(k : ℤ)-1) : ℝ) := by ring
          rw [hneg, h_mul_eq]
          have h_ineq : -(1 + (10 : ℝ)^(-(k : ℤ)-1) : ℝ) ≥ -(1 + (10 : ℝ)^(-(n : ℤ)-2) : ℝ) := by
            nlinarith
          exact_mod_cast h_ineq
    rw [h_inf, if_pos h]
    rfl
  · have hm : (Example_6_4_7.from (n : ℤ)).m = (n : ℤ) := by simp
    have hn_nonneg : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast (Nat.zero_le n)
    have h_val_n : (Example_6_4_7.from (n : ℤ)) (n : ℤ) = (-(1 + (10 : ℝ)^(-(n : ℤ)-1) : ℝ) : ℝ) := by
      calc
        (Example_6_4_7.from (n : ℤ)) (n : ℤ) = Example_6_4_7 (n : ℤ) :=
          Sequence.from_eval _ (le_refl _)
        _ = ((-1 : ℝ) ^ n) * (1 + (10 : ℝ)^(-(n : ℤ)-1)) := by
          simp [hn_nonneg]
        _ = (-1 : ℝ) * (1 + (10 : ℝ)^(-(n : ℤ)-1)) := by simp [neg_one_pow_odd n h]
        _ = -(1 + (10 : ℝ)^(-(n : ℤ)-1) : ℝ) := by ring
    have h_inf : (Example_6_4_7.from (n : ℤ)).inf = (-(1 + (10 : ℝ)^(-(n : ℤ)-1) : ℝ) : EReal) := by
      apply le_antisymm
      · have hk : (n : ℤ) ≥ (Example_6_4_7.from (n : ℤ)).m := by rw [hm]
        have h_ge_inf := Sequence.ge_inf (a := Example_6_4_7.from (n : ℤ)) hk
        calc
          (Example_6_4_7.from (n : ℤ)).inf ≤ (Example_6_4_7.from (n : ℤ)) (n : ℤ) := h_ge_inf
          _ = (-(1 + (10 : ℝ)^(-(n : ℤ)-1) : ℝ) : EReal) := by exact_mod_cast h_val_n
      · apply Sequence.inf_ge_lower
        intro k hk
        have hk' : k ≥ (n : ℤ) := by simpa [hm] using hk
        have hk_nonneg : k ≥ 0 := by omega
        have h_val_k : (Example_6_4_7.from (n : ℤ)) k = Example_6_4_7 k := Sequence.from_eval _ hk'
        rw [h_val_k]
        have h_expr : Example_6_4_7 k = ((-1 : ℝ) ^ (k.toNat : ℕ)) * (1 + (10 : ℝ)^(-(k : ℤ)-1)) := by
          simp [hk_nonneg]
        rw [h_expr]
        rcases neg_one_pow_eq_or ℝ (k.toNat : ℕ) with hneg | hneg
        · rw [hneg, one_mul]
          have h_ineq : (1 : ℝ) + (10 : ℝ)^(-(k : ℤ)-1) ≥ -(1 + (10 : ℝ)^(-(n : ℤ)-1) : ℝ) := by
            have hz_nonneg : 0 ≤ (10 : ℝ)^(-(k : ℤ)-1) := zpow_nonneg (by norm_num : (0 : ℝ) ≤ 10) _
            have hz_nonneg' : 0 ≤ (10 : ℝ)^(-(n : ℤ)-1) := zpow_nonneg (by norm_num : (0 : ℝ) ≤ 10) _
            nlinarith
          exact_mod_cast h_ineq
        · have h_bound : (10 : ℝ)^(-(k : ℤ)-1) ≤ (10 : ℝ)^(-(n : ℤ)-1) := by
            have h_exp : (-(k : ℤ)-1 : ℤ) ≤ (-(n : ℤ)-1 : ℤ) := by omega
            exact (zpow_le_zpow_iff_right₀ (a := (10:ℝ)) (by norm_num : 1 < (10:ℝ))).mpr h_exp
          have h_mul_eq : (-1 : ℝ) * (1 + (10 : ℝ)^(-(k : ℤ)-1)) = -(1 + (10 : ℝ)^(-(k : ℤ)-1) : ℝ) := by ring
          rw [hneg, h_mul_eq]
          have h_ineq : -(1 + (10 : ℝ)^(-(k : ℤ)-1) : ℝ) ≥ -(1 + (10 : ℝ)^(-(n : ℤ)-1) : ℝ) := by
            nlinarith
          exact_mod_cast h_ineq
    rw [h_inf, if_neg h]
    rfl

example (n:ℕ) :
    Example_6_4_7.lowerseq n
    = if Even n then -(1 + (10:ℝ)^(-(n:ℤ)-2)) else -(1 + (10:ℝ)^(-(n:ℤ)-1)) := by
  rw [lowerseq_formula n]

example : Example_6_4_7.liminf = -1 := by
  unfold Sequence.liminf
  have hm : Example_6_4_7.m = (0 : ℤ) := by
    unfold Example_6_4_7; simp
  rw [hm]
  let S := {x | ∃ N ≥ (0 : ℤ), x = Example_6_4_7.lowerseq N}
  have h_nonempty : S.Nonempty := by
    refine ⟨Example_6_4_7.lowerseq (0 : ℤ), ?_⟩
    refine ⟨(0 : ℤ), le_refl _, rfl⟩
  have h_le_neg_one : ∀ a ∈ S, a ≤ (-1 : EReal) := by
    intro a ha
    rcases ha with ⟨N, hN, rfl⟩
    have h_nonneg : N ≥ 0 := hN
    have hN_cast : (N.toNat : ℤ) = N := Int.toNat_of_nonneg h_nonneg
    have h_low_eq : Example_6_4_7.lowerseq N = Example_6_4_7.lowerseq (N.toNat : ℕ) := by
      simp [hN_cast]
    rw [h_low_eq, lowerseq_formula (N.toNat : ℕ)]
    rw [hN_cast]
    by_cases h_even : Even (N.toNat : ℕ)
    · rw [if_pos h_even]
      have h_val : -(1 + (10 : ℝ)^(-(N : ℤ)-2) : ℝ) ≤ (-1 : ℝ) := by
        have h_nonneg_pow2 : 0 ≤ (10 : ℝ)^(-(N : ℤ)-2) := zpow_nonneg (by norm_num : (0 : ℝ) ≤ 10) _
        nlinarith
      exact EReal.coe_le_coe h_val
    · rw [if_neg h_even]
      have h_val : -(1 + (10 : ℝ)^(-(N : ℤ)-1) : ℝ) ≤ (-1 : ℝ) := by
        have h_nonneg_pow1 : 0 ≤ (10 : ℝ)^(-(N : ℤ)-1) := zpow_nonneg (by norm_num : (0 : ℝ) ≤ 10) _
        nlinarith
      exact EReal.coe_le_coe h_val
  have h_gt_exists : ∀ (w : EReal), w < (-1 : EReal) → ∃ a ∈ S, w < a := by
    intro w hw
    rcases w with (w|w)
    · -- w = ⊥
      have h_low_gt_bot : (⊥ : EReal) < Example_6_4_7.lowerseq (0 : ℤ) := by
        have h_val : Example_6_4_7.lowerseq (0 : ℤ) = (-(101/100 : ℝ) : EReal) := by
          calc
            Example_6_4_7.lowerseq (0 : ℤ) = Example_6_4_7.lowerseq (0 : ℕ) := by simp
            _ = (-(1 + (10 : ℝ)^(-(0 : ℤ)-2) : ℝ) : EReal) := by
              rw [lowerseq_formula 0]
              norm_num
            _ = (-(101/100 : ℝ) : EReal) := by norm_num
        rw [h_val]
        exact EReal.bot_lt_coe _
      refine ⟨Example_6_4_7.lowerseq (0 : ℤ), ?_, h_low_gt_bot⟩
      refine ⟨(0 : ℤ), le_refl _, rfl⟩
    · rcases w with (w|w)
      · -- w = ⊤
        exfalso; exact not_top_lt hw
      · -- w = (c : ℝ) where c < -1
        have hc : (w : ℝ) < (-1 : ℝ) :=
          (EReal.coe_lt_coe_iff (x := w) (y := (-1 : ℝ))).mp hw
        have h_ε_pos : 0 < (-1 : ℝ) - w := by linarith
        rcases exists_pow_lt_of_lt_one h_ε_pos (by norm_num : (1/10 : ℝ) < 1) with ⟨k, hk⟩
        have h_expr : (10 : ℝ)^(-(k : ℤ)-1) < (-1 : ℝ) - w := by
          have h_eq : (10 : ℝ)^(-(k : ℤ)-1) = ((1/10 : ℝ) ^ (k+1 : ℕ)) := by
            calc
              (10 : ℝ)^(-(k : ℤ)-1) = (10 : ℝ)^(-(k+1 : ℤ)) := by
                rw [show -(k : ℤ) - 1 = -(k+1 : ℤ) by omega]
              _ = ((10 : ℝ)⁻¹)^(k+1 : ℤ) := by simp
              _ = ((10 : ℝ)⁻¹)^(k+1 : ℕ) := by
                simpa using (zpow_natCast ((10 : ℝ)⁻¹) (k+1))
              _ = ((1/10 : ℝ) ^ (k+1 : ℕ)) := by norm_num
          rw [h_eq]
          have h_lt_pow : ((1/10 : ℝ) ^ (k+1 : ℕ)) < ((1/10 : ℝ) ^ (k : ℕ)) := by
            have h_pow : (10 : ℝ) ^ (k : ℕ) < (10 : ℝ) ^ (k+1 : ℕ) :=
              pow_lt_pow_right₀ (by norm_num : 1 < (10 : ℝ)) (by omega : k < k+1)
            have h_pos_k : 0 < (10 : ℝ) ^ (k : ℕ) := pow_pos (by norm_num : 0 < (10 : ℝ)) _
            have h_pos_k1 : 0 < (10 : ℝ) ^ (k+1 : ℕ) := pow_pos (by norm_num : 0 < (10 : ℝ)) _
            calc
              (1/10 : ℝ) ^ (k+1 : ℕ) = ((10 : ℝ) ^ (k+1 : ℕ))⁻¹ := by
                simp [div_eq_inv_mul]
              _ < ((10 : ℝ) ^ (k : ℕ))⁻¹ := by
                simpa using (one_div_lt_one_div h_pos_k1 h_pos_k).mpr h_pow
              _ = (1/10 : ℝ) ^ (k : ℕ) := by simp [div_eq_inv_mul]
          have h_pow_lt_ε : ((1/10 : ℝ) ^ (k : ℕ)) < (-1 : ℝ) - w := hk
          exact lt_trans h_lt_pow h_pow_lt_ε
        have h_low_gt : (w : EReal) < Example_6_4_7.lowerseq (k : ℕ) := by
          rw [lowerseq_formula k]
          by_cases h_even_k : Even (k : ℕ)
          · rw [if_pos h_even_k]
            have h_val : (w : ℝ) < -(1 + (10 : ℝ)^(-(k : ℤ)-2) : ℝ) := by
              have h_ten : (10 : ℝ)^(-(k : ℤ)-2) ≤ (10 : ℝ)^(-(k : ℤ)-1) := by
                have h_exp : (-(k : ℤ)-2 : ℤ) ≤ (-(k : ℤ)-1 : ℤ) := by omega
                have h_one_lt_ten : 1 < (10 : ℝ) := by norm_num
                exact (zpow_le_zpow_iff_right₀ (a := (10 : ℝ)) h_one_lt_ten).mpr h_exp
              have h_combined : (10 : ℝ)^(-(k : ℤ)-2) < (-1 : ℝ) - w := by
                linarith
              linarith
            exact EReal.coe_lt_coe h_val
          · rw [if_neg h_even_k]
            have h_val : (w : ℝ) < -(1 + (10 : ℝ)^(-(k : ℤ)-1) : ℝ) := by
              linarith
            exact EReal.coe_lt_coe h_val
        refine ⟨Example_6_4_7.lowerseq (k : ℕ), ?_, h_low_gt⟩
        refine ⟨(k : ℤ), ?_, rfl⟩
        exact_mod_cast (Nat.zero_le k)
  exact csSup_eq_of_forall_le_of_forall_lt_exists_gt h_nonempty h_le_neg_one h_gt_exists

example : Example_6_4_7.sup = (1.1:ℝ) := by
  apply le_antisymm
  · apply Sequence.sup_le_upper
    intro n hn
    have hn_nonneg : n ≥ (0 : ℤ) := hn
    rw [EReal.coe_le_coe_iff]
    have h_expr : Example_6_4_7 n = ((-1 : ℝ)^(n.toNat : ℕ)) * (1 + (10 : ℝ)^(-(n : ℤ)-1)) := by
      simp [hn_nonneg]
    rw [h_expr]
    by_cases h : Even n.toNat
    · have h_neg_one : ((-1 : ℝ)^(n.toNat : ℕ)) = 1 := neg_one_pow_even (n.toNat) h
      rw [h_neg_one, one_mul]
      have h_ten : (10 : ℝ)^(-(n : ℤ)-1) ≤ (10 : ℝ)^(-(0 : ℤ)-1) := le_pow_ten hn_nonneg
      have h_ten_val : (10 : ℝ)^(-(0 : ℤ)-1) = (0.1 : ℝ) := by norm_num
      rw [h_ten_val] at h_ten
      nlinarith
    · have h_neg_one : ((-1 : ℝ)^(n.toNat : ℕ)) = -1 := neg_one_pow_odd (n.toNat) h
      rw [h_neg_one]
      have hp : 0 ≤ (10 : ℝ)^(-(n : ℤ)-1) := zpow_nonneg (by norm_num : (0 : ℝ) ≤ 10) _
      nlinarith
  · calc
      ((1.1 : ℝ) : EReal) = (Example_6_4_7 (0 : ℤ) : EReal) := by
        have h0_val : Example_6_4_7 (0 : ℤ) = (1.1 : ℝ) := by
          simp
          norm_num
        exact congrArg (fun x : ℝ => (x : EReal)) h0_val.symm
      _ ≤ Example_6_4_7.sup := Sequence.le_sup (by simp)

example : Example_6_4_7.inf = (-1.01:ℝ) := by
  apply le_antisymm
  · calc
      Example_6_4_7.inf ≤ (Example_6_4_7 (1 : ℤ) : EReal) := Sequence.ge_inf (by simp)
      _ = ((-1.01 : ℝ) : EReal) := by
        have h1_val : Example_6_4_7 (1 : ℤ) = (-1.01 : ℝ) := by
          simp
          norm_num
        exact congrArg (fun x : ℝ => (x : EReal)) h1_val
  · apply Sequence.inf_ge_lower
    intro n hn
    have hn_nonneg : n ≥ (0 : ℤ) := hn
    have h_goal : (-1.01 : ℝ) ≤ Example_6_4_7 n := by
      have h_expr : Example_6_4_7 n = ((-1 : ℝ)^(n.toNat : ℕ)) * (1 + (10 : ℝ)^(-(n : ℤ)-1)) := by
        simp [hn_nonneg]
      rw [h_expr]
      by_cases h : Even n.toNat
      · have h_neg_one : ((-1 : ℝ)^(n.toNat : ℕ)) = 1 := neg_one_pow_even (n.toNat) h
        rw [h_neg_one, one_mul]
        have hp : 0 ≤ (10 : ℝ)^(-(n : ℤ)-1) := zpow_nonneg (by norm_num : (0 : ℝ) ≤ 10) _
        nlinarith
      · have h_neg_one : ((-1 : ℝ)^(n.toNat : ℕ)) = -1 := neg_one_pow_odd (n.toNat) h
        rw [h_neg_one]
        have hn1 : n ≥ (1 : ℤ) := by
          by_contra! hlt
          have : n = 0 := by omega
          subst this
          have hzero_even : Even (0 : ℕ) := by
            refine ⟨0, ?_⟩
            simp
          exact h hzero_even
        have h_ten : (10 : ℝ)^(-(n : ℤ)-1) ≤ (10 : ℝ)^(-(1 : ℤ)-1) := le_pow_ten hn1
        have h_ten_val : (10 : ℝ)^(-(1 : ℤ)-1) = (0.01 : ℝ) := by
          calc
            (10 : ℝ)^(-(1 : ℤ)-1) = (10 : ℝ)^(-(2 : ℤ)) := by ring
            _ = (0.01 : ℝ) := by norm_num
        rw [h_ten_val] at h_ten
        nlinarith
    exact_mod_cast h_goal

noncomputable abbrev Example_6_4_8 : Sequence := (fun (n:ℕ) ↦ if Even n then (n+1:ℝ) else -(n:ℝ)-1)

lemma upperseq_top (n:ℕ) : Example_6_4_8.upperseq n = ⊤ := by
  unfold Sequence.upperseq
  erw [sSup_eq_top]
  intro b hb
  induction b using EReal.rec with
  | bot =>
    have hm : (Example_6_4_8.from (n:ℤ)).m = (n:ℤ) := by
      simp
    refine ⟨(Example_6_4_8.from (n:ℤ)) (n:ℤ), ?_, EReal.bot_lt_coe _⟩
    refine ⟨(n:ℤ), ?_, rfl⟩
    rw [hm]
  | top => exact absurd hb (lt_irrefl _)
  | coe r =>
    have hm : (Example_6_4_8.from (n:ℤ)).m = (n:ℤ) := by
      simp
    obtain ⟨k, hk⟩ := exists_nat_gt (max (r : ℝ) (n : ℝ))
    have hk_nonneg : (k : ℤ) ≥ 0 := by exact_mod_cast (Nat.zero_le k)
    have hk_ge_n : (k : ℤ) ≥ (n : ℤ) := by
      have h_ineq : (n : ℝ) < (k : ℝ) := lt_of_le_of_lt (le_max_right _ _) hk
      exact_mod_cast h_ineq.le
    have hpos : (2 * (k : ℤ) : ℤ) ≥ (n : ℤ) := by
      calc
        (2 * (k : ℤ) : ℤ) ≥ (k : ℤ) := by omega
        _ ≥ (n : ℤ) := hk_ge_n
    have h_toNat : (2*(k : ℤ)).toNat = 2*k := by omega
    have h_even : Even (2*k : ℕ) := ⟨k, by ring⟩
    have h_eval : (Example_6_4_8.from (n:ℤ)) (2 * (k : ℤ)) = ((2*k : ℕ) + 1 : ℝ) := by
      rw [Sequence.from_eval _ hpos]
      simp [h_toNat, h_even]
    refine ⟨(Example_6_4_8.from (n:ℤ)) (2 * (k : ℤ)), ?_, ?_⟩
    · refine ⟨(2 * (k : ℤ)), ?_, rfl⟩
      rw [hm]
      calc
        (2 * (k : ℤ) : ℤ) ≥ (k : ℤ) := by omega
        _ ≥ (n : ℤ) := hk_ge_n
    · rw [h_eval]
      have hr_lt : (r : ℝ) < (2 * (k : ℕ) + 1 : ℝ) := by
        have hk_r : (r : ℝ) < (k : ℝ) := lt_of_le_of_lt (le_max_left _ _) hk
        nlinarith
      exact mod_cast hr_lt

example : Example_6_4_8.limsup = ⊤ := by
  unfold Sequence.limsup
  apply sInf_eq_top.mpr
  intro x hx
  rcases hx with ⟨N, hN, rfl⟩
  have hN_nonneg : N ≥ (0 : ℤ) := hN
  have hN_eq_cast : (N : ℤ) = (N.toNat : ℤ) := by
    simpa using (Int.toNat_of_nonneg hN_nonneg)
  rw [hN_eq_cast]
  exact upperseq_top N.toNat

lemma lowerseq_bot (n:ℕ) : Example_6_4_8.lowerseq n = ⊥ := by
  unfold Sequence.lowerseq
  unfold Sequence.inf
  apply sInf_eq_bot.mpr
  intro b hb
  induction b using EReal.rec with
  | bot => exact absurd hb (lt_irrefl _)
  | top =>
    have hm : (Example_6_4_8.from (n:ℤ)).m = (n:ℤ) := by
      simp
    refine ⟨(Example_6_4_8.from (n:ℤ)) (n:ℤ), ⟨(n:ℤ), ?_, rfl⟩, EReal.coe_lt_top _⟩
    rw [hm]
  | coe r =>
    have hm : (Example_6_4_8.from (n:ℤ)).m = (n:ℤ) := by
      simp
    obtain ⟨k, hk⟩ := exists_nat_gt (max (n : ℝ) (-(r : ℝ) - 1))
    have hk_gt_n : (n : ℝ) < (k : ℝ) := calc
      (n : ℝ) ≤ max (n : ℝ) (-(r : ℝ) - 1) := le_max_left _ _
      _ < (k : ℝ) := hk
    have hk_gt_neg : (-(r : ℝ) - 1 : ℝ) < (k : ℝ) := calc
      (-(r : ℝ) - 1 : ℝ) ≤ max (n : ℝ) (-(r : ℝ) - 1) := le_max_right _ _
      _ < (k : ℝ) := hk
    have h_m_ge_n : (2*(k : ℤ)+1 : ℤ) ≥ (n : ℤ) := by
      have hk_ge_n' : (k : ℤ) ≥ (n : ℤ) := by exact_mod_cast hk_gt_n.le
      omega
    have h_not_even : ¬ Even (2*k+1 : ℕ) := by
      intro h_even
      rcases h_even with ⟨t, ht⟩
      omega
    have h_nonneg : (0 : ℤ) ≤ 2*(k : ℤ)+1 := by
      have hk_nonneg : (0 : ℤ) ≤ (k : ℤ) := by exact_mod_cast (Nat.zero_le k)
      omega
    have h_val : (Example_6_4_8.from (n:ℤ)) (2*(k : ℤ)+1) = (-((2*k+1 : ℕ) : ℝ) - 1 : ℝ) := by
      rw [Sequence.from_eval (a := Example_6_4_8) h_m_ge_n]
      have h_toNat : (2*(k : ℤ)+1).toNat = 2*k+1 := by omega
      simp [h_nonneg, h_not_even, h_toNat]
    have h_lt_r : (-((2*k+1 : ℕ) : ℝ) - 1 : ℝ) < (r : ℝ) := by
      push_cast
      nlinarith
    refine ⟨(Example_6_4_8.from (n:ℤ)) (2*(k : ℤ)+1), ⟨(2*(k : ℤ)+1), ?_, rfl⟩, ?_⟩
    · rw [hm]
      exact h_m_ge_n
    · rw [h_val]
      exact mod_cast h_lt_r

example : Example_6_4_8.liminf = ⊥ := by
  unfold Sequence.liminf
  apply sSup_eq_bot.mpr
  intro x hx
  rcases hx with ⟨N, hN, rfl⟩
  have hN_nonneg : N ≥ (0 : ℤ) := hN
  have hN_eq_cast : (N : ℤ) = (N.toNat : ℤ) := by
    simpa using (Int.toNat_of_nonneg hN_nonneg)
  rw [hN_eq_cast]
  exact lowerseq_bot N.toNat

noncomputable abbrev Example_6_4_9 : Sequence :=
  (fun (n:ℕ) ↦ if Even n then (n+1:ℝ)⁻¹ else -(n+1:ℝ)⁻¹)

lemma upperseq_formula_9 (n:ℕ) : Example_6_4_9.upperseq n = (if Even n then (n+1:ℝ)⁻¹ else (n+2:ℝ)⁻¹ : ℝ) := by
  unfold Sequence.upperseq
  by_cases h : Even n
  · have h_sup : (Example_6_4_9.from (n : ℤ)).sup = ((n : ℝ) + 1)⁻¹ := by
      have hm : (Example_6_4_9.from (n : ℤ)).m = (n : ℤ) := by simp
      have hn_nonneg : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast (Nat.zero_le n)
      have h_val_n : (Example_6_4_9.from (n : ℤ)) (n : ℤ) = ((n : ℝ) + 1)⁻¹ := by
        simp [hn_nonneg, h]
      apply le_antisymm
      · apply Sequence.sup_le_upper
        intro k hk
        have hk' : k ≥ (n : ℤ) := by simpa [hm] using hk
        have hk_nonneg : k ≥ 0 := by omega
        have h_eval : (Example_6_4_9.from (n : ℤ)) k = Example_6_4_9 k := Sequence.from_eval _ hk'
        rw [h_eval]
        have h_expr : Example_6_4_9 k = (if Even (k.toNat : ℕ) then ((k.toNat : ℝ) + 1)⁻¹ else -(((k.toNat : ℝ) + 1)⁻¹)) := by
          simp [hk_nonneg]
        rw [h_expr]
        by_cases hk_even : Even (k.toNat : ℕ)
        · rw [if_pos hk_even]
          have hk_nat_ge_n : (k.toNat : ℕ) ≥ n := by
            have h_int : ((n : ℤ).toNat : ℕ) ≤ (k.toNat : ℕ) := Int.toNat_le_toNat hk'
            simpa using h_int
          have h_pos_n : 0 < (n : ℝ) + 1 := by positivity
          have h_pos_k : 0 < (k.toNat : ℝ) + 1 := by positivity
          have h_add_ineq : (n : ℝ) + 1 ≤ (k.toNat : ℝ) + 1 := by
            have h_n_real : (n : ℝ) ≤ (k.toNat : ℝ) := by exact_mod_cast hk_nat_ge_n
            nlinarith
          have h_ineq : ((k.toNat : ℝ) + 1)⁻¹ ≤ ((n : ℝ) + 1)⁻¹ := by
            simpa using (one_div_le_one_div h_pos_k h_pos_n).mpr h_add_ineq
          exact_mod_cast h_ineq
        · rw [if_neg hk_even]
          have h_nonpos : -(((k.toNat : ℝ) + 1)⁻¹) ≤ 0 := by
            have h_pos_inv : 0 < ((k.toNat : ℝ) + 1)⁻¹ := by positivity
            linarith
          have h_pos_n_inv : 0 ≤ ((n : ℝ) + 1)⁻¹ := by positivity
          have h_ineq_ℝ : -(((k.toNat : ℝ) + 1)⁻¹) ≤ ((n : ℝ) + 1)⁻¹ := by
            calc
              -(((k.toNat : ℝ) + 1)⁻¹) ≤ 0 := h_nonpos
              _ ≤ ((n : ℝ) + 1)⁻¹ := h_pos_n_inv
          exact_mod_cast h_ineq_ℝ
      · calc
          (((n : ℝ) + 1)⁻¹ : EReal) = ((Example_6_4_9.from (n : ℤ)) (n : ℤ) : EReal) := by
            symm; exact congrArg (fun x : ℝ => (x : EReal)) h_val_n
          _ ≤ (Example_6_4_9.from (n : ℤ)).sup := Sequence.le_sup (by simp)
    simp [h, h_sup]
  · have h_sup : (Example_6_4_9.from (n : ℤ)).sup = ((n : ℝ) + 2)⁻¹ := by
      have hm : (Example_6_4_9.from (n : ℤ)).m = (n : ℤ) := by simp
      have hn_nonneg : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast (Nat.zero_le n)
      have hn_nonneg' : (0 : ℤ) ≤ (n : ℤ) + 1 := by omega
      have h_next_even : Even (n+1) := by
        rcases Nat.even_or_odd n with (h_even | h_odd)
        · exfalso; exact h h_even
        · exact h_odd.add_one
      have h_val_np1 : (Example_6_4_9.from (n : ℤ)) ((n : ℤ) + 1) = ((n : ℝ) + 2)⁻¹ := by
        calc
          (Example_6_4_9.from (n : ℤ)) ((n : ℤ) + 1) = Example_6_4_9 ((n : ℤ) + 1) :=
            Sequence.from_eval _ (by omega)
          _ = ((n : ℝ) + 2)⁻¹ := by
            simp [hn_nonneg', h_next_even]; ring
      apply le_antisymm
      · apply Sequence.sup_le_upper
        intro k hk
        have hk' : k ≥ (n : ℤ) := by simpa [hm] using hk
        have hk_nonneg : k ≥ 0 := by omega
        have h_eval : (Example_6_4_9.from (n : ℤ)) k = Example_6_4_9 k := Sequence.from_eval _ hk'
        rw [h_eval]
        have h_expr : Example_6_4_9 k = (if Even (k.toNat : ℕ) then ((k.toNat : ℝ) + 1)⁻¹ else -(((k.toNat : ℝ) + 1)⁻¹)) := by
          simp [hk_nonneg]
        rw [h_expr]
        by_cases hk_even : Even (k.toNat : ℕ)
        · rw [if_pos hk_even]
          have hk_ge_np1 : k ≥ (n : ℤ) + 1 := by
            by_contra! hlt
            have hk_eq : k = (n : ℤ) := by omega
            subst hk_eq
            have h_even_n : Even ((n : ℤ).toNat : ℕ) := hk_even
            have h_n_toNat : ((n : ℤ).toNat : ℕ) = n := by simp
            rw [h_n_toNat] at h_even_n
            exact h h_even_n
          have hk_nat_ge_np1 : (k.toNat : ℕ) ≥ n + 1 := by
            have h_int : (((n : ℤ) + 1).toNat : ℕ) ≤ (k.toNat : ℕ) := Int.toNat_le_toNat hk_ge_np1
            simpa using h_int
          have h_pos_n : 0 < (n : ℝ) + 2 := by positivity
          have h_pos_k : 0 < (k.toNat : ℝ) + 1 := by positivity
          have h_add_ineq : (n : ℝ) + 2 ≤ (k.toNat : ℝ) + 1 := by
            have h_k_real_ge_np1 : (k.toNat : ℝ) ≥ (n + 1 : ℝ) := by exact_mod_cast hk_nat_ge_np1
            linarith
          have h_ineq : ((k.toNat : ℝ) + 1)⁻¹ ≤ ((n : ℝ) + 2)⁻¹ := by
            simpa using (one_div_le_one_div h_pos_k h_pos_n).mpr h_add_ineq
          exact_mod_cast h_ineq
        · rw [if_neg hk_even]
          have h_nonpos : -(((k.toNat : ℝ) + 1)⁻¹) ≤ 0 := by
            have h_pos_inv : 0 < ((k.toNat : ℝ) + 1)⁻¹ := by positivity
            linarith
          have h_pos_n_inv : 0 ≤ ((n : ℝ) + 2)⁻¹ := by positivity
          have h_ineq_ℝ : -(((k.toNat : ℝ) + 1)⁻¹) ≤ ((n : ℝ) + 2)⁻¹ := by
            calc
              -(((k.toNat : ℝ) + 1)⁻¹) ≤ 0 := h_nonpos
              _ ≤ ((n : ℝ) + 2)⁻¹ := h_pos_n_inv
          exact_mod_cast h_ineq_ℝ
      · calc
          (((n : ℝ) + 2)⁻¹ : EReal) = ((Example_6_4_9.from (n : ℤ)) ((n : ℤ) + 1) : EReal) := by
            symm; exact congrArg (fun x : ℝ => (x : EReal)) h_val_np1
          _ ≤ (Example_6_4_9.from (n : ℤ)).sup := Sequence.le_sup (by rw [hm]; omega)
    simp [h, h_sup]

example : Example_6_4_9.limsup = 0 := by
  unfold Sequence.limsup
  have hm : Example_6_4_9.m = (0 : ℤ) := by
    unfold Example_6_4_9; simp
  rw [hm]
  let S := {x | ∃ N ≥ (0 : ℤ), x = Example_6_4_9.upperseq N}
  have h_nonempty : S.Nonempty := by
    refine ⟨Example_6_4_9.upperseq (0 : ℤ), ?_⟩
    refine ⟨(0 : ℤ), le_refl _, rfl⟩
  have h_ge_zero : ∀ a ∈ S, (0 : EReal) ≤ a := by
    intro a ha
    rcases ha with ⟨N, hN, rfl⟩
    have h_nonneg : N ≥ 0 := hN
    have hN_cast : (N.toNat : ℤ) = N := Int.toNat_of_nonneg h_nonneg
    have h_upp_eq : Example_6_4_9.upperseq N = Example_6_4_9.upperseq (N.toNat : ℕ) := by
      simp [hN_cast]
    rw [h_upp_eq]
    have h_nonneg_val : (0 : EReal) ≤ Example_6_4_9.upperseq (N.toNat : ℕ) := by
      have h := upperseq_formula_9 (N.toNat : ℕ)
      by_cases h_even : Even (N.toNat : ℕ)
      · have h_val : Example_6_4_9.upperseq (N.toNat : ℕ) = (((N.toNat : ℝ) + 1)⁻¹ : EReal) := by
          have h' : Example_6_4_9.upperseq (N.toNat : ℕ) = (((N.toNat : ℝ) + 1)⁻¹ : ℝ) := by
            simpa [h_even] using h
          simpa [Nat.cast_add, Nat.cast_one] using (by exact_mod_cast h' : Example_6_4_9.upperseq (N.toNat : ℕ) = (((N.toNat : ℝ) + 1)⁻¹ : EReal))
        rw [h_val]
        have h_nonneg_real : (0 : ℝ) ≤ ((N.toNat : ℝ) + 1)⁻¹ := by positivity
        have : (0 : EReal) ≤ (((N.toNat : ℝ) + 1)⁻¹ : EReal) := EReal.coe_le_coe h_nonneg_real
        exact this
      · have h_val : Example_6_4_9.upperseq (N.toNat : ℕ) = (((N.toNat : ℝ) + 2)⁻¹ : EReal) := by
          have h' : Example_6_4_9.upperseq (N.toNat : ℕ) = (((N.toNat : ℝ) + 2)⁻¹ : ℝ) := by
            simpa [h_even] using h
          have h_cast : Example_6_4_9.upperseq (N.toNat : ℕ) = (((N.toNat : ℝ) + 2)⁻¹ : EReal) := by
            have := (by exact_mod_cast h' : Example_6_4_9.upperseq (N.toNat : ℕ) = ((((N.toNat + 2 : ℕ) : ℝ)⁻¹ : EReal)))
            simpa [Nat.cast_add, Nat.cast_two] using this
          exact h_cast
        rw [h_val]
        have h_nonneg_real : (0 : ℝ) ≤ ((N.toNat : ℝ) + 2)⁻¹ := by positivity
        have : (0 : EReal) ≤ (((N.toNat : ℝ) + 2)⁻¹ : EReal) := EReal.coe_le_coe h_nonneg_real
        exact this
    exact h_nonneg_val
  have h_gt_exists : ∀ (w : EReal), (0 : EReal) < w → ∃ a ∈ S, a < w := by
    intro w hw
    rcases w with (w|w)
    · exfalso; exact not_lt_bot hw
    · rcases w with (w|w)
      · -- w = ⊤
        have h_upp_lt_top : Example_6_4_9.upperseq (0 : ℤ) < ⊤ := by
          have h_val : Example_6_4_9.upperseq (0 : ℤ) = ((1 : ℝ) : EReal) := by
            calc
              Example_6_4_9.upperseq (0 : ℤ) = Example_6_4_9.upperseq (0 : ℕ) := by simp
              _ = ((1 : ℝ) : EReal) := by
                have h_even_0 : Even (0 : ℕ) := ⟨0, by simp⟩
                have h := upperseq_formula_9 0
                have h' : Example_6_4_9.upperseq (0 : ℕ) = (((0 : ℝ) + 1)⁻¹ : ℝ) := by
                  simpa [h_even_0] using h
                have h'' : Example_6_4_9.upperseq (0 : ℕ) = ((1 : ℝ) : EReal) := by
                  calc
                    Example_6_4_9.upperseq (0 : ℕ) = (((0 : ℝ) + 1)⁻¹ : EReal) := by exact_mod_cast h'
                    _ = ((1 : ℝ) : EReal) := by norm_num
                exact h''
          calc
            Example_6_4_9.upperseq (0 : ℤ) = ((1 : ℝ) : EReal) := h_val
            _ < ⊤ := EReal.coe_lt_top (1 : ℝ)
        refine ⟨Example_6_4_9.upperseq (0 : ℤ), ?_, h_upp_lt_top⟩
        refine ⟨(0 : ℤ), le_refl _, rfl⟩
      · -- w = (c : ℝ) where c > 0
        have hc : (0 : ℝ) < w := (EReal.coe_lt_coe_iff (x := (0 : ℝ)) (y := w)).mp hw
        rcases exists_nat_gt (1 / w) with ⟨k, hk⟩
        have hk_real : 1 / w < (k : ℝ) := hk
        have h_pos_k1 : 0 < (k : ℝ) + 1 := by positivity
        have h_pos_k2 : 0 < (k : ℝ) + 2 := by positivity
        have h_inv_ineq1 : ((k : ℝ) + 1)⁻¹ < w := by
          have h_ineq1 : (k : ℝ) + 1 > 1 / w := by linarith
          have h_mul_ineq : ((k : ℝ) + 1)⁻¹ * ((k : ℝ) + 1) < w * ((k : ℝ) + 1) := by
            calc
              ((k : ℝ) + 1)⁻¹ * ((k : ℝ) + 1) = 1 := by field_simp [h_pos_k1.ne.symm]
              _ < ((k : ℝ) + 1) * w := by
                have h_one_lt_mul : 1 < ((k : ℝ) + 1) * w := by
                  calc
                    1 = (1 / w) * w := by field_simp [hc.ne.symm]
                    _ < ((k : ℝ) + 1) * w := mul_lt_mul_of_pos_right h_ineq1 hc
                exact h_one_lt_mul
              _ = w * ((k : ℝ) + 1) := by ring
          exact lt_of_mul_lt_mul_right h_mul_ineq h_pos_k1.le
        have h_inv_ineq2 : ((k : ℝ) + 2)⁻¹ < w := by
          have h_ineq2 : (k : ℝ) + 2 > 1 / w := by linarith
          have h_mul_ineq : ((k : ℝ) + 2)⁻¹ * ((k : ℝ) + 2) < w * ((k : ℝ) + 2) := by
            calc
              ((k : ℝ) + 2)⁻¹ * ((k : ℝ) + 2) = 1 := by field_simp [h_pos_k2.ne.symm]
              _ < ((k : ℝ) + 2) * w := by
                have h_one_lt_mul : 1 < ((k : ℝ) + 2) * w := by
                  calc
                    1 = (1 / w) * w := by field_simp [hc.ne.symm]
                    _ < ((k : ℝ) + 2) * w := mul_lt_mul_of_pos_right h_ineq2 hc
                exact h_one_lt_mul
              _ = w * ((k : ℝ) + 2) := by ring
          exact lt_of_mul_lt_mul_right h_mul_ineq h_pos_k2.le
        have h_upp_lt_c : Example_6_4_9.upperseq (k : ℕ) < (w : EReal) := by
          have h_formula : Example_6_4_9.upperseq (k : ℕ) =
            (if Even k then ((k : ℝ) + 1)⁻¹ else ((k : ℝ) + 2)⁻¹ : EReal) := by
            by_cases hk_even : Even k
            · have h := upperseq_formula_9 k
              have h' : Example_6_4_9.upperseq (k : ℕ) = (((k : ℝ) + 1)⁻¹ : ℝ) := by
                simpa [hk_even] using h
              have h'' : Example_6_4_9.upperseq (k : ℕ) = (((k : ℝ) + 1)⁻¹ : EReal) := by
                simpa [Nat.cast_add, Nat.cast_one, add_comm] using (by exact_mod_cast h' : Example_6_4_9.upperseq (k : ℕ) = (((k : ℝ) + 1)⁻¹ : EReal))
              simpa [hk_even] using h''
            · have h := upperseq_formula_9 k
              have h' : Example_6_4_9.upperseq (k : ℕ) = (((k : ℝ) + 2)⁻¹ : ℝ) := by
                simpa [hk_even] using h
              have h'' : Example_6_4_9.upperseq (k : ℕ) = (((k : ℝ) + 2)⁻¹ : EReal) := by
                have := (by exact_mod_cast h' : Example_6_4_9.upperseq (k : ℕ) = ((((k + 2 : ℕ) : ℝ)⁻¹ : EReal)))
                simpa [Nat.cast_add, Nat.cast_two, add_comm] using this
              simpa [hk_even] using h''
          rw [h_formula]
          by_cases hk_even : Even k
          · simp [hk_even]
            apply EReal.coe_lt_coe
            exact h_inv_ineq1
          · simp [hk_even]
            apply EReal.coe_lt_coe
            exact h_inv_ineq2
        refine ⟨Example_6_4_9.upperseq (k : ℕ), ?_, h_upp_lt_c⟩
        refine ⟨(k : ℤ), ?_, rfl⟩
        exact_mod_cast (Nat.zero_le k)
  dsimp [S] at *
  exact csInf_eq_of_forall_ge_of_forall_gt_exists_lt h_nonempty h_ge_zero h_gt_exists

lemma lowerseq_formula_9 (n:ℕ) : Example_6_4_9.lowerseq n = (if Even n then -(n+2:ℝ)⁻¹ else -(n+1:ℝ)⁻¹ : ℝ) := by
  unfold Sequence.lowerseq
  by_cases h : Even n
  · have hm : (Example_6_4_9.from (n : ℤ)).m = (n : ℤ) := by simp
    have hn_nonneg' : (0 : ℤ) ≤ (n : ℤ) + 1 := by omega
    have h_next_odd : ¬ Even (n+1) := by
      rcases h with ⟨k, hk⟩
      intro h_even
      rcases h_even with ⟨m, hm'⟩
      omega
    have h_val_np1 : (Example_6_4_9.from (n : ℤ)) ((n : ℤ) + 1) = (-((n : ℝ) + 2)⁻¹ : ℝ) := by
      calc
        (Example_6_4_9.from (n : ℤ)) ((n : ℤ) + 1) = Example_6_4_9 ((n : ℤ) + 1) :=
          Sequence.from_eval _ (by omega)
        _ = (if Even (((n : ℤ) + 1).toNat : ℕ) then ((((n : ℤ) + 1).toNat : ℝ) + 1)⁻¹
          else -((((n : ℤ) + 1).toNat : ℝ) + 1)⁻¹) := by
          simp [hn_nonneg']
        _ = (-((n : ℝ) + 2)⁻¹ : ℝ) := by
          have h_toNat : (((n : ℤ) + 1).toNat : ℝ) = (n : ℝ) + 1 := by simp
          rw [h_toNat]; simp [h_next_odd]; ring
    have h_inf : (Example_6_4_9.from (n : ℤ)).inf = (-((n : ℝ) + 2)⁻¹ : EReal) := by
      apply le_antisymm
      · have hk : (n : ℤ) + 1 ≥ (Example_6_4_9.from (n : ℤ)).m := by
          rw [hm]; omega
        calc
          (Example_6_4_9.from (n : ℤ)).inf ≤ (Example_6_4_9.from (n : ℤ)) ((n : ℤ) + 1) := Sequence.ge_inf hk
          _ = (-((n : ℝ) + 2)⁻¹ : EReal) := by exact_mod_cast h_val_np1
      · apply Sequence.inf_ge_lower
        intro k hk
        have hk' : k ≥ (n : ℤ) := by simpa [hm] using hk
        have hk_nonneg : k ≥ 0 := by omega
        have h_val_k : (Example_6_4_9.from (n : ℤ)) k = Example_6_4_9 k := Sequence.from_eval _ hk'
        rw [h_val_k]
        have h_expr : Example_6_4_9 k =
          (if Even (k.toNat : ℕ) then ((k.toNat : ℝ) + 1)⁻¹ else -(((k.toNat : ℝ) + 1)⁻¹)) := by
          simp [hk_nonneg]
        rw [h_expr]
        by_cases hk_even : Even (k.toNat : ℕ)
        · rw [if_pos hk_even]
          have h_nonpos_neg : (-((n : ℝ) + 2)⁻¹ : ℝ) ≤ ((k.toNat : ℝ) + 1)⁻¹ := by
            have h_nonneg_inv_k : 0 ≤ ((k.toNat : ℝ) + 1)⁻¹ := by positivity
            have h_nonpos : (-((n : ℝ) + 2)⁻¹ : ℝ) ≤ 0 := by
              have hpos : 0 < ((n : ℝ) + 2)⁻¹ := by positivity
              linarith
            linarith
          exact_mod_cast h_nonpos_neg
        · rw [if_neg hk_even]
          have hk_ge_np1 : k ≥ (n : ℤ) + 1 := by
            by_contra! hlt
            have hk_eq_n : k = (n : ℤ) := by omega
            subst hk_eq_n
            have hn_even_nat : Even ((n : ℤ).toNat : ℕ) := h
            have hn_toNat : ((n : ℤ).toNat : ℕ) = n := by simp
            rw [hn_toNat] at hn_even_nat
            exact hk_even hn_even_nat
          have hk_nat_ge_np1 : (k.toNat : ℕ) ≥ n + 1 := by
            have h_int : (((n : ℤ) + 1).toNat : ℕ) ≤ (k.toNat : ℕ) := Int.toNat_le_toNat hk_ge_np1
            simpa using h_int
          have h_pos_n : 0 < (n : ℝ) + 2 := by positivity
          have h_pos_k : 0 < (k.toNat : ℝ) + 1 := by positivity
          have h_add_ineq : (n : ℝ) + 2 ≤ (k.toNat : ℝ) + 1 := by
            have h_k_real_ge_np1 : (k.toNat : ℝ) ≥ (n + 1 : ℝ) := by exact_mod_cast hk_nat_ge_np1
            linarith
          have h_ineq : -((k.toNat : ℝ) + 1)⁻¹ ≥ -((n : ℝ) + 2)⁻¹ := by
            have h_inv_ineq : ((k.toNat : ℝ) + 1)⁻¹ ≤ ((n : ℝ) + 2)⁻¹ := by
              simpa using (one_div_le_one_div h_pos_k h_pos_n).mpr h_add_ineq
            linarith
          exact_mod_cast h_ineq
    rw [h_inf, show (-((n : ℝ) + 2)⁻¹ : EReal) = (if Even n then -(n+2:ℝ)⁻¹ else -(n+1:ℝ)⁻¹ : ℝ) by
      simp [h]]
  · have hm : (Example_6_4_9.from (n : ℤ)).m = (n : ℤ) := by simp
    have hn_nonneg : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast (Nat.zero_le n)
    have h_val_n : (Example_6_4_9.from (n : ℤ)) (n : ℤ) = (-((n : ℝ) + 1)⁻¹ : ℝ) := by
      calc
        (Example_6_4_9.from (n : ℤ)) (n : ℤ) = Example_6_4_9 (n : ℤ) :=
          Sequence.from_eval _ (le_refl _)
        _ = (if Even (n : ℕ) then ((n : ℝ) + 1)⁻¹ else -((n : ℝ) + 1)⁻¹) := by
          simp [hn_nonneg]
        _ = (-((n : ℝ) + 1)⁻¹ : ℝ) := by simp [h]
    have h_inf : (Example_6_4_9.from (n : ℤ)).inf = (-((n : ℝ) + 1)⁻¹ : EReal) := by
      apply le_antisymm
      · have hk : (n : ℤ) ≥ (Example_6_4_9.from (n : ℤ)).m := by rw [hm]
        calc
          (Example_6_4_9.from (n : ℤ)).inf ≤ (Example_6_4_9.from (n : ℤ)) (n : ℤ) := Sequence.ge_inf hk
          _ = (-((n : ℝ) + 1)⁻¹ : EReal) := by exact_mod_cast h_val_n
      · apply Sequence.inf_ge_lower
        intro k hk
        have hk' : k ≥ (n : ℤ) := by simpa [hm] using hk
        have hk_nonneg : k ≥ 0 := by omega
        have h_val_k : (Example_6_4_9.from (n : ℤ)) k = Example_6_4_9 k := Sequence.from_eval _ hk'
        rw [h_val_k]
        have h_expr : Example_6_4_9 k =
          (if Even (k.toNat : ℕ) then ((k.toNat : ℝ) + 1)⁻¹ else -(((k.toNat : ℝ) + 1)⁻¹)) := by
          simp [hk_nonneg]
        rw [h_expr]
        by_cases hk_even : Even (k.toNat : ℕ)
        · rw [if_pos hk_even]
          have h_nonpos_neg : (-((n : ℝ) + 1)⁻¹ : ℝ) ≤ ((k.toNat : ℝ) + 1)⁻¹ := by
            have h_nonneg_inv_k : 0 ≤ ((k.toNat : ℝ) + 1)⁻¹ := by positivity
            have h_nonpos : (-((n : ℝ) + 1)⁻¹ : ℝ) ≤ 0 := by
              have hpos : 0 < ((n : ℝ) + 1)⁻¹ := by positivity
              linarith
            linarith
          exact_mod_cast h_nonpos_neg
        · rw [if_neg hk_even]
          have hk_nat_ge_n : (k.toNat : ℕ) ≥ n := by
            have h_int : ((n : ℤ).toNat : ℕ) ≤ (k.toNat : ℕ) := Int.toNat_le_toNat hk'
            simpa using h_int
          have h_pos_n : 0 < (n : ℝ) + 1 := by positivity
          have h_pos_k : 0 < (k.toNat : ℝ) + 1 := by positivity
          have h_add_ineq : (n : ℝ) + 1 ≤ (k.toNat : ℝ) + 1 := by
            have h_k_real_ge_n : (k.toNat : ℝ) ≥ (n : ℝ) := by exact_mod_cast hk_nat_ge_n
            linarith
          have h_ineq : -((k.toNat : ℝ) + 1)⁻¹ ≥ -((n : ℝ) + 1)⁻¹ := by
            have h_inv_ineq : ((k.toNat : ℝ) + 1)⁻¹ ≤ ((n : ℝ) + 1)⁻¹ := by
              simpa using (one_div_le_one_div h_pos_k h_pos_n).mpr h_add_ineq
            linarith
          exact_mod_cast h_ineq
    rw [h_inf, show (-((n : ℝ) + 1)⁻¹ : EReal) = (if Even n then -(n+2:ℝ)⁻¹ else -(n+1:ℝ)⁻¹ : ℝ) by
      simp [h]]

example (n:ℕ) : Example_6_4_9.lowerseq n = if Even n then -(n+2:ℝ)⁻¹ else -(n+1:ℝ)⁻¹ := by
  rw [lowerseq_formula_9 n]

example : Example_6_4_9.liminf = 0 := by
  unfold Sequence.liminf
  have hm : Example_6_4_9.m = (0 : ℤ) := by
    unfold Example_6_4_9; simp
  rw [hm]
  let S := {x | ∃ N ≥ (0 : ℤ), x = Example_6_4_9.lowerseq N}
  have h_nonempty : S.Nonempty := by
    refine ⟨Example_6_4_9.lowerseq (0 : ℤ), ?_⟩
    refine ⟨(0 : ℤ), le_refl _, rfl⟩
  have h_le_zero : ∀ a ∈ S, a ≤ (0 : EReal) := by
    intro a ha
    rcases ha with ⟨N, hN, rfl⟩
    have h_nonneg : N ≥ 0 := hN
    have hN_cast : (N.toNat : ℤ) = N := Int.toNat_of_nonneg h_nonneg
    have h_low_eq : Example_6_4_9.lowerseq N = Example_6_4_9.lowerseq (N.toNat : ℕ) := by
      simp [hN_cast]
    rw [h_low_eq]
    by_cases h_even : Even (N.toNat : ℕ)
    · have h_formula : Example_6_4_9.lowerseq (N.toNat : ℕ) = (-(((N.toNat : ℝ) + 2)⁻¹ : ℝ) : EReal) := by
        have h := lowerseq_formula_9 (N.toNat : ℕ)
        have h' : Example_6_4_9.lowerseq (N.toNat : ℕ) = (-((N.toNat : ℝ) + 2)⁻¹ : ℝ) := by
          simpa [h_even] using h
        exact_mod_cast h'
      rw [h_formula]
      have h_nonpos : (-(((N.toNat : ℝ) + 2)⁻¹ : ℝ) : EReal) ≤ (0 : EReal) := by
        have h_nonpos_real : -(((N.toNat : ℝ) + 2)⁻¹ : ℝ) ≤ (0 : ℝ) := by
          have hpos : 0 < ((N.toNat : ℝ) + 2)⁻¹ := by positivity
          linarith
        exact_mod_cast h_nonpos_real
      exact h_nonpos
    · have h_formula : Example_6_4_9.lowerseq (N.toNat : ℕ) = (-(((N.toNat : ℝ) + 1)⁻¹ : ℝ) : EReal) := by
        have h := lowerseq_formula_9 (N.toNat : ℕ)
        have h' : Example_6_4_9.lowerseq (N.toNat : ℕ) = (-((N.toNat : ℝ) + 1)⁻¹ : ℝ) := by
          simpa [h_even] using h
        exact_mod_cast h'
      rw [h_formula]
      have h_nonpos : (-(((N.toNat : ℝ) + 1)⁻¹ : ℝ) : EReal) ≤ (0 : EReal) := by
        have h_nonpos_real : -(((N.toNat : ℝ) + 1)⁻¹ : ℝ) ≤ (0 : ℝ) := by
          have hpos : 0 < ((N.toNat : ℝ) + 1)⁻¹ := by positivity
          linarith
        exact_mod_cast h_nonpos_real
      exact h_nonpos
  have h_gt_exists : ∀ (w : EReal), w < (0 : EReal) → ∃ a ∈ S, w < a := by
    intro w hw
    rcases w with (w|w)
    · -- w = ⊥
      have h_low_gt_bot : (⊥ : EReal) < Example_6_4_9.lowerseq (0 : ℤ) := by
        have h_val : Example_6_4_9.lowerseq (0 : ℤ) = ((-(1/2 : ℝ) : ℝ) : EReal) := by
          calc
            Example_6_4_9.lowerseq (0 : ℤ) = Example_6_4_9.lowerseq (0 : ℕ) := by simp
            _ = (-(((0 : ℝ) + 2)⁻¹ : ℝ) : EReal) := by
              have h := lowerseq_formula_9 0
              have h' : Example_6_4_9.lowerseq (0 : ℕ) = (-((0 : ℝ) + 2)⁻¹ : ℝ) := by
                have h_even_0 : Even (0 : ℕ) := ⟨0, by simp⟩
                simpa [h_even_0] using h
              exact_mod_cast h'
            _ = ((-(1/2 : ℝ) : ℝ) : EReal) := by norm_num
        have h_val' : Example_6_4_9.lowerseq (0 : ℤ) = ((-(1/2 : ℝ) : ℝ) : EReal) := h_val
        rw [h_val']
        exact EReal.bot_lt_coe _
      refine ⟨Example_6_4_9.lowerseq (0 : ℤ), ?_, h_low_gt_bot⟩
      refine ⟨(0 : ℤ), le_refl _, rfl⟩
    · rcases w with (w|w)
      · -- w = ⊤
        exfalso; exact not_top_lt hw
      · -- w = (c : ℝ) where c < 0
        have hc : (w : ℝ) < (0 : ℝ) := (EReal.coe_lt_coe_iff (x := w) (y := (0 : ℝ))).mp hw
        rcases exists_nat_gt (1 / (-w)) with ⟨k, hk⟩
        have hk_real : 1 / (-w) < (k : ℝ) := hk
        have h_neg_w_pos : 0 < -w := by linarith
        have h_pos_k1 : 0 < (k : ℝ) + 1 := by positivity
        have h_pos_k2 : 0 < (k : ℝ) + 2 := by positivity
        have h_w_ne_zero : w ≠ 0 := by linarith
        have h_inv_ineq1 : ((k : ℝ) + 1)⁻¹ < -w := by
          have h_ineq1 : (k : ℝ) + 1 > 1 / (-w) := by linarith
          have h_one_lt_mul : 1 < ((k : ℝ) + 1) * (-w) := by
            calc
              1 = (1 / (-w)) * (-w) := by field_simp [h_neg_w_pos.ne.symm, h_w_ne_zero]
              _ < ((k : ℝ) + 1) * (-w) := mul_lt_mul_of_pos_right h_ineq1 h_neg_w_pos
          have h_mul_ineq : ((k : ℝ) + 1)⁻¹ * ((k : ℝ) + 1) < (-w) * ((k : ℝ) + 1) := by
            calc
              ((k : ℝ) + 1)⁻¹ * ((k : ℝ) + 1) = 1 := by field_simp [h_pos_k1.ne.symm]
              _ < ((k : ℝ) + 1) * (-w) := h_one_lt_mul
              _ = (-w) * ((k : ℝ) + 1) := by ring
          exact lt_of_mul_lt_mul_right h_mul_ineq h_pos_k1.le
        have h_inv_ineq2 : ((k : ℝ) + 2)⁻¹ < -w := by
          have h_ineq2 : (k : ℝ) + 2 > 1 / (-w) := by linarith
          have h_one_lt_mul : 1 < ((k : ℝ) + 2) * (-w) := by
            calc
              1 = (1 / (-w)) * (-w) := by field_simp [h_neg_w_pos.ne.symm, h_w_ne_zero]
              _ < ((k : ℝ) + 2) * (-w) := mul_lt_mul_of_pos_right h_ineq2 h_neg_w_pos
          have h_mul_ineq : ((k : ℝ) + 2)⁻¹ * ((k : ℝ) + 2) < (-w) * ((k : ℝ) + 2) := by
            calc
              ((k : ℝ) + 2)⁻¹ * ((k : ℝ) + 2) = 1 := by field_simp [h_pos_k2.ne.symm]
              _ < ((k : ℝ) + 2) * (-w) := h_one_lt_mul
              _ = (-w) * ((k : ℝ) + 2) := by ring
          exact lt_of_mul_lt_mul_right h_mul_ineq h_pos_k2.le
        have h_low_gt_c : (w : EReal) < Example_6_4_9.lowerseq (k : ℕ) := by
          by_cases hk_even : Even k
          · have h_formula : Example_6_4_9.lowerseq (k : ℕ) = (-((k : ℝ) + 2)⁻¹ : EReal) := by
              have h := lowerseq_formula_9 k
              have h' : Example_6_4_9.lowerseq (k : ℕ) = (-((k : ℝ) + 2)⁻¹ : ℝ) := by
                simpa [hk_even] using h
              exact_mod_cast h'
            have h_w_lt_val : (w : ℝ) < -((k : ℝ) + 2)⁻¹ := by
              have : ((k : ℝ) + 2)⁻¹ < -w := h_inv_ineq2
              linarith
            have h_w_lt : (w : EReal) < (-((k : ℝ) + 2)⁻¹ : EReal) := by
              apply EReal.coe_lt_coe
              exact h_w_lt_val
            calc
              (w : EReal) < (-((k : ℝ) + 2)⁻¹ : EReal) := h_w_lt
              _ = Example_6_4_9.lowerseq (k : ℕ) := by symm; exact h_formula
          · have h_formula : Example_6_4_9.lowerseq (k : ℕ) = (-((k : ℝ) + 1)⁻¹ : EReal) := by
              have h := lowerseq_formula_9 k
              have h' : Example_6_4_9.lowerseq (k : ℕ) = (-((k : ℝ) + 1)⁻¹ : ℝ) := by
                simpa [hk_even] using h
              exact_mod_cast h'
            have h_w_lt_val : (w : ℝ) < -((k : ℝ) + 1)⁻¹ := by
              have : ((k : ℝ) + 1)⁻¹ < -w := h_inv_ineq1
              linarith
            have h_w_lt : (w : EReal) < (-((k : ℝ) + 1)⁻¹ : EReal) := by
              apply EReal.coe_lt_coe
              exact h_w_lt_val
            calc
              (w : EReal) < (-((k : ℝ) + 1)⁻¹ : EReal) := h_w_lt
              _ = Example_6_4_9.lowerseq (k : ℕ) := by symm; exact h_formula
        refine ⟨Example_6_4_9.lowerseq (k : ℕ), ?_, h_low_gt_c⟩
        refine ⟨(k : ℤ), ?_, rfl⟩
        exact_mod_cast (Nat.zero_le k)
  dsimp [S] at *
  exact csSup_eq_of_forall_le_of_forall_lt_exists_gt h_nonempty h_le_zero h_gt_exists

noncomputable abbrev Example_6_4_10 : Sequence := (fun (n:ℕ) ↦ (n+1:ℝ))

lemma upperseq_top_10 (n:ℕ) : Example_6_4_10.upperseq n = ⊤ := by
  unfold Sequence.upperseq
  erw [sSup_eq_top]
  intro b hb
  induction b using EReal.rec with
  | bot =>
    have hm : (Example_6_4_10.from (n:ℤ)).m = (n:ℤ) := by
      simp
    refine ⟨(Example_6_4_10.from (n:ℤ)) (n:ℤ), ?_, EReal.bot_lt_coe _⟩
    refine ⟨(n:ℤ), ?_, rfl⟩
    rw [hm]
  | top => exact absurd hb (lt_irrefl _)
  | coe r =>
    have hm : (Example_6_4_10.from (n:ℤ)).m = (n:ℤ) := by
      simp
    obtain ⟨k, hk⟩ := exists_nat_gt (max r (n : ℝ))
    have hk_nonneg : (k : ℤ) ≥ 0 := by exact_mod_cast (Nat.zero_le k)
    have hk_ge_n : (k : ℤ) ≥ (n : ℤ) := by
      have h_ineq : (n : ℝ) < (k : ℝ) := lt_of_le_of_lt (le_max_right _ _) hk
      exact_mod_cast h_ineq.le
    have h_eval : (Example_6_4_10.from (n:ℤ)) (k : ℤ) = ((k : ℕ) + 1 : ℝ) := by
      rw [Sequence.from_eval _ hk_ge_n]
      simp [hk_nonneg]
    refine ⟨(Example_6_4_10.from (n:ℤ)) (k : ℤ), ?_, ?_⟩
    · refine ⟨(k : ℤ), ?_, rfl⟩
      rw [hm]
      exact hk_ge_n
    · rw [h_eval]
      have hr_lt : (r : ℝ) < ((k : ℕ) + 1 : ℝ) := by
        have hk_r : (r : ℝ) < (k : ℝ) := lt_of_le_of_lt (le_max_left _ _) hk
        nlinarith
      exact mod_cast hr_lt

example : Example_6_4_10.limsup = ⊤ := by
  unfold Sequence.limsup
  apply sInf_eq_top.mpr
  intro x hx
  rcases hx with ⟨N, hN, rfl⟩
  have hN_nonneg : N ≥ (0 : ℤ) := by
    simpa [Example_6_4_10] using hN
  have hN_eq_cast : (N : ℤ) = (N.toNat : ℤ) := by
    simpa using (Int.toNat_of_nonneg hN_nonneg)
  rw [hN_eq_cast]
  exact upperseq_top_10 N.toNat

lemma lowerseq_n_10 (n:ℕ) : Example_6_4_10.lowerseq n = n+1 := by
  unfold Sequence.lowerseq
  have hm : (Example_6_4_10.from (n:ℤ)).m = (n:ℤ) := by
    simp
  apply le_antisymm
  · apply sInf_le
    refine ⟨(n:ℤ), by rw [hm], ?_⟩
    rw [Sequence.from_eval _ (by exact le_refl (n:ℤ))]
    simp
  · apply le_sInf
    rintro x ⟨k, hk, rfl⟩
    rw [hm] at hk
    rw [Sequence.from_eval _ hk]
    have hk_nonneg : (k : ℤ) ≥ (0 : ℤ) :=
      le_trans (by exact_mod_cast (Nat.zero_le n)) hk
    have h_val : Example_6_4_10 (k : ℤ) = (k.toNat + 1 : ℝ) := by
      simp [hk_nonneg]
    rw [h_val]
    have h_n_le_k : (n : ℕ) ≤ k.toNat := by
      have hk_int : (n : ℤ) ≤ k := hk
      have hn_nonneg_int : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast (Nat.zero_le n)
      have h_toNat := Int.toNat_le_toNat hk_int
      simpa [Int.toNat_of_nonneg hn_nonneg_int] using h_toNat
    have hineq : (n+1 : ℝ) ≤ (k.toNat + 1 : ℝ) := by
      have hcast : (n : ℝ) ≤ (k.toNat : ℝ) := by exact_mod_cast h_n_le_k
      nlinarith
    exact_mod_cast hineq

example : Example_6_4_10.liminf = ⊤ := by
  unfold Sequence.liminf
  erw [sSup_eq_top]
  intro b hb
  induction b using EReal.rec with
  | bot =>
    have h_low : Example_6_4_10.lowerseq 0 = (1 : ℝ) := by
      simpa using lowerseq_n_10 0
    refine ⟨Example_6_4_10.lowerseq 0, ⟨(0 : ℤ), by simp, rfl⟩, ?_⟩
    rw [h_low]
    exact EReal.bot_lt_coe (1 : ℝ)
  | top => exact absurd hb (lt_irrefl _)
  | coe r =>
    obtain ⟨k, hk⟩ := exists_nat_gt r
    have h_low : Example_6_4_10.lowerseq k = (k+1 : ℝ) := by
      simpa using lowerseq_n_10 k
    refine ⟨Example_6_4_10.lowerseq k, ⟨(k : ℤ), by simp, rfl⟩, ?_⟩
    rw [h_low]
    apply EReal.coe_lt_coe
    have hk' : (r : ℝ) < (k+1 : ℝ) := by
      have hk_r : (r : ℝ) < (k : ℝ) := hk
      nlinarith
    exact hk'

/-- Proposition 6.4.12(a) -/
theorem Sequence.gt_limsup_bounds {a:Sequence} {x:EReal} (h: x > a.limsup) :
    ∃ N ≥ a.m, ∀ n ≥ N, a n < x := by
  -- This proof is written to follow the structure of the original text.
  simp only [limsup, sInf_lt_iff] at h
  obtain ⟨y, hy, ha⟩ := h
  obtain ⟨N, hN, hNy⟩ := hy
  rw [hNy] at ha; use N
  simp [hN, upperseq] at ha ⊢; intro n _
  have hn' : n ≥ (a.from N).m := by grind
  convert lt_of_le_of_lt ((a.from N).le_sup hn') ha using 1
  grind

/-- Proposition 6.4.12(a) -/
theorem Sequence.lt_liminf_bounds {a:Sequence} {y:EReal} (h: y < a.liminf) :
    ∃ N ≥ a.m, ∀ n ≥ N, a n > y := by
  simp only [liminf, lt_sSup_iff] at h
  obtain ⟨y', hy', ha⟩ := h
  obtain ⟨N, hN, hNy⟩ := hy'
  rw [hNy] at ha; use N
  simp [hN, lowerseq] at ha ⊢; intro n _
  have hn' : n ≥ (a.from N).m := by grind
  convert lt_of_lt_of_le ha ((a.from N).ge_inf hn') using 1
  grind

/-- Proposition 6.4.12(b) -/
theorem Sequence.lt_limsup_bounds {a:Sequence} {x:EReal} (h: x < a.limsup) {N:ℤ} (hN: N ≥ a.m) :
    ∃ n ≥ N, a n > x := by
  -- This proof is written to follow the structure of the original text.
  have hx : x < a.upperseq N := by apply lt_of_lt_of_le h (sInf_le _); simp; use N
  choose n hn hxn _ using exists_between_lt_sup hx
  grind

/-- Proposition 6.4.12(b) -/
theorem Sequence.gt_liminf_bounds {a:Sequence} {x:EReal} (h: x > a.liminf) {N:ℤ} (hN: N ≥ a.m) :
    ∃ n ≥ N, a n < x := by
  have hx_low : x > a.lowerseq N := by
    calc
      x > a.liminf := h
      _ ≥ a.lowerseq N := le_sSup (by simp [lowerseq]; use N)
  have hx_inf : x > (a.from N).inf := by
    simpa [lowerseq] using hx_low
  obtain ⟨n, hn, hxn, _⟩ := Sequence.exists_between_gt_inf hx_inf
  have hm : (a.from N).m = N := by
    dsimp [Sequence.from, Sequence.mk']; simp [hN]
  rw [hm] at hn
  have h_eq : (a.from N) n = a n := Sequence.from_eval a hn
  rw [h_eq] at hxn
  exact ⟨n, hn, hxn⟩

/-- Proposition 6.4.12(c) / Exercise 6.4.3 -/
theorem Sequence.inf_le_liminf (a:Sequence) : a.inf ≤ a.liminf := by
  have h : (a.from a.m).inf = a.inf := by
    have hm : (a.from a.m).m = a.m := by
      dsimp [Sequence.from, Sequence.mk']; simp
    unfold Sequence.inf
    rw [hm]
    apply congrArg sInf
    ext x; constructor
    · rintro ⟨n, hn, rfl⟩
      refine ⟨n, hn, ?_⟩
      exact_mod_cast Sequence.from_eval a hn
    · rintro ⟨n, hn, rfl⟩
      refine ⟨n, hn, ?_⟩
      exact_mod_cast (Sequence.from_eval a hn).symm
  calc
    a.inf = (a.from a.m).inf := by symm; exact h
    _ = a.lowerseq a.m := rfl
    _ ≤ a.liminf := le_sSup (⟨a.m, le_refl _, rfl⟩)

/-- Proposition 6.4.12(c) / Exercise 6.4.3 -/
theorem Sequence.liminf_le_limsup (a:Sequence) : a.liminf ≤ a.limsup := by
  have h_pair : ∀ N M, a.m ≤ N → a.m ≤ M → a.lowerseq N ≤ a.upperseq M := by
    intro N M hN hM
    have hN_m : (a.from N).m = N := by
      dsimp [Sequence.from, Sequence.mk']; simp [hN]
    have hM_m : (a.from M).m = M := by
      dsimp [Sequence.from, Sequence.mk']; simp [hM]
    set k := max N M with hk_def
    have hkN : k ≥ N := le_max_left _ _
    have hkM : k ≥ M := le_max_right _ _
    calc
      a.lowerseq N = (a.from N).inf := rfl
      _ ≤ ((a.from N) k : EReal) := Sequence.ge_inf (by rw [hN_m]; exact hkN)
      _ = (a k : EReal) := by exact_mod_cast Sequence.from_eval a hkN
      _ = ((a.from M) k : EReal) := by exact_mod_cast (Sequence.from_eval a hkM).symm
      _ ≤ (a.from M).sup := Sequence.le_sup (by rw [hM_m]; exact hkM)
      _ = a.upperseq M := rfl
  apply sSup_le
  rintro x ⟨N, hN, rfl⟩
  apply le_sInf
  rintro y ⟨M, hM, rfl⟩
  exact h_pair N M hN hM

/-- Proposition 6.4.12(c) / Exercise 6.4.3 -/
theorem Sequence.limsup_le_sup (a:Sequence) : a.limsup ≤ a.sup := by
  have h : (a.from a.m).sup = a.sup := by
    have hm : (a.from a.m).m = a.m := by
      dsimp [Sequence.from, Sequence.mk']; simp
    unfold Sequence.sup
    rw [hm]
    apply congrArg sSup
    ext x; constructor
    · rintro ⟨n, hn, rfl⟩
      refine ⟨n, hn, ?_⟩
      exact_mod_cast Sequence.from_eval a hn
    · rintro ⟨n, hn, rfl⟩
      refine ⟨n, hn, ?_⟩
      exact_mod_cast (Sequence.from_eval a hn).symm
  calc
    a.limsup ≤ a.upperseq a.m := sInf_le (⟨a.m, le_refl _, rfl⟩)
    _ = (a.from a.m).sup := rfl
    _ = a.sup := h

/-- Proposition 6.4.12(d) / Exercise 6.4.3 -/
theorem Sequence.limit_point_between_liminf_limsup {a:Sequence} {c:ℝ} (h: a.LimitPoint c) :
  a.liminf ≤ c ∧ c ≤ a.limsup := by
  have h_c_le_limsup : (c : EReal) ≤ a.limsup := by
    by_contra! hc
    -- hc : a.limsup < (c : EReal)
    rcases exists_between hc with ⟨y, h_limsup_lt_y, hy_lt_c⟩
    have hy_not_bot : y ≠ ⊥ := by
      intro hy_eq
      rw [hy_eq] at h_limsup_lt_y
      exact not_lt.mpr bot_le h_limsup_lt_y
    have hy_not_top : y ≠ ⊤ := by
      intro hy_eq
      rw [hy_eq] at hy_lt_c
      exact not_lt.mpr le_top hy_lt_c
    have hy_real : ∃ r : ℝ, y = (r : EReal) := by
      induction y using EReal.rec with
      | bot => exact (hy_not_bot rfl).elim
      | top => exact (hy_not_top rfl).elim
      | coe r => exact ⟨r, rfl⟩
    rcases hy_real with ⟨r, hr⟩
    rw [hr] at h_limsup_lt_y hy_lt_c
    have hr_lt_c : r < c := by exact_mod_cast hy_lt_c
    rcases Sequence.gt_limsup_bounds h_limsup_lt_y with ⟨N₁, hN₁, hN₁_bound⟩
    set ε := (c - r) / 2 with hε_def
    have hε_pos : ε > 0 := by
      dsimp [ε]; nlinarith
    rcases (Sequence.limit_point_def a c).mp h ε hε_pos N₁ hN₁ with ⟨n, hn, hn_bound⟩
    have ha_n_ge_mid : a n ≥ (c + r) / 2 := by
      have ha_n_ge_c_minus_ε : a n ≥ c - ε := by
        linarith [abs_le.mp hn_bound]
      dsimp [ε] at ha_n_ge_c_minus_ε
      nlinarith
    have ha_n_lt_r : a n < r := by
      have := hN₁_bound n hn
      exact_mod_cast this
    nlinarith
  have h_liminf_le_c : a.liminf ≤ (c : EReal) := by
    by_contra! hc
    -- hc : (c : EReal) < a.liminf
    rcases exists_between hc with ⟨y, hc_lt_y, hy_lt_liminf⟩
    have hy_not_bot : y ≠ ⊥ := by
      intro hy_eq
      rw [hy_eq] at hc_lt_y
      exact not_lt.mpr bot_le hc_lt_y
    have hy_not_top : y ≠ ⊤ := by
      intro hy_eq
      rw [hy_eq] at hy_lt_liminf
      exact not_lt.mpr le_top hy_lt_liminf
    have hy_real : ∃ r : ℝ, y = (r : EReal) := by
      induction y using EReal.rec with
      | bot => exact (hy_not_bot rfl).elim
      | top => exact (hy_not_top rfl).elim
      | coe r => exact ⟨r, rfl⟩
    rcases hy_real with ⟨r, hr⟩
    rw [hr] at hc_lt_y hy_lt_liminf
    have hc_lt_r : c < r := by exact_mod_cast hc_lt_y
    rcases Sequence.lt_liminf_bounds hy_lt_liminf with ⟨N₂, hN₂, hN₂_bound⟩
    set ε := (r - c) / 2 with hε_def
    have hε_pos : ε > 0 := by
      dsimp [ε]; nlinarith
    rcases (Sequence.limit_point_def a c).mp h ε hε_pos N₂ hN₂ with ⟨n, hn, hn_bound⟩
    have ha_n_le_mid : a n ≤ (c + r) / 2 := by
      have ha_n_le_c_plus_ε : a n ≤ c + ε := by
        linarith [abs_le.mp hn_bound]
      dsimp [ε] at ha_n_le_c_plus_ε
      nlinarith
    have ha_n_gt_r : a n > r := by
      have := hN₂_bound n hn
      exact_mod_cast this
    nlinarith
  exact ⟨h_liminf_le_c, h_c_le_limsup⟩

/-- Proposition 6.4.12(e) / Exercise 6.4.3 -/
theorem Sequence.limit_point_of_limsup {a:Sequence} {L_plus:ℝ} (h: a.limsup = L_plus) :
    a.LimitPoint L_plus := by
  rw [Sequence.limit_point_def]
  intro ε hε N hN
  have h_lt_limsup : (L_plus - ε : EReal) < a.limsup := by
    rw [h]
    have : L_plus - ε < L_plus := by nlinarith
    exact_mod_cast this
  have h_limsup_lt_plus : a.limsup < (L_plus + ε : EReal) := by
    rw [h]
    have : L_plus < L_plus + ε := by nlinarith
    exact_mod_cast this
  have h_sInf_lt : sInf {x | ∃ K' ≥ a.m, x = Sequence.upperseq a K'} < (L_plus + ε : EReal) := by
    simpa [Sequence.limsup] using h_limsup_lt_plus
  rcases sInf_lt_iff.mp h_sInf_lt with ⟨x, hx, hx_lt⟩
  rcases hx with ⟨K, hK, hx_eq⟩
  rw [hx_eq] at hx_lt
  set N0 := max N K with hN0_def
  have hN0_ge_N : N0 ≥ N := le_max_left _ _
  have hN0_ge_K : N0 ≥ K := le_max_right _ _
  have hN0_ge_am : N0 ≥ a.m := le_trans hN hN0_ge_N
  rcases Sequence.lt_limsup_bounds h_lt_limsup hN0_ge_am with ⟨n, hn, ha_n_gt⟩
  have hn_ge_N : n ≥ N := le_trans hN0_ge_N hn
  have hn_ge_K : n ≥ K := le_trans hN0_ge_K hn
  have hn_ge_am : n ≥ a.m := le_trans hN0_ge_am hn
  have hn_ge_fromK_m : n ≥ (a.from K).m := by
    dsimp [Sequence.from, Sequence.mk']
    have : (max a.m K : ℤ) ≤ n := max_le hn_ge_am hn_ge_K
    simpa
  have ha_n_gt_real : a n > L_plus - ε := by
    exact_mod_cast ha_n_gt
  have ha_n_lt_plus : a n < L_plus + ε := by
    have h_upper : (a n : EReal) ≤ Sequence.upperseq a K := by
      calc
        (a n : EReal) = ((a.from K) n : EReal) := by
          exact_mod_cast (Sequence.from_eval a hn_ge_K).symm
        _ ≤ (a.from K).sup := Sequence.le_sup hn_ge_fromK_m
        _ = Sequence.upperseq a K := rfl
    have h_lt : (a n : EReal) < (L_plus + ε : EReal) := by
      calc
        (a n : EReal) ≤ Sequence.upperseq a K := h_upper
        _ < (L_plus + ε : EReal) := hx_lt
    exact_mod_cast h_lt
  have h_abs : |a n - L_plus| ≤ ε := by
    rw [abs_le]
    constructor
    · nlinarith
    · nlinarith
  exact ⟨n, hn_ge_N, h_abs⟩

/-- Proposition 6.4.12(e) / Exercise 6.4.3 -/
theorem Sequence.limit_point_of_liminf {a:Sequence} {L_minus:ℝ} (h: a.liminf = L_minus) :
    a.LimitPoint L_minus := by
  rw [Sequence.limit_point_def]
  intro ε hε N hN
  have h_lt_liminf : (L_minus - ε : EReal) < a.liminf := by
    rw [h]
    have : L_minus - ε < L_minus := by nlinarith
    exact_mod_cast this
  have h_liminf_lt_plus : a.liminf < (L_minus + ε : EReal) := by
    rw [h]
    have : L_minus < L_minus + ε := by nlinarith
    exact_mod_cast this
  have h_lt_sSup : (L_minus - ε : EReal) < sSup {x | ∃ K' ≥ a.m, x = Sequence.lowerseq a K'} := by
    simpa [Sequence.liminf] using h_lt_liminf
  rcases lt_sSup_iff.mp h_lt_sSup with ⟨x, hx, hx_lt⟩
  rcases hx with ⟨K, hK, hx_eq⟩
  rw [hx_eq] at hx_lt
  set N0 := max N K with hN0_def
  have hN0_ge_N : N0 ≥ N := le_max_left _ _
  have hN0_ge_K : N0 ≥ K := le_max_right _ _
  have hN0_ge_am : N0 ≥ a.m := le_trans hN hN0_ge_N
  rcases Sequence.gt_liminf_bounds h_liminf_lt_plus hN0_ge_am with ⟨n, hn, ha_n_lt⟩
  have hn_ge_N : n ≥ N := le_trans hN0_ge_N hn
  have hn_ge_K : n ≥ K := le_trans hN0_ge_K hn
  have hn_ge_am : n ≥ a.m := le_trans hN0_ge_am hn
  have hn_ge_fromK_m : n ≥ (a.from K).m := by
    dsimp [Sequence.from, Sequence.mk']
    have : (max a.m K : ℤ) ≤ n := max_le hn_ge_am hn_ge_K
    simpa
  have ha_n_gt_minus : a n > L_minus - ε := by
    have h_lower : Sequence.lowerseq a K ≤ (a n : EReal) := by
      calc
        Sequence.lowerseq a K = (a.from K).inf := rfl
        _ ≤ ((a.from K) n : EReal) := Sequence.ge_inf hn_ge_fromK_m
        _ = (a n : EReal) := by
          exact_mod_cast (Sequence.from_eval a hn_ge_K)
    have h_lt_lower : (L_minus - ε : EReal) < Sequence.lowerseq a K := hx_lt
    have : (L_minus - ε : EReal) < (a n : EReal) := lt_of_lt_of_le h_lt_lower h_lower
    exact_mod_cast this
  have ha_n_lt_real : a n < L_minus + ε := by
    exact_mod_cast ha_n_lt
  have h_abs : |a n - L_minus| ≤ ε := by
    rw [abs_le]
    constructor
    · nlinarith
    · nlinarith
  exact ⟨n, hn_ge_N, h_abs⟩

/-- Proposition 6.4.12(f) / Exercise 6.4.3 -/
theorem Sequence.tendsTo_iff_eq_limsup_liminf {a:Sequence} (c:ℝ) :
  a.TendsTo c ↔ a.liminf = c ∧ a.limsup = c := by
  constructor
  · intro hTends
    have h_limit_point : a.LimitPoint c := Sequence.limit_point_of_limit hTends
    have h_between := Sequence.limit_point_between_liminf_limsup h_limit_point
    rcases h_between with ⟨h_liminf_le_c, h_c_le_limsup⟩
    have h_c_le_liminf : (c : EReal) ≤ a.liminf := by
      by_contra! hc
      have hc_lt : a.liminf < (c : EReal) := hc
      rcases exists_between hc_lt with ⟨y, h_liminf_lt_y, hy_lt_c⟩
      have hy_not_bot : y ≠ ⊥ := by
        intro hy_eq
        rw [hy_eq] at h_liminf_lt_y
        exact not_lt.mpr bot_le h_liminf_lt_y
      have hy_not_top : y ≠ ⊤ := by
        intro hy_eq
        rw [hy_eq] at hy_lt_c
        exact not_lt.mpr le_top hy_lt_c
      have hy_real : ∃ r : ℝ, y = (r : EReal) := by
        induction y using EReal.rec with
        | bot => exact (hy_not_bot rfl).elim
        | top => exact (hy_not_top rfl).elim
        | coe r => exact ⟨r, rfl⟩
      rcases hy_real with ⟨r, hr⟩
      rw [hr] at h_liminf_lt_y hy_lt_c
      have hr_lt_c : r < c := by exact_mod_cast hy_lt_c
      rw [Sequence.tendsTo_iff] at hTends
      set δ := c - r with hδ_def
      have hδ_pos : δ > 0 := by nlinarith
      rcases hTends δ hδ_pos with ⟨N, hN⟩
      set N' := max N a.m with hN'_def
      have hN'_ge_am : N' ≥ a.m := le_max_right _ _
      have hN'_ge_N : N' ≥ N := le_max_left _ _
      have hN'_bound : ∀ n ≥ N', a n ≥ r := by
        intro n hn'
        have hn_N : n ≥ N := le_trans hN'_ge_N hn'
        have h_abs : |a n - c| ≤ δ := hN n hn_N
        have : a n ≥ c - δ := by linarith [abs_le.mp h_abs]
        dsimp [δ] at this
        nlinarith
      have h_lower_sup : (r : EReal) ≤ (a.from N').inf := by
        apply le_sInf
        rintro x ⟨n, hn, rfl⟩
        have hn_N' : n ≥ N' := by
          dsimp [Sequence.from, Sequence.mk'] at hn
          simp at hn
          exact hn.2
        have hx_ge_r : a n ≥ r := hN'_bound n hn_N'
        have h_cast : (r : EReal) ≤ (a n : EReal) := by exact_mod_cast hx_ge_r
        rw [Sequence.from_eval a hn_N']
        exact h_cast
      have h_liminf_ge_lower : (a.from N').inf ≤ a.liminf := by
        have : (a.from N').inf = Sequence.lowerseq a N' := rfl
        rw [this]
        exact le_sSup (⟨N', hN'_ge_am, rfl⟩)
      have : (r : EReal) ≤ a.liminf := le_trans h_lower_sup h_liminf_ge_lower
      exact not_lt.mpr this h_liminf_lt_y
    have h_limsup_le_c : a.limsup ≤ (c : EReal) := by
      by_contra! hc
      have hc_lt : (c : EReal) < a.limsup := hc
      rcases exists_between hc_lt with ⟨y, hc_lt_y, hy_lt_limsup⟩
      have hy_not_bot : y ≠ ⊥ := by
        intro hy_eq
        rw [hy_eq] at hc_lt_y
        exact not_lt.mpr bot_le hc_lt_y
      have hy_not_top : y ≠ ⊤ := by
        intro hy_eq
        rw [hy_eq] at hy_lt_limsup
        exact not_lt.mpr le_top hy_lt_limsup
      have hy_real : ∃ r : ℝ, y = (r : EReal) := by
        induction y using EReal.rec with
        | bot => exact (hy_not_bot rfl).elim
        | top => exact (hy_not_top rfl).elim
        | coe r => exact ⟨r, rfl⟩
      rcases hy_real with ⟨r, hr⟩
      rw [hr] at hc_lt_y hy_lt_limsup
      have hc_lt_r : c < r := by exact_mod_cast hc_lt_y
      rw [Sequence.tendsTo_iff] at hTends
      set δ := r - c with hδ_def
      have hδ_pos : δ > 0 := by nlinarith
      rcases hTends δ hδ_pos with ⟨N, hN⟩
      set N' := max N a.m with hN'_def
      have hN'_ge_am : N' ≥ a.m := le_max_right _ _
      have hN'_ge_N : N' ≥ N := le_max_left _ _
      have hN'_bound : ∀ n ≥ N', a n ≤ r := by
        intro n hn'
        have hn_N : n ≥ N := le_trans hN'_ge_N hn'
        have h_abs : |a n - c| ≤ δ := hN n hn_N
        have : a n ≤ c + δ := by linarith [abs_le.mp h_abs]
        dsimp [δ] at this
        nlinarith
      have h_upper_sup : (a.from N').sup ≤ (r : EReal) := by
        apply sSup_le
        rintro x ⟨n, hn, rfl⟩
        have hn_N' : n ≥ N' := by
          dsimp [Sequence.from, Sequence.mk'] at hn
          simp at hn
          exact hn.2
        have hx_le_r : a n ≤ r := hN'_bound n hn_N'
        have h_cast : (a n : EReal) ≤ (r : EReal) := by exact_mod_cast hx_le_r
        rw [Sequence.from_eval a hn_N']
        exact h_cast
      have h_limsup_le_upper : a.limsup ≤ (a.from N').sup :=
        sInf_le (⟨N', hN'_ge_am, rfl⟩)
      have : a.limsup ≤ (r : EReal) := le_trans h_limsup_le_upper h_upper_sup
      exact not_lt.mpr this hy_lt_limsup
    have h_liminf_eq : a.liminf = (c : EReal) := le_antisymm h_liminf_le_c h_c_le_liminf
    have h_limsup_eq : a.limsup = (c : EReal) := le_antisymm h_limsup_le_c h_c_le_limsup
    exact ⟨h_liminf_eq, h_limsup_eq⟩
  · intro h
    rcases h with ⟨h_liminf_eq, h_limsup_eq⟩
    rw [Sequence.tendsTo_iff]
    intro ε hε
    have h_lt_liminf : (c - ε : EReal) < a.liminf := by
      rw [h_liminf_eq]
      have : c - ε < c := by nlinarith
      exact_mod_cast this
    have h_limsup_lt : a.limsup < (c + ε : EReal) := by
      rw [h_limsup_eq]
      have : c < c + ε := by nlinarith
      exact_mod_cast this
    rcases Sequence.lt_liminf_bounds h_lt_liminf with ⟨N₁, hN₁, hN₁_bound⟩
    rcases Sequence.gt_limsup_bounds h_limsup_lt with ⟨N₂, hN₂, hN₂_bound⟩
    set N := max N₁ N₂ with hN_def
    have hN_ge_N₁ : N ≥ N₁ := le_max_left _ _
    have hN_ge_N₂ : N ≥ N₂ := le_max_right _ _
    have hN_ge_am : N ≥ a.m := le_trans hN₁ hN_ge_N₁
    refine ⟨N, ?_⟩
    intro n hn
    have hn_ge_N₁ : n ≥ N₁ := le_trans hN_ge_N₁ hn
    have hn_ge_N₂ : n ≥ N₂ := le_trans hN_ge_N₂ hn
    have h_lower : a n > c - ε := by
      have := hN₁_bound n hn_ge_N₁
      exact_mod_cast this
    have h_upper : a n < c + ε := by
      have := hN₂_bound n hn_ge_N₂
      exact_mod_cast this
    rw [abs_le]
    constructor <;> nlinarith

/-- Lemma 6.4.13 (Comparison principle) / Exercise 6.4.4 -/
theorem Sequence.sup_mono {a b:Sequence} (hm: a.m = b.m) (hab: ∀ n ≥ a.m, a n ≤ b n) :
    a.sup ≤ b.sup := by
  unfold Sequence.sup
  apply sSup_le
  rintro x ⟨n, hn, rfl⟩
  have hmem : (b n : EReal) ∈ { x | ∃ n ≥ b.m, x = (b n : EReal) } := ⟨n, by rwa [← hm], rfl⟩
  have ha_le_b : (a n : EReal) ≤ (b n : EReal) := by exact_mod_cast hab n hn
  exact ha_le_b.trans (le_sSup hmem)

/-- Lemma 6.4.13 (Comparison principle) / Exercise 6.4.4 -/
theorem Sequence.inf_mono {a b:Sequence} (hm: a.m = b.m) (hab: ∀ n ≥ a.m, a n ≤ b n) :
    a.inf ≤ b.inf := by
  unfold Sequence.inf
  apply le_sInf
  rintro x ⟨n, hn, rfl⟩
  have hn_am : n ≥ a.m := by simpa [hm] using hn
  have ha_mem : (a n : EReal) ∈ { x | ∃ n ≥ a.m, x = (a n : EReal) } := ⟨n, hn_am, rfl⟩
  have ha_le_b : (a n : EReal) ≤ (b n : EReal) := by exact_mod_cast hab n hn_am
  exact (sInf_le ha_mem).trans ha_le_b

/-- Lemma 6.4.13 (Comparison principle) / Exercise 6.4.4 -/
theorem Sequence.limsup_mono {a b:Sequence} (hm: a.m = b.m) (hab: ∀ n ≥ a.m, a n ≤ b n) :
    a.limsup ≤ b.limsup := by
  have h_sup_mono (N : ℤ) (hN : N ≥ a.m) : (a.from N).sup ≤ (b.from N).sup := by
    apply Sequence.sup_mono (a := a.from N) (b := b.from N)
    · simp [hm]
    · intro n hn
      have hn_ge_am : n ≥ a.m := le_trans (le_max_left _ _) hn
      have hn_ge_N : n ≥ N := le_trans (le_max_right _ _) hn
      rw [Sequence.from_eval a hn_ge_N, Sequence.from_eval b hn_ge_N]
      exact hab n hn_ge_am
  apply le_sInf
  rintro y ⟨N, hN, rfl⟩
  have hN_am : N ≥ a.m := by
    simpa [hm] using hN
  have hmem : (a.from N).sup ∈ { x | ∃ M ≥ a.m, x = (a.from M).sup } := ⟨N, hN_am, rfl⟩
  have h_limsup_le : a.limsup ≤ (a.from N).sup := sInf_le hmem
  exact h_limsup_le.trans (h_sup_mono N hN_am)

/-- Lemma 6.4.13 (Comparison principle) / Exercise 6.4.4 -/
theorem Sequence.liminf_mono {a b:Sequence} (hm: a.m = b.m) (hab: ∀ n ≥ a.m, a n ≤ b n) :
    a.liminf ≤ b.liminf := by
  have h_inf_mono (N : ℤ) (hN : N ≥ a.m) : (a.from N).inf ≤ (b.from N).inf := by
    apply Sequence.inf_mono (a := a.from N) (b := b.from N)
    · simp [hm]
    · intro n hn
      have hn_ge_am : n ≥ a.m := le_trans (le_max_left _ _) hn
      have hn_ge_N : n ≥ N := le_trans (le_max_right _ _) hn
      rw [Sequence.from_eval a hn_ge_N, Sequence.from_eval b hn_ge_N]
      exact hab n hn_ge_am
  apply sSup_le
  rintro x ⟨N, hN, rfl⟩
  -- hN: N ≥ a.m (from a.liminf's index set)
  have hN_bm : N ≥ b.m := by simpa [hm] using hN
  have hmem : (b.from N).inf ∈ { x | ∃ M ≥ b.m, x = (b.from M).inf } := ⟨N, hN_bm, rfl⟩
  have h_inf_le_bliminf : (b.from N).inf ≤ b.liminf := le_sSup hmem
  exact (h_inf_mono N hN).trans h_inf_le_bliminf

/-- Corollary 6.4.14 (Squeeze test) / Exercise 6.4.5 -/
theorem Sequence.lim_of_between {a b c:Sequence} {L:ℝ} (hm: b.m = a.m ∧ c.m = a.m)
  (hab: ∀ n ≥ a.m, a n ≤ b n ∧ b n ≤ c n) (ha: a.TendsTo L) (hb: c.TendsTo L) :
    b.TendsTo L := by
  rcases hm with ⟨hm1, hm2⟩
  rw [Sequence.tendsTo_iff]
  intro ε hε
  rcases (Sequence.tendsTo_iff a L).mp ha ε hε with ⟨N₁, hN₁⟩
  rcases (Sequence.tendsTo_iff c L).mp hb ε hε with ⟨N₂, hN₂⟩
  use max a.m (max N₁ N₂)
  intro n hn
  have hn_am : n ≥ a.m := by omega
  have hn₁ : n ≥ N₁ := by
    have hmax : N₁ ≤ max a.m (max N₁ N₂) :=
      calc
        N₁ ≤ max N₁ N₂ := le_max_left _ _
        _ ≤ max a.m (max N₁ N₂) := le_max_right _ _
    omega
  have hn₂ : n ≥ N₂ := by
    have hmax : N₂ ≤ max a.m (max N₁ N₂) :=
      calc
        N₂ ≤ max N₁ N₂ := le_max_right _ _
        _ ≤ max a.m (max N₁ N₂) := le_max_right _ _
    omega
  have ha_bound : |a n - L| ≤ ε := hN₁ n hn₁
  have hc_bound : |c n - L| ≤ ε := hN₂ n hn₂
  rcases abs_le.mp ha_bound with ⟨h_low_a, h_high_a⟩
  rcases abs_le.mp hc_bound with ⟨h_low_c, h_high_c⟩
  rcases hab n hn_am with ⟨hle_ab, hle_bc⟩
  rw [abs_le]
  constructor
  · linarith
  · linarith

/-- Example 6.4.15 -/
example : ((fun (n:ℕ) ↦ 2/(n+1:ℝ)):Sequence).TendsTo 0 := by
  rw [Sequence.tendsTo_iff]
  intro ε hε
  rcases exists_nat_gt (2/ε) with ⟨N, hN⟩
  refine ⟨(N : ℤ), ?_⟩
  intro n hn
  have hn_nonneg : (0 : ℤ) ≤ n := by
    have hN_nonneg : (0 : ℤ) ≤ (N : ℤ) := by exact_mod_cast (Nat.zero_le N)
    omega
  have hval : ((fun (n:ℕ) ↦ 2/(n+1:ℝ)):Sequence) n = 2 / ((n.toNat : ℝ) + 1) := by
    simp [hn_nonneg]
  rw [hval, sub_zero]
  have hpos : 0 ≤ 2 / ((n.toNat : ℝ) + 1) := by positivity
  rw [abs_of_nonneg hpos]
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : (2/ε : ℝ) > 0 := div_pos (by norm_num) hε
    linarith
  have h2_lt_Nε : (2 : ℝ) < (N : ℝ) * ε := by
    calc
      (2 : ℝ) = (2/ε) * ε := by field_simp [hε.ne.symm]
      _ < (N : ℝ) * ε := mul_lt_mul_of_pos_right hN hε
  have h_2_div_N_lt_ε : 2 / (N : ℝ) < ε := by
    field_simp [hNpos.ne.symm]
    nlinarith
  have hn_toNat_N : (N : ℕ) ≤ n.toNat := by omega
  have hN_le_n_add_one : (N : ℝ) ≤ (n.toNat : ℝ) + 1 := by
    have hN_toNat : (N : ℝ) ≤ (n.toNat : ℝ) := by exact_mod_cast hn_toNat_N
    linarith
  have h_denom_pos1 : 0 < (n.toNat : ℝ) + 1 := by positivity
  have h_denom_pos2 : 0 < (N : ℝ) := hNpos
  have h_one_div : 1 / ((n.toNat : ℝ) + 1) ≤ 1 / (N : ℝ) :=
    (one_div_le_one_div h_denom_pos1 h_denom_pos2).mpr hN_le_n_add_one
  have h_seq_val : 2 / ((n.toNat : ℝ) + 1) ≤ 2 / (N : ℝ) := by
    calc
      2 / ((n.toNat : ℝ) + 1) = 2 * (1 / ((n.toNat : ℝ) + 1)) := by ring
      _ ≤ 2 * (1 / (N : ℝ)) := mul_le_mul_of_nonneg_left h_one_div (by norm_num)
      _ = 2 / (N : ℝ) := by ring
  linarith

/-- Example 6.4.15 -/
example : ((fun (n:ℕ) ↦ -2/(n+1:ℝ)):Sequence).TendsTo 0 := by
  rw [Sequence.tendsTo_iff]
  intro ε hε
  rcases exists_nat_gt (2/ε) with ⟨N, hN⟩
  refine ⟨(N : ℤ), ?_⟩
  intro n hn
  have hn_nonneg : (0 : ℤ) ≤ n := by
    have hN_nonneg : (0 : ℤ) ≤ (N : ℤ) := by exact_mod_cast (Nat.zero_le N)
    omega
  have hval : ((fun (n:ℕ) ↦ -2/(n+1:ℝ)):Sequence) n = -2 / ((n.toNat : ℝ) + 1) := by
    simp [hn_nonneg]
  rw [hval, sub_zero]
  have h_abs : |-2 / ((n.toNat : ℝ) + 1)| = 2 / ((n.toNat : ℝ) + 1) := by
    have hneg : -2 / ((n.toNat : ℝ) + 1) < 0 := by
      refine (div_neg_iff.2 (Or.inr ⟨by norm_num, by positivity⟩))
    rw [abs_of_neg hneg]
    simp [neg_div, neg_neg]
  rw [h_abs]
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : (2/ε : ℝ) > 0 := div_pos (by norm_num) hε
    linarith
  have h2_lt_Nε : (2 : ℝ) < (N : ℝ) * ε := by
    calc
      (2 : ℝ) = (2/ε) * ε := by field_simp [hε.ne.symm]
      _ < (N : ℝ) * ε := mul_lt_mul_of_pos_right hN hε
  have h_2_div_N_lt_ε : 2 / (N : ℝ) < ε := by
    field_simp [hNpos.ne.symm]
    nlinarith
  have hn_toNat_N : (N : ℕ) ≤ n.toNat := by omega
  have hN_le_n_add_one : (N : ℝ) ≤ (n.toNat : ℝ) + 1 := by
    have hN_toNat : (N : ℝ) ≤ (n.toNat : ℝ) := by exact_mod_cast hn_toNat_N
    linarith
  have h_denom_pos1 : 0 < (n.toNat : ℝ) + 1 := by positivity
  have h_denom_pos2 : 0 < (N : ℝ) := hNpos
  have h_one_div : 1 / ((n.toNat : ℝ) + 1) ≤ 1 / (N : ℝ) :=
    (one_div_le_one_div h_denom_pos1 h_denom_pos2).mpr hN_le_n_add_one
  have h_seq_val : 2 / ((n.toNat : ℝ) + 1) ≤ 2 / (N : ℝ) := by
    calc
      2 / ((n.toNat : ℝ) + 1) = 2 * (1 / ((n.toNat : ℝ) + 1)) := by ring
      _ ≤ 2 * (1 / (N : ℝ)) := mul_le_mul_of_nonneg_left h_one_div (by norm_num)
      _ = 2 / (N : ℝ) := by ring
  linarith

/-- Example 6.4.15 -/
example : ((fun (n:ℕ) ↦ (-1)^n/(n+1:ℝ) + 1 / (n+1)^2):Sequence).TendsTo 0 := by
  rw [Sequence.tendsTo_iff]
  intro ε hε
  rcases exists_nat_gt (2/ε) with ⟨N, hN⟩
  refine ⟨(N : ℤ), ?_⟩
  intro n hn
  have hn_nonneg : (0 : ℤ) ≤ n := by
    have hN_nonneg : (0 : ℤ) ≤ (N : ℤ) := by exact_mod_cast (Nat.zero_le N)
    omega
  have hval : ((fun (n:ℕ) ↦ (-1)^n/(n+1:ℝ) + 1 / (n+1)^2):Sequence) n =
    ((-1 : ℝ) ^ (n.toNat : ℕ) / ((n.toNat : ℝ) + 1) + 1 / (((n.toNat : ℝ) + 1)^2)) := by
    simp [hn_nonneg]
  rw [hval, sub_zero]
  have h_abs_term1 : |((-1 : ℝ) ^ (n.toNat : ℕ) / ((n.toNat : ℝ) + 1))| = 1 / ((n.toNat : ℝ) + 1) := by
    calc
      |((-1 : ℝ) ^ (n.toNat : ℕ) / ((n.toNat : ℝ) + 1))| = |((-1 : ℝ) ^ (n.toNat : ℕ))| / |((n.toNat : ℝ) + 1)| := by rw [abs_div]
      _ = |(-1 : ℝ)| ^ (n.toNat : ℕ) / |((n.toNat : ℝ) + 1)| := by rw [abs_pow]
      _ = 1 ^ (n.toNat : ℕ) / |((n.toNat : ℝ) + 1)| := by norm_num
      _ = 1 / |((n.toNat : ℝ) + 1)| := by simp
      _ = 1 / ((n.toNat : ℝ) + 1) := by rw [abs_of_pos (by positivity : 0 < (n.toNat : ℝ) + 1)]
  have h_abs_term2 : |1 / (((n.toNat : ℝ) + 1)^2)| = 1 / (((n.toNat : ℝ) + 1)^2) := by
    rw [abs_of_nonneg (by positivity : 0 ≤ 1 / (((n.toNat : ℝ) + 1)^2))]
  have h_bound : |((-1 : ℝ) ^ (n.toNat : ℕ) / ((n.toNat : ℝ) + 1) + 1 / (((n.toNat : ℝ) + 1)^2))|
    ≤ 2 / ((n.toNat : ℝ) + 1) := by
    calc
      |((-1 : ℝ) ^ (n.toNat : ℕ) / ((n.toNat : ℝ) + 1) + 1 / (((n.toNat : ℝ) + 1)^2))|
          ≤ |((-1 : ℝ) ^ (n.toNat : ℕ) / ((n.toNat : ℝ) + 1))| + |1 / (((n.toNat : ℝ) + 1)^2)| := abs_add_le _ _
      _ = 1 / ((n.toNat : ℝ) + 1) + 1 / (((n.toNat : ℝ) + 1)^2) := by simp [h_abs_term1]
      _ ≤ 1 / ((n.toNat : ℝ) + 1) + 1 / ((n.toNat : ℝ) + 1) := by
        have h_sq_ineq : ((n.toNat : ℝ) + 1)^2 ≥ (n.toNat : ℝ) + 1 := by
          nlinarith [sq_nonneg (n.toNat : ℝ)]
        have h_inv_ineq : 1 / (((n.toNat : ℝ) + 1)^2) ≤ 1 / ((n.toNat : ℝ) + 1) :=
          (one_div_le_one_div (by positivity : 0 < ((n.toNat : ℝ) + 1)^2)
            (by positivity : 0 < (n.toNat : ℝ) + 1)).mpr h_sq_ineq
        nlinarith
      _ = 2 / ((n.toNat : ℝ) + 1) := by ring
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : (2/ε : ℝ) > 0 := div_pos (by norm_num) hε
    linarith
  have h2_lt_Nε : (2 : ℝ) < (N : ℝ) * ε := by
    calc
      (2 : ℝ) = (2/ε) * ε := by field_simp [hε.ne.symm]
      _ < (N : ℝ) * ε := mul_lt_mul_of_pos_right hN hε
  have h_2_div_N_lt_ε : 2 / (N : ℝ) < ε := by
    field_simp [hNpos.ne.symm]
    nlinarith
  have hn_toNat_N : (N : ℕ) ≤ n.toNat := by omega
  have hN_le_n_add_one : (N : ℝ) ≤ (n.toNat : ℝ) + 1 := by
    have hN_toNat : (N : ℝ) ≤ (n.toNat : ℝ) := by exact_mod_cast hn_toNat_N
    linarith
  have h_denom_pos1 : 0 < (n.toNat : ℝ) + 1 := by positivity
  have h_denom_pos2 : 0 < (N : ℝ) := hNpos
  have h_one_div : 1 / ((n.toNat : ℝ) + 1) ≤ 1 / (N : ℝ) :=
    (one_div_le_one_div h_denom_pos1 h_denom_pos2).mpr hN_le_n_add_one
  have h_seq_val : 2 / ((n.toNat : ℝ) + 1) ≤ 2 / (N : ℝ) := by
    calc
      2 / ((n.toNat : ℝ) + 1) = 2 * (1 / ((n.toNat : ℝ) + 1)) := by ring
      _ ≤ 2 * (1 / (N : ℝ)) := mul_le_mul_of_nonneg_left h_one_div (by norm_num)
      _ = 2 / (N : ℝ) := by ring
  linarith

/-- Example 6.4.15 -/
example : ((fun (n:ℕ) ↦ (2:ℝ)^(-(n:ℤ))):Sequence).TendsTo 0 := by
  rw [Sequence.tendsTo_iff]
  intro ε hε
  rcases exists_pow_lt_of_lt_one hε (by norm_num : (1/2 : ℝ) < 1) with ⟨k, hk⟩
  refine ⟨(k : ℤ), ?_⟩
  intro n hn
  have hn_nonneg : (0 : ℤ) ≤ n := by
    have hk_nonneg : (0 : ℤ) ≤ (k : ℤ) := by exact_mod_cast (Nat.zero_le k)
    omega
  have hval : ((fun (n:ℕ) ↦ (2:ℝ)^(-(n:ℤ))):Sequence) n = (1/2 : ℝ) ^ (n.toNat : ℕ) := by
    calc
      ((fun (n:ℕ) ↦ (2:ℝ)^(-(n:ℤ))):Sequence) n = (2:ℝ)^(-(n.toNat : ℤ)) := by
        dsimp [Sequence.instCoe, Sequence.ofNatFun]
        simp [hn_nonneg]
      _ = ((2:ℝ) ^ (n.toNat : ℤ))⁻¹ := by rw [zpow_neg]
      _ = ((2:ℝ) ^ (n.toNat : ℕ))⁻¹ := by rw [zpow_natCast]
      _ = (1/2 : ℝ) ^ (n.toNat : ℕ) := by simp [inv_pow]
  rw [hval, sub_zero]
  have hpos : 0 ≤ (1/2 : ℝ) ^ (n.toNat : ℕ) := by positivity
  rw [abs_of_nonneg hpos]
  have hk_toNat : (k : ℕ) ≤ n.toNat := by omega
  have h_pow_le : (1/2 : ℝ) ^ (n.toNat : ℕ) ≤ (1/2 : ℝ) ^ k :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hk_toNat
  have h_pow_lt_ε : (1/2 : ℝ) ^ k < ε := hk
  linarith

abbrev Sequence.abs (a:Sequence) : Sequence where
  m := a.m
  seq n := |a n|
  vanish n hn := by simp [a.vanish n hn]


/-- Corollary 6.4.17 (Zero test for sequences) / Exercise 6.4.7 -/
theorem Sequence.tendsTo_zero_iff (a:Sequence) :
  a.TendsTo (0:ℝ) ↔ a.abs.TendsTo (0:ℝ) := by
  rw [Sequence.tendsTo_iff a 0, Sequence.tendsTo_iff (a.abs) 0]
  constructor
  · intro h ε hε
    rcases h ε hε with ⟨N, hN⟩
    refine ⟨N, λ n hn => ?_⟩
    have hN' := hN n hn
    simpa [sub_self, sub_zero, Sequence.abs] using hN'
  · intro h ε hε
    rcases h ε hε with ⟨N, hN⟩
    refine ⟨N, λ n hn => ?_⟩
    have hN' := hN n hn
    simpa [sub_self, sub_zero, Sequence.abs] using hN'

/--
  This helper lemma, implicit in the textbook proofs of Theorem 6.4.18 and Theorem 6.6.8, is made
  explicit here.
-/
theorem Sequence.finite_limsup_liminf_of_bounded {a:Sequence} (hbound: a.IsBounded) :
    (∃ L_plus:ℝ, a.limsup = L_plus) ∧ (∃ L_minus:ℝ, a.liminf = L_minus) := by
  choose M hMpos hbound using hbound
  have hlimsup_bound : a.limsup ≤ M := by
    apply a.limsup_le_sup.trans (sup_le_upper _)
    intro n hN; simp
    exact (le_abs_self _).trans (hbound n)
  have hliminf_bound : -M ≤ a.liminf := by
    apply (inf_ge_lower _).trans a.inf_le_liminf
    intro n hN; simp [←coe_neg]; rw [neg_le]
    exact (neg_le_abs _).trans (hbound n)
  split_ands
  . use a.limsup.toReal
    symm; apply coe_toReal
    . contrapose! hlimsup_bound; simp [hlimsup_bound]
    replace hliminf_bound := hliminf_bound.trans a.liminf_le_limsup
    contrapose! hliminf_bound; simp [hliminf_bound, ←coe_neg]
  use a.liminf.toReal; symm; apply coe_toReal
  . apply a.liminf_le_limsup.trans at hlimsup_bound
    contrapose! hlimsup_bound; simp [hlimsup_bound]
  contrapose! hliminf_bound; simp [hliminf_bound, ←coe_neg]

/-- Theorem 6.4.18 (Completeness of the reals) -/
theorem Sequence.Cauchy_iff_convergent (a:Sequence) :
  a.IsCauchy ↔ a.Convergent := by
  -- This proof is written to follow the structure of the original text.
  refine ⟨ ?_, IsCauchy.convergent ⟩; intro h
  have ⟨ ⟨ L_plus, hL_plus ⟩, ⟨ L_minus, hL_minus ⟩ ⟩ :=
    finite_limsup_liminf_of_bounded (bounded_of_cauchy h)
  use L_minus; simp [tendsTo_iff_eq_limsup_liminf, hL_minus, hL_plus]
  have hlow : 0 ≤ L_plus - L_minus := by
    have := a.liminf_le_limsup; simp [hL_minus, hL_plus] at this; grind
  have hup (ε:ℝ) (hε: ε>0) : L_plus - L_minus ≤ 2*ε := by
    specialize h ε hε; choose N hN hsteady using h
    have hN0 : N ≥ (a.from N).m := by grind
    have hN1 : (a.from N).seq N = a.seq N := by grind
    have h1 : (a N - ε:ℝ) ≤ (a.from N).inf := by
      apply inf_ge_lower; grind [Real.dist_eq, abs_le',EReal.coe_le_coe_iff]
    have h2 : (a.from N).inf ≤ L_minus := by
      simp_rw [←hL_minus, liminf, lowerseq]; apply le_sSup; simp; use N
    have h3 : (a.from N).sup ≤ (a N + ε:ℝ) := by
      apply sup_le_upper; grind [EReal.coe_le_coe_iff, Real.dist_eq, abs_le']
    have h4 : L_plus ≤ (a.from N).sup := by
      simp_rw [←hL_plus, limsup, upperseq]; apply sInf_le; simp; use N
    replace h1 := h1.trans h2
    replace h4 := h4.trans h3
    grind [EReal.coe_le_coe_iff]
  obtain hlow | hlow := le_iff_lt_or_eq.mp hlow
  . specialize hup ((L_plus - L_minus)/3) ?_ <;> linarith
  grind

/-- Exercise 6.4.6 -/
theorem Sequence.sup_not_strict_mono : ∃ (a b:ℕ → ℝ), (∀ n, a n < b n) ∧ ¬ (a:Sequence).sup < (b:Sequence).sup := by
  set a : ℕ → ℝ := λ n => 1 - 1 / ((n : ℝ) + 1) with ha
  set b : ℕ → ℝ := λ _ => 1 with hb
  have ha_pos : ∀ n : ℕ, 1 / ((n : ℝ) + 1) > 0 := by
    intro n; positivity
  have ha_sSup_real : sSup {a n | n : ℕ} = (1 : ℝ) := by
    apply le_antisymm
    · have h_nonempty : ({a n | n : ℕ} : Set ℝ).Nonempty := ⟨a 0, 0, rfl⟩
      apply csSup_le h_nonempty
      rintro x ⟨n, rfl⟩
      dsimp [a]
      have hpos : 1 / ((n : ℝ) + 1) ≥ 0 := (ha_pos n).le
      nlinarith
    · by_contra! hlt
      set d := 1 - sSup {a n | n : ℕ} with hd_def
      have hd_pos : d > 0 := by linarith
      rcases exists_nat_gt (1 / d) with ⟨N, hN⟩
      have hNpos : (N : ℝ) + 1 > 0 := by positivity
      have hN_d : (N : ℝ) * d > 1 := by
        calc
          (N : ℝ) * d > (1 / d) * d := by nlinarith
          _ = 1 := by field_simp [hd_pos.ne.symm]
      have h_mul : 1 < d * ((N : ℝ) + 1) := by nlinarith
      have h_aN : a N = 1 - 1 / ((N : ℝ) + 1) := rfl
      have h_ineq : a N > sSup {a n | n : ℕ} := by
        have hdiv : 1 / ((N : ℝ) + 1) < d := by
          calc
            1 / ((N : ℝ) + 1) < d * ((N : ℝ) + 1) / ((N : ℝ) + 1) := by gcongr
            _ = d := by field_simp [hNpos.ne.symm]
        nlinarith
      have h_mem : a N ∈ {a n | n : ℕ} := ⟨N, rfl⟩
      have h_bdd : _root_.BddAbove {a n | n : ℕ} := by
        refine ⟨1, ?_⟩
        rintro x ⟨n, rfl⟩
        dsimp [a]
        have hpos : 1 / ((n : ℝ) + 1) ≥ 0 := (ha_pos n).le
        nlinarith
      have h_sup_ge : a N ≤ sSup {a n | n : ℕ} := le_csSup h_bdd h_mem
      linarith
  have ha_sup : (a : Sequence).sup = (1 : ℝ) := by
    calc
      (a : Sequence).sup = sSup ((fun (x : ℝ) => (x : EReal)) '' {a n | n : ℕ}) := by
        unfold Sequence.sup
        apply congrArg sSup
        ext x; constructor
        · rintro ⟨n, hn, rfl⟩
          have hn' : n ≥ (0 : ℤ) := hn
          have h_eq : ((a : Sequence) n : EReal) = (a n.toNat : EReal) := by
            simp [hn']
          rw [h_eq]
          exact ⟨a n.toNat, ⟨n.toNat, rfl⟩, rfl⟩
        · rintro ⟨y, ⟨m, rfl⟩, rfl⟩
          refine ⟨(m : ℤ), ?_, ?_⟩
          · simp
          · simp
      _ = ((sSup {a n | n : ℕ} : ℝ) : EReal) :=
        EReal.sup_of_bounded_nonempty
          (by
            refine ⟨1, ?_⟩
            rintro x ⟨n, rfl⟩
            dsimp [a]
            have hpos : 1 / ((n : ℝ) + 1) ≥ 0 := (ha_pos n).le
            nlinarith
            : _root_.BddAbove {a n | n : ℕ})
          ⟨a 0, 0, rfl⟩
      _ = (1 : ℝ) := by norm_num [ha_sSup_real]
  have hb_sup : (b : Sequence).sup = (1 : ℝ) := by
    unfold Sequence.sup
    apply le_antisymm
    · apply sSup_le
      rintro x ⟨n, hn, rfl⟩
      have hpos : n ≥ (0 : ℤ) := by
        simpa using hn
      simp [b, hpos]
    · apply le_sSup
      refine ⟨(0 : ℤ), ?_, ?_⟩
      · simp
      · simp [b]
  refine ⟨a, b, ?_, ?_⟩
  · intro n
    dsimp [a, b]
    have hpos : 1 / ((n : ℝ) + 1) > 0 := ha_pos n
    nlinarith
  · rw [ha_sup, hb_sup]
    norm_num

/- Exercise 6.4.7 -/
def Sequence.tendsTo_real_iff :
  Decidable (∀ (a:Sequence) (x:ℝ), a.TendsTo x ↔ a.abs.TendsTo x) := by
  apply isFalse
  intro h
  let a : Sequence := (fun (n : ℕ) => (-1 : ℝ))
  have h1 : a.TendsTo (-1 : ℝ) := by
    rw [Sequence.tendsTo_iff a (-1 : ℝ)]
    intro ε hε
    refine ⟨0, λ n hn => ?_⟩
    simpa [a, hn] using hε.le
  have h2 : a.abs.TendsTo (-1 : ℝ) := by
    apply (h a (-1 : ℝ)).mp
    exact h1
  have h3 : a.abs.TendsTo (1 : ℝ) := by
    rw [Sequence.tendsTo_iff (a.abs) (1 : ℝ)]
    intro ε hε
    refine ⟨0, λ n hn => ?_⟩
    simpa [a, Sequence.abs, hn] using hε.le
  have h_contra : ¬ (a.abs.TendsTo (-1 : ℝ) ∧ a.abs.TendsTo (1 : ℝ)) :=
    Sequence.tendsTo_unique (a.abs) (by norm_num : (-1 : ℝ) ≠ (1 : ℝ))
  apply h_contra
  exact ⟨h2, h3⟩

/-- This definition is needed for Exercises 6.4.8 and 6.4.9. -/
abbrev Sequence.ExtendedLimitPoint (a:Sequence) (x:EReal) : Prop := if x = ⊤ then ¬ a.BddAbove else if x = ⊥ then ¬ a.BddBelow else a.LimitPoint x.toReal

/-- Exercise 6.4.8 -/
theorem Sequence.extended_limit_point_of_limsup (a:Sequence) : a.ExtendedLimitPoint a.limsup := by
  unfold Sequence.ExtendedLimitPoint
  by_cases hsup_top : a.limsup = ⊤
  · rw [hsup_top, if_pos rfl]
    intro hbdd
    rcases hbdd with ⟨M, hM⟩
    have hlimsup_le_M : a.limsup ≤ (M : EReal) := by
      have h_sInf_le_upper : a.limsup ≤ a.upperseq a.m :=
        sInf_le ⟨a.m, le_refl _, rfl⟩
      have h_upper_le_M : a.upperseq a.m ≤ (M : EReal) := by
        unfold Sequence.upperseq
        apply Sequence.sup_le_upper
        intro n hn
        have hn' : n ≥ a.m := by
          dsimp [Sequence.from, Sequence.mk'] at hn; omega
        have h_eq : (a.from a.m) n = a n := by
          exact_mod_cast Sequence.from_eval a hn'
        rw [h_eq]
        exact_mod_cast hM n hn'
      exact le_trans h_sInf_le_upper h_upper_le_M
    rw [hsup_top] at hlimsup_le_M
    exact (not_le.mpr (EReal.coe_lt_top M)) hlimsup_le_M
  · by_cases hsup_bot : a.limsup = ⊥
    · rw [hsup_bot]
      have h_ne_top : (⊥ : EReal) ≠ ⊤ := by decide
      rw [if_neg h_ne_top, if_pos rfl]
      intro hbdd
      rcases hbdd with ⟨M, hM⟩
      have hM_le_limsup : (M : EReal) ≤ a.limsup := by
        apply le_sInf
        intro x hx
        rcases hx with ⟨N, hN, hx_eq⟩
        rw [hx_eq]
        unfold Sequence.upperseq
        calc
          (M : EReal) ≤ (a N : EReal) := by exact_mod_cast hM N hN
          _ = ((a.from N) N : EReal) := by
            symm; exact_mod_cast (Sequence.from_eval a (le_refl N))
          _ ≤ (a.from N).sup := Sequence.le_sup (by
            dsimp [Sequence.from, Sequence.mk']; omega)
      rw [hsup_bot] at hM_le_limsup
      exact (not_le.mpr (EReal.bot_lt_coe M)) hM_le_limsup
    · rw [if_neg hsup_top, if_neg hsup_bot]
      have hL : a.limsup = (a.limsup.toReal : ℝ) :=
        (EReal.coe_toReal hsup_top hsup_bot).symm
      exact Sequence.limit_point_of_limsup hL

/-- Exercise 6.4.8 -/
theorem Sequence.extended_limit_point_of_liminf (a:Sequence) : a.ExtendedLimitPoint a.liminf := by
  unfold Sequence.ExtendedLimitPoint
  by_cases hinf_top : a.liminf = ⊤
  · rw [hinf_top, if_pos rfl]
    intro hbdd
    rcases hbdd with ⟨M, hM⟩
    have hliminf_le_M : a.liminf ≤ (M : EReal) := by
      apply sSup_le
      rintro x ⟨N, hN, rfl⟩
      unfold Sequence.lowerseq
      have h_inf_le_aN : (a.from N).inf ≤ (a.from N) N :=
        sInf_le ⟨N, show N ≥ (a.from N).m from by
          dsimp [Sequence.from, Sequence.mk']; omega, rfl⟩
      have h_aN_le_M : (a.from N) N ≤ (M : EReal) := by
        have : (a.from N) N = a N := by
          exact_mod_cast Sequence.from_eval a (le_refl N)
        rw [this]
        exact_mod_cast hM N hN
      exact le_trans h_inf_le_aN h_aN_le_M
    rw [hinf_top] at hliminf_le_M
    exact (not_le.mpr (EReal.coe_lt_top M)) hliminf_le_M
  · by_cases hinf_bot : a.liminf = ⊥
    · rw [hinf_bot]
      have h_ne_top : (⊥ : EReal) ≠ ⊤ := by decide
      rw [if_neg h_ne_top, if_pos rfl]
      intro hbdd
      rcases hbdd with ⟨M, hM⟩
      have hM_le_lower : (M : EReal) ≤ Sequence.lowerseq a a.m := by
        unfold Sequence.lowerseq
        apply Sequence.inf_ge_lower
        intro n hn
        have hn' : n ≥ a.m := by
          dsimp [Sequence.from, Sequence.mk'] at hn; omega
        have h_val : (a.from a.m) n = a n := by
          exact_mod_cast Sequence.from_eval a hn'
        have h_val_M : (a.from a.m) n ≥ (M : EReal) := by
          rw [h_val]
          exact_mod_cast hM n hn'
        exact h_val_M
      have h_lower_le_liminf : Sequence.lowerseq a a.m ≤ a.liminf :=
        le_sSup ⟨a.m, le_refl _, rfl⟩
      have hliminf_ge_M : (M : EReal) ≤ a.liminf :=
        le_trans hM_le_lower h_lower_le_liminf
      rw [hinf_bot] at hliminf_ge_M
      exact (not_le.mpr (EReal.bot_lt_coe M)) hliminf_ge_M
    · rw [if_neg hinf_top, if_neg hinf_bot]
      have hL : a.liminf = (a.liminf.toReal : ℝ) :=
        (EReal.coe_toReal hinf_top hinf_bot).symm
      exact Sequence.limit_point_of_liminf hL

lemma tail_bddAbove_imp_bddAbove (a : Sequence) (N : ℤ) (hN : N ≥ a.m) (htail : (a.from N).BddAbove) : a.BddAbove := by
  rcases htail with ⟨M, hM⟩
  have hm_tail : (a.from N).m = max a.m N := rfl
  by_cases hN_eq_am : N = a.m
  · subst hN_eq_am
    refine ⟨M, λ n hn => ?_⟩
    have hn' : n ≥ (a.from a.m).m := by
      dsimp [Sequence.from, Sequence.mk']; omega
    have h_val : (a.from a.m) n = a n := by
      exact_mod_cast Sequence.from_eval a hn
    calc
      a n = (a.from a.m) n := by symm; exact h_val
      _ ≤ M := hM n hn'
  · have h_lt : a.m < N := by
      apply lt_of_le_of_ne hN (Ne.symm hN_eq_am)
    set v := (Finset.Ico (a.m : ℤ) N).image (λ (i : ℤ) => a i) with hv_def
    have hv_nonempty : v.Nonempty := by
      refine ⟨a a.m, Finset.mem_image.mpr ⟨a.m,
        Finset.mem_Ico.mpr ⟨le_refl _, h_lt⟩, rfl⟩⟩
    set M0 := v.max' hv_nonempty with hM0_def
    use max M M0
    intro n hn
    by_cases hn_lt_N : n < N
    · have mem_val_set : a n ∈ v := by
        apply Finset.mem_image.mpr
        refine ⟨n, Finset.mem_Ico.mpr ⟨hn, hn_lt_N⟩, rfl⟩
      have hM0_ge : a n ≤ M0 := Finset.le_max' _ _ mem_val_set
      exact le_trans hM0_ge (le_max_right _ _)
    · have hn_ge_N : n ≥ N := by omega
      have hn' : n ≥ (a.from N).m := by
        dsimp [Sequence.from, Sequence.mk']; omega
      have h_val : (a.from N) n = a n := by
        exact_mod_cast Sequence.from_eval a hn_ge_N
      calc
        a n = (a.from N) n := by symm; exact h_val
        _ ≤ M := hM n hn'
        _ ≤ max M M0 := le_max_left _ _

theorem Sequence.extended_limit_point_le_limsup {a:Sequence} {L:EReal} (h:a.ExtendedLimitPoint L): L ≤ a.limsup := by
  unfold Sequence.ExtendedLimitPoint at h
  by_cases hL_top : L = ⊤
  · rw [hL_top] at h; simp at h
    have h_not_bdd : ¬ a.BddAbove := by
      simpa using h
    have h_limsup_top : a.limsup = ⊤ := by
      by_contra! hne
      have hlt : a.limsup < ⊤ := hne.lt_of_le le_top
      rcases EReal.lt_iff_exists_real_btwn.mp hlt with ⟨c, hc1, hc2⟩
      -- hc1 : a.limsup < (c : EReal), hc2 : (c : EReal) < ⊤
      have h_sInf_lt : sInf { x | ∃ N ≥ a.m, x = Sequence.upperseq a N } < (c : EReal) := by
        simpa [Sequence.limsup] using hc1
      rcases sInf_lt_iff.mp h_sInf_lt with ⟨x, hx, hx_lt⟩
      rcases hx with ⟨N, hN, hx_eq⟩
      rw [hx_eq] at hx_lt
      unfold Sequence.upperseq at hx_lt
      -- hx_lt : (a.from N).sup < (c : EReal)
      have h_tail_bdd : (a.from N).BddAbove := by
        refine ⟨c, λ n hn => ?_⟩
        have h_sup_ge : (a.from N) n ≤ (a.from N).sup := Sequence.le_sup hn
        have h_lt : (a.from N) n < (c : EReal) := lt_of_le_of_lt h_sup_ge hx_lt
        exact_mod_cast h_lt.le
      have ha_bdd : a.BddAbove := tail_bddAbove_imp_bddAbove a N hN h_tail_bdd
      exact h_not_bdd ha_bdd
    rw [hL_top, h_limsup_top]
  · by_cases hL_bot : L = ⊥
    · rw [hL_bot]; exact bot_le
    · rw [if_neg hL_top, if_neg hL_bot] at h
      have h_between := Sequence.limit_point_between_liminf_limsup h
      rcases h_between with ⟨_, h_c_le_limsup⟩
      have hL_eq : L = (L.toReal : EReal) := (EReal.coe_toReal hL_top hL_bot).symm
      rw [hL_eq]
      exact h_c_le_limsup

lemma tail_bddBelow_imp_bddBelow (a : Sequence) (N : ℤ) (hN : N ≥ a.m) (htail : (a.from N).BddBelow) : a.BddBelow := by
  rcases htail with ⟨c, hc⟩
  -- hc : ∀ n ≥ (a.from N).m, (a.from N) n ≥ c
  have hm_tail : (a.from N).m = max a.m N := rfl
  by_cases hN_eq_am : N = a.m
  · subst hN_eq_am
    refine ⟨c, λ n hn => ?_⟩
    have hn' : n ≥ (a.from a.m).m := by
      dsimp [Sequence.from, Sequence.mk']; omega
    have h_val : (a.from a.m) n = a n := by
      exact_mod_cast Sequence.from_eval a hn
    calc
      a n = (a.from a.m) n := by symm; exact h_val
      _ ≥ c := hc n hn'
  · have h_lt : a.m < N := by
      apply lt_of_le_of_ne hN (Ne.symm hN_eq_am)
    set v := (Finset.Ico (a.m : ℤ) N).image (λ (i : ℤ) => a i) with hv_def
    have hv_nonempty : v.Nonempty := by
      refine ⟨a a.m, Finset.mem_image.mpr ⟨a.m,
        Finset.mem_Ico.mpr ⟨le_refl _, h_lt⟩, rfl⟩⟩
    set M0 := v.min' hv_nonempty with hM0_def
    use min c M0
    intro n hn
    by_cases hn_lt_N : n < N
    · have mem_val_set : a n ∈ v := by
        apply Finset.mem_image.mpr
        refine ⟨n, Finset.mem_Ico.mpr ⟨hn, hn_lt_N⟩, rfl⟩
      have hM0_le : M0 ≤ a n := Finset.min'_le _ _ mem_val_set
      exact le_trans (min_le_right _ _) hM0_le
    · have hn_ge_N : n ≥ N := by omega
      have hn' : n ≥ (a.from N).m := by
        dsimp [Sequence.from, Sequence.mk']; omega
      have h_val : (a.from N) n = a n := by
        exact_mod_cast Sequence.from_eval a hn_ge_N
      have h_c_le_a_n : c ≤ a n := by
        calc
          c ≤ (a.from N) n := hc n hn'
          _ = a n := h_val
      exact le_trans (min_le_left _ _) h_c_le_a_n

theorem Sequence.extended_limit_point_ge_liminf {a:Sequence} {L:EReal} (h:a.ExtendedLimitPoint L): L ≥ a.liminf := by
  unfold Sequence.ExtendedLimitPoint at h
  by_cases hL_top : L = ⊤
  · rw [hL_top]; exact (le_top : a.liminf ≤ (⊤ : EReal))
  · by_cases hL_bot : L = ⊥
    · rw [hL_bot] at h; simp at h
      -- h : ∀ (x : ℝ), ∃ n ≥ a.m, a n < x   (equivalent to ¬ a.BddBelow)
      have ha_not_bdd : ¬ a.BddBelow := by
        simpa using h
      by_contra! hlt
      -- hlt : a.liminf > ⊥
      rcases EReal.lt_iff_exists_real_btwn.mp hlt with ⟨c, hc1, hc2⟩
      -- hc1 : ⊥ < (c : EReal), hc2 : (c : EReal) < a.liminf
      have h_lt_sup : (c : EReal) < sSup { x | ∃ N ≥ a.m, x = Sequence.lowerseq a N } := by
        simpa [Sequence.liminf] using hc2
      rcases lt_sSup_iff.mp h_lt_sup with ⟨x, hx, hx_lt⟩
      rcases hx with ⟨N, hN, hx_eq⟩
      rw [hx_eq] at hx_lt
      -- hx_lt : (c : EReal) < Sequence.lowerseq a N
      unfold Sequence.lowerseq at hx_lt
      -- hx_lt : (c : EReal) < (a.from N).inf
      have htail_bdd : (a.from N).BddBelow := by
        refine ⟨c, λ n hn => ?_⟩
        have h_inf_le : (a.from N).inf ≤ (a.from N) n := sInf_le ⟨n, hn, rfl⟩
        have h_c_le : (c : EReal) ≤ (a.from N) n := le_trans (le_of_lt hx_lt) h_inf_le
        exact_mod_cast h_c_le
      have ha_bdd : a.BddBelow := tail_bddBelow_imp_bddBelow a N hN htail_bdd
      exact ha_not_bdd ha_bdd
    · rw [if_neg hL_top, if_neg hL_bot] at h
      have h_between := Sequence.limit_point_between_liminf_limsup h
      rcases h_between with ⟨h_liminf_le_c, _⟩
      have hL_eq : L = (L.toReal : EReal) := (EReal.coe_toReal hL_top hL_bot).symm
      rw [hL_eq]
      exact h_liminf_le_c

/-- Exercise 6.4.9 -/
theorem Sequence.exists_three_limit_points : ∃ a:Sequence, ∀ L:EReal, a.ExtendedLimitPoint L ↔ L = ⊥ ∨ L = 0 ∨ L = ⊤ := by
  let a : Sequence := Sequence.mk' 0 (λ ⟨n, hn⟩ =>
    if n % 3 = 0 then (0 : ℝ)
    else if n % 3 = 1 then (n : ℝ)
    else -(n : ℝ))
  have ha_m : a.m = 0 := rfl
  have ha_val (n : ℤ) (hn : n ≥ 0) : a n = (if n % 3 = 0 then (0 : ℝ) else if n % 3 = 1 then (n : ℝ) else -(n : ℝ)) := by
    dsimp [a, Sequence.mk']; simp [hn]
  have ha_val_mod0 (n : ℤ) (hn : n % 3 = 0) (hn0 : n ≥ 0) : a n = 0 := by
    rw [ha_val n hn0, hn]; simp
  have ha_val_mod1 (n : ℤ) (hn : n % 3 = 1) (hn0 : n ≥ 0) : a n = (n : ℝ) := by
    rw [ha_val n hn0, hn]; simp
  have ha_val_mod2 (n : ℤ) (hn : n % 3 = 2) (hn0 : n ≥ 0) : a n = -(n : ℝ) := by
    rw [ha_val n hn0, hn]; simp
  have ha_limit_point_zero : a.LimitPoint (0 : ℝ) := by
    rw [Sequence.limit_point_def]
    intro ε hε N hN
    have hN0 : 0 ≤ N := le_trans (by omega) hN
    set n : ℤ := 3 * N with hn_def
    have hn_mod0 : n % 3 = 0 := by dsimp [n]; omega
    have ha_n : a n = 0 := ha_val_mod0 n hn_mod0 (by dsimp [n]; omega)
    refine ⟨n, by dsimp [n]; omega, ?_⟩
    simpa [ha_n] using hε.le
  have ha_not_BddAbove : ¬ a.BddAbove := by
    intro hbdd
    rcases hbdd with ⟨M, hM⟩
    let k : ℤ := max 0 (Int.floor M + 1)
    set n : ℤ := 3 * k + 1 with hn_def
    have hn_mod1 : n % 3 = 1 := by dsimp [n]; omega
    have hn_nonneg : n ≥ 0 := by dsimp [n, k]; omega
    have ha_n : a n = (n : ℝ) := ha_val_mod1 n hn_mod1 hn_nonneg
    have hn_ge_am : n ≥ a.m := by dsimp [a]; omega
    have ha_n_le_M : a n ≤ M := hM n hn_ge_am
    have hk_gt_M : (k : ℝ) > M := by
      have h_lt_floor_add_one : M < (Int.floor M : ℝ) + 1 := by exact mod_cast (Int.lt_floor_add_one M)
      have h_floor_add_one_le_k : (Int.floor M : ℝ) + 1 ≤ (k : ℝ) := by
        have : Int.floor M + 1 ≤ k := le_max_right _ _
        exact mod_cast this
      linarith
    have hk_nonneg : (k : ℝ) ≥ 0 := by
      have : (0 : ℤ) ≤ k := le_max_left _ _
      exact_mod_cast this
    have hn_gt_M : (n : ℝ) > M := by
      have hn_eq : (n : ℝ) = 3 * (k : ℝ) + 1 := by norm_num [hn_def]
      rw [hn_eq]
      by_cases hM_nonneg : M ≥ 0
      · nlinarith
      · have hM_neg : M < 0 := by linarith
        nlinarith
    have hk_nonneg : (k : ℝ) ≥ 0 := by
      have : (0 : ℤ) ≤ k := le_max_left _ _
      exact_mod_cast this
    rw [ha_n] at ha_n_le_M
    have hn_eq : (n : ℝ) = 3 * (k : ℝ) + 1 := by norm_num [hn_def]
    rw [hn_eq] at ha_n_le_M
    have : 3 * (k : ℝ) + 1 > M := by
      by_cases hM_nonneg : M ≥ 0
      · nlinarith
      · have hM_neg : M < 0 := by linarith
        nlinarith
    nlinarith
  have ha_not_BddBelow : ¬ a.BddBelow := by
    intro hbdd
    rcases hbdd with ⟨M, hM⟩
    let k : ℤ := max 0 (Int.floor (-M) + 1)
    set n : ℤ := 3 * k + 2 with hn_def
    have hn_mod2 : n % 3 = 2 := by dsimp [n]; omega
    have hn_nonneg : n ≥ 0 := by dsimp [n, k]; omega
    have ha_n : a n = -(n : ℝ) := ha_val_mod2 n hn_mod2 hn_nonneg
    have hn_ge_am : n ≥ a.m := by dsimp [a]; omega
    have ha_n_ge_M : a n ≥ M := hM n hn_ge_am
    have hk_gt_neg_M : (k : ℝ) > -M := by
      have h_lt_floor_add_one : -M < (Int.floor (-M) : ℝ) + 1 := by exact mod_cast (Int.lt_floor_add_one (-M))
      have h_floor_add_one_le_k : (Int.floor (-M) : ℝ) + 1 ≤ (k : ℝ) := by
        have : Int.floor (-M) + 1 ≤ k := le_max_right _ _
        exact mod_cast this
      linarith
    have hk_nonneg : (k : ℝ) ≥ 0 := by
      have : (0 : ℤ) ≤ k := le_max_left _ _
      exact_mod_cast this
    have hn_gt_neg_M : (n : ℝ) > -M := by
      have hn_eq : (n : ℝ) = 3 * (k : ℝ) + 2 := by norm_num [hn_def]
      rw [hn_eq]
      by_cases h_negM_nonneg : -M ≥ 0
      · nlinarith
      · have h_negM_neg : -M < 0 := by linarith
        nlinarith
    rw [ha_n] at ha_n_ge_M
    have hn_eq : (n : ℝ) = 3 * (k : ℝ) + 2 := by norm_num [hn_def]
    rw [hn_eq] at ha_n_ge_M
    have : 3 * (k : ℝ) + 2 > -M := by
      by_cases h_negM_nonneg : -M ≥ 0
      · nlinarith
      · have h_negM_neg : -M < 0 := by linarith
        nlinarith
    nlinarith
  have ha_not_LimitPoint_pos (r : ℝ) (hr_pos : r > 0) : ¬ a.LimitPoint r := by
    rw [Sequence.limit_point_def]
    push_neg
    set ε := r / 2 with hε_def
    have hε_pos : ε > 0 := by linarith
    let k : ℤ := max 0 (Int.floor r + 1)
    have hk_gt_r : (k : ℝ) > r := by
      have hr_lt_floor_add_one : r < (Int.floor r : ℝ) + 1 := by exact mod_cast (Int.lt_floor_add_one r)
      have h_floor_add_one_le_k : (Int.floor r : ℝ) + 1 ≤ (k : ℝ) := by
        have : Int.floor r + 1 ≤ k := le_max_right _ _
        exact mod_cast this
      linarith
    set N : ℤ := 3 * k with hN_def
    have hN_ge_am : N ≥ a.m := by
      dsimp [a, N, k]; omega
    refine ⟨ε, hε_pos, N, hN_ge_am, λ n hn => ?_⟩
    have hn_nonneg : n ≥ 0 := le_trans (by dsimp [N, k]; omega) hn
    have hcases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases hcases with (h0 | h1 | h2)
    · have ha_n : a n = 0 := ha_val_mod0 n h0 hn_nonneg
      rw [ha_n]
      have : |(0 : ℝ) - r| = r := by
        have : |(0 : ℝ) - r| = |r| := by simp
        rw [this, abs_of_pos hr_pos]
      rw [this]
      nlinarith
    · have ha_n : a n = (n : ℝ) := ha_val_mod1 n h1 hn_nonneg
      rw [ha_n]
      have hn_nonneg_real : (n : ℝ) ≥ 0 := by exact_mod_cast hn_nonneg
      have hn_gt_r : (n : ℝ) > r := by
        have hN_eq_3k : (N : ℝ) = 3 * (k : ℝ) := by norm_num [hN_def]
        have hn_ge_N_real : (n : ℝ) ≥ (N : ℝ) := by exact_mod_cast hn
        nlinarith [hk_gt_r, hn_ge_N_real, hN_eq_3k]
      have : |(n : ℝ) - r| = (n : ℝ) - r := abs_of_pos (sub_pos.mpr hn_gt_r)
      rw [this]
      have hn_ge_N_real : (n : ℝ) ≥ (N : ℝ) := by exact_mod_cast hn
      have hN_eq_3k : (N : ℝ) = 3 * (k : ℝ) := by norm_num [hN_def]
      nlinarith [hε_def, hk_gt_r, hn_ge_N_real, hN_eq_3k]
    · have ha_n : a n = -(n : ℝ) := ha_val_mod2 n h2 hn_nonneg
      rw [ha_n]
      have hn_nonneg_real : (n : ℝ) ≥ 0 := by exact_mod_cast hn_nonneg
      have hn_ge_N_real : (n : ℝ) ≥ (N : ℝ) := by exact_mod_cast hn
      have hN_eq_3k : (N : ℝ) = 3 * (k : ℝ) := by norm_num [hN_def]
      have : |-(n : ℝ) - r| = (n : ℝ) + r := by
        have h_neg : -(n : ℝ) - r < 0 := by nlinarith
        rw [abs_of_neg h_neg]
        ring
      rw [this]
      nlinarith [hε_def, hk_gt_r, hn_ge_N_real, hN_eq_3k]
  have ha_not_LimitPoint_neg (r : ℝ) (hr_neg : r < 0) : ¬ a.LimitPoint r := by
    rw [Sequence.limit_point_def]
    push_neg
    set ε := (-r) / 2 with hε_def
    have hε_pos : ε > 0 := by linarith
    let k : ℤ := max 0 (Int.floor (-r) + 1)
    have hk_gt_neg_r : (k : ℝ) > -r := by
      have h_neg_r_lt_floor_add_one : -r < (Int.floor (-r) : ℝ) + 1 := by exact mod_cast (Int.lt_floor_add_one (-r))
      have h_floor_add_one_le_k : (Int.floor (-r) : ℝ) + 1 ≤ (k : ℝ) := by
        have : Int.floor (-r) + 1 ≤ k := le_max_right _ _
        exact mod_cast this
      linarith
    set N : ℤ := 3 * k with hN_def
    have hN_ge_am : N ≥ a.m := by
      dsimp [a, N, k]; omega
    refine ⟨ε, hε_pos, N, hN_ge_am, λ n hn => ?_⟩
    have hn_nonneg : n ≥ 0 := le_trans (by dsimp [N, k]; omega) hn
    have hcases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases hcases with (h0 | h1 | h2)
    · have ha_n : a n = 0 := ha_val_mod0 n h0 hn_nonneg
      rw [ha_n]
      have : |(0 : ℝ) - r| = -r := by
        have : |(0 : ℝ) - r| = |r| := by simp
        rw [this, abs_of_neg hr_neg]
      rw [this]
      nlinarith
    · have ha_n : a n = (n : ℝ) := ha_val_mod1 n h1 hn_nonneg
      rw [ha_n]
      have hn_nonneg_real : (n : ℝ) ≥ 0 := by exact_mod_cast hn_nonneg
      have hn_gt_neg_r : (n : ℝ) > -r := by
        have hN_eq_3k : (N : ℝ) = 3 * (k : ℝ) := by norm_num [hN_def]
        have hn_ge_N_real : (n : ℝ) ≥ (N : ℝ) := by exact_mod_cast hn
        nlinarith [hk_gt_neg_r, hn_ge_N_real, hN_eq_3k]
      have : |(n : ℝ) - r| = (n : ℝ) - r :=
        abs_of_pos (sub_pos.mpr (by nlinarith))
      rw [this]
      have hn_ge_N_real : (n : ℝ) ≥ (N : ℝ) := by exact_mod_cast hn
      have hN_eq_3k : (N : ℝ) = 3 * (k : ℝ) := by norm_num [hN_def]
      nlinarith [hε_def, hk_gt_neg_r, hn_ge_N_real, hN_eq_3k]
    · have ha_n : a n = -(n : ℝ) := ha_val_mod2 n h2 hn_nonneg
      rw [ha_n]
      have hn_nonneg_real : (n : ℝ) ≥ 0 := by exact_mod_cast hn_nonneg
      have hn_ge_N_real : (n : ℝ) ≥ (N : ℝ) := by exact_mod_cast hn
      have hN_eq_3k : (N : ℝ) = 3 * (k : ℝ) := by norm_num [hN_def]
      have hn_plus_r_pos : (n : ℝ) + r > 0 := by
        nlinarith [hk_gt_neg_r, hn_ge_N_real, hN_eq_3k]
      have : |-(n : ℝ) - r| = (n : ℝ) + r := by
        have h_neg : -(n : ℝ) - r < 0 := by nlinarith
        rw [abs_of_neg h_neg]
        ring
      rw [this]
      nlinarith [hε_def, hk_gt_neg_r, hn_ge_N_real, hN_eq_3k]
  refine ⟨a, λ L => ?_⟩
  constructor
  · intro h_ext
    unfold Sequence.ExtendedLimitPoint at h_ext
    split_ifs at h_ext with hL_top hL_bot
    · exact Or.inr (Or.inr hL_top)
    · exact Or.inl hL_bot
    · have hL_real : L = (L.toReal : EReal) := (EReal.coe_toReal hL_top hL_bot).symm
      have hr_eq_zero : L.toReal = (0 : ℝ) := by
        by_contra! hne
        have h_not_limit : ¬ a.LimitPoint L.toReal := by
          by_cases hpos : L.toReal > 0
          · exact ha_not_LimitPoint_pos L.toReal hpos
          · by_cases hneg : L.toReal < 0
            · exact ha_not_LimitPoint_neg L.toReal hneg
            · exfalso; exact hne (le_antisymm (by linarith) (by linarith))
        exact h_not_limit h_ext
      rw [hL_real, hr_eq_zero]
      exact Or.inr (Or.inl rfl)
  · intro h
    rcases h with (hL | hL | hL)
    · rw [hL]
      unfold Sequence.ExtendedLimitPoint
      simp
      simpa using ha_not_BddBelow
    · rw [hL]
      unfold Sequence.ExtendedLimitPoint
      simp
      simpa using ha_limit_point_zero
    · rw [hL]
      unfold Sequence.ExtendedLimitPoint
      simp
      simpa using ha_not_BddAbove

/-- Exercise 6.4.10 -/
theorem Sequence.limit_points_of_limit_points {a b:Sequence} {c:ℝ} (hab: ∀ n ≥ b.m, a.LimitPoint (b n)) (hbc: b.LimitPoint c) : a.LimitPoint c := by
  rw [Sequence.limit_point_def]
  intro ε hε N hN
  have hε2 : ε / 2 > 0 := by linarith
  rcases (Sequence.limit_point_def b c).mp hbc (ε / 2) hε2 (max b.m N) (by omega) with ⟨K, hK, hK_close⟩
  have hK_ge_bm : K ≥ b.m := le_trans (le_max_left _ _) hK
  have hK_ge_N : K ≥ N := le_trans (le_max_right _ _) hK
  have ha_limit_bK : a.LimitPoint (b K) := hab K hK_ge_bm
  rcases (Sequence.limit_point_def a (b K)).mp ha_limit_bK (ε / 2) hε2 (max a.m N) (by omega) with ⟨n, hn, hn_close⟩
  have hn_ge_N : n ≥ N := le_trans (le_max_right _ _) hn
  refine ⟨n, hn_ge_N, ?_⟩
  have h_triangle (x y : ℝ) : |x + y| ≤ |x| + |y| := by
    have h_sq : (|x + y|)^2 = (x + y)^2 := sq_abs _
    have h_sq_x : (|x|)^2 = x^2 := sq_abs _
    have h_sq_y : (|y|)^2 = y^2 := sq_abs _
    have h_nonneg : 0 ≤ |x + y| := abs_nonneg _
    have h_nonneg_sum : 0 ≤ |x| + |y| := by positivity
    have h_xy : x * y ≤ |x| * |y| := by
      have h_abs_mul : |x * y| = |x| * |y| := abs_mul _ _
      have h_le_abs : x * y ≤ |x * y| := by exact le_abs_self (x * y)
      linarith
    have h_ineq_sq : (x + y)^2 ≤ (|x| + |y|)^2 := by
      nlinarith
    have h_sq_ineq : (|x + y|)^2 ≤ (|x| + |y|)^2 := by
      rw [h_sq]
      exact h_ineq_sq
    nlinarith
  calc
    |a n - c| = |(a n - b K) + (b K - c)| := by rw [sub_add_sub_cancel]
    _ ≤ |a n - b K| + |b K - c| := by
      apply h_triangle (a n - b K) (b K - c)
    _ ≤ ε / 2 + ε / 2 := by nlinarith
    _ = ε := by norm_num


end Chapter6
