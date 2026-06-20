import Mathlib.Tactic
import Analysis.Section_6_4

/-!
# Analysis I, Section 6.5: Some standard limits

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Some standard limits, including limits of sequences of the form 1/n^α, x^n, and x^(1/n).

-/

namespace Chapter6

theorem Sequence.lim_of_const (c:ℝ) :  ((fun (_:ℕ) ↦ c):Sequence).TendsTo c := by
  rw [Sequence.tendsTo_iff ((fun (_:ℕ) ↦ c):Sequence) c]
  intro ε hε
  use (0 : ℤ)
  intro n hn
  have hn0 : (0 : ℤ) ≤ n := hn
  simp [hn0, hε.le]

instance Sequence.inst_pow: Pow Sequence ℕ where
  pow a k := {
    m := a.m
    seq n := if n ≥ a.m then a n ^ k else 0
    vanish := by grind
  }

@[simp]
lemma Sequence.pow_eval {a:Sequence} {k: ℕ} {n: ℤ} (hn : n ≥ a.m): (a ^ k) n = a n ^ k := by
  rw [HPow.hPow, instHPow, Pow.pow, inst_pow]
  grind

@[simp]
lemma Sequence.pow_one (a:Sequence) : a^1 = a := by
  ext n; rfl; simp only [HPow.hPow, Pow.pow]; split_ifs with h; simp; simp [a.vanish n (by grind)]

lemma Sequence.pow_succ (a:Sequence) (k:ℕ): a^(k+1) = a^k * a := by
  ext x
  . symm; exact Int.min_self a.m
  . simp only [mul_eval]
    by_cases h: x ≥ a.m
    · simp [pow_eval h]
      rfl
    · rw [a.vanish x (by grind), mul_zero]
      exact vanish _ _ (by simp at h; exact h)

/-- Corollary 6.5.1 -/
theorem Sequence.lim_of_power_decay {k:ℕ} :
    ((fun (n:ℕ) ↦ 1/((n:ℝ)+1)^(1/(k+1:ℝ))):Sequence).TendsTo 0 := by
  -- This proof is written to follow the structure of the original text.
  set a := ((fun (n:ℕ) ↦ 1/((n:ℝ)+1)^(1/(k+1:ℝ))):Sequence)
  have ha : a.BddBelow := by use 0; intro n _; simp [a]; positivity
  have ha' : a.IsAntitone := by
    intro n hn; observe hn' : 0 ≤ n+1; simp [a,hn,hn']
    rw [inv_le_inv₀, Real.rpow_le_rpow_iff] <;> try positivity
    simp
  apply convergent_of_antitone ha at ha'
  have hpow (n:ℕ): (a^(n+1)).Convergent ∧ lim (a^(n+1)) = (lim a)^(n+1) := by
    induction' n with n ih
    . simp [ha', -dite_pow]
    rw [pow_succ]; convert lim_mul ih.1 ha' using 1; rw [ih.2]; grind
  have hlim : (lim a)^(k+1) = 0 := by
    rw [←(hpow k).2]; convert lim_harmonic.2; ext; rfl
    simp only [HPow.hPow, Pow.pow, a]; split_ifs with h
    · simp
      rw [←Real.rpow_natCast,←Real.rpow_mul (by positivity)]
      convert Real.rpow_one _; field_simp; push_cast; ring
    · simp
  simp [lim_eq, ha', eq_zero_of_pow_eq_zero hlim]

/-- Lemma 6.5.2 / Exercise 6.5.2 -/
theorem Sequence.lim_of_geometric {x:ℝ} (hx: |x| < 1) : ((fun (n:ℕ) ↦ x^n):Sequence).TendsTo 0 := by
  rw [Sequence.tendsTo_iff ((fun (n:ℕ) ↦ x^n):Sequence) 0]
  intro ε hε
  rcases em (x = 0) with (hx0 | hx0)
  · subst x; use 1; intro n hn
    have hn_nonneg : (0 : ℤ) ≤ n := by omega
    have hn_pos : n.toNat ≠ 0 := by omega
    simp [hn_nonneg, zero_pow hn_pos, hε.le]
  · have hx_abs_pos : 0 < |x| := abs_pos.mpr hx0
    have h_one_lt : 1 < 1 / |x| := one_lt_one_div hx_abs_pos hx
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / ε) h_one_lt
    use (k : ℤ)
    intro n hn
    have hn_nonneg : (0 : ℤ) ≤ n := by omega
    have ha_n_val : ((fun (n:ℕ) ↦ x^n):Sequence) n = x ^ (n.toNat : ℕ) := by
      simp [hn_nonneg]
    rw [ha_n_val, sub_zero, abs_pow]
    have hx_abs_nonneg : 0 ≤ |x| := abs_nonneg x
    have hx_abs_le_one : |x| ≤ 1 := le_of_lt hx
    have hk_le_toNat : (k : ℕ) ≤ n.toNat := by
      have hn_k : n ≥ (k : ℤ) := hn
      omega
    have h_pow_le : |x| ^ (n.toNat : ℕ) ≤ |x| ^ k :=
      pow_le_pow_of_le_one hx_abs_nonneg hx_abs_le_one hk_le_toNat
    have h_lt : |x| ^ k < ε := by
      have hk' : 1 / ε < 1 / |x| ^ k :=
        calc
          1 / ε < (1 / |x|) ^ k := hk
          _ = 1 / |x| ^ k := by simp
      have hpos_ε : 0 < ε := hε
      have hpos_pow : 0 < |x| ^ k := pow_pos hx_abs_pos k
      exact (one_div_lt_one_div (by positivity : 0 < ε) (by positivity : 0 < |x| ^ k)).mp hk'
    exact le_trans h_pow_le (le_of_lt h_lt)

/-- Lemma 6.5.2 / Exercise 6.5.2 -/
theorem Sequence.lim_of_geometric' {x:ℝ} (hx: x = 1) : ((fun (n:ℕ) ↦ x^n):Sequence).TendsTo 1 := by
  subst x; simpa using Sequence.lim_of_const (1 : ℝ)

/-- Lemma 6.5.2 / Exercise 6.5.2 -/
theorem Sequence.lim_of_geometric'' {x:ℝ} (hx: x = -1 ∨ |x| > 1) :
    ((fun (n:ℕ) ↦ x^n):Sequence).Divergent := by
  rcases hx with (hx | hx)
  · subst hx
    have h_not_cauchy : ¬ ((fun (n:ℕ) ↦ ((-1 : ℝ) ^ n)):Sequence).IsCauchy := by
      intro h_cauchy
      have h_one : (1 : ℝ).EventuallySteady ((fun (n:ℕ) ↦ ((-1 : ℝ) ^ n)):Sequence) :=
        h_cauchy 1 (by norm_num)
      rcases h_one with ⟨N, hN, h_steady⟩
      set a := ((fun (n:ℕ) ↦ ((-1 : ℝ) ^ n)):Sequence) with ha
      have hm_val : (a.from N).m = N := by
        dsimp [Sequence.from, Sequence.mk', a]
        exact max_eq_right hN
      have hN_nonneg : (0 : ℤ) ≤ N := hN
      have hNp1_nonneg : (0 : ℤ) ≤ N + 1 := by omega
      have ha_N_val : a N = (-1 : ℝ) ^ (N.toNat : ℕ) := by simp [hN_nonneg, ha]
      have ha_Np1_val : a (N + 1) = (-1 : ℝ) ^ ((N + 1).toNat : ℕ) := by simp [hNp1_nonneg, ha]
      have h_toNat : ((N + 1 : ℤ).toNat : ℕ) = (N.toNat : ℕ) + 1 := by omega
      have hN_ge_m : N ≥ (a.from N).m := by rw [hm_val]
      have hNp1_ge_m : N+1 ≥ (a.from N).m := by rw [hm_val]; omega
      have h_close : (1 : ℝ).Close ((a.from N) N) ((a.from N) (N+1)) :=
        h_steady N hN_ge_m (N+1) hNp1_ge_m
      rw [Real.Close, Real.dist_eq, Sequence.from_eval _ (le_refl N),
        Sequence.from_eval _ (show N+1 ≥ N from by omega), ha_N_val, ha_Np1_val, h_toNat] at h_close
      have h_sq : (-1 : ℝ) ^ (((N.toNat : ℕ) : ℕ) + 1) = -((-1 : ℝ) ^ ((N.toNat : ℕ) : ℕ)) := by
        calc
          (-1 : ℝ) ^ (((N.toNat : ℕ) : ℕ) + 1) = ((-1 : ℝ) ^ ((N.toNat : ℕ) : ℕ)) * (-1 : ℝ) :=
            _root_.pow_succ (-1 : ℝ) (N.toNat : ℕ)
          _ = -((-1 : ℝ) ^ ((N.toNat : ℕ) : ℕ)) := by simp
      have h_value : |(-1 : ℝ) ^ (N.toNat : ℕ) - (-1 : ℝ) ^ ((N.toNat : ℕ) + 1)| = 2 := by
        calc
          |(-1 : ℝ) ^ (N.toNat : ℕ) - (-1 : ℝ) ^ ((N.toNat : ℕ) + 1)|
              = |(-1 : ℝ) ^ (N.toNat : ℕ) - (-((-1 : ℝ) ^ (N.toNat : ℕ)))| := by rw [h_sq]
          _ = |2 * (-1 : ℝ) ^ (N.toNat : ℕ)| := by ring_nf
          _ = |(2 : ℝ)| * |(-1 : ℝ) ^ (N.toNat : ℕ)| := by rw [abs_mul]
          _ = 2 * |(-1 : ℝ) ^ (N.toNat : ℕ)| := by norm_num
          _ = 2 := by
            have : |(-1 : ℝ) ^ (N.toNat : ℕ)| = 1 := by
              simp [abs_pow]
            rw [this]; norm_num
      rw [h_value] at h_close
      norm_num at h_close
    have h_not_conv : ((fun (n:ℕ) ↦ ((-1 : ℝ) ^ n)):Sequence).Divergent :=
      mt ((Sequence.Cauchy_iff_convergent ((fun (n:ℕ) ↦ ((-1 : ℝ) ^ n)):Sequence)).mpr) h_not_cauchy
    exact h_not_conv
  · have hx_gt_one : (1 : ℝ) < |x| := hx
    have h_not_conv : ¬ ((fun (n:ℕ) ↦ x^n):Sequence).Convergent := by
      intro h_conv
      have h_bounded := Sequence.bounded_of_convergent h_conv
      rcases h_bounded with ⟨M, hM_nonneg, hM⟩
      have hM_nat : ∀ n : ℕ, |x ^ n| ≤ M := by
        intro n
        have h := hM (n : ℤ)
        simpa using h
      have hM_pow : ∀ n : ℕ, |x| ^ n ≤ M := by
        intro n
        simpa [abs_pow] using hM_nat n
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M hx_gt_one
      linarith [hM_pow n, hn]
    exact h_not_conv

/-- Lemma 6.5.3 / Exercise 6.5.3 -/
theorem Sequence.lim_of_roots {x:ℝ} (hx: x > 0) :
    ((fun (n:ℕ) ↦ x^(1/(n+1:ℝ))):Sequence).TendsTo 1 := by
  have h_ge_one (y : ℝ) (hy_pos : y > 0) (hy_ge_one : y ≥ 1) :
      ((fun (n : ℕ) ↦ y ^ (1 / (n + 1 : ℝ))) : Sequence).TendsTo 1 := by
    by_cases hy_eq_one : y = 1
    · subst y; simpa using Sequence.lim_of_const (1 : ℝ)
    · have hy_gt_one : 1 < y :=
        lt_of_le_of_ne hy_ge_one (Ne.symm hy_eq_one)
      rw [Sequence.tendsTo_iff]
      intro ε hε
      have h_one_lt : 1 < 1 + ε := by linarith
      obtain ⟨k : ℕ, hk⟩ := pow_unbounded_of_one_lt y h_one_lt
      use (k : ℤ)
      intro n hn
      have hn_nonneg : (0 : ℤ) ≤ n := by omega
      have h_val : ((fun (n : ℕ) ↦ y ^ (1 / (n + 1 : ℝ))) : Sequence) n = y ^ ((1 : ℝ) / ((n.toNat : ℝ) + 1)) := by
        simp [hn_nonneg]
      rw [h_val]
      have h_sq_ge_one : 1 ≤ y ^ ((1 : ℝ) / ((n.toNat : ℝ) + 1)) :=
        Real.one_le_rpow hy_ge_one (by positivity : 0 ≤ (1 : ℝ) / ((n.toNat : ℝ) + 1))
      have h_sub_nonneg : 0 ≤ y ^ ((1 : ℝ) / ((n.toNat : ℝ) + 1)) - 1 := by linarith
      rw [abs_of_nonneg h_sub_nonneg]
      have h_k_le_toNat : (k : ℕ) ≤ n.toNat := by
        have hn_k : (k : ℤ) ≤ n := hn
        omega
      have h_pow_le : (1 + ε) ^ (k : ℕ) ≤ (1 + ε) ^ (n.toNat + 1 : ℕ) :=
        pow_le_pow_right₀ (by linarith) (by omega)
      have h_y_lt_pow : y < (1 + ε) ^ (n.toNat + 1 : ℕ) := by
        calc
          y < (1 + ε) ^ (k : ℕ) := hk
          _ ≤ (1 + ε) ^ (n.toNat + 1 : ℕ) := h_pow_le
      have h_y_lt_rpow : y ≤ (1 + ε) ^ ((n.toNat : ℝ) + 1) := by
        calc
          y ≤ (1 + ε) ^ (n.toNat + 1 : ℕ) := le_of_lt h_y_lt_pow
          _ = (1 + ε) ^ ((n.toNat + 1 : ℕ) : ℝ) := by
            simpa using (Real.rpow_natCast (1 + ε) (n.toNat + 1)).symm
          _ = (1 + ε) ^ ((n.toNat : ℝ) + 1) := by simp
      have h_rpow_ineq : y ^ ((1 : ℝ) / ((n.toNat : ℝ) + 1)) ≤ ((1 + ε) ^ ((n.toNat : ℝ) + 1)) ^ ((1 : ℝ) / ((n.toNat : ℝ) + 1)) :=
        Real.rpow_le_rpow (by positivity) h_y_lt_rpow (by positivity)
      have h_rpow_mul_simp : ((1 + ε) ^ ((n.toNat : ℝ) + 1)) ^ ((1 : ℝ) / ((n.toNat : ℝ) + 1)) = 1 + ε := by
        calc
          ((1 + ε) ^ ((n.toNat : ℝ) + 1)) ^ ((1 : ℝ) / ((n.toNat : ℝ) + 1))
              = (1 + ε) ^ (((n.toNat : ℝ) + 1) * ((1 : ℝ) / ((n.toNat : ℝ) + 1))) := by
            rw [Real.rpow_mul (by positivity : 0 ≤ 1 + ε) ((n.toNat : ℝ) + 1) ((1 : ℝ) / ((n.toNat : ℝ) + 1))]
          _ = (1 + ε) ^ (1 : ℝ) := by
            field_simp [show (n.toNat : ℝ) + 1 ≠ 0 from by positivity]
          _ = 1 + ε := by simp
      have h_final_ineq : y ^ ((1 : ℝ) / ((n.toNat : ℝ) + 1)) - 1 ≤ ε := by
        linarith
      exact h_final_ineq
  by_cases hx_ge_one : x ≥ 1
  · exact h_ge_one x hx hx_ge_one
  · have hx_lt_one : x < 1 := by linarith
    have hy_gt_one : 1 / x > 1 := one_lt_one_div hx hx_lt_one
    have hy_pos : 0 < 1 / x := div_pos (by norm_num) hx
    have hy_ge_one : 1 / x ≥ 1 := le_of_lt hy_gt_one
    have h_tends_y : ((fun (n : ℕ) ↦ (1 / x) ^ (1 / (n + 1 : ℝ))) : Sequence).TendsTo 1 :=
      h_ge_one (1 / x) hy_pos hy_ge_one
    have h_tends_inv : (((fun (n : ℕ) ↦ (1 / x) ^ (1 / (n + 1 : ℝ))) : Sequence)⁻¹).TendsTo (1⁻¹) :=
      Sequence.tendsTo_inv h_tends_y (by norm_num : (1 : ℝ) ≠ 0)
    have h_inv_rpow (t : ℝ) : ((x⁻¹) ^ t)⁻¹ = x ^ t := by
      calc
        ((x⁻¹) ^ t)⁻¹ = ((x ^ t)⁻¹)⁻¹ := by rw [Real.inv_rpow (by positivity : 0 ≤ x) t]
        _ = x ^ t := by simp
    have h_seq_eq : ((fun (n : ℕ) ↦ (1 / x) ^ (1 / (n + 1 : ℝ))) : Sequence)⁻¹ = (fun (n : ℕ) ↦ x ^ (1 / (n + 1 : ℝ))) := by
      apply Sequence.ext
      · rfl
      · ext n
        by_cases h : n ≥ (0 : ℤ)
        · simp [Sequence.inv_eval, h]
          rw [h_inv_rpow ((↑n.toNat + 1)⁻¹)]
        · simp [Sequence.inv_eval, h]
    rw [h_seq_eq, inv_one] at h_tends_inv
    exact h_tends_inv

/-- Exercise 6.5.1 -/
theorem Sequence.lim_of_rat_power_decay {q:ℚ} (hq: q > 0) :
    (fun (n:ℕ) ↦ 1/((n+1:ℝ)^(q:ℝ)):Sequence).TendsTo 0 := by
  rw [Sequence.tendsTo_iff]
  intro ε hε
  have hq_pos_real : 0 < (q : ℝ) := by exact_mod_cast hq
  have h_eps_inv_pos : 0 < 1/ε := by positivity
  set M := (1/ε) ^ ((1 : ℝ) / (q : ℝ)) with hM_def
  have hM_pos : 0 < M := Real.rpow_pos_of_pos (by positivity) _
  have hM_pow_eq : M ^ (q : ℝ) = 1/ε := by
    dsimp [M]
    calc
      ((1/ε) ^ ((1 : ℝ) / (q : ℝ))) ^ (q : ℝ) = (1/ε) ^ (((1 : ℝ) / (q : ℝ)) * (q : ℝ)) := by
        rw [Real.rpow_mul (by positivity : 0 ≤ 1/ε) ((1 : ℝ) / (q : ℝ)) (q : ℝ)]
      _ = (1/ε) ^ (1 : ℝ) := by
        field_simp [show (q : ℝ) ≠ 0 from by exact_mod_cast hq.ne.symm]
      _ = 1/ε := by simp
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt M
  use (N : ℤ)
  intro n hn
  have hn_nonneg : (0 : ℤ) ≤ n := by omega
  have h_val : (fun (n : ℕ) ↦ 1 / ((n + 1 : ℝ) ^ (q : ℝ)) : Sequence) n = 1 / (((n.toNat : ℝ) + 1) ^ (q : ℝ)) := by
    simp [hn_nonneg]
  rw [h_val, sub_zero]
  have h_pos_denom : 0 < ((n.toNat : ℝ) + 1) ^ (q : ℝ) := by positivity
  have h_abs_eq : |1 / (((n.toNat : ℝ) + 1) ^ (q : ℝ))| = 1 / (((n.toNat : ℝ) + 1) ^ (q : ℝ)) := by
    rw [abs_of_pos (div_pos (by norm_num) h_pos_denom)]
  rw [h_abs_eq]
  have h_N_le_n_nat : (N : ℕ) ≤ n.toNat := by omega
  have h_N_le_n_real : (N : ℝ) ≤ (n.toNat : ℝ) := by exact_mod_cast h_N_le_n_nat
  have h_n_plus_one_gt_M : M < (n.toNat : ℝ) + 1 := by
    calc
      M < (N : ℝ) := hN
      _ ≤ (n.toNat : ℝ) := h_N_le_n_real
      _ < (n.toNat : ℝ) + 1 := by nlinarith
  have h_pow_gt_eps_inv : (1/ε) < ((n.toNat : ℝ) + 1) ^ (q : ℝ) := by
    calc
      (1/ε) = M ^ (q : ℝ) := by rw [hM_pow_eq]
      _ < ((n.toNat : ℝ) + 1) ^ (q : ℝ) :=
        Real.rpow_lt_rpow (by positivity) h_n_plus_one_gt_M hq_pos_real
  have h_final_ineq : 1 / (((n.toNat : ℝ) + 1) ^ (q : ℝ)) ≤ ε := by
    have h_lt : 1 / (((n.toNat : ℝ) + 1) ^ (q : ℝ)) < ε := by
      calc
        1 / (((n.toNat : ℝ) + 1) ^ (q : ℝ)) < 1 / (1/ε) :=
          (one_div_lt_one_div h_pos_denom (by positivity : 0 < 1/ε)).mpr (by
            simpa using h_pow_gt_eps_inv)
        _ = ε := by norm_num
    exact le_of_lt h_lt
  exact h_final_ineq

/-- Exercise 6.5.1 -/
theorem Sequence.lim_of_rat_power_growth {q:ℚ} (hq: q > 0) :
    (fun (n:ℕ) ↦ ((n+1:ℝ)^(q:ℝ)):Sequence).Divergent := by
  intro h_conv
  have h_bounded := Sequence.bounded_of_convergent h_conv
  rcases h_bounded with ⟨M, hM_nonneg, hM⟩
  have hq_pos_real : 0 < (q : ℝ) := by exact_mod_cast hq
  have h_bound : ∀ n : ℕ, ((n : ℝ) + 1) ^ (q : ℝ) ≤ M := by
    intro n
    have hM_n := hM (n : ℤ)
    have h_val : ((fun (n : ℕ) ↦ ((n + 1 : ℝ) ^ (q : ℝ))) : Sequence) (n : ℤ) = ((n : ℝ) + 1) ^ (q : ℝ) := by
      simp
    rw [h_val] at hM_n
    have h_pos : 0 < ((n : ℝ) + 1) ^ (q : ℝ) := by positivity
    have h_abs : |((n : ℝ) + 1) ^ (q : ℝ)| = ((n : ℝ) + 1) ^ (q : ℝ) := abs_of_pos h_pos
    rw [h_abs] at hM_n
    exact hM_n
  by_cases hM_zero : M = 0
  · subst hM_zero
    have h_pos_one : 0 < ((1 : ℝ) ^ (q : ℝ)) := by positivity
    have h_bound_one : ((1 : ℝ) ^ (q : ℝ)) ≤ 0 := by
      simpa [zero_add] using h_bound 0
    linarith
  · have hM_pos' : M > 0 := lt_of_le_of_ne hM_nonneg (Ne.symm hM_zero)
    set t := M ^ (1 / (q : ℝ)) with ht_def
    have ht_pos : 0 < t := Real.rpow_pos_of_pos hM_pos' _
    have h_t_pow_eq : t ^ (q : ℝ) = M := by
      calc
        t ^ (q : ℝ) = (M ^ (1 / (q : ℝ))) ^ (q : ℝ) := rfl
        _ = M ^ ((1 / (q : ℝ)) * (q : ℝ)) := by
          rw [Real.rpow_mul (by positivity : 0 ≤ M) (1 / (q : ℝ)) (q : ℝ)]
        _ = M ^ (1 : ℝ) := by
          field_simp [show (q : ℝ) ≠ 0 from by exact_mod_cast hq.ne.symm]
        _ = M := by simp
    obtain ⟨N : ℕ, hN⟩ := exists_nat_gt t
    have h_N_plus_one_gt_t : t < (N : ℝ) + 1 := by
      have hN' : t < (N : ℝ) := hN
      nlinarith
    have h_pow_gt_M : M < ((N : ℝ) + 1) ^ (q : ℝ) := by
      calc
        M = t ^ (q : ℝ) := by rw [h_t_pow_eq]
        _ < ((N : ℝ) + 1) ^ (q : ℝ) :=
          Real.rpow_lt_rpow (by positivity) h_N_plus_one_gt_t hq_pos_real
    have h_bound_N : ((N : ℝ) + 1) ^ (q : ℝ) ≤ M := h_bound N
    linarith

end Chapter6
