import Mathlib.Tactic
import Analysis.Appendix_B_1

/-!
# Analysis I, Appendix B.2: The decimal representation of real numbers

An implementation of the decimal representation of Mathlib's real numbers {lean}`ℝ`.

This is separate from the way decimal numerals are already represented in Mathlib.  We also represent the integer part of the natural numbers just by {lean}`ℕ`, avoiding using the decimal representation from the
previous section, although we still retain the {name}`AppendixB.Digit` class.
-/

namespace AppendixB

structure NNRealDecimal where
  intPart : ℕ
  fracPart : ℕ → Digit

open NNReal NNRealDecimal

@[coe]
noncomputable def NNRealDecimal.toNNReal (d:NNRealDecimal) : NNReal :=
  d.intPart + ∑' i, (d.fracPart i) * (10:NNReal) ^ (-i-1:ℝ)

noncomputable instance NNRealDecimal.instCoeNNReal : Coe NNRealDecimal NNReal where
  coe := toNNReal

/-- Exercise B.2.1 -/
theorem NNRealDecimal.toNNReal_conv (d:NNRealDecimal) :
  Summable fun i ↦ (d.fracPart i) * (10:NNReal) ^ (-i-1:ℝ) := by
  apply NNReal.summable_of_le (fun i ↦ ?_) ((NNReal.summable_geometric (show (10:NNReal)⁻¹ < 1 from by norm_num)).mul_left 9)
  have hd : (↑↑(d.fracPart i) : NNReal) ≤ 9 := by
    have := (d.fracPart i).isLt
    exact_mod_cast Nat.lt_succ_iff.mp this
  have hrpow : (10:NNReal) ^ ((-↑i - 1 : ℝ)) ≤ 10⁻¹ ^ i := by
    rw [show (-↑i - 1 : ℝ) = -(↑i + 1) from by ring, rpow_neg]
    rw [← rpow_natCast (10⁻¹ : NNReal) i, inv_rpow]
    gcongr
    · norm_num
    · linarith [Nat.cast_nonneg (α := ℝ) i]
  exact mul_le_mul' hd hrpow

theorem NNRealDecimal.surj (x:NNReal) : ∃ d:NNRealDecimal, x = d := by
  -- This proof is written to follow the structure of the original text.
  by_cases h : x = 0
  . use mk 0 fun _ ↦ 0; simp [h, toNNReal]
  let s : ℕ → ℕ := fun n ↦ ⌊ x * 10^n ⌋₊
  have hs (n:ℕ) : s n ≤ x * 10^n := Nat.floor_le (by positivity)
  have hs' (n:ℕ) : x * 10^n < s n + 1 := Nat.lt_floor_add_one _
  have hdigit (n:ℕ) : ∃ a:Digit, s (n+1) = 10 * s n + (a:ℕ) := by
    have hl : (10:NNReal) * s n < s (n+1) + 1 := calc
      _ ≤ 10 * (x * 10^n) := by gcongr; grind
      _ = x * 10^(n+1) := by ring_nf
      _ < _ := hs' _
    have hu : s (n+1) < (10:NNReal) * s n + 10 := calc
      _ ≤ x * 10^(n+1) := hs (n+1)
      _ = 10 * (x * 10^n) := by ring_nf
      _ < 10 * (s n + 1) := by gcongr; grind
      _ = _ := by ring
    norm_cast at hl hu
    set d := s (n+1) - 10 * s n
    have hd : d < 10 := by omega
    have : s (n+1) = 10 * s n + d := by omega
    use Digit.mk hd
  choose a ha using hdigit
  set d := mk (s 0) a; use d
  have hsum (n:ℕ) : s n * (10:NNReal)^(-n:ℝ) = s 0 + ∑ i ∈ .range n, a i * (10:NNReal)^(-i-1:ℝ) := by
    induction' n with n hn; simp
    rw [ha n]; calc
      _ = s n * (10:NNReal)^(-n:ℝ) + a n * 10^(-n-1:ℝ) := by
        simp [add_mul]; ring_nf; congr 1
        rw [mul_assoc, ←rpow_add_one]; ring_nf; norm_num
      _ = s 0 + (∑ i ∈ .range n, a i * (10:NNReal)^(-i-1:ℝ) + a n * 10^(-n-1:ℝ)) := by grind
      _ = _ := by congr; symm; apply Finset.sum_range_succ
  have := (d.toNNReal_conv.tendsto_sum_tsum_nat).const_add (s 0:NNReal)
  convert_to Filter.atTop.Tendsto (fun n ↦ s n * (10:NNReal)^(-n:ℝ)) (nhds (d:NNReal)) at this
  . ext n; rw [hsum n]
  apply tendsto_nhds_unique _ this
  apply Filter.Tendsto.squeeze (g := fun n:ℕ ↦ x - (10:NNReal)^(-n:ℝ)) (h := fun _ ↦ x)
  . convert Filter.Tendsto.const_sub (c := 0) x _
    . simp
    convert tendsto_pow_atTop_nhds_zero_of_lt_one (?_:(1/10:NNReal) < 1) with n
    . rw [←rpow_natCast, one_div, inv_rpow, rpow_neg]
    apply div_lt_one_of_lt; bound
  . exact tendsto_const_nhds
  . intro n; simp; calc
    _ = (x * 10^n) * (10:NNReal)^(-n:ℝ) := by
      rw [mul_assoc, ←rpow_natCast, ←rpow_add]; simp; norm_num
    _ ≤ ((s n:NNReal) + 1)*(10:NNReal)^(-n:ℝ) := by gcongr; grind [le_of_lt]
    _ = _ := by ring
  intro n; simp; calc
    _ ≤ (x * 10^n) * (10:NNReal)^(-n:ℝ) := by gcongr; grind
    _ = x := by rw [mul_assoc, ←rpow_natCast, ←rpow_add]; simp; norm_num

/-- Proposition B.2.2 -/
theorem NNRealDecimal.not_inj : (1:NNReal) = (mk 1 fun _ ↦ 0) ∧ (1:NNReal) = (mk 0 fun _ ↦ 9) := by
  -- This proof is written to follow the structure of the original text.
  simp [toNNReal]
  have := (mk 0 fun _ ↦ 9).toNNReal_conv.tendsto_sum_tsum_nat
  simp at this
  apply tendsto_nhds_unique _ this
  convert_to Filter.atTop.Tendsto (fun n:ℕ ↦ 1 - (10:NNReal)^(-n:ℝ)) (nhds 1) using 2 with n
  . induction' n with n hn
    . simp
    rw [Finset.sum_range_succ, hn, Nat.cast_add, Nat.cast_one, neg_add']
    have : (10:NNReal)^(-n:ℝ) = 10^(-n-1:ℝ) * 10 := by
      rw [←rpow_add_one]; simp; norm_num
    simp [this, ←coe_inj]
    rw [NNReal.coe_sub, NNReal.coe_sub]
    . suffices h : ∀ c a : ℝ, c = 9 → 1 - a * 10 + c * a = 1 - a by apply h; norm_cast
      grind
    . apply rpow_le_one_of_one_le_of_nonpos; norm_num; linarith
    rw [←rpow_add_one]
    apply rpow_le_one_of_one_le_of_nonpos; norm_num; linarith; norm_num
  convert Filter.Tendsto.const_sub (f := fun n:ℕ ↦ (10:NNReal)^(-n:ℝ)) (c := 0) 1 _; simp
  convert tendsto_pow_atTop_nhds_zero_of_lt_one (show (1/10:NNReal) < 1 by bound) with n
  rw [←rpow_natCast, one_div, inv_rpow, rpow_neg]

inductive RealDecimal where
  | pos : NNRealDecimal → RealDecimal
  | neg : NNRealDecimal → RealDecimal

noncomputable instance RealDecimal.instCoeReal : Coe RealDecimal ℝ where
  coe := fun d ↦ match d with
    | RealDecimal.pos d => d.toNNReal
    | RealDecimal.neg d => -(d.toNNReal:ℝ)

theorem RealDecimal.surj (x:ℝ) : ∃ d:RealDecimal, x = d := by
  obtain h | h := le_or_gt 0 x
  . choose d hd using NNRealDecimal.surj (x.toNNReal); use pos d; simp [←hd, h]
  . choose d hd using NNRealDecimal.surj ((-x).toNNReal); use neg d; simp [←hd, show 0 ≤ -x by linarith]

/-- Exercise B.2.2 -/
theorem RealDecimal.not_inj_one (d: RealDecimal) : (d:ℝ) = 1 ↔ (d = pos (mk 1 fun _ ↦ 0) ∨ d = pos (mk 0 fun _ ↦ 9)) := by
  constructor
  · intro h
    rcases d with (nd | nd)
    · -- case: d = pos nd
      have hval : (nd : NNReal) = (1 : NNReal) := by
        apply NNReal.coe_inj.mp
        simpa using h
      let f : ℕ → NNReal := fun i ↦ ((nd.fracPart i : Digit) : NNReal) * (10 : NNReal) ^ (-(i : ℝ) - 1 : ℝ)
      have hsum : (nd.intPart : NNReal) + (tsum f) = (1 : NNReal) := by
        simpa [toNNReal, f] using hval
      have hsum_summable : Summable f := by
        simpa [f] using nd.toNNReal_conv
      have hintPart_le_one : nd.intPart ≤ 1 := by
        have : (nd.intPart : NNReal) ≤ (1 : NNReal) := by
          calc
            (nd.intPart : NNReal) ≤ (nd.intPart : NNReal) + (tsum f) := self_le_add_right _ _
            _ = (1 : NNReal) := hsum
        exact_mod_cast this
      obtain h0 | h1 : nd.intPart = 0 ∨ nd.intPart = 1 := by omega
      · -- case intPart = 0
        have htsum_our : tsum f = (1 : NNReal) := by
          simpa [h0] using hsum
        -- Work in ℝ: the 9-series also sums to 1
        let g : ℕ → NNReal := fun i ↦ ((9 : Digit) : NNReal) * (10 : NNReal) ^ (-(i : ℝ) - 1 : ℝ)
        have htsum_9 : tsum g = (1 : NNReal) := by
          have : (mk 0 fun _ : ℕ ↦ (9 : Digit)).toNNReal = (1 : NNReal) := by
            simpa using NNRealDecimal.not_inj.2.symm
          simpa [toNNReal, mk, g] using this
        have hg_summable : Summable g := by
          simpa [g] using (mk 0 fun _ : ℕ ↦ (9 : Digit)).toNNReal_conv
        -- Consider (g_i - f_i) in ℝ, which are all nonnegative and sum to 0
        set h := fun (i : ℕ) ↦ ((g i : ℝ) - (f i : ℝ)) with hh
        have h_nonneg_diff : ∀ i : ℕ, 0 ≤ h i := by
          intro i
          show 0 ≤ ((g i : ℝ) - (f i : ℝ))
          have hdigit : (g i : ℝ) = (((9 : Digit) : NNReal) : ℝ) * (10 : ℝ) ^ (-(i : ℝ) - 1 : ℝ) := by
            simp [g, NNReal.coe_mul, NNReal.coe_rpow]
          have hdigit_f : (f i : ℝ) = (((nd.fracPart i : Digit) : NNReal) : ℝ) * (10 : ℝ) ^ (-(i : ℝ) - 1 : ℝ) := by
            simp [f, NNReal.coe_mul, NNReal.coe_rpow]
          have hdigit_ℝ : ((nd.fracPart i : Digit) : ℝ) ≤ (9 : ℝ) := by
            have hdigitN : ((nd.fracPart i : Digit) : ℕ) ≤ 9 := by
              have hlt : ((nd.fracPart i : Digit) : ℕ) < 10 := Digit.lt _
              omega
            exact_mod_cast hdigitN
          have hpos : 0 ≤ (10 : ℝ) ^ (-(i : ℝ) - 1 : ℝ) := by positivity
          rw [hdigit, hdigit_f]
          simp
          refine mul_le_mul_of_nonneg_right ?_ hpos
          simpa using hdigit_ℝ
        have hgℝ : Summable fun i : ℕ ↦ (g i : ℝ) := by exact_mod_cast hg_summable
        have hfℝ : Summable fun i : ℕ ↦ (f i : ℝ) := by exact_mod_cast hsum_summable
        have htsum_h : tsum h = (0 : ℝ) := by
          calc
            tsum h = (tsum fun i : ℕ ↦ (g i : ℝ)) - (tsum fun i : ℕ ↦ (f i : ℝ)) := by
              simpa [h] using hgℝ.tsum_sub hfℝ
            _ = (((tsum g : NNReal) : ℝ) - ((tsum f : NNReal) : ℝ)) := by simp [NNReal.coe_tsum]
            _ = (1 : ℝ) - (1 : ℝ) := by simp [htsum_our, htsum_9]
            _ = (0 : ℝ) := by ring
        have h_summable_h : Summable h := hgℝ.sub hfℝ
        have h_hasSum_h : HasSum h (0 : ℝ) := by
          simpa [htsum_h] using h_summable_h.hasSum
        have h_each_zero : ∀ i : ℕ, h i = (0 : ℝ) := by
          have hzero : h = 0 := ((hasSum_zero_iff_of_nonneg h_nonneg_diff).mp h_hasSum_h)
          intro i
          have := congrArg (fun (h' : ℕ → ℝ) ↦ h' i) hzero
          simpa [h] using this
        have h_eq_ℝ : ∀ i : ℕ, ((nd.fracPart i : Digit) : ℝ) = (9 : ℝ) := by
          intro i
          have hzero : h i = (0 : ℝ) := h_each_zero i
          have hzero' : (g i : ℝ) = (f i : ℝ) := by
            have : h i = (g i : ℝ) - (f i : ℝ) := rfl
            rw [this] at hzero
            linarith
          have hpos : (0 : ℝ) < (10 : ℝ) ^ (-(i : ℝ) - 1 : ℝ) := by positivity
          have hg_eq : (g i : ℝ) = (((9 : Digit) : NNReal) : ℝ) * (10 : ℝ) ^ (-(i : ℝ) - 1 : ℝ) := by
            simp [g, NNReal.coe_mul, NNReal.coe_rpow]
          have hf_eq : (f i : ℝ) = (((nd.fracPart i : Digit) : NNReal) : ℝ) * (10 : ℝ) ^ (-(i : ℝ) - 1 : ℝ) := by
            simp [f, NNReal.coe_mul, NNReal.coe_rpow]
          rw [hg_eq, hf_eq] at hzero'
          have hfactor : ((((9 : Digit) : NNReal) : ℝ) - (((nd.fracPart i : Digit) : NNReal) : ℝ)) * (10 : ℝ) ^ (-(i : ℝ) - 1 : ℝ) = 0 := by
            nlinarith
          rcases eq_zero_or_eq_zero_of_mul_eq_zero hfactor with (h | hpower)
          · have : ((nd.fracPart i : Digit) : ℝ) = (9 : ℝ) := by
              calc
                ((nd.fracPart i : Digit) : ℝ) = (((nd.fracPart i : Digit) : NNReal) : ℝ) := by simp
                _ = (((9 : Digit) : NNReal) : ℝ) := by linarith
                _ = (9 : ℝ) := by
                  have : ((9 : Digit) : ℕ) = 9 := by decide
                  exact_mod_cast this
            exact this
          · exfalso; linarith
        have h_digit_eq : ∀ i : ℕ, nd.fracPart i = (9 : Digit) := by
          intro i
          have hNat : ((nd.fracPart i : Digit) : ℕ) = ((9 : Digit) : ℕ) := by
            have hcoeff : ((nd.fracPart i : Digit) : ℝ) = ((9 : Digit) : ℝ) := h_eq_ℝ i
            have hNN : ((nd.fracPart i : Digit) : NNReal) = ((9 : Digit) : NNReal) := by exact_mod_cast hcoeff
            exact_mod_cast hNN
          apply (Digit.inj (nd.fracPart i) (9 : Digit)).mpr
          exact hNat
        have h_nd_eq : nd = mk 0 (fun _ : ℕ ↦ (9 : Digit)) := by
          apply (NNRealDecimal.mk.injEq _ _ _ _).mpr
          constructor
          · exact h0
          · ext i
            simp [h_digit_eq i]
        exact Or.inr (by exact congrArg pos h_nd_eq)
      · -- case intPart = 1
        have h_tsum_zero : tsum f = (0 : NNReal) := by
          have h_eq : (1 : NNReal) + tsum f = (1 : NNReal) := by
            simpa [h1] using hsum
          exact (add_eq_left (a := (1 : NNReal)) (b := tsum f)).mp h_eq
        have h_each_zero : ∀ i : ℕ, f i = (0 : NNReal) :=
          ((Summable.tsum_eq_zero_iff hsum_summable).mp h_tsum_zero)
        have hpos : ∀ i : ℕ, (0 : NNReal) < (10 : NNReal) ^ (-(i : ℝ) - 1 : ℝ) := by
          intro i
          exact NNReal.rpow_pos (hx_pos := (by norm_num : (0 : NNReal) < (10 : NNReal))) (p := (-(i : ℝ) - 1 : ℝ))
        have h_digit_eq : ∀ i : ℕ, nd.fracPart i = (0 : Digit) := by
          intro i
          have h_each : f i = (0 : NNReal) := h_each_zero i
          dsimp [f] at h_each
          have h_coeff_zero : ((nd.fracPart i : Digit) : NNReal) = (0 : NNReal) := by
            rcases mul_eq_zero.mp h_each with (hcoeff | hpow)
            · exact hcoeff
            · exact absurd hpow (hpos i).ne'
          have hNat : ((nd.fracPart i : Digit) : ℕ) = ((0 : Digit) : ℕ) := by
            apply (Nat.cast_inj (R := NNReal)).mp
            simpa using h_coeff_zero
          apply (Digit.inj (nd.fracPart i) (0 : Digit)).mpr
          exact hNat
        have h_nd_eq : nd = mk 1 (fun _ : ℕ ↦ (0 : Digit)) := by
          apply (NNRealDecimal.mk.injEq _ _ _ _).mpr
          constructor
          · exact h1
          · ext i; simp [h_digit_eq i]
        exact Or.inl (by exact congrArg pos h_nd_eq)
    · -- case: d = neg nd
      have : ((RealDecimal.neg nd : ℝ) : ℝ) ≤ 0 := by
        dsimp
        have h_nonneg : 0 ≤ (nd : NNReal) := NNReal.coe_nonneg _
        simp
      linarith
  · intro h
    rcases h with (h | h)
    · subst h
      have h_notinj := NNRealDecimal.not_inj.1
      simpa using (congrArg (fun x : NNReal ↦ (x : ℝ)) h_notinj).symm
    · subst h
      have h_notinj := NNRealDecimal.not_inj.2
      simpa using (congrArg (fun x : NNReal ↦ (x : ℝ)) h_notinj).symm

/-- Exercise B.2.3 -/
abbrev TerminatingDecimal (x:ℝ) : Prop := ∃ (n:ℤ) (m:ℕ), x = n / (10:ℝ)^m

/-- If tsum f = 1 and each digit of f is at most 9, then all digits are 9. -/
lemma all_frac_nine_of_tsum_one {nd : NNRealDecimal}
    (hsum_summable : Summable (fun i : ℕ ↦ ((nd.fracPart i : Digit) : NNReal) * (10 : NNReal) ^ (-(i : ℝ) - 1 : ℝ)))
    (htsum_one : (tsum fun i : ℕ ↦ ((nd.fracPart i : Digit) : NNReal) * (10 : NNReal) ^ (-(i : ℝ) - 1 : ℝ)) = (1 : NNReal)) :
    ∀ i : ℕ, nd.fracPart i = (9 : Digit) := by
  let f : ℕ → NNReal := fun i ↦ ((nd.fracPart i : Digit) : NNReal) * (10 : NNReal) ^ (-(i : ℝ) - 1 : ℝ)
  have htsum_f_one : tsum f = (1 : NNReal) := htsum_one
  let g : ℕ → NNReal := fun i ↦ ((9 : Digit) : NNReal) * (10 : NNReal) ^ (-(i : ℝ) - 1 : ℝ)
  have htsum_g_one : tsum g = (1 : NNReal) := by
    have h9 : (mk 0 fun _ : ℕ ↦ (9 : Digit) : NNReal) = (1 : NNReal) := NNRealDecimal.not_inj.2.symm
    simpa [toNNReal, mk, g] using h9
  have hg_summable : Summable g := by
    simpa [g] using (mk 0 fun _ : ℕ ↦ (9 : Digit)).toNNReal_conv
  set h := fun (i : ℕ) ↦ ((g i : ℝ) - (f i : ℝ)) with hh
  have h_nonneg_diff : ∀ i : ℕ, 0 ≤ h i := by
    intro i
    have hdigit : (g i : ℝ) = (((9 : Digit) : NNReal) : ℝ) * (10 : ℝ) ^ (-(i : ℝ) - 1 : ℝ) := by
      simp [g, NNReal.coe_mul, NNReal.coe_rpow]
    have hdigit_f : (f i : ℝ) = (((nd.fracPart i : Digit) : NNReal) : ℝ) * (10 : ℝ) ^ (-(i : ℝ) - 1 : ℝ) := by
      simp [f, NNReal.coe_mul, NNReal.coe_rpow]
    have hdigit_ℝ : ((nd.fracPart i : Digit) : ℝ) ≤ (9 : ℝ) := by
      have hdigitN : ((nd.fracPart i : Digit) : ℕ) ≤ 9 := by
        have hlt : ((nd.fracPart i : Digit) : ℕ) < 10 := Digit.lt _
        omega
      exact_mod_cast hdigitN
    have hpos : 0 ≤ (10 : ℝ) ^ (-(i : ℝ) - 1 : ℝ) := by positivity
    dsimp [h]
    have : (g i : ℝ) - (f i : ℝ) = (((9 : Digit) : NNReal) : ℝ) * (10 : ℝ) ^ (-(i : ℝ) - 1 : ℝ) - (((nd.fracPart i : Digit) : NNReal) : ℝ) * (10 : ℝ) ^ (-(i : ℝ) - 1 : ℝ) := by
      simp [hdigit, hdigit_f]
    rw [this]
    simp
    refine mul_le_mul_of_nonneg_right ?_ hpos
    simpa using hdigit_ℝ
  have hgℝ : Summable fun i : ℕ ↦ (g i : ℝ) := NNReal.summable_coe.mpr hg_summable
  have hfℝ : Summable fun i : ℕ ↦ (f i : ℝ) := NNReal.summable_coe.mpr hsum_summable
  have htsum_h : tsum h = (0 : ℝ) := by
    calc
      tsum h = (tsum fun i : ℕ ↦ (g i : ℝ)) - (tsum fun i : ℕ ↦ (f i : ℝ)) := by
        simpa [h] using hgℝ.tsum_sub hfℝ
      _ = (((tsum g : NNReal) : ℝ) - ((tsum f : NNReal) : ℝ)) := by simp [NNReal.coe_tsum]
      _ = (1 : ℝ) - (1 : ℝ) := by simp [htsum_f_one, htsum_g_one]
      _ = (0 : ℝ) := by ring
  have h_summable_h : Summable h := hgℝ.sub hfℝ
  have h_hasSum_h : HasSum h (0 : ℝ) := by
    simpa [htsum_h] using h_summable_h.hasSum
  have h_each_zero : ∀ i : ℕ, h i = (0 : ℝ) := by
    have hzero : h = 0 := ((hasSum_zero_iff_of_nonneg h_nonneg_diff).mp h_hasSum_h)
    intro i
    have := congrArg (fun (h' : ℕ → ℝ) ↦ h' i) hzero
    simpa [h] using this
  intro i
  have hzero : h i = (0 : ℝ) := h_each_zero i
  have hzero' : (g i : ℝ) = (f i : ℝ) := by
    have : h i = (g i : ℝ) - (f i : ℝ) := rfl
    rw [this] at hzero; linarith
  have hpos' : (0 : ℝ) < (10 : ℝ) ^ (-(i : ℝ) - 1 : ℝ) := by positivity
  have hg_eq : (g i : ℝ) = (((9 : Digit) : NNReal) : ℝ) * (10 : ℝ) ^ (-(i : ℝ) - 1 : ℝ) := by
    simp [g, NNReal.coe_mul, NNReal.coe_rpow]
  have hf_eq : (f i : ℝ) = (((nd.fracPart i : Digit) : NNReal) : ℝ) * (10 : ℝ) ^ (-(i : ℝ) - 1 : ℝ) := by
    simp [f, NNReal.coe_mul, NNReal.coe_rpow]
  rw [hg_eq, hf_eq] at hzero'
  have hfactor : ((((9 : Digit) : NNReal) : ℝ) - (((nd.fracPart i : Digit) : NNReal) : ℝ)) * (10 : ℝ) ^ (-(i : ℝ) - 1 : ℝ) = 0 := by
    nlinarith
  rcases eq_zero_or_eq_zero_of_mul_eq_zero hfactor with (hcoeff | hpower)
  · have hcoeff_ℝ : ((nd.fracPart i : Digit) : ℝ) = (9 : ℝ) := by
      calc
        ((nd.fracPart i : Digit) : ℝ) = (((nd.fracPart i : Digit) : NNReal) : ℝ) := by simp
        _ = (((9 : Digit) : NNReal) : ℝ) := by linarith
        _ = (9 : ℝ) := by
          have : ((9 : Digit) : ℕ) = 9 := by decide
          exact_mod_cast this
    have hNat : ((nd.fracPart i : Digit) : ℕ) = ((9 : Digit) : ℕ) := by
      have hcoeff_NN : ((nd.fracPart i : Digit) : NNReal) = ((9 : Digit) : NNReal) := by exact_mod_cast hcoeff_ℝ
      exact_mod_cast hcoeff_NN
    apply (Digit.inj (nd.fracPart i) (9 : Digit)).mpr; exact hNat
  · exfalso; linarith

/-- If tsum f = 0 and each term is non-negative, then all digits are 0. -/
lemma all_frac_zero_of_tsum_zero {nd : NNRealDecimal}
    (hsum_summable : Summable (fun i : ℕ ↦ ((nd.fracPart i : Digit) : NNReal) * (10 : NNReal) ^ (-(i : ℝ) - 1 : ℝ)))
    (htsum_zero : (tsum fun i : ℕ ↦ ((nd.fracPart i : Digit) : NNReal) * (10 : NNReal) ^ (-(i : ℝ) - 1 : ℝ)) = (0 : NNReal)) :
    ∀ i : ℕ, nd.fracPart i = (0 : Digit) := by
  have h_each_zero : ∀ i : ℕ, ((nd.fracPart i : Digit) : NNReal) * (10 : NNReal) ^ (-(i : ℝ) - 1 : ℝ) = (0 : NNReal) :=
    (hsum_summable.tsum_eq_zero_iff.mp htsum_zero)
  intro i
  have hpos_rpow' : (0 : NNReal) < (10 : NNReal) ^ (-(i : ℝ) - 1 : ℝ) :=
    NNReal.rpow_pos (hx_pos := (by norm_num : (0 : NNReal) < (10 : NNReal))) (p := (-(i : ℝ) - 1 : ℝ))
  have hcoeff : ((nd.fracPart i : Digit) : NNReal) = 0 := by
    have hzero := h_each_zero i
    rcases mul_eq_zero.mp hzero with (hcoeff | hpow)
    · exact hcoeff
    · exfalso; exact hpos_rpow'.ne' hpow
  have hNat : ((nd.fracPart i : Digit) : ℕ) = (0 : ℕ) := by
    apply (Nat.cast_inj (R := NNReal)).mp; simpa using hcoeff
  apply (Digit.inj (nd.fracPart i) (0 : Digit)).mpr; exact hNat

/-! ## Infrastructure for uniqueness of decimal representations -/

/-
The real-valued fractional part sum is summable.
-/
lemma NNRealDecimal.summable_rterm (nd : NNRealDecimal) :
    Summable (fun i : ℕ ↦ ((nd.fracPart i : Digit) : ℝ) * (10:ℝ)^(-(i:ℝ)-1)) := by
  convert NNReal.summable_coe.mpr ( NNRealDecimal.toNNReal_conv nd ) using 1

/-
The real value of `pos nd` as an integer part plus a real tsum.
-/
lemma NNRealDecimal.coe_pos_eq (nd : NNRealDecimal) :
    (RealDecimal.pos nd : ℝ)
      = (nd.intPart : ℝ) + ∑' i : ℕ, ((nd.fracPart i : Digit) : ℝ) * (10:ℝ)^(-(i:ℝ)-1) := by
  convert congr_arg NNReal.toReal ( NNRealDecimal.toNNReal_conv nd |> fun h => show ( nd.intPart : NNReal ) + ∑' i, ( nd.fracPart i : NNReal ) * 10 ^ ( -i - 1 : ℝ ) = _ from rfl ) using 1;
  rw [ NNReal.coe_add, NNReal.coe_tsum ];
  norm_num [ Real.rpow_add, Real.rpow_sub ]

/-
The tsum of the all-nines fractional series equals 1 (over ℝ).
-/
lemma nine_rtsum : (∑' i : ℕ, (9:ℝ) * (10:ℝ)^(-(i:ℝ)-1)) = 1 := by
  have h_nn : (mk 0 fun _ : ℕ => (9:Digit)).toNNReal = (1:NNReal) := NNRealDecimal.not_inj.2.symm
  have h_val : ((mk 0 fun _ : ℕ => (9:Digit)).toNNReal : ℝ) = (1:ℝ) := by exact_mod_cast h_nn
  unfold NNRealDecimal.toNNReal at h_val
  simp [NNReal.coe_tsum, NNReal.coe_mul, NNReal.coe_rpow] at h_val
  simpa using h_val

/-- The integer partial value: `intPart·10^N` plus the first {name}`N` fractional digits shifted up. -/
def NNRealDecimal.Pnat (nd : NNRealDecimal) (N : ℕ) : ℕ :=
  nd.intPart * 10^N + ∑ i ∈ Finset.range N, (nd.fracPart i : ℕ) * 10^(N-1-i)

lemma NNRealDecimal.Pnat_zero (nd : NNRealDecimal) : nd.Pnat 0 = nd.intPart := by
  simp [NNRealDecimal.Pnat]

/-
The `N`-th fractional digit is recovered from consecutive partial values.
-/
lemma NNRealDecimal.frac_eq_Pnat (nd : NNRealDecimal) (N : ℕ) :
    (nd.fracPart N : ℕ) = nd.Pnat (N+1) - 10 * nd.Pnat N := by
  unfold NNRealDecimal.Pnat;
  simp +decide [ Finset.sum_range_succ, pow_succ' ];
  simp +decide [ mul_add, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, tsub_tsub, add_comm ];
  exact eq_tsub_of_add_eq ( by rw [ show ( ∑ i ∈ Finset.range N, 10 ^ ( N - i ) * ( nd.fracPart i : ℕ ) ) = ∑ i ∈ Finset.range N, 10 * ( 10 ^ ( N - ( i + 1 ) ) * ( nd.fracPart i : ℕ ) ) by exact Finset.sum_congr rfl fun i hi => by rw [ show N - i = N - ( i + 1 ) + 1 by exact Nat.sub_eq_of_eq_add <| by linarith [ Nat.sub_add_cancel <| show i + 1 ≤ N from by linarith [ Finset.mem_range.mp hi ] ] ] ; ring ] ; ring )

/-
Two decimals with identical partial values at every position are equal.
-/
lemma NNRealDecimal.eq_of_Pnat_eq (nd nd' : NNRealDecimal)
    (h : ∀ N, nd.Pnat N = nd'.Pnat N) : nd = nd' := by
  have h_intPart : nd.intPart = nd'.intPart := by
    simpa [ NNRealDecimal.Pnat_zero ] using h 0
  have h_fracPart : ∀ N, (nd.fracPart N : ℕ) = (nd'.fracPart N : ℕ) := by
    grind +suggestions;
  cases nd ; cases nd' ; aesop

/-
`Pnat N` as a real number equals the first `N` real fractional terms, each scaled by `10^N`.
-/
lemma NNRealDecimal.Pnat_real_eq (nd : NNRealDecimal) (N : ℕ) :
    (nd.Pnat N : ℝ)
      = (nd.intPart : ℝ) * 10^N
        + ∑ i ∈ Finset.range N, ((nd.fracPart i : Digit) : ℝ) * (10:ℝ)^(-(i:ℝ)-1) * 10^N := by
  convert congr_arg ( ( ↑ ) : ℕ → ℝ ) ( show ( nd.Pnat N : ℕ ) = nd.intPart * 10 ^ N + ∑ i ∈ Finset.range N, ( nd.fracPart i : ℕ ) * 10 ^ ( N - 1 - i ) from rfl ) using 1 ; norm_num [ Finset.sum_mul _ _ _ ];
  refine Finset.sum_congr rfl fun i hi => ?_;
  rw [ mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add ] <;> norm_num;
  rw [ ← Real.rpow_natCast ] ; rw [ Nat.sub_sub ] ; rw [ Nat.cast_sub <| by linarith [ Finset.mem_range.mp hi ] ] ; push_cast ; ring_nf ; aesop;

/-
The shifted fractional tail is nonnegative.
-/
lemma NNRealDecimal.tail_nonneg (nd : NNRealDecimal) (N : ℕ) :
    0 ≤ ∑' i : ℕ, ((nd.fracPart (i+N) : Digit) : ℝ) * (10:ℝ)^(-((i:ℝ)+N)-1) := by
  exact tsum_nonneg fun _ => by positivity;

/-
The shifted fractional tail is at most `10^(-N)`.
-/
lemma NNRealDecimal.tail_le (nd : NNRealDecimal) (N : ℕ) :
    (∑' i : ℕ, ((nd.fracPart (i+N) : Digit) : ℝ) * (10:ℝ)^(-((i:ℝ)+N)-1)) ≤ (10:ℝ)^(-(N:ℝ)) := by
  convert Summable.tsum_le_tsum _ _ _ using 1;
  rotate_left;
  all_goals try infer_instance;
  use fun i => 9 * ( 10 : ℝ ) ^ ( - ( i + N : ℝ ) - 1 );
  · intro i
    have hdigitN : ((nd.fracPart (i+N) : Digit) : ℕ) ≤ 9 := by
      have hlt : ((nd.fracPart (i+N) : Digit) : ℕ) < 10 := Digit.lt _
      omega
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hdigitN) (by positivity)
  · convert NNRealDecimal.summable_rterm ( nd ) |> Summable.comp_injective <| add_left_injective N using 1;
    exact funext fun i => by rw [ Function.comp_apply ] ; push_cast; ring;
  · norm_num [ Real.rpow_add, Real.rpow_sub ] ; ring_nf ; norm_num;
    exact Summable.mul_right _ ( Summable.mul_left _ ( summable_geometric_of_lt_one ( by norm_num ) ( by norm_num ) ) );
  · convert nine_rtsum.symm ▸ tsum_mul_right.symm using 1;
    rw [ one_mul ];
    exact tsum_congr fun i => by rw [ mul_assoc, ← Real.rpow_add ( by norm_num ) ] ; ring_nf;

/-
Value decomposition: `value · 10^N` is the integer partial value plus the scaled shifted tail.
-/
lemma NNRealDecimal.val_mul_pow (nd : NNRealDecimal) (N : ℕ) :
    (nd.toNNReal : ℝ) * 10^N
      = (nd.Pnat N : ℝ)
        + (∑' i : ℕ, ((nd.fracPart (i+N) : Digit) : ℝ) * (10:ℝ)^(-((i:ℝ)+N)-1)) * 10^N := by
  rw [ NNRealDecimal.Pnat_real_eq ];
  have h_split : (∑' i : ℕ, ((nd.fracPart i : Digit) : ℝ) * (10:ℝ)^(-(i:ℝ)-1)) = (∑ i ∈ Finset.range N, ((nd.fracPart i : Digit) : ℝ) * (10:ℝ)^(-(i:ℝ)-1)) + (∑' i : ℕ, ((nd.fracPart (i+N) : Digit) : ℝ) * (10:ℝ)^(-(i+N:ℝ)-1)) := by
    rw [ ← Summable.sum_add_tsum_nat_add ];
    norm_cast;
    convert NNRealDecimal.summable_rterm nd using 1;
  convert congr_arg ( · * 10 ^ N ) ( congr_arg ( fun x : ℝ => ( nd.intPart : ℝ ) + x ) h_split ) using 1 ; norm_num [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ; ring_nf;
  · convert NNRealDecimal.coe_pos_eq nd using 1;
    exact congrArg _ ( tsum_congr fun i => by ring_nf );
  · norm_num [ add_mul, Finset.sum_mul ] ; ring

/-
Lower floor bound: the integer partial value never exceeds the scaled real value.
-/
lemma NNRealDecimal.Pnat_le_val (nd : NNRealDecimal) (N : ℕ) :
    (nd.Pnat N : ℝ) ≤ (nd.toNNReal : ℝ) * 10^N := by
  have := NNRealDecimal.val_mul_pow nd N;
  exact this ▸ le_add_of_nonneg_right ( mul_nonneg ( tsum_nonneg fun _ => by positivity ) ( by positivity ) )

/-
Upper floor bound: the scaled real value is at most one above the partial value.
-/
lemma NNRealDecimal.val_le_Pnat_succ (nd : NNRealDecimal) (N : ℕ) :
    (nd.toNNReal : ℝ) * 10^N ≤ (nd.Pnat N : ℝ) + 1 := by
  convert add_le_add_left ( mul_le_mul_of_nonneg_right ( NNRealDecimal.tail_le nd N ) ( by positivity : ( 0 : ℝ ) ≤ 10 ^ N ) ) ( nd.Pnat N : ℝ ) using 1;
  · rw [ add_comm, NNRealDecimal.val_mul_pow ];
  · norm_num [ Real.rpow_neg, add_comm ]

/-
For a non-terminating value, the floor of the scaled value is exactly the partial value.
-/
lemma NNRealDecimal.floor_val_eq_Pnat (nd : NNRealDecimal) (N : ℕ)
    (hx : ¬ TerminatingDecimal (nd.toNNReal : ℝ)) :
    ⌊(nd.toNNReal : ℝ) * 10^N⌋₊ = nd.Pnat N := by
  refine' Nat.floor_eq_iff ( by positivity ) |>.2 ⟨ _, _ ⟩;
  · convert NNRealDecimal.Pnat_le_val nd N using 1;
  · contrapose! hx;
    use nd.Pnat N + 1, N;
    convert eq_div_of_mul_eq ( by positivity : ( 10 : ℝ ) ^ N ≠ 0 ) _;
    exact le_antisymm ( mod_cast by exact_mod_cast NNRealDecimal.val_le_Pnat_succ nd N ) ( mod_cast hx )

/-- Two non-terminating decimals with the same value are equal. -/
lemma NNRealDecimal.inj_of_nonterm (nd nd' : NNRealDecimal)
    (h : (nd.toNNReal : ℝ) = (nd'.toNNReal : ℝ))
    (hx : ¬ TerminatingDecimal (nd.toNNReal : ℝ)) : nd = nd' := by
  apply NNRealDecimal.eq_of_Pnat_eq
  intro N
  have e1 := nd.floor_val_eq_Pnat N hx
  have e2 := nd'.floor_val_eq_Pnat N (by rwa [h] at hx)
  rw [← e1, ← e2, h]

@[simp] lemma RealDecimal.coe_pos (nd : NNRealDecimal) :
    (RealDecimal.pos nd : ℝ) = (nd.toNNReal : ℝ) := rfl

@[simp] lemma RealDecimal.coe_neg (nd : NNRealDecimal) :
    (RealDecimal.neg nd : ℝ) = -(nd.toNNReal : ℝ) := rfl

/-
Negation preserves (non-)terminating.
-/
lemma terminating_neg_iff (x : ℝ) : TerminatingDecimal (-x) ↔ TerminatingDecimal x := by
  constructor;
  · rintro ⟨ n, m, h ⟩;
    exact ⟨ -n, m, by push_cast; linear_combination -h ⟩;
  · rintro ⟨ n, m, h ⟩;
    exact ⟨ -n, m, by push_cast [ h ] ; ring ⟩

/-! # Classification of collisions for terminating values -/

/-
If all fractional digits from `N` on are 0, the shifted tail is 0.
-/
lemma NNRealDecimal.tail_all0 (nd : NNRealDecimal) (N : ℕ) (h : ∀ i, nd.fracPart (i+N) = 0) :
    (∑' i : ℕ, ((nd.fracPart (i+N) : Digit) : ℝ) * (10:ℝ)^(-((i:ℝ)+N)-1)) = 0 := by
  aesop

/-
If all fractional digits from `N` on are 9, the shifted tail is `10^(-N)`.
-/
lemma NNRealDecimal.tail_all9 (nd : NNRealDecimal) (N : ℕ) (h : ∀ i, nd.fracPart (i+N) = 9) :
    (∑' i : ℕ, ((nd.fracPart (i+N) : Digit) : ℝ) * (10:ℝ)^(-((i:ℝ)+N)-1)) = (10:ℝ)^(-(N:ℝ)) := by
  have h_add : ∀ i : ℕ, (10:ℝ)^(-((i:ℝ)+N)-1) = (10:ℝ)^(-(i:ℝ)-1) * (10:ℝ)^(-(N:ℝ)) := by
    intro i
    have h10 : (0:ℝ) < 10 := by norm_num
    calc
      (10:ℝ)^(-((i:ℝ)+N)-1) = (10:ℝ)^((-(i:ℝ)-1) + (-(N:ℝ))) := by ring_nf
      _ = (10:ℝ)^(-(i:ℝ)-1) * (10:ℝ)^(-(N:ℝ)) := by rw [Real.rpow_add h10]
  calc
    (∑' i : ℕ, (((nd.fracPart (i+N) : Digit) : ℝ) * (10:ℝ)^(-((i:ℝ)+N)-1)))
        = (∑' i : ℕ, ((9 : Digit) : ℝ) * (10:ℝ)^(-((i:ℝ)+N)-1)) := by
      refine tsum_congr fun i => ?_
      simp [h i]
    _ = (∑' i : ℕ, ((9 : Digit) : ℝ) * ((10:ℝ)^(-(i:ℝ)-1) * (10:ℝ)^(-(N:ℝ)))) := by
      refine tsum_congr fun i => ?_
      rw [h_add i]
    _ = (∑' i : ℕ, (((9 : Digit) : ℝ) * (10:ℝ)^(-(i:ℝ)-1)) * (10:ℝ)^(-(N:ℝ))) := by
      refine tsum_congr fun i => ?_
      ring
    _ = ((∑' i : ℕ, ((9 : Digit) : ℝ) * (10:ℝ)^(-(i:ℝ)-1)) * (10:ℝ)^(-(N:ℝ))) :=
      tsum_mul_right (a := (10:ℝ)^(-(N:ℝ))) (f := fun (i : ℕ) => ((9 : Digit) : ℝ) * (10:ℝ)^(-(i:ℝ)-1))
    _ = (∑' i : ℕ, ((9 : Digit) : ℝ) * (10:ℝ)^(-(i:ℝ)-1)) * (10:ℝ)^(-(N:ℝ)) := rfl
    _ = (∑' i : ℕ, (9:ℝ) * (10:ℝ)^(-(i:ℝ)-1)) * (10:ℝ)^(-(N:ℝ)) := by
      have h9_val : ((9 : Digit) : ℝ) = (9:ℝ) := by
        have h : ((9 : Digit) : ℕ) = (9 : ℕ) := by decide
        exact_mod_cast h
      have h_tsum : (∑' i : ℕ, ((9 : Digit) : ℝ) * (10:ℝ)^(-(i:ℝ)-1)) = (∑' i : ℕ, (9:ℝ) * (10:ℝ)^(-(i:ℝ)-1)) :=
        tsum_congr fun i => by rw [h9_val]
      rw [h_tsum]
    _ = 1 * (10:ℝ)^(-(N:ℝ)) := by rw [nine_rtsum]
    _ = (10:ℝ)^(-(N:ℝ)) := by simp

/-
If some fractional digit from `N` on is not 9, the shifted tail is strictly below `10^(-N)`.
-/
lemma NNRealDecimal.tail_lt (nd : NNRealDecimal) (N : ℕ) (h : ∃ i, nd.fracPart (i+N) ≠ 9) :
    (∑' i : ℕ, ((nd.fracPart (i+N) : Digit) : ℝ) * (10:ℝ)^(-((i:ℝ)+N)-1)) < (10:ℝ)^(-(N:ℝ)) := by
  have h10pos : (0 : ℝ) < (10 : ℝ) := by norm_num
  set f := fun i : ℕ => ((nd.fracPart (i+N) : Digit) : ℝ) * (10:ℝ)^(-((i:ℝ)+N)-1)
  set g := fun i : ℕ => (9:ℝ) * (10:ℝ)^(-((i:ℝ)+N)-1)
  have ha_base : Summable (fun (i : ℕ) => ((nd.fracPart i : Digit) : ℝ) * (10:ℝ)^(-(i:ℝ)-1)) :=
    NNRealDecimal.summable_rterm nd
  have h_geom : Summable (fun (i : ℕ) => ((1/10 : ℝ) ^ (i : ℕ))) :=
    summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ (1/10 : ℝ)) (by norm_num : (1/10 : ℝ) < 1)
  have h_geom9 : Summable (fun (i : ℕ) => (9:ℝ) * (10:ℝ)^(-(i:ℝ)-1)) := by
    -- Since the tsum is 1 (finite), the series must be summable
    by_cases h : Summable (fun (i : ℕ) => (9:ℝ) * (10:ℝ)^(-(i:ℝ)-1))
    · exact h
    · have hzero : (∑' i : ℕ, (9:ℝ) * (10:ℝ)^(-(i:ℝ)-1)) = 0 := tsum_eq_zero_of_not_summable h
      have hone : (∑' i : ℕ, (9:ℝ) * (10:ℝ)^(-(i:ℝ)-1)) = 1 := nine_rtsum
      linarith
  have h_inj : Function.Injective (fun (i : ℕ) => i + N) := by
    exact add_left_injective N
  have hfs : Summable f := by
    have ha_shift' : Summable (fun (i : ℕ) => ((nd.fracPart (i+N) : Digit) : ℝ) * (10:ℝ)^(-((i:ℝ)+N)-1)) := by
      have : (fun (i : ℕ) => ((nd.fracPart i : Digit) : ℝ) * (10:ℝ)^(-(i:ℝ)-1)) ∘ (fun (i : ℕ) => i + N) =
            (fun (i : ℕ) => ((nd.fracPart (i+N) : Digit) : ℝ) * (10:ℝ)^(-((i:ℝ)+N)-1)) := by
        ext i; simp
      rw [← this]
      exact ha_base.comp_injective h_inj
    dsimp [f]
    exact ha_shift'
  have hgs : Summable g := by
    have hg_shift' : Summable (fun (i : ℕ) => (9:ℝ) * (10:ℝ)^(-((i:ℝ)+N)-1)) := by
      have : (fun (i : ℕ) => (9:ℝ) * (10:ℝ)^(-(i:ℝ)-1)) ∘ (fun (i : ℕ) => i + N) =
            (fun (i : ℕ) => (9:ℝ) * (10:ℝ)^(-((i:ℝ)+N)-1)) := by
        ext i; simp
      rw [← this]
      exact h_geom9.comp_injective h_inj
    dsimp [g]
    exact hg_shift'
  have hfg : ∀ i, f i ≤ g i := by
    intro i
    dsimp [f, g]
    have hdigit : ((nd.fracPart (i+N) : Digit) : ℝ) ≤ (9 : ℝ) := by
      have hdigitN : ((nd.fracPart (i+N) : Digit) : ℕ) ≤ 9 := by
        have hlt' : ((nd.fracPart (i+N) : Digit) : ℕ) < 10 := Digit.lt _
        omega
      exact_mod_cast hdigitN
    have hpos : 0 ≤ (10:ℝ)^(-((i:ℝ)+N)-1) := by positivity
    nlinarith
  have hlt : ∃ i, f i < g i := by
    obtain ⟨i, hi⟩ := h
    refine ⟨i, ?_⟩
    dsimp [f, g]
    have hdigit : ((nd.fracPart (i+N) : Digit) : ℝ) ≤ (9 : ℝ) := by
      have hdigitN : ((nd.fracPart (i+N) : Digit) : ℕ) ≤ 9 := by
        have hlt' : ((nd.fracPart (i+N) : Digit) : ℕ) < 10 := Digit.lt _
        omega
      exact_mod_cast hdigitN
    have hdigit' : ((nd.fracPart (i+N) : Digit) : ℝ) ≠ (9 : ℝ) := by
      intro h_eq
      apply hi
      apply (Digit.inj _ _).mpr
      exact_mod_cast h_eq
    have hdigit_lt : ((nd.fracPart (i+N) : Digit) : ℝ) < (9 : ℝ) :=
      lt_of_le_of_ne hdigit hdigit'
    have hpos : 0 < (10:ℝ)^(-((i:ℝ)+N)-1) := by positivity
    nlinarith
  have htsum_g : tsum g = (10:ℝ)^(-(N:ℝ)) := by
    calc
      tsum g = (∑' i : ℕ, (9:ℝ) * (10:ℝ)^(-((i:ℝ)+N)-1)) := rfl
      _ = (∑' i : ℕ, ((9 : Digit) : ℝ) * (10:ℝ)^(-((i:ℝ)+N)-1)) := by
        have h9_val : ((9 : Digit) : ℝ) = (9:ℝ) := by
          have h : ((9 : Digit) : ℕ) = (9 : ℕ) := by decide
          exact_mod_cast h
        refine tsum_congr fun i => ?_
        rw [h9_val]
      _ = (∑' i : ℕ, (((mk 0 fun _ : ℕ => (9:Digit)).fracPart (i+N) : Digit) : ℝ) * (10:ℝ)^(-((i:ℝ)+N)-1)) := by simp
      _ = (10:ℝ)^(-(N:ℝ)) := NNRealDecimal.tail_all9 (mk 0 fun _ : ℕ => (9:Digit)) N (fun _ => rfl)
  have h_nonneg_f : ∀ i, 0 ≤ f i := by
    intro i; dsimp [f]; positivity
  obtain ⟨i_lt, hi_lt⟩ := hlt
  have htsum_lt : tsum f < tsum g :=
    Summable.tsum_lt_tsum_of_nonneg h_nonneg_f hfg hi_lt hgs
  calc
    (∑' i : ℕ, ((nd.fracPart (i+N) : Digit) : ℝ) * (10:ℝ)^(-((i:ℝ)+N)-1))
        = tsum f := rfl
    _ < tsum g := htsum_lt
    _ = (10:ℝ)^(-(N:ℝ)) := htsum_g

/-
Floor from a strict tail bound (used for non-eventually-nine decimals).
-/
lemma NNRealDecimal.floor_of_tail_lt (nd : NNRealDecimal) (N : ℕ)
    (h : (∑' i : ℕ, ((nd.fracPart (i+N) : Digit) : ℝ) * (10:ℝ)^(-((i:ℝ)+N)-1)) < (10:ℝ)^(-(N:ℝ))) :
    ⌊(nd.toNNReal : ℝ) * 10^N⌋₊ = nd.Pnat N := by
  refine Nat.floor_eq_iff ( by positivity ) |>.2 ?_;
  refine' ⟨ _, _ ⟩;
  · convert NNRealDecimal.Pnat_le_val nd N using 1;
  · rw [ NNRealDecimal.val_mul_pow ];
    norm_num [ Real.rpow_neg ] at *;
    rwa [ inv_eq_one_div, lt_div_iff₀ ( by positivity ) ] at h

/-
If all fractional digits from `N` on are 9, then `value · 10^N = Pnat N + 1`.
-/
lemma NNRealDecimal.val_ev9 (nd : NNRealDecimal) (N : ℕ) (h : ∀ i, nd.fracPart (i+N) = 9) :
    (nd.toNNReal : ℝ) * 10^N = (nd.Pnat N : ℝ) + 1 := by
  convert congr_arg ( fun x : ℝ => nd.Pnat N + x * 10 ^ N ) ( show ( ∑' i : ℕ, ( nd.fracPart ( i + N ) : ℝ ) * ( 10 : ℝ ) ^ ( - ( i + N : ℝ ) - 1 ) ) = ( 10 : ℝ ) ^ ( - ( N : ℝ ) ) from ?_ ) using 1;
  · convert NNRealDecimal.val_mul_pow nd N using 1;
  · norm_num [ Real.rpow_neg ];
  · convert NNRealDecimal.tail_all9 nd N h using 1

/-
Partial values shrink by integer division by 10.
-/
lemma NNRealDecimal.Pnat_div (nd : NNRealDecimal) (N : ℕ) : nd.Pnat N = nd.Pnat (N+1) / 10 := by
  have h_key : nd.Pnat (N + 1) = 10 * nd.Pnat N + (nd.fracPart N : ℕ) := by
    simp +arith +decide [ NNRealDecimal.Pnat ];
    simp +decide [ Finset.sum_range_succ, pow_succ', mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
    rw [ add_comm, Finset.sum_congr rfl ] ; intros ; rw [ ← mul_assoc, ← pow_succ', tsub_right_comm, Nat.sub_add_cancel ( Nat.succ_le_of_lt ( Nat.sub_pos_of_lt ( Finset.mem_range.mp ‹_› ) ) ) ];
  grind

/-
Partial value at `N` is obtained from that at `M ≥ N` by dividing out the extra powers of 10.
-/
lemma NNRealDecimal.Pnat_div_pow (nd : NNRealDecimal) {N M : ℕ} (h : N ≤ M) :
    nd.Pnat N = nd.Pnat M / 10^(M-N) := by
  induction h <;> simp_all +decide;
  rw [ Nat.succ_sub ( by linarith ), pow_succ' ];
  rw [ ← Nat.div_div_eq_div_mul, ← NNRealDecimal.Pnat_div ]

/-
Base-10 digit reconstruction of a natural number.
-/
lemma nat_digit_recon (p m : ℕ) :
    p / 10^m * 10^m + ∑ i ∈ Finset.range m, (p / 10^(m-1-i) % 10) * 10^(m-1-i) = p := by
  induction' m with m ih;
  · norm_num;
  · simp_all +decide [ Finset.sum_range_succ', Nat.pow_succ', ← mul_assoc ];
    simp_all +decide [ Nat.sub_sub, add_comm ];
    rw [ show p / ( 10 * 10 ^ m ) = p / 10 ^ m / 10 by rw [ Nat.div_div_eq_div_mul ] ; ring_nf ] ; nlinarith [ Nat.mod_add_div ( p / 10 ^ m ) 10, pow_pos ( by decide : 0 < 10 ) m ]

/-- Two decimals with equal value, neither eventually nine, are equal. -/
lemma NNRealDecimal.eq_of_not_ev9 (nd nd' : NNRealDecimal)
    (hv : (nd.toNNReal : ℝ) = (nd'.toNNReal : ℝ))
    (h1 : ∀ N, ∃ i, nd.fracPart (i+N) ≠ 9)
    (h2 : ∀ N, ∃ i, nd'.fracPart (i+N) ≠ 9) : nd = nd' := by
  apply NNRealDecimal.eq_of_Pnat_eq
  intro N
  have e1 := nd.floor_of_tail_lt N (nd.tail_lt N (h1 N))
  have e2 := nd'.floor_of_tail_lt N (nd'.tail_lt N (h2 N))
  rw [← e1, ← e2, hv]

/-
Two decimals with equal value, both eventually nine, are equal.
-/
lemma NNRealDecimal.eq_of_ev9 (nd nd' : NNRealDecimal)
    (hv : (nd.toNNReal : ℝ) = (nd'.toNNReal : ℝ))
    (h1 : ∃ K, ∀ i, K ≤ i → nd.fracPart i = 9)
    (h2 : ∃ K, ∀ i, K ≤ i → nd'.fracPart i = 9) : nd = nd' := by
  obtain ⟨K1, hK1⟩ := h1
  obtain ⟨K2, hK2⟩ := h2
  set M0 := max K1 K2 with hM0;
  -- First prove `∀ N, M0 ≤ N → nd.Pnat N = nd'.Pnat N`.
  have hPnat_eq : ∀ N, M0 ≤ N → nd.Pnat N = nd'.Pnat N := by
    intros N hN
    have h_eq : (nd.toNNReal : ℝ) * 10^N = (nd.Pnat N : ℝ) + 1 := by
      apply NNRealDecimal.val_ev9;
      exact fun i => hK1 _ ( by linarith [ Nat.le_max_left K1 K2, Nat.le_max_right K1 K2 ] )
    have h_eq' : (nd'.toNNReal : ℝ) * 10^N = (nd'.Pnat N : ℝ) + 1 := by
      exact NNRealDecimal.val_ev9 nd' N fun i => hK2 _ ( by linarith [ Nat.le_max_right K1 K2 ] );
    norm_cast at * ; aesop;
  apply NNRealDecimal.eq_of_Pnat_eq;
  -- Let's choose any $N$ and derive a contradiction if $nd.Pnat N \neq nd'.Pnat N$.
  intro N
  by_contra h_neq;
  exact h_neq <| by have := hPnat_eq ( Max.max N M0 ) ( le_max_right _ _ ) ; have := NNRealDecimal.Pnat_div_pow nd ( show N ≤ Max.max N M0 from le_max_left _ _ ) ; have := NNRealDecimal.Pnat_div_pow nd' ( show N ≤ Max.max N M0 from le_max_left _ _ ) ; aesop;

/-- Explicit decimal builder: the {name}`m`-place base-10 digits of {name}`p` and constant tail digit. -/
def NNRealDecimal.ofNat (p m : ℕ) (tail : Digit) : NNRealDecimal :=
  mk (p / 10^m) (fun i => if i < m then ⟨p / 10^(m-1-i) % 10, Nat.mod_lt _ (by norm_num)⟩ else tail)

/-
Digits of `ofNat` at or beyond position `m` are the tail digit.
-/
lemma NNRealDecimal.ofNat_frac_ge (p m : ℕ) (tail : Digit) (i : ℕ) (hi : m ≤ i) :
    (NNRealDecimal.ofNat p m tail).fracPart i = tail := by
  exact if_neg ( by omega )

/-
The partial value of `ofNat` at position `m` reconstructs `p`.
-/
lemma NNRealDecimal.ofNat_Pnat (p m : ℕ) (tail : Digit) :
    (NNRealDecimal.ofNat p m tail).Pnat m = p := by
  convert nat_digit_recon p m using 1;
  unfold NNRealDecimal.Pnat NNRealDecimal.ofNat; norm_num;
  exact Finset.sum_congr rfl fun x hx => by aesop;

/-
The value of the all-zero-tail builder is `p / 10^m`.
-/
lemma NNRealDecimal.ofNat_val_zero (p m : ℕ) :
    ((NNRealDecimal.ofNat p m 0).toNNReal : ℝ) = (p:ℝ) / (10:ℝ)^m := by
  refine (eq_div_iff (by positivity : (10:ℝ)^m ≠ 0)).mpr ?_
  calc
    ((NNRealDecimal.ofNat p m 0).toNNReal : ℝ) * (10:ℝ)^m
        = ((NNRealDecimal.ofNat p m 0).Pnat m : ℝ) := by
      rw [NNRealDecimal.val_mul_pow, NNRealDecimal.tail_all0 (NNRealDecimal.ofNat p m 0) m
        (fun i => NNRealDecimal.ofNat_frac_ge p m 0 (i+m) (by omega))]
      ring
    _ = (p : ℝ) := by norm_num [NNRealDecimal.ofNat_Pnat]

/-
The value of the all-nine-tail builder (for `p ≥ 1`) is `p / 10^m`.
-/
lemma NNRealDecimal.ofNat_val_nine (p m : ℕ) (hp : 1 ≤ p) :
    ((NNRealDecimal.ofNat (p-1) m 9).toNNReal : ℝ) = (p:ℝ) / (10:ℝ)^m := by
  have h_val_mul_pow : ((NNRealDecimal.ofNat (p - 1) m 9).toNNReal : ℝ) * (10:ℝ)^m = ((p - 1:ℕ) : ℝ) + 1 := by
    have h_val_mul_pow : ((NNRealDecimal.ofNat (p - 1) m 9).toNNReal : ℝ) * (10:ℝ)^m = (NNRealDecimal.ofNat (p - 1) m 9).Pnat m + 1 := by
      convert NNRealDecimal.val_ev9 ( NNRealDecimal.ofNat ( p - 1 ) m 9 ) m _ using 1;
      exact fun i => if_neg ( by omega );
    rw [ h_val_mul_pow, NNRealDecimal.ofNat_Pnat ];
  rw [ eq_div_iff ] <;> first | positivity | cases p <;> aesop;

/-- Helper lemma: for x > 0 and terminating, there are exactly two representations. -/
lemma RealDecimal.not_inj_terminating_pos {x:ℝ} (hx_pos : x > 0) (hx : TerminatingDecimal x) :
    ∃ d₁ d₂:RealDecimal, d₁ ≠ d₂ ∧ ∀ d: RealDecimal, d = x ↔ d = d₁ ∨ d = d₂ := by
  obtain ⟨n, m, hxeq⟩ := hx
  have h10m : (0:ℝ) < (10:ℝ)^m := by positivity
  have hnval : (n:ℝ) = x * (10:ℝ)^m := by
    rw [hxeq]; field_simp
  have hn_pos : (0:ℝ) < (n:ℝ) := by rw [hnval]; positivity
  set p := n.toNat with hp_def
  have hp1 : 1 ≤ p := by
    have : 0 < n := by exact_mod_cast hn_pos
    omega
  have hnp : (n:ℝ) = (p:ℝ) := by
    rw [hp_def]
    have : 0 ≤ n := le_of_lt (by exact_mod_cast hn_pos)
    exact_mod_cast (Int.toNat_of_nonneg this).symm
  have hx_eq_p : x = (p:ℝ) / (10:ℝ)^m := by
    rw [hxeq, hnp]
  -- the two representations
  set da := NNRealDecimal.ofNat p m 0 with hda
  set db := NNRealDecimal.ofNat (p-1) m 9 with hdb
  have hval_da : ((da.toNNReal : ℝ)) = x := by
    rw [hda, NNRealDecimal.ofNat_val_zero, ← hx_eq_p]
  have hval_db : ((db.toNNReal : ℝ)) = x := by
    rw [hdb, NNRealDecimal.ofNat_val_nine p m hp1, ← hx_eq_p]
  -- tail digit behaviour
  have hda_ge : ∀ i, m ≤ i → da.fracPart i = 0 := fun i hi => NNRealDecimal.ofNat_frac_ge p m 0 i hi
  have hdb_ge : ∀ i, m ≤ i → db.fracPart i = 9 := fun i hi => NNRealDecimal.ofNat_frac_ge (p-1) m 9 i hi
  -- distinctness
  have hne_nd : da ≠ db := by
    intro h
    have h0 : da.fracPart m = 0 := hda_ge m (le_refl m)
    have h9 : db.fracPart m = 9 := hdb_ge m (le_refl m)
    rw [h] at h0
    rw [h0] at h9
    exact absurd h9 (by decide)
  refine ⟨RealDecimal.pos da, RealDecimal.pos db, ?_, ?_⟩
  · intro h; exact hne_nd (RealDecimal.pos.injEq da db ▸ h)
  intro d
  constructor
  · intro hdx  -- (d:ℝ) = x
    rcases d with nd | nd
    · -- d = pos nd
      rw [RealDecimal.coe_pos] at hdx
      have hval : (nd.toNNReal : ℝ) = (da.toNNReal : ℝ) := by rw [hdx, hval_da]
      by_cases hev : ∃ K, ∀ i, K ≤ i → nd.fracPart i = 9
      · -- eventually nine ⇒ equals db
        right
        have hvdb : (nd.toNNReal : ℝ) = (db.toNNReal : ℝ) := by rw [hdx, hval_db]
        have : nd = db :=
          NNRealDecimal.eq_of_ev9 nd db hvdb hev ⟨m, fun i hi => hdb_ge i hi⟩
        rw [this]
      · -- not eventually nine ⇒ equals da
        left
        push_neg at hev
        have h1 : ∀ N, ∃ i, nd.fracPart (i+N) ≠ 9 := by
          intro N
          obtain ⟨j, hj, hjne⟩ := hev N
          exact ⟨j - N, by rwa [Nat.sub_add_cancel hj]⟩
        have hda_ne : ∀ N, ∃ i, da.fracPart (i+N) ≠ 9 := by
          intro N
          refine ⟨m, ?_⟩
          rw [hda_ge (m+N) (by omega)]
          decide
        have : nd = da :=
          NNRealDecimal.eq_of_not_ev9 nd da hval h1 hda_ne
        rw [this]
    · -- d = neg nd : impossible since value ≤ 0 < x
      exfalso
      rw [RealDecimal.coe_neg] at hdx
      have : x ≤ 0 := by rw [← hdx]; simp
      linarith
  · intro h
    rcases h with h | h <;> subst h
    · rw [RealDecimal.coe_pos, hval_da]
    · rw [RealDecimal.coe_pos, hval_db]

theorem RealDecimal.not_inj_terminating {x:ℝ} (hx: TerminatingDecimal x) : ∃ d₁ d₂:RealDecimal, d₁ ≠ d₂ ∧ ∀ d: RealDecimal, d = x ↔ d = d₁ ∨ d = d₂ := by
  rcases hx with ⟨n, m, hx_eq⟩
  by_cases hx0 : x = 0
  · subst hx0
    have hpos_val : (pos (mk 0 fun _ : ℕ ↦ (0 : Digit)) : ℝ) = 0 := by simp [toNNReal]
    have hneg_val : (neg (mk 0 fun _ : ℕ ↦ (0 : Digit)) : ℝ) = 0 := by simp [toNNReal]
    have hneq : pos (mk 0 fun _ : ℕ ↦ (0 : Digit)) ≠ neg (mk 0 fun _ : ℕ ↦ (0 : Digit)) := by
      intro h; have := congrArg (fun d : RealDecimal => match d with | RealDecimal.pos _ => 0 | RealDecimal.neg _ => 1) h; simp at this
    refine ⟨pos (mk 0 fun _ : ℕ ↦ (0 : Digit)), neg (mk 0 fun _ : ℕ ↦ (0 : Digit)), hneq, λ d ↦ ?_⟩
    constructor
    · intro hd_eq
      have hd_val0 : (d : ℝ) = 0 := by simpa using hd_eq
      rcases d with (nd | nd)
      · left; apply congrArg pos
        apply (NNRealDecimal.mk.injEq _ _ _ _).mpr
        have hnd_val0 : (nd : NNReal) = 0 := by
          apply NNReal.coe_inj.mp; simpa using hd_val0
        have hsum : (nd.intPart : NNReal) + (tsum fun i : ℕ ↦ ((nd.fracPart i : Digit) : NNReal) * (10 : NNReal) ^ (-(i : ℝ) - 1 : ℝ)) = (0 : NNReal) := by
          simpa [toNNReal] using hnd_val0
        have hint_nonneg : (0 : NNReal) ≤ (nd.intPart : NNReal) := by exact_mod_cast Nat.zero_le _
        have hint_le_zero : (nd.intPart : NNReal) ≤ 0 := by
          calc
            (nd.intPart : NNReal) ≤ (nd.intPart : NNReal) + (tsum fun i : ℕ ↦ ((nd.fracPart i : Digit) : NNReal) * (10 : NNReal) ^ (-(i : ℝ) - 1 : ℝ)) :=
              self_le_add_right _ _
            _ = 0 := hsum
        have hint_zero : (nd.intPart : NNReal) = 0 := le_antisymm hint_le_zero hint_nonneg
        have htsum_zero : (tsum fun i : ℕ ↦ ((nd.fracPart i : Digit) : NNReal) * (10 : NNReal) ^ (-(i : ℝ) - 1 : ℝ)) = 0 := by rw [hint_zero, zero_add] at hsum; exact hsum
        constructor
        · exact_mod_cast hint_zero
        · ext i; exact all_frac_zero_of_tsum_zero nd.toNNReal_conv htsum_zero i
      · right; apply congrArg neg
        apply (NNRealDecimal.mk.injEq _ _ _ _).mpr
        have hnd_nnreal : (nd : NNReal) = 0 := by
          apply NNReal.coe_inj.mp
          have : (nd : ℝ) = 0 := by
            calc
              (nd : ℝ) = -(-(nd : ℝ)) := by simp
              _ = -((neg nd : ℝ)) := rfl
              _ = -(0 : ℝ) := by simp [hd_eq]
              _ = 0 := by simp
          simpa
        have hsum : (nd.intPart : NNReal) + (tsum fun i : ℕ ↦ ((nd.fracPart i : Digit) : NNReal) * (10 : NNReal) ^ (-(i : ℝ) - 1 : ℝ)) = (0 : NNReal) := by
          simpa [toNNReal] using hnd_nnreal
        have hint_nonneg : (0 : NNReal) ≤ (nd.intPart : NNReal) := by exact_mod_cast Nat.zero_le _
        have hint_le_zero : (nd.intPart : NNReal) ≤ 0 := by
          calc
            (nd.intPart : NNReal) ≤ (nd.intPart : NNReal) + (tsum fun i : ℕ ↦ ((nd.fracPart i : Digit) : NNReal) * (10 : NNReal) ^ (-(i : ℝ) - 1 : ℝ)) :=
              self_le_add_right _ _
            _ = 0 := hsum
        have hint_zero : (nd.intPart : NNReal) = 0 := le_antisymm hint_le_zero hint_nonneg
        have htsum_zero : (tsum fun i : ℕ ↦ ((nd.fracPart i : Digit) : NNReal) * (10 : NNReal) ^ (-(i : ℝ) - 1 : ℝ)) = 0 := by rw [hint_zero, zero_add] at hsum; exact hsum
        constructor
        · exact_mod_cast hint_zero
        · ext i; exact all_frac_zero_of_tsum_zero nd.toNNReal_conv htsum_zero i
    · intro h
      rcases h with (h | h) <;> simp [hpos_val, h]
  · by_cases hx_pos : x > 0
    · -- x > 0 case: use the helper lemma
      apply RealDecimal.not_inj_terminating_pos hx_pos
      exact ⟨n, m, hx_eq⟩
    · -- x < 0 case: use x > 0 lemma on -x, then negate
      have hx_neg : x < 0 := by
        refine lt_of_not_ge ?_
        intro h; apply hx0; exact le_antisymm (by linarith) (by linarith)
      set y := -x with hy_def
      have hy_pos : y > 0 := by linarith
      have hy_term : TerminatingDecimal y := by
        use -n, m
        dsimp [y]
        calc
          -x = -((n : ℝ) / (10 : ℝ)^m) := by rw [hx_eq]
          _ = (-(n : ℝ)) / (10 : ℝ)^m := by ring
          _ = ((-n : ℤ) : ℝ) / (10 : ℝ)^m := by simp
      rcases RealDecimal.not_inj_terminating_pos hy_pos hy_term with ⟨d₁', d₂', hneq', huniv'⟩
      -- Negate d₁' and d₂' to get representations of x = -y
      let negD : RealDecimal → RealDecimal := λ d => match d with
        | RealDecimal.pos nd => RealDecimal.neg nd
        | RealDecimal.neg nd => RealDecimal.pos nd
      have hnegD_val : ∀ d : RealDecimal, (negD d : ℝ) = -((d : ℝ)) := by
        intro d; cases d <;> simp [negD]
      have hnegD_invol : ∀ d : RealDecimal, negD (negD d) = d := by
        intro d; cases d <;> simp [negD]
      set d₁ := negD d₁' with hd₁_def
      set d₂ := negD d₂' with hd₂_def
      have hneq : d₁ ≠ d₂ := by
        intro h; apply hneq'
        calc
          d₁' = negD (negD d₁') := by symm; apply hnegD_invol
          _ = negD d₁ := rfl
          _ = negD d₂ := by rw [h]
          _ = negD (negD d₂') := rfl
          _ = d₂' := hnegD_invol d₂'
      have hval1 : (d₁ : ℝ) = x := by
        calc
          (d₁ : ℝ) = -((d₁' : ℝ)) := hnegD_val d₁'
          _ = -(y) := by
            have : (d₁' : ℝ) = y := (huniv' d₁').mpr (Or.inl rfl)
            simp [this]
          _ = x := by simp [hy_def]
      have hval2 : (d₂ : ℝ) = x := by
        calc
          (d₂ : ℝ) = -((d₂' : ℝ)) := hnegD_val d₂'
          _ = -(y) := by
            have : (d₂' : ℝ) = y := (huniv' d₂').mpr (Or.inr rfl)
            simp [this]
          _ = x := by simp [hy_def]
      have huniv : ∀ d : RealDecimal, (d : ℝ) = x ↔ d = d₁ ∨ d = d₂ := by
        intro d; constructor
        · intro hdx
          have hdx' : (negD d : ℝ) = y := by
            calc
              (negD d : ℝ) = -((d : ℝ)) := hnegD_val d
              _ = -(x) := by rw [hdx]
              _ = y := by simp [hy_def]
          rcases (huniv' (negD d)).mp hdx' with (hd₁' | hd₂')
          · left; calc
              d = negD (negD d) := by symm; apply hnegD_invol
              _ = negD d₁' := by rw [hd₁']
              _ = d₁ := rfl
          · right; calc
              d = negD (negD d) := by symm; apply hnegD_invol
              _ = negD d₂' := by rw [hd₂']
              _ = d₂ := rfl
        · intro h
          rcases h with (h | h) <;> simp [h, hval1, hval2]
      exact ⟨d₁, d₂, hneq, huniv⟩

theorem RealDecimal.inj_nonterminating {x:ℝ} (hx: ¬TerminatingDecimal x) : ∃! d:RealDecimal, d = x := by
  obtain ⟨d0, hd0⟩ := RealDecimal.surj x
  refine ⟨d0, hd0.symm, ?_⟩
  have hx0 : x ≠ 0 := by rintro rfl; exact hx ⟨0, 0, by simp⟩
  suffices hkey : ∀ a b : RealDecimal, (a:ℝ) = x → (b:ℝ) = x → a = b by
    intro d hd; exact hkey d d0 hd hd0.symm
  intro a b ha hb
  rcases a with nda | nda <;> rcases b with ndb | ndb
  · -- pos / pos
    rw [RealDecimal.coe_pos] at ha hb
    have hval : (nda.toNNReal : ℝ) = (ndb.toNNReal : ℝ) := by rw [ha, hb]
    have hnt : ¬ TerminatingDecimal (nda.toNNReal : ℝ) := by rw [ha]; exact hx
    exact congrArg RealDecimal.pos (NNRealDecimal.inj_of_nonterm nda ndb hval hnt)
  · -- pos / neg : impossible since values have opposite signs
    exfalso
    rw [RealDecimal.coe_pos] at ha
    rw [RealDecimal.coe_neg] at hb
    have h1 : (0:ℝ) ≤ x := by rw [← ha]; exact (nda.toNNReal).coe_nonneg
    have h2 : x ≤ 0 := by rw [← hb]; simp
    exact hx0 (le_antisymm h2 h1)
  · -- neg / pos : impossible
    exfalso
    rw [RealDecimal.coe_neg] at ha
    rw [RealDecimal.coe_pos] at hb
    have h1 : (0:ℝ) ≤ x := by rw [← hb]; exact (ndb.toNNReal).coe_nonneg
    have h2 : x ≤ 0 := by rw [← ha]; simp
    exact hx0 (le_antisymm h2 h1)
  · -- neg / neg
    rw [RealDecimal.coe_neg] at ha hb
    have hval : (nda.toNNReal : ℝ) = (ndb.toNNReal : ℝ) := by
      have : -(nda.toNNReal : ℝ) = -(ndb.toNNReal : ℝ) := by rw [ha, hb]
      linarith
    have hnt : ¬ TerminatingDecimal (nda.toNNReal : ℝ) := by
      have hxneg : (nda.toNNReal : ℝ) = -x := by rw [← ha]; ring
      rw [hxneg, terminating_neg_iff]; exact hx
    exact congrArg RealDecimal.neg (NNRealDecimal.inj_of_nonterm nda ndb hval hnt)

/-- Exercise B.2.4.  This is Corollary 8.3.4, but the intent is to rewrite the proof using the decimal system. -/
example : Uncountable ℝ := by infer_instance


end AppendixB
