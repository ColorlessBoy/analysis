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
            · exfalso; linarith [hpos i, hpow]
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

/-- Helper lemma: for x > 0 and terminating, there are exactly two representations. -/
lemma RealDecimal.not_inj_terminating_pos {x:ℝ} (hx_pos : x > 0) (hx : TerminatingDecimal x) :
    ∃ d₁ d₂:RealDecimal, d₁ ≠ d₂ ∧ ∀ d: RealDecimal, d = x ↔ d = d₁ ∨ d = d₂ := by
  sorry

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
        have hint_zero : (nd.intPart : NNReal) = 0 := by linarith
        have htsum_zero : (tsum fun i : ℕ ↦ ((nd.fracPart i : Digit) : NNReal) * (10 : NNReal) ^ (-(i : ℝ) - 1 : ℝ)) = 0 := by linarith
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
        have hint_zero : (nd.intPart : NNReal) = 0 := by linarith
        have htsum_zero : (tsum fun i : ℕ ↦ ((nd.fracPart i : Digit) : NNReal) * (10 : NNReal) ^ (-(i : ℝ) - 1 : ℝ)) = 0 := by linarith
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

theorem RealDecimal.inj_nonterminating {x:ℝ} (hx: ¬TerminatingDecimal x) : ∃! d:RealDecimal, d = x := by sorry

/-- Exercise B.2.4.  This is Corollary 8.3.4, but the intent is to rewrite the proof using the decimal system. -/
example : Uncountable ℝ := by sorry


end AppendixB
