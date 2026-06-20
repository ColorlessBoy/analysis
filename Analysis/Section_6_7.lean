import Mathlib.Tactic
import Analysis.Section_5_epilogue
import Analysis.Section_6_6

/-!
# Analysis I, Section 6.7: Real exponentiation, part II

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Real exponentiation.

Because the Chapter 5 reals have been deprecated in favor of the Mathlib reals, and Mathlib real
exponentiation is defined without first going through rational exponentiation, we will adopt a
somewhat awkward compromise, in that we will initially accept the Mathlib exponentiation operation
(with all its API) when the exponent is a rational, and use this to define a notion of real
exponentiation which in the epilogue to this chapter we will show is identical to the Mathlib operation.
-/

namespace Chapter6

open Sequence Real Filter

/-- Helper lemma for Lemma 6.7.1 when x ≥ 1 -/
lemma ratPow_continuous_ge_one {x α:ℝ} (hx: x > 0) (hx1: 1 < x) {q: ℕ → ℚ}
 (hq: ((fun n ↦ (q n:ℝ)):Sequence).TendsTo α) :
 ((fun n ↦ x^(q n:ℝ)):Sequence).Convergent := by
  choose M hM hbound using bounded_of_convergent ⟨ α, hq ⟩
  have h' : 1 ≤ x := by linarith
  rw [←Cauchy_iff_convergent]
  intro ε hε
  choose K hK hclose using lim_of_roots hx (ε*x^(-M)) (by positivity)
  choose N hN hq using IsCauchy.convergent ⟨ α, hq ⟩ (1/(K+1:ℝ)) (by positivity)
  simp [CloseSeq, dist_eq] at hclose hK hN
  lift N to ℕ using hN
  lift K to ℕ using hK
  specialize hclose K (by simp) (by simp); simp at hclose
  use N, by simp
  intro n hn m hm; simp at hn hm
  specialize hq n (by simp [hn]) m (by simp [hm])
  simp [Close, hn, hm, dist_eq] at hq ⊢
  have : 0 ≤ (N:ℤ) := by simp
  lift n to ℕ using by linarith
  lift m to ℕ using by linarith
  simp at hn hm hq ⊢
  obtain hqq | hqq := le_or_gt (q m) (q n)
  . replace : x^(q m:ℝ) ≤ x^(q n:ℝ) := by rw [rpow_le_rpow_left_iff hx1]; norm_cast
    rw [abs_of_nonneg (by linarith)]
    calc
      _ = x^(q m:ℝ) * (x^(q n - q m:ℝ) - 1) := by ring_nf; rw [←rpow_add (by linarith)]; ring_nf
      _ ≤ x^M * (x^(1/(K+1:ℝ)) - 1) := by
        gcongr <;> try exact h'
        . rw [sub_nonneg]; apply one_le_rpow h'; norm_cast; linarith
        . specialize hbound m; simp_all [abs_le']
        grind [abs_le']
      _ ≤ x^M * (ε * x^(-M)) := by gcongr; grind [abs_le']
      _ = ε := by rw [mul_comm, mul_assoc, ←rpow_add]; simp; linarith
  . replace : x^(q n:ℝ) ≤ x^(q m:ℝ) := by rw [rpow_le_rpow_left_iff hx1]; norm_cast; linarith
    rw [abs_of_nonpos (by linarith)]
    calc
      _ = x^(q n:ℝ) * (x^(q m - q n:ℝ) - 1) := by ring_nf; rw [←rpow_add]; ring_nf; positivity
      _ ≤ x^M * (x^(1/(K+1:ℝ)) - 1) := by
        gcongr <;> try exact h'
        . rw [sub_nonneg]; apply one_le_rpow h'; norm_cast; linarith
        . specialize hbound n; simp_all [abs_le']
        grind [abs_le']
      _ ≤ x^M * (ε * x^(-M)) := by gcongr; simp_all [abs_le']
      _ = ε := by rw [mul_comm, mul_assoc, ←rpow_add]; simp; positivity

/-- Lemma 6.7.1 (Continuity of exponentiation) -/
lemma ratPow_continuous {x α:ℝ} (hx: x > 0) {q: ℕ → ℚ}
 (hq: ((fun n ↦ (q n:ℝ)):Sequence).TendsTo α) :
 ((fun n ↦ x^(q n:ℝ)):Sequence).Convergent := by
  choose M hM hbound using bounded_of_convergent ⟨ α, hq ⟩
  obtain h | rfl | h := lt_trichotomy x 1
  . -- x < 1
    have hy_gt_one : 1 < 1/x := one_lt_one_div hx h
    have ha_conv : ((fun n ↦ (1/x : ℝ)^(q n:ℝ)):Sequence).Convergent :=
      ratPow_continuous_ge_one (by positivity) hy_gt_one hq
    set a := ((fun n ↦ (1/x : ℝ)^(q n:ℝ)):Sequence) with ha
    have ha_pos_lower : ∀ n : ℕ, a (n : ℤ) ≥ (1/x : ℝ)^(-M : ℝ) := by
      intro n
      dsimp [a]
      have hbound_n : |(q n : ℝ)| ≤ M := hbound n
      have hq_ge : (q n : ℝ) ≥ -M := by linarith [abs_le'.mp hbound_n]
      have htemp : (1/x : ℝ)^(-M : ℝ) ≤ (1/x : ℝ)^(q n : ℝ) :=
        (rpow_le_rpow_left_iff hy_gt_one).mpr (by simpa using hq_ge)
      simpa using htemp
    have ha_lim_ne_zero : lim a ≠ 0 := by
      intro hzero
      have hlim : a.TendsTo 0 := by
        simpa [hzero] using Sequence.lim_def ha_conv
      rw [Sequence.tendsTo_iff] at hlim
      have hpos : (1/x : ℝ)^(-M : ℝ) > 0 := by positivity
      rcases hlim ((1/x : ℝ)^(-M : ℝ)/2) (by positivity) with ⟨N, hN⟩
      set n := max (N : ℤ) 0 with hn_def
      have hn_ge_N : n ≥ N := by simp [hn_def]
      have hn_ge_0 : n ≥ 0 := by simp [hn_def]
      have hN_val : |a n| ≤ (1/x : ℝ)^(-M : ℝ)/2 := by
        simpa [sub_zero] using hN n hn_ge_N
      have ha_val_pos : a n ≥ (1/x : ℝ)^(-M : ℝ) := by
        have : a n = a (Int.toNat n : ℤ) := by simp [hn_ge_0]
        rw [this]
        exact ha_pos_lower (Int.toNat n)
      have h_abs_pos : a n ≥ 0 := by linarith
      have : |a n| = a n := abs_of_nonneg h_abs_pos
      rw [this] at hN_val
      linarith
    have hx_eq : ((fun n ↦ x^(q n:ℝ)):Sequence) = a⁻¹ := by
      apply Sequence.ext
      · simp [Inv.inv, a]
      · ext i
        by_cases hi : i ≥ (0 : ℤ)
        · simp [hi, a, Real.inv_rpow hx.le]
        · simp [hi, a]
    have h_inv_conv : (a⁻¹).Convergent := (Sequence.lim_inv ha_conv ha_lim_ne_zero).1
    simpa [hx_eq]
  . simp; exact ⟨ 1, lim_of_const 1 ⟩
  . exact ratPow_continuous_ge_one hx h hq


lemma ratPow_lim_uniq {x α:ℝ} (hx: x > 0) {q q': ℕ → ℚ}
 (hq: ((fun n ↦ (q n:ℝ)):Sequence).TendsTo α)
 (hq': ((fun n ↦ (q' n:ℝ)):Sequence).TendsTo α) :
 lim ((fun n ↦ x^(q n:ℝ)):Sequence) = lim ((fun n ↦ x^(q' n:ℝ)):Sequence) := by
 -- This proof is written to follow the structure of the original text.
  set r := q - q'
  suffices : (fun n ↦ x^(r n:ℝ):Sequence).TendsTo 1
  . rw [←mul_one (lim ((fun n ↦ x^(q' n:ℝ)):Sequence))]
    rw [lim_eq] at this
    convert (lim_mul (b := (fun n ↦ x^(r n:ℝ):Sequence)) (ratPow_continuous hx hq') this.1).2
    . rw [mul_coe]
      rcongr _ n
      rw [←rpow_add (by linarith)]
      simp [r]
    exact this.2.symm
  intro ε hε
  have h1 := lim_of_roots hx
  have h2 := tendsTo_inv h1 (by norm_num)
  choose K1 hK1 h3 using h1 ε hε
  choose K2 hK2 h4 using h2 ε hε
  simp [Inv.inv] at hK1 hK2
  lift K1 to ℕ using hK1; lift K2 to ℕ using hK2
  simp [inv_coe] at h4
  set K := max K1 K2
  have hr := tendsTo_sub hq hq'
  rw [sub_coe] at hr
  choose N hN hr using hr (1 / (K + 1:ℝ)) (by positivity)
  refine ⟨ N, by simp_all, ?_ ⟩
  intro n hn; simp at hn
  specialize h3 K (by simp [K]); specialize h4 K (by simp [K])
  simp [hn, dist_eq, abs_le', K, -Nat.cast_max] at h3 h4 ⊢
  specialize hr n (by simp [hn])
  simp [Close, hn, abs_le'] at hr
  obtain h | rfl | h := lt_trichotomy x 1
  . -- x < 1: rpow is decreasing, so inequalities reverse
    have hx_le_one : x ≤ 1 := by linarith
    have h_rn_eq : (r n.toNat : ℝ) = (q n.toNat : ℝ) - (q' n.toNat : ℝ) := by simp [r]
    have h_rn_le_invK : (r n.toNat : ℝ) ≤ ((K : ℝ) + 1)⁻¹ := by
      rw [h_rn_eq]; linarith [hr.1]
    have h_neg_invK_le_rn : -((K : ℝ) + 1)⁻¹ ≤ (r n.toNat : ℝ) := by
      rw [h_rn_eq]; linarith [hr.2]
    have h_lower : x ^ ((K : ℝ) + 1)⁻¹ ≤ x ^ (r n.toNat : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hx hx_le_one h_rn_le_invK
    have h_upper : x ^ (r n.toNat : ℝ) ≤ (x ^ ((K : ℝ) + 1)⁻¹)⁻¹ := by
      calc
        x ^ (r n.toNat : ℝ) ≤ x ^ (-((K : ℝ) + 1)⁻¹) :=
          Real.rpow_le_rpow_of_exponent_ge hx hx_le_one h_neg_invK_le_rn
        _ = (x ^ ((K : ℝ) + 1)⁻¹)⁻¹ := by rw [Real.rpow_neg (by positivity : 0 ≤ x)]
    constructor
    · calc
        x ^ (r n.toNat : ℝ) ≤ (x ^ ((K : ℝ) + 1)⁻¹)⁻¹ := h_upper
        _ ≤ ε + 1 := h4.1
    · have h3_lower : 1 ≤ ε + x ^ ((K : ℝ) + 1)⁻¹ := h3.2
      calc
        1 ≤ ε + x ^ ((K : ℝ) + 1)⁻¹ := h3_lower
        _ ≤ ε + x ^ (r n.toNat : ℝ) := by
          have := add_le_add_right h_lower ε
          -- this : x^A + ε ≤ x^B + ε
          -- goal: ε + x^A ≤ ε + x^B
          -- by commutativity these are equivalent
          simpa [add_comm] using this
  . simp; linarith
  have h5 : x ^ (r n.toNat:ℝ) ≤ x^(K + 1:ℝ)⁻¹ := by gcongr; linarith; simp_all [r]
  have h6 : (x^(K + 1:ℝ)⁻¹)⁻¹ ≤ x ^ (r n.toNat:ℝ) := by
    rw [←rpow_neg (by linarith)]
    gcongr; linarith
    simp [r]; linarith
  split_ands <;> linarith

theorem Real.eq_lim_of_rat (α:ℝ) : ∃ q: ℕ → ℚ, ((fun n ↦ (q n:ℝ)):Sequence).TendsTo α := by
  choose q hcauchy hLIM using (Chapter5.Real.equivR.symm α).eq_lim; use q
  apply lim_eq_LIM at hcauchy
  simp only [←hLIM, Equiv.apply_symm_apply] at hcauchy
  convert hcauchy; aesop

/-- Definition 6.7.2 (Exponentiation to a real exponent) -/
noncomputable abbrev Real.rpow (x:ℝ) (α:ℝ) :ℝ := lim ((fun n ↦ x^((eq_lim_of_rat α).choose n:ℝ)):Sequence)

lemma Real.rpow_eq_lim_ratPow {x α:ℝ} (hx: x > 0) {q: ℕ → ℚ}
 (hq: ((fun n ↦ (q n:ℝ)):Sequence).TendsTo α) :
 rpow x α = lim ((fun n ↦ x^(q n:ℝ)):Sequence) :=
   ratPow_lim_uniq hx (eq_lim_of_rat α).choose_spec hq

lemma Real.ratPow_tendsto_rpow {x α:ℝ} (hx: x > 0) {q: ℕ → ℚ}
 (hq: ((fun n ↦ (q n:ℝ)):Sequence).TendsTo α) :
 ((fun n ↦ x^(q n:ℝ)):Sequence).TendsTo (rpow x α) := by
  rw [lim_eq]
  exact ⟨ ratPow_continuous hx hq, (rpow_eq_lim_ratPow hx hq).symm ⟩

lemma Real.rpow_of_rat_eq_ratPow {x:ℝ} (hx: x > 0) {q: ℚ} :
  rpow x (q:ℝ) = x^(q:ℝ) := by
  convert rpow_eq_lim_ratPow hx (α := q) (lim_of_const _)
  exact (lim_eq.mp (lim_of_const _)).2.symm

/-- Bridge lemma: Chapter6's sequence convergence ↔ Mathlib's filter convergence -/
lemma tendsto_iff_tendsto_nhds (a : ℕ → ℝ) (L : ℝ) :
    ((a : Sequence).TendsTo L) ↔ atTop.Tendsto a (nhds L) := by
  constructor
  · intro h
    rw [Metric.tendsto_atTop]
    rw [Sequence.tendsTo_iff] at h
    intro ε hε
    have hε2 : ε / 2 > 0 := by linarith
    rcases h (ε / 2) hε2 with ⟨N, hN⟩
    refine ⟨max 0 N.toNat, ?_⟩
    intro n hn
    have hnpos : (n : ℤ) ≥ 0 := by exact_mod_cast (Nat.zero_le n)
    have hnN : (n : ℤ) ≥ N := by
      have hmax : (n : ℤ) ≥ (max 0 (N.toNat : ℤ) : ℤ) := by exact_mod_cast hn
      omega
    have hval : ((a : Sequence)) (n : ℤ) = a n := by simp
    have hN_val : |((a : Sequence)) (n : ℤ) - L| ≤ ε / 2 := hN (n : ℤ) hnN
    rw [hval] at hN_val
    have : |a n - L| < ε := by
      have : |a n - L| ≤ ε / 2 := hN_val
      linarith
    simpa [Real.dist_eq]
  · intro h
    rw [Sequence.tendsTo_iff]
    rw [Metric.tendsto_atTop] at h
    intro ε hε
    rcases h ε hε with ⟨N, hN⟩
    refine ⟨(N : ℤ), ?_⟩
    intro n hn
    have hnpos : n ≥ 0 := by omega
    have hnN_nat : n.toNat ≥ N := by
      have : (n : ℤ) ≥ (N : ℤ) := hn
      omega
    have hval : ((a : Sequence)) n = a n.toNat := by simp [hnpos]
    rw [hval]
    have hN_val : |a n.toNat - L| < ε := hN n.toNat hnN_nat
    have : |a n.toNat - L| ≤ ε := by linarith
    simpa [Real.dist_eq]

/-- Identification with Mathlib exponentiation -/
theorem Real.rpow_eq_rpow {x : ℝ} (hx : x > 0) (α : ℝ) : rpow x α = x ^ α := by
  have h_cont : ContinuousAt (fun (t : ℝ) ↦ x ^ t) α :=
    Real.continuousAt_const_rpow (a := x) (b := α) (by linarith : x ≠ 0)
  set q := (eq_lim_of_rat α).choose with hq
  have hq_spec : ((fun n : ℕ ↦ (q n : ℝ)) : Sequence).TendsTo α :=
    (eq_lim_of_rat α).choose_spec
  have hq_tendsto : atTop.Tendsto (fun (n : ℕ) ↦ (q n : ℝ)) (nhds α) :=
    (tendsto_iff_tendsto_nhds (fun n : ℕ ↦ (q n : ℝ)) α).mp hq_spec
  have h_pow_tendsto : atTop.Tendsto (fun (n : ℕ) ↦ x ^ ((q n : ℝ))) (nhds (x ^ α)) :=
    h_cont.tendsto.comp hq_tendsto
  have h_chapter_tendsto : ((fun n : ℕ ↦ x ^ ((q n : ℝ))) : Sequence).TendsTo (rpow x α) := by
    simpa [Real.rpow, hq] using Sequence.lim_def (ratPow_continuous hx (eq_lim_of_rat α).choose_spec)
  have h_chapter_tendsto_metric : atTop.Tendsto (fun (n : ℕ) ↦ x ^ ((q n : ℝ))) (nhds (rpow x α)) :=
    (tendsto_iff_tendsto_nhds (fun n : ℕ ↦ x ^ ((q n : ℝ))) (rpow x α)).mp h_chapter_tendsto
  exact (tendsto_nhds_unique h_pow_tendsto h_chapter_tendsto_metric).symm

/-- Proposition 6.7.3(a) / Exercise 6.7.1 -/
theorem Real.ratPow_nonneg {x:ℝ} (hx: x > 0) (q:ℝ) : rpow x q ≥ 0 := by
  rw [Real.rpow_eq_rpow hx q]
  exact Real.rpow_nonneg hx.le q

/-- Proposition 6.7.3(b) -/
theorem Real.ratPow_add {x:ℝ} (hx: x > 0) (q r:ℝ) : rpow x (q+r) = rpow x q * rpow x r := by
  choose q' hq' using eq_lim_of_rat q
  choose r' hr' using eq_lim_of_rat r
  have hq'r' := tendsTo_add hq' hr'
  rw [add_coe] at hq'r'
  convert_to ((fun n ↦ ((q' n + r' n:ℚ):ℝ)):Sequence).TendsTo (q + r) at hq'r'
  . aesop
  have h1 := ratPow_continuous hx hq'
  have h2 := ratPow_continuous hx hr'
  rw [rpow_eq_lim_ratPow hx hq', rpow_eq_lim_ratPow hx hr', rpow_eq_lim_ratPow hx hq'r', ←(lim_mul h1 h2).2, mul_coe]
  rcongr n; rw [←rpow_add]; simp; linarith

/-- Proposition 6.7.3(b) / Exercise 6.7.1 -/
theorem Real.ratPow_ratPow {x:ℝ} (hx: x > 0) (q r:ℝ) : rpow (rpow x q) r = rpow x (q*r) := by
  have hpos : rpow x q > 0 := by
    rw [Real.rpow_eq_rpow hx q]
    exact Real.rpow_pos_of_pos hx q
  calc
    rpow (rpow x q) r = (rpow x q) ^ r := Real.rpow_eq_rpow hpos r
    _ = (x ^ q) ^ r := by rw [Real.rpow_eq_rpow hx q]
    _ = x ^ (q * r) := by rw [Real.rpow_mul hx.le q r]
    _ = rpow x (q * r) := (Real.rpow_eq_rpow hx (q * r)).symm

/-- Proposition 6.7.3(c) / Exercise 6.7.1 -/
theorem Real.ratPow_neg {x:ℝ} (hx: x > 0) (q:ℝ) : rpow x (-q) = 1 / rpow x q := by
  calc
    rpow x (-q) = x ^ (-q) := Real.rpow_eq_rpow hx (-q)
    _ = (x ^ q)⁻¹ := by rw [Real.rpow_neg hx.le q]
    _ = 1 / (x ^ q) := by field_simp
    _ = 1 / rpow x q := by rw [Real.rpow_eq_rpow hx q]

/-- Proposition 6.7.3(d) / Exercise 6.7.1 -/
theorem Real.ratPow_mono {x y:ℝ} (hx: x > 0) (hy: y > 0) {q:ℝ} (h: q > 0) : x > y ↔ rpow x q > rpow y q := by
  rw [Real.rpow_eq_rpow hx q, Real.rpow_eq_rpow hy q]
  constructor
  · intro hxy; exact Real.rpow_lt_rpow hy.le hxy h
  · intro hxy; by_contra! hle
    have hxle_y : x ≤ y := hle
    have hpow_le : x ^ q ≤ y ^ q := Real.rpow_le_rpow hx.le hxle_y h.le
    linarith

/-- Proposition 6.7.3(e) / Exercise 6.7.1 -/
theorem Real.ratPow_mono_of_gt_one {x:ℝ} (hx: x > 1) {q r:ℝ} : rpow x q > rpow x r ↔ q > r := by
  have hxpos : x > 0 := by linarith
  rw [Real.rpow_eq_rpow hxpos q, Real.rpow_eq_rpow hxpos r]
  constructor
  · intro h; by_contra! hle; have := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ x) hle; linarith
  · intro h; exact Real.rpow_lt_rpow_of_exponent_lt hx h

/-- Proposition 6.7.3(e) / Exercise 6.7.1 -/
theorem Real.ratPow_mono_of_lt_one {x:ℝ} (hx0: 0 < x) (hx: x < 1) {q r:ℝ} : rpow x q > rpow x r ↔ q < r := by
  rw [Real.rpow_eq_rpow hx0 q, Real.rpow_eq_rpow hx0 r]
  constructor
  · intro h; by_contra! hle; have := Real.rpow_le_rpow_of_exponent_ge hx0 (by linarith) hle; linarith
  · intro h; exact Real.rpow_lt_rpow_of_exponent_gt hx0 hx h

/-- Proposition 6.7.3(f) / Exercise 6.7.1 -/
theorem Real.ratPow_mul {x y:ℝ} (hx: x > 0) (hy: y > 0) (q:ℝ) : rpow (x*y) q = rpow x q * rpow y q := by
  rw [Real.rpow_eq_rpow (mul_pos hx hy) q, Real.rpow_eq_rpow hx q, Real.rpow_eq_rpow hy q, Real.mul_rpow hx.le hy.le]

end Chapter6
