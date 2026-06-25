import Mathlib.Tactic
import Mathlib.Algebra.Field.Power

/-!
# Analysis I, Section 7.2: Infinite series

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Formal series and their limits.
- Absolute convergence; basic series laws.

-/

namespace Chapter7

open BigOperators

/--
  Definition 7.2.1 (Formal infinite series). This is similar to Chapter 6 sequence, but is
  manipulated differently. As with Chapter 5, we will start series from 0 by default.
-/
@[ext]
structure Series where
  m : ℤ
  seq : ℤ → ℝ
  vanish : ∀ n < m, seq n = 0

/-- Functions from ℕ to ℝ can be thought of as series. -/
instance Series.instCoe : Coe (ℕ → ℝ) Series where
  coe := fun a ↦ {
    m := 0
    seq n := if n ≥ 0 then a n.toNat else 0
    vanish := by grind
  }

@[simp]
theorem Series.eval_coe (a: ℕ → ℝ) (n: ℕ) : (a: Series).seq n = a n := by simp

abbrev Series.mk' {m:ℤ} (a: { n // n ≥ m } → ℝ) : Series where
  m := m
  seq n := if h : n ≥ m then a ⟨n, h⟩ else 0
  vanish := by grind

theorem Series.eval_mk' {m:ℤ} (a : { n // n ≥ m } → ℝ) {n : ℤ} (h:n ≥ m) :
    (Series.mk' a).seq n = a ⟨ n, h ⟩ := by simp [h]

/-- Definition 7.2.2 (Convergence of series) -/
noncomputable abbrev Series.partial (s : Series) (N:ℤ) : ℝ := ∑ n ∈ Finset.Icc s.m N, s.seq n

theorem Series.partial_succ (s : Series) {N:ℤ} (h: N ≥ s.m-1) : s.partial (N+1) = s.partial N + s.seq (N+1) := by
  unfold Series.partial
  rw [add_comm (s.partial N) _]
  convert Finset.sum_insert (show N+1 ∉ Finset.Icc s.m N by simp)
  symm; apply Finset.insert_Icc_right_eq_Icc_add_one; linarith

theorem Series.partial_of_lt {s : Series} {N:ℤ} (h: N < s.m) : s.partial N = 0 := by
  unfold Series.partial
  rw [Finset.sum_eq_zero]
  intro n hn; simp at hn; grind

abbrev Series.convergesTo (s : Series) (L:ℝ) : Prop := Filter.atTop.Tendsto (s.partial) (nhds L)

abbrev Series.converges (s : Series) : Prop := ∃ L, s.convergesTo L

abbrev Series.diverges (s : Series) : Prop := ¬s.converges

open Classical in
noncomputable abbrev Series.sum (s : Series) : ℝ := if h : s.converges then h.choose else 0

theorem Series.converges_of_convergesTo {s : Series} {L:ℝ} (h: s.convergesTo L) :
    s.converges := by use L

/-- Remark 7.2.3 -/
theorem Series.sum_of_converges {s : Series} {L:ℝ} (h: s.convergesTo L) : s.sum = L := by
  simp [sum, converges_of_convergesTo h]
  exact tendsto_nhds_unique ((converges_of_convergesTo h).choose_spec) h

theorem Series.convergesTo_uniq {s : Series} {L L':ℝ} (h: s.convergesTo L) (h': s.convergesTo L') :
    L = L' := tendsto_nhds_unique h h'

theorem Series.convergesTo_sum {s : Series} (h: s.converges) : s.convergesTo s.sum := by
  simp [sum, h]; exact h.choose_spec

/-- Example 7.2.4 -/
noncomputable abbrev Series.example_7_2_4 := mk' (m := 1) (fun n ↦ (2:ℝ)^(-n:ℤ))

theorem Series.example_7_2_4a {N:ℤ} (hN: N ≥ 1) : example_7_2_4.partial N = 1 - (2:ℝ)^(-N) := by
  have hm : example_7_2_4.m = 1 := rfl
  have hpartial0 : example_7_2_4.partial (0 : ℤ) = 0 := by
    apply partial_of_lt; rw [hm]; omega
  refine Int.le_induction ?base ?step N hN
  · have hseq1 : example_7_2_4.seq 1 = (2:ℝ)^(-(1 : ℤ)) := by
      rw [Series.eval_mk' (fun n : { n // n ≥ 1 } ↦ (2:ℝ)^(-(n:ℤ))) (show (1 : ℤ) ≥ 1 from by omega)]
    calc
      example_7_2_4.partial 1 = example_7_2_4.partial ((0 : ℤ) + 1) := by norm_num
      _ = example_7_2_4.partial (0 : ℤ) + example_7_2_4.seq ((0 : ℤ) + 1) := by
        rw [partial_succ example_7_2_4 (by rw [hm]; omega)]
      _ = example_7_2_4.partial (0 : ℤ) + example_7_2_4.seq 1 := by norm_num
      _ = 0 + example_7_2_4.seq 1 := by rw [hpartial0]
      _ = example_7_2_4.seq 1 := by simp
      _ = (2:ℝ)^(-(1 : ℤ)) := by rw [hseq1]
      _ = 1 - (2:ℝ)^(-(1 : ℤ)) := by norm_num
  · intro k hk IH
    have hseq : example_7_2_4.seq (k+1 : ℤ) = (2:ℝ)^(-(k+1 : ℤ)) := by
      rw [Series.eval_mk' (fun n : { n // n ≥ 1 } ↦ (2:ℝ)^(-(n:ℤ))) (show (k+1 : ℤ) ≥ 1 from by omega)]
    have h_exp : (-k : ℤ) = (-(k+1 : ℤ) + (1 : ℤ)) := by omega
    have hcalc' : (2:ℝ)^(-k : ℤ) = 2 * (2:ℝ)^(-(k+1 : ℤ)) := by
      calc
        (2:ℝ)^(-k : ℤ) = (2:ℝ)^(-(k+1 : ℤ) + (1 : ℤ)) := by rw [h_exp]
        _ = (2:ℝ)^(-(k+1 : ℤ)) * (2:ℝ)^(1 : ℤ) := by
          rw [zpow_add₀ (by norm_num : (2:ℝ) ≠ 0) (-(k+1 : ℤ)) (1 : ℤ)]
        _ = (2:ℝ)^(-(k+1 : ℤ)) * 2 := by norm_num
        _ = 2 * (2:ℝ)^(-(k+1 : ℤ)) := by ring
    calc
      example_7_2_4.partial (k + 1) = example_7_2_4.partial k + example_7_2_4.seq (k + 1) := by
        rw [partial_succ example_7_2_4 (by rw [hm]; omega)]
      _ = (1 - (2:ℝ)^(-k : ℤ)) + example_7_2_4.seq (k + 1) := by rw [IH]
      _ = (1 - (2:ℝ)^(-k : ℤ)) + (2:ℝ)^(-(k + 1 : ℤ)) := by rw [hseq]
      _ = 1 - (2:ℝ)^(-(k + 1 : ℤ)) := by
        calc
          (1 - (2:ℝ)^(-k : ℤ)) + (2:ℝ)^(-(k + 1 : ℤ)) = 1 - ((2:ℝ)^(-k : ℤ) - (2:ℝ)^(-(k + 1 : ℤ))) := by ring
          _ = 1 - ((2 * (2:ℝ)^(-(k + 1 : ℤ))) - (2:ℝ)^(-(k + 1 : ℤ))) := by rw [hcalc']
          _ = 1 - (2:ℝ)^(-(k + 1 : ℤ)) := by ring

theorem Series.example_7_2_4b : example_7_2_4.convergesTo 1 := by
  unfold Series.convergesTo
  have h_eq : example_7_2_4.partial =ᶠ[Filter.atTop] (fun N : ℤ => 1 - (2:ℝ)^(-N : ℤ)) := by
    apply Filter.eventually_atTop.mpr
    refine ⟨1, λ N hN => ?_⟩
    rw [example_7_2_4a hN]
  apply Filter.Tendsto.congr' h_eq.symm
  have hlim : Filter.atTop.Tendsto (fun (N : ℤ) => (2:ℝ)^(-N : ℤ)) (nhds (0 : ℝ)) := by
    have h_nat : Filter.atTop.Tendsto (fun (n : ℕ) => ((1/2 : ℝ) ^ n)) (nhds (0 : ℝ)) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    refine Metric.tendsto_nhds.mpr ?_
    intro ε hε
    have h_nat_eventually : ∀ᶠ (n : ℕ) in Filter.atTop, dist (((1/2 : ℝ) ^ n)) (0 : ℝ) < ε :=
      (Metric.tendsto_nhds.mp h_nat) ε hε
    rcases (Filter.eventually_atTop.mp h_nat_eventually) with ⟨N, hN⟩
    apply Filter.eventually_atTop.mpr
    refine ⟨(N : ℤ), λ z hz => ?_⟩
    have hz_nonneg : (0 : ℤ) ≤ z := by
      have h0z : (0 : ℤ) ≤ (N : ℤ) := by exact_mod_cast Nat.zero_le _
      linarith
    have hN_val : ((1/2 : ℝ) ^ (z.toNat : ℕ)) < ε := by
      have hz_nat : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz_nonneg
      have hN_z : (N : ℤ) ≤ (z.toNat : ℤ) := by
        calc
          (N : ℤ) ≤ z := hz
          _ = (z.toNat : ℤ) := hz_nat.symm
      have h := hN z.toNat (mod_cast hN_z)
      rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity : 0 < ((1/2 : ℝ) ^ (z.toNat : ℕ)))] at h
      exact h
    have hcalc : (2:ℝ)^(-z : ℤ) = ((1/2 : ℝ) ^ (z.toNat : ℕ)) := by
      calc
        (2:ℝ)^(-z : ℤ) = ((2:ℝ)^(z : ℤ))⁻¹ := by rw [zpow_neg]
        _ = (2⁻¹ : ℝ) ^ (z : ℤ) := by rw [inv_zpow]
        _ = ((1/2 : ℝ) ^ (z : ℤ)) := by norm_num
        _ = ((1/2 : ℝ) ^ ((z.toNat : ℕ) : ℤ)) := by
          simp [Int.toNat_of_nonneg hz_nonneg]
        _ = ((1/2 : ℝ) ^ (z.toNat : ℕ)) := by rw [zpow_natCast]
    rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity : 0 < (2:ℝ)^(-z : ℤ)), hcalc]
    exact hN_val
  simpa [sub_eq_add_neg] using (tendsto_const_nhds.sub hlim)

theorem Series.example_7_2_4c : example_7_2_4.sum = 1 := by
  exact sum_of_converges example_7_2_4b

noncomputable abbrev Series.example_7_2_4' := mk' (m := 1) (fun n ↦ (2:ℝ)^(n:ℤ))

theorem Series.example_7_2_4'a {N:ℤ} (hN: N ≥ 1) : example_7_2_4'.partial N = (2:ℝ)^(N+1) - 2 := by
  have hm : example_7_2_4'.m = 1 := rfl
  have hpartial0 : example_7_2_4'.partial (0 : ℤ) = 0 := by
    apply partial_of_lt; rw [hm]; omega
  refine Int.le_induction ?base ?step N hN
  · have hseq1 : example_7_2_4'.seq 1 = (2:ℝ)^(1 : ℤ) := by
      rw [Series.eval_mk' (fun n : { n // n ≥ 1 } ↦ (2:ℝ)^(n:ℤ)) (show (1 : ℤ) ≥ 1 from by omega)]
    calc
      example_7_2_4'.partial 1 = example_7_2_4'.partial ((0 : ℤ) + 1) := by norm_num
      _ = example_7_2_4'.partial (0 : ℤ) + example_7_2_4'.seq ((0 : ℤ) + 1) := by
        rw [partial_succ example_7_2_4' (by rw [hm]; omega)]
      _ = example_7_2_4'.partial (0 : ℤ) + example_7_2_4'.seq 1 := by norm_num
      _ = 0 + example_7_2_4'.seq 1 := by rw [hpartial0]
      _ = example_7_2_4'.seq 1 := by simp
      _ = (2:ℝ)^(1 : ℤ) := by rw [hseq1]
      _ = (2:ℝ)^(1+1 : ℤ) - 2 := by norm_num
  · intro k hk IH
    have hseq : example_7_2_4'.seq (k+1 : ℤ) = (2:ℝ)^((k+1 : ℤ)) := by
      rw [Series.eval_mk' (fun n : { n // n ≥ 1 } ↦ (2:ℝ)^(n:ℤ)) (show (k+1 : ℤ) ≥ 1 from by omega)]
    calc
      example_7_2_4'.partial (k + 1) = example_7_2_4'.partial k + example_7_2_4'.seq (k + 1) := by
        rw [partial_succ example_7_2_4' (by rw [hm]; omega)]
      _ = ((2:ℝ)^(k+1 : ℤ) - 2) + example_7_2_4'.seq (k + 1) := by rw [IH]
      _ = ((2:ℝ)^(k+1 : ℤ) - 2) + (2:ℝ)^(k+1 : ℤ) := by rw [hseq]
      _ = 2 * (2:ℝ)^(k+1 : ℤ) - 2 := by ring
      _ = (2:ℝ)^(1 : ℤ) * (2:ℝ)^(k+1 : ℤ) - 2 := by norm_num
      _ = (2:ℝ)^((1 : ℤ) + (k+1 : ℤ)) - 2 := by
        rw [zpow_add₀ (by norm_num : (2:ℝ) ≠ 0) (1 : ℤ) (k+1 : ℤ)]
      _ = (2:ℝ)^((k+1 : ℤ) + 1) - 2 := by
        have h : (1 : ℤ) + (k+1 : ℤ) = (k+1 : ℤ) + 1 := by omega
        simp [h]

theorem Series.example_7_2_4'b : example_7_2_4'.diverges := by
  unfold Series.diverges Series.converges
  intro h
  rcases h with ⟨L, hL⟩
  have hm : example_7_2_4'.m = 1 := rfl
  have hL_metric : ∀ ε > (0 : ℝ), ∀ᶠ (n : ℤ) in Filter.atTop, |example_7_2_4'.partial n - L| < ε :=
    Metric.tendsto_nhds.mp hL
  have h_event : ∀ᶠ (n : ℤ) in Filter.atTop, |example_7_2_4'.partial n - L| < (1 : ℝ) :=
    hL_metric 1 (by norm_num)
  rcases Filter.eventually_atTop.mp h_event with ⟨N, hN⟩
  let M := max N 1
  have hM_N : M ≥ N := le_max_left _ _
  have hM_one : M ≥ (1 : ℤ) := le_max_right _ _
  have hM_succ_N : M + 1 ≥ N := by omega
  have hbound1 : |example_7_2_4'.partial M - L| < 1 := hN M hM_N
  have hbound2 : |example_7_2_4'.partial (M + 1) - L| < 1 := hN (M + 1) hM_succ_N
  have h_diff_bound : |example_7_2_4'.partial (M + 1) - example_7_2_4'.partial M| < 2 := by
    have h_tri : |example_7_2_4'.partial (M + 1) - example_7_2_4'.partial M|
        ≤ |example_7_2_4'.partial (M + 1) - L| + |example_7_2_4'.partial M - L| := by
      calc
        |example_7_2_4'.partial (M + 1) - example_7_2_4'.partial M|
            = |(example_7_2_4'.partial (M + 1) - L) - (example_7_2_4'.partial M - L)| := by ring_nf
        _ ≤ |example_7_2_4'.partial (M + 1) - L| + |example_7_2_4'.partial M - L| := abs_sub _ _
    nlinarith
  have h_abs_diff : |example_7_2_4'.partial (M + 1) - example_7_2_4'.partial M| = (2 : ℝ)^(M + 1 : ℤ) := by
    have hM_sub_one : M ≥ example_7_2_4'.m - 1 := by rw [hm]; omega
    have hM_succ_one : M + 1 ≥ 1 := by omega
    calc
      |example_7_2_4'.partial (M + 1) - example_7_2_4'.partial M|
          = |example_7_2_4'.seq (M + 1)| := by
            rw [partial_succ example_7_2_4' hM_sub_one, add_sub_cancel_left]
      _ = |(2 : ℝ)^(M + 1 : ℤ)| := by
        rw [Series.eval_mk' (fun n : { n // n ≥ 1 } ↦ (2 : ℝ)^(n : ℤ)) hM_succ_one]
      _ = (2 : ℝ)^(M + 1 : ℤ) := abs_of_pos (by positivity)
  rw [h_abs_diff] at h_diff_bound
  have h_pow_ge_two : (2 : ℝ)^(M + 1 : ℤ) ≥ 2 := by
    have h_two_le_exp : (1 : ℤ) ≤ M + 1 := by omega
    calc
      (2 : ℝ)^(M + 1 : ℤ) ≥ (2 : ℝ)^(1 : ℤ) :=
        zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h_two_le_exp
      _ = 2 := by norm_num
  nlinarith

/-- Proposition 7.2.5 / Exercise 7.2.2 -/
theorem Series.converges_iff_tail_decay (s:Series) :
    s.converges ↔ ∀ ε > 0, ∃ N ≥ s.m, ∀ p ≥ N, ∀ q ≥ N, |∑ n ∈ Finset.Icc p q, s.seq n| ≤ ε := by
  constructor
  · intro h ε hε
    rcases h with ⟨L, hL⟩
    have h_cauchy : CauchySeq s.partial := hL.cauchySeq
    rw [Metric.cauchySeq_iff] at h_cauchy
    rcases h_cauchy ε hε with ⟨K, hK⟩
    use max (K + 1) s.m
    constructor
    · exact le_max_right _ _
    · intro p hp q hq
      have hpK : p ≥ K + 1 := le_of_max_le_left hp
      have hqK : q ≥ K + 1 := le_of_max_le_left hq
      have hp_sm : p ≥ s.m := le_of_max_le_right hp
      have hq_sm : q ≥ s.m := le_of_max_le_right hq
      by_cases hpq : p ≤ q
      · have hp1K : p - 1 ≥ K := by omega
        have h_sum_eq : ∑ n ∈ Finset.Icc p q, s.seq n = s.partial q - s.partial (p - 1) := by
          rcases hp_sm.eq_or_lt with (rfl | hp_sm_lt)
          · simp [Series.partial]
          · have h_sm_pm1 : s.m ≤ p - 1 := by omega
            have h_pm1_q : p - 1 ≤ q := by omega
            unfold Series.partial
            have h_sub : Finset.Icc s.m (p - 1) ⊆ Finset.Icc s.m q :=
              Finset.Icc_subset_Icc (le_refl s.m) h_pm1_q
            have h_sdiff : Finset.Icc s.m q \ Finset.Icc s.m (p - 1) = Finset.Icc p q := by
              ext n; simp; omega
            calc
              ∑ n ∈ Finset.Icc p q, s.seq n
                  = ∑ n ∈ (Finset.Icc s.m q \ Finset.Icc s.m (p - 1)), s.seq n := by rw [h_sdiff]
              _ = (∑ n ∈ Finset.Icc s.m q, s.seq n) - (∑ n ∈ Finset.Icc s.m (p - 1), s.seq n) := by
                rw [← Finset.sum_sdiff h_sub]; simp
              _ = s.partial q - s.partial (p - 1) := rfl
        rw [h_sum_eq]
        have hbound := hK q (by omega) (p - 1) (by omega)
        rw [Real.dist_eq] at hbound
        linarith
      · have h_empty : Finset.Icc p q = ∅ := by
          ext n; simp; omega
        simp [h_empty, hε.le]
  · intro h
    have h_cauchy : CauchySeq s.partial := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      rcases h (ε/2) (half_pos hε) with ⟨N, hN_sm, hN⟩
      use N
      intro m hm n hn
      rw [Real.dist_eq]
      have hm_sm : s.m ≤ m := le_trans hN_sm hm
      have hn_sm : s.m ≤ n := le_trans hN_sm hn
      by_cases hm_le_n : m ≤ n
      · by_cases hm_eq_n : m = n
        · subst hm_eq_n; simp [hε]
        · have hm_lt_n : m < n := by omega
          have h_sum_eq : s.partial n - s.partial m = ∑ k ∈ Finset.Icc (m + 1) n, s.seq k := by
            have h_sm_m1 : s.m ≤ m + 1 := by omega
            have h_m1_n : m + 1 ≤ n := by omega
            rcases h_sm_m1.eq_or_lt with (h_eq | h_sm_m1_lt)
            · have hm_partial : s.partial m = 0 := by
                unfold Series.partial
                rw [h_eq]
                simp
              have hn_partial : s.partial n = ∑ k ∈ Finset.Icc (m + 1) n, s.seq k := by
                unfold Series.partial
                rw [h_eq]
              calc
                s.partial n - s.partial m = (∑ k ∈ Finset.Icc (m + 1) n, s.seq k) - 0 := by
                  rw [hn_partial, hm_partial]
                _ = ∑ k ∈ Finset.Icc (m + 1) n, s.seq k := by simp
            · have h_sm_m : s.m ≤ m := by omega
              have h_m_m1 : m ≤ m + 1 := by omega
              unfold Series.partial
              have h_sub : Finset.Icc s.m m ⊆ Finset.Icc s.m n :=
                Finset.Icc_subset_Icc (le_refl s.m) (by omega)
              have h_sdiff : Finset.Icc s.m n \ Finset.Icc s.m m = Finset.Icc (m + 1) n := by
                ext k; simp; omega
              calc
                s.partial n - s.partial m
                    = (∑ x ∈ Finset.Icc s.m n, s.seq x) - (∑ x ∈ Finset.Icc s.m m, s.seq x) := rfl
                _ = ∑ x ∈ (Finset.Icc s.m n \ Finset.Icc s.m m), s.seq x := by
                  rw [← Finset.sum_sdiff h_sub]; simp
                _ = ∑ k ∈ Finset.Icc (m + 1) n, s.seq k := by rw [h_sdiff]
          have hm1N : m + 1 ≥ N := by omega
          have hbound : |∑ k ∈ Finset.Icc (m + 1) n, s.seq k| ≤ ε/2 :=
            hN (m + 1) hm1N n hn
          calc
            |s.partial m - s.partial n| = |s.partial n - s.partial m| := by rw [abs_sub_comm]
            _ = |∑ k ∈ Finset.Icc (m + 1) n, s.seq k| := by rw [h_sum_eq]
            _ < ε := by linarith
      · have hn_lt_m : n < m := by omega
        have h_sum_eq : s.partial m - s.partial n = ∑ k ∈ Finset.Icc (n + 1) m, s.seq k := by
          have h_sm_n1 : s.m ≤ n + 1 := by omega
          have h_n1_m : n + 1 ≤ m := by omega
          rcases h_sm_n1.eq_or_lt with (h_eq | h_sm_n1_lt)
          · have hn_partial : s.partial n = 0 := by
              unfold Series.partial
              rw [h_eq]
              simp
            have hm_partial : s.partial m = ∑ k ∈ Finset.Icc (n + 1) m, s.seq k := by
              unfold Series.partial
              rw [h_eq]
            calc
              s.partial m - s.partial n = (∑ k ∈ Finset.Icc (n + 1) m, s.seq k) - 0 := by
                rw [hm_partial, hn_partial]
              _ = ∑ k ∈ Finset.Icc (n + 1) m, s.seq k := by simp
          · have h_sm_n : s.m ≤ n := by omega
            have h_n_n1 : n ≤ n + 1 := by omega
            unfold Series.partial
            have h_sub : Finset.Icc s.m n ⊆ Finset.Icc s.m m :=
              Finset.Icc_subset_Icc (le_refl s.m) (by omega)
            have h_sdiff : Finset.Icc s.m m \ Finset.Icc s.m n = Finset.Icc (n + 1) m := by
              ext k; simp; omega
            calc
              s.partial m - s.partial n
                  = (∑ x ∈ Finset.Icc s.m m, s.seq x) - (∑ x ∈ Finset.Icc s.m n, s.seq x) := rfl
              _ = ∑ x ∈ (Finset.Icc s.m m \ Finset.Icc s.m n), s.seq x := by
                rw [← Finset.sum_sdiff h_sub]; simp
              _ = ∑ k ∈ Finset.Icc (n + 1) m, s.seq k := by rw [h_sdiff]
        have hn1N : n + 1 ≥ N := by omega
        have hbound : |∑ k ∈ Finset.Icc (n + 1) m, s.seq k| ≤ ε/2 :=
          hN (n + 1) hn1N m hm
        calc
          |s.partial m - s.partial n| = |∑ k ∈ Finset.Icc (n + 1) m, s.seq k| := by rw [h_sum_eq]
          _ < ε := by linarith
    exact cauchySeq_tendsto_of_complete h_cauchy

/-- Corollary 7.2.6 (Zero test) / Exercise 7.2.3 -/
theorem Series.decay_of_converges {s:Series} (h: s.converges) :
    Filter.atTop.Tendsto s.seq (nhds 0) := by
  have h_tail := (converges_iff_tail_decay s).mp h
  rw [Metric.tendsto_nhds]
  intro ε hε
  rcases h_tail (ε/2) (by linarith) with ⟨N, _, hN⟩
  refine Filter.eventually_atTop.mpr ⟨N, ?_⟩
  intro n hn
  rw [Real.dist_eq, sub_zero]
  have h_bound : |∑ k ∈ Finset.Icc n n, s.seq k| ≤ ε/2 := hN n hn n hn
  have h_singleton : ∑ k ∈ Finset.Icc n n, s.seq k = s.seq n := by simp
  rw [h_singleton] at h_bound
  linarith

theorem Series.diverges_of_nodecay {s:Series} (h: ¬ Filter.atTop.Tendsto s.seq (nhds 0)) :
    s.diverges := by
  intro hconv
  apply h
  exact decay_of_converges hconv

/-- Example 7.2.7 -/
theorem Series.example_7_2_7 : ((fun _:ℕ ↦ (1:ℝ)):Series).diverges := by
  apply diverges_of_nodecay
  intro h
  have h' := (Metric.tendsto_nhds.mp h) 1 (by norm_num : (0 : ℝ) < 1)
  rcases Filter.eventually_atTop.mp h' with ⟨N, hN⟩
  have hN' := hN (max N 0) (le_max_left _ _)
  rw [Real.dist_eq, sub_zero] at hN'
  have hpos : (max N 0 : ℤ) ≥ 0 := le_max_right _ _
  have hseq : ((fun _ : ℕ ↦ (1 : ℝ)) : Series).seq (max N 0) = 1 := by
    simp [hpos]
  rw [hseq] at hN'
  norm_num at hN'

theorem Series.example_7_2_7' : ((fun n:ℕ ↦ (-1:ℝ)^n):Series).diverges := by
  apply diverges_of_nodecay
  intro h
  have h' := (Metric.tendsto_nhds.mp h) 1 (by norm_num : (0 : ℝ) < 1)
  rcases Filter.eventually_atTop.mp h' with ⟨N, hN⟩
  set M := max N 0 with hM
  have hMN : M ≥ N := le_max_left _ _
  have hM0 : M ≥ 0 := le_max_right _ _
  have hNM' : |((-1 : ℝ) ^ M.toNat)| < 1 := by
    simpa [hM0] using hN M hMN
  have h_abs : |((-1 : ℝ) ^ M.toNat)| = 1 := by
    have h_cases : ((-1 : ℝ) ^ M.toNat = 1) ∨ ((-1 : ℝ) ^ M.toNat = -1) := by
      induction' M.toNat with k ih
      · left; norm_num
      · rcases ih with (h1 | h2)
        · right; calc
            (-1 : ℝ) ^ (k + 1) = ((-1 : ℝ) ^ k) * (-1 : ℝ) := by rw [pow_succ]
            _ = (1 : ℝ) * (-1 : ℝ) := by rw [h1]
            _ = (-1 : ℝ) := by norm_num
        · left; calc
            (-1 : ℝ) ^ (k + 1) = ((-1 : ℝ) ^ k) * (-1 : ℝ) := by rw [pow_succ]
            _ = (-1 : ℝ) * (-1 : ℝ) := by rw [h2]
            _ = (1 : ℝ) := by norm_num
    rcases h_cases with (h1 | h2)
    · simp [h1]
    · simp [h2]
  rw [h_abs] at hNM'
  linarith

/-- Definition 7.2.8 (Absolute convergence) -/
abbrev Series.abs (s:Series) : Series := mk' (m:=s.m) (fun n ↦ |s.seq n|)

abbrev Series.absConverges (s:Series) : Prop := s.abs.converges

abbrev Series.condConverges (s:Series) : Prop := s.converges ∧ ¬ s.absConverges

/-- Proposition 7.2.9 (Absolute convergence test) / Exercise 7.2.4 -/
theorem Series.converges_of_absConverges {s:Series} (h : s.absConverges) : s.converges := by
  rw [converges_iff_tail_decay]
  intro ε hε
  rcases (converges_iff_tail_decay s.abs).mp h ε hε with ⟨N, hN, hN'⟩
  refine ⟨N, hN, λ p hp q hq => ?_⟩
  have h_nonneg : 0 ≤ ∑ n ∈ Finset.Icc p q, |s.seq n| :=
    Finset.sum_nonneg (λ n _ => abs_nonneg _)
  have h_abs_eq : |(∑ n ∈ Finset.Icc p q, |s.seq n|)| = ∑ n ∈ Finset.Icc p q, |s.seq n| := by
    rw [abs_of_nonneg h_nonneg]
  have h_tri : |∑ n ∈ Finset.Icc p q, s.seq n| ≤ ∑ n ∈ Finset.Icc p q, |s.seq n| :=
    Finset.abs_sum_le_sum_abs (s.seq) (Finset.Icc p q)
  have h_abs_bound : |(∑ n ∈ Finset.Icc p q, |s.seq n|)| ≤ ε := by
    have hN_sm : s.abs.m = s.m := rfl
    have hN_sm_le : s.m ≤ N := by
      -- from hN: N ≥ s.abs.m = s.m
      rw [hN_sm] at hN
      exact hN
    have h_sum_eq : (∑ n ∈ Finset.Icc p q, |s.seq n|) = (∑ n ∈ Finset.Icc p q, s.abs.seq n) := by
      refine Finset.sum_congr rfl (λ n hn => ?_)
      have hp_n : p ≤ n := (Finset.mem_Icc.mp hn).1
      have hn_sm : n ≥ s.m := le_trans hN_sm_le (le_trans hp hp_n)
      simp [hn_sm]
    simpa [h_sum_eq] using hN' p hp q hq
  linarith

theorem Series.abs_le {s:Series} (h : s.absConverges) : |s.sum| ≤ s.abs.sum := by
  have hconv_s : s.converges := converges_of_absConverges h
  have hconv_abs : s.abs.converges := h
  have h_tendsto_s : Filter.atTop.Tendsto s.partial (nhds s.sum) :=
    convergesTo_sum hconv_s
  have h_tendsto_abs : Filter.atTop.Tendsto s.abs.partial (nhds s.abs.sum) :=
    convergesTo_sum hconv_abs
  have h_ineq : ∀ N : ℤ, |s.partial N| ≤ s.abs.partial N := by
    intro N
    calc
      |s.partial N| = |∑ n ∈ Finset.Icc s.m N, s.seq n| := rfl
      _ ≤ ∑ n ∈ Finset.Icc s.m N, |s.seq n| := Finset.abs_sum_le_sum_abs s.seq (Finset.Icc s.m N)
      _ = s.abs.partial N := by
        dsimp [Series.abs, Series.partial]
        refine Finset.sum_congr rfl fun n hn => ?_
        have hm : s.m ≤ n := (Finset.mem_Icc.mp hn).1
        simp [hm]
  have h_tendsto_abs_partial : Filter.atTop.Tendsto (fun N : ℤ => |s.partial N|) (nhds (|s.sum|)) :=
    h_tendsto_s.abs
  have h_event : ∀ᶠ N : ℤ in Filter.atTop, |s.partial N| ≤ s.abs.partial N := by
    refine Filter.eventually_atTop.mpr ⟨0, fun N hN => ?_⟩
    exact h_ineq N
  exact le_of_tendsto_of_tendsto h_tendsto_abs_partial h_tendsto_abs h_event

/-- Proposition 7.2.12 (Alternating series test) -/
theorem Series.converges_of_alternating {m:ℤ} {a: { n // n ≥ m} → ℝ} (ha: ∀ n, a n ≥ 0)
  (ha': Antitone a) :
    ((mk' (fun n ↦ (-1)^(n:ℤ) * a n)).converges ↔ Filter.atTop.Tendsto a (nhds 0)) := by
  -- This proof is written to follow the structure of the original text.
  constructor
  . intro h; apply decay_of_converges at h
    rw [tendsto_iff_dist_tendsto_zero] at h ⊢
    rw [←Filter.tendsto_comp_val_Ici_atTop (a := m)] at h
    refine h.congr (fun n => ?_)
    simp [n.property]
  intro h
  unfold converges convergesTo
  set b := mk' fun n ↦ (-1) ^ (n:ℤ) * a n
  set S := b.partial
  have claim0 {N:ℤ} (hN: N ≥ m) : S (N+1) = S N + (-1)^(N+1) * a ⟨ N+1, by grind ⟩ := by
    convert b.partial_succ ?_; simp [b, show N+1 ≥ m by grind]; linarith
  have claim1 {N:ℤ} (hN: N ≥ m) : S (N+2) = S N + (-1)^(N+1) * (a ⟨ N+1, by grind ⟩ - a ⟨ N+2, by grind ⟩) := calc
      S (N+2) = S N + (-1)^(N+1) * a ⟨ N+1, by grind ⟩ + (-1)^(N+2) * a ⟨ N+2, by grind ⟩ := by
        simp_rw [←claim0 hN, show N+2=N+1+1 by abel]; apply claim0; linarith
      _ = S N + (-1)^(N+1) * a ⟨ N+1, by grind ⟩ + (-1) * (-1)^(N+1) * a ⟨ N+2, by grind ⟩ := by
        congr; rw [←zpow_one_add₀] <;> grind
      _ = _ := by ring
  have claim2 {N:ℤ} (hN: N ≥ m) (h': Odd N) : S (N+2) ≥ S N := by
    simp [claim1 hN, h'.add_one.neg_one_zpow]; apply ha'; simp
  have claim3 {N:ℤ} (hN: N ≥ m) (h': Even N) : S (N+2) ≤ S N := by
    simp [claim1 hN, h'.add_one.neg_one_zpow]; apply ha'; simp
  have why1 {N:ℤ} (hN: N ≥ m) (h': Even N) (k:ℕ) : S (N+2*k) ≤ S N := by
    induction' k with k ih
    · simp
    · have h_even_N2k : Even (N + 2*k) := by
        exact h'.add (by
          have : Even (2*k : ℤ) := by use k; ring
          exact this)
      rw [show N + 2*(k+1 : ℕ) = (N + 2*k) + 2 by push_cast; ring]
      calc
        S ((N + 2*k) + 2) ≤ S (N + 2*k) := claim3 (by omega) h_even_N2k
        _ ≤ S N := ih
  have why2 {N:ℤ} (hN: N ≥ m) (h': Even N) (k:ℕ) : S (N+2*k+1) ≥ S N - a ⟨ N+1, by grind ⟩ := by
    induction' k with k ih
    · have h_odd : Odd (N+1 : ℤ) := h'.add_one
      calc
        S (N + 2*(0 : ℕ) + 1) = S (N+1) := by simp
        _ = S N + (-1 : ℝ)^(N+1 : ℤ) * a ⟨N+1, by grind⟩ := claim0 hN
        _ = S N + (-1 : ℝ) * a ⟨N+1, by grind⟩ := by rw [h_odd.neg_one_zpow]
        _ = S N - a ⟨N+1, by grind⟩ := by ring
        _ ≥ S N - a ⟨N+1, by grind⟩ := le_rfl
    · have h_2k_even : Even (2*(k : ℤ)) := by use k; ring
      have h_N2k_even : Even (N + 2*(k : ℤ)) := h'.add h_2k_even
      have h_N2k2_even : Even (N + 2*(k : ℤ) + 2) := by
        have : Even (2 : ℤ) := by use 1; ring
        exact h_N2k_even.add this
      have h_N2k3_odd : Odd (N + 2*(k : ℤ) + 3) := by
        simpa [add_assoc] using h_N2k2_even.add_one
      have hN1 : N + 2*(k : ℤ) + 1 ≥ m := by omega
      have hN2 : N + 2*(k : ℤ) + 2 ≥ m := by omega
      have hN3 : N + 2*(k : ℤ) + 3 ≥ m := by omega
      have hS_expr : S (N + 2*(k : ℤ) + 3) = S (N + 2*(k : ℤ) + 1) + (a ⟨N + 2*(k : ℤ) + 2, hN2⟩ - a ⟨N + 2*(k : ℤ) + 3, hN3⟩) := by
        calc
          S (N + 2*(k : ℤ) + 3) = S ((N + 2*(k : ℤ) + 2) + 1) := by ring_nf
          _ = S (N + 2*(k : ℤ) + 2) + (-1 : ℝ)^((N + 2*(k : ℤ) + 2) + 1 : ℤ) * a ⟨(N + 2*(k : ℤ) + 2) + 1, by omega⟩ := by rw [claim0 hN2]
          _ = S ((N + 2*(k : ℤ) + 1) + 1) + (-1 : ℝ)^(N + 2*(k : ℤ) + 3 : ℤ) * a ⟨N + 2*(k : ℤ) + 3, hN3⟩ := by ring_nf
          _ = (S (N + 2*(k : ℤ) + 1) + (-1 : ℝ)^((N + 2*(k : ℤ) + 1) + 1 : ℤ) * a ⟨(N + 2*(k : ℤ) + 1) + 1, by omega⟩) + (-1 : ℝ)^(N + 2*(k : ℤ) + 3 : ℤ) * a ⟨N + 2*(k : ℤ) + 3, hN3⟩ := by
            rw [claim0 hN1]
          _ = (S (N + 2*(k : ℤ) + 1) + (-1 : ℝ)^(N + 2*(k : ℤ) + 2 : ℤ) * a ⟨N + 2*(k : ℤ) + 2, hN2⟩) + (-1 : ℝ)^(N + 2*(k : ℤ) + 3 : ℤ) * a ⟨N + 2*(k : ℤ) + 3, hN3⟩ := by
            have h_idx : ((N : ℤ) + 2*(k : ℤ) + 1) + 1 = N + 2*(k : ℤ) + 2 := by ring
            have h_sub : (⟨((N : ℤ) + 2*(k : ℤ) + 1) + 1, by omega⟩ : {n // n ≥ m}) = ⟨N + 2*(k : ℤ) + 2, hN2⟩ := by
              apply Subtype.ext; exact h_idx
            calc
              (S (N + 2*(k : ℤ) + 1) + (-1 : ℝ)^((N + 2*(k : ℤ) + 1) + 1 : ℤ) * a ⟨(N + 2*(k : ℤ) + 1) + 1, by omega⟩) + (-1 : ℝ)^(N + 2*(k : ℤ) + 3 : ℤ) * a ⟨N + 2*(k : ℤ) + 3, hN3⟩
                  = (S (N + 2*(k : ℤ) + 1) + (-1 : ℝ)^(N + 2*(k : ℤ) + 2 : ℤ) * a ⟨(N + 2*(k : ℤ) + 1) + 1, by omega⟩) + (-1 : ℝ)^(N + 2*(k : ℤ) + 3 : ℤ) * a ⟨N + 2*(k : ℤ) + 3, hN3⟩ := by
                    congr 2; ring_nf
              _ = (S (N + 2*(k : ℤ) + 1) + (-1 : ℝ)^(N + 2*(k : ℤ) + 2 : ℤ) * a ⟨N + 2*(k : ℤ) + 2, hN2⟩) + (-1 : ℝ)^(N + 2*(k : ℤ) + 3 : ℤ) * a ⟨N + 2*(k : ℤ) + 3, hN3⟩ := by
                simp [h_sub]
          _ = S (N + 2*(k : ℤ) + 1) + (1 : ℝ) * a ⟨N + 2*(k : ℤ) + 2, hN2⟩ + (-1 : ℝ) * a ⟨N + 2*(k : ℤ) + 3, hN3⟩ := by
            rw [h_N2k2_even.neg_one_zpow, h_N2k3_odd.neg_one_zpow]
          _ = S (N + 2*(k : ℤ) + 1) + (a ⟨N + 2*(k : ℤ) + 2, hN2⟩ - a ⟨N + 2*(k : ℤ) + 3, hN3⟩) := by ring
      have ha_diff_nonneg : a ⟨N + 2*(k : ℤ) + 2, hN2⟩ - a ⟨N + 2*(k : ℤ) + 3, hN3⟩ ≥ 0 := by
        have ha_order : a ⟨N + 2*(k : ℤ) + 3, hN3⟩ ≤ a ⟨N + 2*(k : ℤ) + 2, hN2⟩ :=
          ha' (Subtype.mk_le_mk.mpr (by omega))
        linarith
      calc
        S (N + 2*(k+1 : ℕ) + 1) = S (N + 2*(k : ℤ) + 3) := by push_cast; ring_nf
        _ = S (N + 2*(k : ℤ) + 1) + (a ⟨N + 2*(k : ℤ) + 2, hN2⟩ - a ⟨N + 2*(k : ℤ) + 3, hN3⟩) := by rw [hS_expr]
        _ ≥ S (N + 2*(k : ℤ) + 1) := by nlinarith
        _ ≥ S N - a ⟨N + 1, by grind⟩ := ih
  have why3 {N:ℤ} (hN: N ≥ m) (h': Even N) (k:ℕ) : S (N+2*k+1) ≤ S (N+2*k) := by
    have h_even_N2k : Even (N+2*k) := h'.add ⟨k, by ring⟩
    have h_odd_N2k1 : Odd (N+2*k+1) := h_even_N2k.add_one
    calc
      S (N+2*k+1) = S (N+2*k) + (-1 : ℝ)^(N+2*k+1 : ℤ) * a ⟨ N+2*k+1, by omega ⟩ := claim0 (by omega)
      _ = S (N+2*k) + (-1 : ℝ) * a ⟨ N+2*k+1, by omega ⟩ := by rw [h_odd_N2k1.neg_one_zpow]
      _ = S (N+2*k) - a ⟨ N+2*k+1, by omega ⟩ := by ring
      _ ≤ S (N+2*k) := by nlinarith [ha ⟨ N+2*k+1, by omega ⟩]
  have claim4 {N:ℤ} (hN: N ≥ m) (h': Even N) (k:ℕ) : S N -
 a ⟨ N+1, by grind ⟩ ≤ S (N + 2*k + 1) ∧ S (N + 2*k + 1) ≤ S (N + 2*k) ∧ S (N + 2*k) ≤ S N := ⟨ ge_iff_le.mp (why2 hN h' k), why3 hN h' k, why1 hN h' k ⟩
  have why4 {N n:ℤ} (hN: N ≥ m) (h': Even N) (hn: n ≥ N) : S N - a ⟨ N+1, by grind ⟩ ≤ S n ∧ S n ≤ S N := by
    obtain ⟨k, hk⟩ := Int.le.dest hn
    have h_parity : (∃ t : ℕ, k = 2*t) ∨ (∃ t : ℕ, k = 2*t + 1) := by
      have h_mod2 := Nat.mod_two_eq_zero_or_one k
      rcases h_mod2 with (h_mod2 | h_mod2)
      · left; refine ⟨k / 2, ?_⟩; omega
      · right; refine ⟨k / 2, ?_⟩; omega
    rcases h_parity with (⟨t, ht⟩ | ⟨t, ht⟩)
    · have hn_eq : n = N + 2*t := by omega
      rw [hn_eq]
      constructor
      · calc
          S N - a ⟨ N+1, by grind ⟩ ≤ S (N + 2*t + 1) := why2 hN h' t
          _ ≤ S (N + 2*t) := why3 hN h' t
      · exact why1 hN h' t
    · have hn_eq : n = N + 2*t + 1 := by omega
      rw [hn_eq]
      constructor
      · exact why2 hN h' t
      · calc
          S (N + 2*t + 1) ≤ S (N + 2*t) := why3 hN h' t
          _ ≤ S N := why1 hN h' t
  have why5 {ε:ℝ} (hε: ε > 0) : ∃ N, ∀ n ≥ N, ∀ m ≥ N, |S n - S m| ≤ ε := by
    rw [Metric.tendsto_nhds] at h
    have h_event := h ε hε
    haveI : Nonempty { n // n ≥ m } := ⟨⟨m, le_refl m⟩⟩
    have h_event' : ∃ M : { n // n ≥ m }, ∀ x : { n // n ≥ m }, x ≥ M → |a x| < ε := by
      have := (Filter.eventually_atTop (α := { n // n ≥ m })).mp h_event
      rcases this with ⟨M, hM⟩
      refine ⟨M, λ x hx => ?_⟩
      have := hM x hx
      rw [Real.dist_eq, sub_zero] at this
      exact this
    rcases h_event' with ⟨⟨M, hM⟩, hM'⟩
    set L := max m M with hL_def
    have hL_m : L ≥ m := le_max_left _ _
    have hL_M : M ≤ L := le_max_right _ _
    have ha_lt_ε : ∀ (k : ℤ) (hk : k ≥ L), a ⟨k, by omega⟩ < ε := by
      intro k hk
      have hk_m : k ≥ m := le_trans hL_m hk
      have hk_sub : (⟨k, hk_m⟩ : { n // n ≥ m }) ≥ (⟨M, hM⟩ : { n // n ≥ m }) :=
        Subtype.mk_le_mk.mpr (le_trans hL_M hk)
      have h_a := hM' (⟨k, hk_m⟩) hk_sub
      rw [abs_of_nonneg (ha ⟨k, hk_m⟩)] at h_a
      exact h_a
    rcases Int.even_or_odd L with (hL_even | hL_odd)
    · use L
      have h_a_lt_ε : a ⟨L + 1, by omega⟩ < ε := ha_lt_ε (L + 1) (by omega)
      have ha_eq : a ⟨L + 1, by grind⟩ = a ⟨L + 1, by omega⟩ := by
        have h_sub_eq : (⟨L + 1, by grind⟩ : { n // n ≥ m }) = (⟨L + 1, by omega⟩ : { n // n ≥ m }) :=
          Subtype.ext rfl
        rw [h_sub_eq]
      intro n hn m hm
      have hS_n := why4 hL_m hL_even hn
      have hS_m := why4 hL_m hL_even hm
      rcases hS_n with ⟨hn_low, hn_upp⟩
      rcases hS_m with ⟨hm_low, hm_upp⟩
      have h1 : S n - S m ≤ a ⟨L + 1, by grind⟩ := by linarith
      have h2 : -(a ⟨L + 1, by grind⟩) ≤ S n - S m := by linarith
      have h_bound : |S n - S m| ≤ a ⟨L + 1, by grind⟩ := by
        rw [_root_.abs_le]
        exact ⟨h2, h1⟩
      exact (h_bound.trans_eq ha_eq).trans h_a_lt_ε.le
    · use L + 1
      have hL1_m : L + 1 ≥ m := by omega
      have hL1_even : Even (L + 1) := hL_odd.add_one
      have h_a_lt_ε : a ⟨(L + 1) + 1, by omega⟩ < ε := ha_lt_ε ((L + 1) + 1) (by omega)
      have ha_eq : a ⟨(L + 1) + 1, by grind⟩ = a ⟨(L + 1) + 1, by omega⟩ := by
        have h_sub_eq : (⟨(L + 1) + 1, by grind⟩ : { n // n ≥ m }) = (⟨(L + 1) + 1, by omega⟩ : { n // n ≥ m }) :=
          Subtype.ext rfl
        rw [h_sub_eq]
      intro n hn m hm
      have hn' : n ≥ L + 1 := hn
      have hm' : m ≥ L + 1 := hm
      have hS_n := why4 hL1_m hL1_even hn'
      have hS_m := why4 hL1_m hL1_even hm'
      rcases hS_n with ⟨hn_low, hn_upp⟩
      rcases hS_m with ⟨hm_low, hm_upp⟩
      have h1 : S n - S m ≤ a ⟨(L + 1) + 1, by grind⟩ := by linarith
      have h2 : -(a ⟨(L + 1) + 1, by grind⟩) ≤ S n - S m := by linarith
      have h_bound : |S n - S m| ≤ a ⟨(L + 1) + 1, by grind⟩ := by
        rw [_root_.abs_le]
        exact ⟨h2, h1⟩
      exact (h_bound.trans_eq ha_eq).trans h_a_lt_ε.le
  have : CauchySeq S := by
    rw [Metric.cauchySeq_iff']
    intro ε hε; choose N hN using why5 (half_pos hε); use N
    intro n hn; rw [Real.dist_eq]; linarith [hN n hn N (by simp)]
  exact cauchySeq_tendsto_of_complete this

/-- Example 7.2.13 -/
noncomputable abbrev Series.example_7_2_13 : Series := (mk' (m:=1) (fun n ↦ (-1:ℝ)^(n:ℤ) / (n:ℤ)))

theorem Series.example_7_2_13a : example_7_2_13.converges := by
  let a : { n : ℤ // n ≥ 1 } → ℝ := fun n => (1 : ℝ) / (n.val : ℝ)
  have ha_nonneg : ∀ n, a n ≥ 0 := by
    intro n
    dsimp [a]
    have hpos : 0 < (n.val : ℝ) := by exact mod_cast (show 0 < n.val from by omega)
    positivity
  have ha_anti : Antitone a := by
    intro x y h
    have hxpos : (0 : ℝ) < (x.val : ℝ) := by exact mod_cast (show 0 < x.val from by omega)
    have hypos : (0 : ℝ) < (y.val : ℝ) := by exact mod_cast (show 0 < y.val from by omega)
    have hval : (x.val : ℝ) ≤ (y.val : ℝ) := by exact mod_cast h
    rcases hval.eq_or_lt with (h_eq | h_lt)
    · have h_eq' : x = y := Subtype.ext (by exact_mod_cast h_eq)
      rw [h_eq']
    · exact (one_div_lt_one_div hypos hxpos).mpr h_lt |>.le
  have ha_tendsto : Filter.atTop.Tendsto a (nhds 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    rcases exists_nat_gt (1 / ε) with ⟨K, hK⟩
    have hKpos' : (0 : ℝ) < (K : ℝ) := by
      have hpos : 0 < 1 / ε := div_pos (by norm_num) hε
      linarith
    have hKpos : K ≠ 0 := by
      intro hzero
      have : (K : ℝ) = 0 := by exact_mod_cast hzero
      linarith [hKpos', this]
    have h_nonempty : Nonempty { n : ℤ // n ≥ 1 } := ⟨⟨1, by omega⟩⟩
    refine Filter.eventually_atTop.mpr ⟨⟨(K : ℤ), by
      have : (K : ℕ) ≥ 1 := Nat.pos_of_ne_zero hKpos
      omega⟩, ?_⟩
    intro n hn
    have hn_val : (K : ℤ) ≤ n.val := hn
    rw [Real.dist_eq, sub_zero]
    have ha_nonneg_n : a n ≥ 0 := ha_nonneg n
    rw [abs_of_nonneg ha_nonneg_n]
    have hnpos : (0 : ℝ) < (n.val : ℝ) := by exact mod_cast (show 0 < n.val from by omega)
    have hKpos'' : (0 : ℝ) < (K : ℝ) := hKpos'
    calc
      a n = (1 : ℝ) / (n.val : ℝ) := rfl
      _ ≤ (1 : ℝ) / (K : ℝ) := by
        refine (one_div_le_one_div hnpos hKpos'').mpr ?_
        exact mod_cast hn_val
      _ < ε := by
        have h_one_div_ε_pos : 0 < 1 / ε := div_pos (by norm_num) hε
        have h_eq' : 1 / (1 / ε) = ε := by field_simp [hε.ne.symm]
        have h_temp : (1 : ℝ) / (K : ℝ) < 1 / (1 / ε) :=
          ((one_div_lt_one_div hKpos'' h_one_div_ε_pos).mpr hK)
        rw [h_eq'] at h_temp
        exact h_temp
  have h_alt := (converges_of_alternating ha_nonneg ha_anti).mpr ha_tendsto
  have h_eq : mk' (fun (n : { n : ℤ // n ≥ 1 }) => (-1 : ℝ) ^ (n : ℤ) * a n) = example_7_2_13 := by
    ext n
    dsimp [Series.mk', example_7_2_13]
    dsimp [a]
    simp
    ring_nf
  rw [h_eq] at h_alt
  exact h_alt

theorem Series.example_7_2_13b : ¬ example_7_2_13.absConverges := by
  unfold absConverges
  rw [converges_iff_tail_decay]
  push_neg
  refine ⟨1/4, by norm_num, ?_⟩
  intro N hN
  have hN1 : (1 : ℤ) ≤ N := hN
  refine ⟨N, le_rfl, 2*N, by omega, ?_⟩
  have h_sum_eq : ∑ n ∈ Finset.Icc N (2*N), (example_7_2_13.abs).seq n =
      ∑ n ∈ Finset.Icc N (2*N), 1 / (n : ℝ) := by
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : n ≥ 1 := by
      have hmem := Finset.mem_Icc.mp hn
      omega
    have hnpos : 0 ≤ (n : ℝ) := by exact mod_cast (show 0 ≤ n from by omega)
    dsimp [Series.abs, example_7_2_13, Series.mk'] at *
    simp [hn1, abs_div, abs_zpow, abs_neg, abs_one, one_zpow, abs_of_nonneg hnpos]
  rw [h_sum_eq]
  have h_nonneg : 0 ≤ ∑ n ∈ Finset.Icc N (2*N), 1 / (n : ℝ) :=
    Finset.sum_nonneg fun n hn => by
      have hmem := Finset.mem_Icc.mp hn
      have hnpos : 0 < (n : ℝ) := by exact mod_cast (show 0 < n from by omega)
      positivity
  rw [abs_of_nonneg h_nonneg]
  have h_Npos : (N : ℝ) > 0 := by exact_mod_cast (show 0 < N from by omega)
  have h_card : (Finset.Icc (N : ℤ) (2*N : ℤ)).card = (Int.toNat N) + 1 := by
    rw [Int.card_Icc]
    have h_range : (2*N : ℤ) + 1 - N = N + 1 := by omega
    rw [h_range]
    have h_nonneg_N : 0 ≤ (N : ℤ) := by omega
    calc
      Int.toNat (N + 1 : ℤ) = Int.toNat N + Int.toNat (1 : ℤ) := by
        rw [Int.toNat_add h_nonneg_N (by omega : (0 : ℤ) ≤ 1)]
      _ = (Int.toNat N) + 1 := by simp
  have h_min : ∀ n ∈ Finset.Icc (N : ℤ) (2*N : ℤ), 1 / ((2*N : ℤ) : ℝ) ≤ 1 / (n : ℝ) := by
    intro n hn
    have hmem := Finset.mem_Icc.mp hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact mod_cast (show 0 < n from by
      have hNn : N ≤ n := hmem.1
      omega)
    have h2Npos : (0 : ℝ) < ((2*N : ℤ) : ℝ) := by positivity
    have hn_upper : (n : ℝ) ≤ ((2*N : ℤ) : ℝ) := by exact mod_cast hmem.2
    exact (one_div_le_one_div h2Npos hnpos).mpr hn_upper
  have h_lower : ∑ n ∈ Finset.Icc N (2*N), 1 / (n : ℝ) ≥
      ((Finset.Icc N (2*N)).card : ℝ) * (1 / ((2*N : ℤ) : ℝ)) := by
    have h_const_sum : ∑ n ∈ Finset.Icc N (2*N), 1 / ((2*N : ℤ) : ℝ) =
        ((Finset.Icc N (2*N)).card : ℝ) * (1 / ((2*N : ℤ) : ℝ)) := by simp
    have h_ineq : ∑ n ∈ Finset.Icc N (2*N), 1 / ((2*N : ℤ) : ℝ) ≤ ∑ n ∈ Finset.Icc N (2*N), 1 / (n : ℝ) :=
      Finset.sum_le_sum fun n hn => h_min n hn
    linarith
  rw [h_card] at h_lower
  have h_simp : (((Int.toNat N : ℕ) + 1 : ℕ) : ℝ) * (1 / ((2*N : ℤ) : ℝ)) = (N + 1 : ℝ) / (2*(N : ℝ)) := by
    push_cast
    field_simp [h_Npos.ne.symm]
    have h_nonneg_N : 0 ≤ (N : ℤ) := by omega
    have h_eq : (Int.toNat N : ℝ) = (N : ℝ) := by exact mod_cast (Int.toNat_of_nonneg h_nonneg_N)
    rw [h_eq]
  rw [h_simp] at h_lower
  have h_ratio : (N + 1 : ℝ) / (2*(N : ℝ)) > 1/4 := by
    field_simp [h_Npos.ne.symm]
    nlinarith
  linarith

theorem Series.example_7_2_13c :  example_7_2_13.condConverges := by
  unfold condConverges
  exact ⟨example_7_2_13a, example_7_2_13b⟩

instance Series.inst_add : Add Series where
  add a b := {
    m := min a.m b.m
    seq n := a.seq n + b.seq n
    vanish n hn := by simp [a.vanish n (by omega), b.vanish n (by omega)]
  }

theorem Series.add_coe (a b: ℕ → ℝ) : (a:Series) + (b:Series) = (fun n ↦ a n + b n) := by
  ext n; rfl
  change (a:Series).seq n + (b:Series).seq n = _
  by_cases h:n ≥ 0 <;> simp [h]

/-- Proposition 7.2.14 (a) (Series laws) / Exercise 7.2.5.  The {name}`convergesTo` form can be more convenient for applications. -/
theorem Series.convergesTo.add {s t:Series} {L M: ℝ} (hs: s.convergesTo L) (ht: t.convergesTo M) :
    (s + t).convergesTo (L + M) := by
  unfold Series.convergesTo
  have h_eventually : (s + t).partial =ᶠ[Filter.atTop] (s.partial + t.partial) := by
    apply Filter.eventually_atTop.mpr
    refine ⟨max s.m t.m, ?_⟩
    intro N hN
    have hNs : s.m ≤ N := le_trans (le_max_left _ _) hN
    have hNt : t.m ≤ N := le_trans (le_max_right _ _) hN
    have h_s_eq : (∑ n ∈ Finset.Icc (min s.m t.m) N, s.seq n) = (∑ n ∈ Finset.Icc s.m N, s.seq n) :=
      (Finset.sum_subset (by
        intro n hn
        have hmem := Finset.mem_Icc.mp hn
        exact Finset.mem_Icc.mpr ⟨le_trans (min_le_left s.m t.m) hmem.1, hmem.2⟩
      ) (by
        intro n hn hnmem
        have hmem := Finset.mem_Icc.mp hn
        have hn_lt_sm : n < s.m := by
          by_contra! hge
          apply hnmem
          exact Finset.mem_Icc.mpr ⟨hge, hmem.2⟩
        simp [s.vanish n hn_lt_sm]
      )).symm
    have h_t_eq : (∑ n ∈ Finset.Icc (min s.m t.m) N, t.seq n) = (∑ n ∈ Finset.Icc t.m N, t.seq n) :=
      (Finset.sum_subset (by
        intro n hn
        have hmem := Finset.mem_Icc.mp hn
        exact Finset.mem_Icc.mpr ⟨le_trans (min_le_right s.m t.m) hmem.1, hmem.2⟩
      ) (by
        intro n hn hnmem
        have hmem := Finset.mem_Icc.mp hn
        have hn_lt_tm : n < t.m := by
          by_contra! hge
          apply hnmem
          exact Finset.mem_Icc.mpr ⟨hge, hmem.2⟩
        simp [t.vanish n hn_lt_tm]
      )).symm
    calc
      (s + t).partial N = ∑ n ∈ Finset.Icc (min s.m t.m) N, (s.seq n + t.seq n) := rfl
      _ = (∑ n ∈ Finset.Icc (min s.m t.m) N, s.seq n) + (∑ n ∈ Finset.Icc (min s.m t.m) N, t.seq n) := by
        rw [Finset.sum_add_distrib]
      _ = (∑ n ∈ Finset.Icc s.m N, s.seq n) + (∑ n ∈ Finset.Icc t.m N, t.seq n) := by
        rw [h_s_eq, h_t_eq]
      _ = s.partial N + t.partial N := rfl
      _ = (s.partial + t.partial) N := rfl
  exact Filter.Tendsto.congr' h_eventually.symm (Filter.Tendsto.add hs ht)

theorem Series.add {s t:Series} (hs: s.converges) (ht: t.converges) :
    (s + t).converges ∧ (s+t).sum = s.sum + t.sum := by
  have hsum := convergesTo_sum hs
  have hsumt := convergesTo_sum ht
  have h_add : (s + t).convergesTo (s.sum + t.sum) := hsum.add hsumt
  refine ⟨?_, ?_⟩
  · exact converges_of_convergesTo h_add
  · exact sum_of_converges h_add

instance Series.inst.smul : SMul ℝ Series where
  smul c s := {
    m := s.m
    seq n := if n ≥ s.m then c * s.seq n else 0
    vanish := by grind
  }

theorem Series.smul_coe (a: ℕ → ℝ) (c: ℝ) : (c • a:Series) = (fun n ↦ c * a n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h, HSMul.hSMul, SMul.smul]

/-- Proposition 7.2.14 (b) (Series laws) / Exercise 7.2.5.  The {name}`convergesTo` form can be more convenient for applications. -/
theorem Series.convergesTo.smul {s:Series} {L c: ℝ} (hs: s.convergesTo L) :
    (c • s).convergesTo (c * L) := by
  unfold Series.convergesTo
  have h_partial : (c • s).partial = fun N : ℤ => c * (s.partial N) := by
    ext N
    simp [Series.partial, HSMul.hSMul, SMul.smul, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro n hn
    have hn_sm : s.m ≤ n := (Finset.mem_Icc.mp hn).1
    simp [hn_sm]
  rw [h_partial]
  simpa using hs.const_smul c

theorem Series.smul {c:ℝ} {s:Series} (hs: s.converges) :
    (c • s).converges ∧ (c • s).sum = c * s.sum := by
  have h_convTo : s.convergesTo s.sum := convergesTo_sum hs
  have h_smul_convTo : (c • s).convergesTo (c * s.sum) := h_convTo.smul
  refine ⟨converges_of_convergesTo h_smul_convTo, sum_of_converges h_smul_convTo⟩

/-- The corresponding API for subtraction was not in the textbook, but is useful in later sections, so is included here. -/
instance Series.inst_sub : Sub Series where
  sub a b := {
    m := min a.m b.m
    seq n := a.seq n - b.seq n
    vanish n hn := by simp [a.vanish n (by omega), b.vanish n (by omega)]
  }

theorem Series.sub_coe (a b: ℕ → ℝ) : (a:Series) - (b:Series) = (fun n ↦ a n - b n) := by
  ext n; rfl
  change (a:Series).seq n - (b:Series).seq n = _
  by_cases h:n ≥ 0 <;> simp [h]

theorem Series.convergesTo.sub {s t:Series} {L M: ℝ} (hs: s.convergesTo L) (ht: t.convergesTo M) :
    (s - t).convergesTo (L - M) := by
  unfold Series.convergesTo
  have h_eventually : (s - t).partial =ᶠ[Filter.atTop] (s.partial - t.partial) := by
    apply Filter.eventually_atTop.mpr
    refine ⟨max s.m t.m, ?_⟩
    intro N hN
    have hNs : s.m ≤ N := le_trans (le_max_left _ _) hN
    have hNt : t.m ≤ N := le_trans (le_max_right _ _) hN
    have h_s_eq : (∑ n ∈ Finset.Icc (min s.m t.m) N, s.seq n) = (∑ n ∈ Finset.Icc s.m N, s.seq n) :=
      (Finset.sum_subset (by
        intro n hn
        have hmem := Finset.mem_Icc.mp hn
        exact Finset.mem_Icc.mpr ⟨le_trans (min_le_left s.m t.m) hmem.1, hmem.2⟩
      ) (by
        intro n hn hnmem
        have hmem := Finset.mem_Icc.mp hn
        have hn_lt_sm : n < s.m := by
          by_contra! hge
          apply hnmem
          exact Finset.mem_Icc.mpr ⟨hge, hmem.2⟩
        simp [s.vanish n hn_lt_sm]
      )).symm
    have h_t_eq : (∑ n ∈ Finset.Icc (min s.m t.m) N, t.seq n) = (∑ n ∈ Finset.Icc t.m N, t.seq n) :=
      (Finset.sum_subset (by
        intro n hn
        have hmem := Finset.mem_Icc.mp hn
        exact Finset.mem_Icc.mpr ⟨le_trans (min_le_right s.m t.m) hmem.1, hmem.2⟩
      ) (by
        intro n hn hnmem
        have hmem := Finset.mem_Icc.mp hn
        have hn_lt_tm : n < t.m := by
          by_contra! hge
          apply hnmem
          exact Finset.mem_Icc.mpr ⟨hge, hmem.2⟩
        simp [t.vanish n hn_lt_tm]
      )).symm
    calc
      (s - t).partial N = ∑ n ∈ Finset.Icc (min s.m t.m) N, (s.seq n - t.seq n) := rfl
      _ = (∑ n ∈ Finset.Icc (min s.m t.m) N, s.seq n) - (∑ n ∈ Finset.Icc (min s.m t.m) N, t.seq n) := by
        rw [Finset.sum_sub_distrib]
      _ = (∑ n ∈ Finset.Icc s.m N, s.seq n) - (∑ n ∈ Finset.Icc t.m N, t.seq n) := by
        rw [h_s_eq, h_t_eq]
      _ = s.partial N - t.partial N := rfl
      _ = (s.partial - t.partial) N := rfl
  exact Filter.Tendsto.congr' h_eventually.symm (Filter.Tendsto.sub hs ht)

theorem Series.sub {s t:Series} (hs: s.converges) (ht: t.converges) :
    (s - t).converges ∧ (s-t).sum = s.sum - t.sum := by
  have hsum := convergesTo_sum hs
  have hsumt := convergesTo_sum ht
  have h_sub : (s - t).convergesTo (s.sum - t.sum) := hsum.sub hsumt
  refine ⟨converges_of_convergesTo h_sub, sum_of_converges h_sub⟩

abbrev Series.from (s:Series) (m₁:ℤ) : Series := mk' (m := max s.m m₁) (fun n ↦ s.seq (n:ℤ))

/-- Proposition 7.2.14 (c) (Series laws) / Exercise 7.2.5 -/
theorem Series.converges_from (s:Series) (k:ℕ) : s.converges ↔ (s.from (s.m+k)).converges := by
  have hm : (s.from (s.m + k)).m = s.m + (k : ℤ) := by
    simp
  have hseq_eq (n : ℤ) (hn : s.m + (k : ℤ) ≤ n) : (s.from (s.m + k)).seq n = s.seq n := by
    simp [hn]
  rw [converges_iff_tail_decay, converges_iff_tail_decay, hm]
  constructor
  · intro h ε hε
    rcases h ε hε with ⟨N, hN, hN'⟩
    refine ⟨max N (s.m + (k : ℤ)), le_max_right _ _, λ p hp q hq => ?_⟩
    have hp_sm_k : s.m + (k : ℤ) ≤ p := le_of_max_le_right hp
    have hq_sm_k : s.m + (k : ℤ) ≤ q := le_of_max_le_right hq
    have hp' : p ≥ N := le_of_max_le_left hp
    have hq' : q ≥ N := le_of_max_le_left hq
    have h_sum_eq : ∑ n ∈ Finset.Icc p q, (s.from (s.m + k)).seq n = ∑ n ∈ Finset.Icc p q, s.seq n :=
      Finset.sum_congr rfl fun n hn => by
        have hmem := Finset.mem_Icc.mp hn
        have hn_ge : s.m + (k : ℤ) ≤ n := by omega
        exact hseq_eq n hn_ge
    rw [h_sum_eq]
    exact hN' p hp' q hq'
  · intro h ε hε
    rcases h ε hε with ⟨N, hN, hN'⟩
    refine ⟨N, by omega, λ p hp q hq => ?_⟩
    have hp_sm_k : s.m + (k : ℤ) ≤ p := le_trans hN hp
    have hq_sm_k : s.m + (k : ℤ) ≤ q := le_trans hN hq
    have h_sum_eq : ∑ n ∈ Finset.Icc p q, s.seq n = ∑ n ∈ Finset.Icc p q, (s.from (s.m + k)).seq n :=
      Finset.sum_congr rfl fun n hn => by
        have hmem := Finset.mem_Icc.mp hn
        have hn_ge : s.m + (k : ℤ) ≤ n := by omega
        exact (hseq_eq n hn_ge).symm
    rw [h_sum_eq]
    exact hN' p hp q hq

theorem Series.sum_from {s:Series} (k:ℕ) (h: s.converges) :
    s.sum = ∑ n ∈ Finset.Ico s.m (s.m+k), s.seq n + (s.from (s.m+k)).sum := by
  have h_convFrom : (s.from (s.m + k)).converges := ((converges_from s k).mp h)
  have h_tendsto_s : s.convergesTo s.sum := convergesTo_sum h
  have h_tendsto_from : (s.from (s.m + k)).convergesTo (s.from (s.m + k)).sum := convergesTo_sum h_convFrom
  set A := ∑ n ∈ Finset.Ico s.m (s.m + (k : ℤ)), s.seq n with hA
  have h_from_partial (N : ℤ) (hN : N ≥ s.m + (k : ℤ)) : (s.from (s.m + k)).partial N = ∑ n ∈ Finset.Icc (s.m + (k : ℤ)) N, s.seq n := by
    unfold Series.from Series.partial
    simp
    refine Finset.sum_congr rfl ?_
    intro n hn
    have hn' : s.m + (k : ℤ) ≤ n := (Finset.mem_Icc.mp hn).1
    simp [hn']
  have h_partial_eq : ∀ N ≥ s.m + (k : ℤ), s.partial N = A + (s.from (s.m + k)).partial N := by
    intro N hN
    calc
      s.partial N = ∑ n ∈ Finset.Icc s.m N, s.seq n := rfl
      _ = (∑ n ∈ Finset.Ico s.m (s.m + (k : ℤ)), s.seq n) + (∑ n ∈ Finset.Icc (s.m + (k : ℤ)) N, s.seq n) := by
        have h_union : Finset.Ico s.m (s.m + (k : ℤ)) ∪ Finset.Icc (s.m + (k : ℤ)) N = Finset.Icc s.m N := by
          ext n; simp; omega
        have h_disjoint : Disjoint (Finset.Ico s.m (s.m + (k : ℤ))) (Finset.Icc (s.m + (k : ℤ)) N) := by
          apply Finset.disjoint_left.mpr; intro n hn1 hn2; simp at hn1 hn2; omega
        rw [← Finset.sum_union h_disjoint, h_union]
      _ = A + (s.from (s.m + k)).partial N := by
        rw [hA, h_from_partial N hN]
  have h_eventually_eq : s.partial =ᶠ[Filter.atTop] (fun N : ℤ => A + (s.from (s.m + k)).partial N) := by
    apply Filter.eventually_atTop.mpr
    refine ⟨s.m + (k : ℤ), λ N hN => ?_⟩
    rw [h_partial_eq N hN]
  have h_tendsto_g : Filter.atTop.Tendsto (fun (N : ℤ) => A + (s.from (s.m + k)).partial N) (nhds (A + (s.from (s.m + k)).sum)) :=
    h_tendsto_from.const_add A
  have h_tendsto_s' : Filter.atTop.Tendsto s.partial (nhds (A + (s.from (s.m + k)).sum)) :=
    Filter.Tendsto.congr' h_eventually_eq.symm h_tendsto_g
  have h_uniq := tendsto_nhds_unique h_tendsto_s h_tendsto_s'
  simpa [hA] using h_uniq

/-- Proposition 7.2.14 (d) (Series laws) / Exercise 7.2.5 -/
theorem Series.shift {s:Series} {x:ℝ} (h: s.convergesTo x) (L:ℤ) :
    (mk' (m := s.m + L) (fun n ↦ s.seq (n - L))).convergesTo x := by
  unfold Series.convergesTo
  set t := mk' (m := s.m + L) (fun n : {k : ℤ // k ≥ s.m + L} ↦ s.seq (n.val - L)) with ht
  have h_partial_eq : ∀ N, s.m + L ≤ N → t.partial N = s.partial (N - L) := by
    intro N hN
    unfold t Series.partial
    calc
      (∑ n ∈ Finset.Icc (s.m + L) N, (mk' (m := s.m + L) (fun n : {k : ℤ // k ≥ s.m + L} ↦ s.seq (n.val - L))).seq n)
          = (∑ n ∈ Finset.Icc (s.m + L) N, s.seq (n - L)) := by
        refine Finset.sum_congr rfl fun n hn => ?_
        have hn' : n ≥ s.m + L := (Finset.mem_Icc.mp hn).1
        simp [hn']
      _ = (∑ k ∈ Finset.Icc s.m (N - L), s.seq k) := by
        have h_image : (Finset.Icc (s.m + L) N).image (fun n : ℤ => n - L) = Finset.Icc s.m (N - L) := by
          ext k
          constructor
          · intro hk
            rcases Finset.mem_image.mp hk with ⟨n, hn, rfl⟩
            have hmem := Finset.mem_Icc.mp hn
            refine Finset.mem_Icc.mpr ⟨by omega, by omega⟩
          · intro hk
            have hmem := Finset.mem_Icc.mp hk
            have hmem' : k + L ∈ Finset.Icc (s.m + L) N :=
              Finset.mem_Icc.mpr ⟨by omega, by omega⟩
            refine Finset.mem_image.mpr ⟨k + L, hmem', ?_⟩
            omega
        calc
          (∑ n ∈ Finset.Icc (s.m + L) N, s.seq (n - L)) =
              (∑ k ∈ (Finset.Icc (s.m + L) N).image (fun n : ℤ => n - L), s.seq k) := by
            symm
            apply Finset.sum_image
            intro x hx y hy h
            linarith
          _ = (∑ k ∈ Finset.Icc s.m (N - L), s.seq k) := by rw [h_image]
      _ = s.partial (N - L) := rfl
  have h_eventually : t.partial =ᶠ[Filter.atTop] (fun N : ℤ => s.partial (N - L)) := by
    apply Filter.eventually_atTop.mpr
    refine ⟨s.m + L, ?_⟩
    intro N hN
    exact h_partial_eq N hN
  have h_tendsto_shift : Filter.atTop.Tendsto (fun N : ℤ => s.partial (N - L)) (nhds x) := by
    have h_shift : Filter.atTop.Tendsto (fun N : ℤ => N - L) Filter.atTop := by
      apply Filter.tendsto_atTop_atTop.mpr
      intro M
      refine ⟨M + L, ?_⟩
      intro N hN
      omega
    exact h.comp h_shift
  exact Filter.Tendsto.congr' h_eventually.symm h_tendsto_shift

/-- Lemma 7.2.15 (telescoping series) / Exercise 7.2.6 -/
theorem Series.telescope {a:ℕ → ℝ} (ha: Filter.atTop.Tendsto a (nhds 0)) :
    ((fun n:ℕ ↦ a n - a (n+1)):Series).convergesTo (a 0) := by
  unfold Series.convergesTo
  set s := ((fun n:ℕ ↦ a n - a (n+1)):Series) with hs
  have hm : s.m = 0 := rfl
  have h_partial_eq (N : ℤ) (hN : 0 ≤ N) : s.partial N = a 0 - a (N.toNat + 1) := by
    refine Int.le_induction ?base ?step N hN
    · unfold s Series.partial
      simp
    · intro k hk IH
      have hk_ge_m_sub_one : k ≥ s.m - 1 := by
        rw [hm]
        omega
      have hk_toNat_succ : ((k+1 : ℤ).toNat : ℕ) = k.toNat + 1 := by
        omega
      have hseq_val : s.seq (k+1 : ℤ) = a (k.toNat + 1) - a (k.toNat + 2) := by
        dsimp [s]
        have hpos : (0 : ℤ) ≤ (k+1 : ℤ) := by omega
        simp [hpos, hk_toNat_succ]
      calc
        s.partial (k+1) = s.partial k + s.seq (k+1) := by
          rw [partial_succ s hk_ge_m_sub_one]
        _ = (a 0 - a (k.toNat + 1)) + (a (k.toNat + 1) - a (k.toNat + 2)) := by rw [IH, hseq_val]
        _ = a 0 - a (k.toNat + 2) := by ring
        _ = a 0 - a (((k+1 : ℤ).toNat : ℕ) + 1) := by rw [hk_toNat_succ]
  have h_eventually : s.partial =ᶠ[Filter.atTop] (fun (N : ℤ) => a 0 - a (N.toNat + 1)) := by
    apply Filter.eventually_atTop.mpr
    refine ⟨0, λ N hN => h_partial_eq N hN⟩
  have h_tendsto_a : Filter.atTop.Tendsto (fun (N : ℤ) => a (N.toNat + 1)) (nhds 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have ha' : ∀ᶠ (n : ℕ) in Filter.atTop, dist (a n) 0 < ε := by
      rw [Metric.tendsto_nhds] at ha
      exact ha ε hε
    rcases Filter.eventually_atTop.mp ha' with ⟨M, hM⟩
    apply Filter.eventually_atTop.mpr
    refine ⟨(M : ℤ), λ N hN => ?_⟩
    have hN_nonneg : 0 ≤ N := by omega
    have hN_eq : (N.toNat : ℤ) = N := Int.toNat_of_nonneg hN_nonneg
    have hM_N_toNat : (M : ℤ) ≤ (N.toNat : ℤ) := by rwa [hN_eq]
    have hN_toNat_ge_M : N.toNat + 1 ≥ M := by
      have hM_N_nat : M ≤ N.toNat := by exact_mod_cast hM_N_toNat
      omega
    have hN_val : |a (N.toNat + 1)| < ε := by
      have := hM (N.toNat + 1) hN_toNat_ge_M
      rw [Real.dist_eq, sub_zero] at this
      exact this
    rw [Real.dist_eq, sub_zero]
    exact hN_val
  have h_target : Filter.atTop.Tendsto (fun (N : ℤ) => a 0 - a (N.toNat + 1)) (nhds (a 0)) := by
    simpa using (tendsto_const_nhds.sub h_tendsto_a)
  exact Filter.Tendsto.congr' h_eventually.symm h_target

/- Exercise 7.2.1  -/

def Series.exercise_7_2_1_convergent :
  Decidable ( (mk' (m := 1) (fun n ↦ (-1:ℝ)^(n:ℤ))).converges ) := by
  apply isFalse
  apply diverges_of_nodecay
  intro h
  have h' := (Metric.tendsto_nhds.mp h) 1 (by norm_num : (0 : ℝ) < 1)
  rcases Filter.eventually_atTop.mp h' with ⟨N, hN⟩
  set M := max N 1 with hM
  have hMN : M ≥ N := le_max_left _ _
  have hM1 : M ≥ 1 := le_max_right _ _
  have hseqM : (mk' (m := 1) (fun n ↦ (-1:ℝ)^(n:ℤ))).seq M = (-1 : ℝ) ^ (M : ℤ) := by
    simp [hM1]
  have hN' : |(mk' (m := 1) (fun n ↦ (-1:ℝ)^(n:ℤ))).seq M| < 1 := by
    have := hN M hMN
    simpa [Real.dist_eq, sub_zero] using this
  rw [hseqM] at hN'
  have h_abs : |((-1 : ℝ) ^ (M : ℤ))| = 1 := by
    calc
      |((-1 : ℝ) ^ (M : ℤ))| = |(-1 : ℝ)| ^ (M : ℤ) := by rw [abs_zpow]
      _ = 1 ^ (M : ℤ) := by norm_num
      _ = 1 := by norm_num
  rw [h_abs] at hN'
  linarith


end Chapter7
