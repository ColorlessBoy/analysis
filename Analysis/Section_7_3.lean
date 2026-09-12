import Mathlib.Tactic
import Mathlib.Algebra.Field.Power
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Analysis.Section_6_1
import Analysis.Section_6_epilogue
import Analysis.Section_7_2

/-!
# Analysis I, Section 7.3: Sums of non-negative numbers

I have attempted to make the translation as faithful a paraphrasing as possible of the original text.  When there is a choice between a more idiomatic Lean solution and a more faithful translation, I have generally chosen the latter.  In particular, there will be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main constructions and results of this section:

- Equivalent characterizations of convergence of nonnegative series.
- Cauchy condensation test.

-/

namespace Chapter7

open Real

abbrev Series.nonneg (s: Series) : Prop := ∀ n, s.seq n ≥ 0

abbrev Series.partial_of_nonneg {s: Series} (h: s.nonneg) : Monotone s.partial := by
  intro a b hle
  unfold Series.partial
  have hsubset : Finset.Icc s.m a ⊆ Finset.Icc s.m b := by
    intro x hx
    rw [Finset.mem_Icc] at hx ⊢
    exact ⟨hx.1, hx.2.trans hle⟩
  have hsum := Finset.sum_sdiff (f := s.seq) hsubset
  have hnonneg : 0 ≤ ∑ x ∈ (Finset.Icc s.m b \ Finset.Icc s.m a), s.seq x := by
    refine Finset.sum_nonneg (fun x hx => h x)
  have htemp : (∑ x ∈ Finset.Icc s.m a, s.seq x) + (∑ x ∈ (Finset.Icc s.m b \ Finset.Icc s.m a), s.seq x) = (∑ x ∈ Finset.Icc s.m b, s.seq x) := by
    simpa [add_comm] using hsum
  have htemp' : (∑ x ∈ Finset.Icc s.m a, s.seq x) ≤ (∑ x ∈ Finset.Icc s.m a, s.seq x) + (∑ x ∈ (Finset.Icc s.m b \ Finset.Icc s.m a), s.seq x) :=
    le_add_of_nonneg_right hnonneg
  exact htemp'.trans (le_of_eq htemp)

/-- Proposition 7.3.1 -/
theorem Series.converges_of_nonneg_iff {s: Series} (h: s.nonneg) : s.converges ↔ ∃ M, ∀ N, s.partial N ≤ M := by
  -- This broadly follows the argument in the text, though for one direction I choose to use Mathlib routines rather than Chapter6 results.
  constructor
  . intro hconv
    set S : Chapter6.Sequence := ⟨ s.m, s.partial, by intro n hn; simp [Series.partial, hn] ⟩
    have : S.IsBounded := by
      apply S.bounded_of_convergent
      rw [Chapter6.Sequence.converges_iff_Tendsto']
      grind
    choose M hpos hM using this
    use M; peel hM with N hM
    exact (le_abs_self _).trans hM
  intro hbound
  obtain hinfin | hfin := tendsto_atTop_of_monotone (partial_of_nonneg h)
  . choose M hM using hbound
    choose N hN using (hinfin.eventually_gt_atTop M).exists
    grind
  assumption

theorem Series.sum_of_nonneg_lt {s: Series} (h: s.nonneg) {M:ℝ} (hM: ∀ N, s.partial N ≤ M) : s.sum ≤ M := by
  have : ∃ M, ∀ N, s.partial N ≤ M  := by use M
  rw [←converges_of_nonneg_iff h] at this; simp [sum, this]
  have hconv := this.choose_spec; simp [convergesTo] at hconv; exact le_of_tendsto' hconv hM

theorem Series.partial_le_sum_of_nonneg {s: Series} (hnon: s.nonneg) (hconv: s.converges) (N : ℤ) :
  s.partial N ≤ s.sum := by
  apply (partial_of_nonneg hnon).ge_of_tendsto
  simp [sum, hconv]; exact hconv.choose_spec

/-- Some useful nonnegativity lemmas for later applications. -/
theorem Series.partial_nonneg {s: Series} (hnon: s.nonneg) (N : ℤ) : 0 ≤ s.partial N := by
  simp [Series.partial]; apply Finset.sum_nonneg; aesop

theorem Series.sum_of_nonneg {s:Series} (hnon: s.nonneg) : 0 ≤ s.sum := by
  by_cases h: s.converges <;> simp [Series.sum, h]
  exact ge_of_tendsto' h.choose_spec (partial_nonneg hnon)

/-- Corollary 7.3.2 (Comparison test) / Exercise 7.3.1 -/
theorem Series.converges_of_le {s t: Series} (hm: s.m = t.m) (hcomp: ∀ n ≥ s.m, |s.seq n| ≤ t.seq n) (hconv : t.converges) : s.absConverges ∧ |s.sum| ≤ s.abs.sum ∧ s.abs.sum ≤ t.sum := by
  have hm_abs_sm : s.abs.m = s.m := by dsimp [Series.abs]
  have h_nonneg_t : t.nonneg := by
    intro n
    by_cases hn : n < t.m
    · simp [t.vanish n hn]
    · have hn' : n ≥ s.m := by
        rw [hm]
        omega
      have h_bound : |s.seq n| ≤ t.seq n := hcomp n hn'
      have h_nonneg_abs : 0 ≤ |s.seq n| := abs_nonneg _
      exact le_trans h_nonneg_abs h_bound
  have h_nonneg_abs : s.abs.nonneg := by
    intro n
    dsimp [Series.abs, Series.mk']
    split
    · exact abs_nonneg _
    · norm_num
  have h_abs_conv : s.absConverges := by
    unfold absConverges
    rw [converges_iff_tail_decay]
    intro ε hε
    rcases (converges_iff_tail_decay t).mp hconv ε hε with ⟨N, hN, hN'⟩
    refine ⟨N, ?_, λ p hp q hq => ?_⟩
    · rw [hm_abs_sm]
      simpa [hm] using hN
    · have hp_sm : p ≥ s.m := by
        calc
          p ≥ N := hp
          _ ≥ t.m := hN
          _ = s.m := hm.symm
      have h_nonneg_sum_abs : 0 ≤ ∑ n ∈ Finset.Icc p q, s.abs.seq n :=
        Finset.sum_nonneg (λ n _ => h_nonneg_abs n)
      have h_sum_abs_eq : ∑ n ∈ Finset.Icc p q, s.abs.seq n = ∑ n ∈ Finset.Icc p q, |s.seq n| := by
        refine Finset.sum_congr rfl (λ n hn => ?_)
        have hn_sm : n ≥ s.m := le_trans hp_sm (Finset.mem_Icc.mp hn).1
        dsimp [Series.abs]
        simp [hn_sm]
      have h_sum_abs_le_sum_t : ∑ n ∈ Finset.Icc p q, s.abs.seq n ≤ |∑ n ∈ Finset.Icc p q, t.seq n| := by
        calc
          ∑ n ∈ Finset.Icc p q, s.abs.seq n = ∑ n ∈ Finset.Icc p q, |s.seq n| := h_sum_abs_eq
          _ ≤ ∑ n ∈ Finset.Icc p q, t.seq n :=
            Finset.sum_le_sum (λ n hn => hcomp n (le_trans hp_sm (Finset.mem_Icc.mp hn).1))
          _ = |∑ n ∈ Finset.Icc p q, t.seq n| := by
            rw [abs_of_nonneg (Finset.sum_nonneg (λ n _ => h_nonneg_t n))]
      calc
        |∑ n ∈ Finset.Icc p q, s.abs.seq n| = ∑ n ∈ Finset.Icc p q, s.abs.seq n :=
          abs_of_nonneg h_nonneg_sum_abs
        _ ≤ |∑ n ∈ Finset.Icc p q, t.seq n| := h_sum_abs_le_sum_t
        _ ≤ ε := hN' p hp q hq
  have h_abs_sum_le_t_sum : s.abs.sum ≤ t.sum := by
    apply sum_of_nonneg_lt h_nonneg_abs
    intro N
    calc
      s.abs.partial N ≤ t.partial N := by
        unfold Series.partial
        calc
          ∑ n ∈ Finset.Icc s.abs.m N, s.abs.seq n = ∑ n ∈ Finset.Icc s.m N, s.abs.seq n := by rw [hm_abs_sm]
          _ = ∑ n ∈ Finset.Icc s.m N, |s.seq n| := by
            refine Finset.sum_congr rfl (λ n hn => ?_)
            have hn_sm : n ≥ s.m := (Finset.mem_Icc.mp hn).1
            dsimp [Series.abs]
            simp [hn_sm]
          _ ≤ ∑ n ∈ Finset.Icc s.m N, t.seq n :=
            Finset.sum_le_sum (λ n hn => hcomp n (Finset.mem_Icc.mp hn).1)
          _ = ∑ n ∈ Finset.Icc t.m N, t.seq n := by rw [hm]
          _ = t.partial N := rfl
      _ ≤ t.sum := partial_le_sum_of_nonneg h_nonneg_t hconv N
  have h_abs_le : |s.sum| ≤ s.abs.sum := abs_le h_abs_conv
  exact ⟨h_abs_conv, h_abs_le, h_abs_sum_le_t_sum⟩

theorem Series.diverges_of_ge {s t: Series} (hm: s.m = t.m) (hcomp: ∀ n ≥ s.m, |s.seq n| ≤ t.seq n) (hdiv: ¬ s.absConverges) : t.diverges := by
  intro hconv_t
  apply hdiv
  have h := converges_of_le hm hcomp hconv_t
  exact h.1

/-- Lemma 7.3.3 (Geometric series) / Exercise 7.3.2 -/
theorem Series.converges_geom {x: ℝ} (hx: |x| < 1) : (fun n ↦ x ^ n : Series).convergesTo (1 / (1 - x)) := by
  set s := (fun n : ℕ ↦ x ^ n : Series) with hs
  have hsm : s.m = 0 := rfl
  have hx_ne_one : x ≠ 1 := by
    intro h
    have : |x| = 1 := by simp [h]
    linarith
  have h_partial_nat (k : ℕ) : s.partial (k : ℤ) = ∑ i ∈ Finset.range (k+1), x ^ i := by
    induction' k with m ih
    · simp [s, Series.partial]
    · have hm_nonneg : (m : ℤ) ≥ s.m - 1 := by
        rw [hsm]; omega
      have hseq : s.seq ((m : ℤ) + 1) = x ^ (m+1 : ℕ) := by
        dsimp [s]
        have hpos : (m : ℤ) + 1 ≥ 0 := by omega
        simp [hpos]
      calc
        s.partial ((m+1 : ℕ) : ℤ) = s.partial ((m : ℤ) + 1) := by norm_cast
        _ = s.partial (m : ℤ) + s.seq ((m : ℤ) + 1) :=
          Series.partial_succ s hm_nonneg
        _ = s.partial (m : ℤ) + x ^ (m+1 : ℕ) := by rw [hseq]
        _ = (∑ i ∈ Finset.range (m+1), x ^ i) + x ^ (m+1 : ℕ) := by rw [ih]
        _ = ∑ i ∈ Finset.range (m+1+1), x ^ i := by
          rw [← Finset.sum_range_succ]
  have h_hasSum' : HasSum (fun (n : ℕ) => x ^ n) (1 / (1 - x)) := by
    have h := hasSum_geometric_of_abs_lt_one hx
    have hsum_eq : (1 - x)⁻¹ = 1 / (1 - x) := inv_eq_one_div _
    rw [← hsum_eq]
    exact h
  have h_tendsto_nat_range : Filter.Tendsto (fun (k : ℕ) => ∑ i ∈ Finset.range (k+1), x ^ i)
      Filter.atTop (nhds (1 / (1 - x))) :=
    h_hasSum'.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)
  have h_tendsto_nat_partial : Filter.Tendsto (fun (k : ℕ) => s.partial (k : ℤ))
      Filter.atTop (nhds (1 / (1 - x))) := by
    simpa [h_partial_nat] using h_tendsto_nat_range
  have h_dist_nat : ∀ ε > (0 : ℝ), ∃ (K : ℕ), ∀ (k : ℕ), k ≥ K → dist (s.partial (k : ℤ)) (1 / (1 - x)) < ε :=
    Metric.tendsto_atTop.mp h_tendsto_nat_partial
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  rcases h_dist_nat ε hε with ⟨K, hK⟩
  use (K : ℤ)
  intro N hN
  have hN_nonneg : 0 ≤ N := by omega
  have hN_nat_ge_K : N.toNat ≥ K := by
    have h_eq_N : (N.toNat : ℤ) = N := by exact mod_cast Int.toNat_of_nonneg hN_nonneg
    have h_N_nat_ge_K : (N.toNat : ℤ) ≥ (K : ℤ) := by
      rw [h_eq_N]
      exact hN
    exact Nat.cast_le.mp h_N_nat_ge_K
  calc
    dist (s.partial N) (1 / (1 - x)) = |s.partial N - (1 / (1 - x))| := by rw [Real.dist_eq]
    _ = |s.partial (N.toNat : ℤ) - (1 / (1 - x))| := by
      have : (N.toNat : ℤ) = N := by exact mod_cast Int.toNat_of_nonneg hN_nonneg
      rw [this]
    _ = dist (s.partial (N.toNat : ℤ)) (1 / (1 - x)) := by rw [Real.dist_eq]
    _ < ε := hK (N.toNat) hN_nat_ge_K

theorem Series.absConverges_geom {x: ℝ} (hx: |x| < 1) : (fun n ↦ x ^ n : Series).absConverges := by
  unfold Series.absConverges
  have h_abs_x : |(|x|)| < 1 := by
    simpa [abs_abs] using hx
  have h_abs_eq : ((fun n : ℕ ↦ x ^ n : Series).abs : Series) = (fun n : ℕ ↦ |x| ^ n : Series) := by
    ext n
    · simp
    · simp
      by_cases h : 0 ≤ n
      · simp [h, abs_pow]
      · simp [h]
  rw [h_abs_eq]
  exact converges_of_convergesTo (converges_geom h_abs_x)

theorem Series.diverges_geom {x: ℝ} (hx: |x| ≥ 1) : (fun n ↦ x ^ n : Series).diverges := by
  apply diverges_of_nodecay
  intro h
  have h' := (Metric.tendsto_nhds.mp h) (1/2) (by norm_num : (0 : ℝ) < 1/2)
  rcases Filter.eventually_atTop.mp h' with ⟨N, hN⟩
  set M := max N 0 with hM
  have hMN : M ≥ N := le_max_left _ _
  have hM0 : M ≥ 0 := le_max_right _ _
  have h_bound : |x| ^ (M.toNat : ℕ) < 1/2 := by
    have := hN M hMN
    simpa [hM0, Real.dist_eq, sub_zero, abs_pow] using this
  have h_abs_ge_one : |x| ^ (M.toNat : ℕ) ≥ 1 := by
    calc
      |x| ^ (M.toNat : ℕ) ≥ (1 : ℝ) ^ (M.toNat : ℕ) := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hx (M.toNat : ℕ)
      _ = 1 := by simp
  linarith

theorem Series.converges_geom_iff (x: ℝ) : (fun n ↦ x ^ n : Series).converges ↔ |x| < 1 := by
  constructor
  · intro h
    by_contra! hx
    -- hx : |x| ≥ 1
    have h_div := diverges_geom hx
    apply h_div
    exact h
  · intro hx
    have h_convTo := converges_geom hx
    exact converges_of_convergesTo h_convTo

/-- Proposition 7.3.4 (Cauchy criterion) -/
theorem Series.cauchy_criterion {s:Series} (hm: s.m = 1) (hs:s.nonneg) (hmono: ∀ n ≥ 1, s.seq (n+1) ≤ s.seq n) : s.converges ↔ (fun k ↦ 2^k * s.seq (2^k): Series).converges := by
  -- This proof is written to follow the structure of the original text.
  set t := (fun k ↦ 2^k * s.seq (2^k):Series)
  have ht: t.nonneg := by intro n; by_cases h: n ≥ 0 <;> simp [t,h]; grind
  have hmono' : ∀ n ≥ 1, ∀ m ≥ n, s.seq m ≤ s.seq n := by
    intro n hn m hm; obtain ⟨ k, rfl ⟩ := Int.le.dest hm; clear hm
    induction' k with k hk; simp
    convert (hmono (n+k) (by grind)).trans hk using 2; grind
  have htm : t.m = 0 := by simp [t]
  rw [converges_of_nonneg_iff hs, converges_of_nonneg_iff ht]
  set S := s.partial
  set T := t.partial
  have Lemma_7_3_6 (K:ℕ) : S (2^(K+1) - 1) ≤ T K ∧ T K ≤ 2 * S (2^K) := by
    induction' K with K hK
    . simp [S,T,Series.partial, hm, t]; grind
    observe h2K : 1 ≤ 2^K; observe h2K' : 1 ≤ 2^(K+1)
    choose hK1 hK2 using hK
    have claim1 : T (K + 1) = T K + 2^(K+1) * s.seq (2^(K+1)) := by apply t.partial_succ; grind
    have claim2a : S (2^(K+1)) ≥ S (2^K) + 2^K * s.seq (2^(K+1)) := calc
      _ = S (2^K) + ∑ n ∈ .Ioc (2^K) (2^(K+1)), s.seq n := by
        have : Disjoint (Finset.Icc s.m (2^K)) (Finset.Ioc (2^K) (2^(K+1))) := by
          rw [Finset.disjoint_iff_ne]; intro x hx y hy; simp at hx hy; linarith
        convert Finset.sum_union this
        ext x; simp; constructor
        . intro ⟨h1, h2⟩; simp [h1, h2, le_or_gt]
        rintro (⟨ h1, h2 ⟩ | ⟨ h1, h2 ⟩)
        . simp [h1,pow_succ']; linarith
        simp [h2, hm]; grind
      _ ≥ S (2^K) + ∑ n ∈ .Ioc ((2:ℤ)^K) (2^(K+1)), s.seq (2^(K+1)) := by
        gcongr with n hn; simp at hn; exact hmono' _ (by grind) _ hn.2
      _ = _ := by simp [pow_succ']; left; ring_nf; norm_cast
    have claim2 : 2 * S (2^(K+1)) ≥ 2 * S (2^K) + 2^(K+1) * s.seq (2^(K+1)) := by
      nth_rewrite 2 [pow_succ']; grind
    have claim3 : S (2^(K+1+1) - 1) ≤ S (2^(K+1)-1) + 2^(K+1) * s.seq (2^(K+1)) := calc
      _ = S (2^(K+1)-1) + ∑ n ∈ .Icc (2^(K+1)) (2^(K+1+1)-1), s.seq n := by
        have : Disjoint (Finset.Icc s.m (2^(K+1)-1)) (Finset.Icc (2^(K+1)) (2^(K+1+1)-1)) := by
          rw [Finset.disjoint_iff_ne]; intro x hx y hy; simp at hx hy; linarith
        convert Finset.sum_union this
        ext; simp; constructor
        . intro ⟨h1, h2⟩; simp [h1, h2]; omega
        rintro (⟨ h1, h2 ⟩ | ⟨ h1, h2 ⟩)
        . simp [h1, pow_succ' _ (K+1)]; linarith
        simp [h2, hm]; linarith
      _ ≤ S (2^(K+1)-1) + ∑ n ∈ .Icc ((2:ℤ)^(K+1)) (2^(K+1+1)-1), s.seq (2^(K+1)) := by
        gcongr with n hn; simp at hn; apply hmono' _ _ _ hn.1; linarith
      _ = _ := by simp [pow_succ']; left; ring_nf; norm_cast
    simp; constructor <;> grind
  constructor
  . intro ⟨ M, hM ⟩; use 2*M; intro N; obtain hN | hN := lt_or_ge N 0
    . simp [T, Series.partial, htm, hN]; convert hM 0; simp [S, Series.partial, hm]
    rw [Int.eq_natCast_toNat.mpr hN]; apply (Lemma_7_3_6 N.toNat).2.trans; grind
  intro ⟨ M, hM ⟩; use M; intro K'; obtain hK' | hK' := lt_or_ge K' 1
  . simp [S, Series.partial, hm, hK']; convert hM (-1)
  set K := (K'-1).toNat; have hK : K' = K + 1 := by rw [Int.toNat_of_nonneg (by linarith)]; abel
  calc
    _ ≤ S (2 ^ (K+1) - 1) := by
      apply partial_of_nonneg hs; rw [hK]
      generalize K = n; induction' n with n hn; simp
      simp [pow_succ] at *; linarith
    _ ≤ T K := (Lemma_7_3_6 K).1
    _ ≤ M := hM K

/-- Corollary 7.3.7 -/
theorem Series.converges_qseries (q: ℝ) (hq: q > 0) : (mk' (m := 1) fun n ↦ 1 / (n:ℝ) ^ q : Series).converges ↔ (q>1) := by
  -- This proof is written to follow the structure of the original text.
  set s := (mk' (m := 1) fun n ↦ 1 / (n:ℝ) ^ q : Series)
  have hs : s.nonneg := by intro n; simp [s]; by_cases h : 1 ≤ n <;> simp [h]; positivity
  have hmono : ∀ n ≥ 1, s.seq (n+1) ≤ s.seq n := by
    intro n hn
    have hn1 : n ≥ 0 := by positivity
    have hn3 : n.toNat > 0 := by omega
    simp [s, hn, hn1]
    apply_rules [inv_anti₀, rpow_le_rpow] <;> try positivity
    simp
  rw [cauchy_criterion (by simp [s]) hs hmono]
  have (n:ℕ) : 2^n * s.seq (2^n) = (2^(1-q))^n := by
    have : 1 ≤ (2:ℤ)^n := by norm_cast; exact Nat.one_le_two_pow
    simp [s, this]
    rw [←rpow_neg, mul_comm, ←rpow_add_one, rpow_pow_comm] <;> (try positivity); grind
  simp [this, converges_geom_iff]
  rw [abs_of_nonneg, rpow_lt_one_iff_of_pos] <;> try positivity
  simp

/-- Remark 7.3.8 -/
theorem Series.zeta_eq {q:ℝ} (hq: q > 1) : (mk' (m := 1) fun n ↦ 1 / (n:ℝ) ^ q : Series).sum = riemannZeta q := by
  -- `riemannZeta` is defined over the complex numbers, so some preliminary work is needed to specialize to the reals.
  set L := ∑' n:ℕ, 1 / (n+1:ℝ)^q
  have hL : L = riemannZeta q := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by norm_cast)]
    convert Complex.ofReal_tsum _ with n
    simp [Complex.ofReal_cpow (x := n+1) (by positivity) _]
  rw [←hL]
  norm_cast; apply sum_of_converges
  have : Summable (fun (n : ℕ)↦ 1 / (n+1:ℝ) ^ q) := by
    convert (summable_one_div_nat_add_rpow 1 q).mpr hq using 4 with n
    rw [abs_of_nonneg]; positivity
  have tail (a: ℤ → ℝ) (L:ℝ) : Filter.atTop.Tendsto a (nhds L) ↔ Filter.atTop.Tendsto (fun n:ℕ ↦ a n) (nhds L) := by
    convert Filter.tendsto_map'_iff (g:= fun n:ℕ ↦ (n:ℤ) )
    simp
  unfold convergesTo
  rw [tail _ L]
  convert Summable.tendsto_sum_tsum_nat this with n
  simp [Series.partial]
  set e : ℕ ↪ ℤ := {
    toFun n := n+1
    inj' _ _ _ := by grind
  }
  convert Finset.sum_map _ e _ using 2 with n _ m hm
  . ext x; simp [e]; constructor
    . intro ⟨ _, _ ⟩; use (x-1).toNat; omega
    grind
  simp [e]

theorem Series.Basel_problem :  (mk' (m := 1) fun n ↦ 1 / (n:ℝ) ^ 2 : Series).sum = Real.pi ^ 2 / 6 := by
  have := zeta_eq (show 2 > 1 by norm_num)
  simp [Complex.ofReal_ofNat, riemannZeta_two] at this
  simpa [←Complex.ofReal_inj]

/-- Exercise 7.3.3 -/
theorem Series.nonneg_sum_zero {a:ℕ → ℝ} (ha: (a:Series).nonneg) (hconv: (a:Series).converges) : (a:Series).sum = 0 ↔ ∀ n, a n = 0 := by
  constructor
  · intro hsum0 n
    have h_nonneg_n : (a : Series).seq (n : ℤ) ≥ 0 := ha (n : ℤ)
    have han_nonneg : 0 ≤ a n := by simpa using h_nonneg_n
    have hmem : (n : ℤ) ∈ Finset.Icc ((a : Series).m : ℤ) (n : ℤ) := by
      have hm : (a : Series).m = (0 : ℤ) := rfl
      rw [hm]
      exact Finset.mem_Icc.mpr ⟨Nat.cast_nonneg n, le_refl _⟩
    have hpartial_ge : (a : Series).seq (n : ℤ) ≤ (a : Series).partial (n : ℤ) :=
      Finset.single_le_sum (fun i hi => ha i) hmem
    have hsum_ge : (a : Series).partial (n : ℤ) ≤ (a : Series).sum :=
      partial_le_sum_of_nonneg ha hconv (n : ℤ)
    have han_le_zero : a n ≤ 0 := by
      calc
        a n = (a : Series).seq (n : ℤ) := by simp
        _ ≤ (a : Series).partial (n : ℤ) := hpartial_ge
        _ ≤ (a : Series).sum := hsum_ge
        _ = 0 := hsum0
    linarith
  · intro hzero
    have hzero_seq : ∀ (i : ℤ), (a : Series).seq i = 0 := by
      intro i
      by_cases hi : i < (a : Series).m
      · exact (a : Series).vanish i hi
      · have hm : (a : Series).m = (0 : ℤ) := rfl
        have hi_nonneg : 0 ≤ i := by
          rw [hm] at hi
          omega
        simp [hi_nonneg, hzero (i.toNat)]
    have hzero_partial : ∀ (N : ℤ), (a : Series).partial N = 0 := by
      intro N
      unfold Series.partial
      apply Finset.sum_eq_zero
      intro i hi
      exact hzero_seq i
    have hsum0 : (a : Series).sum = 0 := by
      have hconv0 : (a : Series).convergesTo 0 := by
        have hzero_fun : (a : Series).partial = fun _ => 0 := by
          ext N; exact hzero_partial N
        rw [Series.convergesTo, hzero_fun]; exact tendsto_const_nhds (x := (0 : ℝ))
      have h_eq : hconv.choose = 0 :=
        tendsto_nhds_unique hconv.choose_spec hconv0
      simp [Series.sum, hconv, h_eq]
    exact hsum0


end Chapter7
