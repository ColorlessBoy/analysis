import Mathlib.Tactic
import Analysis.Section_6_1
import Mathlib.Data.Nat.Nth
import Analysis.Section_9_6
/-!
# Analysis I, Section 9.9: Uniform continuity

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- API for Mathlib's {name}`UniformContinuousOn`.
- Continuous functions on compact intervals are uniformly continuous.

-/

open Chapter6 Filter

namespace Chapter9

example : ContinuousOn (fun x:ℝ ↦ 1/x) (.Ioo 0 2) := by
  refine (continuousOn_const.div continuousOn_id ?_)
  intro x hx; exact ne_of_gt hx.1

example : ¬ BddOn (fun x:ℝ ↦ 1/x) (.Ioo 0 2) := by
  intro h; rcases h with ⟨M, hM⟩
  have hmax_pos : 0 < max M 1 := lt_max_of_lt_right (by norm_num : (0 : ℝ) < 1)
  set x := 1 / (2 * max M 1) with hx
  have hx_mem : x ∈ Set.Ioo (0 : ℝ) 2 := by
    dsimp [x]
    have hpos : 2 * max M 1 > 0 := mul_pos (by norm_num) hmax_pos
    have h_lt : 2 * max M 1 > 1 := by
      have : max M 1 ≥ 1 := le_max_right _ _
      nlinarith
    constructor
    · positivity
    · calc
        1 / (2 * max M 1) < 1 / 1 := by
          refine (one_div_lt_one_div (by positivity) (by positivity)).mpr ?_
          nlinarith
        _ = 1 := by norm_num
        _ < 2 := by norm_num
  have h_val : |1 / x| = 2 * max M 1 := by
    dsimp [x]
    have hpos' : 2 * max M 1 > 0 := mul_pos (by norm_num) hmax_pos
    calc
      |1 / (1 / (2 * max M 1))| = |2 * max M 1| := by field_simp
      _ = 2 * max M 1 := abs_of_pos hpos'
  have h_contra := hM x hx_mem
  rw [h_val] at h_contra
  have : 2 * max M 1 > M := by
    have hmax_ge_M : max M 1 ≥ M := le_max_left _ _
    nlinarith
  nlinarith

/-- Example 9.9.1 -/
example (x : ℝ) :
  let f : ℝ → ℝ := fun x ↦ 1/x
  let ε : ℝ := 0.1
  let x₀ : ℝ := 1
  let δ : ℝ := 1/11
  |x-x₀| ≤ δ → |f x - f x₀| ≤ ε := by
  intro f ε x₀ δ h
  dsimp [f, x₀, δ, ε] at *
  have hx_low : (10 : ℝ)/11 ≤ x := by
    have h_low := (abs_le.mp h).1
    nlinarith
  have hx_pos : 0 < x := by nlinarith
  calc
    |1/x - 1/1| = |1/x - 1| := by norm_num
    _ = |(1-x)/x| := by
      have h_eq : 1/x - 1 = (1-x)/x := by
        field_simp [hx_pos.ne.symm]
      rw [h_eq]
    _ = |1-x| / |x| := by rw [abs_div]
    _ = |x-1| / x := by
      rw [abs_sub_comm, abs_of_pos hx_pos]
    _ ≤ (1/11) / x := by
      calc
        |x-1| / x = |x-1| * (1/x) := by ring
        _ ≤ (1/11) * (1/x) :=
          mul_le_mul_of_nonneg_right h (by positivity : 0 ≤ 1/x)
        _ = (1/11) / x := by ring
    _ ≤ (1/10 : ℝ) := by
      field_simp [hx_pos.ne.symm]
      nlinarith
    _ = (0.1 : ℝ) := by norm_num

example (x:ℝ) :
  let f : ℝ → ℝ := fun x ↦ 1/x
  let ε : ℝ := 0.1
  let x₀ : ℝ := 0.1
  let δ : ℝ := 1/1010
  |x-x₀| ≤ δ → |f x - f x₀| ≤ ε := by
  intro f ε x₀ δ h
  dsimp [f, x₀, δ, ε] at *
  have hx_low : (10 : ℝ)/101 ≤ x := by
    have h_low := (abs_le.mp h).1
    nlinarith
  have hx_pos : 0 < x := by nlinarith
  have h_one_div_01 : (1/0.1 : ℝ) = 10 := by norm_num
  calc
    |1/x - 1/0.1| = |1/x - 10| := by rw [h_one_div_01]
    _ = |(1 - 10*x)/x| := by
      have h_eq : 1/x - 10 = (1 - 10*x)/x := by
        field_simp [hx_pos.ne.symm]
      rw [h_eq]
    _ = |1 - 10*x| / |x| := by rw [abs_div]
    _ = |10*x - 1| / x := by
      rw [abs_sub_comm, abs_of_pos hx_pos]
    _ = 10 * |x - 0.1| / x := by
      calc
        |10*x - 1| / x = |10*(x - 0.1)| / x := by ring_nf
        _ = |(10 : ℝ)| * |x - 0.1| / x := by rw [abs_mul]
        _ = 10 * |x - 0.1| / x := by norm_num
    _ = |x - 0.1| * (10 / x) := by ring
    _ ≤ (1/1010) * (10 / x) :=
      mul_le_mul_of_nonneg_right h (by positivity : 0 ≤ 10 / x)
    _ = (10/1010) / x := by ring
    _ = (1/101) / x := by
      have h_num : (10/1010 : ℝ) = 1/101 := by norm_num
      rw [h_num]
    _ ≤ (1/10 : ℝ) := by
      field_simp [hx_pos.ne.symm]
      nlinarith
    _ = (0.1 : ℝ) := by norm_num

example (x:ℝ) :
  let g : ℝ → ℝ := fun x ↦ 2*x
  let ε : ℝ := 0.1
  let x₀ : ℝ := 1
  let δ : ℝ := 0.05
  |x-x₀| ≤ δ → |g x - g x₀| ≤ ε := by
  intro g ε x₀ δ h
  dsimp [g, x₀, δ, ε] at *
  calc
    |2*x - 2*1| = |2*(x - 1)| := by ring_nf
    _ = |2| * |x-1| := by rw [abs_mul]
    _ = 2 * |x-1| := by norm_num
    _ ≤ 2 * 0.05 := mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ) ≤ 2)
    _ = 0.1 := by norm_num

example (x₀ x : ℝ) :
  let g : ℝ → ℝ := fun x ↦ 2*x
  let ε : ℝ := 0.1
  let δ : ℝ := 0.05
  |x-x₀| ≤ δ → |g x - g x₀| ≤ ε := by
  intro g ε δ h
  dsimp [g, δ, ε] at *
  calc
    |2*x - 2*x₀| = |2*(x - x₀)| := by ring_nf
    _ = |2| * |x - x₀| := by rw [abs_mul]
    _ = 2 * |x - x₀| := by norm_num
    _ ≤ 2 * 0.05 := mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ) ≤ 2)
    _ = 0.1 := by norm_num

/-- Definition 9.9.2.  Here we use the Mathlib term {name}`UniformContinuousOn` -/
theorem UniformContinuousOn.iff (f: ℝ → ℝ) (X:Set ℝ) : UniformContinuousOn f X  ↔
  ∀ ε > (0:ℝ), ∃ δ > (0:ℝ), ∀ x₀ ∈ X, ∀ x ∈ X, δ.Close x x₀ → ε.Close (f x) (f x₀) := by
  simp_rw [Metric.uniformContinuousOn_iff_le, Real.Close]
  grind

theorem ContinuousOn.ofUniformContinuousOn {X:Set ℝ} (f: ℝ → ℝ) (hf: UniformContinuousOn f X) :
  ContinuousOn f X := by
  exact hf.continuousOn

theorem not_uniform_continuous_one_div_Ioo : ¬ UniformContinuousOn (fun x:ℝ ↦ 1/x) (Set.Ioo 0 2) := by
  rw [UniformContinuousOn.iff]
  push_neg
  refine ⟨1, by norm_num, ?_⟩
  intro δ hδ
  set δ' := min δ 1 with hδ'
  have hδ'pos : δ' > 0 := lt_min_iff.mpr ⟨hδ, by norm_num⟩
  have hδ'le1 : δ' ≤ 1 := min_le_right _ _
  have hδ'leδ : δ' ≤ δ := min_le_left _ _
  use δ'/2
  constructor
  · exact Set.mem_Ioo.mpr ⟨by nlinarith, by nlinarith⟩
  use δ'/4
  constructor
  · exact Set.mem_Ioo.mpr ⟨by nlinarith, by nlinarith⟩
  · constructor
    · dsimp [Real.Close, Real.dist_eq]
      have : |δ'/4 - δ'/2| = δ'/4 := by
        have hsub : δ'/4 - δ'/2 = -(δ'/4) := by ring
        rw [hsub, abs_neg, abs_of_pos (by nlinarith : (0 : ℝ) < δ'/4)]
      rw [this]
      nlinarith
    · dsimp [Real.Close, Real.dist_eq]
      have hcalc : 1/(δ'/4) - 1/(δ'/2) = 2/δ' := by
        field_simp [hδ'pos.ne.symm]
        ring
      rw [hcalc]
      have hpos2 : (0 : ℝ) < 2/δ' := by positivity
      rw [abs_of_pos hpos2]
      have : 2/δ' ≥ 2 := by
        field_simp [hδ'pos.ne.symm]
        nlinarith
      nlinarith

end Chapter9

/--
Definition 9.9.5.  This is similar but not identical to {name}`Real.CloseSeq` from
Section 6.1.
-/
abbrev Real.CloseSeqs (ε:ℝ) (a b: Chapter6.Sequence) : Prop :=
  (a.m = b.m) ∧ ∀ n ≥ a.m, ε.Close (a n) (b n)

abbrev Real.EventuallyCloseSeqs (ε:ℝ) (a b: Chapter6.Sequence) : Prop :=
  ∃ N ≥ a.m, ε.CloseSeqs (a.from N) (b.from N)

abbrev Chapter6.Sequence.equiv (a b: Sequence) : Prop :=
  ∀ ε > (0:ℝ), ε.EventuallyCloseSeqs a b

theorem Real.EventuallyCloseSeqs.mono {ε₁ ε₂ : ℝ} {a b : Chapter6.Sequence} (hε : ε₁ ≤ ε₂)
  (h : ε₁.EventuallyCloseSeqs a b) : ε₂.EventuallyCloseSeqs a b := by
  rcases h with ⟨N, hN, ⟨hm, hclose⟩⟩
  refine ⟨N, hN, ⟨hm, ?_⟩⟩
  intro n hn
  have hclose_n := hclose n hn
  exact hclose_n.trans hε

/-- Remark 9.9.6 -/
theorem Chapter6.Sequence.equiv_iff_rat (a b: Sequence) :
  a.equiv b ↔ ∀ ε > (0:ℚ), (ε:ℝ).EventuallyCloseSeqs a b := by
  constructor
  · intro h ε hε
    have hε' : (ε : ℝ) > (0 : ℝ) := by exact_mod_cast hε
    exact h (ε : ℝ) hε'
  · intro h ε hε
    have hεpos : (0 : ℝ) < ε := hε
    rcases exists_rat_btwn hεpos with ⟨q, hq1, hq2⟩
    have hqpos : (0 : ℚ) < q := by exact_mod_cast hq1
    have h' := h q hqpos
    have hqle : (q : ℝ) ≤ ε := by linarith
    exact Real.EventuallyCloseSeqs.mono hqle h'

/-- Lemma 9.9.7 / Exercise 9.9.1 -/
theorem Chapter6.Sequence.equiv_iff (a b: Sequence) :
  a.equiv b ↔ atTop.Tendsto (fun n ↦ a n - b n) (nhds 0) := by
  constructor
  · intro h
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hε2 : ε / 2 > 0 := by positivity
    rcases h (ε / 2) hε2 with ⟨M, hM, ⟨hm, hclose⟩⟩
    have hMax_eq_M : max a.m M = M := max_eq_right hM
    have hclose' : ∀ n : ℤ, n ≥ M → |a n - b n| ≤ ε / 2 := by
      intro n hn
      have hnm : n ≥ (a.from M).m := by
        simp [hMax_eq_M, hn]
      have h := hclose n hnm
      rw [Real.Close, Real.dist_eq] at h
      rw [Sequence.from_eval _ hn, Sequence.from_eval _ hn] at h
      exact h
    by_cases hM_nonneg : (0 : ℤ) ≤ M
    · set N : ℕ := Int.toNat M with hN_def
      use N
      intro n hn
      have hn_int : (n : ℤ) ≥ M := by
        have h : (n : ℤ) ≥ (N : ℤ) := by exact_mod_cast hn
        have hN_eq : (N : ℤ) = M := by rw [hN_def, Int.toNat_of_nonneg hM_nonneg]
        rw [hN_eq] at h
        exact h
      have hc := hclose' (n : ℤ) hn_int
      rw [Real.dist_eq]
      simp
      nlinarith
    · use 0
      intro n hn
      have hn_int : n ≥ M := by
        have hpos : (0 : ℤ) ≤ n := hn
        omega
      have hc := hclose' n hn_int
      rw [Real.dist_eq]
      simp
      nlinarith
  · intro h
    rw [Metric.tendsto_atTop] at h
    intro ε hε
    rcases h ε hε with ⟨N, hN⟩
    set M := max a.m (max b.m (max (N : ℤ) 0)) with hM_def
    have hM_ge_am : M ≥ a.m := le_max_left _ _
    have hM_ge_bm : M ≥ b.m := by
      calc
        M = max a.m (max b.m (max (N : ℤ) 0)) := rfl
        _ ≥ max b.m (max (N : ℤ) 0) := le_max_right _ _
        _ ≥ b.m := le_max_left _ _
    have hM_ge_N : M ≥ (N : ℤ) := by
      calc
        M = max a.m (max b.m (max (N : ℤ) 0)) := rfl
        _ ≥ max b.m (max (N : ℤ) 0) := le_max_right _ _
        _ ≥ max (N : ℤ) 0 := le_max_right _ _
        _ ≥ (N : ℤ) := le_max_left _ _
    have hM_nonneg : (0 : ℤ) ≤ M := by
      calc
        (0 : ℤ) ≤ max (N : ℤ) 0 := le_max_right _ _
        _ ≤ max b.m (max (N : ℤ) 0) := le_max_right _ _
        _ ≤ max a.m (max b.m (max (N : ℤ) 0)) := le_max_right _ _
        _ = M := rfl
    refine ⟨M, hM_ge_am, ?_⟩
    constructor
    · simp [max_eq_right hM_ge_am, max_eq_right hM_ge_bm]
    · intro n hn
      have hnM : n ≥ M := by
        have hmaxM : (a.from M).m = max a.m M := rfl
        have hM_eq_max : max a.m M = M := max_eq_right hM_ge_am
        simpa [Sequence.from, Sequence.mk', hM_eq_max] using hn
      rw [Real.Close, Real.dist_eq]
      have hn_nonneg : (0 : ℤ) ≤ n := le_trans hM_nonneg hnM
      set n' : ℕ := Int.toNat n with hn'_def
      have hn'_eq : (n' : ℤ) = n := by rw [hn'_def, Int.toNat_of_nonneg hn_nonneg]
      have hn'_ge_N : n' ≥ N := by
        have : (n' : ℤ) ≥ (N : ℤ) := by
          rw [hn'_eq]
          exact le_trans hM_ge_N hnM
        exact_mod_cast this
      have hN' : |(a n' - b n') - 0| < ε := hN n' hn'_ge_N
      have hN'clean : |a n' - b n'| < ε := by simpa using hN'
      have hN'le : |a (n' : ℤ) - b (n' : ℤ)| ≤ ε := hN'clean.le
      calc
        |(a.from M) n - (b.from M) n| = |a n - b n| := by
          rw [Sequence.from_eval a hnM, Sequence.from_eval b hnM]
        _ = |a (n' : ℤ) - b (n' : ℤ)| := by simp [hn'_eq]
        _ ≤ ε := hN'le


namespace Chapter9


/-- Proposition 9.9.8 / Exercise 9.9.2 -/
theorem UniformContinuousOn.iff_preserves_equiv {X:Set ℝ} (f: ℝ → ℝ) :
  UniformContinuousOn f X ↔
  ∀ x y: ℕ → ℝ, (∀ n, x n ∈ X) → (∀ n, y n ∈ X) →
  (x:Sequence).equiv (y:Sequence) →
  (f ∘ x:Sequence).equiv (f ∘ y:Sequence) := by
  constructor
  · intro hf x y hx hy hequiv
    rw [Sequence.equiv_iff] at hequiv
    have hz_iff_xy : atTop.Tendsto (fun (z : ℤ) ↦ ((x:Sequence) z - (y:Sequence) z)) (nhds 0) ↔
      atTop.Tendsto (fun (n : ℕ) ↦ x n - y n) (nhds 0) := by
      constructor
      · intro h
        have := h.comp (tendsto_natCast_atTop_atTop : atTop.Tendsto (fun n : ℕ ↦ (n : ℤ)) atTop)
        simpa using this
      · intro h
        rw [← Nat.map_cast_int_atTop, tendsto_map'_iff]
        simpa using h
    have htendsto : atTop.Tendsto (fun (n : ℕ) ↦ x n - y n) (nhds 0) := hz_iff_xy.mp hequiv
    rw [Sequence.equiv_iff]
    have hz_iff_fxy : atTop.Tendsto (fun (z : ℤ) ↦ ((f ∘ x : Sequence) z - (f ∘ y : Sequence) z)) (nhds 0) ↔
      atTop.Tendsto (fun (n : ℕ) ↦ f (x n) - f (y n)) (nhds 0) := by
      constructor
      · intro h
        have := h.comp (tendsto_natCast_atTop_atTop : atTop.Tendsto (fun n : ℕ ↦ (n : ℤ)) atTop)
        simpa using this
      · intro h
        rw [← Nat.map_cast_int_atTop, tendsto_map'_iff]
        simpa using h
    rw [hz_iff_fxy, Metric.tendsto_atTop]
    intro ε hε
    have hε2 : ε / 2 > 0 := by positivity
    rcases (UniformContinuousOn.iff f X).mp hf (ε / 2) hε2 with ⟨δ, hδ, hunif⟩
    rcases Metric.tendsto_atTop.mp htendsto δ hδ with ⟨N, hN⟩
    use N
    intro n hn
    rw [Real.dist_eq, sub_zero]
    have hx_dist : |x n - y n| < δ := by
      simpa [Real.dist_eq, sub_zero] using hN n hn
    have hx_n : x n ∈ X := hx n
    have hy_n : y n ∈ X := hy n
    have hfx_dist := hunif (y n) hy_n (x n) hx_n (by
      rw [Real.Close, Real.dist_eq]
      exact hx_dist.le)
    rw [Real.Close, Real.dist_eq] at hfx_dist
    nlinarith
  · intro h
    rw [UniformContinuousOn.iff]
    by_contra! h_not
    rcases h_not with ⟨ε, hε, hbad⟩
    have h_seq : ∀ n : ℕ, ∃ x₀ ∈ X, ∃ x ∈ X, (1 / ((n : ℝ) + 1)).Close x x₀ ∧ ¬ ε.Close (f x) (f x₀) := by
      intro n
      have hpos : (1 : ℝ)/((n : ℝ) + 1) > 0 := div_pos (by norm_num) (by positivity)
      rcases hbad (1 / ((n : ℝ) + 1)) hpos with ⟨x₀, hx₀, x, hx, hclose, h_notclose⟩
      refine ⟨x₀, hx₀, x, hx, hclose, ?_⟩
      rw [Real.Close, Real.dist_eq]
      intro hle
      rw [Real.dist_eq] at h_notclose
      linarith
    choose x₀ hx₀ x hx hx_close hx_notclose using h_seq
    have hequiv : (x₀:Sequence).equiv (x:Sequence) := by
      rw [Sequence.equiv_iff]
      have hz_iff : atTop.Tendsto (fun (z : ℤ) ↦ ((x₀:Sequence) z - (x:Sequence) z)) (nhds 0) ↔
        atTop.Tendsto (fun (n : ℕ) ↦ x₀ n - x n) (nhds 0) := by
        constructor
        · intro h
          have := h.comp (tendsto_natCast_atTop_atTop : atTop.Tendsto (fun n : ℕ ↦ (n : ℤ)) atTop)
          simpa using this
        · intro h
          rw [← Nat.map_cast_int_atTop, tendsto_map'_iff]
          simpa using h
      rw [hz_iff, Metric.tendsto_atTop]
      intro δ hδ
      rcases exists_nat_gt (1/δ) with ⟨N, hN⟩
      use N
      intro n hn
      rw [Real.dist_eq, sub_zero]
      calc
        |x₀ n - x n| = |x n - x₀ n| := abs_sub_comm _ _
        _ ≤ 1 / ((n : ℝ) + 1) := hx_close n
        _ ≤ 1 / ((N : ℝ) + 1) := by
          refine (one_div_le_one_div (by positivity) (by positivity)).mpr ?_
          have hN_n : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          nlinarith
        _ < δ := by
          calc
            1 / ((N : ℝ) + 1) < 1 / (1/δ) :=
              (one_div_lt_one_div (by positivity) (by positivity)).mpr (by
                have hN' : (1/δ : ℝ) < (N : ℝ) := hN
                nlinarith)
            _ = δ := by field_simp
    have h_non_equiv : ¬ ((f ∘ x₀ : Sequence).equiv (f ∘ x : Sequence)) := by
      intro h_eq
      rw [Sequence.equiv_iff] at h_eq
      have hz_iff_f : atTop.Tendsto (fun (z : ℤ) ↦ ((f ∘ x₀ : Sequence) z - (f ∘ x : Sequence) z)) (nhds 0) ↔
        atTop.Tendsto (fun (n : ℕ) ↦ f (x₀ n) - f (x n)) (nhds 0) := by
        constructor
        · intro h
          have := h.comp (tendsto_natCast_atTop_atTop : atTop.Tendsto (fun n : ℕ ↦ (n : ℤ)) atTop)
          simpa using this
        · intro h
          rw [← Nat.map_cast_int_atTop, tendsto_map'_iff]
          simpa using h
      have hn_contra : atTop.Tendsto (fun (n : ℕ) ↦ f (x₀ n) - f (x n)) (nhds 0) := hz_iff_f.mp h_eq
      rcases Metric.tendsto_atTop.mp hn_contra ε hε with ⟨N, hN⟩
      have h_contra := hN N (le_refl N)
      rw [Real.dist_eq, sub_zero] at h_contra
      have h_bad : |f (x₀ N) - f (x N)| > ε := by
        have h_not := hx_notclose N
        rw [Real.Close, Real.dist_eq] at h_not
        have hpos : |f (x N) - f (x₀ N)| > ε := by
          by_contra! hle
          exact h_not hle
        rw [abs_sub_comm]
        exact hpos
      nlinarith
    exact h_non_equiv (h x₀ x hx₀ hx hequiv)

/-- Remark 9.9.9 -/
theorem Chapter6.Sequence.equiv_const (x₀: ℝ) (x:ℕ → ℝ) : atTop.Tendsto x (nhds x₀) ↔
  (x:Sequence).equiv (fun _ : ℕ ↦ x₀ : Sequence) := by
  rw [Sequence.equiv_iff]
  have hz_iff : atTop.Tendsto (fun (z : ℤ) ↦ ((x:Sequence) z - (fun n : ℕ ↦ x₀ : Sequence) z)) (nhds 0) ↔
    atTop.Tendsto (fun (n : ℕ) ↦ x n - x₀) (nhds 0) := by
    constructor
    · intro h
      have := h.comp (tendsto_natCast_atTop_atTop : atTop.Tendsto (fun n : ℕ ↦ (n : ℤ)) atTop)
      simpa using this
    · intro h
      rw [← Nat.map_cast_int_atTop, tendsto_map'_iff]
      simpa using h
  rw [hz_iff, ← tendsto_sub_nhds_zero_iff (u := x) (x := x₀) (l := atTop)]

/-- Example 9.9.10 -/
noncomputable abbrev f_9_9_10 : ℝ → ℝ := fun x ↦ 1/x

example : (fun n:ℕ ↦ 1/(n+1:ℝ):Sequence).equiv (fun n:ℕ ↦ 1/(2*(n+1):ℝ):Sequence) := by
  rw [Sequence.equiv_iff]
  -- Reduce from ℤ to ℕ
  have hz_iff : atTop.Tendsto (fun (z : ℤ) ↦ ((fun n:ℕ ↦ 1/(n+1:ℝ):Sequence) z - (fun n:ℕ ↦ 1/(2*(n+1):ℝ):Sequence) z)) (nhds 0) ↔
    atTop.Tendsto (fun (n : ℕ) ↦ 1/((n : ℝ) + 1) - 1/(2*((n : ℝ) + 1))) (nhds 0) := by
    constructor
    · intro h
      have := h.comp (tendsto_natCast_atTop_atTop : atTop.Tendsto (fun n : ℕ ↦ (n : ℤ)) atTop)
      simpa using this
    · intro h
      rw [← Nat.map_cast_int_atTop, tendsto_map'_iff]
      simpa using h
  rw [hz_iff]
  -- 1/(n+1) - 1/(2*(n+1)) = 1/(2*(n+1))
  have h_diff : (fun (n : ℕ) ↦ 1/((n : ℝ) + 1) - 1/(2*((n : ℝ) + 1))) = (fun (n : ℕ) ↦ 1/(2*((n : ℝ) + 1))) := by
    ext n; field_simp; ring
  rw [h_diff]
  -- 2*((n:ℝ)+1) → ∞, so 1/(2*((n:ℝ)+1)) → 0
  have h_tendsto : atTop.Tendsto (fun (n : ℕ) ↦ (2 : ℝ)*((n : ℝ) + 1)) atTop := by
    have h_n_plus_one : atTop.Tendsto (fun (n : ℕ) ↦ (n : ℝ) + 1) atTop :=
      tendsto_atTop_add_const_right atTop (1 : ℝ) (tendsto_natCast_atTop_atTop (R := ℝ))
    exact h_n_plus_one.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
  have h_inv' : atTop.Tendsto ((fun (n : ℕ) ↦ (2 : ℝ)*((n : ℝ) + 1))⁻¹) (nhds (0 : ℝ)) :=
    h_tendsto.inv_tendsto_atTop
  have : ((fun (n : ℕ) ↦ (2 : ℝ)*((n : ℝ) + 1))⁻¹) = (fun (n : ℕ) ↦ 1/((2 : ℝ)*((n : ℝ) + 1))) := by
    ext n; simp
  rw [this] at h_inv'
  exact h_inv'

example (n:ℕ) : 1/(n+1:ℝ) ∈ Set.Ioo 0 2 := by
  refine Set.mem_Ioo.mpr ⟨by positivity, ?_⟩
  have h : (1:ℝ)/((n:ℝ)+1) ≤ 1 := by
    refine (div_le_one ?_).mpr ?_
    · positivity
    · have : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
      nlinarith
  nlinarith

example (n:ℕ) : 1/(2*(n+1):ℝ) ∈ Set.Ioo 0 2 := by
  refine Set.mem_Ioo.mpr ⟨by positivity, ?_⟩
  have h : (1:ℝ)/(2*(n+1 : ℝ)) ≤ 1 := by
    refine (div_le_one ?_).mpr ?_
    · positivity
    · have : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
      nlinarith
  nlinarith

example : ¬ (fun n:ℕ ↦ f_9_9_10 (1/(n+1:ℝ)):Sequence).equiv (fun n:ℕ ↦ f_9_9_10 (1/(2*(n+1):ℝ)):Sequence) := by
  rw [Sequence.equiv_iff]
  have hz_iff : atTop.Tendsto (fun (z : ℤ) ↦ ((fun n:ℕ ↦ f_9_9_10 (1/(n+1:ℝ)):Sequence) z - (fun n:ℕ ↦ f_9_9_10 (1/(2*(n+1):ℝ)):Sequence) z)) (nhds 0) ↔
    atTop.Tendsto (fun (n : ℕ) ↦ f_9_9_10 (1/((n : ℝ) + 1)) - f_9_9_10 (1/(2*((n : ℝ) + 1)))) (nhds 0) := by
    constructor
    · intro h
      have := h.comp (tendsto_natCast_atTop_atTop : atTop.Tendsto (fun n : ℕ ↦ (n : ℤ)) atTop)
      simpa using this
    · intro h
      rw [← Nat.map_cast_int_atTop, tendsto_map'_iff]
      simpa using h
  rw [hz_iff]
  have diff : (fun (n : ℕ) ↦ f_9_9_10 (1/((n : ℝ) + 1)) - f_9_9_10 (1/(2*((n : ℝ) + 1)))) = (fun n : ℕ ↦ -(n : ℝ) - 1) := by
    ext n
    dsimp [f_9_9_10]
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
      nlinarith
    field_simp [hpos.ne.symm]
    ring
  rw [diff]
  intro h
  have h' := Metric.tendsto_atTop.mp h 1 (by norm_num)
  rcases h' with ⟨N, hN⟩
  have hN' := hN N (le_refl N)
  rw [Real.dist_eq] at hN'
  have h_simp : (-(N : ℝ) - 1) - 0 = -(N : ℝ) - 1 := by ring
  rw [h_simp] at hN'
  have h_nonpos : -(N : ℝ) - 1 ≤ 0 := by
    have : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (Nat.zero_le N)
    nlinarith
  have abs_val : |-(N : ℝ) - 1| = (N : ℝ) + 1 := by
    rw [abs_of_nonpos h_nonpos]
    ring
  rw [abs_val] at hN'
  have h_nonneg : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (Nat.zero_le N)
  nlinarith

example : ¬ UniformContinuousOn f_9_9_10 (.Ioo 0 2) := by
  exact not_uniform_continuous_one_div_Ioo

/-- Example 9.9.11 -/
abbrev f_9_9_11 : ℝ → ℝ := fun x ↦ x^2

example : ((fun n:ℕ ↦ (n+1:ℝ)):Sequence).equiv ((fun n:ℕ ↦ (n+1)+1/(n+1:ℝ)):Sequence) := by
  rw [Sequence.equiv_iff]
  have hz_iff : atTop.Tendsto (fun (z : ℤ) ↦ ((fun n:ℕ ↦ (n+1:ℝ):Sequence) z - (fun n:ℕ ↦ (n+1)+1/(n+1:ℝ):Sequence) z)) (nhds 0) ↔
    atTop.Tendsto (fun (n : ℕ) ↦ (n+1 : ℝ) - ((n : ℝ) + 1 + 1/((n:ℝ)+1))) (nhds 0) := by
    constructor
    · intro h
      convert h.comp (tendsto_natCast_atTop_atTop : atTop.Tendsto (fun n : ℕ ↦ (n : ℤ)) atTop) using 1
    · intro h
      rw [← Nat.map_cast_int_atTop, tendsto_map'_iff]
      convert h using 1
  rw [hz_iff]
  have diff : (fun n : ℕ ↦ (n+1 : ℝ) - ((n : ℝ) + 1 + 1/((n:ℝ)+1))) = (fun n : ℕ ↦ -(1/((n:ℝ)+1))) := by
    ext n
    have hpos : ((n : ℝ) + 1) ≠ 0 := by
      have : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
      nlinarith
    field_simp [hpos]
    ring
  rw [diff]
  have h : atTop.Tendsto (fun (n : ℕ) => 1/((n : ℝ) + 1)) (nhds (0 : ℝ)) := by
    have h_seq : atTop.Tendsto (fun (n : ℕ) => (n : ℝ) + 1) atTop :=
      tendsto_atTop_add_const_right atTop (1 : ℝ) (tendsto_natCast_atTop_atTop (R := ℝ))
    have h_inv : atTop.Tendsto ((fun (n : ℕ) => (n : ℝ) + 1)⁻¹) (nhds (0 : ℝ)) :=
      h_seq.inv_tendsto_atTop
    simpa using h_inv
  simpa using h.neg

example : ¬ ((fun n:ℕ ↦ f_9_9_11 (n+1:ℝ)):Sequence).equiv ((fun n:ℕ ↦ f_9_9_11 ((n+1)+1/(n+1:ℝ))):Sequence) := by
  rw [Sequence.equiv_iff]
  have hz_iff : atTop.Tendsto (fun (z : ℤ) ↦ ((fun n:ℕ ↦ f_9_9_11 (n+1:ℝ):Sequence) z - (fun n:ℕ ↦ f_9_9_11 ((n+1)+1/(n+1:ℝ)):Sequence) z)) (nhds 0) ↔
    atTop.Tendsto (fun (n : ℕ) ↦ f_9_9_11 ((n : ℝ) + 1) - f_9_9_11 (((n : ℝ) + 1) + 1/((n : ℝ) + 1))) (nhds 0) := by
    constructor
    · intro h
      convert h.comp (tendsto_natCast_atTop_atTop : atTop.Tendsto (fun n : ℕ ↦ (n : ℤ)) atTop) using 1
    · intro h
      rw [← Nat.map_cast_int_atTop, tendsto_map'_iff]
      convert h using 1
  rw [hz_iff]
  have diff : (fun (n : ℕ) ↦ f_9_9_11 ((n : ℝ) + 1) - f_9_9_11 (((n : ℝ) + 1) + 1/((n : ℝ) + 1))) = (fun n : ℕ ↦ -(2 : ℝ) - 1/((n : ℝ) + 1)^2) := by
    ext n
    dsimp [f_9_9_11]
    have hpos : ((n : ℝ) + 1) ≠ 0 := by
      have : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
      nlinarith
    field_simp [hpos]
    ring
  rw [diff]
  intro h
  have h' := Metric.tendsto_atTop.mp h 1 (by norm_num)
  rcases h' with ⟨N, hN⟩
  have hN' := hN N (le_refl N)
  rw [Real.dist_eq] at hN'
  have h_nonpos : (-(2 : ℝ) - 1/((N : ℝ)+1)^2) ≤ 0 := by
    have : 0 < 1/((N : ℝ)+1)^2 := by positivity
    nlinarith
  have abs_val : |(-(2 : ℝ) - 1/((N : ℝ)+1)^2) - 0| = 2 + 1/((N : ℝ)+1)^2 := by
    rw [sub_zero, abs_of_nonpos h_nonpos]
    ring
  rw [abs_val] at hN'
  have : 2 + 1/((N : ℝ)+1)^2 > 1 := by
    have : 1/((N : ℝ)+1)^2 > 0 := by positivity
    nlinarith
  nlinarith

example : ¬ UniformContinuousOn f_9_9_11 .univ := by
  rw [UniformContinuousOn.iff]
  push_neg
  refine ⟨1, by norm_num, ?_⟩
  intro δ hδ
  have hδpos : δ > 0 := hδ
  set x₀ := 1 / δ with hx₀
  set x := 1/δ + δ/2 with hx
  have hx₀_mem : x₀ ∈ Set.univ := Set.mem_univ _
  have hx_mem : x ∈ Set.univ := Set.mem_univ _
  refine ⟨x₀, hx₀_mem, x, hx_mem, ?_, ?_⟩
  · -- |x - x₀| ≤ δ
    dsimp [x, x₀, Real.Close, Real.dist_eq]
    have : |δ/2| = δ/2 := abs_of_pos (by positivity)
    calc
      |(1/δ + δ/2) - 1/δ| = |δ/2| := by
        have h : (1/δ + δ/2) - 1/δ = δ/2 := by
          field_simp [hδpos.ne.symm]
          ring
        rw [h]
      _ = δ/2 := this
      _ ≤ δ := by nlinarith
  · -- ¬ 1.Close (x^2) (x₀^2)
    dsimp [Real.Close, Real.dist_eq, f_9_9_11]
    have hcalc : (1/δ + δ/2)^2 - (1/δ)^2 = 1 + δ^2/4 := by
      field_simp [hδpos.ne.symm]
      ring
    rw [hcalc]
    have h_abs : |1 + δ^2/4| = 1 + δ^2/4 := abs_of_pos (by positivity)
    rw [h_abs]
    have : δ^2/4 > 0 := by positivity
    nlinarith

/-- Proposition 9.9.12 / Exercise 9.9.3  -/
theorem UniformContinuousOn.ofCauchy  {X:Set ℝ} (f: ℝ → ℝ)
  (hf: UniformContinuousOn f X) {x: ℕ → ℝ} (hx: (x:Sequence).IsCauchy) (hmem : ∀ n, x n ∈ X) :
  (f ∘ x:Sequence).IsCauchy := by
  rw [Sequence.IsCauchy.coe] at hx
  rw [Sequence.IsCauchy.coe]
  intro ε hε
  rcases (UniformContinuousOn.iff f X).mp hf ε hε with ⟨δ, hδ, hunif⟩
  rcases hx δ hδ with ⟨N, hN⟩
  use N
  intro j hj k hk
  rw [Real.dist_eq]
  have hx_dist : |x j - x k| ≤ δ := hN j hj k hk
  have hfx_dist := hunif (x k) (hmem k) (x j) (hmem j) hx_dist
  simpa using hfx_dist

/-- Example 9.9.13 -/
example : ((fun n:ℕ ↦ 1/(n+1:ℝ)):Sequence).IsCauchy := by
  rw [Sequence.IsCauchy.coe]
  intro ε hε
  rcases exists_nat_gt (2/ε) with ⟨N, hN⟩
  use N
  intro j hj k hk
  rw [Real.dist_eq]
  have hj' : (N : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hk' : (N : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hpj : 0 < (j : ℝ) + 1 := by
    have : 0 ≤ (j : ℝ) := by exact_mod_cast (Nat.zero_le j)
    nlinarith
  have hpk : 0 < (k : ℝ) + 1 := by
    have : 0 ≤ (k : ℝ) := by exact_mod_cast (Nat.zero_le k)
    nlinarith
  have hpN : 0 < (N : ℝ) + 1 := by
    have : 0 ≤ (N : ℝ) := by exact_mod_cast (Nat.zero_le N)
    nlinarith
  have hNbd : 1/((N : ℝ) + 1) < ε/2 := by
    have hNgt : (N : ℝ) > 2/ε := hN
    have hpos2ε : 0 < 2/ε := div_pos (by norm_num) hε
    have hden_pos : 0 < (N : ℝ) + 1 := by nlinarith
    have hNbig : (N : ℝ) + 1 > 2/ε := by nlinarith
    have hdiv : 1/((N : ℝ) + 1) < 1/((2/ε : ℝ)) :=
      (one_div_lt_one_div (by nlinarith) (by nlinarith)).mpr hNbig
    calc
      1/((N : ℝ) + 1) < 1/((2/ε : ℝ)) := hdiv
      _ = ε/2 := by field_simp
  calc
    |1/((j : ℝ)+1) - 1/((k : ℝ)+1)| ≤ |1/((j : ℝ)+1)| + |1/((k : ℝ)+1)| := abs_sub _ _
    _ = 1/((j : ℝ)+1) + 1/((k : ℝ)+1) := by simp [abs_of_pos hpj, abs_of_pos hpk]
    _ ≤ 1/((N : ℝ)+1) + 1/((N : ℝ)+1) := by
      refine add_le_add ?_ ?_
      · exact (one_div_le_one_div (by nlinarith) (by nlinarith)).mpr (by nlinarith)
      · exact (one_div_le_one_div (by nlinarith) (by nlinarith)).mpr (by nlinarith)
    _ = 2*(1/((N : ℝ)+1)) := by ring
    _ ≤ 2*(ε/2) := by nlinarith
    _ = ε := by ring

example (n:ℕ) : 1/(n+1:ℝ) ∈ Set.Ioo 0 2 := by
  refine Set.mem_Ioo.mpr ⟨by positivity, ?_⟩
  have h : (1:ℝ)/((n:ℝ)+1) ≤ 1 := by
    refine (div_le_one ?_).mpr ?_
    · positivity
    · have : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
      nlinarith
  nlinarith

example : ¬ ((fun n:ℕ ↦ f_9_9_10 (1/(n+1:ℝ))):Sequence).IsCauchy := by
  rw [Sequence.IsCauchy.coe]
  push_neg
  refine ⟨1/2, by norm_num, ?_⟩
  intro N
  refine ⟨N, le_refl N, N+1, by omega, ?_⟩
  rw [Real.dist_eq]
  have hcast : ((N+1 : ℕ) : ℝ) + 1 = (N : ℝ) + 1 + 1 := by simp
  have hval : |f_9_9_10 (1/((N : ℝ) + 1)) - f_9_9_10 (1/((N : ℝ) + 1 + 1))| = 1 := by
    dsimp [f_9_9_10]
    have hpos1 : (N : ℝ) + 1 ≠ 0 := by
      have : 0 ≤ (N : ℝ) := by exact_mod_cast (Nat.zero_le N)
      nlinarith
    have hpos2 : (N : ℝ) + 2 ≠ 0 := by
      have : 0 ≤ (N : ℝ) := by exact_mod_cast (Nat.zero_le N)
      nlinarith
    have hsum : (1 / (1 / ((N : ℝ) + 1))) - (1 / (1 / ((N : ℝ) + 1 + 1))) = (-1 : ℝ) := by
      field_simp [hpos1, hpos2]
      ring
    calc
      |(1 / (1 / ((N : ℝ) + 1))) - (1 / (1 / ((N : ℝ) + 1 + 1)))|
          = |(-1 : ℝ)| := by rw [hsum]
      _ = (1 : ℝ) := by norm_num
  have hgoal : 1/2 < |f_9_9_10 (1/((N : ℝ) + 1)) - f_9_9_10 (1/((N : ℝ) + 1 + 1))| := by
    rw [hval]
    norm_num
  simpa [hcast] using hgoal

example : ¬ UniformContinuousOn f_9_9_10 (Set.Ioo 0 2) := by
  exact not_uniform_continuous_one_div_Ioo

/-- Corollary 9.9.14 / Exercise 9.9.4 -/
theorem UniformContinuousOn.limit_at_adherent  {X:Set ℝ} (f: ℝ → ℝ)
  (hf: UniformContinuousOn f X) {x₀:ℝ} (hx₀: AdherentPt x₀ X) :
  ∃ L:ℝ, (nhdsWithin x₀ X).Tendsto f (nhds L) := by
  rcases (limit_of_AdherentPt X x₀).mp hx₀ with ⟨a, ha, ha_tendsto⟩
  have ha_cauchy_seq : CauchySeq a := ha_tendsto.cauchySeq
  have ha_cauchy : (a : Sequence).IsCauchy := by
    rw [Sequence.IsCauchy.coe]
    intro ε hε
    rcases Metric.cauchySeq_iff.1 ha_cauchy_seq ε hε with ⟨N, hN⟩
    use N
    intro j hj k hk
    exact (hN j hj k hk).le
  have h_f_cauchy : (f ∘ a : Sequence).IsCauchy :=
    UniformContinuousOn.ofCauchy f hf ha_cauchy ha
  have h_f_cauchy_seq : CauchySeq (f ∘ a) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hε2 : 0 < ε / 2 := by nlinarith
    rw [Sequence.IsCauchy.coe] at h_f_cauchy
    rcases h_f_cauchy (ε / 2) hε2 with ⟨N, hN⟩
    use N
    intro m hm n hn
    have h' : dist ((f ∘ a) m) ((f ∘ a) n) ≤ ε / 2 := hN m hm n hn
    nlinarith
  rcases cauchySeq_tendsto_of_complete h_f_cauchy_seq with ⟨L, hL⟩
  refine ⟨L, Metric.tendsto_nhdsWithin_nhds.mpr ?_⟩
  intro ε hε
  have hε3 : 0 < ε / 3 := by nlinarith
  rcases (UniformContinuousOn.iff f X).mp hf (ε / 3) hε3 with ⟨δ, hδ, hunif⟩
  have hδ2 : 0 < δ / 2 := by nlinarith
  rcases Metric.tendsto_atTop.mp ha_tendsto (δ / 2) hδ2 with ⟨N₂, hN₂⟩
  rcases Metric.tendsto_atTop.mp hL (ε / 3) hε3 with ⟨N₁, hN₁⟩
  set n := max N₁ N₂ with hn_def
  have hn_N₁ : n ≥ N₁ := le_max_left _ _
  have hn_N₂ : n ≥ N₂ := le_max_right _ _
  have ha_x₀_bound : |a n - x₀| < δ / 2 := by
    have : dist (a n) x₀ < δ / 2 := hN₂ n hn_N₂
    rw [Real.dist_eq] at this; exact this
  have ha_x₀_bound' : |x₀ - a n| < δ / 2 := by
    rw [abs_sub_comm]; exact ha_x₀_bound
  have hL_bound' : |f (a n) - L| < ε / 3 := by
    have : dist ((f ∘ a) n) L < ε / 3 := hN₁ n hn_N₁
    rw [Real.dist_eq] at this; simpa using this
  refine ⟨δ / 2, hδ2, ?_⟩
  intro y hyX hy_dist
  rw [Real.dist_eq]
  have hy_bound : |y - x₀| < δ / 2 := hy_dist
  have h_an_y_dist : |y - a n| < δ := by
    have h := calc
      |y - a n| = |(y - x₀) + (x₀ - a n)| := by ring_nf
      _ ≤ |y - x₀| + |x₀ - a n| := abs_add_le _ _
    have h' : |y - x₀| + |x₀ - a n| < δ := by
      nlinarith
    exact lt_of_le_of_lt h h'
  have h_unif_bound : |f y - f (a n)| ≤ ε / 3 :=
    hunif (a n) (ha n) y hyX (by
      rw [Real.Close, Real.dist_eq]
      exact h_an_y_dist.le)
  calc
    |f y - L| = |(f y - f (a n)) + (f (a n) - L)| := by ring_nf
    _ ≤ |f y - f (a n)| + |f (a n) - L| := abs_add_le _ _
    _ < ε / 3 + ε / 3 := by nlinarith
    _ < ε := by nlinarith

/-- Proposition 9.9.15 / Exercise 9.9.5 -/
theorem UniformContinuousOn.of_bounded {E X:Set ℝ} {f: ℝ → ℝ}
  (hf: UniformContinuousOn f X) (hEX: E ⊆ X) (hE: Bornology.IsBounded E) :
  Bornology.IsBounded (f '' E) := by
  by_cases hE_empty : E = ∅
  · subst hE_empty; simp
  · rcases Set.nonempty_iff_ne_empty.mpr hE_empty with ⟨x₀, hx₀⟩
    rcases Metric.isBounded_iff.mp hE with ⟨R, hR⟩
    have h_bound : ∀ x ∈ E, |x| ≤ |x₀| + R := by
      intro x hx
      have hdist : dist x x₀ ≤ R := hR hx hx₀
      rw [Real.dist_eq] at hdist
      calc
        |x| = |(x - x₀) + x₀| := by ring_nf
        _ ≤ |x - x₀| + |x₀| := abs_add_le _ _
        _ ≤ R + |x₀| := by nlinarith
        _ = |x₀| + R := by ring
    by_contra! h_not_bdd
    -- h_not_bdd : ¬ Bornology.IsBounded (f '' E)
    have h_seq : ∀ n : ℕ, ∃ x ∈ E, |f x| > (n : ℝ) := by
      by_contra! h
      rcases h with ⟨n, hn⟩
      apply h_not_bdd
      rw [isBounded_iff_forall_norm_le]
      refine ⟨(n : ℝ), ?_⟩
      rintro y ⟨x, hx, rfl⟩
      exact hn x hx
    choose x_seq hx_seq hx_val using h_seq
    have hx_seq_X : ∀ n, x_seq n ∈ X := λ n => hEX (hx_seq n)
    rcases tendsto_subseq_of_bounded hE hx_seq with ⟨L, hL_closure, φ, hφ_mono, h_tendsto⟩
    have h_cauchy_seq : CauchySeq (x_seq ∘ φ) := h_tendsto.cauchySeq
    have h_cauchy : ((x_seq ∘ φ : ℕ → ℝ) : Sequence).IsCauchy := by
      rw [Sequence.IsCauchy.coe]
      intro ε hε
      rcases Metric.cauchySeq_iff.mp h_cauchy_seq ε hε with ⟨N, hN⟩
      use N
      intro j hj k hk
      exact (hN j hj k hk).le
    have h_f_cauchy : ((f ∘ (x_seq ∘ φ) : ℕ → ℝ) : Sequence).IsCauchy :=
      UniformContinuousOn.ofCauchy f hf h_cauchy (by intro n; exact hx_seq_X (φ n))
    rw [Sequence.IsCauchy.coe] at h_f_cauchy
    rcases h_f_cauchy 1 (by norm_num) with ⟨N, hN⟩
    have h_f_bound : ∀ j, j ≥ N → |f (x_seq (φ j))| ≤ |f (x_seq (φ N))| + 1 := by
      intro j hj
      have h_dist := hN N (le_refl N) j hj
      rw [Real.dist_eq] at h_dist
      have h_sub_bound : |f (x_seq (φ j)) - f (x_seq (φ N))| ≤ 1 := by
        rw [abs_sub_comm]; exact h_dist
      have h_ineq : |f (x_seq (φ j))| - |f (x_seq (φ N))| ≤ |f (x_seq (φ j)) - f (x_seq (φ N))| :=
        abs_sub_abs_le_abs_sub _ _
      linarith
    rcases exists_nat_gt (|f (x_seq (φ N))| + 1) with ⟨K, hK⟩
    set n := max N K with hn_def
    have hn_ge_N : n ≥ N := le_max_left _ _
    have hn_ge_K : n ≥ K := le_max_right _ _
    have hφn_ge_n : φ n ≥ n := hφ_mono.id_le n
    have hφn_ge_K : φ n ≥ K := le_trans hn_ge_K hφn_ge_n
    have h_val_seqs : |f (x_seq (φ n))| > (φ n : ℝ) := hx_val (φ n)
    have h_val_φn : (φ n : ℝ) > |f (x_seq (φ N))| + 1 := by
      calc
        (φ n : ℝ) ≥ (K : ℝ) := by exact_mod_cast hφn_ge_K
        _ > |f (x_seq (φ N))| + 1 := hK
    have h_bound_n : |f (x_seq (φ n))| ≤ |f (x_seq (φ N))| + 1 := h_f_bound n hn_ge_N
    nlinarith

/-- Theorem 9.9.16 -/
theorem UniformContinuousOn.of_continuousOn {a b:ℝ} {f:ℝ → ℝ}
  (hcont: ContinuousOn f (.Icc a b)) :
  UniformContinuousOn f (.Icc a b) := by
  -- This proof is written to follow the structure of the original text.
  by_contra h; rw [iff_preserves_equiv] at h
  have h' : ∃ x : ℕ → ℝ, (∀ n, x n ∈ Set.Icc a b) ∧
    ¬ (∀ y : ℕ → ℝ, (∀ n, y n ∈ Set.Icc a b) → (x : Sequence).equiv (y : Sequence) →
      (f ∘ x : Sequence).equiv (f ∘ y : Sequence)) := by
    simpa [not_forall] using h
  rcases h' with ⟨x, hx, h'⟩
  have h'' : ∃ y : ℕ → ℝ, (∀ n, y n ∈ Set.Icc a b) ∧ (x : Sequence).equiv (y : Sequence) ∧
    ¬ ((f ∘ x : Sequence).equiv (f ∘ y : Sequence)) := by
    simpa [not_forall, Classical.not_imp] using h'
  rcases h'' with ⟨y, hy, hequiv, h_not_equiv⟩
  have h_not_eq : ¬ (∀ ε > (0 : ℝ), ε.EventuallyCloseSeqs (f ∘ x : Sequence) (f ∘ y : Sequence)) := by
    simpa [Sequence.equiv] using h_not_equiv
  have h_ex : ∃ ε > (0 : ℝ), ¬ ε.EventuallyCloseSeqs (f ∘ x : Sequence) (f ∘ y : Sequence) := by
    simpa [not_forall] using h_not_eq
  rcases h_ex with ⟨ε, hε, h⟩
  set E : Set ℕ := {n | ¬ ε.Close (f (x n)) (f (y n)) }
  have hE : Infinite E := by
    rw [←not_finite_iff_infinite]
    by_contra! this
    replace : ε.EventuallyCloseSeqs (fun n ↦ f (x n):Sequence) (fun n ↦ f (y n):Sequence) := by
      have hmax : ∃ N : ℕ, ∀ n : ℕ, n ≥ N → ε.Close (f (x n)) (f (y n)) := by
        by_cases h_nonempty : E.Nonempty
        · have hF : Set.Finite E := this
          have hFinset_nonempty : hF.toFinset.Nonempty := by
            rcases h_nonempty with ⟨n, hn⟩
            exact ⟨n, hF.mem_toFinset.mpr hn⟩
          set N := hF.toFinset.max' hFinset_nonempty with hN_def
          use N + 1
          intro n hn
          by_contra! h_not_close
          rw [Real.dist_eq] at h_not_close
          have hn_E : n ∈ E := by
            dsimp [E, Real.Close, Real.dist_eq]
            linarith
          have hn_finset : n ∈ hF.toFinset := hF.mem_toFinset.mpr hn_E
          have hn_le_N : n ≤ N :=
            Finset.le_max' hF.toFinset n hn_finset
          omega
        · use 0
          intro n hn
          by_contra! h_not_close
          rw [Real.dist_eq] at h_not_close
          exact h_nonempty ⟨n, by
            dsimp [E, Real.Close, Real.dist_eq]
            linarith⟩
      rcases hmax with ⟨N, hN⟩
      have hN_ℤ : ∀ (n : ℤ), n ≥ (N : ℤ) → ε.Close (((f ∘ x : Sequence).from (N : ℤ)) n)
        (((f ∘ y : Sequence).from (N : ℤ)) n) := by
        intro n hn
        rw [Sequence.from_eval (f ∘ x : Sequence) hn,
          Sequence.from_eval (f ∘ y : Sequence) hn]
        by_cases hn_nonneg : (0 : ℤ) ≤ n
        · set n' : ℕ := Int.toNat n with hn'_def
          have hn'_eq : (n' : ℤ) = n := Int.toNat_of_nonneg hn_nonneg
          have hn'_ge_N : n' ≥ N := by
            have : (n' : ℤ) ≥ (N : ℤ) := by
              rw [hn'_eq]; exact hn
            exact_mod_cast this
          have h_eval_fx : (f ∘ x : Sequence) n = f (x n') := by
            simp [hn_nonneg, hn'_def]
          have h_eval_fy : (f ∘ y : Sequence) n = f (y n') := by
            simp [hn_nonneg, hn'_def]
          rw [h_eval_fx, h_eval_fy]
          exact hN n' hn'_ge_N
        · have hx_zero : (f ∘ x : Sequence) n = 0 :=
            (f ∘ x : Sequence).vanish n (by
              simp; omega)
          have hy_zero : (f ∘ y : Sequence) n = 0 :=
            (f ∘ y : Sequence).vanish n (by
              simp; omega)
          simp [hn_nonneg]
          exact hε.le
      refine ⟨(N : ℤ), by simp, ?_⟩
      constructor
      · simp
      · exact hN_ℤ
    exact h this
  observe : Countable E
  set n : ℕ → ℕ := Nat.nth E
  rw [Set.infinite_coe_iff] at hE
  have hmono : StrictMono n := by apply_rules [Nat.nth_strictMono]
  have hmem (j:ℕ) : n j ∈ E := j.nth_mem_of_infinite hE
  have hsep (j:ℕ) : |f (x (n j)) - f (y (n j))| > ε := by
    specialize hmem j
    simpa [E, Real.Close, Real.dist_eq] using hmem
  observe hxmem : ∀ j, x (n j) ∈ Set.Icc a b
  observe hymem : ∀ j, y (n j) ∈ Set.Icc a b
  observe hclosed : IsClosed (.Icc a b)
  observe hbounded : Bornology.IsBounded (.Icc a b)
  have ⟨ j, hj, ⟨ L, hL, hconv⟩ ⟩ := (Heine_Borel (.Icc a b)).mp ⟨ hclosed, hbounded ⟩ _ hxmem
  replace hcont := ContinuousOn.continuousWithinAt hcont hL
  have hconv' := hconv.comp_of_continuous hcont (fun k ↦ hxmem (j k))
  rw [Sequence.equiv_iff] at hequiv
  replace hequiv : atTop.Tendsto (fun k ↦ x (n (j k)) - y (n (j k))) (nhds 0) := by
    observe hj' : atTop.Tendsto j .atTop
    observe hn' : atTop.Tendsto n .atTop
    observe hcoe : atTop.Tendsto (fun n:ℕ ↦ (n:ℤ)) .atTop
    exact hequiv.comp (hcoe.comp (hn'.comp hj'))
  have hyconv : atTop.Tendsto (fun k ↦ y (n (j k))) (nhds L) := by
    convert hconv.sub hequiv with k
    . abel
    simp
  replace hyconv := hyconv.comp_of_continuous hcont (fun k ↦ hymem (j k))
  have : atTop.Tendsto (fun k ↦ f (x (n (j k))) - f (y (n (j k)))) (nhds 0) := by
    convert hconv'.sub hyconv; simp
  have h_contra := Metric.tendsto_atTop.mp this ε hε
  rcases h_contra with ⟨K, hK⟩
  have hK' := hK K (le_refl K)
  rw [Real.dist_eq] at hK'
  have h_abs : |f (x (n (j K))) - f (y (n (j K)))| < ε := by
    simpa [sub_zero] using hK'
  have hsep_K := hsep (j K)
  linarith


/-- Exercise 9.9.6 -/
theorem UniformContinuousOn.comp {X Y: Set ℝ} {f g:ℝ → ℝ}
  (hf: UniformContinuousOn f X) (hg: UniformContinuousOn g Y)
  (hrange: f '' X ⊆ Y) : UniformContinuousOn (g ∘ f) X := by
  rw [UniformContinuousOn.iff]
  intro ε hε
  rcases (UniformContinuousOn.iff g Y).mp hg ε hε with ⟨δ₁, hδ₁, hunif_g⟩
  rcases (UniformContinuousOn.iff f X).mp hf δ₁ hδ₁ with ⟨δ, hδ, hunif_f⟩
  refine ⟨δ, hδ, ?_⟩
  intro x₀ hx₀ x hx hx_dist
  have h_fx₀ : f x₀ ∈ Y := hrange (Set.mem_image_of_mem f hx₀)
  have h_fx : f x ∈ Y := hrange (Set.mem_image_of_mem f hx)
  have h_f_dist : δ₁.Close (f x) (f x₀) := hunif_f x₀ hx₀ x hx hx_dist
  have h_g_dist : ε.Close (g (f x)) (g (f x₀)) := hunif_g (f x₀) h_fx₀ (f x) h_fx h_f_dist
  simpa

end Chapter9
