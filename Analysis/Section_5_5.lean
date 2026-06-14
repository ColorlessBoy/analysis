import Mathlib.Tactic
import Analysis.Section_5_4

set_option maxHeartbeats 800000


/-!
# Analysis I, Section 5.5: The least upper bound property

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Upper bound and least upper bound on the real line

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter5

/-- Definition 5.5.1 (upper bounds). Here we use the {name}`upperBounds` set defined in Mathlib. -/
theorem Real.upperBound_def (E: Set Real) (M: Real) : M ∈ upperBounds E ↔ ∀ x ∈ E, x ≤ M :=
  mem_upperBounds

theorem Real.lowerBound_def (E: Set Real) (M: Real) : M ∈ lowerBounds E ↔ ∀ x ∈ E, x ≥ M :=
  mem_lowerBounds

/-- API for Example 5.5.2 -/
theorem Real.Icc_def (x y:Real) : .Icc x y = { z | x ≤ z ∧ z ≤ y } := rfl

/-- API for Example 5.5.2 -/
theorem Real.mem_Icc (x y z:Real) : z ∈ Set.Icc x y ↔ x ≤ z ∧ z ≤ y := by simp [Real.Icc_def]

/-- Example 5.5.2 -/
example (M: Real) : M ∈ upperBounds (.Icc 0 1) ↔ M ≥ 1 := by
  rw [Real.upperBound_def]
  constructor
  · intro h; apply h 1; simp
  · intro h x hx
    have hx' := by simpa [Real.Icc_def] using hx
    rcases hx' with ⟨hx0, hx1⟩
    linarith

/-- API for Example 5.5.3 -/
theorem Real.Ioi_def (x:Real) : .Ioi x = { z | z > x } := rfl

/-- Example 5.5.3 -/
example : ¬ ∃ M : Real, M ∈ upperBounds (.Ioi 0) := by
  rintro ⟨M, hM⟩
  rw [Real.upperBound_def] at hM
  by_cases h : M ≤ 0
  · have hM1 := hM 1 (by
      simpa [Real.Ioi_def] using (by norm_num : (1 : ℝ) > (0 : ℝ)))
    linarith
  · have hpos : M > 0 := by linarith
    have hM' := hM (M + 1) (by
      simpa [Real.Ioi_def] using (by linarith : M + 1 > 0))
    linarith

/-- Example 5.5.4 -/
example : ∀ M, M ∈ upperBounds (∅ : Set Real) := by
  intro M; simp [Real.upperBound_def]

theorem Real.upperBound_upper {M M': Real} (h: M ≤ M') {E: Set Real} (hb: M ∈ upperBounds E) :
    M' ∈ upperBounds E := by
  rw [Real.upperBound_def] at hb ⊢
  intro x hx
  linarith [hb x hx]

/-- Definition 5.5.5 (least upper bound).  Here we use the {name}`IsLUB` predicate defined in Mathlib. -/
theorem Real.isLUB_def (E: Set Real) (M: Real) :
    IsLUB E M ↔ M ∈ upperBounds E ∧ ∀ M' ∈ upperBounds E, M' ≥ M := by rfl

theorem Real.isGLB_def (E: Set Real) (M: Real) :
    IsGLB E M ↔ M ∈ lowerBounds E ∧ ∀ M' ∈ lowerBounds E, M' ≤ M := by rfl

/-- Example 5.5.6 -/
example : IsLUB (.Icc 0 1) (1 : Real) := by
  rw [Real.isLUB_def, Real.upperBound_def]
  constructor
  · intro x hx
    have hx' := by simpa [Real.Icc_def] using hx
    exact hx'.2
  · intro M' hM'
    rw [Real.upperBound_def] at hM'
    exact hM' 1 (by simp)

/-- Example 5.5.7 -/
example : ¬∃ M, IsLUB (∅: Set Real) M := by
  rintro ⟨M, hM⟩
  rw [Real.isLUB_def] at hM
  rcases hM with ⟨hM_ub, hM_min⟩
  have all_ub : ∀ M', M' ∈ upperBounds (∅ : Set Real) := by
    intro M'; simp [Real.upperBound_def]
  have hM1 := hM_min (M - 1) (all_ub (M - 1))
  linarith

/-- Proposition 5.5.8 (Uniqueness of least upper bound)-/
theorem Real.LUB_unique {E: Set Real} {M M': Real} (h1: IsLUB E M) (h2: IsLUB E M') : M = M' := by
  grind [Real.isLUB_def]

/-- Definition of "bounded above", using Mathlib notation -/
theorem Real.bddAbove_def (E: Set Real) : BddAbove E ↔ ∃ M, M ∈ upperBounds E := Set.nonempty_def

theorem Real.bddBelow_def (E: Set Real) : BddBelow E ↔ ∃ M, M ∈ lowerBounds E := Set.nonempty_def

/-- Exercise 5.5.2 -/
theorem Real.upperBound_between {E: Set Real} {n:ℕ} {L K:ℤ} (hLK: L < K)
  (hK: K*((1/(n+1):ℚ):Real) ∈ upperBounds E) (hL: L*((1/(n+1):ℚ):Real) ∉ upperBounds E) :
    ∃ m, L < m
    ∧ m ≤ K
    ∧ m*((1/(n+1):ℚ):Real) ∈ upperBounds E
    ∧ (m-1)*((1/(n+1):ℚ):Real) ∉ upperBounds E := by
  set ε := ((1/(n+1):ℚ):Real)
  have h_range_finite : ((Finset.Icc (L+1 : ℤ) K : Set ℤ)).Finite := Finset.finite_toSet _
  set S := ((Finset.Icc (L+1 : ℤ) K : Set ℤ) ∩ {k : ℤ | k*ε ∈ upperBounds E}) with hS
  have hS_nonempty : S.Nonempty := by
    refine ⟨K, ⟨Finset.mem_Icc.mpr ⟨by omega, le_refl _⟩, hK⟩⟩
  have hS_finite : S.Finite :=
    Set.Finite.subset h_range_finite (by
      intro x hx
      exact hx.1)
  rcases hS_finite.exists_minimal hS_nonempty with ⟨m, hm_mem, hm_min⟩
  rcases hm_mem with ⟨hm_Icc, hm_upper⟩
  rcases Finset.mem_Icc.mp hm_Icc with ⟨hm_L, hm_K⟩
  have hm_gt_L : L < m := by omega
  have hm_not_upper : (m-1)*ε ∉ upperBounds E := by
    intro h
    by_cases hm1_ge_Lp1 : L+1 ≤ m-1
    · have hm1_Icc : m-1 ∈ Finset.Icc (L+1 : ℤ) K :=
        Finset.mem_Icc.mpr ⟨hm1_ge_Lp1, by omega⟩
      have h' : (↑(m-1 : ℤ) : Real) * ε ∈ upperBounds E := by
        simpa using h
      have hm1_S : m-1 ∈ S := ⟨hm1_Icc, h'⟩
      have hm1_lt_m : m-1 < m := by omega
      have hm1_notin_S : m-1 ∉ S := sorry
      exact hm1_notin_S hm1_S
    · have hm1_eq_L : m-1 = L := by omega
      have hL' : (L:ℤ)*ε ∉ upperBounds E := hL
      have h_after_subst : (L : ℤ)*ε ∈ upperBounds E := by
        subst hm1_eq_L; simpa using h
      exact hL' h_after_subst
  refine ⟨m, hm_gt_L, hm_K, hm_upper, hm_not_upper⟩

/-- Exercise 5.5.3 -/
theorem Real.upperBound_discrete_unique {E: Set Real} {n:ℕ} {m m':ℤ}
  (hm1: (((m:ℚ) / (n+1):ℚ):Real) ∈ upperBounds E)
  (hm2: (((m:ℚ) / (n+1) - 1 / (n+1):ℚ):Real) ∉ upperBounds E)
  (hm'1: (((m':ℚ) / (n+1):ℚ):Real) ∈ upperBounds E)
  (hm'2: (((m':ℚ) / (n+1) - 1 / (n+1):ℚ):Real) ∉ upperBounds E) :
    m = m' := by
  by_contra! hne
  have h_or : m < m' ∨ m' < m := lt_or_gt_of_ne hne
  rcases h_or with (h | h)
  · have hz : (m : ℤ) ≤ (m' : ℤ) - 1 := by omega
    have hm_bound : (m : ℚ) ≤ (m' : ℚ) - 1 := mod_cast hz
    have hnpos' : (n : ℚ) + 1 ≠ 0 := by positivity
    have hineq : ((m : ℚ) / ((n : ℚ) + 1) : ℚ) ≤ (((m' : ℚ) - 1) / ((n : ℚ) + 1) : ℚ) := by
      field_simp [hnpos']
      nlinarith
    have hm1_ub : ∀ x ∈ E, x ≤ (((m : ℚ) / (n+1) : ℚ) : Real) := by
      simpa using (mem_upperBounds (a := (((m : ℚ) / (n+1) : ℚ) : Real))).mp hm1
    have hINEQ : ∀ x ∈ E, x ≤ ((((m' : ℚ) - 1) / (n+1) : ℚ) : Real) := by
      intro x hx
      have hx1 : x ≤ (((m : ℚ) / (n+1) : ℚ) : Real) := hm1_ub x hx
      set q := (m : ℚ) / ((n : ℚ) + 1) with hq
      set q' := ((m' : ℚ) - 1) / ((n : ℚ) + 1) with hq'
      have hineq_r : (((m : ℚ) / (n+1) : ℚ) : Real) ≤ ((((m' : ℚ) - 1) / (n+1) : ℚ) : Real) := by
        have hineq_real : (q : Real) < (q' : Real) ∨ (q : Real) = (q' : Real) := by
          rcases hineq.lt_or_eq with (hlt | heq)
          · left; exact (Real.lt_of_coe q q').mp hlt
          · right; exact congrArg (fun x : ℚ => (x : Real)) heq
        have dn_eq : (q : Real) = (((m : ℚ) / (n+1) : ℚ) : Real) := by
          calc
            (q : Real) = (((m : ℚ) / ((n : ℚ) + 1) : ℚ) : Real) := rfl
            _ = (((m : ℚ) / (n+1 : ℚ) : ℚ) : Real) := by norm_num
        have dn_eq' : (q' : Real) = ((((m' : ℚ) - 1) / (n+1) : ℚ) : Real) := by
          calc
            (q' : Real) = ((((m' : ℚ) - 1) / ((n : ℚ) + 1) : ℚ) : Real) := rfl
            _ = ((((m' : ℚ) - 1) / (n+1 : ℚ) : ℚ) : Real) := by norm_num
        rcases hineq_real with (hreal | heq_real)
        · have hle : (q : Real) ≤ (q' : Real) := le_of_lt hreal
          rw [dn_eq, dn_eq'] at hle
          exact hle
        · rw [dn_eq, dn_eq'] at heq_real
          exact heq_real.le
      exact le_trans hx1 hineq_r
    apply hm'2
    -- Show that the goal equals hINEQ
    -- Goal: (((m' : ℚ) / (n+1) - 1 / (n+1) : ℚ) : Real) ∈ upperBounds E
    -- hINEQ: ∀ x ∈ E, x ≤ (((m' : ℚ) - 1) / (n+1) : ℚ) : Real)
    -- These are equal because m'/(n+1) - 1/(n+1) = (m' - 1)/(n+1) in ℚ
    have hcast_q : (m' : ℚ) / (n+1 : ℚ) - 1 / (n+1 : ℚ) = ((m' : ℚ) - 1) / (n+1 : ℚ) := by
      field_simp [hnpos']
    have hcast_r : (((m' : ℚ) / (n+1) - 1 / (n+1) : ℚ) : Real) = ((((m' : ℚ) - 1) / (n+1) : ℚ) : Real) := by
      simpa using congrArg (fun x : ℚ => (x : Real)) hcast_q
    rw [hcast_r]
    exact (mem_upperBounds (a := ((((m' : ℚ) - 1) / (n+1) : ℚ) : Real))).mpr hINEQ
  · have hz : (m' : ℤ) ≤ (m : ℤ) - 1 := by omega
    have hm_bound : (m' : ℚ) ≤ (m : ℚ) - 1 := mod_cast hz
    have hnpos' : (n : ℚ) + 1 ≠ 0 := by positivity
    have hineq : ((m' : ℚ) / ((n : ℚ) + 1) : ℚ) ≤ (((m : ℚ) - 1) / ((n : ℚ) + 1) : ℚ) := by
      field_simp [hnpos']
      nlinarith
    have hm'1_ub : ∀ x ∈ E, x ≤ (((m' : ℚ) / (n+1) : ℚ) : Real) := by
      simpa using (mem_upperBounds (a := (((m' : ℚ) / (n+1) : ℚ) : Real))).mp hm'1
    have hINEQ : ∀ x ∈ E, x ≤ ((((m : ℚ) - 1) / (n+1) : ℚ) : Real) := by
      intro x hx
      have hx1 : x ≤ (((m' : ℚ) / (n+1) : ℚ) : Real) := hm'1_ub x hx
      set q := (m' : ℚ) / ((n : ℚ) + 1) with hq
      set q' := ((m : ℚ) - 1) / ((n : ℚ) + 1) with hq'
      have hineq_r : (((m' : ℚ) / (n+1) : ℚ) : Real) ≤ ((((m : ℚ) - 1) / (n+1) : ℚ) : Real) := by
        have hineq_real : (q : Real) < (q' : Real) ∨ (q : Real) = (q' : Real) := by
          rcases hineq.lt_or_eq with (hlt | heq)
          · left; exact (Real.lt_of_coe q q').mp hlt
          · right; exact congrArg (fun x : ℚ => (x : Real)) heq
        have dn_eq : (q : Real) = (((m' : ℚ) / (n+1) : ℚ) : Real) := by
          calc
            (q : Real) = (((m' : ℚ) / ((n : ℚ) + 1) : ℚ) : Real) := rfl
            _ = (((m' : ℚ) / (n+1 : ℚ) : ℚ) : Real) := by norm_num
        have dn_eq' : (q' : Real) = ((((m : ℚ) - 1) / (n+1) : ℚ) : Real) := by
          calc
            (q' : Real) = ((((m : ℚ) - 1) / ((n : ℚ) + 1) : ℚ) : Real) := rfl
            _ = ((((m : ℚ) - 1) / (n+1 : ℚ) : ℚ) : Real) := by norm_num
        rcases hineq_real with (hreal | heq_real)
        · have hle : (q : Real) ≤ (q' : Real) := le_of_lt hreal
          rw [dn_eq, dn_eq'] at hle
          exact hle
        · rw [dn_eq, dn_eq'] at heq_real
          exact heq_real.le
      exact le_trans hx1 hineq_r
    apply hm2
    -- Goal: (((m : ℚ) / (n+1) - 1 / (n+1) : ℚ) : Real) ∈ upperBounds E
    have hcast_q : (m : ℚ) / (n+1 : ℚ) - 1 / (n+1 : ℚ) = ((m : ℚ) - 1) / (n+1 : ℚ) := by
      field_simp [hnpos']
    have hcast_r : (((m : ℚ) / (n+1) - 1 / (n+1) : ℚ) : Real) = ((((m : ℚ) - 1) / (n+1) : ℚ) : Real) := by
      simpa using congrArg (fun x : ℚ => (x : Real)) hcast_q
    rw [hcast_r]
    exact (mem_upperBounds (a := ((((m : ℚ) - 1) / (n+1) : ℚ) : Real))).mpr hINEQ

/-- Lemmas that can be helpful for proving 5.5.4 -/
theorem Sequence.IsCauchy.abs {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy):
  ((|a| : ℕ → ℚ) : Sequence).IsCauchy := by
  rw [Sequence.IsCauchy.coe] at ha ⊢
  intro ε hε
  rcases ha ε hε with ⟨N, hN⟩
  use N
  intro j hj k hk
  have h := hN j hj k hk
  rw [Section_4_3.dist, Section_4_3.abs_eq_abs, Pi.abs_apply]
  calc
    |(|a j| - |a k|)|
        ≤ |a j - a k| := by
          rw [abs_le]
          constructor
          · have h' : |a k| - |a j| ≤ |a k - a j| := abs_sub_abs_le_abs_sub (a k) (a j)
            rw [abs_sub_comm] at h'
            linarith
          · exact abs_sub_abs_le_abs_sub (a j) (a k)
    _ = Section_4_3.abs (a j - a k) := by rw [Section_4_3.abs_eq_abs]
    _ = Section_4_3.dist (a j) (a k) := rfl
    _ ≤ ε := h

theorem Real.LIM.abs_eq {a b:ℕ → ℚ} (ha: (a: Sequence).IsCauchy)
    (hb: (b: Sequence).IsCauchy) (h: LIM a = LIM b): LIM |a| = LIM |b| := by
  have ha_abs : ((|a| : ℕ → ℚ) : Sequence).IsCauchy := Sequence.IsCauchy.abs ha
  have hb_abs : ((|b| : ℕ → ℚ) : Sequence).IsCauchy := Sequence.IsCauchy.abs hb
  apply (Real.LIM_eq_LIM ha_abs hb_abs).mpr
  rw [Sequence.equiv_iff]
  intro ε hε
  have hequiv' : ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - b n| ≤ ε :=
    (Sequence.equiv_iff a b).mp ((Real.LIM_eq_LIM ha hb).mp h)
  rcases hequiv' ε hε with ⟨N, hN⟩
  refine ⟨N, λ n hn => ?_⟩
  have hN' : |a n - b n| ≤ ε := hN n hn
  calc
    |((|a| : ℕ → ℚ) n - (|b| : ℕ → ℚ) n)| = |(|a n| - |b n|)| := by simp
    _ ≤ |a n - b n| := by
      rw [abs_le]
      constructor
      · have h' : |b n| - |a n| ≤ |b n - a n| := abs_sub_abs_le_abs_sub (b n) (a n)
        rw [abs_sub_comm] at h'
        linarith
      · exact abs_sub_abs_le_abs_sub (a n) (b n)
    _ ≤ ε := hN'

theorem Real.LIM.abs_eq_pos {a: ℕ → ℚ} (h: LIM a > 0) (ha: (a:Sequence).IsCauchy):
    LIM a = LIM |a| := by
  have h_ispos : (LIM a).IsPos := by
    simpa [Real.gt_iff, sub_zero] using h
  rcases h_ispos with ⟨c, hc_pos, hc_cauchy, hc_eq⟩
  rcases hc_pos with ⟨c0, hc0_pos, hc0_bound⟩
  have h_equiv_ac' : ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - c n| ≤ ε :=
    (Sequence.equiv_iff a c).mp ((Real.LIM_eq_LIM ha hc_cauchy).mp (by rw [hc_eq]))
  have h_eventually_pos : ∃ N, ∀ n ≥ N, a n > 0 := by
    rcases h_equiv_ac' (c0/2) (by nlinarith) with ⟨N, hN⟩
    use N
    intro n hn
    have h_close : |a n - c n| ≤ c0 / 2 := hN n hn
    have h_cn_pos : c n ≥ c0 := hc0_bound n
    have h_lower : a n ≥ c n - c0/2 := by
      rcases abs_le.mp h_close with ⟨hle, hge⟩
      linarith
    nlinarith
  rcases h_eventually_pos with ⟨N, hN⟩
  have ha_abs_cauchy : ((|a| : ℕ → ℚ) : Sequence).IsCauchy := Sequence.IsCauchy.abs ha
  have h_equiv : Sequence.Equiv a (|a| : ℕ → ℚ) := by
    rw [Sequence.equiv_iff]
    intro ε hε
    refine ⟨N, λ n hn => ?_⟩
    have hpos : a n > 0 := hN n hn
    have h_eq : |a n| = a n := by
      calc
        |a n| = Section_4_3.abs (a n) := (Section_4_3.abs_eq_abs (a n)).symm
        _ = a n := Section_4_3.abs_of_pos (by linarith : 0 < a n)
    simp [h_eq, hε.le]
  exact (Real.LIM_eq_LIM ha ha_abs_cauchy).mpr h_equiv

theorem Real.LIM_abs {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy): |LIM a| = LIM |a| := by
  rw [Real.abs_eq_abs (LIM a)]
  have h := Real.trichotomous' (LIM a) 0
  rcases h with (hgt | hlt | heq)
  · -- LIM a > 0
    have hpos : (LIM a).IsPos := (Real.isPos_iff _).mpr hgt
    rw [Real.abs_of_pos (LIM a) hpos, Real.LIM.abs_eq_pos hgt ha]
  · -- LIM a < 0
    have hneg : (LIM a).IsNeg := (Real.isNeg_iff _).mpr hlt
    have hneg_gt : LIM (-a) > 0 := by
      have hnegpos : (-(LIM a)).IsPos := (Real.neg_iff_pos_of_neg (LIM a)).mp hneg
      rw [Real.neg_LIM a ha] at hnegpos
      exact (Real.isPos_iff _).mp hnegpos
    have h_neg_abs : LIM |a| = -(LIM a) := by
      calc
        LIM |a| = LIM |-a| := by simp
        _ = LIM (-a) := (Real.LIM.abs_eq_pos hneg_gt (Sequence.IsCauchy.neg a ha)).symm
        _ = -(LIM a) := (Real.neg_LIM a ha).symm
    rw [Real.abs_of_neg (LIM a) hneg, h_neg_abs]
  · -- LIM a = 0
    rw [heq, Real.abs_of_zero]
    have ha_abs : ((|a| : ℕ → ℚ) : Sequence).IsCauchy := Sequence.IsCauchy.abs ha
    have hzero : LIM (|a| : ℕ → ℚ) = 0 :=
      calc
        LIM (|a| : ℕ → ℚ) = LIM (fun _ : ℕ => (0 : ℚ)) :=
          (Real.LIM_eq_LIM ha_abs (Sequence.IsCauchy.const (0 : ℚ))).mpr (by
            rw [Sequence.equiv_iff]
            intro ε hε
            have hzero_equiv : ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - 0| ≤ ε :=
              (Sequence.equiv_iff a (fun _ : ℕ => (0 : ℚ))).mp
                ((Real.LIM_eq_LIM ha (Sequence.IsCauchy.const (0 : ℚ))).mp (by
                  calc
                    LIM a = 0 := heq
                    _ = LIM (fun _ : ℕ => (0 : ℚ)) := (Real.ratCast_def (0 : ℚ))))
            rcases hzero_equiv ε hε with ⟨N, hN⟩
            refine ⟨N, λ n hn => ?_⟩
            have hN' : |a n - 0| ≤ ε := hN n hn
            simpa using hN')
        _ = 0 := (Real.ratCast_def (0 : ℚ)).symm
    rw [hzero]

theorem Real.LIM_of_le' {x:Real} {a:ℕ → ℚ} (hcauchy: (a:Sequence).IsCauchy)
    (h: ∃ N, ∀ n ≥ N, a n ≤ x) : LIM a ≤ x := by
  rcases h with ⟨N, hN⟩
  set a' := fun n : ℕ => a (n + N) with ha'
  have ha'_cauchy : ((a' : ℕ → ℚ) : Sequence).IsCauchy := by
    rw [Sequence.IsCauchy.coe]
    intro ε hε
    have ha_cauchy_coe : ∀ ε > (0 : ℚ), ∃ N, ∀ j ≥ N, ∀ k ≥ N,
      Section_4_3.dist (a j) (a k) ≤ ε :=
      (Sequence.IsCauchy.coe a).mp hcauchy
    rcases ha_cauchy_coe ε hε with ⟨M, hM⟩
    use M
    intro j hj k hk
    apply hM (j + N) (by omega) (k + N) (by omega)
  have hLIM_eq : LIM a' = LIM a := by
    apply (Real.LIM_eq_LIM ha'_cauchy hcauchy).mpr
    rw [Sequence.equiv_iff]
    intro ε hε
    have ha_cauchy_coe : ∀ ε > (0 : ℚ), ∃ N, ∀ j ≥ N, ∀ k ≥ N,
      Section_4_3.dist (a j) (a k) ≤ ε :=
      (Sequence.IsCauchy.coe a).mp hcauchy
    rcases ha_cauchy_coe ε hε with ⟨M, hM⟩
    use M
    intro n hn
    have hM' : Section_4_3.dist (a (n + N)) (a n) ≤ ε :=
      hM (n + N) (by omega) n hn
    rw [Section_4_3.dist, Section_4_3.abs_eq_abs] at hM'
    simpa [a'] using hM'
  have h_all : ∀ n, (a' n : Real) ≤ x := by
    intro n
    have hN' : a (n + N) ≤ x := hN (n + N) (by omega)
    simpa [a'] using hN'
  have h_neg_all : ∀ n, -(a' n : Real) ≥ -x := by
    intro n
    have hn : (a' n : Real) ≤ x := h_all n
    linarith
  have h_LIM_neg_ge : LIM (-a') ≥ -x := by
    have h_cau : ((-a' : ℕ → ℚ) : Sequence).IsCauchy :=
      Sequence.IsCauchy.neg a' ha'_cauchy
    have h_all' : ∀ n, ((-a' : ℕ → ℚ) n : Real) ≥ -x := by
      intro n
      have h : -(a' n : Real) ≥ -x := h_neg_all n
      rw [ha'] at h ⊢
      dsimp at h ⊢
      simpa [Real.neg_ratCast] using h
    exact Real.LIM_of_ge h_cau h_all'
  rw [← Real.neg_LIM a' ha'_cauchy] at h_LIM_neg_ge
  have h_LIM_a'_le_x : LIM a' ≤ x := by linarith
  rw [← hLIM_eq]
  exact h_LIM_a'_le_x

lemma cauchy_of_rate {q : ℕ → ℚ} (hq : ∀ M, ∀ n ≥ M, ∀ n' ≥ M, |q n - q n'| ≤ 1 / (M+1)) :
    (q : Sequence).IsCauchy := by
  rw [Sequence.IsCauchy.coe]
  intro ε hε
  rcases exists_nat_gt ((1 : ℚ) / ε) with ⟨N, hN⟩
  use N
  intro j hj k hk
  have h_rate : |q j - q k| ≤ 1 / ((N : ℚ) + 1) := by
    simpa using hq N j hj k hk
  have h_one_div_N1_le_ε : (1 : ℚ) / ((N : ℚ) + 1) ≤ ε := by
    have hNpos : (N : ℚ) + 1 > 0 := by positivity
    have h_one_div_ε_pos : (1 : ℚ) / ε > 0 := div_pos (by norm_num) hε
    have h_ineq : (N : ℚ) + 1 > (1 : ℚ) / ε := by linarith
    have h_temp : (1 : ℚ) / ((N : ℚ) + 1) < ε := by
      calc
        (1 : ℚ) / ((N : ℚ) + 1) < (1 : ℚ) / ((1 : ℚ) / ε) :=
          (one_div_lt_one_div hNpos h_one_div_ε_pos).mpr h_ineq
        _ = ε := by field_simp [hε.ne.symm]
    linarith
  rw [Section_4_3.dist, Section_4_3.abs_eq_abs]
  exact le_trans h_rate h_one_div_N1_le_ε

/-- Exercise 5.5.4 -/
theorem Real.LIM_of_Cauchy {q:ℕ → ℚ} (hq: ∀ M, ∀ n ≥ M, ∀ n' ≥ M, |q n - q n'| ≤ 1 / (M+1)) :
    (q:Sequence).IsCauchy ∧ ∀ M, |q M - LIM q| ≤ 1 / (M+1) := by
  sorry

lemma Real.LUB_claim2 {E : Set Real} (N:ℕ) {a b: ℕ → ℚ}
  (hb : ∀ n, b n = 1 / (↑n + 1))
  (hm1 : ∀ (n : ℕ), ↑(a n) ∈ upperBounds E)
  (hm2 : ∀ (n : ℕ), ↑((a - b) n) ∉ upperBounds E)
: ∀ n ≥ N, ∀ n' ≥ N, |a n - a n'| ≤ 1 / (N+1) := by
    intro n hn n' hn'
    rw [abs_le]
    split_ands
    . specialize hm1 n; specialize hm2 n'
      have bound1 : ((a-b) n') < a n := by rw [lt_of_coe]; contrapose! hm2; grind [upperBound_upper]
      have bound3 : 1/((n':ℚ)+1) ≤ 1/(N+1) := by gcongr
      rw [←neg_le_neg_iff] at bound3; rw [Pi.sub_apply] at bound1; grind
    specialize hm1 n'; specialize hm2 n
    have bound1 : ((a-b) n) < a n' := by rw [lt_of_coe]; contrapose! hm2; grind [upperBound_upper]
    have bound2 : ((a-b) n) = a n - 1 / (n+1) := by simp [hb n]
    have bound3 : 1/((n+1):ℚ) ≤ 1/(N+1) := by gcongr
    linarith

/-- Theorem 5.5.9 (Existence of least upper bound)-/
theorem Real.LUB_exist {E: Set Real} (hE: Set.Nonempty E) (hbound: BddAbove E): ∃ S, IsLUB E S := by
  sorry

/-- A bare-bones extended real class to define supremum. -/
inductive ExtendedReal where
| neg_infty : ExtendedReal
| real (x:Real) : ExtendedReal
| infty : ExtendedReal

/-- Mathlib prefers {syntax term}`⊤` to denote the +∞ element. -/
instance ExtendedReal.inst_Top : Top ExtendedReal where
  top := infty

/-- Mathlib prefers {syntax term}`⊥` to denote the -∞ element. -/
instance ExtendedReal.inst_Bot: Bot ExtendedReal where
  bot := neg_infty

instance ExtendedReal.coe_real : Coe Real ExtendedReal where
  coe x := ExtendedReal.real x

instance ExtendedReal.real_coe : Coe ExtendedReal Real where
  coe X := match X with
  | neg_infty => 0
  | real x => x
  | infty => 0

abbrev ExtendedReal.IsFinite (X : ExtendedReal) : Prop := match X with
  | neg_infty => False
  | real _ => True
  | infty => False

theorem ExtendedReal.finite_eq_coe {X: ExtendedReal} (hX: X.IsFinite) :
    X = ((X:Real):ExtendedReal) := by
  cases X <;> try simp [IsFinite] at hX
  simp

open Classical in
/-- Definition 5.5.10 (Supremum)-/
noncomputable abbrev ExtendedReal.sup (E: Set Real) : ExtendedReal :=
  if h1:E.Nonempty then (if h2:BddAbove E then ((Real.LUB_exist h1 h2).choose:Real) else ⊤) else ⊥

/-- Definition 5.5.10 (Supremum)-/
theorem ExtendedReal.sup_of_empty : sup ∅ = ⊥ := by simp [sup]

/-- Definition 5.5.10 (Supremum)-/
theorem ExtendedReal.sup_of_unbounded {E: Set Real} (hb: ¬ BddAbove E) : sup E = ⊤ := by
  have hE : E.Nonempty := by contrapose! hb; simp [hb]
  simp [sup, hE, hb]

/-- Definition 5.5.10 (Supremum)-/
theorem ExtendedReal.sup_of_bounded {E: Set Real} (hnon: E.Nonempty) (hb: BddAbove E) :
    IsLUB E (sup E) := by
  simp [hnon, hb, sup]; exact (Real.LUB_exist hnon hb).choose_spec

theorem ExtendedReal.sup_of_bounded_finite {E: Set Real} (hnon: E.Nonempty) (hb: BddAbove E) :
    (sup E).IsFinite := by simp [sup, hnon, hb, IsFinite]

/-- Proposition 5.5.12 -/
theorem Real.exist_sqrt_two : ∃ x:Real, x^2 = 2 := by
  sorry

/-- Remark 5.5.13 -/
theorem Real.exist_irrational : ∃ x:Real, ¬ ∃ q:ℚ, x = (q:Real) := by sorry

/-- Helper lemma for Exercise 5.5.1. -/
theorem Real.mem_neg (E: Set Real) (x:Real) : x ∈ -E ↔ -x ∈ E := Set.mem_neg

/-- Exercise 5.5.1-/
theorem Real.inf_neg {E: Set Real} {M:Real} (h: IsLUB E M) : IsGLB (-E) (-M) := by sorry

theorem Real.GLB_exist {E: Set Real} (hE: Set.Nonempty E) (hbound: BddBelow E): ∃ S, IsGLB E S := by
  sorry

open Classical in
noncomputable abbrev ExtendedReal.inf (E: Set Real) : ExtendedReal :=
  if h1:E.Nonempty then (if h2:BddBelow E then ((Real.GLB_exist h1 h2).choose:Real) else ⊥) else ⊤

theorem ExtendedReal.inf_of_empty : inf ∅ = ⊤ := by simp [inf]

theorem ExtendedReal.inf_of_unbounded {E: Set Real} (hb: ¬ BddBelow E) : inf E = ⊥ := by
  have hE : E.Nonempty := by contrapose! hb; simp [hb]
  simp [inf, hE, hb]

theorem ExtendedReal.inf_of_bounded {E: Set Real} (hnon: E.Nonempty) (hb: BddBelow E) :
    IsGLB E (inf E) := by simp [hnon, hb, inf]; exact (Real.GLB_exist hnon hb).choose_spec

theorem ExtendedReal.inf_of_bounded_finite {E: Set Real} (hnon: E.Nonempty) (hb: BddBelow E) :
    (inf E).IsFinite := by simp [inf, hnon, hb, IsFinite]

/-- Exercise 5.5.5 -/
theorem Real.irrat_between {x y:Real} (hxy: x < y) :
    ∃ z, x < z ∧ z < y ∧ ¬ ∃ q:ℚ, z = (q:Real) := by sorry

/- Use the notion of supremum in this section to define a Mathlib `sSup` operation -/
noncomputable instance Real.inst_SupSet : SupSet Real where
  sSup E := ((ExtendedReal.sup E):Real)

/-- Use the {name}`sSup` operation to build a conditionally complete lattice structure on {name}`Real`. -/
noncomputable instance Real.inst_conditionallyCompleteLattice :
    ConditionallyCompleteLattice Real :=
  conditionallyCompleteLatticeOfLatticeOfsSup Real
  (by intros; solve_by_elim [ExtendedReal.sup_of_bounded])

theorem ExtendedReal.sSup_of_bounded {E: Set Real} (hnon: E.Nonempty) (hb: BddAbove E) :
    IsLUB E (sSup E) := sup_of_bounded hnon hb

end Chapter5
