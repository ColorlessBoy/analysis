import Mathlib.Tactic
import Analysis.Section_6_4
import Analysis.Section_7_4
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Analysis I, Section 7.5: The root and ratio tests

I have attempted to make the translation as faithful a paraphrasing as possible of the original text.  When there is a choice between a more idiomatic Lean solution and a more faithful translation, I have generally chosen the latter.  In particular, there will be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main constructions and results of this section:

- The root and ratio tests/

A point that is only implicitly stated in the text is that for the root and ratio tests, the lim inf and lim sup should be interpreted within the extended reals.  The Lean formalizations below make this point more explicit.

-/

namespace Chapter7

open Filter Real EReal

lemma eventually_gt_of_liminf_lt {α : Type _} {f : Filter α} {u : α → EReal} {b : EReal}
    (h : b < liminf u f) : ∀ᶠ a in f, b < u a := by
  have hneg : limsup (-u) f < -b := by
    rw [EReal.limsup_neg]
    exact EReal.neg_lt_neg_iff.mpr h
  have hneg_event : ∀ᶠ a in f, (-u) a < -b :=
    eventually_lt_of_limsup_lt hneg
  filter_upwards [hneg_event] with a ha
  exact EReal.neg_lt_neg_iff.mp ha

lemma zpow_add_ℝ {a : ℝ} (ha : a ≠ 0) (m n : ℤ) : a ^ (m + n) = a ^ m * a ^ n := by
  have h := zpow_add (Units.mk0 a ha) m n
  simpa using congrArg (fun (u : ℝˣ) => (u : ℝ)) h

lemma tendsto_const_pow_one_div_n {a : ℝ} (ha : a > 0) : atTop.Tendsto (fun n : ℤ ↦ a ^ (1/(n:ℝ))) (nhds 1) := by
  have h_inv : Tendsto (fun n : ℤ ↦ (1/(n:ℝ))) atTop (nhds (0 : ℝ)) := by
    simpa [one_div] using (tendsto_inv_atTop_zero.comp (tendsto_intCast_atTop_atTop (R := ℝ)))
  have ha' : a ^ (0 : ℝ) = 1 := by simp
  have h_cont : ContinuousAt (fun x : ℝ ↦ a ^ x) (0 : ℝ) :=
    continuousAt_const_rpow ha.ne'
  simpa [ha'] using h_cont.tendsto.comp h_inv

lemma tendsto_sub_div_n (N : ℤ) : atTop.Tendsto (fun n : ℤ ↦ ((n : ℝ) - (N : ℝ)) / (n : ℝ)) (nhds (1 : ℝ)) := by
  have hN_div_n : atTop.Tendsto (fun n : ℤ ↦ (N : ℝ) / (n : ℝ)) (nhds (0 : ℝ)) := by
    simpa [one_div] using (tendsto_inv_atTop_zero.comp (tendsto_intCast_atTop_atTop (R := ℝ))).const_mul (N : ℝ)
  have h_eq : ∀ᶠ (n : ℤ) in atTop, ((n : ℝ) - (N : ℝ)) / (n : ℝ) = 1 - (N : ℝ) / (n : ℝ) := by
    refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
    have hnpos : (n : ℝ) ≠ 0 := by
      intro hzero
      have : (n : ℤ) = 0 := by exact_mod_cast hzero
      have : (n : ℤ) ≥ 1 := hn
      omega
    field_simp [hnpos]
  rw [tendsto_congr' h_eq]
  simpa using (tendsto_const_nhds.sub hN_div_n)

lemma bound_tendsto {cN y : ℝ} (hcN : cN > 0) (hy : y > 0) (N : ℤ) :
    atTop.Tendsto (fun n : ℤ ↦ cN ^ (1/(n:ℝ)) * y ^ (((n : ℝ) - (N : ℝ)) / (n : ℝ))) (nhds y) := by
  have h1 : atTop.Tendsto (fun n : ℤ ↦ cN ^ (1/(n:ℝ))) (nhds (1 : ℝ)) :=
    tendsto_const_pow_one_div_n hcN
  have h2 : atTop.Tendsto (fun n : ℤ ↦ y ^ (((n : ℝ) - (N : ℝ)) / (n : ℝ))) (nhds y) := by
    have h_cont : ContinuousAt (fun x : ℝ ↦ y ^ x) (1 : ℝ) :=
      continuousAt_const_rpow hy.ne'
    simpa [rpow_one] using h_cont.tendsto.comp (tendsto_sub_div_n N)
  simpa [one_mul] using h1.mul h2

/-- Theorem 7.5.1(a) (Root test).  A technical condition is needed to ensure the limsup is finite. -/
theorem Series.root_test_pos {s : Series}
  (h : atTop.limsup (fun n ↦ ((|s.seq n|^(1/(n:ℝ)):ℝ):EReal)) < 1) : s.absConverges := by
    -- This proof is written to follow the structure of the original text.
    set α':EReal := atTop.limsup (fun n ↦ ↑(|s.seq n|^(1/(n:ℝ)):ℝ))
    have hpos : 0 ≤ α' := by
      apply le_limsup_of_frequently_le (Frequently.of_forall _) (by isBoundedDefault)
      intros; positivity
    set α := α'.toReal
    have hαα' : α' = α := by
      symm; apply coe_toReal
      . contrapose! h; simp [h]; exact le_top
      contrapose! hpos; simp [hpos]
    rw [hαα'] at h hpos; norm_cast at h hpos
    set ε := (1-α)/2
    have hε : 0 < ε := by simp [ε]; linarith
    have hε' : α' < (α+ε:ℝ) := by rw [hαα', EReal.coe_lt_coe_iff]; linarith
    have hα : α + ε < 1 := by simp [ε]; linarith
    have hα' : 0 < α + ε := by linarith
    have := eventually_lt_of_limsup_lt hε' (by isBoundedDefault)
    rw [eventually_atTop] at this
    choose N' hN using this; set N := max N' (max s.m 1)
    have (n:ℤ) (hn: n ≥ N) : |s.seq n| ≤ (α + ε)^n := by
      have : n ≥ N' := by omega
      have npos : 0 < n := by omega
      specialize hN n this
      rw [EReal.coe_lt_coe_iff] at hN
      calc
        _ = (|s.seq n|^(1/(n:ℝ)))^n := by
          rw [←rpow_intCast, ←rpow_mul (by positivity)]
          symm; convert rpow_one _; field_simp
        _ ≤ _ := by
          convert pow_le_pow_left₀ (by positivity) (le_of_lt hN) n.toNat
          all_goals convert zpow_natCast _ _; omega
    set k := (N - s.m).toNat
    have hNk : N = s.m + k := by omega
    have hgeom : (fun n ↦ (α+ε) ^ n : Series).converges := by
      simp [converges_geom_iff, abs_of_pos hα', hα]
    rw [converges_from _ N.toNat] at hgeom
    have : (s.from N).absConverges := by
      apply (converges_of_le _ _ hgeom).1
      . simp; omega
      intro n hn; simp at hn
      have hn' : n ≥ 0 := by omega
      simp [hn.1, hn.2, hn']
      convert this n hn.2; symm; convert zpow_natCast _ _; omega
    unfold absConverges at this ⊢
    rw [converges_from _ k]; convert this; simp; refine ⟨ by omega, ?_ ⟩
    ext n
    by_cases hnm : n ≥ s.m <;> simp [hnm]
    by_cases hn: n ≥ N <;> simp [hn] <;> grind


/-- Theorem 7.5.1(b) (Root test) -/
theorem Series.root_test_neg {s : Series}
  (h : atTop.limsup (fun n ↦ ((|s.seq n|^(1/(n:ℝ)):ℝ):EReal)) > 1) : s.diverges := by
    -- This proof is written to follow the structure of the original text.
    apply frequently_lt_of_lt_limsup (by isBoundedDefault) at h
    apply diverges_of_nodecay
    by_contra this; rw [LinearOrderedAddCommGroup.tendsto_nhds] at this; specialize this 1 (by positivity)
    choose n hn hs hs' using (h.and_eventually this).forall_exists_of_atTop 1
    simp at hs'; replace hs' := rpow_lt_one ?_ hs' (?_:0 < 1/(n:ℝ)) <;> try positivity
    rw [show (1:EReal) = (1:ℝ) by simp, EReal.coe_lt_coe_iff] at hs
    linarith

/-- Theorem 7.5.1(c) (Root test) / Exercise 7.5.3 -/
theorem Series.root_test_inconclusive: ∃ s:Series,
  atTop.Tendsto (fun n ↦ |s.seq n|^(1/(n:ℝ))) (nhds 1) ∧ s.diverges := by
  set s := ((fun _ : ℕ ↦ (1 : ℝ)) : Series) with hs
  have hdiv : s.diverges := Series.example_7_2_7
  have hlim : atTop.Tendsto (fun n : ℤ ↦ |s.seq n|^(1/(n : ℝ))) (nhds 1) := by
    have h_event : ∀ᶠ n in atTop, |s.seq n|^(1/(n : ℝ)) = (1 : ℝ) := by
      refine Filter.eventually_atTop.mpr ⟨0, fun n hn => ?_⟩
      simp [hs, hn]
    exact (tendsto_congr' h_event).mpr tendsto_const_nhds
  exact ⟨s, hlim, hdiv⟩

/-- Theorem 7.5.1 (Root test) / Exercise 7.5.3 -/
theorem Series.root_test_inconclusive' : ∃ s:Series,
  atTop.Tendsto (fun n ↦ |s.seq n|^(1/(n:ℝ))) (nhds 1) ∧ s.absConverges := by
  let s : Series := {
    m := 1
    seq := fun n : ℤ ↦ if h : n ≥ 1 then 1 / ((n:ℝ) * ((n:ℝ) + 1)) else 0
    vanish := by
      intro n hn
      have : n < 1 := hn
      simp [this]
  }
  have hpos : ∀ n, s.seq n ≥ 0 := by
    intro n
    dsimp [s]
    split
    · positivity
    · norm_num
  have habseq : s.abs = s := by
    ext n
    dsimp [Series.abs, Series.mk', s]
    by_cases hn : n ≥ 1
    · have h_nonneg : s.seq n ≥ 0 := hpos n
      have h1n : (1 : ℤ) ≤ n := hn
      calc
        s.abs.seq n = |s.seq n| := by
          dsimp [Series.abs, Series.mk', s]
          simp [h1n]
        _ = s.seq n := abs_of_nonneg h_nonneg
    · simp [s.vanish n (show n < 1 from by omega)]
  have h_partial_eq (N : ℤ) (hN : 1 ≤ N) : s.partial N = 1 - 1 / ((N : ℝ) + 1) := by
    refine Int.le_induction ?base ?step N hN
    · unfold s Series.partial
      simp
      ring
    · intro k hk IH
      have hk_ge_m_sub_one : k ≥ s.m - 1 := by
        dsimp [s]
        omega
      rw [Series.partial_succ s hk_ge_m_sub_one, IH]
      have hseq_val : s.seq (k + 1) = 1 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
        have hpos' : (k + 1 : ℤ) ≥ 1 := by omega
        dsimp [s]
        rw [if_pos hpos']
        have hcast : ((k + 1 : ℤ) : ℝ) = (k : ℝ) + 1 := by simp
        rw [hcast]
        have denom_eq : ((k : ℝ) + 1) + 1 = (k : ℝ) + 2 := by ring
        rw [denom_eq]
      rw [hseq_val]
      have hkpos : (k : ℝ) + 1 ≠ 0 := by
        have : (k : ℝ) ≥ 1 := by exact_mod_cast hk
        linarith
      have hkpos2 : (k : ℝ) + 2 ≠ 0 := by
        have : (k : ℝ) ≥ 1 := by exact_mod_cast hk
        linarith
      have temp_eq : (1 - 1 / ((k : ℝ) + 1)) + 1 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) = 1 - 1 / ((k : ℝ) + 2) := by
        have hkpos' : (1 : ℝ) + (k : ℝ) ≠ 0 := by simpa [add_comm] using hkpos
        have hkpos2' : (2 : ℝ) + (k : ℝ) ≠ 0 := by simpa [add_comm] using hkpos2
        field_simp [hkpos, hkpos', hkpos2, hkpos2']; ring
      have main_eq : (1 - 1 / ((k : ℝ) + 1)) + 1 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) = 1 - 1 / (((k + 1 : ℤ) : ℝ) + 1) := by
        calc
          (1 - 1 / ((k : ℝ) + 1)) + 1 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) = 1 - 1 / ((k : ℝ) + 2) := temp_eq
          _ = 1 - 1 / (((k + 1 : ℤ) : ℝ) + 1) := by
            have hcast : ((k + 1 : ℤ) : ℝ) = (k : ℝ) + 1 := by simp
            simp [hcast]
            ring
      exact main_eq
  have hconv : s.converges := by
    have hnonneg : s.nonneg := hpos
    refine ((converges_of_nonneg_iff hnonneg).mpr ?_)
    use 1
    intro N
    by_cases hN : 1 ≤ N
    · rw [h_partial_eq N hN]
      have hpos' : 0 ≤ 1 / ((N : ℝ) + 1) := by positivity
      linarith
    · unfold Series.partial
      have : Finset.Icc (1 : ℤ) N = ∅ := by
        ext n; simp; omega
      simp [s, this]
  have habs_conv : s.absConverges := by
    rw [absConverges, habseq]
    exact hconv
  have hlim : atTop.Tendsto (fun n ↦ |s.seq n|^(1/(n:ℝ))) (nhds 1) := by
    have h_event : ∀ᶠ n in atTop, |s.seq n|^(1/(n:ℝ)) =
      ((1 : ℝ) / ((n:ℝ) * ((n:ℝ) + 1))) ^ (1 / (n:ℝ)) := by
      refine Filter.eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
      have h_val : s.seq n = 1 / ((n : ℝ) * ((n : ℝ) + 1)) := by
        dsimp [s]
        simp [hn]
      have h_nonneg : 0 ≤ 1 / ((n : ℝ) * ((n : ℝ) + 1)) := by positivity
      calc
        |s.seq n| ^ (1 / (n : ℝ)) = |1 / ((n : ℝ) * ((n : ℝ) + 1))| ^ (1 / (n : ℝ)) := by rw [h_val]
        _ = (1 / ((n : ℝ) * ((n : ℝ) + 1))) ^ (1 / (n : ℝ)) := by rw [abs_of_nonneg h_nonneg]
        _ = ((1 : ℝ) / ((n : ℝ) * ((n : ℝ) + 1))) ^ (1 / (n : ℝ)) := rfl
    refine (tendsto_congr' h_event).mpr ?_
    have hn_atTop : Tendsto (fun n : ℤ => (n : ℝ)) atTop atTop :=
      tendsto_intCast_atTop_atTop
    have h_one_div_n : Tendsto (fun n : ℤ => 1 / (n : ℝ)) atTop (nhds 0) := by
      simpa [one_div] using (tendsto_inv_atTop_zero.comp hn_atTop)
    have h_n_pow_neg_one_div_n : Tendsto (fun n : ℤ => (n : ℝ) ^ (-1 / (n : ℝ))) atTop (nhds 1) := by
      have h := tendsto_rpow_neg_div.comp hn_atTop
      simpa using h
    have h_n_plus_one_pow_neg_one_div_n : Tendsto (fun n : ℤ => ((n : ℝ) + 1) ^ (-1 / (n : ℝ))) atTop (nhds 1) := by
      have h_shift : Tendsto (fun n : ℤ => (n : ℝ) + 1) atTop atTop :=
        tendsto_atTop_add_const_right atTop (1 : ℝ) hn_atTop
      have h_a : Tendsto (fun n : ℤ => ((n : ℝ) + 1) ^ (-1 / ((n : ℝ) + 1))) atTop (nhds 1) := by
        simpa using (tendsto_rpow_neg_div.comp h_shift)
      have h_b : Tendsto (fun n : ℤ => ((n : ℝ) + 1) / (n : ℝ)) atTop (nhds (1 : ℝ)) := by
        have h_eq : ∀ᶠ n : ℤ in atTop, ((n : ℝ) + 1) / (n : ℝ) = (1 : ℝ) + 1 / (n : ℝ) := by
          refine Filter.eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
          have hnpos : (n : ℝ) ≠ 0 := by
            have : (n : ℝ) ≥ 1 := by exact_mod_cast hn
            positivity
          field_simp [hnpos]
        refine ((tendsto_congr' h_eq).mpr ?_)
        simpa using (tendsto_const_nhds.add h_one_div_n)
      have h_factor : ∀ᶠ n : ℤ in atTop, ((n : ℝ) + 1) ^ (-1 / (n : ℝ)) =
        (((n : ℝ) + 1) ^ (-1 / ((n : ℝ) + 1))) ^ (((n : ℝ) + 1) / (n : ℝ)) := by
        refine Filter.eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
        have hn_nonneg : 0 ≤ (n : ℝ) + 1 := by positivity
        have h_exp_eq : (-1 / (n : ℝ)) = (-1 / ((n : ℝ) + 1)) * (((n : ℝ) + 1) / (n : ℝ)) := by
          field_simp [show (n : ℝ) ≠ 0 from by positivity]
        calc
          ((n : ℝ) + 1) ^ (-1 / (n : ℝ)) = ((n : ℝ) + 1) ^ ((-1 / ((n : ℝ) + 1)) * (((n : ℝ) + 1) / (n : ℝ))) := by
            rw [h_exp_eq]
          _ = (((n : ℝ) + 1) ^ (-1 / ((n : ℝ) + 1))) ^ (((n : ℝ) + 1) / (n : ℝ)) := by
            rw [Real.rpow_mul hn_nonneg (-1 / ((n : ℝ) + 1)) (((n : ℝ) + 1) / (n : ℝ))]
      have h_comp : Tendsto (fun n : ℤ => (((n : ℝ) + 1) ^ (-1 / ((n : ℝ) + 1))) ^ (((n : ℝ) + 1) / (n : ℝ))) atTop (nhds 1) := by
        simpa [one_rpow] using h_a.rpow h_b (Or.inl (by norm_num : (1 : ℝ) ≠ 0))
      exact ((tendsto_congr' h_factor).mpr h_comp)
    have h_factor_target : ∀ᶠ n : ℤ in atTop, ((1 : ℝ) / ((n : ℝ) * ((n : ℝ) + 1))) ^ (1 / (n : ℝ)) =
      ((n : ℝ) ^ (-1 / (n : ℝ))) * (((n : ℝ) + 1) ^ (-1 / (n : ℝ))) := by
      refine Filter.eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
      have hn_nonneg : 0 ≤ (n : ℝ) := by
        have : (n : ℝ) ≥ 1 := by exact_mod_cast hn
        positivity
      have hn_nonneg_sq : 0 ≤ (n : ℝ) * ((n : ℝ) + 1) := by positivity
      calc
        ((1 : ℝ) / ((n : ℝ) * ((n : ℝ) + 1))) ^ (1 / (n : ℝ))
            = (1 : ℝ) ^ (1 / (n : ℝ)) / (((n : ℝ) * ((n : ℝ) + 1)) ^ (1 / (n : ℝ))) := by
              rw [div_rpow (by norm_num : (0 : ℝ) ≤ 1) hn_nonneg_sq]
        _ = 1 / (((n : ℝ) * ((n : ℝ) + 1)) ^ (1 / (n : ℝ))) := by simp
        _ = (((n : ℝ) * ((n : ℝ) + 1)) ^ (1 / (n : ℝ)))⁻¹ := by
          rw [← inv_eq_one_div]
        _ = ((n : ℝ) * ((n : ℝ) + 1)) ^ (-(1 / (n : ℝ))) := by
          rw [rpow_neg hn_nonneg_sq (1 / (n : ℝ))]
        _ = ((n : ℝ) * ((n : ℝ) + 1)) ^ (-1 / (n : ℝ)) := by ring_nf
        _ = (n : ℝ) ^ (-1 / (n : ℝ)) * ((n : ℝ) + 1) ^ (-1 / (n : ℝ)) := by
          rw [mul_rpow hn_nonneg (by positivity : 0 ≤ (n : ℝ) + 1)]
    have h_prod : Tendsto (fun n : ℤ => ((n : ℝ) ^ (-1 / (n : ℝ))) * (((n : ℝ) + 1) ^ (-1 / (n : ℝ)))) atTop (nhds (1 : ℝ)) := by
      simpa [one_mul] using h_n_pow_neg_one_div_n.mul h_n_plus_one_pow_neg_one_div_n
    exact ((tendsto_congr' h_factor_target).mpr h_prod)
  exact ⟨s, hlim, habs_conv⟩

/-- Lemma 7.5.2 / Exercise 7.5.1 -/
theorem Series.ratio_ineq {c:ℤ → ℝ} (m:ℤ) (hpos: ∀ n ≥ m, c n > 0) :
  atTop.liminf (fun n ↦ ((c (n+1) / c n:ℝ):EReal)) ≤
    atTop.liminf (fun n ↦ ↑((c n)^(1/(n:ℝ)):ℝ))
  ∧ atTop.liminf (fun n ↦ (((c n)^(1/(n:ℝ)):ℝ):EReal)) ≤
    atTop.limsup (fun n ↦ ↑((c n)^(1/(n:ℝ)):ℝ))
  ∧ atTop.limsup (fun n ↦ (((c n)^(1/(n:ℝ)):ℝ):EReal)) ≤
    atTop.limsup (fun n ↦ ↑(c (n+1) / c n:ℝ))
    := by
  -- This proof is written to follow the structure of the original text.
  refine ⟨ ?_, liminf_le_limsup ?_ ?_, ?_ ⟩ <;> try isBoundedDefault
  · -- First subgoal: liminf ratio ≤ liminf root
    set L := atTop.liminf (fun n ↦ ((c (n+1) / c n:ℝ):EReal)) with hL
    apply le_of_forall_lt_imp_le_of_dense
    intro y hy
    by_cases hy_bot : y = ⊥; · rw [hy_bot]; exact bot_le
    have hy_top : y ≠ ⊤ := by
      intro h; rw [h] at hy; exact not_top_lt hy
    have hy_event : ∀ᶠ n in atTop, (y : EReal) < ((c (n+1) / c n : ℝ) : EReal) :=
      eventually_gt_of_liminf_lt hy
    rcases eventually_atTop.mp hy_event with ⟨N, hN⟩
    set y' := y.toReal with hy'_def
    have hy'_eq : (y' : EReal) = y := EReal.coe_toReal hy_top hy_bot
    have h_ratio_gt (n : ℤ) (hn : n ≥ N) : y' < c (n+1) / c n := by
      have h := hN n hn
      rw [← hy'_eq] at h
      simpa using h
    
    by_cases hy'_le_zero : y' ≤ 0
    · have h_root_nonneg : (0 : EReal) ≤ atTop.liminf (fun n ↦ ↑((c n)^(1/(n:ℝ)):ℝ)) := by
        have h_nonneg : ∀ᶠ n : ℤ in atTop, ((0 : ℝ) : EReal) ≤ ↑((c n)^(1/(n:ℝ)):ℝ) := by
          refine eventually_atTop.mpr ⟨m, fun n hn => ?_⟩
          have hpos_cn : 0 < c n := hpos n hn
          have hpos_root : 0 ≤ (c n)^(1/(n:ℝ)) := by positivity
          exact mod_cast hpos_root
        have h_liminf0 : atTop.liminf (fun _ : ℤ ↦ ((0 : ℝ) : EReal)) = (0 : EReal) := by
          simp
        have h_liminf_ineq : atTop.liminf (fun _ : ℤ ↦ ((0 : ℝ) : EReal)) ≤ atTop.liminf (fun n ↦ ↑((c n)^(1/(n:ℝ)):ℝ)) :=
          liminf_le_liminf h_nonneg (by isBoundedDefault) (by isBoundedDefault)
        rw [h_liminf0] at h_liminf_ineq
        exact h_liminf_ineq
      calc
        y ≤ (0 : EReal) := by
          calc
            y = (y' : EReal) := Eq.symm hy'_eq
            _ ≤ (0 : EReal) := mod_cast hy'_le_zero
        _ ≤ atTop.liminf (fun n ↦ ↑((c n)^(1/(n:ℝ)):ℝ)) := h_root_nonneg
    · have hy'_pos : y' > 0 := by linarith
      set N' := max N (max m 1) with hN'_def
      have hN_le_N' : N ≤ N' := by
        unfold N'; omega
      have hm_le_N' : m ≤ N' := by
        unfold N'; omega
      have hN'_h_ratio (n : ℤ) (hn : n ≥ N') : y' < c (n+1) / c n :=
        h_ratio_gt n (by omega)
      have h_c_bound (n : ℤ) (hn : n ≥ N') : c n ≥ c N' * y' ^ (n - N') := by
        refine Int.le_induction ?base ?step n hn
        · simp
        · intro k hk h_induction
          have hmk : m ≤ k := by omega
          have hkpos : 0 < c k := hpos k hmk
          have h_ratio : y' < c (k+1) / c k := hN'_h_ratio k hk
          have h_mul : y' * c k < c (k+1) := by
            calc
              y' * c k < (c (k+1) / c k) * c k := mul_lt_mul_of_pos_right h_ratio hkpos
              _ = c (k+1) := by field_simp [hkpos.ne']
          calc
            c N' * y' ^ ((k+1) - N') = c N' * y' ^ ((k - N') + 1) := by ring_nf
            _ = c N' * (y' ^ (k - N') * y' ^ (1 : ℤ)) := by rw [zpow_add_ℝ (by linarith) (k - N') (1 : ℤ)]
            _ = c N' * (y' ^ (k - N') * y') := by simp
            _ = c N' * y' ^ (k - N') * y' := by ring
            _ ≤ c k * y' := by
              nlinarith
            _ = y' * c k := mul_comm _ _
            _ ≤ c (k+1) := le_of_lt h_mul
      have h_root_bound (n : ℤ) (hn : n ≥ N') : (c n : ℝ) ^ (1/(n:ℝ)) ≥ (c N' : ℝ) ^ (1/(n:ℝ)) * y' ^ (((n : ℝ) - (N' : ℝ)) / (n : ℝ)) := by
        have hcN' : 0 ≤ c N' := by linarith [hpos N' (by unfold N'; omega)]
        have hy' : 0 ≤ y' := by linarith
        have hy'_nonzero : y' ≠ 0 := by linarith
        have hnpos' : (n : ℝ) > 0 := by
          have : n ≥ N' := hn
          have hN'_pos : N' ≥ 1 := by
            unfold N'; omega
          exact_mod_cast show n ≥ 1 from by omega
        have h_exp_nonneg : 0 ≤ 1/(n:ℝ) := by positivity
        have h_base_nonneg : 0 ≤ (c N' : ℝ) * y' ^ ((n : ℤ) - (N' : ℤ)) := by
          apply mul_nonneg
          · exact hcN'
          · apply zpow_nonneg hy'
        calc
          (c n : ℝ) ^ (1/(n:ℝ)) ≥ ((c N' : ℝ) * y' ^ ((n : ℤ) - (N' : ℤ))) ^ (1/(n:ℝ)) :=
            rpow_le_rpow (by positivity) (h_c_bound n hn) h_exp_nonneg
          _ = (c N' : ℝ) ^ (1/(n:ℝ)) * (y' ^ ((n : ℤ) - (N' : ℤ))) ^ (1/(n:ℝ)) :=
            mul_rpow (by positivity) (by
              have hy_nonneg : 0 ≤ y' := by linarith
              have : 0 ≤ y' ^ ((n : ℤ) - (N' : ℤ)) := by
                apply zpow_nonneg hy_nonneg
              exact this)
          _ = (c N' : ℝ) ^ (1/(n:ℝ)) * y' ^ (((n : ℝ) - (N' : ℝ)) / (n : ℝ)) := by
            have h_rpow : (y' ^ ((n : ℤ) - (N' : ℤ))) ^ (1/(n:ℝ)) = y' ^ (((n : ℝ) - (N' : ℝ)) / (n : ℝ)) := by
              have h_base : y' ^ ((n : ℤ) - (N' : ℤ)) = y' ^ (((n : ℤ) - (N' : ℤ) : ℝ)) := by
                rw [← rpow_intCast y' ((n : ℤ) - (N' : ℤ)), Int.cast_sub]
              calc
                (y' ^ ((n : ℤ) - (N' : ℤ))) ^ (1/(n:ℝ)) = (y' ^ (((n : ℤ) - (N' : ℤ) : ℝ))) ^ (1/(n:ℝ)) := by
                  rw [h_base]
                _ = y' ^ ((((n : ℤ) - (N' : ℤ) : ℝ)) * (1/(n:ℝ))) := by
                  rw [rpow_mul hy' _]
                _ = y' ^ (((n : ℝ) - (N' : ℝ)) / (n : ℝ)) := by
                  field_simp
            rw [h_rpow]
      have h_liminf : (y' : EReal) ≤ atTop.liminf (fun n ↦ ↑((c n)^(1/(n:ℝ)):ℝ)) := by
        have hN'_pos : 0 < c N' := hpos N' (by unfold N'; omega)
        have h_tendsto : atTop.Tendsto (fun n : ℤ ↦ (c N' : ℝ) ^ (1/(n:ℝ)) * y' ^ (((n : ℝ) - (N' : ℝ)) / (n : ℝ))) (nhds y') :=
          bound_tendsto hN'_pos hy'_pos N'
        rw [le_liminf_iff (by isBoundedDefault) (by isBoundedDefault)]
        intro z hz
        by_cases hz_bot : z = ⊥; · rw [hz_bot]; exact eventually_atTop.mpr ⟨0, fun n hn => by
          simp⟩
        have hz_real : z ≠ ⊤ := by
          intro h; rw [h] at hz; exact not_top_lt hz
        set z' := z.toReal with hz'_def
        have hz'_eq : (z' : EReal) = z := EReal.coe_toReal hz_real hz_bot
        have hz_lt_y' : (z' : ℝ) < y' := by
          have : (z : EReal) < (y' : EReal) := hz
          rw [← hz'_eq] at this
          simpa using this
        have hz_bound_event : ∀ᶠ (n : ℤ) in atTop, (z' : ℝ) < (c N' : ℝ) ^ (1/(n:ℝ)) * y' ^ (((n : ℝ) - (N' : ℝ)) / (n : ℝ)) :=
          h_tendsto.eventually (lt_mem_nhds hz_lt_y')
        have h_root_event : ∀ᶠ (n : ℤ) in atTop, (c N' : ℝ) ^ (1/(n:ℝ)) * y' ^ (((n : ℝ) - (N' : ℝ)) / (n : ℝ)) ≤ (c n : ℝ) ^ (1/(n:ℝ)) := by
          refine eventually_atTop.mpr ⟨N', fun n hn => h_root_bound n hn⟩
        filter_upwards [hz_bound_event, h_root_event] with n hn h_root
        have hz_lt_root : (z' : ℝ) < (c n : ℝ) ^ (1/(n:ℝ)) := by
          linarith
        have h_cast : (z' : EReal) < ↑((c n : ℝ) ^ (1/(n:ℝ)) : ℝ) := by exact_mod_cast hz_lt_root
        rw [← hz'_eq]
        exact h_cast
      calc
        y = (y' : EReal) := Eq.symm hy'_eq
        _ ≤ atTop.liminf (fun n ↦ ↑((c n)^(1/(n:ℝ)):ℝ)) := h_liminf
  · -- Third subgoal: limsup root ≤ limsup ratio
    set L' := limsup (fun n ↦ ((c (n+1) / c n:ℝ):EReal)) .atTop
    by_cases hL : L' = ⊤; · rw [hL]; exact le_top
    have hL'pos : 0 ≤ L' := by
      apply le_limsup_of_frequently_le'
      rw [frequently_atTop]
      intro N; use max N m, by omega
      have hpos1 := hpos (max N m) (by omega)
      have hpos2 := hpos ((max N m)+1) (by omega)
      positivity
    have hL'_not_bot : L' ≠ ⊥ := by
      intro hbot; rw [hbot] at hL'pos; simp at hL'pos
    set L := L'.toReal
    have hL' : L' = L := (coe_toReal hL hL'_not_bot).symm
    have hLpos : 0 ≤ L := by rw [hL'] at hL'pos; norm_cast at hL'pos
    apply le_of_forall_gt_imp_ge_of_dense
    intro y hy
    by_cases hy' : y = ⊤; · simp [hy']; exact le_top
    have : y = y.toReal := by symm; apply coe_toReal hy'; contrapose! hy; simp [hy]
    rw [this, hL', EReal.coe_lt_coe_iff] at hy
    set ε := y.toReal - L
    have hε : 0 < ε := by grind
    replace this : y = (L+ε:ℝ) := by convert this; simp [ε]
    rw [this]
    have hε' : L' < (L+ε:ℝ) := by rw [hL', EReal.coe_lt_coe_iff]; linarith
    have := eventually_lt_of_limsup_lt hε' (by isBoundedDefault)
    rw [eventually_atTop] at this; choose N' hN using this
    set N := max N' (max m 1)
    have h_ratio_le (n:ℤ) (hn: n ≥ N) : c (n+1) / c n ≤ (L + ε) := by
      have : n ≥ N' := by omega
      have npos : 0 < n := by omega
      specialize hN n this; norm_cast at hN; order
    set A := c N * (L+ε)^(-N)
    have hA : 0 < A := by specialize hpos N (by omega); positivity
    have why2 (n:ℤ) (hn: n ≥ N) : c n ≤ A * (L+ε)^n := by
      have hLε_ne : (L+ε : ℝ) ≠ 0 := by nlinarith
      dsimp [A]
      have base_case : c N ≤ (c N * (L+ε)^(-N : ℤ)) * (L+ε)^(N : ℤ) := by
        have h_eq : c N = (c N * (L+ε)^(-N : ℤ)) * (L+ε)^(N : ℤ) := by
          calc
            c N = c N * 1 := by simp
            _ = c N * ((L+ε : ℝ) ^ (0 : ℤ)) := by simp
            _ = c N * ((L+ε : ℝ) ^ ((-N : ℤ) + (N : ℤ))) := by simp
            _ = c N * ((L+ε : ℝ) ^ (-N : ℤ) * (L+ε : ℝ) ^ (N : ℤ)) := by rw [zpow_add_ℝ hLε_ne]
            _ = (c N * (L+ε : ℝ) ^ (-N : ℤ)) * (L+ε : ℝ) ^ (N : ℤ) := by ring
            _ = (c N * (L+ε)^(-N : ℤ)) * (L+ε)^(N : ℤ) := rfl
        exact h_eq.le
      have hLε_nonneg : 0 ≤ L+ε := by nlinarith
      have step_case (k : ℤ) (hk : N ≤ k) (h_induction : c k ≤ (c N * (L+ε)^(-N : ℤ)) * (L+ε)^k) :
        c (k+1) ≤ (c N * (L+ε)^(-N : ℤ)) * (L+ε)^(k+1) := by
        have hkpos : 0 < c k := hpos k (by omega)
        calc
          c (k+1) ≤ (L+ε) * c k := by
            have htmp : c (k+1) / c k ≤ (L+ε) := h_ratio_le k hk
            exact (div_le_iff₀ hkpos).mp htmp
          _ ≤ (L+ε) * ((c N * (L+ε)^(-N : ℤ)) * (L+ε)^k) :=
            mul_le_mul_of_nonneg_left h_induction hLε_nonneg
          _ = (c N * (L+ε)^(-N : ℤ)) * (L+ε)^(k+1) := by
            calc
              (L+ε) * ((c N * (L+ε)^(-N : ℤ)) * (L+ε)^k)
                  = (c N * (L+ε)^(-N : ℤ)) * ((L+ε) * (L+ε)^k) := by
                    simp [mul_assoc, mul_comm, mul_left_comm]
              _ = (c N * (L+ε)^(-N : ℤ)) * ((L+ε : ℝ) ^ ((1 : ℤ) + k)) := by
                calc
                  (c N * (L+ε)^(-N : ℤ)) * ((L+ε) * (L+ε)^k)
                      = (c N * (L+ε)^(-N : ℤ)) * ((L+ε : ℝ) ^ (1 : ℤ) * (L+ε)^k) := by simp
                  _ = (c N * (L+ε)^(-N : ℤ)) * ((L+ε : ℝ) ^ ((1 : ℤ) + k)) := by
                    rw [zpow_add_ℝ hLε_ne (1 : ℤ) k]
              _ = (c N * (L+ε)^(-N : ℤ)) * (L+ε : ℝ) ^ (k + (1 : ℤ)) := by
                rw [add_comm (1 : ℤ) k]
              _ = (c N * (L+ε)^(-N : ℤ)) * (L+ε)^(k+1) := rfl
      exact Int.le_induction base_case step_case n hn
    have why2_root (n:ℤ) (hn: n ≥ N) : (((c n)^(1/(n:ℝ)):ℝ):EReal) ≤ (A^(1/(n:ℝ)) * (L+ε):ℝ) := by
      rw [EReal.coe_le_coe_iff]
      have h_cn_nonneg : 0 ≤ c n := by linarith [hpos n (by omega)]
      have hnpos' : (n : ℝ) > 0 := by exact_mod_cast (show n > 0 from by omega)
      have h_exp_nonneg : 0 ≤ 1/(n : ℝ) := by positivity
      have hLε_nonneg : 0 ≤ L+ε := by nlinarith
      calc
        ((c n : ℝ) ^ (1/(n : ℝ)) : ℝ) ≤ (A * (L+ε)^n)^(1/(n:ℝ)) :=
          rpow_le_rpow h_cn_nonneg (why2 n hn) h_exp_nonneg
        _ = A^(1/(n:ℝ)) * ((L+ε)^n)^(1/(n:ℝ)) := mul_rpow (hA.le) (zpow_nonneg hLε_nonneg n)
        _ = A^(1/(n:ℝ)) * (L+ε : ℝ) := by
          calc
            A ^ (1/(n : ℝ)) * ((L + ε) ^ n) ^ (1/(n : ℝ))
                = A ^ (1/(n : ℝ)) * (((L + ε) ^ (n : ℝ)) ^ (1/(n : ℝ))) := by
                  rw [(Real.rpow_intCast (L+ε) n).symm]
            _ = A ^ (1/(n : ℝ)) * ((L + ε) ^ ((n : ℝ) * (1/(n : ℝ)))) := by
              rw [← rpow_mul hLε_nonneg]
            _ = A ^ (1/(n : ℝ)) * ((L + ε) ^ (1 : ℝ)) := by field_simp [hnpos'.ne']
            _ = A ^ (1/(n : ℝ)) * (L + ε : ℝ) := by simp
    calc
      atTop.limsup (fun n:ℤ ↦ (((c n)^(1/(n:ℝ)):ℝ):EReal))
          ≤ atTop.limsup (fun n:ℤ ↦ ((A^(1/(n:ℝ)) * (L+ε):ℝ):EReal)) := by
        apply limsup_le_limsup <;> try isBoundedDefault
        unfold EventuallyLE; rw [eventually_atTop]
        use N
      _ ≤ (atTop.limsup (fun n:ℤ ↦ ((A^(1/(n:ℝ)):ℝ):EReal))) * (atTop.limsup (fun n:ℤ ↦ ((L+ε:ℝ):EReal))) := by
        convert EReal.limsup_mul_le _ _ _ _ with n
        . rfl
        . apply Frequently.of_forall; intros; positivity
        . apply Eventually.of_forall; simp; positivity
        . simp [-coe_add]
        simp [-coe_add]; grind
      _ = (L+ε:ℝ) := by
        simp; convert one_mul _
        apply Tendsto.limsup_eq
        convert Tendsto.comp (f := fun n:ℤ ↦ (A ^ (n:ℝ)⁻¹)) (g := fun x:ℝ ↦ (x:EReal)) (y := nhds 1) _ _
        . apply continuous_coe_real_ereal.tendsto'; norm_num
        convert Tendsto.comp (f := fun n:ℤ ↦ (n:ℝ)⁻¹) (g := fun x:ℝ ↦ A^x) (y := nhds 0) _ _
        . apply (continuous_const_rpow (by positivity)).tendsto'; simp
        exact tendsto_inv_atTop_zero.comp tendsto_intCast_atTop_atTop

/-- Corollary 7.5.3 (Ratio test)-/
theorem Series.ratio_test_pos {s : Series} (hnon: ∀ n ≥ s.m, s.seq n ≠ 0)
  (h : atTop.limsup (fun n ↦ ((|s.seq (n+1)| / |s.seq n|:ℝ):EReal)) < 1) : s.absConverges := by
    apply Series.root_test_pos (lt_of_le_of_lt _ h)
    convert (ratio_ineq s.m _).2.2
    convert hnon using 1 with n
    simp

/-- Corollary 7.5.3 (Ratio test)-/
theorem Series.ratio_test_neg {s : Series} (hnon: ∀ n ≥ s.m, s.seq n ≠ 0)
  (h : atTop.liminf (fun n ↦ ((|s.seq (n+1)| / |s.seq n|:ℝ):EReal)) > 1) : s.diverges := by
    apply Series.root_test_neg (lt_of_lt_of_le h _)
    convert (ratio_ineq s.m _).1.trans (ratio_ineq s.m _).2.1 with n; rfl
    all_goals convert hnon using 1 with n; simp

/-- Corollary 7.5.3 (Ratio test) / Exercise 7.5.3 -/
theorem Series.ratio_test_inconclusive: ∃ s:Series, (∀ n ≥ s.m, s.seq n ≠ 0) ∧
  atTop.Tendsto (fun n ↦ |s.seq (n+1)| / |s.seq n|) (nhds 1) ∧ s.diverges := by
  set s := ((fun _ : ℕ ↦ (1 : ℝ)) : Series) with hs
  refine ⟨s, ?_, ?_, ?_⟩
  · intro n hn
    have hn0 : (0 : ℤ) ≤ n := by simpa [hs] using hn
    simp [hs, hn0]
  · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop (0 : ℤ)] with n hn
    have hn0 : (0 : ℤ) ≤ n := hn
    have hn1 : (0 : ℤ) ≤ n + 1 := by omega
    simp [hs, hn0, hn1]
  · exact Series.example_7_2_7

/-- Corollary 7.5.3 (Ratio test) / Exercise 7.5.3 -/
theorem Series.ratio_test_inconclusive' : ∃ s:Series, (∀ n ≥ s.m, s.seq n ≠ 0) ∧
  atTop.Tendsto (fun n ↦ |s.seq (n+1)| / |s.seq n|) (nhds 1) ∧ s.absConverges := by
  let s : Series := {
    m := 1
    seq := fun n : ℤ ↦ if h : n ≥ 1 then 1 / ((n:ℝ) * ((n:ℝ) + 1)) else 0
    vanish := by
      intro n hn
      have : n < 1 := hn
      simp [this]
  }
  have hpos : ∀ n, s.seq n ≥ 0 := by
    intro n
    dsimp [s]
    split
    · positivity
    · norm_num
  have habseq : s.abs = s := by
    ext n
    dsimp [Series.abs, Series.mk', s]
    by_cases hn : n ≥ 1
    · have h_nonneg : s.seq n ≥ 0 := hpos n
      have h1n : (1 : ℤ) ≤ n := hn
      calc
        s.abs.seq n = |s.seq n| := by
          dsimp [Series.abs, Series.mk', s]
          simp [h1n]
        _ = s.seq n := abs_of_nonneg h_nonneg
    · simp [s.vanish n (show n < 1 from by omega)]
  have h_partial_eq (N : ℤ) (hN : 1 ≤ N) : s.partial N = 1 - 1 / ((N : ℝ) + 1) := by
    refine Int.le_induction ?base ?step N hN
    · unfold s Series.partial
      simp
      ring
    · intro k hk IH
      have hk_ge_m_sub_one : k ≥ s.m - 1 := by
        dsimp [s]
        omega
      rw [Series.partial_succ s hk_ge_m_sub_one, IH]
      have hseq_val : s.seq (k + 1) = 1 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
        have hpos' : (k + 1 : ℤ) ≥ 1 := by omega
        dsimp [s]
        rw [if_pos hpos']
        have hcast : ((k + 1 : ℤ) : ℝ) = (k : ℝ) + 1 := by simp
        rw [hcast]
        have denom_eq : ((k : ℝ) + 1) + 1 = (k : ℝ) + 2 := by ring
        rw [denom_eq]
      rw [hseq_val]
      have hkpos : (k : ℝ) + 1 ≠ 0 := by
        have : (k : ℝ) ≥ 1 := by exact_mod_cast hk
        linarith
      have hkpos2 : (k : ℝ) + 2 ≠ 0 := by
        have : (k : ℝ) ≥ 1 := by exact_mod_cast hk
        linarith
      have temp_eq : (1 - 1 / ((k : ℝ) + 1)) + 1 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) = 1 - 1 / ((k : ℝ) + 2) := by
        have hkpos' : (1 : ℝ) + (k : ℝ) ≠ 0 := by simpa [add_comm] using hkpos
        have hkpos2' : (2 : ℝ) + (k : ℝ) ≠ 0 := by simpa [add_comm] using hkpos2
        field_simp [hkpos, hkpos', hkpos2, hkpos2']; ring
      have main_eq : (1 - 1 / ((k : ℝ) + 1)) + 1 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) = 1 - 1 / (((k + 1 : ℤ) : ℝ) + 1) := by
        calc
          (1 - 1 / ((k : ℝ) + 1)) + 1 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) = 1 - 1 / ((k : ℝ) + 2) := temp_eq
          _ = 1 - 1 / (((k + 1 : ℤ) : ℝ) + 1) := by
            have hcast : ((k + 1 : ℤ) : ℝ) = (k : ℝ) + 1 := by simp
            simp [hcast]
            ring
      exact main_eq
  have hconv : s.converges := by
    have hnonneg : s.nonneg := hpos
    refine ((converges_of_nonneg_iff hnonneg).mpr ?_)
    use 1
    intro N
    by_cases hN : 1 ≤ N
    · rw [h_partial_eq N hN]
      have hpos' : 0 ≤ 1 / ((N : ℝ) + 1) := by positivity
      linarith
    · unfold Series.partial
      have : Finset.Icc (1 : ℤ) N = ∅ := by
        ext n; simp; omega
      simp [s, this]
  have habs_conv : s.absConverges := by
    rw [absConverges, habseq]
    exact hconv
  have h_nonzero : ∀ n ≥ s.m, s.seq n ≠ 0 := by
    intro n hn
    have hn1 : (n : ℤ) ≥ 1 := hn
    have h_pos : 0 < s.seq n := by
      dsimp [s]
      simp [hn1]
      have hpos_n : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show (1 : ℤ) ≤ n from hn1)
      positivity
    exact ne_of_gt h_pos
  have h_ratio_eq : ∀ᶠ (n : ℤ) in atTop, |s.seq (n+1)| / |s.seq n| = (n : ℝ) / ((n : ℝ) + 2) := by
    refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
    have hn1 : (n : ℤ) ≥ 1 := hn
    have hn1_real : (n : ℝ) > 0 := by exact_mod_cast hn1
    have hnpos' : (n + 1 : ℤ) ≥ 1 := by omega
    have h_val_n : s.seq n = 1 / ((n : ℝ) * ((n : ℝ) + 1)) := by
      dsimp [s]
      simp [hn1]
    have h_val_np1 : s.seq (n + 1) = 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
      dsimp [s]
      rw [if_pos hnpos']
      have hcast : ((n + 1 : ℤ) : ℝ) = (n : ℝ) + 1 := by simp
      calc
        1 / (((n + 1 : ℤ) : ℝ) * (((n + 1 : ℤ) : ℝ) + 1)) = 1 / (((n : ℝ) + 1) * (((n : ℝ) + 1) + 1)) := by rw [hcast]
        _ = 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
          rw [show ((n : ℝ) + 1) + 1 = (n : ℝ) + 2 by ring]
    have h_nonneg_n : 0 ≤ s.seq n := hpos n
    have h_nonneg_np1 : 0 ≤ s.seq (n + 1) := hpos (n + 1)
    have h_ratio_val : |s.seq (n+1)| / |s.seq n| = (n : ℝ) / ((n : ℝ) + 2) := by
      calc
        |s.seq (n+1)| / |s.seq n| = s.seq (n+1) / s.seq n := by
          rw [abs_of_nonneg h_nonneg_np1, abs_of_nonneg h_nonneg_n]
        _ = (1 / (((n : ℝ) + 1) * ((n : ℝ) + 2))) / (1 / ((n : ℝ) * ((n : ℝ) + 1))) := by
          rw [h_val_np1, h_val_n]
        _ = (n : ℝ) / ((n : ℝ) + 2) := by
          have hN : (n : ℝ) ≠ 0 := by linarith
          have hN1 : (n : ℝ) + 1 ≠ 0 := by linarith
          have hN2 : (n : ℝ) + 2 ≠ 0 := by linarith
          field_simp [hN, hN1, hN2]
    rw [h_ratio_val]
  have h_ratio_limit : atTop.Tendsto (fun n : ℤ ↦ (n : ℝ) / ((n : ℝ) + 2)) (nhds 1) := by
    have h_event : ∀ᶠ (n : ℤ) in atTop, (n : ℝ) / ((n : ℝ) + 2) = 1 - 2 / ((n : ℝ) + 2) := by
      refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
      have hpos : (n : ℝ) + 2 ≠ 0 := by
        have : (n : ℝ) ≥ 1 := by exact_mod_cast hn
        linarith
      field_simp [hpos]
      ring
    have h_tendsto : atTop.Tendsto (fun n : ℤ ↦ 1 - 2 / ((n : ℝ) + 2)) (nhds 1) := by
      have h_two_div : atTop.Tendsto (fun n : ℤ ↦ 2 / ((n : ℝ) + 2)) (nhds 0) := by
        have h_inv : atTop.Tendsto (fun n : ℤ ↦ 1 / ((n : ℝ) + 2)) (nhds 0) := by
          have h_add : atTop.Tendsto (fun n : ℤ ↦ (n : ℝ) + 2) atTop :=
            tendsto_atTop_add_const_right atTop (2 : ℝ) (tendsto_intCast_atTop_atTop (R := ℝ))
          simpa [one_div] using (tendsto_inv_atTop_zero.comp h_add)
        simpa [div_eq_mul_inv, mul_comm] using h_inv.const_mul (2 : ℝ)
      simpa using tendsto_const_nhds.sub h_two_div
    exact ((tendsto_congr' h_event).mpr h_tendsto)
  refine ⟨s, h_nonzero, ?_, habs_conv⟩
  exact ((tendsto_congr' h_ratio_eq).mpr h_ratio_limit)

/-- Proposition 7.5.4 -/
theorem Series.root_self_converges : atTop.Tendsto (fun (n:ℕ) ↦ (n:ℝ)^(1 / (n:ℝ))) (nhds 1) := by
  simpa using tendsto_rpow_div.comp (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)

/-- Exercise 7.5.2 -/
theorem Series.poly_mul_geom_converges {x:ℝ} (hx: |x|<1) (q:ℝ) : (fun n:ℕ ↦ (n:ℝ)^q * x^n : Series).converges
  ∧ atTop.Tendsto (fun n:ℕ ↦ (n:ℝ)^q * x^n) (nhds 0) := by
  set s : Series := (fun n : ℕ ↦ (n : ℝ) ^ q * x ^ n : Series) with hs
  have hx_nonneg : 0 ≤ |x| := abs_nonneg _
  have h_s_seq_eq : ∀ n : ℤ, (0 : ℤ) ≤ n → s.seq n = ((n : ℝ) ^ q * x ^ n) := by
    intro n hn
    have h_val : s.seq n = ((n.toNat : ℝ) ^ q * x ^ n.toNat) := by
      rw [hs]
      simp [hn]
    have h_toNat_n : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn
    have h_n_real : (n.toNat : ℝ) = (n : ℝ) := by exact_mod_cast h_toNat_n
    have h_x_pow : x ^ n.toNat = x ^ (n.toNat : ℤ) := by
      simpa using (zpow_natCast (x : ℝ) (n.toNat)).symm
    have h_x_pow' : x ^ (n.toNat : ℤ) = x ^ n := by rw [h_toNat_n]
    calc
      s.seq n = ((n.toNat : ℝ) ^ q * x ^ n.toNat) := h_val
      _ = ((n.toNat : ℝ) ^ q * x ^ (n.toNat : ℤ)) := by rw [h_x_pow]
      _ = ((n.toNat : ℝ) ^ q * x ^ n) := by rw [h_x_pow']
      _ = ((n : ℝ) ^ q * x ^ n) := by rw [h_n_real]
  have h_abs_s_eq : ∀ n : ℤ, (0 : ℤ) ≤ n → |s.seq n| = ((n : ℝ) ^ q) * |x| ^ n := by
    intro n hn
    have hn' : 0 ≤ (n : ℝ) := by exact_mod_cast hn
    rw [h_s_seq_eq n hn, _root_.abs_mul, abs_rpow_of_nonneg hn', abs_zpow, abs_of_nonneg hn']
  have h_root_tendsto : atTop.Tendsto (fun n : ℤ ↦ |s.seq n| ^ (1 / (n : ℝ))) (nhds |x|) := by
    have h_simplify : ∀ᶠ (n : ℤ) in atTop, |s.seq n| ^ (1 / (n : ℝ)) = ((n : ℝ) ^ (q / (n : ℝ))) * |x| := by
      refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
      have hn_nonneg : (0 : ℤ) ≤ n := by omega
      have hn_nonneg' : 0 ≤ (n : ℝ) := by exact_mod_cast hn_nonneg
      have hnpos : (n : ℝ) > 0 := by exact_mod_cast (show (1 : ℤ) ≤ n from hn)
      have h_nonneg_npow : 0 ≤ (n : ℝ) ^ q := rpow_nonneg hn_nonneg' q
      have h_nonneg_absx_zpow : 0 ≤ |x| ^ n := zpow_nonneg hx_nonneg n
      calc
        |s.seq n| ^ (1 / (n : ℝ)) = (((n : ℝ) ^ q) * |x| ^ n) ^ (1 / (n : ℝ)) := by rw [h_abs_s_eq n hn_nonneg]
        _ = ((n : ℝ) ^ q) ^ (1 / (n : ℝ)) * (|x| ^ n) ^ (1 / (n : ℝ)) := by
          rw [mul_rpow h_nonneg_npow h_nonneg_absx_zpow]
        _ = (((n : ℝ) ^ q) ^ (1 / (n : ℝ))) * |x| := by
          have h1 : (|x| ^ n) ^ (1 / (n : ℝ)) = |x| := by
            calc
              (|x| ^ n) ^ (1 / (n : ℝ)) = (|x| ^ (n : ℝ)) ^ (1 / (n : ℝ)) := by rw [rpow_intCast]
              _ = |x| ^ ((n : ℝ) * (1 / (n : ℝ))) := by rw [rpow_mul hx_nonneg]
              _ = |x| ^ (1 : ℝ) := by field_simp [hnpos.ne']
              _ = |x| := by simp
          rw [h1]
        _ = ((n : ℝ) ^ (q / (n : ℝ))) * |x| := by
          rw [← rpow_mul hn_nonneg', show q * (1 / (n : ℝ)) = q / (n : ℝ) by ring]
    refine (tendsto_congr' h_simplify).mpr ?_
    have h_n_pow_q_div_n : atTop.Tendsto (fun n : ℤ ↦ (n : ℝ) ^ (q / (n : ℝ))) (nhds (1 : ℝ)) := by
      have h1 : atTop.Tendsto (fun n : ℤ ↦ (n : ℝ) ^ (1 / (n : ℝ))) (nhds (1 : ℝ)) := by
        simpa using tendsto_rpow_div.comp (tendsto_intCast_atTop_atTop (R := ℝ))
      have hq_cont : ContinuousAt (fun (t : ℝ) => t ^ q) (1 : ℝ) :=
        continuousAt_rpow_const (1 : ℝ) q (Or.inl (by norm_num))
      have h_eq_event : ∀ᶠ (n : ℤ) in atTop, (n : ℝ) ^ (q / (n : ℝ)) = (((n : ℝ) ^ (1 / (n : ℝ))) ^ q) := by
        refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
        have hn_nonneg' : 0 ≤ (n : ℝ) := by exact_mod_cast (show (0 : ℤ) ≤ n from by omega)
        calc
          (n : ℝ) ^ (q / (n : ℝ)) = (n : ℝ) ^ ((1 / (n : ℝ)) * q) := by
            have h_exp : q / (n : ℝ) = (1 / (n : ℝ)) * q := by
              simp [div_eq_mul_inv, mul_comm]
            rw [h_exp]
          _ = ((n : ℝ) ^ (1 / (n : ℝ))) ^ q := by rw [rpow_mul hn_nonneg' (1 / (n : ℝ)) q]
      refine (tendsto_congr' h_eq_event).mpr ?_
      simpa [one_rpow] using hq_cont.tendsto.comp h1
    simpa using h_n_pow_q_div_n.mul (tendsto_const_nhds : atTop.Tendsto (fun _ : ℤ ↦ |x|) (nhds |x|))
  have h_limsup_lt_one : atTop.limsup (fun n : ℤ ↦ ((|s.seq n| ^ (1 / (n : ℝ)) : ℝ) : EReal)) < 1 := by
    have hlim_ereal : atTop.Tendsto (fun n : ℤ ↦ ((|s.seq n| ^ (1 / (n : ℝ)) : ℝ) : EReal)) (nhds ((|x| : ℝ) : EReal)) :=
      (continuous_coe_real_ereal.tendsto (|x|)).comp h_root_tendsto
    have hlimsup_eq : atTop.limsup (fun n : ℤ ↦ ((|s.seq n| ^ (1 / (n : ℝ)) : ℝ) : EReal)) = (|x| : ℝ) :=
      hlim_ereal.limsup_eq
    rw [hlimsup_eq]
    exact EReal.coe_lt_coe_iff.mpr hx
  have habs : s.absConverges := Series.root_test_pos h_limsup_lt_one
  have hconv : s.converges := converges_of_absConverges habs
  have hzero_seq : atTop.Tendsto s.seq (nhds 0) := Series.decay_of_converges hconv
  have hzero : atTop.Tendsto (fun n : ℕ ↦ (n : ℝ) ^ q * x ^ n) (nhds 0) := by
    have hzero_n : atTop.Tendsto (fun n : ℕ ↦ s.seq (n : ℤ)) (nhds 0) :=
      hzero_seq.comp (tendsto_natCast_atTop_atTop (R := ℤ))
    refine hzero_n.congr' ?_
    refine Filter.eventually_atTop.mpr ⟨0, fun n hn => ?_⟩
    have hn' : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
    exact h_s_seq_eq (n : ℤ) hn'
  exact ⟨hconv, hzero⟩

end Chapter7
