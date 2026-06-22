import Mathlib.Tactic
import Analysis.Section_6_4
import Analysis.Section_7_2
import Analysis.Section_7_3
-- import Analysis.Section_7_4
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

/-- Proposition 7.5.4 -/
theorem Series.root_self_converges : atTop.Tendsto (fun (n:ℕ) ↦ (n:ℝ)^(1 / (n:ℝ))) (nhds 1) := by
  simpa using tendsto_rpow_div.comp (tendsto_natCast_atTop_atTop (R := ℝ))

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
  let s : Series := (fun _ : ℕ ↦ (1 : ℝ))
  have hdiv : s.diverges := by
    apply diverges_of_nodecay
    intro h
    rw [Metric.tendsto_nhds] at h
    have h' := h 1 (by norm_num : (0 : ℝ) < 1)
    rcases Filter.eventually_atTop.mp h' with ⟨N, hN⟩
    have hseq : s.seq (max N 0) = 1 := by simp [s]
    have hbound := hN (max N 0) (by omega)
    rw [Real.dist_eq, hseq, sub_zero] at hbound
    norm_num at hbound
  have hlim : atTop.Tendsto (fun n ↦ |s.seq n|^(1/(n:ℝ))) (nhds 1) := by
    have h_event : ∀ᶠ n in atTop, |s.seq n|^(1/(n:ℝ)) = 1 := by
      refine eventually_atTop.mpr ⟨0, fun n hn => ?_⟩
      simp [s, show n ≥ 0 from hn]
    refine (tendsto_congr' h_event).mpr ?_
    simpa using tendsto_const_nhds (x := (1 : ℝ))
  exact ⟨s, hlim, hdiv⟩

lemma hasSum_series_convergesTo {a : ℕ → ℝ} {L : ℝ} (h : HasSum a L) : (a : Series).convergesTo L := by
  rw [Series.convergesTo]
  have hsum : Filter.Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, a i) Filter.atTop (nhds L) :=
    h.tendsto_sum_nat
  have hsum' : Filter.Tendsto (fun n : ℕ => ∑ i ∈ Finset.range (n+1), a i) Filter.atTop (nhds L) := by
    simpa [Finset.sum_range_succ] using hsum.comp (tendsto_add_atTop_nat 1)
  have h_toNat_tendsto : Filter.Tendsto (fun (N : ℤ) => N.toNat) Filter.atTop Filter.atTop := by
    refine Filter.atTop_tendsto_atTop.mpr fun n => ?_
    refine ⟨(n : ℤ), by omega, fun N hN => ?_⟩
    have hN_nonneg : 0 ≤ N := by omega
    omega
  have h_comp : Filter.Tendsto (fun (N : ℤ) => ∑ i ∈ Finset.range (N.toNat + 1), a i) Filter.atTop (nhds L) :=
    hsum'.comp h_toNat_tendsto
  have h_event : ∀ᶠ (N : ℤ) in Filter.atTop, (a : Series).partial N = ∑ i ∈ Finset.range (N.toNat + 1), a i := by
    refine Filter.eventually_atTop.mpr ⟨0, fun N hN => ?_⟩
    unfold Series.partial
    simp [hN, Series.eval_coe]
    have hIcc_eq : Finset.Icc (0 : ℤ) N = (Finset.range (N.toNat + 1)).image (fun (i : ℕ) => (i : ℤ)) := by
      ext x
      constructor
      · intro hx
        rcases Finset.mem_Icc.mp hx with ⟨hx1, hx2⟩
        have hx_lt : x.toNat < N.toNat + 1 := by omega
        apply Finset.mem_image.mpr
        refine ⟨x.toNat, Finset.mem_range.mpr hx_lt, ?_⟩
        simp
      · intro hx
        rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
        rw [Finset.mem_range] at hi
        have hi_nonneg : (0 : ℤ) ≤ (i : ℤ) := by exact mod_cast Nat.zero_le i
        have hi_le_N : (i : ℤ) ≤ N := by
          have hNtoNat_eq : (N.toNat : ℤ) = N := by exact mod_cast Int.toNat_of_nonneg hN
          have hi_le_NtoNat : i ≤ N.toNat := by omega
          exact mod_cast hi_le_NtoNat
        exact Finset.mem_Icc.mpr ⟨hi_nonneg, hi_le_N⟩
    rw [hIcc_eq, Finset.sum_image]
    · simp
    · intro x hx y hy h
      exact Nat.cast_inj.mp h
  exact Filter.Tendsto.congr' h_event h_comp

lemma summable_series_converges {a : ℕ → ℝ} (ha : Summable a) : (a : Series).converges := by
  exact Series.converges_of_convergesTo (hasSum_series_convergesTo ha.hasSum)

/-- Theorem 7.5.1 (Root test) / Exercise 7.5.3 -/
theorem Series.root_test_inconclusive' : ∃ s:Series,
  atTop.Tendsto (fun n ↦ |s.seq n|^(1/(n:ℝ))) (nhds 1) ∧ s.absConverges := by
  set s := (fun n : ℕ ↦ 1/((n+1:ℝ)^2) : Series) with hs
  have h_nonneg : ∀ n : ℤ, 0 ≤ s.seq n := by
    intro n
    dsimp [s, Series.instCoe]
    split <;> positivity
  have h_absConv : s.absConverges := by
    rw [Series.absConverges]
    have h_abs_eq : s.abs = s := by
      apply Series.ext
      · rfl
      · ext n; simp [s, h_nonneg n]
    rw [h_abs_eq]
    have h_q_conv : (mk' (m := 1) fun (n : ℤ) => 1 / ((n : ℝ)^2) : Series).converges :=
      ((Series.converges_qseries (2 : ℝ) (by norm_num : (2 : ℝ) > 0)).mpr (by norm_num : (2 : ℝ) > 1))
    have h_q_convTo : (mk' (m := 1) fun (n : ℤ) => 1 / ((n : ℝ)^2) : Series).convergesTo 
      ((mk' (m := 1) fun (n : ℤ) => 1 / ((n : ℝ)^2) : Series).sum) :=
      Series.convergesTo_sum h_q_conv
    have h_shifted_convTo : (mk' (m := 0) fun (n : ℤ) => 
        ((mk' (m := 1) fun (n : ℤ) => 1 / ((n : ℝ)^2) : Series).seq (n + 1))).convergesTo
        ((mk' (m := 1) fun (n : ℤ) => 1 / ((n : ℝ)^2) : Series).sum) :=
      Series.shift h_q_convTo (-1 : ℤ)
    have h_eq : (mk' (m := 0) fun (n : ℤ) => 
        ((mk' (m := 1) fun (n : ℤ) => 1 / ((n : ℝ)^2) : Series).seq (n + 1))) = s := by
      apply Series.ext
      · rfl
      · ext n; simp [s]
    have h_convTo : s.convergesTo ((mk' (m := 1) fun (n : ℤ) => 1 / ((n : ℝ)^2) : Series).sum) := by
      rw [h_eq] at h_shifted_convTo; exact h_shifted_convTo
    exact ⟨(mk' (m := 1) fun (n : ℤ) => 1 / ((n : ℝ)^2) : Series).sum, h_convTo⟩
  have h_root_limit : atTop.Tendsto (fun n : ℕ ↦ |s.seq n|^(1/(n:ℝ))) (nhds (1 : ℝ)) := by
    have h_no_abs : ∀ n : ℕ, |s.seq n| = s.seq n := by
      intro n; rw [abs_of_nonneg (h_nonneg n)]
    simp_rw [h_no_abs, s]
    have h_pos : ∀ n : ℕ, 0 < (1 / (((n : ℝ) + 1)^2)) ^ (1 / (n : ℝ)) := by
      intro n; positivity
    have h_log_eq : ∀ n : ℕ, Real.log ((1 / (((n : ℝ) + 1)^2)) ^ (1 / (n : ℝ))) = (-2 : ℝ) * (Real.log ((n : ℝ) + 1) / (n : ℝ)) := by
      intro n
      have h_nonzero_one : (1 : ℝ) ≠ 0 := by norm_num
      have h_nonzero_np1sq : ((n : ℝ) + 1)^2 ≠ 0 := by positivity
      calc
        Real.log ((1 / (((n : ℝ) + 1)^2)) ^ (1 / (n : ℝ))) = (1 / (n : ℝ)) * Real.log (1 / (((n : ℝ) + 1)^2)) := by
          rw [Real.log_rpow (by positivity : 0 < 1 / (((n : ℝ) + 1)^2)) (1 / (n : ℝ))]
        _ = (1 / (n : ℝ)) * (Real.log 1 - Real.log (((n : ℝ) + 1)^2)) := by
          rw [Real.log_div h_nonzero_one h_nonzero_np1sq]
        _ = (1 / (n : ℝ)) * (0 - Real.log (((n : ℝ) + 1)^2)) := by norm_num
        _ = (1 / (n : ℝ)) * (-Real.log (((n : ℝ) + 1)^2)) := by ring
        _ = -(Real.log (((n : ℝ) + 1)^2)) / (n : ℝ) := by ring
        _ = -(2 * Real.log ((n : ℝ) + 1)) / (n : ℝ) := by rw [Real.log_pow, Nat.cast_ofNat]
        _ = (-2 : ℝ) * (Real.log ((n : ℝ) + 1) / (n : ℝ)) := by ring
    have h_log_tendsto : atTop.Tendsto (fun (n : ℕ) => Real.log ((1 / (((n : ℝ) + 1)^2)) ^ (1 / (n : ℝ)))) (nhds (0 : ℝ)) := by
      have h_eq : (fun (n : ℕ) => Real.log ((1 / (((n : ℝ) + 1)^2)) ^ (1 / (n : ℝ)))) = 
        (fun (n : ℕ) => (-2 : ℝ) * (Real.log ((n : ℝ) + 1) / (n : ℝ))) := by
        ext n; exact h_log_eq n
      rw [h_eq]
      have h_tendsto : atTop.Tendsto (fun (n : ℕ) => (-2 : ℝ) * (Real.log ((n : ℝ) + 1) / (n : ℝ))) (nhds ((-2 : ℝ) * (0 : ℝ))) :=
        (tendsto_const_nhds.mul ?_)
      · simpa using h_tendsto
      · -- tendsto_log_np1_div_n_atTop
        have h_log_np1_div_n : atTop.Tendsto (fun (n : ℕ) => Real.log ((n : ℝ) + 1) / (n : ℝ)) (nhds (0 : ℝ)) := by
          have h_log_div_np1 : atTop.Tendsto (fun (n : ℕ) => Real.log ((n : ℝ) + 1) / ((n : ℝ) + 1)) (nhds (0 : ℝ)) := by
            have h_base : atTop.Tendsto (fun (n : ℕ) => Real.log (n : ℝ) / (n : ℝ)) (nhds (0 : ℝ)) := by
              -- This follows from root_self_converges
              have h_root_n : atTop.Tendsto (fun (n : ℕ) => ((n : ℝ) ^ (1 / (n : ℝ)) : ℝ)) (nhds 1) := by
                simpa using tendsto_rpow_div.comp (tendsto_natCast_atTop_atTop (R := ℝ))
              have h_log_cont : ContinuousAt Real.log (1 : ℝ) :=
                Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)
              have h_log_root : atTop.Tendsto (fun (n : ℕ) => Real.log (((n : ℝ) ^ (1 / (n : ℝ))))) (nhds (0 : ℝ)) := by
                have := h_log_cont.tendsto.comp h_root_n
                simpa using this
              have h_log_eq : (fun (n : ℕ) => Real.log (((n : ℝ) ^ (1 / (n : ℝ))))) =ᶠ[atTop]
                  (fun (n : ℕ) => Real.log (n : ℝ) / (n : ℝ)) := by
                refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
                have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n from by omega)
                calc
                  Real.log (((n : ℝ) ^ (1 / (n : ℝ)))) = ((1 / (n : ℝ)) * Real.log (n : ℝ)) := by
                    rw [Real.log_rpow hnpos (1 / (n : ℝ))]
                  _ = Real.log (n : ℝ) / (n : ℝ) := by ring
              have h_log_root' : atTop.Tendsto (fun (n : ℕ) => Real.log (n : ℝ) / (n : ℝ)) (nhds (0 : ℝ)) :=
                h_log_root.congr' h_log_eq
              exact h_log_root'
            have h_eq : ((fun (n : ℕ) => Real.log (n : ℝ) / (n : ℝ)) ∘ (fun (n : ℕ) => n+1)) = 
              (fun (n : ℕ) => Real.log ((n : ℝ) + 1) / ((n : ℝ) + 1)) := by
              ext n; simp
            simpa [h_eq] using h_base.comp (tendsto_add_atTop_nat 1)
          have h_ratio : atTop.Tendsto (fun (n : ℕ) => ((n : ℝ) + 1) / (n : ℝ)) (nhds (1 : ℝ)) := by
            have h_one_div : atTop.Tendsto (fun (n : ℕ) => (1 : ℝ) / (n : ℝ)) (nhds (0 : ℝ)) := by
              simpa [div_eq_inv_mul] using (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp (tendsto_natCast_atTop_atTop (R := ℝ))
            have h_eq : (fun (n : ℕ) => ((n : ℝ) + 1) / (n : ℝ)) =ᶠ[atTop] (fun (n : ℕ) => (1 : ℝ) + (1 : ℝ) / (n : ℝ)) := by
              refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
              have hnpos : (n : ℝ) ≠ 0 := by
                have : 0 < n := by omega
                exact_mod_cast this.ne'
              field_simp [hnpos]
            refine (tendsto_congr' h_eq).mpr ?_
            simpa using (tendsto_const_nhds.add h_one_div)
          have h_log_np1_div_n' : (fun (n : ℕ) => Real.log ((n : ℝ) + 1) / (n : ℝ)) =ᶠ[atTop]
              (fun (n : ℕ) => (Real.log ((n : ℝ) + 1) / ((n : ℝ) + 1)) * (((n : ℝ) + 1) / (n : ℝ))) := by
            refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
            have hnpos : (n : ℝ) ≠ 0 := by
              have : 0 < n := by omega
              exact_mod_cast this.ne'
            field_simp [hnpos]
          have h_product : atTop.Tendsto (fun (n : ℕ) => (Real.log ((n : ℝ) + 1) / ((n : ℝ) + 1)) * (((n : ℝ) + 1) / (n : ℝ))) (nhds (0 : ℝ)) := by
            have : (0 : ℝ) = (0 : ℝ) * (1 : ℝ) := by norm_num
            rw [this]
            exact h_log_div_np1.mul h_ratio
          exact (tendsto_congr' h_log_np1_div_n').mpr h_product
        exact h_log_np1_div_n
    have h_cont_exp : ContinuousAt Real.exp (0 : ℝ) := Real.continuous_exp.continuousAt
    have h_exp_tendsto : atTop.Tendsto (fun (n : ℕ) => Real.exp (Real.log ((1 / (((n : ℝ) + 1)^2)) ^ (1 / (n : ℝ))))) (nhds (Real.exp (0 : ℝ))) :=
      h_cont_exp.tendsto.comp h_log_tendsto
    have h_eq_exp : (fun (n : ℕ) => (1 / (((n : ℝ) + 1)^2)) ^ (1 / (n : ℝ))) = 
      (fun (n : ℕ) => Real.exp (Real.log ((1 / (((n : ℝ) + 1)^2)) ^ (1 / (n : ℝ))))) := by
      ext n; rw [Real.exp_log (h_pos n)]
    rw [h_eq_exp]; simpa using h_exp_tendsto
  exact ⟨s, h_root_limit, h_absConv⟩

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
  refine ⟨ ?_, ?_, ?_ ⟩
  · set L' := atTop.liminf (fun n ↦ ((c (n+1) / c n:ℝ):EReal))
    by_cases hL_bot : L' = ⊥; · rw [hL_bot]; exact bot_le
    have hL'pos : 0 ≤ L' := by
      apply le_limsup_of_frequently_le'
      rw [frequently_atTop]
      intro N; refine ⟨max N m, by omega, ?_⟩
      have hpos1 := hpos (max N m) (by omega)
      have hpos2 := hpos ((max N m)+1) (by omega)
      positivity
    have h_core (r : ℝ) (hr_pos : 0 < r) (hr_liminf : (r : EReal) < L') :
      (r : EReal) ≤ atTop.liminf (fun n ↦ ↑((c n)^(1/(n:ℝ)):ℝ)) := by
      have h_eventually : ∀ᶠ n in atTop, ((r : ℝ) : EReal) < ((c (n+1) / c n:ℝ):EReal) :=
        eventually_lt_of_lt_liminf hr_liminf (by isBoundedDefault)
      rw [eventually_atTop] at h_eventually
      choose N' hN using h_eventually
      set N := max N' (max m 1)
      have h_ratio_lower_bound (n : ℤ) (hn : n ≥ N) : r < c (n+1) / c n := by
        have hn' : n ≥ N' := by omega
        have h := hN n hn'
        rw [EReal.coe_lt_coe_iff] at h
        exact h
      set B := c N * r ^ (-N : ℤ)
      have hBpos : 0 < B := by
        specialize hpos N (by omega)
        positivity
      have why2_lower (n : ℤ) (hn : n ≥ N) : B * r ^ (n : ℤ) ≤ c n := by
        refine Int.le_induction ?_ (fun k hk ih => ?_) n hn
        · dsimp [B]
          have hr_ne_zero : r ≠ 0 := by linarith
          calc
            (c N * r ^ (-N : ℤ)) * r ^ (N : ℤ) = c N * (r ^ (-N : ℤ) * r ^ (N : ℤ)) := by ring
            _ = c N * (r ^ ((-N : ℤ) + (N : ℤ))) := by rw [zpow_add₀ hr_ne_zero]
            _ = c N * (r ^ (0 : ℤ)) := by ring
            _ = c N * 1 := by simp
            _ = c N := by simp
        · have hposk : c k > 0 := hpos k (by omega)
          have h_ratio_lower : r < c (k+1) / c k := h_ratio_lower_bound k (by omega)
          have h_r_ne_zero : r ≠ 0 := by linarith
          have h_step : B * r ^ (k+1 : ℤ) < c (k+1) := by
            calc
              B * r ^ (k+1 : ℤ) = (B * r ^ (k : ℤ)) * r := by
                calc
                  B * r ^ (k+1 : ℤ) = B * (r ^ (k : ℤ) * r) := by
                    rw [zpow_add₀ h_r_ne_zero (k : ℤ) (1 : ℤ), zpow_one, mul_comm]
                  _ = (B * r ^ (k : ℤ)) * r := by ring
              _ ≤ c k * r := by nlinarith
              _ = r * c k := by ring
              _ < c (k+1) := by
                have h_mul : (c (k+1) / c k - r) * c k > 0 := by
                  have h_diff_pos : 0 < c (k+1) / c k - r := by linarith
                  nlinarith [hposk]
                nlinarith
          exact le_of_lt h_step
      have why2_root (n : ℤ) (hn : n ≥ N) : ((B ^ (1 / (n : ℝ)) * r : ℝ) : EReal) ≤ (((c n)^(1/(n:ℝ)):ℝ):EReal) := by
        rw [EReal.coe_le_coe_iff]
        have hn' : n > 0 := by omega
        have hposn : c n > 0 := hpos n (by omega)
        have hr_nonneg : 0 ≤ r := by linarith
        have hB_nonneg : 0 ≤ B := by linarith
        calc
          B ^ (1 / (n : ℝ)) * r = (B ^ (1 / (n : ℝ))) * ((r : ℝ) ^ (n : ℝ)) ^ (1 / (n : ℝ)) := by
            calc
              r = r ^ (1 : ℝ) := by simp
              _ = ((r : ℝ) ^ (n : ℝ)) ^ (1 / (n : ℝ)) := by
                rw [← rpow_mul hr_nonneg, show (n : ℝ) * (1 / (n : ℝ)) = (1 : ℝ) by field_simp [hn'.ne'], rpow_one]
              _ = ((r : ℝ) ^ (n : ℝ)) ^ (1 / (n : ℝ)) := rfl
            _ = B ^ (1 / (n : ℝ)) * ((r : ℝ) ^ (n : ℝ)) ^ (1 / (n : ℝ)) := by rfl
          _ = (B * (r : ℝ) ^ (n : ℝ)) ^ (1 / (n : ℝ)) := by
            rw [mul_rpow (by positivity : 0 ≤ B) (by positivity : 0 ≤ (r : ℝ) ^ (n : ℝ))]
          _ ≤ (c n) ^ (1 / (n : ℝ)) := by
            apply rpow_le_rpow (by positivity) ?_ (by positivity : 0 ≤ 1 / (n : ℝ))
            calc
              B * (r : ℝ) ^ (n : ℝ) = B * ((r : ℝ) ^ (n : ℤ) : ℝ) := by
                simp [rpow_intCast]
              _ ≤ c n := why2_lower n hn
      have h_B_tendsto_one : atTop.Tendsto (fun n : ℤ ↦ B ^ (1 / (n : ℝ))) (nhds (1 : ℝ)) := by
        have h_exp_tendsto : atTop.Tendsto (fun n : ℤ ↦ (n : ℝ)⁻¹) (nhds (0 : ℝ)) := by
          simpa using tendsto_inv_atTop_zero.comp tendsto_intCast_atTop_atTop
        have h_cont : ContinuousAt (fun x : ℝ ↦ B ^ x) (0 : ℝ) :=
          continuousAt_const_rpow (by linarith [hBpos])
        have : (fun n : ℤ ↦ B ^ (1 / (n : ℝ))) = (fun x : ℝ ↦ B ^ x) ∘ (fun n : ℤ ↦ (n : ℝ)⁻¹) := by
          ext n; simp
        rw [this]
        exact h_cont.tendsto.comp h_exp_tendsto
      have h_Br_tendsto : atTop.Tendsto (fun n : ℤ ↦ (B ^ (1 / (n : ℝ)) * r : ℝ)) (nhds (r : ℝ)) := by
        simpa [mul_comm] using (h_B_tendsto_one.mul (tendsto_const_nhds (x := r)))
      have h_Br_liminf : atTop.liminf (fun n : ℤ ↦ ((B ^ (1 / (n : ℝ)) * r : ℝ) : EReal)) = (r : EReal) := by
        apply Filter.Tendsto.liminf_eq
        refine (continuous_coe_real_ereal.tendsto (r : ℝ)).comp h_Br_tendsto
      calc
        (r : EReal) = atTop.liminf (fun n : ℤ ↦ ((B ^ (1 / (n : ℝ)) * r : ℝ) : EReal)) := by
          rw [h_Br_liminf]
        _ ≤ atTop.liminf (fun n : ℤ ↦ (((c n)^(1/(n:ℝ)):ℝ):EReal)) := by
          apply liminf_le_liminf
          · unfold EventuallyLE; rw [eventually_atTop]
            refine ⟨N, fun n hn => why2_root n hn⟩
          · isBoundedDefault
          · isBoundedDefault
    by_cases hL_top : L' = ⊤
    · rw [hL_top]
      apply le_of_forall_lt_imp_le_of_dense
      intro y hy
      by_cases hy_nonpos : y ≤ (0 : EReal)
      · calc
          y ≤ (0 : EReal) := hy_nonpos
          _ ≤ atTop.liminf (fun n ↦ ↑((c n)^(1/(n:ℝ)):ℝ)) := by
            apply le_liminf_of_le (by isBoundedDefault)
            rw [eventually_atTop]
            refine ⟨m, fun n hn => ?_⟩
            positivity
      have hy_pos : (0 : EReal) < y := lt_of_not_ge hy_nonpos
      have hy_not_top : y ≠ ⊤ := by
        intro hyt; rw [hyt] at hy; exact lt_irrefl ⊤ hy
      have hy_not_bot : y ≠ ⊥ := by
        intro hyb; rw [hyb] at hy_pos; exact lt_irrefl (0 : EReal) hy_pos
      set r := y.toReal
      have hy_eq : (y : EReal) = (r : ℝ) := (coe_toReal hy_not_top hy_not_bot).symm
      have hr_pos : 0 < r := by
        rw [hy_eq] at hy_pos
        exact EReal.coe_pos.mp hy_pos
      have hr_liminf : (r : EReal) < L' := by
        rw [hL_top]; exact coe_lt_top (r : ℝ)
      calc
        y = (r : EReal) := hy_eq.symm
        _ ≤ atTop.liminf (fun n ↦ ↑((c n)^(1/(n:ℝ)):ℝ)) := h_core r hr_pos hr_liminf
    have hL'ne_top : L' ≠ ⊤ := hL_top
    set L := L'.toReal
    have hL' : L' = L := (coe_toReal hL'ne_top hL_bot).symm
    have hLpos : 0 ≤ L := by
      rw [hL'] at hL'pos; norm_cast at hL'pos
    apply le_of_forall_lt_imp_le_of_dense
    intro y hy
    by_cases hy_nonpos : y ≤ (0 : EReal)
    · calc
        y ≤ (0 : EReal) := hy_nonpos
        _ ≤ atTop.liminf (fun n ↦ ↑((c n)^(1/(n:ℝ)):ℝ)) := by
          apply le_liminf_of_le (by isBoundedDefault)
          rw [eventually_atTop]
          refine ⟨m, fun n hn => ?_⟩
          positivity
    have hy_pos : (0 : EReal) < y := lt_of_not_ge hy_nonpos
    have hy_not_top : y ≠ ⊤ := by
      intro hyt; rw [hyt, hL'] at hy; simp at hy
    have hy_not_bot : y ≠ ⊥ := by
      intro hyb; rw [hyb] at hy_pos; exact lt_irrefl (0 : EReal) hy_pos
    set r := y.toReal
    have hy_eq : (y : EReal) = (r : ℝ) := (coe_toReal hy_not_top hy_not_bot).symm
    have hr_pos : 0 < r := by
      rw [hy_eq] at hy_pos
      exact EReal.coe_pos.mp hy_pos
    have hr_liminf : (r : EReal) < L' := by
      rw [hy_eq, hL', EReal.coe_lt_coe_iff] at hy
      exact hy
    calc
      y = (r : EReal) := hy_eq.symm
      _ ≤ atTop.liminf (fun n ↦ ↑((c n)^(1/(n:ℝ)):ℝ)) := h_core r hr_pos hr_liminf
  · refine liminf_le_limsup ?_ ?_
    · isBoundedDefault
    · isBoundedDefault
  · set L' := limsup (fun n ↦ ((c (n+1) / c n:ℝ):EReal)) .atTop
    by_cases hL : L' = ⊤; · rw [hL]; exact le_top
    have hL'pos : 0 ≤ L' := by
      apply le_limsup_of_frequently_le'
      rw [frequently_atTop]
      intro N; use max N m, by omega
      have hpos1 := hpos (max N m) (by omega)
      have hpos2 := hpos ((max N m)+1) (by omega)
      positivity
    have why : L' ≠ ⊥ := by
      intro h
      have h0 : 0 ≤ L' := hL'pos
      rw [h] at h0
      have : ¬ ((0 : EReal) ≤ ⊥) := by simp
      exact this h0
    set L := L'.toReal
    have hL' : L' = L := (coe_toReal hL why).symm
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
    have h_ratio_bound (n:ℤ) (hn: n ≥ N) : c (n+1) / c n ≤ (L + ε) := by
      have : n ≥ N' := by omega
      have npos : 0 < n := by omega
      specialize hN n this; norm_cast at hN; linarith
    set A := c N * (L+ε)^(-N)
    have hA : 0 < A := by specialize hpos N (by omega); positivity
    have why2 (n:ℤ) (hn: n ≥ N) : c n ≤ A * (L+ε)^n := by
      refine Int.le_induction ?_ (fun k hk ih => ?_) n hn
      · dsimp [A]
        have hposN : c N > 0 := hpos N (by
          have : N ≥ m := by
            have : N = max N' (max m 1) := rfl
            omega
          exact this)
        have hpos_base : L + ε > 0 := by nlinarith
        calc
          c N ≤ c N * 1 := by nlinarith
          _ = c N * ((L + ε) ^ (-N : ℤ) * (L + ε) ^ (N : ℤ)) := by
            have : (L + ε) ^ (-N : ℤ) * (L + ε) ^ (N : ℤ) = 1 := by
              calc
                (L + ε) ^ (-N : ℤ) * (L + ε) ^ (N : ℤ) = ((L + ε) ^ (N : ℤ))⁻¹ * (L + ε) ^ (N : ℤ) := by simp
                _ = 1 := by field_simp [hpos_base.ne']
            rw [this]
          _ = (c N * (L + ε) ^ (-N : ℤ)) * (L + ε) ^ (N : ℤ) := by ring
      · have hk_ge_N : k ≥ N := hk
        have hposk : c k > 0 := hpos k (by
          have : k ≥ m := by omega
          exact this)
        calc
        c (k+1) = (c (k+1) / c k) * c k := by field_simp [hposk.ne']
        _ ≤ (L + ε) * (A * (L + ε)^k) := by
          have h_bound := h_ratio_bound k (by omega)
          have h_mul' : c (k+1) ≤ (L + ε) * c k := by
            have h_diff_nonpos : c (k+1) / c k - (L + ε) ≤ 0 := sub_nonpos.mpr h_bound
            have h_prod_nonpos : (c (k+1) / c k - (L + ε)) * c k ≤ 0 :=
              mul_nonpos_of_nonpos_of_nonneg h_diff_nonpos (by positivity)
            have h_eq : c (k+1) - (L + ε) * c k = (c (k+1) / c k - (L + ε)) * c k := by
              field_simp [hposk.ne']
            nlinarith
          calc
            (c (k+1) / c k) * c k = c (k+1) := by field_simp [hposk.ne']
            _ ≤ (L + ε) * c k := h_mul'
            _ ≤ (L + ε) * (A * (L + ε)^k) := by
              nlinarith
        _ = A * (L + ε)^(k+1) := by
          calc
            (L + ε) * (A * (L + ε)^k) = A * ((L + ε) * (L + ε)^k) := by ring
            _ = A * (L + ε)^(k+1) := by
              calc
                A * ((L + ε) * (L + ε)^(k : ℤ)) = A * ((L + ε)^(1 : ℤ) * (L + ε)^(k : ℤ)) := by simp
                _ = A * ((L + ε)^((1 : ℤ) + (k : ℤ))) := by
                  rw [zpow_add₀ (by positivity : (L + ε) ≠ 0) (1 : ℤ) (k : ℤ)]
                _ = A * (L + ε)^(k+1 : ℤ) := by ring
                _ = A * (L + ε)^(k+1) := rfl
    have why2_root (n:ℤ) (hn: n ≥ N) : (((c n)^(1/(n:ℝ)):ℝ):EReal) ≤ (A^(1/(n:ℝ)) * (L+ε):ℝ) := by
      rw [EReal.coe_le_coe_iff]
      have hn' : n > 0 := by omega
      calc
        _ ≤ (A * (L+ε)^n)^(1/(n:ℝ)) := by
          apply_rules [rpow_le_rpow, le_of_lt (hpos n _)]; omega; positivity
        _ = A^(1/(n:ℝ)) * ((L+ε)^n)^(1/(n:ℝ)) := mul_rpow (by positivity) (by positivity)
        _ = _ := by
          congr
          rw [←rpow_intCast, ←rpow_mul (by positivity)]
          convert rpow_one _
          field_simp
    calc
      _ ≤ atTop.limsup (fun n:ℤ ↦ ((A^(1/(n:ℝ)) * (L+ε):ℝ):EReal)) := by
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
  let s : Series := (fun _ : ℕ ↦ (1 : ℝ))
  have h_nonzero : ∀ n ≥ s.m, s.seq n ≠ 0 := by
    intro n hn
    have hn_nonneg : n ≥ 0 := hn
    have h_one_ne_zero : (1 : ℝ) ≠ 0 := by norm_num
    simpa [s, Series.instCoe, hn_nonneg] using h_one_ne_zero
  have h_tendsto : atTop.Tendsto (fun n ↦ |s.seq (n+1)| / |s.seq n|) (nhds (1 : ℝ)) := by
    have h_event : ∀ᶠ n in atTop, |s.seq (n+1)| / |s.seq n| = 1 := by
      refine eventually_atTop.mpr ⟨0, fun n hn => ?_⟩
      have hn_nonneg : n ≥ 0 := hn
      have hn1_nonneg : n+1 ≥ 0 := by omega
      simp [s, Series.instCoe, hn_nonneg, hn1_nonneg]
    refine (tendsto_congr' h_event).mpr ?_
    simpa using tendsto_const_nhds (x := (1 : ℝ))
  have h_div : s.diverges := by
    apply diverges_of_nodecay
    intro h
    rw [Metric.tendsto_nhds] at h
    have h' := h 1 (by norm_num : (0 : ℝ) < 1)
    rcases Filter.eventually_atTop.mp h' with ⟨N, hN⟩
    have hseq : s.seq (max N 0) = 1 := by simp [s]
    have hbound := hN (max N 0) (by omega)
    rw [Real.dist_eq, hseq, sub_zero] at hbound
    norm_num at hbound
  exact ⟨s, h_nonzero, h_tendsto, h_div⟩

/-- Corollary 7.5.3 (Ratio test) / Exercise 7.5.3 -/
theorem Series.ratio_test_inconclusive' : ∃ s:Series, (∀ n ≥ s.m, s.seq n ≠ 0) ∧
  atTop.Tendsto (fun n ↦ |s.seq (n+1)| / |s.seq n|) (nhds 1) ∧ s.absConverges := by
  set s := (fun n : ℕ ↦ 1/((n+1:ℝ)^2) : Series) with hs
  have h_nonneg : ∀ n : ℤ, 0 ≤ s.seq n := by
    intro n
    dsimp [s, Series.instCoe]
    split
    · simp; positivity
    · simp
  have h_nonzero : ∀ n ≥ s.m, s.seq n ≠ 0 := by
    intro n hn
    have hpos : s.seq n > 0 := by
      dsimp [s, Series.instCoe]
      have hn_nonneg : n ≥ (0 : ℤ) := hn
      split
      · positivity
      · omega
    exact hpos.ne'
  have h_absConv : s.absConverges := by
    rw [Series.absConverges]
    have h_abs_eq : s.abs = s := by
      apply Series.ext
      · rfl
      · ext n; simp [s, h_nonneg n]
    rw [h_abs_eq]
    have h_q_conv : (Series.mk' (m := 1) fun (n : ℤ) => 1 / ((n : ℝ)^2) : Series).converges :=
      ((Series.converges_qseries (2 : ℝ) (by norm_num : (2 : ℝ) > 0)).mpr (by norm_num : (2 : ℝ) > 1))
    have h_q_convTo : (Series.mk' (m := 1) fun (n : ℤ) => 1 / ((n : ℝ)^2) : Series).convergesTo
      ((Series.mk' (m := 1) fun (n : ℤ) => 1 / ((n : ℝ)^2) : Series).sum) :=
      Series.convergesTo_sum h_q_conv
    have h_shifted_convTo : (Series.mk' (m := 0) fun (n : ℤ) =>
        ((Series.mk' (m := 1) fun (n : ℤ) => 1 / ((n : ℝ)^2) : Series).seq (n + 1))).convergesTo
        ((Series.mk' (m := 1) fun (n : ℤ) => 1 / ((n : ℝ)^2) : Series).sum) :=
      Series.shift h_q_convTo (-1 : ℤ)
    have h_eq : (Series.mk' (m := 0) fun (n : ℤ) =>
        ((Series.mk' (m := 1) fun (n : ℤ) => 1 / ((n : ℝ)^2) : Series).seq (n + 1))) = s := by
      apply Series.ext
      · rfl
      · ext n; simp [s]
    have h_convTo : s.convergesTo ((Series.mk' (m := 1) fun (n : ℤ) => 1 / ((n : ℝ)^2) : Series).sum) := by
      rw [h_eq] at h_shifted_convTo; exact h_shifted_convTo
    exact ⟨(Series.mk' (m := 1) fun (n : ℤ) => 1 / ((n : ℝ)^2) : Series).sum, h_convTo⟩
  have h_tendsto : atTop.Tendsto (fun n ↦ |s.seq (n+1)| / |s.seq n|) (nhds (1 : ℝ)) := by
    have h_ratio_simp : ∀ n : ℕ, |s.seq (n+1)| / |s.seq n| = (((n : ℝ)+1)/((n : ℝ)+2))^2 := by
      intro n
      have h_nonneg_n : s.seq (n : ℤ) ≥ 0 := h_nonneg (n : ℤ)
      have h_nonneg_np1 : s.seq ((n : ℤ) + 1) ≥ 0 := h_nonneg ((n : ℤ) + 1)
      have hseq_n : s.seq (n : ℤ) = 1 / (((n : ℝ) + 1)^2) := by
        dsimp [s, Series.instCoe]
      have hseq_np1 : s.seq ((n : ℤ) + 1) = 1 / (((n : ℝ) + 2)^2) := by
        dsimp [s, Series.instCoe]
        have hn1_nonneg : (n : ℤ) + 1 ≥ (0 : ℤ) := by omega
        simp [hn1_nonneg]
        ring
      calc
        |s.seq (n+1)| / |s.seq n| = |s.seq ((n : ℤ) + 1)| / |s.seq (n : ℤ)| := by simp
        _ = s.seq ((n : ℤ) + 1) / s.seq (n : ℤ) := by simp [abs_of_nonneg h_nonneg_np1, abs_of_nonneg h_nonneg_n]
        _ = (1 / (((n : ℝ) + 2)^2)) / (1 / (((n : ℝ) + 1)^2)) := by simp [hseq_n, hseq_np1]
        _ = (((n : ℝ) + 1) / ((n : ℝ) + 2))^2 := by
          field_simp [show (n : ℝ) + 1 ≠ 0 from by positivity, show (n : ℝ) + 2 ≠ 0 from by positivity]
          ring
    have h_limit : atTop.Tendsto (fun (n : ℕ) => (((n : ℝ)+1)/((n : ℝ)+2))^2) (nhds (1 : ℝ)) := by
      have h_one_div_np2 : atTop.Tendsto (fun (n : ℕ) => 1 / ((n : ℝ) + 2)) (nhds (0 : ℝ)) := by
        have h_np2_tendsto : atTop.Tendsto (fun (n : ℕ) => (n : ℝ) + 2) atTop :=
          (tendsto_natCast_atTop_atTop (R := ℝ)).add_const 2
        simpa [one_div] using (tendsto_inv_atTop_zero).comp h_np2_tendsto
      have h_inner : atTop.Tendsto (fun (n : ℕ) => ((n : ℝ) + 1) / ((n : ℝ) + 2)) (nhds (1 : ℝ)) := by
        have h_eq : (fun n : ℕ => ((n : ℝ) + 1) / ((n : ℝ) + 2)) =ᶠ[atTop] (fun n : ℕ => (1 : ℝ) - 1 / ((n : ℝ) + 2)) := by
          refine eventually_atTop.mpr ⟨0, fun n hn => ?_⟩
          have hpos : (n : ℝ) + 2 ≠ 0 := by positivity
          field_simp [hpos]
          ring
        refine (tendsto_congr' h_eq).mpr ?_
        simpa [sub_eq_add_neg] using (tendsto_const_nhds.sub h_one_div_np2)
      have h_cont_sq : ContinuousAt (fun (x : ℝ) => x^2) (1 : ℝ) := by continuity
      exact h_cont_sq.tendsto.comp h_inner
    refine (tendsto_congr' ?_).mpr h_limit
    refine eventually_atTop.mpr ⟨0, fun n hn => ?_⟩
    rw [h_ratio_simp n]
  exact ⟨s, h_nonzero, h_tendsto, h_absConv⟩


/-- Exercise 7.5.2 -/
theorem Series.poly_mul_geom_converges {x:ℝ} (hx: |x|<1) (q:ℝ) : (fun n:ℕ ↦ (n:ℝ)^q * x^n : Series).converges
  ∧ atTop.Tendsto (fun n:ℕ ↦ (n:ℝ)^q * x^n) (nhds 0) := by
  set s := (fun n:ℕ ↦ (n:ℝ)^q * x^n : Series)
  have hseq_simp (n : ℤ) (hn : n ≥ 1) : |s.seq n|^(1/(n:ℝ)) = |x| * ((n : ℝ) ^ (q / (n : ℝ))) := by
    have hn0 : (0 : ℤ) ≤ n := by omega
    have hnpos : (n : ℝ) > 0 := by exact_mod_cast (show (1 : ℤ) ≤ n from hn)
    have hseq_val : s.seq n = ((n : ℝ) ^ q) * (x ^ (n.toNat : ℕ)) := by
      simp [s, hn0]
    calc
      |s.seq n|^(1/(n:ℝ)) = |((n : ℝ) ^ q) * (x ^ (n.toNat : ℕ))|^(1/(n:ℝ)) := by rw [hseq_val]
      _ = (|(n : ℝ) ^ q| * |x ^ (n.toNat : ℕ)|)^(1/(n:ℝ)) := by rw [abs_mul]
      _ = ((n : ℝ) ^ q * |x| ^ (n.toNat : ℕ))^(1/(n:ℝ)) := by
        rw [abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) ^ q), abs_pow]
      _ = ((n : ℝ) ^ q)^(1/(n:ℝ)) * (|x| ^ (n.toNat : ℕ))^(1/(n:ℝ)) := by
        rw [mul_rpow (by positivity : 0 ≤ (n : ℝ) ^ q) (by positivity : 0 ≤ |x| ^ (n.toNat : ℕ))]
      _ = ((n : ℝ) ^ q)^(1/(n:ℝ)) * (|x| ^ (n : ℝ))^(1/(n:ℝ)) := by
        simp [show (n.toNat : ℝ) = (n : ℝ) by simp]
      _ = ((n : ℝ) ^ (q / (n : ℝ))) * (|x| ^ ((n : ℝ) * (1 / (n : ℝ)))) := by
        rw [rpow_mul (by positivity : 0 ≤ (n : ℝ)) q (1 / (n : ℝ)),
          rpow_mul (abs_nonneg x) (n : ℝ) (1 / (n : ℝ))]
      _ = ((n : ℝ) ^ (q / (n : ℝ))) * (|x| ^ (1 : ℝ)) := by
        field_simp [hnpos.ne']
      _ = ((n : ℝ) ^ (q / (n : ℝ))) * |x| := by simp
      _ = |x| * ((n : ℝ) ^ (q / (n : ℝ))) := by ring
  have h_eventually_simp : ∀ᶠ (n : ℤ) in atTop, |s.seq n|^(1/(n:ℝ)) = |x| * ((n : ℝ) ^ (q / (n : ℝ))) := by
    refine eventually_atTop.mpr ⟨1, fun n hn => hseq_simp n hn⟩
  have h_tendsto_rpow : atTop.Tendsto (fun (n : ℤ) ↦ ((n : ℝ) ^ (q / (n : ℝ)))) (nhds (1 : ℝ)) :=
    (tendsto_rpow_div q).comp (tendsto_intCast_atTop_atTop (R := ℝ))
  have h_tendsto_term : atTop.Tendsto (fun (n : ℤ) ↦ |x| * ((n : ℝ) ^ (q / (n : ℝ)))) (nhds (|x| * 1)) := by
    simpa [mul_comm] using h_tendsto_rpow.mul (tendsto_const_nhds (x := |x|))
  have h_tendsto_sq_real : atTop.Tendsto (fun (n : ℤ) ↦ |s.seq n|^(1/(n:ℝ))) (nhds |x|) := by
    refine (tendsto_congr' h_eventually_simp).mpr ?_
    simpa [mul_one] using h_tendsto_term
  have h_tendsto_ereal : atTop.Tendsto (fun (n : ℤ) ↦ ((|s.seq n|^(1/(n:ℝ)) : ℝ) : EReal)) (nhds ((|x| : ℝ) : EReal)) :=
    continuous_coe_real_ereal.continuousAt.tendsto.comp h_tendsto_sq_real
  have h_limsup_eq : atTop.limsup (fun (n : ℤ) ↦ ((|s.seq n|^(1/(n:ℝ)) : ℝ) : EReal)) = (|x| : EReal) :=
    h_tendsto_ereal.limsup_eq
  have h_limsup_lt_one : atTop.limsup (fun (n : ℤ) ↦ ((|s.seq n|^(1/(n:ℝ)) : ℝ) : EReal)) < (1 : EReal) := by
    rw [h_limsup_eq]
    exact EReal.coe_lt_coe_iff.mpr hx
  have h_abs_conv : s.absConverges := root_test_pos h_limsup_lt_one
  have h_conv : s.converges := converges_of_absConverges h_abs_conv
  have h_decay : atTop.Tendsto s.seq (nhds 0) := decay_of_converges h_conv
  have h_tendsto_nat : atTop.Tendsto (fun n : ℕ ↦ (n:ℝ)^q * x^n) (nhds 0) := by
    have : (fun (n : ℕ) => s.seq (n : ℤ)) = (fun n : ℕ ↦ (n:ℝ)^q * x^n) := by
      ext n; simp [s, Series.eval_coe]
    rw [this]
    exact h_decay.comp (tendsto_natCast_atTop_atTop (R := ℤ))
  exact ⟨h_conv, h_tendsto_nat⟩

end Chapter7
