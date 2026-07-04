import Mathlib.Tactic
import Analysis.Section_9_9
import Analysis.Section_11_4

/-!
# Analysis I, Section 11.5: Riemann integrability of continuous functions

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Riemann integrability of uniformly continuous functions.
- Riemann integrability of bounded continuous functions.

-/

namespace Chapter11
open BoundedInterval
open Chapter9

/-- Theorem 11.5.1 -/
theorem integ_of_uniform_cts {I: BoundedInterval} {f:ℝ → ℝ} (hf: UniformContinuousOn f I) :
  IntegrableOn f I := by
  -- This proof is written to follow the structure of the original text.
  have hfbound : BddOn f I := by
    rw [BddOn.iff']; exact hf.of_bounded subset_rfl (Bornology.IsBounded.of_boundedInterval I)
  refine ⟨ hfbound, ?_ ⟩
  by_cases hsing : |I|ₗ = 0
  . exact (integ_on_subsingleton hsing).1.2
  simp [length] at hsing
  set a := I.a
  set b := I.b
  have hsing' : 0 < b-a := by linarith
  have (ε:ℝ) (hε: ε > 0) : upper_integral f I - lower_integral f I ≤ ε * (b-a) := by
    rw [UniformContinuousOn.iff] at hf
    choose δ hδ hf using hf ε hε; simp [Real.Close, Real.dist_eq] at hf
    choose N hN using exists_nat_gt ((b-a)/δ)
    have hNpos : 0 < N := by
      have : 0 < (b-a)/δ := by positivity
      rify; order
    have hN' : (b-a)/N < δ := by rwa [div_lt_comm₀] <;> positivity
    have : ∃ P: Partition I, P.intervals.card = N ∧ ∀ J ∈ P.intervals, |J|ₗ = (b-a) / N := by
      have hI_len_pos : 0 < |I|ₗ := by
        have hsub_nonneg : 0 ≤ I.b - I.a := by linarith
        have : |I|ₗ = I.b - I.a := by
          rw [length, max_eq_left hsub_nonneg]
        rw [this]
        linarith
      have h_lemma : ∀ (I' : BoundedInterval) (n : ℕ), 0 < n → (0 < |I'|ₗ) →
        ∃ P : Partition I', P.intervals.card = n ∧ ∀ J ∈ P.intervals, |J|ₗ = (|I'|ₗ)/n := by
        intro I' n hnpos hlenpos
        induction' n with k ih generalizing I'
        · exact absurd hnpos (lt_irrefl _)
        · by_cases hk0 : k = 0
          · subst hk0
            refine ⟨⊥, by simp, ?_⟩
            intro J hJ; simp at hJ; subst hJ
            simp [length]
          · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
            have ha_lt_b : I'.a < I'.b := by
              by_contra! hle
              have : |I'|ₗ = 0 := by
                simp [length, hle]
              linarith
            set Δ := (|I'|ₗ)/((k+1 : ℕ) : ℝ) with hΔ
            have hΔpos : 0 < Δ := by positivity
            have hlen_eq : |I'|ₗ = I'.b - I'.a := by
              simp [length, ha_lt_b.le]
            have ha_aΔ_lt : I'.a < I'.a + Δ := by nlinarith
            have ha_aΔ_le : I'.a ≤ I'.a + Δ := by nlinarith
            have haΔ_b : I'.a + Δ ≤ I'.b := by
              have hΔ_le : Δ ≤ |I'|ₗ := by
                rw [hΔ]
                refine div_le_self (by positivity) ?_
                exact_mod_cast (show 1 ≤ (k+1 : ℕ) from by omega)
              nlinarith
            have haΔ_lt_b : I'.a + Δ < I'.b := by
              have hΔ_lt : Δ < |I'|ₗ := by
                rw [hΔ]
                have hkp1_gt_1 : (1 : ℝ) < ((k+1 : ℕ) : ℝ) := by
                  exact_mod_cast (show 1 < k+1 from by omega)
                have hkp1_pos : 0 < ((k+1 : ℕ) : ℝ) := by positivity
                have h_one_div_lt_one : (1 : ℝ) / ((k+1 : ℕ) : ℝ) < 1 :=
                  (div_lt_one hkp1_pos).mpr hkp1_gt_1
                calc
                  |I'|ₗ / ((k+1 : ℕ) : ℝ) = |I'|ₗ * ((1 : ℝ) / ((k+1 : ℕ) : ℝ)) := by ring
                  _ < |I'|ₗ * 1 := by nlinarith
                  _ = |I'|ₗ := by simp
              nlinarith
            let I_left : BoundedInterval := match I' with
              | Icc _ _ => Ico I'.a (I'.a+Δ)
              | Ico _ _ => Ico I'.a (I'.a+Δ)
              | Ioc _ _ => Ioc I'.a (I'.a+Δ)
              | Ioo _ _ => Ioo I'.a (I'.a+Δ)
            let I_right : BoundedInterval := match I' with
              | Icc _ _ => Icc (I'.a+Δ) I'.b
              | Ico _ _ => Ico (I'.a+Δ) I'.b
              | Ioc _ _ => Ioc (I'.a+Δ) I'.b
              | Ioo _ _ => Ico (I'.a+Δ) I'.b
            have hI_left_len : |I_left|ₗ = Δ := by
              dsimp [I_left]
              cases I' <;> simp [length, hΔpos.le]
            have hI_right_a : I_right.a = I'.a + Δ := by
              dsimp [I_right]; cases I' <;> rfl
            have hI_right_b : I_right.b = I'.b := by
              dsimp [I_right]; cases I' <;> rfl
            have hI_right_len : |I_right|ₗ = k * Δ := by
              rw [length, hI_right_a, hI_right_b]
              have hsub : I'.b - (I'.a + Δ) = k * Δ := by
                calc
                  I'.b - (I'.a + Δ) = (I'.b - I'.a) - Δ := by ring
                  _ = |I'|ₗ - Δ := by rw [hlen_eq]
                  _ = |I'|ₗ - (|I'|ₗ / ((k+1 : ℕ) : ℝ)) := by rw [hΔ]
                  _ = (|I'|ₗ * (((k+1 : ℕ) : ℝ) - 1)) / ((k+1 : ℕ) : ℝ) := by
                    field_simp
                  _ = (|I'|ₗ * (k : ℝ)) / ((k+1 : ℕ) : ℝ) := by push_cast; ring
                  _ = (|I'|ₗ / ((k+1 : ℕ) : ℝ)) * (k : ℝ) := by ring
                  _ = Δ * (k : ℝ) := by rw [hΔ]
                  _ = k * Δ := mul_comm _ _
              rw [hsub]
              have hpos : 0 < k * Δ := by positivity
              simp [hpos.le]
            have hI_right_len_pos : 0 < |I_right|ₗ := by
              rw [hI_right_len]; positivity
            have hjoin : I'.joins I_left I_right := by
              dsimp [I_left, I_right]
              cases I' with
              | Icc a b => exact BoundedInterval.join_Ico_Icc ha_aΔ_le haΔ_b
              | Ico a b => exact BoundedInterval.join_Ico_Ico ha_aΔ_le haΔ_b
              | Ioc a b => exact BoundedInterval.join_Ioc_Ioc ha_aΔ_le haΔ_b
              | Ioo a b => exact BoundedInterval.join_Ioo_Ico ha_aΔ_lt haΔ_b
            have h_inter_empty : (I_left : Set ℝ) ∩ (I_right : Set ℝ) = ∅ := hjoin.1
            let P_left : Partition I_left := ⊥
            have hcard_left : P_left.intervals.card = 1 := by
              simp [P_left]
            have hlen_left_all : ∀ J ∈ P_left.intervals, |J|ₗ = (|I'|ₗ)/((k+1 : ℕ) : ℝ) := by
              intro J hJ
              have hJ_eq : J = I_left := by
                have : P_left.intervals = {I_left} := by simp [P_left]
                simpa [this] using hJ
              subst hJ_eq; rw [← hΔ]; exact hI_left_len
            have h_right_spec : ∃ P : Partition I_right, P.intervals.card = k ∧ ∀ J ∈ P.intervals, |J|ₗ = (|I_right|ₗ)/k :=
              ih I_right hkpos hI_right_len_pos
            rcases h_right_spec with ⟨P_right, hcard_right, hlen_right⟩
            have hlen_right_all : ∀ J ∈ P_right.intervals, |J|ₗ = (|I'|ₗ)/((k+1 : ℕ) : ℝ) := by
              intro J hJ
              rw [hlen_right J hJ, hI_right_len]
              calc
                (k * Δ) / (k : ℝ) = Δ := by
                  field_simp [show (k : ℝ) ≠ 0 from by exact_mod_cast hkpos.ne.symm]
                _ = (|I'|ₗ)/((k+1 : ℕ) : ℝ) := by rw [hΔ]
            have h_not_mem : I_left ∉ P_right.intervals := by
              intro hmem
              have hsub : I_left ⊆ I_right := P_right.contains I_left hmem
              have h_empty : (I_left : Set ℝ) = ∅ := by
                have hsub' : (I_left : Set ℝ) ⊆ (I_right : Set ℝ) := hsub
                have h_eq : (I_left : Set ℝ) = (I_left : Set ℝ) ∩ (I_right : Set ℝ) :=
                  (Set.inter_eq_left.mpr hsub').symm
                calc
                  (I_left : Set ℝ) = (I_left : Set ℝ) ∩ (I_right : Set ℝ) := h_eq
                  _ = ∅ := h_inter_empty
              have hlen0 : |I_left|ₗ = 0 := BoundedInterval.length_of_empty h_empty
              rw [hI_left_len] at hlen0
              linarith
            have hcard_total : (P_left.join P_right hjoin).intervals.card = k+1 := by
              rw [Partition.intervals_of_join]
              have hcard_union : (P_left.intervals ∪ P_right.intervals).card = 1 + k := by
                have hcard_singleton : P_left.intervals = {I_left} := by simp [P_left]
                rw [hcard_singleton]
                by_cases hmem : I_left ∈ P_right.intervals
                · exact absurd hmem h_not_mem
                · simp [hcard_right, hmem, add_comm]
              simpa [add_comm] using hcard_union
            refine ⟨P_left.join P_right hjoin, hcard_total, ?_⟩
            intro J hJ
            rw [Partition.intervals_of_join] at hJ
            rcases Finset.mem_union.mp hJ with (hJ_left | hJ_right)
            · exact hlen_left_all J hJ_left
            · exact hlen_right_all J hJ_right
      rcases h_lemma I N hNpos hI_len_pos with ⟨P, hcard, hlen⟩
      have hI_len_eq : |I|ₗ = b-a := by
        have : 0 ≤ b-a := by linarith
        rw [length, max_eq_left this]
      refine ⟨P, hcard, ?_⟩
      intro J hJ
      rw [hlen J hJ, hI_len_eq]
    choose P hcard hlength using this
    calc
      _ ≤ ∑ J ∈ P.intervals, (sSup (f '' J) - sInf (f '' J)) * |J|ₗ := by
        have h1 := upper_integ_le_upper_sum hfbound P
        have h2 := lower_integ_ge_lower_sum hfbound P
        simp [sub_mul, upper_riemann_sum, lower_riemann_sum] at *
        linarith
      _ ≤ ∑ J ∈ P.intervals, ε * |J|ₗ := by
        apply Finset.sum_le_sum; intro J hJ; gcongr
        have {x y:ℝ} (hx: x ∈ J) (hy: y ∈ J) : f x ≤ f y + ε := by
          have : J ⊆ I := P.contains _ hJ
          have : |f x - f y| ≤ ε := by
            apply hf y _ x _ _ <;> try solve_by_elim
            apply (BoundedInterval.dist_le_length hx hy).trans; grind
          grind [abs_le']
        have hJnon : (f '' J).Nonempty := by
          simp; by_contra! h
          replace h : Subsingleton (J:Set ℝ) := by simp [h]
          simp only [length_of_subsingleton, hlength J hJ] at h
          linarith [show 0 < (b-a) / N by positivity]
        replace (y:ℝ) (hy:y ∈ J) : sSup (f '' J) ≤ f y + ε := by
          apply csSup_le hJnon; rintro _ ⟨z, hz, rfl⟩; exact this hz hy
        replace : sSup (f '' J) - ε ≤ sInf (f '' J) := by
          apply le_csInf hJnon; grind [mem_iff]
        linarith
      _ = ∑ J ∈ P.intervals, ε * (b-a)/N := by grind [Finset.sum_congr]
      _ = _ := by simp [hcard]; field_simp
  have lower_le_upper : 0 ≤ upper_integral f I - lower_integral f I := by linarith [lower_integral_le_upper hfbound]
  obtain h | h := le_iff_lt_or_eq.mp lower_le_upper
  . set ε := (upper_integral f I - lower_integral f I)/(2*(b-a))
    replace : upper_integral f I - lower_integral f I ≤ (upper_integral f I - lower_integral f I)/2 := by
      convert this ε (by positivity) using 1; grind
    linarith
  linarith

/-- Corollary 11.5.2 -/
theorem integ_of_cts {a b:ℝ} {f:ℝ → ℝ} (hf: ContinuousOn f (Icc a b)) :
  IntegrableOn f (Icc a b) := integ_of_uniform_cts (UniformContinuousOn.of_continuousOn hf)

example : ¬ ContinuousOn (fun x:ℝ ↦ 1/x) (Icc 0 1) := by
  intro h
  have h0 : ContinuousWithinAt (fun x : ℝ => 1/x) ((Icc 0 1 : Set ℝ)) 0 :=
    h 0 (by rw [BoundedInterval.set_Icc]; exact Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  have htendsto : Filter.Tendsto (fun x : ℝ => 1/x) (nhdsWithin 0 (Icc 0 1 : Set ℝ)) (nhds 0) := by
    simpa [div_zero] using h0.tendsto
  rcases (Metric.tendsto_nhdsWithin_nhds.mp htendsto) 1 (by norm_num) with ⟨δ, hδpos, hδ⟩
  set x := min (δ / 2) (1/2) with hx_def
  have hx_nonneg : 0 ≤ x := by
    unfold x; refine le_min (by nlinarith) (by norm_num)
  have hx_le_one : x ≤ 1 := by
    unfold x; exact (min_le_right _ _).trans (by norm_num)
  have hx_mem : x ∈ (Icc 0 1 : Set ℝ) :=
    Set.mem_Icc.mpr ⟨hx_nonneg, hx_le_one⟩
  have hx_pos : 0 < x := by
    unfold x; refine lt_min_iff.mpr ⟨by nlinarith, by norm_num⟩
  have hx_dist : dist x 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hx_pos]
    have hx_lt : x < δ := by
      unfold x; refine lt_of_lt_of_le (min_lt_iff.mpr (Or.inl ?_)) (le_refl _)
      nlinarith
    exact hx_lt
  have h_bound : dist (1 / x) 0 < 1 := hδ hx_mem hx_dist
  rw [Real.dist_eq, sub_zero] at h_bound
  have hx_lt_one : x < 1 := by
    unfold x; exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have h_one_div_gt_one : 1 < 1 / x :=
    one_lt_one_div hx_pos hx_lt_one
  have h_abs : |1 / x| = 1 / x := abs_of_pos (by positivity)
  have : |1 / x| > 1 := by
    calc
      |1 / x| = 1 / x := h_abs
      _ > 1 := h_one_div_gt_one
  nlinarith

example : ¬ IntegrableOn (fun x:ℝ ↦ 1/x) (Icc 0 1) := by
  intro h
  rcases h with ⟨hBdd, hInt⟩
  rcases hBdd with ⟨M, hM⟩
  by_cases hMneg : M < 0
  · have h1mem : (1 : ℝ) ∈ (Icc 0 1 : Set ℝ) := by
      rw [BoundedInterval.set_Icc]; exact Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
    have hM1 : |(1 / (1 : ℝ))| ≤ M := hM (1 : ℝ) h1mem
    have : |(1 : ℝ)| = 1 := abs_one
    nlinarith
  · have hM_nonneg : 0 ≤ M := by linarith
    set x := 1 / (M + 1) with hx_def
    have hx_nonneg : 0 ≤ x := by positivity
    have hx_le_one : x ≤ 1 := by
      dsimp [x]
      have htemp : 1 / (M + 1) ≤ 1 / (1 : ℝ) :=
        (one_div_le_one_div (by positivity : 0 < M + 1) (by norm_num : (0 : ℝ) < 1)).mpr (by nlinarith)
      simpa using htemp
    have hx_mem : x ∈ (Icc 0 1 : Set ℝ) := by
      rw [BoundedInterval.set_Icc]; exact Set.mem_Icc.mpr ⟨hx_nonneg, hx_le_one⟩
    have hx_pos : 0 < x := by positivity
    have hval : |(1 / x)| = M + 1 := by
      calc
        |(1 / x)| = |(M + 1)| := by
          dsimp [x]; field_simp
        _ = M + 1 := abs_of_pos (by nlinarith)
    have hval_bound : |(1 / x)| ≤ M := hM x hx_mem
    nlinarith

open PiecewiseConstantOn ConstantOn in
set_option maxHeartbeats 300000 in
/-- Proposition 11.5.3 -/
theorem integ_of_bdd_cts {I: BoundedInterval} {f:ℝ → ℝ} (hbound: BddOn f I)
  (hf: ContinuousOn f I) : IntegrableOn f I := by
  -- This proof is written to follow the structure of the original text.
  by_cases hsing : |I|ₗ = 0
  . exact (integ_on_subsingleton hsing).1
  have hI : (I:Set ℝ).Nonempty := by by_contra!; rw [←BoundedInterval.length_of_subsingleton] at hsing; simp_all
  simp at hsing
  set a := I.a
  set b := I.b
  have lower_le_upper := lower_integral_le_upper hbound
  have ⟨ M, hM ⟩ := hbound
  have hMpos : 0 ≤ M := (abs_nonneg _).trans (hM hI.some hI.some_mem)
  have (ε:ℝ) (hε: ε > 0) : upper_integral f I - lower_integral f I ≤ (4*M+2) * ε := by
    wlog hε' : ε < (b-a)/2
    . specialize this _ _ _ _ _ _ hM _ ((b-a)/3) _ _
        <;> first | assumption | linarith | apply this.trans; gcongr; linarith
    set I' := Icc (a+ε) (b-ε)
    set Ileft : BoundedInterval := match I with
    | Icc _ _ => Ico a (a + ε)
    | Ico _ _ => Ico a (a + ε)
    | Ioc _ _ => Ioo a (a + ε)
    | Ioo _ _ => Ioo a (a + ε)
    set Iright : BoundedInterval := match I with
    | Icc _ _ => Ioc (b - ε) b
    | Ico _ _ => Ioo (b - ε) b
    | Ioc _ _ => Ioc (b - ε) b
    | Ioo _ _ => Ioo (b - ε) b
    set Ileft' : BoundedInterval := match I with
    | Icc _ _ => Icc a (b - ε)
    | Ico _ _ => Icc a (b - ε)
    | Ioc _ _ => Ioc a (b - ε)
    | Ioo _ _ => Ioc a (b - ε)
    have Ileftlen : |Ileft|ₗ = ε := by cases I <;> simp [Ileft, length, le_of_lt hε]
    have Irightlen : |Iright|ₗ = ε := by cases I <;> simp [Iright, length, le_of_lt hε]
    have hjoin1 : Ileft'.joins Ileft I' := by
      cases I
      case Icc _ _ => apply join_Ico_Icc <;> linarith
      case Ico _ _ => apply join_Ico_Icc <;> linarith
      case Ioc _ _ => apply join_Ioo_Icc <;> linarith
      case Ioo _ _ => apply join_Ioo_Icc <;> linarith
    have hjoin2: I.joins Ileft' Iright := by
      cases I
      case Icc _ _ => apply join_Icc_Ioc <;> linarith
      case Ico _ _ => apply join_Icc_Ioo <;> linarith
      case Ioc _ _ => apply join_Ioc_Ioc <;> linarith
      case Ioo _ _ => apply join_Ioc_Ioo <;> linarith
    have hf' : IntegrableOn f I' := by
      apply integ_of_cts $ ContinuousOn.mono hf $ subset_trans _ $ (subset_iff _ _).mp $ Ioo_subset I
      intro _; simp; grind
    choose h hhmin hhconst hhint using lt_of_gt_upper_integral hf'.1 (show upper_integral f I' < integ f I' + ε by linarith [hf'.2])
    classical
    set h' : ℝ → ℝ := fun x ↦ if x ∈ I' then h x else M
    have h'const_left (x:ℝ) (hx: x ∈ Ileft) : h' x = M := by
      replace hjoin1 := Set.eq_empty_iff_forall_notMem.mp hjoin1.1 x
      simp_all [h',mem_iff]
    have h'const_right (x:ℝ) (hx: x ∈ Iright) : h' x = M := by
      replace hjoin2 := Set.eq_empty_iff_forall_notMem.mp hjoin2.1 x
      replace hjoin1 := congrArg (x ∈ ·) hjoin1.2.1
      simp_all [h',mem_iff]
    have h'const : PiecewiseConstantOn h' I := by
      rw [of_join hjoin2, of_join hjoin1]; split_ands
      . apply_rules [piecewiseConstantOn, of_const]
      . apply hhconst.congr'; grind [mem_iff]
      apply_rules [piecewiseConstantOn, of_const]
    have h'maj : MajorizesOn h' f I := by
      intro x _; by_cases hxI': x ∈ I' <;> simp [h', hxI']; solve_by_elim; grind [abs_le']
    observe h'maj : upper_integral f I ≤ h'const.integ'
    have h'integ1 := h'const.integ_of_join hjoin2
    have h'integ2 := ((of_join hjoin2 _).mp h'const).1.integ_of_join hjoin1
    have h'integ3 : PiecewiseConstantOn.integ h' Ileft = M * ε := by
      rw [PiecewiseConstantOn.integ_congr h'const_left, integ_const, Ileftlen]
    have h'integ4 : PiecewiseConstantOn.integ h' Iright = M * ε := by
      rw [PiecewiseConstantOn.integ_congr h'const_right, integ_const, Irightlen]
    have h'integ5 : PiecewiseConstantOn.integ h' I' = PiecewiseConstantOn.integ h I' := by
      apply PiecewiseConstantOn.integ_congr; grind [mem_iff]
    choose g hgmin hgconst hgint using gt_of_lt_lower_integral hf'.1 (show integ f I' - ε < lower_integral f I' by linarith [hf'.2])
    set g' : ℝ → ℝ := fun x ↦ if x ∈ I' then g x else -M
    have g'const_left (x:ℝ) (hx: x ∈ Ileft) : g' x = -M := by
      replace hjoin1 := Set.eq_empty_iff_forall_notMem.mp hjoin1.1 x
      simp_all [g', mem_iff]
    have g'const_right (x:ℝ) (hx: x ∈ Iright) : g' x = -M := by
      replace hjoin2 := Set.eq_empty_iff_forall_notMem.mp hjoin2.1 x
      replace hjoin1 := congrArg (x ∈ ·) hjoin1.2.1
      simp_all [g', mem_iff]
    have g'const : PiecewiseConstantOn g' I := by
      rw [of_join hjoin2, of_join hjoin1]; split_ands
      . apply_rules [piecewiseConstantOn, of_const]
      . apply hgconst.congr'; grind [mem_iff]
      apply_rules [piecewiseConstantOn, of_const]
    have g'maj : MinorizesOn g' f I := by
      intro x _; by_cases hxI': x ∈ I' <;> simp [g', hxI']; solve_by_elim; grind [abs_le']
    observe g'maj : g'const.integ' ≤ lower_integral f I
    have g'integ1 := g'const.integ_of_join hjoin2
    have g'integ2 := ((of_join hjoin2 _).mp g'const).1.integ_of_join hjoin1
    have g'integ3 : PiecewiseConstantOn.integ g' Ileft = -M * ε := by
      rw [PiecewiseConstantOn.integ_congr g'const_left, integ_const, Ileftlen]
    have g'integ4 : PiecewiseConstantOn.integ g' Iright = -M * ε := by
      rw [PiecewiseConstantOn.integ_congr g'const_right, integ_const, Irightlen]
    have g'integ5 : PiecewiseConstantOn.integ g' I' = PiecewiseConstantOn.integ g I' := by
      apply PiecewiseConstantOn.integ_congr; grind [mem_iff]
    grind
  exact ⟨ hbound, by linarith [nonneg_of_le_const_mul_eps this] ⟩

/-- Definition 11.5.4 -/
abbrev PiecewiseContinuousOn (f:ℝ → ℝ) (I:BoundedInterval) : Prop :=
  ∃ P: Partition I, ∀ J ∈ P.intervals, ContinuousOn f J

/-- Example 11.5.5 -/
noncomputable abbrev f_11_5_5 : ℝ → ℝ := fun x ↦
  if x < 2 then x^2
  else if x = 2 then 7
  else x^3

example : ¬ ContinuousOn f_11_5_5 (Icc 1 3) := by
  intro h
  have h2 : ContinuousWithinAt f_11_5_5 (Icc 1 3 : Set ℝ) 2 :=
    h 2 (by norm_num : (2 : ℝ) ∈ (Icc 1 3 : Set ℝ))
  rcases Metric.tendsto_nhdsWithin_nhds.mp h2.tendsto 1 (by norm_num : (0 : ℝ) < 1) with ⟨δ, hδpos, hδ⟩
  have hval : f_11_5_5 2 = 7 := by
    simp [f_11_5_5]
  set δ' := min δ 1 with hδ'def
  have hδ'pos : 0 < δ' := lt_min_iff.mpr ⟨hδpos, by norm_num⟩
  have hδ'_le_δ : δ' ≤ δ := min_le_left _ _
  set x := 2 - δ' / 3 with hxdef
  have hx_lt2 : x < 2 := by nlinarith
  have hx_ge_1 : 1 ≤ x := by
    have : δ' ≤ 1 := min_le_right _ _
    nlinarith
  have hx_mem : x ∈ (Icc 1 3 : Set ℝ) :=
    Set.mem_Icc.mpr ⟨hx_ge_1, by nlinarith⟩
  have hx_dist : dist x 2 < δ := by
    rw [Real.dist_eq, hxdef]
    have : |(2 - δ' / 3) - 2| = δ' / 3 := by
      have hsub : (2 - δ' / 3) - 2 = -(δ' / 3) := by ring
      rw [hsub, abs_neg, abs_of_pos (by nlinarith : 0 < δ' / 3)]
    rw [this]
    nlinarith
  have hbound : dist (f_11_5_5 x) (f_11_5_5 2) < 1 := hδ hx_mem hx_dist
  have hfx : f_11_5_5 x = x ^ 2 := by
    simp [f_11_5_5, hx_lt2]
  rw [hfx, hval, Real.dist_eq] at hbound
  have hx_sq_lt_4 : x ^ 2 < 4 := by
    nlinarith
  have hpos : 7 - x ^ 2 > 1 := by
    nlinarith
  have habs : |x ^ 2 - 7| = 7 - x ^ 2 := by
    have hneg : x ^ 2 - 7 < 0 := by nlinarith
    rw [abs_of_neg hneg]
    ring
  rw [habs] at hbound
  nlinarith

example : ContinuousOn f_11_5_5 (Ico 1 2) := by
  have h_sq_cts : ContinuousOn (fun x : ℝ => x ^ 2) (Ico 1 2) :=
    (continuousOn_id.pow 2).mono (Set.subset_univ _)
  have h_eq : Set.EqOn f_11_5_5 (fun x : ℝ => x ^ 2) (Ico 1 2) := by
    intro x hx
    simp [f_11_5_5, hx.2]
  exact h_sq_cts.congr h_eq

example : ContinuousOn f_11_5_5 (Icc 2 2) := by
  simp [Set.Icc_self]

example : ContinuousOn f_11_5_5 (Ioc 2 3) := by
  have h_cube_cts : ContinuousOn (fun x : ℝ => x ^ 3) (Ioc 2 3) :=
    (continuousOn_id.pow 3).mono (Set.subset_univ _)
  have h_eq : Set.EqOn f_11_5_5 (fun x : ℝ => x ^ 3) (Ioc 2 3) := by
    intro x hx
    have hx_gt2 : 2 < x := hx.1
    simp [f_11_5_5, show ¬ x < 2 from by linarith, show x ≠ 2 from by linarith]
  exact h_cube_cts.congr h_eq

example : PiecewiseContinuousOn f_11_5_5 (Icc 1 3) := by
  set P1 : Partition (Ico 1 2) := ⊥ with hP1
  set P2 : Partition (Icc 2 2) := ⊥ with hP2
  have hjoin1 : (Icc 1 2).joins (Ico 1 2) (Icc 2 2) := by
    apply join_Ico_Icc <;> norm_num
  set P12 : Partition (Icc 1 2) := P1.join P2 hjoin1 with hP12
  set P3 : Partition (Ioc 2 3) := ⊥ with hP3
  have hjoin2 : (Icc 1 3).joins (Icc 1 2) (Ioc 2 3) := by
    apply join_Icc_Ioc <;> norm_num
  set P : Partition (Icc 1 3) := P12.join P3 hjoin2 with hP
  have h_intervals : P.intervals = {Ico 1 2, Icc 2 2, Ioc 2 3} := by
    calc
      P.intervals = (P12.join P3 hjoin2).intervals := rfl
      _ = P12.intervals ∪ P3.intervals := by simp
      _ = ((P1.join P2 hjoin1).intervals) ∪ (⊥ : Partition (Ioc 2 3)).intervals := rfl
      _ = (P1.intervals ∪ P2.intervals) ∪ (⊥ : Partition (Ioc 2 3)).intervals := by simp
      _ = ({Ico 1 2} ∪ {Icc 2 2}) ∪ {Ioc 2 3} := by simp [hP1, hP2]
      _ = {Ico 1 2, Icc 2 2, Ioc 2 3} := by simp
  refine ⟨P, ?_⟩
  intro J hJ
  have hJ_mem : J ∈ ({Ico 1 2, Icc 2 2, Ioc 2 3} : Finset BoundedInterval) := by
    simpa [h_intervals] using hJ
  rcases Finset.mem_insert.mp hJ_mem with (hJ_eq | hJ_rest)
  · -- J = Ico 1 2
    rw [hJ_eq]
    have h_sq_cts : ContinuousOn (fun x : ℝ => x ^ 2) (Ico 1 2) :=
      (continuousOn_id.pow 2).mono (Set.subset_univ _)
    have h_eq : Set.EqOn f_11_5_5 (fun x : ℝ => x ^ 2) (Ico 1 2) := by
      intro x hx; simp [f_11_5_5, hx.2]
    exact h_sq_cts.congr h_eq
  · rcases Finset.mem_insert.mp hJ_rest with (hJ_eq | hJ_rest)
    · -- J = Icc 2 2
      rw [hJ_eq]
      simp [Set.Icc_self]
    · -- J = Ioc 2 3
      rw [Finset.mem_singleton.mp hJ_rest]
      have h_cube_cts : ContinuousOn (fun x : ℝ => x ^ 3) (Ioc 2 3) :=
        (continuousOn_id.pow 3).mono (Set.subset_univ _)
      have h_eq : Set.EqOn f_11_5_5 (fun x : ℝ => x ^ 3) (Ioc 2 3) := by
        intro x hx
        have hx_gt2 : 2 < x := hx.1
        simp [f_11_5_5, show ¬ x < 2 from by linarith, show x ≠ 2 from by linarith]
      exact h_cube_cts.congr h_eq

/-- Proposition 11.5.6 / Exercise 11.5.1 -/
theorem integ_of_bdd_piecewise_cts {I: BoundedInterval} {f:ℝ → ℝ}
  (hbound: BddOn f I) (hf: PiecewiseContinuousOn f I) : IntegrableOn f I := by
  rcases hf with ⟨P, hf⟩
  have h_int_on : ∀ J ∈ P.intervals, IntegrableOn f J := by
    intro J hJ
    have hBddJ : BddOn f J := by
      rcases hbound with ⟨M, hM⟩
      refine ⟨M, λ x hx => hM x ((P.contains J hJ) x hx)⟩
    have h_cts : ContinuousOn f J := hf J hJ
    exact integ_of_bdd_cts hBddJ h_cts
  have hlemma : ∀ (n : ℕ) (I : BoundedInterval), BddOn f I → (P : Partition I) →
    (∀ J ∈ P.intervals, IntegrableOn f J) → P.intervals.card = n → IntegrableOn f I := by
    intro n
    induction' n with n hn
    · intro I hbound P h_int_on hcard
      have hcard0 : P.intervals = ∅ := by
        simpa [Finset.card_eq_zero] using hcard
      have hIempty : (I : Set ℝ) = ∅ := by
        by_contra! hne
        rcases hne with ⟨x, hx⟩
        rcases P.exists_unique x hx with ⟨J, ⟨hJmem, _⟩, _⟩
        rw [hcard0] at hJmem; simp at hJmem
      have hlen0 : |I|ₗ = 0 := BoundedInterval.length_of_empty hIempty
      exact (integ_on_subsingleton hlen0).1
    · intro I hbound P h_int_on hcard
      by_cases hsing : Subsingleton (I : Set ℝ)
      · have hlen0 : |I|ₗ = 0 := BoundedInterval.length_of_subsingleton.mp hsing
        exact (integ_on_subsingleton hlen0).1
      · rcases partition_join_erase P hsing with ⟨K, L, hK, hjoin, P', hP'⟩
        have hcard' : P'.intervals.card = n := by
          rw [hP', Finset.card_erase_of_mem hK, hcard]
          omega
        have h_int_on_L : ∀ J ∈ P'.intervals, IntegrableOn f J := by
          intro J hJ
          apply h_int_on J
          rw [hP'] at hJ
          exact (Finset.mem_erase.mp hJ).2
        have hBddL : BddOn f L := by
          rcases hbound with ⟨M, hM⟩
          refine ⟨M, λ x hx => ?_⟩
          have hxI : x ∈ (I : Set ℝ) := by
            rw [hjoin.2.1]
            exact Or.inl hx
          exact hM x hxI
        have hintL : IntegrableOn f L := hn L hBddL P' h_int_on_L hcard'
        have h_int_on_K : IntegrableOn f K := h_int_on K hK
        rcases IntegrableOn.of_join hjoin hintL h_int_on_K with ⟨hintI, _⟩
        exact hintI
  exact hlemma (P.intervals.card) I hbound P h_int_on rfl

/-- If {lean}`f` is integrable on {lean}`I`, non-negative on {lean}`I`, and {lean}`J ⊆ I`, then {lean}`integ f J = 0` whenever
    {lean}`integ f I = 0`. -/
lemma integ_zero_subset {I J : BoundedInterval} (hIJ : J ⊆ I) {f : ℝ → ℝ}
    (hf_nonneg : ∀ x ∈ I, 0 ≤ f x) (hf_int : IntegrableOn f I) (hinteg_I : integ f I = 0) :
    integ f J = 0 := by
  have hf_int_J : IntegrableOn f J := IntegrableOn.mono' hIJ hf_int
  have h_nonneg : 0 ≤ integ f J := by
    have h0_int_J : IntegrableOn (fun _ : ℝ ↦ 0) J := (IntegrableOn.const (0 : ℝ) J).1
    have hmaj_J : MajorizesOn f (fun _ : ℝ ↦ 0) J := λ x hx => hf_nonneg x (hIJ x hx)
    have h_m := IntegrableOn.mono h0_int_J hf_int_J hmaj_J
    have h_integ_0 : integ (fun _ : ℝ ↦ 0) J = 0 := by
      have h0_const := IntegrableOn.const (0 : ℝ) J
      rw [h0_const.2, zero_mul]
    rw [h_integ_0] at h_m
    exact h_m
  have h_nonpos : integ f J ≤ 0 := by
    refine le_of_forall_pos_lt_add ?_
    intro ε hε
    have h_lt : upper_integral f I < ε := by
      dsimp [integ] at hinteg_I
      nlinarith
    have hbdd := hf_int.1
    rcases lt_of_gt_upper_integral hbdd h_lt with ⟨g, hmaj, hg_pc, hg_int⟩
    have hmaj_J : MajorizesOn g f J := λ x hx => hmaj x (hIJ x hx)
    have hg_pc_J : PiecewiseConstantOn g J := pc_of_subset hIJ hg_pc
    have hg_int_J : IntegrableOn g J := (integ_of_piecewise_const hg_pc_J).1
    have hg_nonneg : ∀ x ∈ I, 0 ≤ g x := by
      intro x hx
      have hfx_nonneg : 0 ≤ f x := hf_nonneg x hx
      have hgx_ge_fx : f x ≤ g x := hmaj x hx
      linarith
    have h_f_le_g_J : MajorizesOn g f J := hmaj_J
    have h_f_integ_le_g_J : integ f J ≤ integ g J :=
      IntegrableOn.mono hf_int_J hg_int_J h_f_le_g_J
    have h_g_integ_J_le_g_integ_I : integ g J ≤ integ g I :=
      integ_nonneg_subset hIJ hg_pc hg_nonneg
    have h_g_integ_I_lt_ε : integ g I < ε := by
      have h_pc_integ_eq : PiecewiseConstantOn.integ g I = integ g I := by
        have h_eq := (integ_of_piecewise_const hg_pc).2
        have h_integ' : hg_pc.integ' = PiecewiseConstantOn.integ g I := by
          unfold PiecewiseConstantOn.integ'
          rfl
        calc
          PiecewiseConstantOn.integ g I = hg_pc.integ' := h_integ'.symm
          _ = integ g I := h_eq.symm
      rw [← h_pc_integ_eq]
      exact hg_int
    have h_f_lt_ε : integ f J < ε := by
      calc
        integ f J ≤ integ g J := h_f_integ_le_g_J
        _ ≤ integ g I := h_g_integ_J_le_g_integ_I
        _ < ε := h_g_integ_I_lt_ε
    nlinarith
  exact le_antisymm h_nonpos h_nonneg

/-- Exercise 11.5.2 -/
theorem integ_zero {a b:ℝ} (hab: a < b) (f: ℝ → ℝ) (hf: ContinuousOn f (Icc a b))
  (hnonneg: MajorizesOn f (fun _ ↦ 0) (Icc a b)) (hinteg : integ f (Icc a b) = 0) :
  ∀ x ∈ Icc a b, f x = 0 := by
  by_cases h_all_zero : ∀ x ∈ Icc a b, f x = 0
  · exact h_all_zero
  · push_neg at h_all_zero
    rcases h_all_zero with ⟨x₀, hx₀, hx₀_ne_zero⟩
    have hx₀_pos : f x₀ > 0 := by
      have h_nonneg : 0 ≤ f x₀ := hnonneg x₀ hx₀
      by_contra! hle
      have : f x₀ = 0 := le_antisymm hle h_nonneg
      exact hx₀_ne_zero this
    exfalso
    set I := Icc a b with hI
    have hbdd : BddOn f I := by
      have h_compact : IsCompact (I : Set ℝ) :=
        ConditionallyCompleteLinearOrder.isCompact_Icc a b
      have h_bdd_above : BddAbove (f '' (I : Set ℝ)) :=
        h_compact.bddAbove_image hf
      have h_bdd_below : BddBelow (f '' (I : Set ℝ)) :=
        h_compact.bddBelow_image hf
      rcases h_bdd_above with ⟨M, hM_above⟩
      rcases h_bdd_below with ⟨m, hM_below⟩
      refine ⟨max (-m) M, λ x hx => ?_⟩
      have hx' : x ∈ (I : Set ℝ) := hx
      have h_fx_above : f x ≤ M := hM_above ⟨x, hx', rfl⟩
      have h_fx_below : m ≤ f x := hM_below ⟨x, hx', rfl⟩
      have h_abs : |f x| ≤ max (-m) M := by
        apply abs_le.mpr
        constructor
        · calc
            -max (-m) M ≤ m := by
              have : max (-m) M ≥ -m := le_max_left _ _
              linarith
            _ ≤ f x := h_fx_below
        · calc
            f x ≤ M := h_fx_above
            _ ≤ max (-m) M := le_max_right _ _
      exact h_abs
    have h_int : IntegrableOn f I := integ_of_bdd_cts hbdd hf
    have h_lower_eq : lower_integral f I = 0 := by
      calc
        lower_integral f I = upper_integral f I := h_int.2
        _ = integ f I := rfl
        _ = 0 := hinteg
    have h_cont : ContinuousWithinAt f I x₀ := hf x₀ hx₀
    have hε_pos : f x₀ / 2 > 0 := by linarith
    rcases Metric.continuousWithinAt_iff.mp h_cont (f x₀ / 2) hε_pos with ⟨δ, hδ_pos, hδ⟩
    let ε := f x₀ / 2
    have h_f_gt_ε : ∀ y ∈ I, |y - x₀| < δ → f y > ε := by
      intro y hy hy_dist
      have hy_set : y ∈ (I : Set ℝ) := hy
      have h' := hδ (x := y) hy_set hy_dist
      have h_abs' : |f y - f x₀| < f x₀ / 2 := h'
      have h_temp : f y > f x₀ - f x₀ / 2 := by
        have h_abs_lt := abs_lt.mp h_abs'
        nlinarith
      calc
        f y > f x₀ - f x₀ / 2 := h_temp
        _ = f x₀ / 2 := by ring
        _ = ε := rfl
    set c := max a (x₀ - δ / 2) with hc_def
    set d := min b (x₀ + δ / 2) with hd_def
    have ha_c : a ≤ c := le_max_left _ _
    have hc_x₀ : c ≤ x₀ := by
      apply max_le
      · exact hx₀.1
      · nlinarith
    have hx₀_d : x₀ ≤ d := by
      apply le_min
      · exact hx₀.2
      · nlinarith
    have hd_b : d ≤ b := min_le_left _ _
    have hc_lt_d : c < d := by
      by_cases ha_lt_x₀ : a < x₀
      · -- c < x₀ ≤ d, so c < d
        have hc_lt_x₀ : c < x₀ := by
          apply max_lt ha_lt_x₀
          nlinarith
        calc
          c < x₀ := hc_lt_x₀
          _ ≤ d := hx₀_d
      · -- a = x₀ (since a ≤ x₀)
        have ha_eq_x₀ : a = x₀ := by linarith
        have hx₀_lt_b : x₀ < b := by
          calc
            x₀ = a := ha_eq_x₀.symm
            _ < b := hab
        have hx₀_lt_d : x₀ < d := by
          apply lt_min_iff.mpr
          constructor
          · exact hx₀_lt_b
          · nlinarith
        have hc_eq_x₀ : c = x₀ := by
          dsimp [c]
          rw [ha_eq_x₀]
          apply max_eq_left
          nlinarith
        calc
          c = x₀ := hc_eq_x₀
          _ < d := hx₀_lt_d
    set J := Icc c d with hJ
    have h_nonzero_len : |J|ₗ > 0 := by
      dsimp [J, BoundedInterval.length]
      simp [hc_lt_d]
    have hJ_sub_I : J ⊆ I := by
      intro x hx
      have hx_mem : x ∈ (I : Set ℝ) := by
        rcases hx with ⟨hcx, hxd⟩
        exact ⟨le_trans ha_c hcx, le_trans hxd hd_b⟩
      exact hx_mem
    have h_f_gt_ε_on_J : ∀ x ∈ J, f x > ε := by
      intro x hx
      have hx_I : x ∈ I := hJ_sub_I x hx
      have hx_dist : |x - x₀| < δ := by
        have hx_low : x₀ - δ / 2 ≤ x := by
          have : c ≤ x := hx.1
          calc
            x₀ - δ / 2 ≤ max a (x₀ - δ / 2) := le_max_right _ _
            _ = c := rfl
            _ ≤ x := this
        have hx_high : x ≤ x₀ + δ / 2 := by
          have : x ≤ d := hx.2
          calc
            x ≤ d := this
            _ = min b (x₀ + δ / 2) := rfl
            _ ≤ x₀ + δ / 2 := min_le_right _ _
        have : x - x₀ < δ := by nlinarith
        have : -(x - x₀) < δ := by nlinarith
        rw [abs_lt]
        constructor <;> nlinarith
      exact h_f_gt_ε x hx_I hx_dist
    have hf_nonneg_on_I : ∀ x ∈ I, 0 ≤ f x :=
      hnonneg
    have h_integ_J_zero : integ f J = 0 :=
      integ_zero_subset hJ_sub_I hf_nonneg_on_I h_int hinteg
    have h_int_J : IntegrableOn f J := IntegrableOn.mono' hJ_sub_I h_int
    have hbdd_J : BddOn f J := by
      rcases hbdd with ⟨M, hM⟩
      exact ⟨M, λ x hx => hM x (hJ_sub_I x hx)⟩
    set P := (⊥ : Partition J) with hP
    have h_lower_riemann : lower_riemann_sum f P = (sInf (f '' (J : Set ℝ))) * |J|ₗ := by
      dsimp [lower_riemann_sum, P]
      simp [Partition.intervals_of_bot]
    have h_sInf_ge_ε : ε ≤ sInf (f '' (J : Set ℝ)) := by
      have h_nonempty : (f '' (J : Set ℝ)).Nonempty := by
        have hx₀_mem : x₀ ∈ J := ⟨by
          calc
            c ≤ x₀ := hc_x₀
            _ = x₀ := rfl
          , by
          calc
            x₀ = x₀ := rfl
            _ ≤ d := hx₀_d
          ⟩
        exact ⟨f x₀, x₀, hx₀_mem, rfl⟩
      refine le_csInf h_nonempty ?_
      rintro y ⟨x, hx, rfl⟩
      have h_fx_gt_ε : f x > ε := h_f_gt_ε_on_J x hx
      exact le_of_lt h_fx_gt_ε
    have h_lower_riemann_pos : 0 < lower_riemann_sum f P := by
      have h_pos_mul : 0 < ε * |J|ₗ := mul_pos hε_pos h_nonzero_len
      have h_sum_ge : ε * |J|ₗ ≤ (sInf (f '' (J : Set ℝ))) * |J|ₗ := by
        nlinarith
      calc
        0 < ε * |J|ₗ := h_pos_mul
        _ ≤ (sInf (f '' (J : Set ℝ))) * |J|ₗ := h_sum_ge
        _ = lower_riemann_sum f P := by rw [h_lower_riemann]
    have h_lower_riemann_le_lower_integral : lower_riemann_sum f P ≤ lower_integral f J :=
      lower_integ_ge_lower_sum hbdd_J P
    have h_lower_J_zero : lower_integral f J = 0 := by
      rw [h_int_J.2]
      simpa using h_integ_J_zero
    nlinarith

end Chapter11
