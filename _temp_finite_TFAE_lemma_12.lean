import Analysis.MeasureTheory.Section_1_2_2

open Set
open EReal

lemma add_sub_cancel_finite' {x y : EReal} (hy_fin : y ≠ ⊤) (hy_not_bot : y ≠ ⊥) : (x + y) - y = x := by
  have hy_real : ∃ (r : ℝ), y = (r : EReal) := by
    have h_cases : y = ⊥ ∨ (∃ r : ℝ, y = (r : EReal)) ∨ y = ⊤ := by
      match y with
      | ⊥ => exact Or.inl rfl
      | (r : ℝ) => exact Or.inr (Or.inl ⟨r, rfl⟩)
      | ⊤ => exact Or.inr (Or.inr rfl)
    rcases h_cases with (hbot | hreal | htop)
    · exact (hy_not_bot hbot).elim
    · exact hreal
    · exact (hy_fin htop).elim
  rcases hy_real with ⟨r, hr⟩
  subst hr
  have h_add_neg : ((r : ℝ) : EReal) + (-((r : ℝ) : EReal)) = (0 : EReal) := by
    have h : (r : ℝ) + (-(r : ℝ)) = (0 : ℝ) := by ring
    exact_mod_cast h
  calc
    (x + ((r : ℝ) : EReal)) - ((r : ℝ) : EReal) = (x + ((r : ℝ) : EReal)) + (-((r : ℝ) : EReal)) := rfl
    _ = x + (((r : ℝ) : EReal) + (-((r : ℝ) : EReal))) := by rw [add_assoc]
    _ = x + (0 : EReal) := by rw [h_add_neg]
    _ = x := by simp

lemma finite_TFAE_1_implies_2 {d : ℕ} (E : Set (EuclideanSpace' d))
    (h1 : ∀ ε > 0, ∃ U : Set (EuclideanSpace' d), IsOpen U ∧ E ⊆ U ∧ Lebesgue_measure U < ⊤ ∧ Lebesgue_outer_measure (U \ E) ≤ ε) :
    ∀ ε > 0, ∃ U : Set (EuclideanSpace' d), IsOpen U ∧ Bornology.IsBounded U ∧ Lebesgue_outer_measure (symmDiff U E) ≤ ε := by
  intro ε hε
  by_cases hε_top : ε = ⊤
  · subst hε_top
    refine ⟨Metric.ball 0 1, Metric.isOpen_ball, Metric.isBounded_ball, le_top⟩
  · -- ε ≠ ⊤, and ε > 0, so ε must be a positive real
    have hε_real : ∃ (r : ℝ), 0 < r ∧ (r : EReal) = ε := by
      have h_cases : ε = ⊥ ∨ (∃ r : ℝ, ε = (r : EReal)) ∨ ε = ⊤ := by
        match ε with
        | ⊥ => exact Or.inl rfl
        | (r : ℝ) => exact Or.inr (Or.inl ⟨r, rfl⟩)
        | ⊤ => exact Or.inr (Or.inr rfl)
      rcases h_cases with (hbot | hreal | htop)
      · exfalso
        rw [hbot] at hε
        exact (EReal.bot_lt_zero.trans hε).ne rfl
      · rcases hreal with ⟨r, hr⟩
        refine ⟨r, ?_, hr.symm⟩
        have hpos : (0 : EReal) < (r : EReal) := by rw [← hr]; exact hε
        exact_mod_cast hpos
      · exact (hε_top htop).elim
    rcases hε_real with ⟨r, hr_pos, hr_eq⟩
    subst hr_eq
    -- Now ε = (r : EReal) with r > 0
    have hr4_pos : (r / 4 : ℝ) > 0 := by linarith
    rcases h1 ((r / 4 : ℝ) : EReal) (by exact_mod_cast hr4_pos) with ⟨U0, hU0_open, hE_sub_U0, hU0_fin, hU0_diff⟩
    -- U0 is open, contains E, has finite measure, and μ(U0\E) ≤ r/4
    
    -- We need: find open bounded V with μ(symmDiff V E) ≤ r
    -- Strategy: V = U0 ∩ B_R for a large ball B_R such that μ(U0\B_R) ≤ r/4
    
    -- First, get R using upward monotone convergence
    let A : ℕ → Set (EuclideanSpace' d) := fun n => U0 ∩ Metric.ball (0 : EuclideanSpace' d) (n : ℝ)
    have hA_mes : ∀ n, LebesgueMeasurable (A n) := by
      intro n
      exact hU0_open.measurable.inter Metric.isOpen_ball.measurable
    have hA_mono : ∀ n, A n ⊆ A (n + 1) := by
      intro n x ⟨hxU0, hxball⟩
      refine ⟨hxU0, Metric.ball_subset_ball (by exact_mod_cast Nat.le_succ n) hxball⟩
    have h_union_A_eq_U0 : ⋃ n, A n = U0 := by
      ext x; constructor
      · intro hx; rcases Set.mem_iUnion.mp hx with ⟨n, hx'⟩; exact hx'.1
      · intro hxU0
        rcases exists_nat_gt (‖x‖) with ⟨n, hn⟩
        refine Set.mem_iUnion.mpr ⟨n, hxU0, ?_⟩
        rw [Metric.mem_ball, dist_eq_norm, sub_zero]
        exact hn
    have h_tendsto_A : Filter.atTop.Tendsto (fun n ↦ Lebesgue_measure (A n)) (nhds (Lebesgue_measure U0)) := by
      have h_temp := Lebesgue_measure.upward_monotone_convergence hA_mes hA_mono
      simpa [h_union_A_eq_U0] using h_temp
    -- Since μ(U0) < ⊤, convert to ℝ-convergence
    have hU0_not_top : Lebesgue_measure U0 ≠ ⊤ := hU0_fin.ne
    have hU0_not_bot : Lebesgue_measure U0 ≠ ⊥ := by
      have h_nonneg : 0 ≤ Lebesgue_measure U0 := Lebesgue_outer_measure.nonneg _
      intro hbot; rw [hbot] at h_nonneg; exact (EReal.bot_lt_zero.trans_le h_nonneg).ne rfl
    have h_tendsto_A_real : Filter.atTop.Tendsto (fun n ↦ (Lebesgue_measure (A n)).toReal) (nhds ((Lebesgue_measure U0).toReal)) :=
      (EReal.tendsto_toReal hU0_not_top hU0_not_bot).comp h_tendsto_A
    -- Find N such that |μ(A_N).toReal - μ(U0).toReal| < r/4
    have h_exists_N : ∃ N : ℕ, |(Lebesgue_measure (A N)).toReal - (Lebesgue_measure U0).toReal| < r / 4 := by
      have h := Metric.tendsto_atTop.mp h_tendsto_A_real (r / 4) (by linarith)
      rcases h with ⟨N, hN⟩
      refine ⟨N, ?_⟩
      have := hN N (le_refl N)
      rw [Real.dist_eq] at this
      exact this
    rcases h_exists_N with ⟨N, hN⟩
    -- hN gives |μ(A_N).toReal - μ(U0).toReal| < r/4
    have h_mono_real : (Lebesgue_measure (A N)).toReal ≤ (Lebesgue_measure U0).toReal := by
      have h_sub : A N ⊆ U0 := fun x hx => hx.1
      have h_mu : Lebesgue_measure (A N) ≤ Lebesgue_measure U0 :=
        Lebesgue_outer_measure.mono h_sub
      have h_not_bot : Lebesgue_measure (A N) ≠ ⊥ := by
        have h_nonneg : 0 ≤ Lebesgue_measure (A N) := Lebesgue_outer_measure.nonneg _
        intro hbot; rw [hbot] at h_nonneg; exact (EReal.bot_lt_zero.trans_le h_nonneg).ne rfl
      have h_not_top_U0 : Lebesgue_measure U0 ≠ ⊤ := hU0_not_top
      exact EReal.toReal_le_toReal h_mu h_not_bot h_not_top_U0
    have h_diff_real_bound : (Lebesgue_measure U0).toReal - (Lebesgue_measure (A N)).toReal < r / 4 := by
      have h_abs_eq : |(Lebesgue_measure (A N)).toReal - (Lebesgue_measure U0).toReal| =
          (Lebesgue_measure U0).toReal - (Lebesgue_measure (A N)).toReal := by
        have h_nonpos : (Lebesgue_measure (A N)).toReal - (Lebesgue_measure U0).toReal ≤ 0 := by linarith
        rw [abs_of_nonpos h_nonpos]
        ring
      rw [h_abs_eq] at hN
      exact hN
    
    -- Now V = A N = U0 ∩ ball(0, N) is open and bounded
    let V : Set (EuclideanSpace' d) := A N
    have hV_open : IsOpen V := IsOpen.inter hU0_open Metric.isOpen_ball
    have hV_bounded : Bornology.IsBounded V :=
      Bornology.IsBounded.subset Metric.isBounded_ball (Set.inter_subset_right)
    
    have h_AN_fin : Lebesgue_measure (A N) < ⊤ := by
      have h_sub : A N ⊆ U0 := fun x hx => hx.1
      calc
        Lebesgue_measure (A N) ≤ Lebesgue_measure U0 := Lebesgue_outer_measure.mono h_sub
        _ < ⊤ := hU0_fin
    
    -- Show μ(U0 \ V) = μ(U0) - μ(V) (both finite and V ⊆ U0)
    have h_mu_diff_exact : Lebesgue_outer_measure (U0 \ V) = (Lebesgue_measure U0).toReal - (Lebesgue_measure V).toReal := by
      have h_meas_V : LebesgueMeasurable V := hA_mes N
      have h_disj : V ∩ (U0 \ V) = ∅ := by ext x; simp
      have hV_sub_U0 : V ⊆ U0 := by
        intro x hx
        -- V = A N = U0 ∩ ball(0, N)
        have hxV : x ∈ A N := hx
        exact hxV.1
      have h_union : U0 = V ∪ (U0 \ V) := by
        apply Set.Subset.antisymm
        · intro x hxU0
          by_cases hxV : x ∈ V
          · exact Set.mem_union_left _ hxV
          · exact Set.mem_union_right _ ⟨hxU0, hxV⟩
        · intro x hx
          rcases hx with (hxV | ⟨hxU0, _⟩)
          · exact hV_sub_U0 hxV
          · exact hxU0
      have h_union_meas : LebesgueMeasurable (U0 \ V) :=
        hU0_open.measurable.inter (LebesgueMeasurable.complement h_meas_V)
      have h_add : Lebesgue_measure U0 = Lebesgue_measure V + Lebesgue_measure (U0 \ V) := by
        -- Write U0 as V ∪ (U0 \ V) and apply Lebesgue_measure.union
        calc
          Lebesgue_measure U0 = Lebesgue_measure (V ∪ (U0 \ V)) := by
            -- Use h_union to rewrite: U0 = V ∪ (U0 \ V)
            -- We need to rewrite U0 only in the argument of Lebesgue_measure, not in (U0 \ V)
            -- Use `rw` with `h_union` only at the `U0` occurrence
            conv => lhs; rw [h_union]
          _ = Lebesgue_measure V + Lebesgue_measure (U0 \ V) :=
            Lebesgue_measure.union h_meas_V h_union_meas h_disj
      have h_V_not_top : Lebesgue_measure V ≠ ⊤ := h_AN_fin.ne
      have h_V_not_bot : Lebesgue_measure V ≠ ⊥ := by
        have h_nonneg : 0 ≤ Lebesgue_measure V := Lebesgue_outer_measure.nonneg _
        intro hbot; rw [hbot] at h_nonneg; exact (EReal.bot_lt_zero.trans_le h_nonneg).ne rfl
      have h_diff_not_top : Lebesgue_measure (U0 \ V) ≠ ⊤ := by
        have h_sub : U0 \ V ⊆ U0 := Set.diff_subset
        have h_le : Lebesgue_measure (U0 \ V) ≤ Lebesgue_measure U0 :=
          Lebesgue_outer_measure.mono h_sub
        exact ne_of_lt (lt_of_le_of_lt h_le hU0_fin)
      have h_diff_not_bot : Lebesgue_measure (U0 \ V) ≠ ⊥ := by
        have h_nonneg : 0 ≤ Lebesgue_measure (U0 \ V) := Lebesgue_outer_measure.nonneg _
        intro hbot; rw [hbot] at h_nonneg; exact (EReal.bot_lt_zero.trans_le h_nonneg).ne rfl
      calc
        Lebesgue_outer_measure (U0 \ V) = Lebesgue_measure (U0 \ V) := rfl
        _ = Lebesgue_measure V + Lebesgue_measure (U0 \ V) - Lebesgue_measure V := by
          rw [add_comm, add_sub_cancel_finite' h_V_not_top h_V_not_bot]
        _ = Lebesgue_measure U0 - Lebesgue_measure V := by rw [h_add]
        _ = ((Lebesgue_measure U0).toReal : EReal) - ((Lebesgue_measure V).toReal : EReal) := by
          simp [EReal.coe_toReal hU0_not_top hU0_not_bot, EReal.coe_toReal h_V_not_top h_V_not_bot]
        _ = (((Lebesgue_measure U0).toReal - (Lebesgue_measure V).toReal : ℝ) : EReal) := by simp
    
    have h_mu_U0_diff_V : Lebesgue_outer_measure (U0 \ V) ≤ (r / 4 : ℝ) := by
      rw [h_mu_diff_exact]
      have h_bound : (Lebesgue_measure U0).toReal - (Lebesgue_measure V).toReal < r / 4 := by
        simpa [V] using h_diff_real_bound
      -- Convert the real inequality to EReal
      have h_bound_ereal : (((Lebesgue_measure U0).toReal - (Lebesgue_measure V).toReal : ℝ) : EReal) ≤ ((r / 4 : ℝ) : EReal) := by
        exact_mod_cast h_bound.le
      exact h_bound_ereal
    
    -- Claim: μ(symmDiff V E) ≤ (r : EReal)
    have h_symmDiff_bound : Lebesgue_outer_measure (symmDiff V E) ≤ (r : EReal) := by
      rw [Set.symmDiff_def]
      have h_sub1 : V \ E ⊆ U0 \ E := Set.diff_subset_diff_left (by
        -- V ⊆ U0 because V = A N ⊆ U0
        have hV_sub_U0 : V ⊆ U0 := fun x hx => hx.1
        exact hV_sub_U0)
      have h_sub2 : E \ V ⊆ U0 \ V := by
        intro x ⟨hxE, hxnotV⟩
        refine ⟨hE_sub_U0 hxE, ?_⟩
        intro hxUV; apply hxnotV; exact hxUV
      have h_sub_union : (V \ E) ∪ (E \ V) ⊆ (U0 \ E) ∪ (U0 \ V) := by
        apply Set.union_subset
        · exact Set.Subset.trans h_sub1
            (Set.subset_union_left (s := U0 \ E) (t := U0 \ V))
        · exact Set.Subset.trans h_sub2
            (Set.subset_union_right (s := U0 \ E) (t := U0 \ V))
      have h_mu_union : Lebesgue_outer_measure ((V \ E) ∪ (E \ V)) ≤ Lebesgue_outer_measure ((U0 \ E) ∪ (U0 \ V)) :=
        Lebesgue_outer_measure.mono h_sub_union
      -- Use subadditivity: μ((U0\E)∪(U0\V)) ≤ μ(U0\E) + μ(U0\V)
      have h_subadd : Lebesgue_outer_measure ((U0 \ E) ∪ (U0 \ V)) ≤
          Lebesgue_outer_measure (U0 \ E) + Lebesgue_outer_measure (U0 \ V) := by
        let F : Fin 2 → Set (EuclideanSpace' d) := ![U0 \ E, U0 \ V]
        have h_union : (⋃ i, F i) = (U0 \ E) ∪ (U0 \ V) := by
          ext x; simp [F]
        have h_fin_union : Lebesgue_outer_measure (⋃ i, F i) ≤ ∑ i : Fin 2, Lebesgue_outer_measure (F i) :=
          Lebesgue_outer_measure.finite_union_le F
        have h_sum : ∑ i : Fin 2, Lebesgue_outer_measure (F i) = Lebesgue_outer_measure (U0 \ E) + Lebesgue_outer_measure (U0 \ V) := by
          simp [F, Fin.sum_univ_two]
        calc
          Lebesgue_outer_measure ((U0 \ E) ∪ (U0 \ V)) = Lebesgue_outer_measure (⋃ i, F i) := by rw [h_union]
          _ ≤ ∑ i : Fin 2, Lebesgue_outer_measure (F i) := h_fin_union
          _ = Lebesgue_outer_measure (U0 \ E) + Lebesgue_outer_measure (U0 \ V) := h_sum
      have h_total : Lebesgue_outer_measure (U0 \ E) + Lebesgue_outer_measure (U0 \ V) ≤ (r : EReal) := by
        have hU0_diff' : Lebesgue_outer_measure (U0 \ E) ≤ ((r / 4 : ℝ) : EReal) := hU0_diff
        have h_mu_U0_diff_V' : Lebesgue_outer_measure (U0 \ V) ≤ ((r / 4 : ℝ) : EReal) := h_mu_U0_diff_V
        have h_sum : Lebesgue_outer_measure (U0 \ E) + Lebesgue_outer_measure (U0 \ V) ≤
            ((r / 4 : ℝ) : EReal) + ((r / 4 : ℝ) : EReal) := add_le_add hU0_diff' h_mu_U0_diff_V'
        have h_sum_eq : ((r / 4 : ℝ) : EReal) + ((r / 4 : ℝ) : EReal) = ((r / 2 : ℝ) : EReal) := by
          have h_real : (r / 4 : ℝ) + (r / 4 : ℝ) = (r / 2 : ℝ) := by ring
          simpa [add_comm, add_left_comm, add_assoc] using congrArg (fun x : ℝ => (x : EReal)) h_real
        have h_lt : ((r / 2 : ℝ) : EReal) < (r : EReal) := by
          have : (r / 2 : ℝ) < r := by linarith
          exact_mod_cast this
        calc
          Lebesgue_outer_measure (U0 \ E) + Lebesgue_outer_measure (U0 \ V) ≤ ((r / 4 : ℝ) : EReal) + ((r / 4 : ℝ) : EReal) := h_sum
          _ = ((r / 2 : ℝ) : EReal) := h_sum_eq
          _ ≤ (r : EReal) := h_lt.le
      calc
        Lebesgue_outer_measure (symmDiff V E) = Lebesgue_outer_measure ((V \ E) ∪ (E \ V)) := by rw [Set.symmDiff_def]
        _ ≤ Lebesgue_outer_measure ((U0 \ E) ∪ (U0 \ V)) := h_mu_union
        _ ≤ Lebesgue_outer_measure (U0 \ E) + Lebesgue_outer_measure (U0 \ V) := h_subadd
        _ ≤ (r : EReal) := h_total
    
    exact ⟨V, hV_open, hV_bounded, h_symmDiff_bound⟩
