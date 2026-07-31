import Analysis.MeasureTheory.Section_1_2_2

open Set
open Filter

lemma finite_TFAE_5_implies_6 {d : ℕ} (E : Set (EuclideanSpace' d))
    (h5 : ∀ ε > 0, ∃ E' : Set (EuclideanSpace' d), LebesgueMeasurable E' ∧ Lebesgue_measure E' < ⊤ ∧ Lebesgue_outer_measure (symmDiff E' E) ≤ ε) :
    ∀ ε > 0, ∃ E' : Set (EuclideanSpace' d), LebesgueMeasurable E' ∧ Bornology.IsBounded E' ∧ Lebesgue_outer_measure (symmDiff E' E) ≤ ε := by
  intro ε hε
  by_cases hε_top : ε = ⊤
  · subst hε_top
    refine ⟨∅, LebesgueMeasurable.empty, Bornology.isBounded_empty, ?_⟩
    exact le_top
  · -- ε is a positive real number
    have hε_pos_real : ∃ r : ℝ, ε = (r : EReal) ∧ 0 < r := by
      have h_cases : ε = ⊥ ∨ (∃ r : ℝ, ε = (r : EReal)) ∨ ε = ⊤ := by
        match ε with
        | ⊥ => exact Or.inl rfl
        | (r : ℝ) => exact Or.inr (Or.inl ⟨r, rfl⟩)
        | ⊤ => exact Or.inr (Or.inr rfl)
      rcases h_cases with (hbot | hreal | htop)
      · -- ε = ⊥, but ε > 0 contradicts EReal.bot_lt_zero
        rw [hbot] at hε
        have hpos : (0 : EReal) < (⊥ : EReal) := hε
        have hbot_lt_zero : (⊥ : EReal) < 0 := EReal.bot_lt_zero
        have : (0 : EReal) < 0 := hpos.trans hbot_lt_zero
        exact (lt_irrefl (0 : EReal) this).elim
      · rcases hreal with ⟨r, hr⟩
        have hr_pos : 0 < r := by
          have hpos_ereal : (0 : EReal) < (r : EReal) := by rw [← hr]; exact hε
          exact_mod_cast hpos_ereal
        exact ⟨r, hr, hr_pos⟩
      · exact (hε_top htop).elim
    rcases hε_pos_real with ⟨r, hr, hr_pos⟩
    subst hr
    -- Now ε = (r : EReal) with r > 0
    have hr_div_pos : 0 < r/2 := by linarith
    rcases h5 ((r/2 : ℝ) : EReal) (by exact_mod_cast hr_div_pos) with ⟨E', hE'_meas, hE'_fin, h_symm⟩
    
    -- Define A_n = E' ∩ closedBall 0 n (increasing to E')
    let A (n : ℕ) : Set (EuclideanSpace' d) := E' ∩ Metric.closedBall (0 : EuclideanSpace' d) ((n : ℕ) : ℝ)
    
    have hA_meas (n : ℕ) : LebesgueMeasurable (A n) :=
      LebesgueMeasurable.inter hE'_meas (Metric.isClosed_closedBall (x := 0) (ε := ((n : ℕ) : ℝ))).measurable
    
    have hA_mono (n : ℕ) : A n ⊆ A (n+1) := by
      intro x hx
      rcases hx with ⟨hxE', hx_ball⟩
      refine ⟨hxE', ?_⟩
      have h_dist : dist x (0 : EuclideanSpace' d) ≤ ((n : ℕ) : ℝ) := Metric.mem_closedBall.mp hx_ball
      have hn : ((n : ℕ) : ℝ) ≤ (((n+1 : ℕ) : ℕ) : ℝ) := by push_cast; nlinarith
      exact Metric.mem_closedBall.mpr (le_trans h_dist hn)
    
    have hA_union : ⋃ n, A n = E' := Metric.iUnion_inter_closedBall_nat E' 0
    
    have h_tendsto : Filter.atTop.Tendsto (fun n : ℕ => Lebesgue_measure (A n)) (nhds (Lebesgue_measure E')) := by
      have h_temp := Lebesgue_measure.upward_monotone_convergence hA_meas hA_mono
      rw [hA_union] at h_temp
      exact h_temp
    
    have h_E'_fin_ne_top : Lebesgue_measure E' ≠ ⊤ := ne_of_lt hE'_fin
    have h_E'_nonneg : 0 ≤ Lebesgue_measure E' := Lebesgue_outer_measure.nonneg E'
    have h_E'_not_bot : Lebesgue_measure E' ≠ ⊥ := by
      intro hbot
      rw [hbot] at h_E'_nonneg
      have h_lt : (⊥ : EReal) < 0 := EReal.bot_lt_zero
      have : (⊥ : EReal) < (⊥ : EReal) := h_lt.trans_le h_E'_nonneg
      exact lt_irrefl _ this
    
    -- Convert to ℝ-valued convergence
    have h_tendsto_real : Filter.atTop.Tendsto (fun n : ℕ => (Lebesgue_measure (A n)).toReal) (nhds ((Lebesgue_measure E').toReal)) :=
      (EReal.tendsto_toReal h_E'_fin_ne_top h_E'_not_bot).comp h_tendsto
    
    -- Since (m(A_n)).toReal → (m(E')).toReal, for δ = r/4 > 0, there exists N such that
    -- (m(E')).toReal - (m(A_N)).toReal < r/4
    have h_limit : ∀ᶠ n in atTop, |(Lebesgue_measure (A n)).toReal - (Lebesgue_measure E').toReal| < r/4 := by
      rw [Metric.tendsto_nhds] at h_tendsto_real
      exact h_tendsto_real (r/4) (by nlinarith)
    
    rcases Filter.eventually_atTop.mp h_limit with ⟨N, hN⟩
    have h_N_bound : (Lebesgue_measure E').toReal - (Lebesgue_measure (A N)).toReal < r/4 := by
      have h_abs := hN N (le_refl N)
      have h_abs_symm : |(Lebesgue_measure E').toReal - (Lebesgue_measure (A N)).toReal| < r/4 := by
        simpa [abs_sub_comm] using h_abs
      rcases abs_lt.mp h_abs_symm with ⟨h_low, h_high⟩
      linarith
    
    -- Let E'' = A N = E' ∩ closedBall 0 N (bounded and measurable)
    set E'' := A N with hE''_def
    
    have hE''_meas : LebesgueMeasurable E'' := hA_meas N
    
    have hE''_bounded : Bornology.IsBounded E'' := by
      dsimp [E'', A]
      apply (Metric.isBounded_closedBall (x := 0) (r := ((N : ℕ) : ℝ))).subset
      exact Set.inter_subset_right
    
    -- Main inequality: m*(symmDiff(E'', E)) ≤ r
    have h_main : Lebesgue_outer_measure (symmDiff E'' E) ≤ (r : EReal) := by
      -- SymmDiff bound: symmDiff(E'', E) ⊆ symmDiff(E', E) ∪ (E' \ closedBall 0 N)
      have h_symm_sub : symmDiff E'' E ⊆ symmDiff E' E ∪ (E' \ Metric.closedBall (0 : EuclideanSpace' d) ((N : ℕ) : ℝ)) := by
        intro x hx
        rw [symmDiff_def] at hx
        rcases hx with (⟨hxE'', hx_not_E⟩ | ⟨hxE, hx_not_E''⟩)
        · -- x ∈ E'' \ E ⊆ E' \ E ⊆ symmDiff(E',E)
          dsimp [E'', A] at hxE''
          rcases hxE'' with ⟨hxE', _⟩
          have : x ∈ symmDiff E' E := by
            rw [symmDiff_def]
            exact Or.inl ⟨hxE', hx_not_E⟩
          exact Set.mem_union_left _ this
        · -- x ∈ E \ E''
          -- Either x ∈ E' or not
          by_cases hxE' : x ∈ E'
          · -- x ∈ E' \ A_N = E' \ closedBall 0 N
            dsimp [E'', A] at hx_not_E''
            have : x ∉ Metric.closedBall (0 : EuclideanSpace' d) ((N : ℕ) : ℝ) := by
              intro hx_cb
              apply hx_not_E''
              exact ⟨hxE', hx_cb⟩
            exact Set.mem_union_right _ ⟨hxE', this⟩
          · -- x ∉ E', so x ∈ E \ E' ⊆ symmDiff(E',E)
            have : x ∈ symmDiff E' E := by
              rw [symmDiff_def]
              exact Or.inr ⟨hxE, hxE'⟩
            exact Set.mem_union_left _ this
    
      have h_outer_sub : Lebesgue_outer_measure (symmDiff E'' E)
          ≤ Lebesgue_outer_measure (symmDiff E' E ∪ (E' \ Metric.closedBall (0 : EuclideanSpace' d) ((N : ℕ) : ℝ))) :=
        Lebesgue_outer_measure.mono h_symm_sub
    
      -- Finite subadditivity for two sets using Fin 2
      let F : Fin 2 → Set (EuclideanSpace' d) := ![symmDiff E' E, E' \ Metric.closedBall (0 : EuclideanSpace' d) ((N : ℕ) : ℝ)]
      have h_union_sub : (symmDiff E' E ∪ (E' \ Metric.closedBall (0 : EuclideanSpace' d) ((N : ℕ) : ℝ))) = ⋃ i : Fin 2, F i := by
        ext x; simp [F, Set.mem_union, Set.mem_iUnion]
      have h_finite_union_le : Lebesgue_outer_measure (symmDiff E' E ∪ (E' \ Metric.closedBall (0 : EuclideanSpace' d) ((N : ℕ) : ℝ)))
          ≤ Lebesgue_outer_measure (symmDiff E' E) + Lebesgue_outer_measure (E' \ Metric.closedBall (0 : EuclideanSpace' d) ((N : ℕ) : ℝ)) := by
        calc
          Lebesgue_outer_measure (symmDiff E' E ∪ (E' \ Metric.closedBall (0 : EuclideanSpace' d) ((N : ℕ) : ℝ)))
              = Lebesgue_outer_measure (⋃ i : Fin 2, F i) := by rw [h_union_sub]
          _ ≤ ∑ i : Fin 2, Lebesgue_outer_measure (F i) := Lebesgue_outer_measure.finite_union_le F
          _ = Lebesgue_outer_measure (F 0) + Lebesgue_outer_measure (F 1) := Fin.sum_univ_two _
          _ = Lebesgue_outer_measure (symmDiff E' E) + Lebesgue_outer_measure (E' \ Metric.closedBall (0 : EuclideanSpace' d) ((N : ℕ) : ℝ)) := by simp [F]
    
      -- Bound the second term: m(E' \ closedBall 0 N) ≤ r/2
      have h_diff_bound : Lebesgue_outer_measure (E' \ Metric.closedBall (0 : EuclideanSpace' d) ((N : ℕ) : ℝ)) ≤ ((r/2 : ℝ) : EReal) := by
        let D := E' \ Metric.closedBall (0 : EuclideanSpace' d) ((N : ℕ) : ℝ)
        have hD_meas : LebesgueMeasurable D :=
          LebesgueMeasurable.inter hE'_meas (LebesgueMeasurable.complement
            (Metric.isClosed_closedBall (x := 0) (ε := ((N : ℕ) : ℝ))).measurable)
        have h_union_eq : E' = (A N) ∪ D := by
          ext x
          constructor
          · intro hx
            by_cases hx_ball : x ∈ Metric.closedBall (0 : EuclideanSpace' d) ((N : ℕ) : ℝ)
            · apply Or.inl; exact ⟨hx, hx_ball⟩
            · apply Or.inr; exact ⟨hx, hx_ball⟩
          · intro hx
            rcases hx with (⟨hx, _⟩ | ⟨hx, _⟩)
            · exact hx
            · exact hx
        have h_disjoint : (A N) ∩ D = ∅ := by
          ext x
          constructor
          · intro hx
            rcases hx with ⟨⟨hxE', hx_ball⟩, ⟨hxE'2, hx_not_ball⟩⟩
            exact absurd hx_ball hx_not_ball
          · intro hx
            exfalso
            exact hx
        have h_measure_eq : Lebesgue_measure E' = Lebesgue_measure (A N) + Lebesgue_measure D := by
          calc
            Lebesgue_measure E' = Lebesgue_measure ((A N) ∪ D) := by rw [h_union_eq]
            _ = Lebesgue_measure (A N) + Lebesgue_measure D :=
              Lebesgue_measure.union (hA_meas N) hD_meas h_disjoint
        
        -- From h_measure_eq, m(D) = m(E') - m(A N)
        -- Since m(E') and m(A N) are finite, (m(D)).toReal = (m(E')).toReal - (m(A N)).toReal
        have h_D_fin : Lebesgue_measure D < ⊤ := by
          calc
            Lebesgue_measure D ≤ Lebesgue_measure E' := Lebesgue_outer_measure.mono Set.diff_subset
            _ < ⊤ := hE'_fin
        
        have h_D_not_bot : Lebesgue_measure D ≠ ⊥ := by
          intro hbot
          have h_nonneg : 0 ≤ Lebesgue_measure D := Lebesgue_outer_measure.nonneg D
          rw [hbot] at h_nonneg
          have h_lt : (⊥ : EReal) < 0 := EReal.bot_lt_zero
          have : (⊥ : EReal) < (⊥ : EReal) := h_lt.trans_le h_nonneg
          exact lt_irrefl (⊥ : EReal) this
        
        have h_A_N_fin : Lebesgue_measure (A N) < ⊤ := by
          calc
            Lebesgue_measure (A N) ≤ Lebesgue_measure E' := Lebesgue_outer_measure.mono (Set.inter_subset_left)
            _ < ⊤ := hE'_fin
        
        have h_A_N_not_bot : Lebesgue_measure (A N) ≠ ⊥ := by
          intro hbot
          have h_nonneg : 0 ≤ Lebesgue_measure (A N) := Lebesgue_outer_measure.nonneg _
          rw [hbot] at h_nonneg
          have h_lt : (⊥ : EReal) < 0 := EReal.bot_lt_zero
          have : (⊥ : EReal) < (⊥ : EReal) := h_lt.trans_le h_nonneg
          exact lt_irrefl _ this
        
        have h_D_toReal_eq : (Lebesgue_measure D).toReal = (Lebesgue_measure E').toReal - (Lebesgue_measure (A N)).toReal := by
          -- From h_measure_eq: m(E') = m(A N) + m(D)
          -- Using EReal.toReal_add (since all are finite non-bot)
          have h_add_toReal : (Lebesgue_measure E').toReal = (Lebesgue_measure (A N)).toReal + (Lebesgue_measure D).toReal := by
            calc
              (Lebesgue_measure E').toReal = (Lebesgue_measure (A N) + Lebesgue_measure D).toReal := by rw [h_measure_eq]
              _ = (Lebesgue_measure (A N)).toReal + (Lebesgue_measure D).toReal :=
                EReal.toReal_add (h_A_N_fin.ne_top) (h_A_N_not_bot) (h_D_fin.ne_top) (h_D_not_bot)
          linarith
        
        have h_toReal_bound : (Lebesgue_measure D).toReal < r/2 := by
          calc
            (Lebesgue_measure D).toReal = (Lebesgue_measure E').toReal - (Lebesgue_measure (A N)).toReal := h_D_toReal_eq
            _ < r/4 := h_N_bound
            _ < r/2 := by nlinarith
        
        have h_D_lt_top : Lebesgue_measure D ≠ ⊤ := h_D_fin.ne_top
        
        -- Now we can bound the EReal value
        have h_D_ereal : Lebesgue_measure D ≤ ((r/2 : ℝ) : EReal) := by
          -- By EReal.coe_toReal, since m(D) is finite non-bot: m(D) = ((m(D)).toReal : EReal)
          -- And (m(D)).toReal < r/2 implies (m(D)).toReal ≤ r/2
          have h_coe : Lebesgue_measure D = ((Lebesgue_measure D).toReal : EReal) :=
            (EReal.coe_toReal h_D_lt_top h_D_not_bot).symm
          rw [h_coe]
          have : (Lebesgue_measure D).toReal ≤ r/2 := by linarith
          exact_mod_cast this
        
        -- And since Lebesgue_outer_measure = Lebesgue_measure for measurable sets
        simpa [D] using h_D_ereal
      
      -- Combine bounds
      calc
        Lebesgue_outer_measure (symmDiff E'' E) ≤ Lebesgue_outer_measure (symmDiff E' E ∪ (E' \ Metric.closedBall (0 : EuclideanSpace' d) ((N : ℕ) : ℝ))) := h_outer_sub
        _ ≤ Lebesgue_outer_measure (symmDiff E' E) + Lebesgue_outer_measure (E' \ Metric.closedBall (0 : EuclideanSpace' d) ((N : ℕ) : ℝ)) := h_finite_union_le
        _ ≤ ((r/2 : ℝ) : EReal) + ((r/2 : ℝ) : EReal) := 
          add_le_add h_symm h_diff_bound
        _ = (r : EReal) := by
          have : (r/2 : ℝ) + (r/2 : ℝ) = r := by ring
          exact_mod_cast this
    
    exact ⟨E'', hE''_meas, hE''_bounded, h_main⟩