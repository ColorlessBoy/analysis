import Analysis.MeasureTheory.Section_1_2_2
open Set
open Filter

lemma exists_compact_subset_measure_approx {d : ℕ} (E : Set (EuclideanSpace' d))
    (hE_meas : LebesgueMeasurable E) (hE_fin : Lebesgue_measure E < ⊤) (ε : ℝ) (hε_pos : 0 < ε) :
    ∃ K, IsCompact K ∧ K ⊆ E ∧ Lebesgue_outer_measure (E \ K) ≤ (ε : ℝ) := by
  have hε2_pos : (0 : EReal) < (ε / 2 : ℝ) := by exact_mod_cast (half_pos hε_pos)
  have h_closed_approx : ∀ δ > 0, ∃ F, IsClosed F ∧ F ⊆ E ∧ Lebesgue_outer_measure (E \ F) ≤ δ :=
    ((LebesgueMeasurable.TFAE E).out 0 3).mp hE_meas
  rcases h_closed_approx ((ε / 2 : ℝ) : EReal) hε2_pos with ⟨F, hF_closed, hF_sub_E, hF_diff⟩
  have hF_fin : Lebesgue_measure F < ⊤ := lt_of_le_of_lt (Lebesgue_outer_measure.mono hF_sub_E) hE_fin
  let Fseq : ℕ → Set (EuclideanSpace' d) := fun n => F ∩ Metric.closedBall (0 : EuclideanSpace' d) (n : ℝ)
  have hFseq_meas : ∀ n, LebesgueMeasurable (Fseq n) := fun n =>
    hF_closed.measurable.inter (by
      have : LebesgueMeasurable (Metric.closedBall (0 : EuclideanSpace' d) (n : ℝ)) :=
        Metric.isClosed_closedBall.measurable
      exact this)
  have hFseq_mono : ∀ n, Fseq n ⊆ Fseq (n+1) := by
    intro n x hx
    rcases hx with ⟨hxF, hx_ball⟩
    refine ⟨hxF, ?_⟩
    have hn : (n : ℝ) ≤ ((n+1 : ℕ) : ℝ) := by exact_mod_cast (Nat.le_succ n)
    have hx_dist : dist x (0 : EuclideanSpace' d) ≤ (n : ℝ) := Metric.mem_closedBall.mp hx_ball
    exact Metric.mem_closedBall.mpr (le_trans hx_dist hn)
  have hFseq_eq : ∀ n, Fseq n = F ∩ Metric.closedBall (0 : EuclideanSpace' d) (n : ℝ) := by intro n; rfl
  have hFseq_union : ⋃ (k : ℕ), Fseq k = F := by
    ext x; constructor
    · intro h; rcases h with ⟨(k : ℕ), hx⟩; rw [hFseq_eq k] at hx; exact hx.1
    · intro hxF
      rcases exists_nat_gt (‖x‖) with ⟨k, hk⟩
      refine Set.mem_iUnion.mpr ⟨k, ⟨hxF, ?_⟩⟩
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      exact hk.le
  have h_tendsto : atTop.Tendsto (fun n : ℕ => Lebesgue_measure (Fseq n)) (nhds (Lebesgue_measure F)) := by
    have h_temp := Lebesgue_measure.upward_monotone_convergence hFseq_meas hFseq_mono
    simpa [hFseq_union] using h_temp
  have hFseqot_top : Lebesgue_measure F ≠ ⊤ := hF_fin.ne
  have hFseqot_bot : Lebesgue_measure F ≠ ⊥ := by
    have h_nonneg : 0 ≤ Lebesgue_measure F := Lebesgue_outer_measure.nonneg F
    intro hbot; rw [hbot] at h_nonneg; exact (EReal.bot_lt_zero.trans_le h_nonneg).ne rfl
  have h_tendsto_real : atTop.Tendsto (fun n : ℕ => (Lebesgue_measure (Fseq n)).toReal) (nhds ((Lebesgue_measure F).toReal)) :=
    (EReal.tendsto_toReal hFseqot_top hFseqot_bot).comp h_tendsto
  have h_limit_event : ∀ᶠ n in atTop, |(Lebesgue_measure (Fseq n)).toReal - (Lebesgue_measure F).toReal| < ε / 2 := by
    rw [Metric.tendsto_nhds] at h_tendsto_real
    exact h_tendsto_real (ε / 2) (by linarith)
  rcases Filter.eventually_atTop.mp h_limit_event with ⟨N, hN⟩
  let K := Fseq N
  have hK_compact : IsCompact K := by
    have h_closed : IsClosed K := IsClosed.inter hF_closed Metric.isClosed_closedBall
    have h_bounded : Bornology.IsBounded K :=
      (Metric.isBounded_closedBall (x := 0) (r := (N : ℝ))).subset (Set.inter_subset_right (s := F))
    exact Metric.isCompact_of_isClosed_isBounded h_closed h_bounded
  have hK_sub_E : K ⊆ E := Set.Subset.trans (Set.inter_subset_left) hF_sub_E
  have h_diff_bound : (Lebesgue_measure F).toReal - (Lebesgue_measure (Fseq N)).toReal < ε / 2 := by
    have h_abs := hN N (le_refl N)
    have h_mono : (Lebesgue_measure (Fseq N)).toReal ≤ (Lebesgue_measure F).toReal := by
      have h_sub : Fseq N ⊆ F := by intro x hx; exact hx.1
      have h_mu : Lebesgue_measure (Fseq N) ≤ Lebesgue_measure F := Lebesgue_outer_measure.mono h_sub
      refine EReal.toReal_le_toReal h_mu ?_ hFseqot_top
      have h_nonneg' : 0 ≤ Lebesgue_measure (Fseq N) := Lebesgue_outer_measure.nonneg _
      intro hbot; rw [hbot] at h_nonneg'; exact (EReal.bot_lt_zero.trans_le h_nonneg').ne rfl
    rcases abs_lt.mp h_abs with ⟨h_low, h_high⟩
    linarith
  have hK_diff : Lebesgue_outer_measure (E \ K) ≤ (ε : ℝ) := by
    have h_sub : E \ K ⊆ (E \ F) ∪ (F \ K) := by
      intro x hx; rcases hx with ⟨hxE, hxK⟩
      by_cases hxF : x ∈ F
      · apply Set.mem_union_right
        exact ⟨hxF, hxK⟩
      · apply Set.mem_union_left
        exact ⟨hxE, hxF⟩
    have h_subadd : Lebesgue_outer_measure ((E \ F) ∪ (F \ K)) ≤ Lebesgue_outer_measure (E \ F) + Lebesgue_outer_measure (F \ K) := by
      let S' : Fin 2 → Set (EuclideanSpace' d) := ![E \ F, F \ K]
      have h_union : (E \ F) ∪ (F \ K) = ⋃ i : Fin 2, S' i := by ext x; simp [S']
      calc
        Lebesgue_outer_measure ((E \ F) ∪ (F \ K)) = Lebesgue_outer_measure (⋃ i : Fin 2, S' i) := by rw [h_union]
        _ ≤ ∑ i : Fin 2, Lebesgue_outer_measure (S' i) := Lebesgue_outer_measure.finite_union_le S'
        _ = Lebesgue_outer_measure (E \ F) + Lebesgue_outer_measure (F \ K) := by simp [S', Fin.sum_univ_two]
    have hK_fin : Lebesgue_outer_measure K < ⊤ := by
      have : K ⊆ F := by intro x hx; exact hx.1
      exact lt_of_le_of_lt (Lebesgue_outer_measure.mono this) hF_fin
    have hK_ne_top : Lebesgue_outer_measure K ≠ ⊤ := hK_fin.ne
    have hK_ne_bot : Lebesgue_outer_measure K ≠ ⊥ := by
      have h_nonneg' : 0 ≤ Lebesgue_outer_measure K := Lebesgue_outer_measure.nonneg _
      intro hbot; rw [hbot] at h_nonneg'; exact (EReal.bot_lt_zero.trans_le h_nonneg').ne rfl
    have h_FK_add : Lebesgue_measure K + Lebesgue_measure (F \ K) = Lebesgue_measure F := by
      have hball_meas : LebesgueMeasurable (Metric.closedBall (0 : EuclideanSpace' d) (N : ℝ)) :=
        Metric.isClosed_closedBall.measurable
      have hFK_meas : LebesgueMeasurable (F \ K) :=
        LebesgueMeasurable.inter hF_closed.measurable hball_meas.complement
      have h_union : K ∪ (F \ K) = F := by ext x; simp [K, Fseq]
      have h_disj : K ∩ (F \ K) = ∅ := by ext x; simp
      calc
        Lebesgue_measure K + Lebesgue_measure (F \ K) = Lebesgue_measure (K ∪ (F \ K)) :=
          (Lebesgue_measure.union (hFseq_meas N) hFK_meas h_disj).symm
        _ = Lebesgue_measure F := by rw [h_union]
    have hFK_bound : Lebesgue_outer_measure (F \ K) ≤ ((ε / 2 : ℝ) : EReal) := by
      have hFK_real : ∃ (s : ℝ), Lebesgue_outer_measure (F \ K) = (s : EReal) := by
        have hFK_fin : Lebesgue_outer_measure (F \ K) < ⊤ := by
          have : F \ K ⊆ F := Set.diff_subset
          exact lt_of_le_of_lt (Lebesgue_outer_measure.mono this) hF_fin
        have hFK_ne_top : Lebesgue_outer_measure (F \ K) ≠ ⊤ := hFK_fin.ne
        have hFK_ne_bot : Lebesgue_outer_measure (F \ K) ≠ ⊥ := by
          have h_nonneg' : 0 ≤ Lebesgue_outer_measure (F \ K) := Lebesgue_outer_measure.nonneg _
          intro hbot; rw [hbot] at h_nonneg'; exact (EReal.bot_lt_zero.trans_le h_nonneg').ne rfl
        have h_cases : Lebesgue_outer_measure (F \ K) = ⊥ ∨ (∃ r : ℝ, Lebesgue_outer_measure (F \ K) = (r : EReal)) ∨ Lebesgue_outer_measure (F \ K) = ⊤ := by
          match Lebesgue_outer_measure (F \ K) with
          | ⊥ => exact Or.inl rfl
          | (r : ℝ) => exact Or.inr (Or.inl ⟨r, rfl⟩)
          | ⊤ => exact Or.inr (Or.inr rfl)
        rcases h_cases with (hbot | hreal | htop)
        · exact (hFK_ne_bot hbot).elim
        · exact hreal
        · exact (hFK_ne_top htop).elim
      rcases hFK_real with ⟨s, hs⟩
      have hK_real : ∃ (r : ℝ), Lebesgue_outer_measure K = (r : EReal) := by
        have h_cases : Lebesgue_outer_measure K = ⊥ ∨ (∃ r : ℝ, Lebesgue_outer_measure K = (r : EReal)) ∨ Lebesgue_outer_measure K = ⊤ := by
          match Lebesgue_outer_measure K with
          | ⊥ => exact Or.inl rfl
          | (r : ℝ) => exact Or.inr (Or.inl ⟨r, rfl⟩)
          | ⊤ => exact Or.inr (Or.inr rfl)
        rcases h_cases with (hbot | hreal | htop)
        · exact (hK_ne_bot hbot).elim
        · exact hreal
        · exact (hK_ne_top htop).elim
      rcases hK_real with ⟨r, hr⟩
      have hF_real : ∃ (t : ℝ), Lebesgue_measure F = (t : EReal) := by
        have h_cases : Lebesgue_measure F = ⊥ ∨ (∃ t : ℝ, Lebesgue_measure F = (t : EReal)) ∨ Lebesgue_measure F = ⊤ := by
          match Lebesgue_measure F with
          | ⊥ => exact Or.inl rfl
          | (t : ℝ) => exact Or.inr (Or.inl ⟨t, rfl⟩)
          | ⊤ => exact Or.inr (Or.inr rfl)
        rcases h_cases with (hbot | hreal | htop)
        · exact (hF_not_bot hbot).elim
        · exact hreal
        · exact (hF_not_top htop).elim
      rcases hF_real with ⟨t, ht⟩
      have h_add_real : r + s = t := by
        calc
          (r : EReal) + (s : EReal) = Lebesgue_outer_measure K + Lebesgue_outer_measure (F \ K) := by rw [hr, hs]
          _ = Lebesgue_measure K + Lebesgue_measure (F \ K) := rfl
          _ = Lebesgue_measure F := h_FK_add
          _ = (t : EReal) := ht
        exact_mod_cast this
      have h_diff_real' : t - r < ε / 2 := by
        have hK_toReal : (Lebesgue_measure K).toReal = r := by
          have hK_not_top' : Lebesgue_measure K ≠ ⊤ := hK_ne_top
          have hK_not_bot' : Lebesgue_measure K ≠ ⊥ := hK_ne_bot
          simpa [hr, EReal.coe_toReal hK_not_top' hK_not_bot'] using rfl
        have hF_toReal : (Lebesgue_measure F).toReal = t := by
          simpa [ht, EReal.coe_toReal hFseqot_top hFseqot_bot] using rfl
        simpa [hK_toReal, hF_toReal] using h_diff_bound
      have : (s : EReal) ≤ ((ε / 2 : ℝ) : EReal) := by
        have : s = t - r := by linarith
        rw [this]
        have hle : (t - r : ℝ) ≤ ε / 2 := h_diff_real'.le
        exact_mod_cast hle
      rw [hs]; exact this
    calc
      Lebesgue_outer_measure (E \ K) ≤ Lebesgue_outer_measure ((E \ F) ∪ (F \ K)) := Lebesgue_outer_measure.mono h_sub
      _ ≤ Lebesgue_outer_measure (E \ F) + Lebesgue_outer_measure (F \ K) := h_subadd
      _ ≤ ((ε / 2 : ℝ) : EReal) + ((ε / 2 : ℝ) : EReal) := add_le_add hF_diff hFK_bound
      _ = ((ε : ℝ) : EReal) := by ring
  exact ⟨K, hK_compact, hK_sub_E, hK_diff⟩
