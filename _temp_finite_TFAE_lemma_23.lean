import Analysis.MeasureTheory.Section_1_2_2

open Set

lemma finite_TFAE_2_implies_3 {d : ℕ} (E : Set (EuclideanSpace' d))
    (h2 : ∀ ε > 0, ∃ U : Set (EuclideanSpace' d), IsOpen U ∧ Bornology.IsBounded U ∧ Lebesgue_outer_measure (symmDiff U E) ≤ ε) :
    ∀ ε > 0, ∃ F : Set (EuclideanSpace' d), IsCompact F ∧ F ⊆ E ∧ Lebesgue_outer_measure (E \ F) ≤ ε := by
  -- From h2, E is Lebesgue measurable (using standard TFAE)
  have hE_meas : LebesgueMeasurable E := by
    have h_symm_approx : ∀ ε > 0, ∃ U : Set (EuclideanSpace' d), IsOpen U ∧ Lebesgue_outer_measure (symmDiff U E) ≤ ε := by
      intro ε hε
      rcases h2 ε hε with ⟨U, hU_open, hU_bdd, h_symm⟩
      exact ⟨U, hU_open, h_symm⟩
    exact ((LebesgueMeasurable.TFAE E).out 2 0).mp h_symm_approx

  intro ε hε
  by_cases hε_top : ε = ⊤
  ·     subst hε_top; refine ⟨∅, isCompact_empty, Set.empty_subset _, ?_⟩; simp; exact le_top
  have hε_real : ∃ r : ℝ, 0 < r ∧ (r : EReal) = ε := by
    cases ε with
    | bot => exact absurd hε (not_lt.mpr bot_le)
    | top => exact (hε_top rfl).elim
    | coe r => exact ⟨r, EReal.coe_pos.mp hε, rfl⟩
  rcases hε_real with ⟨r, hr_pos, hr_eq⟩; subst hr_eq
  have hr2_pos : (r / 2 : ℝ) > 0 := by linarith
  have h_hr2_pos : (0 : EReal) < (r / 2 : ℝ) := EReal.coe_pos.mpr hr2_pos
  rcases h2 ((r / 2 : ℝ) : EReal) h_hr2_pos with ⟨U, hU_open, hU_bdd, h_symm⟩

  -- From h_symm: m*(symmDiff U E) ≤ r/2, so m*(E\U) ≤ r/2
  have h_EU_sub : E \ U ⊆ symmDiff U E := by rw [symmDiff_def]; simp
  have h_EU_bound : Lebesgue_outer_measure (E \ U) ≤ (r / 2 : ℝ) :=
    le_trans (Lebesgue_outer_measure.mono h_EU_sub) h_symm

  -- From standard TFAE (3), E measurable gives closed F ⊆ E with m*(E\F) ≤ r/2
  have h_closed_approx : ∀ ε > 0, ∃ F : Set (EuclideanSpace' d), IsClosed F ∧ F ⊆ E ∧ Lebesgue_outer_measure (E \ F) ≤ ε :=
    ((LebesgueMeasurable.TFAE E).out 0 3).mp hE_meas
  rcases h_closed_approx ((r / 2 : ℝ) : EReal) h_hr2_pos with ⟨F, hF_closed, hF_sub_E, hF_diff⟩

  -- closure(U) is compact (bounded closed in ℝ^d)
  have h_closure_compact : IsCompact (closure U) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure hU_bdd.closure

  -- K = closure(U) ∩ F is compact and ⊆ E
  let K := closure U ∩ F
  have hK_closed : IsClosed K := IsClosed.inter isClosed_closure hF_closed
  have hK_bounded : Bornology.IsBounded K := hU_bdd.closure.subset Set.inter_subset_left
  have hK_compact : IsCompact K := Metric.isCompact_of_isClosed_isBounded hK_closed hK_bounded
  have hK_sub_E : K ⊆ E := Set.Subset.trans (Set.inter_subset_right) hF_sub_E

  -- E \ K ⊆ (E \ U) ∪ (E \ F) (since closure U ⊇ U)
  have h_diff_sub : E \ K ⊆ (E \ U) ∪ (E \ F) := by
    intro x hx
    rcases hx with ⟨hxE, hxK⟩
    have hx_not_in : x ∉ closure U ∨ x ∉ F := by
      by_cases hx_closure : x ∈ closure U
      · right; intro hxF; apply hxK; exact ⟨hx_closure, hxF⟩
      · left; exact hx_closure
    rcases hx_not_in with (hx_not_closure | hx_not_F)
    · have hx_not_U : x ∉ U := mt (fun hxU : x ∈ U => subset_closure hxU) hx_not_closure
      apply Set.mem_union_left
      exact ⟨hxE, hx_not_U⟩
    · apply Set.mem_union_right
      exact ⟨hxE, hx_not_F⟩

  have hK_bound : Lebesgue_outer_measure (E \ K) ≤ (r : ℝ) := by
    have h_subadd : Lebesgue_outer_measure ((E \ U) ∪ (E \ F)) ≤
        Lebesgue_outer_measure (E \ U) + Lebesgue_outer_measure (E \ F) := by
      let S : Fin 2 → Set (EuclideanSpace' d) := ![E \ U, E \ F]
      have h_union : ⋃ i : Fin 2, S i = (E \ U) ∪ (E \ F) := by ext x; simp [S]
      calc
        Lebesgue_outer_measure ((E \ U) ∪ (E \ F)) = Lebesgue_outer_measure (⋃ i : Fin 2, S i) := by rw [h_union]
        _ ≤ ∑ i : Fin 2, Lebesgue_outer_measure (S i) := Lebesgue_outer_measure.finite_union_le S
        _ = Lebesgue_outer_measure (E \ U) + Lebesgue_outer_measure (E \ F) := by simp [S, Fin.sum_univ_two]
    calc
      Lebesgue_outer_measure (E \ K) ≤ Lebesgue_outer_measure ((E \ U) ∪ (E \ F)) :=
        Lebesgue_outer_measure.mono h_diff_sub
      _ ≤ Lebesgue_outer_measure (E \ U) + Lebesgue_outer_measure (E \ F) := h_subadd
      _ ≤ ((r / 2 : ℝ) : EReal) + ((r / 2 : ℝ) : EReal) := add_le_add h_EU_bound hF_diff
      _ = ((r : ℝ) : EReal) := by
        calc
          ((r / 2 : ℝ) : EReal) + ((r / 2 : ℝ) : EReal) = ((r / 2 + r / 2 : ℝ) : EReal) := by rw [EReal.coe_add]
          _ = (r : EReal) := by
            have h : (r / 2 : ℝ) + (r / 2 : ℝ) = r := by ring
            rw [h]

  exact ⟨K, hK_compact, hK_sub_E, hK_bound⟩
