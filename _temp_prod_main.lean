import Analysis.MeasureTheory.Section_1_2_2

open Set Bornology

noncomputable def prod_equiv_symm_linear (d₁ d₂ : ℕ) : (EuclideanSpace' d₁ × EuclideanSpace' d₂) →ₗ[ℝ] EuclideanSpace' (d₁ + d₂) :=
  { toFun := (EuclideanSpace'.prod_equiv d₁ d₂).symm
    map_add' := by intro x y; ext i; simp [EuclideanSpace'.prod_equiv]; split_ifs <;> simp
    map_smul' := by intro r x; ext i; simp [EuclideanSpace'.prod_equiv]; split_ifs <;> simp
  }

noncomputable def prod_equiv_linear (d₁ d₂ : ℕ) : EuclideanSpace' (d₁ + d₂) →ₗ[ℝ] (EuclideanSpace' d₁ × EuclideanSpace' d₂) :=
  { toFun := EuclideanSpace'.prod_equiv d₁ d₂
    map_add' := by intro x y; ext i <;> simp [EuclideanSpace'.prod_equiv]
    map_smul' := by intro r x; ext i <;> simp [EuclideanSpace'.prod_equiv]
  }

private lemma h_cont_prod_equiv_symm (d₁ d₂ : ℕ) : Continuous (EuclideanSpace'.prod_equiv d₁ d₂).symm := by
  have h := LinearMap.continuous_of_finiteDimensional (prod_equiv_symm_linear d₁ d₂)
  simpa [prod_equiv_symm_linear] using h

private lemma prod_of_bounded {d₁ d₂ : ℕ} {F₁ : Set (EuclideanSpace' d₁)} {F₂ : Set (EuclideanSpace' d₂)}
    (hF₁ : LebesgueMeasurable F₁) (hF₂ : LebesgueMeasurable F₂)
    (hF₁_bdd : Bornology.IsBounded F₁) (hF₂_bdd : Bornology.IsBounded F₂) :
    LebesgueMeasurable (EuclideanSpace'.prod F₁ F₂) := by
  have hF₁_fin : Lebesgue_outer_measure F₁ ≠ ⊤ := by
    have h_compact : IsCompact (closure F₁) :=
      Metric.isCompact_of_isClosed_isBounded isClosed_closure hF₁_bdd.closure
    have h_fin_closure : Lebesgue_outer_measure (closure F₁) ≠ ⊤ :=
      Lebesgue_outer_measure.finite_of_compact h_compact
    have h_mono : Lebesgue_outer_measure F₁ ≤ Lebesgue_outer_measure (closure F₁) :=
      Lebesgue_outer_measure.mono subset_closure
    intro htop; apply h_fin_closure
    exact le_antisymm le_top (htop.symm ▸ h_mono)
  have hF₂_fin : Lebesgue_outer_measure F₂ ≠ ⊤ := by
    have h_compact : IsCompact (closure F₂) :=
      Metric.isCompact_of_isClosed_isBounded isClosed_closure hF₂_bdd.closure
    have h_fin_closure : Lebesgue_outer_measure (closure F₂) ≠ ⊤ :=
      Lebesgue_outer_measure.finite_of_compact h_compact
    have h_mono : Lebesgue_outer_measure F₂ ≤ Lebesgue_outer_measure (closure F₂) :=
      Lebesgue_outer_measure.mono subset_closure
    intro htop; apply h_fin_closure
    exact le_antisymm le_top (htop.symm ▸ h_mono)
  have get_real (d : ℕ) (F : Set (EuclideanSpace' d)) (hfin : Lebesgue_outer_measure F ≠ ⊤) : ∃ r : ℝ, Lebesgue_outer_measure F = (r : EReal) := by
    have h_nonneg : 0 ≤ Lebesgue_outer_measure F := Lebesgue_outer_measure.nonneg F
    have h_not_bot : Lebesgue_outer_measure F ≠ ⊥ := by
      intro hbot; rw [hbot] at h_nonneg; exact not_lt.mpr h_nonneg (by norm_num : (⊥ : EReal) < (0 : EReal))
    have h_cases : Lebesgue_outer_measure F = ⊥ ∨ (∃ r : ℝ, Lebesgue_outer_measure F = (r : EReal)) ∨ Lebesgue_outer_measure F = ⊤ := by
      refine match Lebesgue_outer_measure F with
      | ⊥ => Or.inl rfl | (r : ℝ) => Or.inr (Or.inl ⟨r, rfl⟩) | ⊤ => Or.inr (Or.inr rfl)
    rcases h_cases with (hbot | h | htop)
    · exact (h_not_bot hbot).elim
    · exact h
    · exact (hfin htop).elim
  rcases get_real d₁ F₁ hF₁_fin with ⟨r₁, hr₁⟩
  rcases get_real d₂ F₂ hF₂_fin with ⟨r₂, hr₂⟩
  have hr₁_nonneg : 0 ≤ r₁ := by
    have h : (0 : EReal) ≤ (r₁ : EReal) := by rw [← hr₁]; exact Lebesgue_outer_measure.nonneg F₁
    exact EReal.coe_nonneg.mp h
  have hr₂_nonneg : 0 ≤ r₂ := by
    have h : (0 : EReal) ≤ (r₂ : EReal) := by rw [← hr₂]; exact Lebesgue_outer_measure.nonneg F₂
    exact EReal.coe_nonneg.mp h
  let P := EuclideanSpace'.prod F₁ F₂
  have h_tfae := LebesgueMeasurable.TFAE P
  have h_30 : (∀ ε > 0, ∃ (F : Set (EuclideanSpace' (d₁ + d₂))), IsClosed F ∧ F ⊆ P ∧
      Lebesgue_outer_measure (P \ F) ≤ ε) → LebesgueMeasurable P :=
    (h_tfae.out 0 3).mpr
  refine h_30 ?_
  intro ε hε
  obtain ⟨ε', hε'_pos, hε'_le⟩ : ∃ ε' : ℝ, 0 < ε' ∧ (ε' : EReal) ≤ ε := by
    cases ε with
    | bot => exact absurd hε (not_lt.mpr bot_le)
    | top => exact ⟨1, one_pos, le_top⟩
    | coe r => exact ⟨r, EReal.coe_pos.mp hε, le_refl _⟩
  set δ₁ := ε' / (2 * (r₂ + 1)) with hδ₁_def
  set δ₂ := ε' / (2 * (r₁ + 1)) with hδ₂_def
  have hδ₁_pos : 0 < δ₁ := div_pos hε'_pos (by nlinarith)
  have hδ₂_pos : 0 < δ₂ := div_pos hε'_pos (by nlinarith)
  have hδ₁_pos' : (0 : EReal) < (δ₁ : ℝ) := by exact_mod_cast hδ₁_pos
  have hδ₂_pos' : (0 : EReal) < (δ₂ : ℝ) := by exact_mod_cast hδ₂_pos
  have h_closed_approx₁ : ∀ ε : EReal, (0 : EReal) < ε → ∃ (K : Set (EuclideanSpace' d₁)),
      IsClosed K ∧ K ⊆ F₁ ∧ Lebesgue_outer_measure (F₁ \ K) ≤ ε :=
    ((LebesgueMeasurable.TFAE F₁).out 0 3).mp hF₁
  have h_closed_approx₂ : ∀ ε : EReal, (0 : EReal) < ε → ∃ (K : Set (EuclideanSpace' d₂)),
      IsClosed K ∧ K ⊆ F₂ ∧ Lebesgue_outer_measure (F₂ \ K) ≤ ε :=
    ((LebesgueMeasurable.TFAE F₂).out 0 3).mp hF₂
  obtain ⟨K₁, hK₁_cl, hK₁_sub, hK₁_diff⟩ := h_closed_approx₁ ((δ₁ : ℝ) : EReal) hδ₁_pos'
  obtain ⟨K₂, hK₂_cl, hK₂_sub, hK₂_diff⟩ := h_closed_approx₂ ((δ₂ : ℝ) : EReal) hδ₂_pos'
  have hK₁_compact : IsCompact K₁ :=
    Metric.isCompact_of_isClosed_isBounded hK₁_cl (hF₁_bdd.subset hK₁_sub)
  have hK₂_compact : IsCompact K₂ :=
    Metric.isCompact_of_isClosed_isBounded hK₂_cl (hF₂_bdd.subset hK₂_sub)
  have h_prod_compact : IsCompact (K₁ ×ˢ K₂) := IsCompact.prod hK₁_compact hK₂_compact
  have h_image_compact : IsCompact (EuclideanSpace'.prod K₁ K₂) :=
    h_prod_compact.image (h_cont_prod_equiv_symm d₁ d₂)
  have h_prod_closed : IsClosed (EuclideanSpace'.prod K₁ K₂) := h_image_compact.isClosed
  have h_prod_sub : EuclideanSpace'.prod K₁ K₂ ⊆ P := by
    intro x hx
    dsimp [EuclideanSpace'.prod] at hx ⊢
    rcases hx with ⟨w, hw, hx_eq⟩; rcases w with ⟨a, b⟩; rcases hw with ⟨ha, hb⟩
    refine ⟨(a, b), ⟨hK₁_sub ha, hK₂_sub hb⟩, hx_eq⟩
  have h_set_diff : (F₁ ×ˢ F₂) \ (K₁ ×ˢ K₂) = ((F₁ \ K₁) ×ˢ F₂) ∪ (F₁ ×ˢ (F₂ \ K₂)) := by
    ext x; constructor
    · intro hx
      rcases hx with ⟨hx12, hx_not⟩
      rcases Set.mem_prod.1 hx12 with ⟨hx1, hx2⟩
      by_cases hxK₁ : x.1 ∈ K₁
      · have hx2_not_K₂ : x.2 ∉ K₂ := by
          intro hxK₂; apply hx_not; exact Set.mem_prod.mpr ⟨hxK₁, hxK₂⟩
        right; exact Set.mem_prod.mpr ⟨hx1, ⟨hx2, hx2_not_K₂⟩⟩
      · left; exact Set.mem_prod.mpr ⟨⟨hx1, hxK₁⟩, hx2⟩
    · intro hx
      rcases hx with (hx | hx)
      · rcases Set.mem_prod.1 hx with ⟨⟨hx1, hxK₁⟩, hx2⟩
        refine ⟨Set.mem_prod.mpr ⟨hx1, hx2⟩, ?_⟩
        intro hxK; exact hxK₁ hxK.1
      · rcases Set.mem_prod.1 hx with ⟨hx1, ⟨hx2, hxK₂⟩⟩
        refine ⟨Set.mem_prod.mpr ⟨hx1, hx2⟩, ?_⟩
        intro hxK; exact hxK₂ hxK.2
  have h_diff_eq : P \ (EuclideanSpace'.prod K₁ K₂) =
      EuclideanSpace'.prod (F₁ \ K₁) F₂ ∪ EuclideanSpace'.prod F₁ (F₂ \ K₂) := by
    calc
      P \ (EuclideanSpace'.prod K₁ K₂)
          = ((EuclideanSpace'.prod_equiv d₁ d₂).symm '' (F₁ ×ˢ F₂)) \ ((EuclideanSpace'.prod_equiv d₁ d₂).symm '' (K₁ ×ˢ K₂)) := rfl
      _ = (EuclideanSpace'.prod_equiv d₁ d₂).symm '' ((F₁ ×ˢ F₂) \ (K₁ ×ˢ K₂)) := by
        rw [Set.image_diff (EuclideanSpace'.prod_equiv d₁ d₂).symm.injective]
      _ = (EuclideanSpace'.prod_equiv d₁ d₂).symm '' (((F₁ \ K₁) ×ˢ F₂) ∪ (F₁ ×ˢ (F₂ \ K₂))) := by rw [h_set_diff]
      _ = EuclideanSpace'.prod (F₁ \ K₁) F₂ ∪ EuclideanSpace'.prod F₁ (F₂ \ K₂) := by
        simp [EuclideanSpace'.prod, Set.image_union]
  have h_bound1 : Lebesgue_outer_measure (EuclideanSpace'.prod (F₁ \ K₁) F₂) ≤ (δ₁ * r₂ : ℝ) := by
    calc
      Lebesgue_outer_measure (EuclideanSpace'.prod (F₁ \ K₁) F₂) ≤
        Lebesgue_outer_measure (F₁ \ K₁) * Lebesgue_outer_measure F₂ :=
        Lebesgue_outer_measure.prod (E₁ := F₁ \ K₁) (E₂ := F₂)
      _ ≤ ((δ₁ : ℝ) : EReal) * (r₂ : EReal) := by
        apply mul_le_mul hK₁_diff (by rw [hr₂])
          (Lebesgue_outer_measure.nonneg F₂) (by exact_mod_cast hδ₁_pos.le)
      _ = ((δ₁ * r₂ : ℝ) : EReal) := by simp
  have h_bound2 : Lebesgue_outer_measure (EuclideanSpace'.prod F₁ (F₂ \ K₂)) ≤ (r₁ * δ₂ : ℝ) := by
    calc
      Lebesgue_outer_measure (EuclideanSpace'.prod F₁ (F₂ \ K₂)) ≤
        Lebesgue_outer_measure F₁ * Lebesgue_outer_measure (F₂ \ K₂) :=
        Lebesgue_outer_measure.prod (E₁ := F₁) (E₂ := F₂ \ K₂)
      _ ≤ (r₁ : EReal) * ((δ₂ : ℝ) : EReal) := by
        apply mul_le_mul (by rw [hr₁]) hK₂_diff
          (Lebesgue_outer_measure.nonneg _) (by exact_mod_cast hr₁_nonneg)
      _ = ((r₁ * δ₂ : ℝ) : EReal) := by simp
  have h_sum_bound : Lebesgue_outer_measure
      (EuclideanSpace'.prod (F₁ \ K₁) F₂ ∪ EuclideanSpace'.prod F₁ (F₂ \ K₂)) ≤ (ε' : ℝ) := by
    have h_subadd : Lebesgue_outer_measure
        (EuclideanSpace'.prod (F₁ \ K₁) F₂ ∪ EuclideanSpace'.prod F₁ (F₂ \ K₂)) ≤
        Lebesgue_outer_measure (EuclideanSpace'.prod (F₁ \ K₁) F₂) +
        Lebesgue_outer_measure (EuclideanSpace'.prod F₁ (F₂ \ K₂)) := by
      let S : Fin 2 → Set (EuclideanSpace' (d₁ + d₂)) :=
        ![EuclideanSpace'.prod (F₁ \ K₁) F₂, EuclideanSpace'.prod F₁ (F₂ \ K₂)]
      have h_union : (EuclideanSpace'.prod (F₁ \ K₁) F₂) ∪ (EuclideanSpace'.prod F₁ (F₂ \ K₂)) = ⋃ i : Fin 2, S i := by
        ext x; simp [S]
      calc
        Lebesgue_outer_measure ((EuclideanSpace'.prod (F₁ \ K₁) F₂) ∪ (EuclideanSpace'.prod F₁ (F₂ \ K₂))) =
            Lebesgue_outer_measure (⋃ i : Fin 2, S i) := by rw [h_union]
        _ ≤ ∑ i : Fin 2, Lebesgue_outer_measure (S i) := Lebesgue_outer_measure.finite_union_le S
        _ = Lebesgue_outer_measure (EuclideanSpace'.prod (F₁ \ K₁) F₂) +
            Lebesgue_outer_measure (EuclideanSpace'.prod F₁ (F₂ \ K₂)) := by simp [S]
    calc
      Lebesgue_outer_measure (EuclideanSpace'.prod (F₁ \ K₁) F₂ ∪ EuclideanSpace'.prod F₁ (F₂ \ K₂)) ≤
        Lebesgue_outer_measure (EuclideanSpace'.prod (F₁ \ K₁) F₂) +
        Lebesgue_outer_measure (EuclideanSpace'.prod F₁ (F₂ \ K₂)) := h_subadd
      _ ≤ ((δ₁ * r₂ : ℝ) : EReal) + ((r₁ * δ₂ : ℝ) : EReal) := add_le_add h_bound1 h_bound2
      _ = ((δ₁ * r₂ + r₁ * δ₂ : ℝ) : EReal) := by simp
      _ ≤ (ε' : ℝ) := by
        have h_ineq1 : δ₁ * r₂ ≤ ε' / 2 := by
          dsimp [δ₁]
          have hnum : 2 * r₂ ≤ 2 * (r₂ + 1) := by nlinarith
          have h_ratio : r₂ / (2 * (r₂ + 1)) ≤ 1/2 := by
            calc
              r₂ / (2 * (r₂ + 1)) ≤ (r₂ + 1) / (2 * (r₂ + 1)) :=
                div_le_div_of_nonneg_right (by nlinarith) (by nlinarith)
              _ = 1/2 := by field_simp; ring
          calc
            (ε' / (2 * (r₂ + 1))) * r₂ = ε' * (r₂ / (2 * (r₂ + 1))) := by ring
            _ ≤ ε' * (1/2) := by gcongr
            _ = ε' / 2 := by ring
        have h_ineq2 : r₁ * δ₂ ≤ ε' / 2 := by
          dsimp [δ₂]
          have hnum : 2 * r₁ ≤ 2 * (r₁ + 1) := by nlinarith
          have h_ratio : r₁ / (2 * (r₁ + 1)) ≤ 1/2 := by
            calc
              r₁ / (2 * (r₁ + 1)) ≤ (r₁ + 1) / (2 * (r₁ + 1)) :=
                div_le_div_of_nonneg_right (by nlinarith) (by nlinarith)
              _ = 1/2 := by field_simp; ring
          calc
            r₁ * (ε' / (2 * (r₁ + 1))) = ε' * (r₁ / (2 * (r₁ + 1))) := by ring
            _ ≤ ε' * (1/2) := by gcongr
            _ = ε' / 2 := by ring
        have h_eps_ineq : (δ₁ * r₂ : ℝ) + (r₁ * δ₂ : ℝ) ≤ (ε' : ℝ) := by nlinarith
        exact_mod_cast h_eps_ineq
  have h_final : Lebesgue_outer_measure (P \ EuclideanSpace'.prod K₁ K₂) ≤ ε := by
    calc
      Lebesgue_outer_measure (P \ EuclideanSpace'.prod K₁ K₂)
          = Lebesgue_outer_measure (EuclideanSpace'.prod (F₁ \ K₁) F₂ ∪ EuclideanSpace'.prod F₁ (F₂ \ K₂)) := by rw [h_diff_eq]
      _ ≤ (ε' : ℝ) := h_sum_bound
      _ ≤ ε := hε'_le
  exact ⟨EuclideanSpace'.prod K₁ K₂, h_prod_closed, h_prod_sub, h_final⟩