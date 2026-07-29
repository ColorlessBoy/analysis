import Analysis.MeasureTheory.Section_1_2_2

open Set
open Bornology

/-- If F₁, F₂ are bounded Lebesgue measurable sets, then their product is Lebesgue measurable.
    Uses inner approximation by closed sets and the TFAE characterization. -/
private lemma prod_of_bounded {d₁ d₂ : ℕ} {F₁ : Set (EuclideanSpace' d₁)} {F₂ : Set (EuclideanSpace' d₂)}
    (hF₁ : LebesgueMeasurable F₁) (hF₂ : LebesgueMeasurable F₂)
    (hF₁_bdd : Bornology.IsBounded F₁) (hF₂_bdd : Bornology.IsBounded F₂) :
    LebesgueMeasurable (EuclideanSpace'.prod F₁ F₂) := by
  -- bounded sets have finite outer measure
  have h_fin (F : Set (EuclideanSpace' _)) (h_bdd : Bornology.IsBounded F) : Lebesgue_outer_measure F ≠ ⊤ := by
    have h_compact : IsCompact (closure F) :=
      Metric.isCompact_of_isClosed_isBounded isClosed_closure h_bdd.closure
    have h_fin_closure : Lebesgue_outer_measure (closure F) ≠ ⊤ :=
      Lebesgue_outer_measure.finite_of_compact h_compact
    have h_mono : Lebesgue_outer_measure F ≤ Lebesgue_outer_measure (closure F) :=
      Lebesgue_outer_measure.mono subset_closure
    intro htop; apply h_fin_closure
    exact le_antisymm le_top (htop.symm ▸ h_mono)
  have hF₁_fin : Lebesgue_outer_measure F₁ ≠ ⊤ := h_fin F₁ hF₁_bdd
  have hF₂_fin : Lebesgue_outer_measure F₂ ≠ ⊤ := h_fin F₂ hF₂_bdd
  -- find real values of finite measures
  have get_real (hfin : Lebesgue_outer_measure (F : Set (EuclideanSpace' _)) ≠ ⊤) : ∃ r : ℝ, Lebesgue_outer_measure F = (r : EReal) := by
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
  rcases get_real hF₁_fin with ⟨r₁, hr₁⟩
  rcases get_real hF₂_fin with ⟨r₂, hr₂⟩
  have hr₁_nonneg : 0 ≤ r₁ := by
    have h : (0 : EReal) ≤ (r₁ : EReal) := by rw [← hr₁]; exact Lebesgue_outer_measure.nonneg F₁
    exact EReal.coe_nonneg.mp h
  have hr₂_nonneg : 0 ≤ r₂ := by
    have h : (0 : EReal) ≤ (r₂ : EReal) := by rw [← hr₂]; exact Lebesgue_outer_measure.nonneg F₂
    exact EReal.coe_nonneg.mp h
  -- Use TFAE(3→0): closed inner approximation ⇒ measurability
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
  -- choose δ₁, δ₂ so that δ₁ * r₂ + r₁ * δ₂ ≤ ε'
  set δ₁ := ε' / (2 * (r₂ + 1)) with hδ₁_def
  set δ₂ := ε' / (2 * (r₁ + 1)) with hδ₂_def
  have hδ₁_pos : 0 < δ₁ := div_pos hε'_pos (by nlinarith)
  have hδ₂_pos : 0 < δ₂ := div_pos hε'_pos (by nlinarith)
  have hδ₁_pos' : (0 : EReal) < (δ₁ : ℝ) := by exact_mod_cast hδ₁_pos
  have hδ₂_pos' : (0 : EReal) < (δ₂ : ℝ) := by exact_mod_cast hδ₂_pos
  -- closed inner approximation via TFAE(0→3)
  have h_closed_approx₁ : ∀ ε : EReal, (0 : EReal) < ε → ∃ (K : Set (EuclideanSpace' d₁)),
      IsClosed K ∧ K ⊆ F₁ ∧ Lebesgue_outer_measure (F₁ \ K) ≤ ε :=
    ((LebesgueMeasurable.TFAE F₁).out 0 3).mp hF₁
  have h_closed_approx₂ : ∀ ε : EReal, (0 : EReal) < ε → ∃ (K : Set (EuclideanSpace' d₂)),
      IsClosed K ∧ K ⊆ F₂ ∧ Lebesgue_outer_measure (F₂ \ K) ≤ ε :=
    ((LebesgueMeasurable.TFAE F₂).out 0 3).mp hF₂
  obtain ⟨K₁, hK₁_cl, hK₁_sub, hK₁_diff⟩ := h_closed_approx₁ ((δ₁ : ℝ) : EReal) hδ₁_pos'
  obtain ⟨K₂, hK₂_cl, hK₂_sub, hK₂_diff⟩ := h_closed_approx₂ ((δ₂ : ℝ) : EReal) hδ₂_pos'
  -- K₁×K₂ is closed (product of closed sets via homeomorphism)
  have h_prod_closed : IsClosed (EuclideanSpace'.prod K₁ K₂) := by
    have h_closed_prod : IsClosed (K₁ ×ˢ K₂ : Set (EuclideanSpace' d₁ × EuclideanSpace' d₂)) :=
      IsClosed.prod hK₁_cl hK₂_cl
    have h_homeo : Homeomorph (EuclideanSpace' d₁ × EuclideanSpace' d₂) (EuclideanSpace' (d₁ + d₂)) :=
      (EuclideanSpace'.prod_equiv d₁ d₂).symm.toHomeomorph
    have h_eq : EuclideanSpace'.prod K₁ K₂ = h_homeo '' (K₁ ×ˢ K₂) := rfl
    rw [h_eq]; exact h_closed_prod.image h_homeo
  have h_prod_sub : EuclideanSpace'.prod K₁ K₂ ⊆ P := by
    intro x hx
    rw [EuclideanSpace'.prod, Set.mem_image] at hx ⊢
    rcases hx with ⟨(a, b), ⟨ha, hb⟩, rfl⟩
    refine ⟨(a, b), ⟨hK₁_sub ha, hK₂_sub hb⟩, rfl⟩
  -- set difference identity
  have h_diff_eq : P \ (EuclideanSpace'.prod K₁ K₂) =
      EuclideanSpace'.prod (F₁ \ K₁) F₂ ∪ EuclideanSpace'.prod F₁ (F₂ \ K₂) := by
    ext x; constructor
    · intro ⟨hx_mem, hx_not⟩
      rw [EuclideanSpace'.prod, Set.mem_image] at hx_mem ⊢
      rcases hx_mem with ⟨(y₁, y₂), ⟨hy₁, hy₂⟩, hx_eq⟩
      by_cases hy₁K₁ : y₁ ∈ K₁
      · have hy₂_not_K₂ : y₂ ∉ K₂ := by
          intro h; apply hx_not; rw [EuclideanSpace'.prod, Set.mem_image]
          exact ⟨(y₁, y₂), ⟨hy₁K₁, h⟩, hx_eq⟩
        apply Set.mem_union_right; refine ⟨(y₁, y₂), ⟨hy₁, hy₂, hy₂_not_K₂⟩, hx_eq⟩
      · apply Set.mem_union_left; refine ⟨(y₁, y₂), ⟨hy₁, hy₁K₁, hy₂⟩, hx_eq⟩
    · intro hx
      rcases hx with (hx | hx)
      · rw [EuclideanSpace'.prod, Set.mem_image] at hx ⊢
        rcases hx with ⟨(y₁, y₂), ⟨⟨hy₁, hy₁_not⟩, hy₂⟩, hx_eq⟩
        refine ⟨(y₁, y₂), ⟨hy₁, hy₂⟩, hx_eq⟩
        intro h; rcases h with ⟨(z₁, z₂), ⟨hz₁K₁, hz₂K₂⟩, h_eq⟩
        apply hy₁_not; have h_eq' : (y₁, y₂) = (z₁, z₂) :=
          (EuclideanSpace'.prod_equiv d₁ d₂).symm.injective (hx_eq.trans h_eq.symm)
        rcases Prod.mk.inj h_eq' with ⟨rfl, rfl⟩; exact hz₁K₁
      · rw [EuclideanSpace'.prod, Set.mem_image] at hx ⊢
        rcases hx with ⟨(y₁, y₂), ⟨hy₁, hy₂, hy₂_not⟩, hx_eq⟩
        refine ⟨(y₁, y₂), ⟨hy₁, hy₂⟩, hx_eq⟩
        intro h; rcases h with ⟨(z₁, z₂), ⟨hz₁K₁, hz₂K₂⟩, h_eq⟩
        apply hy₂_not; have h_eq' : (y₁, y₂) = (z₁, z₂) :=
          (EuclideanSpace'.prod_equiv d₁ d₂).symm.injective (hx_eq.trans h_eq.symm)
        rcases Prod.mk.inj h_eq' with ⟨rfl, rfl⟩; exact hz₂K₂
  rw [h_diff_eq]
  -- bound the measure of the union
  have h_bound1 : Lebesgue_outer_measure (EuclideanSpace'.prod (F₁ \ K₁) F₂) ≤ (δ₁ * r₂ : ℝ) := by
    calc
      Lebesgue_outer_measure (EuclideanSpace'.prod (F₁ \ K₁) F₂) ≤
        Lebesgue_outer_measure (F₁ \ K₁) * Lebesgue_outer_measure F₂ :=
        Lebesgue_outer_measure.prod (E₁ := F₁ \ K₁) (E₂ := F₂)
      _ ≤ ((δ₁ : ℝ) : EReal) * (r₂ : EReal) := mul_le_mul hK₁_diff (by rw [hr₂])
        (Lebesgue_outer_measure.nonneg _) (by exact_mod_cast hδ₁_pos.le)
      _ = ((δ₁ * r₂ : ℝ) : EReal) := by simp
  have h_bound2 : Lebesgue_outer_measure (EuclideanSpace'.prod F₁ (F₂ \ K₂)) ≤ (r₁ * δ₂ : ℝ) := by
    calc
      Lebesgue_outer_measure (EuclideanSpace'.prod F₁ (F₂ \ K₂)) ≤
        Lebesgue_outer_measure F₁ * Lebesgue_outer_measure (F₂ \ K₂) :=
        Lebesgue_outer_measure.prod (E₁ := F₁) (E₂ := F₂ \ K₂)
      _ ≤ (r₁ : EReal) * ((δ₂ : ℝ) : EReal) := mul_le_mul (by rw [hr₁]) hK₂_diff
        (by exact_mod_cast hδ₂_pos.le) (Lebesgue_outer_measure.nonneg _)
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
          dsimp [δ₁]; calc
            (ε' / (2 * (r₂ + 1))) * r₂ = ε' * (r₂ / (2 * (r₂ + 1))) := by ring
            _ ≤ ε' * (1/2) := by
              have : r₂ / (2 * (r₂ + 1)) ≤ 1/2 := by
                have hpos : 0 < 2 * (r₂ + 1) := by nlinarith
                nlinarith
              nlinarith
            _ = ε' / 2 := by ring
        have h_ineq2 : r₁ * δ₂ ≤ ε' / 2 := by
          dsimp [δ₂]; calc
            r₁ * (ε' / (2 * (r₁ + 1))) = ε' * (r₁ / (2 * (r₁ + 1))) := by ring
            _ ≤ ε' * (1/2) := by
              have : r₁ / (2 * (r₁ + 1)) ≤ 1/2 := by
                have hpos : 0 < 2 * (r₁ + 1) := by nlinarith
                nlinarith
              nlinarith
            _ = ε' / 2 := by ring
        have h_eps_ineq : (δ₁ * r₂ : ℝ) + (r₁ * δ₂ : ℝ) ≤ (ε' : ℝ) := by nlinarith
        exact_mod_cast h_eps_ineq
  exact ⟨EuclideanSpace'.prod K₁ K₂, h_prod_closed, h_prod_sub, h_sum_bound⟩
