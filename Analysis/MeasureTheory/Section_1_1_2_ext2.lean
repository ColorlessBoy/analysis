import Analysis.MeasureTheory.Section_1_1_2_ext

set_option maxHeartbeats 0

open Pointwise

/-
Exercise 1.1.14

Jordan measurability is characterized by convergence of scaled dyadic metric entropy difference to zero.
-/
theorem JordanMeasure.iff {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E) :
  JordanMeasurable E ↔ Filter.atTop.Tendsto (fun n ↦ (2:ℝ)^(-(d*n:ℤ)) * ((metric_entropy_upper E n - metric_entropy_lower E n))) (nhds 0) := by
    constructor <;> intro h;
    · convert Filter.Tendsto.sub ( metric_entropy_upper_tendsto hE ) ( metric_entropy_lower_tendsto hE ) using 2 ; ring;
      rw [ h.2, sub_self ];
    · refine' ⟨ hE, _ ⟩;
      linarith [ tendsto_nhds_unique ( by simpa [ mul_sub ] using Filter.Tendsto.sub ( metric_entropy_upper_tendsto hE ) ( metric_entropy_lower_tendsto hE ) ) h ]

/-
Jordan measure equals the limit of scaled lower metric entropy.
-/
theorem JordanMeasure.eq_lim_lower {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: JordanMeasurable E) :
   Filter.atTop.Tendsto (fun n ↦ (2:ℝ)^(-(d*n:ℤ)) * (metric_entropy_lower E n)) (nhds hE.measure) := by
     convert metric_entropy_lower_tendsto hE.1 using 1

/-
Jordan measure equals the limit of scaled upper metric entropy.
-/
theorem JordanMeasure.eq_lim_upper {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: JordanMeasurable E) :
   Filter.atTop.Tendsto (fun n ↦ (2:ℝ)^(-(d*n:ℤ)) * (metric_entropy_upper E n)) (nhds hE.measure) := by
     have := @JordanMeasure.iff d E ?_;
     · convert Filter.Tendsto.add ( this.mp hE ) ( JordanMeasure.eq_lim_lower hE ) using 2 <;> ring;
     · grind +qlia

/-- Exercise 1.1.15 (Uniqueness of Jordan measure) -/
theorem JordanMeasure.measure_uniq {d:ℕ} {m': (E: Set (EuclideanSpace' d)) → (JordanMeasurable E) → ℝ}
  (hnonneg: ∀ E: Set (EuclideanSpace' d), ∀ hE: JordanMeasurable E, m' E hE ≥ 0)
  (hadd: ∀ E F: Set (EuclideanSpace' d), ∀ (hE: JordanMeasurable E) (hF: JordanMeasurable F),
   Disjoint E F → m' (E ∪ F) (hE.union hF) = m' E hE + m' F hF)
  (htrans: ∀ E: Set (EuclideanSpace' d), ∀ (hE: JordanMeasurable E) (x: EuclideanSpace' d), m' (E + {x}) (hE.translate x) = m' E hE) : ∃ c, c ≥ 0 ∧ ∀ E: Set (EuclideanSpace' d), ∀ hE: JordanMeasurable E, m' E hE = c * hE.measure := by
  classical
  have h_pi : ∀ (E : Set (EuclideanSpace' d)) (h1 h2 : JordanMeasurable E), m' E h1 = m' E h2 := by
    intro E h1 h2
    have hm1 := hadd E (∅ : Set (EuclideanSpace' d)) h1 (JordanMeasurable.empty d) (by simp)
    have hm2 := hadd E (∅ : Set (EuclideanSpace' d)) h2 (JordanMeasurable.empty d) (by simp)
    have h_eq : h1.union (JordanMeasurable.empty d) = h2.union (JordanMeasurable.empty d) := by
      apply Subsingleton.elim
    have hL : m' (E ∪ ∅) (h1.union (JordanMeasurable.empty d)) = m' (E ∪ ∅) (h2.union (JordanMeasurable.empty d)) := by
      rw [h_eq]
    linarith
  let μ (E : Set (EuclideanSpace' d)) : ℝ :=
    if h : JordanMeasurable E then m' E h else 0
  have hμ_nonneg : ∀ E, 0 ≤ μ E := by
    intro E; dsimp [μ]
    by_cases h : JordanMeasurable E
    · rw [dif_pos h]; exact hnonneg E h
    · simp [h]
  have hμ_add : ∀ (E F : Set (EuclideanSpace' d)), Disjoint E F → JordanMeasurable E → JordanMeasurable F →
      μ (E ∪ F) = μ E + μ F := by
    intro E F hdisj hE_J hF_J
    dsimp [μ]
    have hunion_J : JordanMeasurable (E ∪ F) := hE_J.union hF_J
    have h_add := hadd E F hE_J hF_J hdisj
    have h_pi_union : m' (E ∪ F) hunion_J = m' (E ∪ F) (hE_J.union hF_J) := h_pi (E ∪ F) hunion_J (hE_J.union hF_J)
    rw [dif_pos hunion_J, dif_pos hE_J, dif_pos hF_J, h_pi_union, h_add]
  have hμ_trans : ∀ (E : Set (EuclideanSpace' d)) (x : EuclideanSpace' d), JordanMeasurable E → μ (E + {x}) = μ E := by
    intro E x hE_J
    dsimp [μ]
    have htrans_J : JordanMeasurable (E + {x}) := hE_J.translate x
    rw [dif_pos htrans_J, dif_pos hE_J, h_pi (E + {x}) htrans_J (hE_J.translate x), htrans E hE_J x]
  set c := μ (Box.unit_cube d).toSet with hc_def
  have hc_nonneg : 0 ≤ c := hμ_nonneg _
  have h_μ_via_m' : ∀ (E : Set (EuclideanSpace' d)) (hE : JordanMeasurable E), μ E = m' E hE := by
    intro E hE; dsimp [μ]; simp [hE, h_pi E _ hE]
  let μ_elem (E : Set (EuclideanSpace' d)) (_ : IsElementary E) : ℝ := μ E
  have hμ_elem_nonneg : ∀ E (hE_elem : IsElementary E), μ_elem E hE_elem ≥ 0 := by
    intro E _; exact hμ_nonneg E
  have hμ_elem_add : ∀ E F (hE_elem : IsElementary E) (hF_elem : IsElementary F), Disjoint E F →
      μ_elem (E ∪ F) (hE_elem.union hF_elem) = μ_elem E hE_elem + μ_elem F hF_elem := by
    intro E F hE_elem hF_elem hdisj
    dsimp [μ_elem]
    exact hμ_add E F hdisj hE_elem.jordanMeasurable hF_elem.jordanMeasurable
  have hμ_elem_trans : ∀ E (hE_elem : IsElementary E) (x : EuclideanSpace' d),
      μ_elem (E + {x}) (hE_elem.translate x) = μ_elem E hE_elem := by
    intro E hE_elem x
    dsimp [μ_elem]
    exact hμ_trans E x hE_elem.jordanMeasurable
  obtain ⟨c', hc'_nonneg, hc'_eq⟩ :=
    IsElementary.measure_uniq (m' := μ_elem) hμ_elem_nonneg hμ_elem_add hμ_elem_trans
  have h_cube_val : μ (Box.unit_cube d).toSet = c' := by
    calc
      μ (Box.unit_cube d).toSet = μ_elem (Box.unit_cube d).toSet (IsElementary.box (Box.unit_cube d)) := rfl
      _ = c' * (IsElementary.box (Box.unit_cube d)).measure := hc'_eq _ _
      _ = c' * 1 := by simp [IsElementary.measure_of_box, Box.volume, Box.unit_cube, BoundedInterval.length]
      _ = c' := by ring
  have hc'_eq_c : c' = c := by
    calc
      c' = μ (Box.unit_cube d).toSet := by symm; exact h_cube_val
      _ = c := by symm; exact hc_def
  have hμ_eq : ∀ (E : Set (EuclideanSpace' d)) (hE_J : JordanMeasurable E), μ E = c' * hE_J.measure := by
    intro E hE_J
    have h_tfae := (JordanMeasurable.equiv hE_J.1).out 0 1
    have h_cond1 : ∀ ε > 0, ∃ (A B : Set (EuclideanSpace' d)) (hA : IsElementary A) (hB : IsElementary B),
      A ⊆ E ∧ E ⊆ B ∧ (hB.sdiff hA).measure ≤ ε := h_tfae.mp hE_J
    apply le_antisymm
    · apply le_of_forall_pos_le_add
      intro δ hδ
      have hε_pos : 0 < δ / (c' + 1) := div_pos hδ (by nlinarith [hc'_nonneg])
      obtain ⟨A, B, hA, hB, hA_sub, hB_sub, h_diff⟩ := h_cond1 (δ / (c' + 1)) hε_pos
      have hA_elem : IsElementary A := hA
      have hB_elem : IsElementary B := hB
      have hA_val : μ A = c' * hA_elem.measure := by
        simpa [μ_elem] using hc'_eq A hA_elem
      have hB_val : μ B = c' * hB_elem.measure := by
        simpa [μ_elem] using hc'_eq B hB_elem
      have hAE : μ A ≤ μ E := by
        have hA_J : JordanMeasurable A := hA_elem.jordanMeasurable
        have h_sdiff : JordanMeasurable (E \ A) := hE_J.sdiff hA_J
        have h_disj : Disjoint A (E \ A) := disjoint_sdiff_self_right
        have h_union_eq : A ∪ (E \ A) = E := Set.union_diff_cancel hA_sub
        have h_add := hμ_add A (E \ A) h_disj hA_J h_sdiff
        rw [h_union_eq] at h_add
        rw [h_add]
        nlinarith [hμ_nonneg (E \ A)]
      have hEB : μ E ≤ μ B := by
        have h_sdiff : JordanMeasurable (B \ E) := hB_elem.jordanMeasurable.sdiff hE_J
        have h_disj : Disjoint E (B \ E) := disjoint_sdiff_self_right
        have h_union_eq : E ∪ (B \ E) = B := Set.union_diff_cancel hB_sub
        have h_add := hμ_add E (B \ E) h_disj hE_J h_sdiff
        rw [h_union_eq] at h_add
        rw [h_add]
        nlinarith [hμ_nonneg (B \ E)]
      have h_meas_A_le : hA_elem.measure ≤ hE_J.measure := by
        calc
          hA_elem.measure = Jordan_inner_measure A :=
            (JordanMeasurable.mes_of_elementary hA_elem).symm
          _ ≤ Jordan_inner_measure E := Jordan_inner_measure_mono hA_sub hE_J.1
          _ = hE_J.measure := rfl
      have h_diff_meas : hB_elem.measure - hA_elem.measure ≤ δ / (c' + 1) := by
        have h_eq : hB_elem.measure = hA_elem.measure + (hB_elem.sdiff hA_elem).measure := by
          have h_union_eq' : A ∪ (B \ A) = B := Set.union_diff_cancel (Set.Subset.trans hA_sub hB_sub)
          have h_disj' : Disjoint A (B \ A) := disjoint_sdiff_self_right
          have h_same_measure : (hA_elem.union (hB_elem.sdiff hA_elem)).measure = hB_elem.measure :=
            IsElementary.measure_eq_of_set_eq (hA_elem.union (hB_elem.sdiff hA_elem)) hB_elem h_union_eq'
          calc
            hB_elem.measure = (hA_elem.union (hB_elem.sdiff hA_elem)).measure := by symm; exact h_same_measure
            _ = hA_elem.measure + (hB_elem.sdiff hA_elem).measure :=
              IsElementary.measure_of_disjUnion hA_elem (hB_elem.sdiff hA_elem) h_disj'
        rw [h_eq]
        have : (hA_elem.measure + (hB_elem.sdiff hA_elem).measure) - hA_elem.measure = (hB_elem.sdiff hA_elem).measure := by ring
        rw [this]
        exact h_diff
      have h_bound : μ E - c' * hE_J.measure < δ := by
        have h1 : μ E - c' * hE_J.measure ≤ μ B - c' * hA_elem.measure := by nlinarith
        have h2 : μ B - c' * hA_elem.measure = c' * (hB_elem.measure - hA_elem.measure) := by
          rw [hB_val]; ring
        have h3 : c' * (hB_elem.measure - hA_elem.measure) ≤ c' * (δ / (c' + 1)) := by nlinarith
        have h4 : c' * (δ / (c' + 1)) < δ := by
          have hpos : 0 < c' + 1 := by nlinarith
          calc
            c' * (δ / (c' + 1)) = (c' / (c' + 1)) * δ := by ring
            _ < 1 * δ := mul_lt_mul_of_pos_right (by
              have : c' / (c' + 1) < 1 := by
                refine (div_lt_one ?_).mpr ?_
                · nlinarith
                · nlinarith
              exact this) hδ
            _ = δ := by simp
        nlinarith
      nlinarith
    · apply le_of_forall_pos_le_add
      intro δ hδ
      have hε_pos : 0 < δ / (c' + 1) := div_pos hδ (by nlinarith [hc'_nonneg])
      obtain ⟨A, B, hA, hB, hA_sub, hB_sub, h_diff⟩ := h_cond1 (δ / (c' + 1)) hε_pos
      have hA_elem : IsElementary A := hA
      have hB_elem : IsElementary B := hB
      have hA_val : μ A = c' * hA_elem.measure := by
        simpa [μ_elem] using hc'_eq A hA_elem
      have hB_val : μ B = c' * hB_elem.measure := by
        simpa [μ_elem] using hc'_eq B hB_elem
      have hAE : μ A ≤ μ E := by
        have hA_J : JordanMeasurable A := hA_elem.jordanMeasurable
        have h_sdiff : JordanMeasurable (E \ A) := hE_J.sdiff hA_J
        have h_disj : Disjoint A (E \ A) := disjoint_sdiff_self_right
        have h_union_eq : A ∪ (E \ A) = E := Set.union_diff_cancel hA_sub
        have h_add := hμ_add A (E \ A) h_disj hA_J h_sdiff
        rw [h_union_eq] at h_add
        rw [h_add]
        nlinarith [hμ_nonneg (E \ A)]
      have hEB : μ E ≤ μ B := by
        have h_sdiff : JordanMeasurable (B \ E) := hB_elem.jordanMeasurable.sdiff hE_J
        have h_disj : Disjoint E (B \ E) := disjoint_sdiff_self_right
        have h_union_eq : E ∪ (B \ E) = B := Set.union_diff_cancel hB_sub
        have h_add := hμ_add E (B \ E) h_disj hE_J h_sdiff
        rw [h_union_eq] at h_add
        rw [h_add]
        nlinarith [hμ_nonneg (B \ E)]
      have h_meas_E_le : hE_J.measure ≤ hB_elem.measure := by
        calc
          hE_J.measure = Jordan_outer_measure E := hE_J.eq_outer
          _ ≤ Jordan_outer_measure B := Jordan_outer_measure_mono_of_subset hB_sub hB_elem.isBounded
          _ = Jordan_inner_measure B := ((hB_elem.jordanMeasurable).2).symm
          _ = hB_elem.measure := JordanMeasurable.mes_of_elementary hB_elem
      have h_diff_meas : hB_elem.measure - hA_elem.measure ≤ δ / (c' + 1) := by
        have h_eq : hB_elem.measure = hA_elem.measure + (hB_elem.sdiff hA_elem).measure := by
          have h_union_eq' : A ∪ (B \ A) = B := Set.union_diff_cancel (Set.Subset.trans hA_sub hB_sub)
          have h_disj' : Disjoint A (B \ A) := disjoint_sdiff_self_right
          have h_same_measure : (hA_elem.union (hB_elem.sdiff hA_elem)).measure = hB_elem.measure :=
            IsElementary.measure_eq_of_set_eq (hA_elem.union (hB_elem.sdiff hA_elem)) hB_elem h_union_eq'
          calc
            hB_elem.measure = (hA_elem.union (hB_elem.sdiff hA_elem)).measure := by symm; exact h_same_measure
            _ = hA_elem.measure + (hB_elem.sdiff hA_elem).measure :=
              IsElementary.measure_of_disjUnion hA_elem (hB_elem.sdiff hA_elem) h_disj'
        rw [h_eq]
        have : (hA_elem.measure + (hB_elem.sdiff hA_elem).measure) - hA_elem.measure = (hB_elem.sdiff hA_elem).measure := by ring
        rw [this]
        exact h_diff
      have h_bound : c' * hE_J.measure - μ E < δ := by
        have h1 : c' * hE_J.measure - μ E ≤ c' * hB_elem.measure - μ A := by nlinarith
        have h2 : c' * hB_elem.measure - μ A = c' * (hB_elem.measure - hA_elem.measure) := by
          rw [hA_val]; ring
        have h3 : c' * (hB_elem.measure - hA_elem.measure) ≤ c' * (δ / (c' + 1)) := by nlinarith
        have h4 : c' * (δ / (c' + 1)) < δ := by
          have hpos : 0 < c' + 1 := by nlinarith
          calc
            c' * (δ / (c' + 1)) = (c' / (c' + 1)) * δ := by ring
            _ < 1 * δ := mul_lt_mul_of_pos_right (by
              have : c' / (c' + 1) < 1 := by
                refine (div_lt_one ?_).mpr ?_
                · nlinarith
                · nlinarith
              exact this) hδ
            _ = δ := by simp
        nlinarith
      nlinarith
  refine ⟨c, hc_nonneg, ?_⟩
  intro E hE
  calc
    m' E hE = μ E := by symm; exact h_μ_via_m' E hE
    _ = c' * hE.measure := hμ_eq E hE
    _ = c * hE.measure := by rw [hc'_eq_c]

/-- With unit cube normalization, the unique such function equals Jordan measure. -/
theorem JordanMeasure.measure_uniq' {d:ℕ} {m': (E: Set (EuclideanSpace' d)) → (JordanMeasurable E) → ℝ}
  (hnonneg: ∀ E: Set (EuclideanSpace' d), ∀ hE: JordanMeasurable E, m' E hE ≥ 0)
  (hadd: ∀ E F: Set (EuclideanSpace' d), ∀ (hE: JordanMeasurable E) (hF: JordanMeasurable F),
   Disjoint E F → m' (E ∪ F) (hE.union hF) = m' E hE + m' F hF)
  (htrans: ∀ E: Set (EuclideanSpace' d), ∀ (hE: JordanMeasurable E) (x: EuclideanSpace' d), m' (E + {x}) (hE.translate x) = m' E hE)
  (hcube : m' (Box.unit_cube d) (IsElementary.box _).jordanMeasurable = 1) :
  ∀ E: Set (EuclideanSpace' d), ∀ hE: JordanMeasurable E, m' E hE = hE.measure := by
  have h_uniq := JordanMeasure.measure_uniq (m' := m') hnonneg hadd htrans
  rcases h_uniq with ⟨c, hc_nonneg, hc_eq⟩
  have hc_one : c = 1 := by
    have h_cube_measure : (IsElementary.box (Box.unit_cube d)).jordanMeasurable.measure = 1 := by
      rw [JordanMeasurable.mes_of_elementary (IsElementary.box (Box.unit_cube d)),
        IsElementary.measure_of_box (Box.unit_cube d), Box.volume]
      simp [BoundedInterval.length]
    calc
      c = c * ((IsElementary.box (Box.unit_cube d)).jordanMeasurable.measure) := by
        simp [h_cube_measure]
      _ = m' (Box.unit_cube d) ((IsElementary.box (Box.unit_cube d)).jordanMeasurable) :=
        (hc_eq (Box.unit_cube d) ((IsElementary.box (Box.unit_cube d)).jordanMeasurable)).symm
      _ = 1 := hcube
  intro E hE
  calc
    m' E hE = c * hE.measure := hc_eq E hE
    _ = 1 * hE.measure := by rw [hc_one]
    _ = hE.measure := by simp


/-- Exercise 1.1.16 -/
theorem JordanMeasurable.prod {d₁ d₂:ℕ} {E₁: Set (EuclideanSpace' d₁)} {E₂: Set (EuclideanSpace' d₂)}
  (hE₁: JordanMeasurable E₁) (hE₂: JordanMeasurable E₂) : JordanMeasurable (EuclideanSpace'.prod E₁ E₂) := by
  have hb₁ : Bornology.IsBounded E₁ := hE₁.1
  have hb₂ : Bornology.IsBounded E₂ := hE₂.1
  obtain ⟨B₁₀, hB₁₀, hB₁₀_sup⟩ := IsElementary.contains_bounded hb₁
  obtain ⟨B₂₀, hB₂₀, hB₂₀_sup⟩ := IsElementary.contains_bounded hb₂
  have hb_prod : Bornology.IsBounded (EuclideanSpace'.prod E₁ E₂) := by
    have h_prod_elem : IsElementary (EuclideanSpace'.prod B₁₀ B₂₀) := IsElementary.prod hB₁₀ hB₂₀
    have h_sub : EuclideanSpace'.prod E₁ E₂ ⊆ EuclideanSpace'.prod B₁₀ B₂₀ := by
      dsimp [EuclideanSpace'.prod]
      apply Set.image_mono
      exact Set.prod_mono hB₁₀_sup hB₂₀_sup
    exact h_prod_elem.isBounded.subset h_sub
  set M₁ := hB₁₀.measure with hM₁
  set M₂ := hB₂₀.measure with hM₂
  have hM₁_nonneg : 0 ≤ M₁ := IsElementary.measure_nonneg hB₁₀
  have hM₂_nonneg : 0 ≤ M₂ := IsElementary.measure_nonneg hB₂₀
  have h_approx : ∀ ε > 0, ∃ A B : Set (EuclideanSpace' (d₁ + d₂)), ∃ hA : IsElementary A, ∃ hB : IsElementary B,
      A ⊆ EuclideanSpace'.prod E₁ E₂ ∧ EuclideanSpace'.prod E₁ E₂ ⊆ B ∧ (hB.sdiff hA).measure ≤ ε := by
    intro ε hε
    set ε₁ := ε / (2*(M₂ + 1)) with hε₁_def
    set ε₂ := ε / (2*(M₁ + 1)) with hε₂_def
    have hε₁_pos : ε₁ > 0 := by
      dsimp [ε₁]
      refine div_pos hε ?_
      nlinarith
    have hε₂_pos : ε₂ > 0 := by
      dsimp [ε₂]
      refine div_pos hε ?_
      nlinarith
    have h_approx₁ : ∃ A₁ B₁ : Set (EuclideanSpace' d₁), ∃ hA₁ : IsElementary A₁, ∃ hB₁ : IsElementary B₁,
      A₁ ⊆ E₁ ∧ E₁ ⊆ B₁ ∧ (hB₁.sdiff hA₁).measure ≤ ε₁ := by
      have := (JordanMeasurable.equiv hb₁).out 0 1; simp_all only [gt_iff_lt, exists_and_left, implies_true,
        iff_true, div_pos_iff_of_pos_left]
    rcases h_approx₁ with ⟨A₁, B₁, hA₁, hB₁, hA₁_sub, hB₁_sup, h_diff₁⟩
    have h_approx₂ : ∃ A₂ B₂ : Set (EuclideanSpace' d₂), ∃ hA₂ : IsElementary A₂, ∃ hB₂ : IsElementary B₂,
      A₂ ⊆ E₂ ∧ E₂ ⊆ B₂ ∧ (hB₂.sdiff hA₂).measure ≤ ε₂ := by
      have := (JordanMeasurable.equiv hb₂).out 0 1; simp_all only [gt_iff_lt, exists_and_left, implies_true,
        iff_true, div_pos_iff_of_pos_left]
    rcases h_approx₂ with ⟨A₂, B₂, hA₂, hB₂, hA₂_sub, hB₂_sup, h_diff₂⟩
    set B₁' := B₁ ∩ B₁₀ with hB₁'_def
    set B₂' := B₂ ∩ B₂₀ with hB₂'_def
    have hB₁'_elem : IsElementary B₁' := IsElementary.inter hB₁ hB₁₀
    have hB₂'_elem : IsElementary B₂' := IsElementary.inter hB₂ hB₂₀
    have hB₁'_sup : E₁ ⊆ B₁' := by
      simpa [hB₁'_def] using Set.subset_inter hB₁_sup hB₁₀_sup
    have hB₂'_sup : E₂ ⊆ B₂' := by
      simpa [hB₂'_def] using Set.subset_inter hB₂_sup hB₂₀_sup
    have hB₁'_meas_le : hB₁'_elem.measure ≤ M₁ :=
      IsElementary.measure_mono hB₁'_elem hB₁₀ (by
        intro x hx; exact hx.2)
    have hB₂'_meas_le : hB₂'_elem.measure ≤ M₂ :=
      IsElementary.measure_mono hB₂'_elem hB₂₀ (by
        intro x hx; exact hx.2)
    have h_diff₁' : (hB₁'_elem.sdiff hA₁).measure ≤ ε₁ :=
      calc
        (hB₁'_elem.sdiff hA₁).measure ≤ (hB₁.sdiff hA₁).measure :=
          IsElementary.measure_mono (hB₁'_elem.sdiff hA₁) (hB₁.sdiff hA₁) (by
            intro x hx; exact ⟨hx.1.1, hx.2⟩)
        _ ≤ ε₁ := h_diff₁
    have h_diff₂' : (hB₂'_elem.sdiff hA₂).measure ≤ ε₂ :=
      calc
        (hB₂'_elem.sdiff hA₂).measure ≤ (hB₂.sdiff hA₂).measure :=
          IsElementary.measure_mono (hB₂'_elem.sdiff hA₂) (hB₂.sdiff hA₂) (by
            intro x hx; exact ⟨hx.1.1, hx.2⟩)
        _ ≤ ε₂ := h_diff₂
    set A := EuclideanSpace'.prod A₁ A₂ with hA_def
    set B := EuclideanSpace'.prod B₁' B₂' with hB_def
    have hA_elem : IsElementary A := IsElementary.prod hA₁ hA₂
    have hB_elem : IsElementary B := IsElementary.prod hB₁'_elem hB₂'_elem
    have hA_sub_prod : A ⊆ EuclideanSpace'.prod E₁ E₂ := by
      dsimp [A, EuclideanSpace'.prod]
      exact Set.image_mono (Set.prod_mono hA₁_sub hA₂_sub)
    have hB_sup_prod : EuclideanSpace'.prod E₁ E₂ ⊆ B := by
      dsimp [B, EuclideanSpace'.prod]
      exact Set.image_mono (Set.prod_mono hB₁'_sup hB₂'_sup)
    have h_diff_prod : (hB_elem.sdiff hA_elem).measure ≤ ε := by
      have hprod_diff_sub : B \ A ⊆ (EuclideanSpace'.prod (B₁' \ A₁) B₂') ∪ (EuclideanSpace'.prod B₁' (B₂' \ A₂)) := by
        intro x hx
        rcases hx with ⟨hxB, hx_notA⟩
        rw [hB_def, EuclideanSpace'.prod] at hxB
        rw [hA_def, EuclideanSpace'.prod] at hx_notA
        rcases hxB with ⟨⟨a, b⟩, ⟨ha, hb⟩, hx_eq⟩
        by_cases haA₁ : a ∈ A₁
        · have hb_notA₂ : b ∉ A₂ := by
            intro hbA₂
            apply hx_notA
            refine ⟨⟨a, b⟩, ⟨haA₁, hbA₂⟩, hx_eq⟩
          apply Set.mem_union_right
          dsimp [EuclideanSpace'.prod]
          refine (Set.mem_image (EuclideanSpace'.prod_equiv d₁ d₂).symm (B₁' ×ˢ (B₂' \ A₂)) x).mpr ?_
          refine ⟨(a, b), ⟨⟨ha, hb, hb_notA₂⟩, hx_eq⟩⟩
        · apply Set.mem_union_left
          dsimp [EuclideanSpace'.prod]
          refine (Set.mem_image (EuclideanSpace'.prod_equiv d₁ d₂).symm ((B₁' \ A₁) ×ˢ B₂') x).mpr ?_
          refine ⟨(a, b), ⟨⟨⟨ha, haA₁⟩, hb⟩, hx_eq⟩⟩
      have hU : IsElementary (EuclideanSpace'.prod (B₁' \ A₁) B₂') :=
        IsElementary.prod (hB₁'_elem.sdiff hA₁) hB₂'_elem
      have hV : IsElementary (EuclideanSpace'.prod B₁' (B₂' \ A₂)) :=
        IsElementary.prod hB₁'_elem (hB₂'_elem.sdiff hA₂)
      have hU_measure : hU.measure = (hB₁'_elem.sdiff hA₁).measure * hB₂'_elem.measure :=
        IsElementary.measure_of_prod (hB₁'_elem.sdiff hA₁) hB₂'_elem
      have hV_measure : hV.measure = hB₁'_elem.measure * (hB₂'_elem.sdiff hA₂).measure :=
        IsElementary.measure_of_prod hB₁'_elem (hB₂'_elem.sdiff hA₂)
      have h_nonneg_B₁' : 0 ≤ hB₁'_elem.measure := IsElementary.measure_nonneg hB₁'_elem
      have h_nonneg_B₂' : 0 ≤ hB₂'_elem.measure := IsElementary.measure_nonneg hB₂'_elem
      have h_nonneg_ε₁ : 0 ≤ ε₁ := by nlinarith
      have h_nonneg_ε₂ : 0 ≤ ε₂ := by nlinarith
      have h_nonneg_M₁ : 0 ≤ M₁ := hM₁_nonneg
      have h_nonneg_M₂ : 0 ≤ M₂ := hM₂_nonneg
      -- Chain inequalities
      have h1 : (hB_elem.sdiff hA_elem).measure ≤ hU.measure + hV.measure := by
        calc
          (hB_elem.sdiff hA_elem).measure ≤ (hU.union hV).measure :=
            IsElementary.measure_mono (hB_elem.sdiff hA_elem) (hU.union hV) hprod_diff_sub
          _ ≤ hU.measure + hV.measure := IsElementary.measure_of_union hU hV
      have h2 : hU.measure + hV.measure = (hB₁'_elem.sdiff hA₁).measure * hB₂'_elem.measure + hB₁'_elem.measure * (hB₂'_elem.sdiff hA₂).measure := by
        rw [hU_measure, hV_measure]
      have h3 : (hB₁'_elem.sdiff hA₁).measure * hB₂'_elem.measure + hB₁'_elem.measure * (hB₂'_elem.sdiff hA₂).measure ≤ ε₁ * hB₂'_elem.measure + hB₁'_elem.measure * ε₂ := by
        have h_nonneg_sdiff₁ : 0 ≤ (hB₁'_elem.sdiff hA₁).measure :=
          IsElementary.measure_nonneg (hB₁'_elem.sdiff hA₁)
        have h_nonneg_sdiff₂ : 0 ≤ (hB₂'_elem.sdiff hA₂).measure :=
          IsElementary.measure_nonneg (hB₂'_elem.sdiff hA₂)
        have h_mul₁ : (hB₁'_elem.sdiff hA₁).measure * hB₂'_elem.measure ≤ ε₁ * hB₂'_elem.measure :=
          mul_le_mul_of_nonneg_right h_diff₁' h_nonneg_B₂'
        have h_mul₂ : hB₁'_elem.measure * (hB₂'_elem.sdiff hA₂).measure ≤ hB₁'_elem.measure * ε₂ :=
          mul_le_mul_of_nonneg_left h_diff₂' h_nonneg_B₁'
        nlinarith
      have h4 : ε₁ * hB₂'_elem.measure + hB₁'_elem.measure * ε₂ ≤ ε₁ * M₂ + M₁ * ε₂ := by
        have h_mul₁ : ε₁ * hB₂'_elem.measure ≤ ε₁ * M₂ :=
          mul_le_mul_of_nonneg_left hB₂'_meas_le h_nonneg_ε₁
        have h_mul₂ : hB₁'_elem.measure * ε₂ ≤ M₁ * ε₂ :=
          mul_le_mul_of_nonneg_right hB₁'_meas_le h_nonneg_ε₂
        nlinarith
      have h5 : ε₁ * M₂ + M₁ * ε₂ = ε / (2*(M₂ + 1)) * M₂ + M₁ * (ε / (2*(M₁ + 1))) := rfl
      have h_ε_nonneg : 0 ≤ ε := by nlinarith
      have hM₂_ratio : M₂ / (2*(M₂ + 1)) ≤ 1/2 := by
        have hpos_nonneg : 0 ≤ 2*(M₂ + 1) := by nlinarith
        have hM₂_le_succ : M₂ ≤ M₂ + 1 := by nlinarith
        have htemp : (M₂ + 1) / (2*(M₂ + 1)) = 1/2 := by field_simp
        calc
          M₂ / (2*(M₂ + 1)) ≤ (M₂ + 1) / (2*(M₂ + 1)) :=
            div_le_div_of_nonneg_right hM₂_le_succ hpos_nonneg
          _ = 1/2 := htemp
      have hM₁_ratio : M₁ / (2*(M₁ + 1)) ≤ 1/2 := by
        have hpos_nonneg : 0 ≤ 2*(M₁ + 1) := by nlinarith
        have hM₁_le_succ : M₁ ≤ M₁ + 1 := by nlinarith
        have htemp : (M₁ + 1) / (2*(M₁ + 1)) = 1/2 := by field_simp
        calc
          M₁ / (2*(M₁ + 1)) ≤ (M₁ + 1) / (2*(M₁ + 1)) :=
            div_le_div_of_nonneg_right hM₁_le_succ hpos_nonneg
          _ = 1/2 := htemp
      have h6 : ε / (2*(M₂ + 1)) * M₂ + M₁ * (ε / (2*(M₁ + 1))) ≤ ε := by
        calc
          ε / (2*(M₂ + 1)) * M₂ + M₁ * (ε / (2*(M₁ + 1)))
              = ε * (M₂ / (2*(M₂ + 1)) + M₁ / (2*(M₁ + 1))) := by ring
          _ ≤ ε * (1/2 + 1/2) :=
            mul_le_mul_of_nonneg_left (by nlinarith) h_ε_nonneg
          _ = ε := by ring
      calc
        (hB_elem.sdiff hA_elem).measure ≤ hU.measure + hV.measure := h1
        _ = (hB₁'_elem.sdiff hA₁).measure * hB₂'_elem.measure + hB₁'_elem.measure * (hB₂'_elem.sdiff hA₂).measure := h2
        _ ≤ ε₁ * hB₂'_elem.measure + hB₁'_elem.measure * ε₂ := h3
        _ ≤ ε₁ * M₂ + M₁ * ε₂ := h4
        _ = ε / (2*(M₂ + 1)) * M₂ + M₁ * (ε / (2*(M₁ + 1))) := h5
        _ ≤ ε := h6
    exact ⟨A, B, hA_elem, hB_elem, hA_sub_prod, hB_sup_prod, h_diff_prod⟩
  have h_tfae_iff := (JordanMeasurable.equiv hb_prod).out 1 0
  exact h_tfae_iff.mp h_approx

/-- Jordan measure is multiplicative on products: μ(E₁ × E₂) = μ(E₁) \* μ(E₂). -/
theorem JordanMeasurable.measure_of_prod {d₁ d₂:ℕ} {E₁: Set (EuclideanSpace' d₁)} {E₂: Set (EuclideanSpace' d₂)}
  (hE₁: JordanMeasurable E₁) (hE₂: JordanMeasurable E₂)
  : (hE₁.prod hE₂).measure = hE₁.measure * hE₂.measure := by
  have hprod : JordanMeasurable (EuclideanSpace'.prod E₁ E₂) := hE₁.prod hE₂
  have hb₁ : Bornology.IsBounded E₁ := hE₁.1
  have hb₂ : Bornology.IsBounded E₂ := hE₂.1
  have h_nonneg₁ : 0 ≤ hE₁.measure := Jordan_inner_measure_nonneg E₁
  have h_nonneg₂ : 0 ≤ hE₂.measure := Jordan_inner_measure_nonneg E₂
  have h_inner_eq : Jordan_inner_measure (EuclideanSpace'.prod E₁ E₂) = (hE₁.prod hE₂).measure := rfl
  apply le_antisymm
  · -- (hE₁.prod hE₂).measure ≤ hE₁.measure * hE₂.measure
    let T := { m : ℝ | ∃ C : Set (EuclideanSpace' (d₁ + d₂)), ∃ hC : IsElementary C,
      EuclideanSpace'.prod E₁ E₂ ⊆ C ∧ m = hC.measure }
    have hT_nonempty : T.Nonempty := by
      obtain ⟨C, hC, hC_sup⟩ := IsElementary.contains_bounded hprod.1
      exact ⟨hC.measure, C, hC, hC_sup, rfl⟩
    have h_goal : Jordan_outer_measure (EuclideanSpace'.prod E₁ E₂) ≤ hE₁.measure * hE₂.measure := by
      -- For any δ > 0, find B₁, B₂ with tight bounds
      refine le_of_forall_pos_le_add fun δ hδ => ?_
      set ε := min ((δ / (2*(hE₁.measure + hE₂.measure + 1)))) 1 with hε_def
      have hε_pos : ε > 0 := by
        refine lt_min_iff.mpr ⟨?_, by norm_num⟩
        refine div_pos hδ ?_
        nlinarith
      have h_ε_le_one : ε ≤ 1 := by
        exact min_le_right _ _
      have h_ε_bound : ε*(hE₁.measure + hE₂.measure + 1) ≤ δ/2 := by
        by_cases h : δ / (2*(hE₁.measure + hE₂.measure + 1)) ≤ 1
        · have hε_eq : ε = δ / (2*(hE₁.measure + hE₂.measure + 1)) := by
            dsimp [ε]; rw [min_eq_left h]
          rw [hε_eq]
          have hpos : 2*(hE₁.measure + hE₂.measure + 1) ≠ 0 := by nlinarith
          have h_eq : (δ / (2*(hE₁.measure + hE₂.measure + 1))) * (hE₁.measure + hE₂.measure + 1) = δ/2 := by
            field_simp [hpos]
          nlinarith
        · have hε_eq : ε = 1 := by
            have h' : 1 ≤ δ / (2*(hE₁.measure + hE₂.measure + 1)) := by nlinarith
            dsimp [ε]; rw [min_eq_right h']
          rw [hε_eq]
          have h_δ_gt_2C : δ > 2*(hE₁.measure + hE₂.measure + 1) := by
            have hpos : 0 < 2*(hE₁.measure + hE₂.measure + 1) := by nlinarith
            have h_gt_one : 1 < δ / (2*(hE₁.measure + hE₂.measure + 1)) := by
              by_contra! hle; exact h hle
            exact (one_lt_div hpos).mp h_gt_one
          nlinarith
      have h_exists_B₁ : ∃ B₁ : Set (EuclideanSpace' d₁), ∃ hB₁ : IsElementary B₁, E₁ ⊆ B₁ ∧ hB₁.measure < hE₁.measure + ε := by
        let T₁ := { m : ℝ | ∃ C : Set (EuclideanSpace' d₁), ∃ hC : IsElementary C, E₁ ⊆ C ∧ m = hC.measure }
        have hT₁_nonempty : T₁.Nonempty := by
          obtain ⟨C, hC, hC_sup⟩ := IsElementary.contains_bounded hb₁
          exact ⟨hC.measure, C, hC, hC_sup, rfl⟩
        have h_csInf_T₁ : sInf T₁ = hE₁.measure := by
          calc
            sInf T₁ = Jordan_outer_measure E₁ := rfl
            _ = hE₁.measure := hE₁.eq_outer.symm
        have h_lt_sInf : sInf T₁ < hE₁.measure + ε := by
          rw [h_csInf_T₁]
          nlinarith
        obtain ⟨a, ha, ha_lt⟩ := exists_lt_of_csInf_lt hT₁_nonempty h_lt_sInf
        rcases ha with ⟨B₁, hB₁, hB₁_sup, ha_eq⟩
        refine ⟨B₁, hB₁, hB₁_sup, ?_⟩
        rw [ha_eq] at ha_lt
        exact ha_lt
      obtain ⟨B₁, hB₁, hB₁_sup, hB₁_lt⟩ := h_exists_B₁
      have h_exists_B₂ : ∃ B₂ : Set (EuclideanSpace' d₂), ∃ hB₂ : IsElementary B₂, E₂ ⊆ B₂ ∧ hB₂.measure < hE₂.measure + ε := by
        let T₂ := { m : ℝ | ∃ C : Set (EuclideanSpace' d₂), ∃ hC : IsElementary C, E₂ ⊆ C ∧ m = hC.measure }
        have hT₂_nonempty : T₂.Nonempty := by
          obtain ⟨C, hC, hC_sup⟩ := IsElementary.contains_bounded hb₂
          exact ⟨hC.measure, C, hC, hC_sup, rfl⟩
        have h_csInf_T₂ : sInf T₂ = hE₂.measure := by
          calc
            sInf T₂ = Jordan_outer_measure E₂ := rfl
            _ = hE₂.measure := hE₂.eq_outer.symm
        have h_lt_sInf : sInf T₂ < hE₂.measure + ε := by
          rw [h_csInf_T₂]
          nlinarith
        obtain ⟨a, ha, ha_lt⟩ := exists_lt_of_csInf_lt hT₂_nonempty h_lt_sInf
        rcases ha with ⟨B₂, hB₂, hB₂_sup, ha_eq⟩
        refine ⟨B₂, hB₂, hB₂_sup, ?_⟩
        rw [ha_eq] at ha_lt
        exact ha_lt
      obtain ⟨B₂, hB₂, hB₂_sup, hB₂_lt⟩ := h_exists_B₂
      have h_superset : EuclideanSpace'.prod E₁ E₂ ⊆ EuclideanSpace'.prod B₁ B₂ := by
        dsimp [EuclideanSpace'.prod]
        exact Set.image_mono (Set.prod_mono hB₁_sup hB₂_sup)
      have h_superset_measure : Jordan_outer_measure (EuclideanSpace'.prod E₁ E₂) ≤ hB₁.measure * hB₂.measure := by
        -- Since EuclideanSpace'.prod B₁ B₂ is elementary and contains E₁×E₂
        have hB_prod_elem : IsElementary (EuclideanSpace'.prod B₁ B₂) := IsElementary.prod hB₁ hB₂
        have h_in_set : hB₁.measure * hB₂.measure ∈ T := by
          refine ⟨EuclideanSpace'.prod B₁ B₂, hB_prod_elem, h_superset, ?_⟩
          exact (IsElementary.measure_of_prod hB₁ hB₂).symm
        refine csInf_le (by
          refine ⟨0, ?_⟩
          intro m hm
          obtain ⟨_, hC, _, hm_eq⟩ := hm
          rw [hm_eq]
          exact IsElementary.measure_nonneg hC) ?_
        exact h_in_set
      have h_sum : hB₁.measure * hB₂.measure < (hE₁.measure + ε)*(hE₂.measure + ε) := by
        have hpos_E₁_ε : 0 ≤ hE₁.measure + ε := by nlinarith
        have hpos_sum : 0 < (hE₁.measure + ε)*(hE₂.measure + ε) := by
          positivity
        by_cases hzero : hB₂.measure = 0
        · rw [hzero, mul_zero]
          exact hpos_sum
        · have hpos_B₂ : 0 < hB₂.measure := by
            by_contra! hle
            have : hB₂.measure ≤ 0 := hle
            have : hB₂.measure = 0 := le_antisymm this (IsElementary.measure_nonneg hB₂)
            exact hzero this
          have h1 : hB₁.measure * hB₂.measure < (hE₁.measure + ε) * hB₂.measure :=
            mul_lt_mul_of_pos_right hB₁_lt hpos_B₂
          have h2 : (hE₁.measure + ε) * hB₂.measure ≤ (hE₁.measure + ε)*(hE₂.measure + ε) :=
            mul_le_mul_of_nonneg_left hB₂_lt.le hpos_E₁_ε
          nlinarith
      have h_diff : (hE₁.measure + ε)*(hE₂.measure + ε) ≤ hE₁.measure * hE₂.measure + δ := by
        calc
          (hE₁.measure + ε)*(hE₂.measure + ε) = hE₁.measure * hE₂.measure + ε*(hE₁.measure + hE₂.measure) + ε^2 := by ring
          _ ≤ hE₁.measure * hE₂.measure + δ := by
            have h_sq_le_ε : ε^2 ≤ ε := by
              nlinarith [h_ε_le_one, hε_pos]
            nlinarith
      have h_chain : Jordan_outer_measure (EuclideanSpace'.prod E₁ E₂) < hE₁.measure * hE₂.measure + δ := by
        calc
          Jordan_outer_measure (EuclideanSpace'.prod E₁ E₂) ≤ hB₁.measure * hB₂.measure := h_superset_measure
          _ < (hE₁.measure + ε)*(hE₂.measure + ε) := h_sum
          _ ≤ hE₁.measure * hE₂.measure + δ := h_diff
      exact h_chain.le
    exact hprod.eq_outer ▸ h_goal
  · -- hE₁.measure * hE₂.measure ≤ (hE₁.prod hE₂).measure
    by_cases hzero₁ : hE₁.measure = 0
    · rw [hzero₁, zero_mul]; exact Jordan_inner_measure_nonneg _
    by_cases hzero₂ : hE₂.measure = 0
    · rw [hzero₂, mul_zero]; exact Jordan_inner_measure_nonneg _
    have hpos₁ : 0 < hE₁.measure := by
      by_contra! hle
      have : hE₁.measure = 0 := le_antisymm hle h_nonneg₁
      exact hzero₁ this
    have hpos₂ : 0 < hE₂.measure := by
      by_contra! hle
      have : hE₂.measure = 0 := le_antisymm hle h_nonneg₂
      exact hzero₂ this
    have h_nonneg_prod : 0 ≤ (hE₁.prod hE₂).measure := by
      simpa [h_inner_eq] using Jordan_inner_measure_nonneg (EuclideanSpace'.prod E₁ E₂)
    by_contra! h_lt
    -- h_lt : hE₁.measure * hE₂.measure > (hE₁.prod hE₂).measure
    set δ := hE₁.measure * hE₂.measure - (hE₁.prod hE₂).measure with hδ_def
    have hδ_pos : 0 < δ := sub_pos.mpr h_lt
    set ε := min (δ / (2*(hE₁.measure + hE₂.measure + 1))) (min (hE₁.measure / 2) (hE₂.measure / 2)) with hε_def
    have hε_pos : ε > 0 := by
      refine lt_min_iff.mpr ⟨?_, ?_⟩
      · refine div_pos hδ_pos ?_; nlinarith
      · exact lt_min_iff.mpr ⟨by nlinarith, by nlinarith⟩
    have h_ε_le_half₁ : ε ≤ hE₁.measure / 2 := by
      have : ε ≤ min (hE₁.measure / 2) (hE₂.measure / 2) := min_le_right _ _
      exact le_trans this (min_le_left _ _)
    have h_ε_le_half₂ : ε ≤ hE₂.measure / 2 := by
      have : ε ≤ min (hE₁.measure / 2) (hE₂.measure / 2) := min_le_right _ _
      exact le_trans this (min_le_right _ _)
    have h_sub_pos₁ : 0 < hE₁.measure - ε := by nlinarith
    have h_sub_pos₂ : 0 < hE₂.measure - ε := by nlinarith
    -- Pick an elementary subset A₁ ⊆ E₁ with measure > hE₁.measure - ε
    have h_exists_A₁ : ∃ A₁ : Set (EuclideanSpace' d₁), ∃ hA₁ : IsElementary A₁, A₁ ⊆ E₁ ∧ hA₁.measure > hE₁.measure - ε := by
      let S₁ := { m : ℝ | ∃ A : Set (EuclideanSpace' d₁), ∃ hA : IsElementary A, A ⊆ E₁ ∧ m = hA.measure }
      have h_nonempty_S₁ : S₁.Nonempty := by
        refine ⟨0, ∅, IsElementary.empty _, Set.empty_subset _, ?_⟩
        exact (IsElementary.measure_of_empty d₁).symm
      have h_sSup_S₁ : sSup S₁ = hE₁.measure := rfl
      have h_lt_sSup : hE₁.measure - ε < sSup S₁ := by
        rw [h_sSup_S₁]; nlinarith
      obtain ⟨a, ha, ha_gt⟩ := exists_lt_of_lt_csSup h_nonempty_S₁ h_lt_sSup
      rcases ha with ⟨A₁, hA₁, hA₁_sub, ha_eq⟩
      refine ⟨A₁, hA₁, hA₁_sub, ?_⟩
      rw [ha_eq] at ha_gt; exact ha_gt
    obtain ⟨A₁, hA₁, hA₁_sub, hA₁_gt⟩ := h_exists_A₁
    -- Pick an elementary subset A₂ ⊆ E₂ with measure > hE₂.measure - ε
    have h_exists_A₂ : ∃ A₂ : Set (EuclideanSpace' d₂), ∃ hA₂ : IsElementary A₂, A₂ ⊆ E₂ ∧ hA₂.measure > hE₂.measure - ε := by
      let S₂ := { m : ℝ | ∃ A : Set (EuclideanSpace' d₂), ∃ hA : IsElementary A, A ⊆ E₂ ∧ m = hA.measure }
      have h_nonempty_S₂ : S₂.Nonempty := by
        refine ⟨0, ∅, IsElementary.empty _, Set.empty_subset _, ?_⟩
        exact (IsElementary.measure_of_empty d₂).symm
      have h_sSup_S₂ : sSup S₂ = hE₂.measure := rfl
      have h_lt_sSup : hE₂.measure - ε < sSup S₂ := by
        rw [h_sSup_S₂]; nlinarith
      obtain ⟨a, ha, ha_gt⟩ := exists_lt_of_lt_csSup h_nonempty_S₂ h_lt_sSup
      rcases ha with ⟨A₂, hA₂, hA₂_sub, ha_eq⟩
      refine ⟨A₂, hA₂, hA₂_sub, ?_⟩
      rw [ha_eq] at ha_gt; exact ha_gt
    obtain ⟨A₂, hA₂, hA₂_sub, hA₂_gt⟩ := h_exists_A₂
    have hA_prod_elem : IsElementary (EuclideanSpace'.prod A₁ A₂) := IsElementary.prod hA₁ hA₂
    have hA_prod_sub : EuclideanSpace'.prod A₁ A₂ ⊆ EuclideanSpace'.prod E₁ E₂ := by
      dsimp [EuclideanSpace'.prod]
      apply Set.image_mono (Set.prod_mono hA₁_sub hA₂_sub)
    have hA_prod_measure : hA_prod_elem.measure = hA₁.measure * hA₂.measure :=
      IsElementary.measure_of_prod hA₁ hA₂
    have h_le_inner : hA₁.measure * hA₂.measure ≤ Jordan_inner_measure (EuclideanSpace'.prod E₁ E₂) := by
      rw [Jordan_inner_measure]
      apply le_csSup
      · obtain ⟨C, hC, hC_sup⟩ := IsElementary.contains_bounded hprod.1
        refine ⟨hC.measure, ?_⟩
        rintro m ⟨C', hC'_elem, hC'_sub, hm_eq⟩
        rw [hm_eq]
        exact IsElementary.measure_mono hC'_elem hC (Set.Subset.trans hC'_sub hC_sup)
      · exact ⟨EuclideanSpace'.prod A₁ A₂, hA_prod_elem, hA_prod_sub, hA_prod_measure.symm⟩
    rw [h_inner_eq] at h_le_inner
    -- Contradiction: (hE₁.prod hE₂).measure is ≥ (hE₁.measure - ε)*(hE₂.measure - ε), which is > δ
    have h_prod_bound : (hE₁.measure - ε)*(hE₂.measure - ε) < hA₁.measure * hA₂.measure := by
      have hA₁_ge_sub : hE₁.measure - ε < hA₁.measure := hA₁_gt
      have hA₂_ge_sub : hE₂.measure - ε < hA₂.measure := hA₂_gt
      have hpos_prod_sub : 0 < (hE₁.measure - ε)*(hE₂.measure - ε) := mul_pos h_sub_pos₁ h_sub_pos₂
      nlinarith
    have h_lower : (hE₁.measure - ε)*(hE₂.measure - ε) < (hE₁.prod hE₂).measure := by
      nlinarith
    have h_ε_ineq : (hE₁.measure - ε)*(hE₂.measure - ε) ≥ hE₁.measure * hE₂.measure - δ/2 := by
      have h_expand : hE₁.measure * hE₂.measure - (hE₁.measure - ε)*(hE₂.measure - ε) = ε*(hE₁.measure + hE₂.measure) - ε^2 := by ring
      have h_bound : ε*(hE₁.measure + hE₂.measure) - ε^2 ≤ δ/2 := by
        have h_ε_val : ε*(hE₁.measure + hE₂.measure + 1) ≤ δ/2 := by
          have h_δ_bound : δ / (2*(hE₁.measure + hE₂.measure + 1)) ≤ δ / (2*(hE₁.measure + hE₂.measure + 1)) := le_refl _
          -- use the first component of the min
          have h_ε_le_ratio : ε ≤ δ / (2*(hE₁.measure + hE₂.measure + 1)) := min_le_left _ _
          calc
            ε*(hE₁.measure + hE₂.measure + 1) ≤ (δ / (2*(hE₁.measure + hE₂.measure + 1))) * (hE₁.measure + hE₂.measure + 1) := by
              nlinarith
            _ = δ/2 := by
              field_simp
        nlinarith
      nlinarith
    -- Putting it together: (hE₁.prod hE₂).measure > hE₁.measure * hE₂.measure - δ/2
    -- But by definition δ = hE₁.measure * hE₂.measure - (hE₁.prod hE₂).measure
    -- So (hE₁.prod hE₂).measure > hE₁.measure * hE₂.measure - δ/2 = (hE₁.prod hE₂).measure + δ/2
    -- Therefore δ/2 < 0, i.e., δ < 0, contradiction
    nlinarith

/-- Two sets are isometric if one is an orthogonal transformation plus translation of the other. -/
abbrev Isometric {d:ℕ} (E F: Set (EuclideanSpace' d)) : Prop :=
 ∃ A ∈ Matrix.orthogonalGroup (Fin d) ℝ, ∃ x₀, F = ((fun x => WithLp.toLp 2 (Matrix.toLin' A x.ofLp)) '' E) + {x₀}

/-
Exercise 1.1.17.

WARNING: the statement below (kept for reference, commented out) is FALSE as written for
dimension `d ≥ 3`.  Without assuming that the pieces `P i`, `Q i` are themselves Jordan
measurable, the Banach–Tarski paradox provides a counterexample: the unit ball `E` can be cut
into finitely many (non-measurable) pieces `P i` that are pairwise disjoint, and reassembled by
isometries into two disjoint unit balls `F` (the reassembled pieces `Q i` even have empty interior,
so `hQdisj` holds vacuously), yet `hE.measure = vol(ball) ≠ 2·vol(ball) = hF.measure`.  Neither a
proof nor a disproof is possible from Mathlib as-is (Banach–Tarski is not available), so the
original statement is retained only as a comment.

The corrected statement (`JordanMeasurable.measure_of_equidecomposable`, below) adds the
standard hypothesis that the pieces are Jordan measurable, matching Tao's exercise.

theorem JordanMeasurable.measure_of_equidecomposable {d n:ℕ} {E F: Set (EuclideanSpace' d)}
(hE: JordanMeasurable E) (hF: JordanMeasurable F)
{P Q: Fin n → Set (EuclideanSpace' d)} (hPQ: ∀ i, Isometric (P i) (Q i))
(hPE: E = ⋃ i, P i) (hQF: F = ⋃ i, Q i) (hPdisj: Set.PairwiseDisjoint .univ P)
(hQdisj: Set.PairwiseDisjoint .univ (fun i ↦ (interior (Q i))))
(hPmeas : ∀ i, JordanMeasurable (P i)) : hE.measure = hF.measure := by
  have hQmeas : ∀ i, JordanMeasurable (Q i) := by
    intro i
    rcases hPQ i with ⟨A, hA, x₀, rfl⟩
    have hQ_i' : JordanMeasurable ((fun x => WithLp.toLp 2 (Matrix.toLin' A x.ofLp)) '' (P i)) :=
      JordanMeasurable.linear (A.linear_equiv) (hPmeas i)
    exact hQ_i'.translate x₀
  have h_sum_P : (JordanMeasurable.union' (λ i hi => hPmeas i)).measure = ∑ i : Fin n, (hPmeas i).measure :=
    JordanMeasurable.measure_of_disjUnion' (λ i hi => hPmeas i) (by
      intro i hi j hj hne
      apply hPdisj (Set.mem_univ i) (Set.mem_univ j) hne)
  have h_sum_Q : (JordanMeasurable.union' (λ i hi => hQmeas i)).measure = ∑ i : Fin n, (hQmeas i).measure :=
    JordanMeasurable.measure_of_disjUnion' (λ i hi => hQmeas i) (by
      intro i hi j hj hne
      rcases hPQ i with ⟨A_i, hA_i, x_i, rfl⟩
      rcases hPQ j with ⟨A_j, hA_j, x_j, rfl⟩
      apply Set.disjoint_iff.mpr; intro x hx; rcases hx with ⟨hx_i, hx_j⟩
      have hx_i' : x - x_i ∈ ((fun x => WithLp.toLp 2 (Matrix.toLin' A_i x.ofLp)) '' (P i)) := by
        rcases hx_i with ⟨y, hy, rfl⟩; exact ⟨y, hy, by simp⟩
      have hx_j' : x - x_j ∈ ((fun x => WithLp.toLp 2 (Matrix.toLin' A_j x.ofLp)) '' (P j)) := by
        rcases hx_j with ⟨y, hy, rfl⟩; exact ⟨y, hy, by simp⟩
      have hP_i_inv : (A_i.linear_equiv.symm) (x - x_i) ∈ P i := by
        rcases hx_i' with ⟨y, hy, h_eq⟩
        have : (A_i.linear_equiv.symm) ((fun x => WithLp.toLp 2 (Matrix.toLin' A_i x.ofLp)) y) = y := by simp
        simpa [h_eq, this] using hy
      have hP_j_inv : (A_j.linear_equiv.symm) (x - x_j) ∈ P j := by
        rcases hx_j' with ⟨y, hy, h_eq⟩
        have : (A_j.linear_equiv.symm) ((fun x => WithLp.toLp 2 (Matrix.toLin' A_j x.ofLp)) y) = y := by simp
        simpa [h_eq, this] using hy
      have h_disjoint : Disjoint (P i) (P j) := hPdisj (Set.mem_univ i) (Set.mem_univ j) (by
        intro h_eq; apply hne; exact h_eq)
      exact h_disjoint ⟨hP_i_inv, hP_j_inv⟩)
  have h_union_E : (⋃ i, P i) = E := by symm; exact hPE
  have h_union_F : (⋃ i, Q i) = F := by symm; exact hQF
  have h_union_E_meas : JordanMeasurable (⋃ i, P i) := JordanMeasurable.union' hPmeas
  have h_union_F_meas : JordanMeasurable (⋃ i, Q i) := JordanMeasurable.union' hQmeas
  have h_E_meas_eq : (JordanMeasurable.union' hPmeas).measure = hE.measure := by
    apply congrArg (·.measure)
    apply Subsingleton.elim (h_union_E_meas) (hPE.symm ▸ hE)
  have h_F_meas_eq : (JordanMeasurable.union' hQmeas).measure = hF.measure := by
    apply congrArg (·.measure)
    apply Subsingleton.elim (h_union_F_meas) (hQF.symm ▸ hF)
  have h_measures_eq : ∑ i : Fin n, (hPmeas i).measure = ∑ i : Fin n, (hQmeas i).measure := by
    refine Finset.sum_congr rfl fun i _ => ?_
    exact isometric_measure_eq (hPQ i) (hPmeas i) (hQmeas i)
  calc
    hE.measure = (JordanMeasurable.union' hPmeas).measure := by symm; exact h_E_meas_eq
    _ = ∑ i : Fin n, (hPmeas i).measure := h_sum_P
    _ = ∑ i : Fin n, (hQmeas i).measure := h_measures_eq
    _ = (JordanMeasurable.union' hQmeas).measure := by symm; exact h_sum_Q
    _ = hF.measure := h_F_meas_eq

An orthogonal matrix has `|det| = 1`.
-/
lemma Matrix.abs_det_orthogonal {d:ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : A ∈ Matrix.orthogonalGroup (Fin d) ℝ) : |A.det| = 1 := by
      have := congr_arg Matrix.det ( hA.2 );
      simp_all +decide [ Matrix.det_one, Matrix.star_eq_conjTranspose ];
      cases abs_cases ( Matrix.det A ) <;> nlinarith

/-- An orthogonal matrix is invertible. -/
@[reducible]
noncomputable def Matrix.invertibleOfOrthogonal {d:ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : A ∈ Matrix.orthogonalGroup (Fin d) ℝ) : Invertible A :=
  A.invertibleOfIsUnitDet (by
    have : |A.det| = 1 := Matrix.abs_det_orthogonal hA
    have : A.det ≠ 0 := by intro h; rw [h] at this; simp at this
    exact isUnit_iff_ne_zero.mpr this)

/-
Isometric Jordan measurable sets have the same Jordan measure.
-/
lemma isometric_measure_eq {d:ℕ} {E F : Set (EuclideanSpace' d)} (hiso : Isometric E F)
    (hE : JordanMeasurable E) (hF : JordanMeasurable F) : hF.measure = hE.measure := by
      obtain ⟨ A, hA, x₀, rfl ⟩ := hiso;
      -- Let S := (A.linear_equiv) '' E.
      set S := (fun x => WithLp.toLp 2 (Matrix.toLin' A x.ofLp)) '' E with hS_def
      have hS : JordanMeasurable S := by
        have := hF;
        convert this.translate ( -x₀ ) using 1 ; ext ; simp +decide
      have hS_measure : hS.measure = hE.measure := by
        haveI := Matrix.invertibleOfOrthogonal hA;
        convert linear_measure_eq ( A.linear_equiv ) hE using 1;
        simp +decide [ Matrix.linear_equiv_det ];
        rw [ Matrix.abs_det_orthogonal hA, one_mul ]
      have hF_eq_S : (fun x => WithLp.toLp 2 (Matrix.toLin' A x.ofLp)) '' E + {x₀} = S + {x₀} := by
        rfl
      have hF_measure : hF.measure ≤ hS.measure := by
        convert JordanMeasurable.measure_of_translate hS x₀ using 1
      have hF_measure_ge : hS.measure ≤ hF.measure := by
        have hF_measure_ge : (hF.translate (-x₀)).measure ≤ hF.measure := by
          convert JordanMeasurable.measure_of_translate hF ( -x₀ ) using 1;
        convert hF_measure_ge using 1;
        congr! 1;
        norm_num [ Set.ext_iff, Set.mem_add ]
      have hF_measure_eq : hF.measure = hS.measure := by
        exact le_antisymm hF_measure hF_measure_ge
      rw [hS_measure] at hF_measure_eq
      exact hF_measure_eq.symm ▸ rfl


/-- Helper: closure of a bounded interval is contained in the closed interval between its endpoints. -/
lemma BoundedInterval.closure_subset_Icc (I : BoundedInterval) : closure (I : Set ℝ) ⊆ (Icc I.a I.b : Set ℝ) := by
  cases I with
  | Ioo a b =>
    by_cases h : a ≠ b
    · rw [BoundedInterval.set_Ioo, closure_Ioo h]; simp
    · have heq : a = b := by exact not_not.mp h
      subst heq; simp [BoundedInterval.set_Ioo]
  | Icc a b =>
    simp [BoundedInterval.set_Icc, isClosed_Icc.closure_eq]
  | Ioc a b =>
    by_cases h : a ≠ b
    · rw [BoundedInterval.set_Ioc, closure_Ioc h]; simp
    · have heq : a = b := by exact not_not.mp h
      subst heq; simp [BoundedInterval.set_Ioc]
  | Ico a b =>
    by_cases h : a ≠ b
    · rw [BoundedInterval.set_Ico, closure_Ico h]; simp
    · have heq : a = b := by exact not_not.mp h
      subst heq; simp [BoundedInterval.set_Ico]

/-- Closing all sides of a box to {lit}`Icc`. Preserves volume. -/
def Box.closure {d:ℕ} (B : Box d) : Box d :=
  ⟨fun i => BoundedInterval.Icc (B.side i).a (B.side i).b⟩

@[simp]
lemma Box.volume_closure {d:ℕ} (B : Box d) : |B.closure|ᵥ = |B|ᵥ := by
  simp [Box.volume, Box.closure, BoundedInterval.length]

lemma Box.volume_nonneg {d:ℕ} (B : Box d) : 0 ≤ |B|ᵥ := by
  apply Finset.prod_nonneg; intro i _; exact le_max_right _ _

lemma closure_finset_biUnion {d : ℕ} (T : Finset (Box d)) : closure (⋃ B ∈ T, (B : Set (EuclideanSpace' d))) = ⋃ B ∈ T, closure (B : Set (EuclideanSpace' d)) := by
  classical
  induction' T using Finset.induction_on with B T hT ih
  · simp
  · simp [closure_union, ih]

lemma box_closure_subset_closure {d:ℕ} (B : Box d) : closure (B : Set (EuclideanSpace' d)) ⊆ (Box.closure B).toSet := by
  intro x hx; rw [Box.mem_toSet]; intro i
  set f : EuclideanSpace' d → ℝ := fun y => y.ofLp i with hf
  have hf_cont : Continuous f := by
    simpa [hf] using PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i
  have hf_maps : Set.MapsTo f (B : Set (EuclideanSpace' d)) ((B.side i : Set ℝ)) := by
    intro y hy; rw [Box.mem_toSet] at hy; exact hy i
  have hx_i : f x ∈ closure ((B.side i : Set ℝ)) := map_mem_closure hf_cont hx hf_maps
  have h_sub' : closure ((B.side i : Set ℝ)) ⊆ (BoundedInterval.Icc (B.side i).a (B.side i).b : Set ℝ) :=
    BoundedInterval.closure_subset_Icc (B.side i)
  exact h_sub' hx_i

noncomputable def elementary_measure {d:ℕ} (S : Set (EuclideanSpace' d)) : ℝ := by
  classical
  exact if h : IsElementary S then h.measure else 0

lemma elementary_measure_nonneg {d:ℕ} (S : Set (EuclideanSpace' d)) : 0 ≤ elementary_measure S := by
  classical
  unfold elementary_measure; split
  · exact IsElementary.measure_nonneg _
  · exact le_refl 0

lemma elementary_measure_eq {d:ℕ} {S : Set (EuclideanSpace' d)} (hS : IsElementary S) : elementary_measure S = hS.measure := by
  classical
  simp [elementary_measure, hS]

lemma sum_image_volume_le_sum_volume' {d : ℕ} [DecidableEq (Box d)] (T : Finset (Box d)) (f : Box d → Box d) (hf : ∀ B, |f B|ᵥ = |B|ᵥ) :
    ∑ B' ∈ T.image f, |B'|ᵥ ≤ ∑ B ∈ T, |B|ᵥ := by
  induction' T using Finset.induction_on with B T hT ih
  · simp
  · rw [Finset.image_insert, Finset.sum_insert hT]
    by_cases h : f B ∈ T.image f
    · have h_insert : insert (f B) (T.image f) = T.image f := Finset.insert_eq_of_mem h
      rw [h_insert]
      calc
        ∑ B' ∈ T.image f, |B'|ᵥ ≤ ∑ B ∈ T, |B|ᵥ := ih
        _ ≤ |B|ᵥ + ∑ B ∈ T, |B|ᵥ := by nlinarith [Box.volume_nonneg B]
    · simp [h, ih, hf B]

lemma Finset.sum_image_le_sum' {α β : Type*} [DecidableEq α] [DecidableEq β] {s : Finset α} (f : α → β) (g : β → ℝ) (hg : ∀ x : β, 0 ≤ g x) :
    ∑ x ∈ s.image f, g x ≤ ∑ x ∈ s, g (f x) := by
  induction' s using Finset.induction_on with a s has ih
  · simp
  · rw [Finset.image_insert]
    by_cases hmem : f a ∈ s.image f
    · rw [Finset.insert_eq_of_mem hmem, Finset.sum_insert has]
      exact le_trans ih (by nlinarith [hg (f a)])
    · rw [Finset.sum_insert hmem, Finset.sum_insert has]
      simp [ih]

lemma Finset.sum_attach_image_eq_sum_image {α β : Type*} [DecidableEq α] [DecidableEq β] (s : Finset α) (f : α → β) (g : β → ℝ) :
    ∑ x ∈ s.image f, g x = ∑ y ∈ s.image f, g y := rfl

theorem JordanMeasurable.outer_measure_of_closure {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E) :
  Jordan_outer_measure (closure E) = Jordan_outer_measure E := by
  classical
  apply le_antisymm
  · -- J^*(closure E) ≤ J^*(E)
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨A, hA, hEA, hA_measure⟩ : ∃ (A : Set (EuclideanSpace' d)) (hA : IsElementary A), E ⊆ A ∧ hA.measure < Jordan_outer_measure E + ε := by
      have h_nonempty : { m : ℝ | ∃ (A : Set (EuclideanSpace' d)), ∃ hA : IsElementary A, E ⊆ A ∧ m = hA.measure }.Nonempty := by
        obtain ⟨A, hA, hEA⟩ := IsElementary.contains_bounded hE
        exact ⟨hA.measure, A, hA, hEA, rfl⟩
      have h_lt : sInf { m : ℝ | ∃ (A : Set (EuclideanSpace' d)), ∃ hA : IsElementary A, E ⊆ A ∧ m = hA.measure } < Jordan_outer_measure E + ε := by
        dsimp [Jordan_outer_measure]; nlinarith
      obtain ⟨m, hm, hm_lt⟩ := exists_lt_of_csInf_lt h_nonempty h_lt
      obtain ⟨A, hA, hEA, rfl⟩ := hm; exact ⟨A, hA, hEA, hm_lt⟩
    obtain ⟨T, hT_disj, hA_eq⟩ := hA.partition
    let C := ⋃ B ∈ T, (Box.closure B : Set (EuclideanSpace' d))
    have hC_elem : IsElementary C := by
      refine ⟨T.image Box.closure, ?_⟩
      ext x; simp [C]
    have h_closure_sub_C : closure E ⊆ C := by
      have h_closure_A_sub_C : closure A ⊆ C := by
        rw [hA_eq, closure_finset_biUnion T]
        refine Set.biUnion_mono (Set.Subset.refl (T : Set (Box d))) (fun B hB => ?_)
        exact box_closure_subset_closure B
      exact Set.Subset.trans (closure_mono hEA) h_closure_A_sub_C
    have h_outer_le_C : Jordan_outer_measure (closure E) ≤ hC_elem.measure := by
      unfold Jordan_outer_measure
      apply csInf_le
      · refine ⟨0, ?_⟩
        rintro m' ⟨A', hA', hA'_sub, rfl⟩; exact IsElementary.measure_nonneg hA'
      · exact ⟨C, hC_elem, h_closure_sub_C, rfl⟩
    have hC_measure_le_A : hC_elem.measure ≤ hA.measure := by
      let Cs : Finset (Set (EuclideanSpace' d)) :=
        T.image (fun (B : Box d) => (Box.closure B : Set (EuclideanSpace' d)))
      have hCs_elem : ∀ (S : Set (EuclideanSpace' d)), S ∈ Cs → IsElementary S := by
        intro S hS; rcases Finset.mem_image.mp hS with ⟨B, hB, rfl⟩; exact IsElementary.box (Box.closure B)
      have h_union_Cs : (⋃ S ∈ Cs, S) = C := by
        ext x; simp [C, Cs]
      have h_union_elem : IsElementary (⋃ S ∈ Cs, S) := IsElementary.union' hCs_elem
      have h_measure_eq : hC_elem.measure = h_union_elem.measure :=
        IsElementary.measure_eq_of_set_eq hC_elem h_union_elem h_union_Cs.symm
      have h_subadd : h_union_elem.measure ≤ ∑ S : Cs, (hCs_elem S.val S.property).measure :=
        IsElementary.measure_of_union' hCs_elem
      have h_sum_le : ∑ S : Cs, (hCs_elem S.val S.property).measure ≤ hA.measure := by
        let f : Box d → Set (EuclideanSpace' d) := fun B => (Box.closure B : Set (EuclideanSpace' d))
        have hCs_eq : Cs = T.image f := rfl
        have h_sum_eq : ∑ S : Cs, (hCs_elem S.val S.property).measure = ∑ S ∈ Cs, elementary_measure S := by
          -- Note: ∑ S : Cs, f = ∑ S ∈ Cs.attach, f S.val. Using Finset.sum_attach we convert to ∑ S ∈ Cs, f S.
          -- But f = λ S.val => (hCs_elem S.val S.property).measure, which depends on the membership proof S.property.
          -- We define an auxiliary function that doesn't depend on the proof.
          let g (S : Set (EuclideanSpace' d)) : ℝ := elementary_measure S
          have hg_eq : ∀ (S : Set (EuclideanSpace' d)) (hS : S ∈ Cs), (hCs_elem S hS).measure = g S := by
            intro S hS; simp [g, elementary_measure_eq (hCs_elem S hS)]
          calc
            ∑ S : Cs, (hCs_elem S.val S.property).measure = ∑ S : Cs, g S.val := by
              refine Finset.sum_congr rfl fun S hS => ?_
              simp [g, hg_eq S.val S.property]
            _ = ∑ S ∈ Cs, g S := by simp [Finset.sum_attach]
            _ = ∑ S ∈ Cs, elementary_measure S := rfl
        rw [h_sum_eq]
        have h_image_sum : ∑ S ∈ T.image f, elementary_measure S ≤ ∑ B ∈ T, elementary_measure (f B) :=
          Finset.sum_image_le_sum' f elementary_measure (fun _ => elementary_measure_nonneg _)
        have h_f_measure : ∀ B, elementary_measure (f B) = |B|ᵥ := by
          intro B; simp [f, elementary_measure_eq (IsElementary.box (Box.closure B)), IsElementary.measure_of_box, Box.volume_closure]
        have h_measure_sum : ∑ B ∈ T, |B|ᵥ = hA.measure := (hA.measure_eq hT_disj hA_eq).symm
        calc
          ∑ S ∈ Cs, elementary_measure S = ∑ S ∈ T.image f, elementary_measure S := rfl
          _ ≤ ∑ B ∈ T, elementary_measure (f B) := h_image_sum
          _ = ∑ B ∈ T, |B|ᵥ := by simp [h_f_measure]
          _ = hA.measure := h_measure_sum
      calc
        hC_elem.measure = h_union_elem.measure := h_measure_eq
        _ ≤ ∑ S : Cs, (hCs_elem S.val S.property).measure := h_subadd
        _ ≤ hA.measure := h_sum_le
    nlinarith
  · -- J^*(E) ≤ J^*(closure E)
    unfold Jordan_outer_measure
    apply csInf_le_csInf
    · refine ⟨0, ?_⟩
      rintro m ⟨A, hA, _, rfl⟩; exact IsElementary.measure_nonneg hA
    · have h_bounded_cl : Bornology.IsBounded (closure E) := hE.closure
      obtain ⟨A, hA, h_clEA⟩ := IsElementary.contains_bounded h_bounded_cl
      exact ⟨hA.measure, A, hA, h_clEA, rfl⟩
    · intro m hm
      obtain ⟨A, hA, hA_sub, rfl⟩ := hm
      exact ⟨A, hA, Set.Subset.trans (subset_closure (s := E)) hA_sub, rfl⟩

/-- Exercise 1.1.18 (2) -/
-- The inner Jordan measure of a set equals the inner measure of its interior.
theorem JordanMeasurable.inner_measure_of_interior {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E) :
  Jordan_inner_measure (interior E) = Jordan_inner_measure E := by
  have h_sub : interior E ⊆ E := interior_subset
  apply le_antisymm
  · -- Jordan_inner_measure (interior E) ≤ Jordan_inner_measure E
    unfold Jordan_inner_measure
    apply csSup_le_csSup
    · -- ht: BddAbove {m | ∃ A, IsElementary A, A ⊆ E ∧ m = hA.measure}
      obtain ⟨B, hB, hEB⟩ := IsElementary.contains_bounded hE
      refine ⟨hB.measure, ?_⟩
      rintro m ⟨A, hA, hA_sub, rfl⟩
      exact IsElementary.measure_mono hA hB (Set.Subset.trans hA_sub hEB)
    · -- hs: {m | ∃ A, IsElementary A, A ⊆ interior E ∧ m = hA.measure}.Nonempty
      refine ⟨0, ?_⟩
      refine ⟨∅, IsElementary.empty d, Set.empty_subset _, ?_⟩
      exact Eq.symm (IsElementary.measure_of_empty d)
    · -- h: {m | ... ⊆ interior E} ⊆ {m | ... ⊆ E}
      rintro m ⟨A, hA, hA_sub, rfl⟩
      exact ⟨A, hA, Set.Subset.trans hA_sub h_sub, rfl⟩
  · -- Jordan_inner_measure E ≤ Jordan_inner_measure (interior E)
    unfold Jordan_inner_measure
    apply csSup_le_csSup
    · -- ht: BddAbove {m | ∃ A, IsElementary A, A ⊆ interior E ∧ m = hA.measure}
      obtain ⟨B, hB, hEB⟩ := IsElementary.contains_bounded hE
      have h_sub_int_B : interior E ⊆ B := Set.Subset.trans interior_subset hEB
      refine ⟨hB.measure, ?_⟩
      rintro m ⟨A, hA, hA_sub, rfl⟩
      exact IsElementary.measure_mono hA hB (Set.Subset.trans hA_sub h_sub_int_B)
    · -- hs: {m | ∃ A, IsElementary A, A ⊆ E ∧ m = hA.measure}.Nonempty
      refine ⟨0, ?_⟩
      refine ⟨∅, IsElementary.empty d, Set.empty_subset _, ?_⟩
      exact Eq.symm (IsElementary.measure_of_empty d)
    · -- h: {m | ... ⊆ E} ⊆ {m | ... ⊆ interior E}
      rintro m ⟨A, hA, hA_sub_E, rfl⟩
      obtain ⟨T, hT_disj, hA_eq⟩ := hA.partition
      have h_box_sub_E (B : Box d) (hB : B ∈ T) : B.toSet ⊆ E := by
        intro x hx
        apply hA_sub_E
        rw [hA_eq]
        exact Set.mem_biUnion hB hx
      let f : Box d → Box d := λ B => { side := λ i => BoundedInterval.Ioo (B.side i).a (B.side i).b }
      have h_vol_eq (B : Box d) : |f B|ᵥ = |B|ᵥ := by
        simp [Box.volume, f, BoundedInterval.length]
      have h_open_sub (B : Box d) : (f B).toSet ⊆ B.toSet := by
        intro x hx
        rw [Box.mem_toSet] at hx ⊢
        intro i
        have hx_i : x i ∈ (BoundedInterval.Ioo (B.side i).a (B.side i).b : Set ℝ) := hx i
        have h_sub' : (BoundedInterval.Ioo (B.side i).a (B.side i).b : Set ℝ) ⊆ (B.side i : Set ℝ) :=
          BoundedInterval.Ioo_subset (B.side i)
        exact h_sub' hx_i
      have h_open_sub_int (B : Box d) : (f B).toSet ⊆ interior (B.toSet) := by
        refine interior_maximal (h_open_sub B) ?_
        have h_open : IsOpen ((f B).toSet) := by
          have h_eq : (f B).toSet = ⋂ i ∈ (Finset.univ : Finset (Fin d)), (fun (x : EuclideanSpace' d) => x i)⁻¹' (Set.Ioo ((B.side i).a) ((B.side i).b)) := by
            ext x; simp [Box.mem_toSet, f, Set.mem_iInter, Set.mem_preimage]
          rw [h_eq]
          refine isOpen_biInter_finset (fun i hi => ?_)
          apply IsOpen.preimage
          · exact PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i
          · exact isOpen_Ioo
        exact h_open
      have h_open_sub_int_E (B : Box d) (hB : B ∈ T) : (f B).toSet ⊆ interior E := by
        intro x hx
        have hx_int_B : x ∈ interior (B.toSet) := h_open_sub_int B hx
        have h_int_mono : interior (B.toSet) ⊆ interior E := interior_mono (h_box_sub_E B hB)
        exact h_int_mono hx_int_B
      set A' := ⋃ B ∈ T, (f B).toSet with hA'_def
      classical
      let T' : Finset (Box d) := T.image f
      have hA'_eq_boxes : A' = ⋃ B ∈ T', B.toSet := by
        ext x; simp [hA'_def, T', Box.mem_toSet, f]
      have hT'_disj : (T' : Set (Box d)).PairwiseDisjoint Box.toSet := by
        intro B₁' hB₁' B₂' hB₂' hne'
        have hB₁'_fin : B₁' ∈ T.image f := Finset.mem_coe.mp hB₁'
        have hB₂'_fin : B₂' ∈ T.image f := Finset.mem_coe.mp hB₂'
        rcases Finset.mem_image.mp hB₁'_fin with ⟨B₁, hB₁, rfl⟩
        rcases Finset.mem_image.mp hB₂'_fin with ⟨B₂, hB₂, rfl⟩
        have hne : B₁ ≠ B₂ := by
          intro h_eq
          apply hne'
          simp [h_eq]
        have h_base : Disjoint (B₁.toSet : Set (EuclideanSpace' d)) (B₂.toSet : Set (EuclideanSpace' d)) :=
          hT_disj hB₁ hB₂ hne
        refine h_base.mono (h_open_sub B₁) (h_open_sub B₂)
      let S' : Finset (Set (EuclideanSpace' d)) := T'.image (fun (B : Box d) => (B : Set (EuclideanSpace' d)))
      have hS'_elem : ∀ s ∈ S', IsElementary s := by
        intro s hs
        rcases Finset.mem_image.mp hs with ⟨B', hB', rfl⟩
        rcases Finset.mem_image.mp hB' with ⟨B, hB, rfl⟩
        exact IsElementary.box (f B)
      have hA'_elem : IsElementary A' := by
        have hA'_eq_sets : A' = ⋃ s ∈ S', s := by
          ext x; simp [hA'_eq_boxes, S']
        rw [hA'_eq_sets]
        exact IsElementary.union' hS'_elem
      have hA'_sub_int : A' ⊆ interior E := by
        intro x hx
        rw [hA'_def] at hx
        -- hx : x ∈ ⋃ B ∈ T, (f B).toSet
        -- This is Set.iUnion (fun (B : Box d) => Set.iUnion (fun (h : B ∈ (T : Set (Box d))) => (f B).toSet))
        -- But x ∈ Set.iUnion ... matches with rcases
        -- Try using conversion
        have hx' : ∃ (B' : Box d), ∃ (hB' : B' ∈ (T : Set (Box d))), x ∈ (f B').toSet := by simpa using hx
        rcases hx' with ⟨B', hB', hx⟩
        exact h_open_sub_int_E B' (Finset.mem_coe.mp hB') hx
      have h_zero_if_dup : ∀ B₁ ∈ T, ∀ B₂ ∈ T, B₁ ≠ B₂ → f B₁ = f B₂ → |f B₁|ᵥ = 0 := by
        intro B₁ hB₁ B₂ hB₂ hne h_eq
        have h_disj_box : Disjoint (B₁.toSet : Set (EuclideanSpace' d)) (B₂.toSet : Set (EuclideanSpace' d)) :=
          hT_disj hB₁ hB₂ hne
        have h_sub1 : (f B₁).toSet ⊆ B₁.toSet := h_open_sub B₁
        have h_sub2 : (f B₁).toSet ⊆ B₂.toSet := by
          intro x hx
          have hx' : x ∈ (f B₂).toSet := by simpa [h_eq] using hx
          exact h_open_sub B₂ hx'
        have h_inter : (f B₁).toSet ⊆ B₁.toSet ∩ B₂.toSet := by
          intro x hx; exact ⟨h_sub1 hx, h_sub2 hx⟩
        have h_empty_inter : B₁.toSet ∩ B₂.toSet = ∅ := Set.disjoint_iff_inter_eq_empty.mp h_disj_box
        have h_empty_f : (f B₁).toSet = ∅ := by
          apply Set.not_nonempty_iff_eq_empty.mp
          intro hne'
          rcases hne' with ⟨x, hx⟩
          have : x ∈ B₁.toSet ∩ B₂.toSet := h_inter hx
          rw [h_empty_inter] at this
          exact this
        exact Box.volume_eq_zero_of_empty (f B₁) h_empty_f
      have h_sum_eq : ∑ B' ∈ T', |B'|ᵥ = ∑ B ∈ T, |B|ᵥ := by
        let T_nonzero := T.filter (λ B => |f B|ᵥ ≠ 0)
        let T_zero := T.filter (λ B => |f B|ᵥ = 0)
        have h_disjoint : Disjoint T_nonzero T_zero := by
          apply (Finset.disjoint_filter (s := T) (p := λ B => |f B|ᵥ ≠ 0) (q := λ B => |f B|ᵥ = 0)).mpr
          intro B hB hpos hzero
          exact hpos hzero
        have h_T_union : T = T_nonzero ∪ T_zero := by
          ext B; simp [T_nonzero, T_zero, h_vol_eq]; tauto
        have h_T0_sum : ∑ B ∈ T_zero, |B|ᵥ = 0 := by
          refine Finset.sum_eq_zero ?_
          intro B hB
          rcases Finset.mem_filter.mp hB with ⟨hBT, hzero⟩
          calc
            |B|ᵥ = |f B|ᵥ := by symm; exact h_vol_eq B
            _ = 0 := hzero
        have h_T_sum : ∑ B ∈ T, |B|ᵥ = ∑ B ∈ T_nonzero, |B|ᵥ := by
          calc
            ∑ B ∈ T, |B|ᵥ = ∑ B ∈ T_nonzero, |B|ᵥ + ∑ B ∈ T_zero, |B|ᵥ := by
              rw [h_T_union, Finset.sum_union h_disjoint]
            _ = ∑ B ∈ T_nonzero, |B|ᵥ := by simp [h_T0_sum]
        have h_nonzero_inj : Set.InjOn f (T_nonzero : Set (Box d)) := by
          intro B₁ hB₁ B₂ hB₂ h_eq
          rcases Finset.mem_filter.mp hB₁ with ⟨hB₁T, hB₁pos⟩
          rcases Finset.mem_filter.mp hB₂ with ⟨hB₂T, hB₂pos⟩
          by_contra! hne
          have hzero : |f B₁|ᵥ = 0 := h_zero_if_dup B₁ hB₁T B₂ hB₂T hne h_eq
          rw [hzero] at hB₁pos
          exact hB₁pos rfl
        have h_image_nonzero_sum : ∑ B' ∈ T_nonzero.image f, |B'|ᵥ = ∑ B ∈ T_nonzero, |f B|ᵥ :=
          Finset.sum_image h_nonzero_inj
        have h_image_sum_nonzero_subset : T_nonzero.image f ⊆ T.image f :=
          Finset.image_subset_image (f := f) (Finset.filter_subset (λ B => |f B|ᵥ ≠ 0) T)
        have h_image_diff_sum_zero : ∑ B' ∈ T.image f \ T_nonzero.image f, |B'|ᵥ = 0 := by
          apply Finset.sum_eq_zero
          intro B' hB'
          rcases Finset.mem_sdiff.mp hB' with ⟨hB'_img, hB'_not⟩
          rcases Finset.mem_image.mp hB'_img with ⟨B, hB, rfl⟩
          have hB_zero : |f B|ᵥ = 0 := by
            by_cases h : |f B|ᵥ ≠ 0
            · exfalso
              apply hB'_not
              apply Finset.mem_image.mpr
              exact ⟨B, Finset.mem_filter.mpr ⟨hB, h⟩, rfl⟩
            · push_neg at h
              exact h
          simp [hB_zero]
        calc
          ∑ B' ∈ T', |B'|ᵥ = ∑ B' ∈ T.image f, |B'|ᵥ := rfl
          _ = (∑ B' ∈ T.image f \ T_nonzero.image f, |B'|ᵥ) + (∑ B' ∈ T_nonzero.image f, |B'|ᵥ) := by
            rw [(Finset.sum_sdiff h_image_sum_nonzero_subset).symm]
          _ = (∑ B' ∈ T_nonzero.image f, |B'|ᵥ) + (∑ B' ∈ T.image f \ T_nonzero.image f, |B'|ᵥ) := by ring
          _ = ∑ B' ∈ T_nonzero.image f, |B'|ᵥ := by simp [h_image_diff_sum_zero]
          _ = ∑ B ∈ T_nonzero, |f B|ᵥ := h_image_nonzero_sum
          _ = ∑ B ∈ T_nonzero, |B|ᵥ := by simp [h_vol_eq]
          _ = ∑ B ∈ T, |B|ᵥ := by rw [h_T_sum]
      have hA'_measure : hA'_elem.measure = hA.measure := by
        have hA_meas : hA.measure = ∑ B ∈ T, |B|ᵥ :=
          IsElementary.measure_eq hA hT_disj hA_eq
        have hA'_meas : hA'_elem.measure = ∑ B ∈ T', |B|ᵥ :=
          IsElementary.measure_eq hA'_elem hT'_disj hA'_eq_boxes
        rw [hA'_meas, h_sum_eq, hA_meas]
      exact ⟨A', hA'_elem, hA'_sub_int, hA'_measure.symm⟩

/-- Exercise 1.1.18 (3) -/
-- A bounded set is Jordan measurable if and only if its boundary is Jordan null.
theorem JordanMeasurable.iff_boundary_null {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E) :
  JordanMeasurable E ↔ JordanMeasurable.null (frontier E) := by
  constructor
  · intro hJM
    have hBounded_frontier : Bornology.IsBounded (frontier E) :=
      hE.closure.subset frontier_subset_closure
    have h_inner_mono : Jordan_inner_measure E ≤ Jordan_inner_measure (closure E) := by
      unfold Jordan_inner_measure
      refine csSup_le_csSup ?_ ?_ ?_
      · obtain ⟨C, hC, hC_cover⟩ := IsElementary.contains_bounded hE.closure
        refine ⟨hC.measure, ?_⟩
        rintro m ⟨A, hA, hA_sub, rfl⟩
        exact IsElementary.measure_mono hA hC (Set.Subset.trans hA_sub hC_cover)
      · refine ⟨0, ∅, IsElementary.empty d, Set.empty_subset _, ?_⟩
        exact (IsElementary.measure_of_empty d).symm
      · rintro m ⟨A, hA, hA_sub, rfl⟩
        exact ⟨A, hA, Set.Subset.trans hA_sub subset_closure, rfl⟩
    have hCl_outer_eq : Jordan_outer_measure (closure E) = hJM.measure := by
      rw [JordanMeasurable.outer_measure_of_closure hE, hJM.eq_outer]
    have hCl_inner_eq : Jordan_inner_measure (closure E) = hJM.measure := by
      apply le_antisymm
      · calc
          Jordan_inner_measure (closure E) ≤ Jordan_outer_measure (closure E) :=
            Jordan_inner_le_outer hE.closure
          _ = hJM.measure := hCl_outer_eq
      · calc
          hJM.measure = Jordan_inner_measure E := hJM.eq_inner.symm
          _ ≤ Jordan_inner_measure (closure E) := h_inner_mono
    have hClJM : JordanMeasurable (closure E) :=
      ⟨hE.closure, hCl_inner_eq.trans hCl_outer_eq.symm⟩
    have hInt_inner_eq : Jordan_inner_measure (interior E) = hJM.measure := by
      rw [JordanMeasurable.inner_measure_of_interior hE, hJM.eq_inner]
    have hInt_bdd : Bornology.IsBounded (interior E) :=
      hE.closure.subset interior_subset_closure
    have hInt_outer_ge : hJM.measure ≤ Jordan_outer_measure (interior E) := by
      calc
        hJM.measure = Jordan_inner_measure (interior E) := hInt_inner_eq.symm
        _ ≤ Jordan_outer_measure (interior E) := Jordan_inner_le_outer hInt_bdd
    have hInt_outer_le : Jordan_outer_measure (interior E) ≤ hJM.measure := by
      calc
        Jordan_outer_measure (interior E) ≤ Jordan_outer_measure E :=
          Jordan_outer_measure_mono_of_subset interior_subset hE
        _ = hJM.measure := hJM.eq_outer.symm
    have hInt_outer_eq : Jordan_outer_measure (interior E) = hJM.measure :=
      le_antisymm hInt_outer_le hInt_outer_ge
    have hIntJM : JordanMeasurable (interior E) :=
      ⟨hInt_bdd, hInt_inner_eq.trans hInt_outer_eq.symm⟩
    have hFrJM : JordanMeasurable (frontier E) := JordanMeasurable.sdiff hClJM hIntJM
    have h_disjoint : Disjoint (interior E) (frontier E) := by
      rw [frontier]
      exact Set.disjoint_iff_inter_eq_empty.mpr (Set.inter_diff_self (interior E) (closure E))
    have h_add : (hIntJM.union hFrJM).measure = hIntJM.measure + hFrJM.measure :=
      JordanMeasurable.mes_of_disjUnion hIntJM hFrJM h_disjoint
    have h_union_eq : closure E = interior E ∪ frontier E :=
      closure_eq_interior_union_frontier E
    have h_eq_measure : (hIntJM.union hFrJM).measure = hClJM.measure := by
      calc
        (hIntJM.union hFrJM).measure = Jordan_inner_measure (interior E ∪ frontier E) := rfl
        _ = Jordan_inner_measure (closure E) := by rw [h_union_eq]
        _ = hClJM.measure := rfl
    have h_sum : hClJM.measure = hIntJM.measure + hFrJM.measure := by
      rw [← h_eq_measure, h_add]
    have h_int_measure_eq : hIntJM.measure = hClJM.measure := by
      calc
        hIntJM.measure = Jordan_inner_measure (interior E) := rfl
        _ = hJM.measure := hInt_inner_eq
        _ = Jordan_inner_measure (closure E) := hCl_inner_eq.symm
        _ = hClJM.measure := rfl
    have h_fr_measure_zero : hFrJM.measure = 0 := by
      linarith
    have h_outer_zero : Jordan_outer_measure (frontier E) = 0 := by
      calc
        Jordan_outer_measure (frontier E) = hFrJM.measure := hFrJM.eq_outer.symm
        _ = 0 := h_fr_measure_zero
    rw [JordanMeasurable.null_iff]
    exact ⟨hBounded_frontier, h_outer_zero⟩
  · rintro ⟨hFrJM, hFr_measure⟩
    have h_frontier_outer_zero : Jordan_outer_measure (frontier E) = 0 := by
      calc
        Jordan_outer_measure (frontier E) = hFrJM.measure := hFrJM.eq_outer.symm
        _ = 0 := hFr_measure
    exact JordanMeasurable.if_frontier_null hE h_frontier_outer_zero

/-- The unit square with all rational points removed (not Jordan measurable). -/
abbrev bullet_riddled_square : Set (EuclideanSpace' 2) := { x | ∀ i, x i ∈ Set.Icc 0 1 ∧ x i ∉ (fun (q:ℚ) ↦ (q:ℝ)) '' .univ}

/-- The set of rational points in the unit square (not Jordan measurable). -/
abbrev bullets : Set (EuclideanSpace' 2) := { x | ∀ i, x i ∈ Set.Icc 0 1 ∧ x i ∈ (fun (q:ℚ) ↦ (q:ℝ)) '' .univ}

/-- The bullet-riddled square has inner Jordan measure 0 (no elementary subset). -/
theorem bullet_riddled_square.inner : Jordan_inner_measure bullet_riddled_square = 0 := by
  have h_zero_measure : ∀ (A : Set (EuclideanSpace' 2)) (hA : IsElementary A), A ⊆ bullet_riddled_square → hA.measure = 0 := by
    intro A hA hA_sub
    by_contra! hpos
    have hpos' : 0 < hA.measure := by
      have hnonneg := IsElementary.measure_nonneg hA
      by_contra! hle; apply hpos; linarith
    obtain ⟨T, hT_disj, hA_eq⟩ := hA.partition
    have h_measure_eq : hA.measure = ∑ B ∈ T, |B|ᵥ := hA.measure_eq hT_disj hA_eq
    rw [h_measure_eq] at hpos'
    have h_pos_box : ∃ B ∈ T, 0 < |B|ᵥ := by
      by_contra! h_all
      have h_sum : ∑ B ∈ T, |B|ᵥ ≤ 0 := Finset.sum_nonpos fun B hB => h_all B hB
      linarith
    rcases h_pos_box with ⟨B, hB, hB_vol⟩
    have h_side_len_pos : ∀ i : Fin 2, 0 < |B.side i|ₗ := by
      intro i
      have h_nonneg : 0 ≤ |B.side i|ₗ := BoundedInterval.length_nonneg (B.side i)
      by_contra! hle
      have h_zero : |B.side i|ₗ = 0 := by linarith
      have h_vol_zero : |B|ᵥ = 0 := by
        rw [Box.volume]
        apply Finset.prod_eq_zero (Finset.mem_univ i) h_zero
      linarith
    have h_side_lt : ∀ i : Fin 2, (B.side i).a < (B.side i).b := by
      intro i
      have h_len : |B.side i|ₗ = max ((B.side i).b - (B.side i).a) 0 := rfl
      have h_pos_len : 0 < |B.side i|ₗ := h_side_len_pos i
      rw [h_len] at h_pos_len
      by_contra! hle
      have : max ((B.side i).b - (B.side i).a) 0 = 0 := by
        apply max_eq_right; linarith
      rw [this] at h_pos_len; linarith
    have h_rationals : ∀ i : Fin 2, ∃ q : ℚ, (B.side i).a < (q : ℝ) ∧ (q : ℝ) < (B.side i).b :=
      fun i => exists_rat_btwn (h_side_lt i)
    choose q hq1 hq2 using h_rationals
    let x : EuclideanSpace' 2 := .toLp 2 (fun i => (q i : ℝ))
    have hx_box : x ∈ (B : Set (EuclideanSpace' 2)) := by
      rw [Box.mem_toSet]
      intro i
      have h_open : (q i : ℝ) ∈ Set.Ioo ((B.side i).a) ((B.side i).b) :=
        Set.mem_Ioo.mpr ⟨hq1 i, hq2 i⟩
      have h_sub : Set.Ioo ((B.side i).a) ((B.side i).b) ⊆ (B.side i : Set ℝ) :=
        BoundedInterval.Ioo_subset (B.side i)
      simpa [x] using h_sub h_open
    have hx_A : x ∈ A := by
      rw [hA_eq]
      refine Set.mem_iUnion₂.mpr ⟨B, hB, hx_box⟩
    have hx_brs : x ∈ bullet_riddled_square := hA_sub hx_A
    have h_no_rational : ∀ i : Fin 2, x i ∉ (fun (q : ℚ) ↦ (q : ℝ)) '' Set.univ :=
      fun i => (hx_brs i).2
    have h_rational_0 : x 0 ∈ (fun (q : ℚ) ↦ (q : ℝ)) '' Set.univ := by
      simp [x]
    exact h_no_rational 0 h_rational_0
  apply le_antisymm
  · unfold Jordan_inner_measure
    apply csSup_le
    · use 0; use ∅; use IsElementary.empty 2; simp [IsElementary.measure_of_empty]
    · intro m hm
      obtain ⟨A, hA, hA_sub, rfl⟩ := hm
      have hzero : hA.measure = 0 := h_zero_measure A hA hA_sub
      linarith
  · exact Jordan_inner_measure_nonneg _

/-- The bullet-riddled square has outer Jordan measure 1 (fills the unit square). -/
theorem bullet_riddled_square.outer : Jordan_outer_measure bullet_riddled_square = 1 := by
  let U : Box 2 := { side := fun _ => BoundedInterval.Icc (0 : ℝ) 1 }
  have hU_elem : IsElementary (U : Set (EuclideanSpace' 2)) := IsElementary.box U
  have hU_measure : hU_elem.measure = 1 := by
    calc
      hU_elem.measure = |U|ᵥ := IsElementary.measure_of_box U
      _ = ∏ i : Fin 2, |U.side i|ₗ := rfl
      _ = ∏ i : Fin 2, |(BoundedInterval.Icc (0 : ℝ) 1 : BoundedInterval)|ₗ := rfl
      _ = ∏ i : Fin 2, max (1 - 0) 0 := rfl
      _ = ∏ i : Fin 2, 1 := by simp
      _ = 1 := by simp
  have h_sub_brs_U : bullet_riddled_square ⊆ (U : Set (EuclideanSpace' 2)) := by
    intro x hx i; exact (hx i).1
  apply le_antisymm
  · unfold Jordan_outer_measure
    apply csInf_le
    · refine ⟨0, ?_⟩
      rintro m ⟨A, hA, _, rfl⟩; exact IsElementary.measure_nonneg hA
    · refine ⟨U, hU_elem, h_sub_brs_U, hU_measure.symm⟩
  · have h_ge_one : ∀ (A : Set (EuclideanSpace' 2)) (hA : IsElementary A), bullet_riddled_square ⊆ A → 1 ≤ hA.measure := by
      intro A hA hA_sup
      set D := (U : Set (EuclideanSpace' 2)) \ A with hD_def
      have hD_elem : IsElementary D := IsElementary.sdiff hU_elem hA
      have hD_measure_zero : hD_elem.measure = 0 := by
        by_contra! hpos
        have hpos' : 0 < hD_elem.measure := by
          have hnonneg := IsElementary.measure_nonneg hD_elem
          by_contra! hle; apply hpos; linarith
        obtain ⟨T, hT_disj, hD_eq⟩ := hD_elem.partition
        have h_measure_eq : hD_elem.measure = ∑ B ∈ T, |B|ᵥ := hD_elem.measure_eq hT_disj hD_eq
        rw [h_measure_eq] at hpos'
        have h_pos_box : ∃ B ∈ T, 0 < |B|ᵥ := by
          by_contra! h_all
          have h_sum : ∑ B ∈ T, |B|ᵥ ≤ 0 := Finset.sum_nonpos fun B hB => h_all B hB
          linarith
        rcases h_pos_box with ⟨B, hB, hB_vol⟩
        have h_side_len_pos : ∀ i : Fin 2, 0 < |B.side i|ₗ := by
          intro i
          have h_nonneg : 0 ≤ |B.side i|ₗ := BoundedInterval.length_nonneg (B.side i)
          by_contra! hle
          have h_zero : |B.side i|ₗ = 0 := by linarith
          have h_vol_zero : |B|ᵥ = 0 := by
            rw [Box.volume]
            apply Finset.prod_eq_zero (Finset.mem_univ i) h_zero
          linarith
        have h_side_lt : ∀ i : Fin 2, (B.side i).a < (B.side i).b := by
          intro i
          have h_len : |B.side i|ₗ = max ((B.side i).b - (B.side i).a) 0 := rfl
          have h_pos_len : 0 < |B.side i|ₗ := h_side_len_pos i
          rw [h_len] at h_pos_len
          by_contra! hle
          have : max ((B.side i).b - (B.side i).a) 0 = 0 := by
            apply max_eq_right; linarith
          rw [this] at h_pos_len; linarith
        have h_irrational_point : ∃ x : EuclideanSpace' 2, x ∈ (B : Set (EuclideanSpace' 2)) ∧ x ∈ bullet_riddled_square := by
          have h_irrationals : ∀ i : Fin 2, ∃ r : ℝ, Irrational r ∧ (B.side i).a < r ∧ r < (B.side i).b :=
            fun i => exists_irrational_btwn (h_side_lt i)
          choose r hir hr1 hr2 using h_irrationals
          let x : EuclideanSpace' 2 := .toLp 2 r
          have hx_box : x ∈ (B : Set (EuclideanSpace' 2)) := by
            rw [Box.mem_toSet]
            intro i
            have h_open : r i ∈ Set.Ioo ((B.side i).a) ((B.side i).b) :=
              Set.mem_Ioo.mpr ⟨hr1 i, hr2 i⟩
            have h_sub : Set.Ioo ((B.side i).a) ((B.side i).b) ⊆ (B.side i : Set ℝ) :=
              BoundedInterval.Ioo_subset (B.side i)
            simpa [x] using h_sub h_open
          have hx_brs : x ∈ bullet_riddled_square := by
            intro i
            have hB_sub_D : (B : Set (EuclideanSpace' 2)) ⊆ D := by
              rw [hD_eq]
              intro y hy; exact Set.mem_iUnion₂.mpr ⟨B, hB, hy⟩
            have hB_sub_U : (B : Set (EuclideanSpace' 2)) ⊆ (U : Set (EuclideanSpace' 2)) :=
              Set.Subset.trans hB_sub_D (Set.diff_subset (s := (U : Set (EuclideanSpace' 2))) (t := A))
            have hxU : x ∈ (U : Set (EuclideanSpace' 2)) := hB_sub_U hx_box
            have hx_i_Icc : x i ∈ Set.Icc (0 : ℝ) 1 := hxU i
            have h_not_rational : x i ∉ (fun (q : ℚ) ↦ (q : ℝ)) '' Set.univ := by
              have hxi_eq : x i = r i := by simp [x]
              rw [hxi_eq]
              intro h; rcases h with ⟨q, _, hq⟩; exact hir i ⟨q, hq⟩
            exact ⟨hx_i_Icc, h_not_rational⟩
          exact ⟨x, hx_box, hx_brs⟩
        obtain ⟨x, hx_B, hx_brs⟩ := h_irrational_point
        have hx_D : x ∈ D := by
          rw [hD_eq]
          exact Set.mem_iUnion₂.mpr ⟨B, hB, hx_B⟩
        have h_disjoint : D ∩ bullet_riddled_square = ∅ := by
          ext x; exact ⟨by { rintro ⟨⟨hxU, hxA⟩, hxBr⟩; exact hxA (hA_sup hxBr) }, by { intro h; exfalso; exact h }⟩
        have hx_mem : x ∈ D ∩ bullet_riddled_square := ⟨hx_D, hx_brs⟩
        rw [h_disjoint] at hx_mem; simp at hx_mem
      have h_inter_elem : IsElementary ((U : Set (EuclideanSpace' 2)) ∩ A) := IsElementary.inter hU_elem hA
      have h_disjoint_union : Disjoint D ((U : Set (EuclideanSpace' 2)) ∩ A) := by
        rw [hD_def]; exact Set.disjoint_sdiff_inter
      have h_union_eq : (U : Set (EuclideanSpace' 2)) = D ∪ ((U : Set (EuclideanSpace' 2)) ∩ A) := by
        ext x; constructor
        · intro hxU
          by_cases hxA : x ∈ A
          · apply Or.inr; exact ⟨hxU, hxA⟩
          · apply Or.inl; exact ⟨hxU, hxA⟩
        · rintro (⟨hxU, hxA⟩ | ⟨hxU, hxA⟩)
          · exact hxU
          · exact hxU
      have h_U_measure_eq : hU_elem.measure = hD_elem.measure + h_inter_elem.measure := by
        have h_disj_measure : (hD_elem.union h_inter_elem).measure = hD_elem.measure + h_inter_elem.measure :=
          IsElementary.measure_of_disjUnion hD_elem h_inter_elem h_disjoint_union
        have h_eq_measure : hU_elem.measure = (hD_elem.union h_inter_elem).measure :=
          IsElementary.measure_eq_of_set_eq hU_elem (hD_elem.union h_inter_elem) h_union_eq
        rw [h_eq_measure, h_disj_measure]
      have h1_eq_hinter : 1 = h_inter_elem.measure := by
        rw [hU_measure, hD_measure_zero, zero_add] at h_U_measure_eq
        exact h_U_measure_eq
      have h_inter_sub_A : (U : Set (EuclideanSpace' 2)) ∩ A ⊆ A :=
        Set.inter_subset_right (s := (U : Set (EuclideanSpace' 2))) (t := A)
      have h_mono : h_inter_elem.measure ≤ hA.measure :=
        IsElementary.measure_mono h_inter_elem hA h_inter_sub_A
      rw [← h1_eq_hinter] at h_mono
      exact h_mono
    unfold Jordan_outer_measure
    apply le_csInf
    · have h_bounded : Bornology.IsBounded (bullet_riddled_square : Set (EuclideanSpace' 2)) := by
        have hU_bounded : Bornology.IsBounded (U : Set (EuclideanSpace' 2)) :=
          (IsElementary.box U).isBounded
        exact hU_bounded.subset h_sub_brs_U
      obtain ⟨B, hB, hB_sup⟩ := IsElementary.contains_bounded h_bounded
      exact ⟨hB.measure, B, hB, hB_sup, rfl⟩
    · intro m hm
      obtain ⟨A, hA, hA_sup, rfl⟩ := hm
      exact h_ge_one A hA hA_sup

/-- The rational points in the unit square have inner Jordan measure 0. -/
theorem bullets.inner : Jordan_inner_measure bullets = 0 := by
  have h_zero_measure : ∀ (A : Set (EuclideanSpace' 2)) (hA : IsElementary A), A ⊆ bullets → hA.measure = 0 := by
    intro A hA hA_sub
    by_contra! hpos
    have hpos' : 0 < hA.measure := by
      have hnonneg := IsElementary.measure_nonneg hA
      by_contra! hle; apply hpos; linarith
    obtain ⟨T, hT_disj, hA_eq⟩ := hA.partition
    have h_measure_eq : hA.measure = ∑ B ∈ T, |B|ᵥ := hA.measure_eq hT_disj hA_eq
    rw [h_measure_eq] at hpos'
    have h_pos_box : ∃ B ∈ T, 0 < |B|ᵥ := by
      by_contra! h_all
      have h_sum : ∑ B ∈ T, |B|ᵥ ≤ 0 := Finset.sum_nonpos fun B hB => h_all B hB
      linarith
    rcases h_pos_box with ⟨B, hB, hB_vol⟩
    have h_side_len_pos : ∀ i : Fin 2, 0 < |B.side i|ₗ := by
      intro i
      have h_nonneg : 0 ≤ |B.side i|ₗ := BoundedInterval.length_nonneg (B.side i)
      by_contra! hle
      have h_zero : |B.side i|ₗ = 0 := by linarith
      have h_vol_zero : |B|ᵥ = 0 := by
        rw [Box.volume]
        apply Finset.prod_eq_zero (Finset.mem_univ i) h_zero
      linarith
    have h_side_lt : ∀ i : Fin 2, (B.side i).a < (B.side i).b := by
      intro i
      have h_len : |B.side i|ₗ = max ((B.side i).b - (B.side i).a) 0 := rfl
      have h_pos_len : 0 < |B.side i|ₗ := h_side_len_pos i
      rw [h_len] at h_pos_len
      by_contra! hle
      have : max ((B.side i).b - (B.side i).a) 0 = 0 := by
        apply max_eq_right; linarith
      rw [this] at h_pos_len; linarith
    have h_irrationals : ∀ i : Fin 2, ∃ r : ℝ, Irrational r ∧ (B.side i).a < r ∧ r < (B.side i).b :=
      fun i => exists_irrational_btwn (h_side_lt i)
    choose r hir hr1 hr2 using h_irrationals
    let x : EuclideanSpace' 2 := .toLp 2 r
    have hx_box : x ∈ (B : Set (EuclideanSpace' 2)) := by
      rw [Box.mem_toSet]
      intro i
      have h_open : r i ∈ Set.Ioo ((B.side i).a) ((B.side i).b) :=
        Set.mem_Ioo.mpr ⟨hr1 i, hr2 i⟩
      have h_sub : Set.Ioo ((B.side i).a) ((B.side i).b) ⊆ (B.side i : Set ℝ) :=
        BoundedInterval.Ioo_subset (B.side i)
      simpa [x] using h_sub h_open
    have hx_A : x ∈ A := by
      rw [hA_eq]
      refine Set.mem_iUnion₂.mpr ⟨B, hB, hx_box⟩
    have hx_bullets : x ∈ bullets := hA_sub hx_A
    have h_rational : ∀ i : Fin 2, x i ∈ (fun (q : ℚ) ↦ (q : ℝ)) '' Set.univ :=
      fun i => (hx_bullets i).2
    have h_irrational_0 : x 0 ∉ (fun (q : ℚ) ↦ (q : ℝ)) '' Set.univ := by
      have hx0 : x 0 = r 0 := by simp [x]
      rw [hx0]
      intro h; rcases h with ⟨q, _, hq⟩; exact hir 0 ⟨q, hq⟩
    exact h_irrational_0 (h_rational 0)
  apply le_antisymm
  · unfold Jordan_inner_measure
    apply csSup_le
    · use 0; use ∅; use IsElementary.empty 2; simp [IsElementary.measure_of_empty]
    · intro m hm
      obtain ⟨A, hA, hA_sub, rfl⟩ := hm
      have hzero : hA.measure = 0 := h_zero_measure A hA hA_sub
      linarith
  · exact Jordan_inner_measure_nonneg _

/-- The rational points in the unit square have outer Jordan measure 1. -/
theorem bullets.outer : Jordan_outer_measure bullets = 1 := by
  let U : Box 2 := { side := fun _ => BoundedInterval.Icc (0 : ℝ) 1 }
  have hU_elem : IsElementary (U : Set (EuclideanSpace' 2)) := IsElementary.box U
  have hU_measure : hU_elem.measure = 1 := by
    calc
      hU_elem.measure = |U|ᵥ := IsElementary.measure_of_box U
      _ = ∏ i : Fin 2, |U.side i|ₗ := rfl
      _ = ∏ i : Fin 2, |(BoundedInterval.Icc (0 : ℝ) 1 : BoundedInterval)|ₗ := rfl
      _ = ∏ i : Fin 2, max (1 - 0) 0 := rfl
      _ = ∏ i : Fin 2, 1 := by simp
      _ = 1 := by simp
  have h_sub_bullets_U : bullets ⊆ (U : Set (EuclideanSpace' 2)) := by
    intro x hx i; exact (hx i).1
  apply le_antisymm
  · unfold Jordan_outer_measure
    apply csInf_le
    · refine ⟨0, ?_⟩
      rintro m ⟨A, hA, _, rfl⟩; exact IsElementary.measure_nonneg hA
    · refine ⟨U, hU_elem, h_sub_bullets_U, hU_measure.symm⟩
  · have h_ge_one : ∀ (A : Set (EuclideanSpace' 2)) (hA : IsElementary A), bullets ⊆ A → 1 ≤ hA.measure := by
      intro A hA hA_sup
      set D := (U : Set (EuclideanSpace' 2)) \ A with hD_def
      have hD_elem : IsElementary D := IsElementary.sdiff hU_elem hA
      have hD_measure_zero : hD_elem.measure = 0 := by
        by_contra! hpos
        have hpos' : 0 < hD_elem.measure := by
          have hnonneg := IsElementary.measure_nonneg hD_elem
          by_contra! hle; apply hpos; linarith
        obtain ⟨T, hT_disj, hD_eq⟩ := hD_elem.partition
        have h_measure_eq : hD_elem.measure = ∑ B ∈ T, |B|ᵥ := hD_elem.measure_eq hT_disj hD_eq
        rw [h_measure_eq] at hpos'
        have h_pos_box : ∃ B ∈ T, 0 < |B|ᵥ := by
          by_contra! h_all
          have h_sum : ∑ B ∈ T, |B|ᵥ ≤ 0 := Finset.sum_nonpos fun B hB => h_all B hB
          linarith
        rcases h_pos_box with ⟨B, hB, hB_vol⟩
        have h_side_len_pos : ∀ i : Fin 2, 0 < |B.side i|ₗ := by
          intro i
          have h_nonneg : 0 ≤ |B.side i|ₗ := BoundedInterval.length_nonneg (B.side i)
          by_contra! hle
          have h_zero : |B.side i|ₗ = 0 := by linarith
          have h_vol_zero : |B|ᵥ = 0 := by
            rw [Box.volume]
            apply Finset.prod_eq_zero (Finset.mem_univ i) h_zero
          linarith
        have h_side_lt : ∀ i : Fin 2, (B.side i).a < (B.side i).b := by
          intro i
          have h_len : |B.side i|ₗ = max ((B.side i).b - (B.side i).a) 0 := rfl
          have h_pos_len : 0 < |B.side i|ₗ := h_side_len_pos i
          rw [h_len] at h_pos_len
          by_contra! hle
          have : max ((B.side i).b - (B.side i).a) 0 = 0 := by
            apply max_eq_right; linarith
          rw [this] at h_pos_len; linarith
        have h_rational_point : ∃ x : EuclideanSpace' 2, x ∈ (B : Set (EuclideanSpace' 2)) ∧ x ∈ bullets := by
          have h_rationals : ∀ i : Fin 2, ∃ q : ℚ, (B.side i).a < (q : ℝ) ∧ (q : ℝ) < (B.side i).b :=
            fun i => exists_rat_btwn (h_side_lt i)
          choose q hq1 hq2 using h_rationals
          let x : EuclideanSpace' 2 := .toLp 2 (fun i => (q i : ℝ))
          have hx_box : x ∈ (B : Set (EuclideanSpace' 2)) := by
            rw [Box.mem_toSet]
            intro i
            have h_open : (q i : ℝ) ∈ Set.Ioo ((B.side i).a) ((B.side i).b) :=
              Set.mem_Ioo.mpr ⟨hq1 i, hq2 i⟩
            have h_sub : Set.Ioo ((B.side i).a) ((B.side i).b) ⊆ (B.side i : Set ℝ) :=
              BoundedInterval.Ioo_subset (B.side i)
            simpa [x] using h_sub h_open
          have hx_bullets : x ∈ bullets := by
            intro i
            have hB_sub_D : (B : Set (EuclideanSpace' 2)) ⊆ D := by
              rw [hD_eq]
              intro y hy; exact Set.mem_iUnion₂.mpr ⟨B, hB, hy⟩
            have hB_sub_U : (B : Set (EuclideanSpace' 2)) ⊆ (U : Set (EuclideanSpace' 2)) :=
              Set.Subset.trans hB_sub_D (Set.diff_subset (s := (U : Set (EuclideanSpace' 2))) (t := A))
            have hxU : x ∈ (U : Set (EuclideanSpace' 2)) := hB_sub_U hx_box
            have hx_i_Icc : x i ∈ Set.Icc (0 : ℝ) 1 := hxU i
            have h_rational : x i ∈ (fun (q : ℚ) ↦ (q : ℝ)) '' Set.univ := by
              simp [x]
            exact ⟨hx_i_Icc, h_rational⟩
          exact ⟨x, hx_box, hx_bullets⟩
        obtain ⟨x, hx_B, hx_bullets⟩ := h_rational_point
        have hx_D : x ∈ D := by
          rw [hD_eq]
          exact Set.mem_iUnion₂.mpr ⟨B, hB, hx_B⟩
        have h_disjoint : D ∩ bullets = ∅ := by
          ext x; exact ⟨by { rintro ⟨⟨hxU, hxA⟩, hxBr⟩; exact hxA (hA_sup hxBr) }, by { intro h; exfalso; exact h }⟩
        have hx_mem : x ∈ D ∩ bullets := ⟨hx_D, hx_bullets⟩
        rw [h_disjoint] at hx_mem; simp at hx_mem
      have h_inter_elem : IsElementary ((U : Set (EuclideanSpace' 2)) ∩ A) := IsElementary.inter hU_elem hA
      have h_disjoint_union : Disjoint D ((U : Set (EuclideanSpace' 2)) ∩ A) := by
        rw [hD_def]; exact Set.disjoint_sdiff_inter
      have h_union_eq : (U : Set (EuclideanSpace' 2)) = D ∪ ((U : Set (EuclideanSpace' 2)) ∩ A) := by
        ext x; constructor
        · intro hxU
          by_cases hxA : x ∈ A
          · apply Or.inr; exact ⟨hxU, hxA⟩
          · apply Or.inl; exact ⟨hxU, hxA⟩
        · rintro (⟨hxU, hxA⟩ | ⟨hxU, hxA⟩)
          · exact hxU
          · exact hxU
      have h_U_measure_eq : hU_elem.measure = hD_elem.measure + h_inter_elem.measure := by
        have h_disj_measure : (hD_elem.union h_inter_elem).measure = hD_elem.measure + h_inter_elem.measure :=
          IsElementary.measure_of_disjUnion hD_elem h_inter_elem h_disjoint_union
        have h_eq_measure : hU_elem.measure = (hD_elem.union h_inter_elem).measure :=
          IsElementary.measure_eq_of_set_eq hU_elem (hD_elem.union h_inter_elem) h_union_eq
        rw [h_eq_measure, h_disj_measure]
      have h1_eq_hinter : 1 = h_inter_elem.measure := by
        rw [hU_measure, hD_measure_zero, zero_add] at h_U_measure_eq
        exact h_U_measure_eq
      have h_inter_sub_A : (U : Set (EuclideanSpace' 2)) ∩ A ⊆ A :=
        Set.inter_subset_right (s := (U : Set (EuclideanSpace' 2))) (t := A)
      have h_mono : h_inter_elem.measure ≤ hA.measure :=
        IsElementary.measure_mono h_inter_elem hA h_inter_sub_A
      rw [← h1_eq_hinter] at h_mono
      exact h_mono
    unfold Jordan_outer_measure
    apply le_csInf
    · have h_bounded : Bornology.IsBounded (bullets : Set (EuclideanSpace' 2)) := by
        have hU_bounded : Bornology.IsBounded (U : Set (EuclideanSpace' 2)) :=
          (IsElementary.box U).isBounded
        exact hU_bounded.subset h_sub_bullets_U
      obtain ⟨B, hB, hB_sup⟩ := IsElementary.contains_bounded h_bounded
      exact ⟨hB.measure, B, hB, hB_sup, rfl⟩
    · intro m hm
      obtain ⟨A, hA, hA_sup, rfl⟩ := hm
      exact h_ge_one A hA hA_sup

/-- The bullet-riddled square is not Jordan measurable (inner ≠ outer). -/
theorem bullet_riddled_square.not_jordanMeasurable : ¬ JordanMeasurable bullet_riddled_square := by
  intro hJM
  rcases hJM with ⟨_, h_eq⟩
  rw [bullet_riddled_square.inner, bullet_riddled_square.outer] at h_eq
  linarith

/-- The set of rational points is not Jordan measurable (inner ≠ outer). -/
theorem bullets.not_jordanMeasurable : ¬ JordanMeasurable bullets := by
  intro hJM
  rcases hJM with ⟨_, h_eq⟩
  rw [bullets.inner, bullets.outer] at h_eq
  linarith

/-- Exercise 1.1.19 (Caratheodory property) -/
theorem JordanMeasurable.caratheodory {d:ℕ} {E F: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E) (hF: IsElementary F) :
  Jordan_outer_measure E = Jordan_outer_measure (E ∩ F) + Jordan_outer_measure (E \ F) := by
  apply le_antisymm
  · -- ≤ direction
    refine le_of_forall_pos_le_add ?_
    intro ε hε
    have hε2 : ε/2 > 0 := by linarith
    set S_EF : Set ℝ := { m:ℝ | ∃ (A: Set (EuclideanSpace' d)), ∃ hA: IsElementary A, (E ∩ F) ⊆ A ∧ m = hA.measure } with hS_EF
    have h_nonempty_EF : S_EF.Nonempty := by
      have h_bounded : Bornology.IsBounded (E ∩ F) :=
        hE.subset (Set.inter_subset_left (s := E) (t := F))
      obtain ⟨A, hA, h_sub⟩ := IsElementary.contains_bounded h_bounded
      rw [hS_EF]
      exact ⟨hA.measure, A, hA, h_sub, rfl⟩
    have h_sInf_lt_EF : Jordan_outer_measure (E ∩ F) < Jordan_outer_measure (E ∩ F) + ε/2 := by
      nlinarith
    obtain ⟨m_EF, hm_EF, hm_EF_lt⟩ := exists_lt_of_csInf_lt h_nonempty_EF h_sInf_lt_EF
    obtain ⟨A, hA, hA_sub, rfl⟩ := hm_EF
    set S_EsF : Set ℝ := { m:ℝ | ∃ (A: Set (EuclideanSpace' d)), ∃ hA: IsElementary A, (E \ F) ⊆ A ∧ m = hA.measure } with hS_EsF
    have h_nonempty_EsF : S_EsF.Nonempty := by
      have h_bounded : Bornology.IsBounded (E \ F) :=
        hE.subset Set.diff_subset
      obtain ⟨A, hA, h_sub⟩ := IsElementary.contains_bounded h_bounded
      rw [hS_EsF]
      exact ⟨hA.measure, A, hA, h_sub, rfl⟩
    have h_sInf_lt_EsF : Jordan_outer_measure (E \ F) < Jordan_outer_measure (E \ F) + ε/2 := by
      nlinarith
    obtain ⟨m_EsF, hm_EsF, hm_EsF_lt⟩ := exists_lt_of_csInf_lt h_nonempty_EsF h_sInf_lt_EsF
    obtain ⟨B, hB, hB_sub, rfl⟩ := hm_EsF
    have hA_union_B : IsElementary (A ∪ B) := IsElementary.union hA hB
    have hE_sub_A_union_B : E ⊆ A ∪ B := by
      intro x hx
      by_cases hxF : x ∈ F
      · have : x ∈ E ∩ F := ⟨hx, hxF⟩
        exact Or.inl (hA_sub this)
      · have : x ∈ E \ F := ⟨hx, hxF⟩
        exact Or.inr (hB_sub this)
    have h_outer_le_union : Jordan_outer_measure E ≤ (hA_union_B).measure := by
      unfold Jordan_outer_measure
      apply csInf_le
      · refine ⟨0, ?_⟩
        rintro m ⟨A', hA', hA'_sub, rfl⟩
        exact IsElementary.measure_nonneg hA'
      · exact ⟨A ∪ B, hA_union_B, hE_sub_A_union_B, rfl⟩
    have h_union_measure : (hA_union_B).measure ≤ hA.measure + hB.measure :=
      IsElementary.measure_of_union hA hB
    have h_sum_lt : hA.measure + hB.measure < Jordan_outer_measure (E ∩ F) + Jordan_outer_measure (E \ F) + ε := by
      nlinarith
    nlinarith
  · -- ≥ direction
    refine le_of_forall_pos_le_add ?_
    intro ε hε
    set S_E : Set ℝ := { m:ℝ | ∃ (A: Set (EuclideanSpace' d)), ∃ hA: IsElementary A, E ⊆ A ∧ m = hA.measure } with hS_E
    have h_nonempty_E : S_E.Nonempty := by
      obtain ⟨A, hA, h_sub⟩ := IsElementary.contains_bounded hE
      rw [hS_E]
      exact ⟨hA.measure, A, hA, h_sub, rfl⟩
    have h_sInf_lt_E : Jordan_outer_measure E < Jordan_outer_measure E + ε := by
      nlinarith
    obtain ⟨m_E, hm_E, hm_E_lt⟩ := exists_lt_of_csInf_lt h_nonempty_E h_sInf_lt_E
    obtain ⟨C, hC, hC_sub_E, rfl⟩ := hm_E
    have hC_inter_F : IsElementary (C ∩ F) := IsElementary.inter hC hF
    have hC_sdiff_F : IsElementary (C \ F) := IsElementary.sdiff hC hF
    have h_sub_inter : (E ∩ F) ⊆ (C ∩ F) :=
      Set.inter_subset_inter hC_sub_E (Set.Subset.refl F)
    have h_sub_sdiff : (E \ F) ⊆ (C \ F) :=
      Set.diff_subset_diff hC_sub_E (Set.Subset.refl F)
    have h_disjoint : Disjoint (C ∩ F) (C \ F) :=
      (Set.disjoint_sdiff_inter (s := C) (t := F)).symm
    have h_union_eq : (C ∩ F) ∪ (C \ F) = C := by
      ext x; constructor
      · rintro (⟨hxC, hxF⟩ | ⟨hxC, hxF⟩)
        · exact hxC
        · exact hxC
      · intro hxC
        by_cases hxF : x ∈ F
        · exact Or.inl ⟨hxC, hxF⟩
        · exact Or.inr ⟨hxC, hxF⟩
    have h_outer_inter_le : Jordan_outer_measure (E ∩ F) ≤ hC_inter_F.measure := by
      unfold Jordan_outer_measure
      apply csInf_le
      · refine ⟨0, ?_⟩
        rintro m ⟨A', hA', hA'_sub, rfl⟩
        exact IsElementary.measure_nonneg hA'
      · exact ⟨C ∩ F, hC_inter_F, h_sub_inter, rfl⟩
    have h_outer_sdiff_le : Jordan_outer_measure (E \ F) ≤ hC_sdiff_F.measure := by
      unfold Jordan_outer_measure
      apply csInf_le
      · refine ⟨0, ?_⟩
        rintro m ⟨A', hA', hA'_sub, rfl⟩
        exact IsElementary.measure_nonneg hA'
      · exact ⟨C \ F, hC_sdiff_F, h_sub_sdiff, rfl⟩
    have h_measure_add : hC_inter_F.measure + hC_sdiff_F.measure = hC.measure := by
      calc
        hC_inter_F.measure + hC_sdiff_F.measure = (hC_inter_F.union hC_sdiff_F).measure := by
          symm; exact IsElementary.measure_of_disjUnion hC_inter_F hC_sdiff_F h_disjoint
        _ = hC.measure := IsElementary.measure_eq_of_set_eq (hC_inter_F.union hC_sdiff_F) hC h_union_eq
    have h_sum_lt : hC.measure < Jordan_outer_measure E + ε := hm_E_lt
    nlinarith

/-- The frontier of a Jordan measurable set has Lebesgue volume zero. -/
lemma JordanMeasurable.frontier_volume_zero {d:ℕ} {E: Set (EuclideanSpace' d)}
    (hE: JordanMeasurable E) : MeasureTheory.volume (frontier E) = 0 := by
  obtain ⟨hfr, hfr0⟩ := (JordanMeasurable.iff_boundary_null hE.1).mp hE
  have hv : hfr.measure = (MeasureTheory.volume (frontier E)).toReal :=
    JordanMeasurable.measure_eq_volume hfr
  rw [hfr0] at hv
  have hbd : Bornology.IsBounded (frontier E) := hE.1.closure.subset frontier_subset_closure
  have hlt : MeasureTheory.volume (frontier E) < ⊤ := volume_lt_top_of_bounded hbd
  rcases (ENNReal.toReal_eq_zero_iff _).mp hv.symm with h | h
  · exact h
  · exact absurd h hlt.ne

/-- A Jordan measurable set is null-measurable for Lebesgue measure. -/
lemma JordanMeasurable.nullMeasurableSet {d:ℕ} {E: Set (EuclideanSpace' d)}
    (hE: JordanMeasurable E) : MeasureTheory.NullMeasurableSet E MeasureTheory.volume := by
      have h_closure : E =ᵐ[MeasureTheory.volume] closure E := by
        have h_closure : MeasureTheory.volume (closure E \ E) = 0 := by
          refine' MeasureTheory.measure_mono_null _ ( hE.frontier_volume_zero );
          exact fun x hx => ⟨ hx.1, fun hx' => hx.2 <| interior_subset hx' ⟩
        rw [ MeasureTheory.ae_eq_set ];
        exact ⟨ by rw [ Set.diff_eq_empty.mpr ( subset_closure ) ] ; norm_num, h_closure ⟩;
      convert ( measurableSet_closure.nullMeasurableSet ) |> fun h => h.congr h_closure.symm using 1

/-
Exercise 1.1.17 (corrected: the pieces are assumed Jordan measurable).
If a Jordan measurable set `E` is partitioned into Jordan measurable pieces `P i` that are
isometric to Jordan measurable pieces `Q i` whose interiors are pairwise disjoint and whose union
is the Jordan measurable set `F`, then `E` and `F` have the same Jordan measure.
-/
theorem JordanMeasurable.measure_of_equidecomposable {d n:ℕ} {E F: Set (EuclideanSpace' d)}
  (hE: JordanMeasurable E) (hF: JordanMeasurable F)
  {P Q: Fin n → Set (EuclideanSpace' d)} (hPQ: ∀ i, Isometric (P i) (Q i))
  (hP: ∀ i, JordanMeasurable (P i)) (hQ: ∀ i, JordanMeasurable (Q i))
  (hPE: E = ⋃ i, P i) (hQF: F = ⋃ i, Q i) (hPdisj: Set.PairwiseDisjoint .univ P)
  (hQdisj: Set.PairwiseDisjoint .univ (fun i ↦ (interior (Q i)))) : hE.measure = hF.measure := by
  convert JordanMeasurable.measure_eq_volume hE using 1;
  rw [ hPE, MeasureTheory.measure_iUnion₀ ] <;> norm_num [ hPdisj, hP ];
  · rw [ hF.measure_eq_volume, hQF, MeasureTheory.measure_iUnion₀ ];
    · rw [ tsum_fintype, Finset.sum_congr rfl ];
      intro i hi; specialize hPQ i; exact (by
      convert isometric_measure_eq hPQ ( hP i ) ( hQ i ) using 1;
      rw [ ← ENNReal.toReal_eq_toReal_iff' ] <;> norm_num [ JordanMeasurable.measure_eq_volume ];
      · exact ne_of_lt ( volume_lt_top_of_bounded ( hQ i |>.1 ) );
      · exact ne_of_lt ( volume_lt_top_of_bounded ( hP i |>.1 ) ));
    · intro i j hij;
      have h_inter_subset : Q i ∩ Q j ⊆ frontier (Q i) ∪ frontier (Q j) := by
        intro x hx; by_cases hi : x ∈ interior ( Q i ) <;> by_cases hj : x ∈ interior ( Q j ) <;> simp_all +decide ;
        · exact absurd ( hQdisj ( Set.mem_univ i ) ( Set.mem_univ j ) hij ) ( Set.not_disjoint_iff.mpr ⟨ x, hi, hj ⟩ );
        · exact Or.inr ( by rw [ frontier_eq_closure_inter_closure ] ; exact ⟨ subset_closure hx.2, by aesop ⟩ );
        · exact Or.inl <| ⟨ subset_closure hx.1, hi ⟩;
        · exact Or.inl ⟨ subset_closure hx.1, hi ⟩;
      exact MeasureTheory.measure_mono_null h_inter_subset ( MeasureTheory.measure_union_null ( hQ i |> JordanMeasurable.frontier_volume_zero ) ( hQ j |> JordanMeasurable.frontier_volume_zero ) );
    · exact fun i => JordanMeasurable.nullMeasurableSet ( hQ i );
  · intro i j hij; specialize hPdisj ( Set.mem_univ i ) ( Set.mem_univ j ) hij; exact (by
    exact MeasureTheory.measure_mono_null ( fun x hx => by have := hPdisj.le_bot hx; aesop ) ( MeasureTheory.measure_empty ));
  · exact fun i => JordanMeasurable.nullMeasurableSet ( hP i )
