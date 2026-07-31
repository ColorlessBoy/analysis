import Analysis.MeasureTheory.Section_1_2_2

open Set
open EReal

lemma symmDiff_sub_symmDiff_union_symmDiff {α : Type*} {X Y Z : Set α} : symmDiff X Z ⊆ symmDiff X Y ∪ symmDiff Y Z := by
  intro x hx
  rw [Set.symmDiff_def] at hx
  rcases hx with (⟨hxX, hx_not_Z⟩ | ⟨hxZ, hx_not_X⟩)
  · by_cases hxY : x ∈ Y
    · apply Set.mem_union_right; rw [Set.symmDiff_def]; exact Or.inl ⟨hxY, hx_not_Z⟩
    · apply Set.mem_union_left; rw [Set.symmDiff_def]; exact Or.inl ⟨hxX, hxY⟩
  · by_cases hxY : x ∈ Y
    · apply Set.mem_union_left; rw [Set.symmDiff_def]; exact Or.inr ⟨hxY, hx_not_X⟩
    · apply Set.mem_union_right; rw [Set.symmDiff_def]; exact Or.inr ⟨hxZ, hxY⟩

/-- An Ioo box (product of open intervals) is open in EuclideanSpace' d (d > 0). -/
lemma Ioo_box_isOpen {d : ℕ} (hd_pos : 0 < d) (a b : Fin d → ℝ) :
    IsOpen {x : EuclideanSpace' d | ∀ i : Fin d, a i < x i ∧ x i < b i} := by
  rw [Metric.isOpen_iff]
  intro x hx
  have h_dists_pos : ∀ i : Fin d, 0 < min (x i - a i) (b i - x i) := by
    intro i
    have hi : a i < x i ∧ x i < b i := hx i
    exact lt_min_iff.mpr ⟨sub_pos.mpr hi.1, sub_pos.mpr hi.2⟩
  haveI : Nonempty (Fin d) := by
    -- Since d > 0, Fin d is nonempty
    have h : 0 < d := hd_pos
    exact ⟨⟨0, hd_pos⟩⟩
  -- Use a simple radius: we take the minimum over all coordinates of the distance to boundary
  -- Since Fin d is finite, we can compute this minimum
  have hmin_exists : ∃ r : ℝ, 0 < r ∧ ∀ i : Fin d, min (x i - a i) (b i - x i) ≥ r := by
    -- The set of all such minima is finite, so the minimum is positive
    let S : Finset ℝ := Finset.image (fun (i : Fin d) => min (x i - a i) (b i - x i)) Finset.univ
    have hS_nonempty : S.Nonempty := by
      refine Finset.image_nonempty.mpr Finset.univ_nonempty
    have hS_pos : ∀ r ∈ S, 0 < r := by
      intro r hr
      rcases Finset.mem_image.mp hr with ⟨i, hi, rfl⟩
      exact h_dists_pos i
    refine ⟨S.min' hS_nonempty, hS_pos (S.min' hS_nonempty) (Finset.min'_mem _ hS_nonempty), ?_⟩
    intro i
    have hmem : min (x i - a i) (b i - x i) ∈ S := by
      apply Finset.mem_image.mpr; exact ⟨i, Finset.mem_univ i, rfl⟩
    have hle : S.min' (⟨min (x i - a i) (b i - x i), hmem⟩ : S.Nonempty) ≤ min (x i - a i) (b i - x i) :=
      Finset.min'_le (s := S) (x := min (x i - a i) (b i - x i)) hmem
    have : S.min' hS_nonempty ≤ min (x i - a i) (b i - x i) := by
      simpa using hle
    exact this
  rcases hmin_exists with ⟨r, hr_pos, hr_bound⟩
  set ε := r / Real.sqrt (d : ℝ) with hε
  have hε_pos : 0 < ε := div_pos hr_pos (Real.sqrt_pos.mpr (by exact_mod_cast hd_pos))
  refine ⟨ε, hε_pos, ?_⟩
  intro y hy
  rw [Metric.mem_ball, dist_eq_norm] at hy
  have h_coord_bound : ∀ i : Fin d, |y i - x i| < ε := by
    intro i
    have : |y i - x i| ≤ ‖y - x‖ := EuclideanSpace'.coord_le_norm (y - x) i
    exact lt_of_le_of_lt this hy
  intro i
  have hx_diff_lo : x i - a i ≥ r :=
    (hr_bound i).trans (by
      have : min (x i - a i) (b i - x i) ≤ x i - a i := min_le_left _ _
      exact this)
  have hx_diff_hi : b i - x i ≥ r :=
    (hr_bound i).trans (by
      have : min (x i - a i) (b i - x i) ≤ b i - x i := min_le_right _ _
      exact this)
  have h_sqrt_ge1 : 1 ≤ Real.sqrt (d : ℝ) := by
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd_pos
    calc
      (1 : ℝ) = Real.sqrt (1 : ℝ) := by norm_num
      _ ≤ Real.sqrt (d : ℝ) := Real.sqrt_le_sqrt hd1
  have h_sqrt_pos : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hd_pos)
  have h_div_le_r : r / Real.sqrt (d : ℝ) ≤ r := by
    have h_one_div : 1 / Real.sqrt (d : ℝ) ≤ 1 := by
      have h := (one_div_le_one_div h_sqrt_pos (by norm_num : (0 : ℝ) < 1)).mpr h_sqrt_ge1
      simpa [div_one] using h
    calc
      r / Real.sqrt (d : ℝ) = r * (1 / Real.sqrt (d : ℝ)) := by ring
      _ ≤ r * 1 := mul_le_mul_of_nonneg_left h_one_div (by positivity)
      _ = r := by simp
  have h_lo : a i < y i := by
    have h_abs : |y i - x i| < ε := h_coord_bound i
    have h_eps_le : ε ≤ x i - a i := by
      calc
        ε = r / Real.sqrt (d : ℝ) := rfl
        _ ≤ r := h_div_le_r
        _ ≤ x i - a i := hx_diff_lo
    by_contra! hy
    -- hy: y i ≤ a i, so x i - y i ≥ x i - a i ≥ ε
    have h_nonneg : 0 ≤ x i - y i := sub_nonneg.mpr (by linarith)
    have h_abs_ge : |y i - x i| ≥ x i - a i := by
      have : |y i - x i| = |x i - y i| := abs_sub_comm _ _
      rw [this, abs_of_nonneg h_nonneg]
      nlinarith
    nlinarith
  have h_hi : y i < b i := by
    have h_abs : |y i - x i| < ε := h_coord_bound i
    have h_eps_le : ε ≤ b i - x i := by
      calc
        ε = r / Real.sqrt (d : ℝ) := rfl
        _ ≤ r := h_div_le_r
        _ ≤ b i - x i := hx_diff_hi
    by_contra! hy
    -- hy: y i ≥ b i, so y i - x i ≥ b i - x i ≥ ε
    have h_nonneg : 0 ≤ y i - x i := sub_nonneg.mpr (by linarith)
    have h_abs_ge : |y i - x i| ≥ b i - x i := by
      rw [abs_of_nonneg h_nonneg]
      nlinarith
    nlinarith
  exact ⟨h_lo, h_hi⟩

lemma finite_TFAE_6_implies_7 {d : ℕ} (E : Set (EuclideanSpace' d))
    (h6 : ∀ ε > 0, ∃ E' : Set (EuclideanSpace' d), LebesgueMeasurable E' ∧ Bornology.IsBounded E' ∧ Lebesgue_outer_measure (symmDiff E' E) ≤ ε) :
    ∀ ε > 0, ∃ E' : Set (EuclideanSpace' d), IsElementary E' ∧ Lebesgue_outer_measure (symmDiff E' E) ≤ ε := by
  intro ε hε
  by_cases hε_top : ε = ⊤
  · subst hε_top; refine ⟨∅, IsElementary.empty d, le_top⟩
  · -- ε is a positive real
    have hε_pos_real : ∃ r : ℝ, 0 < r ∧ (r : EReal) = ε := by
      have h_cases : ε = ⊥ ∨ (∃ r : ℝ, ε = (r : EReal)) ∨ ε = ⊤ := by
        match ε with
        | ⊥ => exact Or.inl rfl
        | (r : ℝ) => exact Or.inr (Or.inl ⟨r, rfl⟩)
        | ⊤ => exact Or.inr (Or.inr rfl)
      rcases h_cases with (hbot | hreal | htop)
      · rw [hbot] at hε; have hpos : (0 : EReal) < (⊥ : EReal) := hε
        have hbot_lt_zero : (⊥ : EReal) < 0 := EReal.bot_lt_zero
        exact (lt_irrefl (0 : EReal) (hpos.trans hbot_lt_zero)).elim
      · rcases hreal with ⟨r, hr⟩
        have hr_pos : 0 < r := by
          have hpos_ereal : (0 : EReal) < (r : EReal) := by rw [← hr]; exact hε
          exact_mod_cast hpos_ereal
        exact ⟨r, hr_pos, hr.symm⟩
      · exact (hε_top htop).elim
    rcases hε_pos_real with ⟨r, hr_pos, hr_eq⟩; subst hr_eq

    by_cases hd : d = 0
    · subst hd
      rcases h6 (r : EReal) (by exact_mod_cast hr_pos) with ⟨E', hE'_meas, hE'_bounded, h_symm⟩
      refine ⟨E', ?_, h_symm⟩
      by_cases hE'_empty : E' = ∅
      · rw [hE'_empty]; exact IsElementary.empty 0
      · have hE'_nonempty : E'.Nonempty := Set.nonempty_iff_ne_empty.mpr hE'_empty
        have h_univ : E' = Set.univ := by
          apply Set.Subset.antisymm
          · exact Set.subset_univ _
          · intro x hx
            obtain ⟨y, hy⟩ := hE'_nonempty
            have h_eq : x = y := by ext i; exact Fin.elim0 i
            rw [h_eq]; exact hy
        rw [h_univ]
        let B : Box 0 := { side := fun i => BoundedInterval.Icc (0 : ℝ) (0 : ℝ) }
        have hB_elem : IsElementary (B.toSet) := IsElementary.box B
        have hB_univ : B.toSet = Set.univ := by ext x; simp
        rw [← hB_univ]; exact hB_elem

    have hd_pos : 0 < d := Nat.pos_of_ne_zero hd

    -- Get bounded measurable E' with m*(symmDiff(E',E)) ≤ r/2
    have hr2_pos : 0 < r/2 := by linarith
    rcases h6 ((r/2 : ℝ) : EReal) (by exact_mod_cast hr2_pos) with ⟨E', hE'_meas, hE'_bounded, h_symm_EE'⟩

    -- From measurability, get open U ⊇ E' and closed F ⊆ E' with small residuals
    have h_open_approx : ∀ ε > 0, ∃ U : Set (EuclideanSpace' d), IsOpen U ∧ E' ⊆ U ∧ Lebesgue_outer_measure (U \ E') ≤ ε :=
      ((LebesgueMeasurable.TFAE E').out 0 1).mp hE'_meas
    have h_closed_approx : ∀ ε > 0, ∃ F : Set (EuclideanSpace' d), IsClosed F ∧ F ⊆ E' ∧ Lebesgue_outer_measure (E' \ F) ≤ ε :=
      ((LebesgueMeasurable.TFAE E').out 0 3).mp hE'_meas

    have hr8_pos : 0 < r/8 := by linarith
    have h_hr8_pos : (0 : EReal) < (r/8 : ℝ) := by exact_mod_cast hr8_pos
    haveI : Nonempty (Fin d) := ⟨⟨0, hd_pos⟩⟩

    rcases h_open_approx ((r/8 : ℝ) : EReal) h_hr8_pos with ⟨U, hU_open, hE'_sub_U, hU_diff⟩
    rcases h_closed_approx ((r/8 : ℝ) : EReal) h_hr8_pos with ⟨F, hF_closed, hF_sub_E', hF_diff⟩

    have hF_bounded : Bornology.IsBounded F := hE'_bounded.subset hF_sub_E'
    have hF_compact : IsCompact F := Metric.isCompact_of_isClosed_isBounded hF_closed hF_bounded

    -- For each point x ∈ F, find an Ioo box B_x with x ∈ B_x ⊆ U
    have h_boxes_cover : ∀ x ∈ F, ∃ (B : Box d), x ∈ B.toSet ∧ B.toSet ⊆ U ∧ IsOpen (B.toSet) := by
      intro x hxF
      have hxU : x ∈ U := hE'_sub_U (hF_sub_E' hxF)
      have hU_open' : ∀ x ∈ U, ∃ ε > 0, Metric.ball x ε ⊆ U := by
        rw [Metric.isOpen_iff] at hU_open; exact hU_open
      obtain ⟨δ, hδ_pos, hball⟩ := hU_open' x hxU
      set sd := Real.sqrt (d : ℝ) with hsd
      have hsd_pos : 0 < sd := Real.sqrt_pos.mpr (by exact_mod_cast hd_pos)
      -- The open box (product of Ioo intervals) centered at x with side length 2*δ/sd
      let B : Box d := {
        side := fun i => BoundedInterval.Ioo (x i - δ / sd) (x i + δ / sd)
      }
      refine ⟨B, ?_, ?_, ?_⟩
      · -- x ∈ B
        intro i
        simp [B, BoundedInterval.set_Ioo]
        positivity
      · -- B ⊆ U: any y in the box satisfies ‖y-x‖ < δ (since |y_i - x_i| < δ/sd for all i)
        intro y hy
        rw [Box.mem_toSet] at hy
        apply hball
        rw [Metric.mem_ball, dist_eq_norm]
        have h_coord_bound : ∀ i : Fin d, |(y - x) i| < δ / sd := by
          intro i
          have hyi : x i - δ / sd < y i ∧ y i < x i + δ / sd := by
            simpa [B, BoundedInterval.set_Ioo] using hy i
          rcases hyi with ⟨h_lo, h_hi⟩
          have diff_eq : (y - x) i = y i - x i := by simp
          rw [diff_eq, abs_lt]; constructor <;> nlinarith
        -- Show ‖y-x‖^2 < δ^2 using EuclideanSpace'.norm_eq
        have h_norm_sq_lt : ‖y - x‖ ^ 2 < δ ^ 2 := by
          have h_norm_sq_eq : ‖y - x‖ ^ 2 = ∑ i : Fin d, ((y - x) i) ^ 2 := by
            calc
              ‖y - x‖ ^ 2 = (Real.sqrt (∑ i : Fin d, ((y - x) i) ^ 2)) ^ 2 := by
                rw [EuclideanSpace'.norm_eq (y - x)]
              _ = ∑ i : Fin d, ((y - x) i) ^ 2 := by
                have h_nonneg_sum : 0 ≤ ∑ i : Fin d, ((y - x) i) ^ 2 :=
                  Finset.sum_nonneg (fun i _ => pow_two_nonneg _)
                rw [Real.sq_sqrt h_nonneg_sum]
          calc
            ‖y - x‖ ^ 2 = ∑ i : Fin d, ((y - x) i) ^ 2 := h_norm_sq_eq
            _ < ∑ i : Fin d, (δ / sd) ^ 2 := by
              refine Finset.sum_lt_sum (fun i _ => ?_) ?_
              · have hi_sq_le : ((y - x) i) ^ 2 ≤ (δ / sd) ^ 2 := by
                  have hi_abs : |(y - x) i| < δ / sd := h_coord_bound i
                  nlinarith [abs_lt.mp hi_abs]
                exact hi_sq_le
              · have huniv_nonempty : Finset.Nonempty (Finset.univ : Finset (Fin d)) :=
                  Finset.univ_nonempty (α := Fin d)
                obtain ⟨i⟩ := huniv_nonempty
                refine ⟨i, Finset.mem_univ i, ?_⟩
                have hi_sq_lt : ((y - x) i) ^ 2 < (δ / sd) ^ 2 := by
                  have hi_abs : |(y - x) i| < δ / sd := h_coord_bound i
                  nlinarith [abs_lt.mp hi_abs]
                exact hi_sq_lt
            _ = (d : ℝ) * ((δ / sd) ^ 2) := by simp
            _ = δ ^ 2 := by
              calc
                (d : ℝ) * ((δ / sd) ^ 2) = (d : ℝ) * (δ ^ 2 / sd ^ 2) := by ring
                _ = (d : ℝ) * (δ ^ 2 / ((Real.sqrt (d : ℝ)) ^ 2)) := rfl
                _ = (d : ℝ) * (δ ^ 2 / (d : ℝ)) := by rw [Real.sq_sqrt (show 0 ≤ (d : ℝ) from by exact_mod_cast hd_pos.le)]
                _ = δ ^ 2 := by
                  field_simp [show (d : ℝ) ≠ 0 from by exact_mod_cast hd_pos.ne']
        have h_norm_nonneg : 0 ≤ ‖y - x‖ := norm_nonneg _
        nlinarith
      · -- B.toSet is open (product of Ioo intervals)
        have hB_eq : B.toSet = {y | ∀ i : Fin d, (x i - δ / sd) < y i ∧ y i < (x i + δ / sd)} := by
          ext y; simp [Box.mem_toSet, B]
        rw [hB_eq]
        exact Ioo_box_isOpen hd_pos (fun i => x i - δ / sd) (fun i => x i + δ / sd)

    -- The boxes from h_boxes_cover are open and cover F. By compactness, finitely many suffice.
    have h_cover : F ⊆ ⋃ (B : Box d), B.toSet := by
      intro x hxF
      rcases h_boxes_cover x hxF with ⟨B, hxB, _, _⟩
      exact Set.mem_iUnion.mpr ⟨B, hxB⟩
    -- Since F is compact and each box is open, finitely many boxes cover F
    -- Use the IsCompact.elim_finite_subcover with an appropriate indexing
    -- The indexing type is (B : Box d) with the property that B.toSet is open
    -- But not all boxes are open, only the ones we constructed.
    -- So we create an indexed family using the boxes from h_boxes_cover.

    -- Let's construct an index set from F itself
    let V : F → Set (EuclideanSpace' d) := fun x => (h_boxes_cover x.1 x.2).choose.toSet
    have hV_open : ∀ x : F, IsOpen (V x) := by
      intro x
      have h := (h_boxes_cover x.1 x.2).choose_spec
      exact h.2.2
    have hV_cover : F ⊆ ⋃ x : F, V x := by
      intro x hxF
      have h := (h_boxes_cover x hxF).choose_spec
      refine Set.mem_iUnion.mpr ⟨⟨x, hxF⟩, h.1⟩
    rcases hF_compact.elim_finite_subcover V hV_open hV_cover with ⟨t, ht⟩
    -- t : Finset F, and F ⊆ ⋃ x ∈ t, V x

    -- Build the elementary set A
    have hA_elem : IsElementary (⋃ x ∈ t, (h_boxes_cover x.1 x.2).choose.toSet) := by
      let S' : Finset (Set (EuclideanSpace' d)) :=
        Finset.image (fun (x : F) => ((h_boxes_cover x.1 x.2).choose : Box d).toSet) t
      have h_union : (⋃ x ∈ t, (h_boxes_cover x.1 x.2).choose.toSet) = ⋃ E ∈ S', E := by
        ext y; simp [S']
      rw [h_union]
      apply IsElementary.union'
      intro E hE
      rcases Finset.mem_image.mp hE with ⟨x, hx, rfl⟩
      exact IsElementary.box ((h_boxes_cover x.1 x.2).choose)
    set A := ⋃ x ∈ t, (h_boxes_cover x.1 x.2).choose.toSet with hA_def
    have hA_elem' : IsElementary A := hA_elem
    have hF_sub_A : F ⊆ A := by
      intro x hxF
      have hxV : x ∈ ⋃ x' ∈ t, V x' := ht hxF
      rw [Set.mem_iUnion₂] at hxV
      rcases hxV with ⟨x', hx't, hxV'⟩
      have hxV_box : x ∈ (h_boxes_cover x'.1 x'.2).choose.toSet := hxV'
      rw [hA_def, Set.mem_iUnion₂]
      exact ⟨x', hx't, hxV_box⟩
    have hA_sub_U : A ⊆ U := by
      intro x hx
      rw [hA_def] at hx
      rw [Set.mem_iUnion₂] at hx
      rcases hx with ⟨x', hx't, hx⟩
      have hxB := (h_boxes_cover x'.1 x'.2).choose_spec.2.1
      exact hxB hx

    -- Bound m*(symmDiff(A,E')) ≤ r/2
    have h_symm_diff_bound : Lebesgue_outer_measure (symmDiff A E') ≤ (r/2 : ℝ) := by
      have h_sub1 : A \ E' ⊆ U \ E' := Set.diff_subset_diff_left hA_sub_U
      have h_sub2 : E' \ A ⊆ E' \ F := Set.diff_subset_diff_right hF_sub_A
      have h_sub_union : (A \ E') ∪ (E' \ A) ⊆ (U \ E') ∪ (E' \ F) := by
        intro x hx
        rcases hx with (hx1 | hx2)
        · -- x ∈ A \ E'
          have hx_in_A : x ∈ A := hx1.1
          have hxU : x ∈ U := hA_sub_U hx_in_A
          have hx_not_E' : x ∉ E' := hx1.2
          exact Or.inl ⟨hxU, hx_not_E'⟩
        · -- x ∈ E' \ A
          have hxE' : x ∈ E' := hx2.1
          have hx_not_A : x ∉ A := hx2.2
          have hx_not_F : x ∉ F := by
            intro hxF'; apply hx_not_A; exact hF_sub_A hxF'
          exact Or.inr ⟨hxE', hx_not_F⟩
      have h_mu_sub : Lebesgue_outer_measure ((A \ E') ∪ (E' \ A)) ≤
          Lebesgue_outer_measure ((U \ E') ∪ (E' \ F)) :=
        Lebesgue_outer_measure.mono h_sub_union
      let Svec : Fin 2 → Set (EuclideanSpace' d) := ![U \ E', E' \ F]
      have h_union_eq : (U \ E') ∪ (E' \ F) = ⋃ i : Fin 2, Svec i := by
        ext x; simp [Svec]
      have h_fin_union_le : Lebesgue_outer_measure ((U \ E') ∪ (E' \ F)) ≤
          Lebesgue_outer_measure (U \ E') + Lebesgue_outer_measure (E' \ F) := by
        calc
          Lebesgue_outer_measure ((U \ E') ∪ (E' \ F)) = Lebesgue_outer_measure (⋃ i : Fin 2, Svec i) := by rw [h_union_eq]
          _ ≤ ∑ i : Fin 2, Lebesgue_outer_measure (Svec i) := Lebesgue_outer_measure.finite_union_le Svec
          _ = Lebesgue_outer_measure (U \ E') + Lebesgue_outer_measure (E' \ F) := by simp [Svec, Fin.sum_univ_two]
      calc
        Lebesgue_outer_measure (symmDiff A E') = Lebesgue_outer_measure ((A \ E') ∪ (E' \ A)) := by rw [Set.symmDiff_def]
        _ ≤ Lebesgue_outer_measure ((U \ E') ∪ (E' \ F)) := h_mu_sub
        _ ≤ Lebesgue_outer_measure (U \ E') + Lebesgue_outer_measure (E' \ F) := h_fin_union_le
        _ ≤ ((r/8 : ℝ) : EReal) + ((r/8 : ℝ) : EReal) := add_le_add hU_diff hF_diff
        _ = ((r/4 : ℝ) : EReal) := by
          have : (r/8 : ℝ) + (r/8 : ℝ) = r/4 := by ring
          exact_mod_cast this
        _ ≤ (r/2 : ℝ) := by exact_mod_cast (by nlinarith : (r/4 : ℝ) ≤ r/2)

    -- Combine with h_symm_EE': m*(symmDiff(A,E)) ≤ m*(symmDiff(A,E')) + m*(symmDiff(E',E)) ≤ r/2 + r/2 = r
    have h_symm_AE : Lebesgue_outer_measure (symmDiff A E) ≤ (r : EReal) := by
      have h_sub : symmDiff A E ⊆ symmDiff A E' ∪ symmDiff E' E :=
        symmDiff_sub_symmDiff_union_symmDiff
      have h_mono : Lebesgue_outer_measure (symmDiff A E) ≤
          Lebesgue_outer_measure (symmDiff A E' ∪ symmDiff E' E) :=
        Lebesgue_outer_measure.mono h_sub
      let Tvec : Fin 2 → Set (EuclideanSpace' d) := ![symmDiff A E', symmDiff E' E]
      have h_union_eq' : symmDiff A E' ∪ symmDiff E' E = ⋃ i : Fin 2, Tvec i := by
        ext x; simp [Tvec]
      have h_fin_union_le' : Lebesgue_outer_measure (symmDiff A E' ∪ symmDiff E' E) ≤
          Lebesgue_outer_measure (symmDiff A E') + Lebesgue_outer_measure (symmDiff E' E) := by
        calc
          Lebesgue_outer_measure (symmDiff A E' ∪ symmDiff E' E) = Lebesgue_outer_measure (⋃ i : Fin 2, Tvec i) := by rw [h_union_eq']
          _ ≤ ∑ i : Fin 2, Lebesgue_outer_measure (Tvec i) := Lebesgue_outer_measure.finite_union_le Tvec
          _ = Lebesgue_outer_measure (symmDiff A E') + Lebesgue_outer_measure (symmDiff E' E) := by simp [Tvec, Fin.sum_univ_two]
      calc
        Lebesgue_outer_measure (symmDiff A E) ≤ Lebesgue_outer_measure (symmDiff A E' ∪ symmDiff E' E) := h_mono
        _ ≤ Lebesgue_outer_measure (symmDiff A E') + Lebesgue_outer_measure (symmDiff E' E) := h_fin_union_le'
        _ ≤ ((r/2 : ℝ) : EReal) + ((r/2 : ℝ) : EReal) := add_le_add h_symm_diff_bound h_symm_EE'
        _ = (r : EReal) := by
          have : (r/2 : ℝ) + (r/2 : ℝ) = r := by ring
          exact_mod_cast this

    refine ⟨A, hA_elem', h_symm_AE⟩