import Analysis.MeasureTheory.Section_1_2_1
open Set EReal Metric

private lemma prod_le_of_finite {d₁ d₂ : ℕ} {E₁ : Set (EuclideanSpace' d₁)} {E₂ : Set (EuclideanSpace' d₂)}
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (h₁_fin : Lebesgue_outer_measure E₁ ≠ ⊤) (h₂_fin : Lebesgue_outer_measure E₂ ≠ ⊤) :
    Lebesgue_outer_measure (EuclideanSpace'.prod E₁ E₂) ≤ Lebesgue_outer_measure E₁ * Lebesgue_outer_measure E₂ := by
  set m₁ := Lebesgue_outer_measure E₁ with hm₁_def
  set m₂ := Lebesgue_outer_measure E₂ with hm₂_def
  have hm₁_nonneg : 0 ≤ m₁ := Lebesgue_outer_measure.nonneg E₁
  have hm₂_nonneg : 0 ≤ m₂ := Lebesgue_outer_measure.nonneg E₂
  have hm₁_ne_bot : m₁ ≠ ⊥ := by
    intro h; have : (0 : EReal) ≤ ⊥ := by simpa [h] using hm₁_nonneg
    have hlt : (⊥ : EReal) < (0 : EReal) := EReal.bot_lt_zero; exact not_le.mpr hlt this
  have hm₂_ne_bot : m₂ ≠ ⊥ := by
    intro h; have : (0 : EReal) ≤ ⊥ := by simpa [h] using hm₂_nonneg
    have hlt : (⊥ : EReal) < (0 : EReal) := EReal.bot_lt_zero; exact not_le.mpr hlt this
  have hm₁_real : (m₁.toReal : EReal) = m₁ := EReal.coe_toReal h₁_fin hm₁_ne_bot
  have hm₂_real : (m₂.toReal : EReal) = m₂ := EReal.coe_toReal h₂_fin hm₂_ne_bot
  set a := m₁.toReal with ha_def
  set b := m₂.toReal with hb_def
  have ha_nonneg : 0 ≤ a := by
    have h : (0 : EReal) ≤ (a : EReal) := by rw [hm₁_real]; exact hm₁_nonneg; exact_mod_cast h
  have hb_nonneg : 0 ≤ b := by
    have h : (0 : EReal) ≤ (b : EReal) := by rw [hm₂_real]; exact hm₂_nonneg; exact_mod_cast h
  refine EReal.le_of_forall_pos_le_add' ?_
  intro ε hε
  rcases exists_delta_ineq a b ha_nonneg hb_nonneg ε hε with ⟨δ, hδ_pos, h_ineq⟩
  obtain ⟨S₁, hS₁_cover, hS₁_sum⟩ := Lebesgue_outer_measure.exists_cover_close hd₁ E₁ δ hδ_pos h₁_fin
  obtain ⟨S₂, hS₂_cover, hS₂_sum⟩ := Lebesgue_outer_measure.exists_cover_close hd₂ E₂ δ hδ_pos h₂_fin
  have h_prod_cover : EuclideanSpace'.prod E₁ E₂ ⊆ ⋃ k, (Box.prod (S₁ ((Nat.pairEquiv.symm k).1)) (S₂ ((Nat.pairEquiv.symm k).2))).toSet :=
    prod_cover_aux E₁ E₂ S₁ S₂ hS₁_cover hS₂_cover
  have h_vol_tsum : ∑' k, ((Box.prod (S₁ ((Nat.pairEquiv.symm k).1)) (S₂ ((Nat.pairEquiv.symm k).2))).volume.toEReal) =
      (∑' i, ((S₁ i).volume.toEReal)) * (∑' j, ((S₂ j).volume.toEReal)) :=
    tsum_vol_prod_eq_mul_tsum S₁ S₂
  have h_m_le_vol : Lebesgue_outer_measure (EuclideanSpace'.prod E₁ E₂) ≤
      ∑' k, ((Box.prod (S₁ ((Nat.pairEquiv.symm k).1)) (S₂ ((Nat.pairEquiv.symm k).2))).volume.toEReal) := by
    unfold Lebesgue_outer_measure; apply sInf_le
    let s : Set ℕ := Set.univ
    let R : s → Box (d₁ + d₂) := fun x =>
      Box.prod (S₁ ((Nat.pairEquiv.symm x.val).1)) (S₂ ((Nat.pairEquiv.symm x.val).2))
    have hR_cover : EuclideanSpace'.prod E₁ E₂ ⊆ ⋃ (n : s), (R n).toSet := by
      intro y hy; have hy' : ∃ (k : ℕ), y ∈ (Box.prod (S₁ ((Nat.pairEquiv.symm k).1)) (S₂ ((Nat.pairEquiv.symm k).2))).toSet := by
        simpa using h_prod_cover hy
      rcases hy' with ⟨k, hk⟩; refine Set.mem_iUnion.mpr ⟨⟨k, Set.mem_univ k⟩, ?_⟩; simpa [R] using hk
    have hR_sum : ∑' (n : s), (R n).volume.toEReal =
        ∑' k : ℕ, ((Box.prod (S₁ ((Nat.pairEquiv.symm k).1)) (S₂ ((Nat.pairEquiv.symm k).2))).volume.toEReal) := by
      have h := tsum_subtype s (fun (k : ℕ) => ((Box.prod (S₁ ((Nat.pairEquiv.symm k).1)) (S₂ ((Nat.pairEquiv.symm k).2))).volume.toEReal))
      simpa [R, s] using h
    refine ⟨Set.univ, R, hR_cover, ?_⟩; rw [hR_sum]
  have hδ_ne_top : ((δ : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top δ
  have hm₁_add_ne_top : m₁ + (δ : ℝ) ≠ ⊤ := ne_of_lt (EReal.add_lt_top h₁_fin hδ_ne_top)
  have hm₂_add_ne_top : m₂ + (δ : ℝ) ≠ ⊤ := ne_of_lt (EReal.add_lt_top h₂_fin hδ_ne_top)
  have h_fin_a_add : ((a + δ : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top (a + δ)
  have h_fin_b_add : ((b + δ : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top (b + δ)
  have h_nonneg_vol₁ : 0 ≤ ∑' i, ((S₁ i).volume.toEReal) := by
    apply tsum_nonneg; intro n; exact EReal.coe_nonneg.mpr (Box.volume_nonneg _)
  have h_nonneg_vol₂ : 0 ≤ ∑' j, ((S₂ j).volume.toEReal) := by
    apply tsum_nonneg; intro n; exact EReal.coe_nonneg.mpr (Box.volume_nonneg _)
  have h_nonneg_a_add : 0 ≤ (a + δ : ℝ) := by positivity
  have h_nonneg_b_add : 0 ≤ (b + δ : ℝ) := by positivity
  have hS₁_sum' : (∑' i, ((S₁ i).volume.toEReal)) ≤ ((a + δ : ℝ) : EReal) := by
    calc
      ∑' i, ((S₁ i).volume.toEReal) ≤ Lebesgue_outer_measure E₁ + (δ : ℝ) := hS₁_sum
      _ = m₁ + (δ : ℝ) := by rw [hm₁_def]
      _ = ((a : ℝ) : EReal) + (δ : ℝ) := by rw [hm₁_real]
      _ = ((a + δ : ℝ) : EReal) := by simp
  have hS₂_sum' : (∑' j, ((S₂ j).volume.toEReal)) ≤ ((b + δ : ℝ) : EReal) := by
    calc
      ∑' j, ((S₂ j).volume.toEReal) ≤ Lebesgue_outer_measure E₂ + (δ : ℝ) := hS₂_sum
      _ = m₂ + (δ : ℝ) := by rw [hm₂_def]
      _ = ((b : ℝ) : EReal) + (δ : ℝ) := by rw [hm₂_real]
      _ = ((b + δ : ℝ) : EReal) := by simp
  have h_vol_bound : (∑' i, ((S₁ i).volume.toEReal)) * (∑' j, ((S₂ j).volume.toEReal)) ≤
      ((a + δ : ℝ) : EReal) * ((b + δ : ℝ) : EReal) := by
    apply mul_le_mul_ereal_fin h_nonneg_vol₁ h_nonneg_vol₂
      (by exact_mod_cast h_nonneg_a_add) (by exact_mod_cast h_nonneg_b_add)
      hS₁_sum' hS₂_sum' h_fin_a_add h_fin_b_add
  calc
    Lebesgue_outer_measure (EuclideanSpace'.prod E₁ E₂) ≤
        ∑' k, ((Box.prod (S₁ ((Nat.pairEquiv.symm k).1)) (S₂ ((Nat.pairEquiv.symm k).2))).volume.toEReal) := h_m_le_vol
    _ = (∑' i, ((S₁ i).volume.toEReal)) * (∑' j, ((S₂ j).volume.toEReal)) := h_vol_tsum
    _ ≤ ((a + δ : ℝ) : EReal) * ((b + δ : ℝ) : EReal) := h_vol_bound
    _ = ((a + δ) * (b + δ) : ℝ) := by simp
    _ ≤ (a * b + ε : ℝ) := by exact_mod_cast h_ineq
    _ = ((a : ℝ) * (b : ℝ) + (ε : ℝ) : EReal) := by simp
    _ = (a : EReal) * (b : EReal) + (ε : EReal) := by simp
    _ = m₁ * m₂ + (ε : EReal) := by simp [hm₁_real, hm₂_real]

/-- If m(E₂) = 0, then m(prod E₁ E₂) = 0 for any E₁,d₁,d₂.
    Uses σ-finiteness: write E₁ = ⋃_n (E₁ ∩ closedBall 0 n), each with finite outer measure,
    then apply the main theorem's epsilon argument to each piece, plus countable subadditivity. -/
lemma prod_null_of_null_second {d₁ d₂ : ℕ} {E₁ : Set (EuclideanSpace' d₁)} {E₂ : Set (EuclideanSpace' d₂)}
    (hm₂ : Lebesgue_outer_measure E₂ = 0) : Lebesgue_outer_measure (EuclideanSpace'.prod E₁ E₂) = 0 := by
  by_cases hd₂ : d₂ = 0
  · subst hd₂
    rw [Lebesgue_outer_measure_of_dim_zero] at hm₂
    have hE₂_empty : E₂ = ∅ := by
      contrapose! hm₂; simp [hm₂]
    subst hE₂_empty; simp [EuclideanSpace'.prod, Lebesgue_outer_measure.of_empty]
  · have hd₂_pos : 0 < d₂ := Nat.pos_of_ne_zero hd₂
    have hE₂_fin : Lebesgue_outer_measure E₂ ≠ ⊤ := by rw [hm₂]; exact EReal.zero_ne_top
    by_cases hd₁ : d₁ = 0
    · subst hd₁
      have hE₂_eq0 : Lebesgue_outer_measure E₂ = 0 := hm₂
      have h_nat_lift : ∀ (S : ℕ → Box d₂), E₂ ⊆ ⋃ n : ℕ, (S n).toSet →
          EuclideanSpace'.prod E₁ E₂ ⊆ ⋃ n : ℕ, (Box.prod (Box.unit_cube 0) (S n)).toSet := by
        intro S hS_cover y hy
        rw [EuclideanSpace'.prod] at hy; rcases hy with ⟨⟨a, b⟩, ⟨ha, hb⟩, hy_eq⟩
        obtain ⟨n, hn⟩ : ∃ (n : ℕ), b ∈ (S n).toSet := by simpa using hS_cover hb
        refine Set.mem_iUnion.mpr ⟨n, ?_⟩
        have h_cube_univ : (Box.unit_cube 0).toSet = Set.univ := by
          ext x; simp [Box.unit_cube, Box.toSet]
        rw [Box.prod_toSet, EuclideanSpace'.prod, Set.mem_image]
        refine ⟨(a, b), ⟨by rw [h_cube_univ]; exact Set.mem_univ _, hn⟩, hy_eq⟩
      apply le_antisymm ?_ (Lebesgue_outer_measure.nonneg _)
      refine EReal.le_of_forall_pos_le_add' ?_
      intro ε hε
      obtain ⟨S, hS_cover, hS_sum⟩ := Lebesgue_outer_measure.exists_cover_close hd₂_pos E₂ ε hε hE₂_fin
      have h_prod_cover : EuclideanSpace'.prod E₁ E₂ ⊆ ⋃ n : ℕ, (Box.prod (Box.unit_cube 0) (S n)).toSet :=
        h_nat_lift S hS_cover
      have h_m_le_vol : Lebesgue_outer_measure (EuclideanSpace'.prod E₁ E₂) ≤
          ∑' n : ℕ, ((Box.prod (Box.unit_cube 0) (S n)).volume.toEReal : EReal) := by
        unfold Lebesgue_outer_measure; apply sInf_le
        let s : Set ℕ := Set.univ
        let R : s → Box (0 + d₂) := fun n => Box.prod (Box.unit_cube 0) (S n.val)
        have hR_cover : EuclideanSpace'.prod E₁ E₂ ⊆ ⋃ (m : s), (R m).toSet := by
          intro y hy; have hy' : y ∈ ⋃ n : ℕ, (Box.prod (Box.unit_cube 0) (S n)).toSet := h_prod_cover hy
          rcases hy' with ⟨k, hk⟩; refine Set.mem_iUnion.mpr ⟨⟨k, trivial⟩, ?_⟩; simpa [R] using hk
        have hR_sum : ∑' (m : s), (R m).volume.toEReal = ∑' n : ℕ, ((Box.prod (Box.unit_cube 0) (S n)).volume.toEReal : EReal) := by
          have h := tsum_subtype s (fun (n : ℕ) => ((Box.prod (Box.unit_cube 0) (S n)).volume.toEReal : EReal))
          simpa [R, s] using h
        refine ⟨s, R, hR_cover, ?_⟩; rw [hR_sum]
      have h_vol_eq : ∑' n : ℕ, ((Box.prod (Box.unit_cube 0) (S n)).volume.toEReal : EReal) =
          ∑' n : ℕ, ((S n).volume.toEReal : EReal) := by
        refine tsum_congr (fun n => ?_)
        rw [Box.volume_prod, show (Box.unit_cube 0).volume = (1 : ℝ) by unfold Box.unit_cube Box.volume; simp, mul_one]
      calc
        Lebesgue_outer_measure (EuclideanSpace'.prod E₁ E₂) ≤
            ∑' n : ℕ, ((Box.prod (Box.unit_cube 0) (S n)).volume.toEReal : EReal) := h_m_le_vol
        _ = ∑' n : ℕ, ((S n).volume.toEReal : EReal) := h_vol_eq
        _ ≤ Lebesgue_outer_measure E₂ + (ε : ℝ) := hS_sum
        _ = (0 : EReal) + (ε : ℝ) := by rw [hm₂]
        _ = (ε : EReal) := by simp
    · have hd₁_pos : 0 < d₁ := Nat.pos_of_ne_zero hd₁
      have h_ball_cover : E₁ = ⋃ n : ℕ, (E₁ ∩ Metric.closedBall 0 (n : ℝ)) :=
        (Metric.iUnion_inter_closedBall_nat E₁ 0).symm
      have h_prod_union : EuclideanSpace'.prod E₁ E₂ =
          ⋃ n : ℕ, EuclideanSpace'.prod (E₁ ∩ Metric.closedBall 0 (n : ℝ)) E₂ := by
        calc
          EuclideanSpace'.prod E₁ E₂ = (EuclideanSpace'.prod_equiv d₁ d₂).symm '' (E₁ ×ˢ E₂) := rfl
          _ = (EuclideanSpace'.prod_equiv d₁ d₂).symm '' ((⋃ n : ℕ, (E₁ ∩ Metric.closedBall 0 (n : ℝ))) ×ˢ E₂) := by rw [h_ball_cover]
          _ = (EuclideanSpace'.prod_equiv d₁ d₂).symm '' (⋃ n : ℕ, ((E₁ ∩ Metric.closedBall 0 (n : ℝ)) ×ˢ E₂)) := by rw [Set.iUnion_prod_const]
          _ = ⋃ n : ℕ, ((EuclideanSpace'.prod_equiv d₁ d₂).symm '' ((E₁ ∩ Metric.closedBall 0 (n : ℝ)) ×ˢ E₂)) := by rw [Set.image_iUnion]
          _ = ⋃ n : ℕ, EuclideanSpace'.prod (E₁ ∩ Metric.closedBall 0 (n : ℝ)) E₂ := rfl
      rw [h_prod_union]
      apply le_trans (Lebesgue_outer_measure.union_le (fun n : ℕ => EuclideanSpace'.prod (E₁ ∩ Metric.closedBall 0 (n : ℝ)) E₂)) ?_
      have h_each_zero : ∀ n : ℕ, Lebesgue_outer_measure (EuclideanSpace'.prod (E₁ ∩ Metric.closedBall 0 (n : ℝ)) E₂) = 0 := by
        intro n
        set F_n := E₁ ∩ Metric.closedBall 0 (n : ℝ) with hF_n_def
        have hF_n_fin : Lebesgue_outer_measure F_n ≠ ⊤ := by
          have h_ball_fin : Lebesgue_outer_measure (Metric.closedBall 0 (n : ℝ) : Set (EuclideanSpace' d₁)) ≠ ⊤ :=
            Lebesgue_outer_measure.finite_of_compact (isCompact_closedBall 0 (n : ℝ))
          have h_sub : F_n ⊆ Metric.closedBall 0 (n : ℝ) := Set.inter_subset_right
          have h_mono : Lebesgue_outer_measure F_n ≤ Lebesgue_outer_measure (Metric.closedBall 0 (n : ℝ)) :=
            Lebesgue_outer_measure.mono h_sub
          intro h_eq; apply h_ball_fin; have h_top : (⊤ : EReal) ≤ Lebesgue_outer_measure (Metric.closedBall 0 (n : ℝ)) := by
            simpa [h_eq] using h_mono; exact le_antisymm le_top h_top
        have h_ineq : Lebesgue_outer_measure (EuclideanSpace'.prod F_n E₂) ≤
            Lebesgue_outer_measure F_n * Lebesgue_outer_measure E₂ :=
          prod_le_of_finite hd₁_pos hd₂_pos hF_n_fin hE₂_fin
        rw [hm₂, mul_zero] at h_ineq
        exact le_antisymm h_ineq (Lebesgue_outer_measure.nonneg _)
      simp [h_each_zero]
