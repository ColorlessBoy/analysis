import Analysis.MeasureTheory.Section_1_2_1

open Set
open EReal

/-- Given ℕ-indexed box covers of E₁ and E₂, construct a ℕ-indexed box cover of their product.
    Uses the pairing function ℕ ≃ ℕ × ℕ. -/
lemma prod_cover_aux {d₁ d₂ : ℕ} (E₁ : Set (EuclideanSpace' d₁)) (E₂ : Set (EuclideanSpace' d₂))
    (S₁ : ℕ → Box d₁) (S₂ : ℕ → Box d₂) (h₁ : E₁ ⊆ ⋃ n, (S₁ n).toSet) (h₂ : E₂ ⊆ ⋃ n, (S₂ n).toSet) :
    EuclideanSpace'.prod E₁ E₂ ⊆ ⋃ k, (Box.prod (S₁ ((Nat.pairEquiv.symm k).1)) (S₂ ((Nat.pairEquiv.symm k).2))).toSet := by
  intro x hx
  rw [EuclideanSpace'.prod] at hx
  rcases hx with ⟨⟨a, b⟩, ⟨ha, hb⟩, hx_eq⟩
  have ha_cov : a ∈ ⋃ n, (S₁ n).toSet := h₁ ha
  have hb_cov : b ∈ ⋃ n, (S₂ n).toSet := h₂ hb
  have ha_cov' : ∃ (n : ℕ), a ∈ (S₁ n).toSet := by simpa using ha_cov
  have hb_cov' : ∃ (m : ℕ), b ∈ (S₂ m).toSet := by simpa using hb_cov
  rcases ha_cov' with ⟨n, hn⟩
  rcases hb_cov' with ⟨m, hm⟩
  let k := Nat.pairEquiv (n, m)
  refine Set.mem_iUnion.mpr ⟨k, ?_⟩
  have hk : (Nat.pairEquiv.symm k) = (n, m) := by
    dsimp [k]
    simp
  rw [hk]
  rw [Box.prod_toSet, EuclideanSpace'.prod, Set.mem_image]
  refine ⟨(a, b), ⟨hn, hm⟩, hx_eq⟩

/-- Volume sum of the product cover = product of the volume sums. -/
lemma tsum_vol_prod_eq_mul_tsum {d₁ d₂ : ℕ} (S₁ : ℕ → Box d₁) (S₂ : ℕ → Box d₂) :
    ∑' k : ℕ, ((Box.prod (S₁ ((Nat.pairEquiv.symm k).1)) (S₂ ((Nat.pairEquiv.symm k).2))).volume.toEReal) =
    (∑' i, ((S₁ i).volume.toEReal)) * (∑' j, ((S₂ j).volume.toEReal)) := by
  have hprod : ∑' (ij : ℕ × ℕ), ((Box.prod (S₁ ij.1) (S₂ ij.2)).volume.toEReal) =
      (∑' i, ((S₁ i).volume.toEReal)) * (∑' j, ((S₂ j).volume.toEReal)) := by
    calc
      ∑' (ij : ℕ × ℕ), ((Box.prod (S₁ ij.1) (S₂ ij.2)).volume.toEReal) =
          ∑' (ij : ℕ × ℕ), (((S₁ ij.1).volume * (S₂ ij.2).volume : ℝ) : EReal) := by
        refine tsum_congr (fun ij => ?_)
        rw [Box.volume_prod, EReal.coe_mul]
      _ = (∑' i, ((S₁ i).volume.toEReal)) * (∑' j, ((S₂ j).volume.toEReal)) :=
        tsum_prod_mul_ereal_of_nonneg
          (fun i => (S₁ i).volume) (fun j => (S₂ j).volume)
          (fun i => Box.volume_nonneg _) (fun j => Box.volume_nonneg _)
  -- reindex using Nat.pairEquiv.symm : ℕ ≃ ℕ × ℕ
  have h_reindex : ∑' (ij : ℕ × ℕ), ((Box.prod (S₁ ij.1) (S₂ ij.2)).volume.toEReal) =
      ∑' k : ℕ, ((Box.prod (S₁ ((Nat.pairEquiv.symm k).1)) (S₂ ((Nat.pairEquiv.symm k).2))).volume.toEReal) :=
    (Equiv.tsum_eq (Nat.pairEquiv.symm) (fun (ij : ℕ × ℕ) => ((Box.prod (S₁ ij.1) (S₂ ij.2)).volume.toEReal))).symm
  rw [← h_reindex, hprod]

/-- Algebraic lemma: for nonnegative reals a,b and ε > 0, there exists δ > 0 such that
    (a+δ)*(b+δ) ≤ a*b + ε. -/
lemma exists_delta_ineq (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (ε : ℝ) (hε : 0 < ε) :
    ∃ (δ : ℝ), 0 < δ ∧ (a + δ) * (b + δ) ≤ a * b + ε := by
  have h_sum_pos : a + b + 1 > 0 := by linarith
  set δ := min (ε / (a + b + 1)) 1 with hδ_def
  have hδ_pos : 0 < δ := by
    refine lt_min_iff.mpr ⟨div_pos hε (by linarith), by norm_num⟩
  have hδ_le_one : δ ≤ 1 := min_le_right _ _
  have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos
  have hδ_sq_le_δ : δ ^ 2 ≤ δ := by nlinarith
  have h_mul_bound : (a + b + 1) * δ ≤ ε := by
    by_cases h : ε / (a + b + 1) ≤ 1
    · have hδ_eq : δ = ε / (a + b + 1) := by
        rw [hδ_def, min_eq_left h]
      rw [hδ_eq]
      field_simp [h_sum_pos.ne']
      norm_num
    · push_neg at h
      have hδ_eq : δ = 1 := by
        rw [hδ_def, min_eq_right (by linarith : 1 ≤ ε / (a + b + 1))]
      rw [hδ_eq]
      have h_ineq' : a + b + 1 < ε := by
        calc
          a + b + 1 = 1 * (a + b + 1) := by simp
          _ < (ε / (a + b + 1)) * (a + b + 1) := mul_lt_mul_of_pos_right h h_sum_pos
          _ = ε := by field_simp [h_sum_pos.ne']
      nlinarith
  have h_ineq : (a + δ) * (b + δ) ≤ a * b + ε := by
    calc
      (a + δ) * (b + δ) = a * b + (a + b) * δ + δ ^ 2 := by ring
      _ ≤ a * b + (a + b) * δ + δ := by nlinarith
      _ = a * b + (a + b + 1) * δ := by ring
      _ ≤ a * b + ε := by nlinarith
  exact ⟨δ, hδ_pos, h_ineq⟩

/-- Multiplication is monotone for finite nonnegative EReals. -/
lemma mul_le_mul_ereal_fin {a b c d : EReal} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hac : a ≤ c) (hbd : b ≤ d) (hc_fin : c ≠ ⊤) (hd_fin : d ≠ ⊤) : a * b ≤ c * d := by
  have ha_fin : a ≠ ⊤ := by
    intro h
    apply hc_fin
    have : (⊤ : EReal) ≤ c := by simpa [h] using hac
    exact le_antisymm le_top this
  have ha_not_bot : a ≠ ⊥ := by
    intro h
    have : (0 : EReal) ≤ ⊥ := by simpa [h] using ha
    have h_not : ¬ (0 : EReal) ≤ ⊥ := by
      have hlt : (⊥ : EReal) < (0 : EReal) := EReal.bot_lt_zero
      exact not_le.mpr hlt
    exact h_not this
  have hb_fin : b ≠ ⊤ := by
    intro h
    apply hd_fin
    have : (⊤ : EReal) ≤ d := by simpa [h] using hbd
    exact le_antisymm le_top this
  have hb_not_bot : b ≠ ⊥ := by
    intro h
    have : (0 : EReal) ≤ ⊥ := by simpa [h] using hb
    have h_not : ¬ (0 : EReal) ≤ ⊥ := by
      have hlt : (⊥ : EReal) < (0 : EReal) := EReal.bot_lt_zero
      exact not_le.mpr hlt
    exact h_not this
  have hc_not_bot : c ≠ ⊥ := by
    intro h
    have : (0 : EReal) ≤ ⊥ := by simpa [h] using hc
    have h_not : ¬ (0 : EReal) ≤ ⊥ := by
      have hlt : (⊥ : EReal) < (0 : EReal) := by exact EReal.bot_lt_zero
      exact not_le.mpr hlt
    exact h_not this
  have hd_not_bot : d ≠ ⊥ := by
    intro h
    have : (0 : EReal) ≤ ⊥ := by simpa [h] using hd
    have h_not : ¬ (0 : EReal) ≤ ⊥ := by
      have hlt : (⊥ : EReal) < (0 : EReal) := by exact EReal.bot_lt_zero
      exact not_le.mpr hlt
    exact h_not this
  have ha_real : (a.toReal : EReal) = a := EReal.coe_toReal ha_fin ha_not_bot
  have hb_real : (b.toReal : EReal) = b := EReal.coe_toReal hb_fin hb_not_bot
  have hc_real : (c.toReal : EReal) = c := EReal.coe_toReal hc_fin hc_not_bot
  have hd_real : (d.toReal : EReal) = d := EReal.coe_toReal hd_fin hd_not_bot
  have hac_real : a.toReal ≤ c.toReal := by
    have : (a.toReal : EReal) ≤ (c.toReal : EReal) := by rw [ha_real, hc_real]; exact hac
    exact_mod_cast this
  have hbd_real : b.toReal ≤ d.toReal := by
    have : (b.toReal : EReal) ≤ (d.toReal : EReal) := by rw [hb_real, hd_real]; exact hbd
    exact_mod_cast this
  have ha_nonneg_real : 0 ≤ a.toReal := by
    have : (0 : EReal) ≤ (a.toReal : EReal) := by rw [ha_real]; exact ha
    exact_mod_cast this
  have hb_nonneg_real : 0 ≤ b.toReal := by
    have : (0 : EReal) ≤ (b.toReal : EReal) := by rw [hb_real]; exact hb
    exact_mod_cast this
  have hc_nonneg_real : 0 ≤ c.toReal := by
    have : (0 : EReal) ≤ (c.toReal : EReal) := by rw [hc_real]; exact hc
    exact_mod_cast this
  calc
    a * b = (a.toReal : EReal) * (b.toReal : EReal) := by rw [ha_real, hb_real]
    _ = ((a.toReal * b.toReal : ℝ) : EReal) := by simp
    _ ≤ ((c.toReal * d.toReal : ℝ) : EReal) := by
      have h_mul_real : a.toReal * b.toReal ≤ c.toReal * d.toReal :=
        mul_le_mul hac_real hbd_real hb_nonneg_real hc_nonneg_real
      exact_mod_cast h_mul_real
    _ = (c.toReal : EReal) * (d.toReal : EReal) := by simp
    _ = c * d := by rw [hc_real, hd_real]

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
    have h : (0 : EReal) ≤ (a : EReal) := by rw [hm₁_real]; exact hm₁_nonneg
    exact_mod_cast h
  have hb_nonneg : 0 ≤ b := by
    have h : (0 : EReal) ≤ (b : EReal) := by rw [hm₂_real]; exact hm₂_nonneg
    exact_mod_cast h
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
    unfold Lebesgue_outer_measure
    apply sInf_le
    let s : Set ℕ := Set.univ
    let R : s → Box (d₁ + d₂) := fun x =>
      Box.prod (S₁ ((Nat.pairEquiv.symm x.val).1)) (S₂ ((Nat.pairEquiv.symm x.val).2))
    have hR_cover : EuclideanSpace'.prod E₁ E₂ ⊆ ⋃ (n : s), (R n).toSet := by
      intro y hy
      have hy' : ∃ (k : ℕ), y ∈ (Box.prod (S₁ ((Nat.pairEquiv.symm k).1)) (S₂ ((Nat.pairEquiv.symm k).2))).toSet := by
        simpa using h_prod_cover hy
      rcases hy' with ⟨k, hk⟩
      refine Set.mem_iUnion.mpr ⟨⟨k, Set.mem_univ k⟩, ?_⟩
      simpa [R] using hk
    have hR_sum : ∑' (n : s), (R n).volume.toEReal =
        ∑' k : ℕ, ((Box.prod (S₁ ((Nat.pairEquiv.symm k).1)) (S₂ ((Nat.pairEquiv.symm k).2))).volume.toEReal) := by
      have h := tsum_subtype s (fun (k : ℕ) => ((Box.prod (S₁ ((Nat.pairEquiv.symm k).1)) (S₂ ((Nat.pairEquiv.symm k).2))).volume.toEReal))
      simpa [R, s] using h
    refine ⟨Set.univ, R, hR_cover, ?_⟩
    rw [hR_sum]
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

theorem Lebesgue_outer_measure.prod {d₁ d₂:ℕ} {E₁: Set (EuclideanSpace' d₁)} {E₂: Set (EuclideanSpace' d₂)}
  : Lebesgue_outer_measure (EuclideanSpace'.prod E₁ E₂) ≤ Lebesgue_outer_measure E₁ * Lebesgue_outer_measure E₂ := by
  set m₁ := Lebesgue_outer_measure E₁ with hm₁_def
  set m₂ := Lebesgue_outer_measure E₂ with hm₂_def
  by_cases h₁_top : m₁ = ⊤
  · -- m₁ = ⊤
    by_cases h₂_zero : m₂ = 0
    · -- m₁ = ⊤, m₂ = 0: then m₁*m₂ = 0, need m(prod) ≤ 0.
      -- Use σ-finiteness: decompose E₁ = ⋃_n (E₁ ∩ closedBall 0 n).
      rw [h₁_top, h₂_zero, mul_zero]
      have hm₂_eq0 : Lebesgue_outer_measure E₂ = 0 := by
        calc
          Lebesgue_outer_measure E₂ = m₂ := hm₂_def.symm
          _ = 0 := h₂_zero
      have h_union : E₁ = ⋃ n : ℕ, (E₁ ∩ Metric.closedBall 0 (n : ℝ)) :=
        (Metric.iUnion_inter_closedBall_nat E₁ 0).symm
      have h_prod_union : EuclideanSpace'.prod E₁ E₂ =
          ⋃ n : ℕ, EuclideanSpace'.prod (E₁ ∩ Metric.closedBall 0 (n : ℝ)) E₂ := by
        rw [h_union, EuclideanSpace'.prod, Set.image_iUnion, Set.iUnion_prod_const]
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
          intro h_eq
          apply h_ball_fin
          have h_top : (⊤ : EReal) ≤ Lebesgue_outer_measure (Metric.closedBall 0 (n : ℝ)) := by
            simpa [h_eq] using h_mono
          exact le_antisymm le_top h_top
        have hE₂_fin : Lebesgue_outer_measure E₂ ≠ ⊤ := by rw [hm₂_eq0]; exact EReal.zero_ne_top
        by_cases hd₁_pos : 0 < d₁
        · by_cases hd₂_pos : 0 < d₂
          · -- d₁ > 0, d₂ > 0: use prod_le_of_finite
            have h_ineq : Lebesgue_outer_measure (EuclideanSpace'.prod F_n E₂) ≤
                Lebesgue_outer_measure F_n * Lebesgue_outer_measure E₂ :=
              prod_le_of_finite hd₁_pos hd₂_pos hF_n_fin hE₂_fin
            rw [hm₂_eq0, mul_zero] at h_ineq
            exact le_antisymm h_ineq (Lebesgue_outer_measure.nonneg _)
          · -- d₂ = 0: E₂ empty (measure 0 in dim 0 → only empty set qualifies)
            have hd₂_eq0 : d₂ = 0 := by omega
            subst hd₂_eq0
            rw [Lebesgue_outer_measure_of_dim_zero] at hm₂_eq0
            have hE₂_empty : E₂ = ∅ := by
              contrapose! hm₂_eq0
              simp [hm₂_eq0]
            subst hE₂_empty
            simp [EuclideanSpace'.prod, Lebesgue_outer_measure.of_empty]
        · -- d₁ = 0: use the edge case proof (box-cover-lift from E₂)
          have hd₁_eq0 : d₁ = 0 := by omega
          subst hd₁_eq0
          have h_nat_lift : ∀ (S : ℕ → Box d₂), E₂ ⊆ ⋃ n : ℕ, (S n).toSet →
              EuclideanSpace'.prod F_n E₂ ⊆ ⋃ n : ℕ, (Box.prod (Box.unit_cube 0) (S n)).toSet := by
            intro S hS_cover y hy
            rw [EuclideanSpace'.prod] at hy
            rcases hy with ⟨⟨a, b⟩, ⟨ha, hb⟩, hy_eq⟩
            obtain ⟨n, hn⟩ : ∃ (n : ℕ), b ∈ (S n).toSet := by simpa using hS_cover hb
            refine Set.mem_iUnion.mpr ⟨n, ?_⟩
            have h_cube_univ : (Box.unit_cube 0).toSet = Set.univ := by
              ext x; simp [Box.unit_cube, Box.toSet]
            rw [Box.prod_toSet, EuclideanSpace'.prod, Set.mem_image]
            refine ⟨(a, b), ⟨by rw [h_cube_univ]; exact Set.mem_univ _, hn⟩, hy_eq⟩
          have h_nat_sum : ∀ (S : ℕ → Box d₂), ∑' (n : ℕ), (Box.prod (Box.unit_cube 0) (S n)).volume.toEReal = ∑' (n : ℕ), (S n).volume.toEReal := by
            intro S
            refine tsum_congr (fun n => ?_)
            rw [Box.volume_prod, show (Box.unit_cube 0).volume = (1 : ℝ) by unfold Box.unit_cube Box.volume; simp, one_mul]
          -- Use the ℕ-indexed equivalence for prod (when possible)
          by_cases hd₂_pos : 0 < d₂
          · have hm₂_ne_top : Lebesgue_outer_measure E₂ ≠ ⊤ := by
              rw [hm₂_eq0]; exact EReal.zero_ne_top
            refine le_antisymm ?_ (Lebesgue_outer_measure.nonneg _)
            refine EReal.le_of_forall_pos_le_add' ?_
            intro δ hδ
            obtain ⟨S, hS_cover, hS_sum⟩ := Lebesgue_outer_measure.exists_cover_close hd₂_pos E₂ δ hδ hm₂_ne_top
            have h_prod_cover : EuclideanSpace'.prod F_n E₂ ⊆ ⋃ n : ℕ, (Box.prod (Box.unit_cube 0) (S n)).toSet :=
              h_nat_lift S hS_cover
            have h_vol_eq : ∑' (n : ℕ), ((Box.prod (Box.unit_cube 0) (S n)).volume.toEReal : EReal) =
                ∑' (n : ℕ), ((S n).volume.toEReal : EReal) := h_nat_sum S
            have h_m_le_vol : Lebesgue_outer_measure (EuclideanSpace'.prod F_n E₂) ≤
                ∑' (n : ℕ), ((Box.prod (Box.unit_cube 0) (S n)).volume.toEReal : EReal) := by
              unfold Lebesgue_outer_measure
              apply sInf_le
              let s : Set ℕ := Set.univ
              let R : s → Box (0 + d₂) := fun n => Box.prod (Box.unit_cube 0) (S n.val)
              have hR_cover : EuclideanSpace'.prod F_n E₂ ⊆ ⋃ (m : s), (R m).toSet := by
                intro y hy; have hy' : y ∈ ⋃ n : ℕ, (Box.prod (Box.unit_cube 0) (S n)).toSet := h_prod_cover hy
                rcases hy' with ⟨k, hk⟩; refine Set.mem_iUnion.mpr ⟨⟨k, trivial⟩, ?_⟩; simpa [R] using hk
              have hR_sum : ∑' (m : s), (R m).volume.toEReal = ∑' (n : ℕ), ((Box.prod (Box.unit_cube 0) (S n)).volume.toEReal : EReal) := by
                have h := tsum_subtype s (fun (n : ℕ) => ((Box.prod (Box.unit_cube 0) (S n)).volume.toEReal : EReal))
                simpa [R, s] using h
              refine ⟨s, R, hR_cover, ?_⟩
              rw [hR_sum]
            calc
              Lebesgue_outer_measure (EuclideanSpace'.prod F_n E₂) ≤
                  ∑' (n : ℕ), ((Box.prod (Box.unit_cube 0) (S n)).volume.toEReal : EReal) := h_m_le_vol
              _ = ∑' (n : ℕ), ((S n).volume.toEReal : EReal) := h_vol_eq
              _ ≤ Lebesgue_outer_measure E₂ + (δ : ℝ) := hS_sum
              _ = (0 : EReal) + (δ : ℝ) := by rw [hm₂_eq0]
              _ = (δ : EReal) := by simp
              _ ≤ (0 : EReal) + (δ : EReal) := by simp
          · -- d₂ = 0: then E₂ empty, product empty
            have hd₂_eq0 : d₂ = 0 := by omega
            subst hd₂_eq0
            rw [Lebesgue_outer_measure_of_dim_zero] at hm₂_eq0
            have hE₂_empty : E₂ = ∅ := by
              contrapose! hm₂_eq0; simp [hm₂_eq0]
            subst hE₂_empty
            simp [EuclideanSpace'.prod, Lebesgue_outer_measure.of_empty]
      simp [h_each_zero]
    · rw [h₁_top]
      have hm₂_nonneg : 0 ≤ m₂ := Lebesgue_outer_measure.nonneg E₂
      have hm₂_pos : 0 < m₂ := by
        by_contra! hle; have : m₂ = 0 := le_antisymm hle hm₂_nonneg; exact h₂_zero this
      have htop_mul : (⊤ : EReal) * m₂ = ⊤ := top_mul_of_pos hm₂_pos
      rw [htop_mul]; exact le_top
  · by_cases h₂_top : m₂ = ⊤
    · by_cases h₁_zero : m₁ = 0
      · rw [h₁_zero, h₂_top, zero_mul]
        -- symmetric to h₁_top, h₂_zero case: use σ-finiteness on E₂
        have hm₁_eq0 : Lebesgue_outer_measure E₁ = 0 := by
          calc
            Lebesgue_outer_measure E₁ = m₁ := hm₁_def.symm
            _ = 0 := h₁_zero
        have h_union : E₂ = ⋃ n : ℕ, (E₂ ∩ Metric.closedBall 0 (n : ℝ)) :=
          (Metric.iUnion_inter_closedBall_nat E₂ 0).symm
        have h_prod_union : EuclideanSpace'.prod E₁ E₂ =
            ⋃ n : ℕ, EuclideanSpace'.prod E₁ (E₂ ∩ Metric.closedBall 0 (n : ℝ)) := by
          rw [h_union, EuclideanSpace'.prod, Set.image_iUnion, Set.prod_iUnion]
        rw [h_prod_union]
        apply le_trans (Lebesgue_outer_measure.union_le (fun n : ℕ => EuclideanSpace'.prod E₁ (E₂ ∩ Metric.closedBall 0 (n : ℝ)))) ?_
        have h_each_zero : ∀ n : ℕ, Lebesgue_outer_measure (EuclideanSpace'.prod E₁ (E₂ ∩ Metric.closedBall 0 (n : ℝ))) = 0 := by
          intro n
          set G_n := E₂ ∩ Metric.closedBall 0 (n : ℝ) with hG_n_def
          have hG_n_fin : Lebesgue_outer_measure G_n ≠ ⊤ := by
            have h_ball_fin : Lebesgue_outer_measure (Metric.closedBall 0 (n : ℝ) : Set (EuclideanSpace' d₂)) ≠ ⊤ :=
              Lebesgue_outer_measure.finite_of_compact (isCompact_closedBall 0 (n : ℝ))
            have h_sub : G_n ⊆ Metric.closedBall 0 (n : ℝ) := Set.inter_subset_right
            have h_mono : Lebesgue_outer_measure G_n ≤ Lebesgue_outer_measure (Metric.closedBall 0 (n : ℝ)) :=
              Lebesgue_outer_measure.mono h_sub
            intro h_eq
            apply h_ball_fin
            have h_top : (⊤ : EReal) ≤ Lebesgue_outer_measure (Metric.closedBall 0 (n : ℝ)) := by
              simpa [h_eq] using h_mono
            exact le_antisymm le_top h_top
          have hE₁_fin : Lebesgue_outer_measure E₁ ≠ ⊤ := by rw [hm₁_eq0]; exact EReal.zero_ne_top
          by_cases hd₁_pos : 0 < d₁
          · by_cases hd₂_pos : 0 < d₂
            · -- d₁ > 0, d₂ > 0: use prod_le_of_finite
              have h_ineq : Lebesgue_outer_measure (EuclideanSpace'.prod E₁ G_n) ≤
                  Lebesgue_outer_measure E₁ * Lebesgue_outer_measure G_n :=
                prod_le_of_finite hd₁_pos hd₂_pos hE₁_fin hG_n_fin
              rw [hm₁_eq0, zero_mul] at h_ineq
              exact le_antisymm h_ineq (Lebesgue_outer_measure.nonneg _)
            · -- d₂ = 0: use box-cover-lifting from E₁ (since G_n is in dim 0)
              have hd₂_eq0 : d₂ = 0 := by omega
              subst hd₂_eq0
              have h_nat_lift_G : ∀ (S : ℕ → Box d₁), E₁ ⊆ ⋃ n : ℕ, (S n).toSet →
                  EuclideanSpace'.prod E₁ G_n ⊆ ⋃ n : ℕ, (Box.prod (S n) (Box.unit_cube 0)).toSet := by
                intro S hS_cover y hy
                rw [EuclideanSpace'.prod] at hy
                rcases hy with ⟨⟨a, b⟩, ⟨ha, hb⟩, hy_eq⟩
                obtain ⟨n, hn⟩ : ∃ (n : ℕ), a ∈ (S n).toSet := by simpa using hS_cover ha
                refine Set.mem_iUnion.mpr ⟨n, ?_⟩
                have h_cube_univ : (Box.unit_cube 0).toSet = Set.univ := by
                  ext x; simp [Box.unit_cube, Box.toSet]
                rw [Box.prod_toSet, EuclideanSpace'.prod, Set.mem_image]
                refine ⟨(a, b), ⟨hn, by rw [h_cube_univ]; exact Set.mem_univ _⟩, hy_eq⟩
              have h_nat_sum_G : ∀ (S : ℕ → Box d₁), ∑' (n : ℕ), (Box.prod (S n) (Box.unit_cube 0)).volume.toEReal = ∑' (n : ℕ), (S n).volume.toEReal := by
                intro S
                refine tsum_congr (fun n => ?_)
                rw [Box.volume_prod, show (Box.unit_cube 0).volume = (1 : ℝ) by unfold Box.unit_cube Box.volume; simp, mul_one]
              have hE₁_ne_top : Lebesgue_outer_measure E₁ ≠ ⊤ := by rw [hm₁_eq0]; exact EReal.zero_ne_top
              refine le_antisymm ?_ (Lebesgue_outer_measure.nonneg _)
              refine EReal.le_of_forall_pos_le_add' ?_
              intro δ hδ
              by_cases hd₁_pos_G : 0 < d₁
              · obtain ⟨S, hS_cover, hS_sum⟩ := Lebesgue_outer_measure.exists_cover_close hd₁_pos_G E₁ δ hδ hE₁_ne_top
                have h_prod_cover_G : EuclideanSpace'.prod E₁ G_n ⊆ ⋃ n : ℕ, (Box.prod (S n) (Box.unit_cube 0)).toSet :=
                  h_nat_lift_G S hS_cover
                have h_vol_eq_G : ∑' (n : ℕ), ((Box.prod (S n) (Box.unit_cube 0)).volume.toEReal : EReal) =
                    ∑' (n : ℕ), ((S n).volume.toEReal : EReal) := h_nat_sum_G S
                have h_m_le_vol_G : Lebesgue_outer_measure (EuclideanSpace'.prod E₁ G_n) ≤
                    ∑' (n : ℕ), ((Box.prod (S n) (Box.unit_cube 0)).volume.toEReal : EReal) := by
                  unfold Lebesgue_outer_measure; apply sInf_le
                  refine ⟨Set.univ, fun n : ℕ => Box.prod (S n) (Box.unit_cube 0), h_prod_cover_G, rfl⟩
                calc
                  Lebesgue_outer_measure (EuclideanSpace'.prod E₁ G_n) ≤
                      ∑' (n : ℕ), ((Box.prod (S n) (Box.unit_cube 0)).volume.toEReal : EReal) := h_m_le_vol_G
                  _ = ∑' (n : ℕ), ((S n).volume.toEReal : EReal) := h_vol_eq_G
                  _ ≤ Lebesgue_outer_measure E₁ + (δ : ℝ) := hS_sum
                  _ = (0 : EReal) + (δ : ℝ) := by rw [hm₁_eq0]
                  _ = (δ : EReal) := by simp
                  _ ≤ (0 : EReal) + (δ : EReal) := by simp
              · have hd₁_eq0_G : d₁ = 0 := by omega
                subst hd₁_eq0_G
                simp [EuclideanSpace'.prod, Lebesgue_outer_measure.of_empty]
          · -- d₁ = 0: use box-cover-lifting from G_n (since E₁ is in dim 0)
            have hd₁_eq0 : d₁ = 0 := by omega
            subst hd₁_eq0
              have hd₁_eq0_H : d₁ = 0 := by omega
              subst hd₁_eq0_H
              rw [Lebesgue_outer_measure_of_dim_zero] at hm₁_eq0
              have hE₁_empty : E₁ = ∅ := by
                contrapose! hm₁_eq0; simp [hm₁_eq0]
              subst hE₁_empty
              simp [EuclideanSpace'.prod, Lebesgue_outer_measure.of_empty]
        simp [h_each_zero]
      · rw [h₂_top]
        have hm₁_nonneg : 0 ≤ m₁ := Lebesgue_outer_measure.nonneg E₁
        have hm₁_pos : 0 < m₁ := by
          by_contra! hle; have : m₁ = 0 := le_antisymm hle hm₁_nonneg; exact h₁_zero this
        have htemp : (⊤ : EReal) * m₁ = ⊤ := top_mul_of_pos hm₁_pos
        have htop_mul : m₁ * (⊤ : EReal) = ⊤ := by simpa [mul_comm] using htemp
        rw [htop_mul]; exact le_top
    · -- Both m₁, m₂ ≠ ⊤. They are nonnegative since outer measure is nonnegative.
      have hm₁_nonneg : 0 ≤ m₁ := Lebesgue_outer_measure.nonneg E₁
      have hm₂_nonneg : 0 ≤ m₂ := Lebesgue_outer_measure.nonneg E₂
      have hm₁_ne_bot : m₁ ≠ ⊥ := by
        intro h
        have : (0 : EReal) ≤ ⊥ := by simpa [h] using hm₁_nonneg
        have h_not : ¬ (0 : EReal) ≤ ⊥ := by
          have hlt : (⊥ : EReal) < (0 : EReal) := EReal.bot_lt_zero
          exact not_le.mpr hlt
        exact h_not this
      have hm₂_ne_bot : m₂ ≠ ⊥ := by
        intro h
        have : (0 : EReal) ≤ ⊥ := by simpa [h] using hm₂_nonneg
        have h_not : ¬ (0 : EReal) ≤ ⊥ := by
          have hlt : (⊥ : EReal) < (0 : EReal) := EReal.bot_lt_zero
          exact not_le.mpr hlt
        exact h_not this
      -- Convert to ℝ
      have hm₁_real : (m₁.toReal : EReal) = m₁ := EReal.coe_toReal h₁_top hm₁_ne_bot
      have hm₂_real : (m₂.toReal : EReal) = m₂ := EReal.coe_toReal h₂_top hm₂_ne_bot
      set a := m₁.toReal with ha_def
      set b := m₂.toReal with hb_def
      have ha_nonneg : 0 ≤ a := by
        have : (0 : EReal) ≤ (a : EReal) := by rw [hm₁_real]; exact hm₁_nonneg
        exact_mod_cast this
      have hb_nonneg : 0 ≤ b := by
        have : (0 : EReal) ≤ (b : EReal) := by rw [hm₂_real]; exact hm₂_nonneg
        exact_mod_cast this
      -- Use epsilon argument
      refine EReal.le_of_forall_pos_le_add' ?_
      intro ε hε
      rcases exists_delta_ineq a b ha_nonneg hb_nonneg ε hε with ⟨δ, hδ_pos, h_ineq⟩
      by_cases hd₁ : 0 < d₁
      · by_cases hd₂ : 0 < d₂
        · -- Both dimensions > 0, use exists_cover_close
          obtain ⟨S₁, hS₁_cover, hS₁_sum⟩ := Lebesgue_outer_measure.exists_cover_close hd₁ E₁ δ hδ_pos h₁_top
          obtain ⟨S₂, hS₂_cover, hS₂_sum⟩ := Lebesgue_outer_measure.exists_cover_close hd₂ E₂ δ hδ_pos h₂_top
          have h_prod_cover : EuclideanSpace'.prod E₁ E₂ ⊆ ⋃ k, (Box.prod (S₁ ((Nat.pairEquiv.symm k).1)) (S₂ ((Nat.pairEquiv.symm k).2))).toSet :=
            prod_cover_aux E₁ E₂ S₁ S₂ hS₁_cover hS₂_cover
          have h_vol_tsum : ∑' k, ((Box.prod (S₁ ((Nat.pairEquiv.symm k).1)) (S₂ ((Nat.pairEquiv.symm k).2))).volume.toEReal) =
              (∑' i, ((S₁ i).volume.toEReal)) * (∑' j, ((S₂ j).volume.toEReal)) :=
            tsum_vol_prod_eq_mul_tsum S₁ S₂
          -- The product cover volume is in the defining set, so m(prod) ≤ it
          have h_m_le_vol : Lebesgue_outer_measure (EuclideanSpace'.prod E₁ E₂) ≤
              ∑' k, ((Box.prod (S₁ ((Nat.pairEquiv.symm k).1)) (S₂ ((Nat.pairEquiv.symm k).2))).volume.toEReal) := by
            unfold Lebesgue_outer_measure
            apply sInf_le
            let s : Set ℕ := Set.univ
            let R : s → Box (d₁ + d₂) := fun x =>
              Box.prod (S₁ ((Nat.pairEquiv.symm x.val).1)) (S₂ ((Nat.pairEquiv.symm x.val).2))
            have hR_cover : EuclideanSpace'.prod E₁ E₂ ⊆ ⋃ (n : s), (R n).toSet := by
              intro y hy
              have hy' : y ∈ ⋃ k : ℕ, (Box.prod (S₁ ((Nat.pairEquiv.symm k).1)) (S₂ ((Nat.pairEquiv.symm k).2))).toSet := h_prod_cover hy
              have hy'' : ∃ (k : ℕ), y ∈ (Box.prod (S₁ ((Nat.pairEquiv.symm k).1)) (S₂ ((Nat.pairEquiv.symm k).2))).toSet := by
                simpa using hy'
              rcases hy'' with ⟨k, hk⟩
              refine Set.mem_iUnion.mpr ⟨⟨k, Set.mem_univ k⟩, ?_⟩
              simpa [R] using hk
            have hR_sum : ∑' (n : s), (R n).volume.toEReal =
                ∑' k : ℕ, ((Box.prod (S₁ ((Nat.pairEquiv.symm k).1)) (S₂ ((Nat.pairEquiv.symm k).2))).volume.toEReal) := by
              -- tsum_subtype: ∑' (x : s), f ↑x = ∑' (x : ℕ), s.indicator f x
              -- With s = Set.univ, s.indicator f = f, so we get the equality
              have h := tsum_subtype s (fun (k : ℕ) => ((Box.prod (S₁ ((Nat.pairEquiv.symm k).1)) (S₂ ((Nat.pairEquiv.symm k).2))).volume.toEReal))
              simpa [R, s] using h
            refine ⟨Set.univ, R, hR_cover, ?_⟩
            rw [hR_sum]
          -- Show finiteness: m₁ + δ ≠ ⊤ and m₂ + δ ≠ ⊤
          have hδ_ne_top : ((δ : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top δ
          have hm₁_add_ne_top : m₁ + (δ : ℝ) ≠ ⊤ :=
            ne_of_lt (EReal.add_lt_top h₁_top hδ_ne_top)
          have hm₂_add_ne_top : m₂ + (δ : ℝ) ≠ ⊤ :=
            ne_of_lt (EReal.add_lt_top h₂_top hδ_ne_top)
          -- Also (a + δ) and (b + δ) as EReals are ≠ ⊤
          have h_fin_a_add : ((a + δ : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top (a + δ)
          have h_fin_b_add : ((b + δ : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top (b + δ)
          -- Nonnegativity of the values
          have h_nonneg_vol₁ : 0 ≤ ∑' i, ((S₁ i).volume.toEReal) := by
            apply tsum_nonneg; intro n; exact EReal.coe_nonneg.mpr (Box.volume_nonneg _)
          have h_nonneg_vol₂ : 0 ≤ ∑' j, ((S₂ j).volume.toEReal) := by
            apply tsum_nonneg; intro n; exact EReal.coe_nonneg.mpr (Box.volume_nonneg _)
          have h_nonneg_a_add : 0 ≤ (a + δ : ℝ) := by positivity
          have h_nonneg_b_add : 0 ≤ (b + δ : ℝ) := by positivity
          -- Rewrite sums using m₁, m₂
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
          -- Bound the product: (∑|S₁|)*(∑|S₂|) ≤ (a+δ)*(b+δ)
          have h_vol_bound : (∑' i, ((S₁ i).volume.toEReal)) * (∑' j, ((S₂ j).volume.toEReal)) ≤
              ((a + δ : ℝ) : EReal) * ((b + δ : ℝ) : EReal) := by
            apply mul_le_mul_ereal_fin h_nonneg_vol₁ h_nonneg_vol₂
              (by exact_mod_cast h_nonneg_a_add) (by exact_mod_cast h_nonneg_b_add)
              hS₁_sum' hS₂_sum' h_fin_a_add h_fin_b_add
          -- Now chain the inequalities
          calc
            Lebesgue_outer_measure (EuclideanSpace'.prod E₁ E₂) ≤
                ∑' k, ((Box.prod (S₁ ((Nat.pairEquiv.symm k).1)) (S₂ ((Nat.pairEquiv.symm k).2))).volume.toEReal) := h_m_le_vol
            _ = (∑' i, ((S₁ i).volume.toEReal)) * (∑' j, ((S₂ j).volume.toEReal)) := h_vol_tsum
            _ ≤ ((a + δ : ℝ) : EReal) * ((b + δ : ℝ) : EReal) := h_vol_bound
            _ = ((a + δ) * (b + δ) : ℝ) := by simp
            _ ≤ (a * b + ε : ℝ) := by exact_mod_cast h_ineq
            _ = ((a : ℝ) * (b : ℝ) + (ε : ℝ) : EReal) := by simp
            _ = (a : EReal) * (b : EReal) + (ε : EReal) := by simp
            _ = m₁ * m₂ + (ε : EReal) := by
              simp [hm₁_real, hm₂_real]
        · -- d₂ = 0
          have hd₂_eq0 : d₂ = 0 := by omega
          subst hd₂_eq0
          by_cases hE₂_empty : E₂ = ∅
          · subst hE₂_empty
            have h_prod_empty : EuclideanSpace'.prod E₁ (∅ : Set (EuclideanSpace' 0)) = (∅ : Set (EuclideanSpace' (d₁ + 0))) := by
              dsimp [EuclideanSpace'.prod]; simp
            rw [h_prod_empty, Lebesgue_outer_measure.of_empty]
            have hm₂_zero : m₂ = (0 : EReal) := by
              rw [hm₂_def, Lebesgue_outer_measure_of_dim_zero]
              have hE₂_not_nonempty : ¬ (∅ : Set (EuclideanSpace' 0)).Nonempty := by simp
              simp [hE₂_not_nonempty]
            rw [hm₂_zero, mul_zero]
            have hε_nonneg : (0 : EReal) ≤ (ε : EReal) := by exact_mod_cast hε.le
            simpa [zero_add] using hε_nonneg
          · have hE₂_ne : E₂.Nonempty := Set.nonempty_iff_ne_empty.mpr hE₂_empty
            have hm₂_one : m₂ = (1 : EReal) := by
              rw [hm₂_def, Lebesgue_outer_measure_of_dim_zero, if_pos hE₂_ne]
            have h_prod_le_m₁ : Lebesgue_outer_measure (EuclideanSpace'.prod E₁ E₂) ≤ m₁ := by
              have h_nat_cover_lift : ∀ (S : ℕ → Box d₁), E₁ ⊆ ⋃ n : ℕ, (S n).toSet →
                  EuclideanSpace'.prod E₁ E₂ ⊆ ⋃ n : ℕ, (Box.prod (S n) (Box.unit_cube 0)).toSet := by
                intro S hS_cover y hy
                rw [EuclideanSpace'.prod] at hy
                rcases hy with ⟨⟨a, b⟩, ⟨ha, hb⟩, hy_eq⟩
                obtain ⟨n, hn⟩ : ∃ (n : ℕ), a ∈ (S n).toSet := by
                  simpa using hS_cover ha
                have h_cube_univ : (Box.unit_cube 0).toSet = Set.univ := by
                  ext x; simp [Box.unit_cube, Box.toSet]
                refine Set.mem_iUnion.mpr ⟨n, ?_⟩
                rw [Box.prod_toSet, EuclideanSpace'.prod, Set.mem_image]
                refine ⟨(a, b), ⟨hn, by rw [h_cube_univ]; apply Set.mem_univ⟩, hy_eq⟩
              have h_nat_sum_eq : ∀ (S : ℕ → Box d₁), ∑' (n : ℕ), (Box.prod (S n) (Box.unit_cube 0)).volume.toEReal = ∑' (n : ℕ), (S n).volume.toEReal := by
                intro S
                refine tsum_congr (fun n => ?_)
                rw [Box.volume_prod, show (Box.unit_cube 0).volume = (1 : ℝ) by unfold Box.unit_cube Box.volume; simp, mul_one]
              -- Use the ℕ-indexed cover equivalence (available since hd₁ > 0)
              have h_eq_m₁ : m₁ = sInf ((fun (S : ℕ → Box d₁) ↦ ∑' (n : ℕ), ((S n).volume.toEReal : EReal)) ''
                  {S : ℕ → Box d₁ | E₁ ⊆ ⋃ n : ℕ, (S n).toSet}) := by
                rw [hm₁_def, Lebesgue_outer_measure_eq_nat_indexed hd₁ E₁]
              have h_eq_m_prod : Lebesgue_outer_measure (EuclideanSpace'.prod E₁ E₂) = sInf ((fun (R : ℕ → Box (d₁ + 0)) ↦ ∑' (n : ℕ), ((R n).volume.toEReal : EReal)) ''
                  {R : ℕ → Box (d₁ + 0) | EuclideanSpace'.prod E₁ E₂ ⊆ ⋃ n : ℕ, (R n).toSet}) := by
                rw [Lebesgue_outer_measure_eq_nat_indexed (by
                  have : 0 < d₁ + 0 := hd₁
                  exact this) (EuclideanSpace'.prod E₁ E₂)]
              rw [h_eq_m₁, h_eq_m_prod]
              -- Show the sInf for prod ≤ sInf for E₁ by lifting covers
              refine sInf_le_sInf ?_
              intro V hV
              rcases hV with ⟨S, hS_cover, hV_eq⟩
              have h_vol : ((fun R : ℕ → Box (d₁ + 0) ↦ ∑' (n : ℕ), ((R n).volume.toEReal : EReal))
                  (fun n : ℕ => Box.prod (S n) (Box.unit_cube 0))) = V := by
                calc
                  ∑' (n : ℕ), ((Box.prod (S n) (Box.unit_cube 0)).volume.toEReal : EReal) =
                      ∑' (n : ℕ), ((S n).volume.toEReal : EReal) := by rw [h_nat_sum_eq S]
                  _ = (fun S : ℕ → Box d₁ ↦ ∑' (n : ℕ), ((S n).volume.toEReal : EReal)) S := rfl
                  _ = V := hV_eq
              refine ⟨fun n : ℕ => Box.prod (S n) (Box.unit_cube 0), h_nat_cover_lift S hS_cover, h_vol⟩
            calc
              Lebesgue_outer_measure (EuclideanSpace'.prod E₁ E₂) ≤ m₁ := h_prod_le_m₁
              _ = m₁ * (1 : EReal) := by simp
              _ = m₁ * m₂ := by rw [hm₂_one]
              _ ≤ m₁ * m₂ + (ε : EReal) := le_add_of_nonneg_right (by exact_mod_cast hε.le)
      · -- d₁ = 0
        have hd₁_eq0 : d₁ = 0 := by omega
        subst hd₁_eq0
        by_cases hE₁_empty : E₁ = ∅
        · subst hE₁_empty
          have h_prod_empty : EuclideanSpace'.prod (∅ : Set (EuclideanSpace' 0)) E₂ = (∅ : Set (EuclideanSpace' (0 + d₂))) := by
            dsimp [EuclideanSpace'.prod]; simp
          rw [h_prod_empty, Lebesgue_outer_measure.of_empty]
          have hm₁_zero : m₁ = (0 : EReal) := by
            rw [hm₁_def, Lebesgue_outer_measure_of_dim_zero]
            have hE₁_not_nonempty : ¬ (∅ : Set (EuclideanSpace' 0)).Nonempty := by simp
            simp [hE₁_not_nonempty]
          rw [hm₁_zero, zero_mul]
          have hε_nonneg'' : (0 : EReal) ≤ (ε : EReal) := by exact_mod_cast hε.le
          simpa [zero_add] using hε_nonneg''
        · have hE₁_ne : E₁.Nonempty := Set.nonempty_iff_ne_empty.mpr hE₁_empty
          have hm₁_one : m₁ = (1 : EReal) := by
            rw [hm₁_def, Lebesgue_outer_measure_of_dim_zero, if_pos hE₁_ne]
          by_cases hd₂_pos : 0 < d₂
          · -- d₁ = 0, d₂ > 0
            have h_prod_le_m₂ : Lebesgue_outer_measure (EuclideanSpace'.prod E₁ E₂) ≤ m₂ := by
              have h_nat_cover_lift : ∀ (S : ℕ → Box d₂), E₂ ⊆ ⋃ n : ℕ, (S n).toSet →
                  EuclideanSpace'.prod E₁ E₂ ⊆ ⋃ n : ℕ, (Box.prod (Box.unit_cube 0) (S n)).toSet := by
                intro S hS_cover y hy
                rw [EuclideanSpace'.prod] at hy
                rcases hy with ⟨⟨a, b⟩, ⟨ha, hb⟩, hy_eq⟩
                obtain ⟨n, hn⟩ : ∃ (n : ℕ), b ∈ (S n).toSet := by
                  simpa using hS_cover hb
                have h_cube_univ : (Box.unit_cube 0).toSet = Set.univ := by
                  ext x; simp [Box.unit_cube, Box.toSet]
                refine Set.mem_iUnion.mpr ⟨n, ?_⟩
                rw [Box.prod_toSet, EuclideanSpace'.prod, Set.mem_image]
                refine ⟨(a, b), ⟨by rw [h_cube_univ]; apply Set.mem_univ, hn⟩, hy_eq⟩
              have h_nat_sum_eq : ∀ (S : ℕ → Box d₂), ∑' (n : ℕ), (Box.prod (Box.unit_cube 0) (S n)).volume.toEReal = ∑' (n : ℕ), (S n).volume.toEReal := by
                intro S
                refine tsum_congr (fun n => ?_)
                rw [Box.volume_prod, show (Box.unit_cube 0).volume = (1 : ℝ) by unfold Box.unit_cube Box.volume; simp, one_mul]
              have hd₂_pos' : 0 < 0 + d₂ := by simpa using hd₂_pos
              have h_eq_m₂ : m₂ = sInf ((fun (S : ℕ → Box d₂) ↦ ∑' (n : ℕ), ((S n).volume.toEReal : EReal)) ''
                  {S : ℕ → Box d₂ | E₂ ⊆ ⋃ n : ℕ, (S n).toSet}) := by
                rw [hm₂_def, Lebesgue_outer_measure_eq_nat_indexed hd₂_pos E₂]
              have h_eq_m_prod : Lebesgue_outer_measure (EuclideanSpace'.prod E₁ E₂) = sInf ((fun (R : ℕ → Box (0 + d₂)) ↦ ∑' (n : ℕ), ((R n).volume.toEReal : EReal)) ''
                  {R : ℕ → Box (0 + d₂) | EuclideanSpace'.prod E₁ E₂ ⊆ ⋃ n : ℕ, (R n).toSet}) := by
                rw [Lebesgue_outer_measure_eq_nat_indexed hd₂_pos' (EuclideanSpace'.prod E₁ E₂)]
              rw [h_eq_m₂, h_eq_m_prod]
              refine sInf_le_sInf ?_
              intro V hV
              rcases hV with ⟨S, hS_cover, hV_eq⟩
              have h_vol : ((fun R : ℕ → Box (0 + d₂) ↦ ∑' (n : ℕ), ((R n).volume.toEReal : EReal))
                  (fun n : ℕ => Box.prod (Box.unit_cube 0) (S n))) = V := by
                calc
                  ∑' (n : ℕ), ((Box.prod (Box.unit_cube 0) (S n)).volume.toEReal : EReal) =
                      ∑' (n : ℕ), ((S n).volume.toEReal : EReal) := by rw [h_nat_sum_eq S]
                  _ = (fun S : ℕ → Box d₂ ↦ ∑' (n : ℕ), ((S n).volume.toEReal : EReal)) S := rfl
                  _ = V := hV_eq
              refine ⟨fun n : ℕ => Box.prod (Box.unit_cube 0) (S n), h_nat_cover_lift S hS_cover, h_vol⟩
            calc
              Lebesgue_outer_measure (EuclideanSpace'.prod E₁ E₂) ≤ m₂ := h_prod_le_m₂
              _ = (1 : EReal) * m₂ := by simp
              _ = m₁ * m₂ := by rw [hm₁_one]
              _ ≤ m₁ * m₂ + (ε : EReal) := le_add_of_nonneg_right (by exact_mod_cast hε.le)
          · -- d₁ = 0, d₂ = 0
            have hd₂_eq0 : d₂ = 0 := by omega
            subst hd₂_eq0
            by_cases hE₂_empty : E₂ = ∅
            · subst hE₂_empty
              have h_prod_empty : EuclideanSpace'.prod E₁ (∅ : Set (EuclideanSpace' 0)) = (∅ : Set (EuclideanSpace' 0)) := by
                dsimp [EuclideanSpace'.prod]; simp
              rw [h_prod_empty, Lebesgue_outer_measure.of_empty]
              have hm₂_zero : m₂ = (0 : EReal) := by
                rw [hm₂_def, Lebesgue_outer_measure_of_dim_zero]
                simp
              rw [hm₂_zero, mul_zero]
              have hε_nonneg' : (0 : EReal) ≤ (ε : EReal) := by exact_mod_cast hε.le
              simpa [zero_add] using hε_nonneg'
            · have hE₂_ne : E₂.Nonempty := Set.nonempty_iff_ne_empty.mpr hE₂_empty
              have hm₂_one : m₂ = (1 : EReal) := by
                rw [hm₂_def, Lebesgue_outer_measure_of_dim_zero, if_pos hE₂_ne]
              calc
                Lebesgue_outer_measure (EuclideanSpace'.prod E₁ E₂) ≤ (1 : EReal) := by
                  have : EuclideanSpace'.prod E₁ E₂ ⊆ (Set.univ : Set (EuclideanSpace' 0)) := Set.subset_univ _
                  have h_univ_meas : Lebesgue_outer_measure (Set.univ : Set (EuclideanSpace' 0)) = (1 : EReal) := by
                    rw [Lebesgue_outer_measure_of_dim_zero, if_pos (by simp)]
                  calc
                    Lebesgue_outer_measure (EuclideanSpace'.prod E₁ E₂) ≤ Lebesgue_outer_measure (Set.univ : Set (EuclideanSpace' 0)) :=
                      Lebesgue_outer_measure.mono this
                    _ = (1 : EReal) := h_univ_meas
                _ = m₁ * m₂ := by rw [hm₁_one, hm₂_one, mul_one]
                _ ≤ m₁ * m₂ + (ε : EReal) := le_add_of_nonneg_right (by exact_mod_cast hε.le)