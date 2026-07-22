import Analysis.MeasureTheory.Section_1_2_1

/-!
# Introduction to Measure Theory, Section 1.2.2: Lebesgue measurability

A companion to (the introduction to) Section 1.2.2 of the book "An introduction to Measure Theory".

-/

/-- Lemma 1.2.13(i) (Every open set is Lebesgue measurable). -/
theorem IsOpen.measurable {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: IsOpen E) : LebesgueMeasurable E := by
  -- Strategy: For any ε > 0, choose U = E itself
  -- Since E is already open, U \ E = E \ E = ∅, and m*(∅) = 0 ≤ ε
  intro ε hε
  -- Witness: U = E
  use E
  constructor
  · -- E is open (given)
    exact hE
  constructor
  · -- E ⊆ E (reflexivity)
    rfl
  · -- Show m*(E \ E) ≤ ε
    have h_empty : E \ E = ∅ := Set.diff_self
    rw [h_empty]
    have h_zero : Lebesgue_outer_measure (∅ : Set (EuclideanSpace' d)) = 0 :=
      Lebesgue_outer_measure.of_empty d
    rw [h_zero]
    exact le_of_lt hε

/-- Helper: For a finset of pairwise almost disjoint dyadic boxes, the outer measure of their
    union equals the sum of their volumes. -/
private lemma Lebesgue_outer_measure.sum_of_almost_disjoint_finset {d : ℕ} (_hd_pos : 0 < d)
    {t : Finset ℕ} {Q : ℕ → Box d} (_hQ_dyadic : ∀ i, (Q i).IsDyadic)
    (hQ : Pairwise (Function.onFun AlmostDisjoint Q)) :
    Lebesgue_outer_measure (⋃ i ∈ t, (Q i).toSet) = ∑ i ∈ t, ((Q i).volume : EReal) := by
  -- Direct proof using elementary set theory (avoids flawed union_of_separated approach)
  -- Convert to Fin (t.card) indexed boxes via Finset.equivFin
  let equiv := t.equivFin
  let B' : Fin t.card → Box d := fun i => Q (equiv.symm i).val
  -- Show the biUnion equals the iUnion over Fin t.card
  have h_eq : (⋃ i ∈ t, (Q i).toSet) = ⋃ (i : Fin t.card), (B' i).toSet := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_iUnion, B']
    constructor
    · intro ⟨i, hi, hx⟩
      exact ⟨equiv ⟨i, hi⟩, by simp [hx]⟩
    · intro ⟨i, hx⟩
      exact ⟨(equiv.symm i).val, (equiv.symm i).property, hx⟩
  rw [h_eq]
  -- The finite union is elementary
  have hElem : IsElementary (⋃ (i : Fin t.card), (B' i).toSet) :=
    IsElementary.iUnion_boxes B'
  -- Almost-disjointness for Fin-indexed boxes
  have hB'_disj : Pairwise (Function.onFun AlmostDisjoint B') := by
    intro i j h_ne
    simp only [Function.onFun, B']
    apply hQ
    intro h_eq
    have heq : equiv.symm i = equiv.symm j := Subtype.ext h_eq
    exact h_ne (equiv.symm.injective heq)
  -- Apply IsElementary.almost_disjoint: measure = ∑ volumes
  have h_measure := IsElementary.almost_disjoint hElem B' rfl hB'_disj
  -- Convert measure to outer measure
  have h_outer := Lebesgue_outer_measure.elementary _ hElem
  -- Sum conversion: ∑ i : Fin t.card, (B' i).volume = ∑ i ∈ t, (Q i).volume
  have h_sum_eq : ∑ i : Fin t.card, (B' i).volume = ∑ i ∈ t, (Q i).volume := by
    conv_rhs => rw [← Finset.sum_attach]
    refine Finset.sum_equiv equiv.symm ?_ ?_
    · intro i; simp [Finset.mem_univ, Finset.mem_attach]
    · intro i _; simp only [B']
  rw [h_outer, h_measure, h_sum_eq]
  -- Now need: ↑(∑ i ∈ t, (Q i).volume) = ∑ i ∈ t, ↑(Q i).volume
  exact EReal.coe_finset_sum (fun i _ => Box.volume_nonneg _)


/-- Helper: Bounded closed sets are measurable (Lemma 1.2.13(ii) for bounded case).
    For bounded closed E (compact by Heine-Borel), show that for any ε > 0,
    there exists open U ⊇ E with m\*(U \ E) ≤ ε. -/
private lemma IsClosed.measurable_of_bounded {d:ℕ} {E: Set (EuclideanSpace' d)}
    (hE: IsClosed E) (hE_bounded : Bornology.IsBounded E) : LebesgueMeasurable E := by
  intro ε hε
  -- Empty case
  by_cases hE_empty : E = ∅
  · use ∅
    refine ⟨isOpen_empty, ?_, ?_⟩
    · rw [hE_empty]
    · simp [Lebesgue_outer_measure.of_empty]; exact le_of_lt hε
  -- Non-empty bounded closed E is compact
  have hE_nonempty : E.Nonempty := Set.nonempty_iff_ne_empty.mpr hE_empty
  -- Get open U with m*(U) ≤ m*(E) + ε/2
  have hε_half_pos : (0 : EReal) < ε / 2 := by
    cases ε with
    | bot => exact absurd hε (not_lt.mpr bot_le)
    | top =>
      show (0 : EReal) < ⊤ / 2
      -- ⊤ / 2 = ⊤ in EReal since 2 > 0 and 2 ≠ ⊤
      have : (⊤ : EReal) / 2 = ⊤ := by
        have h2_pos : (0 : EReal) < 2 := by norm_num
        have h2_ne_top : (2 : EReal) ≠ ⊤ := by
          intro h
          have : (2 : EReal) = (2 : ℝ) := rfl
          rw [this] at h
          exact EReal.coe_ne_top 2 h
        exact EReal.top_div_of_pos_ne_top h2_pos h2_ne_top
      rw [this]
      exact EReal.zero_lt_top
    | coe r =>
      have hr_pos : 0 < r := EReal.coe_pos.mp hε
      rw [show (2 : EReal) = (2 : ℝ) from rfl, ← EReal.coe_div r 2]
      exact EReal.coe_pos.mpr (half_pos hr_pos)
  obtain ⟨U, hU_open, hE_sub_U, hU_meas⟩ := Lebesgue_outer_measure.exists_open_superset_measure_le E (ε/2) hε_half_pos
  use U
  refine ⟨hU_open, hE_sub_U, ?_⟩
  -- Key: show m*(U \ E) ≤ ε
  -- U \ E is open
  have h_diff_open : IsOpen (U \ E) := hU_open.sdiff hE
  -- Handle d = 0 separately
  by_cases hd : d = 0
  · -- In dimension 0, EuclideanSpace' 0 = Fin 0 → ℝ is a subsingleton
    -- Since E is nonempty and E ⊆ U, and U is nonempty (contains E), we have E = U
    -- Therefore U \ E = ∅, so m*(U \ E) = 0 ≤ ε
    subst hd
    have : Subsingleton (EuclideanSpace' 0) := by
      unfold EuclideanSpace'
      infer_instance
    have hU_nonempty : U.Nonempty := hE_nonempty.mono hE_sub_U
    have hEU_eq : E = U := by
      apply Set.Subset.antisymm hE_sub_U
      intro x hx
      obtain ⟨y, hy⟩ := hE_nonempty
      have hxy : x = y := Subsingleton.elim x y
      rw [hxy]
      exact hy
    rw [hEU_eq, Set.diff_self, Lebesgue_outer_measure.of_empty]
    exact le_of_lt hε
  push_neg at hd
  have hd_pos : 0 < d := Nat.pos_of_ne_zero hd
  -- If U \ E is empty, trivial
  by_cases h_diff_empty : U \ E = ∅
  · rw [h_diff_empty, Lebesgue_outer_measure.of_empty]; exact le_of_lt hε
  -- Main argument: U \ E is nonempty open, decompose into cubes
  have h_diff_nonempty : (U \ E).Nonempty := Set.nonempty_iff_ne_empty.mpr h_diff_empty
  obtain ⟨Q, hQ_union, hQ_dyadic, hQ_pairwise⟩ := h_diff_open.eq_union_boxes hd_pos (U \ E) h_diff_nonempty
  rw [hQ_union]
  -- m*(⋃ Q_n) = ∑ |Q_n|
  have h_measure_eq : Lebesgue_outer_measure (⋃ n, (Q n).toSet) = ∑' n, (Q n).volume.toEReal := by
    have h1 := Lebesgue_outer_measure.union_of_almost_disjoint hQ_pairwise
    simp_rw [Lebesgue_outer_measure.elementary _ (IsElementary.box _),
             IsElementary.measure_of_box] at h1
    exact h1
  rw [h_measure_eq]
  -- Use compactness: E is compact (closed + bounded)
  -- EuclideanSpace ℝ (Fin d) is finite-dimensional, hence ProperSpace
  -- By Heine-Borel: closed + bounded = compact in proper spaces
  have hE_compact : IsCompact E := Metric.isCompact_of_isClosed_isBounded hE hE_bounded
  calc ∑' n, (Q n).volume.toEReal
      = Lebesgue_outer_measure (⋃ n, (Q n).toSet) := h_measure_eq.symm
    _ = Lebesgue_outer_measure (U \ E) := by rw [← hQ_union]
    _ ≤ ε / 2 := by
        -- Key: E is compact, so m*(E) is finite (not ⊥ or ⊤)
        have hE_finite : Lebesgue_outer_measure E ≠ ⊤ :=
          Lebesgue_outer_measure.finite_of_compact hE_compact
        have hE_ne_bot : Lebesgue_outer_measure E ≠ ⊥ := by
          have h_nonneg : 0 ≤ Lebesgue_outer_measure E := Lebesgue_outer_measure.nonneg E
          intro h_eq
          rw [h_eq] at h_nonneg
          -- 0 ≤ ⊥ is false in EReal
          exact not_le.mpr EReal.bot_lt_zero h_nonneg

        -- For each finite N, show ∑_{i < N} vol(Q_i) ≤ ε/2
        have h_finite_sum_bound : ∀ (t : Finset ℕ),
            ∑ i ∈ t, ((Q i).volume : EReal) ≤ ε / 2 := by
          intro t
          -- Handle empty finset case
          by_cases ht_empty : t = ∅
          · rw [ht_empty]
            simp
            exact le_of_lt hε_half_pos
          -- Now t is nonempty
          -- Let F_t = ⋃_{i ∈ t} Q_i
          let F_t := ⋃ i ∈ t, (Q i).toSet
          -- F_t is compact (finite union of compact boxes)
          have hF_compact : IsCompact F_t := by
            -- Each box is compact (product of compact intervals)
            have hQ_compact : ∀ i ∈ t, IsCompact ((Q i).toSet) := by
              intro i _
              exact Box.isCompact (Q i) (Box.IsDyadic.all_sides_Icc (hQ_dyadic i))
            -- Finite union of compact sets is compact
            exact Finset.isCompact_biUnion t hQ_compact
          -- E ∩ F_t = ∅ (since F_t ⊆ U\E)
          have hE_F_disj : E ∩ F_t = ∅ := by
            ext x
            simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and, F_t]
            intro hxE
            simp only [Set.mem_iUnion, not_exists]
            intro i hi
            -- x ∈ E and x ∈ Q_i, but Q_i ⊆ U\E
            have hQ_sub : (Q i).toSet ⊆ U \ E := by
              have : (Q i).toSet ⊆ ⋃ n, (Q n).toSet := by
                intro y hy
                exact Set.mem_iUnion_of_mem i hy
              rw [← hQ_union] at this
              exact this
            intro hxi
            exact (hQ_sub hxi).2 hxE
          -- By compactness: set_dist E F_t > 0 (t is nonempty, so F_t is nonempty)
          have ht_ne : t.Nonempty := Finset.nonempty_iff_ne_empty.mpr ht_empty
          obtain ⟨i, hi⟩ := ht_ne
          have hF_nonempty : F_t.Nonempty :=
            (Box.toSet_nonempty_of_IsDyadic (hQ_dyadic i)).mono (Set.subset_biUnion_of_mem hi)
          have h_sep : set_dist E F_t > 0 :=
            dist_of_disj_compact_pos E F_t hE_nonempty hF_nonempty hE_compact hF_compact hE_F_disj
          -- By separation: m*(E ∪ F_t) = m*(E) + m*(F_t)
          have h_add : Lebesgue_outer_measure (E ∪ F_t) =
                       Lebesgue_outer_measure E + Lebesgue_outer_measure F_t :=
            Lebesgue_outer_measure.union_of_separated hd_pos h_sep
          -- E ∪ F_t ⊆ U
          have h_sub : E ∪ F_t ⊆ U := by
            intro x hx
            cases hx with
            | inl hxE => exact hE_sub_U hxE
            | inr hxF =>
              -- F_t ⊆ ⋃ n, Q_n = U\E ⊆ U
              have : F_t ⊆ ⋃ n, (Q n).toSet := by
                intro y hy
                simp [F_t] at hy
                obtain ⟨i, hi, hyi⟩ := hy
                exact Set.mem_iUnion_of_mem i hyi
              have hF_sub : (⋃ n, (Q n).toSet) ⊆ U := by
                rw [← hQ_union]
                exact Set.diff_subset
              exact hF_sub (this hxF)
          -- So m*(E ∪ F_t) ≤ m*(U) ≤ m*(E) + ε/2
          have h_bound : Lebesgue_outer_measure (E ∪ F_t) ≤ Lebesgue_outer_measure E + ε / 2 := by
            calc Lebesgue_outer_measure (E ∪ F_t)
                ≤ Lebesgue_outer_measure U := Lebesgue_outer_measure.mono h_sub
              _ ≤ Lebesgue_outer_measure E + ε / 2 := hU_meas
          -- Therefore m*(E) + m*(F_t) ≤ m*(E) + ε/2, so m*(F_t) ≤ ε/2
          rw [h_add] at h_bound
          -- Cancellation: m*(E) + m*(F_t) ≤ m*(E) + ε/2 implies m*(F_t) ≤ ε/2
          have h_F_bound : Lebesgue_outer_measure F_t ≤ ε / 2 := by
            -- Use EReal.sub_le_of_le_add': if a ≤ b + c then a - b ≤ c
            have h1 : Lebesgue_outer_measure E + Lebesgue_outer_measure F_t - Lebesgue_outer_measure E ≤ ε / 2 :=
              EReal.sub_le_of_le_add' h_bound
            -- Since m*(E) is finite (not ⊥ or ⊤), we have (m*(E) + m*(F_t)) - m*(E) = m*(F_t)
            -- Case analysis on m*(E) being a real number
            have h_cancel : Lebesgue_outer_measure E + Lebesgue_outer_measure F_t - Lebesgue_outer_measure E = Lebesgue_outer_measure F_t := by
              cases h : Lebesgue_outer_measure E with
              | bot => exact absurd h hE_ne_bot
              | top => exact absurd h hE_finite
              | coe r =>
                -- m*(E) = r (a real number), so the goal is already r + m*(F_t) - r = m*(F_t)
                exact EReal.add_sub_cancel_left
            rw [h_cancel] at h1
            exact h1
          -- Finally: m*(F_t) = ∑_{i ∈ t} vol(Q_i) by almost disjoint union
          calc ∑ i ∈ t, ((Q i).volume : EReal)
              = Lebesgue_outer_measure F_t := by
                symm
                exact Lebesgue_outer_measure.sum_of_almost_disjoint_finset hd_pos hQ_dyadic hQ_pairwise
            _ ≤ ε / 2 := h_F_bound

        -- Now: ∑' n, vol(Q_n) ≤ ε/2 by supremum of finite sums
        have hvol_nonneg : ∀ n, 0 ≤ (Q n).volume := fun n => Box.volume_nonneg _
        have h_range_bound : ∀ N : ℕ, ∑ i ∈ Finset.range N, ((Q i).volume : EReal) ≤ ε / 2 :=
          fun N => h_finite_sum_bound (Finset.range N)
        have h_tsum_bound : ∑' n, ((Q n).volume : EReal) ≤ ε / 2 :=
          EReal.tsum_le_of_sum_range_le hvol_nonneg h_range_bound
        -- Convert back using h_measure_eq
        calc Lebesgue_outer_measure (U \ E)
            = Lebesgue_outer_measure (⋃ n, (Q n).toSet) := by rw [hQ_union]
          _ = ∑' n, ((Q n).volume : EReal) := h_measure_eq
          _ ≤ ε / 2 := h_tsum_bound
    _ ≤ ε := by
        cases ε with
        | bot => exact absurd hε (not_lt.mpr bot_le)
        | top => exact le_top
        | coe r =>
          have hr_pos : 0 < r := EReal.coe_pos.mp hε
          rw [show (2 : EReal) = (2 : ℝ) from rfl, ← EReal.coe_div r 2]
          exact EReal.coe_le_coe_iff.mpr (half_le_self (le_of_lt hr_pos))

/-- Lemma 1.2.13(ii) (Every closed set is Lebesgue measurable). -/
theorem IsClosed.measurable {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: IsClosed E) : LebesgueMeasurable E := by
  -- Write E = ⋃_{n=0}^∞ (E ∩ closedBall 0 n)
  have h_union : E = ⋃ n : ℕ, E ∩ Metric.closedBall 0 n := (Metric.iUnion_inter_closedBall_nat E 0).symm
  rw [h_union]
  -- Each E ∩ closedBall 0 n is closed (intersection of closed sets) and bounded
  have h_closed : ∀ n : ℕ, IsClosed (E ∩ Metric.closedBall 0 n) :=
    fun n => hE.inter Metric.isClosed_closedBall
  have h_bounded : ∀ n : ℕ, Bornology.IsBounded (E ∩ Metric.closedBall 0 n) :=
    fun n => Metric.isBounded_closedBall.subset Set.inter_subset_right
  -- Apply IsClosed.measurable_of_bounded to each piece
  have h_meas : ∀ n : ℕ, LebesgueMeasurable (E ∩ Metric.closedBall 0 n) :=
    fun n => IsClosed.measurable_of_bounded (h_closed n) (h_bounded n)
  -- Inline countable union proof (Lemma 1.2.13(vi) is defined later in this file)
  intro ε hε
  -- Convert EReal ε to a real number ε' with 0 < ε' ≤ ε
  obtain ⟨ε', hε'_pos, hε'_le⟩ : ∃ ε' : ℝ, 0 < ε' ∧ (ε' : EReal) ≤ ε := by
    cases ε with
    | bot => exact absurd hε (not_lt.mpr bot_le)
    | top => exact ⟨1, one_pos, le_top⟩
    | coe r =>
      have hr : 0 < r := EReal.coe_pos.mp hε
      exact ⟨r, hr, le_refl _⟩
  -- For each n, get U_n open with (E ∩ closedBall 0 n) ⊆ U_n and m*(U_n \ (E ∩ closedBall 0 n)) ≤ ε'/2^(n+1)
  have hδ_pos : ∀ n, (0:EReal) < ε' / 2^(n+1) := fun n => by
    apply EReal.div_pos (EReal.coe_pos.mpr hε'_pos)
    · exact EReal.coe_pow 2 (n+1) ▸ EReal.coe_pos.mpr (by positivity)
    · exact EReal.coe_pow 2 (n+1) ▸ EReal.coe_ne_top ((2:ℝ)^(n+1))
  choose U hU_open hE_sub hU_diff using fun n => h_meas n (ε' / 2^(n+1)) (hδ_pos n)
  -- The open set is ⋃ n, U n
  use ⋃ n, U n
  constructor
  · exact isOpen_iUnion hU_open
  constructor
  · apply Set.iUnion_mono; intro n; exact hE_sub n
  · -- m*((⋃ n, U n) \ (⋃ n, E ∩ closedBall 0 n)) ≤ ε
    have h_diff_subset : (⋃ (n : ℕ), U n) \ (⋃ (n : ℕ), E ∩ Metric.closedBall 0 ↑n) ⊆ ⋃ (n : ℕ), (U n \ (E ∩ Metric.closedBall 0 ↑n)) := by
      intro x ⟨hx_in_U, hx_not_in_E⟩
      simp only [Set.mem_iUnion] at hx_in_U hx_not_in_E ⊢
      obtain ⟨k, hxk⟩ := hx_in_U
      use k
      constructor
      · exact hxk
      · intro hx_Ek; exact hx_not_in_E ⟨k, hx_Ek⟩
    calc Lebesgue_outer_measure ((⋃ (n : ℕ), U n) \ (⋃ (n : ℕ), E ∩ Metric.closedBall 0 ↑n))
        ≤ Lebesgue_outer_measure (⋃ (n : ℕ), (U n \ (E ∩ Metric.closedBall 0 ↑n))) :=
          Lebesgue_outer_measure.mono h_diff_subset
      _ ≤ ∑' (n : ℕ), Lebesgue_outer_measure (U n \ (E ∩ Metric.closedBall 0 ↑n)) :=
          Lebesgue_outer_measure.union_le _
      _ ≤ ∑' (n : ℕ), ((ε' / 2^(n+1) : ℝ) : EReal) := by
          have h_nonneg : ∀ n, 0 ≤ ε' / 2^(n+1) := fun n => by positivity
          have h_summable : Summable (fun n => ε' / 2^(n+1)) :=
            (summable_geometric_two' ε').congr (fun n => by ring)
          have h_f_nonneg : ∀ n, 0 ≤ Lebesgue_outer_measure (U n \ (E ∩ Metric.closedBall 0 ↑n)) :=
            fun n => Lebesgue_outer_measure.nonneg _
          have h_le_coe : ∀ n, Lebesgue_outer_measure (U n \ (E ∩ Metric.closedBall 0 ↑n)) ≤ ((ε' / 2^(n+1) : ℝ) : EReal) := by
            intro n
            calc Lebesgue_outer_measure (U n \ (E ∩ Metric.closedBall 0 ↑n))
                ≤ (↑ε' : EReal) / 2^(n+1) := hU_diff n
              _ = ↑(ε' / 2^(n+1)) := by
                  rw [EReal.coe_div]
                  congr 1
                  exact Eq.symm (EReal.coe_pow 2 (n + 1))
          exact EReal.tsum_le_coe_tsum_of_forall_le h_f_nonneg h_nonneg h_summable h_le_coe
      _ = ε' := by
          have h_sum : ∑' n : ℕ, (ε' : ℝ) / 2^(n+1) = ε' := tsum_geometric_eps ε' hε'_pos
          have h_summable : Summable (fun n => ε' / 2^(n+1)) :=
            (summable_geometric_two' ε').congr (fun n => by ring)
          have h_nonneg : ∀ n, 0 ≤ ε' / 2^(n+1) := fun n => by positivity
          rw [← EReal.coe_tsum_of_nonneg h_nonneg h_summable, h_sum]
      _ ≤ ε := hε'_le

abbrev IsNull {d:ℕ} (E: Set (EuclideanSpace' d)) : Prop := Lebesgue_outer_measure E = 0

/-- Lemma 1.2.13(iii) (Every null set is Lebesgue measurable). -/
theorem IsNull.measurable {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: IsNull E) : LebesgueMeasurable E := by
  -- Strategy: For any ε > 0, since m*(E) = 0, get a box cover with total volume < ε,
  -- then inflate boxes to open sets. The union is open and contains E.
  intro ε hε
  -- Handle dimension 0 separately
  by_cases hd : d = 0
  · -- In dimension 0, EuclideanSpace' 0 is a single point.
    -- Since m*(E) = 0 and m*(univ) = 1 for nonempty sets in d=0, E must be empty.
    -- Use U = E = ∅, which is open, E ⊆ U, and U \ E = ∅ has measure 0.
    subst hd
    -- In d=0: m*(E) = if E.Nonempty then 1 else 0
    -- hE : IsNull E is an abbrev for Lebesgue_outer_measure E = 0
    have hE' : Lebesgue_outer_measure E = 0 := hE
    rw [Lebesgue_outer_measure_of_dim_zero] at hE'
    simp only [ite_eq_right_iff, one_ne_zero] at hE'
    -- hE' : E.Nonempty → False, i.e., E = ∅
    have hE_empty : E = ∅ := Set.not_nonempty_iff_eq_empty.mp hE'
    use ∅
    refine ⟨isOpen_empty, ?_, ?_⟩
    · rw [hE_empty]
    · simp only [Set.empty_diff]
      rw [Lebesgue_outer_measure.of_empty]
      exact le_of_lt hε
  -- Now d > 0
  push_neg at hd
  have hd_pos : 0 < d := Nat.pos_of_ne_zero hd
  -- m*(E) = 0 implies m*(E) ≠ ⊤
  have h_finite : Lebesgue_outer_measure E ≠ ⊤ := by rw [hE]; exact EReal.zero_ne_top
  -- Convert EReal ε to a real number
  -- Since ε > 0, get a real ε' with 0 < ε' and ε' ≤ ε
  obtain ⟨ε', hε'_pos, hε'_le⟩ : ∃ ε' : ℝ, 0 < ε' ∧ (ε' : EReal) ≤ ε := by
    cases ε with
    | bot => exact absurd hε (not_lt.mpr bot_le)
    | top => exact ⟨1, one_pos, le_top⟩
    | coe r =>
      have hr : 0 < r := EReal.coe_pos.mp hε
      exact ⟨r, hr, le_refl _⟩
  -- Get an ε'/2-close box cover
  have hε2_pos : 0 < ε' / 2 := by linarith
  obtain ⟨S, hS_cover, hS_vol⟩ := Lebesgue_outer_measure.exists_cover_close hd_pos E (ε' / 2) hε2_pos h_finite
  -- hS_vol : ∑' n, (S n).volume.toEReal ≤ m*(E) + ε'/2 = 0 + ε'/2 = ε'/2
  rw [hE] at hS_vol
  simp only [zero_add] at hS_vol
  -- Inflate each box to get an open set containing it
  -- Use δₙ = ε' / 2^(n+2) so that ∑ δₙ = ε'/2
  let δ : ℕ → ℝ := fun n => ε' / 2 / 2 ^ (n + 1)
  have hδ_pos : ∀ n, 0 < δ n := fun n => by simp only [δ]; positivity
  -- Get inflated boxes using Box.inflate
  have h_inflate := fun n => Box.inflate (S n) (δ n) (hδ_pos n)
  choose U' hU'_subset hU'_open hU'_vol using h_inflate
  -- Define U as union of interiors of inflated boxes
  let U := ⋃ n, interior (U' n).toSet
  use U
  constructor
  · -- U is open (union of open sets)
    exact isOpen_iUnion (fun n => isOpen_interior)
  constructor
  · -- E ⊆ U
    calc E ⊆ ⋃ n, (S n).toSet := hS_cover
         _ ⊆ ⋃ n, interior (U' n).toSet := Set.iUnion_mono (fun n => hU'_subset n)
  · -- m*(U \ E) ≤ ε
    -- Key bounds: m*(U \ E) ≤ m*(U) ≤ ∑ |U' n|ᵥ ≤ ∑ (|S n|ᵥ + δ n) ≤ ε'/2 + ε'/2 = ε' ≤ ε
    have h1 : Lebesgue_outer_measure (U \ E) ≤ Lebesgue_outer_measure U :=
      Lebesgue_outer_measure.mono Set.diff_subset
    have h2 : Lebesgue_outer_measure U ≤ ∑' n, Lebesgue_outer_measure (interior (U' n).toSet) := by
      have : U = ⋃ n, interior (U' n).toSet := rfl
      rw [this]
      exact Lebesgue_outer_measure.union_le _
    -- Each interior has measure ≤ box volume
    have h3 : ∀ n, Lebesgue_outer_measure (interior (U' n).toSet) ≤ (U' n).volume.toEReal := by
      intro n
      calc Lebesgue_outer_measure (interior (U' n).toSet)
          ≤ Lebesgue_outer_measure (U' n).toSet := Lebesgue_outer_measure.mono interior_subset
        _ = (IsElementary.box (U' n)).measure.toEReal := by
            rw [Lebesgue_outer_measure.elementary _ (IsElementary.box _)]
        _ = (U' n).volume.toEReal := by rw [IsElementary.measure_of_box]
    -- Each inflated box volume ≤ original + δ
    have h4 : ∀ n, (U' n).volume.toEReal ≤ ((S n).volume + δ n).toEReal := by
      intro n
      exact EReal.coe_le_coe_iff.mpr (hU'_vol n)
    -- The sum splits: ∑ (|S n|ᵥ + δ n) = ∑ |S n|ᵥ + ∑ δ n ≤ ε'/2 + ε'/2 = ε' ≤ ε
    have hδ_sum : ∑' n, (δ n : ℝ) = ε' / 2 := by
      simp only [δ, div_div]
      have h := tsum_geometric_two' (ε' / 2)
      convert h using 1
      congr 1
      ext n
      ring_nf
    -- Combine the bounds to show m*(U \ E) ≤ ε' ≤ ε
    -- Strategy:
    -- m*(U\E) ≤ m*(U) ≤ ∑ m*(interior U'_n) ≤ ∑ vol(U'_n) ≤ ∑ (vol(S_n) + δ_n)
    --         ≤ ∑ vol(S_n) + ∑ δ_n ≤ ε'/2 + ε'/2 = ε' ≤ ε
    -- The key steps use h1, h2, h3, h4, hS_vol, hδ_sum, hε'_le
    have h_sum_le : ∑' n, Lebesgue_outer_measure (interior (U' n).toSet) ≤ ε' := by
      -- Each interior measure ≤ vol(U' n) ≤ vol(S n) + δ n
      -- Sum: ∑ vol(S n) ≤ ε'/2, ∑ δ n = ε'/2, so total ≤ ε'
      -- First show δ is summable (geometric series)
      have hδ_summable : Summable δ := by
        simp only [δ, div_div]
        exact (summable_geometric_two' (ε' / 2)).congr (fun n => by ring_nf)
      -- Show volumes are summable (from the bound hS_vol)
      have hvol_nonneg : ∀ n, 0 ≤ (S n).volume := fun n => Box.volume_nonneg _
      have hvol_sum : Summable (fun n => (S n).volume) := by
        -- Key: use that the partial sums in EReal are bounded
        have h_partial_bound : ∀ t : Finset ℕ, (∑ n ∈ t, (S n).volume : EReal) ≤ ε' / 2 := by
          intro t
          calc (∑ n ∈ t, (S n).volume : EReal)
              ≤ ∑' n, ((S n).volume : EReal) := EReal.finset_sum_le_tsum hvol_nonneg t
            _ ≤ ε' / 2 := hS_vol
        -- In ℝ: partial sums bounded implies summable for nonneg sequences
        have h_partial_real : ∀ t : Finset ℕ, ∑ n ∈ t, (S n).volume ≤ ε' / 2 := by
          intro t
          have h := h_partial_bound t
          have h_coe : (∑ n ∈ t, (S n).volume : EReal) = ↑(∑ n ∈ t, (S n).volume) :=
            (EReal.coe_finset_sum (fun n _ => hvol_nonneg n)).symm
          rw [h_coe] at h; exact EReal.coe_le_coe_iff.mp h
        exact summable_of_sum_le hvol_nonneg h_partial_real
      have hsum_combined : Summable (fun n => (S n).volume + δ n) := hvol_sum.add hδ_summable
      -- Use transitivity through ε' bound:
      -- ∑ m*(interior U'_n) ≤ ∑ vol(U'_n) ≤ ∑ (vol S_n + δ_n) = ∑ vol S_n + ∑ δ_n ≤ ε'/2 + ε'/2 = ε'
      have h_interior_bound : ∀ n, Lebesgue_outer_measure (interior (U' n).toSet) ≤ ((S n).volume + δ n : EReal) := by
        intro n
        calc Lebesgue_outer_measure (interior (U' n).toSet)
            ≤ (U' n).volume.toEReal := h3 n
          _ ≤ ((S n).volume + δ n).toEReal := h4 n
          _ = ((S n).volume + δ n : EReal) := rfl
      -- Sum bound: use EReal.tsum_le_coe_tsum_of_forall_le
      have hg_nonneg : ∀ n, 0 ≤ (S n).volume + δ n := fun n => by linarith [hvol_nonneg n, hδ_pos n]
      have h_tsum_bound : ∑' n, Lebesgue_outer_measure (interior (U' n).toSet) ≤ ∑' n, ((S n).volume + δ n : EReal) :=
        EReal.tsum_le_coe_tsum_of_forall_le (fun n => Lebesgue_outer_measure.nonneg _)
          hg_nonneg hsum_combined h_interior_bound
      -- Key equality: tsums in EReal with coercion can be rewritten
      have h_tsum_eq : ∑' n, (↑(S n).volume + ↑(δ n) : EReal) = ↑(∑' n, ((S n).volume + δ n)) := by
        have h1 : ∑' n, (↑(S n).volume + ↑(δ n) : EReal) = ∑' n, ↑((S n).volume + δ n) := by
          apply tsum_congr
          intro n; exact (EReal.coe_add _ _).symm
        have h2 : ∑' n, (↑((S n).volume + δ n) : EReal) = ↑(∑' n, ((S n).volume + δ n)) :=
          (EReal.coe_tsum_of_nonneg hg_nonneg hsum_combined).symm
        rw [h1, h2]
      calc ∑' n, Lebesgue_outer_measure (interior (U' n).toSet)
          ≤ ∑' n, (↑(S n).volume + ↑(δ n) : EReal) := h_tsum_bound
        _ = ↑(∑' n, ((S n).volume + δ n)) := h_tsum_eq
        _ = ↑(∑' n, (S n).volume + ∑' n, δ n) := by rw [hvol_sum.tsum_add hδ_summable]
        _ = ↑(∑' n, (S n).volume) + ↑(∑' n, δ n) := by rw [EReal.coe_add]
        _ ≤ ↑(ε' / 2) + ↑(ε' / 2) := by
            apply add_le_add
            · have := EReal.coe_tsum_of_nonneg hvol_nonneg hvol_sum
              rw [this]; exact hS_vol
            · rw [hδ_sum]
        _ = ε' := by rw [← EReal.coe_add]; norm_cast; ring
    calc Lebesgue_outer_measure (U \ E)
        ≤ Lebesgue_outer_measure U := h1
      _ ≤ ∑' n, Lebesgue_outer_measure (interior (U' n).toSet) := h2
      _ ≤ ε' := h_sum_le
      _ ≤ ε := hε'_le

/-- A subset of a null set is null. -/
lemma IsNull.subset {d:ℕ} {E F : Set (EuclideanSpace' d)} (hE : IsNull E) (hFE : F ⊆ E) : IsNull F := by
  have := Lebesgue_outer_measure.mono hFE
  rw [hE] at this
  exact le_antisymm this (Lebesgue_outer_measure.nonneg F)

/-- Lemma 1.2.13(iv) (Empty set is measurable). -/
theorem LebesgueMeasurable.empty {d:ℕ} : LebesgueMeasurable (∅: Set (EuclideanSpace' d)) :=
-- use (i) directly
  IsOpen.measurable isOpen_empty

theorem LebesgueMeasurable.empty' {d:ℕ} : LebesgueMeasurable (∅: Set (EuclideanSpace' d)) := by
-- use definition of Lebesgue measurability
  intro ε hε
  use ∅
  constructor
  · exact isOpen_empty
  constructor
  · exact Set.empty_subset ∅
  · have h_empty : ∅ \ ∅ = (∅ : Set (EuclideanSpace' d)) := Set.diff_self
    rw [h_empty]
    rw [Lebesgue_outer_measure.of_empty d]
    exact le_of_lt hε

/-- Lemma 1.2.13(vi) (Countable union of measurable sets is measurable). -/
theorem LebesgueMeasurable.countable_union {d:ℕ} {E: ℕ → Set (EuclideanSpace' d)} (hE: ∀ n, LebesgueMeasurable (E n)) : LebesgueMeasurable (⋃ n, E n) := by
  -- Use the ε/2^n trick: let ε > 0 be arbitrary
  intro ε hε
  -- Convert EReal ε to a real number ε' with 0 < ε' ≤ ε
  obtain ⟨ε', hε'_pos, hε'_le⟩ : ∃ ε' : ℝ, 0 < ε' ∧ (ε' : EReal) ≤ ε := by
    cases ε with
    | bot => exact absurd hε (not_lt.mpr bot_le)
    | top => exact ⟨1, one_pos, le_top⟩
    | coe r =>
      have hr : 0 < r := EReal.coe_pos.mp hε
      exact ⟨r, hr, le_refl _⟩
  -- For each n, get U_n open with E_n ⊆ U_n and m*(U_n \ E_n) ≤ ε'/2^(n+1)
  have hδ_pos : ∀ n, (0:EReal) < ε' / 2^(n+1) := fun n => by
    apply EReal.div_pos (EReal.coe_pos.mpr hε'_pos)
    · exact EReal.coe_pow 2 (n+1) ▸ EReal.coe_pos.mpr (by positivity)
    · exact EReal.coe_pow 2 (n+1) ▸ EReal.coe_ne_top ((2:ℝ)^(n+1))
  -- Apply measurability of each E_n with ε'/2^(n+1)
  choose U hU_open hE_sub hU_diff using fun n => hE n (ε' / 2^(n+1)) (hδ_pos n)
  -- The open set is ⋃ n, U n
  use ⋃ n, U n
  constructor
  · -- ⋃ n, U n is open (union of open sets)
    exact isOpen_iUnion hU_open
  constructor
  · -- ⋃ n, E n ⊆ ⋃ n, U n
    apply Set.iUnion_mono
    intro n; exact hE_sub n
  · -- m*((⋃ n, U n) \ (⋃ n, E n)) ≤ ε
    -- Key: (⋃ U_n) \ (⋃ E_n) ⊆ ⋃ (U_n \ E_n)
    have h_diff_subset : (⋃ n, U n) \ (⋃ n, E n) ⊆ ⋃ n, (U n \ E n) := by
      intro x ⟨hx_in_U, hx_not_in_E⟩
      simp only [Set.mem_iUnion] at hx_in_U hx_not_in_E ⊢
      obtain ⟨k, hxk⟩ := hx_in_U
      use k
      constructor
      · exact hxk
      · intro hx_Ek
        exact hx_not_in_E ⟨k, hx_Ek⟩
    calc Lebesgue_outer_measure ((⋃ n, U n) \ (⋃ n, E n))
        ≤ Lebesgue_outer_measure (⋃ n, (U n \ E n)) :=
          Lebesgue_outer_measure.mono h_diff_subset
      _ ≤ ∑' n, Lebesgue_outer_measure (U n \ E n) :=
          Lebesgue_outer_measure.union_le _
      _ ≤ ∑' n, ((ε' / 2^(n+1) : ℝ) : EReal) := by
          -- Use EReal.tsum_le_coe_tsum_of_forall_le
          have h_nonneg : ∀ n, 0 ≤ ε' / 2^(n+1) := fun n => by positivity
          have h_summable : Summable (fun n => ε' / 2^(n+1)) :=
            (summable_geometric_two' ε').congr (fun n => by ring)
          have h_f_nonneg : ∀ n, 0 ≤ Lebesgue_outer_measure (U n \ E n) :=
            fun n => Lebesgue_outer_measure.nonneg _
          have h_le_coe : ∀ n, Lebesgue_outer_measure (U n \ E n) ≤ ((ε' / 2^(n+1) : ℝ) : EReal) := by
            intro n
            calc Lebesgue_outer_measure (U n \ E n)
                ≤ (↑ε' : EReal) / 2^(n+1) := hU_diff n
              _ = ↑(ε' / 2^(n+1)) := by
                  rw [EReal.coe_div]
                  congr 1
                  exact Eq.symm (EReal.coe_pow 2 (n + 1))
          exact EReal.tsum_le_coe_tsum_of_forall_le h_f_nonneg h_nonneg h_summable h_le_coe
      _ = ε' := by
          -- ∑ n, ε'/2^(n+1) = ε' (geometric series)
          have h_sum : ∑' n : ℕ, (ε' : ℝ) / 2^(n+1) = ε' := tsum_geometric_eps ε' hε'_pos
          have h_summable : Summable (fun n => ε' / 2^(n+1)) :=
            (summable_geometric_two' ε').congr (fun n => by ring)
          have h_nonneg : ∀ n, 0 ≤ ε' / 2^(n+1) := fun n => by positivity
          rw [← EReal.coe_tsum_of_nonneg h_nonneg h_summable, h_sum]
      _ ≤ ε := hε'_le

/-- Lemma 1.2.13(v) (Complement of a measurable set is measurable). -/
theorem LebesgueMeasurable.complement {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) : LebesgueMeasurable (Eᶜ) := by
  -- Strategy: For each n, find open Uₙ ⊇ E with m*(Uₙ \ E) ≤ 1/(n+1).
  -- Let Fₙ = Uₙᶜ (closed). Then Eᶜ ⊇ Fₙ and m*(Eᶜ \ Fₙ) = m*(Uₙ \ E) ≤ 1/(n+1).
  -- Let F = ⋃ Fₙ. Then m*(Eᶜ \ F) = 0 and Eᶜ = F ∪ (Eᶜ \ F).
  -- F is measurable (countable union of closed sets), Eᶜ \ F is null (hence measurable).

  -- Step 1: For each n, get open Uₙ with E ⊆ Uₙ and m*(Uₙ \ E) ≤ 1/(n+1)
  have h_eps_pos : ∀ n : ℕ, (0 : EReal) < 1 / (n + 1 : ℕ) := fun n => by
    have h1 : (0 : EReal) < 1 := EReal.coe_pos.mpr (by norm_num : (0 : ℝ) < 1)
    have h2 : (0 : EReal) < (n + 1 : ℕ) := by
      simp only [Nat.cast_add, Nat.cast_one]
      exact EReal.coe_pos.mpr (by linarith : (0 : ℝ) < n + 1)
    exact EReal.div_pos h1 h2 (EReal.coe_ne_top _)
  choose U hU_open hE_sub_U hU_diff using fun n => hE (1 / (n + 1 : ℕ)) (h_eps_pos n)

  -- Step 2: Define Fₙ = Uₙᶜ (closed sets)
  let F_n : ℕ → Set (EuclideanSpace' d) := fun n => (U n)ᶜ
  have hF_closed : ∀ n, IsClosed (F_n n) := fun n => (hU_open n).isClosed_compl

  -- Key set-theoretic fact: Eᶜ \ Fₙ = Uₙ \ E
  have h_diff_eq : ∀ n, Eᶜ \ F_n n = U n \ E := fun n => by
    simp only [F_n, Set.diff_compl]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_diff]
    tauto

  -- Step 3: Define F = ⋃ Fₙ (F-sigma set)
  let F := ⋃ n, F_n n

  -- Step 4: Show m*(Eᶜ \ F) = 0
  have h_diff_F : ∀ n, Eᶜ \ F ⊆ U n \ E := fun n => by
    have h1 : Eᶜ \ F ⊆ Eᶜ \ F_n n := Set.diff_subset_diff_right (Set.subset_iUnion F_n n)
    rw [h_diff_eq n] at h1
    exact h1

  have h_measure_bound : ∀ n, Lebesgue_outer_measure (Eᶜ \ F) ≤ 1 / (n + 1 : ℕ) := fun n =>
    calc Lebesgue_outer_measure (Eᶜ \ F)
        ≤ Lebesgue_outer_measure (U n \ E) := Lebesgue_outer_measure.mono (h_diff_F n)
      _ ≤ 1 / (n + 1 : ℕ) := hU_diff n

  have h_null : IsNull (Eᶜ \ F) := by
    apply le_antisymm
    · -- Show m*(Eᶜ \ F) ≤ 0 by showing it's ≤ 1/(n+1) for all n
      by_contra h_ne
      push_neg at h_ne
      have h_pos : 0 < Lebesgue_outer_measure (Eᶜ \ F) := h_ne
      -- Get a real ε with 0 < ε ≤ m*(Eᶜ \ F)
      obtain ⟨ε, hε_pos, hε_le⟩ : ∃ ε : ℝ, 0 < ε ∧ (ε : EReal) ≤ Lebesgue_outer_measure (Eᶜ \ F) := by
        cases hm : Lebesgue_outer_measure (Eᶜ \ F) with
        | bot => rw [hm] at h_pos; exact absurd h_pos (not_lt.mpr bot_le)
        | top => exact ⟨1, one_pos, le_top⟩
        | coe r =>
          rw [hm] at h_pos
          have hr : 0 < r := EReal.coe_pos.mp h_pos
          exact ⟨r, hr, le_refl _⟩
      -- Find N with 1/(N+1) < ε
      obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
      have hNp1_pos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
      have hN1 : 1 / ((N : ℝ) + 1) < ε := by
        have h1 : 1 / ε < (N : ℝ) + 1 := lt_of_lt_of_le hN (by norm_cast; exact Nat.le_succ N)
        rw [one_div_lt hNp1_pos hε_pos]; exact h1
      -- h_measure_bound N says m*(Eᶜ \ F) ≤ 1/(N+1)
      have h_bound : Lebesgue_outer_measure (Eᶜ \ F) ≤ 1 / (N + 1 : ℕ) := h_measure_bound N
      have h_eq : (1 : EReal) / (N + 1 : ℕ) = ↑(1 / ((N : ℝ) + 1)) := by
        rw [EReal.coe_div, EReal.coe_one]; norm_cast
      rw [h_eq] at h_bound
      -- ε ≤ m*(Eᶜ \ F) ≤ 1/(N+1) < ε, contradiction
      have h_final : (ε : EReal) < (ε : EReal) := calc
        (ε : EReal) ≤ Lebesgue_outer_measure (Eᶜ \ F) := hε_le
        _ ≤ ↑(1 / ((N : ℝ) + 1)) := h_bound
        _ < ε := EReal.coe_lt_coe_iff.mpr hN1
      exact lt_irrefl (ε : EReal) h_final
    · exact Lebesgue_outer_measure.nonneg _

  -- Step 5: Show Eᶜ = F ∪ (Eᶜ \ F)
  have h_decomp : Eᶜ = F ∪ (Eᶜ \ F) := by
    ext x
    simp only [Set.mem_union, Set.mem_diff]
    constructor
    · intro hx
      by_cases hxF : x ∈ F
      · left; exact hxF
      · right; exact ⟨hx, hxF⟩
    · intro h
      cases h with
      | inl hxF =>
        simp only [F, Set.mem_iUnion] at hxF
        obtain ⟨n, hxFn⟩ := hxF
        simp only [F_n, Set.mem_compl_iff] at hxFn
        have hxE : x ∉ E := fun h => hxFn (hE_sub_U n h)
        exact hxE
      | inr hxEcF => exact hxEcF.1

  -- Step 6: Apply measurability results
  rw [h_decomp]
  have hF_meas : LebesgueMeasurable F := by
    have : F = ⋃ n, F_n n := rfl
    rw [this]
    exact LebesgueMeasurable.countable_union (fun n => (hF_closed n).measurable)
  have hN_meas : LebesgueMeasurable (Eᶜ \ F) := h_null.measurable
  -- Union of two measurable sets
  let S : ℕ → Set (EuclideanSpace' d) := fun n => if n = 0 then F else if n = 1 then Eᶜ \ F else ∅
  have hS_meas : ∀ n, LebesgueMeasurable (S n) := fun n => by
    simp only [S]
    split_ifs with h0 h1
    · exact hF_meas
    · exact hN_meas
    · exact LebesgueMeasurable.empty
  have h_eq : F ∪ (Eᶜ \ F) = ⋃ n, S n := by
    ext x
    simp only [Set.mem_union, Set.mem_iUnion, S]
    constructor
    · intro h
      cases h with
      | inl hF => exact ⟨0, by simp [hF]⟩
      | inr hN => exact ⟨1, by simp [hN]⟩
    · intro ⟨n, hn⟩
      split_ifs at hn with h0 h1
      · left; exact hn
      · right; exact hn
      · exact absurd hn (Set.notMem_empty x)
  rw [h_eq]
  exact LebesgueMeasurable.countable_union hS_meas

theorem LebesgueMeasurable.finite_union {d n:ℕ} {E: Fin n → Set (EuclideanSpace' d)} (hE: ∀ i, LebesgueMeasurable (E i)) : LebesgueMeasurable (⋃ i, E i) := by
  -- Extend E to ℕ-indexed family by padding with empty sets
  let E' : ℕ → Set (EuclideanSpace' d) := fun k => if h : k < n then E ⟨k, h⟩ else ∅
  have hE'_meas : ∀ k, LebesgueMeasurable (E' k) := fun k => by
    simp only [E']
    split_ifs with hk
    · exact hE ⟨k, hk⟩
    · exact LebesgueMeasurable.empty
  -- Show ⋃ i : Fin n, E i = ⋃ k : ℕ, E' k
  have h_eq : (⋃ i : Fin n, E i) = ⋃ k : ℕ, E' k := by
    ext x
    simp only [Set.mem_iUnion, E']
    constructor
    · intro ⟨i, hx⟩
      use i.val
      simp only [i.isLt, ↓reduceDIte, hx]
    · intro ⟨k, hx⟩
      split_ifs at hx with hk
      · exact ⟨⟨k, hk⟩, hx⟩
      · exact absurd hx (Set.notMem_empty x)
  rw [h_eq]
  exact LebesgueMeasurable.countable_union hE'_meas

theorem LebesgueMeasurable.union {d :ℕ} {E F: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) (hF: LebesgueMeasurable F) : LebesgueMeasurable (E ∪ F) := by
  -- Express E ∪ F as union over Fin 2
  let S : Fin 2 → Set (EuclideanSpace' d) := ![E, F]
  have hS : ∀ i, LebesgueMeasurable (S i) := fun i => by fin_cases i <;> simp [S, hE, hF]
  have h_eq : E ∪ F = ⋃ i : Fin 2, S i := by
    ext x
    simp only [Set.mem_union, Set.mem_iUnion, S]
    constructor
    · rintro (hx | hx)
      · exact ⟨0, by simp [hx]⟩
      · exact ⟨1, by simp [hx]⟩
    · rintro ⟨i, hi⟩
      fin_cases i <;> simp_all
  rw [h_eq]
  exact LebesgueMeasurable.finite_union hS

/-- Lemma 1.2.13(vii) (Countable intersection of measurable sets is measurable). -/
theorem LebesgueMeasurable.countable_inter {d:ℕ} {E: ℕ → Set (EuclideanSpace' d)} (hE: ∀ n, LebesgueMeasurable (E n)) : LebesgueMeasurable (⋂ n, E n) := by
  -- By de Morgan: ⋂ Eₙ = (⋃ Eₙᶜ)ᶜ
  have h_eq : (⋂ n, E n) = (⋃ n, (E n)ᶜ)ᶜ := by
    rw [Set.compl_iUnion]
    simp only [compl_compl]
  rw [h_eq]
  -- Each Eₙᶜ is measurable by (v)
  have hE_compl : ∀ n, LebesgueMeasurable ((E n)ᶜ) := fun n => (hE n).complement
  -- ⋃ Eₙᶜ is measurable by (vi)
  have h_union : LebesgueMeasurable (⋃ n, (E n)ᶜ) := LebesgueMeasurable.countable_union hE_compl
  -- (⋃ Eₙᶜ)ᶜ is measurable by (v) again
  exact h_union.complement

theorem LebesgueMeasurable.finite_inter {d n:ℕ} {E: Fin n → Set (EuclideanSpace' d)} (hE: ∀ i, LebesgueMeasurable (E i)) : LebesgueMeasurable (⋂ i, E i) := by
  -- Extend Fin n indexed family to ℕ indexed family with univ for k ≥ n
  let E' : ℕ → Set (EuclideanSpace' d) := fun k => if h : k < n then E ⟨k, h⟩ else Set.univ
  have hE'_meas : ∀ k, LebesgueMeasurable (E' k) := fun k => by
    simp only [E']
    split_ifs with hk
    · exact hE ⟨k, hk⟩
    · -- univ = ∅ᶜ, so measurable by complement of empty
      rw [← Set.compl_empty]
      exact LebesgueMeasurable.empty.complement
  have h_eq : (⋂ i : Fin n, E i) = ⋂ k : ℕ, E' k := by
    ext x
    simp only [Set.mem_iInter, E']
    constructor
    · intro hx k
      split_ifs with hk
      · exact hx ⟨k, hk⟩
      · exact Set.mem_univ x
    · intro hx ⟨i, hi⟩
      have := hx i
      simp only [hi, dite_true] at this
      exact this
  rw [h_eq]
  exact LebesgueMeasurable.countable_inter hE'_meas

theorem LebesgueMeasurable.inter {d :ℕ} {E F: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) (hF: LebesgueMeasurable F) : LebesgueMeasurable (E ∩ F) := by
  -- Express E ∩ F as intersection over Fin 2
  let S : Fin 2 → Set (EuclideanSpace' d) := ![E, F]
  have hS : ∀ i, LebesgueMeasurable (S i) := fun i => by fin_cases i <;> simp [S, hE, hF]
  have h_eq : E ∩ F = ⋂ i : Fin 2, S i := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_iInter, S]
    constructor
    · intro ⟨hxE, hxF⟩ i
      fin_cases i <;> simp_all
    · intro hx
      exact ⟨hx 0, hx 1⟩
  rw [h_eq]
  exact LebesgueMeasurable.finite_inter hS

/-- Finite intersection indexed by a {name}`Finset` is Lebesgue measurable. -/
lemma LebesgueMeasurable.finset_inter {d : ℕ} {α : Type*} [DecidableEq α]
    {E : α → Set (EuclideanSpace' d)} {S : Finset α}
    (hE : ∀ i ∈ S, LebesgueMeasurable (E i)) :
    LebesgueMeasurable (⋂ i ∈ S, E i) := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.notMem_empty, Set.iInter_of_empty, Set.iInter_univ]
    rw [← Set.compl_empty]
    exact LebesgueMeasurable.empty.complement
  | insert a S' ha ih =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at hE
    have hE_a := hE.1
    have hE_rest := fun i hi => hE.2 i hi
    rw [show (⋂ i ∈ insert a S', E i) = E a ∩ (⋂ i ∈ S', E i) by
      ext x
      simp only [Set.mem_iInter, Set.mem_inter_iff]
      constructor
      · intro h; exact ⟨h a (Finset.mem_insert_self a S'), fun i hi => h i (Finset.mem_insert_of_mem hi)⟩
      · intro ⟨ha', h⟩ i hi
        rcases Finset.mem_insert.mp hi with rfl | hi'
        · exact ha'
        · exact h i hi']
    exact LebesgueMeasurable.inter hE_a (ih hE_rest)

/-- Finite union indexed by a {name}`Finset` is Lebesgue measurable. -/
lemma LebesgueMeasurable.finset_union {d : ℕ} {α : Type*} [DecidableEq α]
    {E : α → Set (EuclideanSpace' d)} {S : Finset α}
    (hE : ∀ i ∈ S, LebesgueMeasurable (E i)) :
    LebesgueMeasurable (⋃ i ∈ S, E i) := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty]
    exact LebesgueMeasurable.empty
  | insert a S' ha ih =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at hE
    have hE_a := hE.1
    have hE_rest := fun i hi => hE.2 i hi
    rw [show (⋃ i ∈ insert a S', E i) = E a ∪ (⋃ i ∈ S', E i) by
      ext x
      simp only [Set.mem_iUnion, Set.mem_union]
      constructor
      · intro ⟨i, hi, hx⟩
        rcases Finset.mem_insert.mp hi with rfl | hi'
        · left; exact hx
        · right; exact ⟨i, hi', hx⟩
      · intro h
        cases h with
        | inl h => exact ⟨a, Finset.mem_insert_self a S', h⟩
        | inr h => obtain ⟨i, hi, hx⟩ := h; exact ⟨i, Finset.mem_insert_of_mem hi, hx⟩]
    exact LebesgueMeasurable.union hE_a (ih hE_rest)

/-- If A = B outside a null set N (i.e., A ∩ Nᶜ = B ∩ Nᶜ), then A is measurable if B is. -/
lemma LebesgueMeasurable.of_ae_eq {d : ℕ} {A B N : Set (EuclideanSpace' d)}
    (hB : LebesgueMeasurable B) (hN : IsNull N) (h_eq : A ∩ Nᶜ = B ∩ Nᶜ) :
    LebesgueMeasurable A := by
  -- A = (B ∩ Nᶜ) ∪ (A ∩ N)
  have h_decomp : A = (B ∩ Nᶜ) ∪ (A ∩ N) := by
    ext x
    constructor
    · intro hx
      by_cases hxN : x ∈ N
      · right; exact ⟨hx, hxN⟩
      · left; rw [← h_eq]; exact ⟨hx, hxN⟩
    · intro hx
      cases hx with
      | inl h => rw [← h_eq] at h; exact h.1
      | inr h => exact h.1
  rw [h_decomp]
  apply LebesgueMeasurable.union
  · exact LebesgueMeasurable.inter hB (IsNull.measurable hN).complement
  · exact IsNull.measurable (IsNull.subset hN Set.inter_subset_right)

/-- Closed balls are Lebesgue measurable. -/
lemma LebesgueMeasurable.closedBall {d : ℕ} (c : EuclideanSpace' d) (r : ℝ) :
    LebesgueMeasurable (Metric.closedBall c r) :=
  Metric.isClosed_closedBall.measurable

/-- Exercise 1.2.7 (Criteria for measurability). -/
theorem LebesgueMeasurable.TFAE {d:ℕ} (E: Set (EuclideanSpace' d)) :
    [
      LebesgueMeasurable E,
      (∀ ε > 0, ∃ U : Set (EuclideanSpace' d), IsOpen U ∧ E ⊆ U ∧ Lebesgue_outer_measure (U \ E) ≤ ε),
      (∀ ε > 0, ∃ U : Set (EuclideanSpace' d), IsOpen U ∧ Lebesgue_outer_measure (symmDiff U E) ≤ ε),
      (∀ ε > 0, ∃ F: Set (EuclideanSpace' d), IsClosed F ∧ F ⊆ E ∧ Lebesgue_outer_measure (E \ F) ≤ ε),
      (∀ ε > 0, ∃ F: Set (EuclideanSpace' d), IsClosed F ∧ Lebesgue_outer_measure (symmDiff F E) ≤ ε),
      (∀ ε > 0, ∃ E': Set (EuclideanSpace' d), LebesgueMeasurable E' ∧ Lebesgue_outer_measure (symmDiff E' E) ≤ ε)
    ].TFAE
  := by
  apply List.tfae_of_cycle
  · -- h_chain: IsChain (· → ·) [0, 1, 2, 3, 4, 5]
    rw [List.isChain_cons_cons]
    refine ⟨?_, ?_⟩
    · -- 0 → 1: definitional
      intro h0 ε hε
      exact h0 ε hε
    · -- IsChain for [1, 2, 3, 4, 5]
      rw [List.isChain_cons_cons]
      refine ⟨?_, ?_⟩
      · -- 1 → 2: symmDiff = U \ E when E ⊆ U
        intro h1 ε hε
        rcases h1 ε hε with ⟨U, hU_open, hE_sub_U, hU_diff⟩
        refine ⟨U, hU_open, ?_⟩
        have h_symm_eq : symmDiff U E = U \ E := by
          rw [symmDiff_def]
          simp [Set.diff_eq_empty.mpr hE_sub_U]
        rw [h_symm_eq]
        exact hU_diff
      · -- IsChain for [2, 3, 4, 5]
        rw [List.isChain_cons_cons]
        refine ⟨?_, ?_⟩
        · -- 2 → 3: via 2 → 1 → 0 → 3
          intro h2
          -- First, prove 2 → 1
          have h1 : ∀ ε > 0, ∃ U : Set (EuclideanSpace' d), IsOpen U ∧ E ⊆ U ∧
              Lebesgue_outer_measure (U \ E) ≤ ε := by
            intro ε hε
            obtain ⟨ε', hε'_pos, hε'_le⟩ : ∃ ε' : ℝ, 0 < ε' ∧ (ε' : EReal) ≤ ε := by
              cases ε with
              | bot => exact absurd hε (not_lt.mpr bot_le)
              | top => exact ⟨1, one_pos, le_top⟩
              | coe r => exact ⟨r, EReal.coe_pos.mp hε, le_refl _⟩
            have h_pos : (0 : EReal) < (ε' / 3 : ℝ) :=
              EReal.coe_pos.mpr (by linarith)
            rcases h2 ((ε' / 3 : ℝ) : EReal) h_pos with ⟨U, hU_open, h_symm_le⟩
            have h_UE_sub : U \ E ⊆ symmDiff U E := by
              rw [symmDiff_def]
              simp
            have h_EU_sub : E \ U ⊆ symmDiff U E := by
              rw [symmDiff_def]
              simp
            have h_UE_bound : Lebesgue_outer_measure (U \ E) ≤ (ε' / 3 : ℝ) :=
              calc
                Lebesgue_outer_measure (U \ E) ≤ Lebesgue_outer_measure (symmDiff U E) :=
                  Lebesgue_outer_measure.mono h_UE_sub
                _ ≤ (ε' / 3 : ℝ) := h_symm_le
            have h_EU_bound : Lebesgue_outer_measure (E \ U) ≤ (ε' / 3 : ℝ) :=
              calc
                Lebesgue_outer_measure (E \ U) ≤ Lebesgue_outer_measure (symmDiff U E) :=
                  Lebesgue_outer_measure.mono h_EU_sub
                _ ≤ (ε' / 3 : ℝ) := h_symm_le
            rcases Lebesgue_outer_measure.exists_open_superset_measure_le (E \ U) ((ε' / 3 : ℝ) : EReal) h_pos
              with ⟨W, hW_open, h_EU_sub_W, hW_meas⟩
            have hW_bound : Lebesgue_outer_measure W ≤ (2 * ε' / 3 : ℝ) := by
              calc
                Lebesgue_outer_measure W ≤ Lebesgue_outer_measure (E \ U) + (ε' / 3 : ℝ) := hW_meas
                _ ≤ (ε' / 3 : ℝ) + (ε' / 3 : ℝ) := by
                  -- h_EU_bound: Lebesgue_outer_measure (E \ U) ≤ (ε' / 3 : ℝ)
                  -- Need: Lebesgue_outer_measure (E \ U) + (ε' / 3 : ℝ) ≤ (ε' / 3 : ℝ) + (ε' / 3 : ℝ)
                  simpa [add_comm] using add_le_add h_EU_bound (le_refl ((ε' / 3 : ℝ) : EReal))
                _ = ((2 * ε' / 3 : ℝ) : EReal) := by
                  simpa using congrArg (fun x : ℝ => (x : EReal)) (show (ε' / 3 : ℝ) + (ε' / 3 : ℝ) = (2 * ε' / 3 : ℝ) by ring)
            let V := U ∪ W
            have hV_open : IsOpen V := IsOpen.union hU_open hW_open
            have hE_sub_V : E ⊆ V := by
              intro x hx
              by_cases hxU : x ∈ U
              · exact Set.mem_union_left W hxU
              · have hx_EU : x ∈ E \ U := ⟨hx, hxU⟩
                exact Set.mem_union_right U (h_EU_sub_W hx_EU)
            have hV_bound : Lebesgue_outer_measure (V \ E) ≤ (ε' : ℝ) := by
              have h_sub : V \ E ⊆ (U \ E) ∪ W := by
                intro x hx
                rcases hx with ⟨hxV, hxE⟩
                rcases hxV with (hxU | hxW)
                · left; exact ⟨hxU, hxE⟩
                · right; exact hxW
              have h_add : Lebesgue_outer_measure ((U \ E) ∪ W) ≤
                  Lebesgue_outer_measure (U \ E) + Lebesgue_outer_measure W := by
                let S : Fin 2 → Set (EuclideanSpace' d) := ![U \ E, W]
                have h_union : ⋃ i : Fin 2, S i = (U \ E) ∪ W := by
                  ext x; simp [S]
                calc
                  Lebesgue_outer_measure ((U \ E) ∪ W) = Lebesgue_outer_measure (⋃ i : Fin 2, S i) := by rw [h_union]
                  _ ≤ ∑ i : Fin 2, Lebesgue_outer_measure (S i) := Lebesgue_outer_measure.finite_union_le S
                  _ = Lebesgue_outer_measure (U \ E) + Lebesgue_outer_measure W := by simp [S]
              calc
                Lebesgue_outer_measure (V \ E) ≤ Lebesgue_outer_measure ((U \ E) ∪ W) :=
                  Lebesgue_outer_measure.mono h_sub
                _ ≤ Lebesgue_outer_measure (U \ E) + Lebesgue_outer_measure W := h_add
                _ ≤ (ε' / 3 : ℝ) + (2 * ε' / 3 : ℝ) := add_le_add h_UE_bound hW_bound
                _ = ((ε' : ℝ) : EReal) := by
                  simpa using congrArg (fun x : ℝ => (x : EReal)) (show (ε' / 3 : ℝ) + (2 * ε' / 3 : ℝ) = (ε' : ℝ) by ring)
            refine ⟨V, hV_open, hE_sub_V, ?_⟩
            calc
              Lebesgue_outer_measure (V \ E) ≤ (ε' : ℝ) := hV_bound
              _ ≤ ε := hε'_le
          -- Now from h1, E is Lebesgue measurable (definitionally)
          have h0 : LebesgueMeasurable E := h1
          -- From h0 (measurable), get (3) by complement argument
          intro ε hε
          obtain ⟨ε', hε'_pos, hε'_le⟩ : ∃ ε' : ℝ, 0 < ε' ∧ (ε' : EReal) ≤ ε := by
            cases ε with
            | bot => exact absurd hε (not_lt.mpr bot_le)
            | top => exact ⟨1, one_pos, le_top⟩
            | coe r => exact ⟨r, EReal.coe_pos.mp hε, le_refl _⟩
          have hEc_meas : LebesgueMeasurable (Eᶜ) := h0.complement
          rcases hEc_meas ((ε' : ℝ) : EReal) (EReal.coe_pos.mpr hε'_pos) with ⟨V, hV_open, hEc_sub_V, hV_diff⟩
          refine ⟨Vᶜ, hV_open.isClosed_compl, ?_, ?_⟩
          · -- Vᶜ ⊆ E
            intro x hx
            have hx_not_V : x ∉ V := hx
            by_contra hx_not_E
            have hx_Ec : x ∈ (Eᶜ : Set (EuclideanSpace' d)) := hx_not_E
            have hx_V : x ∈ V := hEc_sub_V hx_Ec
            exact hx_not_V hx_V
          · -- m(E \ Vᶜ) ≤ ε
            have h_eq : (E \ Vᶜ : Set (EuclideanSpace' d)) = V \ (Eᶜ : Set (EuclideanSpace' d)) := by
              ext x; simp; tauto
            rw [h_eq]
            calc
              Lebesgue_outer_measure (V \ (Eᶜ : Set (EuclideanSpace' d))) ≤ (ε' : ℝ) := hV_diff
              _ ≤ ε := hε'_le
        · -- IsChain for [3, 4, 5]
          rw [List.isChain_cons_cons]
          refine ⟨?_, ?_⟩
          · -- 3 → 4: symmDiff = E \ F when F ⊆ E
            intro h3 ε hε
            rcases h3 ε hε with ⟨F, hF_closed, hF_sub_E, h_diff⟩
            refine ⟨F, hF_closed, ?_⟩
            have h_symm_eq : symmDiff F E = E \ F := by
              rw [symmDiff_def]
              simp [Set.diff_eq_empty.mpr hF_sub_E]
            rw [h_symm_eq]
            exact h_diff
          · -- IsChain for [4, 5]
            rw [List.isChain_cons_cons]
            refine ⟨?_, List.isChain_singleton _⟩
            · -- 4 → 5: closed → measurable
              intro h4 ε hε
              rcases h4 ε hε with ⟨F, hF_closed, h_symm⟩
              refine ⟨F, hF_closed.measurable, h_symm⟩
  · -- h_last: 5 → 0: via measurable E' with small symmDiff
    intro h5 ε hε
    obtain ⟨ε', hε'_pos, hε'_le⟩ : ∃ ε' : ℝ, 0 < ε' ∧ (ε' : EReal) ≤ ε := by
      cases ε with
      | bot => exact absurd hε (not_lt.mpr bot_le)
      | top => exact ⟨1, one_pos, le_top⟩
      | coe r => exact ⟨r, EReal.coe_pos.mp hε, le_refl _⟩
    set δ := ε'/4 with hδ
    have hδ_pos : (0 : ℝ) < δ := by linarith
    have hδ_pos' : (0 : EReal) < (δ : ℝ) := EReal.coe_pos.mpr hδ_pos
    rcases h5 ((δ : ℝ) : EReal) hδ_pos' with ⟨E', hE'_meas, h_symm⟩
    -- Get open U ⊇ E' with m(U \ E') ≤ δ
    rcases hE'_meas ((δ : ℝ) : EReal) hδ_pos' with ⟨U, hU_open, hE'_sub_U, hU_diff⟩
    have h_E'E_bound : Lebesgue_outer_measure (E' \ E) ≤ (δ : ℝ) := by
      have h_sub : E' \ E ⊆ symmDiff E' E := by
        rw [symmDiff_def]
        simp
      calc
        Lebesgue_outer_measure (E' \ E) ≤ Lebesgue_outer_measure (symmDiff E' E) :=
          Lebesgue_outer_measure.mono h_sub
        _ ≤ (δ : ℝ) := h_symm
    have h_EE'_bound : Lebesgue_outer_measure (E \ E') ≤ (δ : ℝ) := by
      have h_sub : E \ E' ⊆ symmDiff E' E := by
        rw [symmDiff_def]
        simp
      calc
        Lebesgue_outer_measure (E \ E') ≤ Lebesgue_outer_measure (symmDiff E' E) :=
          Lebesgue_outer_measure.mono h_sub
        _ ≤ (δ : ℝ) := h_symm
    have h_UE_bound : Lebesgue_outer_measure (U \ E) ≤ (2 * δ : ℝ) := by
      have h_sub : U \ E ⊆ (U \ E') ∪ (E' \ E) := by
        intro x hx
        have hxU : x ∈ U := hx.1
        have hx_not_E : x ∉ E := hx.2
        by_cases hxE' : x ∈ E'
        · right; exact ⟨hxE', hx_not_E⟩
        · left; exact ⟨hxU, hxE'⟩
      have h_add : Lebesgue_outer_measure ((U \ E') ∪ (E' \ E)) ≤
          Lebesgue_outer_measure (U \ E') + Lebesgue_outer_measure (E' \ E) := by
        let S : Fin 2 → Set (EuclideanSpace' d) := ![U \ E', E' \ E]
        have h_union : ⋃ i : Fin 2, S i = (U \ E') ∪ (E' \ E) := by
          ext x; simp [S]
        calc
          Lebesgue_outer_measure ((U \ E') ∪ (E' \ E)) = Lebesgue_outer_measure (⋃ i : Fin 2, S i) := by rw [h_union]
          _ ≤ ∑ i : Fin 2, Lebesgue_outer_measure (S i) := Lebesgue_outer_measure.finite_union_le S
          _ = Lebesgue_outer_measure (U \ E') + Lebesgue_outer_measure (E' \ E) := by simp [S]
      calc
        Lebesgue_outer_measure (U \ E) ≤ Lebesgue_outer_measure ((U \ E') ∪ (E' \ E)) :=
          Lebesgue_outer_measure.mono h_sub
        _ ≤ Lebesgue_outer_measure (U \ E') + Lebesgue_outer_measure (E' \ E) := h_add
        _ ≤ (δ : ℝ) + (δ : ℝ) := add_le_add hU_diff h_E'E_bound
        _ = ((2 * δ : ℝ) : EReal) := by
          simpa using congrArg (fun x : ℝ => (x : EReal)) (show (δ : ℝ) + (δ : ℝ) = (2 * δ : ℝ) by ring)
    rcases Lebesgue_outer_measure.exists_open_superset_measure_le (E \ E') ((δ : ℝ) : EReal) hδ_pos'
      with ⟨W, hW_open, h_EE'_sub_W, hW_meas⟩
    have hW_bound : Lebesgue_outer_measure W ≤ (2 * δ : ℝ) := by
      calc
        Lebesgue_outer_measure W ≤ Lebesgue_outer_measure (E \ E') + (δ : ℝ) := hW_meas
        _ ≤ (δ : ℝ) + (δ : ℝ) := by
          simpa [add_comm] using add_le_add h_EE'_bound (le_refl ((δ : ℝ) : EReal))
        _ = ((2 * δ : ℝ) : EReal) := by
          simpa using congrArg (fun x : ℝ => (x : EReal)) (show (δ : ℝ) + (δ : ℝ) = (2 * δ : ℝ) by ring)
    let V := U ∪ W
    have hV_open : IsOpen V := IsOpen.union hU_open hW_open
    have hE_sub_V : E ⊆ V := by
      intro x hx
      by_cases hxE' : x ∈ E'
      · apply Set.mem_union_left W; exact hE'_sub_U hxE'
      · have hx_EE' : x ∈ E \ E' := ⟨hx, hxE'⟩
        apply Set.mem_union_right U; exact h_EE'_sub_W hx_EE'
    have hV_bound : Lebesgue_outer_measure (V \ E) ≤ (ε' : ℝ) := by
      have h_sub : V \ E ⊆ (U \ E) ∪ W := by
        intro x hx
        rcases hx with ⟨hxV, hxE⟩
        rcases hxV with (hxU | hxW)
        · left; exact ⟨hxU, hxE⟩
        · right; exact hxW
      have h_add : Lebesgue_outer_measure ((U \ E) ∪ W) ≤
          Lebesgue_outer_measure (U \ E) + Lebesgue_outer_measure W := by
        let S : Fin 2 → Set (EuclideanSpace' d) := ![U \ E, W]
        have h_union : ⋃ i : Fin 2, S i = (U \ E) ∪ W := by
          ext x; simp [S]
        calc
          Lebesgue_outer_measure ((U \ E) ∪ W) = Lebesgue_outer_measure (⋃ i : Fin 2, S i) := by rw [h_union]
          _ ≤ ∑ i : Fin 2, Lebesgue_outer_measure (S i) := Lebesgue_outer_measure.finite_union_le S
          _ = Lebesgue_outer_measure (U \ E) + Lebesgue_outer_measure W := by simp [S]
      calc
        Lebesgue_outer_measure (V \ E) ≤ Lebesgue_outer_measure ((U \ E) ∪ W) :=
          Lebesgue_outer_measure.mono h_sub
        _ ≤ Lebesgue_outer_measure (U \ E) + Lebesgue_outer_measure W := h_add
        _ ≤ (2 * δ : ℝ) + (2 * δ : ℝ) := add_le_add h_UE_bound hW_bound
        _ = ((4 * δ : ℝ) : EReal) := by
          simpa using congrArg (fun x : ℝ => (x : EReal)) (show (2 * δ : ℝ) + (2 * δ : ℝ) = (4 * δ : ℝ) by ring)
        _ = ((ε' : ℝ) : EReal) := by
          dsimp [δ]
          simpa using congrArg (fun x : ℝ => (x : EReal)) (show (4 * (ε' / 4 : ℝ) : ℝ) = ε' by ring)
    refine ⟨V, hV_open, hE_sub_V, ?_⟩
    calc
      Lebesgue_outer_measure (V \ E) ≤ (ε' : ℝ) := hV_bound
      _ ≤ ε := hε'_le

  /-- Exercise 1.2.8 -/
theorem Jordan_measurable.lebesgue {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: JordanMeasurable E) : LebesgueMeasurable E := by
  have hE_bounded : Bornology.IsBounded E := hE.1
  have h_interior_open : IsOpen (interior E) := isOpen_interior
  have h_interior_meas : LebesgueMeasurable (interior E) :=
    IsOpen.measurable h_interior_open

  have h_diff_sub_frontier : E \ interior E ⊆ frontier E := by
    intro x hx
    have hxE : x ∈ E := hx.1
    have hx_not_int : x ∉ interior E := hx.2
    have hx_cl : x ∈ closure E := subset_closure hxE
    rw [frontier, Set.mem_diff]
    exact ⟨hx_cl, hx_not_int⟩

  have h_frontier_bounded : Bornology.IsBounded (frontier E) :=
    hE_bounded.closure.subset frontier_subset_closure

  have h_frontier_null : JordanMeasurable.null (frontier E) :=
    (JordanMeasurable.iff_boundary_null hE_bounded).mp hE

  rcases h_frontier_null with ⟨hFrJM, hFr_measure⟩

  have h_frontier_outer_zero : Jordan_outer_measure (frontier E) = 0 := by
    calc
      Jordan_outer_measure (frontier E) = hFrJM.measure := hFrJM.eq_outer.symm
      _ = 0 := hFr_measure

  have h_frontier_Lebesgue_null : IsNull (frontier E) := by
    apply le_antisymm ?_ (Lebesgue_outer_measure.nonneg _)
    calc
      Lebesgue_outer_measure (frontier E) ≤ Jordan_outer_measure (frontier E) :=
        Lebesgue_outer_measure_le_Jordan h_frontier_bounded
      _ = 0 := by
        simpa using congrArg (fun x : ℝ => (x : EReal)) h_frontier_outer_zero

  have h_diff_null : IsNull (E \ interior E) :=
    IsNull.subset h_frontier_Lebesgue_null h_diff_sub_frontier

  have h_diff_meas : LebesgueMeasurable (E \ interior E) :=
    IsNull.measurable h_diff_null

  have h_union_eq : interior E ∪ (E \ interior E) = E :=
    Set.union_diff_cancel interior_subset

  rw [← h_union_eq]
  exact LebesgueMeasurable.union h_interior_meas h_diff_meas

open BoundedInterval

abbrev CantorInterval (n:ℕ) : Set ℝ := ⋃ a : Fin n → ({0, 2}:Set ℕ), (Icc (∑ i, (a i)/(3:ℝ)^(i.val+1)) (∑ i, a i/(3:ℝ)^(i.val+1) + 1/(3:ℝ)^n)).toSet

abbrev CantorSet : Set ℝ := ⋂ n : ℕ, CantorInterval n

/-- Exercise 1.2.9 (Middle thirds Cantor set ) -/
theorem CantorSet.compact : IsCompact CantorSet := by
  have hC_closed (n : ℕ) : IsClosed (CantorInterval n) := by
    unfold CantorInterval
    have h_finite : (Set.univ : Set (Fin n → ({0, 2} : Set ℕ))).Finite := Set.finite_univ
    have h_union : (⋃ a : Fin n → ({0, 2} : Set ℕ), (Icc (∑ i, (a i)/(3:ℝ)^(i.val+1)) (∑ i, a i/(3:ℝ)^(i.val+1) + 1/(3:ℝ)^n)).toSet) =
      ⋃ a ∈ (Set.univ : Set (Fin n → ({0, 2} : Set ℕ))), (Icc (∑ i, (a i)/(3:ℝ)^(i.val+1)) (∑ i, a i/(3:ℝ)^(i.val+1) + 1/(3:ℝ)^n)).toSet := by
      ext x; simp
    rw [h_union]
    refine h_finite.isClosed_biUnion (fun a ha => ?_)
    simp [BoundedInterval.toSet, isClosed_Icc]
  have h_closed : IsClosed CantorSet := by
    rw [CantorSet]
    apply isClosed_iInter
    exact hC_closed

  have h_C0_eq : CantorInterval 0 = Set.Icc (0 : ℝ) 1 := by
    unfold CantorInterval
    haveI : Nonempty (Fin 0 → ({0, 2} : Set ℕ)) := ⟨fun i => i.elim0⟩
    simp [Set.iUnion_const]

  have h_bounded : Bornology.IsBounded CantorSet := by
    have h_sub : CantorSet ⊆ Set.Icc (0 : ℝ) 1 := by
      intro x hx
      have hx0 : x ∈ CantorInterval 0 := Set.mem_iInter.mp hx 0
      rw [h_C0_eq] at hx0
      exact hx0
    exact (Metric.isBounded_Icc (0 : ℝ) 1).subset h_sub

  exact Metric.isCompact_of_isClosed_isBounded h_closed h_bounded

instance : Uncountable (ℕ → Bool) := by
  refine ⟨?h⟩
  intro h
  have h_nonempty : Nonempty (ℕ → Bool) := ⟨fun _ => false⟩
  rcases (countable_iff_exists_surjective (α := ℕ → Bool)).mp h with ⟨f, hf⟩
  let g : ℕ → Bool := fun n => !(f n n)
  rcases hf g with ⟨k, hk⟩
  have h_contra : g k = !(g k) := by
    calc
      g k = !(f k k) := rfl
      _ = !(g k) := by rw [hk]
  cases hg : g k
  · rw [hg] at h_contra; simp at h_contra
  · rw [hg] at h_contra; simp at h_contra

noncomputable def cantorEmbedding (b : ℕ → Bool) : ℝ :=
  ∑' n : ℕ, ((if b n then 2 else 0 : ℝ)) / (3 : ℝ) ^ (n + 1)

lemma summable_two_div_three_pow : Summable (fun n : ℕ => (2 : ℝ) / (3 : ℝ) ^ (n + 1)) := by
  have h_geom : Summable (fun n : ℕ => ((1/3 : ℝ) ^ n : ℝ)) := by
    have h_norm : ‖(1/3 : ℝ)‖ < 1 := by norm_num
    exact summable_geometric_of_norm_lt_one h_norm
  have h_nonneg : ∀ n : ℕ, 0 ≤ (2 : ℝ) / (3 : ℝ) ^ (n + 1) := by
    intro n; positivity
  have h_le : ∀ n : ℕ, (2 : ℝ) / (3 : ℝ) ^ (n + 1) ≤ (2/3 : ℝ) * ((1/3 : ℝ) ^ n) := by
    intro n
    have h_eq : (2 : ℝ) / (3 : ℝ) ^ (n + 1) = (2/3 : ℝ) * ((1/3 : ℝ) ^ n) := by
      calc
        (2 : ℝ) / (3 : ℝ) ^ (n + 1) = (2 : ℝ) * ((3 : ℝ) ^ (n + 1))⁻¹ := rfl
        _ = (2 : ℝ) * ((3 : ℝ) * (3 : ℝ) ^ n)⁻¹ := by
          simp [pow_succ, mul_comm]
        _ = (2 : ℝ) * ((3 : ℝ)⁻¹ * ((3 : ℝ) ^ n)⁻¹) := by
          rw [mul_inv_rev, mul_comm ((3 : ℝ) ^ n)⁻¹]
        _ = ((2 : ℝ) * (3 : ℝ)⁻¹) * ((3 : ℝ) ^ n)⁻¹ := by ring
        _ = (2/3 : ℝ) * ((3 : ℝ) ^ n)⁻¹ := rfl
        _ = (2/3 : ℝ) * ((1/3 : ℝ) ^ n) := by simp
    exact h_eq.le
  exact Summable.of_nonneg_of_le h_nonneg h_le (Summable.mul_left (2/3 : ℝ) h_geom)

lemma cantorEmbedding_tsum (b : ℕ → Bool) : Summable (fun n : ℕ => ((if b n then 2 else 0 : ℝ)) / (3 : ℝ) ^ (n + 1)) := by
  have h_nonneg : ∀ n : ℕ, 0 ≤ ((if b n then 2 else 0 : ℝ)) / (3 : ℝ) ^ (n + 1) := by
    intro n
    by_cases h : b n
    · have hval : ((if b n then 2 else 0 : ℝ)) = (2 : ℝ) := by simp [h]
      simp [hval]; positivity
    · have hval : ((if b n then 2 else 0 : ℝ)) = (0 : ℝ) := by simp [h]
      simp [hval]
  have h_bound : ∀ n : ℕ, ((if b n then 2 else 0 : ℝ)) / (3 : ℝ) ^ (n + 1) ≤ (2 : ℝ) / (3 : ℝ) ^ (n + 1) := by
    intro n
    by_cases h : b n
    · have hval : ((if b n then 2 else 0 : ℝ)) = (2 : ℝ) := by simp [h]
      simp [hval]
    · have hval : ((if b n then 2 else 0 : ℝ)) = (0 : ℝ) := by simp [h]
      rw [hval, zero_div]
      positivity
  exact Summable.of_nonneg_of_le h_nonneg h_bound summable_two_div_three_pow

lemma tsum_tail_two_three_pow (N : ℕ) : ∑' n : ℕ, (2 : ℝ) / (3 : ℝ) ^ (n + N + 1) = 1 / (3 : ℝ) ^ N := by
  have h_geom : ∑' n : ℕ, ((1/3 : ℝ) ^ n : ℝ) = (1 - (1/3 : ℝ))⁻¹ :=
    tsum_geometric_of_norm_lt_one (by norm_num : ‖(1/3 : ℝ)‖ < 1)
  calc
    ∑' n : ℕ, (2 : ℝ) / (3 : ℝ) ^ (n + N + 1)
        = ∑' n : ℕ, (((2 : ℝ) / (3 : ℝ) ^ (N + 1 : ℕ)) * ((1/3 : ℝ) ^ n)) := by
      refine tsum_congr (fun n => ?_)
      calc
        (2 : ℝ) / (3 : ℝ) ^ (n + N + 1) = (2 : ℝ) / ((3 : ℝ) ^ (n + N + 1)) := rfl
        _ = (2 : ℝ) / ((3 : ℝ) ^ (N + 1) * (3 : ℝ) ^ n) := by
          rw [show (n + N + 1 : ℕ) = (N + 1) + n by omega, pow_add]
        _ = ((2 : ℝ) / (3 : ℝ) ^ (N + 1)) * (1 / (3 : ℝ) ^ n) := by
          field_simp
        _ = ((2 : ℝ) / (3 : ℝ) ^ (N + 1 : ℕ)) * ((1/3 : ℝ) ^ n) := by simp
    _ = ((2 : ℝ) / (3 : ℝ) ^ (N + 1 : ℕ)) * ∑' n : ℕ, ((1/3 : ℝ) ^ n) := by rw [tsum_mul_left]
    _ = ((2 : ℝ) / (3 : ℝ) ^ (N + 1 : ℕ)) * ((1 - (1/3 : ℝ))⁻¹) := by rw [h_geom]
    _ = 1 / (3 : ℝ) ^ N := by
      field_simp
      ring

noncomputable def cantorPartialSum (b : ℕ → Bool) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, ((if b n then 2 else 0 : ℝ)) / (3 : ℝ) ^ (n + 1)

lemma cantorPartialSum_nonneg (b : ℕ → Bool) (N : ℕ) : 0 ≤ cantorPartialSum b N := by
  unfold cantorPartialSum
  apply Finset.sum_nonneg
  intro n hn
  by_cases h : b n
  · simp [h]; positivity
  · simp [h]

lemma cantorEmbedding_eq_partial_add_tail (b : ℕ → Bool) (N : ℕ) :
    cantorPartialSum b N + ∑' n : ℕ, ((if b (n + N) then 2 else 0 : ℝ)) / (3 : ℝ) ^ (n + N + 1) = cantorEmbedding b := by
  have h := Summable.sum_add_tsum_nat_add N (cantorEmbedding_tsum b)
  unfold cantorPartialSum; unfold cantorEmbedding
  simpa using h

lemma cantorEmbedding_tail_nonneg (b : ℕ → Bool) (N : ℕ) :
    0 ≤ ∑' n : ℕ, ((if b (n + N) then 2 else 0 : ℝ)) / (3 : ℝ) ^ (n + N + 1) := by
  apply tsum_nonneg
  intro n
  by_cases h : b (n + N)
  · simp [h]; positivity
  · simp [h]

lemma cantorTailBound (b : ℕ → Bool) (N : ℕ) :
    ∑' n : ℕ, ((if b (n + N) then 2 else 0 : ℝ)) / (3 : ℝ) ^ (n + N + 1) ≤ 1 / (3 : ℝ) ^ N := by
  have h_bound : ∀ n : ℕ, ((if b (n + N) then 2 else 0 : ℝ)) / (3 : ℝ) ^ (n + N + 1) ≤
      (2 : ℝ) / (3 : ℝ) ^ (n + N + 1) := by
    intro n
    by_cases h : b (n + N)
    · simp [h]
    · simp [h]; positivity
  have hf_summable : Summable (fun n : ℕ => ((if b (n + N) then 2 else 0 : ℝ)) / (3 : ℝ) ^ (n + N + 1)) := by
    simpa using (summable_nat_add_iff (G := ℝ) N).mpr (cantorEmbedding_tsum b)
  have hg_summable : Summable (fun n : ℕ => (2 : ℝ) / (3 : ℝ) ^ (n + N + 1)) := by
    simpa using (summable_nat_add_iff (G := ℝ) N).mpr summable_two_div_three_pow
  have h_hasSum_f : HasSum (fun n : ℕ => ((if b (n + N) then 2 else 0 : ℝ)) / (3 : ℝ) ^ (n + N + 1))
      (∑' n : ℕ, ((if b (n + N) then 2 else 0 : ℝ)) / (3 : ℝ) ^ (n + N + 1)) :=
    hf_summable.hasSum
  have h_hasSum_g : HasSum (fun n : ℕ => (2 : ℝ) / (3 : ℝ) ^ (n + N + 1))
      (∑' n : ℕ, (2 : ℝ) / (3 : ℝ) ^ (n + N + 1)) :=
    hg_summable.hasSum
  have h_le_tsum : (∑' n : ℕ, ((if b (n + N) then 2 else 0 : ℝ)) / (3 : ℝ) ^ (n + N + 1)) ≤
      (∑' n : ℕ, (2 : ℝ) / (3 : ℝ) ^ (n + N + 1)) :=
    hasSum_le h_bound h_hasSum_f h_hasSum_g
  calc
    (∑' n : ℕ, ((if b (n + N) then 2 else 0 : ℝ)) / (3 : ℝ) ^ (n + N + 1)) ≤
        ∑' n : ℕ, (2 : ℝ) / (3 : ℝ) ^ (n + N + 1) := h_le_tsum
    _ = 1 / (3 : ℝ) ^ N := tsum_tail_two_three_pow N

lemma cantorPartialSum_le_cantorEmbedding (b : ℕ → Bool) (N : ℕ) :
    cantorPartialSum b N ≤ cantorEmbedding b := by
  linarith [cantorEmbedding_eq_partial_add_tail b N, cantorEmbedding_tail_nonneg b N]

lemma cantorEmbedding_le_partial_add_inv (b : ℕ → Bool) (N : ℕ) :
    cantorEmbedding b ≤ cantorPartialSum b N + 1 / (3 : ℝ) ^ N := by
  linarith [cantorEmbedding_eq_partial_add_tail b N, cantorTailBound b N]

lemma cantorPartialSum_diff_abs (b₁ b₂ : ℕ → Bool) (k : ℕ) (hk : b₁ k ≠ b₂ k)
    (h_agree : ∀ m < k, b₁ m = b₂ m) :
    |cantorPartialSum b₁ (k+1) - cantorPartialSum b₂ (k+1)| = 2 / (3 : ℝ) ^ (k+1) := by
  unfold cantorPartialSum
  have h_range_split : Finset.range (k+1) = (Finset.range k) ∪ {k} := by
    simp [Finset.range_add_one]
  have h_disjoint : Disjoint (Finset.range k) ({k} : Finset ℕ) := by
    simp [Finset.disjoint_singleton_right, Finset.mem_range]
  have h_sum_cancel : (∑ m ∈ Finset.range k, ((if b₁ m then 2 else 0 : ℝ)) / (3 : ℝ) ^ (m + 1)) =
      (∑ m ∈ Finset.range k, ((if b₂ m then 2 else 0 : ℝ)) / (3 : ℝ) ^ (m + 1)) := by
    apply Finset.sum_congr rfl; intro m hm; simp [h_agree m (Finset.mem_range.1 hm)]
  have h_sum1 : (∑ m ∈ Finset.range (k+1), ((if b₁ m then 2 else 0 : ℝ)) / (3 : ℝ) ^ (m + 1)) =
      (∑ m ∈ Finset.range k, ((if b₁ m then 2 else 0 : ℝ)) / (3 : ℝ) ^ (m + 1)) +
      ((if b₁ k then 2 else 0 : ℝ)) / (3 : ℝ) ^ (k + 1) := by
    rw [h_range_split, Finset.sum_union h_disjoint, Finset.sum_singleton]
  have h_sum2 : (∑ m ∈ Finset.range (k+1), ((if b₂ m then 2 else 0 : ℝ)) / (3 : ℝ) ^ (m + 1)) =
      (∑ m ∈ Finset.range k, ((if b₂ m then 2 else 0 : ℝ)) / (3 : ℝ) ^ (m + 1)) +
      ((if b₂ k then 2 else 0 : ℝ)) / (3 : ℝ) ^ (k + 1) := by
    rw [h_range_split, Finset.sum_union h_disjoint, Finset.sum_singleton]
  rw [h_sum1, h_sum2, h_sum_cancel]
  simp
  have h_dif : |(if b₁ k then 2 else 0 : ℝ) - (if b₂ k then 2 else 0 : ℝ)| = 2 := by
    by_cases h₁ : b₁ k
    · by_cases h₂ : b₂ k
      · exfalso; exact hk (by simp [h₁, h₂])
      · simp [h₁, h₂]
    · by_cases h₂ : b₂ k
      · simp [h₁, h₂]
      · exfalso; exact hk (by simp [h₁, h₂])
  calc
    |(((if b₁ k then 2 else 0 : ℝ)) / (3 : ℝ) ^ (k + 1)) -
      ((if b₂ k then 2 else 0 : ℝ)) / (3 : ℝ) ^ (k + 1)|
        = |((if b₁ k then 2 else 0 : ℝ) - (if b₂ k then 2 else 0 : ℝ)) / (3 : ℝ) ^ (k + 1)| := by
      field_simp
    _ = |(if b₁ k then 2 else 0 : ℝ) - (if b₂ k then 2 else 0 : ℝ)| / |(3 : ℝ) ^ (k + 1)| := by rw [abs_div]
    _ = |(if b₁ k then 2 else 0 : ℝ) - (if b₂ k then 2 else 0 : ℝ)| / ((3 : ℝ) ^ (k + 1)) := by
      simp [abs_of_pos (by positivity : 0 < (3 : ℝ) ^ (k + 1))]
    _ = 2 / (3 : ℝ) ^ (k + 1) := by rw [h_dif]

lemma cantorEmbedding_injective : Function.Injective cantorEmbedding := by
  intro b₁ b₂ h_eq
  ext n
  by_contra! h_ne
  have h_exists : ∃ n, b₁ n ≠ b₂ n := ⟨n, h_ne⟩
  let k := Nat.find h_exists
  have hk : b₁ k ≠ b₂ k := Nat.find_spec h_exists
  have hk_min' : ∀ m < k, b₁ m = b₂ m := by
    intro m hm
    have h_not_ne : ¬ b₁ m ≠ b₂ m := Nat.find_min h_exists hm
    exact not_ne_iff.mp h_not_ne
  let N := k+1
  have h_diff_abs : |cantorPartialSum b₁ N - cantorPartialSum b₂ N| = 2 / (3 : ℝ) ^ N :=
    cantorPartialSum_diff_abs b₁ b₂ k hk hk_min'
  have h_tail_nonneg₁ : 0 ≤ ∑' n : ℕ, ((if b₁ (n + N) then 2 else 0 : ℝ)) / (3 : ℝ) ^ (n + N + 1) :=
    cantorEmbedding_tail_nonneg b₁ N
  have h_tail_nonneg₂ : 0 ≤ ∑' n : ℕ, ((if b₂ (n + N) then 2 else 0 : ℝ)) / (3 : ℝ) ^ (n + N + 1) :=
    cantorEmbedding_tail_nonneg b₂ N
  have h_tail_bound₁ : ∑' n : ℕ, ((if b₁ (n + N) then 2 else 0 : ℝ)) / (3 : ℝ) ^ (n + N + 1) ≤ 1 / (3 : ℝ) ^ N :=
    cantorTailBound b₁ N
  have h_tail_bound₂ : ∑' n : ℕ, ((if b₂ (n + N) then 2 else 0 : ℝ)) / (3 : ℝ) ^ (n + N + 1) ≤ 1 / (3 : ℝ) ^ N :=
    cantorTailBound b₂ N
  have h_tail_diff_abs_bound :
      |(∑' n : ℕ, ((if b₂ (n + N) then 2 else 0 : ℝ)) / (3 : ℝ) ^ (n + N + 1)) -
        (∑' n : ℕ, ((if b₁ (n + N) then 2 else 0 : ℝ)) / (3 : ℝ) ^ (n + N + 1))| ≤ 1 / (3 : ℝ) ^ N := by
    let A := ∑' n : ℕ, ((if b₁ (n + N) then 2 else 0 : ℝ)) / (3 : ℝ) ^ (n + N + 1)
    let B := ∑' n : ℕ, ((if b₂ (n + N) then 2 else 0 : ℝ)) / (3 : ℝ) ^ (n + N + 1)
    have hA_nonneg : 0 ≤ A := h_tail_nonneg₁
    have hB_nonneg : 0 ≤ B := h_tail_nonneg₂
    have hA_bound : A ≤ 1 / (3 : ℝ) ^ N := h_tail_bound₁
    have hB_bound : B ≤ 1 / (3 : ℝ) ^ N := h_tail_bound₂
    have h_abs_le_max : |A - B| ≤ max A B := by
      by_cases hAB : A ≥ B
      · have h_abs : |A - B| = A - B := abs_of_nonneg (sub_nonneg.mpr hAB)
        rw [h_abs, max_eq_left hAB]
        nlinarith
      · have hBA : B ≥ A := by linarith
        have h_abs : |A - B| = B - A := by
          rw [abs_of_nonpos (sub_nonpos.mpr hBA)]
          ring
        rw [h_abs, max_eq_right hBA]
        nlinarith
    have h_max_bound : max A B ≤ 1 / (3 : ℝ) ^ N := max_le hA_bound hB_bound
    have h_symm : |B - A| = |A - B| := abs_sub_comm _ _
    rw [h_symm]
    exact le_trans h_abs_le_max h_max_bound
  have h_eq_tails : cantorPartialSum b₁ N - cantorPartialSum b₂ N =
      (∑' n : ℕ, ((if b₂ (n + N) then 2 else 0 : ℝ)) / (3 : ℝ) ^ (n + N + 1)) -
      (∑' n : ℕ, ((if b₁ (n + N) then 2 else 0 : ℝ)) / (3 : ℝ) ^ (n + N + 1)) := by
    linarith [cantorEmbedding_eq_partial_add_tail b₁ N, cantorEmbedding_eq_partial_add_tail b₂ N, h_eq]
  have h_contra : 2 / (3 : ℝ) ^ N ≤ 1 / (3 : ℝ) ^ N := by
    calc
      2 / (3 : ℝ) ^ N = |cantorPartialSum b₁ N - cantorPartialSum b₂ N| := by rw [h_diff_abs]
      _ = |(∑' n : ℕ, ((if b₂ (n + N) then 2 else 0 : ℝ)) / (3 : ℝ) ^ (n + N + 1)) -
            (∑' n : ℕ, ((if b₁ (n + N) then 2 else 0 : ℝ)) / (3 : ℝ) ^ (n + N + 1))| := by
        rw [h_eq_tails]
      _ ≤ 1 / (3 : ℝ) ^ N := h_tail_diff_abs_bound
  have hpos : 0 < (3 : ℝ) ^ N := by positivity
  have : 1 / (3 : ℝ) ^ N < 2 / (3 : ℝ) ^ N := by
    field_simp [hpos.ne.symm]
    nlinarith
  linarith

lemma cantorEmbedding_mem (b : ℕ → Bool) : cantorEmbedding b ∈ CantorSet := by
  rw [CantorSet]
  refine Set.mem_iInter.mpr ?_
  intro N
  unfold CantorInterval
  let a : Fin N → ({0, 2} : Set ℕ) := fun i =>
    if h : b i.val then ⟨2, by norm_num⟩ else ⟨0, by norm_num⟩
  have ha_val : ∀ i : Fin N, (a i : ℝ) = if b i.val then (2 : ℝ) else (0 : ℝ) := by
    intro i; dsimp [a]; split_ifs <;> simp
  have h_left : (∑ i : Fin N, ((a i : ℝ) / (3 : ℝ) ^ (i.val + 1))) = cantorPartialSum b N := by
    unfold cantorPartialSum
    calc
      (∑ i : Fin N, ((a i : ℝ) / (3 : ℝ) ^ (i.val + 1)))
          = (∑ i : Fin N, ((if b i.val then 2 else 0 : ℝ)) / (3 : ℝ) ^ (i.val + 1)) := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        rw [ha_val i]
      _ = ∑ n ∈ Finset.range N, ((if b n then 2 else 0 : ℝ)) / (3 : ℝ) ^ (n + 1) := by
        simpa using (Fin.sum_univ_eq_sum_range (fun n : ℕ => ((if b n then 2 else 0 : ℝ)) / (3 : ℝ) ^ (n + 1)) N)
  have h_lower : (∑ i : Fin N, ((a i : ℝ) / (3 : ℝ) ^ (i.val + 1))) ≤ cantorEmbedding b := by
    rw [h_left]
    exact cantorPartialSum_le_cantorEmbedding b N
  have h_upper : cantorEmbedding b ≤ (∑ i : Fin N, ((a i : ℝ) / (3 : ℝ) ^ (i.val + 1))) + 1 / (3 : ℝ) ^ N := by
    rw [h_left]
    exact cantorEmbedding_le_partial_add_inv b N
  apply Set.mem_iUnion.mpr
  refine ⟨a, ?_⟩
  simp [BoundedInterval.toSet, Set.mem_Icc]
  constructor
  · simpa using h_lower
  · simpa [div_eq_inv_mul] using h_upper

theorem CantorSet.uncountable : Uncountable CantorSet := by
  have h_uncountable_nat_bool : Uncountable (ℕ → Bool) := by infer_instance
  have h_injective : Function.Injective (fun (b : ℕ → Bool) => (⟨cantorEmbedding b, cantorEmbedding_mem b⟩ : CantorSet)) := by
    intro b₁ b₂ h
    apply cantorEmbedding_injective
    exact Subtype.ext_iff.mp h
  refine ⟨?h⟩
  intro h_countable
  haveI : Countable CantorSet := h_countable
  have h_countable_nat_bool : Countable (ℕ → Bool) :=
    h_injective.countable
  exact h_uncountable_nat_bool.not_countable h_countable_nat_bool

theorem CantorSet.null : IsNull (Real.equiv_EuclideanSpace' '' CantorSet) := by
  have h_subset (n : ℕ) : CantorSet ⊆ CantorInterval n := by
    intro x hx; exact Set.mem_iInter.mp hx n

  have h_image_subset (n : ℕ) : Real.equiv_EuclideanSpace' '' CantorSet ⊆ Real.equiv_EuclideanSpace' '' CantorInterval n :=
    Set.image_mono (h_subset n)

  have h_mono (n : ℕ) : Lebesgue_outer_measure (Real.equiv_EuclideanSpace' '' CantorSet) ≤
      Lebesgue_outer_measure (Real.equiv_EuclideanSpace' '' CantorInterval n) :=
    Lebesgue_outer_measure.mono (h_image_subset n)

  have h_each_measure (n : ℕ) (a : Fin n → ({0, 2} : Set ℕ)) : Lebesgue_outer_measure
      (Real.equiv_EuclideanSpace' '' ((Icc (∑ i, (a i : ℝ)/(3:ℝ)^(i.val+1)) (∑ i, (a i : ℝ)/(3:ℝ)^(i.val+1) + 1/(3:ℝ)^n)).toSet)) = (((1/3 : ℝ)^n : ℝ) : EReal) := by
    set a_sum := ∑ i : Fin n, ((a i : ℝ) / (3 : ℝ) ^ (i.val + 1)) with ha_sum
    set b_sum := a_sum + 1 / (3 : ℝ) ^ n with hb_sum
    have h_len : b_sum - a_sum = 1 / (3 : ℝ) ^ n := by
      rw [hb_sum]; ring
    have h_nonneg_len : 0 ≤ b_sum - a_sum := by
      rw [h_len]; positivity
    have h_vol : |((Icc a_sum b_sum : Box 1))|ᵥ = (1/3 : ℝ)^n := by
      unfold Box.volume
      simp [length, BoundedInterval.a, BoundedInterval.b, h_len]
    calc
      Lebesgue_outer_measure (Real.equiv_EuclideanSpace' '' ((Icc a_sum b_sum).toSet))
          = Lebesgue_outer_measure (((Icc a_sum b_sum : Box 1).toSet)) := by
            rw [BoundedInterval.coe_of_box]
      _ = (IsElementary.box (Icc a_sum b_sum : Box 1)).measure := by
        rw [Lebesgue_outer_measure.elementary _ (IsElementary.box _)]
      _ = |(Icc a_sum b_sum : Box 1)|ᵥ := by rw [IsElementary.measure_of_box]
      _ = (((1/3 : ℝ)^n : ℝ) : EReal) := by
        exact_mod_cast h_vol

  have h_measure_CantorInterval (n : ℕ) :
      Lebesgue_outer_measure (Real.equiv_EuclideanSpace' '' CantorInterval n) ≤ (((2/3 : ℝ)^n : ℝ) : EReal) := by
    let α := Fin n → ({0, 2} : Set ℕ)
    have h_card_nat : Fintype.card α = 2^n := by
      dsimp [α]; simp
    have h_card_real : (Fintype.card α : ℝ) = (2^n : ℝ) := by exact_mod_cast h_card_nat
    let card := Fintype.card α
    let e : α ≃ Fin card := Fintype.equivFin α
    let B (a : α) : Set (EuclideanSpace' 1) :=
      Real.equiv_EuclideanSpace' '' ((Icc (∑ i : Fin n, ((a i : ℝ) / (3 : ℝ) ^ (i.val + 1)))
        (∑ i : Fin n, ((a i : ℝ) / (3 : ℝ) ^ (i.val + 1)) + 1 / (3 : ℝ) ^ n)).toSet)
    have h_image_union : Real.equiv_EuclideanSpace' '' CantorInterval n = ⋃ i : Fin card, B (e.symm i) := by
      unfold CantorInterval
      calc
        Real.equiv_EuclideanSpace' '' (⋃ a : α, (Icc (∑ i, (a i : ℝ)/(3:ℝ)^(i.val+1)) (∑ i, (a i : ℝ)/(3:ℝ)^(i.val+1) + 1/(3:ℝ)^n)).toSet)
            = ⋃ a : α, Real.equiv_EuclideanSpace' '' ((Icc (∑ i, (a i : ℝ)/(3:ℝ)^(i.val+1)) (∑ i, (a i : ℝ)/(3:ℝ)^(i.val+1) + 1/(3:ℝ)^n)).toSet) := by
              rw [Set.image_iUnion]
        _ = ⋃ a : α, B a := rfl
        _ = ⋃ i : Fin card, B (e.symm i) := by
          ext x; constructor
          · intro h; rcases Set.mem_iUnion.mp h with ⟨a, hx⟩
            refine Set.mem_iUnion.mpr ⟨e a, ?_⟩; simpa using hx
          · intro h; rcases Set.mem_iUnion.mp h with ⟨i, hx⟩
            refine Set.mem_iUnion.mpr ⟨e.symm i, ?_⟩; simpa using hx
    rw [h_image_union]
    have h_subadditive : Lebesgue_outer_measure (⋃ i : Fin card, B (e.symm i)) ≤
        ∑ i : Fin card, Lebesgue_outer_measure (B (e.symm i)) :=
      Lebesgue_outer_measure.finite_union_le (fun i : Fin card => B (e.symm i))
    apply le_trans h_subadditive
    have h_sum_eq : ∑ i : Fin card, Lebesgue_outer_measure (B (e.symm i)) = (((2/3 : ℝ)^n : ℝ) : EReal) := by
      calc
        ∑ i : Fin card, Lebesgue_outer_measure (B (e.symm i))
            = ∑ i : Fin card, (((1/3 : ℝ)^n : ℝ) : EReal) := by
              refine Finset.sum_congr rfl (fun i hi => ?_)
              dsimp [B]
              exact h_each_measure n (e.symm i)
        _ = ((∑ i : Fin card, ((1/3 : ℝ)^n : ℝ) : ℝ) : EReal) := by simp
        _ = (((Fintype.card (Fin card) : ℝ) * ((1/3 : ℝ)^n : ℝ) : ℝ) : EReal) := by simp
        _ = (((card : ℝ) * ((1/3 : ℝ)^n : ℝ) : ℝ) : EReal) := by simp
        _ = (((Fintype.card α : ℝ) * ((1/3 : ℝ)^n : ℝ) : ℝ) : EReal) := by
          dsimp [card]
        _ = (((2^n : ℝ) * ((1/3 : ℝ)^n : ℝ) : ℝ) : EReal) := by
          simp [h_card_real]
        _ = (((2/3 : ℝ)^n : ℝ) : EReal) := by
          have h : (2 : ℝ)^n * (1/3 : ℝ)^n = (2/3 : ℝ)^n := by
            calc
              (2 : ℝ)^n * (1/3 : ℝ)^n = ((2 : ℝ) * (1/3 : ℝ)) ^ n := by rw [← mul_pow]
              _ = (2/3 : ℝ)^n := by norm_num
          simpa using congrArg (fun (x : ℝ) => (x : EReal)) h
    exact h_sum_eq.le

  have h_all_n (n : ℕ) : Lebesgue_outer_measure (Real.equiv_EuclideanSpace' '' CantorSet) ≤ (((2/3 : ℝ)^n : ℝ) : EReal) :=
    le_trans (h_mono n) (h_measure_CantorInterval n)

  have h_zero : Lebesgue_outer_measure (Real.equiv_EuclideanSpace' '' CantorSet) ≤ 0 := by
    apply EReal.le_of_forall_pos_le_add' (b := 0)
    intro ε hε
    have h_tendsto : Filter.Tendsto (fun n : ℕ => ((2/3 : ℝ)^n : ℝ)) Filter.atTop (nhds (0 : ℝ)) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    rcases Metric.tendsto_atTop.mp h_tendsto ε hε with ⟨N, hN⟩
    have h_N_lt_ε : ((2/3 : ℝ)^N : ℝ) < ε := by
      have h_bound := hN N (le_refl N)
      rw [Real.dist_eq, sub_zero] at h_bound
      have h_nonneg : 0 ≤ (2/3 : ℝ)^N := pow_nonneg (by norm_num) N
      rw [abs_of_nonneg h_nonneg] at h_bound
      exact h_bound
    have h_lt : Lebesgue_outer_measure (Real.equiv_EuclideanSpace' '' CantorSet) < (ε : EReal) := by
      calc
        Lebesgue_outer_measure (Real.equiv_EuclideanSpace' '' CantorSet) ≤ (((2/3 : ℝ)^N : ℝ) : EReal) := h_all_n N
        _ < (ε : EReal) := by exact_mod_cast h_N_lt_ε
    calc
      Lebesgue_outer_measure (Real.equiv_EuclideanSpace' '' CantorSet) ≤ (ε : EReal) := le_of_lt h_lt
      _ = (0 : EReal) + (ε : EReal) := by simp

  exact le_antisymm h_zero (Lebesgue_outer_measure.nonneg _)

private lemma strictMono_g : StrictMono fun (x : ℝ) => x / (1 + |x|) := by
  intro a b h
  dsimp
  by_cases ha : 0 ≤ a
  · have hb : 0 ≤ b := by nlinarith
    rw [abs_of_nonneg ha, abs_of_nonneg hb]
    have ha_pos : 0 < 1 + a := by nlinarith
    have hb_pos : 0 < 1 + b := by nlinarith
    field_simp [ha_pos.ne', hb_pos.ne']
    nlinarith
  · have ha_neg : a < 0 := by nlinarith
    by_cases hb : 0 ≤ b
    · rw [abs_of_neg ha_neg, abs_of_nonneg hb]
      have ha_val : a / (1 - a) < 0 :=
        (div_neg_iff.mpr (Or.inr ⟨by nlinarith, by nlinarith⟩))
      have hb_val : b / (1 + b) ≥ 0 := div_nonneg hb (by nlinarith)
      exact lt_of_lt_of_le ha_val hb_val
    · have hb_neg : b < 0 := by nlinarith
      rw [abs_of_neg ha_neg, abs_of_neg hb_neg]
      have ha_pos : 0 < 1 + (-a) := by nlinarith
      have hb_pos : 0 < 1 + (-b) := by nlinarith
      field_simp [ha_pos.ne', hb_pos.ne']
      nlinarith

private lemma not_countable_Ioo {a b : ℝ} (h : a < b) : ¬ Set.Countable (Set.Ioo a b) := by
  set g : ℝ → ℝ := λ x => (x / (1 + |x|) + 1) / 2 with hg
  have hg_range : ∀ x : ℝ, g x ∈ Set.Ioo (0 : ℝ) 1 := by
    intro x
    have hlow : 0 < (x / (1 + |x|) + 1) / 2 := by
      have : -1 < x / (1 + |x|) := by
        by_cases hx : 0 ≤ x
        · rw [abs_of_nonneg hx]
          have : 0 ≤ x / (1 + x) := div_nonneg hx (by nlinarith)
          nlinarith
        · rw [abs_of_neg (by nlinarith : x < 0)]
          have hden : 0 < 1 + (-x) := by nlinarith
          have h_eq : x / (1 + (-x)) + 1 = 1 / (1 + (-x)) := by
            field_simp [hden.ne'] ; ring
          have h_pos : 0 < 1 / (1 + (-x)) := div_pos (by norm_num) hden
          nlinarith
      nlinarith
    have hhigh : (x / (1 + |x|) + 1) / 2 < 1 := by
      have : x / (1 + |x|) < 1 := by
        by_cases hx : 0 ≤ x
        · rw [abs_of_nonneg hx]
          have hpos : 0 < 1 + x := by nlinarith
          field_simp [hpos.ne']
          nlinarith
        · rw [abs_of_neg (by nlinarith : x < 0)]
          have hpos : 0 < 1 + (-x) := by nlinarith
          field_simp [hpos.ne']
          nlinarith
      nlinarith
    exact ⟨hlow, hhigh⟩
  have hg_inj : Function.Injective g := by
    intro x y h
    have : (x / (1 + |x|) + 1) / 2 = (y / (1 + |y|) + 1) / 2 := h
    have h_eq : x / (1 + |x|) = y / (1 + |y|) := by nlinarith
    exact strictMono_g.injective h_eq
  set f : ℝ → Set.Ioo a b := λ x => ⟨a + (b - a) * g x, by
    have hgx : g x ∈ Set.Ioo (0 : ℝ) 1 := hg_range x
    rcases hgx with ⟨hlow, hhigh⟩
    have hpos : 0 < b - a := sub_pos.mpr h
    have ha_pos : a + (b - a) * g x > a := by nlinarith
    have hb_less : a + (b - a) * g x < b := by nlinarith
    exact ⟨ha_pos, hb_less⟩⟩ with hf
  have hf_inj : Function.Injective f := by
    intro x y h
    have hval : (f x : ℝ) = (f y : ℝ) := by simpa using congrArg Subtype.val h
    have : a + (b - a) * g x = a + (b - a) * g y := hval
    have hba_ne : b - a ≠ 0 := by nlinarith
    have : g x = g y := by nlinarith
    exact hg_inj this
  intro hcount
  have hcount_type : Countable (Set.Ioo a b) := Set.Countable.to_subtype hcount
  have : Countable ℝ := Function.Injective.countable hf_inj
  have : ¬ Countable ℝ := by
    intro hc
    have h' : Set.Countable (Set.univ : Set ℝ) := Set.countable_univ
    exact Set.not_countable_univ h'
  exact this ‹_›

/-- If a BoundedInterval has a closed underlying set, it must be of the form {lit}`Icc a b` (possibly empty). -/
lemma closed_eq_Icc_or_empty {I : BoundedInterval} (h : IsClosed I.toSet) : (∃ a b, I = Icc a b) ∨ (I.toSet = ∅) := by
  cases I with
  | Icc a b => left; exact ⟨a, b, rfl⟩
  | Ioo a b =>
    right
    simp [BoundedInterval.toSet] at h
    have hba : ¬ a < b := by linarith
    simp [BoundedInterval.toSet, Set.Ioo_eq_empty_iff.mpr hba]
  | Ioc a b =>
    right
    simp [BoundedInterval.toSet] at h
    have hba : ¬ a < b := by linarith
    simp [BoundedInterval.toSet, Set.Ioc_eq_empty_iff.mpr hba]
  | Ico a b =>
    right
    simp [BoundedInterval.toSet] at h
    have hba : ¬ a < b := by linarith
    simp [BoundedInterval.toSet, Set.Ico_eq_empty_iff.mpr hba]

/-- Exercise 1.2.10 (\[0,1) is not the countable union of pairwise disjoint closed intervals)-/
example : ¬ ∃ (I: ℕ → BoundedInterval), (∀ n, IsClosed (I n).toSet) ∧ (Set.univ.PairwiseDisjoint (fun n ↦ (I n).toSet) ) ∧ (⋃ n, (I n).toSet = Set.Ico 0 1) := by
  sorry

theorem Jordan_measurable.Lebesgue_measure {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: JordanMeasurable E) : Lebesgue_outer_measure E = (hE.measure : EReal) := by
  have hE_bounded : Bornology.IsBounded E := hE.1
  apply le_antisymm
  · calc
      Lebesgue_outer_measure E ≤ (Jordan_outer_measure E : EReal) := Lebesgue_outer_measure_le_Jordan hE_bounded
      _ = (hE.measure : EReal) := by
        simp [hE.eq_outer]
  · have h_nonempty : {m : ℝ | ∃ (A : Set (EuclideanSpace' d)) (hA : IsElementary A), A ⊆ E ∧ m = hA.measure}.Nonempty := by
      refine ⟨0, ∅, IsElementary.empty d, Set.empty_subset _, ?_⟩
      exact (IsElementary.measure_of_empty d).symm
    obtain ⟨B, hB, hB_superset⟩ := IsElementary.contains_bounded hE_bounded
    have h_B_bounds : BddAbove {m : ℝ | ∃ (A : Set (EuclideanSpace' d)) (hA : IsElementary A), A ⊆ E ∧ m = hA.measure} := by
      refine ⟨hB.measure, ?_⟩
      rintro m ⟨A, hA, hA_sub, rfl⟩
      exact IsElementary.measure_mono hA hB (Set.Subset.trans hA_sub hB_superset)
    have h_ineq_forall : ∀ ε' : ℝ, 0 < ε' → (hE.measure : EReal) < Lebesgue_outer_measure E + (ε' : EReal) := by
      intro ε' hε'_pos
      have h_exists : ∃ (A : Set (EuclideanSpace' d)) (hA : IsElementary A), A ⊆ E ∧ Jordan_inner_measure E - ε' < hA.measure := by
        have h_lt : Jordan_inner_measure E - ε' < Jordan_inner_measure E := by nlinarith
        rw [Jordan_inner_measure] at h_lt
        rcases exists_lt_of_lt_csSup h_nonempty h_lt with ⟨s, hs, hs_gt⟩
        rcases hs with ⟨A, hA, hA_sub, rfl⟩
        exact ⟨A, hA, hA_sub, hs_gt⟩
      rcases h_exists with ⟨A, hA, hA_sub, h_ineq⟩
      have h_ineq' : (Jordan_inner_measure E : EReal) < (hA.measure : EReal) + (ε' : EReal) := by
        have h_ineq_real : Jordan_inner_measure E < hA.measure + ε' := by nlinarith
        exact_mod_cast h_ineq_real
      have h_measure_A : (hA.measure : EReal) = Lebesgue_outer_measure A :=
        (Lebesgue_outer_measure.elementary A hA).symm
      have h_mono : Lebesgue_outer_measure A ≤ Lebesgue_outer_measure E :=
        Lebesgue_outer_measure.mono hA_sub
      calc
        (hE.measure : EReal) = (Jordan_inner_measure E : EReal) := by rfl
        _ < (hA.measure : EReal) + (ε' : EReal) := h_ineq'
        _ = Lebesgue_outer_measure A + (ε' : EReal) := by rw [h_measure_A]
        _ ≤ Lebesgue_outer_measure E + (ε' : EReal) := add_le_add_left h_mono (ε' : EReal)
    -- Deduce (hE.measure : EReal) ≤ Lebesgue_outer_measure E
    by_cases h_top : Lebesgue_outer_measure E = ⊤
    · rw [h_top]; exact le_top
    · -- Since EReal has 3 constructors (⊥, coe, ⊤), and we ruled out ⊤, it's either ⊥ or coe r
      have h_cases : Lebesgue_outer_measure E = ⊥ ∨ ∃ (r : ℝ), Lebesgue_outer_measure E = (r : EReal) := by
        by_cases h_bot : Lebesgue_outer_measure E = ⊥
        · exact Or.inl h_bot
        · have h_not_bot : Lebesgue_outer_measure E ≠ ⊥ := h_bot
          have h_not_top : Lebesgue_outer_measure E ≠ ⊤ := h_top
          -- The only remaining possibility is coe r
          have h_real : ∃ (s : ℝ), Lebesgue_outer_measure E = (s : EReal) := by
            -- Use the fact that EReal has 3 constructors
            have h_eq_or : Lebesgue_outer_measure E = ⊥ ∨ (∃ s : ℝ, Lebesgue_outer_measure E = (s : EReal)) ∨ Lebesgue_outer_measure E = ⊤ := by
              refine match Lebesgue_outer_measure E with
              | ⊥ => Or.inl rfl
              | (s : ℝ) => Or.inr (Or.inl ⟨s, rfl⟩)
              | ⊤ => Or.inr (Or.inr rfl)
            rcases h_eq_or with (h' | h' | h')
            · exact (h_not_bot h').elim
            · exact h'
            · exact (h_not_top h').elim
          exact Or.inr h_real
      rcases h_cases with (h_bot | ⟨r, hr⟩)
      · -- Lebesgue_outer_measure E = ⊥: impossible because h_ineq_forall gives (hE.measure : EReal) < ⊥
        have h_impossible : (hE.measure : EReal) < ⊥ := by
          have h := h_ineq_forall 1 (by norm_num : (0 : ℝ) < 1)
          rw [h_bot] at h
          -- h : (hE.measure : EReal) < ⊥ + (1 : ℝ)
          -- In EReal, ⊥ + a = ⊥ for any a
          have : (⊥ : EReal) + ((1 : ℝ) : EReal) = (⊥ : EReal) := by simp
          rw [this] at h
          exact h
        have h_nonneg_measure : 0 ≤ (hE.measure : EReal) := by
          exact_mod_cast JordanMeasurable.nonneg hE
        have h_bot_lt_zero : ⊥ < (0 : EReal) := EReal.bot_lt_zero
        have h_lt_zero : (hE.measure : EReal) < (0 : EReal) :=
          lt_trans h_impossible h_bot_lt_zero
        have : ¬ (0 : EReal) ≤ (hE.measure : EReal) := not_le.mpr h_lt_zero
        exact absurd h_nonneg_measure this
      · rw [hr]
        have h_ineq_reals : ∀ ε' : ℝ, 0 < ε' → hE.measure < r + ε' := by
          intro ε' hε'_pos
          have h := h_ineq_forall ε' hε'_pos
          rw [hr] at h
          have : (r : EReal) + (ε' : EReal) = ((r + ε' : ℝ) : EReal) := by simp
          rw [this] at h
          exact_mod_cast h
        have h_measure_le_r : hE.measure ≤ r := by
          by_contra! hgt
          set δ := hE.measure - r with hδ
          have hδ_pos : 0 < δ := sub_pos.mpr hgt
          have h := h_ineq_reals δ hδ_pos
          nlinarith
        exact_mod_cast h_measure_le_r

/-- Lemma 1.2.15(a) (Empty set has zero Lebesgue measure). The proof is missing. -/
@[simp]
theorem Lebesgue_measure.empty {d:ℕ} : Lebesgue_measure (∅: Set (EuclideanSpace' d)) = 0 :=
  -- Direct application of Lebesgue_outer_measure.of_empty since Lebesgue_measure = Lebesgue_outer_measure
  Lebesgue_outer_measure.of_empty d

/-- Helper: Countable additivity for compact sets.
    When all $`E_n` are compact and pairwise disjoint, $`m(⋃ E_n) = ∑' m(E_n)`.
    Key: compact disjoint sets have positive separation, so we can use Lemma 1.2.5. -/
private lemma Lebesgue_measure.countable_union_compact {d:ℕ} (hd : 0 < d)
    {E: ℕ → Set (EuclideanSpace' d)}
    (hcompact: ∀ n, IsCompact (E n))
    (hdisj: Set.univ.PairwiseDisjoint E) :
    Lebesgue_measure (⋃ n, E n) = ∑' n, Lebesgue_measure (E n) := by
  -- Direction ≤: Countable subadditivity
  have h_le : Lebesgue_measure (⋃ n, E n) ≤ ∑' n, Lebesgue_measure (E n) :=
    Lebesgue_outer_measure.union_le E
  -- Direction ≥: For each N, m(⋃_{n<N} E_n) = ∑_{n<N} m(E_n) by finite additivity + separation
  have h_ge : ∑' n, Lebesgue_measure (E n) ≤ Lebesgue_measure (⋃ n, E n) := by
    -- For each N, by induction, m(⋃_{n≤N} E_n) = ∑_{n≤N} m(E_n)
    have h_finite_sum : ∀ N : ℕ, Lebesgue_measure (⋃ n ∈ Finset.range N, E n) =
        ∑ n ∈ Finset.range N, Lebesgue_measure (E n) := by
      intro N
      induction N with
      | zero =>
        simp only [Finset.range_zero, Finset.sum_empty]
        -- ⋃ n ∈ ∅, E n = ∅
        have : (⋃ n ∈ (∅ : Finset ℕ), E n) = ∅ := by simp
        rw [this, Lebesgue_measure.empty]
      | succ N ih =>
        -- ⋃_{n<N+1} E_n = (⋃_{n<N} E_n) ∪ E_N
        have h_union_eq : (⋃ n ∈ Finset.range (N + 1), E n) =
            (⋃ n ∈ Finset.range N, E n) ∪ E N := by
          ext x
          simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_union]
          constructor
          · intro ⟨n, ⟨hn, hx⟩⟩
            by_cases hnN : n < N
            · left; exact ⟨n, ⟨hnN, hx⟩⟩
            · right
              have : n = N := Nat.eq_of_lt_succ_of_not_lt hn hnN
              rw [← this]; exact hx
          · intro h
            cases h with
            | inl hl =>
              obtain ⟨n, ⟨hn, hx⟩⟩ := hl
              exact ⟨n, ⟨Nat.lt_succ_of_lt hn, hx⟩⟩
            | inr hr => exact ⟨N, ⟨Nat.lt_succ_self N, hr⟩⟩
        rw [h_union_eq]
        -- The two parts are disjoint
        have h_disj_parts : (⋃ n ∈ Finset.range N, E n) ∩ E N = ∅ := by
          ext x
          simp only [Set.mem_inter_iff, Set.mem_iUnion, Finset.mem_range, Set.mem_empty_iff_false,
            iff_false, not_and]
          intro ⟨n, ⟨hn, hxn⟩⟩ hxN
          have hne : n ≠ N := Nat.ne_of_lt hn
          have hdisj_pair : Disjoint (E n) (E N) := hdisj (Set.mem_univ n) (Set.mem_univ N) hne
          exact Set.disjoint_iff.mp hdisj_pair ⟨hxn, hxN⟩
        -- The finite union is compact
        have hcompact_finite : IsCompact (⋃ n ∈ Finset.range N, E n) :=
          Finset.isCompact_biUnion _ (fun n _ => hcompact n)
        -- Use separation of compact disjoint sets
        by_cases h_empty_N : E N = ∅
        · -- If E_N is empty, the union doesn't change
          simp only [h_empty_N, Set.union_empty]
          rw [Finset.sum_range_succ, ih]
          simp [h_empty_N, Lebesgue_measure.empty]
        · by_cases h_empty_union : (⋃ n ∈ Finset.range N, E n) = ∅
          · simp only [h_empty_union, Set.empty_union, Finset.sum_range_succ]
            have h_sum_zero : ∑ n ∈ Finset.range N, Lebesgue_measure (E n) = 0 := by
              have h_all_empty : ∀ n ∈ Finset.range N, E n = ∅ := by
                intro n hn
                by_contra hne
                have hnonempty : (E n).Nonempty := Set.nonempty_iff_ne_empty.mpr hne
                have hsub : (E n) ⊆ ⋃ n ∈ Finset.range N, E n := Set.subset_biUnion_of_mem hn
                rw [h_empty_union] at hsub
                obtain ⟨x, hx⟩ := hnonempty
                exact Set.notMem_empty x (hsub hx)
              apply Finset.sum_eq_zero
              intro n hn
              rw [h_all_empty n hn, Lebesgue_measure.empty]
            rw [h_sum_zero, zero_add]
          · -- Both parts are nonempty compact and disjoint
            have h_nonempty_N : (E N).Nonempty := Set.nonempty_iff_ne_empty.mpr h_empty_N
            have h_nonempty_union : (⋃ n ∈ Finset.range N, E n).Nonempty :=
              Set.nonempty_iff_ne_empty.mpr h_empty_union
            have h_sep : set_dist (⋃ n ∈ Finset.range N, E n) (E N) > 0 :=
              dist_of_disj_compact_pos _ _ h_nonempty_union h_nonempty_N hcompact_finite (hcompact N) h_disj_parts
            have h_add := Lebesgue_outer_measure.union_of_separated hd h_sep
            -- h_add : Lebesgue_outer_measure (...) = Lebesgue_outer_measure (...) + Lebesgue_outer_measure (E N)
            -- Since Lebesgue_measure = Lebesgue_outer_measure, we can use this directly
            calc Lebesgue_measure ((⋃ n ∈ Finset.range N, E n) ∪ E N)
                = Lebesgue_outer_measure ((⋃ n ∈ Finset.range N, E n) ∪ E N) := rfl
              _ = Lebesgue_outer_measure (⋃ n ∈ Finset.range N, E n) + Lebesgue_outer_measure (E N) := h_add
              _ = Lebesgue_measure (⋃ n ∈ Finset.range N, E n) + Lebesgue_measure (E N) := rfl
              _ = ∑ n ∈ Finset.range N, Lebesgue_measure (E n) + Lebesgue_measure (E N) := by rw [ih]
              _ = ∑ n ∈ Finset.range (N + 1), Lebesgue_measure (E n) := by rw [Finset.sum_range_succ]
    -- Now: ∑' m(E_n) = sup_N ∑_{n < N} m(E_n) ≤ sup_N m(⋃_{n < N} E_n) ≤ m(⋃ E_n)
    have h_mono : ∀ N : ℕ, (⋃ n ∈ Finset.range N, E n) ⊆ (⋃ n, E n) := by
      intro N x hx
      simp only [Set.mem_iUnion, Finset.mem_range] at hx ⊢
      obtain ⟨n, ⟨_, hxn⟩⟩ := hx
      exact ⟨n, hxn⟩
    have h_sum_le : ∀ N : ℕ, ∑ n ∈ Finset.range N, Lebesgue_measure (E n) ≤
        Lebesgue_measure (⋃ n, E n) := by
      intro N
      rw [← h_finite_sum N]
      exact Lebesgue_outer_measure.mono (h_mono N)
    -- All measures are nonnegative (by definition of outer measure)
    have h_nn : ∀ n, 0 ≤ Lebesgue_measure (E n) := fun _ => Lebesgue_outer_measure.nonneg _
    exact EReal.tsum_le_of_sum_range_le_of_nonneg h_nn h_sum_le
  exact le_antisymm h_le h_ge

/-- Helper: Countable additivity for bounded sets.
    Following the textbook approach: Use ε/2ⁿ trick with inner regularity (Exercise 1.2.7).
    For bounded measurable $`E_n`, find compact $`K_n ⊆ E_n` with $`m(E_n) ≤ m(K_n) + ε/2^(n+1)`.
    The $`K_n` are pairwise disjoint (since $`K_n ⊆ E_n`), so $`m(⋃ K_n) = ∑' m(K_n)` by compact case,
    and $`m(⋃ E_n) ≥ m(⋃ K_n) = ∑' m(K_n) ≥ ∑' m(E_n) - ε`. Let ε → 0. -/
private lemma Lebesgue_measure.countable_union_bounded {d:ℕ} (hd : 0 < d)
    {E: ℕ → Set (EuclideanSpace' d)}
    (hmes: ∀ n, LebesgueMeasurable (E n))
    (hbdd: ∀ n, Bornology.IsBounded (E n))
    (hdisj: Set.univ.PairwiseDisjoint E) :
    Lebesgue_measure (⋃ n, E n) = ∑' n, Lebesgue_measure (E n) := by
  -- Direction ≤: Countable subadditivity (always holds)
  have h_le : Lebesgue_measure (⋃ n, E n) ≤ ∑' n, Lebesgue_measure (E n) :=
    Lebesgue_outer_measure.union_le E
  -- Direction ≥: Use ε/2ⁿ trick with compact approximation
  have h_ge : ∑' n, Lebesgue_measure (E n) ≤ Lebesgue_measure (⋃ n, E n) := by
    -- Each bounded set has finite measure
    have h_finite : ∀ n, Lebesgue_measure (E n) ≠ ⊤ := by
      intro n
      have h_closure_compact : IsCompact (closure (E n)) :=
        Metric.isCompact_of_isClosed_isBounded isClosed_closure (hbdd n).closure
      have h_closure_finite : Lebesgue_measure (closure (E n)) ≠ ⊤ :=
        Lebesgue_outer_measure.finite_of_compact h_closure_compact
      have h_mono_closure : Lebesgue_measure (E n) ≤ Lebesgue_measure (closure (E n)) :=
        Lebesgue_outer_measure.mono subset_closure
      intro h_eq_top
      rw [h_eq_top] at h_mono_closure
      exact h_closure_finite (eq_top_iff.mpr h_mono_closure)
    -- Use ε-characterization: prove ∑' m(E_n) ≤ m(⋃ E_n) + ε for all ε > 0
    apply EReal.le_of_forall_pos_le_add'
    intro ε hε
    -- Extract TFAE condition (4): inner approximation by closed sets
    have h_TFAE := fun n => LebesgueMeasurable.TFAE (E n)
    -- Condition (1) → Condition (4): For measurable E, closed F ⊆ E with m(E \ F) ≤ δ
    have h_inner : ∀ n, ∀ δ > (0 : EReal), ∃ F : Set (EuclideanSpace' d),
        IsClosed F ∧ F ⊆ E n ∧ Lebesgue_outer_measure (E n \ F) ≤ δ := by
      intro n δ hδ
      have h_tfae := h_TFAE n
      -- TFAE gives us: (1) ↔ (4)
      -- Condition (1) is hmes n : LebesgueMeasurable (E n)
      -- Condition (4) is ∀ ε > 0, ∃ F closed, F ⊆ E, m(E \ F) ≤ ε
      have h_14 : LebesgueMeasurable (E n) →
          (∀ ε > 0, ∃ F : Set (EuclideanSpace' d), IsClosed F ∧ F ⊆ E n ∧
            Lebesgue_outer_measure (E n \ F) ≤ ε) := by
        have := List.TFAE.out h_tfae 0 3
        exact this.mp
      exact h_14 (hmes n) δ hδ
    -- Choose ε_n = ε / 2^{n+1} for each n
    -- For each n, get compact K_n ⊆ E_n with m(E_n) ≤ m(K_n) + ε/2^{n+1}
    have h_eps_pos : ∀ n, (0 : EReal) < ε / 2^(n+1) := by
      intro n
      have h_pow_pos : (0 : ℝ) < 2^(n+1) := by positivity
      have h_eps_over_pow : (0 : ℝ) < ε / 2^(n+1) := by positivity
      -- ε/2^(n+1) > 0 by straightforward calculation
      calc (0 : EReal) < (ε / 2^(n+1) : ℝ) := EReal.coe_pos.mpr h_eps_over_pow
        _ = (ε : EReal) / (2^(n+1) : ℝ) := by rw [EReal.coe_div]
        _ = (ε : EReal) / (2 : EReal)^(n+1) := by simp only [EReal.coe_pow]; rfl
    choose F hF using fun n => h_inner n (ε / 2^(n+1)) (h_eps_pos n)
    -- F_n is closed (from h_inner), bounded (since F_n ⊆ E_n and E_n bounded), hence compact
    have hF_compact : ∀ n, IsCompact (F n) := by
      intro n
      have hF_closed : IsClosed (F n) := (hF n).1
      have hF_bdd : Bornology.IsBounded (F n) :=
        Bornology.IsBounded.subset (hbdd n) (hF n).2.1
      exact Metric.isCompact_of_isClosed_isBounded hF_closed hF_bdd
    -- F_n are pairwise disjoint (since F_n ⊆ E_n and E_n are pairwise disjoint)
    have hF_disj : Set.univ.PairwiseDisjoint F := by
      intro i _ j _ hij
      have hE_disj : Disjoint (E i) (E j) := hdisj (Set.mem_univ i) (Set.mem_univ j) hij
      exact Set.disjoint_of_subset_left (hF i).2.1 (Set.disjoint_of_subset_right (hF j).2.1 hE_disj)
    -- By the compact case: m(⋃ F_n) = ∑' m(F_n)
    have h_compact_case : Lebesgue_measure (⋃ n, F n) = ∑' n, Lebesgue_measure (F n) :=
      Lebesgue_measure.countable_union_compact hd hF_compact hF_disj
    -- Key inequality: m(E_n) ≤ m(F_n) + ε/2^{n+1}
    have h_approx : ∀ n, Lebesgue_measure (E n) ≤ Lebesgue_measure (F n) + ε / 2^(n+1) := by
      intro n
      -- E_n = F_n ∪ (E_n \ F_n), and F_n ⊆ E_n
      -- By monotonicity and subadditivity: m(E_n) ≤ m(F_n) + m(E_n \ F_n) ≤ m(F_n) + ε/2^{n+1}
      have h_partition : E n = F n ∪ (E n \ F n) := (Set.union_diff_cancel (hF n).2.1).symm
      -- Binary subadditivity: m(A ∪ B) ≤ m(A) + m(B)
      have h_binary_subadd : Lebesgue_measure (F n ∪ (E n \ F n)) ≤
          Lebesgue_measure (F n) + Lebesgue_measure (E n \ F n) := by
        -- Use finite_union_le with Fin 2
        let S : Fin 2 → Set (EuclideanSpace' d) := ![F n, E n \ F n]
        have h_eq : F n ∪ (E n \ F n) = ⋃ i : Fin 2, S i := by
          ext x
          simp only [Set.mem_union, Set.mem_iUnion, S]
          constructor
          · intro h
            cases h with
            | inl hF => exact ⟨0, by simp [hF]⟩
            | inr hDiff => exact ⟨1, by simp [hDiff]⟩
          · intro ⟨i, hi⟩
            fin_cases i
            · left; exact hi
            · right; exact hi
        rw [h_eq]
        calc Lebesgue_measure (⋃ i : Fin 2, S i)
            ≤ ∑ i : Fin 2, Lebesgue_outer_measure (S i) := Lebesgue_outer_measure.finite_union_le S
          _ = Lebesgue_outer_measure (S 0) + Lebesgue_outer_measure (S 1) := Fin.sum_univ_two _
          _ = Lebesgue_measure (F n) + Lebesgue_measure (E n \ F n) := by simp only [S]; rfl
      calc Lebesgue_measure (E n) = Lebesgue_measure (F n ∪ (E n \ F n)) := by
            conv_lhs => rw [h_partition]
        _ ≤ Lebesgue_measure (F n) + Lebesgue_measure (E n \ F n) := h_binary_subadd
        _ ≤ Lebesgue_measure (F n) + ε / 2^(n+1) := by
          apply add_le_add_right
          exact (hF n).2.2
    -- Sum the approximations: ∑' m(E_n) ≤ ∑' m(F_n) + ∑' (ε/2^{n+1}) = ∑' m(F_n) + ε
    have h_sum_eps : ∑' n, (ε / (2 : EReal)^(n+1)) = ε := by
      -- ∑_{n=0}^∞ ε/2^{n+1} = ε · ∑_{n=0}^∞ 1/2^{n+1} = ε · 1 = ε
      -- First show (2 : EReal)^k = ((2^k : ℝ) : EReal) by induction
      have h2_eq : ∀ k : ℕ, (2 : EReal) ^ k = ((2 ^ k : ℝ) : EReal) := by
        intro k
        induction k with
        | zero => simp
        | succ k ih => simp only [pow_succ]; rw [ih]; push_cast; rfl
      -- Show EReal division equals Real division coerced
      have h_eq : ∀ n, (ε : EReal) / (2 : EReal) ^ (n + 1) = ((ε / (2 : ℝ)^(n+1)) : ℝ) := fun n => by
        rw [h2_eq (n + 1), ← EReal.coe_div]
      -- Summability and non-negativity for Real series
      have h_nn : ∀ n, 0 ≤ ε / (2 : ℝ)^(n+1) := fun n => by positivity
      have h_sum : Summable (fun n => ε / (2 : ℝ)^(n+1)) := by
        have h_eq_fn : (fun n => ε / (2 : ℝ)^(n+1)) = (fun n => ε/2 * (1/2 : ℝ)^n) := by
          ext n
          have h2 : (2 : ℝ) ^ (n+1) = 2 * 2^n := by ring
          field_simp [h2]; ring_nf; simp
        rw [h_eq_fn]
        exact summable_geometric_two.mul_left (ε/2)
      simp_rw [h_eq, ← EReal.coe_tsum_of_nonneg h_nn h_sum, tsum_geometric_eps ε hε]
    -- ∑' m(E_n) ≤ ∑' m(F_n) + ε
    have h_tsum_approx : ∑' n, Lebesgue_measure (E n) ≤ ∑' n, Lebesgue_measure (F n) + ε := by
      -- Lift to ENNReal where tsum_le_tsum and tsum_add work cleanly
      let mE_enn : ℕ → ENNReal := fun n => (Lebesgue_measure (E n)).toENNReal
      let mF_enn : ℕ → ENNReal := fun n => (Lebesgue_measure (F n)).toENNReal
      let eps_enn : ℕ → ENNReal := fun n => ((ε : EReal) / 2 ^ (n + 1)).toENNReal
      have h_mE_nn : ∀ n, 0 ≤ Lebesgue_measure (E n) := fun n => Lebesgue_outer_measure.nonneg (E n)
      have h_mF_nn : ∀ n, 0 ≤ Lebesgue_measure (F n) := fun n => Lebesgue_outer_measure.nonneg (F n)
      have h_eps_nn : ∀ n, (0 : EReal) ≤ (ε : EReal) / 2 ^ (n + 1) := fun n => le_of_lt (h_eps_pos n)
      -- Coerce back: x = x.toENNReal for non-negative EReal
      have h_mE_coe : ∀ n, Lebesgue_measure (E n) = (mE_enn n : EReal) := fun n =>
        (EReal.coe_toENNReal (h_mE_nn n)).symm
      have h_mF_coe : ∀ n, Lebesgue_measure (F n) = (mF_enn n : EReal) := fun n =>
        (EReal.coe_toENNReal (h_mF_nn n)).symm
      have h_eps_coe : ∀ n, (ε : EReal) / 2 ^ (n + 1) = (eps_enn n : EReal) := fun n =>
        (EReal.coe_toENNReal (h_eps_nn n)).symm
      -- In ENNReal: h_approx gives mE_enn n ≤ mF_enn n + eps_enn n
      have h_approx_enn : ∀ n, mE_enn n ≤ mF_enn n + eps_enn n := by
        intro n
        have h := h_approx n
        rw [h_mE_coe, h_mF_coe, h_eps_coe] at h
        rw [← EReal.coe_ennreal_add] at h
        exact EReal.coe_ennreal_le_coe_ennreal_iff.mp h
      -- ENNReal tsum_le_tsum: ∑' mE_enn ≤ ∑' (mF_enn + eps_enn)
      have h_tsum_le : ∑' n, mE_enn n ≤ ∑' n, (mF_enn n + eps_enn n) :=
        ENNReal.tsum_le_tsum h_approx_enn
      -- ENNReal tsum_add: ∑' (mF_enn + eps_enn) = ∑' mF_enn + ∑' eps_enn
      have h_tsum_add : ∑' n, (mF_enn n + eps_enn n) = ∑' n, mF_enn n + ∑' n, eps_enn n :=
        ENNReal.tsum_add
      -- Coerce back to EReal
      simp_rw [h_mE_coe, h_mF_coe]
      -- Use continuous coercion to lift tsum results
      have h_cont : Continuous (fun x : ENNReal => (x : EReal)) := continuous_coe_ennreal_ereal
      let φ : ENNReal →+ EReal := {
        toFun := (↑·)
        map_zero' := rfl
        map_add' := EReal.coe_ennreal_add
      }
      have h_tsum_mE : ∑' n, (mE_enn n : EReal) = φ (∑' n, mE_enn n) :=
        (Summable.map_tsum ENNReal.summable φ h_cont).symm
      have h_tsum_mF : ∑' n, (mF_enn n : EReal) = φ (∑' n, mF_enn n) :=
        (Summable.map_tsum ENNReal.summable φ h_cont).symm
      have h_tsum_eps : ∑' n, (eps_enn n : EReal) = φ (∑' n, eps_enn n) :=
        (Summable.map_tsum ENNReal.summable φ h_cont).symm
      rw [h_tsum_mE, h_tsum_mF]
      -- Show φ (∑' mE_enn) ≤ φ (∑' mF_enn) + ε
      calc φ (∑' n, mE_enn n)
          ≤ φ (∑' n, (mF_enn n + eps_enn n)) := by
            apply EReal.coe_ennreal_le_coe_ennreal_iff.mpr h_tsum_le
        _ = φ (∑' n, mF_enn n + ∑' n, eps_enn n) := by rw [h_tsum_add]
        _ = φ (∑' n, mF_enn n) + φ (∑' n, eps_enn n) := φ.map_add _ _
        _ = φ (∑' n, mF_enn n) + ∑' n, (eps_enn n : EReal) := by rw [← h_tsum_eps]
        _ = φ (∑' n, mF_enn n) + ∑' n, (ε : EReal) / 2 ^ (n + 1) := by simp_rw [← h_eps_coe]
        _ = φ (∑' n, mF_enn n) + ε := by rw [h_sum_eps]
    -- m(⋃ F_n) ≤ m(⋃ E_n) by monotonicity (since F_n ⊆ E_n)
    have h_union_mono : Lebesgue_measure (⋃ n, F n) ≤ Lebesgue_measure (⋃ n, E n) := by
      apply Lebesgue_outer_measure.mono
      apply Set.iUnion_mono
      intro n
      exact (hF n).2.1
    -- Combine: ∑' m(E_n) ≤ ∑' m(F_n) + ε = m(⋃ F_n) + ε ≤ m(⋃ E_n) + ε
    calc ∑' n, Lebesgue_measure (E n)
        ≤ ∑' n, Lebesgue_measure (F n) + ε := h_tsum_approx
      _ = Lebesgue_measure (⋃ n, F n) + ε := by rw [h_compact_case]
      _ ≤ Lebesgue_measure (⋃ n, E n) + ε := add_le_add_left h_union_mono ε
  exact le_antisymm h_le h_ge

/-- Lemma 1.2.15(b) (Countable additivity).
    Strategy: `m(⋃ E_n) = ∑' m(E_n)` for pairwise disjoint measurable sets.
    - Direction ≤: Countable subadditivity ({name}`Lebesgue_outer_measure.union_le`)
    - Direction ≥: Decompose ℝᵈ into annuli Aₘ, express each `E_n = ⋃_m (E_n ∩ Aₘ)`,
      apply bounded case to the doubly-indexed family $`(E_n ∩ Aₘ)`. -/
theorem Lebesgue_measure.countable_union {d:ℕ} {E: ℕ → Set (EuclideanSpace' d)} (hmes: ∀ n, LebesgueMeasurable (E n)) (hdisj: Set.univ.PairwiseDisjoint E) : Lebesgue_measure (⋃ n, E n) = ∑' n, Lebesgue_measure (E n) := by
  -- Direction ≤: Countable subadditivity
  have h_le : Lebesgue_measure (⋃ n, E n) ≤ ∑' n, Lebesgue_measure (E n) :=
    Lebesgue_outer_measure.union_le E
  -- Direction ≥: Use annuli decomposition for general case
  have h_ge : ∑' n, Lebesgue_measure (E n) ≤ Lebesgue_measure (⋃ n, E n) := by
    -- Handle d = 0 case separately (trivial)
    by_cases hd : d = 0
    · -- In dimension 0, the space is a singleton (Subsingleton), so any pairwise disjoint
      -- family has at most one nonempty set. The sum equals the measure of the union.
      subst hd
      haveI : Subsingleton (EuclideanSpace' 0) := inferInstance
      -- Each E n is either ∅ or univ (the singleton). For disjoint sets, at most one is nonempty.
      by_cases h_empty : ∀ n, E n = ∅
      · -- All sets are empty: both sides are 0
        simp_rw [h_empty, Set.iUnion_empty]
        simp only [Lebesgue_measure.empty, tsum_zero, le_refl]
      · -- At least one E n is nonempty; by disjointness in a subsingleton, exactly one
        push_neg at h_empty
        obtain ⟨n₀, hn₀⟩ := h_empty
        -- In a Subsingleton, a nonempty set equals univ
        have hE_univ : E n₀ = Set.univ := by
          ext x
          simp only [Set.mem_univ, iff_true]
          exact Subsingleton.mem_iff_nonempty.mpr hn₀
        -- All other E m must be empty (disjoint from E n₀ = univ)
        have hE_empty : ∀ m, m ≠ n₀ → E m = ∅ := by
          intro m hm
          have hdisj' : Disjoint (E n₀) (E m) := hdisj (Set.mem_univ n₀) (Set.mem_univ m) hm.symm
          rw [hE_univ, Set.disjoint_iff] at hdisj'
          ext x
          simp only [Set.mem_empty_iff_false, iff_false]
          intro hx
          have : x ∈ Set.univ ∩ E m := ⟨Set.mem_univ x, hx⟩
          exact Set.notMem_empty x (hdisj' this)
        -- The union equals E n₀
        have h_union : (⋃ n, E n) = E n₀ := by
          ext x
          simp only [Set.mem_iUnion]
          constructor
          · intro ⟨n, hxn⟩
            by_cases hn : n = n₀
            · exact hn ▸ hxn
            · rw [hE_empty n hn] at hxn
              exact (Set.notMem_empty x hxn).elim
          · intro hx
            exact ⟨n₀, hx⟩
        -- The sum has only one nonzero term
        have h_sum : ∑' n, Lebesgue_measure (E n) = Lebesgue_measure (E n₀) := by
          apply tsum_eq_single n₀
          intro m hm
          rw [hE_empty m hm, Lebesgue_measure.empty]
        rw [h_sum, h_union]
    · -- For d ≥ 1, use the annuli decomposition from the textbook
      push_neg at hd
      have hd_pos : 0 < d := Nat.pos_of_ne_zero hd
      -- Define annuli: A_m = { x : m ≤ |x| < m+1 } for m ≥ 0
      -- Then ℝᵈ = ⋃_m A_m (disjoint union) and each A_m is bounded
      let A : ℕ → Set (EuclideanSpace' d) := fun m =>
        { x | (m : ℝ) ≤ ‖x‖ ∧ ‖x‖ < m + 1 }
      -- Each annulus is bounded
      have hA_bdd : ∀ m, Bornology.IsBounded (A m) := by
        intro m
        rw [Metric.isBounded_iff_subset_closedBall 0]
        use m + 1
        intro x hx
        simp only [Metric.mem_closedBall, dist_zero_right, A, Set.mem_setOf_eq] at hx ⊢
        exact le_of_lt hx.2
      -- The annuli cover all of ℝᵈ
      have hA_cover : ∀ x : EuclideanSpace' d, ∃ m, x ∈ A m := by
        intro x
        use ⌊‖x‖⌋₊
        simp only [A, Set.mem_setOf_eq]
        constructor
        · exact Nat.floor_le (norm_nonneg x)
        · exact Nat.lt_floor_add_one ‖x‖
      -- The annuli are pairwise disjoint
      have hA_disj : Set.univ.PairwiseDisjoint A := by
        intro i _ j _ hij
        simp only [Function.onFun, Set.disjoint_iff]
        intro x ⟨hi, hj⟩
        simp only [A, Set.mem_setOf_eq, Set.mem_empty_iff_false] at hi hj ⊢
        by_cases h : i < j
        · have h1 : (j : ℝ) ≤ ‖x‖ := hj.1
          have h2 : ‖x‖ < i + 1 := hi.2
          have h3 : (j : ℝ) < i + 1 := lt_of_le_of_lt h1 h2
          have h4 : j < i + 1 := by exact_mod_cast h3
          omega
        · push_neg at h
          have hji : j < i := lt_of_le_of_ne h (Ne.symm hij)
          have h1 : (i : ℝ) ≤ ‖x‖ := hi.1
          have h2 : ‖x‖ < j + 1 := hj.2
          have h3 : (i : ℝ) < j + 1 := lt_of_le_of_lt h1 h2
          have h4 : i < j + 1 := by exact_mod_cast h3
          omega
      -- Define the doubly-indexed family E'(n,m) = E_n ∩ A_m
      let E' : ℕ × ℕ → Set (EuclideanSpace' d) := fun ⟨n, m⟩ => E n ∩ A m
      -- E' is measurable (intersection of measurable and Borel sets)
      have hE'_mes : ∀ p, LebesgueMeasurable (E' p) := by
        intro ⟨n, m⟩
        -- E n is measurable, A m is Borel (hence measurable)
        have hA_meas : LebesgueMeasurable (A m) := by
          -- A m = { x | m ≤ ‖x‖ } ∩ { x | ‖x‖ < m + 1 }
          -- { x | m ≤ ‖x‖ } is closed, { x | ‖x‖ < m + 1 } is open
          have h1 : IsClosed { x : EuclideanSpace' d | (m : ℝ) ≤ ‖x‖ } :=
            isClosed_le continuous_const continuous_norm
          have h2 : IsOpen { x : EuclideanSpace' d | ‖x‖ < (m : ℝ) + 1 } :=
            isOpen_lt continuous_norm continuous_const
          have heq : A m = { x | (m : ℝ) ≤ ‖x‖ } ∩ { x | ‖x‖ < (m : ℝ) + 1 } := by
            ext x; simp only [A, Set.mem_setOf_eq, Set.mem_inter_iff]
          rw [heq]
          exact LebesgueMeasurable.inter h1.measurable h2.measurable
        exact LebesgueMeasurable.inter (hmes n) hA_meas
      -- E' is bounded (subset of bounded A_m)
      have hE'_bdd : ∀ p, Bornology.IsBounded (E' p) := by
        intro ⟨n, m⟩
        exact Bornology.IsBounded.subset (hA_bdd m) Set.inter_subset_right
      -- E' is pairwise disjoint
      have hE'_disj : Set.univ.PairwiseDisjoint E' := by
        intro ⟨n₁, m₁⟩ _ ⟨n₂, m₂⟩ _ hne
        simp only [E', Function.onFun]
        by_cases hn : n₁ = n₂
        · -- Same n, different m: disjoint by annuli
          subst hn
          have hm : m₁ ≠ m₂ := by
            intro heq
            exact hne (Prod.ext rfl heq)
          have hA_disj' : Disjoint (A m₁) (A m₂) :=
            hA_disj (Set.mem_univ m₁) (Set.mem_univ m₂) hm
          exact Set.disjoint_of_subset_left Set.inter_subset_right
            (Set.disjoint_of_subset_right Set.inter_subset_right hA_disj')
        · -- Different n: disjoint by original family
          have hE_disj' : Disjoint (E n₁) (E n₂) :=
            hdisj (Set.mem_univ n₁) (Set.mem_univ n₂) hn
          exact Set.disjoint_of_subset_left Set.inter_subset_left
            (Set.disjoint_of_subset_right Set.inter_subset_left hE_disj')
      -- ⋃_n E_n = ⋃_p E' p (reindex the union)
      have h_union_eq : (⋃ n, E n) = ⋃ p, E' p := by
        ext x
        simp only [Set.mem_iUnion, E']
        constructor
        · intro ⟨n, hx⟩
          obtain ⟨m, hm⟩ := hA_cover x
          exact ⟨⟨n, m⟩, ⟨hx, hm⟩⟩
        · intro ⟨⟨n, m⟩, hx⟩
          exact ⟨n, hx.1⟩
      -- Apply countable_union_bounded to E' (reindexed as ℕ via equivalence ℕ × ℕ ≃ ℕ)
      -- Step 1: Reindex E' to E'' : ℕ → Set using Nat.pairEquiv
      let e := Nat.pairEquiv.symm  -- e : ℕ ≃ ℕ × ℕ
      let E'' : ℕ → Set (EuclideanSpace' d) := fun k => E' (e k)
      -- Step 2: E'' inherits measurability, boundedness, and disjointness
      have hE''_mes : ∀ k, LebesgueMeasurable (E'' k) := fun k => hE'_mes (e k)
      have hE''_bdd : ∀ k, Bornology.IsBounded (E'' k) := fun k => hE'_bdd (e k)
      have hE''_disj : Set.univ.PairwiseDisjoint E'' := by
        intro i _ j _ hij
        simp only [E'', Function.onFun]
        have hne : e i ≠ e j := by
          intro heq
          apply hij
          exact e.injective heq
        exact hE'_disj (Set.mem_univ (e i)) (Set.mem_univ (e j)) hne
      -- Step 3: The unions are equal
      have h_union_E'' : (⋃ p, E' p) = ⋃ k, E'' k := by
        ext x
        simp only [Set.mem_iUnion, E'']
        constructor
        · intro ⟨p, hp⟩
          use e.symm p
          simp [hp]
        · intro ⟨k, hk⟩
          use e k
      -- Step 4: Apply countable_union_bounded to E''
      have h_E''_eq : Lebesgue_measure (⋃ k, E'' k) = ∑' k, Lebesgue_measure (E'' k) :=
        Lebesgue_measure.countable_union_bounded hd_pos hE''_mes hE''_bdd hE''_disj
      -- Step 5: Relate sums: ∑' k, m(E'' k) = ∑' p, m(E' p) by reindexing
      have h_tsum_reindex : ∑' k, Lebesgue_measure (E'' k) = ∑' p, Lebesgue_measure (E' p) := by
        rw [show (∑' p, Lebesgue_measure (E' p)) = ∑' k, Lebesgue_measure (E' (e k)) from
          (Equiv.tsum_eq e (fun p => Lebesgue_measure (E' p))).symm]
      -- Step 6: Relate ∑' n, m(E n) to ∑' p, m(E' p)
      -- Each E n = ⋃ k, (E n ∩ A k) is a disjoint union of bounded measurable sets
      -- So m(E n) = ∑' k, m(E n ∩ A k) by countable_union_bounded
      have h_En_decomp : ∀ n, Lebesgue_measure (E n) = ∑' k, Lebesgue_measure (E n ∩ A k) := by
        intro n
        -- Define the family for fixed n
        let F : ℕ → Set (EuclideanSpace' d) := fun k => E n ∩ A k
        have hF_eq : E n = ⋃ k, F k := by
          ext x
          simp only [F, Set.mem_iUnion, Set.mem_inter_iff]
          constructor
          · intro hx
            obtain ⟨k, hk⟩ := hA_cover x
            exact ⟨k, hx, hk⟩
          · intro ⟨k, hx, _⟩
            exact hx
        have hF_mes : ∀ k, LebesgueMeasurable (F k) := fun k => hE'_mes (n, k)
        have hF_bdd : ∀ k, Bornology.IsBounded (F k) := fun k => hE'_bdd (n, k)
        have hF_disj : Set.univ.PairwiseDisjoint F := by
          intro k₁ _ k₂ _ hk
          simp only [F, Function.onFun]
          have hA_disj' : Disjoint (A k₁) (A k₂) :=
            hA_disj (Set.mem_univ k₁) (Set.mem_univ k₂) hk
          exact Set.disjoint_of_subset_right Set.inter_subset_right
            (Set.disjoint_of_subset_left Set.inter_subset_right hA_disj')
        calc Lebesgue_measure (E n)
            = Lebesgue_measure (⋃ k, F k) := by rw [hF_eq]
          _ = ∑' k, Lebesgue_measure (F k) :=
              Lebesgue_measure.countable_union_bounded hd_pos hF_mes hF_bdd hF_disj
          _ = ∑' k, Lebesgue_measure (E n ∩ A k) := rfl
      -- Step 7: Now relate the double sum to the product sum
      -- ∑' n, m(E n) = ∑' n, ∑' k, m(E n ∩ A k) = ∑' (n,k), m(E n ∩ A k) = ∑' p, m(E' p)
      have h_sum_eq : ∑' n, Lebesgue_measure (E n) = ∑' p, Lebesgue_measure (E' p) := by
        simp_rw [h_En_decomp]
        -- Need: ∑' n, ∑' k, m(E n ∩ A k) = ∑' p, m(E' p)
        -- Simplify the inner sums to use E'
        have h_eq : ∀ n k, Lebesgue_measure (E n ∩ A k) = Lebesgue_measure (E' (n, k)) := by
          intro n k; simp only [E']
        simp_rw [h_eq]
        -- Now need: ∑' n, ∑' k, m(E' (n, k)) = ∑' p, m(E' p)
        -- Lift to ENNReal where tsum_prod' works unconditionally
        -- Define ENNReal version: f_enn p = m(E' p).toENNReal
        let f_enn : ℕ × ℕ → ENNReal := fun p => (Lebesgue_measure (E' p)).toENNReal
        -- Lebesgue measure is non-negative, so toENNReal is well-defined
        have hf_nn : ∀ p, 0 ≤ Lebesgue_measure (E' p) := fun p => Lebesgue_outer_measure.nonneg (E' p)
        -- ENNReal.tsum_prod' gives: ∑' p, f_enn p = ∑' n, ∑' k, f_enn (n, k)
        have h_enn_prod : ∑' n, ∑' k, f_enn (n, k) = ∑' p, f_enn p := ENNReal.tsum_prod'.symm
        -- Coerce back to EReal: For non-negative EReal, x = (x.toENNReal : EReal)
        have h_coe : ∀ p, Lebesgue_measure (E' p) = (f_enn p : EReal) := by
          intro p
          simp only [f_enn]
          exact (EReal.coe_toENNReal (hf_nn p)).symm
        simp_rw [h_coe]
        -- Now need: ∑' n, ∑' k, (f_enn (n, k) : EReal) = ∑' p, (f_enn p : EReal)
        -- Use continuous coercion from ENNReal to EReal
        have h_cont : Continuous (fun x : ENNReal => (x : EReal)) := continuous_coe_ennreal_ereal
        -- Define coercion as AddMonoidHom
        let φ : ENNReal →+ EReal := {
          toFun := (↑·)
          map_zero' := rfl
          map_add' := EReal.coe_ennreal_add
        }
        -- Map tsum through coercion using Summable.map_tsum
        -- For ENNReal, Summable always holds
        have h_map_outer : ∑' p, (f_enn p : EReal) = φ (∑' p, f_enn p) :=
          (Summable.map_tsum ENNReal.summable φ h_cont).symm
        have h_map_inner : ∀ n, ∑' k, (f_enn (n, k) : EReal) = φ (∑' k, f_enn (n, k)) := by
          intro n
          exact (Summable.map_tsum ENNReal.summable φ h_cont).symm
        have h_map_double : ∑' n, φ (∑' k, f_enn (n, k)) = φ (∑' n, ∑' k, f_enn (n, k)) :=
          (Summable.map_tsum ENNReal.summable φ h_cont).symm
        simp_rw [h_map_inner]
        rw [h_map_double, h_map_outer, h_enn_prod]
      -- Final step: combine everything
      calc ∑' n, Lebesgue_measure (E n)
          = ∑' p, Lebesgue_measure (E' p) := h_sum_eq
        _ = ∑' k, Lebesgue_measure (E'' k) := h_tsum_reindex.symm
        _ = Lebesgue_measure (⋃ k, E'' k) := h_E''_eq.symm
        _ = Lebesgue_measure (⋃ p, E' p) := by rw [← h_union_E'']
        _ = Lebesgue_measure (⋃ n, E n) := by rw [← h_union_eq]
        _ ≤ Lebesgue_measure (⋃ n, E n) := le_refl _
  exact le_antisymm h_le h_ge

theorem Lebesgue_measure.finite_union {d n:ℕ} {E: Fin n → Set (EuclideanSpace' d)} (hmes: ∀ n, LebesgueMeasurable (E n)) (hdisj: Set.univ.PairwiseDisjoint E) : Lebesgue_measure (⋃ n, E n) = ∑' n, Lebesgue_measure (E n) := by
  -- Strategy: Extend E to ℕ-indexed family by padding with empty sets, then use countable_union
  -- Define E' : ℕ → Set by E'(k) = E(k) if k < n, else ∅
  let E' : ℕ → Set (EuclideanSpace' d) := fun k =>
    if h : k < n then E ⟨k, h⟩ else ∅

  -- The union over Fin n equals the union over ℕ with E'
  have h_union : (⋃ i : Fin n, E i) = (⋃ k, E' k) := by
    ext x
    simp only [Set.mem_iUnion, E']
    constructor
    · intro ⟨i, hi⟩
      use i.val
      simp [hi]
    · intro ⟨k, hx⟩
      by_cases hk : k < n
      · use ⟨k, hk⟩
        simpa [dif_pos hk] using hx
      · simp [dif_neg hk] at hx

  -- E' is measurable (E(k) is measurable, ∅ is measurable)
  have hmes' : ∀ k, LebesgueMeasurable (E' k) := by
    intro k
    simp only [E']
    by_cases hk : k < n
    · simp [dif_pos hk]
      exact hmes ⟨k, hk⟩
    · simp [dif_neg hk]
      exact LebesgueMeasurable.empty

  -- E' is pairwise disjoint
  have hdisj' : Set.univ.PairwiseDisjoint E' := by
    intro i _ j _ hij
    simp only [E', Function.onFun]
    by_cases hi : i < n <;> by_cases hj : j < n
    · simp only [dif_pos hi, dif_pos hj]
      have hne : (⟨i, hi⟩ : Fin n) ≠ ⟨j, hj⟩ := by
        intro heq
        apply hij
        exact congrArg Fin.val heq
      exact hdisj (Set.mem_univ _) (Set.mem_univ _) hne
    · simp only [dif_pos hi, dif_neg hj]
      exact disjoint_bot_right
    · simp only [dif_neg hi, dif_pos hj]
      exact disjoint_bot_left
    · simp only [dif_neg hi, dif_neg hj]
      exact disjoint_bot_left

  -- Apply countable_union
  rw [h_union, Lebesgue_measure.countable_union hmes' hdisj']

  -- The tsum over ℕ equals the tsum over Fin n (since E' k = ∅ for k ≥ n)
  have h_empty : ∀ k ≥ n, E' k = ∅ := fun k hk => dif_neg (not_lt.mpr hk)
  have h_measure_empty : ∀ k ≥ n, Lebesgue_measure (E' k) = 0 := by
    intro k hk
    rw [h_empty k hk, Lebesgue_measure.empty]

  -- Convert tsum over ℕ to tsum over Fin n
  -- Key: E' k = E ⟨k, h⟩ for k < n, and E' k = ∅ for k ≥ n

  -- Direct approach: show term-by-term equality using the embedding
  have h_eq_terms : ∀ i : Fin n, Lebesgue_measure (E' i.val) = Lebesgue_measure (E i) := by
    intro i
    simp only [E', dif_pos i.isLt]

  -- The tsum over ℕ equals the tsum over Fin n via reindexing
  -- Show that the support of E' is contained in {k : k < n}
  have h_support : Function.support (fun k => Lebesgue_measure (E' k)) ⊆ Set.Iio n := by
    intro k hk
    simp only [Set.mem_Iio]
    contrapose! hk
    simp only [Function.mem_support, not_not]
    exact h_measure_empty k hk
  -- Reindex from ℕ to Set.Iio n
  rw [← tsum_subtype_eq_of_support_subset h_support]
  -- Define equivalence between ↑(Set.Iio n) and Fin n
  let e : ↑(Set.Iio n) ≃ Fin n := {
    toFun := fun ⟨k, hk⟩ => ⟨k, Set.mem_Iio.mp hk⟩
    invFun := fun i => ⟨i.val, Set.mem_Iio.mpr i.isLt⟩
    left_inv := fun ⟨k, hk⟩ => rfl
    right_inv := fun i => rfl
  }
  -- Use the equivalence to reindex the tsum
  rw [← Equiv.tsum_eq e]
  congr 1
  ext ⟨k, hk⟩
  simp only [e, Equiv.coe_fn_mk]
  exact h_eq_terms ⟨k, Set.mem_Iio.mp hk⟩

theorem Lebesgue_measure.union {d:ℕ} {E F: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) (hF: LebesgueMeasurable F) (hdisj: E ∩ F = ∅) : Lebesgue_measure (E ∪ F) = Lebesgue_measure E + Lebesgue_measure F := by
  -- Apply finite_union with n=2
  let S : Fin 2 → Set (EuclideanSpace' d) := ![E, F]
  have h_union : E ∪ F = ⋃ n, S n := by
    ext x
    simp only [S, Set.mem_union, Set.mem_iUnion]
    constructor
    · intro h
      cases h with
      | inl hl => exact ⟨0, hl⟩
      | inr hr => exact ⟨1, hr⟩
    · intro ⟨n, hn⟩
      fin_cases n
      · left; exact hn
      · right; exact hn
  have hmes : ∀ n, LebesgueMeasurable (S n) := by intro n; fin_cases n <;> simp [S, hE, hF]
  have hdisj' : Set.univ.PairwiseDisjoint S := by
    intro i _ j _ hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · simp only [S, Function.onFun]
      exact Set.disjoint_iff_inter_eq_empty.mpr hdisj
    · simp only [S, Function.onFun]
      exact Set.disjoint_iff_inter_eq_empty.mpr (Set.inter_comm F E ▸ hdisj)
    · exact (hij rfl).elim
  rw [h_union, Lebesgue_measure.finite_union hmes hdisj']
  rw [tsum_fintype]
  simp only [S, Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Exercise 1.2.11(a) (Upward monotone convergence). -/
theorem Lebesgue_measure.upward_monotone_convergence {d:ℕ} {E: ℕ → Set (EuclideanSpace' d)} (hE: ∀ n, LebesgueMeasurable (E n)) (hmono: ∀ n, E n ⊆ E (n + 1)) : Filter.atTop.Tendsto (fun n ↦ Lebesgue_measure (E n)) (nhds (Lebesgue_measure (⋃ n, E n))) := by
  have hmono_chain {k m : ℕ} (hkm : k ≤ m) : E k ⊆ E m := by
    induction' hkm with l hl ih
    · exact Set.Subset.refl _
    · exact Set.Subset.trans ih (hmono l)
  let F : ℕ → Set (EuclideanSpace' d) := fun
    | 0 => E 0
    | n+1 => E (n+1) \ E n
  have hF_mes : ∀ n, LebesgueMeasurable (F n) := by
    intro n
    cases n with
    | zero => simp [F, hE 0]
    | succ n =>
      dsimp [F]
      exact LebesgueMeasurable.inter (hE (n+1)) (LebesgueMeasurable.complement (hE n))
  have ha_nn : ∀ n, 0 ≤ Lebesgue_measure (F n) := by
    intro n
    exact Lebesgue_outer_measure.nonneg (F n)
  have hF_disj : Set.univ.PairwiseDisjoint F := by
    intro i _ j _ hij
    by_cases h_lt : i < j
    · have h_sub : F i ⊆ E (j - 1) := by
        intro x hx
        rcases i with (rfl | i)
        · dsimp [F] at hx
          exact hmono_chain (Nat.zero_le (j - 1)) hx
        · dsimp [F] at hx
          exact hmono_chain (show i.succ ≤ j - 1 from by omega) hx.1
      have h_disjoint : Disjoint (E (j - 1)) (F j) := by
        rcases j with (rfl | j)
        · omega
        · dsimp [F]
          rw [Set.disjoint_iff_inter_eq_empty]
          ext x; simp
      exact Set.disjoint_of_subset_left h_sub h_disjoint
    · have h_lt' : j < i := by
        by_contra! hge
        apply hij
        omega
      have h_sub : F j ⊆ E (i - 1) := by
        intro x hx
        rcases j with (rfl | j)
        · dsimp [F] at hx
          exact hmono_chain (Nat.zero_le (i - 1)) hx
        · dsimp [F] at hx
          exact hmono_chain (show j.succ ≤ i - 1 from by omega) hx.1
      have h_disjoint : Disjoint (E (i - 1)) (F i) := by
        rcases i with (rfl | i)
        · omega
        · dsimp [F]
          rw [Set.disjoint_iff_inter_eq_empty]
          ext x; simp
      exact (Set.disjoint_of_subset_left h_sub h_disjoint).symm
  have h_countable : Lebesgue_measure (⋃ n, F n) = ∑' n, Lebesgue_measure (F n) :=
    Lebesgue_measure.countable_union hF_mes hF_disj
  have h_union_total : ⋃ n, F n = ⋃ n, E n := by
    ext x
    constructor
    · intro hx
      rcases (Set.mem_iUnion.mp hx) with ⟨n, hx⟩
      induction n with
      | zero =>
        dsimp [F] at hx
        exact Set.mem_iUnion.mpr ⟨0, hx⟩
      | succ n ih =>
        dsimp [F] at hx
        exact Set.mem_iUnion.mpr ⟨n.succ, hx.1⟩
    · intro hx
      rcases (Set.mem_iUnion.mp hx) with ⟨n, hx⟩
      classical
        have h_exists : ∃ m, x ∈ E m := ⟨n, hx⟩
        have hm_mem : x ∈ E (Nat.find h_exists) := Nat.find_spec h_exists
        have hm_min : ∀ k, x ∈ E k → Nat.find h_exists ≤ k := fun k hk => Nat.find_min' h_exists hk
        by_cases hm0 : Nat.find h_exists = 0
        · have h0 : x ∈ F 0 := by
            have hx0 : x ∈ E 0 := by
              rw [← hm0]; exact hm_mem
            simp [F, hx0]
          exact Set.mem_iUnion.mpr ⟨0, h0⟩
        · have hm_not_prev : x ∉ E (Nat.find h_exists - 1) := by
            intro hprev
            have hle : Nat.find h_exists ≤ Nat.find h_exists - 1 := hm_min (Nat.find h_exists - 1) hprev
            omega
          have hm_mem_F : x ∈ F (Nat.find h_exists) := by
            rcases Nat.exists_eq_succ_of_ne_zero hm0 with ⟨k, hk⟩
            have hk_sub : Nat.find h_exists - 1 = k := by omega
            have hm_mem_k : x ∈ E (k.succ) := by rw [← hk]; exact hm_mem
            have hm_not_prev_k : x ∉ E k := by rw [← hk_sub]; exact hm_not_prev
            simpa [F, hk, hk_sub] using ⟨hm_mem_k, hm_not_prev_k⟩
          exact Set.mem_iUnion.mpr ⟨Nat.find h_exists, hm_mem_F⟩
  have h_measure_E_range : ∀ N, Lebesgue_measure (E N) = ∑ k ∈ Finset.range (N + 1), Lebesgue_measure (F k) := by
    intro N
    induction' N with N ih
    · simp [F]
    · have h_union : E (N + 1) = E N ∪ F (N + 1) := by
        ext x; constructor
        · intro hx
          by_cases hx' : x ∈ E N
          · exact Set.mem_union_left _ hx'
          · refine Set.mem_union_right _ ?_
            simp [F, hx, hx']
        · intro hx
          rcases hx with (hx | hx)
          · exact hmono N hx
          · simp [F] at hx
            exact hx.1
      have h_disjoint : E N ∩ F (N + 1) = ∅ := by
        ext x; constructor
        · intro ⟨hxN, hxF⟩; simp [F] at hxF; exact hxF.2 hxN
        · intro hx; simp at hx
      have h_union_meas : LebesgueMeasurable (F (N + 1)) := hF_mes (N + 1)
      rw [h_union, Lebesgue_measure.union (hE N) h_union_meas h_disjoint, ih]
      simp [Finset.sum_range_succ, add_assoc, add_comm, add_left_comm]
  let a : ℕ → EReal := fun n => Lebesgue_measure (F n)
  let g : ℕ → ENNReal := fun n => (a n).toENNReal
  have ha_eq_g : ∀ n, a n = (g n : EReal) := by
    intro n
    dsimp [g, a]
    rw [EReal.coe_toENNReal (ha_nn n)]
  have h_tendsto_g : Filter.atTop.Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, g k) (nhds (∑' k, g k)) :=
    ENNReal.tendsto_nat_tsum g
  have h_cont : Continuous (fun (x : ENNReal) => (x : EReal)) := continuous_coe_ennreal_ereal
  have h_tendsto_sum_coe : Filter.atTop.Tendsto (fun N : ℕ => (∑ k ∈ Finset.range N, g k : ENNReal).toEReal) (nhds ((∑' k, g k : ENNReal).toEReal)) :=
    (h_cont.tendsto (∑' k, g k)).comp h_tendsto_g
  have h_sum_eq : ∀ N, (∑ k ∈ Finset.range N, g k : ENNReal).toEReal = ∑ k ∈ Finset.range N, a k := by
    intro N
    calc
      (∑ k ∈ Finset.range N, g k : ENNReal).toEReal = ∑ k ∈ Finset.range N, (g k : EReal) := by
        simp [EReal.coe_ennreal_finset_sum]
      _ = ∑ k ∈ Finset.range N, a k := by
        simp [ha_eq_g]
  have h_tendsto_sum_a : Filter.atTop.Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, a k) (nhds ((∑' k, g k : ENNReal).toEReal)) := by
    simpa [h_sum_eq] using h_tendsto_sum_coe
  have h_tsum_a_eq : (∑' k, g k : ENNReal).toEReal = ∑' k, a k := by
    let φ : ENNReal →+ EReal := {
      toFun := (↑·)
      map_zero' := by simp
      map_add' := EReal.coe_ennreal_add
    }
    have h_map : ∑' k, (g k : EReal) = (∑' k, g k : ENNReal).toEReal :=
      (Summable.map_tsum (f := g) ENNReal.summable φ h_cont).symm
    have h_map' : ∑' k, (g k : EReal) = ∑' k, a k := by
      refine tsum_congr ?_
      intro n
      exact (ha_eq_g n).symm
    rw [h_map'] at h_map
    exact h_map.symm
  rw [h_tsum_a_eq] at h_tendsto_sum_a
  have h_tendsto_sum_a_succ : Filter.atTop.Tendsto (fun N : ℕ => ∑ k ∈ Finset.range (N + 1), a k) (nhds (∑' k, a k)) :=
    h_tendsto_sum_a.comp (Filter.tendsto_add_atTop_nat 1)
  have h_tendsto_E : Filter.atTop.Tendsto (fun N : ℕ => Lebesgue_measure (E N)) (nhds (∑' k, a k)) := by
    have h_eq : (fun N : ℕ => Lebesgue_measure (E N)) = (fun N : ℕ => ∑ k ∈ Finset.range (N + 1), a k) := by
      ext N; exact h_measure_E_range N
    rw [h_eq]
    exact h_tendsto_sum_a_succ
  have h_tsum_total : ∑' k, a k = Lebesgue_measure (⋃ n, E n) := by
    calc
      ∑' k, a k = ∑' k, Lebesgue_measure (F k) := rfl
      _ = Lebesgue_measure (⋃ n, F n) := by rw [h_countable.symm]
      _ = Lebesgue_measure (⋃ n, E n) := by rw [h_union_total]
  rw [h_tsum_total] at h_tendsto_E
  exact h_tendsto_E

/-- Exercise 1.2.11(b) (Downward monotone convergence). -/
theorem Lebesgue_measure.downward_monotone_convergence {d:ℕ} {E: ℕ → Set (EuclideanSpace' d)} (hE: ∀ n, LebesgueMeasurable (E n)) (hmono: ∀ n, E (n+1) ⊆ E n) (hfin: ∃ n, Lebesgue_measure (E n) < ⊤) : Filter.atTop.Tendsto (fun n ↦ Lebesgue_measure (E n)) (nhds (Lebesgue_measure (⋂ n, E n))) := by
  rcases hfin with ⟨n₀, hn₀_fin⟩
  have hn₀_nn : 0 ≤ Lebesgue_measure (E n₀) := Lebesgue_outer_measure.nonneg (E n₀)
  have hn₀_fin' : Lebesgue_measure (E n₀) ≠ ⊤ := ne_of_lt hn₀_fin
  have hn₀_not_bot : Lebesgue_measure (E n₀) ≠ ⊥ := by
    intro hbot
    rw [hbot] at hn₀_nn
    have h_lt : (⊥ : EReal) < 0 := EReal.bot_lt_zero
    have h_lt_self : (⊥ : EReal) < (⊥ : EReal) := h_lt.trans_le hn₀_nn
    exact lt_irrefl _ h_lt_self
  obtain ⟨r0, hr0⟩ : ∃ r : ℝ, Lebesgue_measure (E n₀) = r := by
    refine ⟨(Lebesgue_measure (E n₀)).toReal, ?_⟩
    rw [EReal.coe_toReal hn₀_fin' hn₀_not_bot]

  have hmono_chain {k m : ℕ} (hkm : k ≤ m) : E m ⊆ E k := by
    induction' hkm with l hl ih
    · exact Set.Subset.refl _
    · exact Set.Subset.trans (hmono l) ih

  let F : ℕ → Set (EuclideanSpace' d) := fun n => E n₀ \ E (n₀ + n)
  have hF_mes : ∀ n, LebesgueMeasurable (F n) := by
    intro n
    exact LebesgueMeasurable.inter (hE n₀) (LebesgueMeasurable.complement (hE (n₀ + n)))
  have hF_mono : ∀ n, F n ⊆ F (n+1) := by
    intro n x hx
    rcases hx with ⟨hx_n₀, hx_not⟩
    refine ⟨hx_n₀, ?_⟩
    intro hx_E
    apply hx_not
    exact hmono (n₀ + n) hx_E

  have h_up : Filter.atTop.Tendsto (fun n ↦ Lebesgue_measure (F n)) (nhds (Lebesgue_measure (⋃ n, F n))) :=
    Lebesgue_measure.upward_monotone_convergence hF_mes hF_mono

  have h_union_F_sub_E_n0 : (⋃ n, F n) ⊆ E n₀ := by
    intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨n, hx⟩
    exact hx.1

  have h_union_F : ⋃ n, F n = E n₀ \ ⋂ n, E n := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨n, hx⟩
      rcases hx with ⟨hx_n₀, hx_not⟩
      refine ⟨hx_n₀, ?_⟩
      intro hx_inter
      apply hx_not
      exact (Set.mem_iInter.mp hx_inter) (n₀ + n)
    · intro hx
      rcases hx with ⟨hx_n₀, hx_not_inter⟩
      have : ∃ k, x ∉ E k := by
        simpa [Set.mem_iInter] using hx_not_inter
      rcases this with ⟨k, hk⟩
      have hk_ge_n₀ : n₀ ≤ k := by
        by_contra! hlt
        have : E n₀ ⊆ E k := hmono_chain (Nat.le_of_lt hlt)
        exact hk (this hx_n₀)
      have hx_mem_F : x ∈ F (k - n₀) := by
        refine ⟨hx_n₀, ?_⟩
        intro hx_E_n0_plus
        have : E (n₀ + (k - n₀)) = E k := by rw [Nat.add_sub_cancel' hk_ge_n₀]
        rw [this] at hx_E_n0_plus
        exact hk hx_E_n0_plus
      exact Set.mem_iUnion.mpr ⟨k - n₀, hx_mem_F⟩

  have h_inter_mes : LebesgueMeasurable (⋂ n, E n) :=
    LebesgueMeasurable.countable_inter hE
  have h_union_F_mes : LebesgueMeasurable (⋃ n, F n) :=
    LebesgueMeasurable.countable_union hF_mes

  have h_disjoint_inter_union_F : (⋂ n, E n) ∩ (⋃ n, F n) = ∅ := by
    rw [h_union_F]
    ext x; simp

  have h_set_eq_inter : E n₀ = (⋂ n, E n) ∪ (E n₀ \ ⋂ n, E n) := by
    ext x
    constructor
    · intro hx
      by_cases hx_inter : x ∈ ⋂ n, E n
      · exact Or.inl hx_inter
      · exact Or.inr ⟨hx, hx_inter⟩
    · intro hx
      rcases hx with (hx_inter | ⟨hx, _⟩)
      · exact (Set.mem_iInter.mp hx_inter) n₀
      · exact hx

  have h_partition_inter : Lebesgue_measure (E n₀) = Lebesgue_measure (⋂ n, E n) + Lebesgue_measure (⋃ n, F n) := by
    calc
      Lebesgue_measure (E n₀) = Lebesgue_measure ((⋂ n, E n) ∪ (E n₀ \ ⋂ n, E n)) :=
        congrArg Lebesgue_measure h_set_eq_inter
      _ = Lebesgue_measure ((⋂ n, E n) ∪ (⋃ n, F n)) := by rw [h_union_F]
      _ = Lebesgue_measure (⋂ n, E n) + Lebesgue_measure (⋃ n, F n) :=
        Lebesgue_measure.union h_inter_mes h_union_F_mes h_disjoint_inter_union_F

  have h_sub_n (n : ℕ) : E (n₀ + n) ⊆ E n₀ := hmono_chain (Nat.le_add_right n₀ n)

  have h_E_n0_eq_union_n (n : ℕ) : E n₀ = E (n₀ + n) ∪ F n := by
    ext x
    constructor
    · intro hx
      by_cases hx' : x ∈ E (n₀ + n)
      · exact Or.inl hx'
      · exact Or.inr ⟨hx, hx'⟩
    · intro hx
      rcases hx with (hx | ⟨hx, _⟩)
      · exact h_sub_n n hx
      · exact hx

  have h_disjoint_n (n : ℕ) : E (n₀ + n) ∩ F n = ∅ := by
    ext x; simp [F]

  have h_partition_n (n : ℕ) : Lebesgue_measure (E n₀) = Lebesgue_measure (E (n₀ + n)) + Lebesgue_measure (F n) := by
    calc
      Lebesgue_measure (E n₀) = Lebesgue_measure (E (n₀ + n) ∪ F n) := by rw [h_E_n0_eq_union_n n]
      _ = Lebesgue_measure (E (n₀ + n)) + Lebesgue_measure (F n) :=
        Lebesgue_measure.union (hE (n₀ + n)) (hF_mes n) (h_disjoint_n n)

  have hF_n_fin (n : ℕ) : Lebesgue_measure (F n) < ⊤ := by
    calc
      Lebesgue_measure (F n) ≤ Lebesgue_measure (E n₀) :=
        Lebesgue_outer_measure.mono (Set.diff_subset (s := E n₀) (t := E (n₀ + n)))
      _ < ⊤ := hn₀_fin

  have hF_n_not_top (n : ℕ) : Lebesgue_measure (F n) ≠ ⊤ := ne_of_lt (hF_n_fin n)
  have hF_n_nn (n : ℕ) : 0 ≤ Lebesgue_measure (F n) := Lebesgue_outer_measure.nonneg _
  have hF_n_not_bot (n : ℕ) : Lebesgue_measure (F n) ≠ ⊥ := by
    intro hbot
    have h_nonneg := hF_n_nn n
    rw [hbot] at h_nonneg
    have h_lt : (⊥ : EReal) < 0 := EReal.bot_lt_zero
    have h_lt_self : (⊥ : EReal) < (⊥ : EReal) := h_lt.trans_le h_nonneg
    exact lt_irrefl _ h_lt_self

  have h_m_E_n0_plus_n_fin (n : ℕ) : Lebesgue_measure (E (n₀ + n)) < ⊤ := by
    calc
      Lebesgue_measure (E (n₀ + n)) ≤ Lebesgue_measure (E n₀) :=
        Lebesgue_outer_measure.mono (h_sub_n n)
      _ < ⊤ := hn₀_fin

  have h_m_E_n0_plus_n_not_top (n : ℕ) : Lebesgue_measure (E (n₀ + n)) ≠ ⊤ := ne_of_lt (h_m_E_n0_plus_n_fin n)
  have h_m_E_n0_plus_n_nn (n : ℕ) : 0 ≤ Lebesgue_measure (E (n₀ + n)) := Lebesgue_outer_measure.nonneg _
  have h_m_E_n0_plus_n_not_bot (n : ℕ) : Lebesgue_measure (E (n₀ + n)) ≠ ⊥ := by
    intro hbot
    have h_nonneg := h_m_E_n0_plus_n_nn n
    rw [hbot] at h_nonneg
    have h_lt : (⊥ : EReal) < 0 := EReal.bot_lt_zero
    have h_lt_self : (⊥ : EReal) < (⊥ : EReal) := h_lt.trans_le h_nonneg
    exact lt_irrefl _ h_lt_self

  have h_inter_fin : Lebesgue_measure (⋂ n, E n) < ⊤ := by
    calc
      Lebesgue_measure (⋂ n, E n) ≤ Lebesgue_measure (E n₀) :=
        Lebesgue_outer_measure.mono (Set.iInter_subset (fun n : ℕ => E n) n₀)
      _ < ⊤ := hn₀_fin

  have h_m_union_F_fin : Lebesgue_measure (⋃ n, F n) < ⊤ := by
    calc
      Lebesgue_measure (⋃ n, F n) ≤ Lebesgue_measure (E n₀) :=
        Lebesgue_outer_measure.mono h_union_F_sub_E_n0
      _ < ⊤ := hn₀_fin

  have h_m_union_F_not_top : Lebesgue_measure (⋃ n, F n) ≠ ⊤ := ne_of_lt h_m_union_F_fin
  have h_m_union_F_nonneg : 0 ≤ Lebesgue_measure (⋃ n, F n) := Lebesgue_outer_measure.nonneg _
  have h_m_union_F_not_bot : Lebesgue_measure (⋃ n, F n) ≠ ⊥ := by
    intro hbot
    rw [hbot] at h_m_union_F_nonneg
    have h_lt : (⊥ : EReal) < 0 := EReal.bot_lt_zero
    have h_lt_self : (⊥ : EReal) < (⊥ : EReal) := h_lt.trans_le h_m_union_F_nonneg
    exact lt_irrefl _ h_lt_self

  have h_inter_not_top : Lebesgue_measure (⋂ n, E n) ≠ ⊤ := ne_of_lt h_inter_fin
  have h_inter_nonneg : 0 ≤ Lebesgue_measure (⋂ n, E n) := Lebesgue_outer_measure.nonneg _
  have h_inter_not_bot : Lebesgue_measure (⋂ n, E n) ≠ ⊥ := by
    intro hbot
    rw [hbot] at h_inter_nonneg
    have h_lt : (⊥ : EReal) < 0 := EReal.bot_lt_zero
    have h_lt_self : (⊥ : EReal) < (⊥ : EReal) := h_lt.trans_le h_inter_nonneg
    exact lt_irrefl _ h_lt_self

  have hF_tendsto_real : Filter.atTop.Tendsto (fun n ↦ (Lebesgue_measure (F n)).toReal) (nhds ((Lebesgue_measure (⋃ n, F n)).toReal)) :=
    (EReal.tendsto_toReal h_m_union_F_not_top h_m_union_F_not_bot).comp h_up

  have h_sum_real (n : ℕ) : (Lebesgue_measure (E (n₀ + n))).toReal + (Lebesgue_measure (F n)).toReal = r0 := by
    have hE_n0_plus_n : Lebesgue_measure (E (n₀ + n)) = ((Lebesgue_measure (E (n₀ + n))).toReal : EReal) :=
      (EReal.coe_toReal (h_m_E_n0_plus_n_not_top n) (h_m_E_n0_plus_n_not_bot n)).symm
    have hF_n : Lebesgue_measure (F n) = ((Lebesgue_measure (F n)).toReal : EReal) :=
      (EReal.coe_toReal (hF_n_not_top n) (hF_n_not_bot n)).symm
    have h_ereal_eq : ((Lebesgue_measure (E (n₀ + n))).toReal : EReal) + ((Lebesgue_measure (F n)).toReal : EReal) = (r0 : EReal) := by
      calc
        ((Lebesgue_measure (E (n₀ + n))).toReal : EReal) + ((Lebesgue_measure (F n)).toReal : EReal)
            = Lebesgue_measure (E (n₀ + n)) + Lebesgue_measure (F n) := by
              rw [hE_n0_plus_n.symm, hF_n.symm]
        _ = Lebesgue_measure (E n₀) := (h_partition_n n).symm
        _ = (r0 : EReal) := hr0
    apply EReal.coe_injective
    calc
      (((Lebesgue_measure (E (n₀ + n))).toReal + (Lebesgue_measure (F n)).toReal : ℝ) : EReal)
          = ((Lebesgue_measure (E (n₀ + n))).toReal : EReal) + ((Lebesgue_measure (F n)).toReal : EReal) := by rw [EReal.coe_add]
      _ = (r0 : EReal) := h_ereal_eq

  have h_inter_real : (Lebesgue_measure (⋂ n, E n)).toReal + (Lebesgue_measure (⋃ n, F n)).toReal = r0 := by
    have h_inter_ereal' : Lebesgue_measure (⋂ n, E n) = ((Lebesgue_measure (⋂ n, E n)).toReal : EReal) :=
      (EReal.coe_toReal h_inter_not_top h_inter_not_bot).symm
    have h_union_F_ereal : Lebesgue_measure (⋃ n, F n) = ((Lebesgue_measure (⋃ n, F n)).toReal : EReal) :=
      (EReal.coe_toReal h_m_union_F_not_top h_m_union_F_not_bot).symm
    have h_ereal_eq : ((Lebesgue_measure (⋂ n, E n)).toReal : EReal) + ((Lebesgue_measure (⋃ n, F n)).toReal : EReal) = (r0 : EReal) := by
      calc
        ((Lebesgue_measure (⋂ n, E n)).toReal : EReal) + ((Lebesgue_measure (⋃ n, F n)).toReal : EReal)
            = Lebesgue_measure (⋂ n, E n) + Lebesgue_measure (⋃ n, F n) := by
              rw [h_inter_ereal'.symm, h_union_F_ereal.symm]
        _ = Lebesgue_measure (E n₀) := h_partition_inter.symm
        _ = (r0 : EReal) := hr0
    apply EReal.coe_injective
    calc
      (((Lebesgue_measure (⋂ n, E n)).toReal + (Lebesgue_measure (⋃ n, F n)).toReal : ℝ) : EReal)
          = ((Lebesgue_measure (⋂ n, E n)).toReal : EReal) + ((Lebesgue_measure (⋃ n, F n)).toReal : EReal) := by rw [EReal.coe_add]
      _ = (r0 : EReal) := h_ereal_eq

  have h_eq_diff (n : ℕ) : (Lebesgue_measure (E (n₀ + n))).toReal = r0 - (Lebesgue_measure (F n)).toReal := by
    calc
      (Lebesgue_measure (E (n₀ + n))).toReal
          = ((Lebesgue_measure (E (n₀ + n))).toReal + (Lebesgue_measure (F n)).toReal) - (Lebesgue_measure (F n)).toReal := by ring
      _ = r0 - (Lebesgue_measure (F n)).toReal := by rw [h_sum_real n]

  have h_inter_diff : (Lebesgue_measure (⋂ n, E n)).toReal = r0 - (Lebesgue_measure (⋃ n, F n)).toReal := by
    calc
      (Lebesgue_measure (⋂ n, E n)).toReal
          = ((Lebesgue_measure (⋂ n, E n)).toReal + (Lebesgue_measure (⋃ n, F n)).toReal) - (Lebesgue_measure (⋃ n, F n)).toReal := by ring
      _ = r0 - (Lebesgue_measure (⋃ n, F n)).toReal := by rw [h_inter_real]

  have h_tendsto_sub : Filter.atTop.Tendsto (fun n ↦ r0 - (Lebesgue_measure (F n)).toReal) (nhds (r0 - (Lebesgue_measure (⋃ n, F n)).toReal)) :=
    (tendsto_const_nhds.sub hF_tendsto_real)

  have h_tendsto_E_real : Filter.atTop.Tendsto (fun n ↦ (Lebesgue_measure (E (n₀ + n))).toReal) (nhds ((Lebesgue_measure (⋂ n, E n)).toReal)) := by
    have h_tendsto_sub' : Filter.atTop.Tendsto (fun n ↦ (Lebesgue_measure (E (n₀ + n))).toReal) (nhds (r0 - (Lebesgue_measure (⋃ n, F n)).toReal)) := by
      simpa [h_eq_diff] using h_tendsto_sub
    simpa [h_inter_diff] using h_tendsto_sub'

  have h_eq_ereal (n : ℕ) : Lebesgue_measure (E (n₀ + n)) = ((Lebesgue_measure (E (n₀ + n))).toReal : EReal) :=
    (EReal.coe_toReal (h_m_E_n0_plus_n_not_top n) (h_m_E_n0_plus_n_not_bot n)).symm

  have h_inter_ereal : Lebesgue_measure (⋂ n, E n) = ((Lebesgue_measure (⋂ n, E n)).toReal : EReal) :=
    (EReal.coe_toReal h_inter_not_top h_inter_not_bot).symm

  have h_tendsto_E_ereal' : Filter.atTop.Tendsto (fun n ↦ Lebesgue_measure (E (n₀ + n))) (nhds (Lebesgue_measure (⋂ n, E n))) := by
    have h_temp : Filter.atTop.Tendsto (fun n : ℕ => (((Lebesgue_measure (E (n₀ + n))).toReal : ℝ) : EReal))
        (nhds (((Lebesgue_measure (⋂ n, E n)).toReal : ℝ) : EReal)) :=
      (EReal.tendsto_coe (m := fun n : ℕ => (Lebesgue_measure (E (n₀ + n))).toReal)
        (a := (Lebesgue_measure (⋂ n, E n)).toReal)).mpr h_tendsto_E_real
    have h_temp' : Filter.atTop.Tendsto (fun n : ℕ => Lebesgue_measure (E (n₀ + n))) (nhds (((Lebesgue_measure (⋂ n, E n)).toReal : ℝ) : EReal)) :=
      h_temp.congr (fun n => (h_eq_ereal n).symm)
    rw [h_inter_ereal]
    exact h_temp'

  intro t ht
  have h_mem : (fun n : ℕ ↦ Lebesgue_measure (E (n₀ + n)))⁻¹' t ∈ Filter.atTop := h_tendsto_E_ereal' ht
  rcases Filter.mem_atTop_sets.mp h_mem with ⟨N, hN⟩
  refine Filter.mem_atTop_sets.mpr ?_
  refine ⟨n₀ + N, ?_⟩
  intro m hm
  have hm_ge_n₀ : n₀ ≤ m := by omega
  have hm_sub_ge_N : m - n₀ ≥ N := by omega
  simpa [Nat.add_sub_cancel' hm_ge_n₀] using hN (m - n₀) hm_sub_ge_N
/-- Exercise 1.2.11 (c) (counterexample)-/
example : ∃ (d:ℕ) (E: ℕ → Set (EuclideanSpace' d)) (_hE: ∀ n, LebesgueMeasurable (E n)) (_hmono: ∀ n, E (n+1) ⊆ E n), ¬ Filter.atTop.Tendsto (fun n ↦ Lebesgue_measure (E n)) (nhds (Lebesgue_measure (⋂ n, E n))) := by
  set d := 1 with hd
  have hd_pos : 0 < d := by decide
  let E : ℕ → Set (EuclideanSpace' 1) := fun n => {x | ‖x‖ ≥ (n : ℝ)}
  have hE_mes : ∀ n, LebesgueMeasurable (E n) := by
    intro n
    have h_closed : IsClosed (E n) :=
      isClosed_le continuous_const continuous_norm
    exact h_closed.measurable
  have hmono : ∀ n, E (n+1) ⊆ E n := by
    intro n x hx
    have hx' : ‖x‖ ≥ (n+1 : ℝ) := by
      simpa [E] using hx
    have hn_le_np1 : (n : ℝ) ≤ (n+1 : ℝ) := by norm_num
    simpa [E] using hn_le_np1.trans hx'
  have h_inter_empty : ⋂ n, E n = (∅ : Set (EuclideanSpace' 1)) := by
    ext x
    simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false, E, Set.mem_setOf_eq]
    intro h
    have hceil : ‖x‖ ≤ (⌈‖x‖⌉₊ : ℝ) := Nat.le_ceil _
    have hx_norm : (⌈‖x‖⌉₊ : ℝ) + 1 ≤ ‖x‖ := by
      simpa [Nat.cast_add, Nat.cast_one] using h (⌈‖x‖⌉₊ + 1)
    linarith
  have h_meas_En_top : ∀ n, Lebesgue_measure (E n) = ⊤ := by
    intro n
    have hN : ∀ N : ℕ, (N : EReal) ≤ Lebesgue_measure (E n) := by
      intro N
      let UnitBox : (Fin 1 → ℤ) → Box 1 := fun a =>
        { side := fun i => BoundedInterval.Icc (a i : ℝ) ((a i : ℝ) + 1) }
      have h_vol : ∀ a : Fin 1 → ℤ, (UnitBox a).volume = 1 := by
        intro a; simp [UnitBox, Box.volume]
      let pts : Fin N → (Fin 1 → ℤ) := fun i _ => (n : ℤ) + (i : ℤ)
      have h_pts_inj : Function.Injective pts := by
        intro i j h
        apply Fin.ext
        have h_val : (n : ℤ) + (i : ℤ) = (n : ℤ) + (j : ℤ) := by
          simpa [pts] using congrArg (fun f : Fin 1 → ℤ => f ⟨0, hd_pos⟩) h
        exact_mod_cast add_left_cancel h_val
      have h_interior_box (a : Fin 1 → ℤ) : interior ((UnitBox a).toSet : Set (EuclideanSpace' 1)) =
          {x | ∀ i : Fin 1, x i ∈ Set.Ioo (a i : ℝ) ((a i : ℝ) + 1)} := by
        rw [Box.interior_toSet]
        ext x
        simp only [UnitBox, BoundedInterval.toSet, interior_Icc, Set.mem_preimage, Set.mem_pi, Set.mem_univ, Set.mem_setOf_eq, Set.mem_Ioo]
        constructor
        · intro h i
          have h' := h i
          simpa using h'
        · intro h i
          have h' : (PiLp.homeomorph 2 (fun (_ : Fin 1) => ℝ)) x i = x i := rfl
          have : i = (⟨0, hd_pos⟩ : Fin 1) := Subsingleton.elim i ⟨0, hd_pos⟩
          subst this
          simpa using h ⟨0, hd_pos⟩
      have h_almost_disj : ∀ a b : Fin 1 → ℤ, a ≠ b → AlmostDisjoint (UnitBox a) (UnitBox b) := by
        intro a b hab
        rw [AlmostDisjoint]
        ext x
        simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
        intro hxa hxb
        apply hab
        funext i
        have hxa_i : x i ∈ Set.Ioo (a i : ℝ) ((a i : ℝ) + 1) := by
          have := h_interior_box a ▸ hxa
          simpa using this i
        have hxb_i : x i ∈ Set.Ioo (b i : ℝ) ((b i : ℝ) + 1) := by
          have := h_interior_box b ▸ hxb
          simpa using this i
        rw [Set.mem_Ioo] at hxa_i hxb_i
        have ha_floor : (⌊x i⌋ : ℤ) = a i := by
          apply Int.floor_eq_iff.mpr
          constructor
          · exact_mod_cast hxa_i.1.le
          · exact_mod_cast hxa_i.2
        have hb_floor : (⌊x i⌋ : ℤ) = b i := by
          apply Int.floor_eq_iff.mpr
          constructor
          · exact_mod_cast hxb_i.1.le
          · exact_mod_cast hxb_i.2
        exact ha_floor.symm.trans hb_floor
      have h_subset : (⋃ i : Fin N, (UnitBox (pts i)).toSet) ⊆ E n := by
        intro x hx
        rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
        have hi_mem : x ∈ (UnitBox (pts i)).toSet := hi
        have hx_coord : ∀ j : Fin 1, x j ∈ Set.Icc ((pts i j : ℝ)) (((pts i j : ℝ)) + 1) := by
          intro j
          have htemp := (Box.mem_toSet (B := UnitBox (pts i)) (x := x)).mp hi_mem j
          simpa [UnitBox, BoundedInterval.toSet] using htemp
        have hx0_mem : x ⟨0, hd_pos⟩ ∈ Set.Icc ((pts i ⟨0, hd_pos⟩ : ℝ)) (((pts i ⟨0, hd_pos⟩ : ℝ)) + 1) :=
          hx_coord ⟨0, hd_pos⟩
        rcases hx0_mem with ⟨hx_l, hx_r⟩
        have h_pts_ge_n : (n : ℝ) ≤ (pts i ⟨0, hd_pos⟩ : ℝ) := by
          have h_nonneg : (0 : ℝ) ≤ (i : ℝ) := by exact mod_cast (Nat.zero_le i)
          calc
            (n : ℝ) = (n : ℝ) + (0 : ℝ) := by simp
            _ ≤ (n : ℝ) + (i : ℝ) := by gcongr
            _ = (pts i ⟨0, hd_pos⟩ : ℝ) := by simp [pts]
        have hx0_ge_n : (n : ℝ) ≤ x ⟨0, hd_pos⟩ := le_trans h_pts_ge_n hx_l
        have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := by exact mod_cast (Nat.zero_le n)
        have hx0_nonneg : 0 ≤ x ⟨0, hd_pos⟩ := le_trans hn_nonneg hx0_ge_n
        have hx_norm_ge_n : ‖x‖ ≥ (n : ℝ) :=
          calc
            ‖x‖ ≥ |x ⟨0, hd_pos⟩| := EuclideanSpace'.coord_le_norm x ⟨0, hd_pos⟩
            _ = x ⟨0, hd_pos⟩ := abs_of_nonneg hx0_nonneg
            _ ≥ (n : ℝ) := hx0_ge_n
        simpa [E] using hx_norm_ge_n
      have hElem : IsElementary (⋃ i : Fin N, (UnitBox (pts i)).toSet) :=
        IsElementary.iUnion_boxes (fun i : Fin N => UnitBox (pts i))
      have h_pw : Pairwise (Function.onFun AlmostDisjoint (fun i : Fin N => UnitBox (pts i))) := by
        intro i j hij
        simp only [Function.onFun]
        apply h_almost_disj
        intro heq
        exact hij (h_pts_inj heq)
      have h_sum_vol : (∑ i : Fin N, (UnitBox (pts i)).volume) = (N : ℝ) := by
        simp [h_vol, Finset.sum_const, nsmul_eq_mul, mul_one]
      have h_elem_eq : hElem.measure = ∑ i : Fin N, (UnitBox (pts i)).volume :=
        IsElementary.almost_disjoint hElem (fun i : Fin N => UnitBox (pts i)) rfl h_pw
      calc
        (N : EReal) = ((N : ℝ) : EReal) := by norm_cast
        _ = (∑ i : Fin N, (UnitBox (pts i)).volume : ℝ) := by rw [h_sum_vol]
        _ = (hElem.measure : EReal) := by rw [h_elem_eq]
        _ = Lebesgue_measure (⋃ i : Fin N, (UnitBox (pts i)).toSet) := by
          rw [← Lebesgue_outer_measure.elementary _ hElem, Lebesgue_measure]
        _ ≤ Lebesgue_measure (E n) := Lebesgue_outer_measure.mono h_subset
    rw [EReal.eq_top_iff_forall_lt]
    intro r
    obtain ⟨N, hNr⟩ := exists_nat_gt r
    calc
      (r : EReal) < (N : ℝ) := EReal.coe_lt_coe hNr
      _ = (N : EReal) := by norm_cast
      _ ≤ Lebesgue_measure (E n) := hN N
  have h_not_tendsto : ¬ Filter.atTop.Tendsto (fun n ↦ Lebesgue_measure (E n)) (nhds (Lebesgue_measure (⋂ n, E n))) := by
    rw [h_inter_empty, Lebesgue_measure.empty]
    intro h_tendsto
    have h_nhd : Set.Ioo (-1 : EReal) (1 : EReal) ∈ nhds (0 : EReal) := by
      apply isOpen_Ioo.mem_nhds
      norm_num
    have h_event : ∀ᶠ n in Filter.atTop, Lebesgue_measure (E n) ∈ Set.Ioo (-1 : EReal) (1 : EReal) :=
      h_tendsto h_nhd
    rcases Filter.Eventually.exists_forall_of_atTop h_event with ⟨N, hN⟩
    have h_meas_N : Lebesgue_measure (E N) = ⊤ := h_meas_En_top N
    have h_N_in_Ioo : Lebesgue_measure (E N) ∈ Set.Ioo (-1 : EReal) (1 : EReal) := hN N (le_refl N)
    rw [h_meas_N] at h_N_in_Ioo
    rcases h_N_in_Ioo with ⟨h_left, h_right⟩
    have h_top_not_lt_one : ¬ (⊤ : EReal) < (1 : EReal) := by
      intro h
      have : (1 : EReal) < (⊤ : EReal) := EReal.coe_lt_top (1 : ℝ)
      have : (⊤ : EReal) < (⊤ : EReal) := h.trans this
      exact lt_irrefl _ this
    exact h_top_not_lt_one h_right
  refine ⟨1, E, hE_mes, hmono, h_not_tendsto⟩

private lemma exercise_1_2_12_monotonicity {d:ℕ} (m: Set (EuclideanSpace' d) → EReal) (h_empty: m ∅ = 0) (h_pos: ∀ E, 0 ≤ m E) (hadd: ∀ E: ℕ → Set (EuclideanSpace' d), (Set.univ.PairwiseDisjoint E) → (∀ n, LebesgueMeasurable (E n)) → m (⋃ n, E n) = ∑' n, m (E n)) {E F: Set (EuclideanSpace' d)}
(hsub: E ⊆ F) (hE: LebesgueMeasurable E) (hF: LebesgueMeasurable F) : m E ≤ m F := by
  have h_diff_meas : LebesgueMeasurable (F \ E) :=
    hF.inter (hE.complement)
  have h_diff_disjoint : Disjoint E (F \ E) := by
    rw [Set.disjoint_iff_inter_eq_empty]
    ext x; simp
  let G : ℕ → Set (EuclideanSpace' d) := fun n =>
    if n = 0 then E else if n = 1 then F \ E else ∅
  have hG_meas : ∀ n, LebesgueMeasurable (G n) := by
    intro n
    dsimp [G]
    by_cases hn0 : n = 0
    · subst hn0; exact hE
    · by_cases hn1 : n = 1
      · subst hn1; exact h_diff_meas
      · simp [hn0, hn1]; exact LebesgueMeasurable.empty
  have hG_disj : Set.univ.PairwiseDisjoint G := by
    intro i _ j _ hij
    by_cases hi0 : i = 0
    · subst hi0
      by_cases hj0 : j = 0
      · exact (hij (hj0.symm)).elim
      · by_cases hj1 : j = 1
        · subst hj1; exact h_diff_disjoint
        · show Disjoint (G 0) (G j)
          simp [G, hj0, hj1]
    · by_cases hi1 : i = 1
      · subst hi1
        by_cases hj0 : j = 0
        · subst hj0
          show Disjoint (G 1) (G 0)
          simpa [G] using h_diff_disjoint.symm
        · by_cases hj1 : j = 1
          · exact (hij (hj1.symm)).elim
          · show Disjoint (G 1) (G j)
            simp [G, hj0, hj1]
      · show Disjoint (G i) (G j)
        simp [G, hi0, hi1]
  have h_union : ⋃ n, G n = F := by
    ext x; constructor
    · intro hx
      rw [Set.mem_iUnion] at hx
      rcases hx with ⟨n, hn⟩
      simp [G] at hn
      by_cases hn0 : n = 0
      · subst hn0; exact hsub hn
      · by_cases hn1 : n = 1
        · subst hn1; exact hn.1
        · simp [hn0, hn1] at hn
    · intro hx
      by_cases hxE : x ∈ E
      · apply Set.mem_iUnion.mpr; refine ⟨0, ?_⟩; simp [G, hxE]
      · apply Set.mem_iUnion.mpr; refine ⟨1, ?_⟩; simp [G, hx, hxE]
  have h_sum : ∑' n, m (G n) = m E + m (F \ E) := by
    have h_support : ∀ n, n ∉ Finset.range 2 → m (G n) = 0 := by
      intro n hn
      rw [Finset.mem_range] at hn
      have hn0 : n ≠ 0 := by omega
      have hn1 : n ≠ 1 := by omega
      have hG_empty : G n = ∅ := by
        dsimp [G]; simp [hn0, hn1]
      simp [hG_empty, h_empty]
    calc
      ∑' n, m (G n) = ∑ n ∈ Finset.range 2, m (G n) := by
        rw [tsum_eq_sum h_support]
      _ = m (G 0) + m (G 1) := by
        simp [Finset.sum_range_succ]
      _ = m E + m (F \ E) := by
        simp [G]
  have h_mF : m F = m E + m (F \ E) := by
    calc
      m F = m (⋃ n, G n) := by rw [h_union]
      _ = ∑' n, m (G n) := hadd G hG_disj hG_meas
      _ = m E + m (F \ E) := h_sum
  have h_nonneg_diff : 0 ≤ m (F \ E) := h_pos (F \ E)
  have h_mE_le : m E ≤ m E + m (F \ E) := by
    have := add_le_add_right h_nonneg_diff (m E)
    simpa [add_comm, add_left_comm, add_assoc] using this
  calc
    m E ≤ m E + m (F \ E) := h_mE_le
    _ = m F := by rw [h_mF]

/-- Exercise 1.2.12(i) (Monotonicity)-/
example {d:ℕ} (m: Set (EuclideanSpace' d) → EReal) (h_empty: m ∅ = 0) (h_pos: ∀ E, 0 ≤ m E) (hadd: ∀ E: ℕ → Set (EuclideanSpace' d), (Set.univ.PairwiseDisjoint E) → (∀ n, LebesgueMeasurable (E n)) → m (⋃ n, E n) = ∑' n, m (E n)) {E F: Set (EuclideanSpace' d)}
(hsub: E ⊆ F) (hE: LebesgueMeasurable E) (hF: LebesgueMeasurable F) : m E ≤ m F := by
  exact exercise_1_2_12_monotonicity m h_empty h_pos hadd hsub hE hF

/-- Exercise 1.2.12(ii) (σ-subadditivity)-/
example {d:ℕ} (m: Set (EuclideanSpace' d) → EReal) (h_empty: m ∅ = 0) (h_pos: ∀ E, 0 ≤ m E) (hadd: ∀ E: ℕ → Set (EuclideanSpace' d), (Set.univ.PairwiseDisjoint E) → (∀ n, LebesgueMeasurable (E n)) → m (⋃ n, E n) = ∑' n, m (E n)) {E: ℕ → Set (EuclideanSpace' d)} (hE: ∀ n, LebesgueMeasurable (E n)):  m (⋃ n, E n) ≤ ∑' n, m (E n) := by
  let F : ℕ → Set (EuclideanSpace' d) := fun n =>
    E n \ (⋃ k ∈ Finset.range n, E k)
  have hF_meas : ∀ n, LebesgueMeasurable (F n) := by
    intro n
    dsimp [F]
    have h_union_meas : LebesgueMeasurable (⋃ k ∈ Finset.range n, E k) := by
      have : (⋃ k ∈ Finset.range n, E k) = (⋃ i : Fin n, E i.val) := by
        ext x; constructor
        · intro hx
          rcases Set.mem_iUnion₂.mp hx with ⟨k, hk, hx'⟩
          have hk_lt_n : k < n := Finset.mem_range.mp hk
          exact Set.mem_iUnion.mpr ⟨⟨k, hk_lt_n⟩, hx'⟩
        · intro hx
          rcases Set.mem_iUnion.mp hx with ⟨⟨k, hk_lt_n⟩, hx'⟩
          have hk_mem : k ∈ Finset.range n := Finset.mem_range.mpr hk_lt_n
          exact Set.mem_iUnion₂.mpr ⟨k, hk_mem, hx'⟩
      rw [this]
      exact LebesgueMeasurable.finite_union (fun i : Fin n => hE i.val)
    exact (hE n).inter (h_union_meas.complement)
  have hF_sub : ∀ n, F n ⊆ E n := fun n => Set.diff_subset
  have hF_disj_aux : ∀ i j, i < j → Disjoint (F i) (F j) := by
    intro i j hij
    rw [Set.disjoint_iff_inter_eq_empty]
    ext x; constructor
    · intro hx; exfalso
      rcases hx with ⟨hxFi, hxFj⟩
      have hxEi : x ∈ E i := hxFi.1
      have hx_not_union : x ∉ ⋃ k ∈ Finset.range j, E k := hxFj.2
      apply hx_not_union
      exact Set.mem_iUnion₂.mpr ⟨i, Finset.mem_range.mpr hij, hxEi⟩
    · simp
  have hF_disj : Set.univ.PairwiseDisjoint F := by
    intro i _ j _ hij
    by_cases hij' : i < j
    · exact hF_disj_aux i j hij'
    · have hji : j < i := by
        have hle : j ≤ i := Nat.not_lt.mp hij'
        exact Nat.lt_of_le_of_ne hle hij.symm
      have h := hF_disj_aux j i hji
      show Disjoint (F i) (F j)
      rw [Set.disjoint_iff_inter_eq_empty, Set.inter_comm, ← Set.disjoint_iff_inter_eq_empty]
      exact h
  have h_union : ⋃ n, F n = ⋃ n, E n := by
    ext x; constructor
    · intro hx
      rw [Set.mem_iUnion] at hx
      rcases hx with ⟨n, hn⟩
      rw [Set.mem_iUnion]
      exact ⟨n, hn.1⟩
    · intro hx
      rw [Set.mem_iUnion] at hx
      rcases hx with ⟨n, hn⟩
      have h_exists : ∃ k, x ∈ E k := ⟨n, hn⟩
      classical
        let k := Nat.find h_exists
        have hk_mem : x ∈ E k := Nat.find_spec h_exists
        have hk_min : ∀ m, m < k → x ∉ E m := by
          intro m hm
          exact Nat.find_min h_exists hm
        have hx_not_union : x ∉ ⋃ m ∈ Finset.range k, E m := by
          intro hx_union
          rcases Set.mem_iUnion₂.mp hx_union with ⟨m, hm, hm_mem⟩
          have hm_lt_k : m < k := Finset.mem_range.mp hm
          exact hk_min m hm_lt_k hm_mem
        rw [Set.mem_iUnion]
        refine ⟨k, ?_⟩
        exact ⟨hk_mem, hx_not_union⟩
  have h_mono : ∀ n, m (F n) ≤ m (E n) := by
    intro n
    exact exercise_1_2_12_monotonicity m h_empty h_pos hadd (hF_sub n) (hF_meas n) (hE n)
  have h_m_union : m (⋃ n, E n) = ∑' n, m (F n) := by
    calc
      m (⋃ n, E n) = m (⋃ n, F n) := by rw [h_union]
      _ = ∑' n, m (F n) := hadd F hF_disj hF_meas
  rw [h_m_union]
  have h_nn_F : ∀ n, 0 ≤ m (F n) := fun n => h_pos (F n)
  have h_finset_sum_le_tsum (f : ℕ → EReal) (hf : ∀ n, 0 ≤ f n) (s : Finset ℕ) :
      (∑ n ∈ s, f n) ≤ ∑' n, f n := by
    let g : ℕ → ENNReal := fun n => (f n).toENNReal
    have hf_eq : ∀ n, f n = (g n : EReal) := fun n => (EReal.coe_toENNReal (hf n)).symm
    have h_tsum_f : ∑' n, f n = (∑' n, g n : ENNReal).toEReal := by
      calc
        ∑' n, f n = ∑' n, (g n : EReal) := tsum_congr hf_eq
        _ = (∑' n, g n : ENNReal).toEReal := by
          let φ : ENNReal →+ EReal := {
            toFun := (↑·)
            map_zero' := by simp
            map_add' := EReal.coe_ennreal_add
          }
          have h_cont : Continuous φ := continuous_coe_ennreal_ereal
          have h_summable : Summable g := ENNReal.summable
          exact (h_summable.map_tsum φ h_cont).symm
    calc
      (∑ n ∈ s, f n) = (∑ n ∈ s, (g n : EReal)) := by simp [hf_eq]
      _ = ((∑ n ∈ s, g n : ENNReal) : EReal) := by
        simp [EReal.coe_ennreal_finset_sum]
      _ ≤ (∑' n, g n : ENNReal).toEReal := by
        have h_enn_sum_le : (∑ n ∈ s, g n : ENNReal) ≤ ∑' n, g n := ENNReal.sum_le_tsum s
        exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr h_enn_sum_le
      _ = ∑' n, f n := h_tsum_f.symm
  have h_tsum_F_le_tsum_E : ∑' n, m (F n) ≤ ∑' n, m (E n) := by
    have h_nonneg : ∀ n, 0 ≤ m (F n) := h_nn_F
    have h_sum_le : ∀ N : ℕ, ∑ n ∈ Finset.range N, m (F n) ≤ ∑' n, m (E n) := by
      intro N
      calc
        ∑ n ∈ Finset.range N, m (F n) ≤ ∑ n ∈ Finset.range N, m (E n) :=
          Finset.sum_le_sum (fun n hn => h_mono n)
        _ ≤ ∑' n, m (E n) := h_finset_sum_le_tsum (m ∘ E) (fun n => h_pos (E n)) (Finset.range N)
    exact EReal.tsum_le_of_sum_range_le_of_nonneg h_nonneg h_sum_le
  exact h_tsum_F_le_tsum_E

/-- Exercise 1.2.13(i) -/
example {d:ℕ} {E: ℕ → Set (EuclideanSpace' d)} {E₀: Set (EuclideanSpace' d)} (hE: ∀ n, LebesgueMeasurable (E n)) (hpoint: ∀ x, Filter.atTop.Tendsto (fun n ↦ (E n).indicator' x) (nhds (E₀.indicator' x))) : LebesgueMeasurable E₀ := by
  have h_liminf : E₀ = Set.iUnion (fun (N : ℕ) => Set.iInter (fun (n : ℕ) => E (N + n))) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_iInter]
    constructor
    · intro hx
      have hx_E0 : E₀.indicator' x = 1 := by simp [hx]
      have h_conv := hpoint x
      rw [hx_E0] at h_conv
      rcases Metric.tendsto_atTop.mp h_conv (1/2 : ℝ) (by norm_num) with ⟨N, hN⟩
      refine ⟨N, λ n => ?_⟩
      have h := hN (N + n) (Nat.le_add_right N n)
      rw [Real.dist_eq] at h
      by_cases hx_mem : x ∈ E (N + n)
      · exact hx_mem
      · have h0 : (E (N + n)).indicator' x = 0 := Set.indicator'_of_notMem hx_mem
        rw [h0] at h
        norm_num at h
    · intro hx
      rcases hx with ⟨N, hx⟩
      by_cases hx0 : x ∈ E₀
      · exact hx0
      · have hx_not_E0 : E₀.indicator' x = 0 := by simp [hx0]
        have h_conv := hpoint x
        rw [hx_not_E0] at h_conv
        rcases Metric.tendsto_atTop.mp h_conv (1/2 : ℝ) (by norm_num) with ⟨M, hM⟩
        have hx_E_max : x ∈ E (max N M) := by
          have hmN : N ≤ max N M := le_max_left _ _
          have hk : max N M = N + (max N M - N) := by omega
          rw [hk]
          exact hx (max N M - N)
        have h_ind_max : (E (max N M)).indicator' x = 1 := by simp [hx_E_max]
        have h_max_ev : dist ((E (max N M)).indicator' x) (0 : ℝ) < 1/2 :=
          hM (max N M) (le_max_right _ _)
        rw [Real.dist_eq, h_ind_max, sub_zero] at h_max_ev
        norm_num at h_max_ev
  rw [h_liminf]
  refine LebesgueMeasurable.countable_union (fun N => ?_)
  exact LebesgueMeasurable.countable_inter (fun n => hE (N + n))
/-- Exercise 1.2.13(ii) -/
example {d:ℕ} {E: ℕ → Set (EuclideanSpace' d)} {E₀ F: Set (EuclideanSpace' d)}
  (hE: ∀ n, LebesgueMeasurable (E n))
  (hpoint: ∀ x, Filter.atTop.Tendsto (fun n ↦ (E n).indicator' x) (nhds (E₀.indicator' x)))
  (hsub: ∀ n, E n ⊆ F) (_hFmes: LebesgueMeasurable F) (hfin: Lebesgue_measure F < ⊤) : Filter.atTop.Tendsto (fun n ↦ Lebesgue_measure (E n)) (nhds (Lebesgue_measure E₀)) := by
  let A : ℕ → Set (EuclideanSpace' d) := fun k => ⋂ j, E (k + j)
  let B : ℕ → Set (EuclideanSpace' d) := fun k => ⋃ j, E (k + j)
  have hA_mes : ∀ k, LebesgueMeasurable (A k) := by
    intro k
    refine LebesgueMeasurable.countable_inter (fun j => ?_)
    exact hE (k + j)
  have hB_mes : ∀ k, LebesgueMeasurable (B k) := by
    intro k
    refine LebesgueMeasurable.countable_union (fun j => ?_)
    exact hE (k + j)
  have hA_mono : ∀ k, A k ⊆ A (k + 1) := by
    intro k x hx
    dsimp [A] at hx
    have hx_all : ∀ j, x ∈ E (k + j) := fun j => Set.mem_iInter.mp hx j
    apply Set.mem_iInter.mpr
    intro j
    have : (k + 1) + j = k + (j + 1) := by omega
    rw [this]
    exact hx_all (j + 1)
  have hB_mono : ∀ k, B (k + 1) ⊆ B k := by
    intro k x hx
    dsimp [B] at hx
    rcases Set.mem_iUnion.mp hx with ⟨j, hx⟩
    have h_eq : (k + 1) + j = k + (j + 1) := by omega
    rw [h_eq] at hx
    apply Set.mem_iUnion.mpr
    exact ⟨j + 1, hx⟩
  have h_incl : ∀ k, A k ⊆ E k ∧ E k ⊆ B k := by
    intro k
    constructor
    · intro x hx
      dsimp [A] at hx
      have hx0 := Set.mem_iInter.mp hx 0
      simpa using hx0
    · intro x hx
      apply Set.mem_iUnion.mpr
      refine ⟨0, ?_⟩
      simpa using hx
  have hA_sub_F : ∀ k, A k ⊆ F := by
    intro k x hx
    apply hsub k
    exact (h_incl k).1 hx
  have hB_sub_F : ∀ k, B k ⊆ F := by
    intro k x hx
    dsimp [B] at hx
    rcases Set.mem_iUnion.mp hx with ⟨j, hx⟩
    exact hsub (k + j) hx
  have h_union_A_eq_E₀ : ⋃ (k : ℕ), A k = E₀ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_iInter, A]
    constructor
    · intro hx
      rcases hx with ⟨(k : ℕ), hx⟩
      by_contra hx0
      have hx0' : E₀.indicator' x = 0 := by simp [hx0]
      have h_conv := hpoint x
      rw [hx0'] at h_conv
      rcases Metric.tendsto_atTop.mp h_conv (1/2 : ℝ) (by norm_num) with ⟨N, hN⟩
      have hx_Emax : x ∈ E (max k N) := by
        have : max k N = k + (max k N - k) := by omega
        rw [this]
        exact hx (max k N - k)
      have h_ind_max : (E (max k N)).indicator' x = 1 := by simp [hx_Emax]
      have h_dist : dist ((E (max k N)).indicator' x) (0 : ℝ) < 1/2 :=
        hN (max k N) (le_max_right _ _)
      rw [Real.dist_eq, h_ind_max, sub_zero] at h_dist
      norm_num at h_dist
    · intro hx
      have hx_val : E₀.indicator' x = 1 := by simp [hx]
      have h_conv := hpoint x
      rw [hx_val] at h_conv
      rcases Metric.tendsto_atTop.mp h_conv (1/2 : ℝ) (by norm_num) with ⟨N, hN⟩
      refine ⟨N, ?_⟩
      intro j
      have h := hN (N + j) (Nat.le_add_right N j)
      rw [Real.dist_eq] at h
      by_cases hx_mem : x ∈ E (N + j)
      · exact hx_mem
      · have h0 : (E (N + j)).indicator' x = 0 := Set.indicator'_of_notMem hx_mem
        rw [h0] at h
        norm_num at h
  have h_inter_B_eq_E₀ : ⋂ (k : ℕ), B k = E₀ := by
    ext x
    simp only [Set.mem_iInter, Set.mem_iUnion, B]
    constructor
    · intro hx
      by_contra hx0
      have hx0' : E₀.indicator' x = 0 := by simp [hx0]
      have h_conv := hpoint x
      rw [hx0'] at h_conv
      rcases Metric.tendsto_atTop.mp h_conv (1/2 : ℝ) (by norm_num) with ⟨N, hN⟩
      have hx_not_all : ∀ n, n ≥ N → x ∉ E n := by
        intro n hn
        have h := hN n hn
        rw [Real.dist_eq] at h
        by_cases hx_mem : x ∈ E n
        · have h1 : (E n).indicator' x = 1 := by simp [hx_mem]
          rw [h1] at h
          norm_num at h
        · exact hx_mem
      rcases hx N with ⟨j, hx_BN⟩
      have hpos : N + j ≥ N := by omega
      exact hx_not_all (N + j) hpos hx_BN
    · intro hx (m : ℕ)
      have hx_val : E₀.indicator' x = 1 := by simp [hx]
      have h_conv := hpoint x
      rw [hx_val] at h_conv
      rcases Metric.tendsto_atTop.mp h_conv (1/2 : ℝ) (by norm_num) with ⟨N, hN⟩
      have hx_all : ∀ n, n ≥ N → x ∈ E n := by
        intro n hn
        have h := hN n hn
        rw [Real.dist_eq] at h
        by_cases hx_mem : x ∈ E n
        · exact hx_mem
        · have h0 : (E n).indicator' x = 0 := Set.indicator'_of_notMem hx_mem
          rw [h0] at h
          norm_num at h
      let n := Nat.max m N
      have hn_ge_m : n ≥ m := Nat.le_max_left _ _
      have hn_ge_N : n ≥ N := Nat.le_max_right _ _
      have hx_En : x ∈ E n := hx_all n hn_ge_N
      refine ⟨n - m, ?_⟩
      have : m + (n - m) = n := by omega
      simpa [this]
  have hA_fin : ∃ n, Lebesgue_measure (A n) < ⊤ := by
    refine ⟨0, ?_⟩
    calc
      Lebesgue_measure (A 0) ≤ Lebesgue_measure F :=
        Lebesgue_outer_measure.mono (hA_sub_F 0)
      _ < ⊤ := hfin
  have h_tendsto_A : Filter.atTop.Tendsto (fun k ↦ Lebesgue_measure (A k)) (nhds (Lebesgue_measure (⋃ k, A k))) :=
    Lebesgue_measure.upward_monotone_convergence hA_mes hA_mono
  have h_tendsto_A_E₀ : Filter.atTop.Tendsto (fun k ↦ Lebesgue_measure (A k)) (nhds (Lebesgue_measure E₀)) := by
    simpa [h_union_A_eq_E₀] using h_tendsto_A
  have hB_fin : ∃ n, Lebesgue_measure (B n) < ⊤ := by
    refine ⟨0, ?_⟩
    calc
      Lebesgue_measure (B 0) ≤ Lebesgue_measure F :=
        Lebesgue_outer_measure.mono (hB_sub_F 0)
      _ < ⊤ := hfin
  have h_tendsto_B : Filter.atTop.Tendsto (fun k ↦ Lebesgue_measure (B k)) (nhds (Lebesgue_measure (⋂ k, B k))) :=
    Lebesgue_measure.downward_monotone_convergence hB_mes hB_mono hB_fin
  have h_tendsto_B_E₀ : Filter.atTop.Tendsto (fun k ↦ Lebesgue_measure (B k)) (nhds (Lebesgue_measure E₀)) := by
    simpa [h_inter_B_eq_E₀] using h_tendsto_B
  have h_sandwich : ∀ k, Lebesgue_measure (A k) ≤ Lebesgue_measure (E k) ∧ Lebesgue_measure (E k) ≤ Lebesgue_measure (B k) := by
    intro k
    have hAE : A k ⊆ E k := (h_incl k).1
    have hEB : E k ⊆ B k := (h_incl k).2
    constructor
    · exact Lebesgue_outer_measure.mono hAE
    · exact Lebesgue_outer_measure.mono hEB
  have h_lower : ∀ k, Lebesgue_measure (A k) ≤ Lebesgue_measure (E k) := fun k => (h_sandwich k).1
  have h_upper : ∀ k, Lebesgue_measure (E k) ≤ Lebesgue_measure (B k) := fun k => (h_sandwich k).2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le h_tendsto_A_E₀ h_tendsto_B_E₀ h_lower h_upper

/-- Exercise 1.2.13(iii) -/
example : ∃ (d:ℕ) (E: ℕ → Set (EuclideanSpace' d)) (E₀ F: Set (EuclideanSpace' d))
  (_hE: ∀ n, LebesgueMeasurable (E n))
  (_hpoint: ∀ x, Filter.atTop.Tendsto (fun n ↦ (E n).indicator' x) (nhds (E₀.indicator' x)))
  (_hsub: ∀ n, E n ⊆ F) (_hFmes: LebesgueMeasurable F), ¬ Filter.atTop.Tendsto (fun n ↦ Lebesgue_measure (E n)) (nhds (Lebesgue_measure E₀)) := by
  set d := 1 with hd
  have hd_pos : 0 < d := by decide
  let E : ℕ → Set (EuclideanSpace' 1) := fun n => {x | ‖x‖ ≥ (n : ℝ)}
  let E₀ : Set (EuclideanSpace' 1) := ∅
  let F : Set (EuclideanSpace' 1) := Set.univ
  have hE_mes : ∀ n, LebesgueMeasurable (E n) := by
    intro n
    have h_closed : IsClosed (E n) :=
      isClosed_le continuous_const continuous_norm
    exact h_closed.measurable
  have hF_mes : LebesgueMeasurable F := isOpen_univ.measurable
  have hsub : ∀ n, E n ⊆ F := fun n => Set.subset_univ _
  have hpoint : ∀ x, Filter.atTop.Tendsto (fun n ↦ (E n).indicator' x) (nhds (E₀.indicator' x)) := by
    intro x
    simp [E₀]
    rcases exists_nat_gt (‖x‖) with ⟨N, hN⟩
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    refine ⟨N, fun n hn => ?_⟩
    have hnx : ‖x‖ < (n : ℝ) := by
      calc
        ‖x‖ < (N : ℝ) := hN
        _ ≤ (n : ℝ) := by exact_mod_cast hn
    have hx_not_mem : x ∉ E n := by
      intro hx_mem
      have hx_mem' : (n : ℝ) ≤ ‖x‖ := hx_mem
      linarith
    have h0 : (E n).indicator' x = (0 : ℝ) := Set.indicator'_of_notMem hx_not_mem
    rw [h0, Real.dist_eq, sub_self, abs_zero]
    exact hε
  have h_meas_En_top : ∀ n, Lebesgue_measure (E n) = ⊤ := by
    intro n
    have hN : ∀ N : ℕ, (N : EReal) ≤ Lebesgue_measure (E n) := by
      intro N
      let UnitBox : (Fin 1 → ℤ) → Box 1 := fun a =>
        { side := fun i => BoundedInterval.Icc (a i : ℝ) ((a i : ℝ) + 1) }
      have h_vol : ∀ a : Fin 1 → ℤ, (UnitBox a).volume = 1 := by
        intro a; simp [UnitBox, Box.volume]
      let pts : Fin N → (Fin 1 → ℤ) := fun i _ => (n : ℤ) + (i : ℤ)
      have h_pts_inj : Function.Injective pts := by
        intro i j h
        apply Fin.ext
        have h_val : (n : ℤ) + (i : ℤ) = (n : ℤ) + (j : ℤ) := by
          simpa [pts] using congrArg (fun f : Fin 1 → ℤ => f ⟨0, hd_pos⟩) h
        exact_mod_cast add_left_cancel h_val
      have h_interior_box (a : Fin 1 → ℤ) : interior ((UnitBox a).toSet : Set (EuclideanSpace' 1)) =
          {x | ∀ i : Fin 1, x i ∈ Set.Ioo (a i : ℝ) ((a i : ℝ) + 1)} := by
        rw [Box.interior_toSet]
        ext x
        simp only [UnitBox, BoundedInterval.toSet, interior_Icc, Set.mem_preimage, Set.mem_pi, Set.mem_univ, Set.mem_setOf_eq, Set.mem_Ioo]
        constructor
        · intro h i
          have h' := h i
          simpa using h'
        · intro h i
          have : i = (⟨0, hd_pos⟩ : Fin 1) := Subsingleton.elim i ⟨0, hd_pos⟩
          subst this
          simpa using h ⟨0, hd_pos⟩
      have h_almost_disj : ∀ a b : Fin 1 → ℤ, a ≠ b → AlmostDisjoint (UnitBox a) (UnitBox b) := by
        intro a b hab
        rw [AlmostDisjoint]
        ext x
        simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
        intro hxa hxb
        apply hab
        funext i
        have hxa_i : x i ∈ Set.Ioo (a i : ℝ) ((a i : ℝ) + 1) := by
          have := h_interior_box a ▸ hxa
          simpa using this i
        have hxb_i : x i ∈ Set.Ioo (b i : ℝ) ((b i : ℝ) + 1) := by
          have := h_interior_box b ▸ hxb
          simpa using this i
        rw [Set.mem_Ioo] at hxa_i hxb_i
        have ha_floor : (⌊x i⌋ : ℤ) = a i := by
          apply Int.floor_eq_iff.mpr
          constructor
          · exact_mod_cast hxa_i.1.le
          · exact_mod_cast hxa_i.2
        have hb_floor : (⌊x i⌋ : ℤ) = b i := by
          apply Int.floor_eq_iff.mpr
          constructor
          · exact_mod_cast hxb_i.1.le
          · exact_mod_cast hxb_i.2
        exact ha_floor.symm.trans hb_floor
      have h_subset : (⋃ i : Fin N, (UnitBox (pts i)).toSet) ⊆ E n := by
        intro x hx
        rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
        have hi_mem : x ∈ (UnitBox (pts i)).toSet := hi
        have hx_coord : ∀ j : Fin 1, x j ∈ Set.Icc ((pts i j : ℝ)) (((pts i j : ℝ)) + 1) := by
          intro j
          have htemp := (Box.mem_toSet (B := UnitBox (pts i)) (x := x)).mp hi_mem j
          simpa [UnitBox, BoundedInterval.toSet] using htemp
        have hx0_mem : x ⟨0, hd_pos⟩ ∈ Set.Icc ((pts i ⟨0, hd_pos⟩ : ℝ)) (((pts i ⟨0, hd_pos⟩ : ℝ)) + 1) :=
          hx_coord ⟨0, hd_pos⟩
        rcases hx0_mem with ⟨hx_l, hx_r⟩
        have h_pts_ge_n : (n : ℝ) ≤ (pts i ⟨0, hd_pos⟩ : ℝ) := by
          have h_nonneg : (0 : ℝ) ≤ (i : ℝ) := by exact mod_cast (Nat.zero_le i)
          calc
            (n : ℝ) = (n : ℝ) + (0 : ℝ) := by simp
            _ ≤ (n : ℝ) + (i : ℝ) := by gcongr
            _ = (pts i ⟨0, hd_pos⟩ : ℝ) := by simp [pts]
        have hx0_ge_n : (n : ℝ) ≤ x ⟨0, hd_pos⟩ := le_trans h_pts_ge_n hx_l
        have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := by exact mod_cast (Nat.zero_le n)
        have hx0_nonneg : 0 ≤ x ⟨0, hd_pos⟩ := le_trans hn_nonneg hx0_ge_n
        have hx_norm_ge_n : ‖x‖ ≥ (n : ℝ) :=
          calc
            ‖x‖ ≥ |x ⟨0, hd_pos⟩| := EuclideanSpace'.coord_le_norm x ⟨0, hd_pos⟩
            _ = x ⟨0, hd_pos⟩ := abs_of_nonneg hx0_nonneg
            _ ≥ (n : ℝ) := hx0_ge_n
        simpa [E] using hx_norm_ge_n
      have hElem : IsElementary (⋃ i : Fin N, (UnitBox (pts i)).toSet) :=
        IsElementary.iUnion_boxes (fun i : Fin N => UnitBox (pts i))
      have h_pw : Pairwise (Function.onFun AlmostDisjoint (fun i : Fin N => UnitBox (pts i))) := by
        intro i j hij
        simp only [Function.onFun]
        apply h_almost_disj
        intro heq
        exact hij (h_pts_inj heq)
      have h_sum_vol : (∑ i : Fin N, (UnitBox (pts i)).volume) = (N : ℝ) := by
        simp [h_vol, Finset.sum_const, nsmul_eq_mul, mul_one]
      have h_elem_eq : hElem.measure = ∑ i : Fin N, (UnitBox (pts i)).volume :=
        IsElementary.almost_disjoint hElem (fun i : Fin N => UnitBox (pts i)) rfl h_pw
      calc
        (N : EReal) = ((N : ℝ) : EReal) := by norm_cast
        _ = (∑ i : Fin N, (UnitBox (pts i)).volume : ℝ) := by rw [h_sum_vol]
        _ = (hElem.measure : EReal) := by rw [h_elem_eq]
        _ = Lebesgue_measure (⋃ i : Fin N, (UnitBox (pts i)).toSet) := by
          rw [← Lebesgue_outer_measure.elementary _ hElem, Lebesgue_measure]
        _ ≤ Lebesgue_measure (E n) := Lebesgue_outer_measure.mono h_subset
    rw [EReal.eq_top_iff_forall_lt]
    intro r
    obtain ⟨N, hNr⟩ := exists_nat_gt r
    calc
      (r : EReal) < (N : ℝ) := EReal.coe_lt_coe hNr
      _ = (N : EReal) := by norm_cast
      _ ≤ Lebesgue_measure (E n) := hN N
  have h_meas_E₀ : Lebesgue_measure E₀ = 0 := by
    simp [E₀]
  have h_not_tendsto : ¬ Filter.atTop.Tendsto (fun n ↦ Lebesgue_measure (E n)) (nhds (Lebesgue_measure E₀)) := by
    rw [h_meas_E₀]
    intro h_tendsto
    have h_nhd : Set.Ioo (-1 : EReal) (1 : EReal) ∈ nhds (0 : EReal) := by
      apply isOpen_Ioo.mem_nhds
      norm_num
    have h_event : ∀ᶠ n in Filter.atTop, Lebesgue_measure (E n) ∈ Set.Ioo (-1 : EReal) (1 : EReal) :=
      h_tendsto h_nhd
    rcases Filter.Eventually.exists_forall_of_atTop h_event with ⟨N, hN⟩
    have h_meas_N : Lebesgue_measure (E N) = ⊤ := h_meas_En_top N
    have h_N_in_Ioo : Lebesgue_measure (E N) ∈ Set.Ioo (-1 : EReal) (1 : EReal) := hN N (le_refl N)
    rw [h_meas_N] at h_N_in_Ioo
    rcases h_N_in_Ioo with ⟨h_left, h_right⟩
    have h_top_not_lt_one : ¬ (⊤ : EReal) < (1 : EReal) := by
      intro h
      have : (1 : EReal) < (⊤ : EReal) := EReal.coe_lt_top (1 : ℝ)
      have : (⊤ : EReal) < (⊤ : EReal) := h.trans this
      exact lt_irrefl _ this
    exact h_top_not_lt_one h_right
  refine ⟨1, E, E₀, F, hE_mes, hpoint, hsub, hF_mes, h_not_tendsto⟩

/-- Exercise 1.2.14 -/
example {d:ℕ} (E: Set (EuclideanSpace' d)) : ∃ (F: Set (EuclideanSpace' d)), E ⊆ F ∧ LebesgueMeasurable F ∧ Lebesgue_measure F = Lebesgue_outer_measure E := by
  by_cases h_top : Lebesgue_outer_measure E = ⊤
  · refine ⟨Set.univ, Set.subset_univ E, IsOpen.measurable isOpen_univ, ?_⟩
    rw [h_top]
    have h_mono : Lebesgue_outer_measure E ≤ Lebesgue_outer_measure Set.univ :=
      Lebesgue_outer_measure.mono (Set.subset_univ E)
    rw [h_top] at h_mono
    exact le_antisymm le_top h_mono
  · have h_eps_pos : ∀ n : ℕ, (0 : EReal) < ((1 : ℝ) / ((n : ℝ) + 1) : EReal) := fun n => by
      have hpos : (0 : ℝ) < (1 : ℝ) / ((n : ℝ) + 1) := by
        refine div_pos (by norm_num) (by
          nlinarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg _])
      exact EReal.coe_pos.mpr hpos
    have h_exists : ∀ n : ℕ, ∃ U : Set (EuclideanSpace' d), IsOpen U ∧ E ⊆ U ∧
      Lebesgue_outer_measure U ≤ Lebesgue_outer_measure E + (((1 : ℝ) / ((n : ℝ) + 1)) : EReal) := by
      intro n
      exact Lebesgue_outer_measure.exists_open_superset_measure_le E (((1 : ℝ) / ((n : ℝ) + 1)) : EReal) (h_eps_pos n)
    choose U hU_open hE_sub_U hU_bound using h_exists
    let F := ⋂ n, U n
    have h_sub : E ⊆ F := by
      intro x hx
      simp only [F, Set.mem_iInter]
      intro n
      exact hE_sub_U n hx
    have h_meas : LebesgueMeasurable F := by
      rw [show F = ⋂ (n : ℕ), U n from rfl]
      refine LebesgueMeasurable.countable_inter (fun n => ?_)
      exact IsOpen.measurable (hU_open n)
    have h_mF_eq : Lebesgue_measure F = Lebesgue_outer_measure E := by
      have h_ge : Lebesgue_outer_measure E ≤ Lebesgue_measure F :=
        Lebesgue_outer_measure.mono h_sub
      have h_le : Lebesgue_measure F ≤ Lebesgue_outer_measure E := by
        have h_bound : ∀ n : ℕ, Lebesgue_measure F ≤ Lebesgue_outer_measure E + (((1 : ℝ) / ((n : ℝ) + 1)) : EReal) := by
          intro n
          have h_F_sub_U : F ⊆ U n := Set.iInter_subset (fun (n : ℕ) => U n) n
          calc
            Lebesgue_measure F ≤ Lebesgue_outer_measure (U n) := Lebesgue_outer_measure.mono h_F_sub_U
            _ ≤ Lebesgue_outer_measure E + (((1 : ℝ) / ((n : ℝ) + 1)) : EReal) := hU_bound n
        by_contra! h_lt
        by_cases hF_top : Lebesgue_measure F = ⊤
        · have h_bound_0 : Lebesgue_measure F ≤ Lebesgue_outer_measure E + (((1 : ℝ) / ((0 : ℝ) + 1)) : EReal) := by
            simpa using h_bound (0 : ℕ)
          rw [hF_top] at h_bound_0
          have h_add_ne_top : Lebesgue_outer_measure E + (((1 : ℝ) / ((0 : ℝ) + 1)) : EReal) ≠ ⊤ := by
            have : ((1 : ℝ) / ((0 : ℝ) + 1) : EReal) = ((1 : ℝ) : EReal) := by norm_num
            rw [this]
            exact EReal.add_ne_top h_top (EReal.coe_ne_top (1 : ℝ))
          have h_eq_top : Lebesgue_outer_measure E + (((1 : ℝ) / ((0 : ℝ) + 1)) : EReal) = ⊤ :=
            le_antisymm le_top h_bound_0
          exact h_add_ne_top h_eq_top
        · have h_nonneg_F : 0 ≤ Lebesgue_measure F := Lebesgue_outer_measure.nonneg F
          have h_cases : Lebesgue_measure F = ⊥ ∨ (∃ s : ℝ, Lebesgue_measure F = (s : EReal)) ∨ Lebesgue_measure F = ⊤ := by
            refine match Lebesgue_measure F with
            | ⊥ => Or.inl rfl
            | (s : ℝ) => Or.inr (Or.inl ⟨s, rfl⟩)
            | ⊤ => Or.inr (Or.inr rfl)
          rcases h_cases with (hbot | ⟨s, hF⟩ | htop)
          · exfalso
            have : (0 : EReal) ≤ (⊥ : EReal) := by
              rw [hbot] at h_nonneg_F; exact h_nonneg_F
            exact not_lt.mpr this EReal.bot_lt_zero
          · have h_cases' : Lebesgue_outer_measure E = ⊥ ∨ (∃ r : ℝ, Lebesgue_outer_measure E = (r : EReal)) ∨ Lebesgue_outer_measure E = ⊤ := by
              refine match Lebesgue_outer_measure E with
              | ⊥ => Or.inl rfl
              | (r : ℝ) => Or.inr (Or.inl ⟨r, rfl⟩)
              | ⊤ => Or.inr (Or.inr rfl)
            rcases h_cases' with (hbot' | ⟨r, hE⟩ | htop')
            · exfalso
              have : (0 : EReal) ≤ (⊥ : EReal) := by
                simpa [hbot'] using Lebesgue_outer_measure.nonneg E
              exact not_lt.mpr this EReal.bot_lt_zero
            · have h_rs : r < s := by
                have : (r : EReal) < (s : EReal) := by
                  rw [← hE, ← hF]
                  exact h_lt
                exact EReal.coe_lt_coe_iff.mp this
              have h_bound_real : ∀ n : ℕ, s ≤ r + (1 : ℝ) / ((n : ℝ) + 1) := by
                intro n
                have h_bound_ereal : (s : EReal) ≤ (r : EReal) + (((1 : ℝ) / ((n : ℝ) + 1)) : EReal) := by
                  calc
                    (s : EReal) = Lebesgue_measure F := by symm; exact hF
                    _ ≤ Lebesgue_outer_measure E + (((1 : ℝ) / ((n : ℝ) + 1)) : EReal) := h_bound n
                    _ = (r : EReal) + (((1 : ℝ) / ((n : ℝ) + 1)) : EReal) := by rw [hE]
                have h_target : (s : EReal) ≤ ((r + (1 : ℝ) / ((n : ℝ) + 1) : ℝ) : EReal) := by
                  simpa [EReal.coe_add, EReal.coe_div, EReal.coe_one] using h_bound_ereal
                exact EReal.coe_le_coe_iff.mp h_target
              set δ := (s - r) / 3 with hδ
              have hδ_pos : 0 < δ := by
                dsimp [δ]
                refine div_pos (sub_pos.mpr h_rs) (by norm_num : (0 : ℝ) < 3)
              have h_one_div_delta_pos : 0 < 1 / δ := div_pos (by norm_num) hδ_pos
              obtain ⟨N, hN⟩ : ∃ N : ℕ, 1 / δ < (N : ℝ) := exists_nat_gt (1 / δ)
              have hNp1_pos : (0 : ℝ) < (N : ℝ) + 1 := by
                nlinarith [show (0 : ℝ) ≤ (N : ℝ) from Nat.cast_nonneg _]
              have hN1 : 1 / ((N : ℝ) + 1) < δ :=
                (one_div_lt hNp1_pos hδ_pos).mpr (calc
                  1 / δ < (N : ℝ) := hN
                  _ ≤ (N : ℝ) + 1 := by nlinarith)
              have h_bound_N : s ≤ r + 1 / ((N : ℝ) + 1) := h_bound_real N
              have h_contra : s < s := by
                calc
                  s ≤ r + 1 / ((N : ℝ) + 1) := h_bound_N
                  _ < r + δ := by
                    nlinarith
                  _ = r + (s - r) / 3 := rfl
                  _ < s := by
                    nlinarith
              exact lt_irrefl s h_contra
            · exfalso; exact h_top htop'
          · exfalso; exact hF_top htop
      exact le_antisymm h_le h_ge
    exact ⟨F, h_sub, h_meas, h_mF_eq⟩

/-- Exercise 1.2.15 (Inner regularity). -/
theorem Lebesgue_measure.eq {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E): Lebesgue_measure E = sSup { M | ∃ K, K ⊆ E ∧ IsCompact K ∧ M = Lebesgue_measure K} := by
  sorry

/-- Exercise 1.2.16 (Criteria for finite measure). -/
theorem LebesgueMeasurable.finite_TFAE {d:ℕ} (E: Set (EuclideanSpace' d)) :
    [
      LebesgueMeasurable E ∧ Lebesgue_measure E < ⊤,
      (∀ ε > 0, ∃ U : Set (EuclideanSpace' d), IsOpen U ∧ E ⊆ U ∧ Lebesgue_measure U < ⊤ ∧ Lebesgue_outer_measure (U \ E) ≤ ε),
      (∀ ε > 0, ∃ U : Set (EuclideanSpace' d), IsOpen U ∧ Bornology.IsBounded U ∧ Lebesgue_outer_measure (symmDiff U E) ≤ ε),
      (∀ ε > 0, ∃ F: Set (EuclideanSpace' d), IsCompact F ∧ F ⊆ E ∧ Lebesgue_outer_measure (E \ F) ≤ ε),
      (∀ ε > 0, ∃ F: Set (EuclideanSpace' d), IsCompact F ∧ Lebesgue_outer_measure (symmDiff F E) ≤ ε),
      (∀ ε > 0, ∃ E': Set (EuclideanSpace' d), LebesgueMeasurable E' ∧ Lebesgue_measure E' < ⊤ ∧ Lebesgue_outer_measure (symmDiff E' E) ≤ ε),
      (∀ ε > 0, ∃ E': Set (EuclideanSpace' d), LebesgueMeasurable E' ∧ Bornology.IsBounded E' ∧ Lebesgue_outer_measure (symmDiff E' E) ≤ ε),
      (∀ ε > 0, ∃ E': Set (EuclideanSpace' d), IsElementary E' ∧ Lebesgue_outer_measure (symmDiff E' E) ≤ ε),
      (∀ ε > 0, ∃ (n:ℤ) (F: Finset (Box d)), (∀ B ∈ F, B.IsDyadicAtScale n) ∧ Lebesgue_outer_measure (symmDiff (⋃ B ∈ F, B.toSet) E) ≤ ε)
    ].TFAE
  := by sorry

/-- Exercise 1.2.17 (Caratheodory criterion one direction). -/
theorem LebesgueMeasurable.caratheodory {d:ℕ} (E: Set (EuclideanSpace' d)) :
    [
      LebesgueMeasurable E,
      (∀ A: Set (EuclideanSpace' d), IsElementary A → Lebesgue_outer_measure A = Lebesgue_outer_measure (A ∩ E) + Lebesgue_outer_measure (A \ E)),
      (∀ (B:Box d),  Lebesgue_outer_measure B.toSet = Lebesgue_outer_measure (B.toSet ∩ E) + Lebesgue_outer_measure (B.toSet \ E))
    ].TFAE
  := by sorry

theorem Bornology.IsBounded.inElementary {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E) : ∃ (A: Set (EuclideanSpace' d)), IsElementary A ∧ E ⊆ A := IsElementary.contains_bounded hE

noncomputable def inner_measure {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E) : ℝ := (Lebesgue_measure hE.inElementary.choose).toReal - (Lebesgue_measure (hE.inElementary.choose \ E)).toReal

/-- Exercise 1.2.18(i) (Inner measure). -/
theorem inner_measure.eq {d:ℕ} {E A: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E)
  (hA: IsElementary A) (hsub: E ⊆ A) : inner_measure hE = Lebesgue_measure A - Lebesgue_outer_measure (A \ E) := by
  sorry

/-- Exercise 1.2.18(ii) (Inner measure). -/
theorem inner_measure.le {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E)
  : inner_measure hE ≤ Lebesgue_outer_measure E := by
  set A₀ := hE.inElementary.choose with hA₀_def
  have hA₀_elem : IsElementary A₀ := hE.inElementary.choose_spec.1
  have hE_sub_A₀ : E ⊆ A₀ := hE.inElementary.choose_spec.2
  have hA₀_bdd : Bornology.IsBounded A₀ := IsElementary.isBounded hA₀_elem
  have hA₀_fin : Lebesgue_outer_measure A₀ ≠ ⊤ := by
    have h_compact : IsCompact (closure A₀) :=
      Metric.isCompact_of_isClosed_isBounded isClosed_closure hA₀_bdd.closure
    have h_fin : Lebesgue_outer_measure (closure A₀) ≠ ⊤ :=
      Lebesgue_outer_measure.finite_of_compact h_compact
    have h_mono : Lebesgue_outer_measure A₀ ≤ Lebesgue_outer_measure (closure A₀) :=
      Lebesgue_outer_measure.mono subset_closure
    intro htop
    apply h_fin
    exact le_antisymm le_top (by
      calc
        ⊤ = Lebesgue_outer_measure A₀ := htop.symm
        _ ≤ Lebesgue_outer_measure (closure A₀) := h_mono)
  have h_subadd : Lebesgue_outer_measure A₀ ≤ Lebesgue_outer_measure E + Lebesgue_outer_measure (A₀ \ E) := by
    let S : Fin 2 → Set (EuclideanSpace' d) := ![E, A₀ \ E]
    have h_union_eq : (E ∪ (A₀ \ E)) = ⋃ i : Fin 2, S i := by
      ext x; simp [S]; tauto
    have h_sum_eq : ∑ i : Fin 2, Lebesgue_outer_measure (S i) = Lebesgue_outer_measure E + Lebesgue_outer_measure (A₀ \ E) := by
      simp [S, Fin.sum_univ_two]
    calc
      Lebesgue_outer_measure A₀ = Lebesgue_outer_measure (E ∪ (A₀ \ E)) := by
        rw [Set.union_diff_cancel hE_sub_A₀]
      _ = Lebesgue_outer_measure (⋃ i : Fin 2, S i) := by rw [h_union_eq]
      _ ≤ ∑ i : Fin 2, Lebesgue_outer_measure (S i) := Lebesgue_outer_measure.finite_union_le S
      _ = Lebesgue_outer_measure E + Lebesgue_outer_measure (A₀ \ E) := by rw [h_sum_eq]
  have h_diff_not_top : Lebesgue_outer_measure (A₀ \ E) ≠ ⊤ := by
    intro htop
    apply hA₀_fin
    have h_mono : Lebesgue_outer_measure (A₀ \ E) ≤ Lebesgue_outer_measure A₀ :=
      Lebesgue_outer_measure.mono (fun x hx => hx.1)
    exact le_antisymm le_top (by
      calc
        ⊤ = Lebesgue_outer_measure (A₀ \ E) := htop.symm
        _ ≤ Lebesgue_outer_measure A₀ := h_mono)
  unfold inner_measure
  rw [← hA₀_def]
  dsimp [Lebesgue_measure]
  have h_nonneg_E : 0 ≤ Lebesgue_outer_measure E := Lebesgue_outer_measure.nonneg E
  by_cases hE_top : Lebesgue_outer_measure E = ⊤
  · rw [hE_top]; exact le_top
  · have hA₀_nonneg : 0 ≤ Lebesgue_outer_measure A₀ := Lebesgue_outer_measure.nonneg A₀
    have h_diff_nonneg : 0 ≤ Lebesgue_outer_measure (A₀ \ E) := Lebesgue_outer_measure.nonneg (A₀ \ E)
    have h0_gt_bot : (⊥ : EReal) < (0 : EReal) := by norm_num
    have hA₀_not_bot : Lebesgue_outer_measure A₀ ≠ ⊥ := by
      intro hbot
      have h_contra : (⊥ : EReal) < (⊥ : EReal) := h0_gt_bot.trans_le (hbot ▸ hA₀_nonneg)
      exact (lt_irrefl _) h_contra
    have h_diff_not_bot : Lebesgue_outer_measure (A₀ \ E) ≠ ⊥ := by
      intro hbot
      have h_contra : (⊥ : EReal) < (⊥ : EReal) := h0_gt_bot.trans_le (hbot ▸ h_diff_nonneg)
      exact (lt_irrefl _) h_contra
    have hE_not_bot : Lebesgue_outer_measure E ≠ ⊥ := by
      intro hbot
      have h_contra : (⊥ : EReal) < (⊥ : EReal) := h0_gt_bot.trans_le (hbot ▸ h_nonneg_E)
      exact (lt_irrefl _) h_contra
    have hA₀_val : Lebesgue_outer_measure A₀ = ((Lebesgue_outer_measure A₀).toReal : EReal) :=
      (EReal.coe_toReal hA₀_fin hA₀_not_bot).symm
    have h_diff_val : Lebesgue_outer_measure (A₀ \ E) = ((Lebesgue_outer_measure (A₀ \ E)).toReal : EReal) :=
      (EReal.coe_toReal h_diff_not_top h_diff_not_bot).symm
    have hE_val : Lebesgue_outer_measure E = ((Lebesgue_outer_measure E).toReal : EReal) :=
      (EReal.coe_toReal hE_top hE_not_bot).symm
    have h_subadd' : ((Lebesgue_outer_measure A₀).toReal : EReal) ≤ ((Lebesgue_outer_measure E).toReal : EReal) + ((Lebesgue_outer_measure (A₀ \ E)).toReal : EReal) := by
      rw [hA₀_val, h_diff_val, hE_val] at h_subadd
      exact h_subadd
    have h_add : ((Lebesgue_outer_measure E).toReal : EReal) + ((Lebesgue_outer_measure (A₀ \ E)).toReal : EReal) =
      (((Lebesgue_outer_measure E).toReal + (Lebesgue_outer_measure (A₀ \ E)).toReal : ℝ) : EReal) := by
      simp
    have h_subadd_real : (Lebesgue_outer_measure A₀).toReal ≤ (Lebesgue_outer_measure E).toReal + (Lebesgue_outer_measure (A₀ \ E)).toReal := by
      rw [h_add] at h_subadd'
      exact (EReal.coe_le_coe_iff.mp h_subadd')
    have h_goal_real : (Lebesgue_outer_measure A₀).toReal - (Lebesgue_outer_measure (A₀ \ E)).toReal ≤ (Lebesgue_outer_measure E).toReal := by
      linarith
    rw [hE_val]
    exact_mod_cast h_goal_real

/-- Exercise 1.2.18(ii') (Inner measure). -/
theorem inner_measure.eq_iff {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E)
  : inner_measure hE = Lebesgue_outer_measure E ↔ LebesgueMeasurable E := by
  sorry

def IsFσ  {X:Type*} [TopologicalSpace X] (s : Set X) : Prop :=
  ∃ T : Set (Set X), (∀ t ∈ T, IsClosed t) ∧ T.Countable ∧ s = ⋃₀ T

/-- Exercise 1.2.19 -/
theorem LebesgueMeasurable.TFAE' {d:ℕ} (E: Set (EuclideanSpace' d)) :
    [
      LebesgueMeasurable E,
      (∃ F, ∃ N, IsGδ F ∧ IsNull N ∧ E = F \ N),
      (∃ F, ∃ N, IsFσ F ∧ IsNull N ∧ E = F ∪ N)
    ].TFAE
  := by sorry

open Pointwise

lemma IsOpen.add_singleton {d : ℕ} {U : Set (EuclideanSpace' d)} (hU : IsOpen U) (x : EuclideanSpace' d) : IsOpen (U + {x}) := by
  have h_eq : (Homeomorph.addRight x) '' U = U + {x} := by ext y; simp
  rw [← h_eq]
  exact ((Homeomorph.addRight x).isOpen_image.mpr hU)

lemma Lebesgue_outer_measure.translate {d:ℕ} (E: Set (EuclideanSpace' d)) (x: EuclideanSpace' d) :
    Lebesgue_outer_measure (E + {x}) = Lebesgue_outer_measure E := by
  have h_le (F : Set (EuclideanSpace' d)) (v : EuclideanSpace' d) : Lebesgue_outer_measure (F + {v}) ≤ Lebesgue_outer_measure F := by
    unfold Lebesgue_outer_measure
    apply sInf_le_sInf
    intro V hV
    obtain ⟨X, S, hF_cover, rfl⟩ := hV
    have h_boxes : ∀ n : X, ∃ B' : Box d, B'.toSet = (S n).toSet + {v} ∧ |B'|ᵥ = |S n|ᵥ :=
      fun n => Box.volume_of_translate (S n) v
    choose S' hS' using h_boxes
    refine ⟨X, S', ?_, ?_⟩
    · intro y hy
      rcases Set.mem_add.mp hy with ⟨e, he, z, hz, rfl⟩
      have hz_eq : z = v := Set.mem_singleton_iff.mp hz
      rw [hz_eq]
      have he_cover : e ∈ ⋃ n, (S n).toSet := hF_cover he
      rcases Set.mem_iUnion.mp he_cover with ⟨n, hn⟩
      apply Set.mem_iUnion.mpr
      refine ⟨n, ?_⟩
      rw [(hS' n).1]
      exact Set.mem_add.mpr ⟨e, hn, v, Set.mem_singleton v, rfl⟩
    · refine tsum_congr (fun n => ?_)
      rw [(hS' n).2]
  apply le_antisymm
  · exact h_le E x
  · have h_add_neg : (E + {x}) + {(-x)} = E := by ext y; simp
    calc
      Lebesgue_outer_measure E = Lebesgue_outer_measure ((E + {x}) + {(-x)}) := by rw [h_add_neg]
      _ ≤ Lebesgue_outer_measure (E + {x}) := h_le (E + {x}) (-x)

/-- Exercise 1.2.20 (Translation invariance) -/
theorem LebesgueMeasurable.translate {d:ℕ} (E: Set (EuclideanSpace' d)) (x: EuclideanSpace' d) :
    LebesgueMeasurable E ↔ LebesgueMeasurable (E + {x}) := by
  constructor
  · intro hE ε hε
    rcases hE ε hε with ⟨U, hU_open, hE_sub_U, h_outer⟩
    have h_diff_eq : (U + {x}) \ (E + {x}) = (U \ E) + {x} := by ext y; simp
    refine ⟨U + {x}, IsOpen.add_singleton hU_open x, Set.add_subset_add hE_sub_U (Set.Subset.refl {x}), ?_⟩
    calc
      Lebesgue_outer_measure ((U + {x}) \ (E + {x})) = Lebesgue_outer_measure ((U \ E) + {x}) := by rw [h_diff_eq]
      _ = Lebesgue_outer_measure (U \ E) := Lebesgue_outer_measure.translate (U \ E) x
      _ ≤ ε := h_outer
  · intro hE ε hε
    rcases hE ε hε with ⟨U, hU_open, hE_sub_U, h_outer⟩
    have hU_open' : IsOpen (U + {(-x)}) := IsOpen.add_singleton hU_open (-x)
    have h_sub' : E ⊆ U + {(-x)} := by
      intro e he
      have : e + x ∈ E + {x} := Set.mem_add.mpr ⟨e, he, x, Set.mem_singleton x, rfl⟩
      have h_e_x : e + x ∈ U := hE_sub_U this
      have : e = (e + x) + (-x) := by simp
      rw [this]
      exact Set.mem_add.mpr ⟨e + x, h_e_x, -x, Set.mem_singleton (-x), rfl⟩
    have h_diff_eq : ((U + {(-x)}) \ E) + {x} = U \ (E + {x}) := by
      calc
        ((U + {(-x)}) \ E) + {x} = ((U + {(-x)}) + {x}) \ (E + {x}) := by ext y; simp
        _ = U \ (E + {x}) := by ext y; simp
    have h_outer' : Lebesgue_outer_measure ((U + {(-x)}) \ E) ≤ ε := by
      calc
        Lebesgue_outer_measure ((U + {(-x)}) \ E) =
            Lebesgue_outer_measure (((U + {(-x)}) \ E) + {x}) := by
              rw [← Lebesgue_outer_measure.translate ((U + {(-x)}) \ E) x]
        _ = Lebesgue_outer_measure (U \ (E + {x})) := by rw [h_diff_eq]
        _ ≤ ε := h_outer
    exact ⟨U + {(-x)}, hU_open', h_sub', h_outer'⟩

theorem Lebesgue_measure.translate {d:ℕ} {E: Set (EuclideanSpace' d)} (x: EuclideanSpace' d)
   (_hE: LebesgueMeasurable E): Lebesgue_measure (E + {x}) = Lebesgue_measure E := by
  rw [Lebesgue_measure, Lebesgue_measure, Lebesgue_outer_measure.translate E x]

/-- Exercise 1.2.21 (Change of variables) -/
lemma LebesgueMeasurable.linear {d:ℕ} (T: EuclideanSpace' d ≃ₗ[ℝ] EuclideanSpace' d)
{E: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E): LebesgueMeasurable (T '' E) := by
  sorry

/-- Exercise 1.2.21 (Change of variables) -/
lemma Lebesgue_measure.linear {d:ℕ} (A: Matrix (Fin d) (Fin d) ℝ) [Invertible A]
 {E: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E): Lebesgue_measure (A.linear_equiv '' E) = |A.det| * Lebesgue_measure E := by
  sorry

/-- Exercise 1.2.22(i) (Outer measure product bound)-/
theorem Lebesgue_outer_measure.prod {d₁ d₂:ℕ} {E₁: Set (EuclideanSpace' d₁)} {E₂: Set (EuclideanSpace' d₂)}
  : Lebesgue_outer_measure (EuclideanSpace'.prod E₁ E₂) ≤ Lebesgue_outer_measure E₁ * Lebesgue_outer_measure E₂ := by sorry

/-- Exercise 1.2.22(ii) (Measurability of product)-/
theorem LebesgueMeasurable.prod {d₁ d₂:ℕ} {E₁: Set (EuclideanSpace' d₁)} {E₂: Set (EuclideanSpace' d₂)}
  (hE₁: LebesgueMeasurable E₁) (hE₂: LebesgueMeasurable E₂) : LebesgueMeasurable (EuclideanSpace'.prod E₁ E₂) := by sorry

/-- Exercise 1.2.22(ii') (Product measure formula) -/
theorem Lebesgue_measure.prod {d₁ d₂:ℕ} {E₁: Set (EuclideanSpace' d₁)} {E₂: Set (EuclideanSpace' d₂)}
  (hE₁: LebesgueMeasurable E₁) (hE₂: LebesgueMeasurable E₂)
  : Lebesgue_measure (EuclideanSpace'.prod E₁ E₂) = Lebesgue_measure E₁ * Lebesgue_measure E₂ := by sorry

/-- Exercise 1.2.23 (Uniqueness of Lebesgue measure) -/
theorem Lebesgue_measure.unique {d:ℕ} (m: Set (EuclideanSpace' d) → EReal)
  (h_empty: m ∅ = 0) (h_pos: ∀ E, 0 ≤ m E)
  (h_add: ∀ E: ℕ → Set (EuclideanSpace' d), (Set.univ.PairwiseDisjoint E) → (∀ n, LebesgueMeasurable (E n)) → m (⋃ n, E n) = ∑' n, m (E n))
  (h_transl: ∀ (x : EuclideanSpace' d) (E : Set (EuclideanSpace' d)), m (E + {x}) = m E)
  (hnorm: m (Box.unit_cube d) = 1)
  : ∀ E, LebesgueMeasurable E → m E = Lebesgue_measure E := by sorry

/-- Exercise 1.2.24(i) (Lebesgue measure as the completion of elementary measure). -/
instance IsElementary.ae_equiv {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A):
Setoid (Set A) := {
   r E F := IsNull (Subtype.val '' (_root_.symmDiff E F))
   iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      have : IsNull (∅ : Set (EuclideanSpace' d)) := Lebesgue_outer_measure.of_empty d
      simpa [symmDiff_self, Set.image_empty] using this
    · intro x y h
      rw [symmDiff_comm]
      exact h
    · intro x y z hxy hyz
      have h_triangle : _root_.symmDiff x z ⊆ _root_.symmDiff x y ∪ _root_.symmDiff y z := by
        simpa using symmDiff_triangle x y z
      have h_sub : Subtype.val '' (_root_.symmDiff x z) ⊆ Subtype.val '' (_root_.symmDiff x y) ∪ Subtype.val '' (_root_.symmDiff y z) :=
        calc
          Subtype.val '' (_root_.symmDiff x z) ⊆ Subtype.val '' (_root_.symmDiff x y ∪ _root_.symmDiff y z) := Set.image_mono h_triangle
          _ = Subtype.val '' (_root_.symmDiff x y) ∪ Subtype.val '' (_root_.symmDiff y z) := Set.image_union _ _ _
      have h_union_null : IsNull (Subtype.val '' (_root_.symmDiff x y) ∪ Subtype.val '' (_root_.symmDiff y z)) := by
        let F : Fin 2 → Set (EuclideanSpace' d) := λ | 0 => Subtype.val '' (_root_.symmDiff x y) | 1 => Subtype.val '' (_root_.symmDiff y z)
        have h_union_eq : ⋃ i : Fin 2, F i = Subtype.val '' (_root_.symmDiff x y) ∪ Subtype.val '' (_root_.symmDiff y z) := by
          ext w; simp [F]
        have h_sum_zero : ∑ i : Fin 2, Lebesgue_outer_measure (F i) = 0 := by
          simp [F, hxy, hyz]
        have h_measure_le_zero : Lebesgue_outer_measure (⋃ i : Fin 2, F i) ≤ 0 := by
          calc
            Lebesgue_outer_measure (⋃ i : Fin 2, F i) ≤ ∑ i : Fin 2, Lebesgue_outer_measure (F i) :=
              Lebesgue_outer_measure.finite_union_le F
            _ = 0 := h_sum_zero
        rw [← h_union_eq]
        exact le_antisymm h_measure_le_zero (Lebesgue_outer_measure.nonneg _)
      exact IsNull.subset h_union_null h_sub
}

def IsElementary.ae_subsets {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A) := Quotient hA.ae_equiv

def IsElementary.ae_quot {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A) (E: Set A): hA.ae_subsets := Quotient.mk' (s := hA.ae_equiv) E

/-- Exercise 1.2.24(ii) (Lebesgue measure as the completion of elementary measure)-/
noncomputable def IsElementary.dist {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A) : hA.ae_subsets → hA.ae_subsets → ℝ :=
  Quotient.lift₂ (fun E F ↦ (Lebesgue_outer_measure (Subtype.val '' (_root_.symmDiff E F))).toReal) (by
    intro E F E' F' hE_eq hF_eq
    have h_meas_eq : Lebesgue_outer_measure (Subtype.val '' (_root_.symmDiff E F)) =
        Lebesgue_outer_measure (Subtype.val '' (_root_.symmDiff E' F')) := by
      have h_aux (X Y X' Y' : Set A) (hX : IsNull (Subtype.val '' (_root_.symmDiff X X')))
          (hY : IsNull (Subtype.val '' (_root_.symmDiff Y Y'))) :
          Lebesgue_outer_measure (Subtype.val '' (_root_.symmDiff X Y)) ≤
          Lebesgue_outer_measure (Subtype.val '' (_root_.symmDiff X' Y')) := by
        have h_symm_sub : _root_.symmDiff X Y ⊆ _root_.symmDiff X X' ∪ _root_.symmDiff X' Y' ∪ _root_.symmDiff Y Y' := by
          intro z hz
          have hz1 : z ∈ _root_.symmDiff X X' ∪ _root_.symmDiff X' Y := symmDiff_triangle X X' Y hz
          rcases hz1 with (hz1' | hz2')
          · exact Or.inl (Or.inl hz1')
          · have hz3 : z ∈ _root_.symmDiff X' Y' ∪ _root_.symmDiff Y' Y := symmDiff_triangle X' Y' Y hz2'
            rcases hz3 with (hz3' | hz4')
            · exact Or.inl (Or.inr hz3')
            · rw [symmDiff_comm] at hz4'
              exact Or.inr hz4'
        have h_image_sub : Subtype.val '' (_root_.symmDiff X Y) ⊆
            (Subtype.val '' (_root_.symmDiff X X')) ∪ (Subtype.val '' (_root_.symmDiff X' Y')) ∪
            (Subtype.val '' (_root_.symmDiff Y Y')) :=
          calc
            Subtype.val '' (_root_.symmDiff X Y) ⊆
                Subtype.val '' (_root_.symmDiff X X' ∪ _root_.symmDiff X' Y' ∪ _root_.symmDiff Y Y') :=
              Set.image_mono h_symm_sub
            _ = (Subtype.val '' (_root_.symmDiff X X')) ∪ (Subtype.val '' (_root_.symmDiff X' Y')) ∪
                (Subtype.val '' (_root_.symmDiff Y Y')) := by
              simp [Set.image_union, Set.union_assoc]
        have h_mono : Lebesgue_outer_measure (Subtype.val '' (_root_.symmDiff X Y)) ≤
            Lebesgue_outer_measure ((Subtype.val '' (_root_.symmDiff X X')) ∪
              (Subtype.val '' (_root_.symmDiff X' Y')) ∪ (Subtype.val '' (_root_.symmDiff Y Y'))) :=
          Lebesgue_outer_measure.mono h_image_sub
        have h_union_two (A B : Set (EuclideanSpace' d)) : (⋃ i : Fin 2, (λ
            | 0 => A
            | 1 => B) i) = A ∪ B := by
          ext w; simp
        have h_sub_union : Lebesgue_outer_measure ((Subtype.val '' (_root_.symmDiff X X')) ∪
            (Subtype.val '' (_root_.symmDiff X' Y')) ∪ (Subtype.val '' (_root_.symmDiff Y Y'))) ≤
            Lebesgue_outer_measure (Subtype.val '' (_root_.symmDiff X' Y')) := by
          have h_ineq1 : Lebesgue_outer_measure (((Subtype.val '' (_root_.symmDiff X X')) ∪
              (Subtype.val '' (_root_.symmDiff X' Y'))) ∪ (Subtype.val '' (_root_.symmDiff Y Y'))) ≤
              Lebesgue_outer_measure ((Subtype.val '' (_root_.symmDiff X X')) ∪
                (Subtype.val '' (_root_.symmDiff X' Y'))) +
              Lebesgue_outer_measure (Subtype.val '' (_root_.symmDiff Y Y')) := by
            let F : Fin 2 → Set (EuclideanSpace' d) := λ
              | 0 => (Subtype.val '' (_root_.symmDiff X X')) ∪ (Subtype.val '' (_root_.symmDiff X' Y'))
              | 1 => Subtype.val '' (_root_.symmDiff Y Y')
            have h_union_eq : (⋃ i : Fin 2, F i) = ((Subtype.val '' (_root_.symmDiff X X')) ∪
                (Subtype.val '' (_root_.symmDiff X' Y'))) ∪ (Subtype.val '' (_root_.symmDiff Y Y')) := by
              simpa [F] using h_union_two ((Subtype.val '' (_root_.symmDiff X X')) ∪
                (Subtype.val '' (_root_.symmDiff X' Y'))) (Subtype.val '' (_root_.symmDiff Y Y'))
            rw [← h_union_eq]
            simpa [F] using Lebesgue_outer_measure.finite_union_le F
          have h_ineq2 : Lebesgue_outer_measure ((Subtype.val '' (_root_.symmDiff X X')) ∪
              (Subtype.val '' (_root_.symmDiff X' Y'))) ≤
              Lebesgue_outer_measure (Subtype.val '' (_root_.symmDiff X X')) +
              Lebesgue_outer_measure (Subtype.val '' (_root_.symmDiff X' Y')) := by
            let F : Fin 2 → Set (EuclideanSpace' d) := λ
              | 0 => Subtype.val '' (_root_.symmDiff X X')
              | 1 => Subtype.val '' (_root_.symmDiff X' Y')
            have h_union_eq : (⋃ i : Fin 2, F i) = (Subtype.val '' (_root_.symmDiff X X')) ∪
                (Subtype.val '' (_root_.symmDiff X' Y')) := by
              simpa [F] using h_union_two (Subtype.val '' (_root_.symmDiff X X'))
                (Subtype.val '' (_root_.symmDiff X' Y'))
            rw [← h_union_eq]
            simpa [F] using Lebesgue_outer_measure.finite_union_le F
          calc
            Lebesgue_outer_measure ((Subtype.val '' (_root_.symmDiff X X')) ∪
              (Subtype.val '' (_root_.symmDiff X' Y')) ∪ (Subtype.val '' (_root_.symmDiff Y Y')))
                = Lebesgue_outer_measure (((Subtype.val '' (_root_.symmDiff X X')) ∪
                  (Subtype.val '' (_root_.symmDiff X' Y'))) ∪ (Subtype.val '' (_root_.symmDiff Y Y'))) := by
              simp [Set.union_assoc]
            _ ≤ Lebesgue_outer_measure ((Subtype.val '' (_root_.symmDiff X X')) ∪
                (Subtype.val '' (_root_.symmDiff X' Y'))) +
              Lebesgue_outer_measure (Subtype.val '' (_root_.symmDiff Y Y')) := h_ineq1
            _ ≤ (Lebesgue_outer_measure (Subtype.val '' (_root_.symmDiff X X')) +
              Lebesgue_outer_measure (Subtype.val '' (_root_.symmDiff X' Y'))) +
              Lebesgue_outer_measure (Subtype.val '' (_root_.symmDiff Y Y')) := by
              have := add_le_add_right h_ineq2 (Lebesgue_outer_measure (Subtype.val '' (_root_.symmDiff Y Y')))
              simpa [add_comm, add_left_comm, add_assoc] using this
            _ = Lebesgue_outer_measure (Subtype.val '' (_root_.symmDiff X X')) +
              Lebesgue_outer_measure (Subtype.val '' (_root_.symmDiff X' Y')) +
              Lebesgue_outer_measure (Subtype.val '' (_root_.symmDiff Y Y')) := by ring
            _ = 0 + Lebesgue_outer_measure (Subtype.val '' (_root_.symmDiff X' Y')) + 0 := by rw [hX, hY]
            _ = Lebesgue_outer_measure (Subtype.val '' (_root_.symmDiff X' Y')) := by simp
        calc
          Lebesgue_outer_measure (Subtype.val '' (_root_.symmDiff X Y))
              ≤ Lebesgue_outer_measure ((Subtype.val '' (_root_.symmDiff X X')) ∪
                (Subtype.val '' (_root_.symmDiff X' Y')) ∪ (Subtype.val '' (_root_.symmDiff Y Y'))) := h_mono
          _ ≤ Lebesgue_outer_measure (Subtype.val '' (_root_.symmDiff X' Y')) := h_sub_union
      have hE_eq' : IsNull (Subtype.val '' (_root_.symmDiff E' E)) := by
        simpa [symmDiff_comm] using hE_eq
      have hF_eq' : IsNull (Subtype.val '' (_root_.symmDiff F' F)) := by
        simpa [symmDiff_comm] using hF_eq
      exact le_antisymm (h_aux E F E' F' hE_eq hF_eq) (h_aux E' F' E F hE_eq' hF_eq')
    simp [h_meas_eq])

noncomputable instance IsElementary.metric {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A) : MetricSpace hA.ae_subsets := {
    dist := hA.dist
    dist_self := by
      intro x
      refine Quotient.inductionOn x ?_
      intro E
      unfold IsElementary.dist
      simp [symmDiff_self, Set.image_empty, Lebesgue_outer_measure.of_empty d]
    eq_of_dist_eq_zero := by sorry
    dist_comm := by
      intro x y
      refine Quotient.inductionOn₂ x y ?_
      intro E F
      unfold IsElementary.dist
      simp [symmDiff_comm]
    dist_triangle := by sorry
  }

instance IsElementary.complete {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A) : CompleteSpace hA.ae_subsets := by
  sorry

noncomputable def IsElementary.ae_elem {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A) : Set hA.ae_subsets := { E | ∃ F: Set A, IsElementary (Subtype.val '' F) ∧ hA.ae_quot F = E }

noncomputable def IsElementary.ae_measurable {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A) : Set hA.ae_subsets := { E | ∃ F: Set A, LebesgueMeasurable (Subtype.val '' F) ∧ hA.ae_quot F = E }

/-- Exercise 1.2.24(iii) (Lebesgue measure as the completion of elementary measure). -/
theorem IsElementary.measurable_eq_closure_elem {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A) : closure hA.ae_elem = hA.ae_measurable := by
  sorry

noncomputable def IsElementary.ae_measure {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A) (E: hA.ae_measurable) : ℝ := (Lebesgue_measure (Subtype.val '' E.property.choose)).toReal

noncomputable def IsElementary.ae_elem_measure {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A) (E: hA.ae_elem) : ℝ := E.property.choose_spec.1.measure

/-- Exercise 1.2.24(iv) (Lebesgue measure as the completion of elementary measure). -/
theorem IsElementary.ae_measure_eq_completion {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A) (m: hA.ae_subsets → ℝ) :
ContinuousOn m hA.ae_measurable ∧ (∀ (E:hA.ae_elem), m E.val = hA.ae_elem_measure E)
↔ (∀ (E:hA.ae_measurable), m E.val = hA.ae_measure E) := by sorry

noncomputable abbrev IsCurve {d:ℕ} (C: Set (EuclideanSpace' d)) : Prop := ∃ (a b:ℝ) (γ: ℝ → EuclideanSpace' d), C = γ '' (Set.Icc a b) ∧ ContDiffOn ℝ 1 γ (Set.Icc a b)

/-- Exercise 1.2.25(i) -/
theorem IsCurve.null {d:ℕ} (hd: d ≥ 2) {C: Set (EuclideanSpace' d)} (hC: IsCurve C) : IsNull C := by sorry

example : ∃ (d:ℕ) (C: Set (EuclideanSpace' d)) (hC: IsCurve C), ¬ IsNull C := by
  sorry

/-- Exercise 1.2.25 -/
example {d:ℕ} (hd: d ≥ 2) : ¬ ∃ C: ℕ → Set (EuclideanSpace' d), (∀ n, IsCurve (C n)) ∧ (⋃ n, C n = (Box.unit_cube d).toSet) := by
  sorry
