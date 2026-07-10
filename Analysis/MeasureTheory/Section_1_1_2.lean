import Analysis.MeasureTheory.Section_1_1_1
import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Normed.Module.Convex

set_option maxHeartbeats 0


/-!
# Introduction to Measure Theory, Section 1.1.2: Jordan measure

A companion to Section 1.1.2 of the book "An introduction to Measure Theory".

-/

/-- Definition 1.1.4.  We intend these concepts to only be applied for bounded sets {lean}`E`, but
it is convenient to permit {lean}`E` to be unbounded for the purposes of making the definitions.
-/
noncomputable abbrev Jordan_inner_measure {d:ℕ} (E: Set (EuclideanSpace' d)) : ℝ :=
  sSup { m:ℝ | ∃ (A: Set (EuclideanSpace' d)), ∃ hA: IsElementary A, A ⊆ E ∧ m = hA.measure }

noncomputable abbrev Jordan_outer_measure {d:ℕ} (E: Set (EuclideanSpace' d)) : ℝ :=
  sInf { m:ℝ | ∃ (A: Set (EuclideanSpace' d)), ∃ hA: IsElementary A, E ⊆ A ∧ m = hA.measure }

/-- A bounded set is Jordan measurable if its inner and outer Jordan measures coincide. -/
noncomputable abbrev JordanMeasurable {d:ℕ} (E: Set (EuclideanSpace' d)) : Prop :=
  Bornology.IsBounded E ∧ Jordan_inner_measure E = Jordan_outer_measure E

/-- The Jordan measure of a Jordan measurable set (equals both inner and outer measure). -/
noncomputable abbrev JordanMeasurable.measure {d:ℕ} {E: Set (EuclideanSpace' d)} (_: JordanMeasurable E) : ℝ :=
  Jordan_inner_measure E

/-- Jordan measure equals the inner Jordan measure by definition. -/
theorem JordanMeasurable.eq_inner {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: JordanMeasurable E) : hE.measure = Jordan_inner_measure E := rfl

/-- For Jordan measurable sets, the measure also equals the outer Jordan measure. -/
theorem JordanMeasurable.eq_outer {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: JordanMeasurable E) : hE.measure = Jordan_outer_measure E := by grind


/-- Any bounded set is contained in some elementary set (a sufficiently large box). -/
theorem IsElementary.contains_bounded {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E) : ∃ A: Set (EuclideanSpace' d), IsElementary A ∧ E ⊆ A := by
  -- Strategy:
  -- 1. Get bound M from boundedness: E ⊆ Metric.closedBall 0 M
  -- 2. Construct box B with Icc (-M') M' in each coordinate, where M' = max M 0 + 1
  -- 3. Show E ⊆ B.toSet: for x ∈ E, we have ‖x‖ ≤ M < M', so |x i| ≤ ‖x‖ < M' for each coordinate i
  -- 4. Use IsElementary.box to show B.toSet is elementary
  -- Step 1: Get bound M from boundedness
  rw [Metric.isBounded_iff_subset_closedBall 0] at hE
  obtain ⟨M, hE_ball⟩ := hE
  -- Step 2: Construct box B with Icc (-M') M' in each coordinate
  set M' := max M 0 + 1
  let B : Box d := {
    side := fun _ => BoundedInterval.Icc (-M') M'
  }
  -- Step 3: Show E ⊆ B.toSet
  have hE_subset : E ⊆ B.toSet := by
    intro x hx
    simp only [Box.mem_toSet]
    intro i
    have h_mem : x ∈ Metric.closedBall 0 M := hE_ball hx
    rw [Metric.mem_closedBall, dist_zero_right] at h_mem
    have h_M_bound : M ≤ max M 0 := le_max_left _ _
    have h_M'_bound : max M 0 < M' := by
      dsimp [M']
      exact lt_add_one (max M 0)
    have h_norm_bound : ‖x‖ < M' := lt_of_le_of_lt h_mem (lt_of_le_of_lt h_M_bound h_M'_bound)
    have h_coord_sq : (x i)^2 ≤ ∑ j, (x j)^2 := by
      exact Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    have h_coord : |x i| ≤ ‖x‖ := by
      rw [EuclideanSpace'.norm_eq]
      calc |x i| = Real.sqrt ((x i)^2) := by rw [Real.sqrt_sq_eq_abs]
        _ ≤ Real.sqrt (∑ j, (x j)^2) := Real.sqrt_le_sqrt h_coord_sq
    have h_abs_bound : |x i| < M' := lt_of_le_of_lt h_coord h_norm_bound
    constructor
    · have : -M' < x i := by
        rw [abs_lt] at h_abs_bound
        exact h_abs_bound.1
      linarith
    · have : x i < M' := by
        rw [abs_lt] at h_abs_bound
        exact h_abs_bound.2
      linarith
  -- Step 4: Show B.toSet is elementary
  have hB_elem : IsElementary B.toSet := IsElementary.box B
  exact ⟨B.toSet, hB_elem, hE_subset⟩

/-- The inner Jordan measure is always non-negative. -/
theorem Jordan_inner_measure_nonneg {d:ℕ} (E: Set (EuclideanSpace' d)) : 0 ≤ Jordan_inner_measure E := by
  -- Strategy:
  -- 1. Unfold the definition: Jordan_inner_measure E = sSup { m | ∃ A, IsElementary A, A ⊆ E ∧ m = hA.measure }
  -- 2. Apply Real.sSup_nonneg: this requires showing ∀ m in the set, 0 ≤ m
  -- 3. For any m in the set, extract the elementary set A and use IsElementary.measure_nonneg
  -- Note: Real.sSup_nonneg handles both empty and nonempty sets, so we don't need to show nonemptiness
  unfold Jordan_inner_measure
  apply Real.sSup_nonneg
  -- For any m in the set, there exists an elementary set A ⊆ E with m = hA.measure
  intro m hm
  -- Extract the elementary set and its measure
  obtain ⟨A, hA, hA_subset, rfl⟩ := hm
  -- Apply IsElementary.measure_nonneg to show 0 ≤ hA.measure
  exact IsElementary.measure_nonneg hA

/-- The outer Jordan measure is always non-negative. -/
theorem Jordan_outer_measure_nonneg {d:ℕ} (E: Set (EuclideanSpace' d)) : 0 ≤ Jordan_outer_measure E := by
  -- Strategy:
  -- 1. Unfold the definition: Jordan_outer_measure E = sInf { m | ∃ A, IsElementary A, E ⊆ A ∧ m = hA.measure }
  -- 2. Apply Real.sInf_nonneg: this requires showing ∀ m in the set, 0 ≤ m
  -- 3. For any m in the set, extract the elementary set A and use IsElementary.measure_nonneg
  -- Note: Real.sInf_nonneg handles both empty and nonempty sets, so we don't need to show nonemptiness
  unfold Jordan_outer_measure
  apply Real.sInf_nonneg
  -- For any m in the set, there exists an elementary set A ⊇ E with m = hA.measure
  intro m hm
  -- Extract the elementary set and its measure
  obtain ⟨A, hA, hE_subset, rfl⟩ := hm
  -- Apply IsElementary.measure_nonneg to show 0 ≤ hA.measure
  exact IsElementary.measure_nonneg hA

/-- For bounded sets, inner Jordan measure is at most outer Jordan measure. -/
theorem Jordan_inner_le_outer {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E) : Jordan_inner_measure E ≤ Jordan_outer_measure E := by
  -- Strategy:
  -- 1. Unfold both definitions to work with sSup and sInf directly
  -- 2. Use csSup_le to show that outer measure is an upper bound for inner measure set
  --    csSup_le requires two goals:
  --    a. Show inner measure set {A.measure | A ⊆ E, elementary} is nonempty (it contains at least 0)
  --    b. Show outer measure is an upper bound: for any m in inner measure set, m ≤ outer measure
  unfold Jordan_inner_measure Jordan_outer_measure
  apply csSup_le
  · -- Show the set is nonempty (it contains at least 0)
    use 0
    use ∅
    use IsElementary.empty d
    simp [IsElementary.measure_of_empty]
  · -- Show that sInf {B.measure | B ⊇ E, elementary} is an upper bound
    intro m hm
    obtain ⟨A, hA, hA_subset_E, rfl⟩ := hm
    -- For any elementary B ⊇ E, we have A ⊆ B, so A.measure ≤ B.measure
    -- Taking infimum over all such B gives A.measure ≤ sInf {B.measure | B ⊇ E, elementary}
    apply le_csInf
    · -- Show the outer measure set is nonempty (use IsElementary.contains_bounded)
      obtain ⟨B, hB, hE_subset_B⟩ := IsElementary.contains_bounded hE
      exact ⟨hB.measure, B, hB, hE_subset_B, rfl⟩
    · -- Show A.measure is a lower bound for the outer measure set
      intro b hb
      obtain ⟨B, hB, hE_subset_B, rfl⟩ := hb
      -- Since A ⊆ E ⊆ B, we have A ⊆ B, so A.measure ≤ B.measure
      exact IsElementary.measure_mono hA hB (Set.Subset.trans hA_subset_E hE_subset_B)

/-- Elementary measure of a subset is a lower bound for inner Jordan measure. -/
theorem le_Jordan_inner {d:ℕ} {E A: Set (EuclideanSpace' d)}
  (hA: IsElementary A) (_hAE: A ⊆ E) : hA.measure ≤ Jordan_inner_measure A := by
  -- Strategy:
  -- 1. Unfold definition: Jordan_inner_measure A = sSup { m | ∃ B, IsElementary B, B ⊆ A ∧ m = hB.measure }
  -- 2. Show hA.measure is in this set: use A itself (A ⊆ A, and hA.measure = hA.measure)
  -- 3. Show the set is bounded above by hA.measure: for any B ⊆ A elementary, B.measure ≤ A.measure by monotonicity
  -- 4. Apply le_csSup: any element of a set is ≤ its supremum
  unfold Jordan_inner_measure
  -- Step 2: Show hA.measure is in the set
  have h_mem : hA.measure ∈ { m:ℝ | ∃ (B: Set (EuclideanSpace' d)), ∃ hB: IsElementary B, B ⊆ A ∧ m = hB.measure } := by
    use A, hA, Set.Subset.refl A
  -- Step 3: Show the set is bounded above by hA.measure
  have h_bdd : BddAbove { m:ℝ | ∃ (B: Set (EuclideanSpace' d)), ∃ hB: IsElementary B, B ⊆ A ∧ m = hB.measure } := by
    use hA.measure
    intro m hm
    obtain ⟨B, hB, hB_subset_A, rfl⟩ := hm
    -- Since B ⊆ A and both are elementary, B.measure ≤ A.measure by monotonicity
    exact IsElementary.measure_mono hB hA hB_subset_A
  -- Step 4: Apply le_csSup
  exact le_csSup h_bdd h_mem

/-- Elementary measure of a superset is an upper bound for outer Jordan measure. -/
theorem Jordan_outer_le {d:ℕ} {E A: Set (EuclideanSpace' d)}
  (hA: IsElementary A) (_hAE: E ⊆ A) : Jordan_outer_measure A ≤ hA.measure := by
  -- Strategy:
  -- 1. Unfold definition: Jordan_outer_measure A = sInf { m | ∃ B, IsElementary B, A ⊆ B ∧ m = hB.measure }
  -- 2. Show hA.measure is in this set: use A itself (A ⊆ A, and hA.measure = hA.measure)
  -- 3. Show the set is bounded below by 0: for any B ⊇ A elementary, 0 ≤ B.measure by nonnegativity
  -- 4. Apply csInf_le: infimum of a set is ≤ any element in the set
  unfold Jordan_outer_measure
  -- Step 2: Show hA.measure is in the set
  have h_mem : hA.measure ∈ { m:ℝ | ∃ (B: Set (EuclideanSpace' d)), ∃ hB: IsElementary B, A ⊆ B ∧ m = hB.measure } := by
    use A, hA, Set.Subset.refl A
  -- Step 3: Show the set is bounded below by 0
  have h_bdd : BddBelow { m:ℝ | ∃ (B: Set (EuclideanSpace' d)), ∃ hB: IsElementary B, A ⊆ B ∧ m = hB.measure } := by
    use 0
    intro m hm
    obtain ⟨B, hB, _, rfl⟩ := hm
    -- Since B is elementary, 0 ≤ B.measure by nonnegativity
    exact IsElementary.measure_nonneg hB
  -- Step 4: Apply csInf_le
  exact csInf_le h_bdd h_mem

/-- If m < inner measure, there exists an elementary subset with measure > m. -/
theorem Jordan_inner_le {d:ℕ} {E: Set (EuclideanSpace' d)} {m:ℝ}
  (hm: m < Jordan_inner_measure E) : ∃ A: Set (EuclideanSpace' d), ∃ hA: IsElementary A, A ⊆ E ∧ m < hA.measure := by
  -- Strategy:
  -- 1. Unfold definition: Jordan_inner_measure E = sSup { m' | ∃ A, IsElementary A, A ⊆ E ∧ m' = hA.measure }
  -- 2. Show the set is nonempty (empty set is elementary with measure 0)
  -- 3. Apply exists_lt_of_lt_csSup to get existence of element greater than m
  -- 4. Extract the elementary set A from the witness
  unfold Jordan_inner_measure at hm
  set S := { m:ℝ | ∃ (A: Set (EuclideanSpace' d)), ∃ hA: IsElementary A, A ⊆ E ∧ m = hA.measure }
  -- Step 2: Show the set is nonempty
  have h_nonempty : S.Nonempty := by
    use 0
    use ∅
    use IsElementary.empty d
    constructor
    · exact Set.empty_subset E
    · exact Eq.symm (IsElementary.measure_of_empty d)
  -- Step 3: Apply exists_lt_of_lt_csSup to get existence of element greater than m
  obtain ⟨m', hm', hm_lt⟩ := exists_lt_of_lt_csSup h_nonempty hm
  -- Step 4: Extract the elementary set A from the witness
  obtain ⟨A, hA, hA_subset, rfl⟩ := hm'
  exact ⟨A, hA, hA_subset, hm_lt⟩

/-- If outer measure < m, there exists an elementary superset with measure < m. -/
theorem le_Jordan_outer {d:ℕ} {E: Set (EuclideanSpace' d)} {m:ℝ}
  (hm: Jordan_outer_measure E < m) (hbound: Bornology.IsBounded E) :
  ∃ A: Set (EuclideanSpace' d), ∃ hA: IsElementary A, E ⊆ A ∧ hA.measure < m := by
  -- Strategy:
  -- 1. Unfold definition: Jordan_outer_measure E = sInf { m' | ∃ A, IsElementary A, E ⊆ A ∧ m' = hA.measure }
  -- 2. Since sInf S < m, by properties of infimum, there exists x ∈ S with x < m
  -- 3. Use IsElementary.contains_bounded to show the set is nonempty (since E is bounded)
  -- 4. Apply exists_lt_of_csInf_lt to get existence of element less than m
  -- 5. Extract the elementary set A from the witness
  unfold Jordan_outer_measure at hm
  set S := { m:ℝ | ∃ (A: Set (EuclideanSpace' d)), ∃ hA: IsElementary A, E ⊆ A ∧ m = hA.measure }
  -- Step 3: Show the set is nonempty
  have h_nonempty : S.Nonempty := by
    obtain ⟨A, hA, hE_subset⟩ := IsElementary.contains_bounded hbound
    exact ⟨hA.measure, A, hA, hE_subset, rfl⟩
  -- Step 4: Apply exists_lt_of_csInf_lt to get existence of element less than m
  obtain ⟨m', hm', hm'_lt⟩ := exists_lt_of_csInf_lt h_nonempty hm
  -- Step 5: Extract the elementary set A from the witness
  obtain ⟨A, hA, hE_subset, rfl⟩ := hm'
  exact ⟨A, hA, hE_subset, hm'_lt⟩

/-- Elementary sets are bounded. -/
lemma IsElementary.isBounded {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: IsElementary E) : Bornology.IsBounded E := by
  obtain ⟨S, hE_eq⟩ := hE
  rw [hE_eq]
  refine (Bornology.isBounded_biUnion_finset _).mpr ?_
  intro B hB
  have h_box_bounded : Bornology.IsBounded (B.toSet : Set (EuclideanSpace' d)) := by
    have h_pi_bounded : Bornology.IsBounded (Set.pi Set.univ (fun i : Fin d => (B.side i : Set ℝ))) :=
      Bornology.IsBounded.pi (fun i => Bornology.IsBounded.of_boundedInterval (B.side i))
    have h_eq : B.toSet = (WithLp.ofLp (p := 2) : EuclideanSpace' d → (Fin d → ℝ)) ⁻¹'
        (Set.pi Set.univ (fun i : Fin d => (B.side i : Set ℝ))) := by
      ext x; simp [Box.mem_toSet, Set.mem_preimage, Set.mem_pi, Set.mem_univ]
    rw [h_eq]
    exact (PiLp.antilipschitzWith_ofLp 2 (fun _ : Fin d => ℝ)).isBounded_preimage h_pi_bounded
  exact h_box_bounded

/-- Exercise 1.1.5 -/
-- Equivalent characterizations of Jordan measurability: inner and outer measures coincide.
theorem JordanMeasurable.equiv {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E) :
 [JordanMeasurable E,
  ∀ ε>0, ∃ A, ∃ B, ∃ hA: IsElementary A, ∃ hB: IsElementary B,
    A ⊆ E ∧ E ⊆ B ∧ (hB.sdiff hA).measure ≤ ε,
  ∀ ε>0, ∃ A, ∃ _hA: IsElementary A, Jordan_outer_measure (symmDiff E A) ≤ ε].TFAE := by
  apply List.tfae_of_cycle
  · rw [List.isChain_cons_cons]
    refine ⟨?_, ?_⟩
    · -- 0 → 1: JordanMeasurable → elementary approximation
      intro hJM
      rcases hJM with ⟨hEbounded, h_eq⟩
      intro ε hε
      set m := Jordan_inner_measure E with hm
      have hm_outer : Jordan_outer_measure E = m := by rw [← h_eq, hm]
      have h_inner_exists : ∃ A, ∃ hA : IsElementary A, A ⊆ E ∧ (m - ε/2) < hA.measure := by
        apply Jordan_inner_le; dsimp [m]; linarith
      obtain ⟨A, hA, hA_sub_E, hA_gt⟩ := h_inner_exists
      have h_outer_exists : ∃ B, ∃ hB : IsElementary B, E ⊆ B ∧ hB.measure < (m + ε/2) := by
        apply le_Jordan_outer; rw [hm_outer]; linarith
        exact hEbounded
      obtain ⟨B, hB, hE_sub_B, hB_lt⟩ := h_outer_exists
      have hAB : A ⊆ B := hA_sub_E.trans hE_sub_B
      have h_union_eq : A ∪ (B \ A) = B := by
        ext x; constructor
        · rintro (hx | ⟨hxB, hxA⟩)
          · exact hAB hx
          · exact hxB
        · intro hx
          classical
            by_cases hxA : x ∈ A
            · exact Or.inl hxA
            · exact Or.inr ⟨hx, hxA⟩
      have h_disjoint : Disjoint A (B \ A) := disjoint_sdiff_self_right
      have h_measure_eq : hB.measure = hA.measure + (hB.sdiff hA).measure := by
        have h_union_measure : (hA.union (hB.sdiff hA)).measure = hA.measure + (hB.sdiff hA).measure :=
          IsElementary.measure_of_disjUnion hA (hB.sdiff hA) h_disjoint
        have h_same_set : (hA.union (hB.sdiff hA)).measure = hB.measure :=
          IsElementary.measure_eq_of_set_eq (hA.union (hB.sdiff hA)) hB h_union_eq
        calc
          hB.measure = (hA.union (hB.sdiff hA)).measure := by symm; exact h_same_set
          _ = hA.measure + (hB.sdiff hA).measure := h_union_measure
      have h_diff_lt : (hB.sdiff hA).measure ≤ ε := by
        have : hB.measure - hA.measure < ε := by linarith
        linarith
      exact ⟨A, B, hA, hB, hA_sub_E, hE_sub_B, h_diff_lt⟩
    · rw [List.isChain_cons_cons]
      refine ⟨?_, ?_⟩
      · -- 1 → 2: elementary approximation → symmDiff small
        intro h_approx ε hε
        obtain ⟨A, B, hA, hB, hA_sub_E, hE_sub_B, h_diff⟩ := h_approx ε hε
        have h_symm_eq : symmDiff E A = E \ A := by
          rw [symmDiff_def]
          simp [hA_sub_E]
        have h_sub : E \ A ⊆ B \ A := Set.diff_subset_diff hE_sub_B (Set.Subset.refl A)
        have h_outer_B_A : Jordan_outer_measure (B \ A) ≤ (hB.sdiff hA).measure :=
          Jordan_outer_le (hB.sdiff hA) (Set.Subset.refl _)
        have h_outer_E_A : Jordan_outer_measure (E \ A) ≤ Jordan_outer_measure (B \ A) := by
          set s := { m : ℝ | ∃ (C : Set (EuclideanSpace' d)), ∃ hC : IsElementary C, (B \ A) ⊆ C ∧ m = hC.measure }
          set t := { m : ℝ | ∃ (C : Set (EuclideanSpace' d)), ∃ hC : IsElementary C, (E \ A) ⊆ C ∧ m = hC.measure }
          have hst : s ⊆ t := by
            rintro m ⟨C, hC, hC_sub, rfl⟩
            exact ⟨C, hC, h_sub.trans hC_sub, rfl⟩
          have hBdd : BddBelow t := by
            refine ⟨0, ?_⟩
            rintro m ⟨C, hC, hC_sub, rfl⟩
            exact IsElementary.measure_nonneg hC
          have hNonempty : s.Nonempty := ⟨(hB.sdiff hA).measure, B \ A, hB.sdiff hA, Set.Subset.refl _, rfl⟩
          calc
            Jordan_outer_measure (E \ A) = sInf t := rfl
            _ ≤ sInf s := csInf_le_csInf hBdd hNonempty hst
            _ = Jordan_outer_measure (B \ A) := rfl
        have h_outer_le : Jordan_outer_measure (symmDiff E A) ≤ (hB.sdiff hA).measure := by
          rw [h_symm_eq]
          exact le_trans h_outer_E_A h_outer_B_A
        exact ⟨A, hA, le_trans h_outer_le h_diff⟩
      · simp
  · -- 2 → 0: symmDiff small → JordanMeasurable
    intro h_symm
    have h_eq : Jordan_inner_measure E = Jordan_outer_measure E := by
      apply le_antisymm (Jordan_inner_le_outer hE)
      refine le_of_forall_pos_le_add ?_
      intro ε hε
      obtain ⟨A, hA, h_symm_outer⟩ := h_symm (ε/2) (by linarith)
      have h_nonempty : { m : ℝ | ∃ (C : Set (EuclideanSpace' d)), ∃ hC : IsElementary C, symmDiff E A ⊆ C ∧ m = hC.measure }.Nonempty := by
        obtain ⟨B, hB, hE_sub_B⟩ := IsElementary.contains_bounded hE
        refine ⟨(hB.union hA).measure, B ∪ A, hB.union hA, ?_, rfl⟩
        rw [symmDiff_def]
        apply Set.union_subset_union
        · exact Set.diff_subset.trans hE_sub_B
        · exact Set.diff_subset
      have h_sInf_lt : sInf { m : ℝ | ∃ (C : Set (EuclideanSpace' d)), ∃ hC : IsElementary C, symmDiff E A ⊆ C ∧ m = hC.measure } < ε := by
        have h_outer_eq : Jordan_outer_measure (symmDiff E A) =
            sInf { m : ℝ | ∃ (C : Set (EuclideanSpace' d)), ∃ hC : IsElementary C, symmDiff E A ⊆ C ∧ m = hC.measure } := rfl
        rw [← h_outer_eq]; linarith
      obtain ⟨m, hm, hm_lt⟩ := exists_lt_of_csInf_lt h_nonempty h_sInf_lt
      obtain ⟨C, hC, h_symm_sub_C, rfl⟩ := hm
      set A₁ := A \ C
      set B := A ∪ C
      have hA₁_elem : IsElementary A₁ := hA.sdiff hC
      have hB_elem : IsElementary B := hA.union hC
      have hA₁_sub_E : A₁ ⊆ E := by
        intro x hx
        obtain ⟨hxA, hx_not_C⟩ := hx
        by_contra hx_not_E
        have : x ∈ symmDiff E A := by
          rw [symmDiff_def]
          exact Or.inr ⟨hxA, hx_not_E⟩
        exact hx_not_C (h_symm_sub_C this)
      have hE_sub_B : E ⊆ B := by
        intro x hx
        by_cases hxA : x ∈ A
        · exact Or.inl hxA
        · have : x ∈ symmDiff E A := by
            rw [symmDiff_def]
            exact Or.inl ⟨hx, hxA⟩
          exact Or.inr (h_symm_sub_C this)
      have h_set_eq : B \ A₁ = C := by
        ext x; constructor
        · rintro ⟨hx_union, hx_not_A₁⟩
          rcases hx_union with (hxA | hxC)
          · by_contra hx_not_C
            apply hx_not_A₁
            exact ⟨hxA, hx_not_C⟩
          · exact hxC
        · intro hxC
          refine ⟨Or.inr hxC, ?_⟩
          intro hx_A₁
          obtain ⟨hxA, hx_not_C⟩ := hx_A₁
          exact hx_not_C hxC
      have h_measure_eq : (hB_elem.sdiff hA₁_elem).measure = hC.measure :=
        IsElementary.measure_eq_of_set_eq (hB_elem.sdiff hA₁_elem) hC h_set_eq
      have h_diff_le : (hB_elem.sdiff hA₁_elem).measure ≤ ε := by
        rw [h_measure_eq]; linarith
      have h_inner_upper_bound : hA₁_elem.measure ≤ Jordan_inner_measure E := by
        have h_mem : hA₁_elem.measure ∈ { m : ℝ | ∃ (X : Set (EuclideanSpace' d)), ∃ hX : IsElementary X, X ⊆ E ∧ m = hX.measure } :=
          ⟨A₁, hA₁_elem, hA₁_sub_E, rfl⟩
        have h_bdd : BddAbove { m : ℝ | ∃ (X : Set (EuclideanSpace' d)), ∃ hX : IsElementary X, X ⊆ E ∧ m = hX.measure } := by
          obtain ⟨U, hU, hEU⟩ := IsElementary.contains_bounded hE
          refine ⟨hU.measure, ?_⟩
          rintro m' ⟨X, hX, hXE, rfl⟩
          exact IsElementary.measure_mono hX hU (hXE.trans hEU)
        exact le_csSup h_bdd h_mem
      have h_outer_lower_bound : Jordan_outer_measure E ≤ hB_elem.measure := by
        have h_mem : hB_elem.measure ∈ { m : ℝ | ∃ (Y : Set (EuclideanSpace' d)), ∃ hY : IsElementary Y, E ⊆ Y ∧ m = hY.measure } :=
          ⟨B, hB_elem, hE_sub_B, rfl⟩
        have h_bdd : BddBelow { m : ℝ | ∃ (Y : Set (EuclideanSpace' d)), ∃ hY : IsElementary Y, E ⊆ Y ∧ m = hY.measure } := by
          refine ⟨0, ?_⟩
          rintro m' ⟨Y, hY, hEY, rfl⟩
          exact IsElementary.measure_nonneg hY
        exact csInf_le h_bdd h_mem
      have hB_measure_eq : hB_elem.measure = hA₁_elem.measure + (hB_elem.sdiff hA₁_elem).measure := by
        have h_union_eq' : A₁ ∪ (B \ A₁) = B := by
          ext x; constructor
          · rintro (hx | ⟨hxB, hxA₁⟩)
            · exact hA₁_sub_E.trans hE_sub_B hx
            · exact hxB
          · intro hx
            by_cases hxA₁ : x ∈ A₁
            · exact Or.inl hxA₁
            · exact Or.inr ⟨hx, hxA₁⟩
        have h_disjoint' : Disjoint A₁ (B \ A₁) := disjoint_sdiff_self_right
        have h_union_measure : (hA₁_elem.union (hB_elem.sdiff hA₁_elem)).measure = hA₁_elem.measure + (hB_elem.sdiff hA₁_elem).measure :=
          IsElementary.measure_of_disjUnion hA₁_elem (hB_elem.sdiff hA₁_elem) h_disjoint'
        have h_same_set' : (hA₁_elem.union (hB_elem.sdiff hA₁_elem)).measure = hB_elem.measure :=
          IsElementary.measure_eq_of_set_eq (hA₁_elem.union (hB_elem.sdiff hA₁_elem)) hB_elem h_union_eq'
        calc
          hB_elem.measure = (hA₁_elem.union (hB_elem.sdiff hA₁_elem)).measure := by symm; exact h_same_set'
          _ = hA₁_elem.measure + (hB_elem.sdiff hA₁_elem).measure := h_union_measure
      have h_outer_sub_inner : Jordan_outer_measure E ≤ Jordan_inner_measure E + ε := by
        calc
          Jordan_outer_measure E ≤ hB_elem.measure := h_outer_lower_bound
          _ = hA₁_elem.measure + (hB_elem.sdiff hA₁_elem).measure := hB_measure_eq
          _ ≤ Jordan_inner_measure E + (hB_elem.sdiff hA₁_elem).measure := by
            nlinarith
          _ ≤ Jordan_inner_measure E + ε := by nlinarith
      exact h_outer_sub_inner
    exact ⟨hE, h_eq⟩

/-- Every elementary set is Jordan measurable. -/
theorem IsElementary.jordanMeasurable {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: IsElementary E) : JordanMeasurable E := by
  have h_bounded : Bornology.IsBounded E := hE.isBounded
  have h_eq : Jordan_inner_measure E = Jordan_outer_measure E := by
    apply le_antisymm
    · exact Jordan_inner_le_outer h_bounded
    · calc
      Jordan_outer_measure E ≤ hE.measure := Jordan_outer_le hE (Set.Subset.refl E)
      _ ≤ Jordan_inner_measure E := le_Jordan_inner hE (Set.Subset.refl E)
  exact ⟨h_bounded, h_eq⟩

/-- The Jordan measure of an elementary set equals its elementary measure. -/
theorem JordanMeasurable.mes_of_elementary {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: IsElementary E) : hE.jordanMeasurable.measure = hE.measure := by
  rw [hE.jordanMeasurable.eq_inner]
  apply le_antisymm
  · -- Jordan_inner_measure E ≤ hE.measure
    dsimp [Jordan_inner_measure]
    apply csSup_le
    · -- set is nonempty
      refine ⟨0, ∅, IsElementary.empty d, Set.empty_subset E, ?_⟩
      exact Eq.symm (IsElementary.measure_of_empty d)
    · -- hE.measure is an upper bound
      intro m hm
      obtain ⟨A, hA, hA_sub_E, rfl⟩ := hm
      exact IsElementary.measure_mono hA hE hA_sub_E
  · -- hE.measure ≤ Jordan_inner_measure E
    exact le_Jordan_inner hE (Set.Subset.refl E)

/-- The empty set is Jordan measurable. -/
theorem JordanMeasurable.empty (d:ℕ) : JordanMeasurable (∅: Set (EuclideanSpace' d)) :=
  (IsElementary.empty d).jordanMeasurable

/-- The empty set has Jordan measure zero. -/
@[simp]
theorem JordanMeasurable.mes_of_empty (d:ℕ) : (JordanMeasurable.empty d).measure = 0 := by
  rw [JordanMeasurable.mes_of_elementary (IsElementary.empty d), IsElementary.measure_of_empty d]


/-- Exercise 1.1.6 (i) (Boolean closure) -/
theorem JordanMeasurable.union {d:ℕ} {E F : Set (EuclideanSpace' d)}
  (hE: JordanMeasurable E) (hF: JordanMeasurable F) : JordanMeasurable (E ∪ F) := by
  -- Since $E$ and $F$ are both Jordan measurable, they are bounded.
  have hE_bounded : Bornology.IsBounded E := by
    exact hE.1
  have hF_bounded : Bornology.IsBounded F := by
    exact hF.1;
  constructor;
  · exact hE_bounded.union hF_bounded;
  · -- Since $E$ and $F$ are Jordan measurable, their inner and outer measures are equal.
    have h_inner_outer_eq : ∀ ε > 0, ∃ A B : Set (EuclideanSpace' d), ∃ hA : IsElementary A, ∃ hB : IsElementary B, A ⊆ E ∪ F ∧ E ∪ F ⊆ B ∧ (IsElementary.measure (hB.sdiff hA)) ≤ ε := by
      intro ε hε_pos
      obtain ⟨A₁, B₁, hA₁, hB₁, hA₁_subset_E, hE_subset_B₁, hB₁_minus_A₁⟩ : ∃ A₁ B₁ : Set (EuclideanSpace' d), ∃ hA₁ : IsElementary A₁, ∃ hB₁ : IsElementary B₁, A₁ ⊆ E ∧ E ⊆ B₁ ∧ (IsElementary.measure (hB₁.sdiff hA₁)) ≤ ε / 2 := by
        have := JordanMeasurable.equiv hE_bounded |>.out 0 1 ; simp_all only [gt_iff_lt, exists_and_left, implies_true,
          iff_true, div_pos_iff_of_pos_left, Nat.ofNat_pos]
      obtain ⟨A₂, B₂, hA₂, hB₂, hA₂_subset_F, hF_subset_B₂, hB₂_minus_A₂⟩ : ∃ A₂ B₂ : Set (EuclideanSpace' d), ∃ hA₂ : IsElementary A₂, ∃ hB₂ : IsElementary B₂, A₂ ⊆ F ∧ F ⊆ B₂ ∧ (IsElementary.measure (hB₂.sdiff hA₂)) ≤ ε / 2 := by
        have := JordanMeasurable.equiv hF_bounded |>.out 0 1;
        exact this.mp hF ( ε / 2 ) ( half_pos hε_pos ) |> fun ⟨ A₂, B₂, hA₂, hB₂, hA₂_subset_F, hF_subset_B₂, hB₂_minus_A₂ ⟩ => ⟨ A₂, B₂, hA₂, hB₂, hA₂_subset_F, hF_subset_B₂, by linarith ⟩;
      refine' ⟨ A₁ ∪ A₂, B₁ ∪ B₂, _, _, _, _, _ ⟩ <;> try { exact hA₁.union hA₂ } <;> try { exact hB₁.union hB₂ } <;> try { exact Set.union_subset_union hA₁_subset_E hA₂_subset_F } <;> try { exact Set.union_subset_union hE_subset_B₁ hF_subset_B₂ };
      refine' le_trans ( le_trans ( IsElementary.measure_mono _ _ _ ) ( IsElementary.measure_of_union _ _ ) ) _;
      rotate_left;
      exact B₁ \ A₁
      exact B₂ \ A₂
      exact hB₁.sdiff hA₁
      exact hB₂.sdiff hA₂
      exact by linarith! [ hB₁_minus_A₁, hB₂_minus_A₂ ] ;
      intro x hx; simp_all only [gt_iff_lt, Set.mem_diff, Set.mem_union, not_or, not_false_eq_true, and_true];
    refine' le_antisymm _ _;
    · apply_rules [ Jordan_inner_le_outer ];
      exact hE_bounded.union hF_bounded;
    · refine' le_of_forall_pos_le_add fun ε ε_pos => _;
      obtain ⟨ A, B, hA, hB, hA_sub, hB_sub, hAB ⟩ := h_inner_outer_eq ( ε / 2 ) ( half_pos ε_pos );
      -- Since $A \subseteq E \cup F \subseteq B$, we have $m(A) \leq m(E \cup F) \leq m(B)$.
      have h_bounds : hA.measure ≤ Jordan_inner_measure (E ∪ F) ∧ Jordan_outer_measure (E ∪ F) ≤ hB.measure := by
        apply And.intro;
        · exact le_csSup ( show BddAbove { m : ℝ | ∃ A : Set ( EuclideanSpace' d ), ∃ hA : IsElementary A, A ⊆ E ∪ F ∧ m = hA.measure } from ⟨ hB.measure, by rintro m ⟨ A, hA, hA_sub, rfl ⟩ ; exact le_trans ( IsElementary.measure_mono hA hB ( by tauto ) ) ( by linarith ) ⟩ ) ⟨ A, hA, hA_sub, rfl ⟩;
        · exact csInf_le ⟨ 0, by rintro x ⟨ A, hA, hA_sub, rfl ⟩ ; exact IsElementary.measure_nonneg _ ⟩ ⟨ B, hB, hB_sub, rfl ⟩;
      -- Since $A \subseteq E \cup F \subseteq B$, we have $m(B) \leq m(A) + m(B \setminus A)$.
      have h_measure_B : hB.measure ≤ hA.measure + (IsElementary.measure (hB.sdiff hA)) := by
        have h_measure_B : hB.measure ≤ (IsElementary.measure (hA.union (hB.sdiff hA))) := by
          apply_rules [ IsElementary.measure_mono ];
          grind;
        refine le_trans h_measure_B ?_;
        exact IsElementary.measure_of_union hA (IsElementary.sdiff hB hA);
      linarith

/-- The union of a finset of Jordan measurable sets is Jordan measurable. -/
lemma JordanMeasurable.union' {d:ℕ} {S: Finset (Set (EuclideanSpace' d))}
(hE: ∀ E ∈ S, JordanMeasurable E) : JordanMeasurable (⋃ E ∈ S, E) := by
  induction' S using Finset.induction with E S ih hS;
  simp +zetaDelta at *;
  exact empty d;
  norm_num +zetaDelta at *;
  · exact JordanMeasurable.union hE.1 ( hS hE.2 );

/-- Exercise 1.1.6 (i) (Boolean closure) -/
theorem JordanMeasurable.inter {d:ℕ} {E F : Set (EuclideanSpace' d)}
  (hE: JordanMeasurable E) (hF: JordanMeasurable F) : JordanMeasurable (E ∩ F) := by
  -- Since $E$ and $F$ are bounded, $E \cap F$ is also bounded.
  have h_bound : Bornology.IsBounded (E ∩ F) := by
    exact hE.1.subset ( Set.inter_subset_left );
  -- Since $E$ and $F$ are bounded, their intersection $E \cap F$ is also bounded. We'll use the fact that the intersection of two Jordan measurable sets is Jordan measurable.
  have h_jordan_measurable : ∀ ε > 0, ∃ A B : Set (EuclideanSpace' d), ∃ hA : IsElementary A, ∃ hB : IsElementary B, A ⊆ E ∩ F ∧ E ∩ F ⊆ B ∧ (hB.sdiff hA).measure ≤ ε := by
    -- Since $E$ and $F$ are bounded, we can find elementary sets $A$ and $B$ such that $A \subseteq E \cap F \subseteq B$ and $|B| - |A| \leq \epsilon$.
    have h_jordan_measurable : ∀ ε > 0, ∃ A B : Set (EuclideanSpace' d), ∃ hA : IsElementary A, ∃ hB : IsElementary B, A ⊆ E ∧ E ⊆ B ∧ (hB.sdiff hA).measure ≤ ε / 2 ∧ ∃ C D : Set (EuclideanSpace' d), ∃ hC : IsElementary C, ∃ hD : IsElementary D, C ⊆ F ∧ F ⊆ D ∧ (hD.sdiff hC).measure ≤ ε / 2 := by
      intro ε hε_pos
      obtain ⟨A, B, hA, hB, hA_sub, hB_sup, hA_B⟩ : ∃ A B : Set (EuclideanSpace' d), ∃ hA : IsElementary A, ∃ hB : IsElementary B, A ⊆ E ∧ E ⊆ B ∧ (hB.sdiff hA).measure ≤ ε / 2 := by
        have := JordanMeasurable.equiv (hE.1) |>.out 0 1; simp_all only [gt_iff_lt, exists_and_left, implies_true,
          iff_true, div_pos_iff_of_pos_left, Nat.ofNat_pos];
      obtain ⟨C, D, hC, hD, hC_sub, hD_sup, hC_D⟩ : ∃ C D : Set (EuclideanSpace' d), ∃ hC : IsElementary C, ∃ hD : IsElementary D, C ⊆ F ∧ F ⊆ D ∧ (hD.sdiff hC).measure ≤ ε / 2 := by
        have := JordanMeasurable.equiv ( show Bornology.IsBounded F from hF.1 ) |>.out 0 1;
        exact this.mp hF ( ε / 2 ) ( half_pos hε_pos ) |> fun ⟨ C, D, hC, hD, hC_sub, hD_sup, hC_D ⟩ => ⟨ C, D, hC, hD, hC_sub, hD_sup, by linarith ⟩
      use A, B, hA, hB, hA_sub, hB_sup, hA_B, C, D, hC, hD, hC_sub, hD_sup, hC_D;
    intro ε hε_pos
    obtain ⟨A, B, hA, hB, hAE, hEB, hAB, C, D, hC, hD, hCF, hFD, hCD⟩ := h_jordan_measurable ε hε_pos
    use A ∩ C, B ∩ D;
    refine' ⟨ _, _, _, _, _ ⟩;
    exact IsElementary.inter hA hC;
    exact IsElementary.inter hB hD;
    · exact Set.inter_subset_inter hAE hCF;
    · exact Set.inter_subset_inter hEB hFD;
    · -- Since $A \cap C \subseteq B \cap D$, we have $(B \cap D) \setminus (A \cap C) \subseteq (B \setminus A) \cup (D \setminus C)$.
      have h_subset : (B ∩ D) \ (A ∩ C) ⊆ (B \ A) ∪ (D \ C) := by
        simp +contextual [ Set.subset_def ];
        tauto;
      -- Since the measure of a union is less than or equal to the sum of the measures, we have:
      have h_measure_union : (IsElementary.union (hB.sdiff hA) (hD.sdiff hC)).measure ≤ (hB.sdiff hA).measure + (hD.sdiff hC).measure := by
        exact IsElementary.measure_of_union (IsElementary.sdiff hB hA) (IsElementary.sdiff hD hC);
      refine' le_trans _ ( h_measure_union.trans _ );
      · apply_rules [ IsElementary.measure_mono ];
      · linarith!;
  have h_jordan_measurable : ∀ ε > 0, Jordan_outer_measure (E ∩ F) - Jordan_inner_measure (E ∩ F) ≤ ε := by
    intro ε hε_pos
    obtain ⟨A, B, hA, hB, hA_sub, hB_sub, h_diff⟩ := h_jordan_measurable ε hε_pos
    have h_diff_le : Jordan_outer_measure (E ∩ F) ≤ hB.measure ∧ hA.measure ≤ Jordan_inner_measure (E ∩ F) := by
      exact ⟨ csInf_le ⟨ 0, by rintro x ⟨ C, hC, hC_sub, rfl ⟩ ; exact IsElementary.measure_nonneg hC ⟩ ⟨ B, hB, hB_sub, rfl ⟩, le_csSup ⟨ hB.measure, by rintro x ⟨ C, hC, hC_sub, rfl ⟩ ; exact IsElementary.measure_mono hC hB ( Set.Subset.trans hC_sub hB_sub ) ⟩ ⟨ A, hA, hA_sub, rfl ⟩ ⟩;
    have h_diff_eq : hB.measure = hA.measure + (hB.sdiff hA).measure := by
      have h_disjoint : Disjoint A (B \ A) := by
        exact disjoint_sdiff_self_right
      convert IsElementary.measure_of_disjUnion hA ( IsElementary.sdiff hB hA ) h_disjoint using 1;
      convert IsElementary.measure_irrelevant _ _;
      · exact Set.union_diff_cancel' (fun ⦃a⦄ a ↦ a) fun ⦃a⦄ a_1 ↦ hB_sub (hA_sub a_1);
      · exact hB;
    linarith;
  have h_jordan_measurable : Jordan_outer_measure (E ∩ F) - Jordan_inner_measure (E ∩ F) = 0 := by
    exact le_antisymm ( le_of_forall_pos_le_add fun ε hε => by linarith [ h_jordan_measurable ε hε ] ) ( sub_nonneg_of_le <| Jordan_inner_le_outer h_bound );
  exact ⟨ h_bound, by linarith ⟩

/-- Exercise 1.1.6 (i) (Boolean closure) -/
theorem JordanMeasurable.sdiff {d:ℕ} {E F : Set (EuclideanSpace' d)}
  (hE: JordanMeasurable E) (hF: JordanMeasurable F) : JordanMeasurable (E \ F) := by
  refine' ⟨ _, _ ⟩;
  · exact hE.1.subset ( Set.diff_subset );
  · have h_diff : ∀ ε > 0, ∃ A B : Set (EuclideanSpace' d), ∃ hA : IsElementary A, ∃ hB : IsElementary B, A ⊆ E \ F ∧ E \ F ⊆ B ∧ (hB.sdiff hA).measure ≤ ε := by
      have h_diff : ∀ ε > 0, ∃ A B : Set (EuclideanSpace' d), ∃ hA : IsElementary A, ∃ hB : IsElementary B, A ⊆ E ∧ E ⊆ B ∧ (hB.sdiff hA).measure ≤ ε / 2 ∧ ∃ C D : Set (EuclideanSpace' d), ∃ hC : IsElementary C, ∃ hD : IsElementary D, C ⊆ F ∧ F ⊆ D ∧ (hD.sdiff hC).measure ≤ ε / 2 := by
        intros ε hε_pos
        obtain ⟨A, B, hA, hB, hAB⟩ : ∃ A B : Set (EuclideanSpace' d), ∃ hA : IsElementary A, ∃ hB : IsElementary B, A ⊆ E ∧ E ⊆ B ∧ (hB.sdiff hA).measure ≤ ε / 2 := by
          have := JordanMeasurable.equiv hE.1 |>.out 0 1;
          exact this.mp hE ( ε / 2 ) ( half_pos hε_pos );
        have h_diff : ∀ ε > 0, ∃ C D : Set (EuclideanSpace' d), ∃ hC : IsElementary C, ∃ hD : IsElementary D, C ⊆ F ∧ F ⊆ D ∧ (hD.sdiff hC).measure ≤ ε / 2 := by
          have := JordanMeasurable.equiv hF.1;
          have := this.out 0 1;
          intro ε_1 a
          simp_all only [gt_iff_lt, exists_and_left, implies_true, exists_prop, List.tfae_cons_self, iff_true,
            div_pos_iff_of_pos_left, Nat.ofNat_pos];
        exact ⟨ A, B, hA, hB, hAB.1, hAB.2.1, hAB.2.2, h_diff ε hε_pos ⟩;
      intro ε hε
      obtain ⟨A, B, hA, hB, hA_sub_E, hE_sub_B, hB_diff_A, C, D, hC, hD, hC_sub_F, hF_sub_D, hD_diff_C⟩ := h_diff ε hε;
      use A \ D, B \ C;
      refine' ⟨ hA.sdiff hD, hB.sdiff hC, _, _, _ ⟩;
      · exact fun x hx => ⟨ hA_sub_E hx.1, fun hx' => hx.2 <| hF_sub_D hx' ⟩;
      · exact Set.diff_subset_diff hE_sub_B hC_sub_F;
      · refine' le_trans ( IsElementary.measure_mono _ _ _ ) _;
        exact ( B \ A ) ∪ ( D \ C );
        exact IsElementary.union ( hB.sdiff hA ) ( hD.sdiff hC );
        · grind only [= Set.setOf_true, = Set.mem_union, = Set.subset_def, = Set.setOf_false, = Set.mem_diff];
        · exact le_trans ( IsElementary.measure_of_union _ _ ) ( by linarith );
    refine' le_antisymm _ _;
    · apply_rules [ Jordan_inner_le_outer ];
      exact hE.1.subset ( Set.diff_subset );
    · refine' le_of_forall_pos_le_add fun ε ε_pos => _;
      obtain ⟨ A, B, hA, hB, hA', hB', h ⟩ := h_diff ε ε_pos;
      refine' le_trans ( csInf_le _ ⟨ B, hB, hB', rfl ⟩ ) _;
      · exact ⟨ 0, by rintro x ⟨ A, hA, hA', rfl ⟩ ; exact hA.measure_nonneg ⟩;
      · -- Since $A \subseteq E \setminus F$, we have $hA.measure \leq \text{Jordan\_inner\_measure} (E \setminus F)$.
        have hA_le_inner : hA.measure ≤ Jordan_inner_measure (E \ F) := by
          exact le_csSup ⟨ _, fun m hm => by obtain ⟨ A, hA, hA', rfl ⟩ := hm; exact le_csSup ( show BddAbove { m : ℝ | ∃ A : Set ( EuclideanSpace' d ), ∃ hA : IsElementary A, A ⊆ E \ F ∧ m = hA.measure } from ⟨ _, fun m hm => by obtain ⟨ A, hA, hA', rfl ⟩ := hm; exact le_csSup ( show BddAbove { m : ℝ | ∃ A : Set ( EuclideanSpace' d ), ∃ hA : IsElementary A, A ⊆ E \ F ∧ m = hA.measure } from by
                                                                                                                                                                                                                                                                                          refine' ⟨ _, fun m hm => _ ⟩;
                                                                                                                                                                                                                                                                                          exact hB.measure;
                                                                                                                                                                                                                                                                                          obtain ⟨ A, hA, hA', rfl ⟩ := hm;
                                                                                                                                                                                                                                                                                          exact IsElementary.measure_mono hA hB fun ⦃a⦄ a_1 ↦ hB' (hA' a_1) ) ⟨ A, hA, hA', rfl ⟩ ⟩ ) ⟨ A, hA, hA', rfl ⟩ ⟩ ⟨ A, hA, hA', rfl ⟩;
        have hB_le_inner : hB.measure ≤ hA.measure + (hB.sdiff hA).measure := by
          have hB_le_inner : hB.measure ≤ (hA.union (hB.sdiff hA)).measure := by
            apply_rules [ IsElementary.measure_mono ];
            exact fun x hx => by by_cases hx' : x ∈ A <;> simp_all only [gt_iff_lt, exists_and_left,
              Set.union_diff_self, Set.mem_union, or_true];
          exact hB_le_inner.trans ( by simpa using IsElementary.measure_of_disjUnion hA ( hB.sdiff hA ) ( Set.disjoint_left.mpr fun x hx₁ hx₂ => by simp_all only [gt_iff_lt,
            exists_and_left, Set.union_diff_self, Set.mem_diff, not_true_eq_false, and_false] ) |> le_of_eq );
        linarith

/-- Exercise 1.1.6 (i) (Boolean closure) -/
theorem JordanMeasurable.symmDiff {d:ℕ} {E F : Set (EuclideanSpace' d)}
  (hE: JordanMeasurable E) (hF: JordanMeasurable F) : JordanMeasurable (symmDiff E F) := by
  convert JordanMeasurable.union ( hE.sdiff hF ) ( hF.sdiff hE ) using 1

/-- Exercise 1.1.6 (ii) (non-negativity) -/
theorem JordanMeasurable.nonneg {d:ℕ} {E : Set (EuclideanSpace' d)}
  (hE: JordanMeasurable E) : 0 ≤ hE.measure := by
  exact Jordan_inner_measure_nonneg E

/- Exercise 1.1.6 (iii) (finite additivity) -/
noncomputable section JordanFiniteAdditivityLemmas

/-
The sum of the inner Jordan measures of two disjoint bounded sets is at most the inner Jordan measure of their union.
-/
theorem Jordan_inner_add_le {d:ℕ} {E F: Set (EuclideanSpace' d)}
  (hE: Bornology.IsBounded E) (hF: Bornology.IsBounded F) (hdisj: Disjoint E F) :
  Jordan_inner_measure E + Jordan_inner_measure F ≤ Jordan_inner_measure (E ∪ F) := by
    -- For any $a \in S_E, b \in S_F$, there exist elementary $A \subseteq E, B \subseteq F$ with $m(A)=a, m(B)=b$.
    -- Since $E, F$ are disjoint, $A, B$ are disjoint.
    -- $A \cup B \subseteq E \cup F$ is elementary, and $m(A \cup B) = m(A) + m(B) = a + b$ (by additivity of elementary measure).
    have h_sum : ∀ a ∈ {m | ∃ A, ∃ hA : IsElementary A, A ⊆ E ∧ m = hA.measure}, ∀ b ∈ {m | ∃ A, ∃ hA : IsElementary A, A ⊆ F ∧ m = hA.measure}, a + b ≤ Jordan_inner_measure (E ∪ F) := by
      intro a ha b hb
      obtain ⟨A, hA, hAE, rfl⟩ := ha
      obtain ⟨B, hB, hBF, rfl⟩ := hb
      have h_union : A ∪ B ⊆ E ∪ F := by
        exact Set.union_subset_union hAE hBF
      have h_elem : IsElementary (A ∪ B) := by
        exact IsElementary.union hA hB
      have h_add : (hA.union hB).measure = hA.measure + hB.measure := by
        apply IsElementary.measure_of_disjUnion hA hB (Disjoint.mono hAE hBF hdisj)
      have h_le : (hA.union hB).measure ≤ Jordan_inner_measure (E ∪ F) := by
        apply le_csSup; (
        obtain ⟨ C, hC ⟩ := IsElementary.contains_bounded ( hE.union hF );
        exact ⟨ _, by rintro x ⟨ A, hA, hAE, rfl ⟩ ; exact hA.measure_mono hC.1 ( hAE.trans hC.2 ) ⟩); use A ∪ B; simp_all only [Set.union_subset_iff,
          and_self, exists_const];
      linarith [h_add, h_le];
    by_contra h_contra;
    -- By definition of supremum, for any $\epsilon > 0$, there exist $a \in S_E$ and $b \in S_F$ such that $a + b > \sup S_E + \sup S_F - \epsilon$.
    obtain ⟨a, ha⟩ : ∃ a ∈ {m | ∃ A, ∃ hA : IsElementary A, A ⊆ E ∧ m = hA.measure}, a > Jordan_inner_measure E - (Jordan_inner_measure E + Jordan_inner_measure F - Jordan_inner_measure (E ∪ F)) / 2 := by
      exact by rcases exists_lt_of_lt_csSup ( show { m : ℝ | ∃ A : Set ( EuclideanSpace' d ), ∃ hA : IsElementary A, A ⊆ E ∧ m = hA.measure }.Nonempty from by exact ⟨ _, ⟨ ∅, IsElementary.empty _, by norm_num, rfl ⟩ ⟩ ) ( show Jordan_inner_measure E - ( Jordan_inner_measure E + Jordan_inner_measure F - Jordan_inner_measure ( E ∪ F ) ) / 2 < Jordan_inner_measure E from by linarith [ show 0 ≤ Jordan_inner_measure F from Jordan_inner_measure_nonneg F ] ) with ⟨ a, ha₁, ha₂ ⟩ ; exact ⟨ a, ha₁, ha₂ ⟩ ;
    obtain ⟨b, hb⟩ : ∃ b ∈ {m | ∃ A, ∃ hA : IsElementary A, A ⊆ F ∧ m = hA.measure}, b > Jordan_inner_measure F - (Jordan_inner_measure E + Jordan_inner_measure F - Jordan_inner_measure (E ∪ F)) / 2 := by
      exact exists_lt_of_lt_csSup ( show { m | ∃ A : Set ( EuclideanSpace' d ), ∃ hA : IsElementary A, A ⊆ F ∧ m = hA.measure }.Nonempty from by exact ⟨ _, ⟨ ∅, IsElementary.empty _, Set.empty_subset _, rfl ⟩ ⟩ ) ( by linarith );
    linarith [ h_sum a ha.1 b hb.1 ]

/-
The outer Jordan measure is subadditive for bounded sets.
-/
theorem Jordan_outer_subadd {d:ℕ} {E F: Set (EuclideanSpace' d)}
  (hE: Bornology.IsBounded E) (hF: Bornology.IsBounded F) :
  Jordan_outer_measure (E ∪ F) ≤ Jordan_outer_measure E + Jordan_outer_measure F := by
    -- Fix any $a \in S_E$ and $b \in S_F$.
    have h_le : ∀ a ∈ {m : ℝ | ∃ A : Set (EuclideanSpace' d), ∃ hA : IsElementary A, E ⊆ A ∧ m = hA.measure}, ∀ b ∈ {m : ℝ | ∃ B : Set (EuclideanSpace' d), ∃ hB : IsElementary B, F ⊆ B ∧ m = hB.measure}, Jordan_outer_measure (E ∪ F) ≤ a + b := by
      rintro a ⟨ A, hA, hEA, rfl ⟩ b ⟨ B, hB, hFB, rfl ⟩;
      refine' le_trans ( csInf_le _ ⟨ A ∪ B, _, _, rfl ⟩ ) _;
      any_goals exact hA.union hB;
      · exact ⟨ 0, by rintro m ⟨ A, hA, hEA, rfl ⟩ ; exact IsElementary.measure_nonneg _ ⟩;
      · exact Set.union_subset_union hEA hFB;
      · exact IsElementary.measure_of_union hA hB;
    refine' le_of_forall_pos_le_add fun ε εpos => _;
    -- Choose $a \in S_E$ and $b \in S_F$ such that $a < m^*(E) + \frac{\epsilon}{2}$ and $b < m^*(F) + \frac{\epsilon}{2}$.
    obtain ⟨a, ha₁, ha₂⟩ : ∃ a ∈ {m : ℝ | ∃ A : Set (EuclideanSpace' d), ∃ hA : IsElementary A, E ⊆ A ∧ m = hA.measure}, a < Jordan_outer_measure E + ε / 2 := by
      have := exists_lt_of_csInf_lt ( show { m : ℝ | ∃ A : Set ( EuclideanSpace' d ), ∃ hA : IsElementary A, E ⊆ A ∧ m = hA.measure }.Nonempty from ?_ ) ( show Jordan_outer_measure E + ε / 2 > Jordan_outer_measure E from by linarith );
      · exact this;
      · exact Exists.elim ( IsElementary.contains_bounded hE ) fun A hA => ⟨ _, ⟨ A, hA.1, hA.2, rfl ⟩ ⟩
    obtain ⟨b, hb₁, hb₂⟩ : ∃ b ∈ {m : ℝ | ∃ B : Set (EuclideanSpace' d), ∃ hB : IsElementary B, F ⊆ B ∧ m = hB.measure}, b < Jordan_outer_measure F + ε / 2 := by
      exact exists_lt_of_csInf_lt ( by rcases IsElementary.contains_bounded hF with ⟨ B, hB₁, hB₂ ⟩ ; exact ⟨ _, ⟨ B, hB₁, hB₂, rfl ⟩ ⟩ ) ( lt_add_of_pos_right _ ( half_pos εpos ) );
    linarith [ h_le a ha₁ b hb₁ ]

end JordanFiniteAdditivityLemmas

theorem JordanMeasurable.mes_of_disjUnion {d:ℕ} {E F : Set (EuclideanSpace' d)}
  (hE: JordanMeasurable E) (hF: JordanMeasurable F) (hEF: Disjoint E F)
  : (hE.union hF).measure = hE.measure + hF.measure := by
  -- Apply the additivity property of the Jordan measure.
  have h_add : Jordan_outer_measure (E ∪ F) = Jordan_outer_measure E + Jordan_outer_measure F := by
    apply le_antisymm
    generalize_proofs at *; (
    apply_rules [ Jordan_outer_subadd, hE.1, hF.1 ]);
    -- By Lemma 1.1.11, we have Jordan_inner_measure E + Jordan_inner_measure F ≤ Jordan_inner_measure (E ∪ F).
    have h_inner_add : Jordan_inner_measure E + Jordan_inner_measure F ≤ Jordan_inner_measure (E ∪ F) := by
      exact Jordan_inner_add_le hE.1 hF.1 hEF;
    linarith [ hE.2, hF.2, Jordan_inner_le_outer hE.1, Jordan_inner_le_outer hF.1, Jordan_inner_le_outer ( hE.1.union hF.1 ) ]
  generalize_proofs at *;
  rw [ JordanMeasurable.eq_outer, JordanMeasurable.eq_outer, JordanMeasurable.eq_outer ] ; simp_all only


/-- Exercise 1.1.6 (iii) (finite additivity) -/
lemma JordanMeasurable.measure_of_disjUnion' {d:ℕ} {S: Finset (Set (EuclideanSpace' d))}
(hE: ∀ E ∈ S, JordanMeasurable E) (hdisj: (S : Set (Set (EuclideanSpace' d))).PairwiseDisjoint id):
  (JordanMeasurable.union' hE).measure = ∑ E:S, (hE E.val E.property).measure := by
  induction' S using Finset.induction with E S hS ih;
  · simp_all only [Finset.coe_empty, Set.pairwiseDisjoint_empty, Finset.notMem_empty, Set.iUnion_of_empty,
    Set.iUnion_empty, mes_of_empty, Finset.univ_eq_empty, Finset.coe_mem, Finset.sum_empty];
  · simp_all only [Set.PairwiseDisjoint, Finset.univ_eq_attach, Finset.mem_insert,
    Finset.coe_mem, or_true, Finset.coe_insert, Set.iUnion_iUnion_eq_or_left, Finset.attach_insert,
    Finset.mem_image, Finset.mem_attach, Subtype.mk.injEq, true_and, Subtype.exists, exists_prop,
    exists_eq_right, not_false_eq_true, Finset.sum_insert, Finset.coe_attach, Subtype.forall,
    implies_true, Set.injOn_of_eq_iff_eq, Finset.sum_image];
    convert JordanMeasurable.mes_of_disjUnion ( hE E ( Finset.mem_insert_self E S ) ) ( JordanMeasurable.union' fun x hx => hE x ( Finset.mem_insert_of_mem hx ) ) _ using 1;
    · congr! 1;
      · rw [ eq_comm ];
        convert JordanMeasurable.eq_outer ( hE E ( Finset.mem_insert_self E S ) ) using 1;
      · convert ih ( fun x hx => hE x ( Finset.mem_insert_of_mem hx ) ) ( fun x hx y hy hxy => hdisj ( by simp_all only [Finset.mem_insert,
        forall_eq_or_imp, Finset.mem_coe, ne_eq, Set.mem_insert_iff, or_true] ) ( by simp_all only [Finset.mem_insert,
          forall_eq_or_imp, Finset.mem_coe, ne_eq, Set.mem_insert_iff, or_true] ) hxy ) |> Eq.symm;
    · simp_all only [Finset.mem_insert, forall_eq_or_imp, Set.Pairwise, Finset.mem_coe,
      ne_eq, Set.mem_insert_iff, not_true_eq_false, disjoint_self, id_eq, Set.bot_eq_empty,
      IsEmpty.forall_iff, true_and, Set.disjoint_iUnion_right, not_false_eq_true, implies_true,
      forall_const];
      exact fun x hx => hdisj.1 x hx ( by
      obtain ⟨left, right⟩ := hE
      obtain ⟨left_1, right_1⟩ := hdisj
      obtain ⟨left, right_2⟩ := left
      apply Aesop.BuiltinRules.not_intro
      intro a
      subst a
      simp_all only [not_true_eq_false] )

/-- Exercise 1.1.6 (iv) (monotonicity) -/
theorem JordanMeasurable.mono {d:ℕ} {E F : Set (EuclideanSpace' d)}
  (hE: JordanMeasurable E) (hF: JordanMeasurable F) (hEF: E ⊆ F)
  : hE.measure ≤ hF.measure := by
  obtain ⟨ M, M_mem ⟩ := hF;
  obtain ⟨ N, N_mem ⟩ := hE;
  convert le_csInf _ _;
  · obtain ⟨ A, hA ⟩ := IsElementary.contains_bounded M;
    exact ⟨ _, ⟨ A, hA.1, hA.2, rfl ⟩ ⟩;
  · rintro _ ⟨ A, hA, hAF, rfl ⟩;
    refine' csInf_le _ _;
    · exact ⟨ 0, by rintro x ⟨ A, hA, hAE, rfl ⟩ ; exact hA.measure_nonneg ⟩;
    · exact ⟨ A, hA, hEF.trans hAF, rfl ⟩

/-- Exercise 1.1.6 (v) (finite subadditivity) -/
theorem JordanMeasurable.mes_of_union {d:ℕ} {E F : Set (EuclideanSpace' d)}
  (hE: JordanMeasurable E) (hF: JordanMeasurable F)
  : (hE.union hF).measure ≤ hE.measure + hF.measure := by
  by_contra h_contra;
  -- Since $E$ and $F$ are not disjoint, we can find a smaller set $G$ such that $E \cup F = E \cup G$ and $G$ is disjoint from $E$.
  obtain ⟨G, hG⟩ : ∃ G : Set (EuclideanSpace' d), Disjoint E G ∧ E ∪ F = E ∪ G ∧ G ⊆ F := by
    exact ⟨ F \ E, disjoint_sdiff_self_right, by simp_all only [not_le, Set.union_diff_self], fun x hx => hx.1 ⟩;
  have hG_measurable : JordanMeasurable G := by
    have hG_measurable : JordanMeasurable (F \ E) := by
      exact sdiff hF hE;
    convert hG_measurable using 1;
    ext x;
    exact ⟨ fun hx => ⟨ hG.2.2 hx, fun hx' => hG.1.le_bot ⟨ hx', hx ⟩ ⟩, fun hx => by rw [ Set.ext_iff ] at hG; specialize hG; have := hG.2.1 x; simp_all only [not_le,
      Set.mem_diff, Set.mem_union, or_true, false_or, true_iff] ⟩;
  have hG_measure : (hE.union hG_measurable).measure = hE.measure + hG_measurable.measure := by
    convert JordanMeasurable.mes_of_disjUnion hE hG_measurable hG.1 using 1;
  have hG_measure_le : hG_measurable.measure ≤ hF.measure := by
    apply JordanMeasurable.mono hG_measurable hF hG.2.2;
  exact h_contra <| by simpa only [ hG.2.1 ] using hG_measure.le.trans <| add_le_add_right hG_measure_le _;

/-- Exercise 1.1.6 (v) (finite subadditivity) -/
lemma JordanMeasurable.measure_of_union' {d:ℕ} {S: Finset (Set (EuclideanSpace' d))}
(hE: ∀ E ∈ S, JordanMeasurable E) :
  (JordanMeasurable.union' hE).measure ≤ ∑ E:S, (hE E.val E.property).measure := by
  induction' S using Finset.induction_on with a S ha ih;
  · simp_all only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty, mes_of_empty, Finset.univ_eq_empty,
    Finset.coe_mem, Finset.sum_empty, le_refl];
  · convert le_trans ( JordanMeasurable.mes_of_union ( hE a ( Finset.mem_insert_self a S ) ) ( JordanMeasurable.union' fun E hE' => hE E ( Finset.mem_insert_of_mem hE' ) ) ) ( add_le_add_right ( ih fun E hE' => hE E ( Finset.mem_insert_of_mem hE' ) ) _ ) using 1;
    · simp_all only [Finset.univ_eq_attach, Finset.mem_insert, Finset.coe_mem, or_true, Set.iUnion_iUnion_eq_or_left];
    · simp +decide [Finset.sum_insert, ha]
      classical
      apply Finset.sum_image; intro x _ y _ hxy; exact Subtype.ext (Subtype.mk.inj hxy)

open Pointwise

/-- Exercise 1.1.6 (vi) (translation invariance) -/
theorem JordanMeasurable.translate {d:ℕ} {E: Set (EuclideanSpace' d)}
  (hE: JordanMeasurable E) (x: EuclideanSpace' d) : JordanMeasurable (E + {x}) := by
  refine' ⟨ _, _ ⟩;
  · have := hE.1;
    rw [ isBounded_iff_forall_norm_le ] at *;
    exact ⟨ this.choose + ‖x‖, fun y hy => by rcases Set.mem_add.mp hy with ⟨ y', hy', z', hz', rfl ⟩ ; exact le_trans ( norm_add_le _ _ ) ( add_le_add ( this.choose_spec _ hy' ) ( by simp_all only [Set.mem_singleton_iff,
      Set.add_singleton, Set.image_add_right, Set.mem_preimage, add_neg_cancel_right, le_refl] ) ) ⟩;
  · -- By definition of Jordan inner and outer measures, we have:
    have h_inner : Jordan_inner_measure (E + {x}) = Jordan_inner_measure E := by
      unfold Jordan_inner_measure;
      congr! 3;
      constructor <;> rintro ⟨ A, hA, hA', h ⟩;
      · use A + { -x };
        refine' ⟨ _, _, _ ⟩;
        exact IsElementary.translate hA (-x);
        intro y hy; obtain ⟨ a, ha, b, hb, rfl ⟩ := hy;
        subst h
        simp_all only [Set.add_singleton, Set.image_add_right, Set.mem_singleton_iff]
        subst hb
        obtain ⟨left, right⟩ := hE
        obtain ⟨w, h⟩ := hA
        subst h
        simp_all only [Set.iUnion_subset_iff, Set.mem_iUnion, exists_prop]
        obtain ⟨w_1, h⟩ := ha
        obtain ⟨left_1, right_1⟩ := h
        apply hA'
        on_goal 2 => { exact right_1
        }
        · simp_all only;
        · rw [ h, IsElementary.measure_of_translate ];
      · use A + {x};
        refine' ⟨ _, _, _ ⟩;
        exact IsElementary.translate hA x;
        · exact Set.add_subset_add hA' ( Set.Subset.refl _ );
        · rw [ h, IsElementary.measure_of_translate ]
    have h_outer : Jordan_outer_measure (E + {x}) = Jordan_outer_measure E := by
      rw [ eq_comm, Jordan_outer_measure, Jordan_outer_measure ];
      congr! 3;
      constructor <;> rintro ⟨ A, hA, hA', rfl ⟩;
      · refine' ⟨ A + { x }, _, _, _ ⟩;
        exact IsElementary.translate hA x;
        · exact Set.add_subset_add hA' ( Set.Subset.refl _ );
        · exact Eq.symm (IsElementary.measure_of_translate hA x);
      · refine' ⟨ A + { -x }, _, _, _ ⟩;
        exact IsElementary.translate hA (-x);
        · intro y hy; specialize hA' ( Set.add_mem_add hy ( Set.mem_singleton x ) ) ; simp_all only [Set.add_singleton,
          Set.image_add_right, neg_neg, Set.mem_preimage];
        · exact Eq.symm (IsElementary.measure_of_translate hA (-x));
    exact h_inner.trans ( hE.2.trans h_outer.symm )

/-- Exercise 1.1.6 (vi) (translation invariance) -/
lemma JordanMeasurable.measure_of_translate {d:ℕ} {E: Set (EuclideanSpace' d)}
(hE: JordanMeasurable E) (x: EuclideanSpace' d):
  (hE.translate x).measure ≤ hE.measure := by
  have := hE.1;
  have h_factor : ∀ (E : Set (EuclideanSpace' d)), Bornology.IsBounded E → Jordan_outer_measure (E + {x}) ≤ Jordan_outer_measure E := by
    intros E hE_bounded
    have h_factor : ∀ (A : Set (EuclideanSpace' d)), Bornology.IsBounded E → IsElementary A → E ⊆ A → E + {x} ⊆ A + {x} := by
      exact fun A a a a ↦ Set.add_subset_add_right a;
    apply_rules [ csInf_le_csInf ];
    · exact ⟨ 0, by rintro m ⟨ A, hA, hA', rfl ⟩ ; exact IsElementary.measure_nonneg hA ⟩;
    · exact Exists.elim ( IsElementary.contains_bounded hE_bounded ) fun A hA => ⟨ _, ⟨ A, hA.1, hA.2, rfl ⟩ ⟩;
    · rintro m ⟨ A, hA, hEA, rfl ⟩;
      use A + {x};
      exact ⟨ hA.translate x, h_factor A hE_bounded hA hEA, by exact Eq.symm (IsElementary.measure_of_translate hA x) ⟩;
  convert h_factor E this using 1;
  · convert JordanMeasurable.eq_outer _;
  · exact eq_outer hE;

/-!
## Auxiliary lemmas for Exercise 1.1.7 (regions under graphs)

The original statement of {lit}`JordanMeasurable.graph` below (kept commented out) is **false** as
stated: it only assumes {lit}`ContinuousOn f B.toSet` for an arbitrary box {lit}`B`.  A box may have open
sides (e.g. {lit}`Ioo`), on which a continuous function can be unbounded (for instance {lit}`f x = 1/x` on
{lit}`(0,1)`).  Its graph is then an unbounded set, hence *not* Jordan measurable.  This matches Tao's
actual Exercise 1.1.7, which is stated for a **closed** box.  We therefore add the hypothesis
{lit}`hB : ∀ i, ∃ a b, B.side i = BoundedInterval.Icc a b` (all sides closed) to the corrected versions.
-/

section GraphMeasurableAux

/-
The Jordan outer measure of the empty set is zero.
-/
lemma Jordan_outer_measure_empty (d:ℕ) : Jordan_outer_measure (∅ : Set (EuclideanSpace' d)) = 0 := by
  convert JordanMeasurable.mes_of_empty d using 1;
  exact Eq.symm (JordanMeasurable.eq_outer (JordanMeasurable.empty d))

/-
The Jordan outer measure of a box equals its volume.
-/
lemma Jordan_outer_measure_of_box {d:ℕ} (B: Box d) :
    Jordan_outer_measure B.toSet = |B|ᵥ := by
  refine' le_antisymm _ _;
  · refine' csInf_le _ _;
    · exact ⟨ 0, by rintro x ⟨ A, hA, hAB, rfl ⟩ ; exact IsElementary.measure_nonneg _ ⟩;
    · exact ⟨ _, IsElementary.box B, Set.Subset.refl _, IsElementary.measure_of_box B ▸ rfl ⟩;
  · refine' le_csInf _ _;
    · exact ⟨ _, ⟨ _, IsElementary.box B, Set.Subset.refl _, rfl ⟩ ⟩;
    · rintro _ ⟨ A, hA, hBA, rfl ⟩;
      obtain ⟨ T, hT ⟩ := hA;
      convert IsElementary.measure_mono _ _ hBA;
      rotate_left;
      exact IsElementary.box B;
      · exact ⟨ T, hT ⟩;
      · exact Eq.symm (IsElementary.measure_of_box B)

/-
Monotonicity of the Jordan outer measure (for a bounded ambient set).
-/
lemma Jordan_outer_measure_mono_of_subset {d:ℕ} {E F: Set (EuclideanSpace' d)}
    (hEF: E ⊆ F) (hF: Bornology.IsBounded F) :
    Jordan_outer_measure E ≤ Jordan_outer_measure F := by
  apply_rules [ csInf_le_csInf ];
  · exact ⟨ 0, by rintro x ⟨ A, hA, hEA, rfl ⟩ ; exact IsElementary.measure_nonneg hA ⟩;
  · exact Exists.elim ( IsElementary.contains_bounded hF ) fun A hA => ⟨ _, ⟨ A, hA.1, hA.2, rfl ⟩ ⟩;
  · exact fun m hm => by obtain ⟨ A, hA, hFA, rfl ⟩ := hm; exact ⟨ A, hA, hEF.trans hFA, rfl ⟩ ;

/-
A finite union of boxes is bounded.
-/
lemma isBounded_biUnion_box {d:ℕ} {ι: Type*} (s: Finset ι) (C: ι → Box d) :
    Bornology.IsBounded (⋃ i ∈ s, (C i).toSet) := by
  have h_bounded : ∀ i ∈ s, Bornology.IsBounded ((C i).toSet) := by
    exact fun i hi => IsElementary.isBounded ( IsElementary.box _ );
  exact (Bornology.isBounded_biUnion_finset s).mpr h_bounded

/-
Finite subadditivity of the Jordan outer measure over a finite family of boxes.
-/
lemma Jordan_outer_measure_biUnion_box_le {d:ℕ} {ι: Type*} (s: Finset ι) (C: ι → Box d) :
    Jordan_outer_measure (⋃ i ∈ s, (C i).toSet) ≤ ∑ i ∈ s, |C i|ᵥ := by
  induction' s using Finset.induction with a s ha ih;
  all_goals try exact Classical.decEq _;
  · simp +decide [ Jordan_outer_measure_empty ];
  · convert le_trans ( Jordan_outer_subadd ( hE := ?_ ) ( hF := ?_ ) ) ( add_le_add ?_ ih ) using 1;
    rotate_left;
    convert Finset.sum_insert ha;
    exact ( C a ).toSet;
    · exact ( IsElementary.box ( C a ) ).isBounded;
    · exact isBounded_biUnion_box s C;
    · convert Jordan_outer_measure_of_box ( C a ) |> le_of_eq using 1;
    · simp +decide

/-
A closed box (all sides `Icc`) has compact underlying set.
-/
lemma Box.isCompact_of_closed {d:ℕ} {B: Box d}
    (hB: ∀ i, ∃ a b, B.side i = BoundedInterval.Icc a b) : IsCompact B.toSet := by
  -- The product of closed intervals is the intersection of the preimages of closed intervals under the coordinate projections.
  have h_closed_intervals : B.toSet = ⋂ i, (fun x : EuclideanSpace' d => x i) ⁻¹' (Set.Icc (B.side i).a (B.side i).b) := by
    ext x; simp [Box.toSet];
    exact forall_congr' fun i => by obtain ⟨ a, b, h ⟩ := hB i; simp +decide [ h ] ;
  have h_closed : IsClosed (B.toSet) := by
    exact h_closed_intervals ▸ isClosed_iInter fun i => isClosed_Icc.preimage ( continuous_apply _ |> Continuous.comp <| continuous_induced_dom );
  exact ( Metric.isCompact_iff_isClosed_bounded.mpr ⟨ h_closed, by simpa using IsElementary.isBounded ( IsElementary.box B ) ⟩ )

/-
The graph of a continuous function over a closed box is bounded.
-/
lemma graph_isBounded {d:ℕ} {B:Box d} {f: EuclideanSpace' d → ℝ}
    (hB: ∀ i, ∃ a b, B.side i = BoundedInterval.Icc a b) (hf: ContinuousOn f B.toSet) :
    Bornology.IsBounded { p | ∃ x ∈ B.toSet, EuclideanSpace'.prod_equiv d 1 p = ⟨ x, f x ⟩ } := by
  obtain ⟨ M, hM ⟩ := IsCompact.exists_bound_of_continuousOn ( Box.isCompact_of_closed hB ) hf;
  refine' Bornology.IsBounded.subset _ _;
  exact ( Box.prod B ( BoundedInterval.Icc ( -M ) M ) ).toSet;
  · exact IsElementary.isBounded ( IsElementary.box _ );
  · intro p hp; obtain ⟨ x, hx, hx' ⟩ := hp; simp_all +decide [ Box.prod_toSet, EuclideanSpace'.prod ] ;
    exact ⟨ f x, abs_le.mp ( hM x hx ), rfl ⟩

/-- Left endpoint of the {lit}`i`-th side of grid cell {lit}`k` in an {lit}`N`-fold subdivision of {lit}`∏ Icc (a i) (b i)`. -/
noncomputable def GraphGrid.cornerLo {d:ℕ} (a b : Fin d → ℝ) (N:ℕ) (k : Fin d → Fin N) (i:Fin d) : ℝ :=
  a i + (b i - a i) * (k i : ℝ) / (N:ℝ)

/-- Right endpoint of the {lit}`i`-th side of grid cell {lit}`k`. -/
noncomputable def GraphGrid.cornerHi {d:ℕ} (a b : Fin d → ℝ) (N:ℕ) (k : Fin d → Fin N) (i:Fin d) : ℝ :=
  a i + (b i - a i) * ((k i : ℝ) + 1) / (N:ℝ)

/-- The {lit}`d`-dimensional grid cell {lit}`k`. -/
noncomputable def GraphGrid.Qbox {d:ℕ} (a b : Fin d → ℝ) (N:ℕ) (k : Fin d → Fin N) : Box d where
  side i := BoundedInterval.Icc (GraphGrid.cornerLo a b N k i) (GraphGrid.cornerHi a b N k i)

/-- The lower-left corner (sample point) of grid cell {lit}`k`. -/
noncomputable def GraphGrid.corner {d:ℕ} (a b : Fin d → ℝ) (N:ℕ) (k : Fin d → Fin N) : EuclideanSpace' d :=
  .toLp 2 (GraphGrid.cornerLo a b N k)

/-- The {lit}`(d+1)`-dimensional covering box over grid cell {lit}`k`: the cell times the interval
{lit}`[f(corner) - η, f(corner) + η]`. -/
noncomputable def GraphGrid.Cbox {d:ℕ} (a b : Fin d → ℝ) (N:ℕ) (f: EuclideanSpace' d → ℝ) (η:ℝ)
    (k : Fin d → Fin N) : Box (d+1) :=
  Box.prod (GraphGrid.Qbox a b N k)
    (BoundedInterval.Icc (f (GraphGrid.corner a b N k) - η) (f (GraphGrid.corner a b N k) + η))

@[simp] lemma GraphGrid.corner_apply {d:ℕ} (a b : Fin d → ℝ) (N:ℕ) (k : Fin d → Fin N) (i:Fin d) :
    (GraphGrid.corner a b N k) i = GraphGrid.cornerLo a b N k i := by
  simp [GraphGrid.corner]

/-
One-dimensional cell selection: any point of `[a,b]` lies in some cell of the `N`-fold
subdivision.
-/
lemma GraphGrid.exists_cell {a b : ℝ} (hab : a ≤ b) {N:ℕ} (hN: 0 < N) {t:ℝ}
    (hlo: a ≤ t) (hhi: t ≤ b) :
    ∃ m:Fin N, a + (b-a)*(m:ℝ)/(N:ℝ) ≤ t ∧ t ≤ a + (b-a)*((m:ℝ)+1)/(N:ℝ) := by
  by_cases h : a = b;
  · exact ⟨ ⟨ 0, hN ⟩, by norm_num [ h ] ; linarith, by norm_num [ h ] ; linarith ⟩;
  · refine' ⟨ ⟨ Min.min ( Nat.floor ( ( t - a ) / ( b - a ) * N ) ) ( N - 1 ), _ ⟩, _, _ ⟩ <;> norm_num;
    · exact Or.inr hN;
    · rw [ add_div', div_le_iff₀ ] <;> norm_num [ hN ];
      · cases min_cases ( ⌊ ( t - a ) / ( b - a ) * N⌋₊ : ℝ ) ( N - 1 ) <;> nlinarith [ Nat.floor_le ( show 0 ≤ ( t - a ) / ( b - a ) * N by exact mul_nonneg ( div_nonneg ( sub_nonneg.mpr hlo ) ( sub_nonneg.mpr hab ) ) ( Nat.cast_nonneg _ ) ), mul_div_cancel₀ ( t - a ) ( sub_ne_zero.mpr ( Ne.symm h ) ), show ( N : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr hN ];
      · linarith;
    · cases min_cases ( ⌊ ( t - a ) / ( b - a ) * N⌋₊ : ℝ ) ( N - 1 : ℕ ) <;> simp_all +decide;
      · rw [ add_div', le_div_iff₀ ] <;> nlinarith [ Nat.lt_floor_add_one ( ( t - a ) / ( b - a ) * N ), mul_div_cancel₀ ( t - a ) ( sub_ne_zero_of_ne ( Ne.symm h ) ), show ( N : ℝ ) > 0 by positivity ];
      · rw [ mul_div_cancel_right₀ _ ( by positivity ) ] ; linarith

/-
The volume of a grid cell is `∏ i, (b i - a i)/N`.
-/
lemma GraphGrid.Qbox_volume {d:ℕ} (a b : Fin d → ℝ) (hab: ∀ i, a i ≤ b i) {N:ℕ} (hN: 0 < N)
    (k : Fin d → Fin N) :
    |GraphGrid.Qbox a b N k|ᵥ = ∏ i, (b i - a i)/(N:ℝ) := by
  refine' Finset.prod_congr rfl fun i _ => _;
  unfold Qbox BoundedInterval.length; ring_nf;
  unfold cornerLo cornerHi; ring_nf ;
  exact max_eq_left ( by nlinarith [ hab i, show ( N : ℝ ) ⁻¹ ≥ 0 by positivity ] )

/-
The total volume of all covering boxes equals `(∏ i, (b i - a i)) * (2 * η)`.
-/
lemma GraphGrid.sum_vol {d:ℕ} (a b : Fin d → ℝ) (hab: ∀ i, a i ≤ b i) {N:ℕ} (hN: 0 < N)
    (f: EuclideanSpace' d → ℝ) {η:ℝ} (hη: 0 ≤ η) :
    ∑ k, |GraphGrid.Cbox a b N f η k|ᵥ = (∏ i, (b i - a i)) * (2 * η) := by
  -- By definition of Cbox, we have that its volume is the product of the volumes of Qbox and the interval [c - η, c + η].
  have h_volume_Cbox : ∀ k : Fin d → Fin N, (Cbox a b N f η k).volume = (∏ i, (b i - a i) / N) * (2 * η) := by
    intro k
    simp [Cbox, Box.volume_prod, Box.volume_of_interval];
    rw [ GraphGrid.Qbox_volume a b hab hN k ];
    norm_num [ Finset.prod_div_distrib, BoundedInterval.length ] ; ring_nf;
    exact Or.inl <| max_eq_left <| by positivity;
  simp_all +decide [ Finset.prod_div_distrib ];
  rw [ ← mul_assoc, mul_div_cancel₀ _ ( by positivity ) ]

/-
The graph is covered by the grid of covering boxes for a suitable (large) `N`.
-/
lemma GraphGrid.graph_subset {d:ℕ} (a b : Fin d → ℝ) (hab: ∀ i, a i ≤ b i)
    {B:Box d} (hBdef: ∀ i, B.side i = BoundedInterval.Icc (a i) (b i))
    {f: EuclideanSpace' d → ℝ} (hf: ContinuousOn f B.toSet) {η:ℝ} (hη: 0 < η) :
    ∃ N:ℕ, 0 < N ∧
      { p | ∃ x ∈ B.toSet, EuclideanSpace'.prod_equiv d 1 p = ⟨ x, f x ⟩ } ⊆
        (⋃ k : Fin d → Fin N, (GraphGrid.Cbox a b N f η k).toSet) := by
  -- Let S := B.toSet. It is compact: hcompact := Box.isCompact_of_closed (fun i => ⟨a i, b i, hBdef i⟩).
  set S := B.toSet
  have hcompact : IsCompact S := by
    exact Box.isCompact_of_closed ( fun i => ⟨ a i, b i, hBdef i ⟩ );
  -- By `IsCompact.uniformContinuousOn_of_continuous hcompact hf`, `f` is uniformly continuous on `S`.
  obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ u v : EuclideanSpace' d, u ∈ S → v ∈ S → dist u v < δ → |f u - f v| < η := by
    have := Metric.uniformContinuousOn_iff.mp ( hcompact.uniformContinuousOn_of_continuous hf ) η hη; aesop;
  -- Choose `N`: let `L := Real.sqrt (∑ i, (b i - a i)^2) ≥ 0`. By `exists_nat_gt (L/δ)` get `N` with `L/δ < N`; then `N > 0` (since `L/δ ≥ 0`) and `L/N < δ` (from `δ > 0`).
  obtain ⟨N, hN_pos, hN⟩ : ∃ N : ℕ, 0 < N ∧ Real.sqrt (∑ i, (b i - a i)^2) / (N : ℝ) < δ := by
    exact ⟨ ⌊Real.sqrt ( ∑ i, ( b i - a i ) ^ 2 ) / δ⌋₊ + 1, Nat.succ_pos _, by rw [ div_lt_iff₀ ] <;> push_cast <;> nlinarith [ Nat.lt_floor_add_one ( Real.sqrt ( ∑ i, ( b i - a i ) ^ 2 ) / δ ), mul_div_cancel₀ ( Real.sqrt ( ∑ i, ( b i - a i ) ^ 2 ) ) hδ_pos.ne' ] ⟩;
  refine' ⟨ N, hN_pos, _ ⟩;
  intro p hp
  obtain ⟨x, hxS, hx⟩ := hp
  have hx_coord : ∀ i, a i ≤ x i ∧ x i ≤ b i := by
    exact fun i => by have := hxS i; rw [ hBdef ] at this; exact this;
  have hx_corner : ∃ k : Fin d → Fin N, ∀ i, GraphGrid.cornerLo a b N k i ≤ x i ∧ x i ≤ GraphGrid.cornerHi a b N k i := by
    exact ⟨ fun i => Classical.choose ( GraphGrid.exists_cell ( hab i ) hN_pos ( hx_coord i |>.1 ) ( hx_coord i |>.2 ) ), fun i => Classical.choose_spec ( GraphGrid.exists_cell ( hab i ) hN_pos ( hx_coord i |>.1 ) ( hx_coord i |>.2 ) ) ⟩
  obtain ⟨k, hk⟩ := hx_corner
  have hx_dist : dist x (GraphGrid.corner a b N k) ≤ Real.sqrt (∑ i, (b i - a i)^2) / (N : ℝ) := by
    have hx_dist : dist x (GraphGrid.corner a b N k) = Real.sqrt (∑ i, (x i - GraphGrid.cornerLo a b N k i)^2) := by
      simp +decide [ dist_eq_norm, EuclideanSpace.norm_eq ];
    have hx_dist_le : ∀ i, (x i - GraphGrid.cornerLo a b N k i)^2 ≤ ((b i - a i) / (N : ℝ))^2 := by
      intro i
      have h_diff : x.ofLp i - GraphGrid.cornerLo a b N k i ≤ (b i - a i) / (N : ℝ) := by
        have := hk i; rw [ show cornerHi a b N k i = cornerLo a b N k i + ( b i - a i ) / N from ?_ ] at this; ring_nf at *; linarith;
        unfold cornerHi cornerLo; ring;
      exact pow_le_pow_left₀ ( sub_nonneg.mpr ( hk i |>.1 ) ) h_diff 2;
    rw [ hx_dist, Real.sqrt_le_iff ];
    exact ⟨ by positivity, by rw [ div_pow, Real.sq_sqrt <| Finset.sum_nonneg fun _ _ => sq_nonneg _ ] ; exact le_trans ( Finset.sum_le_sum fun _ _ => hx_dist_le _ ) <| by simp +decide [ div_pow, Finset.sum_div _ _ _ ] ⟩
  have hx_f : |f x - f (GraphGrid.corner a b N k)| < η := by
    apply hδ x (GraphGrid.corner a b N k) hxS (by
    simp +zetaDelta at *;
    simp_all +decide [ cornerLo, cornerHi ];
    exact fun i => ⟨ div_nonneg ( mul_nonneg ( sub_nonneg.mpr ( hab i ) ) ( Nat.cast_nonneg _ ) ) ( Nat.cast_nonneg _ ), by nlinarith [ hk i, hab i, show ( k i : ℝ ) + 1 ≤ N by norm_cast; linarith [ Fin.is_lt ( k i ) ], mul_div_cancel₀ ( ( b i - a i ) * ( k i : ℝ ) ) ( by positivity : ( N : ℝ ) ≠ 0 ) ] ⟩) (by
    exact lt_of_le_of_lt hx_dist hN)
  have hx_prod : p ∈ (Cbox a b N f η k).toSet := by
    simp_all +decide [ Cbox, Box.prod ];
    intro i; split_ifs <;> simp_all +decide [ Prod.ext_iff, EuclideanSpace'.prod_equiv ] ;
    · convert hk ⟨ i, by linarith ⟩ using 1;
      simp +decide [ ← hx.1, Qbox ];
    · grind
  exact Set.mem_iUnion.mpr ⟨k, hx_prod⟩

/-
Grid covering: for a closed box `B`, a continuous `f`, and `ε > 0`, there is a finite grid of
`(d+1)`-boxes covering the graph of `f` with total volume at most `ε`.
-/
lemma graph_grid_cover {d:ℕ} {B:Box d} {f: EuclideanSpace' d → ℝ}
    (hB: ∀ i, ∃ a b, B.side i = BoundedInterval.Icc a b) (hf: ContinuousOn f B.toSet)
    {ε:ℝ} (hε: 0 < ε) :
    ∃ (N:ℕ) (C: (Fin d → Fin N) → Box (d+1)),
      { p | ∃ x ∈ B.toSet, EuclideanSpace'.prod_equiv d 1 p = ⟨ x, f x ⟩ } ⊆ (⋃ j, (C j).toSet)
        ∧ ∑ j, |C j|ᵥ ≤ ε := by
  by_cases h : ∀ i : Fin d, ∃ a b : ℝ, B.side i = BoundedInterval.Icc a b ∧ a ≤ b;
  · choose a b h₁ h₂ using h;
    obtain ⟨N, hN⟩ : ∃ N : ℕ, 0 < N ∧ { p | ∃ x ∈ B.toSet, EuclideanSpace'.prod_equiv d 1 p = ⟨ x, f x ⟩ } ⊆ ⋃ k : Fin d → Fin N, (GraphGrid.Cbox a b N f (ε / (2 * (∏ i, (b i - a i) + 1))) k).toSet := by
      apply GraphGrid.graph_subset a b h₂ h₁ hf (by
      exact div_pos hε ( mul_pos zero_lt_two ( add_pos_of_nonneg_of_pos ( Finset.prod_nonneg fun _ _ => sub_nonneg.mpr ( h₂ _ ) ) zero_lt_one ) ));
    refine' ⟨ N, _, hN.2, _ ⟩;
    rw [ GraphGrid.sum_vol ];
    · nlinarith [ mul_div_cancel₀ ε ( by linarith [ show 0 ≤ ∏ i, ( b i - a i ) from Finset.prod_nonneg fun _ _ => sub_nonneg.mpr ( h₂ _ ) ] : ( 2 * ( ∏ i, ( b i - a i ) + 1 ) ) ≠ 0 ), show 0 ≤ ∏ i, ( b i - a i ) from Finset.prod_nonneg fun _ _ => sub_nonneg.mpr ( h₂ _ ) ];
    · assumption;
    · linarith;
    · exact div_nonneg hε.le ( mul_nonneg zero_le_two ( add_nonneg ( Finset.prod_nonneg fun _ _ => sub_nonneg.mpr ( h₂ _ ) ) zero_le_one ) );
  · -- Since there exists an i such that B.side i is not a closed interval, B.toSet is empty.
    have hB_empty : B.toSet = ∅ := by
      simp_all +decide [ Set.ext_iff, Box.mem_toSet ];
      obtain ⟨ i, hi ⟩ := h;
      exact fun x => ⟨ i, by obtain ⟨ a, b, h ⟩ := hB i; specialize hi a b h; rw [ h ] ; exact fun ⟨ ha, hb ⟩ => by linarith ⟩;
    refine' ⟨ 0, fun _ => ⟨ fun _ => BoundedInterval.Icc 0 0 ⟩, _, _ ⟩ <;> norm_num [ hB_empty ];
    cases d <;> norm_num [ Box.volume ] at * ; linarith

/-- The graph of a continuous function over a closed box has Jordan outer measure zero. -/
lemma graph_outer_measure_zero {d:ℕ} {B:Box d} {f: EuclideanSpace' d → ℝ}
    (hB: ∀ i, ∃ a b, B.side i = BoundedInterval.Icc a b) (hf: ContinuousOn f B.toSet) :
    Jordan_outer_measure { p | ∃ x ∈ B.toSet, EuclideanSpace'.prod_equiv d 1 p = ⟨ x, f x ⟩ } = 0 := by
  refine le_antisymm ?_ (Jordan_outer_measure_nonneg _)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨N, C, hcov, hsum⟩ := graph_grid_cover hB hf hε
  have hbdd : Bornology.IsBounded (⋃ j, (C j).toSet) := by
    have := isBounded_biUnion_box (Finset.univ : Finset (Fin d → Fin N)) C
    simpa using this
  calc Jordan_outer_measure { p | ∃ x ∈ B.toSet, EuclideanSpace'.prod_equiv d 1 p = ⟨ x, f x ⟩ }
      ≤ Jordan_outer_measure (⋃ j, (C j).toSet) := Jordan_outer_measure_mono_of_subset hcov hbdd
    _ = Jordan_outer_measure (⋃ j ∈ (Finset.univ : Finset (Fin d → Fin N)), (C j).toSet) := by simp
    _ ≤ ∑ j, |C j|ᵥ := Jordan_outer_measure_biUnion_box_le _ _
    _ ≤ ε := hsum
    _ ≤ 0 + ε := by linarith

end GraphMeasurableAux

/-- Exercise 1.1.7 (i) (Regions under graphs are Jordan measurable)

Corrected statement: {lit}`B` is required to be a **closed** box (all sides {lit}`Icc`), matching Tao's
Exercise 1.1.7.  Without this hypothesis the statement is false (see the commented-out original
below and the note above). -/
lemma JordanMeasurable.graph {d:ℕ} {B:Box d} {f: EuclideanSpace' d → ℝ}
    (hB: ∀ i, ∃ a b, B.side i = BoundedInterval.Icc a b) (hf: ContinuousOn f B.toSet) :
    JordanMeasurable { p | ∃ x ∈ B.toSet, EuclideanSpace'.prod_equiv d 1 p = ⟨ x, f x ⟩ } := by
  refine ⟨graph_isBounded hB hf, ?_⟩
  have ho := graph_outer_measure_zero hB hf
  have hio := Jordan_inner_le_outer (graph_isBounded hB hf)
  have hin := Jordan_inner_measure_nonneg
    { p | ∃ x ∈ B.toSet, EuclideanSpace'.prod_equiv d 1 p = ⟨ x, f x ⟩ }
  rw [ho] at hio ⊢
  linarith

-- Original (incorrect) statement of Exercise 1.1.7 (i), kept for reference.  It is FALSE for boxes
-- with open sides: e.g. `f x = 1/x` is continuous on the open box `(0,1)` but its graph is
-- unbounded, hence not Jordan measurable.
-- lemma JordanMeasurable.graph {d:ℕ} {B:Box d} {f: EuclideanSpace' d → ℝ} (hf: ContinuousOn f B.toSet) : JordanMeasurable { p | ∃ x ∈ B.toSet, EuclideanSpace'.prod_equiv d 1 p = ⟨ x, f x ⟩ } := by
--   sorry

/-- Exercise 1.1.7 (i) (Regions under graphs are Jordan measurable).

Corrected statement: {lit}`B` is required to be a closed box (see {lit}`JordanMeasurable.graph`). -/
lemma JordanMeasurable.measure_of_graph {d:ℕ} {B:Box d} {f: EuclideanSpace' d → ℝ}
    (hB: ∀ i, ∃ a b, B.side i = BoundedInterval.Icc a b) (hf: ContinuousOn f B.toSet) :
    (JordanMeasurable.graph hB hf).measure = 0 := by
  have hJM := JordanMeasurable.graph hB hf
  rw [hJM.eq_outer]
  exact graph_outer_measure_zero hB hf

/-- If {lit}`u` and {lit}`η` are real and {lit}`η ≥ 0`, then `max(0, u+η) - max(0, u-η) ≤ 2*η`. -/
lemma max_sub_max_le {u η : ℝ} (hη : 0 ≤ η) : max 0 (u + η) - max 0 (u - η) ≤ 2 * η := by
  by_cases h : 0 ≤ u - η
  · -- u - η ≥ 0, so u + η ≥ 2η ≥ 0, both maxes equal to u±η
    have h1 : max 0 (u - η) = u - η := max_eq_right h
    have h2 : max 0 (u + η) = u + η := max_eq_right (by nlinarith)
    rw [h1, h2]
    nlinarith
  · -- u - η < 0, so max(0, u-η) = 0
    have h0 : u - η ≤ 0 := by linarith
    have h1 : max 0 (u - η) = 0 := max_eq_left h0
    rw [h1]
    by_cases h' : 0 ≤ u + η
    · -- u + η ≥ 0 > u - η
      have : max 0 (u + η) = u + η := max_eq_right h'
      rw [this]
      nlinarith
    · -- u + η < 0, so both maxes are 0
      have h0' : u + η ≤ 0 := by linarith
      have : max 0 (u + η) = 0 := max_eq_left h0'
      rw [this]
      nlinarith

/-- The total volume of all Qbox cells equals the volume of the big box B. -/
lemma GraphGrid.sum_vol_Qbox {d:ℕ} (a b : Fin d → ℝ) (hab: ∀ i, a i ≤ b i) {N:ℕ} (hN: 0 < N) :
    ∑ k : Fin d → Fin N, |GraphGrid.Qbox a b N k|ᵥ = ∏ i, (b i - a i) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    ∑ k : Fin d → Fin N, |GraphGrid.Qbox a b N k|ᵥ
        = ∑ k : Fin d → Fin N, ∏ i, ((b i - a i) / (N : ℝ)) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [GraphGrid.Qbox_volume a b hab hN k]
    _ = ((Finset.card (Finset.univ : Finset (Fin d → Fin N))) : ℝ) * (∏ i, ((b i - a i) / (N : ℝ))) := by
      simp
    _ = ((N : ℝ) ^ d) * (∏ i, ((b i - a i) / (N : ℝ))) := by
      simp
    _ = ((N : ℝ) ^ d) * ((∏ i, (b i - a i)) / ((N : ℝ) ^ d)) := by
      simp [Finset.prod_div_distrib]
    _ = ∏ i, (b i - a i) := by
      field_simp [pow_ne_zero d hNpos.ne']


/-- The undergraph of {lean}`f` over a closed box {lean}`B` is bounded. -/
lemma undergraph_isBounded {d:ℕ} {B:Box d} {f: EuclideanSpace' d → ℝ}
    (hB: ∀ i, ∃ a b, B.side i = BoundedInterval.Icc a b) (hf: ContinuousOn f B.toSet) :
    Bornology.IsBounded { p | ∃ x ∈ B.toSet, ∃ t:ℝ, EuclideanSpace'.prod_equiv d 1 p = ⟨ x, t ⟩ ∧ 0 ≤ t ∧ t ≤ f x } := by
  obtain ⟨ M, hM ⟩ := IsCompact.exists_bound_of_continuousOn ( Box.isCompact_of_closed hB ) hf
  have hbox_bounded : Bornology.IsBounded ((Box.prod B ((BoundedInterval.Icc 0 M : Box 1))).toSet) :=
    IsElementary.isBounded (IsElementary.box _)
  refine hbox_bounded.subset ?_
  intro p hp
  obtain ⟨ x, hx, t, hp_eq, ht0, ht ⟩ := hp
  have hfx : f x ≤ M := by
    have := abs_le.mp (hM x hx)
    linarith
  rw [Box.prod_toSet, EuclideanSpace'.prod, Set.mem_image]
  refine ⟨(x, Real.equiv_EuclideanSpace' t), ⟨hx, ?_⟩, ?_⟩
  · rw [BoundedInterval.coe_of_box, Set.mem_image]
    exact ⟨t, ⟨ht0, ht.trans hfx⟩, rfl⟩
  · calc
      (EuclideanSpace'.prod_equiv d 1).symm (x, Real.equiv_EuclideanSpace' t)
          = (EuclideanSpace'.prod_equiv d 1).symm ((EuclideanSpace'.prod_equiv d 1) p) := by
            simp [hp_eq]
      _ = p := by simp

/-- For {lit}`ε>0`, construct elementary {lit}`A` such that
{lit}`Jordan_outer_measure (symmDiff U A) ≤ ε`.
Used to prove {lit}`JordanMeasurable.undergraph` via {lean}`JordanMeasurable.equiv`. -/
lemma undergraph_approx {d:ℕ} {B:Box d} {f: EuclideanSpace' d → ℝ}
    (hB: ∀ i, ∃ a b, B.side i = BoundedInterval.Icc a b) (hf: ContinuousOn f B.toSet)
    {ε:ℝ} (hε: 0 < ε) :
    ∃ A : Set (EuclideanSpace' (d+1)), IsElementary A ∧
    Jordan_outer_measure (symmDiff
      { p | ∃ x ∈ B.toSet, ∃ t:ℝ, EuclideanSpace'.prod_equiv d 1 p = ⟨ x, t ⟩ ∧ 0 ≤ t ∧ t ≤ f x } A) ≤ ε := by
  set U := { p | ∃ x ∈ B.toSet, ∃ t:ℝ, EuclideanSpace'.prod_equiv d 1 p = ⟨ x, t ⟩ ∧ 0 ≤ t ∧ t ≤ f x } with hU
  by_cases h_empty : B.toSet = ∅
  · have hU_empty : U = ∅ := by
      ext p; simp [hU, h_empty]
    refine ⟨∅, IsElementary.empty (d+1), ?_⟩
    have : symmDiff (∅ : Set (EuclideanSpace' (d+1))) ∅ = (∅ : Set (EuclideanSpace' (d+1))) := by
      simp
    rw [hU_empty, this, Jordan_outer_measure_empty]
    exact hε.le
  have h_nonempty : B.toSet.Nonempty := Set.nonempty_iff_ne_empty.mpr h_empty
  have hcompact : IsCompact B.toSet := Box.isCompact_of_closed hB
  have h_vol_nonneg : 0 ≤ |B|ᵥ := by
    apply Finset.prod_nonneg
    intro i _
    exact BoundedInterval.length_nonneg _
  set η := ε / (2 * (|B|ᵥ + 1)) with hη_def
  have hη_pos : 0 < η := by
    apply div_pos hε
    have : 0 < 2 * (|B|ᵥ + 1) := by nlinarith
    exact this
  choose a b hBside using hB
  have hab : ∀ i, a i ≤ b i := by
    intro i
    obtain ⟨x, hx⟩ := h_nonempty
    have hxi := hx i
    rw [hBside i] at hxi
    exact hxi.1.trans hxi.2
  obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ u v : EuclideanSpace' d, u ∈ B.toSet → v ∈ B.toSet → dist u v < δ → |f u - f v| < η := by
    have hunif : UniformContinuousOn f B.toSet :=
      hcompact.uniformContinuousOn_of_continuous hf
    have := Metric.uniformContinuousOn_iff.mp hunif η hη_pos
    aesop
  obtain ⟨N, hN_pos, hN⟩ : ∃ N : ℕ, 0 < N ∧ Real.sqrt (∑ i, (b i - a i)^2) / (N : ℝ) < δ := by
    set s := Real.sqrt (∑ i, (b i - a i)^2) with hs
    have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
    set N0 : ℕ := ⌊s / δ⌋₊ + 1 with hN0
    have hN0_pos : 0 < N0 := Nat.succ_pos _
    have hN0_pos' : (0 : ℝ) < (N0 : ℝ) := by exact_mod_cast hN0_pos
    have h_floor : s / δ < (⌊s / δ⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one (s / δ)
    refine ⟨N0, hN0_pos, ?_⟩
    have h_ineq : s < (N0 : ℝ) * δ := by
      calc
        s = (s / δ) * δ := by field_simp [hδ_pos.ne']
        _ < ((⌊s / δ⌋₊ : ℝ) + 1) * δ := by nlinarith
        _ = (N0 : ℝ) * δ := by
          dsimp [N0]
          simp
    have hpos : (0 : ℝ) < (N0 : ℝ) := by exact_mod_cast hN0_pos
    have : s / (N0 : ℝ) < δ := by
      have h_ineq' : s < δ * (N0 : ℝ) := by
        calc
          s < (N0 : ℝ) * δ := h_ineq
          _ = δ * (N0 : ℝ) := by ring
      calc
        s / (N0 : ℝ) < (δ * (N0 : ℝ)) / (N0 : ℝ) :=
          div_lt_div_of_pos_right h_ineq' hpos
        _ = δ := by field_simp [hpos.ne']
    exact this
  let Qk (k : Fin d → Fin N) : Box d := GraphGrid.Qbox a b N k
  let xk (k : Fin d → Fin N) : EuclideanSpace' d := GraphGrid.corner a b N k
  have h_xk_mem (k : Fin d → Fin N) : xk k ∈ B.toSet := by
    intro i
    rw [hBside i, GraphGrid.corner_apply, GraphGrid.cornerLo]
    have hk_nonneg : (0 : ℝ) ≤ (k i : ℝ) := Nat.cast_nonneg _
    have hk_lt_N : (k i : ℝ) < (N : ℝ) := by exact_mod_cast Fin.is_lt (k i)
    have h_diff_nonneg : 0 ≤ b i - a i := sub_nonneg.mpr (hab i)
    have h_lo : a i ≤ a i + (b i - a i) * (k i : ℝ) / (N : ℝ) := by
      have : 0 ≤ (b i - a i) * (k i : ℝ) / (N : ℝ) := by positivity
      nlinarith
    have h_hi : a i + (b i - a i) * (k i : ℝ) / (N : ℝ) ≤ b i := by
      have h_mul : (b i - a i) * (k i : ℝ) / (N : ℝ) ≤ b i - a i := by
        have h_div : (k i : ℝ) / (N : ℝ) ≤ 1 := (div_le_one (by positivity)).mpr hk_lt_N.le
        calc
          (b i - a i) * (k i : ℝ) / (N : ℝ) = (b i - a i) * ((k i : ℝ) / (N : ℝ)) := by ring
          _ ≤ (b i - a i) * 1 := by gcongr
          _ = b i - a i := by ring
      nlinarith
    exact ⟨h_lo, h_hi⟩
  let mk (k : Fin d → Fin N) : ℝ := max 0 (f (xk k) - η)
  let Mk (k : Fin d → Fin N) : ℝ := max 0 (f (xk k) + η)
  have hmk_nonneg (k : Fin d → Fin N) : 0 ≤ mk k := le_max_left _ _
  have hmk_le_Mk (k : Fin d → Fin N) : mk k ≤ Mk k :=
    max_le_max (le_refl 0) (by nlinarith)
  -- Inner approximation: union of grid cells Qk × [0, mk]
  set A := ⋃ k : Fin d → Fin N, ((Box.prod (Qk k) ((BoundedInterval.Icc 0 (mk k) : Box 1))).toSet) with hA_def
  have hA_elem : IsElementary A := by
    let S : Finset (Set (EuclideanSpace' (d+1))) :=
      Finset.image (fun (k : Fin d → Fin N) => (Box.prod (Qk k) ((BoundedInterval.Icc 0 (mk k) : Box 1))).toSet) Finset.univ
    have hS : ∀ E ∈ S, IsElementary E := by
      intro E hE
      rcases Finset.mem_image.mp hE with ⟨k, _, rfl⟩
      exact IsElementary.box (Box.prod (Qk k) ((BoundedInterval.Icc 0 (mk k) : Box 1)))
    have hA_eq : A = ⋃ E ∈ S, E := by
      ext p; simp [hA_def, S]
    rw [hA_eq]
    exact IsElementary.union' hS
  -- Cover U \ A by boxes Dk = Qk × [mk, Mk]
  let Dk (k : Fin d → Fin N) : Box (d+1) :=
    Box.prod (Qk k) ((BoundedInterval.Icc (mk k) (Mk k) : Box 1))
  have hDk_vol (k : Fin d → Fin N) : |Dk k|ᵥ = |(Qk k)|ᵥ * (Mk k - mk k) := by
    simp [Dk, Box.volume_prod, Box.volume_of_interval, BoundedInterval.length, hmk_le_Mk k]
  have h_diff_bound (k : Fin d → Fin N) : Mk k - mk k ≤ 2 * η :=
    max_sub_max_le (hη_pos.le)
  have h_vol_Qk_nonneg (k : Fin d → Fin N) : 0 ≤ |(Qk k)|ᵥ := by
    apply Finset.prod_nonneg
    intro i _
    apply BoundedInterval.length_nonneg
  have h_sum_vol : ∑ k, |(Qk k)|ᵥ = |B|ᵥ := by
    calc
      ∑ k, |(Qk k)|ᵥ = ∑ k : Fin d → Fin N, |GraphGrid.Qbox a b N k|ᵥ := rfl
      _ = ∏ i, (b i - a i) := GraphGrid.sum_vol_Qbox a b hab hN_pos
      _ = |B|ᵥ := by
        refine calc
          ∏ i, (b i - a i) = ∏ i, |(B.side i : BoundedInterval)|ₗ := by
            refine Finset.prod_congr rfl fun i _ => ?_
            rw [hBside i]
            simp [hab i]
          _ = |B|ᵥ := rfl
  have h_total_vol : ∑ k, |Dk k|ᵥ ≤ 2 * η * |B|ᵥ := by
    calc
      ∑ k, |Dk k|ᵥ = ∑ k, (|(Qk k)|ᵥ * (Mk k - mk k)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hDk_vol k]
      _ ≤ ∑ k, (|(Qk k)|ᵥ * (2 * η)) := by
        refine Finset.sum_le_sum fun k _ => ?_
        have : 0 ≤ |(Qk k)|ᵥ := h_vol_Qk_nonneg k
        gcongr
        exact h_diff_bound k
      _ = (2 * η) * ∑ k, |(Qk k)|ᵥ := by
        simp [Finset.mul_sum, mul_comm, mul_assoc]
      _ = (2 * η) * |B|ᵥ := by rw [h_sum_vol]
  have h_final : 2 * η * |B|ᵥ < ε := by
    dsimp [η]
    have h_vol_plus_one_pos : 0 < |B|ᵥ + 1 := by
      have : 0 ≤ |B|ᵥ := h_vol_nonneg
      nlinarith
    have h_calc : ε * |B|ᵥ / (|B|ᵥ + 1) < ε := by
      refine (div_lt_iff₀ h_vol_plus_one_pos).mpr ?_
      nlinarith
    have h_eq : 2 * (ε / (2 * (|B|ᵥ + 1))) * |B|ᵥ = ε * |B|ᵥ / (|B|ᵥ + 1) := by
      field_simp [h_vol_plus_one_pos.ne']
    nlinarith
  -- Bound Jordan_outer_measure (U \ A) by ∑|Dk k|ᵥ
  have h_bounded_D : Bornology.IsBounded (⋃ k, (Dk k).toSet) := by
    have : Bornology.IsBounded (⋃ k ∈ Finset.univ, (Dk k).toSet) :=
      isBounded_biUnion_box (Finset.univ : Finset (Fin d → Fin N)) Dk
    simpa using this
  have h_cover : U \ A ⊆ ⋃ k, (Dk k).toSet := by
    intro p hp
    rcases hp with ⟨hpU, hpA⟩
    rw [hU] at hpU
    rcases hpU with ⟨x, hx, t, hp_eq, ht0, ht_le_fx⟩
    -- Find which grid cell x belongs to
    have hx_coord : ∀ i, a i ≤ x i ∧ x i ≤ b i := by
      intro i; have hxi := hx i; rw [hBside i] at hxi; exact hxi
    have hx_corner : ∃ k : Fin d → Fin N, ∀ i, GraphGrid.cornerLo a b N k i ≤ x i ∧ x i ≤ GraphGrid.cornerHi a b N k i := by
      exact ⟨ fun i => Classical.choose ( GraphGrid.exists_cell ( hab i ) hN_pos ( hx_coord i |>.1 ) ( hx_coord i |>.2 ) ), fun i => Classical.choose_spec ( GraphGrid.exists_cell ( hab i ) hN_pos ( hx_coord i |>.1 ) ( hx_coord i |>.2 ) ) ⟩
    obtain ⟨k, hk⟩ := hx_corner
    have hxQ : x ∈ (Qk k).toSet := by
      rw [Box.mem_toSet]
      intro i; simpa [Qk, GraphGrid.Qbox] using hk i
    -- Distance bound from x to xk
    have hx_dist : dist x (xk k) ≤ Real.sqrt (∑ i, (b i - a i)^2) / (N : ℝ) := by
      have hx_dist_eq : dist x (xk k) = Real.sqrt (∑ i, (x i - GraphGrid.cornerLo a b N k i)^2) := by
        simp +decide [dist_eq_norm, EuclideanSpace.norm_eq, xk, GraphGrid.corner]
      have hx_dist_le : ∀ i, (x i - GraphGrid.cornerLo a b N k i)^2 ≤ ((b i - a i) / (N : ℝ))^2 := by
        intro i
        have h_diff : x i - GraphGrid.cornerLo a b N k i ≤ (b i - a i) / (N : ℝ) := by
          have h_cornerHi_eq : GraphGrid.cornerHi a b N k i = GraphGrid.cornerLo a b N k i + (b i - a i) / (N : ℝ) := by
            simp [GraphGrid.cornerHi, GraphGrid.cornerLo]
            ring
          have hi := hk i
          rw [h_cornerHi_eq] at hi
          nlinarith
        have h_nonneg : 0 ≤ x i - GraphGrid.cornerLo a b N k i := sub_nonneg.mpr (hk i |>.1)
        exact pow_le_pow_left₀ h_nonneg h_diff 2
      rw [hx_dist_eq, Real.sqrt_le_iff]
      constructor
      · positivity
      · rw [div_pow, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
        calc
          ∑ i, (x i - GraphGrid.cornerLo a b N k i)^2 ≤ ∑ i, ((b i - a i) / (N : ℝ))^2 :=
            Finset.sum_le_sum fun i _ => hx_dist_le i
          _ = (∑ i, (b i - a i)^2) / ((N : ℝ)^2) := by simp [div_pow, Finset.sum_div]
    have h_dist_lt : dist x (xk k) < δ := lt_of_le_of_lt hx_dist hN
    have h_f_diff : |f x - f (xk k)| < η := hδ x (xk k) hx (h_xk_mem k) h_dist_lt
    -- Show that p ∉ A implies mk k < t
    have h_mk_lt_t : mk k < t := by
      by_contra! h
      -- then t ≤ mk k, so p ∈ A, contradiction
      have hpA' : p ∈ A := by
        rw [hA_def]
        refine Set.mem_iUnion.mpr ⟨k, ?_⟩
        rw [Box.prod_toSet, EuclideanSpace'.prod, Set.mem_image]
        refine ⟨(x, Real.equiv_EuclideanSpace' t), ⟨hxQ, ?_⟩, ?_⟩
        · rw [BoundedInterval.coe_of_box, Set.mem_image]
          exact ⟨t, ⟨ht0, h⟩, by simp⟩
        · calc
            (EuclideanSpace'.prod_equiv d 1).symm (x, Real.equiv_EuclideanSpace' t)
                = (EuclideanSpace'.prod_equiv d 1).symm ((EuclideanSpace'.prod_equiv d 1) p) := by
                  simp [hp_eq]
            _ = p := by simp
      exact hpA hpA'
    have ht_Mk : t ≤ Mk k := by
      have h_fx_lt : f x < f (xk k) + η := by
        have := abs_lt.mp h_f_diff
        linarith
      have : f (xk k) + η ≤ Mk k := le_max_right _ _
      nlinarith
    -- Show p ∈ (Dk k).toSet
    refine Set.mem_iUnion.mpr ⟨k, ?_⟩
    rw [Box.prod_toSet, EuclideanSpace'.prod, Set.mem_image]
    refine ⟨(x, Real.equiv_EuclideanSpace' t), ⟨hxQ, ?_⟩, ?_⟩
    · rw [BoundedInterval.coe_of_box, Set.mem_image]
      exact ⟨t, ⟨by nlinarith, ht_Mk⟩, by simp⟩
    · calc
        (EuclideanSpace'.prod_equiv d 1).symm (x, Real.equiv_EuclideanSpace' t)
            = (EuclideanSpace'.prod_equiv d 1).symm ((EuclideanSpace'.prod_equiv d 1) p) := by
              simp [hp_eq]
        _ = p := by simp
  have h_outer_U_A : Jordan_outer_measure (U \ A) ≤ ∑ k, |Dk k|ᵥ := by
    calc
      Jordan_outer_measure (U \ A) ≤ Jordan_outer_measure (⋃ k, (Dk k).toSet) :=
        Jordan_outer_measure_mono_of_subset h_cover h_bounded_D
      _ = Jordan_outer_measure (⋃ k ∈ (Finset.univ : Finset (Fin d → Fin N)), (Dk k).toSet) := by simp
      _ ≤ ∑ k, |Dk k|ᵥ := Jordan_outer_measure_biUnion_box_le (Finset.univ : Finset (Fin d → Fin N)) Dk
  -- Bound Jordan_outer_measure (A \ U): A\U ⊆ B × {0}, which has measure zero
  have h_A_U_sub_floor : A \ U ⊆ (Box.prod B ((BoundedInterval.Icc 0 0 : Box 1))).toSet := by
    intro p hp
    rcases hp with ⟨hpA, hpU⟩
    have hkA : ∃ (k' : Fin d → Fin N), p ∈ ((Box.prod (Qk k') ((BoundedInterval.Icc 0 (mk k') : Box 1))).toSet) := by
      simpa [hA_def, Set.mem_iUnion] using hpA
    rcases hkA with ⟨k, hpA⟩
    -- Decompose p ∈ (Box.prod (Qk k) (Icc 0 (mk k))).toSet
    rw [Box.prod_toSet, EuclideanSpace'.prod, Set.mem_image] at hpA
    rcases hpA with ⟨⟨x, t'⟩, ⟨hx, ht'⟩, hp_eq⟩
    rw [BoundedInterval.coe_of_box] at ht'
    rcases ht' with ⟨t, ht, ht'_eq⟩
    replace hp_eq : (EuclideanSpace'.prod_equiv d 1).symm (x, Real.equiv_EuclideanSpace' t) = p := by
      simpa [ht'_eq] using hp_eq
    rcases ht with ⟨ht0, ht_le_mk⟩
    have hx_in_B : x ∈ B.toSet := by
      rw [Box.mem_toSet]
      intro i
      have hxi := hx i
      -- hxi: x i ∈ (Qk k).side i = Icc (cornerLo a b N k i) (cornerHi a b N k i)
      -- This is contained in Icc (a i) (b i)
      have h_cornerLo_ge_a : a i ≤ GraphGrid.cornerLo a b N k i := by
        dsimp [GraphGrid.cornerLo]
        have h_nonneg : 0 ≤ (b i - a i) * (k i : ℝ) / (N : ℝ) := by
          have h_nonneg_num : 0 ≤ (b i - a i) * (k i : ℝ) :=
            mul_nonneg (sub_nonneg.mpr (hab i)) (Nat.cast_nonneg _)
          have h_pos_denom : 0 ≤ (N : ℝ) := by exact_mod_cast hN_pos.le
          exact div_nonneg h_nonneg_num h_pos_denom
        nlinarith
      have h_cornerHi_le_b : GraphGrid.cornerHi a b N k i ≤ b i := by
        have hk_lt_N : (k i : ℝ) < (N : ℝ) := by exact_mod_cast Fin.is_lt (k i)
        have h_diff_nonneg : 0 ≤ b i - a i := sub_nonneg.mpr (hab i)
        dsimp [GraphGrid.cornerHi]
        have hk1 : (k i : ℝ) + 1 ≤ (N : ℝ) := by
          have : (k i : ℕ) + 1 ≤ N := Nat.succ_le_of_lt (Fin.is_lt (k i))
          exact_mod_cast this
        have h_div : ((k i : ℝ) + 1) / (N : ℝ) ≤ 1 :=
          (div_le_one (by exact_mod_cast hN_pos)).mpr hk1
        calc
          a i + (b i - a i) * ((k i : ℝ) + 1) / (N : ℝ) = a i + (b i - a i) * (((k i : ℝ) + 1) / (N : ℝ)) := by ring
          _ ≤ a i + (b i - a i) := by gcongr; nlinarith
          _ = b i := by ring
      rw [hBside i]
      rcases hxi with ⟨hlo, hhi⟩
      exact ⟨le_trans h_cornerLo_ge_a hlo, le_trans hhi h_cornerHi_le_b⟩
    have hk_cell : ∀ i, GraphGrid.cornerLo a b N k i ≤ x i ∧ x i ≤ GraphGrid.cornerHi a b N k i := by
      intro i
      have hxi := hx i
      simp [Qk, GraphGrid.Qbox] at hxi
      exact hxi
    -- Show that t = 0 (so p lies on the floor)
    have ht_zero : t = 0 := by
      by_contra! ht_pos
      have hmk_pos : 0 < mk k := lt_of_lt_of_le (by positivity) ht_le_mk
      have hfxk_gt_η : η < f (xk k) := by
        by_contra! h
        have : f (xk k) - η ≤ 0 := by linarith
        have hmk_zero : mk k = 0 := by
          dsimp [mk]
          rw [max_eq_left this]
        rw [hmk_zero] at hmk_pos
        linarith
      have hmk_eq : mk k = f (xk k) - η := by
        dsimp [mk]
        have h_nonneg : 0 ≤ f (xk k) - η := by linarith
        rw [max_eq_right h_nonneg]
      have hx_dist : dist x (xk k) ≤ Real.sqrt (∑ i, (b i - a i)^2) / (N : ℝ) := by
        have hx_dist_eq : dist x (xk k) = Real.sqrt (∑ i, (x i - GraphGrid.cornerLo a b N k i)^2) := by
          simp +decide [dist_eq_norm, EuclideanSpace.norm_eq, xk, GraphGrid.corner]
        have hx_dist_le : ∀ i, (x i - GraphGrid.cornerLo a b N k i)^2 ≤ ((b i - a i) / (N : ℝ))^2 := by
          intro i
          have h_diff : x i - GraphGrid.cornerLo a b N k i ≤ (b i - a i) / (N : ℝ) := by
            have h_cornerHi_eq : GraphGrid.cornerHi a b N k i = GraphGrid.cornerLo a b N k i + (b i - a i) / (N : ℝ) := by
              simp [GraphGrid.cornerHi, GraphGrid.cornerLo]
              ring
            have hi := hk_cell i
            rw [h_cornerHi_eq] at hi
            nlinarith
          have h_nonneg : 0 ≤ x i - GraphGrid.cornerLo a b N k i := sub_nonneg.mpr (hk_cell i |>.1)
          exact pow_le_pow_left₀ h_nonneg h_diff 2
        rw [hx_dist_eq, Real.sqrt_le_iff]
        constructor
        · positivity
        · rw [div_pow, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
          calc
            ∑ i, (x i - GraphGrid.cornerLo a b N k i)^2 ≤ ∑ i, ((b i - a i) / (N : ℝ))^2 :=
              Finset.sum_le_sum fun i _ => hx_dist_le i
            _ = (∑ i, (b i - a i)^2) / ((N : ℝ)^2) := by simp [div_pow, Finset.sum_div]
      have h_dist_lt : dist x (xk k) < δ := lt_of_le_of_lt hx_dist hN
      have h_f_diff : |f x - f (xk k)| < η := hδ x (xk k) hx_in_B (h_xk_mem k) h_dist_lt
      have h_fx_gt_mk : f x > mk k := by
        rw [hmk_eq]
        have h_abs := abs_lt.mp h_f_diff
        linarith
      have hpU' : p ∈ U := by
        rw [hU]
        refine ⟨x, hx_in_B, t, ?_, ht0, le_trans ht_le_mk (by linarith)⟩
        calc
          (EuclideanSpace'.prod_equiv d 1) p = (EuclideanSpace'.prod_equiv d 1) ((EuclideanSpace'.prod_equiv d 1).symm (x, Real.equiv_EuclideanSpace' t)) := by rw [hp_eq]
          _ = (x, Real.equiv_EuclideanSpace' t) := by simp
      exact hpU hpU'
    rw [Box.prod_toSet, EuclideanSpace'.prod, Set.mem_image]
    refine ⟨(x, Real.equiv_EuclideanSpace' 0), ⟨hx_in_B, ?_⟩, ?_⟩
    · rw [BoundedInterval.coe_of_box]
      refine ⟨0, ⟨by norm_num, by norm_num⟩, by simp⟩
    · calc
        (EuclideanSpace'.prod_equiv d 1).symm (x, Real.equiv_EuclideanSpace' 0)
            = (EuclideanSpace'.prod_equiv d 1).symm (x, Real.equiv_EuclideanSpace' t) := by simp [ht_zero]
        _ = p := hp_eq
  have h_floor_vol : |Box.prod B ((BoundedInterval.Icc 0 0 : Box 1))|ᵥ = 0 := by
    simp [Box.volume_prod, Box.volume_of_interval, BoundedInterval.length]
  have h_floor_bounded : Bornology.IsBounded ((Box.prod B ((BoundedInterval.Icc 0 0 : Box 1))).toSet) :=
    IsElementary.isBounded (IsElementary.box _)
  have h_outer_A_U : Jordan_outer_measure (A \ U) ≤ 0 := by
    calc
      Jordan_outer_measure (A \ U) ≤ Jordan_outer_measure ((Box.prod B ((BoundedInterval.Icc 0 0 : Box 1))).toSet) :=
        Jordan_outer_measure_mono_of_subset h_A_U_sub_floor h_floor_bounded
      _ = 0 := by
        apply le_antisymm ?_ (Jordan_outer_measure_nonneg _)
        have hElem : IsElementary ((Box.prod B ((BoundedInterval.Icc 0 0 : Box 1))).toSet) :=
          IsElementary.box _
        have hsub : ((Box.prod B ((BoundedInterval.Icc 0 0 : Box 1))).toSet) ⊆
          ((Box.prod B ((BoundedInterval.Icc 0 0 : Box 1))).toSet) := Set.Subset.refl _
        calc
          Jordan_outer_measure ((Box.prod B ((BoundedInterval.Icc 0 0 : Box 1))).toSet)
              ≤ (hElem.measure) := Jordan_outer_le hElem hsub
          _ = |Box.prod B ((BoundedInterval.Icc 0 0 : Box 1))|ᵥ := by
            simp
          _ = 0 := h_floor_vol
  have h_bound : Jordan_outer_measure (symmDiff U A) ≤ ε := by
    have hB' : ∀ i, ∃ a b, B.side i = BoundedInterval.Icc a b := by
      intro i; exact ⟨a i, b i, hBside i⟩
    have hU_bounded : Bornology.IsBounded U := undergraph_isBounded hB' hf
    have h_bounded_U_A : Bornology.IsBounded (U \ A) :=
      hU_bounded.subset (Set.diff_subset (s := U) (t := A))
    have hA_bounded : Bornology.IsBounded A := IsElementary.isBounded hA_elem
    have h_bounded_A_U : Bornology.IsBounded (A \ U) :=
      hA_bounded.subset (Set.diff_subset (s := A) (t := U))
    have h_lt : Jordan_outer_measure (symmDiff U A) < ε := by
      calc
        Jordan_outer_measure (symmDiff U A) = Jordan_outer_measure ((U \ A) ∪ (A \ U)) := by
          simp [symmDiff_def]
        _ ≤ Jordan_outer_measure (U \ A) + Jordan_outer_measure (A \ U) :=
          Jordan_outer_subadd h_bounded_U_A h_bounded_A_U
        _ ≤ ∑ k, |Dk k|ᵥ + 0 := by nlinarith
        _ < ε := by nlinarith
    -- But we need ≤ ε, not < ε
    exact le_of_lt h_lt
  exact ⟨A, hA_elem, h_bound⟩

/-- Exercise 1.1.7 (i) (Regions under graphs are Jordan measurable).

Corrected statement: {lit}`B` is required to be a closed box (see {lit}`JordanMeasurable.graph`).  As with the
graph, the region under the graph of a continuous function on an *open* box need not be Jordan
measurable, so closedness of {lit}`B` is needed. -/
lemma JordanMeasurable.undergraph {d:ℕ} {B:Box d} {f: EuclideanSpace' d → ℝ}
    (hB: ∀ i, ∃ a b, B.side i = BoundedInterval.Icc a b) (hf: ContinuousOn f B.toSet) :
    JordanMeasurable { p | ∃ x ∈ B.toSet, ∃ t:ℝ, EuclideanSpace'.prod_equiv d 1 p = ⟨ x, t ⟩ ∧ 0 ≤ t ∧ t ≤ f x } := by
  set U := { p | ∃ x ∈ B.toSet, ∃ t:ℝ, EuclideanSpace'.prod_equiv d 1 p = ⟨ x, t ⟩ ∧ 0 ≤ t ∧ t ≤ f x } with hU
  have h_bounded : Bornology.IsBounded U := undergraph_isBounded hB hf
  have h_equiv := (JordanMeasurable.equiv h_bounded).out 0 2
  rcases h_equiv with ⟨h_imp, h_imp'⟩
  apply h_imp'
  intro ε hε
  obtain ⟨A, hA, h_bound⟩ := undergraph_approx hB hf hε
  refine ⟨A, hA, ?_⟩
  -- h_bound: Jordan_outer_measure (symmDiff U A) ≤ ε where U is the one from undergraph_approx
  -- But h_bound uses the U defined inside undergraph_approx, which is the same set as our U
  -- So we can just use h_bound directly
  -- Actually, h_bound's type is Jordan_outer_measure (symmDiff ?U A) ≤ ε where ?U = U
  simpa [hU] using h_bound


/-- The sandwich region between lo and hi over a 1D closed box is Jordan measurable. -/
lemma sandwich_jordan (B : Box 1) (hB : ∀ i : Fin 1, ∃ a b, B.side i = BoundedInterval.Icc a b)
    (lo hi : EuclideanSpace' 1 → ℝ) (hlo_cont : ContinuousOn lo B.toSet) (hhi_cont : ContinuousOn hi B.toSet)
    (hlo_nonneg : ∀ x ∈ B.toSet, 0 ≤ lo x) (hlo_le_hi : ∀ x ∈ B.toSet, lo x ≤ hi x) :
    JordanMeasurable {p : EuclideanSpace' 2 | ∃ x ∈ B.toSet, ∃ t : ℝ,
      EuclideanSpace'.prod_equiv 1 1 p = ((x, (t : EuclideanSpace' 1)) : EuclideanSpace' 1 × EuclideanSpace' 1) ∧ lo x ≤ t ∧ t ≤ hi x} := by
  set UG_hi := {p : EuclideanSpace' 2 | ∃ x ∈ B.toSet, ∃ t : ℝ,
    EuclideanSpace'.prod_equiv 1 1 p = ((x, (t : EuclideanSpace' 1)) : EuclideanSpace' 1 × EuclideanSpace' 1) ∧ 0 ≤ t ∧ t ≤ hi x}
  set UG_lo := {p : EuclideanSpace' 2 | ∃ x ∈ B.toSet, ∃ t : ℝ,
    EuclideanSpace'.prod_equiv 1 1 p = ((x, (t : EuclideanSpace' 1)) : EuclideanSpace' 1 × EuclideanSpace' 1) ∧ 0 ≤ t ∧ t ≤ lo x}
  set G_lo := {p : EuclideanSpace' 2 | ∃ x ∈ B.toSet,
    EuclideanSpace'.prod_equiv 1 1 p = ((x, (lo x : EuclideanSpace' 1)) : EuclideanSpace' 1 × EuclideanSpace' 1)}
  have h_UG_hi : JordanMeasurable UG_hi := JordanMeasurable.undergraph hB hhi_cont
  have h_UG_lo : JordanMeasurable UG_lo := JordanMeasurable.undergraph hB hlo_cont
  have h_G_lo : JordanMeasurable G_lo := JordanMeasurable.graph hB hlo_cont
  have h_sub1 : ∀ p, (∃ x ∈ B.toSet, ∃ t : ℝ, EuclideanSpace'.prod_equiv 1 1 p = ((x, (t : EuclideanSpace' 1)) : EuclideanSpace' 1 × EuclideanSpace' 1) ∧ lo x ≤ t ∧ t ≤ hi x) →
      p ∈ ((UG_hi \ UG_lo) ∪ G_lo) := by
    intro p; rintro ⟨x, hx, t, hxyt, h_lo, h_hi⟩
    by_cases h : t = lo x
    · refine Or.inr ⟨x, hx, ?_⟩; simpa [h] using hxyt
    · have h_nonneg_t : 0 ≤ t := by
        have : 0 ≤ lo x := hlo_nonneg x hx; nlinarith
      refine Or.inl ⟨⟨x, hx, t, hxyt, h_nonneg_t, h_hi⟩, ?_⟩
      intro hp; rcases hp with ⟨x', hx', t', hxyt', ht0', ht'_lo⟩
      have h_pair : ((x, (t : EuclideanSpace' 1)) : EuclideanSpace' 1 × EuclideanSpace' 1) = ((x', (t' : EuclideanSpace' 1)) : EuclideanSpace' 1 × EuclideanSpace' 1) :=
        hxyt.symm.trans (hxyt' : EuclideanSpace'.prod_equiv 1 1 p = ((x', (t' : EuclideanSpace' 1)) : EuclideanSpace' 1 × EuclideanSpace' 1))
      have hx_eq : x' = x := congr_arg Prod.fst h_pair.symm
      have ht_val_eq : (t' : EuclideanSpace' 1) = (t : EuclideanSpace' 1) := congr_arg Prod.snd h_pair.symm
      have ht_eq : t' = t := Real.equiv_EuclideanSpace'.injective ht_val_eq
      rw [hx_eq, ht_eq] at ht'_lo
      have : t = lo x := le_antisymm ht'_lo h_lo
      exact h this
  have h_sub2 : ∀ p, p ∈ ((UG_hi \ UG_lo) ∪ G_lo) →
      (∃ x ∈ B.toSet, ∃ t : ℝ, EuclideanSpace'.prod_equiv 1 1 p = ((x, (t : EuclideanSpace' 1)) : EuclideanSpace' 1 × EuclideanSpace' 1) ∧ lo x ≤ t ∧ t ≤ hi x) := by
    intro p; rintro (⟨⟨x, hx, t, hxyt, ht0, ht_hi⟩, hp_not_lo⟩ | ⟨x, hx, hxyt⟩)
    · have h_lo_t : lo x ≤ t := by
        by_contra! h; exact hp_not_lo ⟨x, hx, t, hxyt, ht0, h.le⟩
      exact ⟨x, hx, t, hxyt, h_lo_t, ht_hi⟩
    · exact ⟨x, hx, lo x, hxyt, le_refl (lo x), hlo_le_hi x hx⟩
  have h_eq : {p | ∃ x ∈ B.toSet, ∃ t : ℝ, EuclideanSpace'.prod_equiv 1 1 p = ((x, (t : EuclideanSpace' 1)) : EuclideanSpace' 1 × EuclideanSpace' 1) ∧ lo x ≤ t ∧ t ≤ hi x}
      = (UG_hi \ UG_lo) ∪ G_lo := by
    ext p; constructor; exact h_sub1 p; exact h_sub2 p
  rw [h_eq]
  exact ((h_UG_hi.sdiff h_UG_lo).union h_G_lo)

/-! ### Auxiliary lemmas for Exercise 1.1.8 -/

/-- A singleton in the plane has Jordan outer measure zero, via a degenerate box
whose second side has length 0. -/
lemma singleton_outer_measure_zero (x : EuclideanSpace' 2) :
    Jordan_outer_measure ({x} : Set (EuclideanSpace' 2)) = 0 := by
  refine le_antisymm ?_ (Jordan_outer_measure_nonneg _)
  let B : Box 2 := {
    side := λ i => match i with
    | ⟨0, h⟩ => BoundedInterval.Icc (x 0 - 1) (x 0 + 1)
    | ⟨1, h⟩ => BoundedInterval.Icc (x 1) (x 1)
  }
  have h_sub : ({x} : Set (EuclideanSpace' 2)) ⊆ B.toSet := by
    intro y hy
    simp at hy; subst y
    simp [B, Box.mem_toSet]
  have hbdd : Bornology.IsBounded B.toSet := (IsElementary.box B).isBounded
  have hvol : Jordan_outer_measure B.toSet = 0 := by
    rw [Jordan_outer_measure_of_box, Box.volume]
    simp [B, BoundedInterval.length]
  have hle : Jordan_outer_measure ({x} : Set (EuclideanSpace' 2)) ≤ 0 :=
    le_trans (Jordan_outer_measure_mono_of_subset h_sub hbdd) (by rw [hvol])
  exact hle

/-- A vertical line segment (a₀ = b₀) in R² has Jordan outer measure zero.
For any ε > 0, the segment is contained in a box \[a₀-δ, a₀+δ\] × \[ymin, ymax\]
whose volume 2δ·(ymax-ymin) < ε when δ is chosen small enough. -/
lemma vertical_segment_outer_measure_zero (a b : EuclideanSpace' 2) (h : a 0 = b 0) :
    Jordan_outer_measure (segment ℝ a b) = 0 := by
  refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) (Jordan_outer_measure_nonneg _)
  let ymin := min (a 1) (b 1)
  let ymax := max (a 1) (b 1)
  have hy_diff_nonneg : 0 ≤ ymax - ymin := by
    have : ymin ≤ ymax := le_trans (min_le_left _ _) (le_max_left _ _)
    linarith
  let δ := ε / (2 * (ymax - ymin + 1))
  have hδ_pos : 0 < δ := div_pos hε (by nlinarith)
  let B1 : Box 1 := BoundedInterval.Icc (a 0 - δ) (a 0 + δ)
  let B2 : Box 1 := BoundedInterval.Icc ymin ymax
  let B : Box 2 := {
    side := λ i => match i with
    | ⟨0, h⟩ => BoundedInterval.Icc (a 0 - δ) (a 0 + δ)
    | ⟨1, h⟩ => BoundedInterval.Icc ymin ymax
  }
  have h_seg_sub : segment ℝ a b ⊆ B.toSet := by
    rintro x ⟨s, t, hs, ht, hst, hx⟩
    have hx0 : x 0 = a 0 := by
      calc x 0 = (s • a + t • b) 0 := by rw [hx]
        _ = s * a 0 + t * b 0 := by simp
        _ = s * a 0 + t * a 0 := by rw [h]
        _ = (s + t) * a 0 := by ring
        _ = a 0 := by simp [hst]
    have hx0_low : a 0 - δ ≤ x 0 := by rw [hx0]; nlinarith
    have hx0_high : x 0 ≤ a 0 + δ := by rw [hx0]; nlinarith
    have hx1_val : x 1 = s * a 1 + t * b 1 := by
      calc x 1 = (s • a + t • b) 1 := by rw [hx]
        _ = s * a 1 + t * b 1 := by simp
    have hx1_low : ymin ≤ x 1 := by
      rw [hx1_val]
      rcases le_total (a 1) (b 1) with (horder | horder)
      · rw [show ymin = a 1 from by dsimp [ymin]; simp [horder]]
        calc a 1 = (s + t) * a 1 := by simp [hst]
          _ = s * a 1 + t * a 1 := by ring
          _ = t * a 1 + s * a 1 := by ring
          _ ≤ t * b 1 + s * a 1 := add_le_add_left (mul_le_mul_of_nonneg_left horder ht) (s * a 1)
          _ = s * a 1 + t * b 1 := by ring
      · rw [show ymin = b 1 from by dsimp [ymin]; simp [horder]]
        calc b 1 = (s + t) * b 1 := by simp [hst]
          _ = s * b 1 + t * b 1 := by ring
          _ ≤ s * a 1 + t * b 1 := by nlinarith
    have hx1_high : x 1 ≤ ymax := by
      rw [hx1_val]
      rcases le_total (a 1) (b 1) with (horder | horder)
      · rw [show ymax = b 1 from by dsimp [ymax]; simp [horder]]
        have hAB : s * a 1 + t * b 1 ≤ s * b 1 + t * b 1 := by
          have htemp : s * a 1 ≤ s * b 1 := mul_le_mul_of_nonneg_left horder hs
          nlinarith
        calc
          s * a 1 + t * b 1 ≤ s * b 1 + t * b 1 := hAB
          _ = (s + t) * b 1 := by ring
          _ = b 1 := by simp [hst]
      · rw [show ymax = a 1 from by dsimp [ymax]; simp [horder]]
        have hBA : t * b 1 + s * a 1 ≤ t * a 1 + s * a 1 := by
          nlinarith
        calc
          s * a 1 + t * b 1 = t * b 1 + s * a 1 := by ring
          _ ≤ t * a 1 + s * a 1 := hBA
          _ = s * a 1 + t * a 1 := by ring
          _ = (s + t) * a 1 := by ring
          _ = a 1 := by simp [hst]
    simp [B, Box.mem_toSet, hx0_low, hx0_high, hx1_low, hx1_high]
  have hbdd : Bornology.IsBounded B.toSet := (IsElementary.box B).isBounded
  have hvol : Jordan_outer_measure B.toSet = 2 * δ * (ymax - ymin) := by
    rw [Jordan_outer_measure_of_box, Box.volume]
    have hy_order : ymin ≤ ymax := le_trans (min_le_left _ _) (le_max_left _ _)
    have h_side0 : |B.side 0|ₗ = 2 * δ := by
      dsimp [B, Box.volume_of_interval, BoundedInterval.length]
      have h : (a 0 + δ) - (a 0 - δ) = 2 * δ := by ring
      rw [h]
      exact max_eq_left (by nlinarith)
    have h_side1 : |B.side 1|ₗ = ymax - ymin := by
      dsimp [B, Box.volume_of_interval, BoundedInterval.length]
      rw [max_eq_left (sub_nonneg.mpr hy_order)]
    simp [h_side0, h_side1, Fin.prod_univ_two]
  calc
    Jordan_outer_measure (segment ℝ a b) ≤ Jordan_outer_measure B.toSet :=
      Jordan_outer_measure_mono_of_subset h_seg_sub hbdd
    _ = 2 * δ * (ymax - ymin) := hvol
    _ ≤ ε := by
      have : 2 * δ * (ymax - ymin) < ε := by
        dsimp [δ]
        have hA_nonneg : 0 ≤ ymax - ymin := hy_diff_nonneg
        set A := ymax - ymin with hA_def
        have hApos' : 0 < A + 1 := by nlinarith
        have hineq : 2 * (ε / (2 * (A + 1))) * A < ε := by
          apply (div_lt_one hε).mp
          calc
            (2 * (ε / (2 * (A + 1))) * A) / ε = A / (A + 1) := by
              field_simp [hε.ne']
            _ < 1 := (div_lt_one hApos').mpr (by nlinarith)
        exact hineq
      exact this.le
    _ = 0 + ε := by ring

/-- A non-vertical line segment (a₀ ≠ b₀) in R² has Jordan outer measure zero, because
it is the graph of an affine function over the interval from min(a₀,b₀) to max(a₀,b₀) and
{lit}`graph_outer_measure_zero` applies. -/
lemma nonvertical_segment_outer_measure_zero (a b : EuclideanSpace' 2) (h : a 0 ≠ b 0) :
    Jordan_outer_measure (segment ℝ a b) = 0 := by
  let f : EuclideanSpace' 1 → ℝ := λ x => a 1 + ((EuclideanSpace'.equiv_Real x) - a 0) * (b 1 - a 1) / (b 0 - a 0)
  let B : Box 1 := BoundedInterval.Icc (min (a 0) (b 0)) (max (a 0) (b 0))
  have hB : ∀ i : Fin 1, ∃ a' b' : ℝ, B.side i = BoundedInterval.Icc a' b' := by
    intro i; simp [B]
  have hf_cont : ContinuousOn f B.toSet := by
    refine Continuous.continuousOn ?_
    have h_cont : Continuous EuclideanSpace'.equiv_Real :=
      PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) _
    have h_f_cont : Continuous f := by
      dsimp [f]
      have h_mul : Continuous fun (x : EuclideanSpace' 1) => (EuclideanSpace'.equiv_Real x - a 0) * ((b 1 - a 1) / (b 0 - a 0)) :=
        (h_cont.sub continuous_const).mul continuous_const
      simpa [mul_div_assoc] using continuous_const.add h_mul
    exact h_f_cont
  have h_sub1 : segment ℝ a b ⊆ { p | ∃ x ∈ B.toSet, EuclideanSpace'.prod_equiv 1 1 p = ⟨ x, f x ⟩ } := by
    rintro p ⟨s, t, hs, ht, hst, hp⟩
    let x : EuclideanSpace' 1 := Real.equiv_EuclideanSpace' (s * a 0 + t * b 0)
    have hx_range : min (a 0) (b 0) ≤ s * a 0 + t * b 0 ∧ s * a 0 + t * b 0 ≤ max (a 0) (b 0) := by
      rcases le_total (a 0) (b 0) with (horder | horder)
      · have hmin : min (a 0) (b 0) = a 0 := min_eq_left horder
        have hmax : max (a 0) (b 0) = b 0 := max_eq_right horder
        rw [hmin, hmax]
        have h_temp1 : t * a 0 ≤ t * b 0 := mul_le_mul_of_nonneg_left horder ht
        have h_temp2 : s * a 0 ≤ s * b 0 := mul_le_mul_of_nonneg_left horder hs
        have h1 : a 0 ≤ s * a 0 + t * b 0 := by
          calc a 0 = (s + t) * a 0 := by simp [hst]
            _ = s * a 0 + t * a 0 := by ring
            _ ≤ s * a 0 + t * b 0 := by nlinarith
        have h2 : s * a 0 + t * b 0 ≤ b 0 := by
          calc s * a 0 + t * b 0 ≤ s * b 0 + t * b 0 := by nlinarith
            _ = (s + t) * b 0 := by ring
            _ = b 0 := by simp [hst]
        exact ⟨h1, h2⟩
      · have hmin : min (a 0) (b 0) = b 0 := min_eq_right horder
        have hmax : max (a 0) (b 0) = a 0 := max_eq_left horder
        rw [hmin, hmax]
        have h_temp1 : s * b 0 ≤ s * a 0 := mul_le_mul_of_nonneg_left horder hs
        have h_temp2 : t * b 0 ≤ t * a 0 := mul_le_mul_of_nonneg_left horder ht
        have h1 : b 0 ≤ s * a 0 + t * b 0 := by
          calc b 0 = (s + t) * b 0 := by simp [hst]
            _ = s * b 0 + t * b 0 := by ring
            _ ≤ s * a 0 + t * b 0 := by nlinarith
        have h2 : s * a 0 + t * b 0 ≤ a 0 := by
          calc s * a 0 + t * b 0 ≤ s * a 0 + t * a 0 := by nlinarith
            _ = (s + t) * a 0 := by ring
            _ = a 0 := by simp [hst]
        exact ⟨h1, h2⟩
    have hx_mem : x ∈ B.toSet := by
      rw [Box.mem_toSet]
      intro i; fin_cases i
      simp [B, x, hx_range.1, hx_range.2]
    refine ⟨x, hx_mem, ?_⟩
    -- show EuclideanSpace'.prod_equiv 1 1 p = ⟨x, f x⟩
    ext i : 2
    · -- first coordinate
      calc (EuclideanSpace'.prod_equiv 1 1 p).1 i = p 0 := by simp [EuclideanSpace'.prod_equiv]
        _ = (s • a + t • b) 0 := by rw [hp]
        _ = s * a 0 + t * b 0 := by simp
        _ = x i := by simp [x]
    · -- second coordinate
      have h_den_ne_zero : b 0 - a 0 ≠ 0 := by
        intro hzero
        apply h
        nlinarith
      have : f x = s * a 1 + t * b 1 := by
        dsimp [f, x]
        have h_eq : ((s * a 0 + t * b 0) : ℝ) - a 0 = t * (b 0 - a 0) := by
          calc
            ((s * a 0 + t * b 0) : ℝ) - a 0 = (s - 1) * a 0 + t * b 0 := by ring
            _ = (-t) * a 0 + t * b 0 := by rw [show s - 1 = -t from by linarith]
            _ = t * (b 0 - a 0) := by ring
        calc
          a 1 + (((s * a 0 + t * b 0) : ℝ) - a 0) * (b 1 - a 1) / (b 0 - a 0)
              = a 1 + (t * (b 0 - a 0)) * (b 1 - a 1) / (b 0 - a 0) := by rw [h_eq]
          _ = a 1 + t * (b 1 - a 1) := by
            field_simp [h_den_ne_zero]
          _ = s * a 1 + t * b 1 := by
            have hs' : s = 1 - t := by linarith
            rw [hs']
            ring
      calc (EuclideanSpace'.prod_equiv 1 1 p).2 i = p 1 := by simp [EuclideanSpace'.prod_equiv]
        _ = (s • a + t • b) 1 := by rw [hp]
        _ = s * a 1 + t * b 1 := by simp
        _ = f x := by rw [this]
        _ = (⟨x, f x⟩ : EuclideanSpace' 1 × EuclideanSpace' 1).2 i := by simp
  have h_bounded : Bornology.IsBounded { p | ∃ x ∈ B.toSet, EuclideanSpace'.prod_equiv 1 1 p = ⟨ x, f x ⟩ } :=
    graph_isBounded hB hf_cont
  have h_graph_zero : Jordan_outer_measure { p | ∃ x ∈ B.toSet, EuclideanSpace'.prod_equiv 1 1 p = ⟨ x, f x ⟩ } = 0 :=
    graph_outer_measure_zero hB hf_cont
  have h_le : Jordan_outer_measure (segment ℝ a b) ≤ 0 :=
    le_trans (Jordan_outer_measure_mono_of_subset h_sub1 h_bounded) (by rw [h_graph_zero])
  exact le_antisymm h_le (Jordan_outer_measure_nonneg _)

/-- A line segment in ℝ² has Jordan outer measure zero. -/
lemma segment_outer_measure_zero (a b : EuclideanSpace' 2) :
    Jordan_outer_measure (segment ℝ a b) = 0 := by
  by_cases h_eq : a = b
  · subst b
    have h_singleton : segment ℝ a a = {a} := by
      ext x; constructor
      · rintro ⟨s, t, hs, ht, hst, hx⟩
        have hx_eq : x = a := by
          calc x = s • a + t • a := hx.symm
            _ = (s + t) • a := by rw [add_smul]
            _ = 1 • a := by simp [hst]
            _ = a := by simp
        simp [hx_eq]
      · intro hx; simp at hx; subst x
        refine ⟨1, 0, by norm_num, by norm_num, by norm_num, ?_⟩
        simp [one_smul, zero_smul]
    rw [h_singleton]
    exact singleton_outer_measure_zero a
  · by_cases h_vert : a 0 = b 0
    · exact vertical_segment_outer_measure_zero a b h_vert
    · exact nonvertical_segment_outer_measure_zero a b h_vert

/-- A helper lemma: a bounded interval in ℝ is preconnected. -/
lemma isPreconnected_boundedInterval (I : BoundedInterval) : IsPreconnected (I : Set ℝ) := by
  rcases I with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
  · by_cases h : a < b
    · simpa using (isConnected_Ioo h).isPreconnected
    · have h_empty : (Set.Ioo a b : Set ℝ) = (∅ : Set ℝ) := Set.Ioo_eq_empty (by linarith)
      simpa [h_empty] using isPreconnected_empty
  · by_cases h : a ≤ b
    · simpa using (isConnected_Icc h).isPreconnected
    · have h_empty : (Set.Icc a b : Set ℝ) = (∅ : Set ℝ) := Set.Icc_eq_empty (by linarith)
      simpa [h_empty] using isPreconnected_empty
  · by_cases h : a < b
    · simpa using (isConnected_Ioc h).isPreconnected
    · have h_empty : (Set.Ioc a b : Set ℝ) = (∅ : Set ℝ) := Set.Ioc_eq_empty (by linarith)
      simpa [h_empty] using isPreconnected_empty
  · by_cases h : a < b
    · simpa using (isConnected_Ico h).isPreconnected
    · have h_empty : (Set.Ico a b : Set ℝ) = (∅ : Set ℝ) := Set.Ico_eq_empty (by linarith)
      simpa [h_empty] using isPreconnected_empty

/-- A helper lemma: a box is preconnected in Euclidean space. -/
lemma isPreconnected_box (d : ℕ) (B : Box d) : IsPreconnected (B.toSet : Set (EuclideanSpace' d)) := by
  let e : EuclideanSpace ℝ (Fin d) ≃L[ℝ] (Fin d → ℝ) := EuclideanSpace.equiv (Fin d) ℝ
  have he_preimg : B.toSet = e.symm '' (Set.pi Set.univ (fun i : Fin d => (B.side i : Set ℝ))) := by
    ext x
    constructor
    · intro hx
      have hx' := (Box.mem_toSet.mp hx)
      have hx_coord (i : Fin d) : (e x) i ∈ (B.side i : Set ℝ) := by
        simpa [e] using hx' i
      refine ⟨e x, ?_, ?_⟩
      · simp [Set.mem_pi, hx_coord]
      · simp [e]
    · rintro ⟨y, hy, rfl⟩
      have hx_coord' (i : Fin d) : (e.symm y).ofLp i ∈ (B.side i : Set ℝ) := by
        have hy_i : y i ∈ (B.side i : Set ℝ) := hy i (Set.mem_univ i)
        simp [e, hy_i]
      simpa [Box.mem_toSet] using hx_coord'
  rw [he_preimg]
  have h_preconn : IsPreconnected (Set.pi Set.univ (fun i : Fin d => (B.side i : Set ℝ))) :=
    isPreconnected_univ_pi (fun i => isPreconnected_boundedInterval (B.side i))
  have h_cont : ContinuousOn (e.symm : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d))
    (Set.pi Set.univ (fun i : Fin d => (B.side i : Set ℝ))) :=
    (e.symm).continuous.continuousOn
  exact h_preconn.image (e.symm : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)) h_cont

/-- If a bounded set has Jordan null frontier, then it is Jordan measurable. -/
lemma JordanMeasurable.if_frontier_null {d:ℕ} {E : Set (EuclideanSpace' d)}
    (hBounded : Bornology.IsBounded E)
    (hfrontier : Jordan_outer_measure (frontier E) = 0) : JordanMeasurable E := by
  classical
  have h_inner_le_outer : Jordan_inner_measure E ≤ Jordan_outer_measure E :=
    Jordan_inner_le_outer hBounded
  have h_outer_le_inner : Jordan_outer_measure E ≤ Jordan_inner_measure E := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hε2 : ε/2 > 0 := by linarith
    have h_lt : Jordan_outer_measure (frontier E) < ε/2 := by
      rw [hfrontier]; linarith
    have h_bounded_frontier : Bornology.IsBounded (frontier E) :=
      hBounded.closure.subset frontier_subset_closure
    obtain ⟨C, hC, hC_frontier, hC_measure⟩ := le_Jordan_outer h_lt h_bounded_frontier
    have h_bounded_cl : Bornology.IsBounded (closure E) := hBounded.closure
    obtain ⟨B, hB, hB_closure⟩ := IsElementary.contains_bounded h_bounded_cl
    let C' := C ∩ B
    have hC'_elem : IsElementary C' := hC.inter hB
    have hC'_frontier : frontier E ⊆ C' := by
      intro x hx
      have hx_cl : x ∈ closure E :=
        Set.mem_of_subset_of_mem (frontier_subset_closure) hx
      exact ⟨hC_frontier hx, hB_closure hx_cl⟩
    have hC'_measure_lt : hC'_elem.measure < ε/2 := by
      have hC'_sub_C : C' ⊆ C :=
        show C ∩ B ⊆ C from Set.inter_subset_left (s := C) (t := B)
      have hC'_measure_le : hC'_elem.measure ≤ hC.measure :=
        IsElementary.measure_mono hC'_elem hC hC'_sub_C
      linarith
    have hB_sdiff_C'_elem : IsElementary (B \ C') := hB.sdiff hC'_elem
    obtain ⟨T_boxes, hT_disj, hT_eq⟩ := hB_sdiff_C'_elem.partition
    have hT_eq' : (B \ C' : Set (EuclideanSpace' d)) = ⋃ J ∈ T_boxes, (J : Set (EuclideanSpace' d)) := hT_eq
    let A_sets : Finset (Set (EuclideanSpace' d)) :=
      (T_boxes.image fun (J : Box d) => (J : Set (EuclideanSpace' d))).filter fun S =>
        S ⊆ interior E
    let A := ⋃ S ∈ A_sets, S
    have hA_elem : IsElementary A := by
      refine IsElementary.union' (fun S hS => ?_)
      rcases Finset.mem_filter.mp hS with ⟨hS_img, hS_int⟩
      rcases Finset.mem_image.mp hS_img with ⟨J, hJ, rfl⟩
      exact IsElementary.box J
    have hA_sub_int : A ⊆ interior E := by
      intro x hx
      rcases Set.mem_iUnion₂.mp hx with ⟨S, hS, hxS⟩
      have hS_int : S ⊆ interior E := (Finset.mem_filter.mp hS).2
      exact hS_int hxS
    have hA_sub_E : A ⊆ E := Set.Subset.trans hA_sub_int interior_subset
    have hE_sub_AC' : E ⊆ A ∪ C' := by
      intro x hx
      have hx_cl : x ∈ closure E := subset_closure hx
      have hx_B : x ∈ B := hB_closure hx_cl
      by_cases hx_C' : x ∈ C'
      · exact Or.inr hx_C'
      · have hx_sdiff : x ∈ B \ C' := ⟨hx_B, hx_C'⟩
        rw [hT_eq'] at hx_sdiff
        simp at hx_sdiff
        rcases hx_sdiff with ⟨J_box, hJ_box, hxJ⟩
        have hJ_preconn : IsPreconnected ((J_box : Set (EuclideanSpace' d))) :=
          isPreconnected_box d J_box
        have hy_not_frontier (y : EuclideanSpace' d) (hyJ : y ∈ (J_box : Set (EuclideanSpace' d))) : y ∉ frontier E := by
          intro hy_front
          have hy_C' : y ∈ C' := hC'_frontier hy_front
          have hy_sdiff' : y ∈ B \ C' := by
            have hy_union : y ∈ ⋃ J' ∈ T_boxes, (J' : Set (EuclideanSpace' d)) := by
              simpa using ⟨J_box, hJ_box, hyJ⟩
            rw [← hT_eq'] at hy_union
            exact hy_union
          exact hy_sdiff'.2 hy_C'
        have hJ_sub_union : (J_box : Set (EuclideanSpace' d)) ⊆ interior E ∪ (closure E)ᶜ := by
          intro y hy
          by_cases hy_cl : y ∈ closure E
          · by_cases hy_int : y ∈ interior E
            · exact Or.inl hy_int
            · exfalso
              have hy_front : y ∈ frontier E := by
                rw [frontier, Set.diff_eq]
                exact ⟨hy_cl, hy_int⟩
              exact hy_not_frontier y hy hy_front
          · exact Or.inr hy_cl
        have h_int_open : IsOpen (interior E : Set (EuclideanSpace' d)) := isOpen_interior
        have h_ext_open : IsOpen ((closure E)ᶜ : Set (EuclideanSpace' d)) :=
          isOpen_compl_iff.mpr isClosed_closure
        have h_disjoint_int_ext : Disjoint (interior E) ((closure E)ᶜ : Set (EuclideanSpace' d)) := by
          refine Set.disjoint_left.mpr fun y hy_int hy_ext => ?_
          exact hy_ext (subset_closure (interior_subset hy_int))
        rcases hJ_preconn.subset_or_subset h_int_open h_ext_open h_disjoint_int_ext hJ_sub_union with
          (hJ_int' | hJ_ext')
        · have hJ_set : (J_box : Set (EuclideanSpace' d)) ∈ T_boxes.image (fun J' : Box d => (J' : Set (EuclideanSpace' d))) := by
            apply Finset.mem_image.mpr
            exact ⟨J_box, hJ_box, rfl⟩
          have hJ_A_sets : (J_box : Set (EuclideanSpace' d)) ∈ A_sets :=
            Finset.mem_filter.mpr ⟨hJ_set, hJ_int'⟩
          exact Or.inl (Set.mem_iUnion₂.mpr ⟨(J_box : Set (EuclideanSpace' d)), hJ_A_sets, hxJ⟩)
        · exfalso
          exact hJ_ext' hxJ hx_cl
    let C'' := C' \ A
    have hC''_elem : IsElementary C'' := hC'_elem.sdiff hA_elem
    have hC''_frontier : frontier E ⊆ C'' := by
      intro x hx
      have hx_C' : x ∈ C' := hC'_frontier hx
      have hx_not_A : x ∉ A := by
        intro hxA
        have hx_int : x ∈ interior E := hA_sub_int hxA
        have hx_not_int : x ∉ interior E := by
          rw [frontier, Set.mem_diff] at hx
          exact hx.2
        exact hx_not_int hx_int
      exact ⟨hx_C', hx_not_A⟩
    have hC''_measure_lt : hC''_elem.measure < ε/2 := by
      have hC''_sub_C' : C'' ⊆ C' :=
        show C' \ A ⊆ C' from fun x hx => hx.1
      have hC''_measure_le : hC''_elem.measure ≤ hC'_elem.measure :=
        IsElementary.measure_mono hC''_elem hC'_elem hC''_sub_C'
      linarith
    have h_disjoint_AC'' : Disjoint A C'' := by
      refine Set.disjoint_left.mpr fun x hxA hxC'' => ?_
      exact hxC''.2 hxA
    have hE_sub_AC'' : E ⊆ A ∪ C'' := by
      intro x hx
      rcases hE_sub_AC' hx with (hxA | hxC')
      · exact Or.inl hxA
      · by_cases hxA' : x ∈ A
        · exact Or.inl hxA'
        · exact Or.inr ⟨hxC', hxA'⟩
    have h_outer_bound : Jordan_outer_measure E ≤ (hA_elem.union hC''_elem).measure := by
      have h_sub : Jordan_outer_measure E ≤ Jordan_outer_measure (A ∪ C'') :=
        Jordan_outer_measure_mono_of_subset hE_sub_AC'' ((hA_elem.union hC''_elem).isBounded)
      have h_outer_AC : Jordan_outer_measure (A ∪ C'') ≤ (hA_elem.union hC''_elem).measure :=
        Jordan_outer_le (hA_elem.union hC''_elem) (Set.Subset.refl _)
      exact le_trans h_sub h_outer_AC
    have h_measure_eq : (hA_elem.union hC''_elem).measure = hA_elem.measure + hC''_elem.measure :=
      IsElementary.measure_of_disjUnion hA_elem hC''_elem h_disjoint_AC''
    have hA_measure_le_inner : hA_elem.measure ≤ Jordan_inner_measure E := by
      have h_nonempty : { m : ℝ | ∃ (X : Set (EuclideanSpace' d)) (hX : IsElementary X), X ⊆ E ∧ m = hX.measure }.Nonempty :=
        ⟨0, ∅, IsElementary.empty d, Set.empty_subset _, Eq.symm (IsElementary.measure_of_empty d)⟩
      have h_bdd : BddAbove { m : ℝ | ∃ (X : Set (EuclideanSpace' d)) (hX : IsElementary X), X ⊆ E ∧ m = hX.measure } := by
        obtain ⟨U, hU, hEU⟩ := IsElementary.contains_bounded hBounded
        refine ⟨hU.measure, ?_⟩
        rintro m' ⟨X, hX, hXE, rfl⟩
        exact IsElementary.measure_mono hX hU (hXE.trans hEU)
      apply le_csSup h_bdd
      exact ⟨A, hA_elem, hA_sub_E, rfl⟩
    have h_goal : Jordan_outer_measure E ≤ Jordan_inner_measure E + ε := by
      calc
        Jordan_outer_measure E ≤ (hA_elem.union hC''_elem).measure := h_outer_bound
        _ = hA_elem.measure + hC''_elem.measure := h_measure_eq
        _ ≤ Jordan_inner_measure E + hC''_elem.measure := by nlinarith
        _ ≤ Jordan_inner_measure E + ε/2 := by
          have : hC''_elem.measure < ε/2 := hC''_measure_lt
          linarith
        _ ≤ Jordan_inner_measure E + ε := by nlinarith
    exact h_goal
  have h_eq : Jordan_inner_measure E = Jordan_outer_measure E :=
    le_antisymm h_inner_le_outer h_outer_le_inner
  exact ⟨hBounded, h_eq⟩

/-- The boundary of a triangle is a union of three line segments, hence has Jordan outer
measure zero. -/
lemma triangle_frontier_outer_measure_zero (T : Affine.Triangle ℝ (EuclideanSpace' 2)) :
    Jordan_outer_measure (frontier T.closedInterior) = 0 := by
  have h_bounded : Bornology.IsBounded T.closedInterior := by
    have h_eq : T.closedInterior = convexHull ℝ (Set.range T.points) := by
      symm; exact Affine.Simplex.convexHull_eq_closedInterior T
    rw [h_eq]
    rw [isBounded_convexHull]
    exact (Set.finite_range T.points).isBounded
  -- The frontier of a triangle is the union of its three edges.
  -- Each edge is a segment, whose outer measure is 0 by segment_outer_measure_zero.
  -- By finite subadditivity (Jordan_outer_subadd), the union has outer measure 0.
  have h_span_top : affineSpan ℝ (Set.range T.points) = ⊤ := by
    have h_card : Fintype.card (Fin 3) = Module.finrank ℝ (EuclideanSpace' 2) + 1 := by
      have h_finrank : Module.finrank ℝ (EuclideanSpace' 2) = 2 := by
        simpa using finrank_euclideanSpace (𝕜 := ℝ) (ι := Fin 2)
      have h_card3 : Fintype.card (Fin 3) = 3 := by decide
      calc
        Fintype.card (Fin 3) = 3 := h_card3
        _ = 2 + 1 := by norm_num
        _ = Module.finrank ℝ (EuclideanSpace' 2) + 1 := by rw [h_finrank]
    exact ((T.independent).affineSpan_eq_top_iff_card_eq_finrank_add_one).mpr h_card

  let b : AffineBasis (Fin 3) ℝ (EuclideanSpace' 2) :=
    ⟨T.points, T.independent, h_span_top⟩

  have h_interior_sub : T.interior ⊆ interior T.closedInterior := by
    have h_interior_convexHull : interior (convexHull ℝ (Set.range T.points)) = {x | ∀ i, 0 < b.coord i x} := by
      have h_range : Set.range (b : Fin 3 → EuclideanSpace' 2) = Set.range T.points := rfl
      rw [← h_range]
      exact AffineBasis.interior_convexHull b
    have h_interior_closedInterior : interior T.closedInterior = {x | ∀ i, 0 < b.coord i x} := by
      have h_eq : T.closedInterior = convexHull ℝ (Set.range T.points) := by
        symm; exact Affine.Simplex.convexHull_eq_closedInterior T
      rw [h_eq, h_interior_convexHull]
    rw [h_interior_closedInterior]
    intro x hx_int
    rcases hx_int with ⟨w, hw_sum, hw01, hx_eq⟩
    intro i
    have hw_pos : 0 < w i := (hw01 i).1
    have h_coord_eq : b.coord i x = w i := by
      calc
        b.coord i x = b.coord i (Finset.univ.affineCombination ℝ T.points w) := by rw [hx_eq]
        _ = w i := b.coord_apply_combination_of_mem (Finset.mem_univ i) hw_sum
    rw [h_coord_eq]
    exact hw_pos

  have h_frontier_sub : frontier T.closedInterior ⊆
      ((segment ℝ (T.points 0) (T.points 1)) ∪
       (segment ℝ (T.points 1) (T.points 2)) ∪
       (segment ℝ (T.points 2) (T.points 0))) := by
    intro x hx
    have hx_cl : x ∈ closure T.closedInterior := hx.1
    have hx_not_int : x ∉ interior T.closedInterior := hx.2
    have h_compact : IsCompact T.closedInterior := by
      have h_finite : Set.Finite (Set.range T.points) := Set.finite_range T.points
      have h_eq : T.closedInterior = convexHull ℝ (Set.range T.points) := by
        symm; exact Affine.Simplex.convexHull_eq_closedInterior T
      rw [h_eq]
      exact h_finite.isCompact_convexHull (𝕜 := ℝ)
    have h_closed : IsClosed T.closedInterior := h_compact.isClosed
    have hx_clInt : x ∈ T.closedInterior := by
      rw [h_closed.closure_eq] at hx_cl
      exact hx_cl
    rcases hx_clInt with ⟨w, hw_sum, hw01, hx_eq⟩
    have h_not_all_open : ¬ ∀ i : Fin 3, w i ∈ Set.Ioo (0 : ℝ) 1 := by
      intro h_all_open
      apply hx_not_int
      have h_mem : Finset.univ.affineCombination ℝ T.points w ∈ T.interior := by
        rw [Affine.Simplex.affineCombination_mem_interior_iff hw_sum]
        exact h_all_open
      have hx_int : x ∈ T.interior := by
        rw [← hx_eq]
        exact h_mem
      exact h_interior_sub hx_int
    rcases not_forall.mp h_not_all_open with ⟨i, hi⟩
    -- hi : ¬(w i ∈ Set.Ioo (0 : ℝ) 1)
    have hi_not_open : w i ∉ Set.Ioo (0 : ℝ) 1 := hi
    have hi_cc : w i ∈ Set.Icc (0 : ℝ) 1 := hw01 i
    rcases hi_cc with ⟨hi_lo, hi_hi⟩
    have hi_zero_or_one : w i = 0 ∨ w i = 1 := by
      by_cases hpos : 0 < w i
      · by_cases hlt1 : w i < 1
        · exfalso; exact hi_not_open ⟨hpos, hlt1⟩
        · have : w i = 1 := by linarith
          right; exact this
      · have : w i = 0 := by linarith
        left; exact this
    have h_affine_eq_sum : Finset.univ.affineCombination ℝ T.points w = ∑ i : Fin 3, w i • T.points i := by
      rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
        (s := Finset.univ) w T.points hw_sum 0]
      simp [Finset.weightedVSubOfPoint_apply, vsub_eq_sub]
    have hx_eq_sum : x = ∑ i : Fin 3, w i • T.points i := by
      calc
        x = Finset.univ.affineCombination ℝ T.points w := Eq.symm hx_eq
        _ = ∑ i : Fin 3, w i • T.points i := h_affine_eq_sum
    have h_univ_fin3 : (Finset.univ : Finset (Fin 3)) = {0,1,2} := by decide
    have h_in_union : x ∈ ((segment ℝ (T.points 0) (T.points 1)) ∪
      (segment ℝ (T.points 1) (T.points 2)) ∪
      (segment ℝ (T.points 2) (T.points 0))) := by
      rcases hi_zero_or_one with (hi0 | hi1)
      · -- w i = 0
        match i with
        | 0 =>
          have hsum12 : w 1 + w 2 = 1 := by
            have htemp : (Finset.univ : Finset (Fin 3)).sum w = 1 := hw_sum
            rw [h_univ_fin3] at htemp
            simp [hi0] at htemp
            exact htemp
          have hx_in_seg : x ∈ segment ℝ (T.points 1) (T.points 2) := by
            rw [segment, Set.mem_setOf_eq]
            refine ⟨w 1, w 2, (hw01 1).1, (hw01 2).1, hsum12, ?_⟩
            calc
              w 1 • (T.points 1) + w 2 • (T.points 2) =
                w 0 • (T.points 0) + w 1 • (T.points 1) + w 2 • (T.points 2) := by
                simp [hi0]
              _ = ∑ i : Fin 3, w i • T.points i := by
                rw [h_univ_fin3]; simp [add_assoc]
              _ = x := Eq.symm hx_eq_sum
          exact Or.inl (Or.inr hx_in_seg)
        | 1 =>
          have hsum02 : w 0 + w 2 = 1 := by
            have htemp : (Finset.univ : Finset (Fin 3)).sum w = 1 := hw_sum
            rw [h_univ_fin3] at htemp
            simp [hi0] at htemp
            exact htemp
          have hx_in_seg : x ∈ segment ℝ (T.points 2) (T.points 0) := by
            rw [segment, Set.mem_setOf_eq]
            refine ⟨w 2, w 0, (hw01 2).1, (hw01 0).1, ?_, ?_⟩
            · rw [add_comm]; exact hsum02
            · calc
                w 2 • (T.points 2) + w 0 • (T.points 0) =
                  w 0 • (T.points 0) + w 1 • (T.points 1) + w 2 • (T.points 2) := by
                  simp [hi0, add_comm, add_left_comm, add_assoc]
                _ = ∑ i : Fin 3, w i • T.points i := by
                  rw [h_univ_fin3]; simp [add_assoc]
                _ = x := Eq.symm hx_eq_sum
          exact Or.inr hx_in_seg
        | 2 =>
          have hsum01 : w 0 + w 1 = 1 := by
            have htemp : (Finset.univ : Finset (Fin 3)).sum w = 1 := hw_sum
            rw [h_univ_fin3] at htemp
            simp [hi0] at htemp
            exact htemp
          have hx_in_seg : x ∈ segment ℝ (T.points 0) (T.points 1) := by
            rw [segment, Set.mem_setOf_eq]
            refine ⟨w 0, w 1, (hw01 0).1, (hw01 1).1, hsum01, ?_⟩
            calc
              w 0 • (T.points 0) + w 1 • (T.points 1) =
                w 0 • (T.points 0) + w 1 • (T.points 1) + w 2 • (T.points 2) := by
                simp [hi0]
              _ = ∑ i : Fin 3, w i • T.points i := by
                rw [h_univ_fin3]; simp [add_assoc]
              _ = x := Eq.symm hx_eq_sum
          exact Or.inl (Or.inl hx_in_seg)
      · -- w i = 1
        match i with
        | 0 =>
          have hw1_eq_0 : w 1 = 0 := by
            have htemp : (Finset.univ : Finset (Fin 3)).sum w = 1 := hw_sum
            rw [h_univ_fin3] at htemp
            simp [hi1] at htemp
            have h_nonneg1 : 0 ≤ w 1 := (hw01 1).1
            have h_nonneg2 : 0 ≤ w 2 := (hw01 2).1
            nlinarith
          have hw2_eq_0 : w 2 = 0 := by
            have htemp : (Finset.univ : Finset (Fin 3)).sum w = 1 := hw_sum
            rw [h_univ_fin3] at htemp
            simp [hi1] at htemp
            have h_nonneg1 : 0 ≤ w 1 := (hw01 1).1
            have h_nonneg2 : 0 ≤ w 2 := (hw01 2).1
            nlinarith
          have hx_eq_point : x = T.points 0 := by
            calc
              x = ∑ j : Fin 3, w j • T.points j := hx_eq_sum
              _ = w 0 • (T.points 0) + w 1 • (T.points 1) + w 2 • (T.points 2) := by
                rw [h_univ_fin3]; simp [add_assoc]
              _ = 1 • (T.points 0) + 0 • (T.points 1) + 0 • (T.points 2) := by simp [hi1, hw1_eq_0, hw2_eq_0]
              _ = T.points 0 := by simp
          have hx_in_seg : x ∈ segment ℝ (T.points 0) (T.points 1) := by
            rw [hx_eq_point, segment, Set.mem_setOf_eq]
            exact ⟨1, 0, by norm_num, by norm_num, by norm_num, by simp⟩
          exact Or.inl (Or.inl hx_in_seg)
        | 1 =>
          have hw0_eq_0 : w 0 = 0 := by
            have htemp : (Finset.univ : Finset (Fin 3)).sum w = 1 := hw_sum
            rw [h_univ_fin3] at htemp
            simp [hi1] at htemp
            have h_nonneg0 : 0 ≤ w 0 := (hw01 0).1
            have h_nonneg2 : 0 ≤ w 2 := (hw01 2).1
            nlinarith
          have hw2_eq_0 : w 2 = 0 := by
            have htemp : (Finset.univ : Finset (Fin 3)).sum w = 1 := hw_sum
            rw [h_univ_fin3] at htemp
            simp [hi1] at htemp
            have h_nonneg0 : 0 ≤ w 0 := (hw01 0).1
            have h_nonneg2 : 0 ≤ w 2 := (hw01 2).1
            nlinarith
          have hx_eq_point : x = T.points 1 := by
            calc
              x = ∑ j : Fin 3, w j • T.points j := hx_eq_sum
              _ = w 0 • (T.points 0) + w 1 • (T.points 1) + w 2 • (T.points 2) := by
                rw [h_univ_fin3]; simp [add_assoc]
              _ = 0 • (T.points 0) + 1 • (T.points 1) + 0 • (T.points 2) := by simp [hi1, hw0_eq_0, hw2_eq_0]
              _ = T.points 1 := by simp
          have hx_in_seg : x ∈ segment ℝ (T.points 1) (T.points 2) := by
            rw [hx_eq_point, segment, Set.mem_setOf_eq]
            exact ⟨1, 0, by norm_num, by norm_num, by norm_num, by simp⟩
          exact Or.inl (Or.inr hx_in_seg)
        | 2 =>
          have hw0_eq_0 : w 0 = 0 := by
            have htemp : (Finset.univ : Finset (Fin 3)).sum w = 1 := hw_sum
            rw [h_univ_fin3] at htemp
            simp [hi1] at htemp
            have h_nonneg0 : 0 ≤ w 0 := (hw01 0).1
            have h_nonneg1 : 0 ≤ w 1 := (hw01 1).1
            nlinarith
          have hw1_eq_0 : w 1 = 0 := by
            have htemp : (Finset.univ : Finset (Fin 3)).sum w = 1 := hw_sum
            rw [h_univ_fin3] at htemp
            simp [hi1] at htemp
            have h_nonneg0 : 0 ≤ w 0 := (hw01 0).1
            have h_nonneg1 : 0 ≤ w 1 := (hw01 1).1
            nlinarith
          have hx_eq_point : x = T.points 2 := by
            calc
              x = ∑ j : Fin 3, w j • T.points j := hx_eq_sum
              _ = w 0 • (T.points 0) + w 1 • (T.points 1) + w 2 • (T.points 2) := by
                rw [h_univ_fin3]; simp [add_assoc]
              _ = 0 • (T.points 0) + 0 • (T.points 1) + 1 • (T.points 2) := by simp [hi1, hw0_eq_0, hw1_eq_0]
              _ = T.points 2 := by simp
          have hx_in_seg : x ∈ segment ℝ (T.points 2) (T.points 0) := by
            rw [hx_eq_point, segment, Set.mem_setOf_eq]
            exact ⟨1, 0, by norm_num, by norm_num, by norm_num, by simp⟩
          exact Or.inr hx_in_seg
    exact h_in_union

  have h_edge1 : Jordan_outer_measure (segment ℝ (T.points 0) (T.points 1)) = 0 :=
    segment_outer_measure_zero (T.points 0) (T.points 1)
  have h_edge2 : Jordan_outer_measure (segment ℝ (T.points 1) (T.points 2)) = 0 :=
    segment_outer_measure_zero (T.points 1) (T.points 2)
  have h_edge3 : Jordan_outer_measure (segment ℝ (T.points 2) (T.points 0)) = 0 :=
    segment_outer_measure_zero (T.points 2) (T.points 0)
  -- The triangle's closedInterior = convexHull of its vertices (by convexHull_eq_closedInterior).
  -- Each segment is contained in this convex hull, hence bounded.
  have h_mem0 : T.points 0 ∈ Set.range T.points := Set.mem_range_self 0
  have h_mem1 : T.points 1 ∈ Set.range T.points := Set.mem_range_self 1
  have h_mem2 : T.points 2 ∈ Set.range T.points := Set.mem_range_self 2
  have h_seg_sub01 : segment ℝ (T.points 0) (T.points 1) ⊆ convexHull ℝ (Set.range T.points) :=
    segment_subset_convexHull h_mem0 h_mem1
  have h_seg_sub12 : segment ℝ (T.points 1) (T.points 2) ⊆ convexHull ℝ (Set.range T.points) :=
    segment_subset_convexHull h_mem1 h_mem2
  have h_seg_sub20 : segment ℝ (T.points 2) (T.points 0) ⊆ convexHull ℝ (Set.range T.points) :=
    segment_subset_convexHull h_mem2 h_mem0
  have h_eq_hull : convexHull ℝ (Set.range T.points) = T.closedInterior :=
    Affine.Simplex.convexHull_eq_closedInterior T
  have h_bdd01 : Bornology.IsBounded (segment ℝ (T.points 0) (T.points 1)) :=
    h_bounded.subset (h_seg_sub01.trans h_eq_hull.le)
  have h_bdd12 : Bornology.IsBounded (segment ℝ (T.points 1) (T.points 2)) :=
    h_bounded.subset (h_seg_sub12.trans h_eq_hull.le)
  have h_bdd20 : Bornology.IsBounded (segment ℝ (T.points 2) (T.points 0)) :=
    h_bounded.subset (h_seg_sub20.trans h_eq_hull.le)
  -- subadditivity for the first two
  have h_union12 : Jordan_outer_measure ((segment ℝ (T.points 0) (T.points 1)) ∪
      (segment ℝ (T.points 1) (T.points 2))) = 0 := by
    apply le_antisymm ?_ (Jordan_outer_measure_nonneg _)
    have h_subadd : Jordan_outer_measure ((segment ℝ (T.points 0) (T.points 1)) ∪
      (segment ℝ (T.points 1) (T.points 2))) ≤
      Jordan_outer_measure (segment ℝ (T.points 0) (T.points 1)) +
      Jordan_outer_measure (segment ℝ (T.points 1) (T.points 2)) :=
      Jordan_outer_subadd h_bdd01 h_bdd12
    rw [h_edge1, h_edge2, add_zero] at h_subadd
    exact h_subadd
  have h_union12_bdd : Bornology.IsBounded ((segment ℝ (T.points 0) (T.points 1)) ∪
      (segment ℝ (T.points 1) (T.points 2))) := h_bdd01.union h_bdd12
  -- subadditivity with the third
  have h_union_all : Jordan_outer_measure (((segment ℝ (T.points 0) (T.points 1)) ∪
      (segment ℝ (T.points 1) (T.points 2))) ∪ (segment ℝ (T.points 2) (T.points 0))) = 0 := by
    apply le_antisymm ?_ (Jordan_outer_measure_nonneg _)
    have h_subadd : Jordan_outer_measure (((segment ℝ (T.points 0) (T.points 1)) ∪
      (segment ℝ (T.points 1) (T.points 2))) ∪ (segment ℝ (T.points 2) (T.points 0))) ≤
      Jordan_outer_measure ((segment ℝ (T.points 0) (T.points 1)) ∪ (segment ℝ (T.points 1) (T.points 2))) +
      Jordan_outer_measure (segment ℝ (T.points 2) (T.points 0)) :=
      Jordan_outer_subadd h_union12_bdd h_bdd20
    rw [h_union12, h_edge3, add_zero] at h_subadd
    exact h_subadd
  have h_union_all_bdd : Bornology.IsBounded (((segment ℝ (T.points 0) (T.points 1)) ∪
      (segment ℝ (T.points 1) (T.points 2))) ∪ (segment ℝ (T.points 2) (T.points 0))) :=
    h_union12_bdd.union h_bdd20
  have h_frontier_sub' : frontier T.closedInterior ⊆
      ((segment ℝ (T.points 0) (T.points 1)) ∪ (segment ℝ (T.points 1) (T.points 2))) ∪
      (segment ℝ (T.points 2) (T.points 0)) :=
    h_frontier_sub
  exact le_antisymm
    (le_trans (Jordan_outer_measure_mono_of_subset h_frontier_sub' h_union_all_bdd) h_union_all.le)
    (Jordan_outer_measure_nonneg _)

/-- Exercise 1.1.8 (Jordan measurability of a triangle) -/
lemma JordanMeasurable.triangle (T: Affine.Triangle ℝ (EuclideanSpace' 2)) : JordanMeasurable T.closedInterior := by
  have hBounded : Bornology.IsBounded T.closedInterior := by
    have : Bornology.IsBounded (Set.range T.points) := (Set.finite_range T.points).isBounded
    have h_eq : T.closedInterior = convexHull ℝ (Set.range T.points) := by
      symm; exact Affine.Simplex.convexHull_eq_closedInterior T
    rw [h_eq]
    rw [isBounded_convexHull]
    exact this
  have hfrontier_null : Jordan_outer_measure (frontier T.closedInterior) = 0 :=
    triangle_frontier_outer_measure_zero T
  exact JordanMeasurable.if_frontier_null hBounded hfrontier_null

/-- The 2D wedge product (signed area parallelogram factor) of two vectors. -/
abbrev EuclideanSpace'.plane_wedge (x y: EuclideanSpace' 2) := x 1 * y 0 - x 0 * y 1

/-- Exercise 1.1.8 -/
-- The Jordan measure of a triangle equals half the absolute value of the wedge product of two edge vectors.
lemma JordanMeasurable.measure_triangle (T: Affine.Triangle ℝ (EuclideanSpace' 2)) : (JordanMeasurable.triangle T).measure = |EuclideanSpace'.plane_wedge (T.points 1 - T.points 0) (T.points 2 - T.points 0)| / 2 := by
  sorry

/-- Exercise 1.1.9  A polytope is the convex hull of a finite set of vertices. -/
abbrev IsPolytope {d:ℕ} (P: Set (EuclideanSpace' d)) : Prop :=
  ∃ (V: Finset (EuclideanSpace' d)), P = convexHull ℝ (V : Set _)

/-- Exercise 1.1.9: Every polytope is Jordan measurable. -/
lemma JordanMeasurable.polytope {d:ℕ} {P: Set (EuclideanSpace' d)} (hP: IsPolytope P) : JordanMeasurable P := by
  sorry

/-- The sphere in Euclidean space has Jordan outer measure zero. -/
lemma sphere_outer_measure_zero {d:ℕ} (x₀: EuclideanSpace' d) {r: ℝ} (hr: 0 < r) :
    Jordan_outer_measure (Metric.sphere x₀ r) = 0 := by
  -- translation invariance of Jordan outer measure
  have Jord_trans : ∀ {d':ℕ} (E : Set (EuclideanSpace' d')) (x : EuclideanSpace' d'),
      Jordan_outer_measure (E + {x}) = Jordan_outer_measure E := by
    intro d' E x
    rw [eq_comm, Jordan_outer_measure, Jordan_outer_measure]
    congr! 3
    constructor
    · rintro ⟨A, hA, hA', rfl⟩
      refine ⟨A + {x}, IsElementary.translate hA x, ?_, Eq.symm (IsElementary.measure_of_translate hA x)⟩
      exact Set.add_subset_add hA' (Set.Subset.refl _)
    · rintro ⟨A, hA, hA', rfl⟩
      refine ⟨A + {-x}, IsElementary.translate hA (-x), ?_, Eq.symm (IsElementary.measure_of_translate hA (-x))⟩
      intro y hy
      have hy_plus_x : y + x ∈ E + {x} := Set.mem_add.mpr ⟨y, hy, x, Set.mem_singleton x, rfl⟩
      have hy_plus_x_in_A : y + x ∈ A := hA' hy_plus_x
      refine Set.mem_add.mpr ⟨y + x, hy_plus_x_in_A, -x, Set.mem_singleton (-x), ?_⟩
      abel
  -- sphere translation: sphere x₀ r = {x₀} + sphere (0 : EuclideanSpace' d) r
  have sphere_trans : ∀ {d':ℕ} (x₀' : EuclideanSpace' d') (r' : ℝ),
      Metric.sphere x₀' r' = {x₀'} + Metric.sphere (0 : EuclideanSpace' d') r' := by
    intro d' x₀' r'
    ext x; constructor
    · intro hx
      have hz : x - x₀' ∈ Metric.sphere (0 : EuclideanSpace' d') r' := by
        rw [Metric.mem_sphere, dist_eq_norm]
        simpa [sub_sub_cancel] using hx
      refine Set.mem_add.mpr ⟨x₀', Set.mem_singleton x₀', x - x₀', hz, ?_⟩
      abel
    · rintro ⟨y, hy, z, hz, rfl⟩
      rcases hy with rfl
      rw [Metric.mem_sphere, dist_eq_norm]
      simpa [add_sub_cancel_right] using hz
  -- norm squared equals sum of squares
  have h_norm_sq_eq : ∀ {n : ℕ} (z : EuclideanSpace' n), ‖z‖^2 = ∑ i : Fin n, (z i)^2 := by
    intro n z
    calc
      ‖z‖^2 = (Real.sqrt (∑ i : Fin n, ‖z.ofLp i‖ ^ 2))^2 := by rw [EuclideanSpace.norm_eq]
      _ = (∑ i : Fin n, ‖z.ofLp i‖ ^ 2) := by
        have h_nonneg : 0 ≤ ∑ i : Fin n, ‖z.ofLp i‖ ^ 2 :=
          Finset.sum_nonneg (λ i _ => pow_two_nonneg _)
        rw [Real.sq_sqrt h_nonneg]
      _ = ∑ i : Fin n, (z i)^2 := by simp
  -- main work: sphere at 0 has outer measure 0
  have sphere_zero_zero : Jordan_outer_measure (Metric.sphere (0 : EuclideanSpace' d) r) = 0 := by
    match d with
    | 0 =>
      have h_empty : Metric.sphere (0 : EuclideanSpace' 0) r = ∅ := by
        ext x; simp
        intro h
        have hx0 : x = 0 := Subsingleton.elim _ _
        subst hx0
        simp at h
        linarith
      simp [h_empty, Jordan_outer_measure_empty 0]
    | d'+1 =>
      let B : Box d' := ⟨fun _ => BoundedInterval.Icc (-r) r⟩
      let g : EuclideanSpace' d' → ℝ := λ y => Real.sqrt (max 0 (r^2 - ‖y‖^2))
      have hg_cont : Continuous g := by
        unfold g
        refine Real.continuous_sqrt.comp ?_
        have h_cont : Continuous (λ (y : EuclideanSpace' d') => r^2 - ‖y‖^2) := by
          refine Continuous.sub continuous_const ?_
          exact (continuous_norm.pow 2)
        have h_zero : Continuous (λ (y : EuclideanSpace' d') => (0 : ℝ)) := continuous_const
        simpa [max_comm] using h_cont.max h_zero
      have hg_cont_on : ContinuousOn g B.toSet := hg_cont.continuousOn
      have hB_closed : ∀ i, ∃ a b, B.side i = BoundedInterval.Icc a b := by
        intro i; exact ⟨-r, r, rfl⟩
      have h_graph_zero : Jordan_outer_measure {p | ∃ y ∈ B.toSet, EuclideanSpace'.prod_equiv d' 1 p = ⟨y, g y⟩} = 0 :=
        graph_outer_measure_zero hB_closed hg_cont_on
      have h_bdd_graph : Bornology.IsBounded {p | ∃ y ∈ B.toSet, EuclideanSpace'.prod_equiv d' 1 p = ⟨y, g y⟩} :=
        graph_isBounded hB_closed hg_cont_on
      -- upper hemisphere (last coordinate >= 0)
      have h_upper_sub : {x : EuclideanSpace' (d'+1) | ‖x‖ = r ∧ ((EuclideanSpace'.prod_equiv d' 1 x).2 0) ≥ 0} ⊆
          {p | ∃ y ∈ B.toSet, EuclideanSpace'.prod_equiv d' 1 p = ⟨y, g y⟩} := by
        intro x hx
        rcases hx with ⟨hx_norm, hx_upper⟩
        set y := (EuclideanSpace'.prod_equiv d' 1 x).1 with hy_def
        have hy_mem : y ∈ B.toSet := by
          rw [Box.mem_toSet]
          intro i
          have hxi_sq_bound : (x (Fin.castSucc i))^2 ≤ ‖x‖^2 := by
            rw [h_norm_sq_eq x]
            refine Finset.single_le_sum (λ j _ => pow_two_nonneg _) (Finset.mem_univ (Fin.castSucc i))
          have hxi_bound : |x (Fin.castSucc i)| ≤ r := by
            have hsq : (x (Fin.castSucc i))^2 ≤ r^2 := by nlinarith
            have hr_nonneg : 0 ≤ r := by linarith
            have h_low : -r ≤ x (Fin.castSucc i) := by nlinarith
            have h_high : x (Fin.castSucc i) ≤ r := by nlinarith
            exact abs_le.mpr ⟨h_low, h_high⟩
          have hy_i : y i = x (Fin.castSucc i) := by
            dsimp [y, EuclideanSpace'.prod_equiv]
            apply congrArg x.ofLp; ext; simp
          rw [hy_i]
          exact abs_le.mp hxi_bound
        have hx_last_sq : r^2 - ‖y‖^2 = (x (Fin.last d'))^2 := by
          have h_norm_sq_split : ‖x‖^2 = ‖y‖^2 + (x (Fin.last d'))^2 := by
            calc
              ‖x‖^2 = ∑ j : Fin (d'+1), (x j)^2 := h_norm_sq_eq x
              _ = (∑ i : Fin d', (x (Fin.castSucc i))^2) + (x (Fin.last d'))^2 := by
                rw [Fin.sum_univ_castSucc]
              _ = (∑ i : Fin d', (y i)^2) + (x (Fin.last d'))^2 := by
                refine congrArg (· + (x (Fin.last d'))^2) ?_
                refine Finset.sum_congr rfl (λ i hi => ?_)
                have hy_i : y i = x (Fin.castSucc i) := by
                  dsimp [y, EuclideanSpace'.prod_equiv]
                  apply congrArg x.ofLp; ext; simp
                simp [hy_i]
              _ = ‖y‖^2 + (x (Fin.last d'))^2 := by rw [h_norm_sq_eq y]
          nlinarith
        have hx_last_nonneg : 0 ≤ x (Fin.last d') := by
          have hproj_val : ((EuclideanSpace'.prod_equiv d' 1 x).2 0) = x (Fin.last d') := by
            simp [EuclideanSpace'.prod_equiv, Real.equiv_EuclideanSpace']
            apply congrArg x.ofLp; ext; simp
          rw [hproj_val] at hx_upper
          exact hx_upper
        have hg_val : g y = x (Fin.last d') := by
          dsimp [g]
          have h_sq_nonneg : 0 ≤ r^2 - ‖y‖^2 := by
            have h_nonneg_sq : 0 ≤ (x (Fin.last d'))^2 := pow_two_nonneg _
            nlinarith
          calc
            Real.sqrt (max 0 (r^2 - ‖y‖^2)) = Real.sqrt (r^2 - ‖y‖^2) := by
              rw [max_eq_right h_sq_nonneg]
            _ = Real.sqrt ((x (Fin.last d'))^2) := by rw [hx_last_sq]
            _ = |x (Fin.last d')| := Real.sqrt_sq_eq_abs _
            _ = x (Fin.last d') := abs_of_nonneg hx_last_nonneg
        refine ⟨y, hy_mem, ?_⟩
        apply Prod.ext
        · simp [y]
        · calc
            (EuclideanSpace'.prod_equiv d' 1 x).2 = (Real.equiv_EuclideanSpace' (x (Fin.last d'))) := by
              ext j; simp [EuclideanSpace'.prod_equiv, Real.equiv_EuclideanSpace']
              apply congrArg x.ofLp; ext; simp
            _ = (g y : EuclideanSpace' 1) := by
              ext j; simp [hg_val]
      have h_upper_zero : Jordan_outer_measure {x : EuclideanSpace' (d'+1) | ‖x‖ = r ∧ ((EuclideanSpace'.prod_equiv d' 1 x).2 0) ≥ 0} = 0 :=
        le_antisymm
          (le_trans (Jordan_outer_measure_mono_of_subset h_upper_sub h_bdd_graph) (by rw [h_graph_zero]))
          (Jordan_outer_measure_nonneg _)
      -- lower hemisphere (last coordinate <= 0)
      have h_lower_sub : {x : EuclideanSpace' (d'+1) | ‖x‖ = r ∧ ((EuclideanSpace'.prod_equiv d' 1 x).2 0) ≤ 0} ⊆
          {p | ∃ y ∈ B.toSet, EuclideanSpace'.prod_equiv d' 1 p = ⟨y, -(g y)⟩} := by
        intro x hx
        rcases hx with ⟨hx_norm, hx_lower⟩
        set y := (EuclideanSpace'.prod_equiv d' 1 x).1 with hy_def
        have hy_mem : y ∈ B.toSet := by
          rw [Box.mem_toSet]
          intro i
          have hxi_sq_bound : (x (Fin.castSucc i))^2 ≤ ‖x‖^2 := by
            rw [h_norm_sq_eq x]
            refine Finset.single_le_sum (λ j _ => pow_two_nonneg _) (Finset.mem_univ (Fin.castSucc i))
          have hxi_bound : |x (Fin.castSucc i)| ≤ r := by
            have hsq : (x (Fin.castSucc i))^2 ≤ r^2 := by nlinarith
            have hr_nonneg : 0 ≤ r := by linarith
            have h_low : -r ≤ x (Fin.castSucc i) := by nlinarith
            have h_high : x (Fin.castSucc i) ≤ r := by nlinarith
            exact abs_le.mpr ⟨h_low, h_high⟩
          have hy_i : y i = x (Fin.castSucc i) := by
            dsimp [y, EuclideanSpace'.prod_equiv]
            apply congrArg x.ofLp; ext; simp
          rw [hy_i]
          exact abs_le.mp hxi_bound
        have hx_last_sq : r^2 - ‖y‖^2 = (x (Fin.last d'))^2 := by
          have h_norm_sq_split : ‖x‖^2 = ‖y‖^2 + (x (Fin.last d'))^2 := by
            calc
              ‖x‖^2 = ∑ j : Fin (d'+1), (x j)^2 := h_norm_sq_eq x
              _ = (∑ i : Fin d', (x (Fin.castSucc i))^2) + (x (Fin.last d'))^2 := by
                rw [Fin.sum_univ_castSucc]
              _ = (∑ i : Fin d', (y i)^2) + (x (Fin.last d'))^2 := by
                refine congrArg (· + (x (Fin.last d'))^2) ?_
                refine Finset.sum_congr rfl (λ i hi => ?_)
                have hy_i : y i = x (Fin.castSucc i) := by
                  dsimp [y, EuclideanSpace'.prod_equiv]
                  apply congrArg x.ofLp; ext; simp
                simp [hy_i]
              _ = ‖y‖^2 + (x (Fin.last d'))^2 := by rw [h_norm_sq_eq y]
          nlinarith
        have hx_last_nonpos : x (Fin.last d') ≤ 0 := by
          have hproj_val : ((EuclideanSpace'.prod_equiv d' 1 x).2 0) = x (Fin.last d') := by
            simp [EuclideanSpace'.prod_equiv, Real.equiv_EuclideanSpace']
            apply congrArg x.ofLp; ext; simp
          rw [hproj_val] at hx_lower
          exact hx_lower
        have hg_val : -(g y) = x (Fin.last d') := by
          dsimp [g]
          have h_sq_nonneg : 0 ≤ r^2 - ‖y‖^2 := by
            have h_nonneg_sq : 0 ≤ (x (Fin.last d'))^2 := pow_two_nonneg _
            nlinarith
          calc
            -(Real.sqrt (max 0 (r^2 - ‖y‖^2))) = -(Real.sqrt (r^2 - ‖y‖^2)) := by
              rw [max_eq_right h_sq_nonneg]
            _ = -(Real.sqrt ((x (Fin.last d'))^2)) := by rw [hx_last_sq]
            _ = -|x (Fin.last d')| := by rw [Real.sqrt_sq_eq_abs _]
            _ = x (Fin.last d') := by
              rw [abs_of_nonpos hx_last_nonpos, neg_neg]
        refine ⟨y, hy_mem, ?_⟩
        apply Prod.ext
        · simp [y]
        · calc
            (EuclideanSpace'.prod_equiv d' 1 x).2 = (Real.equiv_EuclideanSpace' (x (Fin.last d'))) := by
              ext j; simp [EuclideanSpace'.prod_equiv, Real.equiv_EuclideanSpace']
              apply congrArg x.ofLp; ext; simp
            _ = (-(g y) : EuclideanSpace' 1) := by
              ext j; simp [hg_val]
      have h_neg_g_cont : ContinuousOn (-g) B.toSet := hg_cont_on.neg
      have h_graph_lower_zero : Jordan_outer_measure {p | ∃ y ∈ B.toSet, EuclideanSpace'.prod_equiv d' 1 p = ⟨y, -(g y)⟩} = 0 :=
        graph_outer_measure_zero hB_closed h_neg_g_cont
      have h_bdd_graph_lower : Bornology.IsBounded {p | ∃ y ∈ B.toSet, EuclideanSpace'.prod_equiv d' 1 p = ⟨y, -(g y)⟩} :=
        graph_isBounded hB_closed h_neg_g_cont
      have h_lower_zero : Jordan_outer_measure {x : EuclideanSpace' (d'+1) | ‖x‖ = r ∧ ((EuclideanSpace'.prod_equiv d' 1 x).2 0) ≤ 0} = 0 :=
        le_antisymm
          (le_trans (Jordan_outer_measure_mono_of_subset h_lower_sub h_bdd_graph_lower) (by rw [h_graph_lower_zero]))
          (Jordan_outer_measure_nonneg _)
      have h_sphere_eq : Metric.sphere (0 : EuclideanSpace' (d'+1)) r =
          {x : EuclideanSpace' (d'+1) | ‖x‖ = r ∧ ((EuclideanSpace'.prod_equiv d' 1 x).2 0) ≥ 0} ∪
          {x : EuclideanSpace' (d'+1) | ‖x‖ = r ∧ ((EuclideanSpace'.prod_equiv d' 1 x).2 0) ≤ 0} := by
        ext x; constructor
        · intro hx
          rw [Metric.mem_sphere, dist_eq_norm] at hx
          have hx_norm : ‖x‖ = r := by simpa [sub_zero] using hx
          by_cases h : ((EuclideanSpace'.prod_equiv d' 1 x).2 0) ≥ 0
          · exact Or.inl ⟨hx_norm, h⟩
          · exact Or.inr ⟨hx_norm, by linarith⟩
        · rintro (⟨hx, _⟩ | ⟨hx, _⟩)
          · rw [Metric.mem_sphere, dist_eq_norm, sub_zero]; exact hx
          · rw [Metric.mem_sphere, dist_eq_norm, sub_zero]; exact hx
      have h_bdd_sphere : Bornology.IsBounded (Metric.sphere (0 : EuclideanSpace' (d'+1)) r) :=
        Metric.isBounded_sphere
      have h_upper_set : {x : EuclideanSpace' (d'+1) | ‖x‖ = r ∧ ((EuclideanSpace'.prod_equiv d' 1 x).2 0) ≥ 0} ⊆
          Metric.sphere (0 : EuclideanSpace' (d'+1)) r := by
        intro x hx; rw [Metric.mem_sphere, dist_eq_norm, sub_zero]; exact hx.1
      have h_lower_set : {x : EuclideanSpace' (d'+1) | ‖x‖ = r ∧ ((EuclideanSpace'.prod_equiv d' 1 x).2 0) ≤ 0} ⊆
          Metric.sphere (0 : EuclideanSpace' (d'+1)) r := by
        intro x hx; rw [Metric.mem_sphere, dist_eq_norm, sub_zero]; exact hx.1
      have h_upper_bdd : Bornology.IsBounded {x : EuclideanSpace' (d'+1) | ‖x‖ = r ∧ ((EuclideanSpace'.prod_equiv d' 1 x).2 0) ≥ 0} :=
        h_bdd_sphere.subset h_upper_set
      have h_lower_bdd : Bornology.IsBounded {x : EuclideanSpace' (d'+1) | ‖x‖ = r ∧ ((EuclideanSpace'.prod_equiv d' 1 x).2 0) ≤ 0} :=
        h_bdd_sphere.subset h_lower_set
      rw [h_sphere_eq]
      have h_subadd : Jordan_outer_measure
          ({x | ‖x‖ = r ∧ ((EuclideanSpace'.prod_equiv d' 1 x).2 0) ≥ 0} ∪
           {x | ‖x‖ = r ∧ ((EuclideanSpace'.prod_equiv d' 1 x).2 0) ≤ 0}) ≤
          Jordan_outer_measure {x | ‖x‖ = r ∧ ((EuclideanSpace'.prod_equiv d' 1 x).2 0) ≥ 0} +
          Jordan_outer_measure {x | ‖x‖ = r ∧ ((EuclideanSpace'.prod_equiv d' 1 x).2 0) ≤ 0} :=
        Jordan_outer_subadd h_upper_bdd h_lower_bdd
      rw [h_upper_zero, h_lower_zero, add_zero] at h_subadd
      exact le_antisymm h_subadd (Jordan_outer_measure_nonneg _)
  calc
    Jordan_outer_measure (Metric.sphere x₀ r) = Jordan_outer_measure ({x₀} + Metric.sphere (0 : EuclideanSpace' d) r) := by
      rw [sphere_trans x₀ r]
    _ = Jordan_outer_measure (Metric.sphere (0 : EuclideanSpace' d) r + {x₀}) := by
      have h_comm : ({x₀} : Set (EuclideanSpace' d)) + Metric.sphere (0 : EuclideanSpace' d) r =
          Metric.sphere (0 : EuclideanSpace' d) r + ({x₀} : Set (EuclideanSpace' d)) := by
        ext x; simp [Set.mem_add, add_comm]
      rw [h_comm]
    _ = Jordan_outer_measure (Metric.sphere (0 : EuclideanSpace' d) r) := Jord_trans _ _
    _ = 0 := sphere_zero_zero

/-- Exercise 1.1.10 (1) -/
-- An open ball is Jordan measurable.
lemma JordanMeasurable.ball {d:ℕ} (x₀: EuclideanSpace' d) {r: ℝ} (hr: 0 < r) : JordanMeasurable (Metric.ball x₀ r) := by
  have hfrontier : frontier (Metric.ball x₀ r) = Metric.sphere x₀ r :=
    frontier_ball x₀ hr.ne.symm
  have hfrontier_null : Jordan_outer_measure (frontier (Metric.ball x₀ r)) = 0 := by
    rw [hfrontier]
    exact sphere_outer_measure_zero x₀ hr
  have hBounded : Bornology.IsBounded (Metric.ball x₀ r) := Metric.isBounded_ball
  exact JordanMeasurable.if_frontier_null hBounded hfrontier_null

/-- Exercise 1.1.10 (1) -/
-- A closed ball is Jordan measurable.
lemma JordanMeasurable.closedBall {d:ℕ} (x₀: EuclideanSpace' d) {r: ℝ} (hr: 0 < r) : JordanMeasurable (Metric.closedBall x₀ r) := by
  have hSpBounded : Bornology.IsBounded (Metric.sphere x₀ r) := Metric.isBounded_sphere
  have hSpFrontierNull : Jordan_outer_measure (frontier (Metric.sphere x₀ r)) = 0 := by
    rw [frontier_sphere x₀ hr.ne.symm, sphere_outer_measure_zero x₀ hr]
  have hSpJM : JordanMeasurable (Metric.sphere x₀ r) :=
    JordanMeasurable.if_frontier_null hSpBounded hSpFrontierNull
  have hBallJM : JordanMeasurable (Metric.ball x₀ r) := JordanMeasurable.ball x₀ hr
  have h_union : Metric.closedBall x₀ r = Metric.ball x₀ r ∪ Metric.sphere x₀ r := by
    ext x; constructor
    · intro hx
      rw [Metric.mem_closedBall, dist_eq_norm] at hx
      by_cases h : ‖x - x₀‖ < r
      · apply Or.inl; rw [Metric.mem_ball, dist_eq_norm]; exact h
      · apply Or.inr; rw [Metric.mem_sphere, dist_eq_norm]; exact le_antisymm hx (by linarith)
    · rintro (hx | hx)
      · rw [Metric.mem_ball, dist_eq_norm] at hx
        rw [Metric.mem_closedBall, dist_eq_norm]; linarith
      · rw [Metric.mem_sphere, dist_eq_norm] at hx
        rw [Metric.mem_closedBall, dist_eq_norm]; linarith
  rw [h_union]
  exact hBallJM.union hSpJM


/-- Exercise 1.1.10 (1) -/
-- The Jordan measure of a ball is proportional to r^d with a dimension-dependent constant.
lemma JordanMeasurable.measure_ball (d:ℕ) : ∃ c, ∀ (x₀: EuclideanSpace' d) (r: ℝ) (hr: 0 < r), (ball x₀ hr).measure = c * r^d := by sorry

/-- The Jordan measure of a closed ball equals that of the open ball. -/
lemma JordanMeasurable.measure_closedBall {d:ℕ} (x₀: EuclideanSpace' d) {r: ℝ} (hr: 0 < r): (closedBall x₀ hr).measure = (ball x₀ hr).measure := by
  have hDisj : Disjoint (Metric.ball x₀ r) (Metric.sphere x₀ r) := by
    rw [Set.disjoint_iff]
    intro x hx
    rcases hx with ⟨hx1, hx2⟩
    rw [Metric.mem_ball] at hx1
    rw [Metric.mem_sphere] at hx2
    linarith
  have hSphereJM : JordanMeasurable (Metric.sphere x₀ r) := by
    have hBounded : Bornology.IsBounded (Metric.sphere x₀ r) := Metric.isBounded_sphere
    have hFrontierNull : Jordan_outer_measure (frontier (Metric.sphere x₀ r)) = 0 := by
      rw [frontier_sphere x₀ hr.ne.symm, sphere_outer_measure_zero x₀ hr]
    exact JordanMeasurable.if_frontier_null hBounded hFrontierNull
  have hSphereMeasure : hSphereJM.measure = 0 := by
    rw [JordanMeasurable.eq_outer hSphereJM, sphere_outer_measure_zero x₀ hr]
  have hEq : Metric.closedBall x₀ r = Metric.ball x₀ r ∪ Metric.sphere x₀ r := by
    ext x; simp [le_iff_lt_or_eq]
  calc
    (closedBall x₀ hr).measure = Jordan_inner_measure (Metric.closedBall x₀ r) := rfl
    _ = Jordan_inner_measure (Metric.ball x₀ r ∪ Metric.sphere x₀ r) := by rw [hEq]
    _ = ((ball x₀ hr).union hSphereJM).measure := rfl
    _ = (ball x₀ hr).measure + hSphereJM.measure := by
      rw [JordanMeasurable.mes_of_disjUnion (ball x₀ hr) hSphereJM hDisj]
    _ = (ball x₀ hr).measure := by rw [hSphereMeasure, add_zero]

/-- Exercise 1.1.10 (2) -/
-- The ball measure constant is bounded above by 2^d.
lemma JordanMeasurable.measure_ball_le (d:ℕ) : (measure_ball d).choose ≤ 2^d := by sorry

/-- Exercise 1.1.10 (2) -/
-- The ball measure constant is bounded below by 2^d / d!.
lemma JordanMeasurable.le_measure_ball (d:ℕ) : 2^d/d.factorial ≤ (measure_ball d).choose := by sorry

/-- Exercise 1.1.11 (1) -/
-- The linear image of an elementary set is Jordan measurable.
lemma JordanMeasurable.linear_of_elem {d:ℕ} (T: EuclideanSpace' d ≃ₗ[ℝ] EuclideanSpace' d)
{E: Set (EuclideanSpace' d)} (hE: IsElementary E): JordanMeasurable (T '' E) := by
  sorry

/-- Exercise 1.1.11 (1) -/
-- The measure of a linear image of an elementary set scales by a fixed factor depending on the transformation.
lemma JordanMeasurable.measure_linear_of_elem {d:ℕ} (T: EuclideanSpace' d ≃ₗ[ℝ] EuclideanSpace' d) : ∃ D > 0, ∀ (E: Set (EuclideanSpace' d)) (hE: IsElementary E), (linear_of_elem T hE).measure = D * hE.measure := by sorry

/-- Exercise 1.1.11 (2) -/
-- The linear image of a Jordan measurable set is Jordan measurable.
lemma JordanMeasurable.linear {d:ℕ} (T: EuclideanSpace' d ≃ₗ[ℝ] EuclideanSpace' d)
{E: Set (EuclideanSpace' d)} (hE: JordanMeasurable E): JordanMeasurable (T '' E) := by
  sorry

/-- Exercise 1.1.11 (2) -/
-- The measure of a linear image of a Jordan measurable set equals the original measure (up to determinant scaling).
lemma JordanMeasurable.measure_linear {d:ℕ} (T: EuclideanSpace' d ≃ₗ[ℝ] EuclideanSpace' d) :
∃ D > 0, ∀ (E: Set (EuclideanSpace' d)) (hE: JordanMeasurable E), (linear T hE).measure = hE.measure := by sorry

/-- An invertible matrix defines a linear equivalence on Euclidean space. -/
noncomputable def Matrix.linear_equiv {d:ℕ} (A: Matrix (Fin d) (Fin d) ℝ) [Invertible A] :
EuclideanSpace' d ≃ₗ[ℝ] EuclideanSpace' d where
  toFun x := .toLp 2 (toLin' A x.ofLp)
  map_add' x y := by
    apply PiLp.ext; intro i; simp [map_add]
  map_smul' r x := by
    apply PiLp.ext; intro i; simp [map_smul]
  invFun x := .toLp 2 (toLin' A⁻¹ x.ofLp)
  left_inv x := by
    apply PiLp.ext; intro i; simp
  right_inv x := by
    apply PiLp.ext; intro i; simp

/-- Exercise 1.1.11 (3) -/
-- For a linear map from an invertible matrix, the measure scaling factor equals the absolute value of the determinant.
lemma JordanMeasurable.measure_linear_det {d:ℕ} (A: Matrix (Fin d) (Fin d) ℝ) [Invertible A] :
(measure_linear A.linear_equiv).choose = |A.det| := by sorry

/-- A set is Jordan null if it is Jordan measurable with measure zero. -/
abbrev JordanMeasurable.null {d:ℕ} (E: Set (EuclideanSpace' d)) : Prop := ∃ hE: JordanMeasurable E, hE.measure = 0

/-- A set is Jordan null iff it's bounded with outer Jordan measure zero. -/
lemma JordanMeasurable.null_iff {d:ℕ} {E: Set (EuclideanSpace' d)} : null E ↔ Bornology.IsBounded E ∧ Jordan_outer_measure E = 0 := by
  constructor
  · rintro ⟨hE, hmeasure⟩
    have hbound : Bornology.IsBounded E := hE.1
    have hinner_outer : Jordan_inner_measure E = Jordan_outer_measure E := hE.2
    exact ⟨hbound, by rw [← hinner_outer]; exact hmeasure⟩
  · rintro ⟨hbound, houter_zero⟩
    have hinner_nonneg : 0 ≤ Jordan_inner_measure E := Jordan_inner_measure_nonneg E
    have hinner_le_outer : Jordan_inner_measure E ≤ Jordan_outer_measure E := Jordan_inner_le_outer hbound
    have hinner_zero : Jordan_inner_measure E = 0 := by linarith
    have hinner_outer_eq : Jordan_inner_measure E = Jordan_outer_measure E := by
      rw [hinner_zero, houter_zero]
    exact ⟨⟨hbound, hinner_outer_eq⟩, hinner_zero⟩

/-- Exercise 1.1.12 -/
-- A subset of a Jordan null set is also Jordan null.
lemma JordanMeasurable.null_mono {d:ℕ} {E F: Set (EuclideanSpace' d)} (h: null E) (hEF: F ⊆ E) : null F := by
  rcases null_iff.mp h with ⟨hEbounded, hEouter⟩
  have hFbounded : Bornology.IsBounded F := hEbounded.subset hEF
  have hFouter : Jordan_outer_measure F = 0 := by
    have h_nonneg : 0 ≤ Jordan_outer_measure F := Jordan_outer_measure_nonneg F
    have hF_le_E : Jordan_outer_measure F ≤ Jordan_outer_measure E := by
      unfold Jordan_outer_measure
      apply csInf_le_csInf
      · -- The set for F is bounded below by 0
        use 0
        intro m hm
        obtain ⟨A, hA, _, hm_eq⟩ := hm
        rw [hm_eq]
        exact hA.measure_nonneg
      · -- The set for E is nonempty: E is bounded, so there exists an elementary superset
        obtain ⟨A, hA, hEA⟩ := IsElementary.contains_bounded hEbounded
        exact ⟨hA.measure, A, hA, hEA, rfl⟩
      · -- Since F ⊆ E, any elementary superset of E is also a superset of F
        intro m hm
        obtain ⟨A, hA, hEA, hm_eq⟩ := hm
        exact ⟨A, hA, Set.Subset.trans hEF hEA, hm_eq⟩
    rw [hEouter] at hF_le_E
    nlinarith
  exact null_iff.mpr ⟨hFbounded, hFouter⟩

/-- Exercise 1.1.13 -/
-- The Jordan measure equals the limit of scaled lattice point counts in the set.
theorem JordanMeasure.measure_eq {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: JordanMeasurable E):
  Filter.atTop.Tendsto (fun N:ℕ ↦ (N:ℝ)^(-d:ℝ) * Nat.card ↥(E ∩ (Set.range (fun (n:Fin d → ℤ) ↦ .toLp 2 (fun i ↦ (N:ℝ)⁻¹*(n i))))))
  (nhds hE.measure) := by sorry

/-- A dyadic box at scale 2^(-n) with multi-index i: the half-open cube \[i/2^n, (i+1)/2^n). -/
noncomputable abbrev Box.dyadic {d:ℕ} (n:ℤ) (i:Fin d → ℤ) : Box d where
  side j := BoundedInterval.Ico ((i j)/2^n) ((i j + 1)/2^n)

/-- Lower metric entropy: count of dyadic boxes at scale n fully contained in E. -/
noncomputable abbrev metric_entropy_lower {d:ℕ} (E: Set (EuclideanSpace' d)) (n:ℤ) : ℕ := Nat.card { i:Fin d → ℤ | (Box.dyadic n i).toSet ⊆ E }

/-- Upper metric entropy: count of dyadic boxes at scale n that intersect E. -/
noncomputable abbrev metric_entropy_upper {d:ℕ} (E: Set (EuclideanSpace' d)) (n:ℤ) : ℕ := Nat.card { i:Fin d → ℤ | (Box.dyadic n i).toSet ∩ E ≠ ∅ }

/-- Exercise 1.1.14 -/
-- Jordan measurability is characterized by convergence of scaled dyadic metric entropy difference to zero.
theorem JordanMeasure.iff {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E) :
  JordanMeasurable E ↔ Filter.atTop.Tendsto (fun n ↦ (2:ℝ)^(-(d*n:ℤ)) * ((metric_entropy_upper E n - metric_entropy_lower E n))) (nhds 0) := by sorry

/-- Jordan measure equals the limit of scaled lower metric entropy. -/
theorem JordanMeasure.eq_lim_lower {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: JordanMeasurable E) :
   Filter.atTop.Tendsto (fun n ↦ (2:ℝ)^(-(d*n:ℤ)) * (metric_entropy_lower E n)) (nhds hE.measure) := by sorry

/-- Jordan measure equals the limit of scaled upper metric entropy. -/
theorem JordanMeasure.eq_lim_upper {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: JordanMeasurable E) :
   Filter.atTop.Tendsto (fun n ↦ (2:ℝ)^(-(d*n:ℤ)) * (metric_entropy_upper E n)) (nhds hE.measure) := by sorry

/-- Exercise 1.1.15 (Uniqueness of Jordan measure) -/
theorem JordanMeasure.measure_uniq {d:ℕ} {m': (E: Set (EuclideanSpace' d)) → (JordanMeasurable E) → ℝ}
  (hnonneg: ∀ E: Set (EuclideanSpace' d), ∀ hE: JordanMeasurable E, m' E hE ≥ 0)
  (hadd: ∀ E F: Set (EuclideanSpace' d), ∀ (hE: JordanMeasurable E) (hF: JordanMeasurable F),
   Disjoint E F → m' (E ∪ F) (hE.union hF) = m' E hE + m' F hF)
  (htrans: ∀ E: Set (EuclideanSpace' d), ∀ (hE: JordanMeasurable E) (x: EuclideanSpace' d), m' (E + {x}) (hE.translate x) = m' E hE) : ∃ c, c ≥ 0 ∧ ∀ E: Set (EuclideanSpace' d), ∀ hE: JordanMeasurable E, m' E hE = c * hE.measure := by
    sorry

/-- With unit cube normalization, the unique such function equals Jordan measure. -/
theorem JordanMeasure.measure_uniq' {d:ℕ} {m': (E: Set (EuclideanSpace' d)) → (JordanMeasurable E) → ℝ}
  (hnonneg: ∀ E: Set (EuclideanSpace' d), ∀ hE: JordanMeasurable E, m' E hE ≥ 0)
  (hadd: ∀ E F: Set (EuclideanSpace' d), ∀ (hE: JordanMeasurable E) (hF: JordanMeasurable F),
   Disjoint E F → m' (E ∪ F) (hE.union hF) = m' E hE + m' F hF)
  (htrans: ∀ E: Set (EuclideanSpace' d), ∀ (hE: JordanMeasurable E) (x: EuclideanSpace' d), m' (E + {x}) (hE.translate x) = m' E hE)
  (hcube : m' (Box.unit_cube d) (IsElementary.box _).jordanMeasurable = 1) :
  ∀ E: Set (EuclideanSpace' d), ∀ hE: JordanMeasurable E, m' E hE = hE.measure := by
    sorry


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

/-- Exercise 1.1.17 -/
theorem JordanMeasurable.measure_of_equidecomposable {d n:ℕ} {E F: Set (EuclideanSpace' d)}
  (hE: JordanMeasurable E) (hF: JordanMeasurable F)
  {P Q: Fin n → Set (EuclideanSpace' d)} (hPQ: ∀ i, Isometric (P i) (Q i))
  (hPE: E = ⋃ i, P i) (hQF: F = ⋃ i, Q i) (hPdisj: Set.PairwiseDisjoint .univ P)
  (hQdisj: Set.PairwiseDisjoint .univ (fun i ↦ (interior (Q i)))) : hE.measure = hF.measure := by
  sorry

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
