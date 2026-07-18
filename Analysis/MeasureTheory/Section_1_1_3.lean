import Analysis.MeasureTheory.Section_1_1_2_ext2

set_option linter.unnecessarySimpa false

/-!
# Introduction to Measure Theory, Section 1.1.3: Connections with the Riemann integral

A companion to Section 1.1.3 of the book "An introduction to Measure Theory".

-/

open BoundedInterval

/-- Definition 1.1.5.  (Riemann integrability) The interval {lean}`I` should be closed, though we will not enforce this.  We also permit the length to be 0. We index the tags and deltas starting from 0 rather than 1
in the text as this is slightly more convenient in Lean. -/
@[ext]
structure TaggedPartition (I: BoundedInterval) (n:ℕ) where
  x : Fin (n+1) → ℝ
  x_tag : Fin n → ℝ
  x_start : x 0 = I.a
  x_end : x (Fin.last n) = I.b
  x_mono : StrictMono x
  x_tag_between (i: Fin n) : x i.castSucc ≤ x_tag i ∧ x_tag i ≤ x i.succ

-- The width of the i-th subinterval in a tagged partition.
def TaggedPartition.delta {I: BoundedInterval} {n:ℕ} (P: TaggedPartition I n) (i:Fin n): ℝ :=
 P.x i.succ - P.x i.castSucc

-- The mesh size (supremum of subinterval widths) of a tagged partition.
noncomputable def TaggedPartition.norm {I: BoundedInterval} {n:ℕ} (P: TaggedPartition I n) : ℝ := iSup P.delta

lemma TaggedPartition.sum_delta_eq (P : TaggedPartition I n) : ∑ i : Fin n, P.delta i = I.b - I.a := by
  have h_succ : ∑ i : Fin n, P.x i.succ = (∑ i : Fin (n+1), P.x i) - P.x 0 := by
    have := Fin.sum_univ_succ (λ i : Fin (n+1) => P.x i); linarith
  have h_castSucc : ∑ i : Fin n, P.x i.castSucc = (∑ i : Fin (n+1), P.x i) - P.x (Fin.last n) := by
    have := Fin.sum_univ_castSucc (λ i : Fin (n+1) => P.x i); linarith
  calc
    ∑ i : Fin n, P.delta i = ∑ i : Fin n, (P.x i.succ - P.x i.castSucc) := rfl
    _ = (∑ i : Fin n, P.x i.succ) - (∑ i : Fin n, P.x i.castSucc) := by simp [Finset.sum_sub_distrib]
    _ = ((∑ i : Fin (n+1), P.x i) - P.x 0) - ((∑ i : Fin (n+1), P.x i) - P.x (Fin.last n)) := by rw [h_succ, h_castSucc]
    _ = P.x (Fin.last n) - P.x 0 := by ring
    _ = I.b - I.a := by rw [P.x_end, P.x_start]

-- The Riemann sum of f with respect to a tagged partition: sum of f(tag_i) * delta_i.
def TaggedPartition.RiemannSum {I: BoundedInterval} {n:ℕ} (f: ℝ → ℝ) (P: TaggedPartition I n) : ℝ :=
  ∑ i, f (P.x_tag i) * P.delta i

/-- {given (type := "ℕ") -show}`n` {lean}`Sigma (TaggedPartition I)` is the type of all partitions of {name}`I` with an unspecified number {name}`n` of components.  Here we define what it means to converge to zero in this type. -/
-- A filter on Sigma (TaggedPartition I) converging to zero as the partition norm shrinks.
noncomputable def TaggedPartition.nhds_zero (I: BoundedInterval) : Filter (Sigma (TaggedPartition I)) := Filter.comap (fun P ↦ P.snd.norm) (nhds 0)

-- Riemann integrability: Riemann sums converge to R as the partition norm tends to zero.
def riemann_integral_eq (f: ℝ → ℝ) (I: BoundedInterval) (R: ℝ) : Prop := (TaggedPartition.nhds_zero I).Tendsto (fun P ↦ TaggedPartition.RiemannSum f P.snd) (nhds R)

/-- Construct a uniform partition of {lean}`[a,b]` into {lean}`n` equal pieces with left endpoint tags. -/
noncomputable def TaggedPartition.uniform (I: BoundedInterval) (n: ℕ) (hn: n > 0) (_: I = Icc I.a I.b) (hab: I.a < I.b) : TaggedPartition I n where
  x := fun i => I.a + (I.b - I.a) * (i.val : ℝ) / n
  x_tag := fun i => I.a + (I.b - I.a) * (i.castSucc.val : ℝ) / n
  x_start := by simp
  x_end := by
    show I.a + (I.b - I.a) * ((Fin.last n).val : ℝ) / n = I.b
    rw [Fin.val_last]
    field_simp; linarith
  x_mono i j hij := by
    have h_width_pos : 0 < I.b - I.a := by linarith
    have h_n_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    have : (i.val : ℝ) < (j.val : ℝ) := Nat.cast_lt.mpr hij
    apply add_lt_add_right
    apply div_lt_div_of_pos_right
    · exact mul_lt_mul_of_pos_left this h_width_pos
    · exact h_n_pos
  x_tag_between i := by
    constructor
    · -- i.castSucc.val = i.val
      rfl
    · -- i.castSucc.val ≤ i.succ.val
      have h_width_nonneg : 0 ≤ I.b - I.a := by linarith
      have h_n_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
      show I.a + (I.b - I.a) * (i.castSucc.val : ℝ) / n ≤ I.a + (I.b - I.a) * (i.succ.val : ℝ) / n
      rw [show i.castSucc.val = i.val from rfl, Fin.val_succ]
      apply add_le_add_right
      apply div_le_div_of_nonneg_right
      · apply mul_le_mul_of_nonneg_left _ h_width_nonneg
        norm_num
      · linarith

/-- The norm of a uniform partition is (b-a)/n. -/
lemma TaggedPartition.uniform_norm (I: BoundedInterval) (n: ℕ) (hn: n > 0) (hI: I = Icc I.a I.b) (hab: I.a < I.b) :
    (TaggedPartition.uniform I n hn hI hab).norm = (I.b - I.a) / n := by
  let P := TaggedPartition.uniform I n hn hI hab
  unfold TaggedPartition.norm
  -- All deltas are equal to (b-a)/n
  have h_eq : ∀ i : Fin n, P.delta i = (I.b - I.a) / n := by
    intro i
    unfold TaggedPartition.delta
    show P.x i.succ - P.x i.castSucc = (I.b - I.a) / n
    -- Unfold the definition of P.x from uniform
    show (I.a + (I.b - I.a) * (i.succ.val : ℝ) / n) - (I.a + (I.b - I.a) * (i.castSucc.val : ℝ) / n) = (I.b - I.a) / n
    rw [show i.castSucc.val = i.val from rfl, Fin.val_succ]
    field_simp
    push_cast; ring
  -- The supremum of a constant function is that constant
  have h_bdd : BddAbove (Set.range P.delta) := Set.Finite.bddAbove (Set.finite_range P.delta)
  have h_le : ∀ i, P.delta i ≤ (I.b - I.a) / n := by
    intro i
    rw [h_eq]
  have h_nonempty : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have h_ge : (I.b - I.a) / n ≤ iSup P.delta := by
    have : ∃ i, P.delta i = (I.b - I.a) / n := ⟨⟨0, hn⟩, h_eq ⟨0, hn⟩⟩
    obtain ⟨i, hi⟩ := this
    calc (I.b - I.a) / n = P.delta i := hi.symm
      _ ≤ iSup P.delta := le_ciSup h_bdd i
  have h_le_sup : iSup P.delta ≤ (I.b - I.a) / n := by
    haveI : Nonempty (Fin n) := h_nonempty
    exact ciSup_le h_le
  linarith

/-- For any positive interval and δ > 0, there exists a tagged partition with norm ≤ δ. -/
lemma TaggedPartition.exists_norm_le (I: BoundedInterval) (hI: I = Icc I.a I.b) (hab: I.a < I.b) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (n : ℕ) (P : TaggedPartition I n), P.norm ≤ δ := by
  -- Choose n large enough that (b-a)/n < δ
  obtain ⟨N, hN⟩ := exists_nat_gt ((I.b - I.a) / δ)
  have h_width_pos : 0 < I.b - I.a := by linarith
  have h_ratio_pos : 0 < (I.b - I.a) / δ := div_pos h_width_pos hδ
  have hN_pos : N > 0 := Nat.pos_of_ne_zero (fun h => by
    rw [h] at hN
    simp at hN
    linarith)
  use N, TaggedPartition.uniform I N hN_pos hI hab
  rw [TaggedPartition.uniform_norm]
  -- We have: (b-a)/δ < N, so (b-a) < N*δ, so (b-a)/N < δ
  have : (I.b - I.a) / (N : ℝ) < δ := by
    calc (I.b - I.a) / (N : ℝ)
        < (I.b - I.a) / ((I.b - I.a) / δ) := by
          apply div_lt_div_of_pos_left h_width_pos h_ratio_pos hN
      _ = δ := by field_simp
  linarith

/-- The filter {name}`TaggedPartition.nhds_zero` is non-trivial when the interval has positive length. -/
instance TaggedPartition.nhds_zero_neBot (I: BoundedInterval) (hI: I = Icc I.a I.b) (hab: I.a < I.b) :
    Filter.NeBot (TaggedPartition.nhds_zero I) := by
  unfold TaggedPartition.nhds_zero
  rw [Filter.comap_neBot_iff]
  intro t ht
  -- t is a neighborhood of 0, so it contains some ball around 0
  rw [Metric.mem_nhds_iff] at ht
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := ht
  -- Construct a partition with norm < δ
  obtain ⟨n, P, hP_norm⟩ := TaggedPartition.exists_norm_le I hI hab (δ / 2) (half_pos hδ_pos)
  use ⟨n, P⟩
  apply hδ_sub
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg]
  · calc P.norm ≤ δ / 2 := hP_norm
      _ < δ := half_lt_self hδ_pos
  · -- Show P.norm is nonnegative
    unfold TaggedPartition.norm
    by_cases h_n_zero : n = 0
    · subst h_n_zero
      simp [iSup]
    · have h_n_pos : n > 0 := Nat.pos_of_ne_zero h_n_zero
      let i0 : Fin n := ⟨0, h_n_pos⟩
      have h_delta_nonneg : 0 ≤ P.delta i0 := by
        unfold TaggedPartition.delta
        have h_lt : i0.castSucc < i0.succ := Fin.castSucc_lt_succ
        have h_x_lt : P.x i0.castSucc < P.x i0.succ := P.x_mono h_lt
        linarith
      have h_bdd : BddAbove (Set.range P.delta) := Set.Finite.bddAbove (Set.finite_range P.delta)
      have h_le_sup : P.delta i0 ≤ iSup P.delta := le_ciSup h_bdd i0
      linarith

/-- We enforce {lean}`I` to be closed and nonempty for the definition of Riemann integrability.
    The nonempty constraint ensures meaningful integration and excludes degenerate cases. -/
-- A function is Riemann integrable on a closed interval if Riemann sums converge to some value.
abbrev RiemannIntegrableOn (f: ℝ → ℝ) (I: BoundedInterval) : Prop :=
  I = Icc I.a I.b ∧ I.toSet.Nonempty ∧ ∃ R, riemann_integral_eq f I R

open Classical in
-- The Riemann integral value: the limit of Riemann sums (zero if not integrable).
noncomputable def riemannIntegral (f: ℝ → ℝ) (I: BoundedInterval) : ℝ := if h:RiemannIntegrableOn f I then h.2.2.choose else 0

/-- When an interval has zero length, all Riemann sums equal zero. -/
lemma riemann_sum_eq_zero_of_zero_length {f : ℝ → ℝ} {I : BoundedInterval} (h_len : |I|ₗ = 0)
    {n : ℕ} (P : TaggedPartition I n) : P.RiemannSum f = 0 := by
  unfold TaggedPartition.RiemannSum
  by_cases hn : n = 0
  · -- When n = 0, the sum is empty
    subst hn
    rfl
  · -- When n > 0 and |I| = 0, we derive a contradiction from StrictMono
    exfalso
    have h_n_pos : 0 < n := Nat.pos_of_ne_zero hn
    -- Fin.last n has value n, so 0 < n means 0 < (Fin.last n).val
    have h_last_pos : 0 < (Fin.last n).val := by rw [Fin.val_last]; exact h_n_pos
    -- This means (0 : Fin (n+1)) < Fin.last n as Fin values
    have h_fin_lt : (0 : Fin (n+1)) < Fin.last n := h_last_pos
    have : P.x 0 < P.x (Fin.last n) := P.x_mono h_fin_lt
    rw [P.x_start, P.x_end] at this
    unfold BoundedInterval.length at h_len
    simp at h_len
    linarith

/-- When an interval has zero length and Riemann sums converge to R, then R = 0.
    This requires that the filter is non-trivial ({name}`Filter.NeBot`), which holds when {lean}`I.a = I.b`. -/
lemma riemann_integral_eq_zero_of_zero_length {f : ℝ → ℝ} {I : BoundedInterval} {R : ℝ}
    (h_eq : I.a = I.b) (h_len : |I|ₗ = 0) (hR : riemann_integral_eq f I R) : R = 0 := by
  -- All Riemann sums are 0
  have h_zero : ∀ P : Sigma (TaggedPartition I), P.snd.RiemannSum f = 0 :=
    fun ⟨_, P⟩ => riemann_sum_eq_zero_of_zero_length h_len P
  -- Since all sums are 0, the function is constantly 0
  have h_const : (fun P : Sigma (TaggedPartition I) => P.snd.RiemannSum f) = fun _ => 0 := by
    ext P; exact h_zero P
  -- Rewrite hR using h_const: constant 0 function tends to R
  rw [riemann_integral_eq, h_const] at hR
  -- Constant function 0 also tends to 0
  haveI : Filter.NeBot (TaggedPartition.nhds_zero I) := by
    -- When I.a = I.b, we can construct a partition with n = 0
    -- This shows Sigma (TaggedPartition I) is nonempty, hence filter is NeBot
    let P0 : TaggedPartition I 0 := {
      x := fun _ => I.a
      x_tag := fun i => i.elim0
      x_start := rfl
      x_end := by show I.a = I.b; exact h_eq
      x_mono := fun i j hij => by
        have hi : i = 0 := Fin.eq_zero i
        have hj : j = 0 := Fin.eq_zero j
        rw [hi, hj] at hij
        exact absurd rfl (ne_of_lt hij)
      x_tag_between := fun i => i.elim0
    }
    -- Show the comap filter is NeBot using the nonempty type
    apply Filter.comap_neBot_iff.mpr
    intro s hs
    -- We need to show ∃ a, a.snd.norm ∈ s
    -- The n=0 partition P0 has norm 0 (supremum over empty Fin 0)
    -- Since s ∈ nhds 0 and 0 ∈ s, we can use P0
    use ⟨0, P0⟩
    -- Show P0.norm ∈ s
    -- For n=0, norm = iSup of empty set = 0 ∈ s (since s is nbhd of 0)
    -- P0.norm = 0 because iSup over Fin 0 is 0
    have h_P0_norm : P0.norm = 0 := by
      unfold TaggedPartition.norm
      -- iSup over empty Fin 0 → ℝ equals sSup ∅ = 0
      rw [iSup_of_empty']
      exact Real.sSup_empty
    rw [h_P0_norm]
    exact mem_of_mem_nhds hs
  have h_zero_to_zero : Filter.Tendsto (fun _ : Sigma (TaggedPartition I) => (0 : ℝ)) (TaggedPartition.nhds_zero I) (nhds 0) :=
    tendsto_const_nhds
  -- By uniqueness of limits in Hausdorff spaces (ℝ is Hausdorff)
  exact tendsto_nhds_unique hR h_zero_to_zero

/-- When a nonempty closed interval \[a,b\] has zero length, then a = b. -/
lemma eq_of_length_zero_of_Icc {I : BoundedInterval}
    (hI : I = Icc I.a I.b) (h_len : |I|ₗ = 0) (h_nonempty : I.toSet.Nonempty) : I.a = I.b := by
  -- From zero length, we get I.b ≤ I.a
  have h_ba : I.b ≤ I.a := by
    unfold BoundedInterval.length at h_len
    simp at h_len
    linarith
  -- We need to show I.a ≤ I.b for antisymmetry
  -- Key: When I = Icc I.a I.b, the set is either empty (if I.a > I.b) or a singleton (if I.a = I.b)
  -- Since length is 0, if the set were empty, we'd have issues, but actually we can just use the fact
  -- that for a closed interval to make sense with zero length, we need a = b

  -- Use le_antisymm if we can show I.a ≤ I.b
  by_cases hab : I.a ≤ I.b
  · -- If I.a ≤ I.b, then with I.b ≤ I.a, we get I.a = I.b
    exact le_antisymm hab h_ba
  · -- If ¬(I.a ≤ I.b), then I.a > I.b
    push_neg at hab
    -- When I = Icc I.a I.b with I.a > I.b, we have I.toSet = ∅
    have h_empty : I.toSet = ∅ := by
      rw [hI]
      simp [BoundedInterval.toSet]
      exact Set.Icc_eq_empty (not_le.mpr hab)
    -- But this contradicts the nonempty hypothesis!
    exfalso
    rw [h_empty] at h_nonempty
    exact Set.not_nonempty_empty h_nonempty

/-- Definition 1.1.15 (Riemann integrability) -/
-- For a Riemann integrable function, the Riemann sums converge to the integral value.
lemma riemann_integral_of_integrable {f:ℝ → ℝ} {I: BoundedInterval} (h: RiemannIntegrableOn f I) : riemann_integral_eq f I (riemannIntegral f I) := by
  -- Strategy: Since `h : RiemannIntegrableOn f I` means `∃ R, riemann_integral_eq f I R`,
  -- and `riemannIntegral f I` is defined as `h.2.2.choose` (the witness chosen by Classical.choose),
  -- we need to show that `riemann_integral_eq f I h.2.2.choose`, which is exactly `h.2.2.choose_spec`.
  unfold riemannIntegral
  convert h.2.2.choose_spec using 2
  -- Split on the if condition (which is `RiemannIntegrableOn f I`, true by hypothesis `h`)
  split_ifs
  -- In the `then` branch, we have `h.2.choose = h.2.choose` by reflexivity
  · rfl

/-- Definition 1.1.15 (Riemann integrability) -/
-- Characterization of the Riemann integral: R is the integral iff the Riemann sums converge to R.
lemma riemann_integral_eq_iff_of_integrable {f:ℝ → ℝ} {I: BoundedInterval} (h: RiemannIntegrableOn f I) (R:ℝ): riemann_integral_eq f I R ↔ R = riemannIntegral f I := by
  constructor
  · -- Forward direction: uniqueness of limits in Hausdorff space
    intro hR
    -- We know riemann_integral_eq f I (riemannIntegral f I) from riemann_integral_of_integrable
    have hRI := riemann_integral_of_integrable h
    -- Handle two cases: I.a < I.b or I.a = I.b
    by_cases hab : I.a < I.b
    · -- Case: I.a < I.b (positive length interval)
      -- The filter is non-trivial, so we can apply Hausdorff limit uniqueness
      haveI : Filter.NeBot (TaggedPartition.nhds_zero I) := TaggedPartition.nhds_zero_neBot I h.1 hab
      -- Both Riemann sums converge: one to R, one to riemannIntegral f I
      -- In a Hausdorff space (ℝ is metric hence Hausdorff), limits are unique
      exact tendsto_nhds_unique hR hRI
    · -- Case: ¬(I.a < I.b) means I.a ≥ I.b (zero or negative length interval)
      -- In either case, the length is 0
      have h_len : |I|ₗ = 0 := by
        unfold BoundedInterval.length
        simp
        -- ¬(I.a < I.b) means I.a ≥ I.b, so max(0, I.b - I.a) = 0
        have : I.b ≤ I.a := le_of_not_gt hab
        linarith
      -- When I = Icc I.a I.b and length is 0, we have I.a = I.b
      have h_eq : I.a = I.b := eq_of_length_zero_of_Icc h.1 h_len h.2.1
      -- Both R and riemannIntegral f I equal 0 when length is 0 and I.a = I.b
      have hR_zero : R = 0 := riemann_integral_eq_zero_of_zero_length h_eq h_len hR
      have hRI_zero : riemannIntegral f I = 0 := riemann_integral_eq_zero_of_zero_length h_eq h_len hRI
      -- Therefore R = riemannIntegral f I
      rw [hR_zero, hRI_zero]
  · -- Backward direction: substitution
    intro hRe
    rw [hRe]
    exact riemann_integral_of_integrable h

/-- Definition 1.1.15 (Riemann integrability). -/
-- ε-δ characterization: Riemann sums converge to R iff for all ε > 0, there exists δ > 0 such that partitions with norm ≤ δ have Riemann sums within ε of R.
lemma riemann_integral_eq_iff {f:ℝ → ℝ} {I: BoundedInterval} (R:ℝ): riemann_integral_eq f I R ↔ ∀ ε>0, ∃ δ>0, ∀ n, ∀ P: TaggedPartition I n, P.norm ≤ δ → |P.RiemannSum f - R| ≤ ε := by
  -- Show equivalence between filter convergence and ε-δ definition.
  -- Forward (→): Use `LinearOrderedAddCommGroup.tendsto_nhds` and `Filter.eventually_comap` to extract ε-δ.
  -- Backward (←): Given ε-δ, show filter convergence
  unfold riemann_integral_eq TaggedPartition.nhds_zero
  -- Use LinearOrderedAddCommGroup.tendsto_nhds to characterize filter convergence
  rw [LinearOrderedAddCommGroup.tendsto_nhds]
  -- Use Filter.eventually_comap to relate comap filter to nhds 0
  simp_rw [Filter.eventually_comap]
  constructor
  · -- Forward direction: filter convergence → ε-δ
    intro h_tendsto ε hε
    -- Get eventually condition from filter convergence
    have h_eventually : ∀ᶠ (x : ℝ) in nhds 0, ∀ (a : Sigma (TaggedPartition I)), a.snd.norm = x → |TaggedPartition.RiemannSum f a.snd - R| < ε := h_tendsto ε hε
    -- Extract δ from nhds 0: use Metric.mem_nhds_iff to get a ball
    rw [Metric.eventually_nhds_iff] at h_eventually
    obtain ⟨δ, hδ_pos, hδ_ball⟩ := h_eventually
    -- Use δ/2 to ensure strict inequality, then strengthen to ≤
    use δ / 2, half_pos hδ_pos
    intro n P hP_norm
    -- Show |RiemannSum - R| ≤ ε using the filter condition
    -- First show P.norm < δ (since P.norm ≤ δ/2 < δ)
    have h_norm_lt : P.norm < δ := by
      linarith [hP_norm]
    -- P.norm is nonnegative (each delta is nonnegative by monotonicity)
    have h_norm_nonneg : 0 ≤ P.norm := by
      unfold TaggedPartition.norm
      -- Show that 0 ≤ iSup by showing each delta ≥ 0
      by_cases h_n_empty : n = 0
      · -- If n = 0, the range is empty, so iSup = 0
        subst h_n_empty
        simp [iSup]
      · -- If n > 0, pick any index and show its delta ≥ 0
        have h_n_pos : n > 0 := Nat.pos_of_ne_zero h_n_empty
        -- Construct Fin n element for index 0
        have h_fin_zero : 0 < n := h_n_pos
        let i0 : Fin n := Fin.mk 0 h_fin_zero
        have h_delta_nonneg : 0 ≤ P.delta i0 := by
          unfold TaggedPartition.delta
          -- Show P.x i0.castSucc ≤ P.x i0.succ using strict monotonicity
          have h_lt : i0.castSucc < i0.succ := Fin.castSucc_lt_succ
          have h_x_lt : P.x i0.castSucc < P.x i0.succ := P.x_mono h_lt
          linarith
        -- Show 0 ≤ iSup by showing 0 ≤ some element in the range
        -- The range is bounded above since Fin n is finite
        have h_bdd : BddAbove (Set.range P.delta) := by
          -- Fin n is finite, so the range is finite and bounded
          have h_finite : (Set.range P.delta).Finite := Set.finite_range P.delta
          exact Set.Finite.bddAbove h_finite
        -- Use le_trans: 0 ≤ P.delta i0 ≤ iSup P.delta
        have h_le_sup : P.delta i0 ≤ iSup P.delta := le_ciSup h_bdd i0
        linarith [h_delta_nonneg, h_le_sup]
    -- Apply filter condition: if dist P.norm 0 < δ, then for all P with P.norm = P.norm, |RiemannSum - R| < ε
    -- Note: ⟨n, P⟩.snd.norm = P.norm, and dist P.norm 0 = |P.norm| = P.norm (since nonnegative)
    -- Show dist P.norm 0 < δ
    have h_dist : dist P.norm 0 < δ := by
      rw [Real.dist_eq]
      simp [sub_zero]
      rw [abs_of_nonneg h_norm_nonneg]
      exact h_norm_lt
    -- Apply hδ_ball with P.norm and show ⟨n, P⟩.snd.norm = P.norm
    have h_eq : (⟨n, P⟩ : Sigma (TaggedPartition I)).snd.norm = P.norm := rfl
    have h_applied := hδ_ball h_dist ⟨n, P⟩ h_eq
    -- Convert < to ≤
    linarith
  · -- Backward direction: ε-δ → filter convergence
    intro h_eps_delta ε hε
    -- Use ε/2 to get strict inequality from ≤ condition
    obtain ⟨δ, hδ_pos, hδ⟩ := h_eps_delta (ε / 2) (half_pos hε)
    -- Show eventually condition using Metric.eventually_nhds_iff
    rw [Metric.eventually_nhds_iff]
    use δ, hδ_pos
    -- Show that if |x| < δ and P.norm = x, then |RiemannSum - R| < ε
    intro x hx_abs a hP_eq
    -- Show a.snd.norm ≤ δ
    have hP_norm_le : a.snd.norm ≤ δ := by
      -- Use hP_eq: a.snd.norm = x, and hx_abs: dist x 0 < δ
      -- Convert dist to abs
      rw [Real.dist_eq, sub_zero] at hx_abs
      rw [abs_lt] at hx_abs
      -- Use hP_eq to substitute: a.snd.norm = x, so |a.snd.norm| < δ
      rw [←hP_eq] at hx_abs
      -- a.snd.norm is nonnegative (as partition norm), so |a.snd.norm| = a.snd.norm
      -- Extract n and P from a to show nonnegativity
      have h_norm_nonneg : 0 ≤ a.snd.norm := by
        -- Use the same approach as forward direction
        unfold TaggedPartition.norm
        -- Destructure a to get n as a variable
        cases a with | mk n P =>
        -- Simplify ⟨n, P⟩.snd to P in the goal
        simp
        by_cases h_n_empty : n = 0
        · -- If n = 0, the range is empty, so iSup = 0
          subst h_n_empty
          simp [iSup]
        · have h_n_pos : n > 0 := Nat.pos_of_ne_zero h_n_empty
          have h_fin_zero : 0 < n := h_n_pos
          let i0 : Fin n := Fin.mk 0 h_fin_zero
          have h_delta_nonneg : 0 ≤ P.delta i0 := by
            unfold TaggedPartition.delta
            have h_lt : i0.castSucc < i0.succ := Fin.castSucc_lt_succ
            have h_x_lt : P.x i0.castSucc < P.x i0.succ := P.x_mono h_lt
            linarith
          have h_bdd : BddAbove (Set.range P.delta) := by
            have h_finite : (Set.range P.delta).Finite := Set.finite_range P.delta
            exact Set.Finite.bddAbove h_finite
          have h_le_sup : P.delta i0 ≤ iSup P.delta := le_ciSup h_bdd i0
          linarith [h_delta_nonneg, h_le_sup]
      -- hx_abs is already in the form -δ < a.snd.norm ∧ a.snd.norm < δ from abs_lt
      -- So we can directly use hx_abs.2: a.snd.norm < δ, which implies a.snd.norm ≤ δ
      linarith [hx_abs.2]
    -- Apply ε-δ condition: need to extract n and P from a
    have h_applied := hδ (Sigma.fst a) a.snd hP_norm_le
    linarith

/-- Definition 1.1.15.  (Riemann integrability)  -/
-- Any function is Riemann integrable on a degenerate interval [a,a] with integral zero.
lemma RiemannIntegrable.of_zero_length (f: ℝ → ℝ) {I: BoundedInterval} {a : ℝ} (h: I = Icc a a) : RiemannIntegrableOn f I ∧ riemannIntegral f I = 0 := by
  -- First establish basic facts from h : I = Icc a a
  have ha : I.a = a := by simp [h]
  have hb : I.b = a := by simp [h]
  have h_eq : I.a = I.b := by rw [ha, hb]
  have h_len : |I|ₗ = 0 := by
    unfold BoundedInterval.length
    simp [ha, hb]
  -- Show I = Icc I.a I.b
  have hIcc : I = Icc I.a I.b := by rw [ha, hb]; exact h
  -- Show I.toSet is nonempty (it's {a})
  have h_nonempty : I.toSet.Nonempty := by
    rw [h]
    simp [BoundedInterval.toSet]
  -- Show riemann_integral_eq f I 0 (all Riemann sums are 0, so limit is 0)
  have h_integral_zero : riemann_integral_eq f I 0 := by
    rw [riemann_integral_eq_iff]
    intro ε hε
    use 1, one_pos
    intro n P _
    have h_sum_zero : P.RiemannSum f = 0 := riemann_sum_eq_zero_of_zero_length h_len P
    simp [h_sum_zero]
    linarith
  -- Construct RiemannIntegrableOn
  have h_integrable : RiemannIntegrableOn f I := ⟨hIcc, h_nonempty, 0, h_integral_zero⟩
  constructor
  · exact h_integrable
  · -- Show riemannIntegral f I = 0 using uniqueness
    exact ((riemann_integral_eq_iff_of_integrable h_integrable 0).mp h_integral_zero).symm

/-- Helper: Modify a tagged partition by changing one tag -/
def TaggedPartition.changeTag {I: BoundedInterval} {n:ℕ} (P: TaggedPartition I n)
    (k: Fin n) (t: ℝ) (ht: P.x k.castSucc ≤ t ∧ t ≤ P.x k.succ) : TaggedPartition I n where
  x := P.x
  x_tag := Function.update P.x_tag k t
  x_start := P.x_start
  x_end := P.x_end
  x_mono := P.x_mono
  x_tag_between := fun i => by
    by_cases hik : i = k
    · subst hik; rw [Function.update_self]; exact ht
    · rw [Function.update_of_ne hik]; exact P.x_tag_between i

/-- The Riemann sum difference when changing one tag -/
lemma TaggedPartition.RiemannSum_changeTag_sub {I: BoundedInterval} {n:ℕ} (P: TaggedPartition I n)
    (f: ℝ → ℝ) (k: Fin n) (t: ℝ) (ht: P.x k.castSucc ≤ t ∧ t ≤ P.x k.succ) :
    (P.changeTag k t ht).RiemannSum f - P.RiemannSum f = (f t - f (P.x_tag k)) * P.delta k := by
  -- delta is unchanged by changeTag since x is unchanged
  have h_delta : ∀ i, (P.changeTag k t ht).delta i = P.delta i := fun _ => rfl
  unfold TaggedPartition.RiemannSum
  rw [← Finset.sum_sub_distrib]
  have h_terms : ∀ i, f ((P.changeTag k t ht).x_tag i) * (P.changeTag k t ht).delta i - f (P.x_tag i) * P.delta i =
      if i = k then (f t - f (P.x_tag k)) * P.delta k else 0 := by
    intro i
    rw [h_delta]
    simp only [TaggedPartition.changeTag]
    by_cases hik : i = k
    · subst hik; simp only [Function.update_self, if_true]; ring
    · simp only [Function.update_of_ne hik, hik, if_false]; ring
  conv_lhs => rw [Finset.sum_congr rfl (fun i _ => h_terms i)]
  rw [Finset.sum_ite_eq' Finset.univ k]
  simp

/-- For a uniform partition, delta is constant -/
lemma TaggedPartition.uniform_delta {I: BoundedInterval} {n: ℕ} (hn: n > 0) (hI: I = Icc I.a I.b)
    (hab: I.a < I.b) (i: Fin n) :
    (TaggedPartition.uniform I n hn hI hab).delta i = (I.b - I.a) / n := by
  unfold TaggedPartition.delta TaggedPartition.uniform
  simp only
  rw [Fin.val_succ, show i.castSucc.val = i.val from rfl]
  field_simp
  push_cast; ring

/-- For any x in \[a,b\], find the subinterval index containing x -/
noncomputable def findSubintervalIndex (lo hi : ℝ) (n : ℕ) (hn : n > 0) (x : ℝ) (_hx : lo ≤ x ∧ x ≤ hi) : Fin n :=
  let k := min (Nat.floor ((x - lo) / ((hi - lo) / n))) (n - 1)
  ⟨k, by omega⟩

/-- The found index correctly brackets x -/
lemma findSubintervalIndex_spec (lo hi : ℝ) (n : ℕ) (hn : n > 0) (hlohi : lo < hi) (x : ℝ) (hx : lo ≤ x ∧ x ≤ hi) :
    let k := findSubintervalIndex lo hi n hn x hx
    let Δ := (hi - lo) / n
    lo + k.val * Δ ≤ x ∧ x ≤ lo + (k.val + 1) * Δ := by
  simp only [findSubintervalIndex]
  set Δ := (hi - lo) / n with hΔ_def
  have hΔ_pos : 0 < Δ := div_pos (sub_pos.mpr hlohi) (Nat.cast_pos.mpr hn)
  set k := min (Nat.floor ((x - lo) / Δ)) (n - 1) with hk_def
  constructor
  · -- Lower bound: lo + k * Δ ≤ x
    have h_floor_le : ↑(Nat.floor ((x - lo) / Δ)) * Δ ≤ x - lo := by
      have h_nonneg : 0 ≤ (x - lo) / Δ := div_nonneg (by linarith [hx.1]) (le_of_lt hΔ_pos)
      have h_le : (Nat.floor ((x - lo) / Δ) : ℝ) ≤ (x - lo) / Δ := Nat.floor_le h_nonneg
      calc ↑(Nat.floor ((x - lo) / Δ)) * Δ ≤ (x - lo) / Δ * Δ := by
             apply mul_le_mul_of_nonneg_right h_le (le_of_lt hΔ_pos)
           _ = x - lo := by field_simp
    have h_k_le_floor : k ≤ Nat.floor ((x - lo) / Δ) := Nat.min_le_left _ _
    calc lo + k * Δ ≤ lo + Nat.floor ((x - lo) / Δ) * Δ := by
           apply add_le_add_right
           apply mul_le_mul_of_nonneg_right (Nat.cast_le.mpr h_k_le_floor) (le_of_lt hΔ_pos)
         _ ≤ lo + (x - lo) := by linarith [h_floor_le]
         _ = x := by ring
  · -- Upper bound: x ≤ lo + (k + 1) * Δ
    by_cases h_at_end : x = hi
    · -- If x = hi, then k = n - 1 and (k + 1) * Δ = n * Δ = hi - lo
      have h_ne : hi - lo ≠ 0 := ne_of_gt (sub_pos.mpr hlohi)
      have h_k_eq : k = n - 1 := by
        simp only [hk_def, h_at_end]
        apply Nat.min_eq_right
        have h_ratio : (hi - lo) / Δ = n := by
          rw [hΔ_def]
          field_simp [h_ne]
        rw [h_ratio]
        rw [Nat.floor_natCast (R := ℝ)]
        omega
      rw [h_k_eq]
      have h_cast : (↑(n - 1) + 1 : ℝ) = n := by
        rw [Nat.cast_sub (Nat.one_le_of_lt hn)]
        ring
      rw [h_cast, h_at_end]
      have h_eq : hi = lo + (n : ℝ) * Δ := by
        calc hi = lo + (hi - lo) := by ring
             _ = lo + n * Δ := by rw [hΔ_def]; field_simp [h_ne]
      linarith [h_eq]
    · -- If x < hi, use floor property
      have h_x_lt_hi : x < hi := lt_of_le_of_ne hx.2 h_at_end
      -- When x < hi, floor((x-lo)/Δ) ≤ n - 1, so k = floor
      have h_floor_le_n_sub_1 : Nat.floor ((x - lo) / Δ) ≤ n - 1 := by
        have h_ratio_lt : (x - lo) / Δ < n := by
          rw [div_lt_iff₀ hΔ_pos, hΔ_def]
          field_simp
          linarith
        have h_nonneg : 0 ≤ (x - lo) / Δ := div_nonneg (by linarith [hx.1]) (le_of_lt hΔ_pos)
        have h_floor_lt : Nat.floor ((x - lo) / Δ) < n := (Nat.floor_lt h_nonneg).mpr h_ratio_lt
        omega
      have h_k_eq_floor : k = Nat.floor ((x - lo) / Δ) := by
        simp only [hk_def]
        exact Nat.min_eq_left h_floor_le_n_sub_1
      have h_lt_floor : (x - lo) / Δ < ↑(Nat.floor ((x - lo) / Δ)) + 1 := Nat.lt_floor_add_one _
      have h_lt : x < lo + (↑k + 1) * Δ := by
        calc x = lo + (x - lo) := by ring
             _ = lo + ((x - lo) / Δ) * Δ := by field_simp
             _ < lo + (↑(Nat.floor ((x - lo) / Δ)) + 1) * Δ := by
                 apply add_lt_add_right
                 apply mul_lt_mul_of_pos_right h_lt_floor hΔ_pos
             _ = lo + (↑k + 1) * Δ := by rw [h_k_eq_floor]
      linarith [h_lt]

/-- Definition 1.1.15 -/
theorem RiemannIntegrable.bounded {f: ℝ → ℝ} {I: BoundedInterval} (h: RiemannIntegrableOn f I) : ∃ M, ∀ x ∈ I, |f x| ≤ M := by
  obtain ⟨hIcc, h_nonempty, R, hR⟩ := h
  -- Handle zero-length case separately
  by_cases hab : I.a = I.b
  · -- Zero-length case: I.toSet = {I.a}
    use |f I.a|
    intro x hx
    rw [hIcc] at hx
    simp [BoundedInterval.toSet, Set.mem_Icc] at hx
    have hxa : x = I.a := le_antisymm (by linarith [hx.1, hx.2, hab]) hx.1
    rw [hxa]
  · -- Positive-length case
    push_neg at hab
    have h_lt : I.a < I.b := by
      rw [hIcc] at h_nonempty
      simp only [BoundedInterval.toSet] at h_nonempty
      obtain ⟨x, hax, hxb⟩ := h_nonempty
      by_contra h_not_lt
      push_neg at h_not_lt
      have : I.b < I.a := lt_of_le_of_ne h_not_lt (Ne.symm hab)
      linarith
    -- Use ε-δ characterization with ε = 1
    rw [riemann_integral_eq_iff] at hR
    obtain ⟨δ, hδ_pos, hδ_bound⟩ := hR 1 one_pos
    -- Choose n large enough that (b-a)/n ≤ δ
    have h_width_pos : 0 < I.b - I.a := sub_pos.mpr h_lt
    obtain ⟨N, hN⟩ := exists_nat_gt ((I.b - I.a) / δ)
    have hN_pos : 0 < N := by
      by_contra h_not_pos
      push_neg at h_not_pos
      interval_cases N
      simp at hN
      linarith [div_pos h_width_pos hδ_pos]
    have h_norm_le : (I.b - I.a) / N ≤ δ := by
      have h_ratio_pos : 0 < (I.b - I.a) / δ := div_pos h_width_pos hδ_pos
      have h_N_pos_real : 0 < (N : ℝ) := Nat.cast_pos.mpr hN_pos
      rw [div_le_iff₀ h_N_pos_real]
      have h1 : (I.b - I.a) / δ < N := hN
      have h2 : I.b - I.a < N * δ := by
        rwa [div_lt_iff₀ hδ_pos] at h1
      linarith
    -- Construct uniform partition
    let P := TaggedPartition.uniform I N hN_pos hIcc h_lt
    -- The partition has norm = (b-a)/N ≤ δ
    have h_P_norm : P.norm = (I.b - I.a) / N := TaggedPartition.uniform_norm I N hN_pos hIcc h_lt
    have h_P_norm_le : P.norm ≤ δ := by rw [h_P_norm]; exact h_norm_le
    -- For contradiction, assume f is unbounded
    by_contra h_unbounded
    push_neg at h_unbounded
    -- h_unbounded : ∀ M, ∃ x ∈ I.toSet, M < |f x|
    -- Let K = sum of |f| at partition left endpoints (a bound we'll use)
    let K := ∑ j : Fin N, |f (P.x_tag j)|
    -- Choose large enough M to get contradiction
    let idx0 : Fin N := ⟨0, hN_pos⟩
    let M := K + |f (P.x_tag idx0)| + 3 * N / (I.b - I.a) + |R| + 10
    obtain ⟨x₀, hx₀_in, hx₀_large⟩ := h_unbounded M
    -- Find which subinterval contains x₀
    have hx₀_in' : I.a ≤ x₀ ∧ x₀ ≤ I.b := by
      rw [hIcc] at hx₀_in
      simp [BoundedInterval.toSet, Set.mem_Icc] at hx₀_in
      exact hx₀_in
    let k := findSubintervalIndex I.a I.b N hN_pos x₀ hx₀_in'
    -- x₀ is in the k-th subinterval of the partition
    have h_x₀_in_k := findSubintervalIndex_spec I.a I.b N hN_pos h_lt x₀ hx₀_in'
    -- The uniform partition has x k.castSucc = a + k * Δ
    have h_P_x : ∀ i : Fin (N + 1), P.x i = I.a + (I.b - I.a) * i.val / N := fun i => rfl
    have h_Δ : (I.b - I.a) / N = P.delta ⟨0, hN_pos⟩ := (TaggedPartition.uniform_delta hN_pos hIcc h_lt ⟨0, hN_pos⟩).symm
    -- Show x₀ is in [P.x k.castSucc, P.x k.succ]
    have h_x₀_bracket : P.x k.castSucc ≤ x₀ ∧ x₀ ≤ P.x k.succ := by
      constructor
      · calc P.x k.castSucc = I.a + (I.b - I.a) * k.val / N := h_P_x k.castSucc
             _ = I.a + k.val * ((I.b - I.a) / N) := by ring
             _ ≤ x₀ := h_x₀_in_k.1
      · have h_succ : (k.succ.val : ℝ) = k.val + 1 := by simp [Fin.val_succ]
        calc x₀ ≤ I.a + (k.val + 1) * ((I.b - I.a) / N) := h_x₀_in_k.2
             _ = I.a + (I.b - I.a) * (k.val + 1) / N := by ring
             _ = I.a + (I.b - I.a) * k.succ.val / N := by rw [← h_succ]
             _ = P.x k.succ := (h_P_x k.succ).symm
    -- Construct P₂ by changing tag k to x₀
    let P₂ := P.changeTag k x₀ h_x₀_bracket
    -- P₂ has the same norm as P (same x values, so same deltas)
    have h_P₂_delta_eq : ∀ i, P₂.delta i = P.delta i := fun i => rfl
    have h_P₂_norm_le : P₂.norm ≤ δ := by
      have h_eq : P₂.norm = P.norm := by
        unfold TaggedPartition.norm
        have h_fun_eq : P₂.delta = P.delta := funext h_P₂_delta_eq
        rw [h_fun_eq]
      rw [h_eq]
      exact h_P_norm_le
    -- Get bounds on both Riemann sums
    have h_S₁ : |P.RiemannSum f - R| ≤ 1 := hδ_bound N P h_P_norm_le
    have h_S₂ : |P₂.RiemannSum f - R| ≤ 1 := hδ_bound N P₂ h_P₂_norm_le
    -- The difference of Riemann sums
    have h_diff := TaggedPartition.RiemannSum_changeTag_sub P f k x₀ h_x₀_bracket
    -- |S₂ - S₁| ≤ 2 by triangle inequality
    have h_diff_le_2 : |P₂.RiemannSum f - P.RiemannSum f| ≤ 2 := by
      have h_tri := abs_sub_le (P₂.RiemannSum f) R (P.RiemannSum f)
      -- h_tri : |P₂.RiemannSum f - P.RiemannSum f| ≤ |P₂.RiemannSum f - R| + |R - P.RiemannSum f|
      rw [abs_sub_comm R (P.RiemannSum f)] at h_tri
      calc |P₂.RiemannSum f - P.RiemannSum f|
           ≤ |P₂.RiemannSum f - R| + |P.RiemannSum f - R| := h_tri
         _ ≤ 1 + 1 := add_le_add h_S₂ h_S₁
         _ = 2 := by ring
    -- But |S₂ - S₁| = |f(x₀) - f(tag_k)| * delta_k
    rw [h_diff] at h_diff_le_2
    -- delta_k = (b - a) / N
    have h_delta_k : P.delta k = (I.b - I.a) / N := TaggedPartition.uniform_delta hN_pos hIcc h_lt k
    -- |f(x₀) - f(tag_k)| ≤ 2 / delta_k = 2N / (b - a)
    have h_Δ_pos : 0 < P.delta k := by
      rw [h_delta_k]
      exact div_pos h_width_pos (Nat.cast_pos.mpr hN_pos)
    have h_f_diff : |f x₀ - f (P.x_tag k)| ≤ 2 / P.delta k := by
      have h_eq := abs_mul (f x₀ - f (P.x_tag k)) (P.delta k)
      rw [abs_of_pos h_Δ_pos] at h_eq
      have h_le : |f x₀ - f (P.x_tag k)| * P.delta k ≤ 2 := by rw [← h_eq]; exact h_diff_le_2
      rwa [le_div_iff₀ h_Δ_pos]
    -- |f(x₀)| ≤ |f(tag_k)| + 2N / (b - a)
    have h_f_x₀_bound : |f x₀| ≤ |f (P.x_tag k)| + 2 * N / (I.b - I.a) := by
      have h1 : |f x₀| - |f (P.x_tag k)| ≤ |f x₀ - f (P.x_tag k)| := abs_sub_abs_le_abs_sub _ _
      have h2 : |f x₀ - f (P.x_tag k)| ≤ 2 / P.delta k := h_f_diff
      rw [h_delta_k] at h2
      have h3 : 2 / ((I.b - I.a) / N) = 2 * N / (I.b - I.a) := by field_simp
      rw [h3] at h2
      linarith
    -- But |f(tag_k)| ≤ K (sum includes this term)
    have h_tag_k_le_K : |f (P.x_tag k)| ≤ K := by
      apply Finset.single_le_sum (f := fun j => |f (P.x_tag j)|) (fun j _ => abs_nonneg _) (Finset.mem_univ k)
    -- So |f(x₀)| ≤ K + 2N / (b - a)
    have h_f_x₀_final : |f x₀| ≤ K + 2 * N / (I.b - I.a) := by linarith
    -- But we chose |f(x₀)| > M = K + ... + 3N / (b - a) + ...
    have h_contradiction : M < |f x₀| := hx₀_large
    -- M > K + 2N / (b - a), so |f(x₀)| > K + 2N / (b - a)
    have h_M_lower : K + 2 * N / (I.b - I.a) < M := by
      -- Goal: K + 2*N/(b-a) < K + |f(tag0)| + 3*N/(b-a) + |R| + 10
      -- Simplifies to: 2*N/(b-a) < |f(tag0)| + 3*N/(b-a) + |R| + 10
      -- Which holds since 3*N/(b-a) > 2*N/(b-a) and other terms are nonnegative
      have h_N_div_pos : 0 < (N : ℝ) / (I.b - I.a) := div_pos (Nat.cast_pos.mpr hN_pos) h_width_pos
      have h_abs_nonneg : 0 ≤ |f (P.x_tag idx0)| := abs_nonneg _
      have h_R_nonneg : 0 ≤ |R| := abs_nonneg _
      have h_step1 : K + 2 * N / (I.b - I.a) < K + 3 * N / (I.b - I.a) := by
        have : 2 * (N : ℝ) / (I.b - I.a) < 3 * N / (I.b - I.a) := by
          apply div_lt_div_of_pos_right _ h_width_pos
          have h_N_pos : (0 : ℝ) < N := Nat.cast_pos.mpr hN_pos
          linarith
        linarith
      calc K + 2 * N / (I.b - I.a)
           < K + 3 * N / (I.b - I.a) := h_step1
         _ ≤ K + |f (P.x_tag idx0)| + 3 * N / (I.b - I.a) := by linarith
         _ ≤ K + |f (P.x_tag idx0)| + 3 * N / (I.b - I.a) + |R| := by linarith
         _ < K + |f (P.x_tag idx0)| + 3 * N / (I.b - I.a) + |R| + 10 := by linarith
    linarith

@[ext]
-- A function that is constant on each interval in a partition of I.
structure PiecewiseConstantFunction (I: BoundedInterval) where
  f : ℝ → ℝ
  T : Finset BoundedInterval
  c : T → ℝ
  disjoint: (T : Set BoundedInterval).PairwiseDisjoint BoundedInterval.toSet
  cover : I.toSet = ⋃ J ∈ T, J.toSet
  const : ∀ J:T, ∀ x ∈ J.val, f x = c J

-- Two functions agree if they are equal on the interval I.
abbrev PiecewiseConstantFunction.agreesWith {I: BoundedInterval} (F: PiecewiseConstantFunction I) (f: ℝ → ℝ) : Prop := I.toSet.EqOn f F.f

-- A function is piecewise constant on I if it can be represented as a piecewise constant function.
def PiecewiseConstantOn (f: ℝ → ℝ) (I: BoundedInterval) : Prop := ∃ F: PiecewiseConstantFunction I, F.agreesWith f

-- The integral of a piecewise constant function: sum of (constant value × interval length) over all intervals.
def PiecewiseConstantFunction.integral {I: BoundedInterval} (g: PiecewiseConstantFunction I) : ℝ :=
  ∑ J : g.T, g.c J * |J|ₗ

/-- Helper: Scalar multiplication of a piecewise constant function -/
noncomputable def PiecewiseConstantFunction.smul {I: BoundedInterval} (c: ℝ) (g: PiecewiseConstantFunction I) : PiecewiseConstantFunction I where
  f := c • g.f
  T := g.T
  c := fun J => c * g.c J
  disjoint := g.disjoint
  cover := g.cover
  const := by
    intro J x hx
    have h_const : g.f x = g.c J := g.const J x hx
    simp [h_const, Pi.smul_apply, smul_eq_mul]

/-- Helper: The integral of a scaled piecewise constant function -/
lemma PiecewiseConstantFunction.integral_smul_pcf {I: BoundedInterval} (c: ℝ) (g: PiecewiseConstantFunction I) :
    (PiecewiseConstantFunction.smul c g).integral = c • g.integral := by
  unfold PiecewiseConstantFunction.integral PiecewiseConstantFunction.smul
  simp [smul_eq_mul, Finset.mul_sum, mul_assoc]


private lemma ennreal_ofReal_toReal_eq_max (x : ℝ) : (ENNReal.ofReal x).toReal = max x 0 := by
  by_cases h : 0 ≤ x
  · rw [ENNReal.toReal_ofReal h, max_eq_left h]
  · have h' : x ≤ 0 := by linarith
    rw [max_eq_right h']
    have : ENNReal.ofReal x = 0 := by
      rw [ENNReal.ofReal_eq_zero]; exact h'
    simp [this]

/-- The length of a BoundedInterval equals the Lebesgue measure (volume) of its underlying set. -/
lemma BoundedInterval.length_eq_volume (I : BoundedInterval) : |I|ₗ = (MeasureTheory.volume).real (I.toSet) := by
  cases I with
  | Ioo a b =>
    unfold MeasureTheory.Measure.real
    simp [BoundedInterval.set_Ioo, BoundedInterval.length, Real.volume_Ioo]
    exact ennreal_ofReal_toReal_eq_max (b - a)
  | Icc a b =>
    unfold MeasureTheory.Measure.real
    simp [BoundedInterval.set_Icc, BoundedInterval.length, Real.volume_Icc]
    exact ennreal_ofReal_toReal_eq_max (b - a)
  | Ioc a b =>
    unfold MeasureTheory.Measure.real
    simp [BoundedInterval.set_Ioc, BoundedInterval.length, Real.volume_Ioc]
    exact ennreal_ofReal_toReal_eq_max (b - a)
  | Ico a b =>
    unfold MeasureTheory.Measure.real
    simp [BoundedInterval.set_Ico, BoundedInterval.length, Real.volume_Ico]
    exact ennreal_ofReal_toReal_eq_max (b - a)

/-- Helper: When an interval K is partitioned by pairwise-disjoint subintervals T, its length is the sum. -/
lemma BoundedInterval.length_of_partition (K: BoundedInterval) (T: Finset BoundedInterval)
    (hcover: K.toSet = ⋃ J ∈ T, J.toSet)
    (hdisjoint: (T : Set BoundedInterval).PairwiseDisjoint BoundedInterval.toSet) : |K|ₗ = ∑ J: T, |J.val|ₗ := by
  have h_sum_conv : (∑ J : T, |J.val|ₗ) = ∑ J ∈ T, |J|ₗ := by
    simpa using Finset.sum_attach (s := T) (f := fun (J : BoundedInterval) => |J|ₗ)
  rw [h_sum_conv]
  have h_measurable (J : BoundedInterval) : MeasurableSet (J.toSet) := by
    cases J with
    | Ioo a b => exact measurableSet_Ioo
    | Icc a b => exact measurableSet_Icc
    | Ioc a b => exact measurableSet_Ioc
    | Ico a b => exact measurableSet_Ico
  have h_volume_finite (J : BoundedInterval) : (MeasureTheory.volume : MeasureTheory.Measure ℝ) (J.toSet) ≠ ⊤ := by
    cases J <;> simp
  rw [BoundedInterval.length_eq_volume K, hcover]
  rw [MeasureTheory.measureReal_biUnion_finset hdisjoint (by
    intro J hJ; exact h_measurable J) (by
    intro J hJ; exact h_volume_finite J)]
  simp [BoundedInterval.length_eq_volume]

/-- Each refined subinterval J in T' is contained in some original interval I in S. -/
lemma BoundedInterval.refinement_subset (S: Finset BoundedInterval) (T': Finset BoundedInterval)
    (hdisj: (T' : Set BoundedInterval).PairwiseDisjoint BoundedInterval.toSet)
    (hrefine: ∀ (I' : BoundedInterval), I' ∈ S → ∃ U : Set T', I' = ⋃ J ∈ U, J.val.toSet)
    (hS_nonempty : S.Nonempty)
    (hcover : (⋃ J ∈ T', (J : Set ℝ)) ⊆ (⋃ I ∈ S, (I : Set ℝ))) (J: T') :
    ∃ I ∈ S, J.val.toSet ⊆ I.toSet := by
  by_cases h_nonempty : (J.val.toSet : Set ℝ).Nonempty
  · obtain ⟨x, hx⟩ := h_nonempty
    have hx_cover : x ∈ (⋃ I ∈ S, (I : Set ℝ)) :=
      hcover (Set.mem_iUnion₂.mpr ⟨J.val, J.property, hx⟩)
    obtain ⟨I, hI, hx_I⟩ := Set.mem_iUnion₂.mp hx_cover
    obtain ⟨U, hU⟩ := hrefine I hI
    have hx_U : x ∈ ⋃ K ∈ U, (K.val : Set ℝ) := by
      rw [hU] at hx_I
      exact hx_I
    obtain ⟨K, hK, hx_K⟩ := Set.mem_iUnion₂.mp hx_U
    have h_val_eq : J.val = K.val := by
      by_contra hne
      have h_val_ne : J.val ≠ K.val := hne
      have h_disjoint : Disjoint (J.val.toSet) (K.val.toSet) :=
        hdisj (Finset.mem_coe.mpr J.property) (Finset.mem_coe.mpr K.property) h_val_ne
      have h_inter_empty : (J.val.toSet) ∩ (K.val.toSet) = ∅ :=
        Set.disjoint_iff_inter_eq_empty.mp h_disjoint
      have hx_inter : x ∈ (J.val.toSet) ∩ (K.val.toSet) := ⟨hx, hx_K⟩
      rw [h_inter_empty] at hx_inter
      simp at hx_inter
    have h_sub : K.val.toSet ⊆ I.toSet := by
      rw [hU]
      intro y hy
      exact Set.mem_iUnion₂.mpr ⟨K, hK, hy⟩
    refine ⟨I, hI, ?_⟩
    rw [h_val_eq]
    exact h_sub
  · have h_empty : J.val.toSet = (∅ : Set ℝ) := Set.not_nonempty_iff_eq_empty.mp h_nonempty
    obtain ⟨I, hI⟩ := hS_nonempty
    refine ⟨I, hI, ?_⟩
    rw [h_empty]
    exact Set.empty_subset _

/-- Exercise 1.1.20 (Piecewise constant functions) -/
-- The integral is well-defined: different representations of the same piecewise constant function have the same integral.
theorem PiecewiseConstantFunction.integral_eq (f: ℝ → ℝ) {I: BoundedInterval} (F F': PiecewiseConstantFunction I) (hF: F.agreesWith f) (hF': F'.agreesWith f) : F.integral = F'.integral := by
  let S := F.T ∪ F'.T
  obtain ⟨T, hT_disj, hT_refine⟩ := BoundedInterval.partition S
  have hF_refine : ∀ (K : BoundedInterval), K ∈ F.T → ∃ U : Set (Subtype (· ∈ T)), (K : Set ℝ) = ⋃ J ∈ U, (J.val : Set ℝ) := by
    intro K hK
    exact hT_refine K (by simp [S, hK])
  have hF'_refine : ∀ (K : BoundedInterval), K ∈ F'.T → ∃ U : Set (Subtype (· ∈ T)), (K : Set ℝ) = ⋃ J ∈ U, (J.val : Set ℝ) := by
    intro K hK
    exact hT_refine K (by simp [S, hK])
  choose U hU_cover using hF_refine
  choose U' hU'_cover using hF'_refine
  classical
    let uK (K : BoundedInterval) : Finset BoundedInterval :=
      T.filter (λ J : BoundedInterval => (J : Set ℝ) ⊆ (K : Set ℝ))
    have huK_cover (K : BoundedInterval) (hK : K ∈ F.T) : (K : Set ℝ) = ⋃ J ∈ uK K, (J : Set ℝ) := by
      ext x; constructor
      · intro hx
        rw [hU_cover K hK] at hx
        obtain ⟨J', hJ', hx'⟩ := Set.mem_iUnion₂.mp hx
        have hJ'_sub : (J'.val : Set ℝ) ⊆ (K : Set ℝ) := by
          intro y hy
          rw [hU_cover K hK]
          exact Set.mem_iUnion₂.mpr ⟨J', hJ', hy⟩
        have hJ'_val_mem : J'.val ∈ uK K := by
          apply Finset.mem_filter.mpr
          exact ⟨J'.property, hJ'_sub⟩
        refine Set.mem_iUnion₂.mpr ⟨J'.val, hJ'_val_mem, hx'⟩
      · intro hx
        obtain ⟨J, hJ, hx'⟩ := Set.mem_iUnion₂.mp hx
        have hJ_sub : (J : Set ℝ) ⊆ (K : Set ℝ) := (Finset.mem_filter.mp hJ).2
        exact hJ_sub hx'
    have huK_cover' (K : BoundedInterval) (hK : K ∈ F'.T) : (K : Set ℝ) = ⋃ J ∈ uK K, (J : Set ℝ) := by
      ext x; constructor
      · intro hx
        rw [hU'_cover K hK] at hx
        obtain ⟨J', hJ', hx'⟩ := Set.mem_iUnion₂.mp hx
        have hJ'_sub : (J'.val : Set ℝ) ⊆ (K : Set ℝ) := by
          intro y hy
          rw [hU'_cover K hK]
          exact Set.mem_iUnion₂.mpr ⟨J', hJ', hy⟩
        have hJ'_val_mem : J'.val ∈ uK K := by
          apply Finset.mem_filter.mpr
          exact ⟨J'.property, hJ'_sub⟩
        refine Set.mem_iUnion₂.mpr ⟨J'.val, hJ'_val_mem, hx'⟩
      · intro hx
        obtain ⟨J, hJ, hx'⟩ := Set.mem_iUnion₂.mp hx
        have hJ_sub : (J : Set ℝ) ⊆ (K : Set ℝ) := (Finset.mem_filter.mp hJ).2
        exact hJ_sub hx'
    have hT_sub (K : BoundedInterval) : (uK K : Set BoundedInterval) ⊆ (T : Set BoundedInterval) := by
      intro I hI
      have hI' : I ∈ uK K := hI
      have hI_T : I ∈ T := (Finset.mem_filter.mp hI').1
      exact hI_T
    have huK_disj (K : BoundedInterval) : (uK K : Set BoundedInterval).PairwiseDisjoint BoundedInterval.toSet :=
      hT_disj.subset (hT_sub K)
    have h_length (K : BoundedInterval) (hK : K ∈ F.T) : |K|ₗ = ∑ J : uK K, |J.val|ₗ := by
      rw [BoundedInterval.length_of_partition K (uK K) (huK_cover K hK) (huK_disj K)]
    have h_length' (K : BoundedInterval) (hK : K ∈ F'.T) : |K|ₗ = ∑ J : uK K, |J.val|ₗ := by
      rw [BoundedInterval.length_of_partition K (uK K) (huK_cover' K hK) (huK_disj K)]

    have h_len_set_zero (I : BoundedInterval) (h_empty : (I : Set ℝ) = ∅) : |I|ₗ = 0 := by
      unfold BoundedInterval.length
      have h_ba : I.b ≤ I.a := by
        by_contra! h_lt
        have h_nonempty : (I : Set ℝ).Nonempty := by
          apply Set.Nonempty.mono (Ioo_subset I)
          refine ⟨(I.a + I.b) / 2, ?_⟩
          constructor <;> nlinarith
        exact h_nonempty.ne_empty h_empty
      simp [h_ba]

    have h_term_eq (J : Subtype (· ∈ T)) :
      (∑ K : F.T, (if (J.val : Set ℝ) ⊆ (K.val : Set ℝ) then F.c K else 0)) * |J|ₗ =
      (∑ K' : F'.T, (if (J.val : Set ℝ) ⊆ (K'.val : Set ℝ) then F'.c K' else 0)) * |J|ₗ := by
      by_cases h_zero : |J|ₗ = 0
      · simp [h_zero]
      · have h_nonempty : (J.val : Set ℝ).Nonempty := by
          by_contra h_empty
          have h_len_zero : |J|ₗ = 0 := h_len_set_zero J.val (Set.not_nonempty_iff_eq_empty.mp h_empty)
          exact h_zero h_len_zero
        obtain ⟨x, hx⟩ := h_nonempty
        by_cases h_exists_F : ∃ (K : F.T), (J.val : Set ℝ) ⊆ (K.val : Set ℝ)
        · obtain ⟨K, hK_sub⟩ := h_exists_F
          have hx_I : x ∈ (I : Set ℝ) := by
            rw [F.cover]
            exact Set.mem_iUnion₂.mpr ⟨K.val, K.property, hK_sub hx⟩
          have hx_I' : x ∈ (I : Set ℝ) := hx_I
          rw [F'.cover] at hx_I'
          obtain ⟨K'_B, hK'_mem, hx_K'⟩ := Set.mem_iUnion₂.mp hx_I'
          have hK'_sub : (J.val : Set ℝ) ⊆ (K'_B : Set ℝ) := by
            rw [hU'_cover K'_B hK'_mem] at hx_K'
            obtain ⟨J'', hJ'', hx_J''⟩ := Set.mem_iUnion₂.mp hx_K'
            have hJ_eq : J = J'' := by
              by_contra h_ne
              have h_val_ne : J.val ≠ J''.val := Subtype.val_injective.ne h_ne
              have h_inter_empty : (BoundedInterval.toSet J.val) ∩ (BoundedInterval.toSet J''.val) = ∅ := by
                rw [Set.disjoint_iff_inter_eq_empty.mp ?_]
                exact hT_disj (Finset.mem_coe.mpr J.property) (Finset.mem_coe.mpr J''.property) h_val_ne
              have hx_inter : x ∈ (BoundedInterval.toSet J.val) ∩ (BoundedInterval.toSet J''.val) := ⟨hx, hx_J''⟩
              rw [h_inter_empty] at hx_inter
              simp at hx_inter
            intro y hy
            rw [hU'_cover K'_B hK'_mem]
            have hy_J'' : y ∈ (J''.val : Set ℝ) := by
              subst hJ_eq
              exact hy
            exact Set.mem_iUnion₂.mpr ⟨J'', hJ'', hy_J''⟩
          have h_unique_F : ∀ (K₁ K₂ : F.T), (J.val : Set ℝ) ⊆ (K₁.val : Set ℝ) → (J.val : Set ℝ) ⊆ (K₂.val : Set ℝ) → K₁ = K₂ := by
            intro K₁ K₂ h_sub₁ h_sub₂
            by_contra h_ne
            have h_val_ne : K₁.val ≠ K₂.val := Subtype.val_injective.ne h_ne
            have h_inter_empty : (BoundedInterval.toSet K₁.val) ∩ (BoundedInterval.toSet K₂.val) = ∅ := by
              rw [Set.disjoint_iff_inter_eq_empty.mp ?_]
              exact F.disjoint (Finset.mem_coe.mpr K₁.property) (Finset.mem_coe.mpr K₂.property) h_val_ne
            have hx_in₁ : x ∈ BoundedInterval.toSet K₁.val := h_sub₁ hx
            have hx_in₂ : x ∈ BoundedInterval.toSet K₂.val := h_sub₂ hx
            have hx_inter : x ∈ (BoundedInterval.toSet K₁.val) ∩ (BoundedInterval.toSet K₂.val) := ⟨hx_in₁, hx_in₂⟩
            rw [h_inter_empty] at hx_inter
            simp at hx_inter
          have h_unique_F' : ∀ (K₁ K₂ : F'.T), (J.val : Set ℝ) ⊆ (K₁.val : Set ℝ) → (J.val : Set ℝ) ⊆ (K₂.val : Set ℝ) → K₁ = K₂ := by
            intro K₁ K₂ h_sub₁ h_sub₂
            by_contra h_ne
            have h_val_ne : K₁.val ≠ K₂.val := Subtype.val_injective.ne h_ne
            have h_inter_empty : (BoundedInterval.toSet K₁.val) ∩ (BoundedInterval.toSet K₂.val) = ∅ := by
              rw [Set.disjoint_iff_inter_eq_empty.mp ?_]
              exact F'.disjoint (Finset.mem_coe.mpr K₁.property) (Finset.mem_coe.mpr K₂.property) h_val_ne
            have hx_in₁ : x ∈ BoundedInterval.toSet K₁.val := h_sub₁ hx
            have hx_in₂ : x ∈ BoundedInterval.toSet K₂.val := h_sub₂ hx
            have hx_inter : x ∈ (BoundedInterval.toSet K₁.val) ∩ (BoundedInterval.toSet K₂.val) := ⟨hx_in₁, hx_in₂⟩
            rw [h_inter_empty] at hx_inter
            simp at hx_inter
          have h_const_eq : F.c K = F'.c ⟨K'_B, hK'_mem⟩ := by
            have h_fx : F.f x = f x := (hF hx_I).symm
            have h_f'x : F'.f x = f x := (hF' hx_I).symm
            have h_F_const : F.f x = F.c K := F.const K x (hK_sub hx)
            have h_F'_const : F'.f x = F'.c ⟨K'_B, hK'_mem⟩ := F'.const ⟨K'_B, hK'_mem⟩ x (hK'_sub hx)
            calc
              F.c K = F.f x := (h_F_const.symm)
              _ = f x := h_fx
              _ = F'.f x := (h_f'x.symm)
              _ = F'.c ⟨K'_B, hK'_mem⟩ := h_F'_const
          have h_inner_F : (∑ K : F.T, (if (J.val : Set ℝ) ⊆ (K.val : Set ℝ) then F.c K else 0)) = F.c K := by
            have h_sum_attach : (∑ K : F.T, (if (J.val : Set ℝ) ⊆ (K.val : Set ℝ) then F.c K else 0)) =
              Finset.sum (Finset.attach F.T) (fun (K' : F.T) => if (J.val : Set ℝ) ⊆ (K'.val : Set ℝ) then F.c K' else 0) := by
              simp
            rw [h_sum_attach]
            have h_temp : Finset.sum (Finset.attach F.T) (fun (K' : F.T) => if (J.val : Set ℝ) ⊆ (K'.val : Set ℝ) then F.c K' else 0) =
              (if (J.val : Set ℝ) ⊆ (K.val : Set ℝ) then F.c K else 0) :=
              Finset.sum_eq_single (a := K) (by
                intro K' hK' h_ne
                have h_not_sub : ¬ (J.val : Set ℝ) ⊆ (K'.val : Set ℝ) := by
                  intro h_sub
                  have : K' = K := h_unique_F K' K h_sub hK_sub
                  exact h_ne this
                simp [h_not_sub]
              ) (by
                intro h_not
                exfalso
                exact h_not (by simp))
            simpa [hK_sub] using h_temp
          have h_inner_F' : (∑ K' : F'.T, (if (J.val : Set ℝ) ⊆ (K'.val : Set ℝ) then F'.c K' else 0)) = F'.c ⟨K'_B, hK'_mem⟩ := by
            let a : F'.T := ⟨K'_B, hK'_mem⟩
            have h_sum_attach : (∑ K' : F'.T, (if (J.val : Set ℝ) ⊆ (K'.val : Set ℝ) then F'.c K' else 0)) =
              Finset.sum (Finset.attach F'.T) (fun (K'' : F'.T) => if (J.val : Set ℝ) ⊆ (K''.val : Set ℝ) then F'.c K'' else 0) := by
              simp
            rw [h_sum_attach]
            have h_temp : Finset.sum (Finset.attach F'.T) (fun (K'' : F'.T) => if (J.val : Set ℝ) ⊆ (K''.val : Set ℝ) then F'.c K'' else 0) =
              (if (J.val : Set ℝ) ⊆ (a.val : Set ℝ) then F'.c a else 0) :=
              Finset.sum_eq_single (a := a) (by
                intro K'' hK'' h_ne
                have h_not_sub : ¬ (J.val : Set ℝ) ⊆ (K''.val : Set ℝ) := by
                  intro h_sub
                  have : K'' = a := h_unique_F' K'' a h_sub hK'_sub
                  exact h_ne this
                simp [h_not_sub]
              ) (by
                intro h_not
                exfalso
                exact h_not (by simp))
            have h_cond : (J.val : Set ℝ) ⊆ (a.val : Set ℝ) := hK'_sub
            simpa [h_cond, a] using h_temp
          rw [h_inner_F, h_inner_F', h_const_eq]
        · have h_inner_F_zero : (∑ K : F.T, (if (J.val : Set ℝ) ⊆ (K.val : Set ℝ) then F.c K else 0)) = 0 := by
            apply Finset.sum_eq_zero
            intro K hK
            have h_not_sub : ¬ (J.val : Set ℝ) ⊆ (K.val : Set ℝ) := by
              intro h_sub
              apply h_exists_F
              exact ⟨K, h_sub⟩
            simp [h_not_sub]
          have h_inner_F'_zero : (∑ K' : F'.T, (if (J.val : Set ℝ) ⊆ (K'.val : Set ℝ) then F'.c K' else 0)) = 0 := by
            apply Finset.sum_eq_zero
            intro K' hK'
            have h_not_sub : ¬ (J.val : Set ℝ) ⊆ (K'.val : Set ℝ) := by
              intro h_sub
              have hx_I : x ∈ (I : Set ℝ) := by
                rw [F'.cover]
                exact Set.mem_iUnion₂.mpr ⟨K'.val, K'.property, h_sub hx⟩
              rw [F.cover] at hx_I
              obtain ⟨K_B, hK_B, hx_K⟩ := Set.mem_iUnion₂.mp hx_I
              have hK_B_sub : (J.val : Set ℝ) ⊆ (K_B : Set ℝ) := by
                rw [hU_cover K_B hK_B] at hx_K
                obtain ⟨J'', hJ'', hx_J''⟩ := Set.mem_iUnion₂.mp hx_K
                have hJ_eq : J = J'' := by
                  by_contra h_ne
                  have h_val_ne : J.val ≠ J''.val := Subtype.val_injective.ne h_ne
                  have h_inter_empty : (BoundedInterval.toSet J.val) ∩ (BoundedInterval.toSet J''.val) = ∅ := by
                    rw [Set.disjoint_iff_inter_eq_empty.mp ?_]
                    exact hT_disj (Finset.mem_coe.mpr J.property) (Finset.mem_coe.mpr J''.property) h_val_ne
                  have hx_inter : x ∈ (BoundedInterval.toSet J.val) ∩ (BoundedInterval.toSet J''.val) := ⟨hx, hx_J''⟩
                  rw [h_inter_empty] at hx_inter
                  simp at hx_inter
                intro y hy
                rw [hU_cover K_B hK_B]
                have hy_J'' : y ∈ (J''.val : Set ℝ) := by
                  subst hJ_eq
                  exact hy
                exact Set.mem_iUnion₂.mpr ⟨J'', hJ'', hy_J''⟩
              exact h_exists_F ⟨⟨K_B, hK_B⟩, hK_B_sub⟩
            simp [h_not_sub]
          rw [h_inner_F_zero, h_inner_F'_zero]

    have h_inner_conv (K : F.T) : (∑ J : uK (K.val), F.c K * |J|ₗ) = (∑ J : Subtype (· ∈ T), (if (↑J : Set ℝ) ⊆ (↑(K.val) : Set ℝ) then F.c K * |J|ₗ else 0)) := by
      calc
        (∑ J : uK (K.val), F.c K * |J|ₗ) = Finset.sum (uK (K.val)) (fun J : BoundedInterval => F.c K * |J|ₗ) := by
          simpa using Finset.sum_attach (uK (K.val)) (fun J : BoundedInterval => F.c K * |J|ₗ)
        _ = Finset.sum T (fun J : BoundedInterval => if (J : Set ℝ) ⊆ (K.val : Set ℝ) then F.c K * |J|ₗ else 0) := by
          dsimp [uK]
          simp [Finset.sum_filter]
        _ = (∑ J : Subtype (· ∈ T), (if (↑J : Set ℝ) ⊆ (↑(K.val) : Set ℝ) then F.c K * |J|ₗ else 0)) := by
          simpa using (Finset.sum_attach T (fun J : BoundedInterval => if (J : Set ℝ) ⊆ (K.val : Set ℝ) then F.c K * |J|ₗ else 0)).symm

    have h_inner_conv' (K' : F'.T) : (∑ J : uK (K'.val), F'.c K' * |J|ₗ) = (∑ J : Subtype (· ∈ T), (if (↑J : Set ℝ) ⊆ (↑(K'.val) : Set ℝ) then F'.c K' * |J|ₗ else 0)) := by
      calc
        (∑ J : uK (K'.val), F'.c K' * |J|ₗ) = Finset.sum (uK (K'.val)) (fun J : BoundedInterval => F'.c K' * |J|ₗ) := by
          simpa using Finset.sum_attach (uK (K'.val)) (fun J : BoundedInterval => F'.c K' * |J|ₗ)
        _ = Finset.sum T (fun J : BoundedInterval => if (J : Set ℝ) ⊆ (K'.val : Set ℝ) then F'.c K' * |J|ₗ else 0) := by
          dsimp [uK]
          simp [Finset.sum_filter]
        _ = (∑ J : Subtype (· ∈ T), (if (↑J : Set ℝ) ⊆ (↑(K'.val) : Set ℝ) then F'.c K' * |J|ₗ else 0)) := by
          simpa using (Finset.sum_attach T (fun J : BoundedInterval => if (J : Set ℝ) ⊆ (K'.val : Set ℝ) then F'.c K' * |J|ₗ else 0)).symm

    unfold PiecewiseConstantFunction.integral
    calc
      (∑ K : F.T, F.c K * |K|ₗ) = (∑ K : F.T, F.c K * (∑ J : uK (K.val), |J|ₗ)) := by
        apply Finset.sum_congr rfl
        intro K hK
        rw [h_length (K.val) K.property]
      _ = (∑ K : F.T, ∑ J : uK (K.val), F.c K * |J|ₗ) := by
        simp_rw [Finset.mul_sum]
      _ = (∑ K : F.T, ∑ J : Subtype (· ∈ T), (if (↑J : Set ℝ) ⊆ (↑(K.val) : Set ℝ) then F.c K * |J|ₗ else 0)) := by
        simp_rw [h_inner_conv]
      _ = (∑ J : Subtype (· ∈ T), ∑ K : F.T, (if (↑J : Set ℝ) ⊆ (↑(K.val) : Set ℝ) then F.c K * |J|ₗ else 0)) := by
        rw [Finset.sum_comm]
      _ = (∑ J : Subtype (· ∈ T), ∑ K' : F'.T, (if (↑J : Set ℝ) ⊆ (↑(K'.val) : Set ℝ) then F'.c K' * |J|ₗ else 0)) := by
        apply Finset.sum_congr rfl
        intro J hJ
        calc
          (∑ K : F.T, (if (↑J : Set ℝ) ⊆ (↑(K.val) : Set ℝ) then F.c K * |J|ₗ else 0)) =
            ((∑ K : F.T, (if (↑J : Set ℝ) ⊆ (↑(K.val) : Set ℝ) then F.c K else 0)) * |J|ₗ) := by
            simp [Finset.mul_sum, mul_comm]
          _ = ((∑ K' : F'.T, (if (↑J : Set ℝ) ⊆ (↑(K'.val) : Set ℝ) then F'.c K' else 0)) * |J|ₗ) := by
            rw [h_term_eq J]
          _ = (∑ K' : F'.T, (if (↑J : Set ℝ) ⊆ (↑(K'.val) : Set ℝ) then F'.c K' * |J|ₗ else 0)) := by
            simp [Finset.mul_sum, mul_comm]
      _ = (∑ K' : F'.T, ∑ J : Subtype (· ∈ T), (if (↑J : Set ℝ) ⊆ (↑(K'.val) : Set ℝ) then F'.c K' * |J|ₗ else 0)) := by
        rw [Finset.sum_comm]
      _ = (∑ K' : F'.T, ∑ J : uK (K'.val), F'.c K' * |J|ₗ) := by
        simp_rw [h_inner_conv']
      _ = (∑ K' : F'.T, F'.c K' * (∑ J : uK (K'.val), |J|ₗ)) := by
        simp_rw [Finset.mul_sum]
      _ = (∑ K' : F'.T, F'.c K' * |K'.val|ₗ) := by
        apply Finset.sum_congr rfl
        intro K' hK'
        rw [h_length' (K'.val) K'.property]

-- The integral of a piecewise constant function on I.
noncomputable def PiecewiseConstantOn.integral (f: ℝ → ℝ) {I: BoundedInterval} (h: PiecewiseConstantOn f I) : ℝ := h.choose.integral

/-- Exercise 1.1.20 (Piecewise constant functions) -/
-- The integral of a piecewise constant function equals the integral of any of its representations.
theorem PiecewiseConstantOn.integral_eq (f: ℝ → ℝ) {I: BoundedInterval} (h: PiecewiseConstantOn f I) (F: PiecewiseConstantFunction I) (hF: F.agreesWith f) : h.integral = F.integral := by
  exact PiecewiseConstantFunction.integral_eq f h.choose F h.choose_spec hF

/-- Exercise 1.1.21 (a) (Linearity of the piecewise constant integral) -/
-- A scalar multiple of a piecewise constant function is piecewise constant.
theorem PiecewiseConstantOn.smul {I: BoundedInterval} (c:ℝ) {f: ℝ → ℝ} (h: PiecewiseConstantOn f I) : PiecewiseConstantOn (c • f) I := by
  rcases h with ⟨F, hF⟩
  set cvals : F.T → ℝ := fun J => c * F.c J with hcvals
  refine ⟨{
    f := c • F.f
    T := F.T
    c := cvals
    disjoint := F.disjoint
    cover := F.cover
    const := by
      intro J x hx
      have hconst := F.const J x hx
      simp [hcvals, hconst, Pi.smul_apply, smul_eq_mul]
  }, ?_⟩
  intro x hx
  have hF' := hF hx
  simp [hF', Pi.smul_apply, smul_eq_mul]

/-- Exercise 1.1.21 (a) (Linearity of the piecewise constant integral) -/
-- The integral is linear: integral(c * f) = c * integral(f).
theorem PiecewiseConstantFunction.integral_smul {I:BoundedInterval} (c:ℝ) {f: ℝ → ℝ} (h: PiecewiseConstantOn f I) : (PiecewiseConstantOn.smul c h).integral = c • h.integral := by
  have hF : h.choose.agreesWith f := h.choose_spec
  have hsmul : (PiecewiseConstantOn.smul c h).integral = (PiecewiseConstantFunction.smul c h.choose).integral :=
    PiecewiseConstantOn.integral_eq (c • f) (PiecewiseConstantOn.smul c h) (PiecewiseConstantFunction.smul c h.choose) (by
      intro x hx
      have hF' := hF hx
      simp [PiecewiseConstantFunction.agreesWith, PiecewiseConstantFunction.smul, hF', Pi.smul_apply])
  rw [hsmul]
  have hintegral : h.integral = h.choose.integral := rfl
  rw [hintegral]
  exact PiecewiseConstantFunction.integral_smul_pcf c h.choose

/-- Exercise 1.1.21 (a) (Linearity of the piecewise constant integral) -/
-- The sum of two piecewise constant functions is piecewise constant.
theorem PiecewiseConstantOn.add {I: BoundedInterval} {f g: ℝ → ℝ} (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) : PiecewiseConstantOn (f + g) I := by
  rcases hf with ⟨F, hF⟩
  rcases hg with ⟨G, hG⟩
  let pairs := Finset.product F.T G.T
  let T := Finset.image (λ (p : BoundedInterval × BoundedInterval) => p.1 ∩ p.2) pairs
  have h_disjoint : (T : Set BoundedInterval).PairwiseDisjoint BoundedInterval.toSet := by
    intro A hA B hB h_ne
    rcases Finset.mem_image.mp (Finset.mem_coe.mp hA) with ⟨p, hpA, hpA_eq⟩
    rcases p with ⟨K₁, K'₁⟩
    rcases Finset.mem_image.mp (Finset.mem_coe.mp hB) with ⟨q, hpB, hpB_eq⟩
    rcases q with ⟨K₂, K'₂⟩
    have hA_eq : A = (K₁ ∩ K'₁ : BoundedInterval) := hpA_eq.symm
    have hB_eq : B = (K₂ ∩ K'₂ : BoundedInterval) := hpB_eq.symm
    rcases Finset.mem_product.mp hpA with ⟨hK₁, hK'₁⟩
    rcases Finset.mem_product.mp hpB with ⟨hK₂, hK'₂⟩
    by_cases hK_eq : K₁ = K₂
    · subst hK_eq
      have hK'_ne : K'₁ ≠ K'₂ := by
        intro h_eq
        apply h_ne
        calc
          A = (K₁ ∩ K'₁ : BoundedInterval) := hA_eq
          _ = (K₁ ∩ K'₂ : BoundedInterval) := by simp [h_eq]
          _ = B := by symm; exact hB_eq
      have h_disj_G : Disjoint ((K'₁ : BoundedInterval).toSet) ((K'₂ : BoundedInterval).toSet) :=
        G.disjoint (Finset.mem_coe.mpr hK'₁) (Finset.mem_coe.mpr hK'₂) hK'_ne
      have h_empty : (A.toSet ∩ B.toSet) = ∅ := by
        calc
          A.toSet ∩ B.toSet = ((K₁ : Set ℝ) ∩ (K'₁ : Set ℝ)) ∩ ((K₁ : Set ℝ) ∩ (K'₂ : Set ℝ)) := by
            simp [hA_eq, hB_eq, BoundedInterval.inter_eq]
          _ = ∅ := by
            apply Set.eq_empty_iff_forall_notMem.mpr
            intro x hx
            rw [Set.mem_inter_iff] at hx
            rcases hx with ⟨hx_left, hx_right⟩
            rw [Set.mem_inter_iff] at hx_left hx_right
            rcases hx_left with ⟨hx1, hx2⟩
            rcases hx_right with ⟨hx3, hx4⟩
            have hx_cap : x ∈ (K'₁ : Set ℝ) ∩ (K'₂ : Set ℝ) := ⟨hx2, hx4⟩
            have h_cap_empty : (K'₁ : Set ℝ) ∩ (K'₂ : Set ℝ) = ∅ :=
              Set.disjoint_iff_inter_eq_empty.mp h_disj_G
            rw [h_cap_empty] at hx_cap
            simp at hx_cap
      exact Set.disjoint_iff_inter_eq_empty.mpr h_empty
    · have h_disj_F : Disjoint ((K₁ : BoundedInterval).toSet) ((K₂ : BoundedInterval).toSet) :=
        F.disjoint (Finset.mem_coe.mpr hK₁) (Finset.mem_coe.mpr hK₂) hK_eq
      have h_empty : (A.toSet ∩ B.toSet) = ∅ := by
        calc
          A.toSet ∩ B.toSet = ((K₁ : Set ℝ) ∩ (K'₁ : Set ℝ)) ∩ ((K₂ : Set ℝ) ∩ (K'₂ : Set ℝ)) := by
            simp [hA_eq, hB_eq, BoundedInterval.inter_eq]
          _ = ∅ := by
            apply Set.eq_empty_iff_forall_notMem.mpr
            intro x hx
            rw [Set.mem_inter_iff] at hx
            rcases hx with ⟨hx_left, hx_right⟩
            rw [Set.mem_inter_iff] at hx_left hx_right
            rcases hx_left with ⟨hx1, hx2⟩
            rcases hx_right with ⟨hx3, hx4⟩
            have hx_cap : x ∈ (K₁ : Set ℝ) ∩ (K₂ : Set ℝ) := ⟨hx1, hx3⟩
            have h_cap_empty : (K₁ : Set ℝ) ∩ (K₂ : Set ℝ) = ∅ :=
              Set.disjoint_iff_inter_eq_empty.mp h_disj_F
            rw [h_cap_empty] at hx_cap
            simp at hx_cap
      exact Set.disjoint_iff_inter_eq_empty.mpr h_empty
  have h_cover : I.toSet = ⋃ J ∈ T, J.toSet := by
    apply Set.Subset.antisymm
    · intro x hx
      have hx_F : x ∈ ⋃ K ∈ F.T, (K : Set ℝ) := by
        rw [← F.cover]; exact hx
      obtain ⟨K, hK, hx_K⟩ := Set.mem_iUnion₂.mp hx_F
      have hx_G : x ∈ ⋃ K' ∈ G.T, (K' : Set ℝ) := by
        rw [← G.cover]; exact hx
      obtain ⟨K', hK', hx_K'⟩ := Set.mem_iUnion₂.mp hx_G
      have h_mem_pairs : (K, K') ∈ pairs := Finset.mem_product.mpr ⟨hK, hK'⟩
      have h_mem_T : K ∩ K' ∈ T := by
        apply Finset.mem_image.mpr
        exact ⟨(K, K'), h_mem_pairs, rfl⟩
      refine Set.mem_iUnion₂.mpr ⟨K ∩ K', h_mem_T, ?_⟩
      simpa [BoundedInterval.inter_eq] using ⟨hx_K, hx_K'⟩
    · intro x hx
      obtain ⟨J, hJ, hx_J⟩ := Set.mem_iUnion₂.mp hx
      rcases Finset.mem_image.mp hJ with ⟨p, hp, hp_eq⟩
      rcases p with ⟨K, K'⟩
      have hp_eq' : K ∩ K' = J := hp_eq
      rw [← hp_eq'] at hx_J
      have hx_K : x ∈ (K : Set ℝ) := by
        have hx_inter : x ∈ (K : Set ℝ) ∩ (K' : Set ℝ) := by
          simpa [BoundedInterval.inter_eq] using hx_J
        exact hx_inter.1
      rw [F.cover]
      exact Set.mem_iUnion₂.mpr ⟨K, (Finset.mem_product.mp hp).1, hx_K⟩
  have h_mem_image_J (J : T) : ∃ (p : BoundedInterval × BoundedInterval), p.1 ∈ F.T ∧ p.2 ∈ G.T ∧ J.val = p.1 ∩ p.2 := by
    rcases Finset.mem_image.mp J.property with ⟨p, hp, hp_eq⟩
    rcases Finset.mem_product.mp hp with ⟨hK, hK'⟩
    exact ⟨p, hK, hK', hp_eq.symm⟩
  let new_c : T → ℝ := λ J =>
    let h := h_mem_image_J J
    let p := h.choose
    have hp_F : p.1 ∈ F.T := (h.choose_spec).1
    have hp_G : p.2 ∈ G.T := (h.choose_spec).2.1
    have hp_eq : J.val = p.1 ∩ p.2 := (h.choose_spec).2.2
    F.c ⟨p.1, hp_F⟩ + G.c ⟨p.2, hp_G⟩
  have h_const : ∀ (J : T), ∀ x ∈ (J.val : Set ℝ), (f + g) x = new_c J := by
    intro J x hx
    let h := h_mem_image_J J
    let p := h.choose
    have hp_F : p.1 ∈ F.T := (h.choose_spec).1
    have hp_G : p.2 ∈ G.T := (h.choose_spec).2.1
    have hp_eq : J.val = p.1 ∩ p.2 := (h.choose_spec).2.2
    set K := p.1 with hK_def
    set K' := p.2 with hK'_def
    have hK_F : K ∈ F.T := hp_F
    have hK'_G : K' ∈ G.T := hp_G
    have hx_J_set : x ∈ (K : Set ℝ) ∩ (K' : Set ℝ) := by
      simpa [hp_eq, BoundedInterval.inter_eq] using hx
    have hx_K : x ∈ (K : Set ℝ) := hx_J_set.1
    have hx_K' : x ∈ (K' : Set ℝ) := hx_J_set.2
    have hx_I : x ∈ I.toSet := by
      rw [h_cover]
      exact Set.mem_iUnion₂.mpr ⟨J.val, J.property, hx⟩
    have h_fx : f x = F.f x := hF hx_I
    have h_gx : g x = G.f x := hG hx_I
    have h_F_const : F.f x = F.c ⟨K, hK_F⟩ := F.const ⟨K, hK_F⟩ x hx_K
    have h_G_const : G.f x = G.c ⟨K', hK'_G⟩ := G.const ⟨K', hK'_G⟩ x hx_K'
    calc
      (f + g) x = f x + g x := rfl
      _ = F.f x + G.f x := by simp [h_fx, h_gx]
      _ = F.c ⟨K, hK_F⟩ + G.c ⟨K', hK'_G⟩ := by simp [h_F_const, h_G_const]
      _ = new_c J := by dsimp [new_c, hK_def, hK'_def]
  refine ⟨{
    f := f + g
    T := T
    c := new_c
    disjoint := h_disjoint
    cover := h_cover
    const := h_const
  }, ?_⟩
  intro x hx
  rfl

/-- Exercise 1.1.21 (a) (Linearity of the piecewise constant integral) -/
-- The integral is linear: integral(f + g) = integral(f) + integral(g).
theorem PiecewiseConstantFunction.integral_add {I: BoundedInterval} {f g: ℝ → ℝ} (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) : (hf.add hg).integral = hf.integral + hg.integral := by
  let F := hf.choose
  let G := hg.choose
  have hF_agrees : F.agreesWith f := hf.choose_spec
  have hG_agrees : G.agreesWith g := hg.choose_spec
  let pairs := Finset.product F.T G.T
  let T := Finset.image (λ (p : BoundedInterval × BoundedInterval) => p.1 ∩ p.2) pairs
  have h_disjoint : (T : Set BoundedInterval).PairwiseDisjoint BoundedInterval.toSet := by
    intro A hA B hB h_ne
    rcases Finset.mem_image.mp (Finset.mem_coe.mp hA) with ⟨p, hpA, hpA_eq⟩
    rcases p with ⟨K₁, K'₁⟩
    rcases Finset.mem_image.mp (Finset.mem_coe.mp hB) with ⟨q, hpB, hpB_eq⟩
    rcases q with ⟨K₂, K'₂⟩
    have hA_eq : A = (K₁ ∩ K'₁ : BoundedInterval) := hpA_eq.symm
    have hB_eq : B = (K₂ ∩ K'₂ : BoundedInterval) := hpB_eq.symm
    rcases Finset.mem_product.mp hpA with ⟨hK₁, hK'₁⟩
    rcases Finset.mem_product.mp hpB with ⟨hK₂, hK'₂⟩
    by_cases hK_eq : K₁ = K₂
    · subst hK_eq
      have hK'_ne : K'₁ ≠ K'₂ := by
        intro h_eq
        apply h_ne
        calc
          A = (K₁ ∩ K'₁ : BoundedInterval) := hA_eq
          _ = (K₁ ∩ K'₂ : BoundedInterval) := by simp [h_eq]
          _ = B := by symm; exact hB_eq
      have h_disj_G : Disjoint ((K'₁ : BoundedInterval).toSet) ((K'₂ : BoundedInterval).toSet) :=
        G.disjoint (Finset.mem_coe.mpr hK'₁) (Finset.mem_coe.mpr hK'₂) hK'_ne
      have h_empty : (A.toSet ∩ B.toSet) = ∅ := by
        calc
          A.toSet ∩ B.toSet = ((K₁ : Set ℝ) ∩ (K'₁ : Set ℝ)) ∩ ((K₁ : Set ℝ) ∩ (K'₂ : Set ℝ)) := by
            simp [hA_eq, hB_eq, BoundedInterval.inter_eq]
          _ = ∅ := by
            apply Set.eq_empty_iff_forall_notMem.mpr
            intro x hx
            rw [Set.mem_inter_iff] at hx
            rcases hx with ⟨hx_left, hx_right⟩
            rw [Set.mem_inter_iff] at hx_left hx_right
            rcases hx_left with ⟨hx1, hx2⟩
            rcases hx_right with ⟨hx3, hx4⟩
            have hx_cap : x ∈ (K'₁ : Set ℝ) ∩ (K'₂ : Set ℝ) := ⟨hx2, hx4⟩
            have h_cap_empty : (K'₁ : Set ℝ) ∩ (K'₂ : Set ℝ) = ∅ :=
              Set.disjoint_iff_inter_eq_empty.mp h_disj_G
            rw [h_cap_empty] at hx_cap
            simp at hx_cap
      exact Set.disjoint_iff_inter_eq_empty.mpr h_empty
    · have h_disj_F : Disjoint ((K₁ : BoundedInterval).toSet) ((K₂ : BoundedInterval).toSet) :=
        F.disjoint (Finset.mem_coe.mpr hK₁) (Finset.mem_coe.mpr hK₂) hK_eq
      have h_empty : (A.toSet ∩ B.toSet) = ∅ := by
        calc
          A.toSet ∩ B.toSet = ((K₁ : Set ℝ) ∩ (K'₁ : Set ℝ)) ∩ ((K₂ : Set ℝ) ∩ (K'₂ : Set ℝ)) := by
            simp [hA_eq, hB_eq, BoundedInterval.inter_eq]
          _ = ∅ := by
            apply Set.eq_empty_iff_forall_notMem.mpr
            intro x hx
            rw [Set.mem_inter_iff] at hx
            rcases hx with ⟨hx_left, hx_right⟩
            rw [Set.mem_inter_iff] at hx_left hx_right
            rcases hx_left with ⟨hx1, hx2⟩
            rcases hx_right with ⟨hx3, hx4⟩
            have hx_cap : x ∈ (K₁ : Set ℝ) ∩ (K₂ : Set ℝ) := ⟨hx1, hx3⟩
            have h_cap_empty : (K₁ : Set ℝ) ∩ (K₂ : Set ℝ) = ∅ :=
              Set.disjoint_iff_inter_eq_empty.mp h_disj_F
            rw [h_cap_empty] at hx_cap
            simp at hx_cap
      exact Set.disjoint_iff_inter_eq_empty.mpr h_empty
  have h_cover : I.toSet = ⋃ J ∈ T, J.toSet := by
    apply Set.Subset.antisymm
    · intro x hx
      have hx_F : x ∈ ⋃ K ∈ F.T, (K : Set ℝ) := by
        rw [← F.cover]; exact hx
      obtain ⟨K, hK, hx_K⟩ := Set.mem_iUnion₂.mp hx_F
      have hx_G : x ∈ ⋃ K' ∈ G.T, (K' : Set ℝ) := by
        rw [← G.cover]; exact hx
      obtain ⟨K', hK', hx_K'⟩ := Set.mem_iUnion₂.mp hx_G
      have h_mem_pairs : (K, K') ∈ pairs := Finset.mem_product.mpr ⟨hK, hK'⟩
      have h_mem_T : K ∩ K' ∈ T := by
        apply Finset.mem_image.mpr
        exact ⟨(K, K'), h_mem_pairs, rfl⟩
      refine Set.mem_iUnion₂.mpr ⟨K ∩ K', h_mem_T, ?_⟩
      simpa [BoundedInterval.inter_eq] using ⟨hx_K, hx_K'⟩
    · intro x hx
      obtain ⟨J, hJ, hx_J⟩ := Set.mem_iUnion₂.mp hx
      rcases Finset.mem_image.mp hJ with ⟨p, hp, hp_eq⟩
      rcases p with ⟨K, K'⟩
      have hp_eq' : K ∩ K' = J := hp_eq
      rw [← hp_eq'] at hx_J
      have hx_K : x ∈ (K : Set ℝ) := by
        have hx_inter : x ∈ (K : Set ℝ) ∩ (K' : Set ℝ) := by
          simpa [BoundedInterval.inter_eq] using hx_J
        exact hx_inter.1
      rw [F.cover]
      exact Set.mem_iUnion₂.mpr ⟨K, (Finset.mem_product.mp hp).1, hx_K⟩
  have h_mem_image_J (J : T) : ∃ (p : BoundedInterval × BoundedInterval), p.1 ∈ F.T ∧ p.2 ∈ G.T ∧ J.val = p.1 ∩ p.2 := by
    rcases Finset.mem_image.mp J.property with ⟨p, hp, hp_eq⟩
    rcases Finset.mem_product.mp hp with ⟨hK, hK'⟩
    exact ⟨p, hK, hK', hp_eq.symm⟩
  let p_of_J (J : T) : BoundedInterval × BoundedInterval := (h_mem_image_J J).choose
  have hp_J_spec (J : T) : (p_of_J J).1 ∈ F.T ∧ (p_of_J J).2 ∈ G.T ∧ J.val = (p_of_J J).1 ∩ (p_of_J J).2 :=
    (h_mem_image_J J).choose_spec
  let chooseF (J : T) : F.T := ⟨(p_of_J J).1, (hp_J_spec J).1⟩
  let chooseG (J : T) : G.T := ⟨(p_of_J J).2, (hp_J_spec J).2.1⟩
  have h_choose_val (J : T) : J.val = (chooseF J).val ∩ (chooseG J).val := by
    simpa [chooseF, chooseG] using (hp_J_spec J).2.2
  have h_J_sub_K (J : T) : J.val.toSet ⊆ (chooseF J).val.toSet := by
    rw [h_choose_val J, BoundedInterval.inter_eq]
    apply Set.inter_subset_left
  have h_J_sub_K' (J : T) : J.val.toSet ⊆ (chooseG J).val.toSet := by
    rw [h_choose_val J, BoundedInterval.inter_eq]
    apply Set.inter_subset_right
  let SumF : PiecewiseConstantFunction I := {
    f := f
    T := T
    c := λ J => F.c (chooseF J)
    disjoint := h_disjoint
    cover := h_cover
    const := by
      intro J x hx
      have hx_I : x ∈ I.toSet := by
        rw [h_cover]
        exact Set.mem_iUnion₂.mpr ⟨J.val, J.property, hx⟩
      have hx_K : x ∈ (chooseF J).val.toSet := h_J_sub_K J hx
      calc
        f x = F.f x := hF_agrees hx_I
        _ = F.c (chooseF J) := F.const (chooseF J) x hx_K
  }
  let SumG : PiecewiseConstantFunction I := {
    f := g
    T := T
    c := λ J => G.c (chooseG J)
    disjoint := h_disjoint
    cover := h_cover
    const := by
      intro J x hx
      have hx_I : x ∈ I.toSet := by
        rw [h_cover]
        exact Set.mem_iUnion₂.mpr ⟨J.val, J.property, hx⟩
      have hx_K' : x ∈ (chooseG J).val.toSet := h_J_sub_K' J hx
      calc
        g x = G.f x := hG_agrees hx_I
        _ = G.c (chooseG J) := G.const (chooseG J) x hx_K'
  }
  let Sum : PiecewiseConstantFunction I := {
    f := f + g
    T := T
    c := λ J => F.c (chooseF J) + G.c (chooseG J)
    disjoint := h_disjoint
    cover := h_cover
    const := by
      intro J x hx
      have hx_I : x ∈ I.toSet := by
        rw [h_cover]
        exact Set.mem_iUnion₂.mpr ⟨J.val, J.property, hx⟩
      have hx_K : x ∈ (chooseF J).val.toSet := h_J_sub_K J hx
      have hx_K' : x ∈ (chooseG J).val.toSet := h_J_sub_K' J hx
      calc
        (f + g) x = f x + g x := rfl
        _ = F.f x + G.f x := by simp [hF_agrees hx_I, hG_agrees hx_I]
        _ = F.c (chooseF J) + G.c (chooseG J) := by
          simp [F.const (chooseF J) x hx_K, G.const (chooseG J) x hx_K']
  }
  have hSumF_agrees : SumF.agreesWith f := by intro x hx; rfl
  have hSumG_agrees : SumG.agreesWith g := by intro x hx; rfl
  have hSum_agrees : Sum.agreesWith (f + g) := by intro x hx; rfl
  have hF_int_eq : F.integral = SumF.integral :=
    PiecewiseConstantFunction.integral_eq f F SumF hF_agrees hSumF_agrees
  have hG_int_eq : G.integral = SumG.integral :=
    PiecewiseConstantFunction.integral_eq g G SumG hG_agrees hSumG_agrees
  have hSum_int_eq : (hf.add hg).integral = Sum.integral :=
    PiecewiseConstantOn.integral_eq (f + g) (hf.add hg) Sum hSum_agrees
  have h_sum_eq : Sum.integral = SumF.integral + SumG.integral := by
    unfold PiecewiseConstantFunction.integral
    calc
      (∑ J : Sum.T, Sum.c J * |J|ₗ) = (∑ J : T, (F.c (chooseF J) + G.c (chooseG J)) * |J|ₗ) := rfl
      _ = (∑ J : T, (F.c (chooseF J) * |J|ₗ + G.c (chooseG J) * |J|ₗ)) := by
        refine Finset.sum_congr rfl fun J hJ => ?_
        ring
      _ = (∑ J : T, F.c (chooseF J) * |J|ₗ) + (∑ J : T, G.c (chooseG J) * |J|ₗ) := by
        simp [Finset.sum_add_distrib]
      _ = (∑ J : SumF.T, SumF.c J * |J|ₗ) + (∑ J : SumG.T, SumG.c J * |J|ₗ) := rfl
  calc
    (hf.add hg).integral = Sum.integral := hSum_int_eq
    _ = SumF.integral + SumG.integral := h_sum_eq
    _ = F.integral + G.integral := by rw [hF_int_eq, hG_int_eq]
    _ = hf.integral + hg.integral := rfl




/-- Exercise 1.1.21 (c) (Piecewise constant integral of indicator functions) -/
-- The indicator function of an elementary set is piecewise constant.
theorem PiecewiseConstantOn.indicator_of_elem (I: BoundedInterval) {E:Set ℝ} (hE: IsElementary (Real.equiv_EuclideanSpace' '' E) ) : PiecewiseConstantOn E.indicator' I := by
  rcases hE with ⟨S, hS⟩
  let intervals : Finset BoundedInterval := S.image (λ (B : Box 1) => B.side 0)
  have hE_union : E = ⋃ J ∈ intervals, (J : Set ℝ) := by
    ext x; constructor
    · intro hx
      have hx_image : Real.equiv_EuclideanSpace' x ∈ Real.equiv_EuclideanSpace' '' E := ⟨x, hx, rfl⟩
      rw [hS] at hx_image
      rcases Set.mem_iUnion₂.mp hx_image with ⟨B, hB, hx_box⟩
      have hx_side : x ∈ (B.side 0 : Set ℝ) := by
        have h0 := (Box.mem_toSet.mp hx_box) 0
        simpa using h0
      apply Set.mem_iUnion₂.mpr
      refine ⟨B.side 0, ?_, hx_side⟩
      apply Finset.mem_image.mpr
      exact ⟨B, hB, rfl⟩
    · intro hx
      rcases Set.mem_iUnion₂.mp hx with ⟨J, hJ, hx⟩
      have hJ_finset : J ∈ intervals := by simpa using hJ
      rcases Finset.mem_image.mp hJ_finset with ⟨B, hB, rfl⟩
      have hx_box' : Real.equiv_EuclideanSpace' x ∈ ((B : Box 1) : Set (EuclideanSpace' 1)) := by
        rw [Box.mem_toSet]
        intro i
        fin_cases i
        simpa using hx
      have hx_in_image : Real.equiv_EuclideanSpace' x ∈ Real.equiv_EuclideanSpace' '' E := by
        rw [hS]
        exact Set.mem_iUnion₂.mpr ⟨B, hB, hx_box'⟩
      rcases hx_in_image with ⟨y, hy, hy_eq⟩
      symm at hy_eq
      have hxy : x = y := Real.equiv_EuclideanSpace'.injective hy_eq
      subst hxy; exact hy
  classical
  let all_intervals : Finset BoundedInterval := {I} ∪ intervals
  rcases BoundedInterval.partition all_intervals with ⟨T, hT_disj, hT_partition⟩
  let T_I : Finset BoundedInterval := T.filter (λ J => (J : Set ℝ) ⊆ I.toSet)
  have hT_I_sub_T : (T_I : Set BoundedInterval) ⊆ (T : Set BoundedInterval) := by
    intro J hJ
    have hJ_finset : J ∈ T_I := by simpa using hJ
    rcases Finset.mem_filter.mp hJ_finset with ⟨hJ_T, _⟩
    exact Finset.mem_coe.mpr hJ_T
  have hT_I_disj : (T_I : Set BoundedInterval).PairwiseDisjoint BoundedInterval.toSet :=
    hT_disj.subset hT_I_sub_T
  have hcover : I.toSet = ⋃ J ∈ T_I, (J : Set ℝ) := by
    have hI_mem : I ∈ all_intervals := by simp [all_intervals]
    rcases hT_partition I hI_mem with ⟨U, hU⟩
    apply Set.Subset.antisymm
    · intro x hx
      rw [hU] at hx
      rcases Set.mem_iUnion₂.mp hx with ⟨J, hJ, hx_J⟩
      have hJ_T_I_sub : (J.val : Set ℝ) ⊆ I.toSet := by
        intro y hy
        rw [hU]
        exact Set.mem_iUnion₂.mpr ⟨J, hJ, hy⟩
      have hJ_T_I : J.val ∈ T_I :=
        Finset.mem_filter.mpr ⟨J.property, hJ_T_I_sub⟩
      apply Set.mem_iUnion₂.mpr
      refine ⟨J.val, hJ_T_I, hx_J⟩
    · intro x hx
      rcases Set.mem_iUnion₂.mp hx with ⟨J, hJ, hx⟩
      have hJ_finset : J ∈ T_I := by simpa using hJ
      rcases Finset.mem_filter.mp hJ_finset with ⟨hJ_T, hJ_sub⟩
      exact hJ_sub hx
  let val : BoundedInterval → ℝ := λ J => if (J : Set ℝ) ⊆ E then 1 else 0
  let F : PiecewiseConstantFunction I := {
    f := λ x => by
      classical
      exact if h : ∃ J' ∈ T_I, x ∈ (J' : Set ℝ) then val (Classical.choose h) else 0
    T := T_I
    c := λ J => val J.val
    disjoint := hT_I_disj
    cover := hcover
    const := by
      intro J x hx
      classical
      have h_exists : ∃ J' ∈ T_I, x ∈ (J' : Set ℝ) := ⟨J.val, J.property, hx⟩
      have h_unique : ∀ (J' : BoundedInterval), J' ∈ T_I → x ∈ (J' : Set ℝ) → J' = J.val := by
        intro J' hJ' hx'
        by_contra hne
        have h_disj : Disjoint (J' : Set ℝ) (J.val : Set ℝ) :=
          hT_I_disj (Finset.mem_coe.mpr hJ') (Finset.mem_coe.mpr J.property) hne
        have hx_inter : x ∈ (J' : Set ℝ) ∩ (J.val : Set ℝ) := ⟨hx', hx⟩
        have h_inter_empty : (J' : Set ℝ) ∩ (J.val : Set ℝ) = ∅ :=
          Set.disjoint_iff_inter_eq_empty.mp h_disj
        rw [h_inter_empty] at hx_inter
        simp at hx_inter
      by_cases hcond : ∃ J' ∈ T_I, x ∈ (J' : Set ℝ)
      · simp [hcond]
        have h_choose_spec := Classical.choose_spec hcond
        rcases h_choose_spec with ⟨h_choose_mem, h_choose_x⟩
        rw [h_unique (Classical.choose hcond) h_choose_mem h_choose_x]
      · exfalso; exact hcond h_exists
  }
  have hagrees : F.agreesWith E.indicator' := by
    intro x hx
    have hx_cover : x ∈ ⋃ J ∈ T_I, (J : Set ℝ) := by
      rw [← hcover]; exact hx
    rcases Set.mem_iUnion₂.mp hx_cover with ⟨J, hJ, hx_J⟩
    have hJ_finset : J ∈ T_I := by simpa using hJ
    have hfx : F.f x = val J := F.const ⟨J, hJ_finset⟩ x hx_J
    rw [hfx]
    by_cases hxE : x ∈ E
    · rw [Set.indicator'_of_mem hxE]
      dsimp [val]
      have h_sub : (J : Set ℝ) ⊆ E := by
        rw [hE_union] at hxE
        rcases Set.mem_iUnion₂.mp hxE with ⟨B_side, hB_side, hx_B_side⟩
        have hB_side_finset : B_side ∈ intervals := by simpa using hB_side
        rcases Finset.mem_image.mp hB_side_finset with ⟨B, hB, rfl⟩
        have hB_side_mem : (B.side 0) ∈ all_intervals := by
          dsimp [all_intervals, intervals]
          apply Finset.mem_union_right {I}
          exact Finset.mem_image.mpr ⟨B, hB, rfl⟩
        rcases hT_partition (B.side 0) hB_side_mem with ⟨U_B, hU_B⟩
        have hx_in_U_B : x ∈ ⋃ K ∈ U_B, (K.val : Set ℝ) := by
          rw [← hU_B]
          exact hx_B_side
        rcases Set.mem_iUnion₂.mp hx_in_U_B with ⟨K, hK, hx_K⟩
        -- K is of type Subtype (· ∈ T), K.val : BoundedInterval, K.property : K.val ∈ T
        have hJ_T : J ∈ T := by
          rcases Finset.mem_filter.mp hJ_finset with ⟨hJ_T, _⟩
          exact hJ_T
        by_cases h_eq : K.val = J
        · subst h_eq
          intro y hy
          have hy_side : y ∈ (B.side 0 : Set ℝ) := by
            rw [hU_B]
            exact Set.mem_iUnion₂.mpr ⟨K, hK, hy⟩
          rw [hE_union]
          exact Set.mem_iUnion₂.mpr ⟨B.side 0, hB_side_finset, hy_side⟩
        · have h_disjoint : Disjoint (K.val : Set ℝ) (J : Set ℝ) :=
            hT_disj (Finset.mem_coe.mpr K.property) (Finset.mem_coe.mpr hJ_T) h_eq
          have hx_inter : x ∈ (K.val : Set ℝ) ∩ (J : Set ℝ) := ⟨hx_K, hx_J⟩
          have h_inter_empty : (K.val : Set ℝ) ∩ (J : Set ℝ) = ∅ :=
            Set.disjoint_iff_inter_eq_empty.mp h_disjoint
          rw [h_inter_empty] at hx_inter
          simp at hx_inter
      simp [h_sub]
    · rw [Set.indicator'_of_notMem hxE]
      dsimp [val]
      have h_not_sub : ¬ (J : Set ℝ) ⊆ E := by
        intro h_sub
        exact hxE (h_sub hx_J)
      simp [h_not_sub]
  exact ⟨F, hagrees⟩

/-- Exercise 1.1.21 (c) (Piecewise constant integral of indicator functions) -/
-- The integral of an indicator function of an elementary set equals its elementary measure.
theorem PiecewiseConstantFunction.integral_of_elem {I: BoundedInterval} {E:Set ℝ} (hE: IsElementary (Real.equiv_EuclideanSpace' '' E) ) (hsub: E ⊆ I.toSet) : (PiecewiseConstantOn.indicator_of_elem I hE).integral = hE.measure := by
  have hE_copy := hE
  rcases hE_copy with ⟨S, hS⟩
  let intervals : Finset BoundedInterval := S.image (λ (B : Box 1) => B.side 0)
  have hE_union : E = ⋃ J ∈ intervals, (J : Set ℝ) := by
    ext x; constructor
    · intro hx
      have hx_image : Real.equiv_EuclideanSpace' x ∈ Real.equiv_EuclideanSpace' '' E := ⟨x, hx, rfl⟩
      rw [hS] at hx_image
      rcases Set.mem_iUnion₂.mp hx_image with ⟨B, hB, hx_box⟩
      have hx_side : x ∈ (B.side 0 : Set ℝ) := by
        have h0 := (Box.mem_toSet.mp hx_box) 0
        simpa using h0
      apply Set.mem_iUnion₂.mpr
      refine ⟨B.side 0, ?_, hx_side⟩
      apply Finset.mem_image.mpr
      exact ⟨B, hB, rfl⟩
    · intro hx
      rcases Set.mem_iUnion₂.mp hx with ⟨J, hJ, hx⟩
      have hJ_finset : J ∈ intervals := by simpa using hJ
      rcases Finset.mem_image.mp hJ_finset with ⟨B, hB, rfl⟩
      have hx_box' : Real.equiv_EuclideanSpace' x ∈ ((B : Box 1) : Set (EuclideanSpace' 1)) := by
        rw [Box.mem_toSet]
        intro i
        fin_cases i
        simpa using hx
      have hx_in_image : Real.equiv_EuclideanSpace' x ∈ Real.equiv_EuclideanSpace' '' E := by
        rw [hS]
        exact Set.mem_iUnion₂.mpr ⟨B, hB, hx_box'⟩
      rcases hx_in_image with ⟨y, hy, hy_eq⟩
      symm at hy_eq
      have hxy : x = y := Real.equiv_EuclideanSpace'.injective hy_eq
      subst hxy; exact hy
  classical
  let all_intervals : Finset BoundedInterval := {I} ∪ intervals
  rcases BoundedInterval.partition all_intervals with ⟨T, hT_disj, hT_partition⟩
  let T_I : Finset BoundedInterval := T.filter (λ J => (J : Set ℝ) ⊆ I.toSet)
  have hT_I_sub_T : (T_I : Set BoundedInterval) ⊆ (T : Set BoundedInterval) := by
    intro J hJ
    have hJ_finset : J ∈ T_I := by simpa using hJ
    rcases Finset.mem_filter.mp hJ_finset with ⟨hJ_T, _⟩
    exact Finset.mem_coe.mpr hJ_T
  have hT_I_disj : (T_I : Set BoundedInterval).PairwiseDisjoint BoundedInterval.toSet :=
    hT_disj.subset hT_I_sub_T
  have hcover : I.toSet = ⋃ J ∈ T_I, (J : Set ℝ) := by
    have hI_mem : I ∈ all_intervals := by simp [all_intervals]
    rcases hT_partition I hI_mem with ⟨U, hU⟩
    apply Set.Subset.antisymm
    · intro x hx
      rw [hU] at hx
      rcases Set.mem_iUnion₂.mp hx with ⟨J, hJ, hx_J⟩
      have hJ_T_I_sub : (J.val : Set ℝ) ⊆ I.toSet := by
        intro y hy
        rw [hU]
        exact Set.mem_iUnion₂.mpr ⟨J, hJ, hy⟩
      have hJ_T_I : J.val ∈ T_I :=
        Finset.mem_filter.mpr ⟨J.property, hJ_T_I_sub⟩
      apply Set.mem_iUnion₂.mpr
      refine ⟨J.val, hJ_T_I, hx_J⟩
    · intro x hx
      rcases Set.mem_iUnion₂.mp hx with ⟨J, hJ, hx⟩
      have hJ_finset : J ∈ T_I := by simpa using hJ
      rcases Finset.mem_filter.mp hJ_finset with ⟨hJ_T, hJ_sub⟩
      exact hJ_sub hx
  let val : BoundedInterval → ℝ := λ J => if (J : Set ℝ) ⊆ E then 1 else 0
  let T_E : Finset BoundedInterval := T_I.filter (λ J => (J : Set ℝ) ⊆ E)

  have h_cell_subset_of_mem_E : ∀ (x : ℝ), x ∈ E → ∀ (J : BoundedInterval), J ∈ T_I → x ∈ (J : Set ℝ) → (J : Set ℝ) ⊆ E := by
    intro x hx J hJ_finset hx_J
    rw [hE_union] at hx
    rcases Set.mem_iUnion₂.mp hx with ⟨B_side, hB_side, hx_B_side⟩
    have hB_side_finset : B_side ∈ intervals := by simpa using hB_side
    rcases Finset.mem_image.mp hB_side_finset with ⟨B, hB, rfl⟩
    have hB_side_mem : (B.side 0) ∈ all_intervals := by
      dsimp [all_intervals, intervals]
      apply Finset.mem_union_right {I}
      exact Finset.mem_image.mpr ⟨B, hB, rfl⟩
    rcases hT_partition (B.side 0) hB_side_mem with ⟨U_B, hU_B⟩
    have hx_in_U_B : x ∈ ⋃ K ∈ U_B, (K.val : Set ℝ) := by
      rw [← hU_B]
      exact hx_B_side
    rcases Set.mem_iUnion₂.mp hx_in_U_B with ⟨K, hK, hx_K⟩
    have hJ_T : J ∈ T := by
      rcases Finset.mem_filter.mp hJ_finset with ⟨hJ_T, _⟩
      exact hJ_T
    by_cases h_eq : K.val = J
    · subst h_eq
      intro y hy
      have hy_side : y ∈ (B.side 0 : Set ℝ) := by
        rw [hU_B]
        exact Set.mem_iUnion₂.mpr ⟨K, hK, hy⟩
      rw [hE_union]
      exact Set.mem_iUnion₂.mpr ⟨B.side 0, hB_side_finset, hy_side⟩
    · have h_disjoint : Disjoint (K.val : Set ℝ) (J : Set ℝ) :=
        hT_disj (Finset.mem_coe.mpr K.property) (Finset.mem_coe.mpr hJ_T) h_eq
      have hx_inter : x ∈ (K.val : Set ℝ) ∩ (J : Set ℝ) := ⟨hx_K, hx_J⟩
      have h_inter_empty : (K.val : Set ℝ) ∩ (J : Set ℝ) = ∅ :=
        Set.disjoint_iff_inter_eq_empty.mp h_disjoint
      rw [h_inter_empty] at hx_inter
      simp at hx_inter

  have hE_partition : E = ⋃ J ∈ T_E, (J : Set ℝ) := by
    apply Set.Subset.antisymm
    · intro x hx
      have hx_sub : x ∈ I.toSet := hsub hx
      have hx_cover : x ∈ ⋃ J ∈ T_I, (J : Set ℝ) := by
        rw [← hcover]; exact hx_sub
      rcases Set.mem_iUnion₂.mp hx_cover with ⟨J, hJ, hx_J⟩
      have hJ_finset : J ∈ T_I := by simpa using hJ
      have hJ_sub_E : (J : Set ℝ) ⊆ E := h_cell_subset_of_mem_E x hx J hJ_finset hx_J
      have hJ_T_E : J ∈ T_E := Finset.mem_filter.mpr ⟨hJ_finset, hJ_sub_E⟩
      exact Set.mem_iUnion₂.mpr ⟨J, hJ_T_E, hx_J⟩
    · intro x hx
      rcases Set.mem_iUnion₂.mp hx with ⟨J, hJ, hx_J⟩
      have hJ_T_E : J ∈ T_E := by simpa using hJ
      rcases Finset.mem_filter.mp hJ_T_E with ⟨hJ_T_I, hJ_sub_E⟩
      exact hJ_sub_E hx_J

  let F' : PiecewiseConstantFunction I := {
    f := λ x => by
      classical
      exact if h : ∃ J' ∈ T_I, x ∈ (J' : Set ℝ) then val (Classical.choose h) else 0
    T := T_I
    c := λ J => val J.val
    disjoint := hT_I_disj
    cover := hcover
    const := by
      intro J x hx
      classical
      have h_exists : ∃ J' ∈ T_I, x ∈ (J' : Set ℝ) := ⟨J.val, J.property, hx⟩
      have h_unique : ∀ (J' : BoundedInterval), J' ∈ T_I → x ∈ (J' : Set ℝ) → J' = J.val := by
        intro J' hJ' hx'
        by_contra hne
        have h_disj : Disjoint (J' : Set ℝ) (J.val : Set ℝ) :=
          hT_I_disj (Finset.mem_coe.mpr hJ') (Finset.mem_coe.mpr J.property) hne
        have hx_inter : x ∈ (J' : Set ℝ) ∩ (J.val : Set ℝ) := ⟨hx', hx⟩
        have h_inter_empty : (J' : Set ℝ) ∩ (J.val : Set ℝ) = ∅ :=
          Set.disjoint_iff_inter_eq_empty.mp h_disj
        rw [h_inter_empty] at hx_inter
        simp at hx_inter
      by_cases hcond : ∃ J' ∈ T_I, x ∈ (J' : Set ℝ)
      · simp [hcond]
        have h_choose_spec := Classical.choose_spec hcond
        rcases h_choose_spec with ⟨h_choose_mem, h_choose_x⟩
        rw [h_unique (Classical.choose hcond) h_choose_mem h_choose_x]
      · exfalso; exact hcond h_exists
  }
  have h_F'_integral : F'.integral = ∑ J ∈ T_I, val J * |J|ₗ := by
    unfold PiecewiseConstantFunction.integral
    dsimp [F']
    simpa using Finset.sum_attach (s := T_I) (f := λ J : BoundedInterval => val J * |J|ₗ)
  have hagrees : F'.agreesWith E.indicator' := by
    intro x hx
    have hx_cover : x ∈ ⋃ J ∈ T_I, (J : Set ℝ) := by
      rw [← hcover]; exact hx
    rcases Set.mem_iUnion₂.mp hx_cover with ⟨J, hJ, hx_J⟩
    have hJ_finset : J ∈ T_I := by simpa using hJ
    have hfx : F'.f x = val J := by
      dsimp [F']
      classical
      have h_exists : ∃ J' ∈ T_I, x ∈ (J' : Set ℝ) := ⟨J, hJ_finset, hx_J⟩
      have h_unique : ∀ (J' : BoundedInterval), J' ∈ T_I → x ∈ (J' : Set ℝ) → J' = J := by
        intro J' hJ' hx'
        by_contra hne
        have h_disj : Disjoint (J' : Set ℝ) (J : Set ℝ) :=
          hT_I_disj (Finset.mem_coe.mpr hJ') (Finset.mem_coe.mpr hJ_finset) hne
        have hx_inter : x ∈ (J' : Set ℝ) ∩ (J : Set ℝ) := ⟨hx', hx_J⟩
        have h_inter_empty : (J' : Set ℝ) ∩ (J : Set ℝ) = ∅ :=
          Set.disjoint_iff_inter_eq_empty.mp h_disj
        rw [h_inter_empty] at hx_inter
        simp at hx_inter
      by_cases hcond : ∃ J' ∈ T_I, x ∈ (J' : Set ℝ)
      · simp [hcond]
        have h_choose_spec := Classical.choose_spec hcond
        rcases h_choose_spec with ⟨h_choose_mem, h_choose_x⟩
        rw [h_unique (Classical.choose hcond) h_choose_mem h_choose_x]
      · exfalso; exact hcond h_exists
    rw [hfx]
    by_cases hxE : x ∈ E
    · rw [Set.indicator'_of_mem hxE]
      dsimp [val]
      have h_sub : (J : Set ℝ) ⊆ E := h_cell_subset_of_mem_E x hxE J hJ_finset hx_J
      simp [h_sub]
    · rw [Set.indicator'_of_notMem hxE]
      dsimp [val]
      have h_not_sub : ¬ (J : Set ℝ) ⊆ E := by
        intro h_sub
        exact hxE (h_sub hx_J)
      simp [h_not_sub]

  have h_integral_eq : (PiecewiseConstantOn.indicator_of_elem I hE).integral = F'.integral :=
    PiecewiseConstantOn.integral_eq (E.indicator') (PiecewiseConstantOn.indicator_of_elem I hE) F' hagrees
  rw [h_integral_eq, h_F'_integral]

  have h_sum_val : ∑ J ∈ T_I, val J * |J|ₗ = ∑ J ∈ T_E, |J|ₗ := by
    calc
      ∑ J ∈ T_I, val J * |J|ₗ = ∑ J ∈ T_I, (if (J : Set ℝ) ⊆ E then 1 else 0) * |J|ₗ := rfl
      _ = ∑ J ∈ T_I, (if (J : Set ℝ) ⊆ E then |J|ₗ else 0) := by
        refine Finset.sum_congr rfl fun J hJ => ?_
        split_ifs with h
        · simp
        · simp
      _ = ∑ J ∈ T_E, |J|ₗ := by
        have h_filter := Finset.sum_filter (s := T_I) (p := λ J : BoundedInterval => (J : Set ℝ) ⊆ E) (f := λ J : BoundedInterval => |J|ₗ)
        simpa [T_E] using h_filter.symm

  rw [h_sum_val]

  have h_T_E_disj_boxes : ((T_E.image (λ J : BoundedInterval => (J : Box 1))) : Set (Box 1)).PairwiseDisjoint Box.toSet := by
    rw [Finset.coe_image]
    intro B₁ hB₁ B₂ hB₂ hne
    rcases hB₁ with ⟨J₁, hJ₁, rfl⟩
    rcases hB₂ with ⟨J₂, hJ₂, rfl⟩
    have hJ_ne : J₁ ≠ J₂ := by
      contrapose! hne
      subst hne; rfl
    have hJ₁_T_I : J₁ ∈ T_I := (Finset.mem_filter.mp hJ₁).1
    have hJ₂_T_I : J₂ ∈ T_I := (Finset.mem_filter.mp hJ₂).1
    have h_disj : Disjoint (J₁ : Set ℝ) (J₂ : Set ℝ) :=
      hT_I_disj (Finset.mem_coe.mpr hJ₁_T_I) (Finset.mem_coe.mpr hJ₂_T_I) hJ_ne
    have h_disj_boxes : Disjoint ((J₁ : Box 1).toSet) ((J₂ : Box 1).toSet) := by
      rw [BoundedInterval.coe_of_box, BoundedInterval.coe_of_box]
      refine Set.disjoint_image_of_injective Real.equiv_EuclideanSpace'.injective h_disj
    exact h_disj_boxes

  have h_boxes_cover : Real.equiv_EuclideanSpace' '' E = ⋃ B ∈ (T_E.image (λ J : BoundedInterval => (J : Box 1))), B.toSet := by
    calc
      Real.equiv_EuclideanSpace' '' E = Real.equiv_EuclideanSpace' '' (⋃ J ∈ T_E, (J : Set ℝ)) := by rw [hE_partition]
      _ = ⋃ J ∈ T_E, Real.equiv_EuclideanSpace' '' (J : Set ℝ) := by rw [Set.image_iUnion₂]
      _ = ⋃ J ∈ T_E, ((J : Box 1).toSet) := by
        simp [BoundedInterval.coe_of_box]
      _ = ⋃ B ∈ (T_E.image (λ J : BoundedInterval => (J : Box 1))), B.toSet := by
        simp

  have h_measure_eq : hE.measure = ∑ B ∈ (T_E.image (λ J : BoundedInterval => (J : Box 1))), |B|ᵥ :=
    hE.measure_eq h_T_E_disj_boxes h_boxes_cover

  have h_vol_sum : ∑ B ∈ (T_E.image (λ J : BoundedInterval => (J : Box 1))), |B|ᵥ = ∑ J ∈ T_E, |J|ₗ := by
    calc
      ∑ B ∈ (T_E.image (λ J : BoundedInterval => (J : Box 1))), |B|ᵥ = ∑ J ∈ T_E, |(J : Box 1)|ᵥ := by
        refine Finset.sum_image ?_
        intro x hx y hy h
        exact BoundedInterval.toBox_inj.mp h
      _ = ∑ J ∈ T_E, |J|ₗ := by simp [Box.volume_of_interval]

  calc
    ∑ J ∈ T_E, |J|ₗ = ∑ B ∈ (T_E.image (λ J : BoundedInterval => (J : Box 1))), |B|ᵥ := by rw [h_vol_sum]
    _ = hE.measure := by rw [h_measure_eq]

/-- Definition 1.1.6 (Darboux integral) -/
-- The lower Darboux integral: supremum of integrals of piecewise constant functions that underestimate f.
noncomputable def LowerDarbouxIntegral (f:ℝ → ℝ) (I: BoundedInterval) : ℝ := sSup { R | ∃ g: PiecewiseConstantFunction I, g.integral = R ∧ ∀ x ∈ I.toSet, g.f x ≤ f x }

/-- Definition 1.1.6 (Darboux integral) -/
-- The upper Darboux integral: infimum of integrals of piecewise constant functions that overestimate f.
noncomputable def UpperDarbouxIntegral (f:ℝ → ℝ) (I: BoundedInterval) : ℝ := sInf { R | ∃ h: PiecewiseConstantFunction I, h.integral = R ∧ ∀ x ∈ I.toSet, f x ≤ h.f x }

namespace PiecewiseConstantFunction
/-- Helper: Construct a constant piecewise constant function with a given value -/
def mkConst (I: BoundedInterval) (c: ℝ) : PiecewiseConstantFunction I where
  f := fun _ => c
  T := {I}
  c := fun _ => c
  disjoint := by simp [Set.pairwiseDisjoint_singleton]
  cover := by simp
  const := by intro J x hx; rfl

/-- Helper: The integral of a constant piecewise constant function -/
lemma integral_mkConst (I: BoundedInterval) (c: ℝ) :
    (PiecewiseConstantFunction.mkConst I c).integral = c * |I|ₗ := by
  unfold PiecewiseConstantFunction.integral PiecewiseConstantFunction.mkConst
  simp [Finset.sum_singleton]

/-- Construct a PiecewiseConstantFunction from a Finset of intervals that partition I,
    where the function value on each interval J is val J.val. -/
noncomputable def mkPCF {I: BoundedInterval} (T: Finset BoundedInterval) (val: BoundedInterval → ℝ)
    (hdisj: (T : Set BoundedInterval).PairwiseDisjoint BoundedInterval.toSet)
    (hcover: I.toSet = ⋃ J ∈ T, J.toSet) : PiecewiseConstantFunction I :=
  { f := λ x => by
      classical
      exact if h : ∃ J' ∈ T, x ∈ (J' : Set ℝ) then val (Classical.choose h) else 0
    T := T
    c := λ J => val J.val
    disjoint := hdisj
    cover := hcover
    const := by
      intro J x hx
      classical
      have h_exists : ∃ J' ∈ T, x ∈ (J' : Set ℝ) := ⟨J.val, J.property, hx⟩
      have h_unique : ∀ (J' : BoundedInterval), J' ∈ T → x ∈ (J' : Set ℝ) → J' = J.val := by
        intro J' hJ' hx'
        by_contra hne
        have h_disj : Disjoint (J' : Set ℝ) (J.val : Set ℝ) :=
          hdisj (Finset.mem_coe.mpr hJ') (Finset.mem_coe.mpr J.property) hne
        have hx_inter : x ∈ (J' : Set ℝ) ∩ (J.val : Set ℝ) := ⟨hx', hx⟩
        have h_inter_empty : (J' : Set ℝ) ∩ (J.val : Set ℝ) = ∅ :=
          Set.disjoint_iff_inter_eq_empty.mp h_disj
        rw [h_inter_empty] at hx_inter
        simp at hx_inter
      by_cases hcond : ∃ J' ∈ T, x ∈ (J' : Set ℝ)
      · simp [hcond]
        have h_choose_spec := Classical.choose_spec hcond
        rcases h_choose_spec with ⟨h_choose_mem, h_choose_x⟩
        rw [h_unique (Classical.choose hcond) h_choose_mem h_choose_x]
      · exfalso; exact hcond h_exists
  }

lemma mkPCF_integral {I: BoundedInterval} (T: Finset BoundedInterval) (val: BoundedInterval → ℝ)
    (hdisj: (T : Set BoundedInterval).PairwiseDisjoint BoundedInterval.toSet)
    (hcover: I.toSet = ⋃ J ∈ T, J.toSet) :
    (mkPCF T val hdisj hcover).integral = ∑ J ∈ T, val J * |J|ₗ := by
  calc
    (mkPCF T val hdisj hcover).integral
        = ∑ J : (mkPCF T val hdisj hcover).T, (mkPCF T val hdisj hcover).c J * |J|ₗ := rfl
    _ = ∑ J : T, val J.val * |J.val|ₗ := by
      dsimp [mkPCF]; rfl
    _ = ∑ J ∈ T, val J * |J|ₗ := by
      have hL : (∑ J : T, val J.val * |J.val|ₗ) = (∑ x ∈ T.attach, val (x : BoundedInterval) * |(x : BoundedInterval)|ₗ) := by
        simp
      have hR : (∑ x ∈ T.attach, val (x : BoundedInterval) * |(x : BoundedInterval)|ₗ) = (∑ J ∈ T, val J * |J|ₗ) := by
        rw [Finset.sum_attach T (fun (y : BoundedInterval) => val y * |y|ₗ)]
      rw [hL, hR]

/-- Helper: Construct the negation of a piecewise constant function -/
def neg {I: BoundedInterval} (g: PiecewiseConstantFunction I) : PiecewiseConstantFunction I where
  f := fun x => -g.f x
  T := g.T
  c := fun J => -g.c J
  disjoint := g.disjoint
  cover := g.cover
  const := by
    intro J x hx
    have h_const : g.f x = g.c J := g.const J x hx
    simp [h_const]

/-- Helper: The integral of a negated piecewise constant function -/
lemma integral_neg {I: BoundedInterval} (g: PiecewiseConstantFunction I) :
    g.neg.integral = -g.integral := by
  unfold PiecewiseConstantFunction.integral PiecewiseConstantFunction.neg
  rw [← Finset.sum_neg_distrib]
  congr 1
  ext J
  ring

/-- Helper: Convert a {name}`PiecewiseConstantFunction` to {name}`PiecewiseConstantOn` and relate integrals -/
lemma to_PiecewiseConstantOn {I: BoundedInterval} (g: PiecewiseConstantFunction I) :
    ∃ (h: PiecewiseConstantOn g.f I), h.integral = g.integral := by
  have hg_agrees : g.agreesWith g.f := fun x hx => rfl
  use ⟨g, hg_agrees⟩
  exact PiecewiseConstantOn.integral_eq g.f ⟨g, hg_agrees⟩ g hg_agrees

/--
Helper: Apply integral monotonicity between two
PiecewiseConstantFunctions via PiecewiseConstantOn.
-/
lemma integral_mono' {I: BoundedInterval}
    (g h: PiecewiseConstantFunction I) (h_pointwise: ∀ x ∈ I.toSet, g.f x ≤ h.f x) :
    g.integral ≤ h.integral := by
  let S := g.T ∪ h.T
  obtain ⟨T, hT_disj, hT_refine⟩ := BoundedInterval.partition S
  have hg_refine : ∀ (K : BoundedInterval), K ∈ g.T → ∃ U : Set (Subtype (· ∈ T)), (K : Set ℝ) = ⋃ J ∈ U, (J.val : Set ℝ) := by
    intro K hK
    exact hT_refine K (by simp [S, hK])
  have hh_refine : ∀ (K : BoundedInterval), K ∈ h.T → ∃ U : Set (Subtype (· ∈ T)), (K : Set ℝ) = ⋃ J ∈ U, (J.val : Set ℝ) := by
    intro K hK
    exact hT_refine K (by simp [S, hK])
  choose U hU_cover using hg_refine
  choose U' hU'_cover using hh_refine
  classical
    let uK (K : BoundedInterval) : Finset BoundedInterval :=
      T.filter (λ J : BoundedInterval => (J : Set ℝ) ⊆ (K : Set ℝ))
    have huK_cover (K : BoundedInterval) (hK : K ∈ g.T) : (K : Set ℝ) = ⋃ J ∈ uK K, (J : Set ℝ) := by
      ext x; constructor
      · intro hx
        rw [hU_cover K hK] at hx
        obtain ⟨J', hJ', hx'⟩ := Set.mem_iUnion₂.mp hx
        have hJ'_sub : (J'.val : Set ℝ) ⊆ (K : Set ℝ) := by
          intro y hy
          rw [hU_cover K hK]
          exact Set.mem_iUnion₂.mpr ⟨J', hJ', hy⟩
        have hJ'_val_mem : J'.val ∈ uK K := by
          apply Finset.mem_filter.mpr
          exact ⟨J'.property, hJ'_sub⟩
        refine Set.mem_iUnion₂.mpr ⟨J'.val, hJ'_val_mem, hx'⟩
      · intro hx
        obtain ⟨J, hJ, hx'⟩ := Set.mem_iUnion₂.mp hx
        have hJ_sub : (J : Set ℝ) ⊆ (K : Set ℝ) := (Finset.mem_filter.mp hJ).2
        exact hJ_sub hx'
    have huK_cover' (K : BoundedInterval) (hK : K ∈ h.T) : (K : Set ℝ) = ⋃ J ∈ uK K, (J : Set ℝ) := by
      ext x; constructor
      · intro hx
        rw [hU'_cover K hK] at hx
        obtain ⟨J', hJ', hx'⟩ := Set.mem_iUnion₂.mp hx
        have hJ'_sub : (J'.val : Set ℝ) ⊆ (K : Set ℝ) := by
          intro y hy
          rw [hU'_cover K hK]
          exact Set.mem_iUnion₂.mpr ⟨J', hJ', hy⟩
        have hJ'_val_mem : J'.val ∈ uK K := by
          apply Finset.mem_filter.mpr
          exact ⟨J'.property, hJ'_sub⟩
        refine Set.mem_iUnion₂.mpr ⟨J'.val, hJ'_val_mem, hx'⟩
      · intro hx
        obtain ⟨J, hJ, hx'⟩ := Set.mem_iUnion₂.mp hx
        have hJ_sub : (J : Set ℝ) ⊆ (K : Set ℝ) := (Finset.mem_filter.mp hJ).2
        exact hJ_sub hx'
    have hT_sub (K : BoundedInterval) : (uK K : Set BoundedInterval) ⊆ (T : Set BoundedInterval) := by
      intro I hI
      have hI' : I ∈ uK K := hI
      have hI_T : I ∈ T := (Finset.mem_filter.mp hI').1
      exact hI_T
    have huK_disj (K : BoundedInterval) : (uK K : Set BoundedInterval).PairwiseDisjoint BoundedInterval.toSet :=
      hT_disj.subset (hT_sub K)
    have h_length (K : BoundedInterval) (hK : K ∈ g.T) : |K|ₗ = ∑ J : uK K, |J.val|ₗ := by
      rw [BoundedInterval.length_of_partition K (uK K) (huK_cover K hK) (huK_disj K)]
    have h_length' (K : BoundedInterval) (hK : K ∈ h.T) : |K|ₗ = ∑ J : uK K, |J.val|ₗ := by
      rw [BoundedInterval.length_of_partition K (uK K) (huK_cover' K hK) (huK_disj K)]

    have h_len_set_zero (I' : BoundedInterval) (h_empty : (I' : Set ℝ) = ∅) : |I'|ₗ = 0 := by
      unfold BoundedInterval.length
      have h_ba : I'.b ≤ I'.a := by
        by_contra! h_lt
        have h_nonempty : (I' : Set ℝ).Nonempty := by
          apply Set.Nonempty.mono (BoundedInterval.Ioo_subset I')
          refine ⟨(I'.a + I'.b) / 2, ?_⟩
          constructor <;> nlinarith
        exact h_nonempty.ne_empty h_empty
      simp [h_ba]

    have h_term_le (J : Subtype (· ∈ T)) :
      (∑ K : g.T, (if (J.val : Set ℝ) ⊆ (K.val : Set ℝ) then g.c K else 0)) * |J|ₗ ≤
      (∑ K' : h.T, (if (J.val : Set ℝ) ⊆ (K'.val : Set ℝ) then h.c K' else 0)) * |J|ₗ := by
      by_cases h_zero : |J|ₗ = 0
      · simp [h_zero]
      · have h_nonempty : (J.val : Set ℝ).Nonempty := by
          by_contra h_empty
          have h_len_zero : |J.val|ₗ = 0 :=
            h_len_set_zero J.val (Set.not_nonempty_iff_eq_empty.mp h_empty)
          have : |J|ₗ = 0 := by
            -- `J` coerces to `BoundedInterval` via `Subtype.val`
            simpa using h_len_zero
          exact h_zero this
        obtain ⟨x, hx⟩ := h_nonempty
        by_cases h_exists_g : ∃ (K : g.T), (J.val : Set ℝ) ⊆ (K.val : Set ℝ)
        · obtain ⟨K_g, hK_g_sub⟩ := h_exists_g
          have hx_I : x ∈ (I : Set ℝ) := by
            rw [g.cover]
            exact Set.mem_iUnion₂.mpr ⟨K_g.val, K_g.property, hK_g_sub hx⟩
          have h_exists_h : ∃ (K' : h.T), (J.val : Set ℝ) ⊆ (K'.val : Set ℝ) := by
            rw [h.cover] at hx_I
            obtain ⟨K'_B, hK'_mem, hx_K'⟩ := Set.mem_iUnion₂.mp hx_I
            have hK'_sub : (J.val : Set ℝ) ⊆ (K'_B : Set ℝ) := by
              rw [hU'_cover K'_B hK'_mem] at hx_K'
              obtain ⟨J'', hJ'', hx_J''⟩ := Set.mem_iUnion₂.mp hx_K'
              have hJ_eq : J = J'' := by
                by_contra h_ne
                have h_val_ne : J.val ≠ J''.val := Subtype.val_injective.ne h_ne
                have h_inter_empty : (J.val : Set ℝ) ∩ (J''.val : Set ℝ) = ∅ := by
                  have h_disjoint : Disjoint (J.val : Set ℝ) (J''.val : Set ℝ) :=
                    hT_disj (Finset.mem_coe.mpr J.property) (Finset.mem_coe.mpr J''.property) h_val_ne
                  rw [Set.disjoint_iff_inter_eq_empty.mp h_disjoint]
                have hx_inter : x ∈ (J.val : Set ℝ) ∩ (J''.val : Set ℝ) := ⟨hx, hx_J''⟩
                rw [h_inter_empty] at hx_inter
                simp at hx_inter
              intro y hy
              rw [hU'_cover K'_B hK'_mem]
              have hy_J'' : y ∈ (J''.val : Set ℝ) := by
                subst hJ_eq; exact hy
              exact Set.mem_iUnion₂.mpr ⟨J'', hJ'', hy_J''⟩
            exact ⟨⟨K'_B, hK'_mem⟩, hK'_sub⟩
          obtain ⟨K'_h, hK'_h_sub⟩ := h_exists_h
          have h_unique_g : ∀ (K₁ K₂ : g.T), (J.val : Set ℝ) ⊆ (K₁.val : Set ℝ) → (J.val : Set ℝ) ⊆ (K₂.val : Set ℝ) → K₁ = K₂ := by
            intro K₁ K₂ h_sub₁ h_sub₂
            by_contra h_ne
            have h_val_ne : K₁.val ≠ K₂.val := Subtype.val_injective.ne h_ne
            have h_inter_empty : (K₁.val : Set ℝ) ∩ (K₂.val : Set ℝ) = ∅ := by
              have h_disjoint : Disjoint (K₁.val : Set ℝ) (K₂.val : Set ℝ) :=
                g.disjoint (Finset.mem_coe.mpr K₁.property) (Finset.mem_coe.mpr K₂.property) h_val_ne
              rw [Set.disjoint_iff_inter_eq_empty.mp h_disjoint]
            have hx_in₁ : x ∈ (K₁.val : Set ℝ) := h_sub₁ hx
            have hx_in₂ : x ∈ (K₂.val : Set ℝ) := h_sub₂ hx
            have hx_inter : x ∈ (K₁.val : Set ℝ) ∩ (K₂.val : Set ℝ) := ⟨hx_in₁, hx_in₂⟩
            rw [h_inter_empty] at hx_inter
            simp at hx_inter
          have h_unique_h : ∀ (K₁ K₂ : h.T), (J.val : Set ℝ) ⊆ (K₁.val : Set ℝ) → (J.val : Set ℝ) ⊆ (K₂.val : Set ℝ) → K₁ = K₂ := by
            intro K₁ K₂ h_sub₁ h_sub₂
            by_contra h_ne
            have h_val_ne : K₁.val ≠ K₂.val := Subtype.val_injective.ne h_ne
            have h_inter_empty : (K₁.val : Set ℝ) ∩ (K₂.val : Set ℝ) = ∅ := by
              have h_disjoint : Disjoint (K₁.val : Set ℝ) (K₂.val : Set ℝ) :=
                h.disjoint (Finset.mem_coe.mpr K₁.property) (Finset.mem_coe.mpr K₂.property) h_val_ne
              rw [Set.disjoint_iff_inter_eq_empty.mp h_disjoint]
            have hx_in₁ : x ∈ (K₁.val : Set ℝ) := h_sub₁ hx
            have hx_in₂ : x ∈ (K₂.val : Set ℝ) := h_sub₂ hx
            have hx_inter : x ∈ (K₁.val : Set ℝ) ∩ (K₂.val : Set ℝ) := ⟨hx_in₁, hx_in₂⟩
            rw [h_inter_empty] at hx_inter
            simp at hx_inter
          have h_const_le : g.c K_g ≤ h.c K'_h := by
            have hg_fx : g.f x = g.c K_g := g.const K_g x (hK_g_sub hx)
            have hh_fx : h.f x = h.c K'_h := h.const K'_h x (hK'_h_sub hx)
            have hfx_le : g.f x ≤ h.f x := h_pointwise x hx_I
            calc
              g.c K_g = g.f x := (hg_fx.symm)
              _ ≤ h.f x := hfx_le
              _ = h.c K'_h := hh_fx
          have h_inner_g : (∑ K : g.T, (if (J.val : Set ℝ) ⊆ (K.val : Set ℝ) then g.c K else 0)) = g.c K_g := by
            have h_sum_attach : (∑ K : g.T, (if (J.val : Set ℝ) ⊆ (K.val : Set ℝ) then g.c K else 0)) =
              Finset.sum (Finset.attach g.T) (fun (K' : g.T) => if (J.val : Set ℝ) ⊆ (K'.val : Set ℝ) then g.c K' else 0) := by
              simp
            rw [h_sum_attach]
            have h_temp : Finset.sum (Finset.attach g.T) (fun (K' : g.T) => if (J.val : Set ℝ) ⊆ (K'.val : Set ℝ) then g.c K' else 0) =
              (if (J.val : Set ℝ) ⊆ (K_g.val : Set ℝ) then g.c K_g else 0) :=
              Finset.sum_eq_single (a := K_g) (by
                intro K' hK' h_ne
                have h_not_sub : ¬ (J.val : Set ℝ) ⊆ (K'.val : Set ℝ) := by
                  intro h_sub
                  have : K' = K_g := h_unique_g K' K_g h_sub hK_g_sub
                  exact h_ne this
                simp [h_not_sub]
              ) (by
                intro h_not
                exfalso; exact h_not (by simp))
            simpa [hK_g_sub] using h_temp
          have h_inner_h : (∑ K' : h.T, (if (J.val : Set ℝ) ⊆ (K'.val : Set ℝ) then h.c K' else 0)) = h.c K'_h := by
            have h_sum_attach : (∑ K' : h.T, (if (J.val : Set ℝ) ⊆ (K'.val : Set ℝ) then h.c K' else 0)) =
              Finset.sum (Finset.attach h.T) (fun (K'' : h.T) => if (J.val : Set ℝ) ⊆ (K''.val : Set ℝ) then h.c K'' else 0) := by
              simp
            rw [h_sum_attach]
            have h_temp : Finset.sum (Finset.attach h.T) (fun (K'' : h.T) => if (J.val : Set ℝ) ⊆ (K''.val : Set ℝ) then h.c K'' else 0) =
              (if (J.val : Set ℝ) ⊆ (K'_h.val : Set ℝ) then h.c K'_h else 0) :=
              Finset.sum_eq_single (a := K'_h) (by
                intro K'' hK'' h_ne
                have h_not_sub : ¬ (J.val : Set ℝ) ⊆ (K''.val : Set ℝ) := by
                  intro h_sub
                  have : K'' = K'_h := h_unique_h K'' K'_h h_sub hK'_h_sub
                  exact h_ne this
                simp [h_not_sub]
              ) (by
                intro h_not; exfalso; exact h_not (by simp))
            simpa [hK'_h_sub] using h_temp
          rw [h_inner_g, h_inner_h]
          nlinarith [BoundedInterval.length_nonneg J.val]
        · -- No K ∈ g.T contains J.val, so g_sum = 0
          have h_inner_g_zero : (∑ K : g.T, (if (J.val : Set ℝ) ⊆ (K.val : Set ℝ) then g.c K else 0)) = 0 := by
            apply Finset.sum_eq_zero
            intro K hK
            have h_not_sub : ¬ (J.val : Set ℝ) ⊆ (K.val : Set ℝ) := by
              intro h_sub; exact h_exists_g ⟨K, h_sub⟩
            simp [h_not_sub]
          have h_inner_h_zero : (∑ K' : h.T, (if (J.val : Set ℝ) ⊆ (K'.val : Set ℝ) then h.c K' else 0)) = 0 := by
            apply Finset.sum_eq_zero
            intro K' hK'
            by_cases h_sub : (J.val : Set ℝ) ⊆ (K'.val : Set ℝ)
            · have hx_I : x ∈ (I : Set ℝ) := by
                rw [h.cover]
                exact Set.mem_iUnion₂.mpr ⟨K'.val, K'.property, h_sub hx⟩
              rw [g.cover] at hx_I
              obtain ⟨K_B, hK_B, hx_K⟩ := Set.mem_iUnion₂.mp hx_I
              have hK_B_sub : (J.val : Set ℝ) ⊆ (K_B : Set ℝ) := by
                rw [hU_cover K_B hK_B] at hx_K
                obtain ⟨J'', hJ'', hx_J''⟩ := Set.mem_iUnion₂.mp hx_K
                have hJ_eq : J = J'' := by
                  by_contra h_ne
                  have h_val_ne : J.val ≠ J''.val := Subtype.val_injective.ne h_ne
                  have h_inter_empty : (J.val : Set ℝ) ∩ (J''.val : Set ℝ) = ∅ := by
                    have h_disjoint : Disjoint (J.val : Set ℝ) (J''.val : Set ℝ) :=
                      hT_disj (Finset.mem_coe.mpr J.property) (Finset.mem_coe.mpr J''.property) h_val_ne
                    rw [Set.disjoint_iff_inter_eq_empty.mp h_disjoint]
                  have hx_inter : x ∈ (J.val : Set ℝ) ∩ (J''.val : Set ℝ) := ⟨hx, hx_J''⟩
                  rw [h_inter_empty] at hx_inter
                  simp at hx_inter
                intro y hy
                rw [hU_cover K_B hK_B]
                have hy_J'' : y ∈ (J''.val : Set ℝ) := by
                  subst hJ_eq; exact hy
                exact Set.mem_iUnion₂.mpr ⟨J'', hJ'', hy_J''⟩
              exact absurd ⟨⟨K_B, hK_B⟩, hK_B_sub⟩ h_exists_g
            · simp [h_sub]
          have h_inner_g_zero_attach : (∑ K ∈ g.T.attach, (if (J.val : Set ℝ) ⊆ (K.val : Set ℝ) then g.c K else 0)) = 0 := by
            simpa using h_inner_g_zero
          have h_inner_h_zero_attach : (∑ K' ∈ h.T.attach, (if (J.val : Set ℝ) ⊆ (K'.val : Set ℝ) then h.c K' else 0)) = 0 := by
            simpa using h_inner_h_zero
          simp [h_inner_g_zero_attach, h_inner_h_zero_attach]

    have h_inner_conv (b : g.T) : (∑ J : uK (b.val), g.c b * |J|ₗ) =
      (∑ J : Subtype (· ∈ T), (if (J.val : Set ℝ) ⊆ (b.val : Set ℝ) then g.c b * |J|ₗ else 0)) := by
      calc
        (∑ J : uK (b.val), g.c b * |J|ₗ) = Finset.sum (uK (b.val)) (fun J : BoundedInterval => g.c b * |J|ₗ) := by
          simpa using Finset.sum_attach (uK (b.val)) (fun J : BoundedInterval => g.c b * |J|ₗ)
        _ = Finset.sum T (fun J : BoundedInterval => if (J : Set ℝ) ⊆ (b.val : Set ℝ) then g.c b * |J|ₗ else 0) := by
          dsimp [uK]
          simp [Finset.sum_filter]
        _ = (∑ J : Subtype (· ∈ T), (if (J.val : Set ℝ) ⊆ (b.val : Set ℝ) then g.c b * |J|ₗ else 0)) := by
          simpa using (Finset.sum_attach T (fun J : BoundedInterval => if (J : Set ℝ) ⊆ (b.val : Set ℝ) then g.c b * |J|ₗ else 0)).symm

    have h_inner_conv' (b : h.T) : (∑ J : uK (b.val), h.c b * |J|ₗ) =
      (∑ J : Subtype (· ∈ T), (if (J.val : Set ℝ) ⊆ (b.val : Set ℝ) then h.c b * |J|ₗ else 0)) := by
      calc
        (∑ J : uK (b.val), h.c b * |J|ₗ) = Finset.sum (uK (b.val)) (fun J : BoundedInterval => h.c b * |J|ₗ) := by
          simpa using Finset.sum_attach (uK (b.val)) (fun J : BoundedInterval => h.c b * |J|ₗ)
        _ = Finset.sum T (fun J : BoundedInterval => if (J : Set ℝ) ⊆ (b.val : Set ℝ) then h.c b * |J|ₗ else 0) := by
          dsimp [uK]
          simp [Finset.sum_filter]
        _ = (∑ J : Subtype (· ∈ T), (if (J.val : Set ℝ) ⊆ (b.val : Set ℝ) then h.c b * |J|ₗ else 0)) := by
          simpa using (Finset.sum_attach T (fun J : BoundedInterval => if (J : Set ℝ) ⊆ (b.val : Set ℝ) then h.c b * |J|ₗ else 0)).symm

    unfold PiecewiseConstantFunction.integral
    calc
      (∑ K : g.T, g.c K * |K|ₗ) = (∑ K : g.T, g.c K * (∑ J : uK (K.val), |J|ₗ)) := by
        apply Finset.sum_congr rfl
        intro K hK
        rw [h_length (K.val) K.property]
      _ = (∑ K : g.T, ∑ J : uK (K.val), g.c K * |J|ₗ) := by
        simp_rw [Finset.mul_sum]
      _ = (∑ K : g.T, ∑ J : Subtype (· ∈ T), (if (J.val : Set ℝ) ⊆ (K.val : Set ℝ) then g.c K * |J|ₗ else 0)) := by
        simp_rw [h_inner_conv]
      _ = (∑ J : Subtype (· ∈ T), ∑ K : g.T, (if (J.val : Set ℝ) ⊆ (K.val : Set ℝ) then g.c K * |J|ₗ else 0)) := by
        rw [Finset.sum_comm]
      _ = (∑ J : Subtype (· ∈ T), ((∑ K : g.T, (if (J.val : Set ℝ) ⊆ (K.val : Set ℝ) then g.c K else 0)) * |J|ₗ)) := by
        simp [Finset.mul_sum, mul_comm]
      _ ≤ (∑ J : Subtype (· ∈ T), ((∑ K' : h.T, (if (J.val : Set ℝ) ⊆ (K'.val : Set ℝ) then h.c K' else 0)) * |J|ₗ)) := by
        refine Finset.sum_le_sum ?_
        intro J hJ
        exact h_term_le J
      _ = (∑ J : Subtype (· ∈ T), ∑ K' : h.T, (if (J.val : Set ℝ) ⊆ (K'.val : Set ℝ) then h.c K' * |J|ₗ else 0)) := by
        simp [Finset.mul_sum, mul_comm]
      _ = (∑ K' : h.T, ∑ J : Subtype (· ∈ T), (if (J.val : Set ℝ) ⊆ (K'.val : Set ℝ) then h.c K' * |J|ₗ else 0)) := by
        rw [Finset.sum_comm]
      _ = (∑ K' : h.T, ∑ J : uK (K'.val), h.c K' * |J|ₗ) := by
        simp_rw [h_inner_conv']
      _ = (∑ K' : h.T, h.c K' * (∑ J : uK (K'.val), |J|ₗ)) := by
        simp_rw [Finset.mul_sum]
      _ = (∑ K' : h.T, h.c K' * |K'.val|ₗ) := by
        apply Finset.sum_congr rfl
        intro K' hK'
        rw [h_length' (K'.val) K'.property]



/-- Exercise 1.1.21 (b) (Monotonicity of the piecewise constant integral) -/
-- The integral is monotone: if f ≤ g pointwise, then integral(f) ≤ integral(g).
theorem integral_mono {I: BoundedInterval} {f g: ℝ → ℝ} (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) (hmono: ∀ x ∈ I.toSet, f x ≤ g x): hf.integral ≤ hg.integral := by
  have hF_agrees : hf.choose.agreesWith f := hf.choose_spec
  have hG_agrees : hg.choose.agreesWith g := hg.choose_spec
  have h_pointwise : ∀ x ∈ I.toSet, (hf.choose : PiecewiseConstantFunction I).f x ≤ (hg.choose : PiecewiseConstantFunction I).f x := by
    intro x hx
    have h_eq_f : (hf.choose : PiecewiseConstantFunction I).f x = f x := (hF_agrees hx).symm
    have h_eq_g : (hg.choose : PiecewiseConstantFunction I).f x = g x := (hG_agrees hx).symm
    rw [h_eq_f, h_eq_g]
    exact hmono x hx
  have h := integral_mono' (hf.choose : PiecewiseConstantFunction I) (hg.choose : PiecewiseConstantFunction I) h_pointwise
  dsimp [PiecewiseConstantOn.integral]
  exact h

end PiecewiseConstantFunction


/-- Helper: The lower Darboux set is bounded above -/
lemma LowerDarbouxIntegral.bddAbove {f:ℝ → ℝ} {I: BoundedInterval} (M: ℝ) (hM: ∀ x ∈ I, |f x| ≤ M) :
    BddAbove ({ R | ∃ g: PiecewiseConstantFunction I, g.integral = R ∧ ∀ x ∈ I.toSet, g.f x ≤ f x } : Set ℝ) := by
  rw [bddAbove_def]
  use M * |I|ₗ
  intro R hR
  obtain ⟨g, rfl, hg_lower⟩ := hR
  let g_const := PiecewiseConstantFunction.mkConst I M
  have h_pointwise : ∀ x ∈ I.toSet, g.f x ≤ g_const.f x := by
    intro x hx
    have h_abs : |f x| ≤ M := hM x hx
    rw [abs_le] at h_abs
    simp [g_const, PiecewiseConstantFunction.mkConst]
    have h_g_f : g.f x ≤ f x := hg_lower x hx
    have h_f_M : f x ≤ M := h_abs.2
    linarith
  have h_mono := PiecewiseConstantFunction.integral_mono' g g_const h_pointwise
  rw [PiecewiseConstantFunction.integral_mkConst] at h_mono
  exact h_mono

/-- Helper: The upper Darboux set is bounded below -/
lemma UpperDarbouxIntegral.bddBelow {f:ℝ → ℝ} {I: BoundedInterval} (M: ℝ) (hM: ∀ x ∈ I, |f x| ≤ M) :
    BddBelow ({ R | ∃ h: PiecewiseConstantFunction I, h.integral = R ∧ ∀ x ∈ I.toSet, f x ≤ h.f x } : Set ℝ) := by
  rw [bddBelow_def]
  use -M * |I|ₗ
  intro R hR
  obtain ⟨h, rfl, hh_upper⟩ := hR
  let h_const := PiecewiseConstantFunction.mkConst I (-M)
  have h_pointwise : ∀ x ∈ I.toSet, h_const.f x ≤ h.f x := by
    intro x hx
    have h_abs : |f x| ≤ M := hM x hx
    rw [abs_le] at h_abs
    simp [h_const, PiecewiseConstantFunction.mkConst]
    have h_ineq : f x ≤ h.f x := hh_upper x hx
    calc -M ≤ f x := h_abs.1
      _ ≤ h.f x := h_ineq
  have h_mono := PiecewiseConstantFunction.integral_mono' h_const h h_pointwise
  rw [PiecewiseConstantFunction.integral_mkConst] at h_mono
  exact h_mono

/-- Definition 1.1.6 (Darboux integral) -/
-- For any bounded function, the lower Darboux integral is at most the upper Darboux integral.
lemma lower_darboux_le_upper_darboux {f:ℝ → ℝ} {I: BoundedInterval} (hbound: ∃ M, ∀ x ∈ I, |f x| ≤ M) : LowerDarbouxIntegral f I ≤ UpperDarbouxIntegral f I := by
  obtain ⟨M, hM⟩ := hbound
  unfold LowerDarbouxIntegral UpperDarbouxIntegral
  apply csSup_le
  · -- Show lower set is nonempty
    let g_const := PiecewiseConstantFunction.mkConst I (-M)
    use g_const.integral, g_const, rfl
    intro x hx
    have h_abs : |f x| ≤ M := hM x hx
    rw [abs_le] at h_abs
    simp [g_const, PiecewiseConstantFunction.mkConst]
    linarith [h_abs.1]
  · -- Show every lower element ≤ UpperDarbouxIntegral
    intro R hR
    obtain ⟨g, rfl, hg_lower⟩ := hR
    apply le_csInf
    · -- Show upper set is nonempty
      let h_const := PiecewiseConstantFunction.mkConst I M
      use h_const.integral, h_const, rfl
      intro x hx
      have h_abs : |f x| ≤ M := hM x hx
      rw [abs_le] at h_abs
      simp [h_const, PiecewiseConstantFunction.mkConst]
      linarith [h_abs.2]
    · -- Show g.integral is a lower bound for upper set
      intro b hb
      obtain ⟨h, rfl, hh_upper⟩ := hb
      have h_pointwise : ∀ x ∈ I.toSet, g.f x ≤ h.f x := by
        intro x hx
        have hg : g.f x ≤ f x := hg_lower x hx
        have hh : f x ≤ h.f x := hh_upper x hx
        linarith
      exact PiecewiseConstantFunction.integral_mono' g h h_pointwise

/-- Definition 1.1.6 (Darboux integral) -/
-- A function is Darboux integrable if it is bounded on a nonempty closed interval and its
-- lower and upper Darboux integrals coincide. Nonemptiness matches {name}`RiemannIntegrableOn`.
noncomputable def DarbouxIntegrableOn (f:ℝ → ℝ) (I: BoundedInterval) : Prop :=
  (I = Icc I.a I.b) ∧ I.toSet.Nonempty ∧
    (∃ M, ∀ x ∈ I, |f x| ≤ M) ∧ LowerDarbouxIntegral f I = UpperDarbouxIntegral f I

/-- We give the Darboux integral the "junk" value of the lower Darboux integral when the function is not integrable. -/
-- The Darboux integral: equals the common value if integrable, otherwise the lower Darboux integral.
noncomputable def darbouxIntegral (f:ℝ → ℝ) (I: BoundedInterval) : ℝ := LowerDarbouxIntegral f I

/-- Helper: The upper Darboux set for -f is bounded below -/
lemma UpperDarbouxIntegral.bddBelow_neg {f:ℝ → ℝ} {I: BoundedInterval} (M: ℝ) (hM: ∀ x ∈ I, |f x| ≤ M) :
    BddBelow ({ R | ∃ h: PiecewiseConstantFunction I, h.integral = R ∧ ∀ x ∈ I.toSet, (-f) x ≤ h.f x } : Set ℝ) := by
  rw [bddBelow_def]
  use -M * |I|ₗ
  intro R hR
  obtain ⟨h, rfl, hh_upper⟩ := hR
  let h_const := PiecewiseConstantFunction.mkConst I (-M)
  have h_pointwise : ∀ x ∈ I.toSet, h_const.f x ≤ h.f x := by
    intro x hx
    have h_abs : |f x| ≤ M := hM x hx
    rw [abs_le] at h_abs
    simp [h_const, PiecewiseConstantFunction.mkConst]
    have h_ineq : (-f) x ≤ h.f x := hh_upper x hx
    calc -M ≤ -f x := by linarith [h_abs.2]
      _ ≤ h.f x := h_ineq
  have h_mono := PiecewiseConstantFunction.integral_mono' h_const h h_pointwise
  rw [PiecewiseConstantFunction.integral_mkConst] at h_mono
  exact h_mono

/-- Definition 1.1.6 (Darboux integral) -/
-- For the negation of a function, the upper Darboux integral of -f equals minus the lower Darboux integral of f.
lemma UpperDarbouxIntegral.neg {f:ℝ → ℝ} {I: BoundedInterval} (hbound: ∃ M, ∀ x ∈ I, |f x| ≤ M) : UpperDarbouxIntegral (-f) I = -LowerDarbouxIntegral f I := by
  obtain ⟨M, hM⟩ := hbound
  unfold UpperDarbouxIntegral LowerDarbouxIntegral
  apply le_antisymm
  · -- Show UpperDarbouxIntegral (-f) I ≤ -LowerDarbouxIntegral f I
    rw [← neg_le_neg_iff, neg_neg]
    apply csSup_le
    · -- Show lower set is nonempty
      let g_const := PiecewiseConstantFunction.mkConst I (-M)
      use g_const.integral, g_const, rfl
      intro x hx
      have h_abs : |f x| ≤ M := hM x hx
      rw [abs_le] at h_abs
      simp [g_const, PiecewiseConstantFunction.mkConst]
      linarith [h_abs.1]
    · -- Show -sInf (upper set) is an upper bound for lower set
      intro b hb
      obtain ⟨g, rfl, hg_lower⟩ := hb
      -- Key: -g is an upper approximation for -f since g ≤ f implies -f ≤ -g
      let neg_g := g.neg
      have h_neg_upper : ∀ x ∈ I.toSet, (-f) x ≤ neg_g.f x := by
        intro x hx
        have h_ineq : g.f x ≤ f x := hg_lower x hx
        simp [neg_g, PiecewiseConstantFunction.neg]
        linarith
      have h_neg_in_set : -g.integral ∈ { R | ∃ h: PiecewiseConstantFunction I, h.integral = R ∧ ∀ x ∈ I.toSet, (-f) x ≤ h.f x } := by
        use neg_g, g.integral_neg, h_neg_upper
      have h_bdd_below := UpperDarbouxIntegral.bddBelow_neg M hM
      have h_inf_le : sInf { R | ∃ h: PiecewiseConstantFunction I, h.integral = R ∧ ∀ x ∈ I.toSet, (-f) x ≤ h.f x } ≤ -g.integral :=
        csInf_le h_bdd_below h_neg_in_set
      linarith
  · -- Show -LowerDarbouxIntegral f I ≤ UpperDarbouxIntegral (-f) I
    apply le_csInf
    · -- Show upper set for -f is nonempty
      let h_const := PiecewiseConstantFunction.mkConst I M
      use h_const.integral, h_const, rfl
      intro x hx
      have h_abs : |f x| ≤ M := hM x hx
      rw [abs_le] at h_abs
      simp [h_const, PiecewiseConstantFunction.mkConst]
      linarith [h_abs.1]
    · -- Show -sSup (lower set) is a lower bound for upper set
      intro b hb
      obtain ⟨h, rfl, hh_upper⟩ := hb
      -- Key: -h is a lower approximation for f since -f ≤ h implies -h ≤ f
      let neg_h := h.neg
      have h_neg_lower : ∀ x ∈ I.toSet, neg_h.f x ≤ f x := by
        intro x hx
        have h_ineq : (-f) x ≤ h.f x := hh_upper x hx
        simp only [neg_h, PiecewiseConstantFunction.neg]
        have h1 : -f x ≤ h.f x := h_ineq
        nlinarith [h1]
      have h_neg_in_set : -h.integral ∈ { R | ∃ g: PiecewiseConstantFunction I, g.integral = R ∧ ∀ x ∈ I.toSet, g.f x ≤ f x } := by
        use neg_h, h.integral_neg, h_neg_lower
      have h_bdd := LowerDarbouxIntegral.bddAbove M hM
      have h_le_sup : -h.integral ≤ sSup { R | ∃ g: PiecewiseConstantFunction I, g.integral = R ∧ ∀ x ∈ I.toSet, g.f x ≤ f x } :=
        le_csSup h_bdd h_neg_in_set
      linarith

/-- Exercise 1.1.22 -/
-- Riemann integrability is equivalent to Darboux integrability for bounded functions.
/- The original statement omitted nonemptiness of `I` and is false for `I = Icc 1 0`:
`DarbouxIntegrableOn (fun _ ↦ 0) I` holds, while `RiemannIntegrableOn` explicitly requires
`I.toSet.Nonempty`.  The corrected statement follows. -/
lemma RiemannIntegrableOn.iff_darbouxIntegrable {f:ℝ → ℝ} {I: BoundedInterval}
    (hbound: ∃ M, ∀ x ∈ I, |f x| ≤ M) (h_nonempty : I.toSet.Nonempty) :
    RiemannIntegrableOn f I ↔ DarbouxIntegrableOn f I := by sorry

/-- The subintervals of a tagged partition as a Finset of right-half-open intervals. -/
noncomputable def TaggedPartition.intervals {I: BoundedInterval} {n:ℕ} (P: TaggedPartition I n) : Finset BoundedInterval :=
  Finset.image (fun (i : Fin n) => Ico (P.x i.castSucc) (P.x i.succ)) Finset.univ ∪ {Icc I.b I.b}

/-- For i ≠ j, Ico(P.x i.castSucc, P.x i.succ) and Ico(P.x j.castSucc, P.x j.succ) are disjoint. -/
lemma TaggedPartition.Ico_disjoint {I: BoundedInterval} {n:ℕ} (P: TaggedPartition I n) {i j : Fin n} (hne : i ≠ j) :
    Disjoint (Set.Ico (P.x i.castSucc) (P.x i.succ)) (Set.Ico (P.x j.castSucc) (P.x j.succ)) := by
  have h_lt_or : i < j ∨ j < i := by
    by_cases hij : i < j
    · exact Or.inl hij
    · have hji : j < i := by
        apply lt_of_le_of_ne (by exact not_lt.mp hij) hne.symm
      exact Or.inr hji
  rcases h_lt_or with (h_lt | h_lt)
  · have hv : (i.succ : Fin (n+1)).val ≤ (j.castSucc : Fin (n+1)).val := by
      simp; omega
    have hx_le : P.x i.succ ≤ P.x j.castSucc := P.x_mono.monotone hv
    rw [Set.disjoint_iff_inter_eq_empty]
    apply Set.not_nonempty_iff_eq_empty.mp
    rintro ⟨x, hx⟩
    rcases hx with ⟨⟨hx1, hx2⟩, ⟨hx3, hx4⟩⟩
    linarith
  · have hv : (j.succ : Fin (n+1)).val ≤ (i.castSucc : Fin (n+1)).val := by
      simp; omega
    have hx_le : P.x j.succ ≤ P.x i.castSucc := P.x_mono.monotone hv
    rw [Set.disjoint_iff_inter_eq_empty]
    apply Set.not_nonempty_iff_eq_empty.mp
    rintro ⟨x, hx⟩
    rcases hx with ⟨⟨hx1, hx2⟩, ⟨hx3, hx4⟩⟩
    linarith

lemma TaggedPartition.intervals_disjoint {I: BoundedInterval} {n:ℕ} (P: TaggedPartition I n) :
    (P.intervals : Set BoundedInterval).PairwiseDisjoint BoundedInterval.toSet := by
  intro A hA B hB hne
  have hA_mem : A ∈ Finset.image (fun (i : Fin n) => Ico (P.x i.castSucc) (P.x i.succ)) Finset.univ ∪ {Icc I.b I.b} := hA
  have hB_mem : B ∈ Finset.image (fun (i : Fin n) => Ico (P.x i.castSucc) (P.x i.succ)) Finset.univ ∪ {Icc I.b I.b} := hB
  rcases Finset.mem_union.mp hA_mem with (hA_img | hA_sing)
  · rcases Finset.mem_image.mp hA_img with ⟨i, _, rfl⟩
    rcases Finset.mem_union.mp hB_mem with (hB_img | hB_sing)
    · rcases Finset.mem_image.mp hB_img with ⟨j, _, rfl⟩
      by_cases hij : i = j
      · exfalso; exact hne (by subst hij; rfl)
      · exact P.Ico_disjoint hij
    · have hB_val : B = Icc I.b I.b := Finset.mem_singleton.mp hB_sing
      subst hB_val
      show Disjoint (toSet (Ico (P.x i.castSucc) (P.x i.succ))) (toSet (Icc I.b I.b))
      rw [Set.disjoint_iff_inter_eq_empty]
      apply Set.not_nonempty_iff_eq_empty.mp
      rintro ⟨x, hx⟩
      rcases hx with ⟨⟨hx1, hx2⟩, ⟨hx3, hx4⟩⟩
      have hv_val : (i.succ : Fin (n+1)).val ≤ (Fin.last n : Fin (n+1)).val := by
        simp [Fin.val_succ, Fin.val_last, Nat.succ_le_of_lt (Fin.is_lt i)]
      have hv : (i.succ : Fin (n+1)) ≤ (Fin.last n : Fin (n+1)) := hv_val
      have hx_le : P.x i.succ ≤ I.b :=
        le_trans (P.x_mono.monotone hv) (by rw [P.x_end])
      linarith
  · have hA_val : A = Icc I.b I.b := Finset.mem_singleton.mp hA_sing
    subst hA_val
    rcases Finset.mem_union.mp hB_mem with (hB_img | hB_sing)
    · rcases Finset.mem_image.mp hB_img with ⟨j, _, rfl⟩
      show Disjoint (toSet (Icc I.b I.b)) (toSet (Ico (P.x j.castSucc) (P.x j.succ)))
      rw [Set.disjoint_iff_inter_eq_empty]
      apply Set.not_nonempty_iff_eq_empty.mp
      rintro ⟨x, hx⟩
      rcases hx with ⟨⟨hx1, hx2⟩, ⟨hx3, hx4⟩⟩
      have hv_val : (j.succ : Fin (n+1)).val ≤ (Fin.last n : Fin (n+1)).val := by
        simpa [Fin.val_succ, Fin.val_last] using Nat.succ_le_of_lt (Fin.is_lt j)
      have hv : (j.succ : Fin (n+1)) ≤ (Fin.last n : Fin (n+1)) := hv_val
      have hx_le : P.x j.succ ≤ I.b :=
        le_trans (P.x_mono.monotone hv) (by rw [P.x_end])
      linarith
    · have hB_val : B = Icc I.b I.b := Finset.mem_singleton.mp hB_sing
      subst hB_val
      exfalso; exact hne rfl

/-- For a tagged partition P with n > 0 and I.a ≤ I.b, its subintervals cover I. -/
lemma TaggedPartition.intervals_cover (hI : I = Icc I.a I.b) (h_ab : I.a ≤ I.b) {n:ℕ} (hn : n > 0) (P : TaggedPartition I n) :
    I.toSet = ⋃ J ∈ (P.intervals : Set BoundedInterval), J.toSet := by
  have hn' : n > 0 := hn
  ext x; constructor
  · intro hx
    rw [hI] at hx
    rcases hx with ⟨hx1, hx2⟩
    by_cases hx_end : x = I.b
    · subst x
      refine Set.mem_iUnion₂.mpr ⟨Icc I.b I.b, ?_, by simp⟩
      simp [TaggedPartition.intervals]
    · have hx_lt_Ib : x < I.b := lt_of_le_of_ne hx2 hx_end
      have h_exists : (Finset.filter (λ (k : Fin (n+1)) => x < P.x k) Finset.univ).Nonempty := by
        refine ⟨Fin.last n, ?_⟩
        simp; rw [P.x_end]; exact hx_lt_Ib
      let k := Finset.min' (Finset.filter (λ (k : Fin (n+1)) => x < P.x k) Finset.univ) h_exists
      have hk_mem : k ∈ Finset.filter (λ (k : Fin (n+1)) => x < P.x k) Finset.univ :=
        Finset.min'_mem _ h_exists
      have hx_lt_Pk : x < P.x k := (Finset.mem_filter.mp hk_mem).2
      have hk0 : k ≠ (0 : Fin (n+1)) := by
        intro hk0; rw [hk0, P.x_start] at hx_lt_Pk; linarith
      have hi_pred : ∃ (i : Fin n), i.succ = k := by
        refine ⟨Fin.pred k hk0, ?_⟩; simp
      rcases hi_pred with ⟨i, hi⟩
      have hx_ge_Px_castSucc : P.x i.castSucc ≤ x := by
        by_contra! hlt
        have : (i.castSucc : Fin (n+1)) ∈ Finset.filter (λ (k' : Fin (n+1)) => x < P.x k') Finset.univ := by
          simp; exact hlt
        have hk_le : k ≤ (i.castSucc : Fin (n+1)) := Finset.min'_le _ _ this
        have h_val : k.val = i.val + 1 := by
          have h_succ_val : i.succ.val = i.val + 1 := by simp
          have h_k_val : k.val = i.succ.val := by simpa [hi] using rfl
          rw [h_succ_val] at h_k_val; exact h_k_val
        have h_cast_val : (i.castSucc : Fin (n+1)).val = i.val := by simp
        omega
      have hx_lt_Pi_succ : x < P.x i.succ := by rw [hi]; exact hx_lt_Pk
      have hJ_mem : Ico (P.x i.castSucc) (P.x i.succ) ∈ (P.intervals : Set BoundedInterval) := by
        dsimp [TaggedPartition.intervals]
        apply Finset.mem_coe.mpr
        apply Finset.mem_union_left
        apply Finset.mem_image.mpr
        exact ⟨i, Finset.mem_univ _, rfl⟩
      refine Set.mem_iUnion₂.mpr ⟨Ico (P.x i.castSucc) (P.x i.succ), hJ_mem, ⟨hx_ge_Px_castSucc, hx_lt_Pi_succ⟩⟩
  · intro hx
    rcases Set.mem_iUnion₂.mp hx with ⟨J, hJ, hxJ⟩
    have hJ_mem_finset : J ∈ P.intervals := hJ
    have hJ_cases : J ∈ Finset.image (fun (i : Fin n) => Ico (P.x i.castSucc) (P.x i.succ)) Finset.univ ∨ J ∈ {Icc I.b I.b} :=
      Finset.mem_union.mp hJ_mem_finset
    rcases hJ_cases with (hJ_img | hJ_sing)
    · rcases Finset.mem_image.mp hJ_img with ⟨i, _, rfl⟩
      rw [hI]
      have hxJ_pair : x ∈ Set.Ico (P.x i.castSucc) (P.x i.succ) := by
        simpa using hxJ
      rcases hxJ_pair with ⟨hxJ_low, hxJ_high⟩
      -- Show I.a ≤ x
      have h_cast_val_nat : (0 : ℕ) ≤ i.val := Nat.zero_le _
      have h_cast_val : (0 : Fin (n+1)).val ≤ (i.castSucc : Fin (n+1)).val := by
        simpa using h_cast_val_nat
      have h_cast : P.x 0 ≤ P.x i.castSucc := P.x_mono.monotone h_cast_val
      have hx_lower : I.a ≤ x := le_trans (le_trans (by rw [P.x_start]) h_cast) hxJ_low
      -- Show x ≤ I.b
      have h_succ_val_nat : i.val + 1 ≤ n := by
        have : i.val < n := Fin.is_lt i; omega
      have h_succ_val : (i.succ : Fin (n+1)).val ≤ (Fin.last n : Fin (n+1)).val := by
        simpa using h_succ_val_nat
      have h_succ : P.x i.succ ≤ P.x (Fin.last n) := P.x_mono.monotone h_succ_val
      have hx_upper : x ≤ I.b := le_trans (le_of_lt hxJ_high) (le_trans h_succ (by rw [P.x_end]))
      exact ⟨hx_lower, hx_upper⟩
    · have hJ_val : J = Icc I.b I.b := Finset.mem_singleton.mp hJ_sing
      subst hJ_val
      rw [hI]
      have hx_eq_b : x = I.b := by
        have : x ∈ (Icc I.b I.b : Set ℝ) := hxJ
        simp at this; exact this
      subst hx_eq_b
      exact ⟨h_ab, le_refl I.b⟩

/-- Exercise 1.1.23 -/
-- Any function continuous on a nonempty closed interval is Riemann integrable.
lemma RiemannIntegrableOn.continuous {f:ℝ → ℝ} {I: BoundedInterval} (hI: I = Icc I.a I.b) (hcont: ContinuousOn f I.toSet) (h_nonempty : I.toSet.Nonempty) : RiemannIntegrableOn f I := by
  have h_ab : I.a ≤ I.b := by
    rcases h_nonempty with ⟨x, hx⟩; rw [hI, BoundedInterval.toSet] at hx; exact hx.1.trans hx.2
  by_cases hab : I.a < I.b
  · have h_width_pos : 0 < I.b - I.a := sub_pos.mpr hab
    have h_compact : IsCompact (Set.Icc I.a I.b) := isCompact_Icc
    have hcont' : ContinuousOn f (Set.Icc I.a I.b) := by
      rw [hI] at hcont; rw [BoundedInterval.toSet] at hcont; exact hcont
    have h_unif_cont : UniformContinuousOn f (Set.Icc I.a I.b) :=
      h_compact.uniformContinuousOn_of_continuous hcont'
    have h_uc : ∀ ε > 0, ∃ δ > 0, ∀ x y, x ∈ I.toSet → y ∈ I.toSet → |x - y| < δ → |f x - f y| < ε := by
      rw [Metric.uniformContinuousOn_iff] at h_unif_cont
      intro ε hε; rcases h_unif_cont ε hε with ⟨δ, hδ, h⟩
      refine ⟨δ, hδ, λ x y hx hy hxy => ?_⟩
      have hx' : x ∈ Set.Icc I.a I.b := by rw [hI, BoundedInterval.toSet] at hx; exact hx
      have hy' : y ∈ Set.Icc I.a I.b := by rw [hI, BoundedInterval.toSet] at hy; exact hy
      have h_dist : dist x y < δ := by rw [Real.dist_eq]; exact hxy
      have h_val := h x hx' y hy' h_dist; rw [Real.dist_eq] at h_val; exact h_val
    -- Core estimate: for P, Q with small norm, |RS(P)-RS(Q)| < ε
    -- This follows from uniform continuity and a common refinement argument.
    -- The common refinement is constructed by intersecting P and Q subintervals.
    have h_cauchy : ∀ ε > 0, ∃ δ > 0, ∀ (P Q : Sigma (TaggedPartition I)),
        P.snd.norm < δ → Q.snd.norm < δ → |P.snd.RiemannSum f - Q.snd.RiemannSum f| < ε := by
      intro ε hε
      have h_eps_div : 0 < ε / (I.b - I.a) := div_pos hε h_width_pos
      rcases h_uc (ε / (I.b - I.a)) h_eps_div with ⟨δ_uc, hδ_uc_pos, h_uc'⟩
      refine ⟨δ_uc / 2, half_pos hδ_uc_pos, ?_⟩
      intro P Q hP hQ
      set P' := P.snd with hP'_def; set Q' := Q.snd with hQ'_def
      have hP_norm : P'.norm < δ_uc / 2 := hP
      have hQ_norm : Q'.norm < δ_uc / 2 := hQ
      -- Express RS(P') and RS(Q') as sums over overlapping subintervals
      -- This requires constructing the common refinement and proving the bound.
      -- The full proof is deferred; see e.g. Rudin's Principles of Mathematical Analysis, Theorem 7.12.
      sorry
    have h_complete : CompleteSpace ℝ := by infer_instance
    have h_cauchy_filter : Cauchy (Filter.map (fun (a : Sigma (TaggedPartition I)) => a.snd.RiemannSum f)
        (TaggedPartition.nhds_zero I)) := by
      rw [Metric.cauchy_iff]
      constructor
      · haveI : Filter.NeBot (TaggedPartition.nhds_zero I) := TaggedPartition.nhds_zero_neBot I hI hab
        exact Filter.map_neBot
      · intro ε hε
        rcases h_cauchy ε hε with ⟨δ, hδ, h_cauchy⟩
        have h_ball : Metric.ball (0 : ℝ) δ ∈ nhds (0 : ℝ) := by
          rw [Metric.mem_nhds_iff]; exact ⟨δ, hδ, fun x hx => hx⟩
        let N : Set (Sigma (TaggedPartition I)) := {P | P.snd.norm < δ}
        have hN_mem : N ∈ TaggedPartition.nhds_zero I := by
          rw [TaggedPartition.nhds_zero, Filter.mem_comap]
          refine ⟨Metric.ball (0 : ℝ) δ, h_ball, λ P hP => ?_⟩
          have hP_norm_lt_δ : P.snd.norm < δ := by
            have hball : P.snd.norm ∈ Metric.ball (0 : ℝ) δ := hP
            rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hball
            exact (abs_lt.mp hball).2
          simpa [N] using hP_norm_lt_δ
        let t : Set ℝ := (fun (a : Sigma (TaggedPartition I)) => a.snd.RiemannSum f) '' N
        have ht_mem : t ∈ Filter.map (fun a : Sigma (TaggedPartition I) => a.snd.RiemannSum f)
            (TaggedPartition.nhds_zero I) := by
          rw [Filter.mem_map]; apply Filter.mem_of_superset hN_mem
          intro P hP; exact ⟨P, hP, rfl⟩
        refine ⟨t, ht_mem, ?_⟩
        intro x hx y hy; rcases hx with ⟨P, hP, rfl⟩; rcases hy with ⟨Q, hQ, rfl⟩
        rw [Real.dist_eq]; exact h_cauchy P Q (by simpa [N] using hP) (by simpa [N] using hQ)
    rcases h_complete.complete h_cauchy_filter with ⟨R, hR⟩
    refine ⟨hI, h_nonempty, ⟨R, hR⟩⟩
  · have heq : I.a = I.b := by linarith
    exact (RiemannIntegrable.of_zero_length f (a := I.a) (by rw [hI, heq])).1

-- A function that is continuous on each piece of a partition is Riemann integrable on the whole interval.
/- The original statement omitted nonemptiness of `I`, so it was false for an empty closed
interval and the empty partition.  The corrected statement follows. -/
lemma RiemannIntegrableOn.piecewise_continuous {f:ℝ → ℝ} {I: BoundedInterval}
    (hI: I = Icc I.a I.b) (h_nonempty : I.toSet.Nonempty)
    (T: Finset BoundedInterval)
    (hdisjoint: (T : Set BoundedInterval).PairwiseDisjoint BoundedInterval.toSet)
    (hcover : I.toSet = ⋃ J ∈ T, J.toSet)
    (hcont: ∀ J ∈ T, ContinuousOn f J.toSet) : RiemannIntegrableOn f I := by sorry

/-- Exercise 1.1.24 (a) (scalar multiple, integrability). -/
-- A scalar multiple of a Riemann integrable function is Riemann integrable.
theorem RiemannIntegrableOn.smul {I: BoundedInterval} (c:ℝ) {f: ℝ → ℝ} (h: RiemannIntegrableOn f I) : RiemannIntegrableOn (c • f) I := by
  rcases h.2.2 with ⟨R, hR⟩
  refine ⟨h.1, h.2.1, ⟨c • R, ?_⟩⟩
  dsimp [riemann_integral_eq, TaggedPartition.nhds_zero] at hR ⊢
  have h_smul_RiemannSum : ∀ {n:ℕ} (P: TaggedPartition I n), P.RiemannSum (c • f) = c • P.RiemannSum f := by
    intro n P
    unfold TaggedPartition.RiemannSum
    simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  simpa [h_smul_RiemannSum] using (hR.const_smul c)

/-- Exercise 1.1.24 (a) (scalar multiple, integral). -/
-- The integral of a scalar multiple: integral(c * f) = c * integral(f).
theorem riemann_integral_smul {I:BoundedInterval} (c:ℝ) {f: ℝ → ℝ} (h: RiemannIntegrableOn f I) : riemannIntegral (c • f) I = c • (riemannIntegral f I) := by
  have h_smul_RiemannSum : ∀ {n:ℕ} (P: TaggedPartition I n), P.RiemannSum (c • f) = c • P.RiemannSum f := by
    intro n P
    unfold TaggedPartition.RiemannSum
    simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  have hRf : riemann_integral_eq f I (riemannIntegral f I) :=
    riemann_integral_of_integrable h
  have h_smul_int : c • riemannIntegral f I = riemannIntegral (c • f) I :=
    (riemann_integral_eq_iff_of_integrable (RiemannIntegrableOn.smul c h) (c • riemannIntegral f I)).mp (by
      dsimp [riemann_integral_eq, TaggedPartition.nhds_zero] at hRf ⊢
      simpa [h_smul_RiemannSum] using (hRf.const_smul c))
  exact h_smul_int.symm

/-- Exercise 1.1.24 (a) (sum, integrability). -/
-- The sum of two Riemann integrable functions is Riemann integrable.
theorem RiemannIntegrableOn.add {I: BoundedInterval} {f g: ℝ → ℝ} (hf: RiemannIntegrableOn f I) (hg: RiemannIntegrableOn g I) : RiemannIntegrableOn (f + g) I := by
  rcases hf.2.2 with ⟨Rf, hRf⟩
  rcases hg.2.2 with ⟨Rg, hRg⟩
  refine ⟨hf.1, hf.2.1, ⟨Rf + Rg, ?_⟩⟩
  dsimp [riemann_integral_eq, TaggedPartition.nhds_zero]
  have h_add_RiemannSum : ∀ {n:ℕ} (P: TaggedPartition I n), P.RiemannSum (f + g) = P.RiemannSum f + P.RiemannSum g := by
    intro n P
    unfold TaggedPartition.RiemannSum
    simp [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  simpa [h_add_RiemannSum] using (hRf.add hRg)

/-- Exercise 1.1.24 (a) (sum, integral). -/
-- The integral of a sum: integral(f + g) = integral(f) + integral(g).
theorem riemann_integral_add {I: BoundedInterval} {f g: ℝ → ℝ} (hf: RiemannIntegrableOn f I) (hg: RiemannIntegrableOn g I) : riemannIntegral (f+g) I = riemannIntegral f I + riemannIntegral g I := by
  have h_add_RiemannSum : ∀ {n:ℕ} (P: TaggedPartition I n), P.RiemannSum (f + g) = P.RiemannSum f + P.RiemannSum g := by
    intro n P
    unfold TaggedPartition.RiemannSum
    simp [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  have hRf : riemann_integral_eq f I (riemannIntegral f I) := riemann_integral_of_integrable hf
  have hRg : riemann_integral_eq g I (riemannIntegral g I) := riemann_integral_of_integrable hg
  have h_add_int : riemannIntegral f I + riemannIntegral g I = riemannIntegral (f + g) I :=
    (riemann_integral_eq_iff_of_integrable (RiemannIntegrableOn.add hf hg) (riemannIntegral f I + riemannIntegral g I)).mp (by
      dsimp [riemann_integral_eq, TaggedPartition.nhds_zero]
      simpa [h_add_RiemannSum] using (hRf.add hRg))
  exact h_add_int.symm

/-- Exercise 1.1.24 (b) (Monotonicity of the piecewise constant integral) -/
-- The integral is monotone: if f ≤ g pointwise, then integral(f) ≤ integral(g).
theorem riemann_integral_mono {I: BoundedInterval} {f g: ℝ → ℝ} (hf: RiemannIntegrableOn f I) (hg: RiemannIntegrableOn g I) (hmono: ∀ x ∈ I.toSet, f x ≤ g x): riemannIntegral f I ≤ riemannIntegral g I := by
  have hRf : riemann_integral_eq f I (riemannIntegral f I) := riemann_integral_of_integrable hf
  have hRg : riemann_integral_eq g I (riemannIntegral g I) := riemann_integral_of_integrable hg
  by_cases h_eq : I.a = I.b
  · -- Zero-length case: both integrals are 0
    have h_len : |I|ₗ = 0 := by
      unfold BoundedInterval.length
      simp [h_eq]
    have hRf0 : riemannIntegral f I = 0 := riemann_integral_eq_zero_of_zero_length h_eq h_len hRf
    have hRg0 : riemannIntegral g I = 0 := riemann_integral_eq_zero_of_zero_length h_eq h_len hRg
    rw [hRf0, hRg0]
  · -- Positive length case: use filter limit argument
    have hI : I = Icc I.a I.b := hf.1
    have hlt : I.a < I.b := by
      have h_nonempty : I.toSet.Nonempty := hf.2.1
      rw [hI] at h_nonempty
      rcases h_nonempty.choose_spec with ⟨h_left, h_right⟩
      have hIab : I.a ≤ I.b := le_trans h_left h_right
      by_contra! hge
      -- hge : I.b ≤ I.a
      have h_eq' : I.a = I.b := le_antisymm hIab hge
      exact h_eq h_eq'
    haveI : Filter.NeBot (TaggedPartition.nhds_zero I) :=
      TaggedPartition.nhds_zero_neBot I hI hlt
    have h_RS_sum_le : ∀ {n:ℕ} (P: TaggedPartition I n), P.RiemannSum f ≤ P.RiemannSum g := by
      intro n P
      unfold TaggedPartition.RiemannSum
      refine Finset.sum_le_sum ?_
      intro i hi
      have hx_in_I : P.x_tag i ∈ I.toSet := by
        have h_btw := P.x_tag_between i
        have hx0 : P.x 0 = I.a := P.x_start
        have hx_last : P.x (Fin.last n) = I.b := P.x_end
        have h_low : I.a ≤ P.x_tag i := by
          calc
            I.a = P.x 0 := by rw [hx0]
            _ ≤ P.x i.castSucc := P.x_mono.monotone (by exact Fin.zero_le _)
            _ ≤ P.x_tag i := h_btw.1
        have h_high : P.x_tag i ≤ I.b := by
          calc
            P.x_tag i ≤ P.x i.succ := h_btw.2
            _ ≤ P.x (Fin.last n) := P.x_mono.monotone (by exact Fin.le_last _)
            _ = I.b := by rw [hx_last]
        have hx_mem : P.x_tag i ∈ (Icc I.a I.b).toSet := by
          unfold BoundedInterval.toSet
          exact ⟨h_low, h_high⟩
        have hI_set : (Icc I.a I.b).toSet = I.toSet := hI.symm ▸ rfl
        rw [hI_set] at hx_mem
        exact hx_mem
      have h_delta_nonneg : 0 ≤ P.delta i := by
        dsimp [TaggedPartition.delta]
        have h_lt_fin : i.castSucc < i.succ := by
          apply Fin.castSucc_lt_succ
        have h_x_lt : P.x i.castSucc < P.x i.succ := P.x_mono h_lt_fin
        linarith
      have hfx_le_gx : f (P.x_tag i) ≤ g (P.x_tag i) := hmono (P.x_tag i) hx_in_I
      nlinarith
    have h_sum_le_eventually : (fun (P : Sigma (TaggedPartition I)) => P.snd.RiemannSum f) ≤ᶠ[TaggedPartition.nhds_zero I]
      (fun (P : Sigma (TaggedPartition I)) => P.snd.RiemannSum g) := by
      refine Filter.eventually_of_mem Filter.univ_mem ?_
      intro P hP
      exact h_RS_sum_le P.snd
    exact le_of_tendsto_of_tendsto hRf hRg h_sum_le_eventually

/-- Exercise 1.1.24 (c) (Indicator functions) -/
-- The indicator function of a Jordan measurable set is Riemann integrable.
/- The original statement omitted the validity conditions on `I`, and is false for
`I = Icc 1 0` even when `E = ∅`.  The corrected statement follows. -/
theorem RiemannIntegrableOn.indicator_of_elem (I: BoundedInterval) {E:Set ℝ}
    (hI : I = Icc I.a I.b) (h_nonempty : I.toSet.Nonempty)
    (hE: JordanMeasurable (Real.equiv_EuclideanSpace' '' E)) :
    RiemannIntegrableOn E.indicator' I := by sorry

/-- Exercise 1.1.24 (c) (Piecewise constant integral of indicator functions) -/
-- The integral of an indicator function equals the measure of the set it indicates.
/- The original statement allowed a non-closed interval `I`.  Then `riemannIntegral` has its
junk value `0`, while a positive-measure elementary subset of `I` can exist.  The corrected
statement follows. -/
theorem riemann_integral_of_elem {I: BoundedInterval} {E:Set ℝ}
    (hI : I = Icc I.a I.b) (h_nonempty : I.toSet.Nonempty)
    (hE: JordanMeasurable (Real.equiv_EuclideanSpace' '' E)) (hsub: E ⊆ I.toSet) :
    riemannIntegral E.indicator' I = hE.measure := by sorry

/-- Exercise 1.1.24 (Uniqueness) -/
-- The Riemann integral is the unique integral satisfying linearity, monotonicity, and normalization on indicator functions.
theorem riemann_integral_unique {I: BoundedInterval} (integ: (ℝ → ℝ) → ℝ)
  (hsmul: ∀ (c:ℝ) (f: ℝ → ℝ) (hf: RiemannIntegrableOn f I), integ (c • f) = c • (integ f))
  (hadd: ∀ (f g: ℝ → ℝ) (hf: RiemannIntegrableOn f I) (hg: RiemannIntegrableOn g I), integ (f + g) = integ f + integ g)
  (hmono: ∀ (f g: ℝ → ℝ) (hf: RiemannIntegrableOn f I) (hg: RiemannIntegrableOn g I) (hmono: ∀ x ∈ I.toSet, f x ≤ g x), integ f ≤ integ g)
  (hindicator: ∀ (E:Set ℝ) (hE: JordanMeasurable (Real.equiv_EuclideanSpace' '' E) ) (hsub: E ⊆ I.toSet), integ E.indicator' = hE.measure) :
  ∀ f, RiemannIntegrableOn f I → integ f = riemannIntegral f I := by sorry

/-- Exercise 1.1.25 (Area interpretation of Riemann integral) -/
-- The region under the graph of a Riemann integrable function is Jordan measurable.
theorem RiemannIntegrableOn.measurable_upper {I: BoundedInterval}
  {f: ℝ → ℝ} (hfint: RiemannIntegrableOn f I) :
  JordanMeasurable { p:EuclideanSpace' 2 | p 0 ∈ I.toSet ∧ 0 ≤ p 1 ∧ p 1 ≤ f (p 0) } := by sorry

/-- Exercise 1.1.25 (Area interpretation of Riemann integral) -/
-- The region below the graph of a Riemann integrable function is Jordan measurable.
theorem RiemannIntegrableOn.measurable_lower {I: BoundedInterval}
  {f: ℝ → ℝ} (hfint: RiemannIntegrableOn f I) :
  JordanMeasurable { p:EuclideanSpace' 2 | p 0 ∈ I.toSet ∧ f (p 0) ≤ p 1 ∧ p 1 ≤ 0 } := by sorry

/-- Exercise 1.1.25 (Area interpretation of Riemann integral) -/
-- A function is Riemann integrable iff the regions above and below its graph are both Jordan measurable.
/- The original statement omitted nonemptiness of `I`; for an empty closed interval both
regions are empty and Jordan measurable, but `RiemannIntegrableOn` is false. -/
theorem JordanMeasurable.iff_integrable {I: BoundedInterval} (hI: I = Icc I.a I.b)
  (h_nonempty : I.toSet.Nonempty) {f: ℝ → ℝ}
  (hf: ∃ M, ∀ x ∈ I.toSet, |f x| ≤ M) : RiemannIntegrableOn f I ↔
  JordanMeasurable { p:EuclideanSpace' 2 | p 0 ∈ I.toSet ∧ 0 ≤ p 1 ∧ p 1 ≤ f (p 0) } ∧
  JordanMeasurable { p:EuclideanSpace' 2 | p 0 ∈ I.toSet ∧ f (p 0) ≤ p 1 ∧ p 1 ≤ 0 }
  := by sorry

/-- Exercise 1.1.25 (Area interpretation of Riemann integral) -/
-- The Riemann integral equals the difference between the measures of the upper and lower regions.
theorem RiemannIntegrableOn.eq_measure {I: BoundedInterval}
  {f: ℝ → ℝ} (hfint: RiemannIntegrableOn f I) :
  riemannIntegral f I = hfint.measurable_upper.measure - hfint.measurable_lower.measure := by sorry


/-- Exercise 1.1.22 -/
-- For Riemann integrable functions, the Riemann integral equals the Darboux integral.
lemma riemann_integral_eq_darboux_integral {f:ℝ → ℝ} {I: BoundedInterval} (hf: RiemannIntegrableOn f I) : riemannIntegral f I = darbouxIntegral f I := by
  have hI : I = Icc I.a I.b := hf.1
  have h_nonempty : I.toSet.Nonempty := hf.2.1
  rcases hf.2.2 with ⟨R, hR⟩
  have hR' : riemannIntegral f I = R := ((riemann_integral_eq_iff_of_integrable hf R).mp hR).symm
  rw [darbouxIntegral]
  by_cases h_eq : I.a = I.b
  · rcases RiemannIntegrable.bounded hf with ⟨M, hM⟩
    have h_len : |I|ₗ = 0 := by unfold BoundedInterval.length; simp [h_eq]
    have hR_zero : R = 0 := riemann_integral_eq_zero_of_zero_length h_eq h_len hR
    have h_all_zero (g : PiecewiseConstantFunction I) : g.integral = 0 := by
      have h_total : |I|ₗ = ∑ J : g.T, |J.val|ₗ := BoundedInterval.length_of_partition I g.T g.cover g.disjoint
      have h_zero_sum : ∑ J : g.T, |J.val|ₗ = 0 := by rw [← h_total, h_len]
      have h_nonneg_len : ∀ J : g.T, 0 ≤ |J.val|ₗ := fun J => BoundedInterval.length_nonneg J.val
      have h_all_len : ∀ J : g.T, |J.val|ₗ = 0 := by
        intro J
        have h_conv : ∑ J' : g.T, |J'.val|ₗ = ∑ J' ∈ g.T, |J'|ₗ := by
          simpa using Finset.sum_attach (s := g.T) (f := fun (J : BoundedInterval) => |J|ₗ)
        rw [h_conv] at h_zero_sum
        have h_term : |J.val|ₗ ≤ ∑ J' ∈ g.T, |J'|ₗ :=
          Finset.single_le_sum (fun J' hJ' => BoundedInterval.length_nonneg J') J.property
        rw [h_zero_sum] at h_term; nlinarith [BoundedInterval.length_nonneg J.val]
      unfold PiecewiseConstantFunction.integral; simp [h_all_len]
    have h_lower_zero : LowerDarbouxIntegral f I = 0 := by
      apply le_antisymm
      · apply csSup_le
        · let g0 := PiecewiseConstantFunction.mkConst I (-M)
          have hg0 : ∀ x ∈ I.toSet, g0.f x ≤ f x := by
            intro x hx; have ha : |f x| ≤ M := hM x hx
            simp [g0, PiecewiseConstantFunction.mkConst]; rcases abs_le.mp ha with ⟨h1, _⟩; linarith
          exact ⟨g0.integral, g0, rfl, hg0⟩
        · intro r hr; rcases hr with ⟨g, rfl, _⟩; rw [h_all_zero g]
      · have h0m : (0 : ℝ) ∈ {R | ∃ g : PiecewiseConstantFunction I, g.integral = R ∧ ∀ x ∈ I.toSet, g.f x ≤ f x} := by
          let g0 := PiecewiseConstantFunction.mkConst I (-M)
          have hg0 : ∀ x ∈ I.toSet, g0.f x ≤ f x := by
            intro x hx; have ha : |f x| ≤ M := hM x hx
            simp [g0, PiecewiseConstantFunction.mkConst]; rcases abs_le.mp ha with ⟨h1, _⟩; linarith
          have hi0 : g0.integral = 0 := h_all_zero g0
          exact ⟨g0, hi0, hg0⟩
        exact le_csSup (LowerDarbouxIntegral.bddAbove M hM) h0m
    rw [hR', hR_zero, h_lower_zero.symm]
  · have h_lt : I.a < I.b := by
      rw [hI] at h_nonempty
      rcases h_nonempty with ⟨x, hx1, hx2⟩
      by_contra! hge
      have : I.a = I.b := by linarith
      exact h_eq this
    rcases RiemannIntegrable.bounded hf with ⟨M, hM⟩
    have h_eps_delta : ∀ ε > 0, ∃ δ > 0, ∀ n, ∀ (P : TaggedPartition I n), P.norm ≤ δ → |P.RiemannSum f - R| ≤ ε :=
      (riemann_integral_eq_iff R).mp hR
    have h_lower_upper : LowerDarbouxIntegral f I ≤ UpperDarbouxIntegral f I :=
      lower_darboux_le_upper_darboux ⟨M, hM⟩
    sorry
/- Exercise 1.1.26: Extend the definition of the Riemann and Darboux integrals to higher dimensions, in such a way that analogues of all the previous results hold; state and prove those analogues. -/
