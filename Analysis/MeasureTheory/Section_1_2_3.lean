import Analysis.MeasureTheory.Section_1_2_2

/-!
# Introduction to Measure Theory, Section 1.2.3: Non-measurable sets

A companion to (the introduction to) Section 1.2.3 of the book "An introduction to Measure Theory".

-/

open scoped Pointwise

/-! ## Vitali Set Construction

We construct a Vitali set by choosing representatives from each coset of ℝ/ℚ
that intersects \[0,1\]. The key is that ℚ acts on ℝ by translation, and this
partitions ℝ into countably many disjoint translates of any transversal.
-/

/-- The additive subgroup of ℚ in ℝ -/
def Rat.addSubgroup : AddSubgroup ℝ where
  carrier := Set.range ((↑) : ℚ → ℝ)
  add_mem' := by
    intro a b ⟨qa, ha⟩ ⟨qb, hb⟩
    exact ⟨qa + qb, by simp [ha, hb]⟩
  zero_mem' := ⟨0, by simp⟩
  neg_mem' := by
    intro a ⟨q, hq⟩
    exact ⟨-q, by simp [hq]⟩

/-- The quotient group ℝ/ℚ (reals modulo rationals) -/
abbrev RealModRat := ℝ ⧸ Rat.addSubgroup

/-- ℚ is dense in ℝ, so every coset of ℝ/ℚ intersects \[0,1\] -/
lemma coset_intersects_unit_interval (c : RealModRat) :
    ∃ x : ℝ, x ∈ Set.Icc 0 1 ∧ QuotientAddGroup.mk (s := Rat.addSubgroup) x = c := by
  obtain ⟨r⟩ := c
  -- r is a representative of the coset c
  -- By density of ℚ, find q ∈ ℚ such that r - q ∈ [0,1]
  have hdense : Dense (Set.range ((↑) : ℚ → ℝ)) := Rat.isDenseEmbedding_coe_real.dense
  -- The set {r - t : t ∈ (0,1)} is open and nonempty, so contains a rational
  have h_open : IsOpen (Set.Ioo (r - 1) r) := isOpen_Ioo
  have h_nonempty : Set.Nonempty (Set.Ioo (r - 1) r) := by
    use r - 1/2; constructor <;> linarith
  obtain ⟨q_real, ⟨hq_rat, hq_in⟩⟩ := hdense.exists_mem_open h_open h_nonempty
  obtain ⟨q, rfl⟩ := hq_rat
  use r - q
  constructor
  · constructor
    · linarith [hq_in.2]
    · linarith [hq_in.1]
  · -- r - q is in the same coset as r
    show QuotientAddGroup.mk (s := Rat.addSubgroup) (r - (q : ℝ)) =
         Quot.mk (QuotientAddGroup.leftRel Rat.addSubgroup) r
    have heq : (QuotientAddGroup.mk (s := Rat.addSubgroup) (r - (q : ℝ))) =
           (QuotientAddGroup.mk (s := Rat.addSubgroup) r) := by
      rw [QuotientAddGroup.eq]
      -- Need to show: -(r - q) + r ∈ Rat.addSubgroup
      -- That is: q ∈ Rat.addSubgroup
      show -(r - ↑q) + r ∈ Rat.addSubgroup
      simp only [neg_sub, sub_add_cancel]
      exact ⟨q, rfl⟩
    rw [heq]
    rfl

/-- The Vitali set: choose one representative from each coset that lies in \[0,1\] -/
noncomputable def VitaliSet : Set ℝ :=
  Set.range (fun c : RealModRat => (coset_intersects_unit_interval c).choose)

/-- Each element of the Vitali set is in \[0,1\] -/
lemma VitaliSet_subset_unit_interval : VitaliSet ⊆ Set.Icc 0 1 := by
  intro x hx
  obtain ⟨c, rfl⟩ := hx
  exact (coset_intersects_unit_interval c).choose_spec.1

/-- Key lemma: \[0,1\] is covered by translates of E by rationals in \[-1,1\] -/
lemma unit_interval_covered_by_translates :
    Set.Icc (0:ℝ) 1 ⊆ ⋃ (q : ℚ) (_ : q ∈ Set.Icc (-1:ℚ) 1), (VitaliSet + {(q:ℝ)}) := by
  intro y hy
  -- y is in some coset c of ℝ/ℚ
  let c : RealModRat := QuotientAddGroup.mk (s := Rat.addSubgroup) y
  -- The Vitali set contains an element x representing coset c
  let x := (coset_intersects_unit_interval c).choose
  have hx_in : x ∈ Set.Icc 0 1 := (coset_intersects_unit_interval c).choose_spec.1
  have hx_coset : QuotientAddGroup.mk (s := Rat.addSubgroup) x = c :=
    (coset_intersects_unit_interval c).choose_spec.2
  -- x and y are in the same coset, so y - x ∈ ℚ
  have h_same_coset : QuotientAddGroup.mk (s := Rat.addSubgroup) x =
      QuotientAddGroup.mk (s := Rat.addSubgroup) y := hx_coset
  rw [QuotientAddGroup.eq] at h_same_coset
  obtain ⟨q, hq⟩ := h_same_coset
  -- So y = x + q for some rational q
  have hy_eq : y = x + q := by linarith [hq]
  -- Since x, y ∈ [0,1], we have q = y - x ∈ [-1,1]
  have hq_bound : (q : ℝ) ∈ Set.Icc (-1) 1 := by
    constructor
    · have h1 : (q : ℝ) = y - x := by linarith [hy_eq]
      linarith [hy.1, hx_in.2]
    · have h1 : (q : ℝ) = y - x := by linarith [hy_eq]
      linarith [hy.2, hx_in.1]
  have hq_bound_rat : q ∈ Set.Icc (-1:ℚ) 1 := by
    constructor
    · have : (-1 : ℝ) ≤ q := hq_bound.1
      exact_mod_cast this
    · have : (q : ℝ) ≤ 1 := hq_bound.2
      exact_mod_cast this
  -- Therefore y ∈ E + {q}
  rw [Set.mem_iUnion]
  use q
  rw [Set.mem_iUnion]
  use hq_bound_rat
  rw [Set.mem_add]
  use x
  constructor
  · exact ⟨c, rfl⟩
  use (q : ℝ)
  constructor
  · rfl
  · linarith [hy_eq]

/-- The rationals in \[-1,1\] are countable -/
lemma rat_Icc_countable : Set.Countable {q : ℚ | q ∈ Set.Icc (-1:ℚ) 1} := by
  exact Set.countable_univ.mono (Set.subset_univ _)

/-- The Lebesgue measure of a closed interval \[a,b\] in ℝ (embedded in {lean}`EuclideanSpace' 1`) equals b - a -/
lemma Lebesgue_measure.Icc_eq (a b : ℝ) (hab : a ≤ b) :
    Lebesgue_measure (Real.equiv_EuclideanSpace' '' Set.Icc a b) = (b - a : ℝ) := by
  -- Use the fact that Set.Icc a b = (BoundedInterval.Icc a b).toSet
  have h_interval : Set.Icc a b = (BoundedInterval.Icc a b).toSet := by rfl
  -- And (I:Box 1).toSet = Real.equiv_EuclideanSpace' '' I.toSet
  have h_box : Real.equiv_EuclideanSpace' '' Set.Icc a b = (BoundedInterval.Icc a b : Box 1).toSet := by
    rw [h_interval, ← BoundedInterval.coe_of_box]
  rw [h_box]
  -- Now use Lebesgue_outer_measure.elementary (Lebesgue_measure = Lebesgue_outer_measure)
  have hE : IsElementary (BoundedInterval.Icc a b : Box 1).toSet := IsElementary.box _
  unfold Lebesgue_measure
  rw [Lebesgue_outer_measure.elementary _ hE, IsElementary.measure_of_box]
  -- Box volume = product of side lengths = b - a for 1D
  simp only [Box.volume, Finset.univ_unique, Fin.default_eq_zero, Finset.prod_singleton]
  simp only [BoundedInterval.length, BoundedInterval.b, BoundedInterval.a]
  -- max (b - a) 0 = b - a since a ≤ b
  rw [max_eq_left (sub_nonneg.mpr hab)]

/-- The Vitali set (lifted to {lean}`EuclideanSpace' 1`) is not Lebesgue measurable.
    This is the core of Proposition 1.2.18. -/
theorem VitaliSet.nonmeasurable : ¬ LebesgueMeasurable (Real.equiv_EuclideanSpace' '' VitaliSet) := by
  let E := Real.equiv_EuclideanSpace' '' VitaliSet
  intro hE_meas
  -- The rationals in [-1,1] form a denumerable set
  have hQ_countable : Set.Countable {q : ℚ | q ∈ Set.Icc (-1:ℚ) 1} := rat_Icc_countable
  have hQ_inf : Set.Infinite {q : ℚ | q ∈ Set.Icc (-1:ℚ) 1} :=
    Set.Icc_infinite (by norm_num : (-1:ℚ) < 1)
  -- Get bijection from ℕ to the subtype using Denumerable structure
  haveI : Infinite {q : ℚ | q ∈ Set.Icc (-1:ℚ) 1} := hQ_inf.to_subtype
  haveI : Countable {q : ℚ | q ∈ Set.Icc (-1:ℚ) 1} := hQ_countable.to_subtype
  haveI denumQ : Denumerable {q : ℚ | q ∈ Set.Icc (-1:ℚ) 1} := (nonempty_denumerable _).some
  -- The equivalence ℕ ≃ {q : ℚ | q ∈ [-1,1]}
  let eqvQ : {q : ℚ | q ∈ Set.Icc (-1:ℚ) 1} ≃ ℕ := Denumerable.eqv _
  -- f : ℕ → ℚ is the injective enumeration of rationals in [-1,1]
  let f : ℕ → ℚ := fun n => (eqvQ.symm n : ℚ)
  -- f is injective
  have hf_inj : Function.Injective f := Subtype.val_injective.comp eqvQ.symm.injective
  -- f n is in [-1,1] for all n
  have hf_mem : ∀ n, f n ∈ Set.Icc (-1:ℚ) 1 := fun n => (eqvQ.symm n).2
  -- f has range = {q | q ∈ [-1,1]}
  have hf_range : {q | q ∈ Set.Icc (-1:ℚ) 1} = Set.range f := by
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_range, f]
    constructor
    · intro hq
      let q' : {q : ℚ | q ∈ Set.Icc (-1:ℚ) 1} := ⟨q, hq⟩
      refine ⟨eqvQ q', ?_⟩
      simp only [Equiv.symm_apply_apply]
      rfl
    · intro ⟨n, hn⟩
      rw [← hn]
      exact (eqvQ.symm n).2
  -- Define the family of translates
  let qSeq : ℕ → ℚ := f
  let translateE : ℕ → Set (EuclideanSpace' 1) := fun n => E + {Real.equiv_EuclideanSpace' (qSeq n)}
  -- Each translate is measurable by translation invariance
  have hmes : ∀ n, LebesgueMeasurable (translateE n) := fun n =>
    (LebesgueMeasurable.translate E _).mp hE_meas
  -- Translates are pairwise disjoint
  have hdisj : Set.univ.PairwiseDisjoint translateE := by
    intro i _ j _ hij
    simp only [Function.onFun, Set.disjoint_iff]
    intro z ⟨hz1, hz2⟩
    -- z ∈ E + {q_i} and z ∈ E + {q_j}
    rw [Set.mem_add] at hz1 hz2
    obtain ⟨x1, hx1, r1, hr1, hz1_eq⟩ := hz1
    obtain ⟨x2, hx2, r2, hr2, hz2_eq⟩ := hz2
    rw [Set.mem_singleton_iff] at hr1 hr2
    subst hr1 hr2
    -- x1, x2 ∈ E = Real.equiv_EuclideanSpace' '' VitaliSet
    obtain ⟨v1, hv1, hx1_eq⟩ := hx1
    obtain ⟨v2, hv2, hx2_eq⟩ := hx2
    -- z = x1 + Real.equiv_EuclideanSpace' (qSeq i)
    -- z = x2 + Real.equiv_EuclideanSpace' (qSeq j)
    -- Extract the 0-th coordinate to get v1 + qSeq i = v2 + qSeq j
    have heq : v1 + (qSeq i : ℝ) = v2 + (qSeq j : ℝ) := by
      have h1 : z 0 = v1 + (qSeq i : ℝ) := by
        rw [← hz1_eq, ← hx1_eq]
        rfl
      have h2 : z 0 = v2 + (qSeq j : ℝ) := by
        rw [← hz2_eq, ← hx2_eq]
        rfl
      linarith
    -- This means v1 and v2 are in the same coset (differ by a rational)
    have h_same_coset : QuotientAddGroup.mk (s := Rat.addSubgroup) v1 =
        QuotientAddGroup.mk (s := Rat.addSubgroup) v2 := by
      rw [QuotientAddGroup.eq]
      use qSeq i - qSeq j
      simp only [Rat.cast_sub]
      linarith
    -- But VitaliSet has exactly one element from each coset
    obtain ⟨c1, hc1⟩ := hv1
    obtain ⟨c2, hc2⟩ := hv2
    have hc1_spec := (coset_intersects_unit_interval c1).choose_spec.2
    have hc2_spec := (coset_intersects_unit_interval c2).choose_spec.2
    -- c1 = c2 since v1, v2 represent the same coset
    have hc_eq : c1 = c2 := by
      rw [← hc1, ← hc2] at h_same_coset
      rw [← hc1_spec, ← hc2_spec]
      exact h_same_coset
    subst hc_eq
    -- So v1 = v2
    have hv_eq : v1 = v2 := hc1.symm.trans hc2
    -- Therefore qSeq i = qSeq j
    have hq_eq : (qSeq i : ℝ) = qSeq j := by linarith [heq, hv_eq]
    -- So i = j (since f is injective)
    have hqi_eq : qSeq i = qSeq j := Rat.cast_injective hq_eq
    exact hij (hf_inj hqi_eq)
  -- By countable additivity
  have h_union_measure : Lebesgue_measure (⋃ n, translateE n) = ∑' n, Lebesgue_measure (translateE n) :=
    Lebesgue_measure.countable_union hmes hdisj
  -- By translation invariance, all translates have the same measure
  have h_translate_measure : ∀ n, Lebesgue_measure (translateE n) = Lebesgue_measure E := fun n =>
    Lebesgue_measure.translate _ hE_meas
  -- We proceed by cases on whether m(E) = 0
  by_cases hE_zero : Lebesgue_measure E = 0
  · -- Case m(E) = 0: Then m(⋃) = 0, but ⋃ covers [0,1], so m(⋃) ≥ 1
    have h_sum_zero : ∑' n, Lebesgue_measure (translateE n) = 0 := by
      simp only [h_translate_measure, hE_zero]
      exact tsum_zero
    rw [h_sum_zero] at h_union_measure
    -- The union covers [0,1] (after conversion)
    have h_cover : Real.equiv_EuclideanSpace' '' Set.Icc 0 1 ⊆ ⋃ n, translateE n := by
      intro z hz
      obtain ⟨y, hy, rfl⟩ := hz
      -- y ∈ [0,1], so by unit_interval_covered_by_translates, y ∈ ⋃_q (VitaliSet + {q})
      have hy_covered := unit_interval_covered_by_translates hy
      rw [Set.mem_iUnion] at hy_covered
      obtain ⟨q, hq⟩ := hy_covered
      rw [Set.mem_iUnion] at hq
      obtain ⟨hq_bound, hy_mem⟩ := hq
      -- q ∈ [-1,1], so q = f n for some n
      have hq_in_range : q ∈ {r : ℚ | r ∈ Set.Icc (-1:ℚ) 1} := hq_bound
      rw [hf_range] at hq_in_range
      obtain ⟨n, rfl⟩ := hq_in_range
      rw [Set.mem_iUnion]
      use n
      -- y ∈ VitaliSet + {q}, so Real.equiv_EuclideanSpace' y ∈ E + {Real.equiv_EuclideanSpace' q}
      rw [Set.mem_add] at hy_mem ⊢
      obtain ⟨v, hv, r, hr, hy_eq⟩ := hy_mem
      rw [Set.mem_singleton_iff] at hr
      subst hr
      use Real.equiv_EuclideanSpace' v
      constructor
      · exact ⟨v, hv, rfl⟩
      use Real.equiv_EuclideanSpace' (f n : ℝ)
      constructor
      · rfl
      · ext i
        fin_cases i
        -- Goal: (Real.equiv_EuclideanSpace' v + Real.equiv_EuclideanSpace' (f n)) 0 = Real.equiv_EuclideanSpace' y 0
        -- Both sides equal y by hy_eq: v + f n = y
        have hlhs : (Real.equiv_EuclideanSpace' v + Real.equiv_EuclideanSpace' (f n : ℝ)) ⟨0, by omega⟩ = v + (f n : ℝ) := rfl
        have hrhs : (Real.equiv_EuclideanSpace' y) ⟨0, by omega⟩ = y := rfl
        rw [hlhs, hrhs, hy_eq]
    -- m(Image [0,1]) = 1
    have h_interval_measure : Lebesgue_measure (Real.equiv_EuclideanSpace' '' Set.Icc 0 1) = 1 := by
      rw [Lebesgue_measure.Icc_eq 0 1 (by norm_num)]
      norm_num
    have h_ge_one : Lebesgue_measure (⋃ n, translateE n) ≥ 1 := by
      calc Lebesgue_measure (⋃ n, translateE n)
          ≥ Lebesgue_measure (Real.equiv_EuclideanSpace' '' Set.Icc 0 1) :=
            Lebesgue_outer_measure.mono h_cover
        _ = 1 := h_interval_measure
    rw [h_union_measure] at h_ge_one
    -- 1 ≤ 0 is a contradiction
    exact absurd h_ge_one (by norm_num : ¬(1 : EReal) ≤ 0)
  · -- Case m(E) > 0: Then ∑ m(E) = ∞, but m(⋃) ≤ 3
    -- The measure is nonnegative
    have hE_nonneg : 0 ≤ Lebesgue_measure E := Lebesgue_outer_measure.nonneg E
    have hE_pos : 0 < Lebesgue_measure E := by
      cases' (hE_nonneg.lt_or_eq) with h h
      · exact h
      · exact absurd h.symm hE_zero
    -- The sum of infinitely many positive values is ∞
    have h_sum_top : ∑' n, Lebesgue_measure (translateE n) = ⊤ := by
      simp only [h_translate_measure]
      -- ∑' n, m(E) = ⊤ when m(E) > 0 and we sum over an infinite type
      exact EReal.tsum_const_eq_top_of_pos hE_pos
    rw [h_sum_top] at h_union_measure
    -- But the union is bounded: ⋃ translateE ⊆ [-1,2]
    have h_bounded : ⋃ n, translateE n ⊆ Real.equiv_EuclideanSpace' '' Set.Icc (-1) 2 := by
      intro z hz
      rw [Set.mem_iUnion] at hz
      obtain ⟨n, hz_n⟩ := hz
      rw [Set.mem_add] at hz_n
      obtain ⟨x, hx, r, hr, hz_eq⟩ := hz_n
      rw [Set.mem_singleton_iff] at hr
      subst hr
      obtain ⟨v, hv, rfl⟩ := hx
      -- v ∈ VitaliSet ⊆ [0,1], f n ∈ [-1,1]
      have hv_in := VitaliSet_subset_unit_interval hv
      have hq_bound : f n ∈ Set.Icc (-1:ℚ) 1 := hf_mem n
      use v + (qSeq n : ℝ)
      constructor
      · constructor
        · have h1 : (qSeq n : ℝ) ≥ -1 := by exact_mod_cast hq_bound.1
          linarith [hv_in.1]
        · have h2 : (qSeq n : ℝ) ≤ 1 := by exact_mod_cast hq_bound.2
          linarith [hv_in.2]
      · ext i
        fin_cases i
        -- Goal: Real.equiv_EuclideanSpace' (v + qSeq n) 0 = z 0
        have hlhs : (Real.equiv_EuclideanSpace' (v + (qSeq n : ℝ))) ⟨0, by omega⟩ = v + (qSeq n : ℝ) := rfl
        have hrhs : z ⟨0, by omega⟩ = (Real.equiv_EuclideanSpace' v + Real.equiv_EuclideanSpace' (qSeq n : ℝ)) ⟨0, by omega⟩ := by
          rw [← hz_eq]
        have hrhs' : (Real.equiv_EuclideanSpace' v + Real.equiv_EuclideanSpace' (qSeq n : ℝ)) ⟨0, by omega⟩ = v + (qSeq n : ℝ) := rfl
        rw [hlhs, hrhs, hrhs']
    have h_interval_measure2 : Lebesgue_measure (Real.equiv_EuclideanSpace' '' Set.Icc (-1) 2) = 3 := by
      rw [Lebesgue_measure.Icc_eq (-1) 2 (by norm_num)]
      norm_cast
    have h_le_three : Lebesgue_measure (⋃ n, translateE n) ≤ 3 := by
      calc Lebesgue_measure (⋃ n, translateE n)
          ≤ Lebesgue_measure (Real.equiv_EuclideanSpace' '' Set.Icc (-1) 2) :=
            Lebesgue_outer_measure.mono h_bounded
        _ = 3 := h_interval_measure2
    rw [h_union_measure] at h_le_three
    -- ⊤ ≤ 3 is a contradiction
    have h_three_ne_top : (3 : EReal) ≠ ⊤ := by decide
    exact h_three_ne_top (le_antisymm le_top h_le_three)

/-- Proposition 1.2.18 -/
theorem LebesgueMeasurable.nonmeasurable : ∃ E : Set (EuclideanSpace' 1), E ⊆ Real.equiv_EuclideanSpace' '' (Set.Icc 0 1) ∧ ¬ LebesgueMeasurable E := by
  use Real.equiv_EuclideanSpace' '' VitaliSet
  constructor
  · -- E ⊆ Real.equiv_EuclideanSpace' '' [0,1]
    intro x hx
    obtain ⟨r, hr, rfl⟩ := hx
    exact ⟨r, VitaliSet_subset_unit_interval hr, rfl⟩
  · exact VitaliSet.nonmeasurable

/-- An injective enumeration of the rationals in the closed interval from -1 to 1 -/
lemma exists_injective_rat_enum_Icc :
    ∃ f : ℕ → ℚ, Function.Injective f ∧ ∀ n, f n ∈ Set.Icc (-1 : ℚ) 1 := by
  have hQ_countable : Set.Countable {q : ℚ | q ∈ Set.Icc (-1:ℚ) 1} := rat_Icc_countable
  have hQ_inf : Set.Infinite {q : ℚ | q ∈ Set.Icc (-1:ℚ) 1} :=
    Set.Icc_infinite (by norm_num : (-1:ℚ) < 1)
  haveI : Infinite {q : ℚ | q ∈ Set.Icc (-1:ℚ) 1} := hQ_inf.to_subtype
  haveI : Countable {q : ℚ | q ∈ Set.Icc (-1:ℚ) 1} := hQ_countable.to_subtype
  haveI denumQ : Denumerable {q : ℚ | q ∈ Set.Icc (-1:ℚ) 1} := (nonempty_denumerable _).some
  let eqvQ : {q : ℚ | q ∈ Set.Icc (-1:ℚ) 1} ≃ ℕ := Denumerable.eqv _
  refine ⟨fun n => (eqvQ.symm n : ℚ), ?_, ?_⟩
  · exact Subtype.val_injective.comp eqvQ.symm.injective
  · intro n
    exact (eqvQ.symm n).2

/-- Translates of the Vitali set by distinct rationals are pairwise disjoint -/
lemma VitaliSet.translates_pairwise_disjoint (f : ℕ → ℚ) (hf_inj : Function.Injective f) :
    Set.univ.PairwiseDisjoint
      (fun n : ℕ => (Real.equiv_EuclideanSpace' '' VitaliSet) + {Real.equiv_EuclideanSpace' (f n : ℚ)}) := by
  intro i _ j _ hij
  simp only [Function.onFun, Set.disjoint_iff]
  intro z ⟨hz1, hz2⟩
  rw [Set.mem_add] at hz1 hz2
  obtain ⟨x1, hx1, r1, hr1, hz1_eq⟩ := hz1
  obtain ⟨x2, hx2, r2, hr2, hz2_eq⟩ := hz2
  rw [Set.mem_singleton_iff] at hr1 hr2
  subst hr1 hr2
  obtain ⟨v1, hv1, hx1_eq⟩ := hx1
  obtain ⟨v2, hv2, hx2_eq⟩ := hx2
  have heq : v1 + (f i : ℝ) = v2 + (f j : ℝ) := by
    have h1 : z 0 = v1 + (f i : ℝ) := by
      rw [← hz1_eq, ← hx1_eq]
      rfl
    have h2 : z 0 = v2 + (f j : ℝ) := by
      rw [← hz2_eq, ← hx2_eq]
      rfl
    linarith
  have h_same_coset : QuotientAddGroup.mk (s := Rat.addSubgroup) v1 =
      QuotientAddGroup.mk (s := Rat.addSubgroup) v2 := by
    rw [QuotientAddGroup.eq]
    use f i - f j
    simp only [Rat.cast_sub]
    linarith
  obtain ⟨c1, hc1⟩ := hv1
  obtain ⟨c2, hc2⟩ := hv2
  have hc1_spec := (coset_intersects_unit_interval c1).choose_spec.2
  have hc2_spec := (coset_intersects_unit_interval c2).choose_spec.2
  have hc_eq : c1 = c2 := by
    rw [← hc1, ← hc2] at h_same_coset
    rw [← hc1_spec, ← hc2_spec]
    exact h_same_coset
  subst hc_eq
  have hv_eq : v1 = v2 := hc1.symm.trans hc2
  have hq_eq : (f i : ℝ) = f j := by linarith [heq, hv_eq]
  have hqi_eq : f i = f j := Rat.cast_injective hq_eq
  exact hij (hf_inj hqi_eq)

/-- The lifted Vitali set is bounded, with positive, finite outer measure -/
lemma vitali_bounded_pos_finite :
    Bornology.IsBounded (Real.equiv_EuclideanSpace' '' VitaliSet) ∧
      0 < Lebesgue_outer_measure (Real.equiv_EuclideanSpace' '' VitaliSet) ∧
      Lebesgue_outer_measure (Real.equiv_EuclideanSpace' '' VitaliSet) ≠ ⊤ := by
  constructor
  · rw [Metric.isBounded_iff_subset_closedBall (0 : EuclideanSpace' 1)]
    use 3
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hz
    have hx01 : x ∈ Set.Icc (0 : ℝ) 1 := VitaliSet_subset_unit_interval hx
    have h_norm_eq : ‖Real.equiv_EuclideanSpace' x‖ = |x| := by
      simp [Real.equiv_EuclideanSpace', EuclideanSpace'.equiv_Real]
      rw [PiLp.norm_eq_of_L2]
      simp
      exact Real.sqrt_sq_eq_abs x
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    rw [h_norm_eq]
    have hx0 : 0 ≤ x := hx01.1
    have hx1 : x ≤ 1 := hx01.2
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · constructor
    · by_contra h
      have hle : Lebesgue_outer_measure (Real.equiv_EuclideanSpace' '' VitaliSet) ≤ 0 := le_of_not_gt h
      have hge : 0 ≤ Lebesgue_outer_measure (Real.equiv_EuclideanSpace' '' VitaliSet) :=
        Lebesgue_outer_measure.nonneg _
      have hzero : Lebesgue_outer_measure (Real.equiv_EuclideanSpace' '' VitaliSet) = 0 :=
        le_antisymm hle hge
      exact absurd (IsNull.measurable (E := Real.equiv_EuclideanSpace' '' VitaliSet) hzero)
        VitaliSet.nonmeasurable
    · intro htop
      have hsub : Real.equiv_EuclideanSpace' '' VitaliSet ⊆ Real.equiv_EuclideanSpace' '' Set.Icc (0 : ℝ) 1 := by
        intro z hz
        obtain ⟨x, hx, rfl⟩ := hz
        exact Set.mem_image_of_mem _ (VitaliSet_subset_unit_interval hx)
      have hmono : Lebesgue_outer_measure (Real.equiv_EuclideanSpace' '' VitaliSet) ≤
          Lebesgue_outer_measure (Real.equiv_EuclideanSpace' '' Set.Icc (0 : ℝ) 1) :=
        Lebesgue_outer_measure.mono hsub
      have hIcc : Lebesgue_outer_measure (Real.equiv_EuclideanSpace' '' Set.Icc (0 : ℝ) 1) = 1 := by
        simpa [Lebesgue_measure] using (Lebesgue_measure.Icc_eq 0 1 (by norm_num))
      rw [htop] at hmono
      rw [hIcc] at hmono
      exact absurd hmono (by decide : ¬(⊤ : EReal) ≤ 1)

/-- Exercise 1.2.26 (Outer measure is not finitely additive)-/
example : ∃ E F : Set (EuclideanSpace' 1), E ∩ F = ∅ ∧ Bornology.IsBounded E ∧ Bornology.IsBounded F ∧ Lebesgue_outer_measure (E ∪ F) ≠ Lebesgue_outer_measure E + Lebesgue_outer_measure F := by
  by_contra h
  push_neg at h
  set V : Set (EuclideanSpace' 1) := Real.equiv_EuclideanSpace' '' VitaliSet with hVdef
  set big : Set (EuclideanSpace' 1) := Real.equiv_EuclideanSpace' '' Set.Icc (-1 : ℝ) 2 with hbig_def
  have hV_bounded : Bornology.IsBounded V := by
    rw [hVdef]
    exact vitali_bounded_pos_finite.1
  have hV_pos : 0 < Lebesgue_outer_measure V := by
    rw [hVdef]
    exact vitali_bounded_pos_finite.2.1
  have hV_fin : Lebesgue_outer_measure V ≠ ⊤ := by
    rw [hVdef]
    exact vitali_bounded_pos_finite.2.2
  have hbig_bounded : Bornology.IsBounded big := by
    rw [hbig_def, Metric.isBounded_iff_subset_closedBall (0 : EuclideanSpace' 1)]
    use 3
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hz
    have h_norm_eq : ‖Real.equiv_EuclideanSpace' x‖ = |x| := by
      simp [Real.equiv_EuclideanSpace', EuclideanSpace'.equiv_Real]
      rw [PiLp.norm_eq_of_L2]
      simp
      exact Real.sqrt_sq_eq_abs x
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    rw [h_norm_eq]
    have hx1 : -1 ≤ x := hx.1
    have hx2 : x ≤ 2 := hx.2
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  obtain ⟨f, hf_inj, hf_mem⟩ := exists_injective_rat_enum_Icc
  let T : ℕ → Set (EuclideanSpace' 1) := fun n => V + {Real.equiv_EuclideanSpace' (f n : ℚ)}
  have hdisj : Set.univ.PairwiseDisjoint T := by
    simpa [T, hVdef] using (VitaliSet.translates_pairwise_disjoint f hf_inj)
  have hT_meas : ∀ n, Lebesgue_outer_measure (T n) = Lebesgue_outer_measure V := by
    intro n
    dsimp [T]
    exact Lebesgue_outer_measure.translate V (Real.equiv_EuclideanSpace' (f n : ℚ))
  have hT_sub_big : ∀ n, T n ⊆ big := by
    intro n z hz
    change z ∈ V + {Real.equiv_EuclideanSpace' (f n : ℚ)} at hz
    rw [Set.mem_add] at hz
    obtain ⟨x, hx, r1, hr1, hz_eq⟩ := hz
    rw [Set.mem_singleton_iff] at hr1
    subst hr1
    obtain ⟨v, hv, rfl⟩ := hx
    have hv_in : v ∈ Set.Icc (0 : ℝ) 1 := VitaliSet_subset_unit_interval hv
    have hq_bound : f n ∈ Set.Icc (-1 : ℚ) 1 := hf_mem n
    rw [hbig_def]
    refine ⟨v + (f n : ℝ), ?_, ?_⟩
    · constructor
      · have h1 : (f n : ℝ) ≥ -1 := by exact_mod_cast hq_bound.1
        linarith [hv_in.1]
      · have h2 : (f n : ℝ) ≤ 1 := by exact_mod_cast hq_bound.2
        linarith [hv_in.2]
    · ext i
      fin_cases i
      have hlhs : (Real.equiv_EuclideanSpace' (v + (f n : ℝ))) ⟨0, by omega⟩ = v + (f n : ℝ) := rfl
      have hrhs : z ⟨0, by omega⟩ = (Real.equiv_EuclideanSpace' v + Real.equiv_EuclideanSpace' (f n : ℝ)) ⟨0, by omega⟩ := by
        rw [← hz_eq]
      have hrhs' : (Real.equiv_EuclideanSpace' v + Real.equiv_EuclideanSpace' (f n : ℝ)) ⟨0, by omega⟩ = v + (f n : ℝ) := rfl
      rw [hlhs, hrhs, hrhs']
  have hT_bounded : ∀ n, Bornology.IsBounded (T n) := fun n => Bornology.IsBounded.subset hbig_bounded (hT_sub_big n)
  obtain ⟨r, hr_pos, hr_eq⟩ : ∃ r : ℝ, 0 < r ∧ Lebesgue_outer_measure V = (r : EReal) := by
    cases hV' : Lebesgue_outer_measure V with
    | bot =>
        have : (0 : EReal) < ⊥ := by rw [hV'] at hV_pos; exact hV_pos
        exact absurd this (by decide : ¬(0 : EReal) < ⊥)
    | top =>
        exact absurd hV' hV_fin
    | coe r =>
        refine ⟨r, ?_, rfl⟩
        have hr_ereal : (0 : EReal) < (r : EReal) := by
          rw [hV'] at hV_pos
          exact hV_pos
        exact_mod_cast hr_ereal
  have h_finite_sum : ∀ n : ℕ, Lebesgue_outer_measure (⋃ k ∈ Finset.range n, T k) = ((n : ℝ) * r : EReal) := by
    intro n
    induction n with
    | zero =>
        simp [Lebesgue_outer_measure.of_empty]
    | succ n ih =>
        have hUnion : (⋃ k ∈ Finset.range (n + 1), T k) = (⋃ k ∈ Finset.range n, T k) ∪ T n := by
          ext z
          constructor
          · intro hz
            rw [Set.mem_iUnion] at hz
            rcases hz with ⟨k, hk⟩
            rw [Set.mem_iUnion] at hk
            rcases hk with ⟨hk₁, hzk⟩
            have hk_lt : k < n + 1 := Finset.mem_range.mp hk₁
            by_cases hkn : k < n
            · left
              rw [Set.mem_iUnion]
              refine ⟨k, ?_⟩
              rw [Set.mem_iUnion]
              exact ⟨Finset.mem_range.mpr hkn, hzk⟩
            · right
              have hk_eq : k = n := by omega
              subst k
              exact hzk
          · intro hz
            rcases hz with hz | hzn
            · rw [Set.mem_iUnion] at hz
              rcases hz with ⟨k, hk⟩
              rw [Set.mem_iUnion] at hk
              rcases hk with ⟨hk₁, hzk⟩
              have hk_lt : k < n := Finset.mem_range.mp hk₁
              rw [Set.mem_iUnion]
              refine ⟨k, ?_⟩
              rw [Set.mem_iUnion]
              exact ⟨Finset.mem_range.mpr (by omega), hzk⟩
            · rw [Set.mem_iUnion]
              refine ⟨n, ?_⟩
              rw [Set.mem_iUnion]
              exact ⟨Finset.mem_range.mpr (by omega), hzn⟩
        have hU_sub : (⋃ k ∈ Finset.range n, T k) ⊆ big := by
          intro z hz
          rw [Set.mem_iUnion] at hz
          rcases hz with ⟨k, hk⟩
          rw [Set.mem_iUnion] at hk
          exact hT_sub_big k hk.2
        have hU_bounded : Bornology.IsBounded (⋃ k ∈ Finset.range n, T k) :=
          Bornology.IsBounded.subset hbig_bounded hU_sub
        have h_disj' : (⋃ k ∈ Finset.range n, T k) ∩ T n = ∅ := by
          rw [← Set.disjoint_iff_inter_eq_empty]
          rw [Set.disjoint_left]
          intro z hz hzn
          rw [Set.mem_iUnion] at hz
          rcases hz with ⟨k, hk⟩
          rw [Set.mem_iUnion] at hk
          have hk_lt : k < n := Finset.mem_range.mp hk.1
          have hkn : k ≠ n := by omega
          have hd : Disjoint (T k) (T n) := hdisj (Set.mem_univ k) (Set.mem_univ n) hkn
          rw [Set.disjoint_left] at hd
          exact hd hk.2 hzn
        rw [hUnion]
        rw [h (⋃ k ∈ Finset.range n, T k) (T n) h_disj' hU_bounded (hT_bounded n)]
        rw [ih, hT_meas n, hr_eq]
        rw [← EReal.coe_mul, ← EReal.coe_add]
        congr 1
        push_cast
        ring
  have h_le_three : ∀ n : ℕ, ((n : ℝ) * r : EReal) ≤ (3 : EReal) := by
    intro n
    rw [← h_finite_sum n]
    calc
      Lebesgue_outer_measure (⋃ k ∈ Finset.range n, T k) ≤ Lebesgue_outer_measure (⋃ m : ℕ, T m) := by
        exact Lebesgue_outer_measure.mono (by
          intro z hz
          rw [Set.mem_iUnion] at hz
          rcases hz with ⟨k, hk⟩
          rw [Set.mem_iUnion] at hk
          rw [Set.mem_iUnion]
          exact ⟨k, hk.2⟩)
      _ ≤ Lebesgue_outer_measure big := by
        exact Lebesgue_outer_measure.mono (by
          intro z hz
          rw [Set.mem_iUnion] at hz
          rcases hz with ⟨k, hk⟩
          exact hT_sub_big k hk)
      _ = 3 := by
        rw [hbig_def]
        change Lebesgue_measure (Real.equiv_EuclideanSpace' '' Set.Icc (-1 : ℝ) 2) = (3 : EReal)
        rw [Lebesgue_measure.Icc_eq (-1) 2 (by norm_num)]
        norm_cast
  have h_le_real : ∀ n : ℕ, (n : ℝ) * r ≤ 3 := by
    intro n
    have hc := h_le_three n
    rw [← EReal.coe_mul] at hc
    exact EReal.coe_le_coe_iff.mp hc
  obtain ⟨N, hN⟩ := exists_nat_gt (3 / r)
  have hbig : (3 / r) * r < (N : ℝ) * r := mul_lt_mul_of_pos_right hN hr_pos
  field_simp [ne_of_gt hr_pos] at hbig
  linarith [h_le_real N]

/-- The set of points whose first coordinate lies in the Vitali set and whose second
    coordinate is zero has Lebesgue measure zero -/
lemma vitali_line_isNull :
    Lebesgue_outer_measure
      ({z : EuclideanSpace' 2 | z 0 ∈ VitaliSet ∧ z 1 = 0} : Set (EuclideanSpace' 2)) = 0 := by
  let B : Box 2 := { side := ![BoundedInterval.Icc 0 1, BoundedInterval.Icc 0 0] }
  have hsub : ({z : EuclideanSpace' 2 | z 0 ∈ VitaliSet ∧ z 1 = 0} : Set (EuclideanSpace' 2)) ⊆ B.toSet := by
    intro z hz
    simp [B]
    constructor
    · exact VitaliSet_subset_unit_interval hz.1
    · simp [hz.2]
  have hvol : Box.volume B = 0 := by
    rw [Box.volume]
    apply Finset.prod_eq_zero (Finset.mem_univ (1 : Fin 2))
    simp [B, BoundedInterval.length]
  have hB_null : IsNull B.toSet := by
    change Lebesgue_outer_measure B.toSet = 0
    rw [Lebesgue_outer_measure.elementary _ (IsElementary.box B), IsElementary.measure_of_box]
    simp [hvol]
  exact IsNull.subset hB_null hsub

/-- Exercise 1.2.27 (Projections of measurable sets need not be measurable) -/
example : ∃ E : Set (EuclideanSpace' 2), LebesgueMeasurable E ∧ ¬ LebesgueMeasurable ((fun x ↦ Real.equiv_EuclideanSpace' (x 0: ℝ)) '' E) := by
  let E : Set (EuclideanSpace' 2) := {z | z 0 ∈ VitaliSet ∧ z 1 = 0}
  refine ⟨E, ?_, ?_⟩
  · let B : Box 2 := { side := ![BoundedInterval.Icc 0 1, BoundedInterval.Icc 0 0] }
    have hsub : E ⊆ B.toSet := by
      intro z hz
      simp [B]
      constructor
      · exact VitaliSet_subset_unit_interval hz.1
      · simp [hz.2]
    have hvol : Box.volume B = 0 := by
      rw [Box.volume]
      apply Finset.prod_eq_zero (Finset.mem_univ (1 : Fin 2))
      simp [B, BoundedInterval.length]
    have hB_null : IsNull B.toSet := by
      change Lebesgue_outer_measure B.toSet = 0
      rw [Lebesgue_outer_measure.elementary _ (IsElementary.box B), IsElementary.measure_of_box]
      simp [hvol]
    have hE_null : IsNull E := IsNull.subset hB_null hsub
    exact IsNull.measurable (E := E) hE_null
  · have hproj : (fun x : EuclideanSpace' 2 ↦ Real.equiv_EuclideanSpace' (x 0: ℝ)) '' E = Real.equiv_EuclideanSpace' '' VitaliSet := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x 0, hx.1, rfl⟩
      · rintro ⟨t, ht, rfl⟩
        let x : EuclideanSpace' 2 := .toLp 2 (fun i : Fin 2 => if i = 1 then (0 : ℝ) else t)
        refine ⟨x, ?_, ?_⟩
        · simp [E, x]
          exact ht
        · congr 1
    rw [hproj]
    exact VitaliSet.nonmeasurable
