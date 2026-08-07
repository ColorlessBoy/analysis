import Analysis.MeasureTheory.Section_1_4_2

open MeasureTheory

/-!
# Introduction to Measure Theory, Section 1.4.3: Countably additive measures and measure spaces

A companion to (the introduction to) Section 1.4.3 of the book "An introduction to Measure Theory".

Note: initially this section will use custom-notions of concrete sigma algebras and countably additive measures, but will transition to the Mathlib notions of {name}`Measurable` and {name}`MeasureTheory.Measure`, which will be in use going forward. In particular, exercises past this point will be easier
to solve using the Mathlib library for measure theory than the custom results defined here.
-/

/-- Definition 1.4.19 (Finitely additive measure) -/
class FinitelyAdditiveMeasure {X:Type*} (B: ConcreteBooleanAlgebra X) where
  measure : Set X → EReal
  measure_pos : ∀ A : Set X, B.measurable A → 0 ≤ measure A
  measure_nonneg : ∀ A : Set X, 0 ≤ measure A
  measure_empty : measure ∅ = 0
  measure_finite_additive : ∀ E F : Set X, B.measurable E → B.measurable F → Disjoint E F →
    measure (E ∪ F) = measure E + measure F

/-- Example 1.4.21 -/
@[implicit_reducible]
noncomputable def FinitelyAdditiveMeasure.lebesgue (d:ℕ) : FinitelyAdditiveMeasure (LebesgueMeasurable.boolean_algebra d) :=
  {
    measure A := Lebesgue_measure A
    measure_pos := by
      intro A hA
      exact Lebesgue_outer_measure.nonneg A
    measure_nonneg := by
      intro A
      exact Lebesgue_outer_measure.nonneg A
    measure_empty := Lebesgue_measure.empty
    measure_finite_additive := by
      intro E F hE hF hdisj
      exact Lebesgue_measure.union hE hF (Set.disjoint_iff_inter_eq_empty.mp hdisj)
  }

/-- Example 1.4.21 -/
@[implicit_reducible]
def FinitelyAdditiveMeasure.restrict_alg {X:Type*} {B: ConcreteBooleanAlgebra X} (μ: FinitelyAdditiveMeasure B) {B':ConcreteBooleanAlgebra X} (hBB': B' ≤ B) : FinitelyAdditiveMeasure B' :=
  {
    measure := μ.measure
    measure_pos := by
      intro A hA
      exact μ.measure_pos A (hBB' A hA)
    measure_nonneg := by
      intro A
      exact μ.measure_nonneg A
    measure_empty := μ.measure_empty
    measure_finite_additive := by
      intro E F hE hF hdisj
      exact μ.measure_finite_additive E F (hBB' E hE) (hBB' F hF) hdisj
  }

/-- Example 1.4.21 -/
@[implicit_reducible]
noncomputable def FinitelyAdditiveMeasure.jordan (d:ℕ) : FinitelyAdditiveMeasure (JordanMeasurable.boolean_algebra d) :=
(FinitelyAdditiveMeasure.lebesgue d).restrict_alg (LebesgueMeasurable.gt_jordan_boolean_algebra d)

/-- Example 1.4.21 -/
@[implicit_reducible]
noncomputable def FinitelyAdditiveMeasure.null (d:ℕ) : FinitelyAdditiveMeasure (IsNull.boolean_algebra d) :=
(FinitelyAdditiveMeasure.lebesgue d).restrict_alg (IsNull.lt_lebesgue_boolean_algebra d)

/-- Example 1.4.21 -/
@[implicit_reducible]
noncomputable def FinitelyAdditiveMeasure.elem (d:ℕ) : FinitelyAdditiveMeasure (EuclideanSpace'.elementary_boolean_algebra d) :=
(FinitelyAdditiveMeasure.lebesgue d).restrict_alg
  (le_trans (JordanMeasurable.gt_elementary_boolean_algebra d) (LebesgueMeasurable.gt_jordan_boolean_algebra d))

open Classical in
/-- Example 1.4.22 (Dirac measure) -/
@[implicit_reducible]
noncomputable def FinitelyAdditiveMeasure.dirac {X:Type*} (x₀:X) (B: ConcreteBooleanAlgebra X) : FinitelyAdditiveMeasure B :=
  {
    measure := fun A => if x₀ ∈ A then 1 else 0
    measure_pos := by
      intro A hA
      by_cases h : x₀ ∈ A
      · simp [h]
      · simp [h]
    measure_nonneg := by
      intro A
      by_cases h : x₀ ∈ A
      · simp [h]
      · simp [h]
    measure_empty := by
      simp
    measure_finite_additive := by
      intro E F hE hF hdisj
      by_cases hE₀ : x₀ ∈ E
      · have hF₀ : x₀ ∉ F := by
          intro hF₀
          have : x₀ ∈ E ∩ F := ⟨hE₀, hF₀⟩
          exact (Set.disjoint_iff.mp hdisj) this
        simp [hE₀, hF₀]
      · by_cases hF₀ : x₀ ∈ F
        · simp [hE₀, hF₀]
        · simp [hE₀, hF₀]
  }

/-- Example 1.4.23 (Zero measure) -/
@[implicit_reducible]
noncomputable instance FinitelyAdditiveMeasure.instZero {X:Type*} (B: ConcreteBooleanAlgebra X) : Zero (FinitelyAdditiveMeasure B) :=
  {
    zero := {
      measure := fun A => 0
      measure_pos := by
        intro A hA
        simp
      measure_nonneg := by
        intro A
        simp
      measure_empty := by
        simp
      measure_finite_additive := by
        intro E F hE hF hdisj
        simp
    }
  }

/-- Example 1.4.24 (linear combinations of measures) -/
@[implicit_reducible]
noncomputable instance FinitelyAdditiveMeasure.instAdd {X:Type*} {B: ConcreteBooleanAlgebra X} : Add (FinitelyAdditiveMeasure B) :=
  {
    add := fun μ ν =>
      {
        measure := fun A => μ.measure A + ν.measure A
        measure_pos := by
          intro A hA
          exact add_nonneg (μ.measure_pos A hA) (ν.measure_pos A hA)
        measure_nonneg := by
          intro A
          exact add_nonneg (μ.measure_nonneg A) (ν.measure_nonneg A)
        measure_empty := by
          simp [μ.measure_empty, ν.measure_empty]
        measure_finite_additive := by
          intro E F hE hF hdisj
          rw [μ.measure_finite_additive E F hE hF hdisj, ν.measure_finite_additive E F hE hF hdisj]
          abel
      }
  }

@[implicit_reducible]
noncomputable instance FinitelyAdditiveMeasure.instSmul {X:Type*} {B: ConcreteBooleanAlgebra X} : SMul ENNReal (FinitelyAdditiveMeasure B) :=
{
    smul := fun c μ =>
        {
        measure := fun A => c * μ.measure A
        measure_pos := by
          intro A hA
          exact mul_nonneg (EReal.coe_ennreal_nonneg c) (μ.measure_pos A hA)
        measure_nonneg := by
          intro A
          exact mul_nonneg (EReal.coe_ennreal_nonneg c) (μ.measure_nonneg A)
        measure_empty := by
          simp [μ.measure_empty]
        measure_finite_additive := by
          intro E F hE hF hdisj
          rw [μ.measure_finite_additive E F hE hF hdisj]
          exact EReal.left_distrib_of_nonneg (a := μ.measure E) (b := μ.measure F)
            (μ.measure_nonneg E) (μ.measure_nonneg F)
        }
}

@[ext]
theorem FinitelyAdditiveMeasure.ext {X:Type*} {B: ConcreteBooleanAlgebra X} {μ ν : FinitelyAdditiveMeasure B}
    (h : ∀ A : Set X, μ.measure A = ν.measure A) : μ = ν := by
  cases μ with
  | mk μ_measure μ_pos μ_empty μ_fadd =>
    cases ν with
    | mk ν_measure ν_pos ν_empty ν_fadd =>
      congr
      funext A
      exact h A

noncomputable instance FinitelyAdditiveMeasure.instAddCommMonoid {X:Type*} {B: ConcreteBooleanAlgebra X} : AddCommMonoid (FinitelyAdditiveMeasure B) :=
{
  add_assoc := by
    intro μ ν τ
    ext A
    change (μ.measure A + ν.measure A) + τ.measure A = μ.measure A + (ν.measure A + τ.measure A)
    abel
  zero_add := by
    intro μ
    ext A
    change (0 : EReal) + μ.measure A = μ.measure A
    simp
  add_zero := by
    intro μ
    ext A
    change μ.measure A + 0 = μ.measure A
    simp
  add_comm := by
    intro μ ν
    ext A
    change μ.measure A + ν.measure A = ν.measure A + μ.measure A
    rw [add_comm]
  nsmul := nsmulRec
}

noncomputable instance FinitelyAdditiveMeasure.instDistribMulAction {X:Type*} {B: ConcreteBooleanAlgebra X} : DistribMulAction ENNReal (FinitelyAdditiveMeasure B) :=
{
  smul_zero := by
    intro c
    ext A
    change (c : EReal) * 0 = 0
    simp
  smul_add := by
    intro c μ ν
    ext A
    change (c : EReal) * (μ.measure A + ν.measure A) = (c : EReal) * μ.measure A + (c : EReal) * ν.measure A
    exact EReal.left_distrib_of_nonneg (a := μ.measure A) (b := ν.measure A)
      (μ.measure_nonneg A) (ν.measure_nonneg A)
  one_smul := by
    intro μ
    ext A
    change (1 : EReal) * μ.measure A = μ.measure A
    simp
  mul_smul := by
    intro c d μ
    ext A
    change ((c * d : ENNReal) : EReal) * μ.measure A = (c : EReal) * ((d : EReal) * μ.measure A)
    rw [EReal.coe_ennreal_mul, mul_assoc]
}

/-- Example 1.4.25 (Restriction of a measure) -/
@[implicit_reducible]
def FinitelyAdditiveMeasure.restrict {X:Type*} {B: ConcreteBooleanAlgebra X} (μ: FinitelyAdditiveMeasure B) (A:Set X) (hA:B.measurable A) : FinitelyAdditiveMeasure (B.restrict A) :=
  {
    measure := fun E => μ.measure E
    measure_pos := by
      intro E hE
      exact μ.measure_pos (E : Set X) ((ConcreteBooleanAlgebra.restrict_iff hA E).mp hE)
    measure_nonneg := by
      intro E
      exact μ.measure_nonneg (E : Set X)
    measure_empty := by
      simpa using μ.measure_empty
    measure_finite_additive := by
      intro E F hE hF hdisj
      have hE' : B.measurable (E : Set X) := (ConcreteBooleanAlgebra.restrict_iff hA E).mp hE
      have hF' : B.measurable (F : Set X) := (ConcreteBooleanAlgebra.restrict_iff hA F).mp hF
      have hdisj' : Disjoint (E : Set X) (F : Set X) := by
        rw [Set.disjoint_iff]
        intro x hx
        rcases hx with ⟨⟨e, he, rfl⟩, ⟨f, hf, hxf⟩⟩
        have hef : f = e := Subtype.val_injective hxf
        exact (Set.disjoint_iff.mp hdisj) ⟨by simpa [hef] using he, hf⟩
      have hunion : Subtype.val '' (E ∪ F) = Subtype.val '' E ∪ Subtype.val '' F := by
        exact Set.image_union Subtype.val E F
      rw [hunion]
      exact μ.measure_finite_additive (E : Set X) (F : Set X) hE' hF' hdisj'
  }

/-- Example 1.4.26 (Counting a measure) -/
@[implicit_reducible]
noncomputable def FinitelyAdditiveMeasure.counting (X:Type*) : FinitelyAdditiveMeasure (⊤  : ConcreteBooleanAlgebra X) :=
  {
    measure := fun E => ENat.card E
    measure_pos := by
      intro A hA
      exact EReal.coe_ennreal_nonneg (ENat.card A)
    measure_nonneg := by
      intro A
      exact EReal.coe_ennreal_nonneg (ENat.card A)
    measure_empty := by
      simp
    measure_finite_additive := by
      intro E F hE hF hdisj
      exact_mod_cast (Set.encard_union_eq hdisj)
  }

/-- Exercise 1.4.20(i) -/
theorem FinitelyAdditiveMeasure.mono {X:Type*} {B: ConcreteBooleanAlgebra X} (μ: FinitelyAdditiveMeasure B) {E F : Set X} (hE : B.measurable E) (hF : B.measurable F) (hsub : E ⊆ F) : μ.measure E ≤ μ.measure F := by
  have hd : Disjoint E (F \ E) := by
    rw [Set.disjoint_iff]
    intro x hx
    exact hx.2.2 hx.1
  have hFd : B.measurable (F \ E) := by
    simpa [Set.diff_eq] using B.inter_mem hF (B.compl_mem E hE)
  have hEsub : F = E ∪ (F \ E) := by
    ext x
    constructor
    · intro hxF
      by_cases hxE : x ∈ E
      · exact Or.inl hxE
      · exact Or.inr ⟨hxF, hxE⟩
    · intro hx
      rcases hx with hx | hx
      · exact hsub hx
      · exact hx.1
  rw [hEsub, μ.measure_finite_additive E (F \ E) hE hFd hd]
  exact le_add_of_nonneg_right (μ.measure_nonneg (F \ E))

/-- Exercise 1.4.20(ii) -/
private lemma FinitelyAdditiveMeasure.measurable_finset_biUnion {X:Type*} {B: ConcreteBooleanAlgebra X} {J:Type*} {I: Finset J} {E: J → Set X}
    (hE: ∀ j:J, B.measurable (E j)) : B.measurable (⋃ j ∈ I, E j) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using B.empty_mem
  | insert j J hjnJ ih =>
      rw [Finset.set_biUnion_insert]
      exact B.union_mem (E j) (⋃ i ∈ J, E i) (hE j) ih

theorem FinitelyAdditiveMeasure.finite_additivity {X:Type*} {B: ConcreteBooleanAlgebra X} (μ: FinitelyAdditiveMeasure B) {J:Type*} {I: Finset J} {E: J → Set X} (hE: ∀ j:J, B.measurable (E j)) (hdisj: Set.univ.PairwiseDisjoint E) :
  μ.measure (⋃ j ∈ I, E j) = ∑ j ∈ I, μ.measure (E j) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [μ.measure_empty]
  | insert j J hjnJ ih =>
      rw [Finset.sum_insert hjnJ]
      rw [Finset.set_biUnion_insert]
      have hUmeas : B.measurable (⋃ i ∈ J, E i) := measurable_finset_biUnion hE
      have hdisj' : Disjoint (E j) (⋃ i ∈ J, E i) := by
        rw [Set.disjoint_iff]
        intro x hx
        rcases hx with ⟨hxj, hxU⟩
        rw [Set.mem_iUnion₂] at hxU
        rcases hxU with ⟨i, hiJ, hxi⟩
        have hne : j ≠ i := by
          intro h
          subst h
          exact hjnJ hiJ
        exact (Set.disjoint_iff.mp (hdisj (Set.mem_univ j) (Set.mem_univ i) hne)) ⟨hxj, hxi⟩
      rw [μ.measure_finite_additive (E j) (⋃ i ∈ J, E i) (hE j) hUmeas hdisj']
      rw [ih]

/-- Exercise 1.4.20(iv) -/
theorem FinitelyAdditiveMeasure.mes_union_add_mes_inter {X:Type*} {B: ConcreteBooleanAlgebra X} (μ: FinitelyAdditiveMeasure B) {E F : Set X}
    (hE: B.measurable E) (hF: B.measurable F) :
  μ.measure (E ∪ F) + μ.measure (E ∩ F) = μ.measure E + μ.measure F := by
  have hFd : B.measurable (F \ E) := by
    simpa [Set.diff_eq] using B.inter_mem hF (B.compl_mem E hE)
  have hEd : B.measurable (E \ F) := by
    simpa [Set.diff_eq] using B.inter_mem hE (B.compl_mem F hF)
  have hEFd : B.measurable (E ∩ F) := B.inter_mem hE hF
  have hd1 : Disjoint E (F \ E) := by
    rw [Set.disjoint_iff]
    intro x hx
    exact hx.2.2 hx.1
  have hd2 : Disjoint (E ∩ F) (F \ E) := by
    rw [Set.disjoint_iff]
    intro x hx
    exact hx.2.2 hx.1.1
  have hunion : E ∪ F = E ∪ (F \ E) := by
    ext x
    constructor
    · intro hx
      rcases hx with hxE | hxF
      · exact Or.inl hxE
      · by_cases hxE : x ∈ E
        · exact Or.inl hxE
        · exact Or.inr ⟨hxF, hxE⟩
    · intro hx
      rcases hx with hxE | hxF
      · exact Or.inl hxE
      · exact Or.inr hxF.1
  have hF_eq : F = (E ∩ F) ∪ (F \ E) := by
    ext x
    constructor
    · intro hx
      by_cases hxE : x ∈ E
      · exact Or.inl ⟨hxE, hx⟩
      · exact Or.inr ⟨hx, hxE⟩
    · intro hx
      rcases hx with hx | hx
      · exact hx.2
      · exact hx.1
  calc
    μ.measure (E ∪ F) + μ.measure (E ∩ F)
        = μ.measure (E ∪ (F \ E)) + μ.measure (E ∩ F) := by rw [hunion]
    _ = (μ.measure E + μ.measure (F \ E)) + μ.measure (E ∩ F) := by
        rw [μ.measure_finite_additive E (F \ E) hE hFd hd1]
    _ = μ.measure E + (μ.measure (E ∩ F) + μ.measure (F \ E)) := by abel
    _ = μ.measure E + μ.measure ((E ∩ F) ∪ (F \ E)) := by
        rw [μ.measure_finite_additive (E ∩ F) (F \ E) hEFd hFd hd2]
    _ = μ.measure E + μ.measure F := by rw [← hF_eq]

/-- Exercise 1.4.20(iii) -/
theorem FinitelyAdditiveMeasure.finite_subadditivity {X:Type*} {B: ConcreteBooleanAlgebra X} (μ: FinitelyAdditiveMeasure B) {J:Type*} {I: Finset J} {E: J → Set X} (hE: ∀ j:J, B.measurable (E j)) :
  μ.measure (⋃ j ∈ I, E j) ≤ ∑ j ∈ I, μ.measure (E j) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [μ.measure_empty]
  | insert j J hjnJ ih =>
      rw [Finset.sum_insert hjnJ]
      rw [Finset.set_biUnion_insert]
      have hUmeas : B.measurable (⋃ i ∈ J, E i) := measurable_finset_biUnion hE
      have hle : μ.measure (E j ∪ (⋃ i ∈ J, E i)) ≤ μ.measure (E j) + μ.measure (⋃ i ∈ J, E i) := by
        have h := μ.mes_union_add_mes_inter (hE j) hUmeas
        calc
          μ.measure (E j ∪ (⋃ i ∈ J, E i))
              ≤ μ.measure (E j ∪ (⋃ i ∈ J, E i)) + μ.measure (E j ∩ (⋃ i ∈ J, E i)) :=
                le_add_of_nonneg_right (μ.measure_nonneg (E j ∩ (⋃ i ∈ J, E i)))
          _ = μ.measure (E j) + μ.measure (⋃ i ∈ J, E i) := by rw [h]
      exact le_trans hle (add_le_add_right ih (μ.measure (E j)))

open Classical in
/-- A measurable set in the atomic algebra is the union of the atoms it contains. -/
private lemma atomic_union_eq {I X : Type*} [Fintype I] {atoms : I → Set X} (h_part : IsPartition atoms)
    (E : Set X) (hE : h_part.to_ConcreteBooleanAlgebra.measurable E) :
    E = ⋃ i ∈ Finset.univ.filter (fun i => atoms i ⊆ E), atoms i := by
  rcases hE with ⟨J, rfl⟩
  ext x
  constructor
  · intro hx
    simp [Set.mem_iUnion] at hx
    rcases hx with ⟨j, hjJ, hxj⟩
    simp [Set.mem_iUnion]
    refine ⟨j, ?_, hxj⟩
    show atoms j ⊆ ⋃ i ∈ J, atoms i
    intro y hy
    simp [Set.mem_iUnion]
    exact ⟨j, hjJ, hy⟩
  · intro hx
    simp [Set.mem_iUnion] at hx
    rcases hx with ⟨i, hi, hxi⟩
    exact hi hxi

open Classical in
/-- Each atom is measurable in the atomic algebra. -/
private lemma atomic_measurable {I X : Type*} [Fintype I] {atoms : I → Set X} (h_part : IsPartition atoms)
    (i : I) : h_part.to_ConcreteBooleanAlgebra.measurable (atoms i) := by
  refine ⟨{i}, ?_⟩
  ext x
  simp

open Classical in
/-- The {lit}`ENNReal` finite sum coerces to the corresponding {lit}`EReal` sum. -/
private lemma finset_sum_coe_ereal {I : Type*} (s : Finset I) (c : I → ENNReal) :
    ((∑ i ∈ s, c i : ENNReal) : EReal) = ∑ i ∈ s, (c i : EReal) := by
  let f : ENNReal →+ EReal :=
    { toFun := (↑·), map_zero' := rfl, map_add' := EReal.coe_ennreal_add }
  exact map_sum f (fun i => c i) s

open Classical in
/-- In a partition, a nonempty atom contained in another atom is that atom. -/
private lemma atomic_subset_empty {I X : Type*} {atoms : I → Set X} (h_part : IsPartition atoms)
    {i j : I} (hsub : atoms j ⊆ atoms i) (hne : j ≠ i) : atoms j = ∅ := by
  have hdisj := h_part.1 (Set.mem_univ j) (Set.mem_univ i) hne
  apply Set.Subset.antisymm
  · intro x hx
    have hxi : x ∈ atoms i := hsub hx
    exact False.elim ((Set.disjoint_iff.mp hdisj) ⟨hx, hxi⟩)
  · intro x hx
    simp at hx

open Classical in
/-- Summing the coefficients of the atoms contained in {lit}`atoms i` recovers {lit}`c i`
  when the empty atoms have coefficient zero. -/
private lemma atomic_filter_sum {I X : Type*} [Fintype I] {atoms : I → Set X} (h_part : IsPartition atoms)
    (i : I) (c : I → ENNReal) (hzero : ∀ j, atoms j = ∅ → c j = 0) :
    (∑ j ∈ Finset.univ.filter (fun j => atoms j ⊆ atoms i), c j) = c i := by
  have hif : ∀ j, (if atoms j ⊆ atoms i then c j else 0) = (if j = i then c i else 0) := by
    intro j
    by_cases hji : j = i
    · subst hji
      simp
    · by_cases hsub : atoms j ⊆ atoms i
      · have hempty : atoms j = ∅ := atomic_subset_empty h_part hsub hji
        simp [hji, hsub, hzero j hempty]
      · simp [hji, hsub]
  calc
    (∑ j ∈ Finset.univ.filter (fun j => atoms j ⊆ atoms i), c j)
        = ∑ j ∈ Finset.univ, (if atoms j ⊆ atoms i then c j else 0) := by
            rw [Finset.sum_filter]
    _ = ∑ j ∈ Finset.univ, (if j = i then c i else 0) := by
            apply Finset.sum_congr rfl
            intro j hj
            exact hif j
    _ = c i := by simp

open Classical in
/-- Exercise 1.4.21 -/
theorem FinitelyAdditiveMeasure.finite_atomic_eq {I X: Type*} [Fintype I] {atoms: I → Set X} (h_part: IsPartition atoms) (μ : FinitelyAdditiveMeasure h_part.to_ConcreteBooleanAlgebra) : ∃! c : I → ENNReal, ∀ E, h_part.to_ConcreteBooleanAlgebra.measurable E → μ.measure E = ∑ i ∈ Finset.univ.filter (fun i => atoms i ⊆ E), c i := by
  -- Existence: c i = (μ.measure (atoms i)).toENNReal
  refine ⟨fun i => (μ.measure (atoms i)).toENNReal, ?_, ?_⟩
  · intro E hE
    have hEq : E = ⋃ i ∈ Finset.univ.filter (fun i => atoms i ⊆ E), atoms i := atomic_union_eq h_part E hE
    calc
      μ.measure E = μ.measure (⋃ i ∈ Finset.univ.filter (fun i => atoms i ⊆ E), atoms i) := by exact congrArg μ.measure hEq
      _ = ∑ i ∈ Finset.univ.filter (fun i => atoms i ⊆ E), μ.measure (atoms i) := by
        exact μ.finite_additivity (fun i => atomic_measurable h_part i) h_part.1
      _ = ((∑ i ∈ Finset.univ.filter (fun i => atoms i ⊆ E), (μ.measure (atoms i)).toENNReal : ENNReal) : EReal) := by
        rw [finset_sum_coe_ereal]
        apply Finset.sum_congr rfl
        intro i hi
        exact (EReal.coe_toENNReal (μ.measure_nonneg (atoms i))).symm
  · intro c hc
    funext i
    have hc0 : ∀ j, atoms j = ∅ → c j = 0 := by
      intro j hj
      classical
      have hEempty : h_part.to_ConcreteBooleanAlgebra.measurable (∅ : Set X) := h_part.to_ConcreteBooleanAlgebra.empty_mem
      have hsum := hc ∅ hEempty
      have hzero : (∑ k ∈ Finset.univ.filter (fun k => atoms k ⊆ (∅ : Set X)), c k) = 0 := by
        have hEreal : ((∑ k ∈ Finset.univ.filter (fun k => atoms k ⊆ (∅ : Set X)), c k : ENNReal) : EReal) = 0 := by
          rw [← hsum, μ.measure_empty]
        exact_mod_cast hEreal
      have hjmem : j ∈ Finset.univ.filter (fun k => atoms k ⊆ (∅ : Set X)) := by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ j, by simp [hj]⟩
      have hle : c j ≤ (∑ k ∈ Finset.univ.filter (fun k => atoms k ⊆ (∅ : Set X)), c k) := by
        exact Finset.single_le_sum (fun k hk => zero_le (c k)) hjmem
      rw [hzero] at hle
      exact le_antisymm hle (zero_le (c j))
    have hEi : h_part.to_ConcreteBooleanAlgebra.measurable (atoms i) := atomic_measurable h_part i
    have hsum := hc (atoms i) hEi
    have hfilter : (∑ j ∈ Finset.univ.filter (fun j => atoms j ⊆ atoms i), c j) = c i :=
      atomic_filter_sum h_part i c hc0
    have hcoerced : (c i : EReal) = μ.measure (atoms i) := by
      rw [← hfilter]
      rw [← hsum]
    have htoennreal := congrArg EReal.toENNReal hcoerced
    simpa [EReal.toENNReal_coe] using htoennreal

/-- Definition 1.4.27 (Countably additive measure) -/
class CountablyAdditiveMeasure {X:Type*} (B: ConcreteSigmaAlgebra X) extends FinitelyAdditiveMeasure B.toConcreteBooleanAlgebra where
  measure_countable_additive : ∀ (E : ℕ → Set X), (∀ n, B.measurable (E n)) → Set.univ.PairwiseDisjoint E →
    measure (⋃ n, E n) = ∑' n, (measure (E n))

def FinitelyAdditiveMeasure.isCountablyAdditive {X:Type*} {B: ConcreteBooleanAlgebra X} (μ: FinitelyAdditiveMeasure B) : Prop :=
  B.isSigmaAlgebra ∧ ∀ (E : ℕ → Set X), (∀ n, B.measurable (E n)) → Set.univ.PairwiseDisjoint E →
    μ.measure (⋃ n, E n) = ∑' n, (μ.measure (E n))

@[implicit_reducible]
def FinitelyAdditiveMeasure.isCountablyAdditive.toCountablyAdditive {X:Type*} {B: ConcreteBooleanAlgebra X} (μ: FinitelyAdditiveMeasure B) (h: μ.isCountablyAdditive) : CountablyAdditiveMeasure h.1.toSigmaAlgebra :=
  {
    measure := μ.measure
    measure_pos := μ.measure_pos
    measure_nonneg := μ.measure_nonneg
    measure_empty := μ.measure_empty
    measure_finite_additive := μ.measure_finite_additive
    measure_countable_additive := h.2
  }

/-- The coefficient hom from {lit}`ENNReal` to {lit}`EReal`, used to transfer tsums. -/
private def erealCoeHom : ENNReal →+ EReal :=
  { toFun := (↑·), map_zero' := rfl, map_add' := EReal.coe_ennreal_add }

private lemma coe_tsum_ereal {ι : Type*} (a : ι → ENNReal) :
    ((∑' i, a i : ENNReal) : EReal) = ∑' i, (a i : EReal) := by
  exact Summable.map_tsum (f := a) ENNReal.summable erealCoeHom (by exact continuous_coe_ennreal_ereal)

/-- {lit}`ENNReal` tsums commute with the sum of two nonnegative {lit}`EReal` families. -/
private lemma ereal_tsum_add {ι : Type*} (a b : ι → EReal) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    (∑' i, a i) + (∑' i, b i) = ∑' i, (a i + b i) := by
  have hcoe_a : ∀ i, ((a i).toENNReal : EReal) = a i := fun i => EReal.coe_toENNReal (ha i)
  have hcoe_b : ∀ i, ((b i).toENNReal : EReal) = b i := fun i => EReal.coe_toENNReal (hb i)
  calc
    (∑' i, a i) + (∑' i, b i)
        = ((∑' i, (a i).toENNReal : ENNReal) : EReal) + ((∑' i, (b i).toENNReal : ENNReal) : EReal) := by
          rw [coe_tsum_ereal (fun i => (a i).toENNReal), coe_tsum_ereal (fun i => (b i).toENNReal)]
          simp_rw [hcoe_a, hcoe_b]
    _ = ((∑' i, ((a i).toENNReal + (b i).toENNReal : ENNReal)) : EReal) := by
          rw [← EReal.coe_ennreal_add]
          rw [← coe_tsum_ereal (fun i => (a i).toENNReal + (b i).toENNReal)]
          congr 1
          rw [ENNReal.tsum_add]
    _ = ∑' i, (a i + b i) := by
          have hcoe_ab : ∀ i, (((a i + b i).toENNReal) : EReal) = a i + b i :=
            fun i => EReal.coe_toENNReal (add_nonneg (ha i) (hb i))
          apply tsum_congr
          intro i
          rw [← hcoe_ab i]
          rw [EReal.toENNReal_add (ha i) (hb i)]

/-- Scalar multiplication by a nonnegative coefficient distributes over {lit}`EReal` tsums. -/
private lemma tsum_ereal_mul_left {ι : Type*} (c : ENNReal) (a : ι → EReal) (ha : ∀ i, 0 ≤ a i) :
    (c : EReal) * (∑' i, a i) = ∑' i, (c : EReal) * a i := by
  have hcoe : ∀ i, ((a i).toENNReal : EReal) = a i := fun i => EReal.coe_toENNReal (ha i)
  calc
    (c : EReal) * (∑' i, a i)
        = (c : EReal) * ((∑' i, (a i).toENNReal : ENNReal) : EReal) := by
            rw [coe_tsum_ereal (fun i => (a i).toENNReal)]
            simp_rw [hcoe]
    _ = ((c * ∑' i, (a i).toENNReal : ENNReal) : EReal) := by
            rw [EReal.coe_ennreal_mul]
    _ = ((∑' i, (c * (a i).toENNReal : ENNReal)) : EReal) := by
            rw [← coe_tsum_ereal (fun i => c * (a i).toENNReal)]
            congr 1
            rw [ENNReal.tsum_mul_left]
    _ = ∑' i, (c : EReal) * a i := by
            apply tsum_congr
            intro i
            rw [EReal.coe_ennreal_mul]
            rw [hcoe i]

/-- The double {lit}`EReal` tsum of a nonnegative family commutes (Fubini). -/
private lemma tsum_comm_ereal {ι κ : Type*} (f : ι → κ → EReal) (hf : ∀ i k, 0 ≤ f i k) :
    (∑' i, ∑' k, f i k) = (∑' k, ∑' i, f i k) := by
  have hcoe : ∀ i k, ((f i k).toENNReal : EReal) = f i k := fun i k => EReal.coe_toENNReal (hf i k)
  calc
    (∑' i, ∑' k, f i k)
        = ((∑' i, (∑' k, (f i k).toENNReal : ENNReal)) : EReal) := by
            apply tsum_congr
            intro i
            rw [coe_tsum_ereal (fun k => (f i k).toENNReal)]
            apply tsum_congr
            intro k
            rw [hcoe i k]
    _ = ((∑' k, (∑' i, (f i k).toENNReal : ENNReal)) : EReal) := by
            rw [← coe_tsum_ereal (fun i => ∑' k, (f i k).toENNReal),
                ← coe_tsum_ereal (fun k => ∑' i, (f i k).toENNReal)]
            congr 1
            exact ENNReal.tsum_comm
    _ = ∑' k, ∑' i, f i k := by
            apply tsum_congr
            intro k
            rw [coe_tsum_ereal (fun i => (f i k).toENNReal)]
            apply tsum_congr
            intro i
            rw [hcoe i k]

open Classical in
/-- The tsum of the indicator of a pairwise disjoint family is 1 if the point lies in the union. -/
private lemma dirac_tsum {X : Type*} {x₀ : X} {E : ℕ → Set X}
    (hdisj : Set.univ.PairwiseDisjoint E) :
    (∑' n, (if x₀ ∈ E n then (1 : EReal) else 0)) = if x₀ ∈ ⋃ n, E n then (1 : EReal) else 0 := by
  classical
  by_cases hx₀ : x₀ ∈ ⋃ n, E n
  · rcases Set.mem_iUnion.mp hx₀ with ⟨n₀, hx₀n₀⟩
    have h0 : ∀ n, n ≠ n₀ → (if x₀ ∈ E n then (1 : EReal) else 0) = 0 := by
      intro n hn
      have hx₀n : x₀ ∉ E n := by
        intro hx₀n
        have hdis : Disjoint (E n₀) (E n) := hdisj (Set.mem_univ n₀) (Set.mem_univ n) (Ne.symm hn)
        exact (Set.disjoint_iff.mp hdis) ⟨hx₀n₀, hx₀n⟩
      simp [hx₀n]
    rw [tsum_eq_single n₀ h0]
    simp [hx₀n₀]
    exact ⟨n₀, hx₀n₀⟩
  · have h0 : ∀ n, (if x₀ ∈ E n then (1 : EReal) else 0) = 0 := by
      intro n
      have hx₀n : x₀ ∉ E n := by
        intro hx₀n
        exact hx₀ (by rw [Set.mem_iUnion]; exact ⟨n, hx₀n⟩)
      simp [hx₀n]
    simp [h0]
    intro x hx
    exact hx₀ (by rw [Set.mem_iUnion]; exact ⟨x, hx⟩)

/-- Example 1.4.28-/
theorem FinitelyAdditiveMeasure.lebesgue_isCountablyAdditive (d:ℕ) : (FinitelyAdditiveMeasure.lebesgue d).isCountablyAdditive := by
  constructor
  · exact LebesgueMeasurable.boolean_algebra.isSigmaAlgebra d
  · intro E hE hdisj
    exact Lebesgue_measure.countable_union (fun n => hE n) hdisj

theorem FinitelyAdditiveMeasure.isCountablyAdditive_restrict_alg {X:Type*} {B B': ConcreteSigmaAlgebra X} (μ: CountablyAdditiveMeasure B) (hBB': B' ≤ B) : (μ.toFinitelyAdditiveMeasure.restrict_alg hBB').isCountablyAdditive := by
  constructor
  · exact ConcreteSigmaAlgebra.isSigmaAlgebra B'
  · intro E hE hdisj
    exact μ.measure_countable_additive E (fun n => hBB' (E n) (hE n)) hdisj

@[implicit_reducible]
def CountablyAdditiveMeasure.restrict_alg {X:Type*} {B B': ConcreteSigmaAlgebra X} (μ: CountablyAdditiveMeasure B) (hBB' : B' ≤ B) : CountablyAdditiveMeasure B' :=
  {
    toFinitelyAdditiveMeasure := μ.toFinitelyAdditiveMeasure.restrict_alg hBB',
    measure_countable_additive := by
      intro E hE hdisj
      exact μ.measure_countable_additive E (fun n => hBB' (E n) (hE n)) hdisj
  }

/-- Example 1.4.29-/
theorem FinitelyAdditiveMeasure.dirac_isCountablyAdditive {X:Type*} (x₀:X) (B: ConcreteBooleanAlgebra X) (hB : B.isSigmaAlgebra) : (FinitelyAdditiveMeasure.dirac x₀ B).isCountablyAdditive := by
  classical
  constructor
  · exact hB
  · intro E hE hdisj
    change (if x₀ ∈ ⋃ n, E n then (1 : EReal) else 0) = ∑' n, (if x₀ ∈ E n then (1 : EReal) else 0)
    exact (dirac_tsum hdisj).symm

/-- Example 1.4.29-/
theorem FinitelyAdditiveMeasure.counting_isCountablyAdditive {X:Type*} : (FinitelyAdditiveMeasure.counting X).isCountablyAdditive := by
  constructor
  · intro E hE
    trivial
  · intro E hE hdisj
    letI : MeasurableSpace X := ⊤
    have hmeas : ∀ n, MeasurableSet (E n) := fun n => by trivial
    have hUmeas : MeasurableSet (⋃ n, E n) := MeasurableSet.iUnion hmeas
    have hd' : Pairwise (Function.onFun Disjoint E) := fun a b hab => hdisj (Set.mem_univ a) (Set.mem_univ b) hab
    have hcount : (MeasureTheory.Measure.count : Measure X) (⋃ n, E n) = ∑' n, (MeasureTheory.Measure.count : Measure X) (E n) :=
      (MeasureTheory.Measure.count : Measure X).m_iUnion (f := E) hmeas hd'
    calc
      (ENat.card (⋃ n, E n) : EReal) = ((MeasureTheory.Measure.count : Measure X) (⋃ n, E n) : EReal) := by
        rw [MeasureTheory.Measure.count_apply hUmeas]
        simp
      _ = ((∑' n, (MeasureTheory.Measure.count : Measure X) (E n) : ENNReal) : EReal) := by
        rw [hcount]
      _ = (∑' n, ((MeasureTheory.Measure.count : Measure X) (E n) : EReal)) := by
        rw [coe_tsum_ereal (fun n => (MeasureTheory.Measure.count : Measure X) (E n))]
      _ = ∑' n, (ENat.card (E n) : EReal) := by
        apply tsum_congr
        intro n
        rw [MeasureTheory.Measure.count_apply (hmeas n)]
        rfl

/-- Example 1.4.30 -/
@[implicit_reducible]
def CountablyAdditiveMeasure.restrict {X:Type*} {B: ConcreteSigmaAlgebra X} (μ: CountablyAdditiveMeasure B) (A:Set X) (hA:B.measurable A) : CountablyAdditiveMeasure (B.restrict A) :=
  {
    toFinitelyAdditiveMeasure := μ.toFinitelyAdditiveMeasure.restrict A hA,
    measure_countable_additive := by
      intro E hE hdisj
      have hE' : ∀ n, B.measurable (E n : Set X) := fun n => (ConcreteBooleanAlgebra.restrict_iff hA (E n)).mp (hE n)
      have hdisj' : Set.univ.PairwiseDisjoint (fun n => (E n : Set X)) := by
        intro a ha b hb hab
        change Disjoint (Subtype.val '' (E a)) (Subtype.val '' (E b))
        rw [Set.disjoint_iff]
        intro x hx
        rcases hx with ⟨⟨e, he, rfl⟩, ⟨f, hf, hxf⟩⟩
        have hef : f = e := Subtype.val_injective hxf
        exact (Set.disjoint_iff.mp (hdisj (Set.mem_univ a) (Set.mem_univ b) hab)) ⟨by simpa [hef] using he, hf⟩
      have hunion : Subtype.val '' (⋃ n, E n) = ⋃ n, Subtype.val '' (E n) := by
        exact Set.image_iUnion (f := Subtype.val) (s := fun n => E n)
      change μ.measure (Subtype.val '' (⋃ n, E n)) = ∑' n, μ.measure (Subtype.val '' (E n))
      rw [hunion]
      exact μ.measure_countable_additive (fun n => Subtype.val '' (E n)) hE' hdisj'
  }

@[implicit_reducible]
noncomputable instance CountablyAdditiveMeasure.instZero {X:Type*} (B: ConcreteSigmaAlgebra X) : Zero (CountablyAdditiveMeasure B) :=
  {
    zero := {
      toFinitelyAdditiveMeasure := 0
      measure_countable_additive := by
        intro E hE hdisj
        change (0 : EReal) = ∑' n, (0 : EReal)
        simp
    }
  }

@[implicit_reducible]
noncomputable instance CountablyAdditiveMeasure.instAdd {X:Type*} {B: ConcreteSigmaAlgebra X} : Add (CountablyAdditiveMeasure B) :=
  {
    add := fun μ ν =>
      {
        toFinitelyAdditiveMeasure := μ.toFinitelyAdditiveMeasure + ν.toFinitelyAdditiveMeasure
        measure_countable_additive := by
          intro E hE hdisj
          change μ.measure (⋃ n, E n) + ν.measure (⋃ n, E n) = ∑' n, (μ.measure (E n) + ν.measure (E n))
          rw [μ.measure_countable_additive E hE hdisj, ν.measure_countable_additive E hE hdisj]
          exact ereal_tsum_add (fun n => μ.measure (E n)) (fun n => ν.measure (E n))
            (fun n => μ.measure_nonneg (E n)) (fun n => ν.measure_nonneg (E n))
      }
  }

@[ext]
theorem CountablyAdditiveMeasure.ext {X:Type*} {B: ConcreteSigmaAlgebra X} {μ ν : CountablyAdditiveMeasure B}
    (h : ∀ A : Set X, μ.measure A = ν.measure A) : μ = ν := by
  have hf : μ.toFinitelyAdditiveMeasure = ν.toFinitelyAdditiveMeasure := by
    apply FinitelyAdditiveMeasure.ext
    exact h
  change ({ toFinitelyAdditiveMeasure := μ.toFinitelyAdditiveMeasure, measure_countable_additive := μ.measure_countable_additive } :
      CountablyAdditiveMeasure B) =
    { toFinitelyAdditiveMeasure := ν.toFinitelyAdditiveMeasure, measure_countable_additive := ν.measure_countable_additive }
  simp [hf]

@[implicit_reducible]
noncomputable instance CountablyAdditiveMeasure.instAddCommMonoid {X:Type*} {B: ConcreteSigmaAlgebra X} : AddCommMonoid (CountablyAdditiveMeasure B) :=
{
  add_assoc := by
    intro μ ν τ
    ext A
    change (μ.measure A + ν.measure A) + τ.measure A = μ.measure A + (ν.measure A + τ.measure A)
    abel
  zero_add := by
    intro μ
    ext A
    change (0 : EReal) + μ.measure A = μ.measure A
    simp
  add_zero := by
    intro μ
    ext A
    change μ.measure A + 0 = μ.measure A
    simp
  add_comm := by
    intro μ ν
    ext A
    change μ.measure A + ν.measure A = ν.measure A + μ.measure A
    rw [add_comm]
  nsmul := nsmulRec
}

/-- Exercise 1.4.22(i) -/
@[implicit_reducible]
noncomputable instance CountablyAdditiveMeasure.instSmul {X:Type*} {B: ConcreteSigmaAlgebra X} : SMul ENNReal (CountablyAdditiveMeasure B) :=
{
    smul := fun c μ =>
        {
        toFinitelyAdditiveMeasure := c • μ.toFinitelyAdditiveMeasure
        measure_countable_additive := by
          intro E hE hdisj
          change (c : EReal) * μ.measure (⋃ n, E n) = ∑' n, (c : EReal) * μ.measure (E n)
          rw [μ.measure_countable_additive E hE hdisj]
          exact tsum_ereal_mul_left c (fun n => μ.measure (E n)) (fun n => μ.measure_nonneg (E n))
        }
}

@[implicit_reducible]
noncomputable instance CountablyAdditiveMeasure.instDistribMulAction {X:Type*} {B: ConcreteSigmaAlgebra X} : DistribMulAction ENNReal (CountablyAdditiveMeasure B) :=
{
  smul_zero := by
    intro c
    ext A
    change (c : EReal) * 0 = 0
    simp
  smul_add := by
    intro c μ ν
    ext A
    change (c : EReal) * (μ.measure A + ν.measure A) = (c : EReal) * μ.measure A + (c : EReal) * ν.measure A
    exact EReal.left_distrib_of_nonneg (a := μ.measure A) (b := ν.measure A)
      (μ.measure_nonneg A) (ν.measure_nonneg A)
  one_smul := by
    intro μ
    ext A
    change (1 : EReal) * μ.measure A = μ.measure A
    simp
  mul_smul := by
    intro c d μ
    ext A
    change ((c * d : ENNReal) : EReal) * μ.measure A = (c : EReal) * ((d : EReal) * μ.measure A)
    rw [EReal.coe_ennreal_mul, mul_assoc]
}

/-- Exercise 1.4.22(ii) -/
@[implicit_reducible]
noncomputable def CountablyAdditiveMeasure.sum {X:Type*} {B: ConcreteSigmaAlgebra X} (μ: ℕ → CountablyAdditiveMeasure B) : CountablyAdditiveMeasure B :=
  {
    toFinitelyAdditiveMeasure := {
      measure := fun A => ∑' n, (μ n).toFinitelyAdditiveMeasure.measure A
      measure_pos := by
        intro A hA
        have hnn : ∀ n, 0 ≤ (μ n).toFinitelyAdditiveMeasure.measure A := fun n => (μ n).measure_nonneg A
        have hcoe : ∀ n, (((μ n).measure A).toENNReal : EReal) = (μ n).measure A :=
          fun n => EReal.coe_toENNReal (hnn n)
        have hsum : (∑' n, (μ n).measure A) = ((∑' n, ((μ n).measure A).toENNReal : ENNReal) : EReal) := by
          rw [coe_tsum_ereal (fun n => ((μ n).measure A).toENNReal)]
          apply tsum_congr
          intro n
          exact (hcoe n).symm
        rw [hsum]
        exact EReal.coe_ennreal_nonneg _
      measure_nonneg := by
        intro A
        have hnn : ∀ n, 0 ≤ (μ n).toFinitelyAdditiveMeasure.measure A := fun n => (μ n).measure_nonneg A
        have hcoe : ∀ n, (((μ n).measure A).toENNReal : EReal) = (μ n).measure A :=
          fun n => EReal.coe_toENNReal (hnn n)
        have hsum : (∑' n, (μ n).measure A) = ((∑' n, ((μ n).measure A).toENNReal : ENNReal) : EReal) := by
          rw [coe_tsum_ereal (fun n => ((μ n).measure A).toENNReal)]
          apply tsum_congr
          intro n
          exact (hcoe n).symm
        rw [hsum]
        exact EReal.coe_ennreal_nonneg _
      measure_empty := by
        have h0 : ∀ n, (μ n).measure ∅ = 0 := fun n => (μ n).toFinitelyAdditiveMeasure.measure_empty
        calc
          (∑' n, (μ n).measure ∅) = ∑' n, (0 : EReal) := by
            apply tsum_congr
            intro n
            exact h0 n
          _ = 0 := by simp
      measure_finite_additive := by
        intro E F hE hF hdisj
        calc
          (∑' n, (μ n).measure (E ∪ F))
              = ∑' n, ((μ n).measure E + (μ n).measure F) := by
                  apply tsum_congr
                  intro n
                  exact (μ n).measure_finite_additive E F hE hF hdisj
          _ = (∑' n, (μ n).measure E) + (∑' n, (μ n).measure F) := by
                  exact (ereal_tsum_add (fun n => (μ n).measure E) (fun n => (μ n).measure F)
                    (fun n => (μ n).measure_nonneg E) (fun n => (μ n).measure_nonneg F)).symm
    }
    measure_countable_additive := by
      intro E hE hdisj
      calc
        (∑' n, (μ n).measure (⋃ m, E m))
            = ∑' n, (∑' m, (μ n).measure (E m)) := by
                apply tsum_congr
                intro n
                exact (μ n).measure_countable_additive E (fun m => hE m) hdisj
        _ = (∑' m, ∑' n, (μ n).measure (E m)) := by
                exact tsum_comm_ereal (fun n m => (μ n).measure (E m)) (fun n m => (μ n).measure_nonneg (E m))
  }

noncomputable def CountablyAdditiveMeasure.toMeasure {X:Type*} {B: ConcreteSigmaAlgebra X} (μ: CountablyAdditiveMeasure B) :
  @Measure X B.measurableSpace :=
  let _measurable := B.measurableSpace
  Measure.ofMeasurable (m := fun E _ => (μ.measure E).toENNReal)
    (m0 := by
      change (μ.measure ∅).toENNReal = 0
      rw [μ.measure_empty]
      simp)
    (mU := by
      intro f hf hd
      have hmeas : ∀ i, B.measurable (f i) := fun i => hf i
      have hd' : Set.univ.PairwiseDisjoint f := fun a ha b hb hab => hd hab
      have hsum : μ.measure (⋃ i, f i) = ∑' i, μ.measure (f i) :=
        μ.measure_countable_additive f hmeas hd'
      change (μ.measure (⋃ i, f i)).toENNReal = ∑' i, (μ.measure (f i)).toENNReal
      rw [hsum]
      have hcoe : ∀ i, ((μ.measure (f i)).toENNReal : EReal) = μ.measure (f i) :=
        fun i => EReal.coe_toENNReal (μ.measure_nonneg (f i))
      have hsum_coe : (∑' i, μ.measure (f i)) = ((∑' i, (μ.measure (f i)).toENNReal : ENNReal) : EReal) := by
        rw [coe_tsum_ereal (fun i => (μ.measure (f i)).toENNReal)]
        apply tsum_congr
        intro i
        exact (hcoe i).symm
      rw [hsum_coe]
      exact EReal.toENNReal_coe)

noncomputable def FinitelyAdditiveMeasure.isCountablyAdditive.toMeasure {X:Type*} {B: ConcreteBooleanAlgebra X} {μ: FinitelyAdditiveMeasure B} (h: μ.isCountablyAdditive) :
  @Measure X h.1.toSigmaAlgebra.measurableSpace := h.toCountablyAdditive.toMeasure

@[implicit_reducible]
def Measure.toCountablyAdditiveMeasure {X:Type*} [M : MeasurableSpace X] (μ: Measure X) : CountablyAdditiveMeasure M.sigmaAlgebra :=
  {
    toFinitelyAdditiveMeasure := {
      measure E := μ.measureOf E
      measure_pos := by
        intro A hA
        exact EReal.coe_ennreal_nonneg (μ.measureOf A)
      measure_nonneg := by
        intro A
        exact EReal.coe_ennreal_nonneg (μ.measureOf A)
      measure_empty := by
        rw [μ.empty]
        simp
      measure_finite_additive := by
        intro E F hE hF hdisj
        have h : μ.measureOf (E ∪ F) = μ.measureOf E + μ.measureOf F :=
          measure_union (μ := μ) hdisj hF
        change (μ.measureOf (E ∪ F) : EReal) = (μ.measureOf E : EReal) + (μ.measureOf F : EReal)
        rw [h]
        rw [EReal.coe_ennreal_add]
    }
    measure_countable_additive := by
      intro E hE hdisj
      have hd' : Pairwise (Function.onFun Disjoint E) := fun a b hab => hdisj (Set.mem_univ a) (Set.mem_univ b) hab
      have h := μ.m_iUnion (f := E) hE hd'
      change (μ.toOuterMeasure (⋃ n, E n) : EReal) = ∑' n, (μ.toOuterMeasure (E n) : EReal)
      rw [h]
      rw [coe_tsum_ereal (fun n => μ.toOuterMeasure (E n))]
  }

/-- Exercise 1.4.23(i) -/
theorem Measure.countable_subadditivity {X:Type*} [MeasurableSpace X] (μ: Measure X) {E : ℕ → Set X} (_hE: ∀ n, Measurable (E n)) :
  μ.measureOf (⋃ n, E n) ≤ ∑' n, μ.measureOf (E n) := by
  exact measure_iUnion_le (μ := μ) E

/-- Exercise 1.4.23(ii) -/
theorem Measure.upwards_mono {X:Type*} [MeasurableSpace X] (μ: Measure X) {E : ℕ → Set X} (_hE: ∀ n, Measurable (E n))
  (hmono : Monotone E) : μ (⋃ n, E n) = ⨆ n, μ.measureOf (E n) := by
  exact hmono.measure_iUnion

/-- Exercise 1.4.23(iii) -/
theorem Measure.downwards_mono {X:Type*} [MeasurableSpace X] (μ: Measure X) {E : ℕ → Set X} (hE: ∀ n, Measurable (E n))
  (hmono : Antitone E) (hfin : ∃ n, μ (E n) < ⊤) : μ (⋂ n, E n) = ⨅ n, μ.measureOf (E n) := by
  have hmeasSet : ∀ i, MeasurableSet (E i) := by
    intro i
    have h := hE i (by trivial : MeasurableSet ({True} : Set Prop))
    have heq : E i ⁻¹' ({True} : Set Prop) = E i := by
      ext x
      rw [Set.mem_preimage]
      simp
      rfl
    rwa [heq] at h
  exact hmono.measure_iInter (hsm := fun i => (hmeasSet i).nullMeasurableSet) (hfin := hfin.imp (fun n hn => ne_of_lt hn))

theorem Measure.downwards_mono_counter : ∃ (X:Type) (_M: MeasurableSpace X) (μ: Measure X) (E : ℕ → Set X) (_hE: ∀ n, Measurable (E n))
  (_hmono : Antitone E), μ (⋂ n, E n) ≠ ⨅ n, μ.measureOf (E n) := by
  refine ⟨ℕ, ⊤, Measure.count, fun n => {m : ℕ | n ≤ m}, ?_, ?_, ?_⟩
  · intro n s hs
    trivial
  · intro a b hab m hm
    simp at hm ⊢
    omega
  · change Measure.count (⋂ n, {m : ℕ | n ≤ m}) ≠ ⨅ n, Measure.count.measureOf {m : ℕ | n ≤ m}
    have hinter : (⋂ n, {m : ℕ | n ≤ m}) = ∅ := by
      ext m
      constructor
      · intro hm
        rw [Set.mem_iInter] at hm
        have hmm : m + 1 ≤ m := hm (m + 1)
        omega
      · intro hm
        exact False.elim hm
    have hcount0 : Measure.count (⋂ n, {m : ℕ | n ≤ m}) = 0 := by
      rw [hinter]
      simp
    have hinf : ∀ n, Measure.count.measureOf {m : ℕ | n ≤ m} = (⊤ : ENNReal) := by
      intro n
      change Measure.count {m : ℕ | n ≤ m} = (⊤ : ENNReal)
      rw [Measure.count_apply_eq_top]
      have hrange : {m : ℕ | n ≤ m} = Set.range (fun k : ℕ => n + k) := by
        ext m
        constructor
        · intro hm
          rw [Set.mem_range]
          refine ⟨m - n, ?_⟩
          have hnle : n ≤ m := by simpa using hm
          omega
        · intro hm
          rw [Set.mem_range] at hm
          rcases hm with ⟨k, hk⟩
          simp
          omega
      rw [hrange]
      exact Set.infinite_range_of_injective (f := fun k : ℕ => n + k) (by intro a b h; exact Nat.add_left_cancel h)
    have hiinf : (⨅ n, Measure.count.measureOf {m : ℕ | n ≤ m}) = (⊤ : ENNReal) := by
      rw [iInf_eq_top]
      exact hinf
    rw [hcount0, hiinf]
    exact ENNReal.zero_ne_top

/-- Genuine pointwise convergence of sets: the indicators converge at each point.
  Unlike the general PointwiseConvergesTo, this requires both directions
  (the Sierpinski topology on Prop makes the general notion one-sided). -/
def SetConvergesTo {X:Type*} (E : ℕ → Set X) (E' : Set X) : Prop :=
  ∀ x : X, ∀ᶠ n in Filter.atTop, x ∈ E n ↔ x ∈ E'

/-- Exercise 1.4.24 (i) (Dominated convergence for sets) -/
theorem Measure.measurable_of_lim {X:Type*} [MeasurableSpace X] (_μ: Measure X) {E : ℕ → Set X} (hE: ∀ n, Measurable (E n))
  {E' : Set X} (hlim : SetConvergesTo E E') : Measurable E' := by
  -- Convert hE : ∀ n, Measurable (E n) to MeasurableSet (E n)
  have hEmeas : ∀ n : ℕ, MeasurableSet (E n) := by
    intro n
    have h := hE n (by trivial : MeasurableSet ({True} : Set Prop))
    have heq : E n ⁻¹' ({True} : Set Prop) = E n := by
      ext x
      rw [Set.mem_preimage]
      simp
      rfl
    rwa [heq] at h
  -- Step 1: E' = {x | ∀ᶠ n, x ∈ E n}
  have hE' : E' = {x : X | ∀ᶠ n in Filter.atTop, x ∈ E n} := by
    ext x
    constructor
    · intro hx
      filter_upwards [hlim x] with n hn
      exact hn.mpr hx
    · intro hx
      by_contra hx'
      change ∀ᶠ n in Filter.atTop, x ∈ E n at hx
      rcases Filter.eventually_atTop.mp (hx.and (hlim x)) with ⟨N, hN⟩
      have hboth : x ∈ E N ∧ (x ∈ E N ↔ x ∈ E') := hN N (le_refl N)
      exact hx' (hboth.2.mp hboth.1)
  -- Step 2: {x | ∀ᶠ n, x ∈ E n} is measurable
  have hmeaslim : MeasurableSet {x : X | ∀ᶠ n in Filter.atTop, x ∈ E n} := by
    have hEq : {x : X | ∀ᶠ n in Filter.atTop, x ∈ E n} = ⋃ N : ℕ, ⋂ n : {n : ℕ // N ≤ n}, E n.1 := by
      ext x
      constructor
      · intro hx
        change ∀ᶠ n in Filter.atTop, x ∈ E n at hx
        rcases Filter.eventually_atTop.mp hx with ⟨N, hN⟩
        rw [Set.mem_iUnion]
        refine ⟨N, ?_⟩
        rw [Set.mem_iInter]
        intro n
        exact hN n.1 n.2
      · intro hx
        rw [Set.mem_iUnion] at hx
        rcases hx with ⟨N, hN⟩
        change ∀ᶠ n in Filter.atTop, x ∈ E n
        rw [Filter.eventually_atTop]
        refine ⟨N, ?_⟩
        intro n hn
        rw [Set.mem_iInter] at hN
        exact hN ⟨n, hn⟩
    rw [hEq]
    apply MeasurableSet.iUnion
    intro N
    apply MeasurableSet.iInter
    intro n
    exact hEmeas n.1
  -- Step 3: MeasurableSet E' → Measurable E'
  have hE'meas : MeasurableSet E' := by
    rw [hE']
    exact hmeaslim
  intro s hs
  by_cases hT : True ∈ s
  · by_cases hF : False ∈ s
    · have hpre : E' ⁻¹' s = Set.univ := by
        ext x
        constructor
        · intro _; trivial
        · intro _; by_cases hx' : E' x
          · have hEqT : E' x = True := propext (Iff.intro (fun _ => trivial) (fun _ => hx'))
            simp [Set.preimage, hEqT, hT]
          · have hEqF : E' x = False := propext (Iff.intro (fun h : E' x => False.elim (hx' h)) (fun f => False.elim f))
            simp [Set.preimage, hEqF, hF]
      rw [hpre]
      exact MeasurableSet.univ
    · have hpre : E' ⁻¹' s = E' := by
        ext x
        constructor
        · intro hx
          by_contra hx'
          have hEqF : E' x = False := propext (Iff.intro (fun h : E' x => False.elim (hx' h)) (fun f => False.elim f))
          simp [Set.preimage, hEqF] at hx
          exact hF hx
        · intro hx
          have hEqT : E' x = True := propext (Iff.intro (fun _ => trivial) (fun _ => hx))
          simp [Set.preimage, hEqT, hT]
      rw [hpre]
      exact hE'meas
  · by_cases hF : False ∈ s
    · have hpre : E' ⁻¹' s = E'ᶜ := by
        ext x
        constructor
        · intro hx hx'
          have hEqT : E' x = True := propext (Iff.intro (fun _ => trivial) (fun _ => hx'))
          simp [Set.preimage, hEqT] at hx
          exact hT hx
        · intro hx
          have hEqF : E' x = False := propext (Iff.intro (fun h : E' x => False.elim (hx h)) (fun f => False.elim f))
          simp [Set.preimage, hEqF, hF]
      rw [hpre]
      exact MeasurableSet.compl hE'meas
    · have hpre : E' ⁻¹' s = ∅ := by
        ext x
        constructor
        · intro hx
          by_cases hx' : E' x
          · have hEqT : E' x = True := propext (Iff.intro (fun _ => trivial) (fun _ => hx'))
            simp [Set.preimage, hEqT] at hx
            exact hT hx
          · have hEqF : E' x = False := propext (Iff.intro (fun h : E' x => False.elim (hx' h)) (fun f => False.elim f))
            simp [Set.preimage, hEqF] at hx
            exact hF hx
        · intro hx
          exact False.elim hx
      rw [hpre]
      exact MeasurableSet.empty

/-- The liminf of a SetConvergesTo-convergent sequence is the limit set. -/
private lemma set_converges_eq_liminf {X : Type*} {E : ℕ → Set X} {E' : Set X}
    (hlim : SetConvergesTo E E') :
    E' = (⋃ N : ℕ, ⋂ n : {n : ℕ // N ≤ n}, E n.1) := by
  apply le_antisymm
  · intro x hx
    rw [Set.mem_iUnion]
    rcases Filter.eventually_atTop.mp (hlim x) with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    rw [Set.mem_iInter]
    intro n
    exact (hN n.1 n.2).mpr hx
  · intro x hx
    by_contra hx'
    rcases Filter.eventually_atTop.mp (hlim x) with ⟨N, hN⟩
    rw [Set.mem_iUnion] at hx
    rcases hx with ⟨M, hM⟩
    rw [Set.mem_iInter] at hM
    have hxEM : x ∈ E (max N M) := hM ⟨max N M, le_max_right N M⟩
    have hiff : x ∈ E (max N M) ↔ x ∈ E' := hN (max N M) (le_max_left N M)
    exact hx' (hiff.mp hxEM)

/-- The limsup of a SetConvergesTo-convergent sequence is the limit set. -/
private lemma set_converges_eq_limsup {X : Type*} {E : ℕ → Set X} {E' : Set X}
    (hlim : SetConvergesTo E E') :
    E' = (⋂ N : ℕ, ⋃ n : {n : ℕ // N ≤ n}, E n.1) := by
  apply le_antisymm
  · intro x hx
    rw [Set.mem_iInter]
    intro N
    rw [Set.mem_iUnion]
    rcases Filter.eventually_atTop.mp (hlim x) with ⟨M, hM⟩
    let n₀ := max N M
    refine ⟨⟨n₀, le_max_left N M⟩, ?_⟩
    exact (hM n₀ (le_max_right N M)).mpr hx
  · intro x hx
    by_contra hx'
    rcases Filter.eventually_atTop.mp (hlim x) with ⟨N, hN⟩
    rw [Set.mem_iInter] at hx
    rcases Set.mem_iUnion.mp (hx N) with ⟨n, hn⟩
    exact hx' ((hN n.1 n.2).mp hn)

/-- Exercise 1.4.24 (ii) (Dominated convergence for sets) -/
theorem Measure.measure_of_lim {X:Type*} [MeasurableSpace X] (μ: Measure X) {E : ℕ → Set X} (hE: ∀ n, Measurable (E n))
  {E' F : Set X} (hlim : SetConvergesTo E E') (_hF : Measurable F) (hfin : μ F < ⊤) (hcon : ∀ n, E n ⊆ F) :
  Filter.atTop.Tendsto (fun n ↦ μ (E n)) (nhds (μ E')) := by
  -- Define liminf and limsup tails
  let L : ℕ → Set X := fun N => ⋂ n : {n : ℕ // N ≤ n}, E n.1
  let U : ℕ → Set X := fun N => ⋃ n : {n : ℕ // N ≤ n}, E n.1
  -- L is monotone, U is antitone
  have hLmono : Monotone L := by
    intro a b hab x hx
    dsimp [L] at hx ⊢
    rw [Set.mem_iInter] at hx ⊢
    intro n
    exact hx ⟨n.1, le_trans hab n.2⟩
  have hUanti : Antitone U := by
    intro a b hab x hx
    dsimp [U] at hx
    rw [Set.mem_iUnion] at hx ⊢
    rcases hx with ⟨n, hn⟩
    exact ⟨⟨n.1, le_trans hab n.2⟩, hn⟩
  -- E' = ⋃ L = ⋂ U
  have hE'L : E' = ⋃ N, L N := by
    rw [← set_converges_eq_liminf hlim]
  have hE'U : E' = ⋂ N, U N := by
    rw [← set_converges_eq_limsup hlim]
  -- μ (L N) → μ E'
  have hLtendsto : Filter.atTop.Tendsto (fun N => μ (L N)) (nhds (μ E')) := by
    have ht : Filter.atTop.Tendsto (fun N => μ (L N)) (nhds (μ (⋃ N, L N))) := by
      exact tendsto_measure_iUnion_atTop hLmono
    rw [← hE'L] at ht
    exact ht
  -- μ (U N) → μ E'
  have hUtendsto : Filter.atTop.Tendsto (fun N => μ (U N)) (nhds (μ E')) := by
    have hfin' : ∃ N, μ (U N) ≠ ⊤ := by
      refine ⟨0, ?_⟩
      have hU0F : U 0 ⊆ F := by
        intro x hx
        dsimp [U] at hx
        rw [Set.mem_iUnion] at hx
        rcases hx with ⟨n, hn⟩
        exact hcon n.1 hn
      exact ne_top_of_le_ne_top (ne_of_lt hfin) (measure_mono hU0F)
    have hnull : ∀ N, NullMeasurableSet (U N) μ := by
      intro N
      have hUmeas : MeasurableSet (U N) := by
        dsimp [U]
        apply MeasurableSet.iUnion
        intro n
        have h := hE n.1 (by trivial : MeasurableSet ({True} : Set Prop))
        have heq : E n.1 ⁻¹' ({True} : Set Prop) = E n.1 := by
          ext x
          rw [Set.mem_preimage]
          simp
          rfl
        rwa [heq] at h
      exact hUmeas.nullMeasurableSet
    have ht : Filter.atTop.Tendsto (fun N => μ (U N)) (nhds (μ (⋂ N, U N))) := by
      exact tendsto_measure_iInter_atTop hnull hUanti hfin'
    rw [← hE'U] at ht
    exact ht
  -- Squeeze: μ (L N) ≤ μ (E N) ≤ μ (U N)
  have hLE : ∀ N, μ (L N) ≤ μ (E N) := by
    intro N
    apply measure_mono
    intro x hx
    dsimp [L] at hx
    rw [Set.mem_iInter] at hx
    exact hx ⟨N, le_refl N⟩
  have hEU : ∀ N, μ (E N) ≤ μ (U N) := by
    intro N
    apply measure_mono
    intro x hx
    dsimp [U]
    rw [Set.mem_iUnion]
    exact ⟨⟨N, le_refl N⟩, hx⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hLtendsto hUtendsto hLE hEU

/-- Exercise 1.4.24 (iii) (Dominated convergence for sets) -/
theorem Measure.measure_of_lim_counter : ∃ (X:Type) (_M:MeasurableSpace X) (μ: Measure X) (E : ℕ → Set X) (_hE: ∀ n, Measurable (E n))
  (E' F : Set X) (_hlim : SetConvergesTo E E') (_hF : Measurable F) (_hcon : ∀ n, E n ⊆ F),
  ¬ Filter.atTop.Tendsto (fun n ↦ μ (E n)) (nhds (μ E')) := by
  refine ⟨ℕ, ⊤, Measure.count, fun n => {m : ℕ | n ≤ m}, ?hE, ∅, Set.univ, ?hlim, ?hF, ?hcon, ?hnot⟩
  · intro n s _hs
    trivial
  · intro x
    filter_upwards [Filter.eventually_ge_atTop (x + 1)] with n hn
    constructor <;> intro hx
    · have hlt : x < n := by omega
      exact (not_le_of_gt hlt) hx
    · exact False.elim hx
  · intro s _hs
    trivial
  · intro n m _hm
    trivial
  · intro ht
    have hconst : ∀ n, Measure.count ({m : ℕ | n ≤ m}) = (⊤ : ENNReal) := by
      intro n
      rw [Measure.count_apply_eq_top]
      have hinf : ({m : ℕ | n ≤ m}).Infinite := by
        intro hfin
        rcases hfin.bddAbove with ⟨M, hM⟩
        have hnM : n ≤ M := hM (show n ∈ ({m : ℕ | n ≤ m}) from by simp)
        have hM1 : M + 1 ∈ ({m : ℕ | n ≤ m}) := by
          simp
          omega
        have hle : M + 1 ≤ M := hM hM1
        omega
      exact hinf
    have hseq : (fun n : ℕ => Measure.count ({m : ℕ | n ≤ m})) = fun _ : ℕ => (⊤ : ENNReal) := by
      funext n
      exact hconst n
    have hzero : Measure.count (∅ : Set ℕ) = (0 : ENNReal) := by simp
    dsimp at ht
    rw [hseq, hzero] at ht
    have htop_eq_zero : (⊤ : ENNReal) = 0 := tendsto_const_nhds_iff.mp ht
    exact ENNReal.top_ne_zero htop_eq_zero

/-- Exercise 1.4.25 -/
theorem Measure.on_countable {X:Type*} [Countable X] [M: MeasurableSpace X] (hM: M = ⊤) (μ: Measure X) :
  ∃! c : X → ENNReal, ∀ E : Set X, μ E = ∑' x : E, c x := by
  -- Existence: c x = μ {x}
  refine ⟨fun x => μ ({x} : Set X), ?_, ?_⟩
  · intro E
    have hdisj : Pairwise (Function.onFun Disjoint (fun x : E => ({x.1} : Set X))) := by
      intro a b hab
      rw [Function.onFun]
      rw [Set.disjoint_iff]
      intro x hx
      rcases hx with ⟨hxa, hxb⟩
      simp at hxa hxb
      have hab' : a.1 = b.1 := hxa.symm ▸ hxb
      exact hab (Subtype.ext hab')
    have hmeas : ∀ x : E, MeasurableSet ({x.1} : Set X) := by
      intro x
      rw [hM]
      trivial
    have hEq : E = ⋃ x : E, ({x.1} : Set X) := by
      ext x
      constructor
      · intro hx
        rw [Set.mem_iUnion]
        refine ⟨⟨x, hx⟩, ?_⟩
        simp
      · intro hx
        rw [Set.mem_iUnion] at hx
        rcases hx with ⟨y, hy⟩
        simp at hy
        exact hy ▸ y.2
    calc
      μ E = μ (⋃ x : E, ({x.1} : Set X)) := by exact congrArg μ hEq
      _ = ∑' x : E, μ ({x.1} : Set X) := by
        exact measure_iUnion hdisj hmeas
  · intro c hc
    funext x
    have h := hc ({x} : Set X)
    have htsum : (∑' y : ({x} : Set X), c y) = c x := by
      rw [tsum_subtype]
      rw [tsum_eq_single x]
      · simp
      · intro y hy
        simp [hy]
    rw [h, htsum]

-- Definition 1.4.31
#check Measure.IsComplete

#check NullMeasurableSpace

#check Measure.completion

/-- Exercise 1.4.26 (Completion) -/
theorem Measure.completion_lt {X:Type*} [M : MeasurableSpace X] (μ: Measure X) (M' : MeasurableSpace X) (μ' : @Measure X M')
  (hcomplete : μ'.IsComplete) (hMM' : M ≤ M') (hμ : ∀ E, M.MeasurableSet' E → μ E = μ' E) : ∀ E : Set X, @NullMeasurableSet X M E μ → (M'.MeasurableSet' E ∧ μ' E = μ.completion E)
   := by
  intro E hE
  rcases NullMeasurableSet.exists_measurable_superset_ae_eq hE with ⟨B, hEB, hBmeasM, hBE⟩
  have hμsd : μ (symmDiff E B) = 0 := by
    exact MeasureTheory.measure_symmDiff_eq_zero_iff.mpr (ae_eq_symm hBE)
  let D : Set X := symmDiff E B
  let N : Set X := @toMeasurable X M μ D
  have hDsubN : D ⊆ N := by
    dsimp [N]
    exact @subset_toMeasurable X M μ D
  have hNmeasM : M.MeasurableSet' N := by
    dsimp [N]
    exact @measurableSet_toMeasurable X M μ D
  have hNμ0 : μ N = 0 := by
    dsimp [N]
    rw [@measure_toMeasurable X M μ D]
    exact hμsd
  have hNmeasM' : M'.MeasurableSet' N := hMM' N hNmeasM
  have hNμ'0 : μ' N = 0 := by
    exact (hμ N hNmeasM).symm.trans hNμ0
  have hDμ'0 : μ' D = 0 := by
    apply le_antisymm
    · have hle : μ' D ≤ μ' N := @measure_mono X (@Measure X M') _ _ μ' D N hDsubN
      rwa [hNμ'0] at hle
    · exact zero_le (μ' D)
  have hDmeasM' : M'.MeasurableSet' D := by
    exact (@Measure.isComplete_iff X M' μ').mp hcomplete D hDμ'0
  have hBmeasM' : M'.MeasurableSet' B := hMM' B hBmeasM
  have hEeq : E = symmDiff B D := by
    unfold D
    ext x
    simp [Set.mem_symmDiff]
    by_cases hx : x ∈ E
    · by_cases hb : x ∈ B
      · simp [hx, hb]
      · simp [hx, hb]
    · by_cases hb : x ∈ B
      · simp [hx, hb]
      · simp [hx, hb]
  have hEmeasM' : M'.MeasurableSet' E := by
    rw [hEeq]
    rw [Set.symmDiff_def]
    have hBm : @MeasurableSet X M' B := hBmeasM'
    have hDm : @MeasurableSet X M' D := hDmeasM'
    exact @MeasurableSet.union X M' (B \ D) (D \ B) (hBm.diff hDm) (hDm.diff hBm)
  have hμ'E : μ' E = μ' B := by
    have hEBsub : E \ B ⊆ D := by
      unfold D
      intro x hx
      rw [Set.mem_symmDiff]
      exact Or.inl hx
    have hBEsub : B \ E ⊆ D := by
      unfold D
      intro x hx
      rw [Set.mem_symmDiff]
      exact Or.inr hx
    have hE_B0 : μ' (E \ B) = 0 := @measure_mono_null X (@Measure X M') _ _ μ' (E \ B) D hEBsub hDμ'0
    have hB_E0 : μ' (B \ E) = 0 := @measure_mono_null X (@Measure X M') _ _ μ' (B \ E) D hBEsub hDμ'0
    have h1 : μ' (E ∩ B) + μ' (E \ B) = μ' E := by
      rw [← @MeasureTheory.measure_inter_add_diff X M' μ' B E hBmeasM']
    have h2 : μ' (B ∩ E) + μ' (B \ E) = μ' B := by
      rw [← @MeasureTheory.measure_inter_add_diff X M' μ' E B hEmeasM']
    have h1' : μ' E = μ' (E ∩ B) := by
      rw [← h1, hE_B0]
      simp
    have h2' : μ' B = μ' (B ∩ E) := by
      rw [← h2, hB_E0]
      simp
    have hinter : μ' (E ∩ B) = μ' (B ∩ E) := by
      congr 1
      ext x
      simp [and_comm]
    exact h1'.trans (hinter.trans h2'.symm)
  have hμ'B : μ' B = μ B := (hμ B hBmeasM).symm
  have hμBE : μ B = μ E := MeasureTheory.measure_congr hBE
  have hμcomp : μ E = μ.completion E := (@Measure.completion_apply X M μ E).symm
  exact ⟨hEmeasM', (hμ'E.trans hμ'B).trans (hμBE.trans hμcomp)⟩

noncomputable def EuclideanSpace'.lebesgueMeasure (d:ℕ) := (FinitelyAdditiveMeasure.lebesgue_isCountablyAdditive d).toMeasure

noncomputable def EuclideanSpace'.borelMeasure (d:ℕ) := ((FinitelyAdditiveMeasure.lebesgue_isCountablyAdditive d).toCountablyAdditive.restrict_alg (BorelSigmaAlgebra.le_LebesgueSigmaAlgebra d)).toMeasure

def Measure.equiv {X:Type*} {M M' : MeasurableSpace X} (μ: @Measure X M) (μ': @Measure X M') : Prop := M = M' ∧ ∀ E, M.MeasurableSet' E → μ E = μ' E

private lemma ereal_toENNReal_mono {a b : EReal} (h : a ≤ b) : a.toENNReal ≤ b.toENNReal := by
  by_cases hb : b ≤ 0
  · rw [EReal.toENNReal_of_nonpos hb, EReal.toENNReal_of_nonpos (le_trans h hb)]
  · have hb' : 0 < b := lt_of_not_ge hb
    by_cases ha : a ≤ 0
    · rw [EReal.toENNReal_of_nonpos ha]
      exact (EReal.toENNReal_pos_iff.mpr hb').le
    · have ha' : 0 < a := lt_of_not_ge ha
      rw [← EReal.coe_ennreal_le_coe_ennreal_iff]
      rw [EReal.coe_toENNReal (le_of_lt ha'), EReal.coe_toENNReal (le_of_lt hb')]
      exact h

private lemma measure_diff_zero_of_ae_eq {α : Type*} [MeasurableSpace α] (μ : Measure α) {s t : Set α}
    (h : t =ᶠ[ae μ] s) : μ (s \ t) = 0 := by
  have hsymm : μ (symmDiff s t) = 0 := measure_symmDiff_eq_zero_iff.mpr h.symm
  exact le_antisymm (by
    apply le_trans (measure_mono (by intro x hx; rw [Set.mem_symmDiff]; exact Or.inl hx))
    simp [hsymm]) (zero_le _)

private lemma borel_measure_on_borel {d : ℕ} {B : Set (EuclideanSpace' d)} (hB : (BorelSigmaAlgebra (EuclideanSpace' d)).measurable B) :
    (EuclideanSpace'.borelMeasure d) B = (Lebesgue_outer_measure B).toENNReal := by
  letI : MeasurableSpace (EuclideanSpace' d) := (BorelSigmaAlgebra (EuclideanSpace' d)).measurableSpace
  unfold EuclideanSpace'.borelMeasure CountablyAdditiveMeasure.toMeasure
  rw [Measure.ofMeasurable_apply B hB]
  rfl

private lemma lebesgue_measure_on_measurable {d : ℕ} {E : Set (EuclideanSpace' d)} (hE : LebesgueMeasurable E) :
    (EuclideanSpace'.lebesgueMeasure d) E = (Lebesgue_outer_measure E).toENNReal := by
  letI : MeasurableSpace (EuclideanSpace' d) := (LebesgueMeasurable.sigmaAlgebra d).measurableSpace
  unfold EuclideanSpace'.lebesgueMeasure FinitelyAdditiveMeasure.isCountablyAdditive.toMeasure CountablyAdditiveMeasure.toMeasure
  rw [Measure.ofMeasurable_apply E hE]
  rfl

private lemma borel_measurable_iff_mathlib {d : ℕ} (s : Set (EuclideanSpace' d)) :
    (BorelSigmaAlgebra (EuclideanSpace' d)).measurable s ↔ MeasurableSet s := by
  have hborel : (inferInstance : MeasurableSpace (EuclideanSpace' d)) = borel (EuclideanSpace' d) :=
    BorelSpace.measurable_eq
  change (BorelSigmaAlgebra (EuclideanSpace' d)).measurable s ↔
    (inferInstance : MeasurableSpace (EuclideanSpace' d)).MeasurableSet' s
  rw [hborel]
  constructor
  · intro h
    let B : ConcreteSigmaAlgebra (EuclideanSpace' d) :=
      MeasurableSpace.sigmaAlgebra (MeasurableSpace.generateFrom (setOf (fun U : Set (EuclideanSpace' d) => IsOpen U)))
    have hle : ConcreteSigmaAlgebra.generated_by { U : Set (EuclideanSpace' d) | IsOpen U } ≤ B := by
      apply ConcreteSigmaAlgebra.generated_by_le'
      intro U hU
      exact MeasurableSpace.measurableSet_generateFrom hU
    exact hle s h
  · intro h
    exact (MeasurableSpace.generateFrom_le (s := {U : Set (EuclideanSpace' d) | IsOpen U})
      (m := (BorelSigmaAlgebra (EuclideanSpace' d)).measurableSpace) (by
        intro U hU
        exact (ConcreteSigmaAlgebra.generated_by_contains (F := {U : Set (EuclideanSpace' d) | IsOpen U}) hU :
          (BorelSigmaAlgebra (EuclideanSpace' d)).measurable U))) s h

private lemma borelMeasure_of_null {d : ℕ} {N : Set (EuclideanSpace' d)} (hN : IsNull N) :
    (EuclideanSpace'.borelMeasure d) N = 0 := by
  apply le_antisymm
  · apply ENNReal.le_of_forall_pos_le_add
    intro δ hδ _
    have hδℝ : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
    have hlt : sInf {V : EReal | ∃ (X : Set ℕ) (S : X → Box d),
        N ⊆ ⋃ n, (S n).toSet ∧ V = ∑' n, (S n).volume.toEReal} < ((δ : ℝ) : EReal) := by
      change Lebesgue_outer_measure N < ((δ : ℝ) : EReal)
      rw [hN]
      exact EReal.coe_strictMono hδℝ
    have hcover : ∃ a ∈ {V : EReal | ∃ (X : Set ℕ) (S : X → Box d),
        N ⊆ ⋃ n, (S n).toSet ∧ V = ∑' n, (S n).volume.toEReal}, a < ((δ : ℝ) : EReal) := by
      exact sInf_lt_iff.mp hlt
    rcases hcover with ⟨V, hV, hVlt⟩
    rcases hV with ⟨X, S, hsub, rfl⟩
    calc
      (EuclideanSpace'.borelMeasure d) N ≤ (EuclideanSpace'.borelMeasure d) (⋃ n : X, (S n).toSet) :=
        measure_mono hsub
      _ ≤ ∑' n : X, (EuclideanSpace'.borelMeasure d) ((S n).toSet) :=
        measure_iUnion_le (fun n : X => (S n).toSet)
      _ = ∑' n : X, (((S n).volume : ℝ) : EReal).toENNReal := by
        apply tsum_congr
        intro n
        rw [borel_measure_on_borel (Box.borel_measurable (S n))]
        rw [Lebesgue_outer_measure.elementary (S n).toSet (IsElementary.box (S n))]
        rw [IsElementary.measure_of_box (S n)]
      _ = (∑' n : X, (((S n).volume : ℝ) : EReal)).toENNReal := by
        exact (EReal.toENNReal_tsum_of_nonneg (by
          intro n
          exact EReal.coe_nonneg.mpr (Box.volume_nonneg (S n)))).symm
      _ ≤ ((δ : ℝ) : EReal).toENNReal := ereal_toENNReal_mono (le_of_lt hVlt)
      _ = (δ : ENNReal) := by
        simp
    · simp
  · exact zero_le _

local instance borelMeasurableSpace' (d : ℕ) : MeasurableSpace (EuclideanSpace' d) :=
  (BorelSigmaAlgebra (EuclideanSpace' d)).measurableSpace

private lemma borelNullMeasurable_iff_lebesgue {d : ℕ} (s : Set (EuclideanSpace' d)) :
    NullMeasurableSet s (EuclideanSpace'.borelMeasure d) ↔ LebesgueMeasurable s := by
  letI : MeasurableSpace (EuclideanSpace' d) := (BorelSigmaAlgebra (EuclideanSpace' d)).measurableSpace
  constructor
  · intro h
    rcases NullMeasurableSet.exists_measurable_subset_ae_eq h with ⟨B, hBsub, hBmeas, hBeq⟩
    have hμdiff : (EuclideanSpace'.borelMeasure d) (s \ B) = 0 :=
      measure_diff_zero_of_ae_eq (EuclideanSpace'.borelMeasure d) hBeq
    have hLebB : LebesgueMeasurable B :=
      (BorelSigmaAlgebra.le_LebesgueSigmaAlgebra d) B hBmeas
    have hT0 : (EuclideanSpace'.borelMeasure d) (toMeasurable (EuclideanSpace'.borelMeasure d) (s \ B)) = 0 := by
      rw [measure_toMeasurable]
      exact hμdiff
    have hTmeas : (BorelSigmaAlgebra (EuclideanSpace' d)).measurable
        (toMeasurable (EuclideanSpace'.borelMeasure d) (s \ B)) :=
      measurableSet_toMeasurable (EuclideanSpace'.borelMeasure d) (s \ B)
    have hL0 : (Lebesgue_outer_measure (toMeasurable (EuclideanSpace'.borelMeasure d) (s \ B))).toENNReal = 0 := by
      rw [← borel_measure_on_borel hTmeas]
      exact hT0
    have hle0 : Lebesgue_outer_measure (toMeasurable (EuclideanSpace'.borelMeasure d) (s \ B)) ≤ 0 :=
      EReal.toENNReal_eq_zero_iff.mp hL0
    have hnull : IsNull (s \ B) := by
      unfold IsNull
      exact le_antisymm
        (le_trans (Lebesgue_outer_measure.mono (subset_toMeasurable (EuclideanSpace'.borelMeasure d) (s \ B))) hle0)
        (Lebesgue_outer_measure.nonneg _)
    have hLebT : LebesgueMeasurable (s \ B) := IsNull.measurable hnull
    have hEq : s = B ∪ (s \ B) := by
      ext x
      constructor
      · intro hx
        by_cases hxB : x ∈ B
        · exact Or.inl hxB
        · exact Or.inr ⟨hx, hxB⟩
      · intro hx
        rcases hx with hxB | hx
        · exact hBsub hxB
        · exact hx.1
    rw [hEq]
    exact LebesgueMeasurable.union hLebB hLebT
  · intro hLeb
    rcases lebesgue_measurable_eq_borel_sdiff_null hLeb with ⟨B, hB, N, hN, hEq⟩
    have hBm : MeasurableSet B := hB
    have hNμ : (EuclideanSpace'.borelMeasure d) N = 0 := borelMeasure_of_null hN
    have hNn : NullMeasurableSet N (EuclideanSpace'.borelMeasure d) := NullMeasurableSet.of_null hNμ
    have hEn : NullMeasurableSet (B \ N) (EuclideanSpace'.borelMeasure d) :=
      NullMeasurableSet.diff hBm.nullMeasurableSet hNn
    simpa [hEq] using hEn

/-- For E ⊆ B with B \ E ⊆ N (N null), the Borel measure of E equals that of B. -/
private lemma borel_measure_sdiff_eq {d : ℕ} {E B N : Set (EuclideanSpace' d)}
    (hN : IsNull N) (hEB : E ⊆ B) (hBE : B \ E ⊆ N) :
    (EuclideanSpace'.borelMeasure d) E = (EuclideanSpace'.borelMeasure d) B := by
  letI : MeasurableSpace (EuclideanSpace' d) := (BorelSigmaAlgebra (EuclideanSpace' d)).measurableSpace
  have hN0 : (EuclideanSpace'.borelMeasure d) N = 0 := borelMeasure_of_null hN
  have hBE0 : (EuclideanSpace'.borelMeasure d) (B \ E) = 0 := by
    exact le_antisymm (by rw [← hN0]; exact measure_mono hBE) (zero_le _)
  have h1 : (EuclideanSpace'.borelMeasure d) E ≤ (EuclideanSpace'.borelMeasure d) B := measure_mono hEB
  have hunion : B = E ∪ (B \ E) := by
    ext x; constructor
    · intro hxB; by_cases hxE : x ∈ E; exact Or.inl hxE; exact Or.inr ⟨hxB, hxE⟩
    · intro hx; rcases hx with hx | hx; exact hEB hx; exact hx.1
  have h2 : (EuclideanSpace'.borelMeasure d) B ≤ (EuclideanSpace'.borelMeasure d) E := by
    rw [hunion]
    simpa [hBE0] using (measure_union_le (μ := (EuclideanSpace'.borelMeasure d)) E (B \ E))
  exact le_antisymm h1 h2

/-- For E ⊆ B with B \ E ⊆ N (N null), the Lebesgue measure of E equals that of B. -/
private lemma lebesgue_measure_sdiff_eq {d : ℕ} {E B N : Set (EuclideanSpace' d)}
    (hE : LebesgueMeasurable E) (hB : (BorelSigmaAlgebra (EuclideanSpace' d)).measurable B)
    (hN : IsNull N) (hEB : E ⊆ B) (hBE : B \ E ⊆ N) :
    (EuclideanSpace'.lebesgueMeasure d) E = (EuclideanSpace'.lebesgueMeasure d) B := by
  letI : MeasurableSpace (EuclideanSpace' d) := (LebesgueMeasurable.sigmaAlgebra d).measurableSpace
  have hBleb : LebesgueMeasurable B := (BorelSigmaAlgebra.le_LebesgueSigmaAlgebra d) B hB
  have hBEleb : LebesgueMeasurable (B \ E) := LebesgueMeasurable.inter hBleb (LebesgueMeasurable.complement hE)
  have hN0 : (EuclideanSpace'.lebesgueMeasure d) N = 0 := by
    have hNleb : LebesgueMeasurable N := IsNull.measurable hN
    rw [lebesgue_measure_on_measurable hNleb]
    change (Lebesgue_outer_measure N).toENNReal = 0
    unfold IsNull at hN
    rw [hN]
    simp
  have hBE0 : (EuclideanSpace'.lebesgueMeasure d) (B \ E) = 0 := by
    exact le_antisymm (by rw [← hN0]; exact measure_mono hBE) (zero_le _)
  have hunion : B = E ∪ (B \ E) := by
    ext x; constructor
    · intro hxB; by_cases hxE : x ∈ E; exact Or.inl hxE; exact Or.inr ⟨hxB, hxE⟩
    · intro hx; rcases hx with hx | hx; exact hEB hx; exact hx.1
  have hEq : (EuclideanSpace'.lebesgueMeasure d) B = (EuclideanSpace'.lebesgueMeasure d) E := by
    rw [hunion]
    rw [measure_union (μ := (EuclideanSpace'.lebesgueMeasure d)) (Set.disjoint_left.mpr (by
      intro x hxE hxB; exact hxB.2 hxE)) hBEleb]
    rw [hBE0]
    simp
  exact hEq.symm

/-- On Lebesgue-measurable sets the Borel and Lebesgue measures agree. -/
private lemma borel_eq_lebesgue_on_measurable {d : ℕ} {E : Set (EuclideanSpace' d)} (hE : LebesgueMeasurable E) :
    (EuclideanSpace'.borelMeasure d) E = (EuclideanSpace'.lebesgueMeasure d) E := by
  rcases lebesgue_measurable_eq_borel_sdiff_null hE with ⟨B, hB, N, hN, hEq⟩
  have hEB : E ⊆ B := by intro x hx; rw [hEq] at hx; exact hx.1
  have hBE : B \ E ⊆ N := by
    intro x hx
    by_contra hxN
    rw [hEq] at hx
    exact hx.2 ⟨hx.1, hxN⟩
  calc
    (EuclideanSpace'.borelMeasure d) E = (EuclideanSpace'.borelMeasure d) B := borel_measure_sdiff_eq hN hEB hBE
    _ = (Lebesgue_outer_measure B).toENNReal := borel_measure_on_borel hB
    _ = (EuclideanSpace'.lebesgueMeasure d) B := (lebesgue_measure_on_measurable ((BorelSigmaAlgebra.le_LebesgueSigmaAlgebra d) B hB)).symm
    _ = (EuclideanSpace'.lebesgueMeasure d) E := (lebesgue_measure_sdiff_eq hE hB hN hEB hBE).symm

/-- Exercise 1.4.27 -/
theorem EuclideanSpace'.borel_completion_eq_lebesgue {d:ℕ} :
  Measure.equiv (EuclideanSpace'.borelMeasure d).completion (EuclideanSpace'.lebesgueMeasure d) := by
  constructor
  · apply MeasurableSpace.ext
    intro s
    simpa using borelNullMeasurable_iff_lebesgue s
  · intro E hE
    have hLeb : LebesgueMeasurable E := (borelNullMeasurable_iff_lebesgue E).mp (by
      simpa using hE)
    rw [Measure.completion_apply]
    exact borel_eq_lebesgue_on_measurable hLeb

open MeasureTheory

private lemma symmDiff_compl {X : Type*} {s t : Set X} : symmDiff sᶜ tᶜ = symmDiff s t := by
  ext x
  by_cases hx : x ∈ s
  · by_cases ht : x ∈ t
    · simp
    · simp [Set.mem_symmDiff, hx, ht]
  · by_cases ht : x ∈ t
    · simp [Set.mem_symmDiff, hx, ht]
    · simp

private lemma iUnion_symmDiff_subset {X : Type*} {E F : ℕ → Set X} :
    symmDiff (⋃ n, E n) (⋃ n, F n) ⊆ ⋃ n, symmDiff (E n) (F n) := by
  intro x hx
  rw [Set.mem_symmDiff] at hx
  rw [Set.mem_iUnion]
  rcases hx with hx | hx
  · rcases Set.mem_iUnion.mp hx.1 with ⟨n, hxn⟩
    refine ⟨n, ?_⟩
    rw [Set.mem_symmDiff]
    refine Or.inl ⟨hxn, ?_⟩
    intro hxF
    exact hx.2 (Set.mem_iUnion.mpr ⟨n, hxF⟩)
  · rcases Set.mem_iUnion.mp hx.1 with ⟨n, hxn⟩
    refine ⟨n, ?_⟩
    rw [Set.mem_symmDiff]
    refine Or.inr ⟨hxn, ?_⟩
    intro hxE
    exact hx.2 (Set.mem_iUnion.mpr ⟨n, hxE⟩)

-- H_N = ⋃_{n < N} F n increases to G = ⋃ F n; measure of G \ H_N → 0
private lemma tail_union_measure {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {F : ℕ → Set X} (hFmeas : ∀ n, MeasurableSet (F n)) (hfin : μ Set.univ < ⊤)
    (ε : ENNReal) (hε : 0 < ε) :
    ∃ N, μ ((⋃ n, F n) \ ⋃ n ∈ Finset.range N, F n) < ε := by
  let H : ℕ → Set X := fun N => ⋃ n ∈ Finset.range N, F n
  have hHmono : Monotone H := by
    intro a b hab x hx
    dsimp [H] at hx
    simp [Set.mem_iUnion] at hx
    rcases hx with ⟨n, hn, hxn⟩
    dsimp [H]
    simp [Set.mem_iUnion]
    exact ⟨n, lt_of_lt_of_le hn hab, hxn⟩
  have hHunion : (⋃ N, H N) = ⋃ n, F n := by
    ext x
    constructor
    · intro hx
      rw [Set.mem_iUnion] at hx
      rcases hx with ⟨N, hN⟩
      rw [Set.mem_iUnion]
      dsimp [H] at hN
      simp [Set.mem_iUnion] at hN
      rcases hN with ⟨n, hn, hxn⟩
      exact ⟨n, hxn⟩
    · intro hx
      rw [Set.mem_iUnion] at hx
      rcases hx with ⟨n, hxn⟩
      rw [Set.mem_iUnion]
      refine ⟨n + 1, ?_⟩
      dsimp [H]
      simpa [Set.mem_iUnion, Finset.mem_range] using ⟨n, le_refl n, hxn⟩
  have hdiff_anti : Antitone (fun N : ℕ => (⋃ n, F n) \ H N) := by
    intro a b hab x hx
    rw [Set.mem_diff] at hx ⊢
    constructor
    · exact hx.1
    · intro hb
      exact hx.2 (hHmono hab hb)
  have hdiff_inter : (⋂ N, (⋃ n, F n) \ H N) = ∅ := by
    ext x
    constructor
    · intro hx
      rw [Set.mem_iInter] at hx
      have hxG : x ∈ ⋃ n, F n := (hx 0).1
      rw [Set.mem_iUnion] at hxG
      rcases hxG with ⟨n, hxn⟩
      have hxH : x ∈ H (n + 1) := by
        dsimp [H]
        simp [Set.mem_iUnion]
        exact ⟨n, le_refl n, hxn⟩
      exact (hx (n + 1)).2 hxH
    · intro hx
      exact False.elim hx
  have hnull : ∀ N, NullMeasurableSet ((⋃ n, F n) \ H N) μ := by
    intro N
    have hGmeas : MeasurableSet (⋃ n, F n) := MeasurableSet.iUnion hFmeas
    have hHmeas : MeasurableSet (H N) := by
      dsimp [H]
      exact MeasurableSet.biUnion (Finset.range N).finite_toSet.countable (by intro n hn; exact hFmeas n)
    exact (hGmeas.diff hHmeas).nullMeasurableSet
  have hdiff : Filter.Tendsto (fun N : ℕ => μ ((⋃ n, F n) \ H N)) Filter.atTop (nhds 0) := by
    have hfin0 : μ ((⋃ n, F n) \ H 0) ≠ ⊤ := by
      exact ne_top_of_le_ne_top (ne_of_lt hfin) (measure_mono (by
        intro x hx
        trivial))
    have ht := tendsto_measure_iInter_atTop hnull hdiff_anti ⟨0, hfin0⟩
    rw [hdiff_inter] at ht
    simpa using ht
  have hev : ∀ᶠ N in Filter.atTop, μ ((⋃ n, F n) \ H N) < ε := by
    exact hdiff.eventually (by
      apply Filter.eventually_iff_exists_mem.mpr
      refine ⟨Set.Iio ε, ?_, ?_⟩
      · exact mem_nhds_iff.mpr ⟨Set.Iio ε, by intro x hx; exact hx, isOpen_Iio, hε⟩
      · intro y hy
        exact hy)
  rcases Filter.eventually_atTop.mp hev with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  simpa [H] using hN N (le_refl N)

-- B-measurable sets are measurable in the generated sigma-algebra
private lemma generated_measurable_of_B {X : Type*} {B : ConcreteBooleanAlgebra X} {F : Set X}
    (hF : B.measurable F) :
    (ConcreteSigmaAlgebra.generated_by B.measurableSets).measurable F := by
  exact ConcreteSigmaAlgebra.generated_by_contains hF

-- finite union of B-measurable sets is B-measurable
private lemma finite_union_mem {X : Type*} {B : ConcreteBooleanAlgebra X} {F : ℕ → Set X}
    (hF : ∀ n, B.measurable (F n)) (N : ℕ) : B.measurable (⋃ n ∈ Finset.range N, F n) := by
  induction N with
  | zero =>
    dsimp
    simp
    exact B.empty_mem
  | succ N ih =>
    have h : (⋃ n ∈ Finset.range (N + 1), F n) = (⋃ n ∈ Finset.range N, F n) ∪ F N := by
      ext x
      simp [Set.mem_iUnion, Finset.mem_range]
      constructor
      · intro hx
        rcases hx with ⟨n, hn, hxn⟩
        by_cases hnN : n = N
        · right
          simpa [hnN] using hxn
        · left
          exact ⟨n, by omega, hxn⟩
      · intro hx
        rcases hx with hx | hx
        · rcases hx with ⟨n, hn, hxn⟩
          exact ⟨n, by omega, hxn⟩
        · exact ⟨N, by omega, hx⟩
    rw [h]
    exact B.union_mem _ _ ih (hF N)

-- geometric sum
private lemma geo_sum (ε : ℝ) (hε : 0 ≤ ε) :
    (∑' n : ℕ, ENNReal.ofReal (ε / (2 ^ (n + 3) : ℝ))) = ENNReal.ofReal (ε / 4) := by
  have hsum2 : (∑' n : ℕ, (2⁻¹ : ENNReal) ^ n) = 2 := ENNReal.tsum_geometric_two
  calc
    (∑' n : ℕ, ENNReal.ofReal (ε / (2 ^ (n + 3) : ℝ)))
        = ∑' n : ℕ, (ENNReal.ofReal (ε / 8) * (2⁻¹ : ENNReal) ^ n) := by
            apply tsum_congr
            intro n
            have hreal : ε / (2 ^ (n + 3) : ℝ) = (ε / 8) * ((1 / 2 : ℝ) ^ n) := by
              ring_nf
              field_simp
            rw [hreal]
            rw [ENNReal.ofReal_mul (by positivity : 0 ≤ ε / 8)]
            congr 1
            rw [ENNReal.ofReal_pow (by norm_num : 0 ≤ (1 / 2 : ℝ))]
            rw [ENNReal.ofReal_div_of_pos (by norm_num : 0 < (2 : ℝ))]
            rw [ENNReal.ofReal_ofNat]
            norm_num
    _ = ENNReal.ofReal (ε / 8) * (∑' n : ℕ, (2⁻¹ : ENNReal) ^ n) := by
            rw [ENNReal.tsum_mul_left]
    _ = ENNReal.ofReal (ε / 8) * 2 := by rw [hsum2]
    _ = ENNReal.ofReal (ε / 4) := by
            have htwo : (2 : ENNReal) = ENNReal.ofReal 2 := by norm_num
            rw [htwo]
            rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ ε / 8)]
            congr 1
            ring_nf

-- The approximable predicate
private def Approx {X : Type*} {B : ConcreteBooleanAlgebra X}
    (μ : @Measure X (ConcreteSigmaAlgebra.generated_by B.measurableSets).measurableSpace)
    (E : Set X) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ F : Set X, B.measurable F ∧ μ (symmDiff E F) < ENNReal.ofReal ε

private lemma approx_of_measurable {X : Type*} {B : ConcreteBooleanAlgebra X}
    (μ : @Measure X (ConcreteSigmaAlgebra.generated_by B.measurableSets).measurableSpace)
    {E : Set X} (hE : B.measurable E) : Approx μ E := by
  intro ε hε
  refine ⟨E, hE, ?_⟩
  have hs : symmDiff E E = ∅ := by
    ext x
    simp
  rw [hs]
  simpa using (ENNReal.ofReal_pos.mpr hε : (0 : ENNReal) < ENNReal.ofReal ε)

private lemma approx_compl {X : Type*} {B : ConcreteBooleanAlgebra X}
    (μ : @Measure X (ConcreteSigmaAlgebra.generated_by B.measurableSets).measurableSpace)
    {E : Set X} (hE : Approx μ E) : Approx μ Eᶜ := by
  intro ε hε
  rcases hE ε hε with ⟨F, hF, h⟩
  refine ⟨Fᶜ, B.compl_mem F hF, ?_⟩
  have hs : symmDiff Eᶜ Fᶜ = symmDiff E F := symmDiff_compl
  rwa [hs]

private lemma approx_iUnion {X : Type*} {B : ConcreteBooleanAlgebra X}
    (μ : @Measure X (ConcreteSigmaAlgebra.generated_by B.measurableSets).measurableSpace)
    (hfin : μ Set.univ < ⊤) {E : ℕ → Set X} (hE : ∀ n, Approx μ (E n)) : Approx μ (⋃ n, E n) := by
  letI : MeasurableSpace X := (ConcreteSigmaAlgebra.generated_by B.measurableSets).measurableSpace
  intro ε hε
  let δ : ℕ → ENNReal := fun n => ENNReal.ofReal (ε / (2 ^ (n + 3) : ℝ))
  have hchoose : ∀ n, ∃ F : Set X, B.measurable F ∧ μ (symmDiff (E n) F) < δ n := by
    intro n
    rcases hE n (ε / (2 ^ (n + 3) : ℝ)) (by positivity) with ⟨F, hF, hμ⟩
    refine ⟨F, hF, ?_⟩
    simpa [δ] using hμ
  let F : ℕ → Set X := fun n => (hchoose n).choose
  have hF_mem : ∀ n, B.measurable (F n) := fun n => (hchoose n).choose_spec.1
  have hF_err : ∀ n, μ (symmDiff (E n) (F n)) < δ n := fun n => (hchoose n).choose_spec.2
  have hδsum : (∑' n, δ n) = ENNReal.ofReal (ε / 4) := by
    dsimp [δ]
    exact geo_sum ε (le_of_lt hε)
  have hEF : μ (symmDiff (⋃ n, E n) (⋃ n, F n)) < ENNReal.ofReal (ε / 2) := by
    have hle : μ (symmDiff (⋃ n, E n) (⋃ n, F n)) ≤ ∑' n, μ (symmDiff (E n) (F n)) := by
      exact le_trans (measure_mono iUnion_symmDiff_subset) (measure_iUnion_le (fun n => symmDiff (E n) (F n)))
    have hlt : (∑' n, μ (symmDiff (E n) (F n))) < ENNReal.ofReal (ε / 2) := by
      have hle' : (∑' n, μ (symmDiff (E n) (F n))) ≤ ENNReal.ofReal (ε / 4) := by
        exact le_trans (ENNReal.tsum_le_tsum (fun n => le_of_lt (hF_err n))) (le_of_eq hδsum)
      have hlt' : ENNReal.ofReal (ε / 4) < ENNReal.ofReal (ε / 2) := by
        rw [ENNReal.ofReal_lt_ofReal_iff]
        linarith
        linarith
      exact lt_of_le_of_lt hle' hlt'
    exact lt_of_le_of_lt hle hlt
  have hFmeas : ∀ n, MeasurableSet (F n) := by
    intro n
    exact generated_measurable_of_B (hF_mem n)
  rcases tail_union_measure μ hFmeas hfin (ENNReal.ofReal (ε / 2)) (by
    rw [ENNReal.ofReal_pos]
    positivity) with ⟨N, htail⟩
  let F' : Set X := ⋃ n ∈ Finset.range N, F n
  have hF'_mem : B.measurable F' := by
    dsimp [F']
    exact finite_union_mem hF_mem N
  have hsub : symmDiff (⋃ n, E n) F' ⊆
      symmDiff (⋃ n, E n) (⋃ n, F n) ∪ ((⋃ n, F n) \ F') := by
    intro x hx
    rw [Set.mem_symmDiff] at hx
    rcases hx with hx | hx
    · rw [Set.mem_union]
      by_cases hxUF : x ∈ ⋃ n, F n
      · right
        rw [Set.mem_diff]
        exact ⟨hxUF, hx.2⟩
      · left
        rw [Set.mem_symmDiff]
        exact Or.inl ⟨hx.1, hxUF⟩
    · rw [Set.mem_union]
      left
      rw [Set.mem_symmDiff]
      right
      constructor
      · dsimp [F'] at hx
        have hx1 : x ∈ ⋃ n ∈ Finset.range N, F n := hx.1
        simp [Set.mem_iUnion] at hx1
        rcases hx1 with ⟨n, hn, hxn⟩
        rw [Set.mem_iUnion]
        exact ⟨n, hxn⟩
      · exact hx.2
  have hμ_sub : μ (symmDiff (⋃ n, E n) F') ≤
      μ (symmDiff (⋃ n, E n) (⋃ n, F n)) + μ ((⋃ n, F n) \ F') := by
    exact le_trans (measure_mono hsub) (measure_union_le _ _)
  have hsum_lt : μ (symmDiff (⋃ n, E n) (⋃ n, F n)) + μ ((⋃ n, F n) \ F') < ENNReal.ofReal ε := by
    have hsum : ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add]
      · congr 1
        ring
      · positivity
      · positivity
    have hlt : μ (symmDiff (⋃ n, E n) (⋃ n, F n)) + μ ((⋃ n, F n) \ F') <
        ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := by
      exact ENNReal.add_lt_add hEF (by
        dsimp [F'] at htail ⊢
        exact htail)
    rwa [hsum] at hlt
  refine ⟨F', hF'_mem, ?_⟩
  exact lt_of_le_of_lt hμ_sub hsum_lt

set_option linter.unusedVariables false in
theorem BooleanAlgebra.approx_finite {X:Type*} {B: ConcreteBooleanAlgebra X} (μ: @Measure X (ConcreteSigmaAlgebra.generated_by B.measurableSets).measurableSpace) (hfin: μ Set.univ < ⊤) : ∀ (ε : ℝ) (hε: ε>0) (E0 : Set X) (hE0: (ConcreteSigmaAlgebra.generated_by B.measurableSets).measurable E0),
  ∃ F : Set X, B.measurable F ∧ μ (symmDiff E0 F) < ENNReal.ofReal ε := by
  letI : MeasurableSpace X := (ConcreteSigmaAlgebra.generated_by B.measurableSets).measurableSpace
  have hAll : ∀ E : Set X, (ConcreteSigmaAlgebra.generated_by B.measurableSets).measurable E → Approx μ E := by
    have hunion : ∀ E F : Set X, Approx μ E → Approx μ F → Approx μ (E ∪ F) := by
      intro E F hE hF
      let E2 : ℕ → Set X := fun n => if n = 0 then E else F
      have hE2 : ∀ n, Approx μ (E2 n) := by
        intro n
        by_cases hn : n = 0
        · simpa [E2, hn] using hE
        · simpa [E2, hn] using hF
      have hseq : (⋃ n, E2 n) = E ∪ F := by
        ext x
        simp [E2, Set.mem_iUnion]
        constructor
        · intro hx
          rcases hx with ⟨n, hn⟩
          by_cases hn0 : n = 0
          · exact Or.inl (by simpa [hn0] using hn)
          · exact Or.inr (by simpa [hn0] using hn)
        · intro hx
          rcases hx with hx | hx
          · exact ⟨0, by simp [hx]⟩
          · exact ⟨1, by simp [hx]⟩
      rw [← hseq]
      exact approx_iUnion μ hfin hE2
    let C : ConcreteBooleanAlgebra X :=
      {
        measurable := fun E => Approx μ E
        empty_mem := by
          intro ε hε
          refine ⟨∅, B.empty_mem, ?_⟩
          simpa [Set.symmDiff_def] using (ENNReal.ofReal_pos.mpr hε : (0 : ENNReal) < ENNReal.ofReal ε)
        compl_mem := by
          intro E hE
          exact approx_compl μ hE
        union_mem := by
          intro E F hE hF
          exact hunion E F hE hF
      }
    have hSigma : C.isSigmaAlgebra := by
      intro E hE
      exact approx_iUnion μ hfin hE
    let Cσ : ConcreteSigmaAlgebra X := hSigma.toSigmaAlgebra
    have hle : ConcreteSigmaAlgebra.generated_by B.measurableSets ≤ Cσ := by
      apply ConcreteSigmaAlgebra.generated_by_le' Cσ
      intro E hE
      exact approx_of_measurable μ hE
    intro E hE
    exact hle E hE
  intro ε hε E0 hE0
  rcases hAll E0 hE0 ε hε with ⟨F, hF, hμ⟩
  exact ⟨F, hF, hμ⟩


set_option linter.unusedVariables false in
/-- Exercise 1.4.28(ii) (Approximation by an algebra) -/
theorem BooleanAlgebra.approx_sigma_finite {X:Type*} {B: ConcreteBooleanAlgebra X} (μ: @Measure X (ConcreteSigmaAlgebra.generated_by B.measurableSets).measurableSpace) (hσfin: ∃ A : ℕ → Set X, (∀ n, B.measurable (A n) ∧ μ (A n) < ⊤) ∧ ⋃ n, A n = ⊤) : ∀ (ε : ℝ) (hε: ε>0) (E : Set X) (hE: (ConcreteSigmaAlgebra.generated_by B.measurableSets).measurable E) (n : ℕ),
  ∃ F : Set X, B.measurable F ∧ F ⊆ (hσfin.choose n) ∧ μ (symmDiff (E ∩ (hσfin.choose n)) F) < ENNReal.ofReal ε := by
  intro ε hε E hE n
  letI : MeasurableSpace X := (ConcreteSigmaAlgebra.generated_by B.measurableSets).measurableSpace
  let A₀ : Set X := hσfin.choose n
  have hA₀mem : B.measurable A₀ := (hσfin.choose_spec.1 n).1
  have hA₀fin : μ A₀ < ⊤ := (hσfin.choose_spec.1 n).2
  have hAm : (ConcreteSigmaAlgebra.generated_by B.measurableSets).measurable A₀ :=
    ConcreteSigmaAlgebra.generated_by_contains hA₀mem
  have hEm : (ConcreteSigmaAlgebra.generated_by B.measurableSets).measurable (E ∩ A₀) :=
    @ConcreteBooleanAlgebra.inter_mem X (ConcreteSigmaAlgebra.generated_by B.measurableSets).toConcreteBooleanAlgebra
      E A₀ hE hAm
  have hfinRestrict : (μ.restrict A₀) Set.univ < ⊤ := by
    rw [Measure.restrict_apply]
    · simpa [Set.inter_comm] using hA₀fin
    · exact MeasurableSet.univ
  rcases BooleanAlgebra.approx_finite (μ.restrict A₀) hfinRestrict ε hε (E ∩ A₀) hEm with ⟨G, hG, hμG⟩
  let F : Set X := G ∩ A₀
  refine ⟨F, ?_, ?_, ?_⟩
  · exact B.inter_mem hG hA₀mem
  · intro x hx
    exact hx.2
  · have hs : symmDiff (E ∩ A₀) F ⊆ symmDiff (E ∩ A₀) G ∩ A₀ := by
      dsimp [F]
      intro x hx
      rw [Set.mem_symmDiff] at hx
      constructor
      · rw [Set.mem_symmDiff]
        rcases hx with hx | hx
        · left
          refine ⟨hx.1, ?_⟩
          intro hg
          exact hx.2 ⟨hg, hx.1.2⟩
        · right
          exact ⟨hx.1.1, hx.2⟩
      · rcases hx with hx | hx
        · exact hx.1.2
        · exact hx.1.2
    have hsG : (ConcreteSigmaAlgebra.generated_by B.measurableSets).measurable (symmDiff (E ∩ A₀) G) := by
      let S := ConcreteSigmaAlgebra.generated_by B.measurableSets
      have hGgen : S.measurable G := ConcreteSigmaAlgebra.generated_by_contains hG
      have hEAc : S.measurable (E ∩ A₀)ᶜ := S.compl_mem (E ∩ A₀) hEm
      have hGd : S.measurable (G \ (E ∩ A₀)) :=
        @ConcreteBooleanAlgebra.inter_mem X S.toConcreteBooleanAlgebra G (E ∩ A₀)ᶜ hGgen hEAc
      have hEd : S.measurable ((E ∩ A₀) \ G) :=
        @ConcreteBooleanAlgebra.inter_mem X S.toConcreteBooleanAlgebra (E ∩ A₀) Gᶜ hEm (S.compl_mem G hGgen)
      rw [Set.symmDiff_def]
      exact S.union_mem ((E ∩ A₀) \ G) (G \ (E ∩ A₀)) hEd hGd
    have htest : μ (symmDiff (E ∩ A₀) G ∩ A₀) < ENNReal.ofReal ε := by
      have hms : MeasurableSet (symmDiff (E ∩ A₀) G) := hsG
      rw [Measure.restrict_apply (ht := hms)] at hμG
      exact hμG
    have hle : μ (symmDiff (E ∩ A₀) F) ≤ μ (symmDiff (E ∩ A₀) G ∩ A₀) :=
      measure_mono hs
    exact lt_of_le_of_lt hle htest
