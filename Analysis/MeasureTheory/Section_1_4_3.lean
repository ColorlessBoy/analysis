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
/-- Exercise 1.4.21 -/
theorem FinitelyAdditiveMeasure.finite_atomic_eq {I X: Type*} [Fintype I] {atoms: I → Set X} (h_part: IsPartition atoms) (μ : FinitelyAdditiveMeasure h_part.to_ConcreteBooleanAlgebra) : ∃! c : I → ENNReal, ∀ E, h_part.to_ConcreteBooleanAlgebra.measurable E → μ.measure E = ∑ i ∈ Finset.univ.filter (fun i => atoms i ⊆ E), c i := by sorry

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

theorem Measure.downwards_mono_counter : ∃ (X:Type) (M: MeasurableSpace X) (μ: Measure X) (E : ℕ → Set X) (hE: ∀ n, Measurable (E n))
  (hmono : Antitone E), μ (⋂ n, E n) ≠ ⨅ n, μ.measureOf (E n) := by sorry

/-- Exercise 1.4.24 (i) (Dominated convergence for sets) -/
theorem Measure.measurable_of_lim {X:Type*} [MeasurableSpace X] (μ: Measure X) {E : ℕ → Set X} (hE: ∀ n, Measurable (E n))
  {E' : Set X} (hlim : PointwiseConvergesTo E E') : Measurable E' := by sorry

/-- Exercise 1.4.24 (ii) (Dominated convergence for sets) -/
theorem Measure.measure_of_lim {X:Type*} [MeasurableSpace X] (μ: Measure X) {E : ℕ → Set X} (hE: ∀ n, Measurable (E n))
  {E' F : Set X} (hlim : PointwiseConvergesTo E E') (hF : Measurable F) (hfin : μ F < ⊤) (hcon : ∀ n, E n ⊆ F) :
  Filter.atTop.Tendsto (fun n ↦ μ (E n)) (nhds (μ E')) := by sorry

/-- Exercise 1.4.24 (iii) (Dominated convergence for sets) -/
theorem Measure.measure_of_lim_counter : ∃ (X:Type) (M:MeasurableSpace X) (μ: Measure X) (E : ℕ → Set X) (hE: ∀ n, Measurable (E n))
  (E' F : Set X) (hlim : PointwiseConvergesTo E E') (hF : Measurable F) (hcon : ∀ n, E n ⊆ F),
  ¬ Filter.atTop.Tendsto (fun n ↦ μ (E n)) (nhds (μ E')) := by sorry

/-- Exercise 1.4.25 -/
theorem Measure.on_countable {X:Type*} [Countable X] [M: MeasurableSpace X] (hM: M = ⊤) (μ: Measure X) :
  ∃! c : X → ENNReal, ∀ E : Set X, μ E = ∑' x : E, c x := by sorry

-- Definition 1.4.31
#check Measure.IsComplete

#check NullMeasurableSpace

#check Measure.completion

/-- Exercise 1.4.26 (Completion) -/
theorem Measure.completion_lt {X:Type*} [M : MeasurableSpace X] (μ: Measure X) (M' : MeasurableSpace X) (μ' : @Measure X M')
  (hcomplete : μ'.IsComplete) (hMM' : M ≤ M') (hμ : ∀ E, M.MeasurableSet' E → μ E = μ' E) : ∀ E : Set X, @NullMeasurableSet X M E μ → (M'.MeasurableSet' E ∧ μ' E = μ.completion E)
   := by sorry

noncomputable def EuclideanSpace'.lebesgueMeasure (d:ℕ) := (FinitelyAdditiveMeasure.lebesgue_isCountablyAdditive d).toMeasure

noncomputable def EuclideanSpace'.borelMeasure (d:ℕ) := ((FinitelyAdditiveMeasure.lebesgue_isCountablyAdditive d).toCountablyAdditive.restrict_alg (BorelSigmaAlgebra.le_LebesgueSigmaAlgebra d)).toMeasure

def Measure.equiv {X:Type*} {M M' : MeasurableSpace X} (μ: @Measure X M) (μ': @Measure X M') : Prop := M = M' ∧ ∀ E, M.MeasurableSet' E → μ E = μ' E

/-- Exercise 1.4.27 -/
theorem EuclideanSpace'.borel_completion_eq_lebesgue {d:ℕ} :
  Measure.equiv (EuclideanSpace'.borelMeasure d).completion (EuclideanSpace'.lebesgueMeasure d) := by sorry

/-- Exercise 1.4.28(i) (Approximation by an algebra) -/
theorem BooleanAlgebra.approx_finite {X:Type*} {B: ConcreteBooleanAlgebra X} (μ: @Measure X (ConcreteSigmaAlgebra.generated_by B.measurableSets).measurableSpace) (hfin: μ Set.univ < ⊤) : ∀ (ε : ℝ) (hε: ε>0) (E : Set X) (hE: (ConcreteSigmaAlgebra.generated_by B.measurableSets).measurable E),
  ∃ F : Set X, B.measurable F ∧ μ (symmDiff E F) < ENNReal.ofReal ε := by sorry

/-- Exercise 1.4.28(ii) (Approximation by an algebra) -/
theorem BooleanAlgebra.approx_sigma_finite {X:Type*} {B: ConcreteBooleanAlgebra X} (μ: @Measure X (ConcreteSigmaAlgebra.generated_by B.measurableSets).measurableSpace) (hσfin: ∃ A : ℕ → Set X, (∀ n, B.measurable (A n) ∧ μ (A n) < ⊤) ∧ ⋃ n, A n = ⊤) : ∀ (ε : ℝ) (hε: ε>0) (E : Set X) (hE: (ConcreteSigmaAlgebra.generated_by B.measurableSets).measurable E),
  ∃ F : Set X, B.measurable F ∧ μ (symmDiff E F) < ENNReal.ofReal ε := by sorry
