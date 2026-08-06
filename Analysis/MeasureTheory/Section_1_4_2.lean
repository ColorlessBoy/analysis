import Mathlib.SetTheory.Cardinal.Aleph
import Analysis.MeasureTheory.Section_1_4_1
/-!
# Introduction to Measure Theory, Section 1.4.2: $\sigma$-algebras and measurable spaces

A companion to (the introduction to) Section 1.4.2 of the book "An introduction to Measure Theory".

-/

/-- Definition 1.4.12 (Sigma algebra) -/
class ConcreteSigmaAlgebra (X:Type*) extends ConcreteBooleanAlgebra X where
  countable_union_mem : ∀ E : ℕ → Set X, (∀ n, measurable (E n)) → measurable (⋃ n, E n)

@[ext]
theorem ConcreteSigmaAlgebra.ext {X:Type*} {B1 B2 : ConcreteSigmaAlgebra X}
    (h : ∀ E, B1.measurable E ↔ B2.measurable E) : B1 = B2 := by
  cases B1
  cases B2
  congr
  apply ConcreteBooleanAlgebra.ext
  exact h

@[implicit_reducible]
def ConcreteSigmaAlgebra.toMeasurableSpace {X: Type*} (B: ConcreteSigmaAlgebra X) : MeasurableSpace X :=
  {
    MeasurableSet' := B.measurable
    measurableSet_empty := B.empty_mem
    measurableSet_compl := B.compl_mem
    measurableSet_iUnion := B.countable_union_mem
  }

@[implicit_reducible]
def MeasurableSpace.toConcreteSigmaAlgebra {X: Type*} (M: MeasurableSpace X) : ConcreteSigmaAlgebra X :=
  {
    measurable := M.MeasurableSet'
    empty_mem := M.measurableSet_empty
    compl_mem := M.measurableSet_compl
    union_mem := by
      intro E F hE hF
      let T : ℕ → Set X := fun n => if n = 0 then E else F
      have hT : ∀ n, M.MeasurableSet' (T n) := by
        intro n
        by_cases hn : n = 0
        · simpa [T, hn] using hE
        · simpa [T, hn] using hF
      have hUnion : (⋃ n, T n) = E ∪ F := by
        ext x
        constructor
        · intro hx
          rw [Set.mem_iUnion] at hx
          rcases hx with ⟨n, hn⟩
          by_cases hn0 : n = 0
          · exact Or.inl (by simpa [T, hn0] using hn)
          · exact Or.inr (by simpa [T, hn0] using hn)
        · intro hx
          rcases hx with hx | hx
          · rw [Set.mem_iUnion]
            exact ⟨0, by simp [T, hx]⟩
          · rw [Set.mem_iUnion]
            exact ⟨1, by simp [T, hx]⟩
      rw [← hUnion]
      exact M.measurableSet_iUnion T hT
    countable_union_mem := M.measurableSet_iUnion
  }

def ConcreteBooleanAlgebra.isSigmaAlgebra {X: Type*} (B: ConcreteBooleanAlgebra X) : Prop := ∀ E : ℕ → Set X, (∀ n, measurable (E n)) → measurable (⋃ n, E n)

theorem ConcreteSigmaAlgebra.isSigmaAlgebra {X: Type*} (B: ConcreteSigmaAlgebra X) : B.isSigmaAlgebra := by
  intro E hE
  exact B.countable_union_mem E hE

@[implicit_reducible]
def ConcreteBooleanAlgebra.isSigmaAlgebra.toSigmaAlgebra {X: Type*} {B: ConcreteBooleanAlgebra X} (h: B.isSigmaAlgebra) : ConcreteSigmaAlgebra X :=
  { countable_union_mem := h }

/-- Exercise 1.4.10 -/
def ConcreteBooleanAlgebra.isAtomic.isSigmaAlgebra {X: Type*} {B: ConcreteBooleanAlgebra X} (h: B.isAtomic) : B.isSigmaAlgebra := by
  rcases h with ⟨I, parts, hI, hB⟩
  intro E hE
  rw [hB] at hE ⊢
  have hE_parts : ∀ n, ∃ J : Set I, E n = ⋃ i ∈ J, parts i := hE
  let J : Set I := {i | ∃ n, i ∈ (hE_parts n).choose}
  refine ⟨J, ?_⟩
  ext x
  constructor
  · intro hx
    rw [Set.mem_iUnion] at hx
    rcases hx with ⟨n, hn⟩
    rw [(hE_parts n).choose_spec] at hn
    simp at hn
    rcases hn with ⟨i, hi, hxi⟩
    simp
    refine ⟨i, ?_, hxi⟩
    exact ⟨n, hi⟩
  · intro hx
    simp at hx
    rcases hx with ⟨i, hiJ, hxi⟩
    rcases hiJ with ⟨n, hin⟩
    rw [Set.mem_iUnion]
    refine ⟨n, ?_⟩
    rw [(hE_parts n).choose_spec]
    simp
    exact ⟨i, hin, hxi⟩

/-- A countable union of null sets is null. -/
lemma IsNull.countable_union' {d:ℕ} {E: ℕ → Set (EuclideanSpace' d)} (hE: ∀ n, IsNull (E n)) : IsNull (⋃ n, E n) := by
  unfold IsNull
  have hsub : Lebesgue_outer_measure (⋃ n, E n) ≤ ∑' n, Lebesgue_outer_measure (E n) :=
    Lebesgue_outer_measure.union_le E
  have hsum : (∑' n, Lebesgue_outer_measure (E n)) = 0 := by
    simp [hE]
  rw [hsum] at hsub
  exact le_antisymm hsub (Lebesgue_outer_measure.nonneg (⋃ n, E n))

/-- Exercise 1.4.11 -/
theorem LebesgueMeasurable.boolean_algebra.isSigmaAlgebra (d:ℕ) : (LebesgueMeasurable.boolean_algebra d).isSigmaAlgebra := by
  intro E hE
  change LebesgueMeasurable (⋃ n, E n)
  exact LebesgueMeasurable.countable_union (fun n => hE n)

@[implicit_reducible]
def LebesgueMeasurable.sigmaAlgebra (d:ℕ) : ConcreteSigmaAlgebra (EuclideanSpace' d) :=
  (LebesgueMeasurable.boolean_algebra.isSigmaAlgebra d).toSigmaAlgebra

theorem IsNull.boolean_algebra.isSigmaAlgebra (d:ℕ) : (IsNull.boolean_algebra d).isSigmaAlgebra := by
  intro E hE
  by_cases hSome : ∃ n, IsNull (E n)ᶜ
  · rcases hSome with ⟨n₀, hn₀⟩
    right
    have hsub : (⋃ n, E n)ᶜ ⊆ (E n₀)ᶜ := by
      intro x hx
      rw [Set.mem_compl_iff] at hx ⊢
      intro hxEn₀
      exact hx (by rw [Set.mem_iUnion]; exact ⟨n₀, hxEn₀⟩)
    exact IsNull.subset hn₀ hsub
  · left
    have hAllNull : ∀ n, IsNull (E n) := by
      intro n
      rcases hE n with hnull | hco
      · exact hnull
      · exact False.elim (hSome ⟨n, hco⟩)
    exact IsNull.countable_union' hAllNull

@[implicit_reducible]
def IsNull.sigmaAlgebra (d:ℕ) : ConcreteSigmaAlgebra (EuclideanSpace' d) :=
  (IsNull.boolean_algebra.isSigmaAlgebra d).toSigmaAlgebra

private lemma abs_self_le (a : ℝ) : -|a| ≤ a := by
  exact (abs_le.mp (le_refl |a|)).1

/-- A box whose first side is {lit}`[0, n]` and whose other sides are {lit}`[-n, n]`. -/
private def halfspaceBox (d : ℕ) (hd : 0 < d) (n : ℕ) : Box d :=
  ⟨fun j => if j = ⟨0, hd⟩ then BoundedInterval.Icc (0 : ℝ) (n : ℝ) else BoundedInterval.Icc (-(n : ℝ)) (n : ℝ)⟩

private lemma coord_norm_le {d : ℕ} (x : EuclideanSpace' d) (j : Fin d) : |x j| ≤ ‖x‖ := by
  rw [PiLp.norm_eq_of_L2]
  have hnonneg : 0 ≤ (∑ i : Fin d, ‖x i‖ ^ 2) := by
    positivity
  rw [Real.le_sqrt (by positivity) hnonneg]
  rw [sq_abs]
  rw [← sq_abs (x j)]
  exact Finset.single_le_sum (s := Finset.univ) (f := fun i => ‖x i‖ ^ 2) (by intro i hi; positivity) (Finset.mem_univ j)

private lemma norm_lt_ceil_toNat_add_one (a : ℝ) (ha : 0 ≤ a) : a < (⌈a⌉.toNat + 1 : ℕ) := by
  have hceil_nonneg : 0 ≤ ⌈a⌉ := Int.ceil_nonneg ha
  have hto : (⌈a⌉.toNat : ℝ) = ⌈a⌉ := by
    exact_mod_cast (Int.toNat_of_nonneg hceil_nonneg)
  have hle : a ≤ ⌈a⌉ := Int.le_ceil a
  change a < ((⌈a⌉.toNat + 1 : ℕ) : ℝ)
  rw [Nat.cast_add, Nat.cast_one, hto]
  linarith

/-- The halfspace {lit}`0 ≤ x 0` is a countable union of boxes. -/
private lemma halfspace_eq_union_boxes {d : ℕ} (hd : 0 < d) :
    {x : EuclideanSpace' d | 0 ≤ x ⟨0, hd⟩} = ⋃ n : ℕ, (halfspaceBox d hd n).toSet := by
  ext x
  constructor
  · intro hx
    let N : ℕ := ⌈‖x‖⌉.toNat + 1
    rw [Set.mem_iUnion]
    refine ⟨N, ?_⟩
    rw [Box.mem_toSet]
    intro j
    by_cases hj : j = ⟨0, hd⟩
    · subst hj
      simp [halfspaceBox]
      constructor
      · exact hx
      · have hle : x ⟨0, hd⟩ ≤ |x ⟨0, hd⟩| := le_abs_self (x ⟨0, hd⟩)
        have hb : |x ⟨0, hd⟩| ≤ ‖x‖ := coord_norm_le x ⟨0, hd⟩
        have hn : ‖x‖ < (N : ℝ) := by
          dsimp [N]
          exact norm_lt_ceil_toNat_add_one ‖x‖ (norm_nonneg x)
        exact le_trans (le_trans hle hb) (le_of_lt hn)
    · simp [halfspaceBox, hj]
      constructor
      · have hle : |x j| ≤ ‖x‖ := coord_norm_le x j
        have hn : ‖x‖ < (N : ℝ) := by
          dsimp [N]
          exact norm_lt_ceil_toNat_add_one ‖x‖ (norm_nonneg x)
        have hb : -(N : ℝ) ≤ x j := by
          exact le_trans (by linarith [abs_self_le (x j), hle, hn]) (le_refl (x j))
        exact hb
      · have hle : |x j| ≤ ‖x‖ := coord_norm_le x j
        have hn : ‖x‖ < (N : ℝ) := by
          dsimp [N]
          exact norm_lt_ceil_toNat_add_one ‖x‖ (norm_nonneg x)
        exact le_trans (le_trans (le_abs_self (x j)) hle) (le_of_lt hn)
  · intro hx
    rw [Set.mem_iUnion] at hx
    rcases hx with ⟨n, hn⟩
    have hx0 : x ⟨0, hd⟩ ∈ Set.Icc (0 : ℝ) (n : ℝ) := by
      have := hn ⟨0, hd⟩
      simpa [halfspaceBox] using this
    exact hx0.1

theorem JordanMeasurable.boolean_algebra.not_isSigmaAlgebra (d:ℕ) (hd: d ≥ 1) :
    ¬ (JordanMeasurable.boolean_algebra d).isSigmaAlgebra := by
  intro h
  have hd0 : 0 < d := by omega
  let H : Set (EuclideanSpace' d) := {x | 0 ≤ x ⟨0, hd0⟩}
  have hH_eq : H = ⋃ n : ℕ, (halfspaceBox d hd0 n).toSet := halfspace_eq_union_boxes hd0
  have hHmeas : (JordanMeasurable.boolean_algebra d).measurable H := by
    rw [hH_eq]
    apply h (fun n => (halfspaceBox d hd0 n).toSet)
    intro n
    exact Or.inl (IsElementary.jordanMeasurable (IsElementary.box (halfspaceBox d hd0 n)))
  rcases hHmeas with hHj | hHjc
  · exact (NotAtomic.halfspace_unbounded hd0) hHj.1
  · exact (NotAtomic.halfspace_compl_unbounded hd0) hHjc.1

/-- Exercise 1.4.12 -/
theorem ConcreteSigmaAlgebra.restrict_is_sigma {X:Type*} (B: ConcreteSigmaAlgebra X) (A:Set X):
    (ConcreteBooleanAlgebra.restrict B.toConcreteBooleanAlgebra A).isSigmaAlgebra := by
  intro E hE
  have hE' : ∀ n, ∃ E' : Set X, B.measurable E' ∧ E n = Subtype.val ⁻¹' E' := by
    intro n
    exact hE n
  let E' : ℕ → Set X := fun n => (hE' n).choose
  have hE'meas : ∀ n, B.measurable (E' n) := fun n => (hE' n).choose_spec.1
  have hEn : ∀ n, E n = Subtype.val ⁻¹' E' n := fun n => (hE' n).choose_spec.2
  have hUnion : (⋃ n, E n) = Subtype.val ⁻¹' (⋃ n, E' n) := by
    ext x
    constructor
    · intro hx
      rw [Set.mem_iUnion] at hx
      rcases hx with ⟨n, hn⟩
      rw [hEn n] at hn
      rw [Set.mem_preimage]
      rw [Set.mem_iUnion]
      exact ⟨n, hn⟩
    · intro hx
      rw [Set.mem_preimage, Set.mem_iUnion] at hx
      rcases hx with ⟨n, hn⟩
      rw [Set.mem_iUnion]
      refine ⟨n, ?_⟩
      rw [hEn n]
      exact hn
  refine ⟨⋃ n, E' n, B.countable_union_mem E' hE'meas, hUnion⟩

@[implicit_reducible]
def ConcreteSigmaAlgebra.restrict {X:Type*} (B: ConcreteSigmaAlgebra X) (A:Set X) : ConcreteSigmaAlgebra A := (B.restrict_is_sigma A).toSigmaAlgebra

instance ConcreteSigmaAlgebra.instLE (X:Type*) : LE (ConcreteSigmaAlgebra X) :=
  ⟨fun B1 B2 => ∀ E, B1.measurable E → B2.measurable E⟩

instance ConcreteSigmaAlgebra.instPartialOrder (X:Type*) : PartialOrder (ConcreteSigmaAlgebra X) :=
  {
    le_refl := fun B E hE => hE
    le_trans := fun B1 B2 B3 h12 h23 E hE => h23 E (h12 E hE)
    le_antisymm := by
      intro B1 B2 h12 h21
      apply ConcreteSigmaAlgebra.ext
      intro E
      exact ⟨h12 E, h21 E⟩
  }

instance ConcreteSigmaAlgebra.instOrderTop {X:Type*} : OrderTop (ConcreteSigmaAlgebra X) :=
  {
    top := {
      measurable := fun _ => True
      empty_mem := trivial
      compl_mem := fun _ _ => trivial
      union_mem := fun _ _ _ _ => trivial
      countable_union_mem := fun _ _ => trivial
    }
    le_top := fun _ _ _ => trivial
  }

instance ConcreteSigmaAlgebra.instOrderBot {X:Type*} : OrderBot (ConcreteSigmaAlgebra X) :=
  {
    bot := {
      measurable := fun E => E = ∅ ∨ E = Set.univ
      empty_mem := by grind
      compl_mem := fun E hE => by grind
      union_mem := fun E F hE hF => by grind
      countable_union_mem := by
        intro E hE
        by_cases hSome : ∃ n, E n = Set.univ
        · rcases hSome with ⟨n, hn⟩
          right
          ext x
          constructor
          · intro _
            trivial
          · intro _
            rw [Set.mem_iUnion]
            exact ⟨n, by simp [hn]⟩
        · left
          have hAllEmpty : ∀ n, E n = ∅ := by
            intro n
            rcases hE n with hn_eq | hn_eq
            · exact hn_eq
            · exact False.elim (hSome ⟨n, hn_eq⟩)
          simp [hAllEmpty]
    }
    bot_le := by
      intro B E hE
      rcases hE with hE | hE
      · rw [hE]
        exact B.empty_mem
      · rw [hE]
        simpa using B.compl_mem ∅ B.empty_mem
  }

/-- Exercise 1.4.13 (Intersection of sigma-algebras) -/
instance ConcreteSigmaAlgebra.instInfSet {X:Type*} : InfSet (ConcreteSigmaAlgebra X) :=
  {
      sInf S :=
        {
          measurable := fun E => ∀ B ∈ S, B.measurable E
          empty_mem := by
            intro B hB
            exact B.empty_mem
          compl_mem := by
            intro E hE B hB
            exact B.compl_mem E (hE B hB)
          union_mem := by
            intro E F hE hF B hB
            exact B.union_mem E F (hE B hB) (hF B hB)
          countable_union_mem := by
            intro E hE B hB
            exact B.countable_union_mem E (fun n => hE n B hB)
        }
  }

@[implicit_reducible]
def ConcreteSigmaAlgebra.generated_by {X:Type*} (F: Set (Set X)) : ConcreteSigmaAlgebra X :=
  sInf { B | ∀ E ∈ F, B.measurable E }

lemma ConcreteSigmaAlgebra.generated_by_contains {X:Type*} {F : Set (Set X)} {E : Set X}
    (hE : E ∈ F) : (ConcreteSigmaAlgebra.generated_by F).measurable E := by
  intro B hB
  exact hB E hE

lemma ConcreteSigmaAlgebra.generated_by_le' {X:Type*} {F : Set (Set X)} (B : ConcreteSigmaAlgebra X)
    (hB : ∀ E ∈ F, B.measurable E) : ConcreteSigmaAlgebra.generated_by F ≤ B := by
  intro E hE
  exact hE B hB

/-- The difference of two measurable sets is measurable. -/
theorem ConcreteSigmaAlgebra.sdiff_mem {X : Type*} (B : ConcreteSigmaAlgebra X) {E F : Set X}
    (hE : B.measurable E) (hF : B.measurable F) : B.measurable (E \ F) := by
  have hU : B.measurable (Eᶜ ∪ F) := B.union_mem _ _ (B.compl_mem E hE) hF
  simpa [Set.diff_eq] using B.compl_mem (Eᶜ ∪ F) hU

/-- Definition 1.4.14 (Generation of σ-algebras) -/
instance ConcreteSigmaAlgebra.instSupSet {X:Type*} : SupSet (ConcreteSigmaAlgebra X) :=
  {
      sSup S := ConcreteSigmaAlgebra.generated_by (⋃ B ∈ S, B.measurableSets)
  }

instance ConcreteSigmaAlgebra.instCompleteLattice {X:Type*} : CompleteLattice (ConcreteSigmaAlgebra X) :=
  {
    sup := fun B1 B2 => sSup ({B1, B2} : Set (ConcreteSigmaAlgebra X))
    le_sup_left := by
      intro B1 B2 E hE
      apply ConcreteSigmaAlgebra.generated_by_contains
      simp
      exact Or.inl hE
    le_sup_right := by
      intro B1 B2 E hE
      apply ConcreteSigmaAlgebra.generated_by_contains
      simp
      exact Or.inr hE
    sup_le := by
      intro B1 B2 C h1 h2
      change ConcreteSigmaAlgebra.generated_by
        (⋃ B ∈ ({B1, B2} : Set (ConcreteSigmaAlgebra X)), B.measurableSets) ≤ C
      apply ConcreteSigmaAlgebra.generated_by_le' C
      intro E hE
      simp at hE
      rcases hE with hE | hE
      · exact h1 E hE
      · exact h2 E hE
    inf := fun B1 B2 => sInf ({B1, B2} : Set (ConcreteSigmaAlgebra X))
    inf_le_left := by
      intro B1 B2 E hE
      exact hE B1 (by simp)
    inf_le_right := by
      intro B1 B2 E hE
      exact hE B2 (by simp)
    le_inf := by
      intro C B1 B2 h1 h2 E hE B hB
      rcases hB with hB | hB
      · subst hB
        exact h1 E hE
      · subst hB
        exact h2 E hE
    le_top := by
      intro B E hE
      trivial
    bot_le := by
      intro B E hE
      rcases hE with hE | hE
      · rw [hE]
        exact B.empty_mem
      · rw [hE]
        simpa using B.compl_mem ∅ B.empty_mem
    isLUB_sSup := by
      intro S
      constructor
      · intro B hB E hE
        apply ConcreteSigmaAlgebra.generated_by_contains
        simp
        exact ⟨B, hB, hE⟩
      · intro C hC
        apply ConcreteSigmaAlgebra.generated_by_le' C
        intro E hE
        simp at hE
        rcases hE with ⟨B, hB, hE'⟩
        exact hC hB E hE'
    isGLB_sInf := by
      intro S
      constructor
      · intro B hB E hE
        exact hE B hB
      · intro C hC E hE B hB
        exact hC hB E hE
  }

theorem ConcreteSigmaAlgebra.generated_by_le {X:Type*} (F: Set (Set X)) : ConcreteBooleanAlgebra.generated_by F ≤ (ConcreteSigmaAlgebra.generated_by F).toConcreteBooleanAlgebra := by
  intro E hE
  exact hE (ConcreteSigmaAlgebra.generated_by F).toConcreteBooleanAlgebra (fun E' hE' => ConcreteSigmaAlgebra.generated_by_contains hE')

/-- The algebra of finite or cofinite subsets of ℕ. -/
@[implicit_reducible]
def finOrCofin : ConcreteBooleanAlgebra ℕ := {
  measurable := fun E => E.Finite ∨ Eᶜ.Finite
  empty_mem := Or.inl (by simp)
  compl_mem := by
    intro E hE
    rcases hE with hE | hEc
    · right
      simpa using hE
    · left
      simpa using hEc
  union_mem := by
    intro E F hE hF
    rcases hE with hE | hEc
    · rcases hF with hF | hFc
      · exact Or.inl (hE.union hF)
      · right
        rw [Set.compl_union]
        exact hFc.subset Set.inter_subset_right
    · right
      rw [Set.compl_union]
      exact hEc.subset Set.inter_subset_left
}

private lemma evens_not_finite : ¬ (Set.range (fun n : ℕ => 2 * n)).Finite := by
  intro hf
  have hinf : (Set.range (fun n : ℕ => 2 * n)).Infinite := by
    exact Set.infinite_range_of_injective (f := fun n : ℕ => 2 * n) (by intro a b h; dsimp at h; omega)
  exact Set.Infinite.not_finite hinf hf

private lemma odds_not_finite : ¬ (Set.range (fun n : ℕ => 2 * n + 1)).Finite := by
  intro hf
  have hinf : (Set.range (fun n : ℕ => 2 * n + 1)).Infinite := by
    exact Set.infinite_range_of_injective (f := fun n : ℕ => 2 * n + 1) (by intro a b h; dsimp at h; omega)
  exact Set.Infinite.not_finite hinf hf

private lemma odds_subset_compl_evens : Set.range (fun n : ℕ => 2 * n + 1) ⊆ (Set.range (fun n : ℕ => 2 * n))ᶜ := by
  intro x hx
  rw [Set.mem_compl_iff, Set.mem_range]
  rcases hx with ⟨k, hk⟩
  rw [← hk]
  rintro ⟨m, hm⟩
  have h' : (2 : ℤ) * (m : ℤ) = (2 : ℤ) * (k : ℤ) + 1 := by exact_mod_cast hm
  omega

private lemma evens_compl_not_finite : ¬ (Set.range (fun n : ℕ => 2 * n))ᶜ.Finite := by
  intro hfin
  have hsubfin : (Set.range (fun n : ℕ => 2 * n + 1)).Finite := hfin.subset odds_subset_compl_evens
  exact odds_not_finite hsubfin

private lemma evens_not_finOrCofin : ¬ finOrCofin.measurable (Set.range (fun n : ℕ => 2 * n)) := by
  intro h
  rcases h with hFin | hCofin
  · exact evens_not_finite hFin
  · exact evens_compl_not_finite hCofin

example : ∃ (X : Type) (F: Set (Set X)), ConcreteBooleanAlgebra.generated_by F ≠ (ConcreteSigmaAlgebra.generated_by F).toConcreteBooleanAlgebra := by
  -- X = ℕ, F = { {2n} : n ∈ ℕ } (the singletons of even numbers).
  -- In the Boolean algebra generated by F, measurable sets are finite unions of {2n} or their complements.
  -- In the σ-algebra, the set of all even numbers E = ⋃ n {2n} is a countable union of generators, hence measurable.
  -- But E is infinite and Eᶜ (odd numbers) is infinite, so E is not a finite union of singletons nor a complement of one.
  let F : Set (Set ℕ) := Set.range (fun n : ℕ => ({2 * n} : Set ℕ))
  refine ⟨ℕ, F, ?_⟩
  let E : Set ℕ := Set.range (fun n : ℕ => 2 * n)
  have hE_sigma : (ConcreteSigmaAlgebra.generated_by F).measurable E := by
    have hE_eq : E = ⋃ n, ({2 * n} : Set ℕ) := by
      ext x
      simp [E]
    rw [hE_eq]
    apply (ConcreteSigmaAlgebra.generated_by F).countable_union_mem
    intro n
    apply ConcreteSigmaAlgebra.generated_by_contains
    dsimp [F]
    exact Set.mem_range.mpr ⟨n, rfl⟩
  have hF_sub : ∀ E' ∈ F, finOrCofin.measurable E' := by
    intro E' hE'
    dsimp [F] at hE'
    rcases hE' with ⟨n, rfl⟩
    exact Or.inl (by simp)
  have hgen_le : ConcreteBooleanAlgebra.generated_by F ≤ finOrCofin := by
    apply ConcreteBooleanAlgebra.generated_by_le finOrCofin
    exact hF_sub
  have hE_not_ba : ¬ (ConcreteBooleanAlgebra.generated_by F).measurable E := by
    intro hmeas
    exact evens_not_finOrCofin (hgen_le E hmeas)
  intro hEq
  have hme : (ConcreteBooleanAlgebra.generated_by F).measurable E := by
    rw [hEq]
    exact hE_sigma
  exact hE_not_ba hme

/-- Remark 1.4.15 -/
theorem ConcreteSigmaAlgebra.induction {X:Type*} {F: Set (Set X)} {P: Set X → Prop}
  (h1: P ∅) (h2: ∀ E ∈ F, P E) (h3: ∀ E, P E → P Eᶜ)
  (h4: ∀ (E : ℕ → Set X), (∀ n, P (E n)) → P (⋃ n, E n)) : ∀ E, (ConcreteSigmaAlgebra.generated_by F).measurable E → P E := by
  let U : ConcreteSigmaAlgebra X := {
    measurable := fun E => P E
    empty_mem := h1
    compl_mem := fun E hE => h3 E hE
    union_mem := by
      intro E F' hE hF'
      let T : ℕ → Set X := fun n => if n = 0 then E else F'
      have hT : ∀ n, P (T n) := by
        intro n
        by_cases hn : n = 0
        · simpa [T, hn] using hE
        · simpa [T, hn] using hF'
      have hUnion : (⋃ n, T n) = E ∪ F' := by
        ext x
        constructor
        · intro hx
          rw [Set.mem_iUnion] at hx
          rcases hx with ⟨n, hn⟩
          by_cases hn0 : n = 0
          · exact Or.inl (by simpa [T, hn0] using hn)
          · exact Or.inr (by simpa [T, hn0] using hn)
        · intro hx
          rcases hx with hx | hx
          · rw [Set.mem_iUnion]
            exact ⟨0, by simp [T, hx]⟩
          · rw [Set.mem_iUnion]
            exact ⟨1, by simp [T, hx]⟩
      rw [← hUnion]
      exact h4 T hT
    countable_union_mem := h4
  }
  intro E hE
  have hgen_le : ConcreteSigmaAlgebra.generated_by F ≤ U := by
    apply ConcreteSigmaAlgebra.generated_by_le' U
    exact h2
  exact hgen_le E hE

/-- Definition 1.4.16 (Borel σ-algebra) -/
@[implicit_reducible]
def BorelSigmaAlgebra (X:Type*) [TopologicalSpace X] : ConcreteSigmaAlgebra X :=
  ConcreteSigmaAlgebra.generated_by { U : Set X | IsOpen U }

/-- Exercise 1.4.14 (i) -/
theorem BorelSigmaAlgebra.generated_by_open (d:ℕ) : BorelSigmaAlgebra (EuclideanSpace' d) = ConcreteSigmaAlgebra.generated_by { U : Set (EuclideanSpace' d) | IsOpen U } := rfl

/-- Exercise 1.4.14 (ii) -/
theorem BorelSigmaAlgebra.generated_by_closed (d:ℕ) : BorelSigmaAlgebra (EuclideanSpace' d) = ConcreteSigmaAlgebra.generated_by { F : Set (EuclideanSpace' d) | IsClosed F } := by
  unfold BorelSigmaAlgebra
  -- {F | IsClosed F} = {E | Eᶜ ∈ {U | IsOpen U}} and generated_by is invariant under complements
  have hclosed : ({F : Set (EuclideanSpace' d) | IsClosed F}) = {E | Eᶜ ∈ ({U : Set (EuclideanSpace' d) | IsOpen U})} := by
    ext E
    constructor
    · intro hE
      simpa [isOpen_compl_iff] using hE
    · intro hE
      simpa [isClosed_compl_iff] using hE
  rw [hclosed]
  have hgen : ConcreteSigmaAlgebra.generated_by {U : Set (EuclideanSpace' d) | IsOpen U} =
      ConcreteSigmaAlgebra.generated_by {E | Eᶜ ∈ ({U : Set (EuclideanSpace' d) | IsOpen U})} := by
    apply le_antisymm
    · apply ConcreteSigmaAlgebra.generated_by_le' (ConcreteSigmaAlgebra.generated_by {E | Eᶜ ∈ ({U : Set (EuclideanSpace' d) | IsOpen U})})
      intro E hE
      have hEc : Eᶜ ∈ {E | Eᶜ ∈ ({U : Set (EuclideanSpace' d) | IsOpen U})} := by
        simp
        simpa using hE
      have hEc_meas : (ConcreteSigmaAlgebra.generated_by {E | Eᶜ ∈ ({U : Set (EuclideanSpace' d) | IsOpen U})}).measurable (Eᶜ) :=
        ConcreteSigmaAlgebra.generated_by_contains hEc
      simpa using (ConcreteSigmaAlgebra.generated_by {E | Eᶜ ∈ ({U : Set (EuclideanSpace' d) | IsOpen U})}).compl_mem (Eᶜ) hEc_meas
    · apply ConcreteSigmaAlgebra.generated_by_le' (ConcreteSigmaAlgebra.generated_by {U : Set (EuclideanSpace' d) | IsOpen U})
      intro E hE
      rw [Set.mem_setOf_eq] at hE
      have hE_meas : (ConcreteSigmaAlgebra.generated_by {U : Set (EuclideanSpace' d) | IsOpen U}).measurable (Eᶜ) :=
        ConcreteSigmaAlgebra.generated_by_contains hE
      simpa using (ConcreteSigmaAlgebra.generated_by {U : Set (EuclideanSpace' d) | IsOpen U}).compl_mem (Eᶜ) hE_meas
  rw [hgen]

/-- Exercise 1.4.14 (iii) -/
theorem BorelSigmaAlgebra.generated_by_compact (d:ℕ) : BorelSigmaAlgebra (EuclideanSpace' d) = ConcreteSigmaAlgebra.generated_by { K : Set (EuclideanSpace' d) | IsCompact K } := by
  apply le_antisymm
  · -- Borel ≤ generated_by {compact}: every closed set is a countable union of compact sets
    rw [BorelSigmaAlgebra.generated_by_closed d]
    apply ConcreteSigmaAlgebra.generated_by_le' (ConcreteSigmaAlgebra.generated_by { K : Set (EuclideanSpace' d) | IsCompact K })
    intro F hF
    have hF_eq : F = ⋃ n : ℕ, (F ∩ Metric.closedBall (0 : EuclideanSpace' d) n) := by
      ext x
      constructor
      · intro hx
        let N : ℕ := ⌈‖x‖⌉.toNat + 1
        rw [Set.mem_iUnion]
        refine ⟨N, ?_⟩
        constructor
        · exact hx
        · rw [Metric.mem_closedBall]
          have hceil_nonneg : 0 ≤ ⌈‖x‖⌉ := Int.ceil_nonneg (norm_nonneg x)
          have hto : (⌈‖x‖⌉.toNat : ℝ) = ⌈‖x‖⌉ := by
            exact_mod_cast (Int.toNat_of_nonneg hceil_nonneg)
          have hle : ‖x‖ ≤ ⌈‖x‖⌉ := Int.le_ceil ‖x‖
          have hn : ‖x‖ < (N : ℝ) := by
            dsimp [N]
            rw [show (N : ℝ) = (⌈‖x‖⌉.toNat + 1 : ℕ) by rfl]
            rw [Nat.cast_add, Nat.cast_one, hto]
            linarith
          rw [dist_eq_norm, sub_zero]
          exact le_of_lt hn
      · intro hx
        rw [Set.mem_iUnion] at hx
        rcases hx with ⟨n, hn⟩
        exact hn.1
    rw [hF_eq]
    apply (ConcreteSigmaAlgebra.generated_by { K : Set (EuclideanSpace' d) | IsCompact K }).countable_union_mem
    intro n
    apply ConcreteSigmaAlgebra.generated_by_contains
    exact IsCompact.inter_left (ProperSpace.isCompact_closedBall (0 : EuclideanSpace' d) n) hF
  · -- generated_by {compact} ≤ Borel: compact sets are closed
    apply ConcreteSigmaAlgebra.generated_by_le' (BorelSigmaAlgebra (EuclideanSpace' d))
    intro K hK
    rw [BorelSigmaAlgebra.generated_by_closed d]
    apply ConcreteSigmaAlgebra.generated_by_contains
    exact hK.isClosed

private lemma sum_sq_le_sum_sq {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (∑ i : ι, a i ^ 2) ≤ (∑ i : ι, a i) ^ 2 := by
  have hsum_nonneg : 0 ≤ ∑ i : ι, a i := Finset.sum_nonneg (fun i hi => ha i)
  have hle : (∑ i : ι, a i ^ 2) ≤ (∑ i : ι, a i) * (∑ i : ι, a i) := by
    calc
      (∑ i : ι, a i ^ 2) = ∑ i : ι, a i * a i := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ ≤ ∑ i : ι, a i * (∑ j : ι, a j) := by
        apply Finset.sum_le_sum
        intro i hi
        nlinarith [Finset.single_le_sum (s := Finset.univ) (f := a) (fun j hj => ha j) (Finset.mem_univ i), ha i, hsum_nonneg]
      _ = (∑ i : ι, a i) * (∑ i : ι, a i) := by
        simp [Finset.sum_mul]
  simpa [pow_two] using hle

private lemma norm_le_sum_abs {d : ℕ} (v : EuclideanSpace' d) : ‖v‖ ≤ ∑ i : Fin d, |v i| := by
  rw [PiLp.norm_eq_of_L2]
  have hnonneg : ∀ i : Fin d, 0 ≤ |v i| := fun i => abs_nonneg (v i)
  have h2 : (∑ i : Fin d, |v i| ^ 2) ≤ (∑ i : Fin d, |v i|) ^ 2 := sum_sq_le_sum_sq (fun i => |v i|) hnonneg
  have hle := Real.sqrt_le_sqrt h2
  rw [Real.sqrt_sq_eq_abs] at hle
  have hsum_nonneg : 0 ≤ ∑ i : Fin d, |v i| := Finset.sum_nonneg (fun i hi => abs_nonneg (v i))
  rwa [abs_of_nonneg hsum_nonneg] at hle

private lemma exists_rat_close (a : ℝ) (δ : ℝ) (hδ : 0 < δ) : ∃ q : ℚ, |a - (q : ℝ)| < δ := by
  have hlt : a - δ < a + δ := by linarith
  rcases exists_rat_btwn hlt with ⟨q, hq1, hq2⟩
  refine ⟨q, ?_⟩
  rw [abs_lt]
  constructor
  · linarith
  · linarith

/-- Every point of Euclidean space has a rational point within distance ε. -/
private lemma exists_ratPoint_close {d : ℕ} (x : EuclideanSpace' d) (ε : ℝ) (hε : 0 < ε) :
    ∃ q : Fin d → ℚ, dist x (.toLp 2 (fun i : Fin d => (q i : ℝ)) : EuclideanSpace' d) < ε := by
  let δ : ℝ := ε / (d + 1)
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  let q : Fin d → ℚ := fun i => Classical.choose (exists_rat_close (x i) δ hδ)
  have hq : ∀ i, |x i - (q i : ℝ)| < δ := fun i => Classical.choose_spec (exists_rat_close (x i) δ hδ)
  refine ⟨q, ?_⟩
  have hnorm : ‖x - (.toLp 2 (fun i : Fin d => (q i : ℝ)) : EuclideanSpace' d)‖ ≤ ∑ i : Fin d, |x i - (q i : ℝ)| := by
    simpa using (norm_le_sum_abs (x - (.toLp 2 (fun i : Fin d => (q i : ℝ)) : EuclideanSpace' d)))
  have hsum : (∑ i : Fin d, |x i - (q i : ℝ)|) < ε := by
    have hδ' : δ * (d + 1) = ε := by
      dsimp [δ]
      field_simp
    have hle : ∑ i : Fin d, |x i - (q i : ℝ)| ≤ (d : ℝ) * δ := by
      have hsum_le : (∑ i : Fin d, |x i - (q i : ℝ)|) ≤ (∑ i : Fin d, δ) := by
        apply Finset.sum_le_sum
        intro i hi
        exact le_of_lt (hq i)
      calc
        (∑ i : Fin d, |x i - (q i : ℝ)|) ≤ (∑ i : Fin d, δ) := hsum_le
        _ = (Fintype.card (Fin d) : ℝ) * δ := by simp
        _ = (d : ℝ) * δ := by simp
    have hlt : (d : ℝ) * δ < ε := by
      have hδpos : 0 < δ := hδ
      have : (d : ℝ) * δ < (d + 1) * δ := by
        nlinarith [hδpos]
      nlinarith [hδ']
    exact lt_of_le_of_lt hle hlt
  rw [dist_eq_norm]
  exact lt_of_le_of_lt hnorm hsum

/-- The set of balls with rational center and rational radius. -/
private def ratBall (d : ℕ) : Set (Set (EuclideanSpace' d)) :=
  {B | ∃ (q : Fin d → ℚ) (r : ℚ), B = Metric.ball (.toLp 2 (fun i : Fin d => (q i : ℝ)) : EuclideanSpace' d) (r : ℝ)}

private lemma ratBall_countable (d : ℕ) : (ratBall d).Countable := by
  have hrange : (ratBall d) = Set.range (fun p : (Fin d → ℚ) × ℚ =>
      Metric.ball (.toLp 2 (fun i : Fin d => (p.1 i : ℝ)) : EuclideanSpace' d) (p.2 : ℝ)) := by
    ext B
    constructor
    · intro hB
      rcases hB with ⟨q, r, rfl⟩
      exact ⟨(q, r), rfl⟩
    · intro hB
      rcases hB with ⟨p, rfl⟩
      exact ⟨p.1, p.2, rfl⟩
  rw [hrange]
  exact Set.countable_range _

/-- Every open set is a countable union of rational balls. -/
private lemma open_eq_union_ratBalls {d : ℕ} (U : Set (EuclideanSpace' d)) (hU : IsOpen U) :
    U = ⋃ B ∈ {B ∈ ratBall d | B ⊆ U}, B := by
  ext x
  constructor
  · intro hx
    rcases (Metric.isOpen_iff.mp hU) x hx with ⟨ε, hε, hball⟩
    rcases exists_ratPoint_close x (ε / 4) (by linarith) with ⟨q, hqx⟩
    have hlt : dist x (.toLp 2 (fun i : Fin d => (q i : ℝ)) : EuclideanSpace' d) < ε / 4 := hqx
    rcases exists_rat_btwn hlt with ⟨r, hr1, hr2⟩
    have hball_sub : Metric.ball (.toLp 2 (fun i : Fin d => (q i : ℝ)) : EuclideanSpace' d) (r : ℝ) ⊆ Metric.ball x ε := by
      intro y hy
      have hyq : dist y (.toLp 2 (fun i : Fin d => (q i : ℝ)) : EuclideanSpace' d) < (r : ℝ) := by
        simpa using (Metric.mem_ball.mp hy)
      have hyq4 : dist y (.toLp 2 (fun i : Fin d => (q i : ℝ)) : EuclideanSpace' d) < ε / 4 := lt_trans hyq hr2
      have hqx4 : dist (.toLp 2 (fun i : Fin d => (q i : ℝ)) : EuclideanSpace' d) x < ε / 4 := by
        simpa [dist_comm] using hqx
      have hdist : dist y x < ε := by
        calc
          dist y x ≤ dist y (.toLp 2 (fun i : Fin d => (q i : ℝ)) : EuclideanSpace' d) + dist (.toLp 2 (fun i : Fin d => (q i : ℝ)) : EuclideanSpace' d) x := dist_triangle y (.toLp 2 (fun i : Fin d => (q i : ℝ)) : EuclideanSpace' d) x
          _ < ε / 4 + ε / 4 := add_lt_add hyq4 hqx4
          _ = ε / 2 := by ring
          _ < ε := by linarith
      exact Metric.mem_ball.mpr hdist
    have hsubU : Metric.ball (.toLp 2 (fun i : Fin d => (q i : ℝ)) : EuclideanSpace' d) (r : ℝ) ⊆ U :=
      hball_sub.trans hball
    rw [Set.mem_iUnion]
    refine ⟨Metric.ball (.toLp 2 (fun i : Fin d => (q i : ℝ)) : EuclideanSpace' d) (r : ℝ), ?_⟩
    rw [Set.mem_iUnion]
    refine ⟨⟨?_, hsubU⟩, ?_⟩
    · rw [ratBall]
      exact ⟨q, r, rfl⟩
    · rw [Metric.mem_ball]
      exact hr1
  · intro hx
    rw [Set.mem_iUnion] at hx
    rcases hx with ⟨B, hB⟩
    rw [Set.mem_iUnion] at hB
    rcases hB with ⟨⟨hB_rat, hB_sub⟩, hx_in⟩
    exact hB_sub hx_in

/-- Exercise 1.4.14 (iv) -/
theorem BorelSigmaAlgebra.generated_by_open_balls (d:ℕ) : BorelSigmaAlgebra (EuclideanSpace' d) = ConcreteSigmaAlgebra.generated_by { B : Set (EuclideanSpace' d) | ∃ x₀ r, B = Metric.ball x₀ r } := by
  apply le_antisymm
  · -- Borel ≤ generated_by {open balls}: every open set is a countable union of open balls
    unfold BorelSigmaAlgebra
    let G : ConcreteSigmaAlgebra (EuclideanSpace' d) :=
      ConcreteSigmaAlgebra.generated_by { B : Set (EuclideanSpace' d) | ∃ x₀ r, B = Metric.ball x₀ r }
    apply ConcreteSigmaAlgebra.generated_by_le' G
    intro U hU
    rw [Set.mem_setOf_eq] at hU
    have hU_eq : U = ⋃ B ∈ {B ∈ ratBall d | B ⊆ U}, B := open_eq_union_ratBalls U hU
    -- enumerate ratBall d
    have hF_nonempty : (ratBall d).Nonempty := by
      refine ⟨Metric.ball (0 : EuclideanSpace' d) 0, ?_⟩
      rw [ratBall]
      exact ⟨(fun _ : Fin d => 0), 0, by simp⟩
    rcases (ratBall_countable d).exists_eq_range hF_nonempty with ⟨f, hf⟩
    -- U = ⋃ n, if f n ⊆ U then f n else ∅
    classical
    let E : ℕ → Set (EuclideanSpace' d) := fun n => if f n ⊆ U then f n else ∅
    have hE_eq : (⋃ n, E n) = U := by
      have hE_union : (⋃ n, E n) = ⋃ B ∈ {B ∈ ratBall d | B ⊆ U}, B := by
        ext x
        constructor
        · intro hx
          rw [Set.mem_iUnion] at hx
          rcases hx with ⟨n, hn⟩
          have hfn : f n ∈ ratBall d := by
            rw [hf]
            exact Set.mem_range.mpr ⟨n, rfl⟩
          by_cases hsub : f n ⊆ U
          · rw [Set.mem_iUnion]
            refine ⟨f n, ?_⟩
            rw [Set.mem_iUnion]
            exact ⟨⟨hfn, hsub⟩, by simpa [E, hsub] using hn⟩
          · simp [E, hsub] at hn
        · intro hx
          rw [Set.mem_iUnion] at hx
          rcases hx with ⟨B, hB⟩
          rw [Set.mem_iUnion] at hB
          rcases hB with ⟨⟨hB_rat, hB_sub⟩, hx_in⟩
          rw [hf] at hB_rat
          rcases hB_rat with ⟨n, hfn⟩
          rw [Set.mem_iUnion]
          refine ⟨n, ?_⟩
          have hsub' : f n ⊆ U := by
            simpa [hfn] using hB_sub
          change x ∈ (if f n ⊆ U then f n else ∅)
          rw [if_pos hsub']
          simpa [hfn] using hx_in
      exact hE_union.trans hU_eq.symm
    have hE_meas : ∀ n, G.measurable (E n) := by
      intro n
      by_cases hsub : f n ⊆ U
      · -- E n = f n, a ball
        have hfn : f n ∈ ratBall d := by
          rw [hf]
          exact Set.mem_range.mpr ⟨n, rfl⟩
        rcases hfn with ⟨q, r, hEq⟩
        have hball_meas : G.measurable (f n) := by
          apply ConcreteSigmaAlgebra.generated_by_contains
          exact ⟨(.toLp 2 (fun i : Fin d => (q i : ℝ)) : EuclideanSpace' d), r, hEq⟩
        simpa [E, hsub] using hball_meas
      · -- E n = ∅
        simpa [E, hsub] using G.empty_mem
    rw [← hE_eq]
    exact G.countable_union_mem E hE_meas
  · -- generated_by {open balls} ≤ Borel: balls are open
    apply ConcreteSigmaAlgebra.generated_by_le' (BorelSigmaAlgebra (EuclideanSpace' d))
    intro B hB
    rcases hB with ⟨x₀, r, rfl⟩
    apply ConcreteSigmaAlgebra.generated_by_contains
    exact (Metric.isOpen_ball (α := EuclideanSpace' d))

/-- Boxes with rational endpoints. -/
private def ratBox (d : ℕ) : Set (Box d) :=
  {B | ∃ q₁ q₂ : Fin d → ℚ, B = ⟨fun i => BoundedInterval.Icc ((q₁ i : ℝ)) ((q₂ i : ℝ))⟩}

private lemma ratBox_countable (d : ℕ) : (ratBox d).Countable := by
  let h : Set (Box d) := Set.range (fun p : (Fin d → ℚ) × (Fin d → ℚ) =>
      ⟨fun i => BoundedInterval.Icc ((p.1 i : ℝ)) ((p.2 i : ℝ))⟩)
  have hh : (ratBox d) = h := by
    ext B
    constructor
    · intro hB
      rcases hB with ⟨q₁, q₂, rfl⟩
      exact ⟨(q₁, q₂), rfl⟩
    · intro hB
      rcases hB with ⟨p, rfl⟩
      exact ⟨p.1, p.2, rfl⟩
  rw [hh]
  exact Set.countable_range _

private lemma bracket_exists (a : ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ q : ℚ × ℚ, a - δ < (q.1 : ℝ) ∧ (q.1 : ℝ) < a ∧ a < (q.2 : ℝ) ∧ (q.2 : ℝ) < a + δ := by
  rcases exists_rat_btwn (show a - δ < a by linarith) with ⟨q₁, hq₁1, hq₁2⟩
  rcases exists_rat_btwn (show a < a + δ by linarith) with ⟨q₂, hq₂1, hq₂2⟩
  exact ⟨(q₁, q₂), hq₁1, hq₁2, hq₂1, hq₂2⟩

/-- Every open set is a countable union of boxes. -/
private lemma open_eq_union_ratBoxes {d : ℕ} (U : Set (EuclideanSpace' d)) (hU : IsOpen U) :
    U = ⋃ B ∈ {B ∈ ratBox d | (B.toSet : Set (EuclideanSpace' d)) ⊆ U}, (B.toSet : Set (EuclideanSpace' d)) := by
  ext x
  constructor
  · intro hx
    rcases (Metric.isOpen_iff.mp hU) x hx with ⟨ε, hε, hball⟩
    let δ : ℝ := ε / (4 * (d + 1))
    have hδ : 0 < δ := by
      dsimp [δ]
      positivity
    let q₁ : Fin d → ℚ := fun i => (bracket_exists (x i) δ hδ).choose.1
    let q₂ : Fin d → ℚ := fun i => (bracket_exists (x i) δ hδ).choose.2
    have hq₁ : ∀ i, x i - δ < (q₁ i : ℝ) ∧ (q₁ i : ℝ) < x i := fun i =>
      ⟨(bracket_exists (x i) δ hδ).choose_spec.1, (bracket_exists (x i) δ hδ).choose_spec.2.1⟩
    have hq₂ : ∀ i, x i < (q₂ i : ℝ) ∧ (q₂ i : ℝ) < x i + δ := fun i =>
      ⟨(bracket_exists (x i) δ hδ).choose_spec.2.2.1, (bracket_exists (x i) δ hδ).choose_spec.2.2.2⟩
    let B : Box d := ⟨fun i => BoundedInterval.Icc ((q₁ i : ℝ)) ((q₂ i : ℝ))⟩
    have hB_rat : B ∈ ratBox d := by
      rw [ratBox]
      exact ⟨q₁, q₂, rfl⟩
    have hB_sub_ball : (B.toSet : Set (EuclideanSpace' d)) ⊆ Metric.ball x ε := by
      intro y hy
      have hyi : ∀ i, (q₁ i : ℝ) ≤ y i ∧ y i ≤ (q₂ i : ℝ) := by
        intro i
        have := hy i
        simpa [B] using this
      rw [Metric.mem_ball]
      have hdist : dist y x < ε := by
        rw [dist_eq_norm]
        have hnorm : ‖y - x‖ ≤ ∑ i : Fin d, |y i - x i| := norm_le_sum_abs (y - x)
        have hsum : (∑ i : Fin d, |y i - x i|) < ε := by
          have hb : ∑ i : Fin d, |y i - x i| ≤ (Fintype.card (Fin d) : ℝ) * (2 * δ) := by
            have hsum_le : ∑ i : Fin d, |y i - x i| ≤ ∑ i : Fin d, (2 * δ) := by
              apply Finset.sum_le_sum
              intro i hi
              have hyi' := hyi i
              have hq₁i := hq₁ i
              have hq₂i := hq₂ i
              have hyix : |y i - x i| ≤ (q₂ i : ℝ) - (q₁ i : ℝ) := by
                have hle1 : y i - x i ≤ (q₂ i : ℝ) - (q₁ i : ℝ) := by
                  linarith
                have hle2 : x i - y i ≤ (q₂ i : ℝ) - (q₁ i : ℝ) := by
                  linarith
                rw [abs_le]
                constructor
                · linarith
                · linarith
              have hd : (q₂ i : ℝ) - (q₁ i : ℝ) < 2 * δ := by
                linarith
              linarith
            calc
              (∑ i : Fin d, |y i - x i|) ≤ ∑ i : Fin d, (2 * δ) := hsum_le
              _ = (Fintype.card (Fin d) : ℝ) * (2 * δ) := by simp
          have hd2 : (Fintype.card (Fin d) : ℝ) * (2 * δ) < ε := by
            have hd' : (d : ℝ) * (2 * δ) < ε := by
              dsimp [δ]
              have hle1_lt : (d : ℝ) / (2 * ((d : ℝ) + 1)) < 1 := by
                have hpos : 0 < 2 * ((d : ℝ) + 1) := by positivity
                have hlt : (d : ℝ) < 2 * ((d : ℝ) + 1) := by linarith
                exact (div_lt_one hpos).mpr hlt
              have hE : (d : ℝ) * (2 * (ε / (4 * (d + 1)))) = (d : ℝ) / (2 * ((d : ℝ) + 1)) * ε := by
                field_simp
                ring
              rw [hE]
              exact mul_lt_of_lt_one_left hε hle1_lt
            simpa [show (Fintype.card (Fin d) : ℝ) = (d : ℝ) by simp] using hd'
          exact lt_of_le_of_lt hb hd2
        exact lt_of_le_of_lt hnorm hsum
      exact hdist
    have hB_sub : (B.toSet : Set (EuclideanSpace' d)) ⊆ U := hB_sub_ball.trans hball
    rw [Set.mem_iUnion]
    refine ⟨B, ?_⟩
    rw [Set.mem_iUnion]
    refine ⟨⟨hB_rat, hB_sub⟩, ?_⟩
    rw [Box.mem_toSet]
    intro i
    constructor
    · exact le_of_lt (hq₁ i).2
    · exact le_of_lt (hq₂ i).1
  · intro hx
    rw [Set.mem_iUnion] at hx
    rcases hx with ⟨B, hB⟩
    rw [Set.mem_iUnion] at hB
    rcases hB with ⟨⟨hB_rat, hB_sub⟩, hx_in⟩
    exact hB_sub hx_in

/-- The n-th closed approximation of a bounded interval. -/
private noncomputable def boxSideApprox (I : BoundedInterval) (n : ℕ) : ℝ × ℝ :=
  match I with
  | BoundedInterval.Ioo a b => (a + ((n : ℝ) + 2)⁻¹, b - ((n : ℝ) + 2)⁻¹)
  | BoundedInterval.Icc a b => (a, b)
  | BoundedInterval.Ioc a b => (a + ((n : ℝ) + 2)⁻¹, b)
  | BoundedInterval.Ico a b => (a, b - ((n : ℝ) + 2)⁻¹)

/-- The n-th closed box approximation of a box. -/
private noncomputable def boxApprox {d : ℕ} (B : Box d) (n : ℕ) : Box d :=
  ⟨fun i => BoundedInterval.Icc (boxSideApprox (B.side i) n).1 (boxSideApprox (B.side i) n).2⟩

private lemma boxSide_inv_pos {n : ℕ} : 0 < ((n : ℝ) + 2)⁻¹ := by
  rw [← one_div]
  positivity

private lemma boxSide_inv_lt_succ {n : ℕ} : ((n : ℝ) + 1 + 2)⁻¹ < ((n : ℝ) + 2)⁻¹ := by
  rw [← one_div, ← one_div]
  rw [one_div_lt_one_div]
  · linarith
  · positivity
  · positivity

private lemma exists_large_nat_lt_inv {δ : ℝ} (hδ : 0 < δ) : ∃ N : ℕ, ((N : ℝ) + 2)⁻¹ < δ := by
  rcases exists_nat_gt (1 / δ) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  rw [← one_div]
  rw [div_lt_iff₀ (by positivity : 0 < (N : ℝ) + 2)]
  have hNδ : 1 < δ * (N : ℝ) := by
    calc
      1 = δ * (1 / δ) := by field_simp [ne_of_gt hδ]
      _ < δ * (N : ℝ) := mul_lt_mul_of_pos_left hN hδ
  nlinarith

private lemma boxSideApprox_nested (I : BoundedInterval) (n : ℕ) :
    (BoundedInterval.Icc (boxSideApprox I n).1 (boxSideApprox I n).2 : Set ℝ) ⊆
      (BoundedInterval.Icc (boxSideApprox I (n + 1)).1 (boxSideApprox I (n + 1)).2 : Set ℝ) := by
  intro x hx
  rcases hx with ⟨hx1, hx2⟩
  match I with
  | BoundedInterval.Ioo a b =>
      simp [boxSideApprox] at hx1 hx2 ⊢
      constructor <;> linarith [boxSide_inv_lt_succ (n := n)]
  | BoundedInterval.Icc a b =>
      simp [boxSideApprox] at hx1 hx2 ⊢
      exact ⟨hx1, hx2⟩
  | BoundedInterval.Ioc a b =>
      simp [boxSideApprox] at hx1 hx2 ⊢
      constructor
      · linarith [boxSide_inv_lt_succ (n := n)]
      · exact hx2
  | BoundedInterval.Ico a b =>
      simp [boxSideApprox] at hx1 hx2 ⊢
      constructor
      · exact hx1
      · linarith [boxSide_inv_lt_succ (n := n)]

private lemma boxSideApprox_mono (I : BoundedInterval) {m : ℕ} :
    ∀ N : ℕ, m ≤ N →
      (BoundedInterval.Icc (boxSideApprox I m).1 (boxSideApprox I m).2 : Set ℝ) ⊆
        (BoundedInterval.Icc (boxSideApprox I N).1 (boxSideApprox I N).2 : Set ℝ) := by
  intro N
  induction N with
  | zero =>
      intro hm
      have hEq : m = 0 := Nat.eq_zero_of_le_zero hm
      subst m
      exact subset_rfl
  | succ N ih =>
      intro hm
      by_cases hle : m ≤ N
      · exact (ih hle).trans (boxSideApprox_nested I N)
      · have hEq : m = N + 1 := by omega
        subst m
        exact subset_rfl

private lemma interval_eq_union_approx (I : BoundedInterval) :
    (I.toSet : Set ℝ) = ⋃ n : ℕ, (BoundedInterval.Icc (boxSideApprox I n).1 (boxSideApprox I n).2 : Set ℝ) := by
  match I with
  | BoundedInterval.Ioo a b =>
      ext x
      constructor
      · intro hx
        rw [BoundedInterval.set_Ioo, Set.mem_Ioo] at hx
        rw [Set.mem_iUnion]
        have hmin : 0 < min (x - a) (b - x) := lt_min_iff.mpr (by constructor <;> linarith)
        rcases exists_large_nat_lt_inv hmin with ⟨N, hN⟩
        have hNa : ((N : ℝ) + 2)⁻¹ < x - a := by
          exact lt_of_lt_of_le hN (min_le_left _ _)
        have hNb : ((N : ℝ) + 2)⁻¹ < b - x := by
          exact lt_of_lt_of_le hN (min_le_right _ _)
        refine ⟨N, ?_⟩
        simp [boxSideApprox]
        constructor <;> linarith
      · intro hx
        rw [Set.mem_iUnion] at hx
        rcases hx with ⟨n, hn⟩
        simp [boxSideApprox] at hn
        rw [BoundedInterval.set_Ioo, Set.mem_Ioo]
        constructor <;> linarith [boxSide_inv_pos (n := n)]
  | BoundedInterval.Icc a b =>
      ext x
      constructor
      · intro hx
        rw [Set.mem_iUnion]
        exact ⟨0, by simpa [boxSideApprox, BoundedInterval.set_Icc] using hx⟩
      · intro hx
        rw [Set.mem_iUnion] at hx
        rcases hx with ⟨n, hn⟩
        simpa [boxSideApprox, BoundedInterval.set_Icc] using hn
  | BoundedInterval.Ioc a b =>
      ext x
      constructor
      · intro hx
        rw [BoundedInterval.set_Ioc, Set.mem_Ioc] at hx
        rw [Set.mem_iUnion]
        rcases exists_large_nat_lt_inv (sub_pos.mpr hx.1) with ⟨N, hN⟩
        refine ⟨N, ?_⟩
        simp [boxSideApprox]
        constructor
        · linarith
        · exact hx.2
      · intro hx
        rw [Set.mem_iUnion] at hx
        rcases hx with ⟨n, hn⟩
        simp [boxSideApprox] at hn
        rw [BoundedInterval.set_Ioc, Set.mem_Ioc]
        constructor
        · linarith [boxSide_inv_pos (n := n)]
        · exact hn.2
  | BoundedInterval.Ico a b =>
      ext x
      constructor
      · intro hx
        rw [BoundedInterval.set_Ico, Set.mem_Ico] at hx
        rw [Set.mem_iUnion]
        rcases exists_large_nat_lt_inv (sub_pos.mpr hx.2) with ⟨N, hN⟩
        refine ⟨N, ?_⟩
        simp [boxSideApprox]
        constructor
        · exact hx.1
        · linarith
      · intro hx
        rw [Set.mem_iUnion] at hx
        rcases hx with ⟨n, hn⟩
        simp [boxSideApprox] at hn
        rw [BoundedInterval.set_Ico, Set.mem_Ico]
        constructor
        · exact hn.1
        · linarith [boxSide_inv_pos (n := n)]

private lemma box_eq_union_approx {d : ℕ} (B : Box d) : B.toSet = ⋃ n : ℕ, (boxApprox B n).toSet := by
  ext x
  constructor
  · intro hx
    have hx_i : ∀ i, x i ∈ (B.side i).toSet := by simpa [Box.mem_toSet] using hx
    have hEx : ∀ i, ∃ n, x i ∈ (BoundedInterval.Icc (boxSideApprox (B.side i) n).1 (boxSideApprox (B.side i) n).2 : Set ℝ) := by
      intro i
      rw [← Set.mem_iUnion]
      rw [← interval_eq_union_approx]
      exact hx_i i
    choose n hxn using hEx
    let N : ℕ := Finset.univ.sup n
    rw [Set.mem_iUnion]
    refine ⟨N, ?_⟩
    rw [Box.mem_toSet]
    intro i
    have hle : n i ≤ N := by
      dsimp [N]
      exact Finset.le_sup (s := Finset.univ) (Finset.mem_univ i)
    exact boxSideApprox_mono (B.side i) N hle (hxn i)
  · intro hx
    rw [Set.mem_iUnion] at hx
    rcases hx with ⟨n, hn⟩
    rw [Box.mem_toSet]
    intro i
    rw [interval_eq_union_approx]
    rw [Set.mem_iUnion]
    exact ⟨n, hn i⟩

private lemma boxApprox_isClosed {d : ℕ} (B : Box d) (n : ℕ) : IsClosed (boxApprox B n).toSet := by
  let a : Fin d → ℝ := fun i => (boxSideApprox (B.side i) n).1
  let b : Fin d → ℝ := fun i => (boxSideApprox (B.side i) n).2
  rw [show (boxApprox B n).toSet = {x : EuclideanSpace' d | ∀ i, a i ≤ x i ∧ x i ≤ b i} by
    ext x
    simp [boxApprox, a, b]]
  rw [show {x : EuclideanSpace' d | ∀ i, a i ≤ x i ∧ x i ≤ b i} = ⋂ i : Fin d, {x : EuclideanSpace' d | a i ≤ x i ∧ x i ≤ b i} by ext x; simp]
  apply isClosed_iInter
  intro i
  rw [show ({x : EuclideanSpace' d | a i ≤ x i ∧ x i ≤ b i} : Set (EuclideanSpace' d)) = (fun x : EuclideanSpace' d => x i) ⁻¹' Set.Icc (a i) (b i) by ext x; simp]
  exact (isClosed_Icc.preimage (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i))

/-- Every box is Borel-measurable. -/
theorem Box.borel_measurable {d : ℕ} (B : Box d) :
    (BorelSigmaAlgebra (EuclideanSpace' d)).measurable B.toSet := by
  rw [BorelSigmaAlgebra.generated_by_closed d]
  rw [box_eq_union_approx B]
  apply (ConcreteSigmaAlgebra.generated_by {F : Set (EuclideanSpace' d) | IsClosed F}).countable_union_mem
  intro n
  apply ConcreteSigmaAlgebra.generated_by_contains
  exact boxApprox_isClosed B n

/-- Exercise 1.4.14 (v) -/
theorem BorelSigmaAlgebra.generated_by_boxes (d:ℕ) : BorelSigmaAlgebra (EuclideanSpace' d) = ConcreteSigmaAlgebra.generated_by (Box.toSet '' Set.univ) := by
  apply le_antisymm
  · -- Borel ≤ generated_by {boxes}: every open set is a countable union of boxes
    unfold BorelSigmaAlgebra
    let G : ConcreteSigmaAlgebra (EuclideanSpace' d) := ConcreteSigmaAlgebra.generated_by (Box.toSet '' Set.univ)
    apply ConcreteSigmaAlgebra.generated_by_le' G
    intro U hU
    rw [Set.mem_setOf_eq] at hU
    have hU_eq : U = ⋃ B ∈ {B ∈ ratBox d | (B.toSet : Set (EuclideanSpace' d)) ⊆ U}, (B.toSet : Set (EuclideanSpace' d)) :=
      open_eq_union_ratBoxes U hU
    have hF_nonempty : (ratBox d).Nonempty := by
      refine ⟨⟨fun _ : Fin d => BoundedInterval.Icc (0 : ℝ) (0 : ℝ)⟩, ?_⟩
      rw [ratBox]
      exact ⟨(fun _ : Fin d => 0), (fun _ : Fin d => 0), by simp⟩
    rcases (ratBox_countable d).exists_eq_range hF_nonempty with ⟨f, hf⟩
    classical
    let E : ℕ → Set (EuclideanSpace' d) := fun n => if (f n).toSet ⊆ U then (f n).toSet else ∅
    have hE_eq : (⋃ n, E n) = U := by
      have hE_union : (⋃ n, E n) = ⋃ B ∈ {B ∈ ratBox d | (B.toSet : Set (EuclideanSpace' d)) ⊆ U}, (B.toSet : Set (EuclideanSpace' d)) := by
        ext x
        constructor
        · intro hx
          rw [Set.mem_iUnion] at hx
          rcases hx with ⟨n, hn⟩
          have hfn : f n ∈ ratBox d := by
            rw [hf]
            exact Set.mem_range.mpr ⟨n, rfl⟩
          by_cases hsub : (f n).toSet ⊆ U
          · rw [Set.mem_iUnion]
            refine ⟨f n, ?_⟩
            rw [Set.mem_iUnion]
            exact ⟨⟨hfn, hsub⟩, by simpa [E, hsub] using hn⟩
          · simp [E, hsub] at hn
        · intro hx
          rw [Set.mem_iUnion] at hx
          rcases hx with ⟨B, hB⟩
          rw [Set.mem_iUnion] at hB
          rcases hB with ⟨⟨hB_rat, hB_sub⟩, hx_in⟩
          rw [hf] at hB_rat
          rcases hB_rat with ⟨n, hfn⟩
          rw [Set.mem_iUnion]
          refine ⟨n, ?_⟩
          have hsub' : (f n).toSet ⊆ U := by
            simpa [hfn] using hB_sub
          change x ∈ (if (f n).toSet ⊆ U then (f n).toSet else ∅)
          rw [if_pos hsub']
          simpa [hfn] using hx_in
      exact hE_union.trans hU_eq.symm
    have hE_meas : ∀ n, G.measurable (E n) := by
      intro n
      by_cases hsub : (f n).toSet ⊆ U
      · have hmeas : G.measurable (f n).toSet := by
          apply ConcreteSigmaAlgebra.generated_by_contains
          exact ⟨f n, by simp⟩
        simpa [E, hsub] using hmeas
      · simpa [E, hsub] using G.empty_mem
    rw [← hE_eq]
    exact G.countable_union_mem E hE_meas
  · -- generated_by {boxes} ≤ Borel: boxes are closed
    apply ConcreteSigmaAlgebra.generated_by_le' (BorelSigmaAlgebra (EuclideanSpace' d))
    intro B hB
    rcases hB with ⟨B', _, rfl⟩
    -- a box is a countable union of closed boxes, hence Borel
    exact Box.borel_measurable B'

/-- Exercise 1.4.14 (vi) -/
theorem BorelSigmaAlgebra.generated_by_elementary (d:ℕ) : BorelSigmaAlgebra (EuclideanSpace' d) = ConcreteSigmaAlgebra.generated_by { E : Set (EuclideanSpace' d) | IsElementary E }  := by
  apply le_antisymm
  · -- Borel ≤ generated_by {elementary}: every open set is a countable union of elementary sets
    unfold BorelSigmaAlgebra
    let G : ConcreteSigmaAlgebra (EuclideanSpace' d) :=
      ConcreteSigmaAlgebra.generated_by { E : Set (EuclideanSpace' d) | IsElementary E }
    apply ConcreteSigmaAlgebra.generated_by_le' G
    intro U hU
    rw [Set.mem_setOf_eq] at hU
    have hU_eq : U = ⋃ B ∈ {B ∈ ratBox d | (B.toSet : Set (EuclideanSpace' d)) ⊆ U}, (B.toSet : Set (EuclideanSpace' d)) :=
      open_eq_union_ratBoxes U hU
    have hF_nonempty : (ratBox d).Nonempty := by
      refine ⟨⟨fun _ : Fin d => BoundedInterval.Icc (0 : ℝ) (0 : ℝ)⟩, ?_⟩
      rw [ratBox]
      exact ⟨(fun _ : Fin d => 0), (fun _ : Fin d => 0), by simp⟩
    rcases (ratBox_countable d).exists_eq_range hF_nonempty with ⟨f, hf⟩
    classical
    let E : ℕ → Set (EuclideanSpace' d) := fun n => if (f n).toSet ⊆ U then (f n).toSet else ∅
    have hE_eq : (⋃ n, E n) = U := by
      have hE_union : (⋃ n, E n) = ⋃ B ∈ {B ∈ ratBox d | (B.toSet : Set (EuclideanSpace' d)) ⊆ U}, (B.toSet : Set (EuclideanSpace' d)) := by
        ext x
        constructor
        · intro hx
          rw [Set.mem_iUnion] at hx
          rcases hx with ⟨n, hn⟩
          have hfn : f n ∈ ratBox d := by
            rw [hf]
            exact Set.mem_range.mpr ⟨n, rfl⟩
          by_cases hsub : (f n).toSet ⊆ U
          · rw [Set.mem_iUnion]
            refine ⟨f n, ?_⟩
            rw [Set.mem_iUnion]
            exact ⟨⟨hfn, hsub⟩, by simpa [E, hsub] using hn⟩
          · simp [E, hsub] at hn
        · intro hx
          rw [Set.mem_iUnion] at hx
          rcases hx with ⟨B, hB⟩
          rw [Set.mem_iUnion] at hB
          rcases hB with ⟨⟨hB_rat, hB_sub⟩, hx_in⟩
          rw [hf] at hB_rat
          rcases hB_rat with ⟨n, hfn⟩
          rw [Set.mem_iUnion]
          refine ⟨n, ?_⟩
          have hsub' : (f n).toSet ⊆ U := by
            simpa [hfn] using hB_sub
          change x ∈ (if (f n).toSet ⊆ U then (f n).toSet else ∅)
          rw [if_pos hsub']
          simpa [hfn] using hx_in
      exact hE_union.trans hU_eq.symm
    have hE_meas : ∀ n, G.measurable (E n) := by
      intro n
      by_cases hsub : (f n).toSet ⊆ U
      · have hmeas : G.measurable (f n).toSet := by
          apply ConcreteSigmaAlgebra.generated_by_contains
          exact IsElementary.box (f n)
        simpa [E, hsub] using hmeas
      · simpa [E, hsub] using G.empty_mem
    rw [← hE_eq]
    exact G.countable_union_mem E hE_meas
  · -- generated_by {elementary} ≤ Borel: elementary sets are finite unions of boxes, boxes are closed
    apply ConcreteSigmaAlgebra.generated_by_le' (BorelSigmaAlgebra (EuclideanSpace' d))
    intro E hE
    -- E is elementary: E = ⋃ B ∈ S, B for a finite S of boxes
    rcases hE with ⟨S, rfl⟩
    rw [BorelSigmaAlgebra.generated_by_boxes d]
    -- finite union of boxes, each box measurable
    classical
    let G : ConcreteSigmaAlgebra (EuclideanSpace' d) := ConcreteSigmaAlgebra.generated_by (Box.toSet '' Set.univ)
    induction S using Finset.induction_on with
    | empty => simpa using G.empty_mem
    | insert B₀ S' hnot ih =>
        rw [show (⋃ B ∈ insert B₀ S', (B : Set (EuclideanSpace' d))) = (B₀ : Set (EuclideanSpace' d)) ∪ (⋃ B ∈ S', (B : Set (EuclideanSpace' d))) by ext x; simp]
        apply G.union_mem
        · apply ConcreteSigmaAlgebra.generated_by_contains
          exact ⟨B₀, by simp⟩
        · exact ih

open Ordinal in
/-- Exercise 1.4.15 (Recursive definition of generated sigma-algebra). -/
def ConcreteSigmaAlgebra.generated_by_eq {X:Type*} (F: Set (Set X)) :
  (ConcreteSigmaAlgebra.generated_by F).measurableSets =
  ⋃ α < ω₁,
  Ordinal.limitRecOn (motive := fun _ ↦ Set (Set X)) α F (fun n G ↦ { E: Set X | (∃ S: Set G, Countable S ∧ E = ⋃ (H:S), H) ∨ (∃ S: Set G, Countable S ∧ E = (⋃ (H:S), H))ᶜ }) (fun α _ G ↦ ⋃ (β : Ordinal) (h : β < α), G β h) := by sorry

open Cardinal in
/-- Exercise 1.4.16 -/
theorem ConcreteSigmaAlgebra.card_of_generated_by {X:Type*} {F: Set (Set X)} [Infinite F] :
  Cardinal.mk (ConcreteSigmaAlgebra.generated_by F).measurableSets ≤ (Cardinal.mk F) ^ ℵ₀ :=
  by sorry

open Cardinal in
theorem BorelSigmaAlgebra.card (d:ℕ) : Cardinal.mk (BorelSigmaAlgebra (EuclideanSpace' d)).measurableSets ≤ 2 ^ ℵ₀ :=
  by sorry

theorem JordanMeasurable.not_borel {d:ℕ} (hd: d ≥ 1) : ∃ E: Set (EuclideanSpace' d), JordanMeasurable E ∧ ¬ (BorelSigmaAlgebra (EuclideanSpace' d)).measurable E :=
  by sorry

/-- Exercise 1.4.17 -/
private lemma prod_equiv_cont (d₁ d₂ : ℕ) : Continuous (EuclideanSpace'.prod_equiv d₁ d₂) := by
  have h := LinearMap.continuous_of_finiteDimensional (prod_equiv_linear d₁ d₂)
  simpa [prod_equiv_linear] using h

private lemma prod_equiv_symm_cont (d₁ d₂ : ℕ) : Continuous (EuclideanSpace'.prod_equiv d₁ d₂).symm := by
  have h := LinearMap.continuous_of_finiteDimensional (prod_equiv_symm_linear d₁ d₂)
  simpa [prod_equiv_symm_linear] using h

private lemma prod_equiv_symm_image_eq_preimage (d₁ d₂ : ℕ) (S : Set (EuclideanSpace' d₁ × EuclideanSpace' d₂)) :
    (EuclideanSpace'.prod_equiv d₁ d₂).symm '' S = (EuclideanSpace'.prod_equiv d₁ d₂) ⁻¹' S := by
  exact Equiv.image_eq_preimage_symm (EuclideanSpace'.prod_equiv d₁ d₂).symm S

private lemma prod_equiv_symm_image_open {d₁ d₂ : ℕ} {S : Set (EuclideanSpace' d₁ × EuclideanSpace' d₂)} (hS : IsOpen S) :
    IsOpen ((EuclideanSpace'.prod_equiv d₁ d₂).symm '' S) := by
  rw [prod_equiv_symm_image_eq_preimage]
  exact (prod_equiv_cont d₁ d₂).isOpen_preimage S hS

theorem BorelSigmaAlgebra.prod {d₁ d₂:ℕ} {E : Set (EuclideanSpace' d₁)} {F : Set (EuclideanSpace' d₂)}
  (hE: (BorelSigmaAlgebra (EuclideanSpace' d₁)).measurable E)
  (hF: (BorelSigmaAlgebra (EuclideanSpace' d₂)).measurable F) :
  (BorelSigmaAlgebra (EuclideanSpace' (d₁ + d₂))).measurable ((EuclideanSpace'.prod_equiv d₁ d₂).symm '' (E ×ˢ F))
  :=
  by
  let φ : (EuclideanSpace' d₁ × EuclideanSpace' d₂) ≃ EuclideanSpace' (d₁ + d₂) := (EuclideanSpace'.prod_equiv d₁ d₂).symm
  have h_second : ∀ U : Set (EuclideanSpace' d₁), IsOpen U → ∀ F, (BorelSigmaAlgebra (EuclideanSpace' d₂)).measurable F →
      (BorelSigmaAlgebra (EuclideanSpace' (d₁ + d₂))).measurable (φ '' (U ×ˢ F)) := by
    intro U hU
    have h_ind : ∀ F, (BorelSigmaAlgebra (EuclideanSpace' d₂)).measurable F →
        (BorelSigmaAlgebra (EuclideanSpace' (d₁ + d₂))).measurable (φ '' (U ×ˢ F)) := by
      apply ConcreteSigmaAlgebra.induction (X := EuclideanSpace' d₂)
        (F := {V : Set (EuclideanSpace' d₂) | IsOpen V})
        (P := fun F => (BorelSigmaAlgebra (EuclideanSpace' (d₁ + d₂))).measurable (φ '' (U ×ˢ F)))
      · have h_empty : φ '' (U ×ˢ (∅ : Set (EuclideanSpace' d₂))) = ∅ := by simp [Set.prod_empty]
        rw [h_empty]
        exact (BorelSigmaAlgebra (EuclideanSpace' (d₁ + d₂))).empty_mem
      · intro V hV
        rw [Set.mem_setOf_eq] at hV
        apply ConcreteSigmaAlgebra.generated_by_contains
        exact prod_equiv_symm_image_open (IsOpen.prod hU hV)
      · intro F hF
        have h1 : φ '' (U ×ˢ Fᶜ) = (φ '' (U ×ˢ (Set.univ : Set (EuclideanSpace' d₂)))) \ (φ '' (U ×ˢ F)) := by
          rw [show U ×ˢ Fᶜ = (U ×ˢ (Set.univ : Set (EuclideanSpace' d₂))) \ (U ×ˢ F) by ext p; aesop]
          rw [Set.image_diff φ.injective]
        rw [h1]
        have hUu : (BorelSigmaAlgebra (EuclideanSpace' (d₁ + d₂))).measurable (φ '' (U ×ˢ (Set.univ : Set (EuclideanSpace' d₂)))) := by
          apply ConcreteSigmaAlgebra.generated_by_contains
          exact prod_equiv_symm_image_open (IsOpen.prod hU isOpen_univ)
        exact (ConcreteSigmaAlgebra.sdiff_mem (BorelSigmaAlgebra (EuclideanSpace' (d₁ + d₂)))) hUu hF
      · intro Fn hFn
        have hpre : φ '' (U ×ˢ (⋃ n, Fn n)) = ⋃ n, φ '' (U ×ˢ Fn n) := by
          rw [show U ×ˢ (⋃ n, Fn n) = ⋃ n, (U ×ˢ Fn n) by ext p; aesop]
          rw [Set.image_iUnion]
        rw [hpre]
        exact (BorelSigmaAlgebra (EuclideanSpace' (d₁ + d₂))).countable_union_mem _ hFn
    intro F hF
    exact h_ind F hF
  have h_main : ∀ E, (BorelSigmaAlgebra (EuclideanSpace' d₁)).measurable E →
      ∀ F, (BorelSigmaAlgebra (EuclideanSpace' d₂)).measurable F →
        (BorelSigmaAlgebra (EuclideanSpace' (d₁ + d₂))).measurable (φ '' (E ×ˢ F)) := by
    apply ConcreteSigmaAlgebra.induction (X := EuclideanSpace' d₁)
      (F := {U : Set (EuclideanSpace' d₁) | IsOpen U})
      (P := fun E => ∀ F, (BorelSigmaAlgebra (EuclideanSpace' d₂)).measurable F →
        (BorelSigmaAlgebra (EuclideanSpace' (d₁ + d₂))).measurable (φ '' (E ×ˢ F)))
    · intro F hF
      have h_empty : φ '' ((∅ : Set (EuclideanSpace' d₁)) ×ˢ F) = ∅ := by simp [Set.empty_prod]
      rw [h_empty]
      exact (BorelSigmaAlgebra (EuclideanSpace' (d₁ + d₂))).empty_mem
    · intro U hU
      rw [Set.mem_setOf_eq] at hU
      exact h_second U hU
    · intro E hE F hF
      have h1 : φ '' (Eᶜ ×ˢ F) = (φ '' ((Set.univ : Set (EuclideanSpace' d₁)) ×ˢ F)) \ (φ '' (E ×ˢ F)) := by
        rw [show Eᶜ ×ˢ F = ((Set.univ : Set (EuclideanSpace' d₁)) ×ˢ F) \ (E ×ˢ F) by ext p; aesop]
        rw [Set.image_diff φ.injective]
      rw [h1]
      have hUu : (BorelSigmaAlgebra (EuclideanSpace' (d₁ + d₂))).measurable (φ '' ((Set.univ : Set (EuclideanSpace' d₁)) ×ˢ F)) :=
        h_second (Set.univ : Set (EuclideanSpace' d₁)) isOpen_univ F hF
      exact (ConcreteSigmaAlgebra.sdiff_mem (BorelSigmaAlgebra (EuclideanSpace' (d₁ + d₂)))) hUu (hE F hF)
    · intro En hEn F hF
      have hpre : φ '' ((⋃ n, En n) ×ˢ F) = ⋃ n, φ '' (En n ×ˢ F) := by
        rw [show (⋃ n, En n) ×ˢ F = ⋃ n, (En n ×ˢ F) by ext p; aesop]
        rw [Set.image_iUnion]
      rw [hpre]
      exact (BorelSigmaAlgebra (EuclideanSpace' (d₁ + d₂))).countable_union_mem _ (fun n => hEn n F hF)
  exact h_main E hE F hF

/-- Exercise 1.4.18(i) -/
private noncomputable def sliceMap (d₁ d₂ : ℕ) (x₂ : EuclideanSpace' d₂) : EuclideanSpace' d₁ → EuclideanSpace' (d₁ + d₂) :=
  fun x₁ => (EuclideanSpace'.prod_equiv d₁ d₂).symm (x₁, x₂)

private lemma sliceMap_continuous (d₁ d₂ : ℕ) (x₂ : EuclideanSpace' d₂) : Continuous (sliceMap d₁ d₂ x₂) := by
  have hsymm : Continuous (EuclideanSpace'.prod_equiv d₁ d₂).symm := by
    have h := LinearMap.continuous_of_finiteDimensional (prod_equiv_symm_linear d₁ d₂)
    simpa [prod_equiv_symm_linear] using h
  have hpair : Continuous (fun x₁ : EuclideanSpace' d₁ => (x₁, x₂)) := Continuous.prodMk continuous_id continuous_const
  exact hsymm.comp hpair

theorem BorelSigmaAlgebra.slice_fst {d₁ d₂:ℕ} {E : Set (EuclideanSpace' (d₁+d₂))}
  (hE: (BorelSigmaAlgebra (EuclideanSpace' (d₁+d₂))).measurable E)
  (x₂ : EuclideanSpace' d₂ ) :
  (BorelSigmaAlgebra (EuclideanSpace' d₁)).measurable { x₁ | (EuclideanSpace'.prod_equiv d₁ d₂).symm ⟨ x₁, x₂ ⟩ ∈ E }
  :=
  by
  rw [show { x₁ | (EuclideanSpace'.prod_equiv d₁ d₂).symm ⟨ x₁, x₂ ⟩ ∈ E } = sliceMap d₁ d₂ x₂ ⁻¹' E by rfl]
  have h_ind : ∀ E, (BorelSigmaAlgebra (EuclideanSpace' (d₁ + d₂))).measurable E →
      (BorelSigmaAlgebra (EuclideanSpace' d₁)).measurable (sliceMap d₁ d₂ x₂ ⁻¹' E) := by
    apply ConcreteSigmaAlgebra.induction (X := EuclideanSpace' (d₁ + d₂))
      (F := {U : Set (EuclideanSpace' (d₁ + d₂)) | IsOpen U})
      (P := fun E => (BorelSigmaAlgebra (EuclideanSpace' d₁)).measurable (sliceMap d₁ d₂ x₂ ⁻¹' E))
    · simpa using (BorelSigmaAlgebra (EuclideanSpace' d₁)).empty_mem
    · intro U hU
      rw [Set.mem_setOf_eq] at hU
      apply ConcreteSigmaAlgebra.generated_by_contains
      exact (sliceMap_continuous d₁ d₂ x₂).isOpen_preimage U hU
    · intro E hE
      have hpre : sliceMap d₁ d₂ x₂ ⁻¹' Eᶜ = (sliceMap d₁ d₂ x₂ ⁻¹' E)ᶜ := by simp
      rw [hpre]
      exact (BorelSigmaAlgebra (EuclideanSpace' d₁)).compl_mem _ hE
    · intro E hE
      have hpre : sliceMap d₁ d₂ x₂ ⁻¹' (⋃ n, E n) = ⋃ n, (sliceMap d₁ d₂ x₂ ⁻¹' E n) := by simp
      rw [hpre]
      exact (BorelSigmaAlgebra (EuclideanSpace' d₁)).countable_union_mem _ hE
  exact h_ind E hE

/-- Exercise 1.4.18(i) (slice along second factor). -/
theorem BorelSigmaAlgebra.slice_snd {d₁ d₂:ℕ} {E : Set (EuclideanSpace' (d₁+d₂))}
  (hE: (BorelSigmaAlgebra (EuclideanSpace' (d₁+d₂))).measurable E)
  (x₁ : EuclideanSpace' d₁ ) :
  (BorelSigmaAlgebra (EuclideanSpace' d₂)).measurable { x₂ | (EuclideanSpace'.prod_equiv d₁ d₂).symm ⟨ x₁, x₂ ⟩ ∈ E }
  :=
  by
  let π₂ : EuclideanSpace' d₂ → EuclideanSpace' (d₁ + d₂) := fun x₂ => (EuclideanSpace'.prod_equiv d₁ d₂).symm (x₁, x₂)
  have hcont : Continuous π₂ := by
    have hsymm : Continuous (EuclideanSpace'.prod_equiv d₁ d₂).symm := by
      have h := LinearMap.continuous_of_finiteDimensional (prod_equiv_symm_linear d₁ d₂)
      simpa [prod_equiv_symm_linear] using h
    have hpair : Continuous (fun x₂ : EuclideanSpace' d₂ => (x₁, x₂)) := Continuous.prodMk continuous_const continuous_id
    exact hsymm.comp hpair
  rw [show { x₂ | (EuclideanSpace'.prod_equiv d₁ d₂).symm ⟨ x₁, x₂ ⟩ ∈ E } = π₂ ⁻¹' E by rfl]
  have h_ind : ∀ E, (BorelSigmaAlgebra (EuclideanSpace' (d₁ + d₂))).measurable E →
      (BorelSigmaAlgebra (EuclideanSpace' d₂)).measurable (π₂ ⁻¹' E) := by
    apply ConcreteSigmaAlgebra.induction (X := EuclideanSpace' (d₁ + d₂))
      (F := {U : Set (EuclideanSpace' (d₁ + d₂)) | IsOpen U})
      (P := fun E => (BorelSigmaAlgebra (EuclideanSpace' d₂)).measurable (π₂ ⁻¹' E))
    · simpa using (BorelSigmaAlgebra (EuclideanSpace' d₂)).empty_mem
    · intro U hU
      rw [Set.mem_setOf_eq] at hU
      apply ConcreteSigmaAlgebra.generated_by_contains
      exact hcont.isOpen_preimage U hU
    · intro E hE
      have hpre : π₂ ⁻¹' Eᶜ = (π₂ ⁻¹' E)ᶜ := by simp
      rw [hpre]
      exact (BorelSigmaAlgebra (EuclideanSpace' d₂)).compl_mem _ hE
    · intro E hE
      have hpre : π₂ ⁻¹' (⋃ n, E n) = ⋃ n, (π₂ ⁻¹' E n) := by simp
      rw [hpre]
      exact (BorelSigmaAlgebra (EuclideanSpace' d₂)).countable_union_mem _ hE
  exact h_ind E hE

/-- Exercise 1.4.18(ii) -/
example : ∃ (d₁ d₂ : ℕ) (E : Set (EuclideanSpace' (d₁+d₂))) (x₂ : EuclideanSpace' d₂),
  LebesgueMeasurable E ∧
  ¬ LebesgueMeasurable { x₁ | (EuclideanSpace'.prod_equiv d₁ d₂).symm ⟨ x₁, x₂ ⟩ ∈ E } := by sorry

/-- Exercise 1.4.19 -/
theorem LebesgueMeasurable.sigmaAlgebra_generated_by {d:ℕ} :
  LebesgueMeasurable.sigmaAlgebra d = ConcreteSigmaAlgebra.generated_by ( (BorelSigmaAlgebra (EuclideanSpace' d)).measurableSets ∪ (IsNull.sigmaAlgebra d).measurableSets) :=
  by sorry

@[implicit_reducible]
def ConcreteSigmaAlgebra.measurableSpace {X: Type*} (B: ConcreteSigmaAlgebra X) : MeasurableSpace X := {
  MeasurableSet' := B.measurable
  measurableSet_empty := B.empty_mem
  measurableSet_compl := B.compl_mem
  measurableSet_iUnion := B.countable_union_mem
}

@[implicit_reducible]
def MeasurableSpace.sigmaAlgebra {X: Type*} (M: MeasurableSpace X) : ConcreteSigmaAlgebra X := {
  measurable := M.MeasurableSet'
  empty_mem := M.measurableSet_empty
  compl_mem := M.measurableSet_compl
  union_mem := by
    intro E F hE hF
    let T : ℕ → Set X := fun n => if n = 0 then E else F
    have hT : ∀ n, M.MeasurableSet' (T n) := by
      intro n
      by_cases hn : n = 0
      · simpa [T, hn] using hE
      · simpa [T, hn] using hF
    have hUnion : (⋃ n, T n) = E ∪ F := by
      ext x
      constructor
      · intro hx
        rw [Set.mem_iUnion] at hx
        rcases hx with ⟨n, hn⟩
        by_cases hn0 : n = 0
        · exact Or.inl (by simpa [T, hn0] using hn)
        · exact Or.inr (by simpa [T, hn0] using hn)
      · intro hx
        rcases hx with hx | hx
        · rw [Set.mem_iUnion]
          exact ⟨0, by simp [T, hx]⟩
        · rw [Set.mem_iUnion]
          exact ⟨1, by simp [T, hx]⟩
    rw [← hUnion]
    exact M.measurableSet_iUnion T hT
  countable_union_mem := M.measurableSet_iUnion
}

theorem BorelSigmaAlgebra.le_LebesgueSigmaAlgebra (d:ℕ) : BorelSigmaAlgebra (EuclideanSpace' d) ≤ LebesgueMeasurable.sigmaAlgebra d := by
  unfold BorelSigmaAlgebra
  apply ConcreteSigmaAlgebra.generated_by_le' (LebesgueMeasurable.sigmaAlgebra d)
  intro E hE
  rw [Set.mem_setOf_eq] at hE
  exact IsOpen.measurable hE
