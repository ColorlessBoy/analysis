import Mathlib.Order.BooleanAlgebra.Defs

import Analysis.MeasureTheory.Section_1_3_5

/-!
# Introduction to Measure Theory, Section 1.4.1: Boolean algebras

A companion to (the introduction to) Section 1.4.1 of the book "An introduction to Measure Theory".

-/

/-- Definition 1.4.1 -/
class ConcreteBooleanAlgebra (X:Type*) where
  measurable : Set X → Prop
  empty_mem : measurable (∅ : Set X)
  compl_mem : ∀ E, measurable E → measurable Eᶜ
  union_mem : ∀ E F, measurable E → measurable F → measurable (E ∪ F)

instance ConcreteBooleanAlgebra.instLE (X:Type*) : LE (ConcreteBooleanAlgebra X) :=
  ⟨fun B1 B2 => ∀ E, B1.measurable E → B2.measurable E⟩

instance ConcreteBooleanAlgebra.instPartialOrder (X:Type*) : PartialOrder (ConcreteBooleanAlgebra X) :=
  {
    le_refl := fun B E hE => hE
    le_trans := fun B1 B2 B3 h12 h23 E hE => h23 E (h12 E hE)
    le_antisymm := by
      intro B1 B2 h12 h21
      cases B1
      cases B2
      congr
      funext E
      exact propext ⟨h12 E, h21 E⟩
  }

def ConcreteBooleanAlgebra.measurableSets {X:Type*} (B: ConcreteBooleanAlgebra X) : Set (Set X) :=
  { E | B.measurable E }

@[ext]
theorem ConcreteBooleanAlgebra.ext {X:Type*} {B1 B2 : ConcreteBooleanAlgebra X}
    (h : ∀ E, B1.measurable E ↔ B2.measurable E) : B1 = B2 := by
  cases B1
  cases B2
  congr
  funext E
  exact propext (h E)

/-- Example 1.4.3 -/
instance ConcreteBooleanAlgebra.instOrderTop {X:Type*} : OrderTop (ConcreteBooleanAlgebra X) :=
  {
    top := {
      measurable := fun _ => True
      empty_mem := trivial
      compl_mem := fun _ _ => trivial
      union_mem := fun _ _ _ _ => trivial
    }
    le_top := fun _ _ _ => trivial
  }

/-- Example 1.4.3 (the smallest algebra) -/
instance ConcreteBooleanAlgebra.instOrderBot {X:Type*} : OrderBot (ConcreteBooleanAlgebra X) :=
  {
    bot := {
      measurable := fun E => E = ∅ ∨ E = Set.univ
      empty_mem := by grind
      compl_mem := fun E hE => by grind
      union_mem := fun E F hE hF => by grind
    }
    bot_le := by
      intro B E hE
      rcases hE with hE | hE
      · rw [hE]
        exact B.empty_mem
      · rw [hE]
        simpa using B.compl_mem ∅ B.empty_mem
  }

/-- Exercise 1.4.1 (Elementary algebra) -/
@[implicit_reducible]
def EuclideanSpace'.elementary_boolean_algebra (d:ℕ) : ConcreteBooleanAlgebra (EuclideanSpace' d) :=
  {
    measurable := fun E => IsElementary E ∨ IsElementary Eᶜ
    empty_mem := Or.inl (IsElementary.empty d)
    compl_mem := by
      intro E hE
      rcases hE with hE | hE
      · exact Or.inr (by simpa using hE)
      · exact Or.inl (by simpa using hE)
    union_mem := by
      intro E F hE hF
      rcases hE with hE | hEc
      · rcases hF with hF | hFc
        · exact Or.inl (IsElementary.union hE hF)
        · exact Or.inr (by rw [Set.compl_union, Set.inter_comm]; simpa using IsElementary.sdiff hFc hE)
      · rcases hF with hF | hFc
        · exact Or.inr (by rw [Set.compl_union]; simpa using IsElementary.sdiff hEc hF)
        · exact Or.inr (by rw [Set.compl_union]; exact IsElementary.inter hEc hFc)
  }

/-- Example 1.4.4 (Jordan algebra) -/
@[implicit_reducible]
def JordanMeasurable.boolean_algebra (d:ℕ) : ConcreteBooleanAlgebra (EuclideanSpace' d) :=
  {
    measurable := fun E => JordanMeasurable E ∨ JordanMeasurable Eᶜ
    empty_mem := Or.inl (JordanMeasurable.empty d)
    compl_mem := by
      intro E hE
      rcases hE with hE | hE
      · exact Or.inr (by simpa using hE)
      · exact Or.inl (by simpa using hE)
    union_mem := by
      intro E F hE hF
      rcases hE with hE | hEc
      · rcases hF with hF | hFc
        · exact Or.inl (JordanMeasurable.union hE hF)
        · exact Or.inr (by rw [Set.compl_union, Set.inter_comm]; simpa using JordanMeasurable.sdiff hFc hE)
      · rcases hF with hF | hFc
        · exact Or.inr (by rw [Set.compl_union]; simpa using JordanMeasurable.sdiff hEc hF)
        · exact Or.inr (by simpa [Set.compl_union] using JordanMeasurable.inter hEc hFc)
  }

def JordanMeasurable.gt_elementary_boolean_algebra (d:ℕ) :
  JordanMeasurable.boolean_algebra d ≥ EuclideanSpace'.elementary_boolean_algebra d := by
  intro E hE
  rcases hE with hE | hE
  · exact Or.inl (IsElementary.jordanMeasurable hE)
  · exact Or.inr (IsElementary.jordanMeasurable hE)

/-- Example 1.4.5 (Lebesgue algebra) -/
@[implicit_reducible]
def LebesgueMeasurable.boolean_algebra (d:ℕ) : ConcreteBooleanAlgebra (EuclideanSpace' d) :=
  {
    measurable := fun E => LebesgueMeasurable E
    empty_mem := LebesgueMeasurable.empty
    compl_mem := fun _ hE => LebesgueMeasurable.complement hE
    union_mem := fun _ _ hE hF => LebesgueMeasurable.union hE hF
  }

def LebesgueMeasurable.gt_jordan_boolean_algebra (d:ℕ) :
  LebesgueMeasurable.boolean_algebra d ≥ JordanMeasurable.boolean_algebra d := by
  intro E hE
  rcases hE with hE | hE
  · exact Jordan_measurable.lebesgue hE
  · simpa using LebesgueMeasurable.complement (Jordan_measurable.lebesgue hE)

/-- Example 1.4.6 (Null algebra) -/
theorem IsNull.union {d:ℕ} {E F : Set (EuclideanSpace' d)} (hE : IsNull E) (hF : IsNull F) : IsNull (E ∪ F) := by
  unfold IsNull at *
  apply le_antisymm
  · have hle := Lebesgue_outer_measure.finite_union_le (n := 2)
      (E := fun i : Fin 2 => if (i : ℕ) = 0 then E else F)
    have hsum : (∑ i : Fin 2, Lebesgue_outer_measure (if (i : ℕ) = 0 then E else F)) = 0 := by
      simp [hE, hF]
    have hunion : (⋃ i : Fin 2, (if (i : ℕ) = 0 then E else F)) = E ∪ F := by
      ext x
      simp
    rw [hunion, hsum] at hle
    exact hle
  · exact Lebesgue_outer_measure.nonneg (E ∪ F)

@[implicit_reducible]
def IsNull.boolean_algebra (d:ℕ) : ConcreteBooleanAlgebra (EuclideanSpace' d) :=
  {
    measurable := fun E => IsNull E ∨ IsNull Eᶜ
    empty_mem := Or.inl (Lebesgue_outer_measure.of_empty d)
    compl_mem := by
      intro E hE
      rcases hE with hE | hE
      · exact Or.inr (by simpa using hE)
      · exact Or.inl (by simpa using hE)
    union_mem := by
      intro E F hE hF
      rcases hE with hE | hEc
      · rcases hF with hF | hFc
        · exact Or.inl (IsNull.union hE hF)
        · exact Or.inr (by simpa [Set.compl_union] using IsNull.subset hFc (by intro x hx; exact hx.2))
      · rcases hF with hF | hFc
        · exact Or.inr (by simpa [Set.compl_union] using IsNull.subset hEc (by intro x hx; exact hx.1))
        · exact Or.inr (by simpa [Set.compl_union] using IsNull.subset hEc (by intro x hx; exact hx.1))
  }

def IsNull.lt_lebesgue_boolean_algebra (d:ℕ) :
  IsNull.boolean_algebra d ≤ LebesgueMeasurable.boolean_algebra d := by
  intro E hE
  rcases hE with hE | hE
  · exact IsNull.measurable hE
  · simpa using LebesgueMeasurable.complement (IsNull.measurable hE)

/-- Exercise 1.4.2 (Restriction) -/
theorem ConcreteBooleanAlgebra.inter_mem {X:Type*} (B: ConcreteBooleanAlgebra X) {E F : Set X}
    (hE : B.measurable E) (hF : B.measurable F) : B.measurable (E ∩ F) := by
  have hU : B.measurable (Eᶜ ∪ Fᶜ) := B.union_mem _ _ (B.compl_mem E hE) (B.compl_mem F hF)
  simpa using B.compl_mem (Eᶜ ∪ Fᶜ) hU

@[implicit_reducible]
def ConcreteBooleanAlgebra.restrict {X:Type*} (B: ConcreteBooleanAlgebra X) (A:Set X) : ConcreteBooleanAlgebra A :=
  {
    measurable := fun E => ∃ E' : Set X, B.measurable E' ∧ E = Subtype.val ⁻¹' E'
    empty_mem := by
      refine ⟨∅, B.empty_mem, ?_⟩
      simp
    compl_mem := by
      intro E hE
      rcases hE with ⟨E', hE', rfl⟩
      refine ⟨E'ᶜ, B.compl_mem E' hE', ?_⟩
      exact (Set.preimage_compl (f := Subtype.val) (s := E')).symm
    union_mem := by
      intro E F hE hF
      rcases hE with ⟨E', hE', rfl⟩
      rcases hF with ⟨F', hF', rfl⟩
      refine ⟨E' ∪ F', B.union_mem E' F' hE' hF', ?_⟩
      exact (Set.preimage_union (f := Subtype.val) (s := E') (t := F')).symm
  }

def ConcreteBooleanAlgebra.restrict_iff {X:Type*} {B: ConcreteBooleanAlgebra X} {A:Set X} (h: B.measurable A) (E: Set A) :
  (B.restrict A).measurable E ↔ B.measurable (Subtype.val '' E) := by
  constructor
  · intro hE
    rcases hE with ⟨E', hE', rfl⟩
    have hA : B.measurable (A ∩ E') := B.inter_mem h hE'
    have himg : (Subtype.val : A → X) '' ((Subtype.val : A → X) ⁻¹' E') = A ∩ E' := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x.property, hx⟩
      · rintro ⟨hyA, hyE⟩
        exact ⟨⟨y, hyA⟩, hyE, rfl⟩
    rw [himg]
    exact hA
  · intro hE'
    refine ⟨Subtype.val '' E, hE', ?_⟩
    exact (Set.preimage_image_eq (f := (Subtype.val : A → X)) E Subtype.val_injective).symm

/-- Remark 1.4.2: {name}`ConcreteBooleanAlgebra`s are {name}`BooleanAlgebra`s -/
@[implicit_reducible]
def ConcreteBooleanAlgebra.toBooleanAlgebra {X:Type*} (B: ConcreteBooleanAlgebra X) : BooleanAlgebra (B.measurableSets) :=
{
   sup := fun E F => ⟨E.val ∪ F.val, B.union_mem E.val F.val E.property F.property⟩
   le_sup_left := by
     intro a b
     change a.val ⊆ a.val ∪ b.val
     exact Set.subset_union_left
   le_sup_right := by
     intro a b
     change b.val ⊆ a.val ∪ b.val
     exact Set.subset_union_right
   sup_le := by
     intro a b c hac hbc
     change a.val ⊆ c.val at hac
     change b.val ⊆ c.val at hbc
     change (a.val ∪ b.val) ⊆ c.val
     exact Set.union_subset hac hbc
   inf := fun E F => ⟨E.val ∩ F.val, B.inter_mem (E := E.val) (F := F.val) E.property F.property⟩
   inf_le_left := by
     intro a b
     change (a.val ∩ b.val) ⊆ a.val
     exact Set.inter_subset_left
   inf_le_right := by
     intro a b
     change (a.val ∩ b.val) ⊆ b.val
     exact Set.inter_subset_right
   le_inf := by
     intro a b c hac hbc
     change a.val ⊆ b.val at hac
     change a.val ⊆ c.val at hbc
     change a.val ⊆ (b.val ∩ c.val)
     exact Set.subset_inter hac hbc
   le_sup_inf := by
     intro a b c
     change ((a.val ∪ b.val) ∩ (a.val ∪ c.val)) ⊆ (a.val ∪ (b.val ∩ c.val))
     intro x hx
     rcases hx with ⟨hx1, hx2⟩
     rcases hx1 with hx1 | hx1
     · exact Or.inl hx1
     · rcases hx2 with hx2 | hx2
       · exact Or.inl hx2
       · exact Or.inr ⟨hx1, hx2⟩
   compl := fun E => ⟨E.valᶜ, B.compl_mem E.val E.property⟩
   top := ⟨Set.univ, by simpa using B.compl_mem ∅ B.empty_mem⟩
   bot := ⟨∅, B.empty_mem⟩
   inf_compl_le_bot := by
     intro a
     change (a.val ∩ a.valᶜ) ⊆ ∅
     simp
   top_le_sup_compl := by
     intro a
     change Set.univ ⊆ (a.val ∪ a.valᶜ)
     intro x hx
     by_cases h : x ∈ a.val
     · exact Or.inl h
     · exact Or.inr h
   le_top := by
     intro a
     change a.val ⊆ Set.univ
     simp
   bot_le := by
     intro a
     change ∅ ⊆ a.val
     simp
}

def IsPartition {I X:Type*} (parts: I → Set X) : Prop := (Set.PairwiseDisjoint Set.univ parts) ∧ (⋃ i, parts i = Set.univ)

/-- Example 1.4.7 (Atomic algebra) -/
@[implicit_reducible]
def IsPartition.to_ConcreteBooleanAlgebra {I X: Type*} {atoms: I → Set X} (h_part: IsPartition atoms) : ConcreteBooleanAlgebra X :=
  {
    measurable := fun E => ∃ J: Set I, E = ⋃ i ∈ J, atoms i
    empty_mem := ⟨∅, by simp⟩
    compl_mem := by
      intro E hE
      rcases hE with ⟨J, rfl⟩
      refine ⟨Jᶜ, ?_⟩
      ext x
      constructor
      · intro hx
        have hxuniv : x ∈ ⋃ i, atoms i := by
          rw [h_part.2]
          trivial
        rcases Set.mem_iUnion.mp hxuniv with ⟨i, hxi⟩
        simp [Set.mem_iUnion]
        refine ⟨i, ?_, hxi⟩
        intro hiJ
        have hmem : x ∈ ⋃ i ∈ J, atoms i := by
          simp [Set.mem_iUnion]
          exact ⟨i, hiJ, hxi⟩
        exact hx hmem
      · intro hx
        simp [Set.mem_iUnion] at hx
        rcases hx with ⟨i, hiJc, hxi⟩
        intro hxJ
        simp [Set.mem_iUnion] at hxJ
        rcases hxJ with ⟨j, hjJ, hxj⟩
        have hne : i ≠ j := by
          intro h
          subst h
          exact hiJc hjJ
        have hdisj := h_part.1 (Set.mem_univ i) (Set.mem_univ j) hne
        exact (Set.disjoint_iff.mp hdisj) ⟨hxi, hxj⟩
    union_mem := by
      intro E F hE hF
      rcases hE with ⟨J_E, rfl⟩
      rcases hF with ⟨J_F, rfl⟩
      refine ⟨J_E ∪ J_F, ?_⟩
      rw [Set.biUnion_union]
  }

def IsPartition.discrete (X:Type*) : IsPartition (fun x:X ↦ {x}) := by
  constructor
  · intro a ha b hb hab
    change Disjoint ({a} : Set X) ({b} : Set X)
    rw [Set.disjoint_iff]
    intro x hx
    rcases hx with ⟨hxa, hxb⟩
    rw [Set.mem_singleton_iff] at hxa hxb
    subst hxa
    exact hab hxb
  · ext y
    constructor
    · intro hy
      trivial
    · intro hy
      simp [Set.mem_iUnion]

def ConcreteBooleanAlgebra.top_atomic (X:Type*) : (IsPartition.discrete X).to_ConcreteBooleanAlgebra = ⊤ := by
  apply ConcreteBooleanAlgebra.ext
  intro E
  constructor
  · intro _
    trivial
  · intro _
    refine ⟨E, ?_⟩
    ext y
    simp

def IsPartition.trivial (X:Type*) : IsPartition (fun (_ : Unit) ↦ (Set.univ: Set X)) := by
  constructor
  · intro a ha b hb hab
    exact False.elim (hab (Subsingleton.elim a b))
  · ext y
    simp

def ConcreteBooleanAlgebra.bot_atomic (X:Type*) : (IsPartition.trivial X).to_ConcreteBooleanAlgebra = ⊥ := by
  apply ConcreteBooleanAlgebra.ext
  intro E
  constructor
  · intro hE
    rcases hE with ⟨J, hJ⟩
    by_cases hJempty : J = ∅
    · left
      rw [hJ, hJempty]
      simp
    · right
      rw [hJ]
      have hnonempty : (J : Set Unit).Nonempty := Set.nonempty_iff_ne_empty.mpr hJempty
      ext y
      constructor
      · intro hy
        trivial
      · intro hy
        rcases hnonempty with ⟨x, hx⟩
        simp [Set.mem_iUnion]
        exact ⟨x, hx⟩
  · intro hE
    rcases hE with hE | hE
    · refine ⟨∅, ?_⟩
      rw [hE]
      simp
    · refine ⟨Set.univ, ?_⟩
      rw [hE]
      ext y
      simp

def IsPartition.finer_than {I J X:Type*} {parts_I: I → Set X} {parts_J: J → Set X}
  (_: IsPartition parts_I) (_: IsPartition parts_J) : Prop :=
  ∀ i:I, ∃ j:J, parts_I i ⊆ parts_J j

def IsPartition.mono {I J X:Type*} {parts_I: I → Set X} {parts_J: J → Set X}
  (hI: IsPartition parts_I) (hJ: IsPartition parts_J)
  (h_finer: hI.finer_than hJ) :
  hJ.to_ConcreteBooleanAlgebra ≤ hI.to_ConcreteBooleanAlgebra := by
  intro E hE
  rcases hE with ⟨J₀, rfl⟩
  let I₀ : Set I := {i | ∃ j, j ∈ J₀ ∧ parts_I i ⊆ parts_J j}
  refine ⟨I₀, ?_⟩
  ext x
  constructor
  · intro hx
    simp [Set.mem_iUnion] at hx
    rcases hx with ⟨j, hjJ₀, hxj⟩
    have hxuniv : x ∈ ⋃ i, parts_I i := by
      rw [hI.2]
      trivial
    rcases Set.mem_iUnion.mp hxuniv with ⟨i, hxi⟩
    rcases h_finer i with ⟨j', hj'_sub⟩
    have hj_eq : j' = j := by
      by_contra hne
      have hdisj := hJ.1 (Set.mem_univ j') (Set.mem_univ j) hne
      exact (Set.disjoint_iff.mp hdisj) ⟨hj'_sub hxi, hxj⟩
    simp [Set.mem_iUnion]
    refine ⟨i, ?_, hxi⟩
    exact ⟨j, hjJ₀, by simpa [hj_eq] using hj'_sub⟩
  · intro hx
    simp [Set.mem_iUnion] at hx
    rcases hx with ⟨i, hiI₀, hxi⟩
    rcases hiI₀ with ⟨j, hjJ₀, hsub⟩
    simp [Set.mem_iUnion]
    exact ⟨j, hjJ₀, hsub hxi⟩

def IsPartition.remove_empty {I X:Type*} {parts: I → Set X} (h_part: IsPartition parts) : IsPartition (fun (i:{i:I // parts i ≠ ∅}) ↦ parts i.val) := by
  constructor
  · intro a ha b hb hab
    have hne : a.val ≠ b.val := by
      intro h
      apply hab
      exact Subtype.ext h
    exact h_part.1 (Set.mem_univ a.val) (Set.mem_univ b.val) hne
  · rw [← h_part.2]
    ext x
    constructor
    · intro hx
      rw [Set.mem_iUnion] at hx
      rcases hx with ⟨i, hxi⟩
      rw [Set.mem_iUnion]
      exact ⟨i.val, hxi⟩
    · intro hx
      rw [Set.mem_iUnion] at hx
      rcases hx with ⟨i, hxi⟩
      rw [Set.mem_iUnion]
      refine ⟨⟨i, ?_⟩, hxi⟩
      intro hp
      simp [hp] at hxi

def IsPartition.remove_empty_to_ConcreteBooleanAlgebra {I X:Type*} {parts: I → Set X} (h_part: IsPartition parts) :
  h_part.to_ConcreteBooleanAlgebra =
  h_part.remove_empty.to_ConcreteBooleanAlgebra := by
  apply ConcreteBooleanAlgebra.ext
  intro E
  constructor
  · intro hE
    rcases hE with ⟨J, rfl⟩
    let J' : Set {i : I // parts i ≠ ∅} := {j | j.val ∈ J}
    refine ⟨J', ?_⟩
    ext x
    constructor
    · intro hx
      simp [Set.mem_iUnion] at hx
      rcases hx with ⟨i, hiJ, hxi⟩
      simp [Set.mem_iUnion]
      refine ⟨i, ?_, hxi⟩
      refine ⟨?_, hiJ⟩
      intro hp
      simp [hp] at hxi
    · intro hx
      simp [Set.mem_iUnion] at hx
      rcases hx with ⟨i, hmem, hxi⟩
      rcases hmem with ⟨hne, hmem'⟩
      simp [Set.mem_iUnion]
      exact ⟨i, hmem', hxi⟩
  · intro hE
    rcases hE with ⟨J', rfl⟩
    let J : Set I := {i | ∃ hi : parts i ≠ ∅, (⟨i, hi⟩ : {i : I // parts i ≠ ∅}) ∈ J'}
    refine ⟨J, ?_⟩
    ext x
    constructor
    · intro hx
      simp [Set.mem_iUnion] at hx
      rcases hx with ⟨i, hmem, hxi⟩
      simp [Set.mem_iUnion]
      exact ⟨i, hmem, hxi⟩
    · intro hx
      simp [Set.mem_iUnion] at hx
      rcases hx with ⟨i, hiJ, hxi⟩
      rcases hiJ with ⟨hne, hmem⟩
      simp [Set.mem_iUnion]
      exact ⟨i, ⟨hne, hmem⟩, hxi⟩

/-- A variant of {name}`DyadicCube` with {name}`BoundedInterval.Ico` intervals -/
noncomputable def DyadicCube' {d:ℕ} (n:ℤ) (a: Fin d → ℤ) : Box d := { side := fun i ↦ BoundedInterval.Ico (a i/2^n) ((a i + 1)/2^n) }

/-- Every real number lies in a unique dyadic interval at scale n. -/
lemma dyadic_one_dim {n : ℤ} (_hn : 0 ≤ n) (x : ℝ) :
    ∃! a : ℤ, (a : ℝ) / (2 : ℝ)^n ≤ x ∧ x < ((a : ℝ) + 1) / (2 : ℝ)^n := by
  let a : ℤ := Int.floor (x * (2 : ℝ)^n)
  refine ⟨a, ?_, ?_⟩
  · constructor
    · have hpos : (0 : ℝ) < (2 : ℝ)^n := by positivity
      rw [div_le_iff₀ hpos]
      exact_mod_cast Int.floor_le (x * (2 : ℝ)^n)
    · have hpos : (0 : ℝ) < (2 : ℝ)^n := by positivity
      rw [lt_div_iff₀ hpos]
      exact_mod_cast Int.lt_floor_add_one (x * (2 : ℝ)^n)
  · intro b hb
    have hpos : (0 : ℝ) < (2 : ℝ)^n := by positivity
    have ha_le_x : (a : ℝ) / (2 : ℝ)^n ≤ x := by
      rw [div_le_iff₀ hpos]
      exact_mod_cast Int.floor_le (x * (2 : ℝ)^n)
    have hx_lt_a1 : x < ((a : ℝ) + 1) / (2 : ℝ)^n := by
      rw [lt_div_iff₀ hpos]
      exact_mod_cast Int.lt_floor_add_one (x * (2 : ℝ)^n)
    have hb_le_x : (b : ℝ) ≤ x * (2 : ℝ)^n := (div_le_iff₀ hpos).mp hb.1
    have hx_lt_b1 : x * (2 : ℝ)^n < (b : ℝ) + 1 := (lt_div_iff₀ hpos).mp hb.2
    have ha_le_x2 : (a : ℝ) ≤ x * (2 : ℝ)^n := (div_le_iff₀ hpos).mp ha_le_x
    have hx_lt_a12 : x * (2 : ℝ)^n < (a : ℝ) + 1 := (lt_div_iff₀ hpos).mp hx_lt_a1
    have ha_le_b : a ≤ b := by
      have h : (a : ℝ) < (b : ℝ) + 1 := by linarith
      exact Int.lt_add_one_iff.mp (by exact_mod_cast h)
    have hb_le_a : b ≤ a := by
      have h : (b : ℝ) < (a : ℝ) + 1 := by linarith
      exact Int.lt_add_one_iff.mp (by exact_mod_cast h)
    exact le_antisymm hb_le_a ha_le_b

/-- Example 1.4.8 -/
def DyadicCube'.partition (d n:ℕ) : IsPartition (fun (a: Fin d → ℤ) ↦ (DyadicCube' n a).toSet) := by
  constructor
  · intro a ha b hb hab
    change Disjoint (DyadicCube' (n : ℤ) a).toSet (DyadicCube' (n : ℤ) b).toSet
    rw [Set.disjoint_iff]
    intro x hx
    rcases hx with ⟨hxa, hxb⟩
    have hab' : a = b := by
      funext i
      have hn : 0 ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
      have h1 : (a i : ℝ) / (2 : ℝ)^(n : ℤ) ≤ x i ∧ x i < ((a i : ℝ) + 1) / (2 : ℝ)^(n : ℤ) := by
        simpa [DyadicCube'] using hxa i
      have h2 : (b i : ℝ) / (2 : ℝ)^(n : ℤ) ≤ x i ∧ x i < ((b i : ℝ) + 1) / (2 : ℝ)^(n : ℤ) := by
        simpa [DyadicCube'] using hxb i
      exact (dyadic_one_dim hn (x i)).unique h1 h2
    exact hab hab'
  · ext x
    constructor
    · intro hx
      trivial
    · intro hx
      have hchoice : ∀ i : Fin d, ∃ a : ℤ,
          (a : ℝ) / (2 : ℝ)^(n : ℤ) ≤ x i ∧ x i < ((a : ℝ) + 1) / (2 : ℝ)^(n : ℤ) := by
        intro i
        exact (dyadic_one_dim (by exact_mod_cast Nat.zero_le n) (x i)).exists
      let a : Fin d → ℤ := fun i => (hchoice i).choose
      rw [Set.mem_iUnion]
      refine ⟨a, ?_⟩
      intro i
      simpa [a, DyadicCube'] using (hchoice i).choose_spec

@[implicit_reducible]
def DyadicCube'.boolean_algebra (d n:ℕ) : ConcreteBooleanAlgebra (EuclideanSpace' d) :=
  (DyadicCube'.partition d n).to_ConcreteBooleanAlgebra

/-- Every dyadic cube at the finer scale n is contained in some cube at the coarser scale m, when m is at most n. -/
lemma dyadic_cube_subset {d m n : ℕ} (h : m ≤ n) (a : Fin d → ℤ) :
    ∃ b : Fin d → ℤ, (DyadicCube' (n : ℤ) a).toSet ⊆ (DyadicCube' (m : ℤ) b).toSet := by
  let k : ℕ := n - m
  have hk : (n : ℤ) = (k : ℤ) + (m : ℤ) := by
    rw [← Nat.cast_add]
    congr 1
    exact (Nat.sub_add_cancel h).symm
  let b : Fin d → ℤ := fun i => Int.floor ((a i : ℝ) / (2 : ℝ)^(k : ℤ))
  refine ⟨b, ?_⟩
  intro x hx i
  have h2pos : (0 : ℝ) < (2 : ℝ)^(k : ℤ) := by positivity
  have h2m : (0 : ℝ) < (2 : ℝ)^(m : ℤ) := by positivity
  have h2ne : (2 : ℝ) ≠ 0 := by norm_num
  have hb1 : (b i : ℝ) ≤ (a i : ℝ) / (2 : ℝ)^(k : ℤ) := by
    simpa [b] using Int.floor_le ((a i : ℝ) / (2 : ℝ)^(k : ℤ))
  have hb2 : (a i : ℝ) / (2 : ℝ)^(k : ℤ) < (b i : ℝ) + 1 := by
    simp [b]
  have hb_le_a : (b i : ℤ) * (2 : ℤ)^k ≤ a i := by
    have hb1' : (b i : ℝ) * (2 : ℝ)^(k : ℤ) ≤ (a i : ℝ) := by
      exact (le_div_iff₀ h2pos).mp hb1
    exact_mod_cast hb1'
  have ha_le_b : a i + 1 ≤ (b i + 1) * (2 : ℤ)^k := by
    have hb2' : (a i : ℝ) < ((b i : ℝ) + 1) * (2 : ℝ)^(k : ℤ) := by
      exact (div_lt_iff₀ h2pos).mp hb2
    have hlt : a i < (b i + 1) * (2 : ℤ)^k := by exact_mod_cast hb2'
    omega
  have hxi : (a i : ℝ) / (2 : ℝ)^(n : ℤ) ≤ x i ∧ x i < ((a i : ℝ) + 1) / (2 : ℝ)^(n : ℤ) := by
    simpa [DyadicCube'] using hx i
  have hlb_real : (b i : ℝ) / (2 : ℝ)^(m : ℤ) ≤ (a i : ℝ) / (2 : ℝ)^(n : ℤ) := by
    rw [hk, zpow_add₀ h2ne (k : ℤ) (m : ℤ)]
    have hb_le_a' : (b i : ℝ) * (2 : ℝ)^(k : ℤ) ≤ (a i : ℝ) := by
      have h : (b i : ℝ) * (2 : ℝ)^k ≤ (a i : ℝ) := by exact_mod_cast hb_le_a
      simpa [zpow_natCast] using h
    field_simp [mul_comm, mul_left_comm, mul_assoc, hb_le_a', h2pos.ne', h2m.ne']
    simpa using hb_le_a'
  have hub_real : ((a i : ℝ) + 1) / (2 : ℝ)^(n : ℤ) ≤ ((b i : ℝ) + 1) / (2 : ℝ)^(m : ℤ) := by
    rw [hk, zpow_add₀ h2ne (k : ℤ) (m : ℤ)]
    have ha_le_b' : (a i : ℝ) + 1 ≤ ((b i : ℝ) + 1) * (2 : ℝ)^(k : ℤ) := by
      have h : (a i : ℝ) + 1 ≤ ((b i : ℝ) + 1) * (2 : ℝ)^k := by exact_mod_cast ha_le_b
      simpa [zpow_natCast] using h
    field_simp [mul_comm, mul_left_comm, mul_assoc, ha_le_b', h2pos.ne', h2m.ne']
    simpa [mul_comm] using ha_le_b'
  have hlower : (b i : ℝ) / (2 : ℝ)^(m : ℤ) ≤ x i := by
    exact le_trans hlb_real hxi.1
  have hupper : x i < ((b i : ℝ) + 1) / (2 : ℝ)^(m : ℤ) := by
    exact lt_of_lt_of_le hxi.2 hub_real
  exact (by simpa [DyadicCube'] using ⟨hlower, hupper⟩)

def DyadicCube'.boolean_algebra_mono (d:ℕ) {m n:ℕ} (h: m ≤ n) :
  DyadicCube'.boolean_algebra d m ≤ DyadicCube'.boolean_algebra d n := by
  apply IsPartition.mono (hI := DyadicCube'.partition d n) (hJ := DyadicCube'.partition d m)
  intro a
  exact dyadic_cube_subset (d := d) h a

def IsPartition.relabels {I J X:Type*} {parts_I: I → Set X} (_: IsPartition parts_I) {parts_J : J → Set X} (_: IsPartition parts_J) : Prop := ∃ e : I ≃ J, ∀ i:I, parts_I i = parts_J (e i)

lemma biUnion_image_eq {α β X : Type*} (e : α ≃ β) (S : Set α) (t : β → Set X) :
    (⋃ i ∈ S, t (e i)) = ⋃ j ∈ (e '' S), t j := by
  ext y
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨i, hi, hy⟩
    exact ⟨e i, ⟨i, hi, rfl⟩, hy⟩
  · rintro ⟨j, hj, hy⟩
    rcases hj with ⟨i, hi, hji⟩
    exact ⟨i, hi, by rwa [← hji] at hy⟩

lemma IsPartition.eq_of_parts_eq {I X : Type*} {parts : I → Set X}
    (h : IsPartition parts) {i i' : I} (hne : parts i ≠ ∅) (hEq : parts i = parts i') :
    i = i' := by
  rcases Set.nonempty_iff_ne_empty.mpr hne with ⟨x, hx⟩
  by_contra hne'
  have hdisj := h.1 (Set.mem_univ i) (Set.mem_univ i') hne'
  exact (Set.disjoint_iff.mp hdisj) ⟨hx, by simpa [← hEq] using hx⟩

/-- A nonempty measurable subset of a partition part equals the whole part. -/
lemma IsPartition.subset_part_eq_of_measurable {I X : Type*} {parts : I → Set X}
    (h : IsPartition parts) (i : I) {F : Set X} (hFsub : F ⊆ parts i) (hFne : F ≠ ∅)
    (hFmeas : ∃ J : Set I, F = ⋃ k ∈ J, parts k) : F = parts i := by
  rcases hFmeas with ⟨J, rfl⟩
  rcases Set.nonempty_iff_ne_empty.mpr hFne with ⟨x, hxF⟩
  simp only [Set.mem_iUnion] at hxF
  rcases hxF with ⟨k₀, hk₀J, hx₀⟩
  have hxi : x ∈ parts i := by
    have : x ∈ ⋃ k ∈ J, parts k := by
      simp only [Set.mem_iUnion]
      exact ⟨k₀, hk₀J, hx₀⟩
    exact hFsub this
  have hki : k₀ = i := by
    by_contra hne
    have hdisj := h.1 (Set.mem_univ k₀) (Set.mem_univ i) hne
    exact (Set.disjoint_iff.mp hdisj) ⟨hx₀, hxi⟩
  subst hki
  apply le_antisymm
  · intro y hy
    exact hFsub hy
  · intro y hy
    simp only [Set.mem_iUnion]
    exact ⟨k₀, hk₀J, hy⟩

lemma IsPartition.part_eq_part_of_eq {I J X : Type*} {parts_I : I → Set X} {parts_J : J → Set X}
    (hI : IsPartition parts_I) (hJ : IsPartition parts_J)
    (hEq : hI.to_ConcreteBooleanAlgebra = hJ.to_ConcreteBooleanAlgebra)
    (i : I) (hne : parts_I i ≠ ∅) : ∃ j : J, parts_I i = parts_J j := by
  have hImeas : hI.to_ConcreteBooleanAlgebra.measurable (parts_I i) := ⟨{i}, by simp⟩
  have hJmeas : hJ.to_ConcreteBooleanAlgebra.measurable (parts_I i) := by
    rwa [hEq] at hImeas
  rcases hJmeas with ⟨J₀, hJ₀⟩
  rcases Set.nonempty_iff_ne_empty.mpr hne with ⟨x, hx⟩
  have hxJ : x ∈ ⋃ j ∈ J₀, parts_J j := by rw [← hJ₀]; exact hx
  simp only [Set.mem_iUnion] at hxJ
  rcases hxJ with ⟨j₀, hj₀J₀, hxj₀⟩
  have hsub : parts_J j₀ ⊆ parts_I i := by
    intro y hy
    rw [hJ₀]
    simp only [Set.mem_iUnion]
    exact ⟨j₀, hj₀J₀, hy⟩
  have hne' : parts_J j₀ ≠ ∅ := by
    intro hp
    simp [hp] at hxj₀
  have hIm : hI.to_ConcreteBooleanAlgebra.measurable (parts_J j₀) := by
    have : hJ.to_ConcreteBooleanAlgebra.measurable (parts_J j₀) := ⟨{j₀}, by simp⟩
    rwa [← hEq] at this
  have heq := hI.subset_part_eq_of_measurable i hsub hne' hIm
  exact ⟨j₀, heq.symm⟩

lemma IsPartition.relabels_of_eq {I J X : Type*} {parts_I : I → Set X} {parts_J : J → Set X}
    (hI : IsPartition parts_I) (hJ : IsPartition parts_J)
    (hEq : hI.to_ConcreteBooleanAlgebra = hJ.to_ConcreteBooleanAlgebra) :
    hI.remove_empty.relabels hJ.remove_empty := by
  classical
  let f : {i : I // parts_I i ≠ ∅} → {j : J // parts_J j ≠ ∅} := fun i' =>
    ⟨(hI.part_eq_part_of_eq hJ hEq i'.val i'.property).choose,
     by rw [← (hI.part_eq_part_of_eq hJ hEq i'.val i'.property).choose_spec]; exact i'.property⟩
  let g : {j : J // parts_J j ≠ ∅} → {i : I // parts_I i ≠ ∅} := fun j' =>
    ⟨(hJ.part_eq_part_of_eq hI hEq.symm j'.val j'.property).choose,
     by rw [← (hJ.part_eq_part_of_eq hI hEq.symm j'.val j'.property).choose_spec]; exact j'.property⟩
  refine ⟨{ toFun := f, invFun := g, left_inv := ?_, right_inv := ?_ }, ?_⟩
  · intro i'
    exact Subtype.ext (hI.eq_of_parts_eq (i := (g (f i')).val) (i' := i'.val) (g (f i')).property (by
      calc
        parts_I (g (f i')).val = parts_J (f i').val := by
          simpa [g] using (hJ.part_eq_part_of_eq hI hEq.symm (f i').val (f i').property).choose_spec.symm
        _ = parts_I i'.val :=
          (hI.part_eq_part_of_eq hJ hEq i'.val i'.property).choose_spec.symm))
  · intro j'
    exact Subtype.ext (hJ.eq_of_parts_eq (i := (f (g j')).val) (i' := j'.val) (f (g j')).property (by
      calc
        parts_J (f (g j')).val = parts_I (g j').val := by
          simpa [f] using (hI.part_eq_part_of_eq hJ hEq (g j').val (g j').property).choose_spec.symm
        _ = parts_J j'.val :=
          (hJ.part_eq_part_of_eq hI hEq.symm j'.val j'.property).choose_spec.symm))
  · intro i'
    exact (hI.part_eq_part_of_eq hJ hEq i'.val i'.property).choose_spec

lemma IsPartition.eq_of_relabels {I J X : Type*} {parts_I : I → Set X} {parts_J : J → Set X}
    (hI : IsPartition parts_I) (hJ : IsPartition parts_J)
    (hRel : hI.remove_empty.relabels hJ.remove_empty) :
    hI.to_ConcreteBooleanAlgebra = hJ.to_ConcreteBooleanAlgebra := by
  rcases hRel with ⟨e, he⟩
  have heβ : ∀ i' : {i : I // parts_I i ≠ ∅}, parts_I i'.val = parts_J (e i').val := by
    intro i'
    simpa using he i'
  have heβ' : ∀ j' : {j : J // parts_J j ≠ ∅}, parts_J j'.val = parts_I (e.symm j').val := by
    intro j'
    simpa using (heβ (e.symm j')).symm
  apply ConcreteBooleanAlgebra.ext
  intro E
  constructor
  · intro hmeas
    have hstep : hI.to_ConcreteBooleanAlgebra.measurable E ↔
        hI.remove_empty.to_ConcreteBooleanAlgebra.measurable E := by
      rw [IsPartition.remove_empty_to_ConcreteBooleanAlgebra hI]
    rcases hstep.mp hmeas with ⟨J₀, rfl⟩
    have hbicongr : (⋃ i' ∈ J₀, parts_I i'.val) = ⋃ i' ∈ J₀, parts_J (e i') := by
      ext y
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨i', hi', hy⟩
        rw [heβ i'] at hy
        exact ⟨i', hi', hy⟩
      · rintro ⟨i', hi', hy⟩
        rw [← heβ i'] at hy
        exact ⟨i', hi', hy⟩
    have hE : (⋃ i' ∈ J₀, parts_I i'.val) = ⋃ j ∈ (e '' J₀), parts_J j.val := by
      rw [hbicongr, biUnion_image_eq e J₀ (fun j : {j : J // parts_J j ≠ ∅} => parts_J j.val)]
    have hJrem : hJ.remove_empty.to_ConcreteBooleanAlgebra.measurable (⋃ i' ∈ J₀, parts_I i'.val) := ⟨e '' J₀, hE⟩
    rw [IsPartition.remove_empty_to_ConcreteBooleanAlgebra hJ]
    exact hJrem
  · intro hmeas
    have hstep : hJ.to_ConcreteBooleanAlgebra.measurable E ↔
        hJ.remove_empty.to_ConcreteBooleanAlgebra.measurable E := by
      rw [IsPartition.remove_empty_to_ConcreteBooleanAlgebra hJ]
    rcases hstep.mp hmeas with ⟨J₀, rfl⟩
    have hbicongr : (⋃ j ∈ J₀, parts_J j.val) = ⋃ j ∈ J₀, parts_I (e.symm j).val := by
      ext y
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨j, hj, hy⟩
        rw [heβ' j] at hy
        exact ⟨j, hj, hy⟩
      · rintro ⟨j, hj, hy⟩
        rw [← heβ' j] at hy
        exact ⟨j, hj, hy⟩
    have hE : (⋃ j ∈ J₀, parts_J j.val) = ⋃ i' ∈ (e.symm '' J₀), parts_I i'.val := by
      rw [hbicongr, biUnion_image_eq e.symm J₀ (fun i' : {i : I // parts_I i ≠ ∅} => parts_I i'.val)]
    have hIrem : hI.remove_empty.to_ConcreteBooleanAlgebra.measurable (⋃ j ∈ J₀, parts_J j.val) := ⟨e.symm '' J₀, hE⟩
    rw [IsPartition.remove_empty_to_ConcreteBooleanAlgebra hI]
    exact hIrem

/-- Exercise 1.4.3 (Non-empty atoms of an atomic algebra determined up to relabeling) -/
def IsPartition.boolean_algebra_eq_iff {I J X:Type*} {parts_I: I → Set X} {parts_J: J → Set X}
  (hI: IsPartition parts_I) (hJ: IsPartition parts_J) : hI.to_ConcreteBooleanAlgebra = hJ.to_ConcreteBooleanAlgebra ↔ hI.remove_empty.relabels hJ.remove_empty := by
  constructor
  · intro hEq
    exact hI.relabels_of_eq hJ hEq
  · intro hRel
    exact hI.eq_of_relabels hJ hRel

def IsPartition.no_empty {I X:Type*} {parts: I → Set X} (_: IsPartition parts) : Prop := ∀ i:I, parts i ≠ ∅

def IsPartition.boolean_algebra_eq_iff' {I J X:Type*} {parts_I: I → Set X} {parts_J: J → Set X}
  (hI: IsPartition parts_I) (hJ: IsPartition parts_J) (hIn: hI.no_empty) (hJn: hJ.no_empty) : hI.to_ConcreteBooleanAlgebra = hJ.to_ConcreteBooleanAlgebra ↔ hI.relabels hJ := by
  let e0 : I ≃ {i : I // parts_I i ≠ ∅} :=
    { toFun := fun i => ⟨i, hIn i⟩, invFun := fun i' => i'.val,
      left_inv := by intro i; rfl, right_inv := by intro i'; apply Subtype.ext; rfl }
  let e1 : J ≃ {j : J // parts_J j ≠ ∅} :=
    { toFun := fun j => ⟨j, hJn j⟩, invFun := fun j' => j'.val,
      left_inv := by intro j; rfl, right_inv := by intro j'; apply Subtype.ext; rfl }
  constructor
  · intro hEq
    rcases (hI.boolean_algebra_eq_iff hJ).mp hEq with ⟨e', he'⟩
    let e : I ≃ J := e0.trans (e'.trans e1.symm)
    refine ⟨e, ?_⟩
    intro i
    have h1 := he' (e0 i)
    have hval : e i = (e' (e0 i)).val := by
      change e1.symm (e' (e0 i)) = (e' (e0 i)).val
      rfl
    calc
      parts_I i = parts_J (e' (e0 i)).val := by simpa [e0] using h1
      _ = parts_J (e i) := by rw [← hval]
  · intro hRel
    rcases hRel with ⟨e, he⟩
    let e' : {i : I // parts_I i ≠ ∅} ≃ {j : J // parts_J j ≠ ∅} := (e0.symm.trans e).trans e1
    refine (hI.boolean_algebra_eq_iff hJ).mpr ⟨e', ?_⟩
    intro i'
    have h1 := he (e0.symm i')
    have hval : (e' i').val = e (e0.symm i') := by
      change (e1 (e (e0.symm i'))).val = e (e0.symm i')
      rfl
    calc
      parts_I i'.val = parts_J (e (e0.symm i')) := by simpa [e0] using h1
      _ = parts_J (e' i').val := by rw [hval]

def ConcreteBooleanAlgebra.isAtomic {X:Type*} (B: ConcreteBooleanAlgebra X) : Prop :=
  ∃ (I:Type*) (parts: I → Set X) (hI:IsPartition parts), B = hI.to_ConcreteBooleanAlgebra

/-- Exercise 1.4.7 (Generation by boxes) -/
theorem ConcreteBooleanAlgebra.finset_union_mem {X:Type*} {α : Type*} (B: ConcreteBooleanAlgebra X)
    {S : Finset α} (t : α → Set X) (hS : ∀ E ∈ S, B.measurable (t E)) : B.measurable (⋃ E ∈ S, t E) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simpa using B.empty_mem
  | insert E S' hEnot ih =>
      have hE : B.measurable (t E) := hS E (Finset.mem_insert_self E S')
      have hS' : ∀ E' ∈ S', B.measurable (t E') := fun E' hE' => hS E' (Finset.mem_insert_of_mem hE')
      convert B.union_mem (t E) (⋃ E' ∈ S', t E') hE (ih hS') using 1
      ext x
      simp [Finset.mem_insert]

open Set

namespace ConcreteBooleanAlgebra

universe u

noncomputable section
open Classical

variable {X : Type*}

/-- The finite set of measurable sets of B that contain x. -/
def atom_set (B : ConcreteBooleanAlgebra X) (h_fin : (B.measurableSets).Finite) (x : X) :
    Finset (Set X) :=
  (h_fin.subset (t := B.measurableSets ∩ {E : Set X | x ∈ E}) (by intro E hE; exact hE.1)).toFinset

lemma atom_set_mem {B : ConcreteBooleanAlgebra X} {h_fin : (B.measurableSets).Finite} {x : X}
    {E : Set X} : E ∈ atom_set B h_fin x ↔ E ∈ (B.measurableSets ∩ {E : Set X | x ∈ E}) := by
  unfold atom_set
  exact Set.Finite.mem_toFinset (h_fin.subset (t := B.measurableSets ∩ {E : Set X | x ∈ E}) (by intro E hE; exact hE.1))

/-- The atom of a point: the intersection of all measurable sets containing it. -/
def atom (B : ConcreteBooleanAlgebra X) (h_fin : (B.measurableSets).Finite) (x : X) : Set X :=
  ⋂ E ∈ atom_set B h_fin x, E

/-- A finite intersection of measurable sets is measurable. -/
lemma finset_inter_mem (B : ConcreteBooleanAlgebra X) (s : Finset (Set X))
    (h : ∀ E ∈ s, B.measurable E) : B.measurable (⋂ E ∈ s, E) := by
  induction s using Finset.induction_on with
  | empty =>
      simpa using (B.compl_mem ∅ B.empty_mem)
  | insert E s' hEn ih =>
      have hE : B.measurable E := h E (Finset.mem_insert_self E s')
      have hS' : ∀ E' ∈ s', B.measurable E' := fun E' hE' => h E' (Finset.mem_insert_of_mem hE')
      convert B.inter_mem hE (ih hS') using 1
      ext y
      simp [Finset.mem_insert]

lemma atom_measurable (B : ConcreteBooleanAlgebra X) (h_fin : (B.measurableSets).Finite) (x : X) :
    B.measurable (atom B h_fin x) := by
  unfold atom
  apply finset_inter_mem
  intro E hE
  exact (atom_set_mem.mp hE).1

lemma mem_atom_self (B : ConcreteBooleanAlgebra X) (h_fin : (B.measurableSets).Finite) (x : X) :
    x ∈ atom B h_fin x := by
  unfold atom
  rw [Set.mem_iInter]
  intro E
  rw [Set.mem_iInter]
  intro hE
  exact (atom_set_mem.mp hE).2

lemma atom_subset (B : ConcreteBooleanAlgebra X) (h_fin : (B.measurableSets).Finite) {x : X}
    {E : Set X} (hE : B.measurable E) (hx : x ∈ E) : atom B h_fin x ⊆ E := by
  intro y hy
  exact (Set.mem_iInter.mp (Set.mem_iInter.mp hy E)) (atom_set_mem.mpr ⟨hE, hx⟩)

/-- If z is in the atom of x, the two atoms are equal. -/
lemma atom_eq_of_mem (B : ConcreteBooleanAlgebra X) (h_fin : (B.measurableSets).Finite) {x z : X}
    (hz : z ∈ atom B h_fin x) : atom B h_fin z = atom B h_fin x := by
  apply le_antisymm
  · exact atom_subset B h_fin (atom_measurable B h_fin x) hz
  · apply atom_subset B h_fin (atom_measurable B h_fin z)
    unfold atom
    rw [Set.mem_iInter]
    intro E
    rw [Set.mem_iInter]
    intro hE
    by_contra hxE
    have hEm : B.measurable E := (atom_set_mem.mp hE).1
    have hEc : B.measurable Eᶜ := B.compl_mem E hEm
    have hxEc : x ∈ Eᶜ := (Set.mem_compl_iff E x).mpr hxE
    have hatomEc : atom B h_fin x ⊆ Eᶜ := atom_subset B h_fin hEc hxEc
    have hzEc : z ∈ Eᶜ := hatomEc hz
    exact (Set.mem_compl_iff E z).mp hzEc (atom_set_mem.mp hE).2

/-- The set of all distinct atoms of B. -/
def Atoms (B : ConcreteBooleanAlgebra X) (h_fin : (B.measurableSets).Finite) : Set (Set X) :=
  {E : Set X | B.measurable E ∧ ∃ x : X, E = atom B h_fin x}

lemma Atoms_subset_measurableSets (B : ConcreteBooleanAlgebra X) (h_fin : (B.measurableSets).Finite) :
    Atoms B h_fin ⊆ B.measurableSets := by
  intro E hE
  exact hE.1

lemma Atoms_finite (B : ConcreteBooleanAlgebra X) (h_fin : (B.measurableSets).Finite) :
    (Atoms B h_fin).Finite :=
  h_fin.subset (Atoms_subset_measurableSets B h_fin)

/-- A union of atoms is measurable (there are only finitely many distinct atoms). -/
lemma union_atoms_measurable (B : ConcreteBooleanAlgebra X) (h_fin : (B.measurableSets).Finite)
    {S : Set (Set X)} (hS : S ⊆ Atoms B h_fin) : B.measurable (⋃ E ∈ S, E) := by
  have hSfin : S.Finite := (Atoms_finite B h_fin).subset hS
  have hEq : (⋃ E ∈ S, E) = (⋃ E ∈ hSfin.toFinset, E) := by
    ext y
    constructor
    · intro hy
      rcases (Set.mem_iUnion.mp hy) with ⟨E, hyE⟩
      rcases (Set.mem_iUnion.mp hyE) with ⟨hE, hyE⟩
      rw [Set.mem_iUnion]
      refine ⟨E, ?_⟩
      rw [Set.mem_iUnion]
      refine ⟨?_, hyE⟩
      exact (Set.Finite.mem_toFinset hSfin).mpr hE
    · intro hy
      rcases (Set.mem_iUnion.mp hy) with ⟨E, hyE⟩
      rcases (Set.mem_iUnion.mp hyE) with ⟨hE, hyE⟩
      rw [Set.mem_iUnion]
      refine ⟨E, ?_⟩
      rw [Set.mem_iUnion]
      refine ⟨?_, hyE⟩
      exact (Set.Finite.mem_toFinset hSfin).mp hE
  have hmeas : B.measurable (⋃ E ∈ hSfin.toFinset, E) := by
    apply B.finset_union_mem (fun E : Set X => E)
    intro E hE
    exact (hS ((Set.Finite.mem_toFinset hSfin).mp hE)).1
  rw [hEq]
  exact hmeas

/-- The type of distinct atoms of B. -/
def AtomType {X : Type u} (B : ConcreteBooleanAlgebra X) (h_fin : (B.measurableSets).Finite) : Type u :=
  {A : Set X // A ∈ Atoms B h_fin}

/-- The distinct atoms form a partition of X. -/
lemma atom_partition (B : ConcreteBooleanAlgebra X) (h_fin : (B.measurableSets).Finite) :
    IsPartition (fun A : AtomType B h_fin => A.1) := by
  constructor
  · intro A1 hA1 A2 hA2 hne
    change Disjoint (A1.1 : Set X) (A2.1 : Set X)
    rw [Set.disjoint_iff]
    intro y hy
    rcases hy with ⟨hy1, hy2⟩
    rcases A1.2 with ⟨hA1m, x1, hx1⟩
    rcases A2.2 with ⟨hA2m, x2, hx2⟩
    have hy1' : y ∈ atom B h_fin x1 := by simpa [hx1] using hy1
    have hy2' : y ∈ atom B h_fin x2 := by simpa [hx2] using hy2
    have hatom12 : atom B h_fin x1 = atom B h_fin x2 := by
      calc
        atom B h_fin x1 = atom B h_fin y := (atom_eq_of_mem B h_fin hy1').symm
        _ = atom B h_fin x2 := atom_eq_of_mem B h_fin hy2'
    have hAeq : A1.1 = A2.1 := by
      calc
        A1.1 = atom B h_fin x1 := hx1
        _ = atom B h_fin x2 := hatom12
        _ = A2.1 := hx2.symm
    exact hne (Subtype.ext hAeq)
  · ext y
    constructor
    · intro hy
      trivial
    · intro hy
      rw [Set.mem_iUnion]
      refine ⟨⟨atom B h_fin y, ?_⟩, ?_⟩
      · exact ⟨atom_measurable B h_fin y, ⟨y, rfl⟩⟩
      · exact mem_atom_self B h_fin y

/-- A set is measurable iff it is a union of atoms. -/
lemma measurable_iff_union_atoms (B : ConcreteBooleanAlgebra X) (h_fin : (B.measurableSets).Finite)
    (E : Set X) : B.measurable E ↔
    ∃ J : Set (AtomType B h_fin), E = ⋃ A ∈ J, A.1 := by
  constructor
  · intro hE
    refine ⟨{A : AtomType B h_fin | A.1 ⊆ E}, ?_⟩
    ext y
    constructor
    · intro hyE
      rw [Set.mem_iUnion]
      refine ⟨⟨atom B h_fin y, ?_⟩, ?_⟩
      · exact ⟨atom_measurable B h_fin y, ⟨y, rfl⟩⟩
      · rw [Set.mem_iUnion]
        refine ⟨?_, mem_atom_self B h_fin y⟩
        exact atom_subset B h_fin hE hyE
    · intro hy
      rcases (Set.mem_iUnion.mp hy) with ⟨A, hyA⟩
      rcases (Set.mem_iUnion.mp hyA) with ⟨hA, hyA⟩
      exact hA hyA
  · rintro ⟨J, hE⟩
    let S : Set (Set X) := (fun A : AtomType B h_fin => A.1) '' J
    have hSsub : S ⊆ Atoms B h_fin := by
      intro A' hA'
      rcases hA' with ⟨A, hA, hEq⟩
      simpa [hEq] using A.2
    have hEqS : (⋃ A' ∈ S, A') = ⋃ A ∈ J, A.1 := by
      ext y
      constructor
      · intro hy
        rcases (Set.mem_iUnion.mp hy) with ⟨A', hyA'⟩
        rcases (Set.mem_iUnion.mp hyA') with ⟨hA', hyA'⟩
        rcases hA' with ⟨A, hA, hEq⟩
        rw [Set.mem_iUnion]
        refine ⟨A, ?_⟩
        rw [Set.mem_iUnion]
        refine ⟨hA, ?_⟩
        simpa [hEq] using hyA'
      · intro hy
        rcases (Set.mem_iUnion.mp hy) with ⟨A, hyA⟩
        rcases (Set.mem_iUnion.mp hyA) with ⟨hA, hyA⟩
        rw [Set.mem_iUnion]
        refine ⟨(fun A : {A : Set X // A ∈ Atoms B h_fin} => A.1) A, ?_⟩
        rw [Set.mem_iUnion]
        refine ⟨⟨A, hA, rfl⟩, ?_⟩
        simpa using hyA
    have hmeas : B.measurable (⋃ A' ∈ S, A') := union_atoms_measurable B h_fin hSsub
    rw [hE, ← hEqS]
    exact hmeas

/-- A finite Boolean algebra is atomic. -/
def atomic_of_finite {X : Type u} (B : ConcreteBooleanAlgebra X)
    (h_fin : (B.measurableSets).Finite) : ConcreteBooleanAlgebra.isAtomic.{u, u} B := by
  refine ⟨AtomType B h_fin, fun A : AtomType B h_fin => A.1, ?_, ?_⟩
  · exact atom_partition B h_fin
  · apply ConcreteBooleanAlgebra.ext
    intro E
    exact measurable_iff_union_atoms B h_fin E

/-- The number of measurable sets of a finite Boolean algebra is a power of two. -/
def card_of_finite {X : Type*} (B : ConcreteBooleanAlgebra X)
    (h_fin : (B.measurableSets).Finite) : ∃ n : ℕ, (B.measurableSets).ncard = 2^n := by
  let A : Set (Set X) := Atoms B h_fin
  have hAf : A.Finite := by simpa [A] using Atoms_finite B h_fin
  have h1 : (B.measurableSets).ncard = (Set.powerset A).ncard := by
    refine (Set.ncard_congr (s := Set.powerset A) (t := B.measurableSets)
      (fun S _ => ⋃ E ∈ S, E) ?_ ?_ ?_).symm
    · intro S hS
      exact union_atoms_measurable B h_fin (by simpa [A] using hS)
    · intro S1 S2 hS1 hS2 hUnion
      have hS1sub : S1 ⊆ A := hS1
      have hS2sub : S2 ⊆ A := hS2
      ext E
      constructor
      · intro hE1
        have hEAtoms : E ∈ Atoms B h_fin := hS1sub hE1
        rcases hEAtoms with ⟨hEm, x, hEq⟩
        have hxE : x ∈ E := by rw [hEq]; exact mem_atom_self B h_fin x
        have hxS1 : x ∈ ⋃ E' ∈ S1, E' := by
          rw [Set.mem_iUnion]
          refine ⟨E, ?_⟩
          rw [Set.mem_iUnion]
          exact ⟨hE1, hxE⟩
        have hxS2 : x ∈ ⋃ E' ∈ S2, E' := by simpa [hUnion] using hxS1
        rcases (Set.mem_iUnion.mp hxS2) with ⟨F, hxFS2⟩
        rcases (Set.mem_iUnion.mp hxFS2) with ⟨hF2, hxF⟩
        have hFAtoms : F ∈ Atoms B h_fin := hS2sub hF2
        rcases hFAtoms with ⟨hFm, y, hFq⟩
        have hxFy : x ∈ atom B h_fin y := by simpa [hFq] using hxF
        have hatom : atom B h_fin x = atom B h_fin y := atom_eq_of_mem B h_fin hxFy
        have hEF : E = F := by
          calc
            E = atom B h_fin x := hEq
            _ = atom B h_fin y := hatom
            _ = F := hFq.symm
        simpa [hEF] using hF2
      · intro hE2
        have hEAtoms : E ∈ Atoms B h_fin := hS2sub hE2
        rcases hEAtoms with ⟨hEm, x, hEq⟩
        have hxE : x ∈ E := by rw [hEq]; exact mem_atom_self B h_fin x
        have hxS2 : x ∈ ⋃ E' ∈ S2, E' := by
          rw [Set.mem_iUnion]
          refine ⟨E, ?_⟩
          rw [Set.mem_iUnion]
          exact ⟨hE2, hxE⟩
        have hxS1 : x ∈ ⋃ E' ∈ S1, E' := by simpa [← hUnion] using hxS2
        rcases (Set.mem_iUnion.mp hxS1) with ⟨F, hxFS1⟩
        rcases (Set.mem_iUnion.mp hxFS1) with ⟨hF1, hxF⟩
        have hFAtoms : F ∈ Atoms B h_fin := hS1sub hF1
        rcases hFAtoms with ⟨hFm, y, hFq⟩
        have hxFy : x ∈ atom B h_fin y := by simpa [hFq] using hxF
        have hatom : atom B h_fin x = atom B h_fin y := atom_eq_of_mem B h_fin hxFy
        have hEF : E = F := by
          calc
            E = atom B h_fin x := hEq
            _ = atom B h_fin y := hatom
            _ = F := hFq.symm
        simpa [hEF] using hF1
    · intro E hE
      refine ⟨{E' : Set X | E' ∈ A ∧ E' ⊆ E}, ?_, ?_⟩
      · intro E' hE'
        exact hE'.1
      · ext y
        constructor
        · intro hy
          rcases (Set.mem_iUnion.mp hy) with ⟨E', hyE'⟩
          rcases (Set.mem_iUnion.mp hyE') with ⟨hE', hyE'⟩
          exact hE'.2 hyE'
        · intro hy
          have hyAtoms : atom B h_fin y ∈ A := by
            change atom B h_fin y ∈ Atoms B h_fin
            exact ⟨atom_measurable B h_fin y, ⟨y, rfl⟩⟩
          rw [Set.mem_iUnion]
          refine ⟨atom B h_fin y, ?_⟩
          rw [Set.mem_iUnion]
          refine ⟨⟨hyAtoms, atom_subset B h_fin hE hy⟩, mem_atom_self B h_fin y⟩
  have h2 : (Set.powerset A).ncard = 2 ^ A.ncard := Set.ncard_powerset A hAf
  exact ⟨A.ncard, h1.trans h2⟩

end
end ConcreteBooleanAlgebra

/-- A measurable set with no nonempty proper measurable subset. -/
def ConcreteBooleanAlgebra.IsAtom {X : Type*} (B : ConcreteBooleanAlgebra X) (A : Set X) : Prop :=
  B.measurable A ∧ A ≠ ∅ ∧ ∀ E, B.measurable E → E ⊆ A → E = ∅ ∨ E = A

lemma IsPartition.part_is_atom {I X : Type*} {parts : I → Set X}
    (h : IsPartition parts) (i : I) (hne : parts i ≠ ∅) :
    ConcreteBooleanAlgebra.IsAtom h.to_ConcreteBooleanAlgebra (parts i) := by
  constructor
  · exact ⟨{i}, by simp⟩
  · constructor
    · exact hne
    · intro E hE hsub
      rcases hE with ⟨J, rfl⟩
      by_cases hEempty : (⋃ k ∈ J, parts k) = ∅
      · left
        exact hEempty
      · right
        exact h.subset_part_eq_of_measurable i hsub hEempty ⟨J, rfl⟩

lemma ConcreteBooleanAlgebra.atom_eq_of_inter {X : Type*} (B : ConcreteBooleanAlgebra X)
    {A A' : Set X} (hA : B.IsAtom A) (hA' : B.IsAtom A') (hne : (A ∩ A') ≠ ∅) : A = A' := by
  have hmeet : B.measurable (A ∩ A') := B.inter_mem hA.1 hA'.1
  have h1 := hA.2.2 (A ∩ A') hmeet Set.inter_subset_left
  have h2 := hA'.2.2 (A ∩ A') hmeet Set.inter_subset_right
  rcases h1 with h1 | h1
  · exact False.elim (hne h1)
  · rcases h2 with h2 | h2
    · exact False.elim (hne h2)
    · exact h1.symm.trans h2

/-- An atomic algebra in which every singleton is measurable is the discrete algebra. -/
lemma ConcreteBooleanAlgebra.isAtomic_imp_discrete_of_singleton {X : Type*} (B : ConcreteBooleanAlgebra X)
    (hA : B.isAtomic) (hSing : ∀ x : X, B.measurable {x}) : ∀ E : Set X, B.measurable E := by
  classical
  rcases hA with ⟨I, parts, hI, hB⟩
  have hsing_part : ∀ x : X, ∃ j : I, parts j = {x} := by
    intro x
    have hxmeas : hI.to_ConcreteBooleanAlgebra.measurable ({x} : Set X) := by
      rw [hB] at hSing
      exact hSing x
    rcases hxmeas with ⟨J, hJ⟩
    have hneJ : (⋃ j ∈ J, parts j) ≠ ∅ := by rw [← hJ]; simp
    have hxmem : x ∈ ⋃ j ∈ J, parts j := by
      rw [← hJ]
      exact Set.mem_singleton x
    simp only [Set.mem_iUnion] at hxmem
    rcases hxmem with ⟨j₀, hj₀, hxj₀⟩
    have hsub : parts j₀ ⊆ {x} := by
      intro z hz
      rw [hJ]
      simp only [Set.mem_iUnion]
      exact ⟨j₀, hj₀, hz⟩
    have hparts_sing : parts j₀ = {x} := by
      apply le_antisymm
      · exact hsub
      · intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst z
        exact hxj₀
    exact ⟨j₀, hparts_sing⟩
  let w : X → I := fun x => (hsing_part x).choose
  have hw : ∀ x : X, parts (w x) = {x} := fun x => (hsing_part x).choose_spec
  have hpart_sing : ∀ i : I, parts i ≠ ∅ → ∃ x : X, parts i = {x} := by
    intro i hnei
    rcases Set.nonempty_iff_ne_empty.mpr hnei with ⟨x, hx⟩
    have hAi : hI.to_ConcreteBooleanAlgebra.IsAtom (parts i) := hI.part_is_atom i hnei
    have hAx : hI.to_ConcreteBooleanAlgebra.IsAtom ({x} : Set X) := by
      rw [← hw x]
      exact hI.part_is_atom (w x) (by rw [hw x]; simp)
    have hEq : parts i = {x} := hI.to_ConcreteBooleanAlgebra.atom_eq_of_inter hAi hAx (by
      intro h
      have hxmeet : x ∈ parts i ∩ {x} := ⟨hx, Set.mem_singleton x⟩
      rw [h] at hxmeet
      exact hxmeet)
    exact ⟨x, hEq⟩
  intro E
  have hE : E = ⋃ x ∈ E, parts (w x) := by
    ext y
    constructor
    · intro hy
      simp only [Set.mem_iUnion]
      exact ⟨y, hy, by rw [hw y]; exact Set.mem_singleton y⟩
    · intro hy
      simp only [Set.mem_iUnion] at hy
      rcases hy with ⟨x, hxE, hyx⟩
      rw [hw x] at hyx
      rw [Set.mem_singleton_iff] at hyx
      subst y
      exact hxE
  have hreindex : (⋃ x ∈ E, parts (w x)) = ⋃ i ∈ (w '' E), parts i := by
    ext y
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨x, hxE, hy⟩
      exact ⟨w x, ⟨x, hxE, rfl⟩, hy⟩
    · rintro ⟨i, hi, hy⟩
      rcases hi with ⟨x, hxE, hwi⟩
      exact ⟨x, hxE, by rwa [hwi]⟩
  have hE2 : E = ⋃ i ∈ (w '' E), parts i := by
    calc
      E = ⋃ x ∈ E, parts (w x) := hE
      _ = ⋃ i ∈ (w '' E), parts i := hreindex
  have hmeas : hI.to_ConcreteBooleanAlgebra.measurable E := ⟨w '' E, hE2⟩
  rwa [← hB] at hmeas

open scoped Pointwise

namespace NotAtomic

/-- A singleton set is an elementary set, via the box whose sides are all degenerate. -/
lemma singleton_isElementary {d : ℕ} (x : EuclideanSpace' d) : IsElementary ({x} : Set (EuclideanSpace' d)) := by
  let B : Box d := ⟨fun i => BoundedInterval.Icc (x i) (x i)⟩
  have hB : ({x} : Set (EuclideanSpace' d)) = B.toSet := by
    ext y
    constructor
    · intro hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      simp [B]
    · intro hy
      rw [Set.mem_singleton_iff]
      ext i
      have hyi : y i ∈ Set.Icc (x i) (x i) := by
        have := hy i
        simpa [B] using this
      exact le_antisymm hyi.2 hyi.1
  rw [hB]
  exact IsElementary.box B

/-- Norm of a vector with a single nonzero coordinate at a given slot. -/
lemma coord_vector_norm {d : ℕ} (hd : 0 < d) (c : ℝ) :
    ‖(.toLp 2 (fun j : Fin d => if j = ⟨0, hd⟩ then c else 0) : EuclideanSpace' d)‖ = |c| := by
  rw [PiLp.norm_eq_of_L2]
  have hsum : (∑ i : Fin d, ‖(if i = ⟨0, hd⟩ then c else 0 : ℝ)‖ ^ 2) = |c| ^ 2 := by
    refine Finset.sum_eq_single (f := fun i => ‖(if i = ⟨0, hd⟩ then c else 0 : ℝ)‖ ^ 2)
      (a := (⟨0, hd⟩ : Fin d)) ?_ ?_
    · intro j _ hj
      have : j ≠ ⟨0, hd⟩ := hj
      simp [this]
    · intro hmem
      exact absurd (Finset.mem_univ (⟨0, hd⟩ : Fin d)) hmem
  rw [hsum]
  rw [Real.sqrt_sq_eq_abs (|c|)]
  simp

/-- A set containing points of arbitrarily large norm is unbounded. -/
lemma not_bounded_of_unbounded_coord {d : ℕ} (E : Set (EuclideanSpace' d))
    (hE : ∀ r : ℝ, ∃ x ∈ E, |r| < ‖x‖) : ¬ Bornology.IsBounded E := by
  intro hbdd
  rw [Metric.isBounded_iff_subset_closedBall (0 : EuclideanSpace' d)] at hbdd
  rcases hbdd with ⟨r, hsub⟩
  rcases hE r with ⟨x, hxE, hnorm⟩
  have hxball : x ∈ Metric.closedBall 0 r := hsub hxE
  have hle : ‖x‖ ≤ |r| := by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hxball
    exact le_trans hxball (le_abs_self r)
  linarith

/-- The halfspace of points with nonnegative first coordinate is unbounded. -/
lemma halfspace_unbounded {d : ℕ} (hd : 0 < d) :
    ¬ Bornology.IsBounded ({x : EuclideanSpace' d | 0 ≤ x ⟨0, hd⟩} : Set (EuclideanSpace' d)) := by
  apply not_bounded_of_unbounded_coord
  intro r
  let N : ℝ := |r| + 1
  let x : EuclideanSpace' d := .toLp 2 (fun j : Fin d => if j = ⟨0, hd⟩ then N else 0)
  refine ⟨x, ?_, ?_⟩
  · change 0 ≤ x ⟨0, hd⟩
    have : x ⟨0, hd⟩ = N := by simp [x]
    rw [this]
    have hN : 0 ≤ N := by dsimp [N]; linarith [abs_nonneg r]
    exact hN
  · have hnorm' := coord_vector_norm hd N
    dsimp [x] at hnorm' ⊢
    rw [hnorm']
    have hN : 0 ≤ N := by dsimp [N]; linarith [abs_nonneg r]
    rw [show |N| = N from abs_of_nonneg hN]
    dsimp [N]
    linarith [abs_nonneg r]

/-- The complement of the halfspace of points with nonnegative first coordinate is unbounded. -/
lemma halfspace_compl_unbounded {d : ℕ} (hd : 0 < d) :
    ¬ Bornology.IsBounded ({x : EuclideanSpace' d | 0 ≤ x ⟨0, hd⟩}ᶜ : Set (EuclideanSpace' d)) := by
  apply not_bounded_of_unbounded_coord
  intro r
  let N : ℝ := |r| + 1
  let x : EuclideanSpace' d := .toLp 2 (fun j : Fin d => if j = ⟨0, hd⟩ then -N else 0)
  refine ⟨x, ?_, ?_⟩
  · change ¬ 0 ≤ x ⟨0, hd⟩
    have : x ⟨0, hd⟩ = -N := by simp [x]
    rw [this]
    have hN : 0 < N := by dsimp [N]; linarith [abs_nonneg r]
    linarith
  · have hnorm' := coord_vector_norm hd (-N)
    have hN : 0 ≤ N := by dsimp [N]; linarith [abs_nonneg r]
    dsimp [x] at hnorm' ⊢
    rw [hnorm']
    rw [abs_neg]
    rw [show |N| = N from abs_of_nonneg hN]
    dsimp [N]
    linarith [abs_nonneg r]

/-- A set containing a box of positive volume is not null. -/
lemma not_null_of_contains_box {d : ℕ} (E : Set (EuclideanSpace' d)) (B : Box d)
    (hBvol : B.volume ≠ 0) (hsub : B.toSet ⊆ E) : ¬ IsNull E := by
  intro hnull
  unfold IsNull at hnull
  have hmono : Lebesgue_outer_measure B.toSet ≤ Lebesgue_outer_measure E :=
    Lebesgue_outer_measure.mono hsub
  have hB : Lebesgue_outer_measure B.toSet = (B.volume : EReal) := by
    rw [Lebesgue_outer_measure.elementary _ (IsElementary.box B)]
    simp [IsElementary.measure_of_box]
  rw [hnull] at hmono
  have hle : (B.volume : EReal) ≤ (0 : EReal) := by simpa [hB] using hmono
  have hpos : 0 < B.volume := by
    exact lt_of_le_of_ne' (Box.volume_nonneg B) hBvol
  have hposE : (0 : EReal) < (B.volume : EReal) := EReal.coe_pos.mpr hpos
  exact not_le_of_gt hposE hle

/-- The open unit cube. -/
def unitCube (d : ℕ) : Box d := ⟨fun _ : Fin d => BoundedInterval.Ioc 0 1⟩

/-- The box whose sides are all the open interval from -1 to 0. -/
def negUnitCube (d : ℕ) : Box d := ⟨fun _ : Fin d => BoundedInterval.Ioc (-1) 0⟩

lemma unitCube_volume {d : ℕ} : (unitCube d).volume = 1 := by
  simp [unitCube, Box.volume]

lemma negUnitCube_volume {d : ℕ} : (negUnitCube d).volume = 1 := by
  simp [negUnitCube, Box.volume]

/-- The Vitali cylinder in dimension d: first coordinate in the Vitali set, other coordinates in the closed unit interval. -/
def vitaliCylinder {d : ℕ} (hd : 0 < d) : Set (EuclideanSpace' d) :=
  {x | x ⟨0, hd⟩ ∈ VitaliSet ∧ ∀ j : Fin d, j ≠ ⟨0, hd⟩ → x j ∈ Set.Icc 0 1}

/-- Translation vector with q in the first coordinate and 0 elsewhere. -/
def shiftVec {d : ℕ} (hd : 0 < d) (q : ℝ) : EuclideanSpace' d :=
  .toLp 2 (fun j : Fin d => if j = ⟨0, hd⟩ then q else 0)

/-- Translating the Vitali cylinder by q in the first coordinate. -/
lemma vitaliCylinder_translate {d : ℕ} (hd : 0 < d) (q : ℝ) :
    (vitaliCylinder hd) + {shiftVec hd q} = {x : EuclideanSpace' d | x ⟨0, hd⟩ ∈ VitaliSet + {q} ∧
      ∀ j : Fin d, j ≠ ⟨0, hd⟩ → x j ∈ Set.Icc 0 1} := by
  ext x
  constructor
  · intro hx
    rw [Set.mem_add] at hx
    rcases hx with ⟨y, hy, r, hr, hx_eq⟩
    rw [Set.mem_singleton_iff] at hr
    subst r
    constructor
    · rw [Set.mem_add]
      refine ⟨y ⟨0, hd⟩, hy.1, q, rfl, ?_⟩
      have hc : x ⟨0, hd⟩ = (y + shiftVec hd q) ⟨0, hd⟩ := by
        rw [hx_eq]
      simpa [shiftVec] using hc.symm
    · intro j hj
      have hyj : y j ∈ Set.Icc 0 1 := hy.2 j hj
      have hc : x j = (y + shiftVec hd q) j := by
        rw [hx_eq]
      have hc' : x j = y j := by
        simpa [shiftVec, hj] using hc
      rw [hc']
      exact hyj
  · intro hx
    let y : EuclideanSpace' d := x - shiftVec hd q
    refine ⟨y, ?_, ?_⟩
    · constructor
      · rcases hx with ⟨hx1, hx2⟩
        rw [Set.mem_add] at hx1
        rcases hx1 with ⟨v, hv, r, hr, hv_eq⟩
        rw [Set.mem_singleton_iff] at hr
        subst r
        have hyc : y ⟨0, hd⟩ = v := by
          dsimp [y]
          have h1 : (shiftVec hd q) ⟨0, hd⟩ = q := by simp [shiftVec]
          rw [h1, ← hv_eq]
          ring
        rw [hyc]
        exact hv
      · intro j hj
        have hx2 : x j ∈ Set.Icc 0 1 := hx.2 j hj
        have hyj : y j = x j := by
          dsimp [y]
          have h1 : (x - shiftVec hd q) j = x j - 0 := by simp [shiftVec, hj]
          simpa using h1
        rw [hyj]
        exact hx2
    · refine ⟨shiftVec hd q, rfl, ?_⟩
      ext i
      simp [y, shiftVec]

/-- The closed unit cube. -/
def closedUnitCube (d : ℕ) : Box d := ⟨fun _ : Fin d => BoundedInterval.Icc 0 1⟩

/-- A box of measure 3: first side from -1 to 2, other sides from 0 to 1. -/
def lebesgueBigBox (d : ℕ) (hd : 0 < d) : Box d :=
  ⟨fun j => if j = ⟨0, hd⟩ then BoundedInterval.Icc (-1) 2 else BoundedInterval.Icc 0 1⟩

/-- Translates of the Vitali set by distinct rationals are disjoint. -/
lemma vitali_translates_disjoint {q₁ q₂ : ℚ} (h : q₁ ≠ q₂) :
    Disjoint ((VitaliSet : Set ℝ) + {(q₁ : ℝ)}) ((VitaliSet : Set ℝ) + {(q₂ : ℝ)}) := by
  rw [Set.disjoint_iff]
  intro z hz
  rcases hz with ⟨hz1, hz2⟩
  rw [Set.mem_add] at hz1 hz2
  obtain ⟨x1, hx1, r1, hr1, hz1_eq⟩ := hz1
  obtain ⟨x2, hx2, r2, hr2, hz2_eq⟩ := hz2
  rw [Set.mem_singleton_iff] at hr1 hr2
  subst hr1 hr2
  have hz_eq : x1 + (q₁ : ℝ) = x2 + (q₂ : ℝ) := by
    calc
      x1 + (q₁ : ℝ) = z := hz1_eq
      _ = x2 + (q₂ : ℝ) := hz2_eq.symm
  have h_same_coset : QuotientAddGroup.mk (s := Rat.addSubgroup) x1 =
      QuotientAddGroup.mk (s := Rat.addSubgroup) x2 := by
    rw [QuotientAddGroup.eq]
    use q₁ - q₂
    simp only [Rat.cast_sub]
    linarith
  obtain ⟨c1, hc1⟩ := hx1
  obtain ⟨c2, hc2⟩ := hx2
  have hc1_spec := (coset_intersects_unit_interval c1).choose_spec.2
  have hc2_spec := (coset_intersects_unit_interval c2).choose_spec.2
  have hc_eq : c1 = c2 := by
    rw [← hc1, ← hc2] at h_same_coset
    rw [← hc1_spec, ← hc2_spec]
    exact h_same_coset
  subst hc_eq
  have hv_eq : x1 = x2 := hc1.symm.trans hc2
  have hq_eq : (q₁ : ℝ) = q₂ := by linarith [hz_eq, hv_eq]
  have hqi_eq : q₁ = q₂ := Rat.cast_injective hq_eq
  exact h hqi_eq

/-- Translates of the Vitali cylinder by distinct rationals are pairwise disjoint. -/
lemma vitaliCylinder_translates_disjoint {d : ℕ} (hd : 0 < d) (f : ℕ → ℚ)
    (hf_inj : Function.Injective f) :
    Set.univ.PairwiseDisjoint (fun n : ℕ => (vitaliCylinder hd) + {shiftVec hd (f n : ℝ)}) := by
  intro i _ j _ hij
  change Disjoint ((vitaliCylinder hd) + {shiftVec hd (f i : ℝ)})
    ((vitaliCylinder hd) + {shiftVec hd (f j : ℝ)})
  rw [Set.disjoint_iff]
  intro z hz
  rcases hz with ⟨hz1, hz2⟩
  rw [vitaliCylinder_translate] at hz1 hz2
  have h1 : z ⟨0, hd⟩ ∈ (VitaliSet : Set ℝ) + {(f i : ℝ)} := hz1.1
  have h2 : z ⟨0, hd⟩ ∈ (VitaliSet : Set ℝ) + {(f j : ℝ)} := hz2.1
  have hne : (f i : ℚ) ≠ f j := by
    intro h
    exact hij (hf_inj h)
  exact (Set.disjoint_iff.mp (vitali_translates_disjoint hne)) ⟨h1, h2⟩

/-- The closed unit cube has Lebesgue measure 1. -/
lemma closedUnitCube_measure (d : ℕ) : Lebesgue_measure (closedUnitCube d).toSet = (1 : EReal) := by
  unfold Lebesgue_measure
  rw [Lebesgue_outer_measure.elementary _ (IsElementary.box (closedUnitCube d))]
  simp [IsElementary.measure_of_box, closedUnitCube, Box.volume, BoundedInterval.length]

/-- The box of measure 3 has volume 3. -/
lemma lebesgueBigBox_volume {d : ℕ} (hd : 0 < d) : (lebesgueBigBox d hd).volume = 3 := by
  rw [Box.volume]
  have hprod : (∏ j : Fin d, |(lebesgueBigBox d hd).side j|ₗ) = |(lebesgueBigBox d hd).side ⟨0, hd⟩|ₗ := by
    refine Finset.prod_eq_single (f := fun j : Fin d => |(lebesgueBigBox d hd).side j|ₗ)
      (a := (⟨0, hd⟩ : Fin d)) ?_ ?_
    · intro j _ hj
      have : j ≠ ⟨0, hd⟩ := hj
      have hside : (lebesgueBigBox d hd).side j = BoundedInterval.Icc 0 1 := by
        simp [lebesgueBigBox, this]
      change ((lebesgueBigBox d hd).side j).length = 1
      rw [hside]
      norm_num [BoundedInterval.length]
    · intro hmem
      exact absurd (Finset.mem_univ (⟨0, hd⟩ : Fin d)) hmem
  rw [hprod]
  have hside : (lebesgueBigBox d hd).side ⟨0, hd⟩ = BoundedInterval.Icc (-1) 2 := by
    simp [lebesgueBigBox]
  rw [hside]
  norm_num [BoundedInterval.length]

/-- The Vitali cylinder is not Lebesgue measurable. -/
theorem not_lebesgue_measurable_cylinder {d : ℕ} (hd : 0 < d) :
    ¬ LebesgueMeasurable (vitaliCylinder hd) := by
  let C : Set (EuclideanSpace' d) := vitaliCylinder hd
  intro hC_meas
  have hQ_countable : Set.Countable {q : ℚ | q ∈ Set.Icc (-1:ℚ) 1} := rat_Icc_countable
  have hQ_inf : Set.Infinite {q : ℚ | q ∈ Set.Icc (-1:ℚ) 1} :=
    Set.Icc_infinite (by norm_num : (-1:ℚ) < 1)
  haveI : Infinite {q : ℚ | q ∈ Set.Icc (-1:ℚ) 1} := hQ_inf.to_subtype
  haveI : Countable {q : ℚ | q ∈ Set.Icc (-1:ℚ) 1} := hQ_countable.to_subtype
  haveI denumQ : Denumerable {q : ℚ | q ∈ Set.Icc (-1:ℚ) 1} := (nonempty_denumerable _).some
  let eqvQ : {q : ℚ | q ∈ Set.Icc (-1:ℚ) 1} ≃ ℕ := Denumerable.eqv _
  let f : ℕ → ℚ := fun n => (eqvQ.symm n : ℚ)
  have hf_inj : Function.Injective f := Subtype.val_injective.comp eqvQ.symm.injective
  have hf_mem : ∀ n, f n ∈ Set.Icc (-1:ℚ) 1 := fun n => (eqvQ.symm n).2
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
  let T : ℕ → Set (EuclideanSpace' d) := fun n => C + {shiftVec hd (f n : ℝ)}
  have hmes : ∀ n, LebesgueMeasurable (T n) := fun n =>
    (LebesgueMeasurable.translate C (shiftVec hd (f n : ℝ))).mp hC_meas
  have hdisj : Set.univ.PairwiseDisjoint T := by
    simpa [T, C] using (vitaliCylinder_translates_disjoint hd f hf_inj)
  have h_union_measure : Lebesgue_measure (⋃ n, T n) = ∑' n, Lebesgue_measure (T n) :=
    Lebesgue_measure.countable_union hmes hdisj
  have h_translate_measure : ∀ n, Lebesgue_measure (T n) = Lebesgue_measure C := fun n =>
    Lebesgue_measure.translate (shiftVec hd (f n : ℝ)) hC_meas
  by_cases hC_zero : Lebesgue_measure C = 0
  · have h_sum_zero : ∑' n, Lebesgue_measure (T n) = 0 := by
      simp only [h_translate_measure, hC_zero]
      exact tsum_zero
    rw [h_sum_zero] at h_union_measure
    have h_cover : (closedUnitCube d).toSet ⊆ ⋃ n, T n := by
      intro z hz
      have hz0 : z ⟨0, hd⟩ ∈ Set.Icc (0 : ℝ) 1 := by
        have := hz ⟨0, hd⟩
        simpa [closedUnitCube] using this
      have hz_covered := unit_interval_covered_by_translates hz0
      rw [Set.mem_iUnion] at hz_covered
      rcases hz_covered with ⟨q, hq⟩
      rw [Set.mem_iUnion] at hq
      rcases hq with ⟨hq_bound, hz_mem⟩
      have hq_in_range : q ∈ {r : ℚ | r ∈ Set.Icc (-1 : ℚ) 1} := hq_bound
      rw [hf_range] at hq_in_range
      rcases hq_in_range with ⟨n, rfl⟩
      rw [Set.mem_iUnion]
      refine ⟨n, ?_⟩
      change z ∈ (vitaliCylinder hd) + {shiftVec hd (f n : ℝ)}
      rw [vitaliCylinder_translate]
      constructor
      · exact hz_mem
      · intro j hj
        have := hz j
        simpa [closedUnitCube] using this
    have h_ge_one : (1 : EReal) ≤ Lebesgue_measure (⋃ n, T n) := by
      calc
        (1 : EReal) ≤ Lebesgue_measure (closedUnitCube d).toSet := by
          rw [closedUnitCube_measure d]
        _ ≤ Lebesgue_measure (⋃ n, T n) := Lebesgue_outer_measure.mono h_cover
    rw [h_union_measure] at h_ge_one
    exact absurd h_ge_one (by norm_num : ¬ (1 : EReal) ≤ 0)
  · have hC_nonneg : 0 ≤ Lebesgue_measure C := Lebesgue_outer_measure.nonneg C
    have hC_pos : 0 < Lebesgue_measure C := by
      cases' (hC_nonneg.lt_or_eq) with h h
      · exact h
      · exact absurd h.symm hC_zero
    have h_sum_top : ∑' n, Lebesgue_measure (T n) = ⊤ := by
      simp only [h_translate_measure]
      exact EReal.tsum_const_eq_top_of_pos hC_pos
    rw [h_sum_top] at h_union_measure
    have h_bounded : ⋃ n, T n ⊆ (lebesgueBigBox d hd).toSet := by
      intro z hz
      rw [Set.mem_iUnion] at hz
      rcases hz with ⟨n, hz_n⟩
      have hz_n' : z ∈ (vitaliCylinder hd) + {shiftVec hd (f n : ℝ)} := by
        simpa [T, C] using hz_n
      rw [vitaliCylinder_translate] at hz_n'
      simp only [Box.mem_toSet, lebesgueBigBox]
      intro j
      by_cases hj : j = ⟨0, hd⟩
      · subst hj
        rcases hz_n'.1 with ⟨v, hv, r, hr, hv_eq⟩
        rw [Set.mem_singleton_iff] at hr
        subst r
        have hv01 : v ∈ Set.Icc (0 : ℝ) 1 := VitaliSet_subset_unit_interval hv
        have hq_bound : (f n : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by
          constructor
          · exact_mod_cast hf_mem n |>.1
          · exact_mod_cast hf_mem n |>.2
        rw [← hv_eq]
        simp
        constructor
        · linarith [hv01.1, hq_bound.1]
        · linarith [hv01.2, hq_bound.2]
      · have : z j ∈ Set.Icc 0 1 := hz_n'.2 j hj
        simpa [hj] using this
    have h_le_three : Lebesgue_measure (⋃ n, T n) ≤ (3 : EReal) := by
      calc
        Lebesgue_measure (⋃ n, T n) ≤ Lebesgue_measure (lebesgueBigBox d hd).toSet :=
          Lebesgue_outer_measure.mono h_bounded
        _ = 3 := by
          unfold Lebesgue_measure
          rw [Lebesgue_outer_measure.elementary _ (IsElementary.box (lebesgueBigBox d hd))]
          rw [IsElementary.measure_of_box, lebesgueBigBox_volume hd]
          rfl
    rw [h_union_measure] at h_le_three
    have h_three_ne_top : (3 : EReal) ≠ ⊤ := by decide
    exact h_three_ne_top (le_antisymm le_top h_le_three)

end NotAtomic

def EuclideanSpace'.elementary_boolean_algebra_not_atomic (d:ℕ) (hd: d ≥ 1) : ¬ (EuclideanSpace'.elementary_boolean_algebra d).isAtomic := by
  intro hA
  have hd0 : 0 < d := by omega
  have hsing : ∀ x : EuclideanSpace' d, (EuclideanSpace'.elementary_boolean_algebra d).measurable {x} := by
    intro x
    exact Or.inl (NotAtomic.singleton_isElementary x)
  have hdisc := ConcreteBooleanAlgebra.isAtomic_imp_discrete_of_singleton
    (EuclideanSpace'.elementary_boolean_algebra d) hA hsing
  let E : Set (EuclideanSpace' d) := {x | 0 ≤ x ⟨0, hd0⟩}
  have hE : ¬ (EuclideanSpace'.elementary_boolean_algebra d).measurable E := by
    change ¬ (IsElementary E ∨ IsElementary Eᶜ)
    rw [not_or]
    constructor
    · intro hElem
      exact (NotAtomic.halfspace_unbounded hd0) (IsElementary.isBounded hElem)
    · intro hElem
      exact (NotAtomic.halfspace_compl_unbounded hd0) (IsElementary.isBounded hElem)
  exact hE (hdisc E)

def JordanMeasurable.boolean_algebra_not_atomic (d:ℕ) (hd: d ≥ 1) : ¬ (JordanMeasurable.boolean_algebra d).isAtomic := by
  intro hA
  have hd0 : 0 < d := by omega
  have hsing : ∀ x : EuclideanSpace' d, (JordanMeasurable.boolean_algebra d).measurable {x} := by
    intro x
    exact Or.inl (IsElementary.jordanMeasurable (NotAtomic.singleton_isElementary x))
  have hdisc := ConcreteBooleanAlgebra.isAtomic_imp_discrete_of_singleton
    (JordanMeasurable.boolean_algebra d) hA hsing
  let E : Set (EuclideanSpace' d) := {x | 0 ≤ x ⟨0, hd0⟩}
  have hE : ¬ (JordanMeasurable.boolean_algebra d).measurable E := by
    change ¬ (JordanMeasurable E ∨ JordanMeasurable Eᶜ)
    rw [not_or]
    constructor
    · intro hJ
      exact (NotAtomic.halfspace_unbounded hd0) hJ.1
    · intro hJ
      exact (NotAtomic.halfspace_compl_unbounded hd0) hJ.1
  exact hE (hdisc E)

def LebesgueMeasurable.boolean_algebra_not_atomic (d:ℕ) (hd: d ≥ 1) : ¬ (LebesgueMeasurable.boolean_algebra d).isAtomic := by
  intro hA
  have hd0 : 0 < d := by omega
  have hsing : ∀ x : EuclideanSpace' d, (LebesgueMeasurable.boolean_algebra d).measurable {x} := by
    intro x
    exact IsNull.measurable (Lebesgue_outer_measure.singleton_zero (by omega : d ≠ 0) x)
  have hdisc := ConcreteBooleanAlgebra.isAtomic_imp_discrete_of_singleton
    (LebesgueMeasurable.boolean_algebra d) hA hsing
  let E : Set (EuclideanSpace' d) := NotAtomic.vitaliCylinder hd0
  have hE : ¬ (LebesgueMeasurable.boolean_algebra d).measurable E := by
    change ¬ LebesgueMeasurable E
    exact NotAtomic.not_lebesgue_measurable_cylinder hd0
  exact hE (hdisc E)

def IsNull.boolean_algebra_not_atomic (d:ℕ) (hd: d ≥ 1) : ¬ (IsNull.boolean_algebra d).isAtomic := by
  intro hA
  have hd0 : 0 < d := by omega
  have hsing : ∀ x : EuclideanSpace' d, (IsNull.boolean_algebra d).measurable {x} := by
    intro x
    exact Or.inl (Lebesgue_outer_measure.singleton_zero (by omega : d ≠ 0) x)
  have hdisc := ConcreteBooleanAlgebra.isAtomic_imp_discrete_of_singleton
    (IsNull.boolean_algebra d) hA hsing
  let E : Set (EuclideanSpace' d) := {x | 0 < x ⟨0, hd0⟩}
  have hE : ¬ (IsNull.boolean_algebra d).measurable E := by
    change ¬ (IsNull E ∨ IsNull Eᶜ)
    rw [not_or]
    constructor
    · apply NotAtomic.not_null_of_contains_box E (NotAtomic.unitCube d)
      · simp [NotAtomic.unitCube, Box.volume]
      · intro x hx
        change 0 < x ⟨0, hd0⟩
        have hx0 : x ⟨0, hd0⟩ ∈ Set.Ioc (0 : ℝ) 1 := by
          have := hx ⟨0, hd0⟩
          simpa [NotAtomic.unitCube] using this
        exact hx0.1
    · apply NotAtomic.not_null_of_contains_box Eᶜ (NotAtomic.negUnitCube d)
      · simp [NotAtomic.negUnitCube, Box.volume]
      · intro x hx
        change ¬ 0 < x ⟨0, hd0⟩
        have hx0 : x ⟨0, hd0⟩ ∈ Set.Ioc (-1 : ℝ) 0 := by
          have := hx ⟨0, hd0⟩
          simpa [NotAtomic.negUnitCube] using this
        exact not_lt_of_ge hx0.2
  exact hE (hdisc E)


/-- Exercise 1.4.6 (Intersection of algebras) -/
instance ConcreteBooleanAlgebra.instInfSet {X:Type*} : InfSet (ConcreteBooleanAlgebra X) :=
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
        }
  }

@[implicit_reducible]
def ConcreteBooleanAlgebra.generated_by {X:Type*} (F: Set (Set X)) : ConcreteBooleanAlgebra X :=
  sInf { B | ∀ E ∈ F, B.measurable E }

lemma ConcreteBooleanAlgebra.generated_by_contains {X:Type*} {F : Set (Set X)} {E : Set X}
    (hE : E ∈ F) : (ConcreteBooleanAlgebra.generated_by F).measurable E := by
  intro B hB
  exact hB E hE

lemma ConcreteBooleanAlgebra.generated_by_le {X:Type*} {F : Set (Set X)} (B : ConcreteBooleanAlgebra X)
    (hB : ∀ E ∈ F, B.measurable E) : ConcreteBooleanAlgebra.generated_by F ≤ B := by
  intro E hE
  exact hE B hB

/-- Definition 1.4.10 (Generation of algebras) -/
instance ConcreteBooleanAlgebra.instSupSet {X:Type*} : SupSet (ConcreteBooleanAlgebra X) :=
  {
      sSup S := ConcreteBooleanAlgebra.generated_by (⋃ B ∈ S, B.measurableSets)
  }

instance ConcreteBooleanAlgebra.instCompleteLattice {X:Type*} : CompleteLattice (ConcreteBooleanAlgebra X) :=
  {
    sup := fun B1 B2 => sSup ({B1, B2} : Set (ConcreteBooleanAlgebra X))
    le_sup_left := by
      intro B1 B2 E hE
      apply ConcreteBooleanAlgebra.generated_by_contains
      simp
      exact Or.inl hE
    le_sup_right := by
      intro B1 B2 E hE
      apply ConcreteBooleanAlgebra.generated_by_contains
      simp
      exact Or.inr hE
    sup_le := by
      intro B1 B2 C h1 h2
      change ConcreteBooleanAlgebra.generated_by
        (⋃ B ∈ ({B1, B2} : Set (ConcreteBooleanAlgebra X)), B.measurableSets) ≤ C
      apply ConcreteBooleanAlgebra.generated_by_le C
      intro E hE
      simp at hE
      rcases hE with hE | hE
      · exact h1 E hE
      · exact h2 E hE
    inf := fun B1 B2 => sInf ({B1, B2} : Set (ConcreteBooleanAlgebra X))
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
        apply ConcreteBooleanAlgebra.generated_by_contains
        simp
        exact ⟨B, hB, hE⟩
      · intro C hC
        apply ConcreteBooleanAlgebra.generated_by_le C
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

/-- Example 1.4.11 -/
instance ConcreteBooleanAlgebra.eq_generated_by_iff {X:Type*} (F: Set (Set X)) : (∃ (B : ConcreteBooleanAlgebra X), B.measurableSets = F) ↔ (ConcreteBooleanAlgebra.generated_by F).measurableSets = F := by
  constructor
  · intro hB
    rcases hB with ⟨B, hBF⟩
    have hg : ConcreteBooleanAlgebra.generated_by F = B := by
      apply le_antisymm
      · apply ConcreteBooleanAlgebra.generated_by_le B
        intro E hE
        rw [← hBF] at hE
        exact hE
      · intro E hE
        apply ConcreteBooleanAlgebra.generated_by_contains
        rw [← hBF]
        exact hE
    rw [hg, hBF]
  · intro hEq
    exact ⟨ConcreteBooleanAlgebra.generated_by F, hEq⟩


instance EuclideanSpace'.elementary_boolean_algebra_generated_by_boxes (d:ℕ) : EuclideanSpace'.elementary_boolean_algebra d =
  ConcreteBooleanAlgebra.generated_by (Box.toSet '' Set.univ) := by
  apply le_antisymm
  · intro E hE
    rcases hE with hE | hE
    · rcases hE with ⟨S, rfl⟩
      apply ConcreteBooleanAlgebra.finset_union_mem (ConcreteBooleanAlgebra.generated_by (Box.toSet '' Set.univ)) (fun B : Box d => (↑B : Set (EuclideanSpace' d)))
      intro B hB
      apply ConcreteBooleanAlgebra.generated_by_contains
      change ∃ B' : Box d, B' ∈ Set.univ ∧ (B' : Set (EuclideanSpace' d)) = (↑B : Set (EuclideanSpace' d))
      exact ⟨B, trivial, rfl⟩
    · rcases hE with ⟨S, hE⟩
      have hEc : (ConcreteBooleanAlgebra.generated_by (Box.toSet '' Set.univ)).measurable (⋃ B ∈ S, (↑B : Set (EuclideanSpace' d))) := by
        apply ConcreteBooleanAlgebra.finset_union_mem (ConcreteBooleanAlgebra.generated_by (Box.toSet '' Set.univ)) (fun B : Box d => (↑B : Set (EuclideanSpace' d)))
        intro B hB
        apply ConcreteBooleanAlgebra.generated_by_contains
        change ∃ B' : Box d, B' ∈ Set.univ ∧ (B' : Set (EuclideanSpace' d)) = (↑B : Set (EuclideanSpace' d))
        exact ⟨B, trivial, rfl⟩
      have hEcomp : (ConcreteBooleanAlgebra.generated_by (Box.toSet '' Set.univ)).measurable ((⋃ B ∈ S, (↑B : Set (EuclideanSpace' d)))ᶜ) :=
        (ConcreteBooleanAlgebra.generated_by (Box.toSet '' Set.univ)).compl_mem (⋃ B ∈ S, (↑B : Set (EuclideanSpace' d))) hEc
      simpa [hE.symm] using hEcomp
  · apply ConcreteBooleanAlgebra.generated_by_le (EuclideanSpace'.elementary_boolean_algebra d)
    intro E hE
    rcases hE with ⟨B, _, rfl⟩
    exact Or.inl (IsElementary.box B)

/-- Exercise 1.4.9 (Recursive definition of generated Boolean algebra)-/
def step {X} (G : Set (Set X)) : Set (Set X) :=
  { E : Set X | (∃ S : Finset G, E = ⋃ (H:S), H) ∨ (∃ S : Finset G, E = (⋃ (H:S), H)ᶜ) }

def iterate {X} (F : Set (Set X)) (n : ℕ) : Set (Set X) :=
  Nat.rec (motive := fun _ => Set (Set X)) F (fun _ G => step G) n

lemma singleton_union {X} {G : Set (Set X)} {E : Set X} (hE : E ∈ G) :
    E = ⋃ H : ({⟨E, hE⟩} : Finset G), (H : Set X) := by
  ext x
  simp [Set.mem_iUnion]

lemma pair_union {X} {G : Set (Set X)} {E E' : Set X} (hE : E ∈ G) (hE' : E' ∈ G) :
    E ∪ E' = ⋃ H : ({⟨E, hE⟩, ⟨E', hE'⟩} : Finset G), (H : Set X) := by
  ext x
  simp [Set.mem_iUnion]

lemma iterate_mono {X} (F : Set (Set X)) (n : ℕ) : iterate F n ⊆ iterate F (n + 1) := by
  intro E hE
  simp [iterate]
  left
  refine ⟨({⟨E, hE⟩} : Finset (iterate F n)), ?_⟩
  exact singleton_union hE

lemma iterate_mono_le {X} (F : Set (Set X)) {n m : ℕ} (h : n ≤ m) : iterate F n ⊆ iterate F m := by
  induction m with
  | zero =>
      have hn : n = 0 := by omega
      simp [hn]
  | succ m ih =>
      by_cases hnm : n ≤ m
      · exact Subset.trans (ih hnm) (iterate_mono F m)
      · have hn : n = m + 1 := by omega
        simp [hn]

lemma iterate_union {X} (F : Set (Set X)) {n : ℕ} {E E' : Set X}
    (hE : E ∈ iterate F n) (hE' : E' ∈ iterate F n) : E ∪ E' ∈ iterate F (n + 1) := by
  simp [iterate]
  left
  refine ⟨({⟨E, hE⟩, ⟨E', hE'⟩} : Finset (iterate F n)), ?_⟩
  exact pair_union hE hE'

lemma iterate_compl {X} (F : Set (Set X)) {n : ℕ} {E : Set X} (hE : E ∈ iterate F n) :
    Eᶜ ∈ iterate F (n + 1) := by
  cases n with
  | zero =>
      simp [iterate]
      right
      refine ⟨({⟨E, hE⟩} : Finset F), ?_⟩
      ext x
      simp
  | succ m =>
      simp [iterate] at hE
      rcases hE with hE | hE
      · rcases hE with ⟨S, hS⟩
        have hc : Eᶜ ∈ iterate F (m + 1) := by
          simp [iterate]
          right
          refine ⟨S, ?_⟩
          rw [hS]
        exact iterate_mono F (m + 1) hc
      · rcases hE with ⟨S, hS⟩
        have hc : Eᶜ ∈ iterate F (m + 1) := by
          simp [iterate]
          left
          refine ⟨S, ?_⟩
          rw [hS]
          simp
        exact iterate_mono F (m + 1) hc

lemma finset_union_eq {X} {G : Set (Set X)} (S : Finset G) :
    (⋃ (H : S), H) = ⋃ H ∈ S, (H : Set X) := by
  ext x
  simp [Set.mem_iUnion]

def ConcreteBooleanAlgebra.generated_by_eq {X:Type*} (F: Set (Set X)) :
  (ConcreteBooleanAlgebra.generated_by F).measurableSets =
  ⋃ n, Nat.rec (motive := fun _ ↦ Set (Set X)) F (fun _n G ↦ { E: Set X | (∃ S: Finset G, E = ⋃ (H:S), H) ∨ (∃ S: Finset G, E = (⋃ (H:S), H)ᶜ) }) n := by
  let U : ConcreteBooleanAlgebra X := {
    measurable := fun E => E ∈ ⋃ n, iterate F n
    empty_mem := by
      rw [Set.mem_iUnion]
      refine ⟨1, ?_⟩
      simp [iterate]
      left
      refine ⟨(∅ : Finset F), ?_⟩
      simp
    compl_mem := by
      intro E hE
      rw [Set.mem_iUnion] at hE
      rcases hE with ⟨n, hn⟩
      rw [Set.mem_iUnion]
      exact ⟨n + 1, iterate_compl F hn⟩
    union_mem := by
      intro E E' hE hE'
      rw [Set.mem_iUnion] at hE hE'
      rcases hE with ⟨n, hn⟩
      rcases hE' with ⟨m, hm⟩
      let N : ℕ := max n m
      have hnN : E ∈ iterate F N := iterate_mono_le F (le_max_left n m) hn
      have hmN : E' ∈ iterate F N := iterate_mono_le F (le_max_right n m) hm
      rw [Set.mem_iUnion]
      exact ⟨N + 1, iterate_union F hnN hmN⟩
  }
  have hU_F : ∀ E ∈ F, U.measurable E := by
    intro E hE
    change E ∈ ⋃ n, iterate F n
    rw [Set.mem_iUnion]
    exact ⟨0, hE⟩
  have h_iter_subset : ∀ n, iterate F n ⊆ (ConcreteBooleanAlgebra.generated_by F).measurableSets := by
    intro n
    induction n with
    | zero =>
        intro E hE
        exact ConcreteBooleanAlgebra.generated_by_contains hE
    | succ m ih =>
        intro E hE
        simp [iterate] at hE
        rcases hE with hE | hE
        · rcases hE with ⟨S, rfl⟩
          rw [finset_union_eq S]
          apply ConcreteBooleanAlgebra.finset_union_mem (ConcreteBooleanAlgebra.generated_by F)
            (fun H : {H : Set X // H ∈ iterate F m} => H.1)
          intro H hH
          exact ih H.property
        · rcases hE with ⟨S, rfl⟩
          have hU : (ConcreteBooleanAlgebra.generated_by F).measurable (⋃ (H : S), H) := by
            rw [finset_union_eq S]
            apply ConcreteBooleanAlgebra.finset_union_mem (ConcreteBooleanAlgebra.generated_by F)
              (fun H : {H : Set X // H ∈ iterate F m} => H.1)
            intro H hH
            exact ih H.property
          exact (ConcreteBooleanAlgebra.generated_by F).compl_mem _ hU
  have hgen_le_U : ConcreteBooleanAlgebra.generated_by F ≤ U := by
    apply ConcreteBooleanAlgebra.generated_by_le U
    exact hU_F
  ext E
  constructor
  · intro hE
    exact hgen_le_U E hE
  · intro hE
    rw [Set.mem_iUnion] at hE
    rcases hE with ⟨n, hn⟩
    exact h_iter_subset n hn


  
