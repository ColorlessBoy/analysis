import Mathlib.Tactic

/-!
# Analysis I, Section 11.1: Partitions

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Bounded intervals and partitions.
- Length of an interval; the lengths of a partition sum to the length of the interval.

-/

namespace Chapter11

inductive BoundedInterval where
  | Ioo (a b:ℝ) : BoundedInterval
  | Icc (a b:ℝ) : BoundedInterval
  | Ioc (a b:ℝ) : BoundedInterval
  | Ico (a b:ℝ) : BoundedInterval

open BoundedInterval

/-- There is a technical issue in that this coercion is not injective: the empty set is represented by multiple bounded intervals.  This causes some of the statements in this section to be a little uglier than necessary. -/
@[coe]
def BoundedInterval.toSet (I: BoundedInterval) : Set ℝ := match I with
  | Ioo a b => .Ioo a b
  | Icc a b => .Icc a b
  | Ioc a b => .Ioc a b
  | Ico a b => .Ico a b

instance BoundedInterval.inst_coeSet : Coe BoundedInterval (Set ℝ) where
  coe := toSet

instance BoundedInterval.instEmpty : EmptyCollection BoundedInterval where
  emptyCollection := Ioo 0 0

@[simp]
theorem BoundedInterval.coe_empty : ((∅ : BoundedInterval):Set ℝ) = ∅ := by
  simp [toSet]

open Classical in
/-- This is to make {name}`Finset`s of {name}`BoundedInterval`s work properly -/
noncomputable instance BoundedInterval.decidableEq : DecidableEq BoundedInterval := instDecidableEqOfLawfulBEq

@[simp]
theorem BoundedInterval.set_Ioo (a b:ℝ) : (Ioo a b : Set ℝ) = .Ioo a b := by rfl

@[simp]
theorem BoundedInterval.set_Icc (a b:ℝ) : (Icc a b : Set ℝ) = .Icc a b := by rfl

@[simp]
theorem BoundedInterval.set_Ioc (a b:ℝ) : (Ioc a b : Set ℝ) = .Ioc a b := by rfl

@[simp]
theorem BoundedInterval.set_Ico (a b:ℝ) : (Ico a b : Set ℝ) = .Ico a b := by rfl

-- Definition 11.1.1
#check Set.ordConnected_def

/-- Examples 11.1.3 -/
example : (Set.Icc 1 2 : Set ℝ).OrdConnected := Set.ordConnected_Icc

example : (Set.Ioo 1 2 : Set ℝ).OrdConnected := Set.ordConnected_Ioo

example : ¬(Set.Icc 1 2 ∪ Set.Icc 3 4 : Set ℝ).OrdConnected := by
  intro h
  have h2 : (2 : ℝ) ∈ Set.Icc (1 : ℝ) (2 : ℝ) := by norm_num
  have h3 : (3 : ℝ) ∈ Set.Icc (3 : ℝ) (4 : ℝ) := by norm_num
  have hmem2 : (2 : ℝ) ∈ (Set.Icc 1 2 ∪ Set.Icc 3 4) := Or.inl h2
  have hmem3 : (3 : ℝ) ∈ (Set.Icc 1 2 ∪ Set.Icc 3 4) := Or.inr h3
  have hord := (Set.ordConnected_def.mp h) hmem2 hmem3
  have h25 : (2.5 : ℝ) ∈ Set.Icc (2 : ℝ) (3 : ℝ) := by
    constructor <;> norm_num
  have h25mem := hord h25
  rcases h25mem with (hIcc | hIcc)
  · rcases hIcc with ⟨h1, h2⟩
    linarith
  · rcases hIcc with ⟨h1, h2⟩
    linarith

example : (∅:Set ℝ).OrdConnected := Set.ordConnected_empty

example (x:ℝ) : ({x}: Set ℝ).OrdConnected := by infer_instance

/-- Lemma 11.1.4 / Exercise 11.1.1 -/
theorem Bornology.IsBounded.of_boundedInterval (I: BoundedInterval) : Bornology.IsBounded (I:Set ℝ) := by
  cases I with
  | Ioo a b => simpa [toSet] using Metric.isBounded_Ioo a b
  | Icc a b => simpa [toSet] using Metric.isBounded_Icc a b
  | Ioc a b => simpa [toSet] using Metric.isBounded_Ioc a b
  | Ico a b => simpa [toSet] using Metric.isBounded_Ico a b

theorem BoundedInterval.ordConnected_iff (X:Set ℝ) : Bornology.IsBounded X ∧ X.OrdConnected ↔ ∃ I: BoundedInterval, X = I := by
  constructor
  · rintro ⟨hBounded, hOrd⟩
    have hbdd := (isBounded_iff_bddBelow_bddAbove (s := X)).mp hBounded
    rcases hbdd with ⟨hBelow, hAbove⟩
    have hPreconn : IsPreconnected X :=
      (isPreconnected_iff_ordConnected (s := X)).mpr hOrd
    have hmem := IsPreconnected.mem_intervals hPreconn
    have hcases : X = Set.Icc (sInf X) (sSup X) ∨ X = Set.Ico (sInf X) (sSup X) ∨ X = Set.Ioc (sInf X) (sSup X) ∨ X = Set.Ioo (sInf X) (sSup X) ∨ X = Set.Ici (sInf X) ∨ X = Set.Ioi (sInf X) ∨ X = Set.Iic (sSup X) ∨ X = Set.Iio (sSup X) ∨ X = Set.univ ∨ X = (∅ : Set ℝ) := by
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
    rcases hcases with (h | h | h | h | h | h | h | h | h | h)
    · refine ⟨Icc (sInf X) (sSup X), ?_⟩
      simpa [BoundedInterval.set_Icc] using h
    · refine ⟨Ico (sInf X) (sSup X), ?_⟩
      simpa [BoundedInterval.set_Ico] using h
    · refine ⟨Ioc (sInf X) (sSup X), ?_⟩
      simpa [BoundedInterval.set_Ioc] using h
    · refine ⟨Ioo (sInf X) (sSup X), ?_⟩
      simpa [BoundedInterval.set_Ioo] using h
    · rw [h] at hAbove
      exact absurd hAbove (not_bddAbove_Ici (sInf X))
    · rw [h] at hAbove
      exact absurd hAbove (not_bddAbove_Ioi (sInf X))
    · rw [h] at hBelow
      exact absurd hBelow (not_bddBelow_Iic (sSup X))
    · rw [h] at hBelow
      exact absurd hBelow (not_bddBelow_Iio (sSup X))
    · rw [h] at hAbove
      exact absurd hAbove not_bddAbove_univ
    · refine ⟨Ioo 0 0, ?_⟩
      simpa [BoundedInterval.set_Ioo, toSet] using h
  · rintro ⟨I, hX⟩
    constructor
    · rw [hX]
      exact Bornology.IsBounded.of_boundedInterval I
    · rw [hX]
      cases I with
      | Ioo a b => exact Set.ordConnected_Ioo
      | Icc a b => exact Set.ordConnected_Icc
      | Ioc a b => exact Set.ordConnected_Ioc
      | Ico a b => exact Set.ordConnected_Ico

/-- Corollary 11.1.6 / Exercise 11.1.2 -/
theorem BoundedInterval.inter (I J: BoundedInterval) : ∃ K : BoundedInterval, (I:Set ℝ) ∩ (J:Set ℝ) = (K:Set ℝ) := by
  have hb : Bornology.IsBounded ((I : Set ℝ) ∩ (J : Set ℝ)) :=
    Bornology.IsBounded.subset (Bornology.IsBounded.of_boundedInterval I) Set.inter_subset_left
  have ho : ((I : Set ℝ) ∩ (J : Set ℝ)).OrdConnected := by
    have hI : ((I : Set ℝ)).OrdConnected := ((BoundedInterval.ordConnected_iff (I : Set ℝ)).mpr ⟨I, rfl⟩).2
    have hJ : ((J : Set ℝ)).OrdConnected := ((BoundedInterval.ordConnected_iff (J : Set ℝ)).mpr ⟨J, rfl⟩).2
    exact Set.OrdConnected.inter hI hJ
  exact (BoundedInterval.ordConnected_iff _).mp ⟨hb, ho⟩

noncomputable instance BoundedInterval.instInter : Inter BoundedInterval where
  inter I J := (inter I J).choose

@[simp]
theorem BoundedInterval.inter_eq (I J: BoundedInterval) : (I ∩ J : BoundedInterval) = (I:Set ℝ) ∩ (J:Set ℝ)  :=
  (BoundedInterval.inter I J).choose_spec.symm

example :
  (Icc 2 4 ∩ Icc 4 6) = (Icc 4 4 : Set ℝ) := by
  ext x; simp [Set.mem_Icc]; grind

instance BoundedInterval.instMembership : Membership ℝ BoundedInterval where
  mem I x := x ∈ (I:Set ℝ)

theorem BoundedInterval.mem_iff (I: BoundedInterval) (x:ℝ) :
  x ∈ I ↔ x ∈ (I:Set ℝ) := by rfl

instance BoundedInterval.instSubset : HasSubset BoundedInterval where
  Subset I J := ∀ x, x ∈ I → x ∈ J

theorem BoundedInterval.subset_iff (I J: BoundedInterval) :
  I ⊆ J ↔ (I:Set ℝ) ⊆ (J:Set ℝ) := by rfl

abbrev BoundedInterval.a (I: BoundedInterval) : ℝ := match I with
  | Ioo a _ => a
  | Icc a _ => a
  | Ioc a _ => a
  | Ico a _ => a

abbrev BoundedInterval.b (I: BoundedInterval) : ℝ := match I with
  | Ioo _ b => b
  | Icc _ b => b
  | Ioc _ b => b
  | Ico _ b => b

theorem BoundedInterval.subset_Icc (I: BoundedInterval) : I ⊆ Icc I.a I.b := match I with
  | Ioo _ _ => by simp [subset_iff, Set.Ioo_subset_Icc_self]
  | Icc _ _ => by simp [subset_iff]
  | Ioc _ _ => by simp [subset_iff, Set.Ioc_subset_Icc_self]
  | Ico _ _ => by simp [subset_iff, Set.Ico_subset_Icc_self]

theorem BoundedInterval.Ioo_subset (I: BoundedInterval) : Ioo I.a I.b ⊆ I := match I with
  | Ioo _ _ => by simp [subset_iff]
  | Icc _ _ => by simp [subset_iff, Set.Ioo_subset_Icc_self]
  | Ioc _ _ => by simp [subset_iff, Set.Ioo_subset_Ioc_self]
  | Ico _ _ => by simp [subset_iff, Set.Ioo_subset_Ico_self]

instance BoundedInterval.instTrans : IsTrans BoundedInterval (· ⊆ ·) where
  trans I J K hIJ hJK := by grind [subset_iff]

@[simp]
theorem BoundedInterval.mem_inter (I J: BoundedInterval) (x:ℝ) :
  x ∈ (I ∩ J : BoundedInterval) ↔ x ∈ I ∧ x ∈ J := by simp [mem_iff]

abbrev BoundedInterval.length (I: BoundedInterval) : ℝ := max (I.b - I.a) 0

/-- Using ||ₗ subscript here to not override || -/
macro:max atomic("|" noWs) a:term noWs "|ₗ" : term => `(BoundedInterval.length $a)

example : |Icc 3 5|ₗ = 2 := by
  norm_num

example : |Ioo 3 5|ₗ = 2 := by
  norm_num

example : |Icc 5 5|ₗ = 0 := by
  norm_num

theorem BoundedInterval.length_nonneg (I: BoundedInterval) : 0 ≤ |I|ₗ := by
  simp

theorem BoundedInterval.empty_of_lt {I: BoundedInterval} (h: I.b < I.a) : (I:Set ℝ) = ∅ := by
  cases I with
  | Ioo _ _ => simp [le_of_lt h]
  | Icc _ _ => simp [h]
  | Ioc _ _ => simp [le_of_lt h]
  | Ico _ _ => simp [le_of_lt h]

theorem BoundedInterval.length_of_empty {I: BoundedInterval} (hI: (I:Set ℝ) = ∅) : |I|ₗ = 0 := by
  have hle : I.b ≤ I.a := by
    cases I with
    | Ioo a b =>
      have h := Set.Ioo_eq_empty_iff.mp (by simpa [toSet] using hI)
      exact not_lt.mp h
    | Icc a b =>
      have h := Set.Icc_eq_empty_iff.mp (by simpa [toSet] using hI)
      exact le_of_lt (not_le.mp h)
    | Ioc a b =>
      have h := (Set.Ioc_eq_empty_iff (a := b) (b := a)).mp (by simpa [toSet] using hI)
      exact not_lt.mp h
    | Ico a b =>
      have h := Set.Ico_eq_empty_iff.mp (by simpa [toSet] using hI)
      exact not_lt.mp h
  rw [length, max_eq_right (sub_nonpos.mpr hle)]

theorem BoundedInterval.length_of_subsingleton {I: BoundedInterval} : Subsingleton (I:Set ℝ) ↔ |I|ₗ = 0 := by
  constructor
  · intro h
    have hle : I.b ≤ I.a := by
      by_contra! hlt
      have ha_lt_b : I.a < I.b := hlt
      have hx_mem : ((2*I.a + I.b) / 3) ∈ (I : Set ℝ) := by
        cases I with
        | Ioo a b => exact Set.mem_Ioo.mpr ⟨by nlinarith, by nlinarith⟩
        | Icc a b => exact Set.mem_Icc.mpr ⟨by nlinarith, by nlinarith⟩
        | Ioc a b => exact Set.mem_Ioc.mpr ⟨by nlinarith, by nlinarith⟩
        | Ico a b => exact Set.mem_Ico.mpr ⟨by nlinarith, by nlinarith⟩
      have hy_mem : ((I.a + 2*I.b) / 3) ∈ (I : Set ℝ) := by
        cases I with
        | Ioo a b => exact Set.mem_Ioo.mpr ⟨by nlinarith, by nlinarith⟩
        | Icc a b => exact Set.mem_Icc.mpr ⟨by nlinarith, by nlinarith⟩
        | Ioc a b => exact Set.mem_Ioc.mpr ⟨by nlinarith, by nlinarith⟩
        | Ico a b => exact Set.mem_Ico.mpr ⟨by nlinarith, by nlinarith⟩
      have hneq : (2*I.a + I.b) / 3 ≠ (I.a + 2*I.b) / 3 := by
        nlinarith
      let x' : (I : Set ℝ) := ⟨(2*I.a + I.b) / 3, hx_mem⟩
      let y' : (I : Set ℝ) := ⟨(I.a + 2*I.b) / 3, hy_mem⟩
      have h_eq : x' = y' := Subsingleton.elim x' y'
      have h_val_eq : x'.val = y'.val := congr_arg Subtype.val h_eq
      exact hneq h_val_eq
    rw [length, max_eq_right (sub_nonpos.mpr hle)]
  · intro h
    have hle : I.b ≤ I.a := by
      by_contra! hlt
      have hpos : I.b - I.a > 0 := sub_pos.mpr hlt
      rw [length] at h
      have hmax : max (I.b - I.a) 0 = I.b - I.a := max_eq_left (by linarith)
      rw [hmax] at h
      linarith
    cases I with
    | Ioo a b =>
      have h_empty : (Ioo a b : Set ℝ) = ∅ := by
        ext x; simp; intro hx; linarith
      simp [h_empty]
    | Icc a b =>
      simpa using Set.subsingleton_Icc_of_ge hle
    | Ioc a b =>
      have h_empty : (Ioc a b : Set ℝ) = ∅ := by
        ext x; simp; intro hx; linarith
      simp [h_empty]
    | Ico a b =>
      have h_empty : (Ico a b : Set ℝ) = ∅ := by
        ext x; simp; intro hx; linarith
      simp [h_empty]

theorem BoundedInterval.dist_le_length {I:BoundedInterval} {x y:ℝ} (hx: x ∈ I) (hy: y ∈ I) : |x - y| ≤ |I|ₗ := by
  apply subset_Icc I at hx; apply subset_Icc I at hy; simp_all [mem_iff, abs_le']; grind

abbrev BoundedInterval.joins (K I J: BoundedInterval) : Prop := (I:Set ℝ) ∩ (J:Set ℝ) = ∅
  ∧ (K:Set ℝ) = (I:Set ℝ) ∪ (J:Set ℝ) ∧ |K|ₗ = |I|ₗ + |J|ₗ

theorem BoundedInterval.join_Icc_Ioc {a b c:ℝ} (hab: a ≤ b) (hbc: b ≤ c) : (Icc a c).joins (Icc a b) (Ioc b c) := by
  simp_all [joins]; grind

theorem BoundedInterval.join_Icc_Ioo {a b c:ℝ} (hab: a ≤ b) (hbc: b < c) : (Ico a c).joins (Icc a b) (Ioo b c) := by
  simp_all [joins, le_of_lt hbc]; grind

theorem BoundedInterval.join_Ioc_Ioc {a b c:ℝ} (hab: a ≤ b) (hbc: b ≤ c) : (Ioc a c).joins (Ioc a b) (Ioc b c) := by
  simp_all [joins]; grind

theorem BoundedInterval.join_Ioc_Ioo {a b c:ℝ} (hab: a ≤ b) (hbc: b < c) : (Ioo a c).joins (Ioc a b) (Ioo b c) := by
  simp_all [joins, le_of_lt hbc]; grind

theorem BoundedInterval.join_Ico_Icc {a b c:ℝ} (hab: a ≤ b) (hbc: b ≤ c) : (Icc a c).joins (Ico a b) (Icc b c) := by
  simp_all [joins]; grind

theorem BoundedInterval.join_Ico_Ico {a b c:ℝ} (hab: a ≤ b) (hbc: b ≤ c) : (Ico a c).joins (Ico a b) (Ico b c) := by
  simp_all [joins]; grind

theorem BoundedInterval.join_Ioo_Icc {a b c:ℝ} (hab: a < b) (hbc: b ≤ c) : (Ioc a c).joins (Ioo a b) (Icc b c) := by
  simp_all [joins, le_of_lt hab]; grind

theorem BoundedInterval.join_Ioo_Ico {a b c:ℝ} (hab: a < b) (hbc: b ≤ c) : (Ioo a c).joins (Ioo a b) (Ico b c) := by
  simp_all [joins, le_of_lt hab]; grind

@[ext]
structure Partition (I: BoundedInterval) where
  intervals : Finset BoundedInterval
  exists_unique (x:ℝ) (hx : x ∈ I) : ∃! J, J ∈ intervals ∧ x ∈ J
  contains (J : BoundedInterval) (hJ : J ∈ intervals) : J ⊆ I

#check Partition.mk

instance Partition.instMembership (I: BoundedInterval) : Membership BoundedInterval (Partition I) where
  mem P J := J ∈ P.intervals

instance Partition.instBot (I: BoundedInterval) : Bot (Partition I) where
  bot := {
    intervals := {I}
    exists_unique x hx := by apply ExistsUnique.intro I <;> grind
    contains := by grind [subset_iff]
    }

@[simp]
theorem Partition.intervals_of_bot (I:BoundedInterval) : (⊥:Partition I).intervals = {I} := by
  rfl

noncomputable abbrev Partition.join {I J K:BoundedInterval} (P: Partition I) (Q: Partition J) (h: K.joins I J) : Partition K
:=
{
  intervals := P.intervals ∪ Q.intervals
  exists_unique x hx := by
    have := congr(x ∈ $(h.1))
    simp [mem_iff, h.2] at hx; obtain hx | hx := hx
    . choose L _ _ using (P.exists_unique _ hx).exists
      apply ExistsUnique.intro L (by grind)
      intro K ⟨hK, hxK⟩; simp at hK; obtain _ | hKQ := hK
      map_tacs [apply (P.exists_unique _ hx).unique; apply (K.subset_iff _).mp (Q.contains _ hKQ) at hxK]
      all_goals grind
    choose L hLQ hxL using (Q.exists_unique _ hx).exists
    apply ExistsUnique.intro L (by grind)
    intro K ⟨hK, hxK⟩; simp at hK; obtain hKP | _ := hK
    map_tacs [apply (K.subset_iff _).mp (P.contains _ hKP) at hxK; apply (Q.exists_unique _ hx).unique]
    all_goals grind
  contains L hL := by
    simp at hL; obtain hLP | hLQ := hL
    . apply (P.contains _ hLP).trans; simp [h, subset_iff]
    apply (Q.contains _ hLQ).trans; simp [h, subset_iff]
}

@[simp]
theorem Partition.intervals_of_join {I J K:BoundedInterval} {h:K.joins I J} (P: Partition I) (Q: Partition J) : (P.join Q h).intervals = P.intervals ∪ Q.intervals := by
  simp

noncomputable abbrev Partition.add_empty {I:BoundedInterval} (P: Partition I) : Partition I := {
  intervals := P.intervals ∪ {∅}
  exists_unique x hx := by
    choose J _ _ using (P.exists_unique _ hx).exists
    apply ExistsUnique.intro J (by aesop)
    intro K ⟨ hK, _ ⟩; simp at hK; obtain rfl | hK := hK
    · simp_all [mem_iff]
    apply (P.exists_unique _ hx).unique <;> grind
  contains L hL := by
    simp at hL; obtain rfl | hL := hL
    · simp [subset_iff]
    exact P.contains _ hL
}

open Classical in
noncomputable abbrev Partition.remove_empty {I:BoundedInterval} (P: Partition I) : Partition I := {
  intervals := P.intervals.filter (fun J ↦ (J:Set ℝ).Nonempty)
  exists_unique x hx := by
    choose J _ _ using (P.exists_unique _ hx).exists
    apply ExistsUnique.intro J (by grind [mem_iff, Set.nonempty_of_mem])
    intro K ⟨ hK, _ ⟩; simp at hK
    apply (P.exists_unique _ hx).unique <;> grind
  contains _ _ := P.contains _ (by grind)
}

@[simp]
theorem Partition.intervals_of_add_empty (I: BoundedInterval) (P: Partition I) : (P.add_empty).intervals = P.intervals ∪ {∅} := by
  simp

example : ∃ P:Partition (Icc 1 8),
  P.intervals = {Icc 1 1, Ioo 1 3, Ico 3 5, Icc 5 5, Ioc 5 8, ∅} := by
  set P1 : Partition (Icc 1 1) := ⊥
  set P2 : Partition (Ico 1 3) := P1.join (⊥:Partition (Ioo 1 3)) (join_Icc_Ioo (by norm_num) (by norm_num) )
  set P3 : Partition (Ico 1 5) := P2.join (⊥:Partition (Ico 3 5)) (join_Ico_Ico (by norm_num) (by norm_num) )
  set P4 : Partition (Icc 1 5) := P3.join (⊥:Partition (Icc 5 5)) (join_Ico_Icc (by norm_num) (by norm_num) )
  set P5 : Partition (Icc 1 8) := P4.join (⊥:Partition (Ioc 5 8)) (join_Icc_Ioc (by norm_num) (by norm_num) )
  use P5.add_empty; simp_all; aesop

example : ∃ P:Partition (Icc 1 8), P.intervals = {Icc 1 1, Ioo 1 3, Ico 3 5, Icc 5 5, Ioc 5 8} := by
  set P1 : Partition (Icc 1 1) := ⊥
  set P2 : Partition (Ico 1 3) := P1.join (⊥:Partition (Ioo 1 3)) (join_Icc_Ioo (by norm_num) (by norm_num))
  set P3 : Partition (Ico 1 5) := P2.join (⊥:Partition (Ico 3 5)) (join_Ico_Ico (by norm_num) (by norm_num))
  set P4 : Partition (Icc 1 5) := P3.join (⊥:Partition (Icc 5 5)) (join_Ico_Icc (by norm_num) (by norm_num))
  set P5 : Partition (Icc 1 8) := P4.join (⊥:Partition (Ioc 5 8)) (join_Icc_Ioc (by norm_num) (by norm_num))
  use P5; simp [P1, P2, P3, P4, P5, Partition.intervals_of_bot]

example : ¬∃ P:Partition (Icc 1 5), P.intervals = {Icc 1 4, Icc 3 5} := by
  intro h
  rcases h with ⟨P, hP⟩
  have hx : (3 : ℝ) ∈ (Icc 1 5 : BoundedInterval) := by
    rw [BoundedInterval.mem_iff, BoundedInterval.set_Icc]; norm_num
  rcases P.exists_unique (3 : ℝ) hx with ⟨J, ⟨hJmem, hJin⟩, huniq⟩
  rw [hP] at hJmem
  have hJcases : J = Icc 1 4 ∨ J = Icc 3 5 := by simpa using hJmem
  rcases hJcases with (rfl | rfl)
  · have hmem2 : (Icc 3 5 : BoundedInterval) ∈ P.intervals := by
      rw [hP]; simp
    have hx2 : (3 : ℝ) ∈ (Icc 3 5 : BoundedInterval) := by
      rw [BoundedInterval.mem_iff, BoundedInterval.set_Icc]; norm_num
    have heq := huniq (Icc 3 5) ⟨hmem2, hx2⟩
    have hneq : (Icc 3 5 : BoundedInterval) ≠ (Icc 1 4 : BoundedInterval) := by
      intro hc; have hb := congr_arg BoundedInterval.b hc; norm_num at hb
    exact hneq heq
  · have hmem2 : (Icc 1 4 : BoundedInterval) ∈ P.intervals := by
      rw [hP]; simp
    have hx2 : (3 : ℝ) ∈ (Icc 1 4 : BoundedInterval) := by
      rw [BoundedInterval.mem_iff, BoundedInterval.set_Icc]; norm_num
    have heq := huniq (Icc 1 4) ⟨hmem2, hx2⟩
    have hneq : (Icc 1 4 : BoundedInterval) ≠ (Icc 3 5 : BoundedInterval) := by
      intro hc; have hb := congr_arg BoundedInterval.b hc; norm_num at hb
    exact hneq heq

example : ¬∃ P:Partition (Ioo 1 5), P.intervals = {Ioo 1 3, Ioo 3 5} := by
  intro h
  rcases h with ⟨P, hP⟩
  have hx : (3 : ℝ) ∈ (Ioo 1 5 : BoundedInterval) := by
    rw [BoundedInterval.mem_iff, BoundedInterval.set_Ioo]; norm_num
  rcases P.exists_unique (3 : ℝ) hx with ⟨J, ⟨hJmem, hJin⟩, huniq⟩
  rw [hP] at hJmem
  have hJcases : J = Ioo 1 3 ∨ J = Ioo 3 5 := by simpa using hJmem
  rcases hJcases with (rfl | rfl)
  · have hnot3 : (3 : ℝ) ∉ (Ioo 1 3 : BoundedInterval) := by
      rw [BoundedInterval.mem_iff, BoundedInterval.set_Ioo]; norm_num
    exact hnot3 hJin
  · have hnot3 : (3 : ℝ) ∉ (Ioo 3 5 : BoundedInterval) := by
      rw [BoundedInterval.mem_iff, BoundedInterval.set_Ioo]; norm_num
    exact hnot3 hJin

example : ¬∃ P:Partition (Ioo 1 5), P.intervals = {Ioo 0 3, Ico 3 5} := by
  intro h
  rcases h with ⟨P, hP⟩
  have hJmem : (Ioo 0 3 : BoundedInterval) ∈ P.intervals := by
    rw [hP]; simp
  have hsubset : (Ioo 0 3 : BoundedInterval) ⊆ (Ioo 1 5 : BoundedInterval) :=
    P.contains (Ioo 0 3) hJmem
  have hmem : (0.5 : ℝ) ∈ (Ioo 0 3 : BoundedInterval) := by
    rw [BoundedInterval.mem_iff, BoundedInterval.set_Ioo]; norm_num
  have hnotmem : (0.5 : ℝ) ∉ (Ioo 1 5 : BoundedInterval) := by
    rw [BoundedInterval.mem_iff, BoundedInterval.set_Ioo]; norm_num
  have hmem' : (0.5 : ℝ) ∈ (Ioo 1 5 : BoundedInterval) := hsubset (0.5 : ℝ) hmem
  exact hnotmem hmem'


/-- Exercise 11.1.3.  The exercise only claims c ≤ b, but the stronger claim c < b is true and useful. -/
theorem Partition.exist_right {I: BoundedInterval} (hI: I.a < I.b) (hI': I.b ∉ I)
  {P: Partition I}
  : ∃ c ∈ Set.Ico I.a I.b, Ioo c I.b ∈ P ∨ Ico c I.b ∈ P := by
  have h_nonempty_I : (I : Set ℝ).Nonempty := by
    cases I with
    | Ioo a b => exact Set.nonempty_Ioo.mpr hI
    | Icc a b => exact Set.nonempty_Icc.mpr (le_of_lt hI)
    | Ioc a b => exact Set.nonempty_Ioc.mpr hI
    | Ico a b => exact Set.nonempty_Ico.mpr hI
  obtain ⟨x, hx⟩ := h_nonempty_I
  obtain ⟨J, hJ_mem, hxJ⟩ := (P.exists_unique x hx).exists
  have hJ_nonempty : (J : Set ℝ).Nonempty := ⟨x, hxJ⟩
  classical
    have h_nonempty_I_rem : (P.remove_empty).intervals.Nonempty := by
      have hJ_rem_mem : J ∈ (P.remove_empty).intervals := by
        dsimp [Partition.remove_empty]
        apply Finset.mem_filter.mpr
        exact ⟨hJ_mem, hJ_nonempty⟩
      exact ⟨J, hJ_rem_mem⟩
    let S := (P.remove_empty).intervals.image BoundedInterval.b
    have hS_nonempty : S.Nonempty := by
      rcases h_nonempty_I_rem with ⟨J', hJ'_mem⟩
      refine ⟨J'.b, Finset.mem_image.mpr ⟨J', hJ'_mem, rfl⟩⟩
    let m := S.max' hS_nonempty
    have hm_mem : m ∈ S := Finset.max'_mem _ hS_nonempty
    rcases Finset.mem_image.mp hm_mem with ⟨J_max, hJ_max_mem, hm_eq⟩
    have hJ_max_P_mem : J_max ∈ P.intervals := by
      have : J_max ∈ (P.remove_empty).intervals := hJ_max_mem
      dsimp [Partition.remove_empty] at this
      exact (Finset.mem_filter.mp this).1
    have hJ_max_nonempty : (J_max : Set ℝ).Nonempty := by
      have : J_max ∈ (P.remove_empty).intervals := hJ_max_mem
      dsimp [Partition.remove_empty] at this
      exact (Finset.mem_filter.mp this).2
    have hJ_max_sub_I : (J_max : Set ℝ) ⊆ (I : Set ℝ) :=
      P.contains J_max hJ_max_P_mem
    have hm_ge : ∀ K ∈ (P.remove_empty).intervals, K.b ≤ m := by
      intro K hK
      apply Finset.le_max' S (K.b)
      exact Finset.mem_image.mpr ⟨K, hK, rfl⟩

    have hz_lt_Ib_of_mem {z : ℝ} (hz_I : z ∈ (I : Set ℝ)) : z < I.b := by
      cases I with
      | Ioo a b => exact (Set.mem_Ioo.mp hz_I).2
      | Ico a b => exact (Set.mem_Ico.mp hz_I).2
      | Icc a b =>
        exfalso; apply hI'
        have ha_lt_b : a < b := hI
        exact Set.mem_Icc.mpr ⟨le_of_lt ha_lt_b, le_refl _⟩
      | Ioc a b =>
        exfalso; apply hI'
        have ha_lt_b : a < b := hI
        exact Set.mem_Ioc.mpr ⟨ha_lt_b, le_refl _⟩

    have hz_mem_I_of_range {z : ℝ} (h_lt : I.a < z) (hz_lt_Ib : z < I.b) : z ∈ (I : Set ℝ) := by
      cases I with
      | Ioo a b => exact Set.mem_Ioo.mpr ⟨h_lt, hz_lt_Ib⟩
      | Ico a b => exact Set.mem_Ico.mpr ⟨le_of_lt h_lt, hz_lt_Ib⟩
      | Icc a b =>
        exfalso; apply hI'
        have ha_lt_b : a < b := hI
        exact Set.mem_Icc.mpr ⟨le_of_lt ha_lt_b, le_refl _⟩
      | Ioc a b =>
        exfalso; apply hI'
        have ha_lt_b : a < b := hI
        exact Set.mem_Ioc.mpr ⟨ha_lt_b, le_refl _⟩

    have hy_all_lt_Ib : ∀ (z : ℝ), z ∈ (J_max : Set ℝ) → z < I.b := by
      intro z hz
      exact hz_lt_Ib_of_mem (hJ_max_sub_I hz)

    have hJ_max_b_le_Ib : J_max.b ≤ I.b := by
      by_contra! hgt
      cases J_max with
      | Ioo c d =>
        have hc_lt_d : c < d := by
          rcases hJ_max_nonempty with ⟨z, hz⟩
          rcases Set.mem_Ioo.mp hz with ⟨hc_z, hz_d⟩
          exact lt_trans hc_z hz_d
        have hd_gt_Ib : d > I.b := hgt
        by_cases hc_lt_Ib : c < I.b
        · have hz_mem : (d + I.b) / 2 ∈ (Ioo c d : Set ℝ) := by
            apply Set.mem_Ioo.mpr
            constructor <;> nlinarith
          have hz_gt_Ib : (d + I.b) / 2 > I.b := by nlinarith
          have hz_lt_Ib := hy_all_lt_Ib ((d + I.b) / 2) hz_mem
          nlinarith
        · rcases hJ_max_nonempty with ⟨z, hz⟩
          rcases Set.mem_Ioo.mp hz with ⟨hc_z, hz_d⟩
          have hIbc : I.b ≤ c := by linarith
          have hz_gt_Ib : z > I.b := by nlinarith
          have hz_lt_Ib := hy_all_lt_Ib z hz
          nlinarith
      | Ico c d =>
        have hc_lt_d : c < d := by
          rcases hJ_max_nonempty with ⟨z, hz⟩
          rcases Set.mem_Ico.mp hz with ⟨hc_z, hz_d⟩
          exact lt_of_le_of_lt hc_z hz_d
        have hd_gt_Ib : d > I.b := hgt
        by_cases hc_lt_Ib : c < I.b
        · have hz_mem : (d + I.b) / 2 ∈ (Ico c d : Set ℝ) := by
            apply Set.mem_Ico.mpr
            constructor <;> nlinarith
          have hz_gt_Ib : (d + I.b) / 2 > I.b := by nlinarith
          have hz_lt_Ib := hy_all_lt_Ib ((d + I.b) / 2) hz_mem
          nlinarith
        · rcases hJ_max_nonempty with ⟨z, hz⟩
          rcases Set.mem_Ico.mp hz with ⟨hc_z, hz_d⟩
          have hIbc : I.b ≤ c := by linarith
          have hz_ge_Ib : z ≥ I.b := by nlinarith
          have hz_lt_Ib := hy_all_lt_Ib z hz
          nlinarith
      | Icc c d =>
        have hc_le_d : c ≤ d := by
          rcases hJ_max_nonempty with ⟨z, hz⟩
          rcases Set.mem_Icc.mp hz with ⟨hc_z, hz_d⟩
          exact le_trans hc_z hz_d
        have hd_mem : d ∈ (Icc c d : Set ℝ) :=
          Set.mem_Icc.mpr ⟨hc_le_d, le_refl d⟩
        have hd_lt_Ib : d < I.b := hy_all_lt_Ib d hd_mem
        nlinarith
      | Ioc c d =>
        have hc_lt_d : c < d := by
          rcases hJ_max_nonempty with ⟨z, hz⟩
          rcases Set.mem_Ioc.mp hz with ⟨hc_z, hz_d⟩
          exact lt_of_lt_of_le hc_z hz_d
        have hd_mem : d ∈ (Ioc c d : Set ℝ) :=
          Set.mem_Ioc.mpr ⟨hc_lt_d, le_refl d⟩
        have hd_lt_Ib : d < I.b := hy_all_lt_Ib d hd_mem
        nlinarith
    have hJ_max_b_eq_Ib : J_max.b = I.b := by
      by_cases h_lt : J_max.b < I.b
      · let z := (J_max.b + I.b) / 2
        have hz_gt_Ia : I.a < z := by
          rcases hJ_max_nonempty with ⟨y, hy⟩
          have hy_I : y ∈ (I : Set ℝ) := hJ_max_sub_I hy
          have hy_le_Jmax_b : y ≤ J_max.b := by
            cases J_max with
            | Ioo c d => rcases Set.mem_Ioo.mp hy with ⟨_, hlt⟩; exact le_of_lt hlt
            | Ico c d => rcases Set.mem_Ico.mp hy with ⟨_, hlt⟩; exact le_of_lt hlt
            | Icc c d => rcases Set.mem_Icc.mp hy with ⟨_, hle⟩; exact hle
            | Ioc c d => rcases Set.mem_Ioc.mp hy with ⟨_, hle⟩; exact hle
          have hy_lt_z : y < z := by dsimp [z]; nlinarith
          have hIa_le_y : I.a ≤ y := by
            cases I with
            | Ioo a b => exact le_of_lt (Set.mem_Ioo.mp hy_I).1
            | Ico a b => exact (Set.mem_Ico.mp hy_I).1
            | Icc a b => exact (Set.mem_Icc.mp hy_I).1
            | Ioc a b => exact le_of_lt (Set.mem_Ioc.mp hy_I).1
          exact lt_of_le_of_lt hIa_le_y hy_lt_z
        have hz_lt_Ib : z < I.b := by dsimp [z]; nlinarith
        have hz_mem_I : z ∈ (I : Set ℝ) := hz_mem_I_of_range hz_gt_Ia hz_lt_Ib
        obtain ⟨K, hK_mem, hzK⟩ := (P.exists_unique z hz_mem_I).exists
        have hK_nonempty : (K : Set ℝ).Nonempty := ⟨z, hzK⟩
        have hK_rem_mem : K ∈ (P.remove_empty).intervals := by
          dsimp [Partition.remove_empty]
          apply Finset.mem_filter.mpr
          exact ⟨hK_mem, hK_nonempty⟩
        have hK_b_le_m : K.b ≤ m := hm_ge K hK_rem_mem
        have hz_le_Kb : z ≤ K.b := by
          cases K with
          | Ioo c d => rcases Set.mem_Ioo.mp hzK with ⟨_, hz_lt_d⟩; exact le_of_lt hz_lt_d
          | Ico c d => rcases Set.mem_Ico.mp hzK with ⟨_, hz_lt_d⟩; exact le_of_lt hz_lt_d
          | Icc c d => rcases Set.mem_Icc.mp hzK with ⟨_, hz_le_d⟩; exact hz_le_d
          | Ioc c d => rcases Set.mem_Ioc.mp hzK with ⟨_, hz_le_d⟩; exact hz_le_d
        have hz_gt_m : z > m := by dsimp [z]; nlinarith
        have hz_le_m : z ≤ m := le_trans hz_le_Kb hK_b_le_m
        nlinarith
      · nlinarith
    have hJ_max_is_Ioo_or_Ico : (∃ c, J_max = Ioo c I.b) ∨ (∃ c, J_max = Ico c I.b) := by
      cases J_max with
      | Ioo c d =>
        have hd_eq_Ib : d = I.b := hJ_max_b_eq_Ib
        subst hd_eq_Ib
        left; exact ⟨c, rfl⟩
      | Ico c d =>
        have hd_eq_Ib : d = I.b := hJ_max_b_eq_Ib
        subst hd_eq_Ib
        right; exact ⟨c, rfl⟩
      | Icc c d =>
        exfalso
        apply hI'
        have hc_le_d : c ≤ d := by
          rcases hJ_max_nonempty with ⟨z, hz⟩
          rcases Set.mem_Icc.mp hz with ⟨hc_z, hz_d⟩
          exact le_trans hc_z hz_d
        have hd_mem : d ∈ (Icc c d : Set ℝ) := Set.mem_Icc.mpr ⟨hc_le_d, le_refl d⟩
        have hd_I : d ∈ (I : Set ℝ) := hJ_max_sub_I hd_mem
        simpa [hJ_max_b_eq_Ib] using hd_I
      | Ioc c d =>
        exfalso
        apply hI'
        have hc_lt_d : c < d := by
          rcases hJ_max_nonempty with ⟨z, hz⟩
          rcases Set.mem_Ioc.mp hz with ⟨hc_z, hz_d⟩
          exact lt_of_lt_of_le hc_z hz_d
        have hd_mem : d ∈ (Ioc c d : Set ℝ) := Set.mem_Ioc.mpr ⟨hc_lt_d, le_refl d⟩
        have hd_I : d ∈ (I : Set ℝ) := hJ_max_sub_I hd_mem
        simpa [hJ_max_b_eq_Ib] using hd_I
    rcases hJ_max_is_Ioo_or_Ico with (⟨c, hJ_max_eq⟩ | ⟨c, hJ_max_eq⟩)
    · subst hJ_max_eq
      have hc_lt_Ib : c < I.b := by
        rcases hJ_max_nonempty with ⟨z, hz⟩
        rcases Set.mem_Ioo.mp hz with ⟨hc_z, hz_d⟩
        calc
          c < z := hc_z
          _ < I.b := hz_d
      have hIa_le_c : I.a ≤ c := by
        by_contra! hlt
        have hx : (c + I.a) / 2 ∈ (Ioo c I.b : Set ℝ) := by
          apply Set.mem_Ioo.mpr
          have hx_lt_Ib : (c + I.a) / 2 < I.b := by nlinarith
          constructor <;> nlinarith
        have hx_not_I : (c + I.a) / 2 ∉ (I : Set ℝ) := by
          intro h
          have hmem_left : I.a ≤ (c + I.a) / 2 := by
            cases I with
            | Ioo a b => exact le_of_lt (Set.mem_Ioo.mp h).1
            | Ico a b => exact (Set.mem_Ico.mp h).1
            | Icc a b => exact (Set.mem_Icc.mp h).1
            | Ioc a b => exact le_of_lt (Set.mem_Ioc.mp h).1
          nlinarith
        exact hx_not_I (hJ_max_sub_I hx)
      refine ⟨c, ⟨hIa_le_c, hc_lt_Ib⟩, Or.inl ?_⟩
      exact hJ_max_P_mem
    · subst hJ_max_eq
      have hc_lt_Ib : c < I.b := by
        rcases hJ_max_nonempty with ⟨z, hz⟩
        rcases Set.mem_Ico.mp hz with ⟨hc_z, hz_d⟩
        exact lt_of_le_of_lt hc_z hz_d
      have hIa_le_c : I.a ≤ c := by
        by_contra! hlt
        have hx : (c + I.a) / 2 ∈ (Ico c I.b : Set ℝ) := by
          apply Set.mem_Ico.mpr
          have hx_lt_Ib : (c + I.a) / 2 < I.b := by nlinarith
          constructor <;> nlinarith
        have hx_not_I : (c + I.a) / 2 ∉ (I : Set ℝ) := by
          intro h
          have hmem_left : I.a ≤ (c + I.a) / 2 := by
            cases I with
            | Ioo a b => exact le_of_lt (Set.mem_Ioo.mp h).1
            | Ico a b => exact (Set.mem_Ico.mp h).1
            | Icc a b => exact (Set.mem_Icc.mp h).1
            | Ioc a b => exact le_of_lt (Set.mem_Ioc.mp h).1
          nlinarith
        exact hx_not_I (hJ_max_sub_I hx)
      refine ⟨c, ⟨hIa_le_c, hc_lt_Ib⟩, Or.inr ?_⟩
      exact hJ_max_P_mem

/-- Theorem 11.1.13 (Length is finitely additive). -/
theorem Partition.sum_of_length  (I: BoundedInterval) (P: Partition I) :
  ∑ J ∈ P.intervals, |J|ₗ = |I|ₗ := by
  -- This proof is written to follow the structure of the original text.
  generalize hcard: P.intervals.card = n
  revert I; induction' n with n hn <;> intro I P hcard
  . rw [Finset.card_eq_zero] at hcard
    have : (I:Set ℝ) = ∅ := by
      by_contra! hne
      rcases hne with ⟨x, hx⟩
      rcases P.exists_unique x hx with ⟨J, ⟨hJmem, _⟩, _⟩
      have hP_empty : P.intervals = ∅ := hcard
      have hJmem' : J ∈ P.intervals := hJmem
      rw [hP_empty] at hJmem'
      simp at hJmem'
    grind [length_of_empty]
  -- the proof in the book treats the n=1 case separately, but this is unnecessary
  by_cases h : Subsingleton (I:Set ℝ)
  . have (J: BoundedInterval) (hJ: J ∈ P) : Subsingleton (J:Set ℝ) := by
      apply Subsingleton.intro
      intro a b
      apply Subtype.ext
      have haJ : a.val ∈ (J : Set ℝ) := a.property
      have hbJ : b.val ∈ (J : Set ℝ) := b.property
      have haI : a.val ∈ (I : Set ℝ) := (P.contains J hJ a.val) haJ
      have hbI : b.val ∈ (I : Set ℝ) := (P.contains J hJ b.val) hbJ
      have h_eq : (⟨a.val, haI⟩ : (I : Set ℝ)) = (⟨b.val, hbI⟩ : (I : Set ℝ)) :=
        Subsingleton.elim _ _
      injection h_eq
    simp_rw [length_of_subsingleton] at *
    convert Finset.sum_eq_zero this
  simp [length_of_subsingleton, length, -Set.subsingleton_coe] at h
  have : ∃ K L : BoundedInterval, K ∈ P ∧ I.joins L K := by
    by_cases hI' : I.b ∈ I
    . choose K hK hbK using (P.exists_unique I.b hI').exists
      observe hKI : K ⊆ I
      by_cases hsub : Subsingleton (K:Set ℝ)
      . simp_all [mem_iff]
        apply hsub.eq_singleton_of_mem at hbK
        have : K = Icc (I.b) (I.b) := by
          have hK_set_eq : (K : Set ℝ) = {I.b} := hbK
          have hmem : I.b ∈ (K : Set ℝ) := by
            simp [hK_set_eq]
          cases K with
          | Ioo a b =>
            rcases Set.mem_Ioo.mp hmem with ⟨ha_lt_Ib, hIb_lt_b⟩
            have ha_lt_b : a < b := lt_trans ha_lt_Ib hIb_lt_b
            have hsub_set : (Ioo a b : Set ℝ).Subsingleton := by
              simpa using hsub
            have hx : (2*a + b)/3 ∈ (Ioo a b : Set ℝ) := by
              apply Set.mem_Ioo.mpr; constructor <;> nlinarith
            have hy : (a + 2*b)/3 ∈ (Ioo a b : Set ℝ) := by
              apply Set.mem_Ioo.mpr; constructor <;> nlinarith
            have h_val_eq : (2*a + b)/3 = (a + 2*b)/3 :=
              hsub_set hx hy
            have hneq : (2*a + b)/3 ≠ (a + 2*b)/3 := by nlinarith
            exfalso; exact hneq h_val_eq
          | Icc a b =>
            have ha_le_Ib : a ≤ I.b := (Set.mem_Icc.mp hmem).1
            have hIb_le_b : I.b ≤ b := (Set.mem_Icc.mp hmem).2
            have hsub_set : (Icc a b : Set ℝ).Subsingleton := by
              simpa using hsub
            have hb_le_a : b ≤ a := by
              have : (Set.Icc a b).Subsingleton := by simpa using hsub_set
              rw [Set.subsingleton_Icc_iff] at this
              exact this
            have ha_eq_Ib : a = I.b := by nlinarith
            have hb_eq_Ib : b = I.b := by nlinarith
            simp [ha_eq_Ib, hb_eq_Ib]
          | Ioc a b =>
            rcases Set.mem_Ioc.mp hmem with ⟨ha_lt_Ib, hIb_le_b⟩
            have ha_lt_b : a < b := lt_of_lt_of_le ha_lt_Ib hIb_le_b
            have hsub_set : (Ioc a b : Set ℝ).Subsingleton := by
              simpa using hsub
            have hx : (2*a + b)/3 ∈ (Ioc a b : Set ℝ) := by
              apply Set.mem_Ioc.mpr; constructor <;> nlinarith
            have hy : (a + 2*b)/3 ∈ (Ioc a b : Set ℝ) := by
              apply Set.mem_Ioc.mpr; constructor <;> nlinarith
            have h_val_eq : (2*a + b)/3 = (a + 2*b)/3 :=
              hsub_set hx hy
            have hneq : (2*a + b)/3 ≠ (a + 2*b)/3 := by nlinarith
            exfalso; exact hneq h_val_eq
          | Ico a b =>
            rcases Set.mem_Ico.mp hmem with ⟨ha_le_Ib, hIb_lt_b⟩
            have ha_lt_b : a < b := lt_of_le_of_lt ha_le_Ib hIb_lt_b
            have hsub_set : (Ico a b : Set ℝ).Subsingleton := by
              simpa using hsub
            have hx : (2*a + b)/3 ∈ (Ico a b : Set ℝ) := by
              apply Set.mem_Ico.mpr; constructor <;> nlinarith
            have hy : (a + 2*b)/3 ∈ (Ico a b : Set ℝ) := by
              apply Set.mem_Ico.mpr; constructor <;> nlinarith
            have h_val_eq : (2*a + b)/3 = (a + 2*b)/3 :=
              hsub_set hx hy
            have hneq : (2*a + b)/3 ≠ (a + 2*b)/3 := by nlinarith
            exfalso; exact hneq h_val_eq
        subst this
        cases I with
        | Ioo _ _ => simp at hI'
        | Icc a b => use (Icc b b), hK, Ico a b; apply join_Ico_Icc <;> order
        | Ioc a b => use (Icc b b), hK, Ioo a b; apply join_Ioo_Icc <;> order
        | Ico _ _ => simp at hI'
      simp [length_of_subsingleton, -Set.subsingleton_coe] at hsub
      have hKI' := (K.Ioo_subset.trans hKI).trans I.subset_Icc
      simp only [subset_iff] at hKI'
      have hKb : K.b = I.b := by
        rw [le_antisymm_iff]; split_ands
        . apply csSup_le_csSup bddAbove_Icc (by simp [hsub]) at hKI'
          simp_all [csSup_Ioo hsub, csSup_Icc (le_of_lt h)]
        have := K.subset_Icc _ hbK; simp [mem_iff] at this; exact this.2
      have hKA : I.a ≤ K.a := by
        apply csInf_le_csInf bddBelow_Icc (by simp [hsub]) at hKI'
        simp_all [csInf_Icc (le_of_lt h), csInf_Ioo]
      cases I with
      | Ioo _ _ => simp [mem_iff] at hI'
      | Icc a₁ b₁ =>
        use K; cases K with
        | Ioo _ _ => simp [mem_iff, subset_iff] at *; grind
        | Icc c₂ b₂ => use Ico a₁ c₂, hK; simp_all; apply join_Ico_Icc <;> order
        | Ioc c₂ b₂ => use Icc a₁ c₂, hK; simp_all; apply join_Icc_Ioc <;> order
        | Ico _ _ => simp [mem_iff] at *; grind
      | Ioc a₁ b₁ =>
        use K; cases K with
        | Ioo _ _ => simp_all [mem_iff]
        | Icc c₂ b₂ =>
          use Ioo a₁ c₂, hK
          simp_all [subset_iff]
          have : c₂ ∈ Set.Icc c₂ b₁ := by grind
          apply hKI at this; grind [join_Ioo_Icc]
        | Ioc c₂ b₂ => use Ioc a₁ c₂, hK; simp_all; apply join_Ioc_Ioc <;> order
        | Ico _ _ => simp [mem_iff, subset_iff] at *; grind
      | Ico _ _ => simp [mem_iff] at hI'
    choose c hc hK using P.exist_right h hI'
    cases I with
    | Ioo a₁ b₁ =>
      obtain hK | hK := hK <;> simp_all [mem_iff]
      . use Ioo c b₁, hK, Ioc a₁ c; apply join_Ioc_Ioo <;> tauto
      use Ico c b₁, hK, Ioo a₁ c
      apply P.contains at hK; simp [subset_iff] at hK
      have : c ∈ Set.Ico c b₁ := by grind
      grind [join_Ioo_Ico]
    | Icc _ _ => simp [mem_iff] at hI' h; order
    | Ioc _ _ => simp [mem_iff] at hI' h; order
    | Ico a₁ b₁ =>
      obtain hK | hK := hK <;> simp_all [mem_iff]
      . use Ioo c b₁, hK, Icc a₁ c; grind [join_Icc_Ioo]
      use Ico c b₁, hK, Ico a₁ c; grind [join_Ico_Ico]
  obtain ⟨ K, L, hK, ⟨ h1, h2, h3 ⟩ ⟩ := this
  have : ∃ P' : Partition L, P'.intervals = P.intervals.erase K := by
    refine ⟨{
      intervals := P.intervals.erase K
      exists_unique := by
        intro x hxL
        have hxI : x ∈ (I : Set ℝ) := by
          rw [h2]
          exact Set.mem_union_left (K : Set ℝ) hxL
        rcases P.exists_unique x hxI with ⟨J, ⟨hJmem, hxJ⟩, huniq⟩
        have hx_not_K : x ∉ (K : Set ℝ) := by
          intro hxK
          have : x ∈ (L : Set ℝ) ∩ (K : Set ℝ) := Set.mem_inter hxL hxK
          rw [h1] at this
          simp at this
        have hJ_ne_K : J ≠ K := by
          intro h_eq
          subst h_eq
          apply hx_not_K
          simpa [mem_iff] using hxJ
        have hJ_mem_erase : J ∈ P.intervals.erase K :=
          Finset.mem_erase.mpr ⟨hJ_ne_K, hJmem⟩
        refine ⟨J, ⟨hJ_mem_erase, hxJ⟩, ?_⟩
        intro J' ⟨hJ'_mem_erase, hxJ'⟩
        have hJ'_mem : J' ∈ P.intervals := (Finset.mem_erase.mp hJ'_mem_erase).2
        exact huniq J' ⟨hJ'_mem, hxJ'⟩
      contains := by
        intro J hJ_erase
        have hJmem : J ∈ P.intervals := (Finset.mem_erase.mp hJ_erase).2
        have hJ_ne_K : J ≠ K := (Finset.mem_erase.mp hJ_erase).1
        intro x hxJ
        have hxI : x ∈ (I : Set ℝ) := (P.contains J hJmem) x hxJ
        rw [h2] at hxI
        rcases hxI with (hxL | hxK)
        · simpa [mem_iff] using hxL
        · exfalso
          have hxI' : x ∈ (I : Set ℝ) := by
            rw [h2]
            exact Set.mem_union_right (L : Set ℝ) hxK
          rcases P.exists_unique x hxI' with ⟨J', ⟨hJ'mem, hxJ'⟩, huniq⟩
          have hJ_eq_K : J = K :=
            (huniq J ⟨hJmem, hxJ⟩).trans (huniq K ⟨hK, by
              simpa [mem_iff] using hxK⟩).symm
          exact hJ_ne_K hJ_eq_K
    }, rfl⟩
  choose P' hP' using this
  rw [h3, ←Finset.add_sum_erase _ _ hK, ←hP', add_comm]; congr
  apply hn; simp [hP', Finset.card_erase_of_mem hK, hcard]

/-- Definition 11.1.14 (Finer and coarser partitions) -/
instance Partition.instLE (I: BoundedInterval) : LE (Partition I) where
  le P P' := ∀ J ∈ P'.intervals, ∃ K ∈ P, J ⊆ K

instance Partition.instPreOrder (I: BoundedInterval) : Preorder (Partition I) where
  le_refl P := by
    intro J hJ
    refine ⟨J, hJ, ?_⟩
    intro x hx
    exact hx
  le_trans P P' P'' hP hP' := by
    intro J hJ
    rcases hP' J hJ with ⟨K, hK, hJK⟩
    rcases hP K hK with ⟨L, hL, hKL⟩
    refine ⟨L, hL, ?_⟩
    exact hJK.trans hKL

instance Partition.instOrderBot (I: BoundedInterval) : OrderBot (Partition I) where
  bot_le := by
    intro P J hJ
    refine ⟨I, by
      have hmem : I ∈ (⊥ : Partition I).intervals := by
        simp [Partition.intervals_of_bot]
      exact hmem, ?_⟩
    exact P.contains J hJ

/-- Example 11.1.15 -/
example : ∃ P P' : Partition (Icc 1 4),
  P.intervals = {Ico 1 2, Icc 2 2, Ioo 2 3,
                 Icc 3 4} ∧
  P'.intervals = {Icc 1 2, Ioc 2 4} ∧
  P' ≤ P := by
  set P1 : Partition (Icc 2 2) := ⊥
  set P2 : Partition (Ico 2 3) :=
    P1.join (⊥ : Partition (Ioo 2 3)) (join_Icc_Ioo (by norm_num) (by norm_num))
  set P3 : Partition (Ico 1 3) :=
    (⊥ : Partition (Ico 1 2)).join P2 (join_Ico_Ico (by norm_num) (by norm_num))
  set P : Partition (Icc 1 4) :=
    P3.join (⊥ : Partition (Icc 3 4)) (join_Ico_Icc (by norm_num) (by norm_num))
  set P' : Partition (Icc 1 4) :=
    (⊥ : Partition (Icc 1 2)).join (⊥ : Partition (Ioc 2 4)) (join_Icc_Ioc (by norm_num) (by norm_num))
  have hP_intervals : P.intervals = {Ico 1 2, Icc 2 2, Ioo 2 3, Icc 3 4} := by
    calc
      P.intervals = {Icc 2 2, Ico 1 2, Ioo 2 3, Icc 3 4} := by
        simp [P, P1, P2, P3, Partition.intervals_of_bot]
      _ = {Ico 1 2, Icc 2 2, Ioo 2 3, Icc 3 4} := by
        ext x; simp; tauto
  have hP'_intervals : P'.intervals = {Icc 1 2, Ioc 2 4} := by
    simp [P', Partition.intervals_of_bot]
  refine ⟨P, P', hP_intervals, hP'_intervals, ?_⟩
  intro J hJ
  simp [hP_intervals] at hJ
  rcases hJ with (rfl|rfl|rfl|rfl)
  · have hmem : Icc 1 2 ∈ P'.intervals := by
      rw [hP'_intervals]; simp
    refine ⟨Icc 1 2, hmem, ?_⟩
    rw [BoundedInterval.subset_iff]; simp [Set.Ico_subset_Icc_self]
  · have hmem : Icc 1 2 ∈ P'.intervals := by
      rw [hP'_intervals]; simp
    refine ⟨Icc 1 2, hmem, ?_⟩
    rw [BoundedInterval.subset_iff]; intro x hx; simp at hx; subst hx; simp
  · have hmem : Ioc 2 4 ∈ P'.intervals := by
      rw [hP'_intervals]; simp
    refine ⟨Ioc 2 4, hmem, ?_⟩
    rw [BoundedInterval.subset_iff]; intro x hx; simp at hx; have ⟨hx1, hx2⟩ := hx; exact ⟨hx1, by nlinarith⟩
  · have hmem : Ioc 2 4 ∈ P'.intervals := by
      rw [hP'_intervals]; simp
    refine ⟨Ioc 2 4, hmem, ?_⟩
    rw [BoundedInterval.subset_iff]; intro x hx; simp at hx; have ⟨hx1, hx2⟩ := hx; exact ⟨by nlinarith, hx2⟩

/-- Definition 11.1.16 (Common refinement). -/
noncomputable instance Partition.instMax (I: BoundedInterval) : Max (Partition I) where
  max P P' := {
    intervals := Finset.image₂ (fun J K ↦ J ∩ K) P.intervals P'.intervals
    exists_unique x hx := by
      choose J _ _ using P.exists_unique _ hx
      choose K _ _ using P'.exists_unique _ hx
      simp at *
      apply ExistsUnique.intro (J ∩ K)
      . simp_all; grind
      simp; grind [mem_inter]
    contains L hL := by
      simp at hL; obtain ⟨ J, hJ, K, hK, rfl ⟩ := hL
      apply P.contains at hJ; apply P'.contains at hK
      simp [subset_iff] at *; grind [Set.inter_subset_left]
    }


/-- Example 11.1.17. -/
example : ∃ P P' : Partition (Icc 1 4),
    P.intervals = {Ico 1 3, Icc 3 4} ∧
    P'.intervals = {Icc 1 2, Ioc 2 4} ∧
    (P' ⊔ P).intervals.image toSet =
      {Set.Icc 1 2, Set.Ioo 2 3, Set.Icc 3 4, ∅} := by
  set P : Partition (Icc 1 4) :=
    (⊥ : Partition (Ico 1 3)).join (⊥ : Partition (Icc 3 4)) (join_Ico_Icc (by norm_num) (by norm_num))
  set P' : Partition (Icc 1 4) :=
    (⊥ : Partition (Icc 1 2)).join (⊥ : Partition (Ioc 2 4)) (join_Icc_Ioc (by norm_num) (by norm_num))
  have hP_intervals : P.intervals = {Ico 1 3, Icc 3 4} := by
    simp [P, Partition.intervals_of_bot]
  have hP'_intervals : P'.intervals = {Icc 1 2, Ioc 2 4} := by
    simp [P', Partition.intervals_of_bot]
  refine ⟨P, P', hP_intervals, hP'_intervals, ?_⟩
  have h1 : (Set.Icc 1 2 : Set ℝ) ∩ (Set.Ico 1 3 : Set ℝ) = Set.Icc 1 2 := by ext x; simp; grind
  have h2 : (Set.Icc 1 2 : Set ℝ) ∩ (Set.Icc 3 4 : Set ℝ) = (∅ : Set ℝ) := by ext x; simp; grind
  have h3 : (Set.Ioc 2 4 : Set ℝ) ∩ (Set.Ico 1 3 : Set ℝ) = Set.Ioo 2 3 := by ext x; simp; grind
  have h4 : (Set.Ioc 2 4 : Set ℝ) ∩ (Set.Icc 3 4 : Set ℝ) = Set.Icc 3 4 := by ext x; simp; grind
  have hsup_image : (P' ⊔ P).intervals.image toSet = ({Set.Icc 1 2, Set.Ioo 2 3, Set.Icc 3 4, (∅ : Set ℝ)} : Finset (Set ℝ)) := by
    calc
      (P' ⊔ P).intervals.image toSet = ((Finset.image₂ (fun (J K : BoundedInterval) => J ∩ K) P'.intervals P.intervals).image toSet) := rfl
      _ = Finset.image₂ (fun (J K : BoundedInterval) => (J ∩ K : BoundedInterval).toSet) P'.intervals P.intervals := by
        rw [Finset.image_image₂]
      _ = Finset.image₂ (fun (J K : BoundedInterval) => (J : Set ℝ) ∩ (K : Set ℝ)) P'.intervals P.intervals := by
        refine Finset.image₂_congr' (fun J K => ?_)
        simp [BoundedInterval.inter_eq]
      _ = Finset.image₂ (fun (J K : BoundedInterval) => (J : Set ℝ) ∩ (K : Set ℝ)) {Icc 1 2, Ioc 2 4} {Ico 1 3, Icc 3 4} := by
        simp [hP_intervals, hP'_intervals]
      _ = ({Set.Icc 1 2, (∅ : Set ℝ), Set.Ioo 2 3, Set.Icc 3 4} : Finset (Set ℝ)) := by
        simp [h1, h2, h3, h4]; ext x; simp; tauto
      _ = {Set.Icc 1 2, Set.Ioo 2 3, Set.Icc 3 4, ∅} := by
        ext x; simp; tauto
  exact hsup_image

/-- Lemma 11.1.8 / Exercise 11.1.4 -/
theorem BoundedInterval.le_max {I: BoundedInterval} (P P': Partition I) :
  P ≤ P ⊔ P' ∧ P' ≤ P ⊔ P' := by
  constructor
  · intro J hJ
    have hsup_intervals : (P ⊔ P').intervals = Finset.image₂ (fun J K => J ∩ K) P.intervals P'.intervals := rfl
    rw [hsup_intervals] at hJ
    simp [Finset.mem_image₂] at hJ
    rcases hJ with ⟨J₁, hJ₁, J₂, hJ₂, rfl⟩
    refine ⟨J₁, hJ₁, ?_⟩
    rw [BoundedInterval.subset_iff, BoundedInterval.inter_eq]
    exact Set.inter_subset_left

  · intro J hJ
    have hsup_intervals : (P ⊔ P').intervals = Finset.image₂ (fun J K => J ∩ K) P.intervals P'.intervals := rfl
    rw [hsup_intervals] at hJ
    simp [Finset.mem_image₂] at hJ
    rcases hJ with ⟨J₁, hJ₁, J₂, hJ₂, rfl⟩
    refine ⟨J₂, hJ₂, ?_⟩
    rw [BoundedInterval.subset_iff, BoundedInterval.inter_eq]
    exact Set.inter_subset_right
/-- Not from textbook: the reverse inclusion -/
theorem BoundedInterval.max_le_iff (I: BoundedInterval) {P P' P'': Partition I}
  {hP : P ≤ P''} {hP': P' ≤ P''} : P ⊔ P' ≤ P''  := by
  intro J hJ
  rcases hP J hJ with ⟨K, hK, hJK⟩
  rcases hP' J hJ with ⟨L, hL, hJL⟩
  refine ⟨K ∩ L, ?_, ?_⟩
  · apply Finset.mem_image₂.mpr
    exact ⟨K, hK, L, hL, rfl⟩
  · intro x hx
    have hxK : x ∈ K := hJK x hx
    have hxL : x ∈ L := hJL x hx
    simp [BoundedInterval.mem_inter, hxK, hxL]

end Chapter11
