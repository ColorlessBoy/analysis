import Mathlib.Tactic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Countable
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Countable.Defs
import Mathlib.Logic.Encodable.Basic
import Mathlib.Logic.Denumerable
import Mathlib.Data.Nat.Find
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.Basic

open Classical

/-!
# Analysis I, Section 8.3: Uncountable sets

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Uncountable sets.

Some non-trivial API is provided beyond what is given in the textbook in order connect these
notions with existing summation notions.

-/

namespace Chapter8

abbrev EqualCard (X Y : Type) : Prop := ∃ f : X → Y, Function.Bijective f

abbrev CountablyInfinite (X : Type) : Prop := EqualCard X ℕ

abbrev AtMostCountable (X : Type) : Prop := CountablyInfinite X ∨ Finite X

namespace EqualCard
  theorem refl (X : Type) : EqualCard X X := ⟨id, Function.bijective_id⟩
  theorem symm {X Y : Type} (h : EqualCard X Y) : EqualCard Y X := by
    rcases h with ⟨f, hf⟩
    have hf_inj : Function.Injective f := hf.1
    have hf_surj : Function.Surjective f := hf.2
    let g : Y → X := fun y => (hf_surj y).choose
    have hg_spec (y : Y) : f (g y) = y := (hf_surj y).choose_spec
    have hg : Function.Bijective g := by
      constructor
      · intro y₁ y₂ h
        calc
          y₁ = f (g y₁) := (hg_spec y₁).symm
          _ = f (g y₂) := by rw [h]
          _ = y₂ := hg_spec y₂
      · intro x
        use f x
        calc
          g (f x) = (hf_surj (f x)).choose := rfl
          _ = x := hf_inj ((hf_surj (f x)).choose_spec)
    exact ⟨g, hg⟩
  theorem trans {X Y Z : Type} (h1 : EqualCard X Y) (h2 : EqualCard Y Z) : EqualCard X Z := by
    rcases h1 with ⟨f, hf⟩; rcases h2 with ⟨g, hg⟩
    exact ⟨g ∘ f, hg.comp hf⟩
end EqualCard

namespace CountablyInfinite
  theorem toCountable (h : CountablyInfinite X) : Countable X := by
    rcases h with ⟨f, hf⟩
    exact hf.1.countable
  theorem toInfinite (h : CountablyInfinite X) : Infinite X := by
    rcases h with ⟨f, hf⟩
    have hf_surj : Function.Surjective f := hf.2
    by_contra! h_fin
    haveI : Finite X := h_fin
    have h_fin_ℕ : Finite ℕ := by
      set g : ℕ → X := fun n => (hf_surj n).choose with hg
      have hg_spec : ∀ n, f (g n) = n := fun n => (hf_surj n).choose_spec
      have hg_inj : Function.Injective g := by
        intro n m h
        calc
          n = f (g n) := (hg_spec n).symm
          _ = f (g m) := by rw [h]
          _ = m := hg_spec m
      exact Finite.of_injective g hg_inj
    have h_inf_ℕ : Infinite ℕ := by infer_instance
    have : ¬ Finite ℕ := by rwa [not_finite_iff_infinite]
    exact this h_fin_ℕ
end CountablyInfinite

namespace AtMostCountable
  theorem iff (X : Type) : AtMostCountable X ↔ Countable X := by
    constructor
    · intro h; rcases h with (h' | h')
      · exact CountablyInfinite.toCountable h'
      · haveI : Finite X := h'; infer_instance
    · intro h
      by_cases hinf : Infinite X
      · left
        have h_enc : Encodable X := by
          haveI : Countable X := h; exact Encodable.ofCountable _
        haveI : Denumerable X := Denumerable.ofEncodableOfInfinite X
        exact ⟨Denumerable.eqv X, (Denumerable.eqv X).bijective⟩
      · right; rw [not_infinite_iff_finite] at hinf; exact hinf
  theorem equiv {X Y : Type} (hXY : EqualCard X Y) : AtMostCountable X ↔ AtMostCountable Y := by
    constructor
    · intro h; rcases h with (h' | h')
      · left; exact hXY.symm.trans h'
      · right
        haveI : Finite X := h'
        rcases hXY with ⟨f, hf⟩
        haveI : Finite Y := Finite.ofBijective hf
        exact inferInstance
    · intro h; rcases h with (h' | h')
      · left; exact hXY.trans h'
      · right
        haveI : Finite Y := h'
        rcases hXY.symm with ⟨g, hg⟩
        haveI : Finite X := Finite.ofBijective hg
        exact inferInstance
end AtMostCountable

noncomputable def Nat.min (X : Set ℕ) : ℕ :=
  if h : X.Nonempty then Nat.find h else 0

theorem Nat.min_spec {X : Set ℕ} (hX : X.Nonempty) : Nat.min X ∈ X ∧ ∀ n ∈ X, Nat.min X ≤ n := by
  dsimp [Nat.min]
  simp [hX]
  constructor
  · exact Nat.find_spec hX
  · intro n hn
    by_contra hle
    -- hle : ¬ ∃ m ≤ n, m ∈ X (by find_le_iff simp lemma)
    have h_exists : ∃ m ≤ n, m ∈ X := ⟨n, le_refl n, hn⟩
    exact hle h_exists

/-- Theorem 8.3.1 -/
theorem EqualCard.power_set_false (X:Type) : ¬ EqualCard X (Set X) := by
  -- This proof is written to follow the structure of the original text.
  by_contra!; choose f hf using this
  set A := {x | x ∉ f x }
  rcases hf.2 A with ⟨x, hx⟩
  by_cases h : x ∈ A <;> have h' := h
  . simp [A] at h'; simp_all
  rw [←hx] at h'
  have : x ∈ A := by simp [A, h']
  contradiction

theorem Uncountable.iff (X:Type) : Uncountable X ↔ ¬ AtMostCountable X := by
  rw [AtMostCountable.iff, uncountable_iff_not_countable]


theorem Uncountable.equiv {X Y: Type} (hXY : EqualCard X Y) :
  Uncountable X ↔ Uncountable Y := by
    rw [Uncountable.iff, Uncountable.iff]
    exact (AtMostCountable.equiv hXY).not

/-- Corollary 8.3.3 -/
theorem Uncountable.power_set_nat : Uncountable (Set ℕ) := by
  -- This proof is written to follow the structure of the original text.
  rw [Uncountable.iff]
  unfold AtMostCountable
  have : ¬ CountablyInfinite (Set ℕ) := by
    have := EqualCard.power_set_false ℕ
    contrapose! this; exact this.symm
  have : ¬ Finite (Set ℕ) := by
    by_contra!
    have : Finite ((fun x:ℕ ↦ ({x}:Set ℕ)) '' .univ) := Finite.Set.subset (s := .univ) (by aesop)
    replace : Finite ℕ := by
      apply Finite.of_finite_univ
      rw [←Set.finite_coe_iff]
      apply Finite.Set.finite_of_finite_image (f := fun x ↦ ({x}:Set ℕ))
      intro _ _ _ _ _; aesop
    have hinf : ¬ Finite ℕ := by rw [not_finite_iff_infinite]; infer_instance
    contradiction
  tauto

open Real in
/-- Corollary 8.3.4 -/
theorem Uncountable.real : Uncountable ℝ := by
  -- This proof is written to follow the structure of the original text.
  set a : ℕ → ℝ := fun n ↦ (10:ℝ)^(-(n:ℝ))
  set f : Set ℕ → ℝ := fun A ↦ ∑' n:A, a n
  have hsummable (A: Set ℕ) : Summable (fun n:A ↦ a n) := by
    apply Summable.subtype (f := a)
    convert summable_geometric_of_lt_one (?_:0 ≤ (1/10:ℝ)) ?_ using 2 with n <;> try norm_num
    unfold a
    rw [one_div_pow, rpow_neg, one_div]; simp; norm_num
  have h_decomp {A B C: Set ℕ} (hC : C = A ∪ B) (hAB: ∀ n, n ∉ A ∩ B) :  ∑' n:C, a n = ∑' n:A, a n + ∑' n:B, a n := by
    convert Summable.tsum_union_disjoint ?_ ?_ ?_ <;> first | infer_instance | try apply hsummable
    . rw [hC]
    rw [Set.disjoint_iff_inter_eq_empty]; grind
  have h_nonneg (A:Set ℕ) : ∑' n:A, a n ≥ 0 := by simp [a]; positivity
  have h_congr {A B: Set ℕ} (hAB: A = B) : ∑' n:A, a n = ∑' n:B, a n  := by rw [hAB]
  have : Function.Injective f := by
    intro A B hAB; by_contra!
    rw [←Set.symmDiff_nonempty] at this
    apply Nat.min_spec at this
    set n₀ := Nat.min (symmDiff A B)
    simp [symmDiff] at this; choose h1 h2 using this
    wlog h : n₀ ∈ A ∧ n₀ ∉ B generalizing A B
    . simp [h] at h1
      apply this hAB.symm <;> simp [symmDiff_comm] <;> grind
    replace h2 {n:ℕ} (hn: n < n₀) : n ∈ A ↔ n ∈ B := by grind
    have : (0:ℝ) > 0 := calc
      _ = f A - f B := by linarith
      _ = ∑' n:A, a n - ∑' n:B, a n := rfl
      _ = (∑' n:{n ∈ A|n ≤ n₀}, a n + ∑' n:{n ∈ A|n > n₀}, a n) -
          (∑' n:{n ∈ B|n ≤ n₀}, a n + ∑' n:{n ∈ B|n > n₀}, a n) := by
        congr; all_goals {
          apply h_decomp
          . ext n; simp; grind
          intro n hn; simp at hn; linarith
        }
      _ = ((∑' n:{n ∈ A|n < n₀}, a n + ∑' n:{n ∈ A|n = n₀}, a n) + ∑' n:{n ∈ A|n > n₀}, a n) -
          ((∑' n:{n ∈ B|n < n₀}, a n + ∑' n:{n ∈ B|n = n₀}, a n) + ∑' n:{n ∈ B|n > n₀}, a n) := by
        congr; all_goals {
          apply h_decomp
          . ext n; simp [le_iff_lt_or_eq]
          intro n hn; simp at hn; linarith
        }
      _ = ((∑' n:{n ∈ A|n < n₀}, a n + a n₀) + ∑' n:{n ∈ A|n > n₀}, a n) -
          ((∑' n:{n ∈ B|n < n₀}, a n + 0) + ∑' n:{n ∈ B|n > n₀}, a n) := by
        congr 3
        . calc
            _ = ∑' n:({n₀}:Set ℕ), a n := by apply h_congr; ext n; simp; grind
            _ = _ := by simp
        . calc
            _ = ∑' n:(∅:Set ℕ), a n := by apply h_congr; ext n; simp; grind
            _ = _ := by simp
      _ = (∑' n:{n ∈ A|n < n₀}, a n - ∑' n:{n ∈ B|n < n₀}, a n) + a n₀ +
          ∑' n:{n ∈ A|n > n₀}, a n - ∑' n:{n ∈ B|n > n₀}, a n := by abel
      _ = 0 + a n₀ + ∑' n:{n ∈ A|n > n₀}, a n - ∑' n:{n ∈ B|n > n₀}, a n := by
        congr; rw [sub_eq_zero]; apply tsum_congr_set_coe; grind
      _ ≥ 0 + a n₀ + 0 - ∑' n:{n|n > n₀}, a n := by
        gcongr; positivity
        calc
          _ = ∑' (n : {n ∈ B|n > n₀}), a n + ∑' (n : {n ∉ B|n > n₀}), a n := by
            apply h_decomp
            . ext n; simp; tauto
            intro n hn; simp at hn; tauto
          _ ≥ ∑' (n : {n ∈ B|n > n₀}), a n + 0 := by gcongr; solve_by_elim
          _ = _ := by simp
      _ = 0 + (10:ℝ)^(-(n₀:ℝ)) + 0 - (1 / (9:ℝ)) * (10:ℝ)^(-(n₀:ℝ)) := by
        congr
        set ι : ℕ → {n | n > n₀} := fun j ↦ ⟨ j+(n₀+1), by simp; linarith ⟩
        have hι : Function.Bijective ι := by
          split_ands
          . intro j k hjk; simpa [ι] using hjk
          intro ⟨ n, hn ⟩; simp [ι] at hn ⊢; use n - n₀ - 1; omega
        rw [←(Equiv.ofBijective ι hι).tsum_eq]
        simp [ι, a]
        calc
          _ = ∑' j:ℕ, (10:ℝ)^(-1-n₀:ℝ) * (1/(10:ℝ))^j := by
            apply tsum_congr; intro j
            simp only [Equiv.ofBijective, DFunLike.coe, EquivLike.coe]
            rw [pow_add, pow_add, rpow_sub, rpow_neg, rpow_one, rpow_natCast] <;> try positivity
            simp; congr
          _ = (10:ℝ)^(-1-n₀:ℝ) * ∑' j:ℕ, (1/(10:ℝ))^j := tsum_mul_left
          _ = _ := by
            rw [tsum_geometric_of_lt_one, (?_:-1 - (n₀:ℝ) = (-n₀:ℝ) + (-1:ℝ)),
                rpow_add, rpow_neg, rpow_natCast] <;> try positivity
            ring; abel; norm_num
      _ = (8 / (9:ℝ)) * (10:ℝ)^(-(n₀:ℝ)) := by ring
      _ > 0 := by positivity
    simp at this
  replace : EqualCard (Set ℕ) (Set.range f) := ⟨(Equiv.ofInjective _ this).toFun, (Equiv.ofInjective _ this).bijective⟩
  replace := (Uncountable.equiv this).mp Uncountable.power_set_nat
  contrapose this
  rw [not_uncountable_iff] at this ⊢
  haveI : Countable ℝ := this
  infer_instance

/-- Exercise 8.3.1 -/
noncomputable example {X:Type} [Finite X] : Nat.card (Set X) = 2 ^ Nat.card X := by
  haveI : Fintype X := (nonempty_fintype X).some
  have h := Fintype.card_set (α := X)
  simpa [Nat.card_eq_fintype_card] using h

open Classical in
/-- Exercise 8.3.2.  Some subtle type changes due to how sets are implemented in Mathlib. Also we shift the sequence {lit}`D` by one so that we can work in {lean}`Set A` rather than {lean}`Set B`. -/
theorem Schroder_Bernstein_lemma {X: Type} {A B C: Set X} (hAB: A ⊆ B) (hBC: B ⊆ C) (f: C ↪ A) :
  let D : ℕ → Set A := Nat.rec ((f.image ∘ ((B.embeddingOfSubset _ hBC).image)) {x:B | ↑x ∉ A}) (fun _ ↦ (f.image ∘ ((B.embeddingOfSubset _ hBC).image) ∘ (A.embeddingOfSubset _ hAB).image))
  Set.univ.PairwiseDisjoint D ∧
  let g : A → B := fun x ↦ if h: x ∈ ⋃ n, D n ∧ ∃ y:B, f ⟨↑y, hBC y.property⟩ = x then h.2.choose else ⟨ ↑x, hAB x.property ⟩
  Function.Bijective g
  := by
  let D : ℕ → Set A :=
    Nat.rec ((f.image ∘ ((B.embeddingOfSubset _ hBC).image)) {x:B | ↑x ∉ A})
      (fun _ ↦ (f.image ∘ ((B.embeddingOfSubset _ hBC).image) ∘ (A.embeddingOfSubset _ hAB).image))
  let g : A → B := fun x ↦ if h: x ∈ ⋃ n, D n ∧ ∃ y:B, f ⟨↑y, hBC y.property⟩ = x then h.2.choose else ⟨ ↑x, hAB x.property ⟩
  -- Characterize membership in D 0
  have hD0 {x : A} : x ∈ D 0 ↔ ∃ (y : B), y.val ∉ A ∧ f ⟨y.val, hBC y.property⟩ = x := by
    dsimp [D]
    simp [Set.mem_image, Set.mem_setOf_eq]
  have hD_succ {n : ℕ} {x : A} : x ∈ D (n+1) ↔ ∃ (z : A), z ∈ D n ∧ f ⟨z.val, hBC (hAB z.property)⟩ = x := by
    dsimp [D]
    simp [Set.mem_image, Set.mem_setOf_eq]

  -- All D n are subsets of A
  have hD_sub_A (n : ℕ) (x : A) (hx : x ∈ D n) : True := trivial

  -- D n are pairwise disjoint
  have h_disjoint : Set.univ.PairwiseDisjoint D := by
    intro i j hi hj hne
    rw [Set.disjoint_iff_inter_eq_empty (s := D i) (t := D j)]
    ext x; constructor
    · intro hx
      exfalso
      rcases hx with ⟨hxi, hxj⟩
      wlog hlt : i < j generalizing i j
      · apply this j i hj hi hne.symm hxj hxi; omega
      induction' j with k ih generalizing i
      · omega
      · by_cases hik : i < k
        · exact ih hik hxi hxj
        · have heq : i = k := by omega
          subst heq
          -- Now we have x ∈ D i and x ∈ D (i+1) and need a contradiction
          rcases hD_succ.mp hxj with ⟨z, hz, hz'⟩
          rcases hD0.mp hxi with ⟨y, hy, hy'⟩
          have hyz : y.val = z.val := by
            apply f.injective
            calc
              f ⟨y.val, hBC y.property⟩ = x := hy'
              _ = f ⟨z.val, hBC (hAB z.property)⟩ := hz'.symm
          have hzA : z.val ∈ A := z.property
          have hy_notA : y.val ∉ A := hy
          rw [hyz] at hy_notA
          exact hy_notA hzA
    · intro hx; exact (Set.not_mem_empty x hx).elim

  -- Forward lemma: if x ∈ D n, then ∃ y ∈ B, f(embed(y)) = x
  have h_fwd (n : ℕ) {x : A} (hx : x ∈ D n) : ∃ y : B, f ⟨y.val, hBC y.property⟩ = x := by
    induction' n with k ih generalizing x
    · rcases hD0.mp hx with ⟨y, hy, hy'⟩; exact ⟨y, hy'⟩
    · rcases hD_succ.mp hx with ⟨z, hz, hz'⟩
      rcases ih hz with ⟨y, hy⟩
      refine ⟨y, ?_⟩
      calc
        f ⟨y.val, hBC y.property⟩ = z := hy
        _ = x := hz'.symm

  -- Key lemma for injectivity: if a₁ ∈ D k and f(embed(a₂)) = a₁ with a₂ ∈ A, then a₂ ∈ ⋃ D n
  have h_key {a₁ a₂ : A} (k : ℕ) (h₁ : a₁ ∈ D k) (h_eq : f ⟨a₂.val, hBC (hAB a₂.property)⟩ = a₁) :
    a₂ ∈ ⋃ n, D n := by
    induction' k with k ih generalizing a₁ a₂
    · rcases hD0.mp h₁ with ⟨y, hy, hy'⟩
      have hyz : y = a₂ := by
        apply f.injective
        calc
          f ⟨y.val, hBC y.property⟩ = a₁ := hy'
          _ = f ⟨a₂.val, hBC (hAB a₂.property)⟩ := h_eq.symm
      have hy_notA : y.val ∉ A := hy
      have ha₂A : a₂.val ∈ A := a₂.property
      rw [hyz] at hy_notA
      exact (hy_notA ha₂A).elim
    · rcases hD_succ.mp h₁ with ⟨z, hz, hz'⟩
      have hzy : z = a₂ := by
        apply f.injective
        calc
          f ⟨z.val, hBC (hAB z.property)⟩ = a₁ := hz'
          _ = f ⟨a₂.val, hBC (hAB a₂.property)⟩ := h_eq.symm
      subst hzy
      exact Set.mem_iUnion.mpr ⟨k, hz⟩

  -- Injectivity of g
  have h_inj : Function.Injective g := by
    intro a₁ a₂ h_eq
    by_cases h₁ : a₁ ∈ ⋃ n, D n
    · rcases h₁ with ⟨k, hk⟩
      have hy₁ : ∃ y : B, f ⟨y.val, hBC y.property⟩ = a₁ := h_fwd k hk
      have h_and₁ : a₁ ∈ ⋃ n, D n ∧ ∃ y : B, f ⟨y.val, hBC y.property⟩ = a₁ := ⟨Set.mem_iUnion.mpr ⟨k, hk⟩, hy₁⟩
      have hg₁ : g a₁ = choose h_and₁.2 := by
        dsimp [g]; simp [h_and₁]
      by_cases h₂ : a₂ ∈ ⋃ n, D n
      · rcases h₂ with ⟨l, hl⟩
        have hy₂ : ∃ y : B, f ⟨y.val, hBC y.property⟩ = a₂ := h_fwd l hl
        have h_and₂ : a₂ ∈ ⋃ n, D n ∧ ∃ y : B, f ⟨y.val, hBC y.property⟩ = a₂ := ⟨Set.mem_iUnion.mpr ⟨l, hl⟩, hy₂⟩
        have hg₂ : g a₂ = choose h_and₂.2 := by
          dsimp [g]; simp [h_and₂]
        have hy_eq : choose h_and₁.2 = choose h_and₂.2 := by
          calc
            choose h_and₁.2 = g a₁ := hg₁.symm
            _ = g a₂ := h_eq
            _ = choose h_and₂.2 := hg₂
        have ha_eq : a₁ = a₂ := by
          calc
            a₁ = f ⟨(choose h_and₁.2).val, hBC (choose h_and₁.2).property⟩ := (choose_spec h_and₁.2).symm
            _ = f ⟨(choose h_and₂.2).val, hBC (choose h_and₂.2).property⟩ := by rw [hy_eq]
            _ = a₂ := choose_spec h_and₂.2
        exact ha_eq
      · have hg_a₂ : g a₂ = ⟨a₂.val, hAB a₂.property⟩ := by
          simp [g, h₂]
        have hy_eq_a₂ : (choose h_and₁.2 : B) = ⟨a₂.val, hAB a₂.property⟩ := by
          calc
            (choose h_and₁.2 : B) = g a₁ := hg₁
            _ = g a₂ := h_eq
            _ = ⟨a₂.val, hAB a₂.property⟩ := hg_a₂
        have ha₁_eq_f_a₂ : f ⟨a₂.val, hBC (hAB a₂.property)⟩ = a₁ := by
          calc
            f ⟨a₂.val, hBC (hAB a₂.property)⟩ = f ⟨(choose h_and₁.2).val, hBC (choose h_and₁.2).property⟩ := by
              congr; exact Subtype.ext_iff.mp hy_eq_a₂
            _ = a₁ := choose_spec h_and₁.2
        have h_a₂_in_union : a₂ ∈ ⋃ n, D n := h_key k hk ha₁_eq_f_a₂
        exact h₂ h_a₂_in_union
    · by_cases h₂ : a₂ ∈ ⋃ n, D n
      · rcases h₂ with ⟨l, hl⟩
        have hy₂ : ∃ y : B, f ⟨y.val, hBC y.property⟩ = a₂ := h_fwd l hl
        have h_and₂ : a₂ ∈ ⋃ n, D n ∧ ∃ y : B, f ⟨y.val, hBC y.property⟩ = a₂ := ⟨Set.mem_iUnion.mpr ⟨l, hl⟩, hy₂⟩
        have hg₂ : g a₂ = choose h_and₂.2 := by
          dsimp [g]; simp [h_and₂]
        have hg_a₁ : g a₁ = ⟨a₁.val, hAB a₁.property⟩ := by
          simp [g, h₁]
        have hy_eq_a₁ : (choose h_and₂.2 : B) = ⟨a₁.val, hAB a₁.property⟩ := by
          calc
            (choose h_and₂.2 : B) = g a₂ := hg₂
            _ = g a₁ := h_eq.symm
            _ = ⟨a₁.val, hAB a₁.property⟩ := hg_a₁
        have ha₂_eq_f_a₁ : f ⟨a₁.val, hBC (hAB a₁.property)⟩ = a₂ := by
          calc
            f ⟨a₁.val, hBC (hAB a₁.property)⟩ = f ⟨(choose h_and₂.2).val, hBC (choose h_and₂.2).property⟩ := by
              congr; exact Subtype.ext_iff.mp hy_eq_a₁
            _ = a₂ := choose_spec h_and₂.2
        have h_a₁_in_union : a₁ ∈ ⋃ n, D n := h_key l hl ha₂_eq_f_a₁
        exact h₁ h_a₁_in_union
      · have hg₁ : g a₁ = ⟨a₁.val, hAB a₁.property⟩ := by
          simp [g, h₁]
        have hg₂ : g a₂ = ⟨a₂.val, hAB a₂.property⟩ := by
          simp [g, h₂]
        have h_eq_val : a₁.val = a₂.val := by
          calc
            a₁.val = (g a₁).val := by simp [hg₁]
            _ = (g a₂).val := by rw [h_eq]
            _ = a₂.val := by simp [hg₂]
        exact Subtype.ext h_eq_val

  -- Surjectivity of g
  have h_surj : Function.Surjective g := by
    intro b
    by_cases hbA : b.val ∈ A
    · -- b ∈ A, so b : A
      let a : A := ⟨b.val, hbA⟩
      by_cases hb_union : a ∈ ⋃ n, D n
      · -- g(f(b)) = b
        let a' : A := f ⟨b.val, hBC b.property⟩
        have ha'_union : a' ∈ ⋃ n, D n := by
          rcases hb_union with ⟨n, hn⟩
          refine ⟨n+1, ?_⟩
          apply hD_succ.mpr
          exact ⟨a, hn, rfl⟩
        have h_ex : ∃ y : B, f ⟨y.val, hBC y.property⟩ = a' := ⟨b, rfl⟩
        have h_and : a' ∈ ⋃ n, D n ∧ ∃ y : B, f ⟨y.val, hBC y.property⟩ = a' := ⟨ha'_union, h_ex⟩
        have hg_a' : g a' = b := by
          dsimp [g, a']; simp [h_and]
          apply Subtype.ext; apply f.injective
          calc
            f ⟨(choose h_and.2).val, hBC (choose h_and.2).property⟩ = a' := choose_spec h_and.2
            _ = f ⟨b.val, hBC b.property⟩ := rfl
        exact ⟨a', hg_a'⟩
      · -- g(b) = b
        have hg_a : g a = b := by
          dsimp [g, a]; simp [hb_union]
          exact Subtype.ext rfl
        exact ⟨a, hg_a⟩
    · -- b ∉ A, so b ∈ B \ A
      have hb_notA : b.val ∉ A := hbA
      let a' : A := f ⟨b.val, hBC b.property⟩
      have ha'_D0 : a' ∈ D 0 := by
        apply hD0.mpr
        exact ⟨b, hb_notA, rfl⟩
      have ha'_union : a' ∈ ⋃ n, D n := ⟨0, ha'_D0⟩
      have h_ex : ∃ y : B, f ⟨y.val, hBC y.property⟩ = a' := ⟨b, rfl⟩
      have h_and : a' ∈ ⋃ n, D n ∧ ∃ y : B, f ⟨y.val, hBC y.property⟩ = a' := ⟨ha'_union, h_ex⟩
      have hg_a' : g a' = b := by
        dsimp [g, a']; simp [h_and]
        apply Subtype.ext; apply f.injective
        calc
          f ⟨(choose h_and.2).val, hBC (choose h_and.2).property⟩ = a' := choose_spec h_and.2
          _ = f ⟨b.val, hBC b.property⟩ := rfl
      exact ⟨a', hg_a'⟩

  exact ⟨h_disjoint, ⟨h_inj, h_surj⟩⟩

abbrev LeCard (X Y: Type) : Prop := ∃ f: X → Y, Function.Injective f

/-- Exercise 8.3.3 -/
theorem Schroder_Bernstein {X Y:Type} (hXY : LeCard X Y) (hYX : LeCard Y X) : EqualCard X Y := by
  rcases hXY with ⟨f, hf⟩
  rcases hYX with ⟨g, hg⟩
  have h_mk_eq : Cardinal.mk X = Cardinal.mk Y := by
    apply le_antisymm
    · exact Cardinal.mk_le_of_injective hf
    · exact Cardinal.mk_le_of_injective hg
  rcases (Cardinal.eq.mp h_mk_eq) with ⟨e⟩
  exact ⟨e, e.bijective⟩

abbrev LtCard (X Y: Type) : Prop := LeCard X Y ∧ ¬ EqualCard X Y

/-- Exercise 8.3.4 -/
example {X:Type} : LtCard X (Set X) := by
  refine ⟨?_, ?_⟩
  · refine ⟨fun x ↦ {x}, ?_⟩
    intro a b h; exact Set.singleton_injective h
  · intro h
    have := EqualCard.power_set_false X
    exact this h.symm

example {A B C: Type} (hAB: LtCard A B) (hBC: LtCard B C) :
  LtCard A C := by
  rcases hAB with ⟨⟨f, hf⟩, hne_AB⟩
  rcases hBC with ⟨⟨g, hg⟩, hne_BC⟩
  refine ⟨⟨g ∘ f, hg.comp hf⟩, ?_⟩
  intro heq_AC
  apply hne_AB
  rcases heq_AC with ⟨h, hh⟩
  have h_BA : LeCard B A := by
    let h_inv : C → A := fun c => (hh.surjective c).choose
    have h_inv_spec : ∀ c, h (h_inv c) = c := fun c => (hh.surjective c).choose_spec
    have h_inv_inj : Function.Injective h_inv := by
      intro x y hxy
      calc
        x = h (h_inv x) := (h_inv_spec x).symm
        _ = h (h_inv y) := by rw [hxy]
        _ = y := h_inv_spec y
    refine ⟨h_inv ∘ g, h_inv_inj.comp hg⟩
  exact Schroder_Bernstein ⟨f, hf⟩ h_BA

abbrev CardOrder : Preorder Type := {
  le := LeCard
  lt := LtCard
  le_refl := by
    intro X; refine ⟨id, ?_⟩; exact Function.injective_id
  le_trans := by
    intro X Y Z ⟨f, hf⟩ ⟨g, hg⟩; refine ⟨g ∘ f, ?_⟩; exact hg.comp hf
  lt_iff_le_not_ge := by
    intro X Y; constructor
    · intro ⟨hle, hne⟩; refine ⟨hle, ?_⟩
      intro hge; apply hne
      rcases hge with ⟨f, hf⟩
      rcases hle with ⟨g, hg⟩
      have h_eq : EqualCard X Y := Schroder_Bernstein ⟨g, hg⟩ ⟨f, hf⟩
      exact h_eq
    · intro ⟨hle, hng⟩; refine ⟨hle, ?_⟩
      intro heq; apply hng
      rcases heq with ⟨f, hf⟩
      exact ⟨f, hf.injective⟩
}

/-- Exercise 8.3.5 -/
example (X:Type) : ¬ CountablyInfinite (Set X) := by
  intro h
  have h_count_X : Countable (Set X) := CountablyInfinite.toCountable h
  have h_uncountable : Uncountable (Set ℕ) := Uncountable.power_set_nat
  have h_not_count_ℕ : ¬ Countable (Set ℕ) := by
    rw [← AtMostCountable.iff, ← Uncountable.iff, not_not]
    exact h_uncountable
  by_cases hX_inf : Infinite X
  · have h_emb : ℕ ↪ X := by infer_instance
    have h_set_emb : Set ℕ → Set X := fun s ↦ h_emb '' s
    have h_inj : Function.Injective h_set_emb := by
      intro s t h_eq
      apply Set.image_injective h_emb.injective
      exact h_eq
    have h_count_ℕ : Countable (Set ℕ) :=
      Countable.of_injective h_set_emb h_inj
    exact h_not_count_ℕ h_count_ℕ
  · have h_fin_X : Finite X := by
      by_contra! h
      apply hX_inf
      rw [not_finite_iff_infinite] at h
      exact h
    have h_fin_set : Finite (Set X) := by infer_instance
    have h_inf_set : Infinite (Set X) := CountablyInfinite.toInfinite h
    have : ¬ Finite (Set X) := by rwa [not_finite_iff_infinite]
    exact this h_fin_set

end Chapter8
