import Mathlib.Tactic
import Mathlib.Data.Rat.Denumerable
import Mathlib.Data.Finite.Defs

/-!
# Analysis I, Section 8.1: Countability

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Custom notions for "equal cardinality", "countable", and "at most countable".  Note that Mathlib's
{name}`Countable` typeclass corresponds to what we call "at most countable" in this text.
- Countability of the integers and rationals.

Note that as the Chapter 3 set theory has been deprecated, we will not re-use relevant constructions from that theory here, replacing them with Mathlib counterparts instead.

-/

namespace Chapter8

/-- The definition of equal cardinality. For simplicity we restrict attention to the Type 0 universe.
This is analogous to `Chapter3.SetTheory.Set.EqualCard`, but we are not using the latter since
the Chapter 3 set theory is deprecated. -/
abbrev EqualCard (X Y : Type) : Prop := ∃ f : X → Y, Function.Bijective f

/-- Relation with Mathlib's {name}`Equiv` concept -/
theorem EqualCard.iff {X Y : Type} : EqualCard X Y ↔ Nonempty (X ≃ Y) := by
  simp [EqualCard]; constructor
  . intro ⟨ f, hf ⟩; exact ⟨ .ofBijective f hf ⟩
  intro ⟨ e ⟩; exact ⟨ e.toFun, e.bijective ⟩

/-- Equivalence with Mathlib's {name}`Cardinal.mk` concept -/
theorem EqualCard.iff' {X Y : Type} : EqualCard X Y ↔ Cardinal.mk X = Cardinal.mk Y := by
  simp [Cardinal.eq, iff]

theorem EqualCard.refl (X : Type) : EqualCard X X :=
  ⟨ id, Function.bijective_id ⟩

theorem EqualCard.symm {X Y : Type} (hXY : EqualCard X Y) : EqualCard Y X := by
  rcases hXY with ⟨ f, hf ⟩
  exact ⟨ (Equiv.ofBijective f hf).symm, (Equiv.ofBijective f hf).symm.bijective ⟩

theorem EqualCard.trans {X Y Z : Type} (hXY : EqualCard X Y) (hYZ : EqualCard Y Z) :
  EqualCard X Z := by
  rcases hXY with ⟨ f, hf ⟩
  rcases hYZ with ⟨ g, hg ⟩
  exact ⟨ g ∘ f, (Equiv.ofBijective g hg).bijective.comp (Equiv.ofBijective f hf).bijective ⟩

instance EqualCard.instSetoid : Setoid Type := ⟨ EqualCard, ⟨ refl, symm, trans ⟩ ⟩

theorem EqualCard.univ (X : Type) : EqualCard (.univ : Set X) X :=
  ⟨ Subtype.val, Subtype.val_injective, by intro _; aesop ⟩

abbrev CountablyInfinite (X : Type) : Prop := EqualCard X ℕ

abbrev AtMostCountable (X : Type) : Prop := CountablyInfinite X ∨ Finite X

theorem CountablyInfinite.equiv {X Y: Type} (hXY : EqualCard X Y) :
  CountablyInfinite X ↔ CountablyInfinite Y := ⟨ hXY.symm.trans, hXY.trans ⟩

theorem Finite.equiv {X Y: Type} (hXY : EqualCard X Y) :
  Finite X ↔ Finite Y := by obtain ⟨ f, hf ⟩ := hXY; exact (Equiv.ofBijective f hf).finite_iff

theorem AtMostCountable.equiv {X Y: Type} (hXY : EqualCard X Y) :
  AtMostCountable X ↔ AtMostCountable Y := by
  simp [AtMostCountable, CountablyInfinite.equiv hXY, Finite.equiv hXY]

/-- Equivalence with Mathlib's {name}`Denumerable` concept (cf. Remark 8.1.2) -/
theorem CountablyInfinite.iff (X : Type) : CountablyInfinite X ↔ Nonempty (Denumerable X) := by
  simp [CountablyInfinite, EqualCard.iff]; constructor
  . intro ⟨ e ⟩; exact ⟨ Denumerable.mk' e ⟩
  intro ⟨ h ⟩; exact ⟨ h.eqv X ⟩

/-- Equivalence with Mathlib's {name}`Countable` typeclass -/
theorem CountablyInfinite.iff' (X : Type) : CountablyInfinite X ↔ Countable X ∧ Infinite X := by
  rw [iff, nonempty_denumerable_iff]

theorem CountablyInfinite.toCountable {X : Type} (hX: CountablyInfinite X) : Countable X := by
  simp_all [iff']

theorem CountablyInfinite.toInfinite {X : Type} (hX: CountablyInfinite X) : Infinite X := by
  simp_all [iff']

theorem AtMostCountable.iff (X : Type) : AtMostCountable X ↔ Countable X := by
  observe h1 : CountablyInfinite X ↔ Countable X ∧ Infinite X
  observe h2 : Finite X ∨ Infinite X
  observe h3 : Finite X → Countable X
  tauto

theorem CountablyInfinite.iff_image_inj {A:Type} (X: Set A) : CountablyInfinite X ↔ ∃ f : ℕ ↪ A, X = f '' .univ := by
  constructor
  . intro ⟨ g, hg ⟩
    choose f hleft hright using Function.bijective_iff_has_inverse.mp hg
    refine ⟨ ⟨ Subtype.val ∘ f, ?_ ⟩, ?_ ⟩
    . intro x y hxy; apply hright.injective; simp_all [Subtype.val_inj]
    ext; simp; constructor
    . intro hx; use g ⟨ _, hx ⟩; simp [hleft _]
    rintro ⟨ _, rfl ⟩; aesop
  intro ⟨ f, hf ⟩
  have := Function.leftInverse_invFun (Function.Embedding.injective f)
  use (Function.invFun f) ∘ Subtype.val; split_ands
  . rintro ⟨ x, hx ⟩ ⟨ y, hy ⟩ h; grind
  intro n; use ⟨ f n, by aesop ⟩; grind

/-- Examples 8.1.3 -/
example : CountablyInfinite ℕ := by
  unfold CountablyInfinite; exact EqualCard.refl ℕ

example : CountablyInfinite (.univ \ {0}: Set ℕ) := by
  rw [CountablyInfinite, EqualCard.iff]
  refine ⟨ ?_ ⟩
  refine {
    toFun := λ ⟨ x, hx ⟩ => x - 1
    invFun := λ n => ⟨ n+1, by simp ⟩
    left_inv := λ ⟨ x, hx ⟩ => by
      have hx0 : x ≠ 0 := by
        intro hzero; apply hx.2; simp [hzero]
      have hx1 : 1 ≤ x := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hx0)
      ext; exact Nat.sub_add_cancel hx1
    right_inv := λ n => by simp
  }

example : CountablyInfinite ((fun n:ℕ ↦ 2*n) '' .univ) := by
  set S := (fun n : ℕ ↦ 2*n) '' .univ with hS
  refine ⟨ fun (x : S) => x.val / 2, ?_ ⟩
  constructor
  · intro x y h
    ext
    have hx_mem' : x.val ∈ (fun n : ℕ ↦ 2*n) '' Set.univ := by
      simpa [hS] using x.property
    have hy_mem' : y.val ∈ (fun n : ℕ ↦ 2*n) '' Set.univ := by
      simpa [hS] using y.property
    rcases hx_mem' with ⟨ nx, _, hx_eq' ⟩
    rcases hy_mem' with ⟨ ny, _, hy_eq' ⟩
    have hx_eq : x.val = 2*nx := hx_eq'.symm
    have hy_eq : y.val = 2*ny := hy_eq'.symm
    have hdiv : (2*nx)/2 = (2*ny)/2 := by
      calc
        (2*nx)/2 = x.val / 2 := by rw [hx_eq]
        _ = y.val / 2 := h
        _ = (2*ny)/2 := by rw [hy_eq]
    have hpos : nx = ny := by omega
    calc
      x.val = 2*nx := hx_eq
      _ = 2*ny := by rw [hpos]
      _ = y.val := by rw [hy_eq]
  · intro n
    refine ⟨ ⟨ 2*n, by simp [hS] ⟩, ?_ ⟩
    simp


/-- Proposition 8.1.4 (Well ordering principle / Exercise 8.1.2 -/
theorem Nat.exists_unique_min {X : Set ℕ} (hX : X.Nonempty) :
  ∃! m ∈ X, ∀ n ∈ X, m ≤ n := by
  classical
  set m := Nat.find hX with hm
  have hm_mem : m ∈ X := Nat.find_spec hX
  have hm_min : ∀ n ∈ X, m ≤ n := by
    intro n hn; exact Nat.find_min' hX hn
  refine ⟨ m, ⟨ hm_mem, hm_min ⟩, ?_ ⟩
  intro m' ⟨ hm'_mem, hm'_min ⟩
  have hmm' : m ≤ m' := Nat.find_min' hX hm'_mem
  have hm'm : m' ≤ m := hm'_min m hm_mem
  omega

def Int.exists_unique_min : Decidable (∀ (X : Set ℤ) (_hX : X.Nonempty), ∃! m ∈ X, ∀ n ∈ X, m ≤ n) := by
  apply isFalse
  intro h
  have huniv_nonempty : (Set.univ : Set ℤ).Nonempty := ⟨ 0, by simp ⟩
  rcases h (Set.univ : Set ℤ) huniv_nonempty with ⟨ m, hm, hm_unique ⟩
  have hm_mem : m ∈ (Set.univ : Set ℤ) := hm.1
  have hm_min : ∀ n ∈ (Set.univ : Set ℤ), m ≤ n := hm.2
  have hm1_mem : m - 1 ∈ (Set.univ : Set ℤ) := by simp
  have hm1_le : m ≤ m - 1 := hm_min (m - 1) hm1_mem
  omega

def NNRat.exists_unique_min : Decidable (∀ (X : Set NNRat) (_hX : X.Nonempty), ∃! m ∈ X, ∀ n ∈ X, m ≤ n) := by
  apply isFalse
  intro h
  let X : Set NNRat := { x | x > 0 }
  have hX_nonempty : X.Nonempty := ⟨ 1, by norm_num [X] ⟩
  rcases h X hX_nonempty with ⟨ m, hm, hm_unique ⟩
  have hm_mem : m ∈ X := hm.1
  have hm_min : ∀ n ∈ X, m ≤ n := hm.2
  have hm_pos : m > 0 := hm_mem
  have hm_half_pos : m / 2 > 0 := by positivity
  have hm_half_mem : m / 2 ∈ X := hm_half_pos
  have hm_half_le : m ≤ m / 2 := hm_min (m / 2) hm_half_mem
  have hm_half_lt_m : m / 2 < m := by
    exact half_lt_self hm_pos
  have : m < m := lt_of_le_of_lt hm_half_le hm_half_lt_m
  exact lt_irrefl _ this


open Classical in
noncomputable abbrev Nat.min (X : Set ℕ) : ℕ := if hX : X.Nonempty then (exists_unique_min hX).exists.choose else 0

theorem Nat.min_spec {X : Set ℕ} (hX : X.Nonempty) : min X ∈ X ∧ ∀ n ∈ X, min X ≤ n := by
  simp [hX, min]; exact (exists_unique_min hX).exists.choose_spec

theorem Nat.min_eq {X : Set ℕ} (hX : X.Nonempty) {a:ℕ} (ha : a ∈ X ∧ ∀ n ∈ X, a ≤ n) : min X = a :=
  (exists_unique_min hX).unique (min_spec hX) ha

@[simp]
theorem Nat.min_empty : min ∅ = 0 := by simp [Nat.min]

example : Nat.min ((fun n ↦ 2*n) '' (.Ici 1)) = 2 := by
  have hX : ((fun n ↦ 2*n) '' (.Ici 1) : Set ℕ).Nonempty := ⟨ 2, 1, by simp, by norm_num ⟩
  apply Nat.min_eq hX
  constructor
  · refine ⟨ 1, by simp, ?_ ⟩
    norm_num
  · rintro _ ⟨ n, hn, rfl ⟩
    have : 1 ≤ n := hn
    nlinarith

theorem Nat.min_eq_sInf {X : Set ℕ} (hX : X.Nonempty) : min X = sInf X := by
  apply le_antisymm
  · have h_sInf_mem : sInf X ∈ X := Nat.sInf_mem hX
    exact (Nat.min_spec hX).2 _ h_sInf_mem
  · exact Nat.sInf_le ((Nat.min_spec hX).1)

open Classical in
/-- Equivalence with Mathlib's {name}`Nat.find` method -/
theorem Nat.min_eq_find {X : Set ℕ} (hX : X.Nonempty) : min X = Nat.find hX := by
  symm; rw [Nat.find_eq_iff]; have := min_spec hX; grind

/-- Proposition 8.1.5 -/
theorem Nat.monotone_enum_of_infinite (X : Set ℕ) [Infinite X] : ∃! f : ℕ → X, Function.Bijective f ∧ StrictMono f := by
  -- This proof is written to follow the structure of the original text.
  let a : ℕ → ℕ := Nat.strongRec (fun n a ↦ min { x ∈ X | ∀ (m:ℕ) (h:m < n), x ≠ a m h })
  have ha : ∀ n, a n = min { x ∈ X | ∀ (m:ℕ) (h:m < n), x ≠ a m } := Nat.strongRec.eq_def _
  have ha_infinite (n:ℕ) : Infinite { x ∈ X | ∀ (m:ℕ) (h:m < n), x ≠ a m } := by
    have h_finite_aim : Set.Finite {a m | m < n} :=
      (Set.finite_lt_nat n).image a
    have h_set : Set.Infinite ({ x ∈ X | ∀ (m:ℕ) (h:m < n), x ≠ a m } : Set ℕ) := by
      intro hfinite
      have h_subset : (X : Set ℕ) ⊆ ({ x ∈ X | ∀ (m:ℕ) (h:m < n), x ≠ a m } : Set ℕ) ∪ {a m | m < n} := by
        intro x hx; simp
        by_cases h : ∀ (m : ℕ), m < n → x ≠ a m
        · exact Or.inl ⟨ hx, h ⟩
        · have h' : ∃ m, m < n ∧ x = a m := by
            push_neg at h; exact h
          rcases h' with ⟨ m, hm, hx_eq ⟩; exact Or.inr ⟨ m, hm, hx_eq.symm ⟩
      have h_finite_X : Set.Finite (X : Set ℕ) :=
        Set.Finite.subset (Set.Finite.union hfinite h_finite_aim) h_subset
      have hX_infinite_set : Set.Infinite (X : Set ℕ) :=
        Set.infinite_coe_iff.mp (by infer_instance : Infinite (Subtype (· ∈ X)))
      exact hX_infinite_set h_finite_X
    exact h_set.to_subtype
  have ha_nonempty (n:ℕ) : { x ∈ X | ∀ (m:ℕ) (h:m < n), x ≠ a m }.Nonempty :=
    Set.Nonempty.of_subtype
  have haX (n:ℕ) : a n ∈ X := by
    rw [ha n]
    have h_nonempty : { x ∈ X | ∀ (m:ℕ) (h:m < n), x ≠ a m }.Nonempty := ha_nonempty n
    exact (Nat.min_spec h_nonempty).1.1
  have ha_mono : StrictMono a := by
    intro i j h
    have ha_j_mem_j : a j ∈ { x ∈ X | ∀ (m:ℕ) (h:m < j), x ≠ a m } := by
      rw [ha j]
      exact (Nat.min_spec (ha_nonempty j)).1
    have ha_j_mem_i : a j ∈ { x ∈ X | ∀ (k:ℕ) (h:k < i), x ≠ a k } := by
      refine ⟨ haX j, λ k hk => ?_ ⟩
      exact ha_j_mem_j.2 k (Nat.lt_trans hk h)
    have ha_i_min : ∀ x ∈ { x ∈ X | ∀ (k:ℕ) (h:k < i), x ≠ a k }, a i ≤ x := by
      intro x hx
      have hmin := (Nat.min_spec (ha_nonempty i)).2 x hx
      rw [← ha i] at hmin
      exact hmin
    have ha_i_le_aj : a i ≤ a j := ha_i_min _ ha_j_mem_i
    have ha_i_ne_aj : a i ≠ a j := by
      intro h_eq
      have : a j ≠ a i := ha_j_mem_j.2 i h
      exact this h_eq.symm
    omega
  have ha_injective : Function.Injective a := ha_mono.injective
  set f : ℕ → X := fun n ↦ ⟨ a n, haX n ⟩
  have hf_injective : Function.Injective f := by
    intro x y hxy; simp [f] at hxy; solve_by_elim
  have hf_surjective : Function.Surjective f := by
    intro ⟨ x, hx ⟩; simp [f]; by_contra h
    have h1 (n:ℕ) : x ∈ { x ∈ X | ∀ (m:ℕ) (h:m < n), x ≠ a m } := by
      refine ⟨ hx, λ m hm h_eq => ?_ ⟩
      exact h ⟨ m, h_eq.symm ⟩
    have h2 (n:ℕ) : x ≥ a n := by
      rw [ha n]; exact ge_iff_le.mpr ((Nat.min_spec (ha_nonempty n)).2 _ (h1 n))
    have h3 (n:ℕ) : a n ≥ n := by
      induction' n with k ih
      · omega
      · have : a k < a (k+1) := ha_mono (Nat.lt_succ_self k)
        omega
    have h4 (n:ℕ) : x ≥ n := (h3 n).trans (h2 n)
    linarith [h4 (x+1)]
  apply ExistsUnique.intro _ ⟨ ⟨ hf_injective, hf_surjective ⟩, ha_mono ⟩
  intro g ⟨ hg_bijective, hg_mono ⟩; by_contra!
  replace : { n | g n ≠ f n }.Nonempty := by
    contrapose! this
    apply funext; simpa [Set.eq_empty_iff_forall_notMem] using this
  set m := min { n | g n ≠ f n }
  have hm : g m ≠ f m := (min_spec this).1
  have hm' {n:ℕ} (hn: n < m) : g n = f n := by by_contra hgfn; linarith [(min_spec this).2 n (by simp [hgfn])]
  have hgm : g m = min { x ∈ X | ∀ (n:ℕ) (h:n < m), x ≠ a n } := by
    set S := { x ∈ X | ∀ (n:ℕ) (h:n < m), x ≠ a n } with hS
    have hS_nonempty : S.Nonempty := ha_nonempty m
    have h_minS_spec := Nat.min_spec hS_nonempty
    have h_minS_mem_S : min S ∈ S := h_minS_spec.1
    have h_minS_min : ∀ x ∈ S, min S ≤ x := h_minS_spec.2
    have h_minS_X : min S ∈ X := h_minS_mem_S.1
    have h_gm_val_mem_S : (g m : ℕ) ∈ S := by
      refine ⟨ (g m).property, λ n hn h_eq => ?_ ⟩
      have h_gn_eq_fn : g n = f n := hm' hn
      have h_gm_val_eq_gn_val : (g m : ℕ) = (g n : ℕ) := by
        calc
          (g m : ℕ) = a n := h_eq
          _ = (f n : ℕ) := by simp [f]
          _ = (g n : ℕ) := by simp [h_gn_eq_fn]
      have h_gm_eq_gn : g m = g n := Subtype.val_injective h_gm_val_eq_gn_val
      have h_mn : m = n := hg_bijective.injective h_gm_eq_gn
      omega
    have h_minS_le_gm_val : min S ≤ (g m : ℕ) := h_minS_min _ h_gm_val_mem_S
    have h_surj_g : Function.Surjective g := hg_bijective.surjective
    have h_exists_k : ∃ k, g k = ⟨ min S, h_minS_X ⟩ := h_surj_g ⟨ min S, h_minS_X ⟩
    rcases h_exists_k with ⟨ k, h_gk_eq ⟩
    have h_gmk_eq_minS : (g k : ℕ) = min S := by simp [h_gk_eq]
    have h_gm_val_le_minS : (g m : ℕ) ≤ min S := by
      by_cases hk_lt_m : k < m
      · exfalso
        have h_gk_eq_fk : g k = f k := hm' hk_lt_m
        have : min S = a k := by
          calc
            min S = (g k : ℕ) := by symm; exact h_gmk_eq_minS
            _ = (f k : ℕ) := by simp [h_gk_eq_fk]
            _ = a k := rfl
        have h_minS_ne_ak : min S ≠ a k := h_minS_mem_S.2 k hk_lt_m
        exact h_minS_ne_ak this
      · by_cases hm_lt_k : m < k
        · have h_gm_lt_gk : (g m : ℕ) < (g k : ℕ) := by exact_mod_cast hg_mono hm_lt_k
          have : (g m : ℕ) < min S := by
            calc
              (g m : ℕ) < (g k : ℕ) := h_gm_lt_gk
              _ = min S := h_gmk_eq_minS
          omega
        · have hm_eq_k : m = k := by omega
          subst hm_eq_k
          simp [h_gmk_eq_minS]
    apply le_antisymm h_gm_val_le_minS h_minS_le_gm_val
  rw [←ha m] at hgm; contrapose! hm; exact Subtype.val_injective hgm

theorem Nat.countable_of_infinite (X : Set ℕ) [Infinite X] : CountablyInfinite X := by
  have := (monotone_enum_of_infinite X).exists
  exact EqualCard.symm ⟨ this.choose, this.choose_spec.1 ⟩

/-- Corollary 8.1.6 -/
theorem Nat.atMostCountable_subset (X: Set ℕ) : AtMostCountable X := by
  obtain _ | _ := finite_or_infinite X
  . tauto
  simp [AtMostCountable, countable_of_infinite]

/-- Corollary 8.1.7 -/
theorem AtMostCountable.subset {X: Type} (hX : AtMostCountable X) (Y: Set X) : AtMostCountable Y := by
  rw [AtMostCountable.iff] at hX ⊢
  haveI : Countable X := hX
  infer_instance

theorem AtMostCountable.subset' {A: Type} {X Y: Set A} (hX: AtMostCountable X) (hY: Y ⊆ X) : AtMostCountable Y := by
  refine' (equiv ⟨ fun y ↦ ⟨ ↑↑y, y.property ⟩, _, _ ⟩).mp (subset hX { x : X | ↑x ∈ Y })
  . intro ⟨ ⟨ _, _ ⟩, _ ⟩ ⟨ ⟨ _, _ ⟩, _ ⟩ _; simp_all
  intro ⟨ y, hy ⟩; use ⟨ ⟨ y, hY hy ⟩, by aesop ⟩

/-- Proposition 8.1.8 / Exercise 8.1.4 -/
theorem AtMostCountable.image_nat (Y: Type) (f: ℕ → Y) : AtMostCountable (f '' .univ) := by
  rw [AtMostCountable.iff]
  have h : (Set.range f).Countable := Set.countable_range f
  simpa using Set.countable_coe_iff.mpr (by simpa using h : (f '' Set.univ).Countable)

/-- Corollary 8.1.9 / Exercise 8.1.5 -/
theorem AtMostCountable.image {X:Type} (hX: CountablyInfinite X) {Y: Type} (f: X → Y) : AtMostCountable (f '' .univ) := by
  rw [AtMostCountable.iff]
  have hX_data := (CountablyInfinite.iff' X).mp hX
  haveI : Countable X := hX_data.1
  have h : (Set.range f).Countable := Set.countable_range f
  simpa using Set.countable_coe_iff.mpr (by simpa using h : (f '' Set.univ).Countable)

/-- Proposition 8.1.10 / Exercise 8.1.7 -/
theorem CountablyInfinite.union {A:Type} {X Y: Set A} (hX: CountablyInfinite X) (hY: CountablyInfinite Y) :
  CountablyInfinite (X ∪ Y: Set A) := by
  rw [CountablyInfinite.iff']
  have hX_data := (CountablyInfinite.iff' (X : Set A)).mp hX
  have hY_data := (CountablyInfinite.iff' (Y : Set A)).mp hY
  have h_countable : Countable (X ∪ Y : Set A) :=
    Set.Countable.union hX_data.1 hY_data.1
  have h_infinite : Infinite (X ∪ Y : Set A) := by
    by_contra! hfinite
    have hX_sub_XY : X ⊆ X ∪ Y := by
      intro x hx; exact Or.inl hx
    have hX_finite_set : Set.Finite (X : Set A) :=
      Set.Finite.subset (Set.finite_coe_iff.mp hfinite) hX_sub_XY
    have hX_finite : Finite (X : Set A) := Set.finite_coe_iff.mp hX_finite_set
    exact hX_data.2.not_finite hX_finite
  exact ⟨ h_countable, h_infinite ⟩

/-- Corollary 8.1.11 --/
theorem Int.countablyInfinite : CountablyInfinite ℤ := by
  have h1 : CountablyInfinite {n:ℤ | n ≥ 0} := by
    rw [CountablyInfinite.iff_image_inj]
    use ⟨ (· : ℕ → ℤ), by intro _ _ _; simp_all ⟩
    ext n; simp; refine ⟨ ?_, by aesop ⟩
    . intro h; use n.toNat; simp [h]
  have h2 : CountablyInfinite {n:ℤ | n ≤ 0} := by
    rw [CountablyInfinite.iff_image_inj]
    use ⟨ (-· : ℕ → ℤ), by intro _ _ _; simp_all ⟩
    ext n; simp; refine ⟨ ?_, by aesop ⟩
    intro h; use (-n).toNat; simp [h]
  have : CountablyInfinite (.univ : Set ℤ) := by
    convert h1.union h2; ext; simp; omega
  rwa [←CountablyInfinite.equiv (.univ _)]

/-- Lemma 8.1.12 -/
theorem CountablyInfinite.lower_diag : CountablyInfinite { n : ℕ × ℕ | n.2 ≤ n.1 } := by
  let A := { n : ℕ × ℕ | n.2 ≤ n.1 }
  let a : ℕ → ℕ := fun n ↦ ∑ m ∈ .range (n+1), m
  have ha_lt_succ (n : ℕ) : a n < a (n+1) := by
    calc
      a (n+1) = a n + (n+1) := by simp [a, Finset.sum_range_succ]
      _ > a n := by omega
  have ha : StrictMono a := strictMono_nat_of_lt_succ ha_lt_succ
  let f : A → ℕ := fun ⟨ (n, m), _ ⟩ ↦ a n + m
  have hf : Function.Injective f := by
    rintro ⟨ ⟨ n, m ⟩, hnm ⟩ ⟨ ⟨ n',m'⟩, hnm' ⟩ h
    simp [A,f] at hnm hnm' ⊢ h
    obtain hnn' | rfl | hnn' := lt_trichotomy n n'
    . have : a n' + m' > a n + m := by calc
        _ ≥ a n' := by linarith
        _ ≥ a (n+1) := ha.monotone (by linarith)
        _ = a n + (n + 1) := Finset.sum_range_succ id _
        _ > a n + m := by linarith
      linarith
    . simpa using h
    have : a n + m > a n' + m' := by calc
        _ ≥ a n := by linarith
        _ ≥ a (n'+1) := ha.monotone (by linarith)
        _ = a n' + (n' + 1) := Finset.sum_range_succ id _
        _ > a n' + m' := by linarith
    linarith
  let f' : A → f '' .univ := fun p ↦ ⟨ f p, by aesop ⟩
  have hf' : Function.Bijective f' := by
    constructor
    . intro p q hpq; simp [f'] at hpq; solve_by_elim
    intro ⟨ l, hl ⟩; simp at hl
    obtain ⟨ n, m, q, rfl ⟩ := hl; use ⟨ (n, m), q ⟩
  have : AtMostCountable A := by rw [AtMostCountable.equiv ⟨ _, hf' ⟩]; apply Nat.atMostCountable_subset
  have hfin : ¬ Finite A := by
    intro hA
    have h_subset : Set.range (fun n : ℕ ↦ (n, 0)) ⊆ A := by
      rintro x ⟨ n, rfl ⟩; simp [A]
    have hA_finite_set : Set.Finite (A : Set (ℕ × ℕ)) := hA
    have h_range_finite : Set.Finite (Set.range (fun n : ℕ ↦ (n, 0))) :=
      Set.Finite.subset hA_finite_set h_subset
    have h_inj : Function.Injective (fun n : ℕ ↦ (n, 0)) := by
      intro a b h; simpa using h
    have h_range_infinite : Set.Infinite (Set.range (fun n : ℕ ↦ (n, 0))) := by
      intro hfinite
      have h_finite_range : Finite (Set.range (fun n : ℕ ↦ (n, 0))) :=
        Set.finite_coe_iff.mp hfinite
      haveI : Finite (Set.range (fun n : ℕ ↦ (n, 0))) := h_finite_range
      let f : ℕ → Set.range (fun n : ℕ ↦ (n, 0)) := fun n ↦ ⟨(n, 0), ⟨n, rfl⟩⟩
      have hf_inj : Function.Injective f := by
        intro a b h
        apply h_inj
        exact congr_arg Subtype.val h
      have : Finite ℕ :=
        Finite.of_injective f hf_inj
      exact not_finite ℕ
    exact h_range_infinite h_range_finite
  simp [AtMostCountable] at this; tauto

/-- Corollary 8.1.13 -/
theorem CountablyInfinite.prod_nat : CountablyInfinite (ℕ × ℕ) := by
  have upper_diag : CountablyInfinite { n : ℕ × ℕ | n.1 ≤ n.2 } := by
    refine (equiv ⟨ fun ⟨ (n, m), _ ⟩ ↦ ⟨ (m, n), by aesop ⟩, ?_, ?_ ⟩).mp lower_diag
    . intro ⟨ (_, _), _ ⟩ ⟨ (_, _), _ ⟩ _; aesop
    intro ⟨ (n, m), _ ⟩; use ⟨ (m, n), by aesop ⟩
  have : CountablyInfinite (.univ : Set (ℕ × ℕ)) := by
    convert union lower_diag upper_diag; ext ⟨ n, m ⟩; simp; omega
  exact (equiv (.univ _)).mp this

/-- Corollary 8.1.14 / Exercise 8.1.8 -/
theorem CountablyInfinite.prod {X Y:Type} (hX: CountablyInfinite X) (hY: CountablyInfinite Y) :
  CountablyInfinite (X × Y) := by
  rcases (CountablyInfinite.iff X).mp hX with ⟨ eX ⟩
  rcases (CountablyInfinite.iff Y).mp hY with ⟨ eY ⟩
  haveI := eX; haveI := eY
  rw [CountablyInfinite.iff]
  exact ⟨ inferInstance ⟩

/-- Corollary 8.1.15 -/
theorem Rat.countablyInfinite : CountablyInfinite ℚ := by
  -- This proof is written to follow the structure of the original text.
  have : CountablyInfinite { n:ℤ | n ≠ 0 } := by
    have h_at_most : AtMostCountable ({ n : ℤ | n ≠ 0 } : Set ℤ) :=
      AtMostCountable.subset (Or.inl Int.countablyInfinite) ({ n : ℤ | n ≠ 0 } : Set ℤ)
    have h_infinite : Set.Infinite ({ n : ℤ | n ≠ 0 } : Set ℤ) := by
      have h_inj : Function.Injective (fun (n : ℕ) ↦ (n+1 : ℤ)) := by
        intro a b h
        have h' : (a : ℤ) = (b : ℤ) := by
          linarith
        exact_mod_cast h'
      have : Set.Infinite (Set.range (fun (n : ℕ) ↦ (n+1 : ℤ))) := by
        intro hfinite
        have h_finite_range : Finite (Set.range (fun (n : ℕ) ↦ (n+1 : ℤ))) :=
          Set.finite_coe_iff.mp hfinite
        have : Finite ℕ := by
          haveI := h_finite_range
          let f : ℕ → Set.range (fun (n : ℕ) ↦ (n+1 : ℤ)) := fun n => ⟨(n+1 : ℤ), Set.mem_range_self n⟩
          refine Finite.of_injective f ?_
          intro a b h
          apply h_inj
          exact congr_arg Subtype.val h
        exact not_finite ℕ
      have h_subset : Set.range (fun (n : ℕ) ↦ (n+1 : ℤ)) ⊆ { n : ℤ | n ≠ 0 } := by
        rintro x ⟨ n, rfl ⟩
        have : (n : ℤ) + 1 ≠ 0 := by
          omega
        exact this
      exact this.mono h_subset
    rcases h_at_most with (h | h)
    · exact h
    · exfalso; exact h_infinite (Set.finite_coe_iff.mp h)
  apply Int.countablyInfinite.prod at this
  let f : ℤ × { n:ℤ | n ≠ 0 } → ℚ := fun (a,b) ↦ (a/b:ℚ)
  replace := AtMostCountable.image this f
  have h : f '' .univ = .univ := by
    ext q; constructor
    · rintro ⟨ ⟨ a, b ⟩, _, rfl ⟩; trivial
    · intro hq
      have h_den_ne_zero : (q.den : ℤ) ≠ 0 := by
        intro hzero
        have : q.den = 0 := by exact_mod_cast hzero
        exact q.den_pos.ne' this
      refine ⟨(q.num, ⟨ (q.den : ℤ), h_den_ne_zero ⟩), Set.mem_univ _, ?_⟩
      simp [f, q.num_div_den]
  rcases this with h1 | h2
  · have h1' : CountablyInfinite (Set.univ : Set ℚ) := h ▸ h1
    rwa [CountablyInfinite.equiv (EqualCard.univ _)] at h1'
  · have h2' : Finite (Set.univ : Set ℚ) := h ▸ h2
    rw [Set.finite_coe_iff, Set.finite_univ_iff] at h2'
    exact absurd h2' (not_finite_iff_infinite.mpr inferInstance)

/-- Exercise 8.1.1 -/
example (X: Type) : Infinite X ↔ ∃ Y : Set X, Y ≠ .univ ∧ EqualCard Y X := by
  constructor
  · intro hX
    have h_nonempty : Nonempty X := by infer_instance
    let x := h_nonempty.some
    set Y := Set.univ \ {x} with hY
    have hY_ne_univ : Y ≠ .univ := by simp [hY]
    have hX_set : Set.Infinite (Set.univ : Set X) := Set.infinite_univ
    have h_card_eq : Cardinal.mk Y = Cardinal.mk X := by
      have hX_infinite_card : Cardinal.aleph0 ≤ Cardinal.mk X := by
        haveI : Infinite X := hX
        exact Cardinal.aleph0_le_mk X
      have h_add_one_X : Cardinal.mk X + 1 = Cardinal.mk X :=
        Cardinal.add_one_eq hX_infinite_card
      have h_equiv : X ≃ (Y : Type) ⊕ PUnit := by
        classical
        refine
        { toFun := λ a => if h : a = x then Sum.inr PUnit.unit else Sum.inl ⟨a, by
            simp [hY, h]
          ⟩
          invFun := λ s => s.elim Subtype.val (λ _ => x)
          left_inv := λ a => by
            by_cases h : a = x
            · simp [h]
            · simp [h]
          right_inv := λ s => by
            rcases s with (⟨y, hy⟩ | ⟨⟩)
            · have hyx : y ≠ x := by
                rw [hY] at hy
                simpa using hy.2
              simp [hyx]
            · simp
        }
      have h_card_split : Cardinal.mk X = Cardinal.mk (Y : Type) + 1 := by
        calc
          Cardinal.mk X = Cardinal.mk ((Y : Type) ⊕ PUnit) :=
            Cardinal.mk_congr h_equiv
          _ = Cardinal.mk (Y : Type) + Cardinal.mk (PUnit : Type) := by
            simp [Cardinal.lift_id, Cardinal.mk_sum (Y : Type) (PUnit : Type)]
          _ = Cardinal.mk Y + 1 := by simp
      have hY_add_one_eq_X_add_one : Cardinal.mk Y + 1 = Cardinal.mk X + 1 := by
        calc
          Cardinal.mk Y + 1 = Cardinal.mk X := h_card_split.symm
          _ = Cardinal.mk X + 1 := by symm; exact h_add_one_X
      exact Cardinal.add_one_inj.mp hY_add_one_eq_X_add_one
    refine ⟨ Y, hY_ne_univ, (EqualCard.iff' (X := Y) (Y := X)).mpr h_card_eq ⟩
  · intro ⟨ Y, hY_ne, hY_eq ⟩
    by_contra! h_finite
    haveI : Finite X := h_finite
    have hY_finite_set : Set.Finite (Y : Set X) :=
      Set.Finite.subset (Set.finite_univ : Set.Finite (Set.univ : Set X)) (Set.subset_univ _)
    haveI : Finite Y := Set.finite_coe_iff.mp hY_finite_set
    haveI : Fintype X := Fintype.ofFinite _
    haveI : Fintype Y := Fintype.ofFinite _
    have h_card_eq : Fintype.card Y = Fintype.card X := by
      have h_card_eq' : Cardinal.mk Y = Cardinal.mk X := (EqualCard.iff' (X := Y) (Y := X)).mp hY_eq
      simpa [Cardinal.mk_fintype] using h_card_eq'
    have hss : (Y : Set X) ⊂ Set.univ := by
      rw [Set.ssubset_univ_iff]; exact hY_ne
    have h_card_lt : Fintype.card Y < Fintype.card X := by
      have h_nat_lt : Nat.card (Y : Set X) < Nat.card (Set.univ : Set X) :=
        Set.Finite.card_lt_card (Set.finite_univ : Set.Finite (Set.univ : Set X)) hss
      simpa using h_nat_lt
    linarith

/-- Exercise 8.1.6 -/
example (A: Type) : AtMostCountable A ↔ ∃ f : A → ℕ, Function.Injective f := by
  constructor
  · intro h
    rcases h with (h' | h')
    · rcases (CountablyInfinite.iff A).mp h' with ⟨ h_denom ⟩
      exact ⟨ h_denom.eqv, h_denom.eqv.injective ⟩
    · haveI : Finite A := h'
      haveI : Fintype A := Fintype.ofFinite A
      refine ⟨ λ a => ((Fintype.equivFin A) a).val, ?_ ⟩
      intro a b h
      apply (Fintype.equivFin A).injective
      exact Fin.ext h
  · intro ⟨ f, hf ⟩
    have h_range_countable : AtMostCountable (Set.range f : Set ℕ) :=
      Nat.atMostCountable_subset (Set.range f)
    have hA_eq : EqualCard A (Set.range f) := by
      refine ⟨ λ a => ⟨ f a, by simp ⟩, ?_, ?_ ⟩
      · intro a b h; apply hf; exact congrArg Subtype.val h
      · intro ⟨ y, hy ⟩; rcases hy with ⟨ a, rfl ⟩; exact ⟨ a, rfl ⟩
    exact (AtMostCountable.equiv hA_eq).mpr h_range_countable

/-- Exercise 8.1.9 -/
example {I X:Type} (hI: AtMostCountable I) (A: I → Set X) (hA: ∀ i, AtMostCountable (A i)) :
  AtMostCountable (⋃ i, A i) := by
  haveI : Countable I := by rwa [AtMostCountable.iff] at hI
  have hA_countable_set : ∀ i, (A i).Countable := by
    intro i
    have hA_countable : Countable (Subtype (A i)) := (AtMostCountable.iff (Subtype (A i))).mp (hA i)
    exact Set.countable_coe_iff.mpr hA_countable
  have h_union_countable_set : (⋃ i, A i).Countable := by
    simpa [Set.biUnion_eq_iUnion] using
      Set.Countable.biUnion (Set.countable_univ (α := I)) (by
        intro i hi; exact hA_countable_set i)
  have h_union_countable : Countable (Subtype (⋃ i, A i)) :=
    Set.countable_coe_iff.mp h_union_countable_set
  rwa [AtMostCountable.iff]

/-- Exercise 8.1.10.  Note the lack of the `noncomputable` keyword in the {lit}`abbrev`. -/
abbrev explicit_bijection : ℕ → ℚ := (Denumerable.eqv (α := ℚ)).symm

theorem explicit_bijection_spec : Function.Bijective explicit_bijection :=
  (Denumerable.eqv (α := ℚ)).symm.bijective

end Chapter8
