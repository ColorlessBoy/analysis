import Mathlib.Tactic
import Analysis.Section_3_3
import Analysis.Section_3_5

/-!
# Analysis I, Section 3.6: Cardinality of sets

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.


Main constructions and results of this section:

- Cardinality of a set
- Finite and infinite sets
- Connections with Mathlib equivalents

After this section, these notions will be deprecated in favor of their Mathlib equivalents.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter3

export SetTheory (Set Object nat)

variable [SetTheory]

/-- Definition 3.6.1 (Equal cardinality) -/
abbrev SetTheory.Set.EqualCard (X Y:Set) : Prop := ∃ f : X → Y, Function.Bijective f

/-- Example 3.6.2 -/
theorem SetTheory.Set.Example_3_6_2 : EqualCard {0,1,2} {3,4,5} := by
  use open Classical in fun x ↦
    ⟨if x.val = 0 then 3 else if x.val = 1 then 4 else 5, by aesop⟩
  constructor
  · intro; aesop
  intro y
  have : y = (3: Object) ∨ y = (4: Object) ∨ y = (5: Object) := by
    have := y.property
    aesop
  rcases this with (_ | _ | _)
  · use ⟨0, by simp⟩; aesop
  · use ⟨1, by simp⟩; aesop
  · use ⟨2, by simp⟩; aesop

/-- Example 3.6.3 -/
theorem SetTheory.Set.Example_3_6_3 : EqualCard nat (nat.specify (fun x ↦ Even (x:ℕ))) := by sorry

@[refl]
theorem SetTheory.Set.EqualCard.refl (X:Set) : EqualCard X X := by
  sorry

@[symm]
theorem SetTheory.Set.EqualCard.symm {X Y:Set} (h: EqualCard X Y) : EqualCard Y X := by
  sorry

@[trans]
theorem SetTheory.Set.EqualCard.trans {X Y Z:Set} (h1: EqualCard X Y) (h2: EqualCard Y Z) : EqualCard X Z := by
  sorry

/-- Proposition 3.6.4 / Exercise 3.6.1 -/
instance SetTheory.Set.EqualCard.inst_setoid : Setoid SetTheory.Set := ⟨ EqualCard, {refl, symm, trans} ⟩

/-- Definition 3.6.5 -/
abbrev SetTheory.Set.has_card (X:Set) (n:ℕ) : Prop := X ≈ Fin n

theorem SetTheory.Set.has_card_iff (X:Set) (n:ℕ) :
    X.has_card n ↔ ∃ f: X → Fin n, Function.Bijective f := by
  simp [has_card, HasEquiv.Equiv, instHasEquivOfSetoid, Setoid.r, EqualCard]

/-- Remark 3.6.6 -/
theorem SetTheory.Set.Remark_3_6_6 (n:ℕ) :
    (nat.specify (fun x ↦ 1 ≤ (x:ℕ) ∧ (x:ℕ) ≤ n)).has_card n := by sorry

/-- Example 3.6.7 -/
theorem SetTheory.Set.Example_3_6_7a (a:Object) : ({a}:Set).has_card 1 := by
  rw [has_card_iff]
  use fun _ ↦ Fin_mk _ 0 (by simp)
  constructor
  · intro x1 x2 hf; aesop
  intro y
  use ⟨a, by simp⟩
  have := Fin.toNat_lt y
  simp_all

theorem SetTheory.Set.Example_3_6_7b {a b c d:Object} (hab: a ≠ b) (hac: a ≠ c) (had: a ≠ d)
    (hbc: b ≠ c) (hbd: b ≠ d) (hcd: c ≠ d) : ({a,b,c,d}:Set).has_card 4 := by
  rw [has_card_iff]
  use open Classical in fun x ↦ Fin_mk _ (
    if x.val = a then 0 else if x.val = b then 1 else if x.val = c then 2 else 3
  ) (by aesop)
  constructor
  · intro x1 x2 hf; aesop
  intro y
  have : y = (0:ℕ) ∨ y = (1:ℕ) ∨ y = (2:ℕ) ∨ y = (3:ℕ) := by
    have := Fin.toNat_lt y
    omega
  rcases this with (_ | _ | _ | _)
  · use ⟨a, by aesop⟩; aesop
  · use ⟨b, by aesop⟩; aesop
  · use ⟨c, by aesop⟩; aesop
  · use ⟨d, by aesop⟩; aesop

/-- Lemma 3.6.9 -/
theorem SetTheory.Set.pos_card_nonempty {n:ℕ} (h: n ≥ 1) {X:Set} (hX: X.has_card n) : X ≠ ∅ := by
  -- This proof is written to follow the structure of the original text.
  by_contra! this
  have hnon : Fin n ≠ ∅ := by
    apply nonempty_of_inhabited (x := 0); rw [mem_Fin]; use 0, (by omega); rfl
  rw [has_card_iff] at hX
  choose f hf using hX
  sorry
  -- obtain a contradiction from the fact that `f` is a bijection from the empty set to a
  -- non-empty set.

/-- Exercise 3.6.2a -/
theorem SetTheory.Set.has_card_zero {X:Set} : X.has_card 0 ↔ X = ∅ := by sorry

/-- Lemma 3.6.9 -/
theorem SetTheory.Set.card_erase {n:ℕ} (h: n ≥ 1) {X:Set} (hX: X.has_card n) (x:X) :
    (X \ {x.val}).has_card (n-1) := by
  -- This proof has been rewritten from the original text to try to make it friendlier to
  -- formalize in Lean.
  rw [has_card_iff] at hX; choose f hf using hX
  set X' : Set := X \ {x.val}
  set ι : X' → X := fun ⟨y, hy⟩ ↦ ⟨ y, by aesop ⟩
  observe hι : ∀ x:X', (ι x:Object) = x
  choose m₀ hm₀ hm₀f using (mem_Fin _ _).mp (f x).property
  set g : X' → Fin (n-1) := fun x' ↦
    let := Fin.toNat_lt (f (ι x'))
    let : (f (ι x'):ℕ) ≠ m₀ := by
      by_contra!; simp [←this, Subtype.val_inj, hf.1.eq_iff, ι] at hm₀f
      have := x'.property; aesop
    if h' : f (ι x') < m₀ then Fin_mk _ (f (ι x')) (by omega)
    else Fin_mk _ (f (ι x') - 1) (by omega)
  have hg_def (x':X') : if (f (ι x'):ℕ) < m₀ then (g x':ℕ) = f (ι x') else (g x':ℕ) = f (ι x') - 1 := by
    split_ifs with h' <;> simp [g,h']
  have hg : Function.Bijective g := by sorry
  use g

/-- Proposition 3.6.8 (Uniqueness of cardinality) -/
theorem SetTheory.Set.card_uniq {X:Set} {n m:ℕ} (h1: X.has_card n) (h2: X.has_card m) : n = m := by
  -- This proof is written to follow the structure of the original text.
  revert X m; induction' n with n hn
  . intro _ _ h1 h2; rw [has_card_zero] at h1; contrapose! h1
    apply pos_card_nonempty _ h2; omega
  intro X m h1 h2
  have : X ≠ ∅ := pos_card_nonempty (by omega) h1
  choose x hx using nonempty_def this
  have : m ≠ 0 := by contrapose! this; simpa [has_card_zero, this] using h2
  specialize hn (card_erase ?_ h1 ⟨ _, hx ⟩) (card_erase ?_ h2 ⟨ _, hx ⟩) <;> omega

lemma SetTheory.Set.Example_3_6_8_a: ({0,1,2}:Set).has_card 3 := by
  rw [has_card_iff]
  have : ({0, 1, 2}: Set) = SetTheory.Set.Fin 3 := by
    ext x
    simp only [mem_insert, mem_singleton, mem_Fin]
    constructor
    · aesop
    rintro ⟨x, ⟨_, rfl⟩⟩
    simp only [nat_coe_eq_iff]
    omega
  rw [this]
  use id
  exact Function.bijective_id

lemma SetTheory.Set.Example_3_6_8_b: ({3,4}:Set).has_card 2 := by
  rw [has_card_iff]
  use open Classical in fun x ↦ Fin_mk _ (if x = (3:Object) then 0 else 1) (by aesop)
  constructor
  · intro x1 x2
    aesop
  intro y
  have := Fin.toNat_lt y
  have : y = (0:ℕ) ∨ y = (1:ℕ) := by omega
  aesop

lemma SetTheory.Set.Example_3_6_8_c : ¬({0,1,2}:Set) ≈ ({3,4}:Set) := by
  by_contra h
  have h1 : Fin 3 ≈ Fin 2 := (Example_3_6_8_a.symm.trans h).trans Example_3_6_8_b
  have h2 : Fin 3 ≈ Fin 3 := by rfl
  have := card_uniq h1 h2
  contradiction

abbrev SetTheory.Set.finite (X:Set) : Prop := ∃ n:ℕ, X.has_card n

abbrev SetTheory.Set.infinite (X:Set) : Prop := ¬ finite X

/-- Exercise 3.6.3, phrased using Mathlib natural numbers -/
theorem SetTheory.Set.bounded_on_finite {n:ℕ} (f: Fin n → nat) : ∃ M, ∀ i, (f i:ℕ) ≤ M := by sorry

/-- Theorem 3.6.12 -/
theorem SetTheory.Set.nat_infinite : infinite nat := by
  -- This proof is written to follow the structure of the original text.
  by_contra this; choose n hn using this
  simp [has_card] at hn; symm at hn; simp [HasEquiv.Equiv] at hn
  choose f hf using hn; choose M hM using bounded_on_finite f
  replace hf := hf.surjective ↑(M+1); contrapose! hf
  peel hM with hi; contrapose! hi
  apply_fun nat_equiv.symm at hi; simp_all

open Classical in
/-- It is convenient for Lean purposes to give infinite sets the "junk" cardinality of zero. -/
noncomputable def SetTheory.Set.card (X:Set) : ℕ := if h:X.finite then h.choose else 0

theorem SetTheory.Set.has_card_card {X:Set} (hX: X.finite) : X.has_card (SetTheory.Set.card X) := by
  simp [card, hX, hX.choose_spec]

theorem SetTheory.Set.has_card_to_card {X:Set} {n: ℕ}: X.has_card n → X.card = n := by
  intro h; simp [card, card_uniq (⟨ n, h ⟩:X.finite).choose_spec h]; aesop

theorem SetTheory.Set.card_to_has_card {X:Set} {n: ℕ} (hn: n ≠ 0): X.card = n → X.has_card n
  := by grind [card, has_card_card]

theorem SetTheory.Set.card_fin_eq (n:ℕ): (Fin n).has_card n := (has_card_iff _ _).mp ⟨ id, Function.bijective_id ⟩

theorem SetTheory.Set.Fin_card (n:ℕ): (Fin n).card = n := has_card_to_card (card_fin_eq n)

theorem SetTheory.Set.Fin_finite (n:ℕ): (Fin n).finite := ⟨n, card_fin_eq n⟩

theorem SetTheory.Set.EquivCard_to_has_card_eq {X Y:Set} {n: ℕ} (h: X ≈ Y): X.has_card n ↔ Y.has_card n := by
  choose f hf using h; let e := Equiv.ofBijective f hf
  constructor <;> (intro h'; rw [has_card_iff] at *; choose g hg using h')
  . use e.symm.trans (.ofBijective _ hg); apply Equiv.bijective
  . use e.trans (.ofBijective _ hg); apply Equiv.bijective

theorem SetTheory.Set.EquivCard_to_card_eq {X Y:Set} (h: X ≈ Y): X.card = Y.card := by
  by_cases hX: X.finite <;> by_cases hY: Y.finite <;> try rw [finite] at hX hY
  . choose nX hXn using hX; choose nY hYn using hY
    simp [has_card_to_card hXn, has_card_to_card hYn, EquivCard_to_has_card_eq h] at *
    solve_by_elim [card_uniq]
  . choose nX hXn using hX; rw [EquivCard_to_has_card_eq h] at hXn; tauto
  . choose nY hYn using hY; rw [←EquivCard_to_has_card_eq h] at hYn; tauto
  simp [card, hX, hY]

/-- Exercise 3.6.2 -/
theorem SetTheory.Set.empty_iff_card_eq_zero {X:Set} : X = ∅ ↔ X.finite ∧ X.card = 0 := by
  sorry

lemma SetTheory.Set.empty_of_card_eq_zero {X:Set} (hX : X.finite) : X.card = 0 → X = ∅ := by
  intro h
  rw [empty_iff_card_eq_zero]
  exact ⟨hX, h⟩

lemma SetTheory.Set.finite_of_empty {X:Set} : X = ∅ → X.finite := by
  intro h
  rw [empty_iff_card_eq_zero] at h
  exact h.1

lemma SetTheory.Set.card_eq_zero_of_empty {X:Set} : X = ∅ → X.card = 0 := by
  intro h
  rw [empty_iff_card_eq_zero] at h
  exact h.2

@[simp]
lemma SetTheory.Set.empty_finite : (∅: Set).finite := finite_of_empty rfl

@[simp]
lemma SetTheory.Set.empty_card_eq_zero : (∅: Set).card = 0 := card_eq_zero_of_empty rfl

/-- Proposition 3.6.14 (a) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_insert {X:Set} (hX: X.finite) {x:Object} (hx: x ∉ X) :
    (X ∪ {x}).finite ∧ (X ∪ {x}).card = X.card + 1 := by sorry

/-- Proposition 3.6.14 (b) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_union {X Y:Set} (hX: X.finite) (hY: Y.finite) :
    (X ∪ Y).finite ∧ (X ∪ Y).card ≤ X.card + Y.card := by sorry

/-- Proposition 3.6.14 (b) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_union_disjoint {X Y:Set} (hX: X.finite) (hY: Y.finite)
  (hdisj: Disjoint X Y) : (X ∪ Y).card = X.card + Y.card := by sorry

/-- Proposition 3.6.14 (c) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_subset {X Y:Set} (hX: X.finite) (hY: Y ⊆ X) :
    Y.finite ∧ Y.card ≤ X.card := by sorry

/-- Proposition 3.6.14 (c) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_ssubset {X Y:Set} (hX: X.finite) (hY: Y ⊂ X) :
    Y.card < X.card := by sorry

/-- Proposition 3.6.14 (d) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_image {X Y:Set} (hX: X.finite) (f: X → Y) :
    (image f X).finite ∧ (image f X).card ≤ X.card := by sorry

/-- Proposition 3.6.14 (d) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_image_inj {X Y:Set} (hX: X.finite) {f: X → Y}
  (hf: Function.Injective f) : (image f X).card = X.card := by sorry

/-- Proposition 3.6.14 (e) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_prod {X Y:Set} (hX: X.finite) (hY: Y.finite) :
    (X ×ˢ Y).finite ∧ (X ×ˢ Y).card = X.card * Y.card := by sorry

noncomputable def SetTheory.Set.pow_fun_equiv {A B : Set} : ↑(A ^ B) ≃ (B → A) where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

lemma SetTheory.Set.pow_fun_eq_iff {A B : Set} (x y : ↑(A ^ B)) : x = y ↔ pow_fun_equiv x = pow_fun_equiv y := by
  rw [←pow_fun_equiv.apply_eq_iff_eq]

theorem SetTheory.Set.pow_prod_pow_EqualCard_pow_union (A B C:Set) (hd: Disjoint B C) :
    EqualCard ((A ^ B) ×ˢ (A ^ C)) (A ^ (B ∪ C)) := by
  classical
  have h_disj_empty : B ∩ C = ∅ := by
    rw [← disjoint_iff]
    exact hd
  -- Step 1: ↑(X ×ˢ Y) ≃ (↑X × ↑Y)
  let prod_equiv : ↑((A ^ B) ×ˢ (A ^ C)) ≃ (↑(A ^ B) × ↑(A ^ C)) := {
    toFun := λ p => (fst p, snd p)
    invFun := λ ⟨p1, p2⟩ => mk_cartesian p1 p2
    left_inv := by intro p; simp
    right_inv := by intro p; simp
  }
  -- Step 2: apply pow_fun_equiv componentwise
  let pow_equiv : (↑(A ^ B) × ↑(A ^ C)) ≃ ((B → A) × (C → A)) := {
    toFun := λ ⟨f, g⟩ => (pow_fun_equiv f, pow_fun_equiv g)
    invFun := λ ⟨f, g⟩ => ((pow_fun_equiv (A := A) (B := B)).symm f, (pow_fun_equiv (A := A) (B := C)).symm g)
    left_inv := by intro p; simp
    right_inv := by intro p; simp
  }
  -- Step 3: glue/split functions across disjoint union
  let BUC : Set := B ∪ C
  let union_equiv : ((B → A) × (C → A)) ≃ (BUC → A) := {
    toFun := λ ⟨f, g⟩ => λ (bc : BUC) =>
      if hB : bc.val ∈ B then f ⟨bc.val, hB⟩
      else
        have hC : bc.val ∈ C := by
          rcases (mem_union bc.val B C).mp bc.property with (h | h)
          · exact absurd h hB
          · exact h
        g ⟨bc.val, hC⟩
    invFun := λ h => (
      λ b => h ⟨b.val, (mem_union b.val B C).mpr (Or.inl b.property)⟩,
      λ c => h ⟨c.val, (mem_union c.val B C).mpr (Or.inr c.property)⟩
    )
    left_inv := by
      rintro ⟨f, g⟩
      apply Prod.ext
      · ext b
        dsimp
        split_ifs with hB
        · rfl
        · exact absurd b.property hB
      · ext c
        dsimp
        split_ifs with hB
        · have hmem_inter : c.val ∈ B ∩ C := by
            rw [mem_inter]; exact ⟨hB, c.property⟩
          rw [h_disj_empty] at hmem_inter
          exact absurd hmem_inter (not_mem_empty _)
        · rfl
    right_inv := by
      intro h
      ext bc
      dsimp
      split_ifs with hB
      · have h_mem : bc.val ∈ BUC := (mem_union bc.val B C).mpr (Or.inl hB)
        have h_eq : (⟨bc.val, h_mem⟩ : BUC) = bc := Subtype.ext rfl
        simp [h_eq]
      · have hC : bc.val ∈ C := by
          rcases (mem_union bc.val B C).mp bc.property with (h | h)
          · exact absurd h hB
          · exact h
        have h_mem : bc.val ∈ BUC := (mem_union bc.val B C).mpr (Or.inr hC)
        have h_eq : (⟨bc.val, h_mem⟩ : BUC) = bc := Subtype.ext rfl
        simp [h_eq]
  }
  -- Step 4: convert back from function to power set
  let e := prod_equiv.trans (pow_equiv.trans (union_equiv.trans (pow_fun_equiv (A := A) (B := BUC)).symm))
  use e; exact e.bijective

/-- Proposition 3.6.14 (f) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_pow {X Y:Set} (hY: Y.finite) (hX: X.finite) :
    (Y ^ X).finite ∧ (Y ^ X).card = Y.card ^ X.card := by
  classical
  have hYc := has_card_card hY
  have hXc := has_card_card hX
  -- Singleton lemma: Y^{x} has the same cardinality as Y
  have h_singleton (x : Object) : (Y ^ ({x} : Set)).finite ∧ (Y ^ ({x} : Set)).card = Y.card := by
    have h_equiv : (Y ^ ({x} : Set)) ≈ Y := by
      let e : ↑(Y ^ ({x} : Set)) ≃ ↑Y :=
        (pow_fun_equiv (A := Y) (B := ({x} : Set))).trans {
          toFun := λ f => f ⟨x, by simp⟩
          invFun := λ y _ => y
          left_inv := by
            intro f
            ext s
            have hs_val : s.val = x := by
              have hm := s.property
              rw [mem_singleton] at hm
              exact hm
            have h_eq : s = (⟨x, by simp⟩ : ({x} : Set)) := Subtype.ext hs_val
            rw [h_eq]
          right_inv := by intro y; rfl
        }
      use e; exact e.bijective
    have h_fin : (Y ^ ({x} : Set)).finite :=
      ⟨Y.card, ((EquivCard_to_has_card_eq h_equiv).mpr hYc)⟩
    have h_card : (Y ^ ({x} : Set)).card = Y.card := EquivCard_to_card_eq h_equiv
    exact ⟨h_fin, h_card⟩
  -- Main induction: ∀ S ⊆ X with has_card k, the result holds for S
  have h_main : ∀ (k : ℕ) (S : Set), S ⊆ X → S.has_card k →
      ((Y ^ S).finite ∧ (Y ^ S).card = Y.card ^ k) := by
    intro k S hS_sub hSk
    induction' k with k ih generalizing S
    · -- k = 0: S = ∅, Y^∅ is a singleton
      have hS_empty : S = ∅ := has_card_zero.mp hSk
      subst hS_empty
      have h_equiv : (Y ^ (∅ : Set)) ≈ ({0} : Set) := by
        let e : ↑(Y ^ (∅ : Set)) ≃ ↑({0} : Set) := {
          toFun := λ _ => ⟨0, by simp⟩
          invFun := λ _ => (pow_fun_equiv (A := Y) (B := (∅ : Set))).symm (λ x => by
            exfalso; exact (not_mem_empty _) x.property)
          left_inv := by
            intro f
            apply (pow_fun_equiv (A := Y) (B := (∅ : Set))).injective
            ext x
            exfalso; exact (not_mem_empty _) x.property
          right_inv := by
            intro y
            apply Subtype.ext
            have hy := y.property
            rw [mem_singleton] at hy
            simp [hy]
        }
        use e; exact e.bijective
      have h_card_one : (Y ^ (∅ : Set)).card = 1 := by
        rw [EquivCard_to_card_eq h_equiv, has_card_to_card (Example_3_6_7a 0)]
      have h_fin : (Y ^ (∅ : Set)).finite :=
        ⟨1, ((EquivCard_to_has_card_eq h_equiv).mpr (Example_3_6_7a 0))⟩
      exact ⟨h_fin, by rw [h_card_one, pow_zero]⟩
    · -- k = k.succ
      have hpos : k.succ ≥ 1 := by omega
      have hne : S ≠ ∅ := pos_card_nonempty hpos hSk
      rcases Set.nonempty_def hne with ⟨x, hx⟩
      set S' := S \ {x} with hS'
      have hS'_sub : S' ⊆ X := by
        intro z hz; rw [hS', mem_sdiff] at hz; exact hS_sub _ hz.1
      have hS'_card : S'.has_card k := by
        have h := card_erase hpos hSk ⟨x, hx⟩
        have hsub : k.succ - 1 = k := by omega
        simpa [hS', hsub] using h
      have h_induction := ih S' hS'_sub hS'_card
      rcases h_induction with ⟨h_fin_pow_S', h_card_pow_S'⟩
      have h_disj : Disjoint S' ({x} : Set) := by
        rw [SetTheory.Set.disjoint_iff, eq_empty_iff_forall_notMem]
        intro z hz
        rw [mem_inter, hS', mem_sdiff, mem_singleton] at hz
        rcases hz with ⟨⟨_, hz_not⟩, hz_eq⟩
        exact hz_not hz_eq
      have h_singleton_subset : ({x} : Set) ⊆ S := by
        intro z hz; rw [mem_singleton] at hz; subst z; exact hx
      have h_union_eq : S' ∪ ({x} : Set) = S := by
        calc
          S' ∪ ({x} : Set) = (S \ {x}) ∪ {x} := by rw [hS']
          _ = ({x} : Set) ∪ (S \ {x}) := by rw [union_comm]
          _ = S := union_compl h_singleton_subset
      have h_pow_union : EqualCard ((Y ^ S') ×ˢ (Y ^ ({x} : Set))) (Y ^ S) := by
        rw [← h_union_eq]
        exact pow_prod_pow_EqualCard_pow_union Y S' ({x} : Set) h_disj
      rcases h_singleton x with ⟨h_fin_singleton, h_card_singleton⟩
      have h_card_prod := card_prod h_fin_pow_S' h_fin_singleton
      rcases h_card_prod with ⟨h_fin_prod, h_card_prod_eq⟩
      have h_card_pow_S : (Y ^ S).card = Y.card ^ k.succ := by
        rw [← (EquivCard_to_card_eq h_pow_union), h_card_prod_eq, h_card_pow_S', h_card_singleton]
        rw [pow_succ]
      have h_fin_pow_S : (Y ^ S).finite := by
        have h_card_val : ((Y ^ S') ×ˢ (Y ^ ({x} : Set))).card = Y.card ^ k.succ := by
          rw [h_card_prod_eq, h_card_pow_S', h_card_singleton]
          rw [pow_succ]
        have h_has_card_prod : ((Y ^ S') ×ˢ (Y ^ ({x} : Set))).has_card (Y.card ^ k.succ) := by
          rw [← h_card_val]
          exact has_card_card h_fin_prod
        exact ⟨Y.card ^ k.succ, ((EquivCard_to_has_card_eq h_pow_union).mp h_has_card_prod)⟩
      exact ⟨h_fin_pow_S, h_card_pow_S⟩
  exact h_main X.card X (by intro _ h; exact h) hXc

/-- Exercise 3.6.5. You might find {name}`SetTheory.Set.prod_commutator` useful. -/
theorem SetTheory.Set.prod_EqualCard_prod (A B:Set) :
    EqualCard (A ×ˢ B) (B ×ˢ A) := by sorry

noncomputable abbrev SetTheory.Set.pow_fun_equiv' (A B : Set) : ↑(A ^ B) ≃ (B → A) :=
  pow_fun_equiv (A:=A) (B:=B)

/-- Exercise 3.6.6. You may find {name}`SetTheory.Set.curry_equiv` useful. -/
theorem SetTheory.Set.pow_pow_EqualCard_pow_prod (A B C:Set) :
    EqualCard ((A ^ B) ^ C) (A ^ (B ×ˢ C)) := by sorry

theorem SetTheory.Set.pow_pow_eq_pow_mul (a b c:ℕ): (a^b)^c = a^(b*c) := by sorry


theorem SetTheory.Set.pow_mul_pow_eq_pow_add (a b c:ℕ): (a^b) * a^c = a^(b+c) := by sorry

/-- Exercise 3.6.7 -/
theorem SetTheory.Set.injection_iff_card_le {A B:Set} (hA: A.finite) (hB: B.finite) :
    (∃ f:A → B, Function.Injective f) ↔ A.card ≤ B.card := sorry

/-- Exercise 3.6.8 -/
theorem SetTheory.Set.surjection_from_injection {A B:Set} (hA: A ≠ ∅) (f: A → B)
  (hf: Function.Injective f) : ∃ g:B → A, Function.Surjective g := by sorry

/-- Exercise 3.6.9 -/
theorem SetTheory.Set.card_union_add_card_inter {A B:Set} (hA: A.finite) (hB: B.finite) :
    A.card + B.card = (A ∪ B).card + (A ∩ B).card := by  sorry

/-- Exercise 3.6.10 -/
theorem SetTheory.Set.pigeonhole_principle {n:ℕ} {A: Fin n → Set}
  (hA: ∀ i, (A i).finite) (hAcard: (iUnion _ A).card > n) : ∃ i, (A i).card ≥ 2 := by
  by_contra h_all
  push_neg at h_all
  -- h_all: ∀ i, (A i).card < 2, i.e., (A i).card ≤ 1
  have h_all_le_one : ∀ i, (A i).card ≤ 1 := by
    intro i; have hi := h_all i; omega
  -- Prove: for any m and family B, if each B i has card ≤ 1, then iUnion B has card ≤ m
  have h_union_bound : ∀ (m : ℕ) (B : Fin m → Set), (∀ i, (B i).finite) → (∀ i, (B i).card ≤ 1) →
      ((Fin m).iUnion B).finite ∧ ((Fin m).iUnion B).card ≤ m := by
    intro m B hB_fin hB_card
    induction' m with m ih
    · have h_empty : (Fin 0).iUnion B = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro x hx; rw [mem_iUnion] at hx; rcases hx with ⟨i, hi⟩
        have hlt := Fin.toNat_lt i; omega
      rw [h_empty]; simp
    · -- Define castSucc and last inline using Fin_embed and Fin_mk
      let castSucc (x : Fin m) : Fin m.succ :=
        Fin_embed m m.succ (Nat.le_succ _) x
      let last : Fin m.succ :=
        Fin_mk m.succ m (Nat.lt_succ_self _)
      let B' : Fin m → Set := fun i => B (castSucc i)
      have hB'_fin : ∀ i, (B' i).finite := fun i => hB_fin (castSucc i)
      have hB'_card : ∀ i, (B' i).card ≤ 1 := fun i => hB_card (castSucc i)
      rcases ih B' hB'_fin hB'_card with ⟨h_fin_iUnion, h_card_iUnion⟩
      have h_union_eq : (Fin m.succ).iUnion B = ((Fin m).iUnion B') ∪ B last := by
        apply SetTheory.Set.ext; intro x
        rw [mem_iUnion, mem_union, mem_iUnion]
        refine ⟨by
          rintro ⟨i, hi⟩
          by_cases hi_last : i = last
          · right; subst hi_last; exact hi
          · have hi_val_lt_m : (i : ℕ) < m := by
              have hi_lt := Fin.toNat_lt i
              have hlast_val : (last : ℕ) = m := by simp [last, Fin_mk]
              have hi_val_ne_m : (i : ℕ) ≠ m := by
                intro heq
                apply hi_last
                apply (Fin.coe_inj (n := m.succ)).mpr
                simpa [hlast_val] using heq
              omega
            let j : Fin m := Fin_mk m (i : ℕ) hi_val_lt_m
            have hembed_eq_i : castSucc j = i := by
              apply (Fin.coe_inj (n := m.succ)).mpr
              simp [castSucc, Fin_embed, j, Fin_mk]
            left; use j; simpa [B', hembed_eq_i] using hi
        , by
          intro h; rcases h with (⟨j, hj⟩ | hlast')
          · exact ⟨castSucc j, hj⟩
          · exact ⟨last, hlast'⟩
        ⟩
      rw [h_union_eq]
      have h_card_union := card_union h_fin_iUnion (hB_fin last)
      rcases h_card_union with ⟨h_fin_union, h_card_le⟩
      refine ⟨h_fin_union, ?_⟩
      have h_last : (B last).card ≤ 1 := hB_card last
      omega
  rcases h_union_bound n A hA h_all_le_one with ⟨_, h_le⟩
  omega

/-- Exercise 3.6.11 -/
theorem SetTheory.Set.two_to_two_iff {X Y:Set} (f: X → Y): Function.Injective f ↔
    ∀ S ⊆ X, S.card = 2 → (image f S).card = 2 := by
  constructor
  · intro hf S hS_sub hS_card
    have hS_fin : S.finite := by
      have hS_has_card : S.has_card 2 := card_to_has_card (by norm_num) hS_card
      exact ⟨2, hS_has_card⟩
    have h_equiv : S ≈ image f S := by
      let ι : S → X := fun x => ⟨x.val, hS_sub x.val x.property⟩
      let g : S → image f S := fun x => ⟨f (ι x), by
        rw [mem_image]; refine ⟨ι x, ?_, rfl⟩; simp [ι]; exact x.property⟩
      refine ⟨g, ?_, ?_⟩
      · intro a b h
        have h_val : (g a).val = (g b).val := congrArg Subtype.val h
        have h_f_val : (f (ι a) : Object) = (f (ι b) : Object) := by simpa [g, ι] using h_val
        have h_f : f (ι a) = f (ι b) := Subtype.val_inj.mp h_f_val
        have h_ι : ι a = ι b := hf h_f
        have h_val_a_b : a.val = b.val := by simpa [ι] using congrArg Subtype.val h_ι
        exact Subtype.val_inj.mp h_val_a_b
      · intro y
        rcases (mem_image f S y.val).mp y.property with ⟨x, hx, h⟩
        use ⟨x.val, hx⟩
        apply Subtype.val_inj.mp
        have hx_eq : (ι ⟨x.val, hx⟩ : X) = x := Subtype.ext rfl
        calc
          (g ⟨x.val, hx⟩).val = (f (ι ⟨x.val, hx⟩) : Object) := rfl
          _ = (f x : Object) := by rw [hx_eq]
          _ = y.val := h
    rw [(EquivCard_to_card_eq h_equiv).symm]; exact hS_card
  · intro h
    by_contra h_not_inj
    rw [Function.Injective] at h_not_inj
    push_neg at h_not_inj
    obtain ⟨a, b, hfeq_val, hneq_val⟩ := h_not_inj
    have ha_val_ne_b_val : a.val ≠ b.val := by
      intro h_eq; apply hneq_val; exact Subtype.val_inj.mp h_eq
    set S := ({a.val, b.val} : Set) with hS
    have hS_sub : S ⊆ X := by
      intro x hx
      rw [hS, mem_insert, mem_singleton] at hx
      rcases hx with (rfl | rfl)
      · exact a.property
      · exact b.property
    have hS_card : S.card = 2 := by
      have h_fin_b : ({b.val} : Set).finite := ⟨1, Example_3_6_7a b.val⟩
      have ha_notin_b : a.val ∉ ({b.val} : Set) := by
        rw [mem_singleton]; exact ha_val_ne_b_val
      have h_card := (card_insert h_fin_b ha_notin_b).2
      have h_singleton_card : ({b.val} : Set).card = 1 :=
        has_card_to_card (Example_3_6_7a b.val)
      have h_eq_set : ({b.val} : Set) ∪ {a.val} = S := by
        rw [hS]; ext x; simp [or_comm]
      rw [h_eq_set, h_singleton_card] at h_card
      omega
    have h_image_S_card : (image f S).card = 1 := by
      have h_img_singleton : image f S = {(f a : Object)} := by
        ext y; constructor
        · rw [mem_image, mem_singleton]; rintro ⟨x, hx, h⟩
          have hx_cases : x.val = a.val ∨ x.val = b.val := by
            rw [hS, mem_insert, mem_singleton] at hx; exact hx
          rcases hx_cases with (hx_val_a | hx_val_b)
          · have hx_eq_a : x = a := Subtype.val_inj.mp hx_val_a
            rw [hx_eq_a] at h
            exact h.symm
          · have hx_eq_b : x = b := Subtype.val_inj.mp hx_val_b
            rw [hx_eq_b] at h
            rw [← hfeq_val] at h
            exact h.symm
        · rw [mem_singleton, mem_image]; intro hy; subst hy
          refine ⟨a, ?_, rfl⟩
          rw [hS, mem_insert, mem_singleton]; simp
      rw [h_img_singleton]; exact has_card_to_card (Example_3_6_7a (f a))
    have h_contra : (image f S).card = 2 := h S hS_sub hS_card
    omega

/-- Exercise 3.6.12 -/
def SetTheory.Set.Permutations (n: ℕ): Set := (Fin n ^ Fin n).specify (fun F ↦
    Function.Bijective (pow_fun_equiv F))

/-- Exercise 3.6.12 (i), first part -/
theorem SetTheory.Set.Permutations_finite (n: ℕ): (Permutations n).finite := by sorry

/- To continue Exercise 3.6.12 (i), we'll first develop some theory about `Permutations` and `Fin`. -/

noncomputable def SetTheory.Set.Permutations_toFun {n: ℕ} (p: Permutations n) : (Fin n) → (Fin n) := by
  have := p.property
  simp only [Permutations, specification_axiom'', powerset_axiom] at this
  exact this.choose.choose

theorem SetTheory.Set.Permutations_bijective {n: ℕ} (p: Permutations n) :
    Function.Bijective (Permutations_toFun p) := by sorry

theorem SetTheory.Set.Permutations_inj {n: ℕ} (p1 p2: Permutations n) :
    Permutations_toFun p1 = Permutations_toFun p2 ↔ p1 = p2 := by sorry

/-- This connects our concept of a permutation with Mathlib's {name}`Equiv` between {lean}`Fin n` and {lean}`Fin n`. -/
noncomputable def SetTheory.Set.perm_equiv_equiv {n : ℕ} : Permutations n ≃ (Fin n ≃ Fin n) := {
  toFun := fun p => Equiv.ofBijective (Permutations_toFun p) (Permutations_bijective p)
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
}

/- Exercise 3.6.12 involves a lot of moving between `Fin n` and `Fin (n + 1)` so let's add some conveniences. -/

/-- Any {lean}`Fin n` can be cast to {lean}`Fin (n + 1)`. Compare to Mathlib {name}`Fin.castSucc`. -/
def SetTheory.Set.Fin.castSucc {n} (x : Fin n) : Fin (n + 1) :=
  Fin_embed _ _ (by omega) x

@[simp]
lemma SetTheory.Set.Fin.castSucc_inj {n} {x y : Fin n} : castSucc x = castSucc y ↔ x = y := by sorry

@[simp]
theorem SetTheory.Set.Fin.castSucc_ne {n} (x : Fin n) : castSucc x ≠ n := by sorry

/-- Any {lean}`Fin (n + 1)` except {lean}`n` can be cast to {lean}`Fin n`. Compare to Mathlib {name}`Fin.castPred`. -/
noncomputable def SetTheory.Set.Fin.castPred {n} (x : Fin (n + 1)) (h : (x : ℕ) ≠ n) : Fin n :=
  Fin_mk _ (x : ℕ) (by have := Fin.toNat_lt x; omega)

@[simp]
theorem SetTheory.Set.Fin.castSucc_castPred {n} (x : Fin (n + 1)) (h : (x : ℕ) ≠ n) :
    castSucc (castPred x h) = x := by sorry

@[simp]
theorem SetTheory.Set.Fin.castPred_castSucc {n} (x : Fin n) (h : ((castSucc x : Fin (n + 1)) : ℕ) ≠ n) :
    castPred (castSucc x) h = x := by sorry

/-- Any natural {lean}`n` can be cast to {lean}`Fin (n + 1)`. Compare to Mathlib {name}`Fin.last`. -/
def SetTheory.Set.Fin.last (n : ℕ) : Fin (n + 1) := Fin_mk _ n (by omega)

/-- Now is a good time to prove this result, which will be useful for completing Exercise 3.6.12 (i). -/
theorem SetTheory.Set.card_iUnion_card_disjoint {n m: ℕ} {S : Fin n → Set}
    (hSc : ∀ i, (S i).has_card m)
    (hSd : Pairwise fun i j => Disjoint (S i) (S j)) :
    ((Fin n).iUnion S).finite ∧ ((Fin n).iUnion S).card = n * m := by sorry

/- Finally, we'll set up a way to shrink `Fin (n + 1)` into `Fin n` (or expand the latter) by making a hole. -/

/--
  If some {lean}`x : Fin (n+1)` is never equal to {name}`i`, we can shrink it into {lean}`Fin n` by shifting all {lean}`(x : ℕ) > i` down by one.
  Compare to Mathlib {name}`Fin.predAbove`.
-/
noncomputable def SetTheory.Set.Fin.predAbove {n} (i : Fin (n + 1)) (x : Fin (n + 1)) (h : x ≠ i) : Fin n :=
  if hx : (x:ℕ) < i then
    Fin_mk _ (x:ℕ) (by sorry)
  else
    Fin_mk _ ((x:ℕ) - 1) (by sorry)

/--
  We can expand {lean}`x : Fin n` into {lean}`Fin (n + 1)` by shifting all {lean}`(x : ℕ) ≥ i` up by one.
  The output is never {name}`i`, so it forms an inverse to the shrinking done by {name}`predAbove`.
  Compare to Mathlib {name}`Fin.succAbove`.
-/
noncomputable def SetTheory.Set.Fin.succAbove {n} (i : Fin (n + 1)) (x : Fin n) : Fin (n + 1) :=
  if (x:ℕ) < i then
    Fin_embed _ _ (by sorry) x
  else
    Fin_mk _ ((x:ℕ) + 1) (by sorry)

@[simp]
theorem SetTheory.Set.Fin.succAbove_ne {n} (i : Fin (n + 1)) (x : Fin n) : succAbove i x ≠ i := by sorry

@[simp]
theorem SetTheory.Set.Fin.succAbove_predAbove {n} (i : Fin (n + 1)) (x : Fin (n + 1)) (h : x ≠ i) :
    (succAbove i) (predAbove i x h) = x := by sorry

@[simp]
theorem SetTheory.Set.Fin.predAbove_succAbove {n} (i : Fin (n + 1)) (x : Fin n) :
    (predAbove i) (succAbove i x) (succAbove_ne i x) = x := by sorry

/-- Exercise 3.6.12 (i), second part -/
theorem SetTheory.Set.Permutations_ih (n: ℕ):
    (Permutations (n + 1)).card = (n + 1) * (Permutations n).card := by
  let S i := (Permutations (n + 1)).specify (fun p ↦ perm_equiv_equiv p (Fin.last n) = i)

  have hSe : ∀ i, S i ≈ Permutations n := by
    classical
    intro i
    -- Hint: you might find `perm_equiv_equiv`, `Fin.succAbove`, and `Fin.predAbove` useful.
    have equiv : S i ≃ Permutations n := by
      -- Restrict: from Equiv on Fin(n+1) with e(last)=i, get Equiv on Fin n
      let restrict (e : Fin (n+1) ≃ Fin (n+1)) (h : e (Fin.last n) = i) : Fin n ≃ Fin n := {
        toFun := λ x =>
          Fin.predAbove i (e (Fin.succAbove (Fin.last n) x)) (by
            intro h_eq
            apply Fin.succAbove_ne (Fin.last n) x
            calc
              Fin.succAbove (Fin.last n) x = e.symm (e (Fin.succAbove (Fin.last n) x)) := by simp
              _ = e.symm i := by rw [h_eq]
              _ = Fin.last n := (e.symm_apply_eq).mpr h.symm)
        invFun := λ y =>
          Fin.predAbove (Fin.last n) (e.symm (Fin.succAbove i y)) (by
            intro h_eq
            apply Fin.succAbove_ne i y
            calc
              Fin.succAbove i y = e (e.symm (Fin.succAbove i y)) := by simp
              _ = e (Fin.last n) := by rw [h_eq]
              _ = i := h)
        left_inv := by intro x; simp
        right_inv := by intro y; simp
      }
      -- Extend: add mapping last→i to an Equiv on Fin n, get Equiv on Fin(n+1)
      let extend (e' : Fin n ≃ Fin n) : Fin (n+1) ≃ Fin (n+1) := {
        toFun := λ y =>
          if h_eq : y = Fin.last n then i
          else Fin.succAbove i (e' (Fin.predAbove (Fin.last n) y h_eq))
        invFun := λ z =>
          if h_eq : z = i then Fin.last n
          else Fin.succAbove (Fin.last n) (e'.symm (Fin.predAbove i z h_eq))
        left_inv := by
          intro y
          by_cases hy : y = Fin.last n
          · subst y; simp
          · have h_ne : Fin.succAbove i (e' (Fin.predAbove (Fin.last n) y hy)) ≠ i :=
              Fin.succAbove_ne i _
            simp [hy, h_ne]
        right_inv := by
          intro z
          by_cases hz : z = i
          · subst z; simp
          · have h_ne : Fin.succAbove (Fin.last n) (e'.symm (Fin.predAbove i z hz)) ≠ Fin.last n :=
              Fin.succAbove_ne (Fin.last n) _
            simp [hz, h_ne]
      }
      have h_extend_last (e' : Fin n ≃ Fin n) : (extend e') (Fin.last n) = i := by
        dsimp [extend]; simp
      -- The equivalence S i ≃ Permutations n
      let toFun_aux (ps : (S i).toSubtype) : (Permutations n).toSubtype :=
        let hps := (specification_axiom'' (x := ps.val) (A := Permutations (n+1))
          (P := fun p ↦ perm_equiv_equiv p (Fin.last n) = i)).mp ps.property
        let hp_mem := hps.1
        let hp_cond := hps.2
        let e := perm_equiv_equiv ⟨ps.val, hp_mem⟩
        (perm_equiv_equiv (n := n)).symm (restrict e hp_cond)
      let invFun_aux (q : (Permutations n).toSubtype) : (S i).toSubtype :=
        let e' := perm_equiv_equiv q
        let p_perm := (perm_equiv_equiv (n := n+1)).symm (extend e')
        have hp_mem : p_perm.val ∈ Permutations (n+1) := p_perm.property
        have hp_spec : perm_equiv_equiv ⟨p_perm.val, hp_mem⟩ (Fin.last n) = i := by
          calc
            perm_equiv_equiv ⟨p_perm.val, hp_mem⟩ (Fin.last n) =
                perm_equiv_equiv p_perm (Fin.last n) := by simp
            _ = (extend e') (Fin.last n) := by simp [p_perm]
            _ = i := h_extend_last e'
        have h_mem_S : p_perm.val ∈ S i := by
          dsimp [S]
          apply (specification_axiom'' (x := p_perm.val) (A := Permutations (n+1))
            (P := fun p ↦ perm_equiv_equiv p (Fin.last n) = i)).mpr
          exact ⟨hp_mem, hp_spec⟩
        ⟨p_perm.val, h_mem_S⟩
      exact Equiv.mk toFun_aux invFun_aux (by
          intro ps
          let hps := (specification_axiom'' (x := ps.val) (A := Permutations (n+1))
            (P := fun p ↦ perm_equiv_equiv p (Fin.last n) = i)).mp ps.property
          let hp_mem := hps.1
          let hp_cond := hps.2
          let e := perm_equiv_equiv ⟨ps.val, hp_mem⟩
          have h_extend_eq : (extend (restrict e hp_cond)) = e := by
            ext y
            dsimp [extend, restrict]
            by_cases hy : y = Fin.last n
            · subst y; simp [hp_cond]
            · simp [hy]
          calc
            invFun_aux (toFun_aux ps) = perm_equiv_equiv.invFun (restrict e hp_cond) := by
              simp [toFun_aux, invFun_aux, hp_cond]
            _ = (perm_equiv_equiv n).symm (restrict e hp_cond) := rfl
            _ = (perm_equiv_equiv n).symm ((perm_equiv_equiv n) ((perm_equiv_equiv n).symm (restrict e hp_cond))) := by simp
            _ = toFun_aux ps := rfl
            _ = _ := ?_ -- need ps here, but toFun_aux ps = (perm_equiv_equiv n).symm (restrict e hp_cond)
            )

    use equiv, equiv.injective, equiv.surjective

  -- Hint: you might find `card_iUnion_card_disjoint` and `Permutations_finite` useful.
  sorry

/-- Exercise 3.6.12 (ii) -/
theorem SetTheory.Set.Permutations_card (n: ℕ):
    (Permutations n).card = n.factorial := by sorry

/-- Connections with Mathlib's {name}`Finite` -/
theorem SetTheory.Set.finite_iff_finite {X:Set} : X.finite ↔ Finite X := by
  rw [finite_iff_exists_equiv_fin, finite]
  constructor
  · rintro ⟨n, hn⟩
    use n
    obtain ⟨f, hf⟩ := hn
    have eq := (Equiv.ofBijective f hf).trans (Fin.Fin_equiv_Fin n)
    exact ⟨eq⟩
  rintro ⟨n, hn⟩
  use n
  have eq := hn.some.trans (Fin.Fin_equiv_Fin n).symm
  exact ⟨eq, eq.bijective⟩

/-- Connections with Mathlib's {name}`Set.Finite` -/
theorem SetTheory.Set.finite_iff_set_finite {X:Set} :
    X.finite ↔ (X :_root_.Set Object).Finite := by
  rw [finite_iff_finite]
  rfl

/-- Connections with Mathlib's {name}`Nat.card` -/
theorem SetTheory.Set.card_eq_nat_card {X:Set} : X.card = Nat.card X := by
  by_cases hf : X.finite
  · by_cases hz : X.card = 0
    · rw [hz]; symm
      have : X = ∅ := empty_of_card_eq_zero hf hz
      rw [this, Nat.card_eq_zero, isEmpty_iff]
      aesop
    symm
    have hc := has_card_card hf
    obtain ⟨f, hf⟩ := hc
    apply Nat.card_eq_of_equiv_fin
    exact (Equiv.ofBijective f hf).trans (Fin.Fin_equiv_Fin X.card)
  simp only [card, hf, ↓reduceDIte]; symm
  rw [Nat.card_eq_zero, ←not_finite_iff_infinite]
  right
  rwa [finite_iff_set_finite] at hf

/-- Connections with Mathlib's {name}`Set.ncard` -/
theorem SetTheory.Set.card_eq_ncard {X:Set} : X.card = (X: _root_.Set Object).ncard := by
  rw [card_eq_nat_card]
  rfl

end Chapter3
