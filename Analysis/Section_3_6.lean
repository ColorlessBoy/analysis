import Mathlib.Tactic
import Analysis.Section_3_3
import Analysis.Section_3_5

set_option linter.unnecessarySimpa false

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
theorem SetTheory.Set.Example_3_6_3 : EqualCard nat (nat.specify (fun x ↦ Even (x:ℕ))) := by
  unfold EqualCard
  set P : nat → Prop := fun x ↦ Even (x:ℕ) with hP
  set f : nat → nat.specify P := fun n ↦
    let k : ℕ := (n:ℕ)
    let d : ℕ := 2*k
    ⟨ (d : Object), (specification_axiom' P (d : nat)).mpr (by
      dsimp [P]
      have : Even d := by
        use k
        omega
      simpa) ⟩
  refine ⟨f, ?_⟩
  constructor
  · intro a b h
    have hval : (f a).val = (f b).val := congrArg Subtype.val h
    have ha_eq_b : a = b := by
      simpa [f] using hval
    exact ha_eq_b
  · intro y
    have h_spec := (specification_axiom'' P y.val).mp y.property
    have h_nat : y.val ∈ nat := h_spec.choose
    have h_even : P ⟨y.val, h_nat⟩ := h_spec.choose_spec
    have h_even' : Even (((⟨y.val, h_nat⟩ : nat) : ℕ)) := by
      simpa [P] using h_even
    let r : ℕ := h_even'.choose
    have hr : ((⟨y.val, h_nat⟩ : nat) : ℕ) = r + r := h_even'.choose_spec
    let m : nat := ⟨y.val, h_nat⟩
    have hm_ℕ_eq_2r : (m:ℕ) = 2*r := by
      calc
        (m:ℕ) = r + r := hr
        _ = 2*r := by omega
    use (r : nat)
    apply Subtype.ext
    have h_f_val : (f (r : nat)).val = y.val := by
      calc
        (f (r : nat)).val = ((2*(r:ℕ) : ℕ) : Object) := by
          simp [f]
        _ = ((2*r : ℕ) : Object) := rfl
        _ = ((m:ℕ) : Object) := by
          simp [hm_ℕ_eq_2r]
        _ = m.val := by
          simp
        _ = y.val := rfl
    exact h_f_val

@[refl]
theorem SetTheory.Set.EqualCard.refl (X:Set) : EqualCard X X := by
  exact ⟨id, Function.bijective_id⟩

@[symm]
theorem SetTheory.Set.EqualCard.symm {X Y:Set} (h: EqualCard X Y) : EqualCard Y X := by
  rcases h with ⟨f, hf⟩
  refine ⟨(Equiv.ofBijective f hf).symm, ?_⟩
  exact (Equiv.ofBijective f hf).symm.bijective

@[trans]
theorem SetTheory.Set.EqualCard.trans {X Y Z:Set} (h1: EqualCard X Y) (h2: EqualCard Y Z) : EqualCard X Z := by
  rcases h1 with ⟨f, hf⟩
  rcases h2 with ⟨g, hg⟩
  refine ⟨(Equiv.ofBijective f hf).trans (Equiv.ofBijective g hg), ?_⟩
  exact ((Equiv.ofBijective f hf).trans (Equiv.ofBijective g hg)).bijective

/-- Proposition 3.6.4 / Exercise 3.6.1 -/
instance SetTheory.Set.EqualCard.inst_setoid : Setoid SetTheory.Set := ⟨ EqualCard, {refl, symm, trans} ⟩

/-- Definition 3.6.5 -/
abbrev SetTheory.Set.has_card (X:Set) (n:ℕ) : Prop := X ≈ Fin n

theorem SetTheory.Set.has_card_iff (X:Set) (n:ℕ) :
    X.has_card n ↔ ∃ f: X → Fin n, Function.Bijective f := by
  simp [has_card, HasEquiv.Equiv, instHasEquivOfSetoid, Setoid.r, EqualCard]

/-- Remark 3.6.6 -/
theorem SetTheory.Set.Remark_3_6_6 (n:ℕ) :
    (nat.specify (fun x ↦ 1 ≤ (x:ℕ) ∧ (x:ℕ) ≤ n)).has_card n := by
  rw [has_card_iff]
  set P : nat → Prop := fun x ↦ 1 ≤ (x:ℕ) ∧ (x:ℕ) ≤ n with hP
  let f : (nat.specify P) → Fin n := fun x ↦
    let hx_mem : x.val ∈ nat := specification_axiom x.property
    let hxP : P ⟨x.val, hx_mem⟩ := (specification_axiom' P ⟨x.val, hx_mem⟩).mp x.property
    let v : ℕ := ((⟨x.val, hx_mem⟩ : nat) : ℕ)
    have hv1 : 1 ≤ v := hxP.1
    have hv2 : v ≤ n := hxP.2
    Fin_mk n (v - 1) (by omega)
  refine ⟨f, ?_⟩
  constructor
  · intro x y h
    apply Subtype.ext
    let hx_mem : x.val ∈ nat := specification_axiom x.property
    let hy_mem : y.val ∈ nat := specification_axiom y.property
    let vx : ℕ := ((⟨x.val, hx_mem⟩ : nat) : ℕ)
    let vy : ℕ := ((⟨y.val, hy_mem⟩ : nat) : ℕ)
    have hvx : 1 ≤ vx := by
      have hxP := (specification_axiom' P ⟨x.val, hx_mem⟩).mp x.property
      dsimp [vx]; exact hxP.1
    have hvy : 1 ≤ vy := by
      have hyP := (specification_axiom' P ⟨y.val, hy_mem⟩).mp y.property
      dsimp [vy]; exact hyP.1
    have h_val_ℕ : vx = vy := by
      have h_f_val : (f x : ℕ) = (f y : ℕ) := by
        simp [h]
      dsimp [f, vx, vy] at h_f_val
      simp [Fin.toNat_mk] at h_f_val
      omega
    have h_nat_eq : (⟨x.val, hx_mem⟩ : nat) = (⟨y.val, hy_mem⟩ : nat) :=
      (nat_equiv_symm_inj _ _).mp h_val_ℕ
    simpa using h_nat_eq
  · intro i
    let k : ℕ := (i:ℕ) + 1
    have hk1 : 1 ≤ k := by omega
    have hkn : k ≤ n := by
      have hi_lt_n : (i:ℕ) < n := Fin.toNat_lt i
      omega
    have h_mem : (k : Object) ∈ nat.specify P :=
      (specification_axiom' P (k : nat)).mpr (by
        simp [P, hk1, hkn])
    use ⟨(k : Object), h_mem⟩
    apply Subtype.ext
    have h_temp : (f ⟨(k : Object), h_mem⟩ : ℕ) = k - 1 := by
      dsimp [f]; simp
    have h_val_ℕ : (f ⟨(k : Object), h_mem⟩ : ℕ) = (i : ℕ) := by
      calc
        (f ⟨(k : Object), h_mem⟩ : ℕ) = k - 1 := h_temp
        _ = ((i : ℕ) + 1) - 1 := rfl
        _ = (i : ℕ) := by omega
    calc
      (f ⟨(k : Object), h_mem⟩).val = ((f ⟨(k : Object), h_mem⟩ : ℕ) : Object) := by
        dsimp [f]; simp
      _ = ((i : ℕ) : Object) := by simp [h_val_ℕ]
      _ = i.val := by simp

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
  have hy : Fin n := Fin_mk n 0 (by omega)
  have hx := hf.2 hy
  rcases hx with ⟨x, _⟩
  have mem : x.val ∈ (∅ : Set) := by
    simpa [this] using x.property
  exact SetTheory.Set.not_mem_empty _ mem
  -- obtain a contradiction from the fact that `f` is a bijection from the empty set to a
  -- non-empty set.

/-- Exercise 3.6.2a -/
theorem SetTheory.Set.has_card_zero {X:Set} : X.has_card 0 ↔ X = ∅ := by
  constructor
  · intro h
    rw [has_card_iff] at h
    rcases h with ⟨f, hf⟩
    by_contra hne
    have ⟨x, hx⟩ := nonempty_def hne
    have mem : (f ⟨x, hx⟩).val ∈ Fin 0 := (f ⟨x, hx⟩).property
    rw [mem_Fin] at mem
    rcases mem with ⟨m, hm, _⟩
    exact Nat.not_lt_zero m hm
  · intro h
    subst h
    rw [has_card_iff]
    refine ⟨fun x => False.elim (Set.not_mem_empty x.val x.property), ?_⟩
    constructor
    · intro a b h
      exact False.elim (Set.not_mem_empty a.val a.property)
    · intro y
      have mem : y.val ∈ Fin 0 := y.property
      rw [mem_Fin] at mem
      rcases mem with ⟨m, hm, _⟩
      exact False.elim (Nat.not_lt_zero m hm)

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
  have hm₀f' : (f x : ℕ) = m₀ := by
    apply (Object.natCast_inj ((f x : ℕ)) m₀).mp
    calc
      ((f x : ℕ) : Object) = (f x : Object) := Fin.coe_toNat (f x)
      _ = (m₀ : Object) := hm₀f
  have hg : Function.Bijective g := by
    have h_ne_m₀ (z : X') : (f (ι z) : ℕ) ≠ m₀ := by
      by_contra! h_eq
      have h_eq_fx : (f x : ℕ) = (f (ι z) : ℕ) := by
        calc
          (f x : ℕ) = m₀ := hm₀f'
          _ = (f (ι z) : ℕ) := by symm; exact h_eq
      have hx_eq_ιz : x = ι z := hf.1 (Fin.coe_inj.2 h_eq_fx)
      have h_val_eq : (x : Object) = (z : Object) := by
        calc
          (x : Object) = (ι z : Object) := by rw [hx_eq_ιz]
          _ = (z : Object) := hι z
      have h_val_eq_val : x.val = z.val := by simpa using h_val_eq
      have hz_not_x : z.val ≠ x.val := by
        intro hx_val_eq
        have hz_prop := z.property
        dsimp [X'] at hz_prop
        simp [hx_val_eq] at hz_prop
      exact hz_not_x h_val_eq_val.symm
    have hg_inj : Function.Injective g := by
      intro a b h
      have hg_coe : (g a : ℕ) = (g b : ℕ) := by
        simpa using congrArg (fun z : Fin (n-1) => (z : ℕ)) h
      have ha_val := hg_def a
      have hb_val := hg_def b
      by_cases ha_lt : (f (ι a) : ℕ) < m₀
      · by_cases hb_lt : (f (ι b) : ℕ) < m₀
        · rw [if_pos ha_lt] at ha_val; rw [if_pos hb_lt] at hb_val
          rw [ha_val, hb_val] at hg_coe
          have h_fa_eq_fb : f (ι a) = f (ι b) := Fin.coe_inj.2 hg_coe
          have h_ia_eq_ib : ι a = ι b := hf.1 h_fa_eq_fb
          have h_val_eq_val : a.val = b.val := by
            calc
              a.val = (ι a : Object) := by simpa using (hι a).symm
              _ = (ι b : Object) := by rw [h_ia_eq_ib]
              _ = b.val := by simpa using hι b
          exact Subtype.val_inj.mp h_val_eq_val
        · rw [if_pos ha_lt] at ha_val; rw [if_neg hb_lt] at hb_val
          rw [ha_val, hb_val] at hg_coe
          have hfa_lt_m₀ : (f (ι a) : ℕ) < m₀ := ha_lt
          have hfb_ne_m₀ : (f (ι b) : ℕ) ≠ m₀ := h_ne_m₀ b
          have hfb_ge_m₀ : (f (ι b) : ℕ) ≥ m₀ := by omega
          have hfb_eq_m₀ : (f (ι b) : ℕ) = m₀ := by
            omega
          exact absurd hfb_eq_m₀ hfb_ne_m₀
      · by_cases hb_lt : (f (ι b) : ℕ) < m₀
        · rw [if_neg ha_lt] at ha_val; rw [if_pos hb_lt] at hb_val
          rw [ha_val, hb_val] at hg_coe
          have hfb_lt_m₀ : (f (ι b) : ℕ) < m₀ := hb_lt
          have hfa_ne_m₀ : (f (ι a) : ℕ) ≠ m₀ := h_ne_m₀ a
          have hfa_ge_m₀ : (f (ι a) : ℕ) ≥ m₀ := by omega
          have hfa_eq_m₀ : (f (ι a) : ℕ) = m₀ := by
            omega
          exact absurd hfa_eq_m₀ hfa_ne_m₀
        · rw [if_neg ha_lt] at ha_val; rw [if_neg hb_lt] at hb_val
          rw [ha_val, hb_val] at hg_coe
          have hfa_gt_m₀ : (f (ι a) : ℕ) > m₀ := by
            have hfa_ne_m₀ : (f (ι a) : ℕ) ≠ m₀ := h_ne_m₀ a
            omega
          have hfb_gt_m₀ : (f (ι b) : ℕ) > m₀ := by
            have hfb_ne_m₀ : (f (ι b) : ℕ) ≠ m₀ := h_ne_m₀ b
            omega
          have h_fa_eq_fb_coe : (f (ι a) : ℕ) = (f (ι b) : ℕ) := by
            omega
          have h_fa_eq_fb : f (ι a) = f (ι b) := Fin.coe_inj.2 h_fa_eq_fb_coe
          have h_ia_eq_ib : ι a = ι b := hf.1 h_fa_eq_fb
          have h_val_eq_val : a.val = b.val := by
            calc
              a.val = (ι a : Object) := by simpa using (hι a).symm
              _ = (ι b : Object) := by rw [h_ia_eq_ib]
              _ = b.val := by simpa using hι b
          exact Subtype.val_inj.mp h_val_eq_val
    have hg_surj : Function.Surjective g := by
      intro y
      have hy_lt_n1 : (y : ℕ) < n - 1 := Fin.toNat_lt y
      by_cases hy_lt_m₀ : (y : ℕ) < m₀
      · have hy_lt_n : (y : ℕ) < n := by omega
        let y_emb : Fin n := Fin_mk n (y : ℕ) hy_lt_n
        rcases hf.2 y_emb with ⟨z, hz⟩
        have hz_val_ne_x_val : z.val ≠ x.val := by
          intro h_eq
          have hy_eq_m₀ : (y : ℕ) = m₀ := by
            calc
              (y : ℕ) = (y_emb : ℕ) := by simp
              _ = (f z : ℕ) := by rw [hz]
              _ = (f x : ℕ) := by rw [Subtype.val_inj.mp h_eq]
              _ = m₀ := hm₀f'
          omega
        have hz_in_X' : z.val ∈ X' := by
          dsimp [X']
          simp [z.property, hz_val_ne_x_val]
        let z' : X' := ⟨z.val, hz_in_X'⟩
        use z'
        have h_iz_eq_z : ι z' = z := by
          apply Subtype.ext
          calc
            (ι z' : Object) = (z' : Object) := hι z'
            _ = (z : Object) := rfl
        have h_f_iz_lt_m₀ : (f (ι z') : ℕ) < m₀ := by
          calc
            (f (ι z') : ℕ) = (f z : ℕ) := by rw [h_iz_eq_z]
            _ = (y_emb : ℕ) := by rw [hz]
            _ = (y : ℕ) := by simp
            _ < m₀ := hy_lt_m₀
        have hg_val_z' : (g z' : ℕ) = (f (ι z') : ℕ) := by
          have h := hg_def z'
          rw [if_pos h_f_iz_lt_m₀] at h
          exact h
        apply Fin.coe_inj.2
        calc
          (g z' : ℕ) = (f (ι z') : ℕ) := hg_val_z'
          _ = (f z : ℕ) := by rw [h_iz_eq_z]
          _ = (y_emb : ℕ) := by rw [hz]
          _ = (y : ℕ) := by simp
      · have h_yp1_lt_n : (y : ℕ) + 1 < n := by omega
        let y_succ_emb : Fin n := Fin_mk n ((y : ℕ) + 1) h_yp1_lt_n
        rcases hf.2 y_succ_emb with ⟨z, hz⟩
        have hz_val_ne_x_val : z.val ≠ x.val := by
          intro h_eq
          have h_yp1_eq_m₀ : (y : ℕ) + 1 = m₀ := by
            calc
              (y : ℕ) + 1 = (y_succ_emb : ℕ) := by simp
              _ = (f z : ℕ) := by rw [hz]
              _ = (f x : ℕ) := by rw [Subtype.val_inj.mp h_eq]
              _ = m₀ := hm₀f'
          omega
        have hz_in_X' : z.val ∈ X' := by
          dsimp [X']
          simp [z.property, hz_val_ne_x_val]
        let z' : X' := ⟨z.val, hz_in_X'⟩
        use z'
        have h_iz_eq_z : ι z' = z := by
          apply Subtype.ext
          calc
            (ι z' : Object) = (z' : Object) := hι z'
            _ = (z : Object) := rfl
        have h_f_iz_ge_m₀ : (f (ι z') : ℕ) ≥ m₀ := by
          calc
            (f (ι z') : ℕ) = (f z : ℕ) := by rw [h_iz_eq_z]
            _ = (y_succ_emb : ℕ) := by rw [hz]
            _ = (y : ℕ) + 1 := by simp
            _ ≥ m₀ := by omega
        have h_f_iz_not_lt_m₀ : ¬ (f (ι z') : ℕ) < m₀ := by omega
        have hg_val_z' : (g z' : ℕ) = (f (ι z') : ℕ) - 1 := by
          have h := hg_def z'
          rw [if_neg h_f_iz_not_lt_m₀] at h
          exact h
        apply Fin.coe_inj.2
        calc
          (g z' : ℕ) = (f (ι z') : ℕ) - 1 := hg_val_z'
          _ = ((f z : ℕ) - 1) := by rw [h_iz_eq_z]
          _ = ((y_succ_emb : ℕ) - 1) := by rw [hz]
          _ = ((y : ℕ) + 1 - 1) := by simp
          _ = (y : ℕ) := by omega
    exact ⟨hg_inj, hg_surj⟩
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
theorem SetTheory.Set.bounded_on_finite {n:ℕ} (f: Fin n → nat) : ∃ M, ∀ i, (f i:ℕ) ≤ M := by
  induction n with
  | zero =>
    use 0
    intro i
    have h_lt : (i : ℕ) < 0 := by
      have hi_mem : i.val ∈ Fin 0 := i.property
      rcases (mem_Fin 0 i.val).mp hi_mem with ⟨m, hm, hm_eq⟩
      omega
    omega
  | succ k ih =>
    let last : Fin (k+1) := Fin_mk (k+1) k (by omega)
    let g : Fin k → nat := fun i => f (Fin_embed k (k+1) (by omega) i)
    rcases ih g with ⟨M, hM⟩
    use max M ((f last : ℕ))
    intro i
    have hi_lt : (i : ℕ) < k+1 := Fin.toNat_lt i
    by_cases h_eq : (i : ℕ) = k
    · have h_last_val : (last : ℕ) = k := by
        apply (Object.natCast_inj ((last : ℕ)) k).mp
        calc
          ((last : ℕ) : Object) = (last : Object) := by exact Fin.coe_toNat last
          _ = (k : Object) := rfl
      have h_val_eq : (i : ℕ) = (last : ℕ) := by
        rw [h_last_val, h_eq]
      have h_i_eq_last : i = last := (Fin.coe_inj (i := i) (j := last)).mpr h_val_eq
      rw [h_i_eq_last]
      exact le_max_right _ _
    · have h_lt_k : (i : ℕ) < k := by omega
      let j : Fin k := Fin_mk k (i : ℕ) h_lt_k
      have h_embed : Fin_embed k (k+1) (by omega) j = i := by
        apply Subtype.ext
        calc
          (Fin_embed k (k+1) (by omega) j).val = j.val := rfl
          _ = ((i : ℕ) : Object) := by
            dsimp [j, Fin_mk]
          _ = (i : Object) := by rw [Fin.coe_toNat i]
          _ = i.val := rfl
      calc
        (f i : ℕ) = (f (Fin_embed k (k+1) (by omega) j) : ℕ) := by rw [h_embed]
        _ = (g j : ℕ) := rfl
        _ ≤ M := hM j
        _ ≤ max M ((f last : ℕ)) := le_max_left _ _

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
  constructor
  · intro h
    subst h
    have hempty0 : (∅ : Set).has_card 0 := ((has_card_zero (X:=∅)).mpr rfl)
    have hemptyFin : (∅ : Set).finite := ⟨0, hempty0⟩
    have hemptyCard : (∅ : Set).card = 0 := has_card_to_card hempty0
    exact ⟨hemptyFin, hemptyCard⟩
  · intro ⟨hX, hcard⟩
    have hXcard : X.has_card (X.card) := has_card_card hX
    rw [hcard] at hXcard
    exact ((has_card_zero (X:=X)).mp hXcard)

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
    (X ∪ {x}).finite ∧ (X ∪ {x}).card = X.card + 1 := by
  classical
    set n := X.card with hn
    have hcardX : X.has_card n := has_card_card hX
    rw [has_card_iff] at hcardX
    rcases hcardX with ⟨f, hf⟩
    have hn_lt_succ : n < n + 1 := by omega
    have hx_mem_union : x ∈ X ∪ {x} := by
      rw [SetTheory.Set.mem_union]; right; simp
    set S : Set := X ∪ {x} with hS
    let g : S → Fin (n+1) := fun z =>
      if hz : z.val ∈ X then
        Fin_embed n (n+1) (by omega) (f ⟨z.val, hz⟩)
      else
        Fin_mk (n+1) n hn_lt_succ
    have hg_injective : Function.Injective g := by
      intro a b h
      by_cases haX : a.val ∈ X
      · by_cases hbX : b.val ∈ X
        · have hg_a : g a = Fin_embed n (n+1) (by omega) (f ⟨a.val, haX⟩) := by
            unfold g; simp [haX]
          have hg_b : g b = Fin_embed n (n+1) (by omega) (f ⟨b.val, hbX⟩) := by
            unfold g; simp [hbX]
          have hg_eq : Fin_embed n (n+1) (by omega) (f ⟨a.val, haX⟩) =
              Fin_embed n (n+1) (by omega) (f ⟨b.val, hbX⟩) := by
            calc
              Fin_embed n (n+1) (by omega) (f ⟨a.val, haX⟩) = g a := by symm; exact hg_a
              _ = g b := h
              _ = Fin_embed n (n+1) (by omega) (f ⟨b.val, hbX⟩) := hg_b
          have h_f_val_eq : (f ⟨a.val, haX⟩).val = (f ⟨b.val, hbX⟩).val := by
            have h_val_eq : (Fin_embed n (n+1) (by omega) (f ⟨a.val, haX⟩)).val =
                (Fin_embed n (n+1) (by omega) (f ⟨b.val, hbX⟩)).val :=
              congrArg Subtype.val hg_eq
            simpa [Fin_embed] using h_val_eq
          have h_f_eq : f ⟨a.val, haX⟩ = f ⟨b.val, hbX⟩ := Subtype.val_inj.mp h_f_val_eq
          have h_ab_eq : (⟨a.val, haX⟩ : X) = (⟨b.val, hbX⟩ : X) := hf.1 h_f_eq
          have h_val_eq : a.val = b.val := by
            have : (⟨a.val, haX⟩ : X).val = (⟨b.val, hbX⟩ : X).val := congrArg Subtype.val h_ab_eq
            simpa using this
          exact Subtype.val_inj.mp h_val_eq
        · have hg_a : g a = Fin_embed n (n+1) (by omega) (f ⟨a.val, haX⟩) := by
            unfold g; simp [haX]
          have hg_b : g b = Fin_mk (n+1) n hn_lt_succ := by
            unfold g; simp [hbX]
          have h_val_eq : (Fin_embed n (n+1) (by omega) (f ⟨a.val, haX⟩)).val =
              (Fin_mk (n+1) n hn_lt_succ).val := by
            calc
              (Fin_embed n (n+1) (by omega) (f ⟨a.val, haX⟩)).val = (g a).val := by simp [hg_a]
              _ = (g b).val := congrArg Subtype.val h
              _ = (Fin_mk (n+1) n hn_lt_succ).val := by simp [hg_b]
          have h_f_val_eq : (f ⟨a.val, haX⟩).val = (n : Object) := by
            simpa [Fin_embed] using h_val_eq
          have h_mem_Fin : (f ⟨a.val, haX⟩).val ∈ Fin n := (f ⟨a.val, haX⟩).property
          have h_exists : ∃ (m : ℕ), m < n ∧ (f ⟨a.val, haX⟩).val = (m : Object) :=
            (mem_Fin n ((f ⟨a.val, haX⟩).val : Object)).mp h_mem_Fin
          rcases h_exists with ⟨m, hm, hm_f⟩
          have h_n_eq_m : (n : Object) = (m : Object) := by
            calc
              (n : Object) = (f ⟨a.val, haX⟩).val := by symm; exact h_f_val_eq
              _ = (m : Object) := hm_f
          have : n = m := (Object.natCast_inj n m).mp h_n_eq_m
          omega
      · by_cases hbX : b.val ∈ X
        · have hg_a : g a = Fin_mk (n+1) n hn_lt_succ := by
            unfold g; simp [haX]
          have hg_b : g b = Fin_embed n (n+1) (by omega) (f ⟨b.val, hbX⟩) := by
            unfold g; simp [hbX]
          have h_val_eq : (Fin_mk (n+1) n hn_lt_succ).val =
              (Fin_embed n (n+1) (by omega) (f ⟨b.val, hbX⟩)).val := by
            calc
              (Fin_mk (n+1) n hn_lt_succ).val = (g a).val := by simp [hg_a]
              _ = (g b).val := congrArg Subtype.val h
              _ = (Fin_embed n (n+1) (by omega) (f ⟨b.val, hbX⟩)).val := by simp [hg_b]
          have h_f_val_eq : (f ⟨b.val, hbX⟩).val = (n : Object) := by
            simpa [Fin_embed] using h_val_eq.symm
          have h_mem_Fin : (f ⟨b.val, hbX⟩).val ∈ Fin n := (f ⟨b.val, hbX⟩).property
          have h_exists : ∃ (m : ℕ), m < n ∧ (f ⟨b.val, hbX⟩).val = (m : Object) :=
            (mem_Fin n ((f ⟨b.val, hbX⟩).val : Object)).mp h_mem_Fin
          rcases h_exists with ⟨m, hm, hm_f⟩
          have h_n_eq_m : (n : Object) = (m : Object) := by
            calc
              (n : Object) = (f ⟨b.val, hbX⟩).val := by symm; exact h_f_val_eq
              _ = (m : Object) := hm_f
          have : n = m := (Object.natCast_inj n m).mp h_n_eq_m
          omega
        · have ha_val_eq_x : a.val = x := by
            have ha_mem_union : a.val ∈ X ∪ {x} := by
              simpa [hS] using a.property
            rw [SetTheory.Set.mem_union] at ha_mem_union
            rcases ha_mem_union with (h | h)
            · exact absurd h haX
            · rw [SetTheory.Set.mem_singleton] at h; exact h
          have hb_val_eq_x : b.val = x := by
            have hb_mem_union : b.val ∈ X ∪ {x} := by
              simpa [hS] using b.property
            rw [SetTheory.Set.mem_union] at hb_mem_union
            rcases hb_mem_union with (h | h)
            · exact absurd h hbX
            · rw [SetTheory.Set.mem_singleton] at h; exact h
          have h_val_eq : a.val = b.val := by
            rw [ha_val_eq_x, hb_val_eq_x]
          exact Subtype.val_inj.mp h_val_eq
    have hg_surjective : Function.Surjective g := by
      intro y
      by_cases hy_lt_n : (y : ℕ) < n
      · let y_fin_n : Fin n := Fin_mk n (y : ℕ) hy_lt_n
        rcases hf.2 y_fin_n with ⟨z, hz⟩
        have hz_mem_S : z.val ∈ S := by
          have : z.val ∈ X := z.property
          rw [hS, SetTheory.Set.mem_union]; left; exact this
        use ⟨z.val, hz_mem_S⟩
        apply Subtype.val_inj.mp
        calc
          (g ⟨z.val, hz_mem_S⟩).val = (Fin_embed n (n+1) (by omega) (f z)).val := by
            have : g ⟨z.val, hz_mem_S⟩ = Fin_embed n (n+1) (by omega) (f z) := by
              unfold g; simp [z.property]
            simp [this]
          _ = (f z).val := rfl
          _ = y_fin_n.val := by rw [hz]
          _ = ((y : ℕ) : Object) := by       simp [y_fin_n]
          _ = (y : Object) := by exact Fin.coe_toNat y
          _ = y.val := rfl
      · have hy_eq_n : (y : ℕ) = n := by
          have hy_lt_succ : (y : ℕ) < n+1 := Fin.toNat_lt y
          omega
        use ⟨x, hx_mem_union⟩
        apply Subtype.val_inj.mp
        calc
          (g ⟨x, hx_mem_union⟩).val = (Fin_mk (n+1) n hn_lt_succ).val := by
            have : g ⟨x, hx_mem_union⟩ = Fin_mk (n+1) n hn_lt_succ := by
              unfold g; simp [hx]
            simp [this]
          _ = (n : Object) := rfl
          _ = ((y : ℕ) : Object) := by simp [hy_eq_n]
          _ = (y : Object) := by exact Fin.coe_toNat y
          _ = y.val := rfl
    have hg_bijective : Function.Bijective g := ⟨hg_injective, hg_surjective⟩
    have h_finite : (X ∪ {x}).finite := ⟨n+1, by
      rw [← hS, has_card_iff]; exact ⟨g, hg_bijective⟩⟩
    have h_card : (X ∪ {x}).card = n + 1 := by
      have hS_has_card : (X ∪ {x}).has_card (n+1) := by
        rw [← hS, has_card_iff]; exact ⟨g, hg_bijective⟩
      rw [has_card_to_card hS_has_card, hn]
    exact ⟨h_finite, h_card⟩

/-- Proposition 3.6.14 (b) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_union {X Y:Set} (hX: X.finite) (hY: Y.finite) :
    (X ∪ Y).finite ∧ (X ∪ Y).card ≤ X.card + Y.card := by
  rcases hY with ⟨n, hYcard⟩
  induction n generalizing Y with
  | zero =>
    have hYempty : Y = ∅ := (has_card_zero.mp hYcard)
    have hYcard_val : Y.card = 0 := card_eq_zero_of_empty hYempty
    have h_finite : (X ∪ Y).finite := by
      rw [hYempty, union_empty]; exact hX
    have h_card : (X ∪ Y).card ≤ X.card + Y.card := by
      rw [hYcard_val, hYempty, union_empty]; omega
    exact ⟨h_finite, h_card⟩
  | succ k ih =>
    have hpos : k.succ ≥ 1 := by omega
    have hY_nonempty : Y ≠ ∅ := pos_card_nonempty hpos hYcard
    rcases nonempty_def hY_nonempty with ⟨y, hy⟩
    let y' : Y := ⟨y, hy⟩
    have h_erase : (Y \ {y}).has_card k := by
      have hpos : k.succ ≥ 1 := by omega
      simpa [Nat.succ_eq_add_one, Nat.add_one_sub_one] using card_erase hpos hYcard y'
    have h_ih := ih h_erase
    rcases h_ih with ⟨hZ_finite, hZ_card⟩
    have h_union_decomp : X ∪ Y = (X ∪ (Y \ {y})) ∪ {y} := by
      ext x
      constructor
      · intro hx
        rcases (SetTheory.Set.mem_union _ _ _).mp hx with (hxX | hxY)
        · apply (SetTheory.Set.mem_union _ _ _).mpr
          left
          apply (SetTheory.Set.mem_union _ _ _).mpr
          left; exact hxX
        · by_cases hx_eq : x = y
          · apply (SetTheory.Set.mem_union _ _ _).mpr
            right
            rw [SetTheory.Set.mem_singleton]; exact hx_eq
          · apply (SetTheory.Set.mem_union _ _ _).mpr
            left
            apply (SetTheory.Set.mem_union _ _ _).mpr
            right
            rw [SetTheory.Set.mem_sdiff]
            refine ⟨hxY, ?_⟩
            intro hx_singleton
            apply hx_eq
            rw [SetTheory.Set.mem_singleton] at hx_singleton
            exact hx_singleton
      · intro hx
        rcases (SetTheory.Set.mem_union _ _ _).mp hx with (hx_union | hx_singleton)
        · rcases (SetTheory.Set.mem_union _ _ _).mp hx_union with (hxX | hxYdiff)
          · apply (SetTheory.Set.mem_union _ _ _).mpr; left; exact hxX
          · apply (SetTheory.Set.mem_union _ _ _).mpr; right
            rw [SetTheory.Set.mem_sdiff] at hxYdiff; exact hxYdiff.1
        · rw [SetTheory.Set.mem_singleton] at hx_singleton
          subst hx_singleton
          apply (SetTheory.Set.mem_union _ _ _).mpr; right; exact hy
    by_cases hyZ : y ∈ X ∪ (Y \ {y})
    · have h_union_eq : X ∪ Y = X ∪ (Y \ {y}) := by
        calc
          X ∪ Y = (X ∪ (Y \ {y})) ∪ {y} := h_union_decomp
          _ = X ∪ (Y \ {y}) := by
            ext x
            constructor
            · intro hx
              rcases (SetTheory.Set.mem_union _ _ _).mp hx with (hx_union | hx_singleton)
              · exact hx_union
              · rw [SetTheory.Set.mem_singleton] at hx_singleton
                subst hx_singleton; exact hyZ
            · intro hx
              apply (SetTheory.Set.mem_union _ _ _).mpr; left; exact hx
      have hYcard_val : Y.card = k + 1 := has_card_to_card hYcard
      have hYdiff_card_val : (Y \ {y}).card = k := has_card_to_card h_erase
      have h_card : (X ∪ Y).card ≤ X.card + Y.card := by
        rw [h_union_eq]
        calc
          (X ∪ (Y \ {y})).card ≤ X.card + (Y \ {y}).card := hZ_card
          _ = X.card + k := by rw [hYdiff_card_val]
          _ ≤ X.card + (k + 1) := by omega
          _ = X.card + Y.card := by rw [hYcard_val]
      exact ⟨by rw [h_union_eq]; exact hZ_finite, h_card⟩
    · have h_insert : ((X ∪ (Y \ {y})) ∪ {y}).finite ∧ ((X ∪ (Y \ {y})) ∪ {y}).card = (X ∪ (Y \ {y})).card + 1 :=
        card_insert hZ_finite hyZ
      have hYcard_val : Y.card = k + 1 := has_card_to_card hYcard
      have hYdiff_card_val : (Y \ {y}).card = k := has_card_to_card h_erase
      have h_card : (X ∪ Y).card ≤ X.card + Y.card := by
        rw [h_union_decomp]
        rw [h_insert.2]
        calc
          (X ∪ (Y \ {y})).card + 1 ≤ (X.card + (Y \ {y}).card) + 1 := by omega
          _ = (X.card + k) + 1 := by rw [hYdiff_card_val]
          _ = X.card + (k + 1) := by omega
          _ = X.card + Y.card := by rw [hYcard_val]
      exact ⟨by rw [h_union_decomp]; exact h_insert.1, h_card⟩

/-- Proposition 3.6.14 (b) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_union_disjoint {X Y:Set} (hX: X.finite) (hY: Y.finite)
  (hdisj: Disjoint X Y) : (X ∪ Y).card = X.card + Y.card := by
  rcases card_union hX hY with ⟨h_finite_union, h_union_le⟩
  have h_ge : X.card + Y.card ≤ (X ∪ Y).card := by
    rcases hY with ⟨n, hYcard⟩
    let P : ℕ → Prop := fun m => ∀ (Y' : Set), Y'.has_card m → Disjoint X Y' → X.card + Y'.card ≤ (X ∪ Y').card
    have hP0 : P 0 := by
      intro Y' hn hdisj'
      have hYempty : Y' = ∅ := (has_card_zero.mp hn)
      have hY_card : Y'.card = 0 := card_eq_zero_of_empty hYempty
      have h_union_empty : X ∪ Y' = X := by rw [hYempty, union_empty]
      have h_eq : X.card + Y'.card = (X ∪ Y').card := by
        calc
          X.card + Y'.card = X.card + 0 := by rw [hY_card]
          _ = X.card := by omega
          _ = (X ∪ Y').card := by rw [h_union_empty]
      omega
    have hPsucc : ∀ k, P k → P (k.succ) := by
      intro k ih Y' hn hdisj'
      have hpos : k.succ ≥ 1 := by omega
      have hY_nonempty : Y' ≠ ∅ := pos_card_nonempty hpos hn
      rcases nonempty_def hY_nonempty with ⟨y, hy⟩
      let y' : Y' := ⟨y, hy⟩
      have h_erase : (Y' \ {y}).has_card k := card_erase hpos hn y'
      have h_erase_finite : (Y' \ {y}).finite := ⟨k, h_erase⟩
      have h_disjoint_sub : Disjoint X (Y' \ {y}) := by
        rw [SetTheory.Set.disjoint_iff] at hdisj' ⊢
        apply SetTheory.Set.eq_empty_iff_forall_notMem.mpr
        intro z hz
        rw [SetTheory.Set.mem_inter] at hz
        rcases hz with ⟨hzX, hzYdiff⟩
        rw [SetTheory.Set.mem_sdiff] at hzYdiff
        have hzY : z ∈ Y' := hzYdiff.1
        have hz_inter : z ∈ X ∩ Y' := by
          rw [SetTheory.Set.mem_inter]
          exact ⟨hzX, hzY⟩
        rw [hdisj'] at hz_inter
        exact SetTheory.Set.not_mem_empty z hz_inter
      have h_ih : X.card + (Y' \ {y}).card ≤ (X ∪ (Y' \ {y})).card :=
        ih (Y' \ {y}) h_erase h_disjoint_sub
      have h_union_finite : (X ∪ (Y' \ {y})).finite := (card_union hX h_erase_finite).1
      have h_union_decomp : X ∪ Y' = (X ∪ (Y' \ {y})) ∪ {y} := by
        ext x
        constructor
        · intro hx
          rcases (SetTheory.Set.mem_union _ _ _).mp hx with (hxX | hxY')
          · apply (SetTheory.Set.mem_union _ _ _).mpr
            left
            apply (SetTheory.Set.mem_union _ _ _).mpr
            left; exact hxX
          · by_cases hx_eq : x = y
            · apply (SetTheory.Set.mem_union _ _ _).mpr
              right
              rw [SetTheory.Set.mem_singleton]; exact hx_eq
            · apply (SetTheory.Set.mem_union _ _ _).mpr
              left
              apply (SetTheory.Set.mem_union _ _ _).mpr
              right
              rw [SetTheory.Set.mem_sdiff]
              refine ⟨hxY', ?_⟩
              intro hx_singleton
              apply hx_eq
              rw [SetTheory.Set.mem_singleton] at hx_singleton
              exact hx_singleton
        · intro hx
          rcases (SetTheory.Set.mem_union _ _ _).mp hx with (hx_union | hx_singleton)
          · rcases (SetTheory.Set.mem_union _ _ _).mp hx_union with (hxX | hxY'diff)
            · apply (SetTheory.Set.mem_union _ _ _).mpr; left; exact hxX
            · apply (SetTheory.Set.mem_union _ _ _).mpr; right
              rw [SetTheory.Set.mem_sdiff] at hxY'diff; exact hxY'diff.1
          · rw [SetTheory.Set.mem_singleton] at hx_singleton
            subst hx_singleton
            apply (SetTheory.Set.mem_union _ _ _).mpr; right; exact hy
      have hy_notin_union : y ∉ X ∪ (Y' \ {y}) := by
        intro hy_union
        rcases (SetTheory.Set.mem_union _ _ _).mp hy_union with (hyX | hyY'diff)
        · have hy_inter : y ∈ X ∩ Y' := by
            rw [SetTheory.Set.mem_inter]; exact ⟨hyX, hy⟩
          rw [SetTheory.Set.disjoint_iff] at hdisj'
          rw [hdisj'] at hy_inter
          exact SetTheory.Set.not_mem_empty y hy_inter
        · rw [SetTheory.Set.mem_sdiff] at hyY'diff
          exact hyY'diff.2 (by
            rw [SetTheory.Set.mem_singleton])
      have h_insert : ((X ∪ (Y' \ {y})) ∪ {y}).finite ∧ ((X ∪ (Y' \ {y})) ∪ {y}).card = (X ∪ (Y' \ {y})).card + 1 :=
        card_insert h_union_finite hy_notin_union
      have hY_card_val : Y'.card = k + 1 := has_card_to_card hn
      have hYdiff_card_val : (Y' \ {y}).card = k := has_card_to_card h_erase
      calc
        X.card + Y'.card = X.card + (k + 1) := by rw [hY_card_val]
        _ = (X.card + k) + 1 := by omega
        _ = (X.card + (Y' \ {y}).card) + 1 := by rw [hYdiff_card_val]
        _ ≤ (X ∪ (Y' \ {y})).card + 1 := by omega
        _ = ((X ∪ (Y' \ {y})) ∪ {y}).card := by rw [h_insert.2]
        _ = (X ∪ Y').card := by rw [h_union_decomp]
    have hPn : P n := Nat.rec hP0 hPsucc n
    exact hPn Y hYcard hdisj
  omega

/-- Proposition 3.6.14 (c) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_subset {X Y:Set} (hX: X.finite) (hY: Y ⊆ X) :
    Y.finite ∧ Y.card ≤ X.card := by
  rcases hX with ⟨n, hXn⟩
  have h_main : ∀ (n : ℕ) (X Y : Set), X.has_card n → (Y ⊆ X) → Y.finite ∧ Y.card ≤ X.card := by
    intro n
    induction n with
    | zero =>
        intro X Y hXn hY
        have hXempty : X = ∅ := (has_card_zero.mp hXn)
        have hYempty : Y = ∅ := by
          rw [eq_empty_iff_forall_notMem]
          intro x hx
          have hxX : x ∈ X := hY x hx
          rw [hXempty] at hxX
          exact not_mem_empty x hxX
        have hYfinite : Y.finite := finite_of_empty hYempty
        have hYcard : Y.card = 0 := card_eq_zero_of_empty hYempty
        have hXcard : X.card = 0 := card_eq_zero_of_empty hXempty
        have card_le : Y.card ≤ X.card := by
          simpa [hYcard, hXcard] using Nat.zero_le 0
        exact ⟨hYfinite, card_le⟩
    | succ k ih =>
        intro X Y hXn hY
        have hpos : k.succ ≥ 1 := by omega
        have hX_nonempty : X ≠ ∅ := pos_card_nonempty hpos hXn
        rcases nonempty_def hX_nonempty with ⟨x, hx⟩
        let x' : X := ⟨x, hx⟩
        have h_erase : (X \ {x'.val}).has_card k := by
          have htemp := card_erase (by omega) hXn x'
          have : k.succ - 1 = k := by omega
          simpa [this] using htemp
        by_cases hxY : x ∈ Y
        · set Y' := Y \ {x'.val} with hY'
          have hY'_sub_X' : Y' ⊆ (X \ {x'.val}) := by
            intro y hy
            rw [hY', mem_sdiff] at hy
            rw [mem_sdiff]
            exact ⟨hY y hy.1, hy.2⟩
          rcases ih (X \ {x'.val}) Y' h_erase hY'_sub_X' with ⟨hY'_finite, hY'_card⟩
          have hx_notin_Y' : x'.val ∉ Y' := by
            intro hxY'
            rw [hY', mem_sdiff] at hxY'
            rcases hxY' with ⟨_, hx_singleton⟩
            exact hx_singleton ((mem_singleton _ _).mpr rfl)
          have hcard_insert := card_insert hY'_finite hx_notin_Y'
          rcases hcard_insert with ⟨hY'_union_finite, hY'_union_card⟩
          have hY_eq : Y = Y' ∪ {x'.val} := by
            ext y
            constructor
            · intro hyY
              rw [mem_union]
              by_cases hy_eq : y = x'.val
              · right; rw [mem_singleton]; exact hy_eq
              · left
                rw [hY', mem_sdiff]
                exact ⟨hyY, by
                  intro hyx; rw [mem_singleton] at hyx; exact hy_eq hyx⟩
            · intro hy_union
              rw [mem_union] at hy_union
              rcases hy_union with (hyY' | hy_singleton)
              · rw [hY', mem_sdiff] at hyY'; exact hyY'.1
              · rw [mem_singleton] at hy_singleton; subst hy_singleton; exact hxY
          have hYfinite : Y.finite := by
            rw [hY_eq]
            exact hY'_union_finite
          have hXcard : X.card = k.succ := has_card_to_card hXn
          have hX'card : (X \ {x'.val}).card = k := has_card_to_card h_erase
          have card_le : Y.card ≤ X.card := by
            rw [hY_eq, hY'_union_card, hXcard]
            have : Y'.card ≤ (X \ {x'.val}).card := hY'_card
            rw [hX'card] at this
            omega
          exact ⟨hYfinite, card_le⟩
        · have hY_sub_X' : Y ⊆ (X \ {x'.val}) := by
            intro y hy
            rw [mem_sdiff]
            constructor
            · exact hY y hy
            · intro hyx
              have hy_eq : y = x'.val := (mem_singleton _ _).mp hyx
              subst hy_eq
              exfalso; exact hxY hy
          rcases ih (X \ {x'.val}) Y h_erase hY_sub_X' with ⟨hYfinite, hYcard⟩
          have hXcard : X.card = k.succ := has_card_to_card hXn
          have hX'card : (X \ {x'.val}).card = k := has_card_to_card h_erase
          have card_le : Y.card ≤ X.card := by
            rw [hXcard]
            have : Y.card ≤ (X \ {x'.val}).card := hYcard
            rw [hX'card] at this
            omega
          exact ⟨hYfinite, card_le⟩
  exact h_main n X Y hXn hY

/-- Proposition 3.6.14 (c) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_ssubset {X Y:Set} (hX: X.finite) (hY: Y ⊂ X) :
    Y.card < X.card := by
  rcases hY with ⟨hY_sub, hY_ne⟩
  have h_exists : ∃ x, x ∈ X ∧ x ∉ Y := by
    by_contra h
    have hX_sub_Y : X ⊆ Y := by
      intro x hx
      by_contra hnx
      apply h
      refine ⟨x, ?_⟩
      exact ⟨hx, hnx⟩
    have h_eq : X = Y := subset_antisymm X Y hX_sub_Y hY_sub
    exact hY_ne h_eq.symm
  rcases h_exists with ⟨x, hxX, hxY⟩
  have h_union_sub_X : Y ∪ {x} ⊆ X := by
    intro z hz
    rcases (mem_union z Y {x}).mp hz with (hzY | hz_singleton)
    · exact hY_sub z hzY
    · have hz_eq_x : z = x := (mem_singleton z x).mp hz_singleton
      rw [hz_eq_x]
      exact hxX
  have h_card_union_sub : (Y ∪ {x}).card ≤ X.card :=
    (card_subset hX h_union_sub_X).2
  have hY_finite : Y.finite := (card_subset hX hY_sub).1
  have h_card_union_eq : (Y ∪ {x}).card = Y.card + 1 :=
    (card_insert hY_finite hxY).2
  have h_ineq : Y.card + 1 ≤ X.card := by
    calc
      Y.card + 1 = (Y ∪ {x}).card := by symm; exact h_card_union_eq
      _ ≤ X.card := h_card_union_sub
  omega

/-- Proposition 3.6.14 (d) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_image {X Y:Set} (hX: X.finite) (f: X → Y) :
    (image f X).finite ∧ (image f X).card ≤ X.card := by
  rcases hX with ⟨n, hn⟩
  have h_main : ∀ (n : ℕ) (X Y : Set), X.has_card n → (∀ (f : X → Y), (image f X).finite ∧ (image f X).card ≤ X.card) := by
    intro n
    induction n with
    | zero =>
      intro X Y hX f
      have hXempty : X = ∅ := (has_card_zero.mp hX)
      subst hXempty
      have hImEmpty : image f ∅ = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro y hy
        rw [mem_image] at hy
        rcases hy with ⟨x, hx, _⟩
        exact not_mem_empty x.val hx
      have hfinite : (image f ∅).finite := by
        rw [hImEmpty]; exact empty_finite
      have hcard : (image f ∅).card ≤ (∅ : Set).card := by
        rw [hImEmpty, empty_card_eq_zero]
      exact ⟨hfinite, hcard⟩
    | succ k ih =>
      intro X Y hX f
      have hpos : k.succ ≥ 1 := by omega
      have hX_nonempty : X ≠ ∅ := pos_card_nonempty hpos hX
      rcases nonempty_def hX_nonempty with ⟨x, hx⟩
      let x' : X := ⟨x, hx⟩
      have h_erase : (X \ {x'.val}).has_card k := by
        have htemp := card_erase (by omega) hX x'
        have : k.succ - 1 = k := by omega
        simpa [this] using htemp
      set X' := X \ {x'.val} with hX'
      have hX'_sub_X : X' ⊆ X := by
        intro y hy
        rw [hX', mem_sdiff] at hy; exact hy.1
      let f' : X' → Y := fun x'' => f ⟨x''.val, hX'_sub_X x''.val x''.property⟩
      have h_image_agree : image f' X' = image f X' := by
        ext y
        rw [mem_image, mem_image]
        constructor
        · rintro ⟨z, hz, hz_f⟩
          refine ⟨⟨z.val, hX'_sub_X z.val z.property⟩, z.property, ?_⟩
          simpa [f'] using hz_f
        · rintro ⟨z, hz, hz_f⟩
          let z' : X' := ⟨z.val, hz⟩
          refine ⟨z', z'.property, ?_⟩
          dsimp [f']
          have hz_eq : (⟨z.val, hX'_sub_X z.val hz⟩ : X) = z := Subtype.ext rfl
          simpa [hz_eq] using hz_f
      have hX'card : X'.card = k := has_card_to_card h_erase
      have hXcard : X.card = k.succ := has_card_to_card hX
      have ihX' : ∀ (f' : X' → Y), (image f' X').finite ∧ (image f' X').card ≤ X'.card :=
        ih X' Y h_erase
      rcases ihX' f' with ⟨hImX'finite', hImX'card'⟩
      have hImX'finite : (image f X').finite := by
        simpa [h_image_agree] using hImX'finite'
      have hImX'card : (image f X').card ≤ X'.card := by
        simpa [h_image_agree] using hImX'card'
      have hImX'card_le_k : (image f X').card ≤ k := by
        rw [hX'card] at hImX'card; exact hImX'card
      have hX_split : X = X' ∪ {x'.val} := by
        ext y
        constructor
        · intro hyX
          rw [mem_union]
          by_cases hy_eq : y = x'.val
          · right; rw [mem_singleton]; exact hy_eq
          · left; rw [hX', mem_sdiff]; exact ⟨hyX, by
            intro hy_sing; rw [mem_singleton] at hy_sing; exact hy_eq hy_sing⟩
        · intro hy_union
          rw [mem_union] at hy_union
          rcases hy_union with (hyX' | hy_sing)
          · rw [hX', mem_sdiff] at hyX'; exact hyX'.1
          · rw [mem_singleton] at hy_sing; subst hy_sing; exact hx
      have h_image_split : image f X = (image f X') ∪ (image f {x'.val}) := by
        calc
          image f X = image f (X' ∪ {x'.val}) := by
            simp [hX_split]
          _ = (image f X') ∪ (image f {x'.val}) := image_of_union f X' {x'.val}
      have h_image_singleton : image f {x'.val} = {(f x').val} := by
        ext y
        rw [mem_image, mem_singleton]
        constructor
        · rintro ⟨z, hz, hz_f⟩
          rw [mem_singleton] at hz
          have hz_eq : z = x' := Subtype.val_inj.mp hz
          subst hz_eq
          exact hz_f.symm
        · intro h
          subst h
          use x'
          simp [mem_singleton]
      have h_image_split' : image f X = (image f X') ∪ {(f x').val} := by
        rw [h_image_split, h_image_singleton]
      by_cases h_fx_mem : (f x').val ∈ image f X'
      · have h_union_eq : (image f X') ∪ {(f x').val} = image f X' := by
          ext y
          constructor
          · intro hy
            rw [mem_union] at hy
            rcases hy with (hy' | hy_sing)
            · exact hy'
            · rw [mem_singleton] at hy_sing; subst hy_sing; exact h_fx_mem
          · intro hy; rw [mem_union]; left; exact hy
        have hfinite : (image f X).finite := by
          rw [h_image_split', h_union_eq]; exact hImX'finite
        have hcard : (image f X).card ≤ X.card := by
          rw [h_image_split', h_union_eq, hXcard]
          omega
        exact ⟨hfinite, hcard⟩
      · have h_insert := card_insert hImX'finite h_fx_mem
        rcases h_insert with ⟨h_union_finite, h_union_card⟩
        have hfinite : (image f X).finite := by
          rw [h_image_split']; exact h_union_finite
        have hcard : (image f X).card ≤ X.card := by
          rw [h_image_split', h_union_card, hXcard]
          omega
        exact ⟨hfinite, hcard⟩
  exact h_main n X Y hn f

/-- Proposition 3.6.14 (d) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_image_inj {X Y:Set} (_hX: X.finite) {f: X → Y}
  (hf: Function.Injective f) : (image f X).card = X.card := by
  have h_image_equiv : EqualCard X (image f X) := by
    let g : X → image f X := fun x => ⟨f x, by
      rw [mem_image]
      exact ⟨x, x.property, rfl⟩⟩
    refine ⟨g, ?_, ?_⟩
    · intro a b h
      have hval : (g a).val = (g b).val := congrArg Subtype.val h
      have : f a = f b := Subtype.val_inj.mp (by simpa [g] using hval)
      exact hf this
    · intro y
      have hy_mem : y.val ∈ image f X := y.property
      rw [mem_image] at hy_mem
      rcases hy_mem with ⟨x, hx, hx_eq⟩
      use x
      apply Subtype.ext
      simpa [g] using hx_eq
  exact (EquivCard_to_card_eq h_image_equiv).symm

/-- Proposition 3.6.14 (e) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_prod {X Y:Set} (hX: X.finite) (hY: Y.finite) :
    (X ×ˢ Y).finite ∧ (X ×ˢ Y).card = X.card * Y.card := by
  rcases hY with ⟨n, hYcard⟩
  have h_main : ∀ (n : ℕ) (Y : Set), Y.has_card n → (X ×ˢ Y).finite ∧ (X ×ˢ Y).card = X.card * Y.card := by
    intro n
    induction n with
    | zero =>
        intro Y hYcard
        have hYempty : Y = ∅ := (has_card_zero.mp hYcard)
        subst hYempty
        have hprod_empty : X ×ˢ (∅ : Set) = ∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro z hz
          rw [mem_cartesian] at hz
          rcases hz with ⟨x, y, hz⟩
          exact (Set.not_mem_empty y.val) y.property
        have h_finite : (X ×ˢ (∅ : Set)).finite := by
          rw [hprod_empty]; exact empty_finite
        have h_card : (X ×ˢ (∅ : Set)).card = X.card * (∅ : Set).card := by
          rw [hprod_empty, empty_card_eq_zero, mul_zero]
        exact ⟨h_finite, h_card⟩
    | succ k ih =>
        intro Y hYcard
        have hpos : k.succ ≥ 1 := by omega
        have hY_nonempty : Y ≠ ∅ := pos_card_nonempty hpos hYcard
        rcases nonempty_def hY_nonempty with ⟨y, hy⟩
        let y_set : Set := {y}
        let y_sing : y_set := ⟨y, by rw [SetTheory.Set.mem_singleton]⟩
        have h_erase : (Y \ y_set).has_card k := by
          simpa [Nat.succ_eq_add_one, Nat.add_one_sub_one] using card_erase hpos hYcard (⟨y, hy⟩ : Y)
        have h_erase_finite : (Y \ y_set).finite := ⟨k, h_erase⟩
        have h_ih := ih (Y \ y_set) h_erase
        rcases h_ih with ⟨h_prod_Ydiff_finite, h_prod_Ydiff_card⟩
        have h_card_Ydiff_val : (Y \ y_set).card = k := has_card_to_card h_erase
        have hYcard_val : Y.card = k.succ := has_card_to_card hYcard
        have h_prod_singleton_equiv : EqualCard X (X ×ˢ y_set) := by
          let f : X → X ×ˢ y_set := fun x => mk_cartesian x y_sing
          refine ⟨f, ?_, ?_⟩
          · intro a b h
            have h_fst : fst (f a) = fst (f b) := congrArg fst h
            simp [f] at h_fst
            exact h_fst
          · intro z
            have hz_mem : z.val ∈ X ×ˢ y_set := z.property
            rw [mem_cartesian] at hz_mem
            rcases hz_mem with ⟨x', z', hz_eq⟩
            use x'
            apply Subtype.ext
            calc
              (f x').val = (mk_cartesian x' y_sing).val := rfl
              _ = (⟨x', y_sing⟩ : OrderedPair) := rfl
              _ = (⟨x', z'⟩ : OrderedPair) := by
                have hz'_val : z'.val = y := by
                  have : z'.val ∈ y_set := z'.property
                  simp [y_set, SetTheory.Set.mem_singleton] at this; exact this
                have h_singleton_eq : y_sing = z' := Subtype.ext (by
                  calc
                    y_sing.val = y := rfl
                    _ = z'.val := hz'_val.symm)
                rw [h_singleton_eq]
              _ = z.val := hz_eq.symm
        have h_prod_singleton_card : (X ×ˢ y_set).card = X.card :=
          (EquivCard_to_card_eq h_prod_singleton_equiv).symm
        have h_prod_singleton_finite : (X ×ˢ y_set).finite := by
          have hX_has_card : X.has_card (X.card) := has_card_card hX
          have h_prod_has_card : (X ×ˢ y_set).has_card (X.card) :=
            ((EquivCard_to_has_card_eq h_prod_singleton_equiv).mp hX_has_card)
          exact ⟨X.card, h_prod_has_card⟩
        have hY_decomp : Y = (Y \ y_set) ∪ y_set := by
          ext x
          constructor
          · intro hx
            by_cases hx_eq : x = y
            · rw [mem_union]; right; rw [SetTheory.Set.mem_singleton]; exact hx_eq
            · rw [mem_union]; left; rw [mem_sdiff]; refine ⟨hx, ?_⟩
              intro hx_singleton
              rw [SetTheory.Set.mem_singleton] at hx_singleton
              exact hx_eq hx_singleton
          · intro hx
            rw [mem_union] at hx
            rcases hx with (hx | hx)
            · rw [mem_sdiff] at hx; exact hx.1
            · rw [SetTheory.Set.mem_singleton] at hx; subst x; exact hy
        have h_prod_decomp : X ×ˢ Y = (X ×ˢ (Y \ y_set)) ∪ (X ×ˢ y_set) :=
          calc
            X ×ˢ Y = X ×ˢ ((Y \ y_set) ∪ y_set) := congrArg (fun S : Set => X ×ˢ S) hY_decomp
            _ = (X ×ˢ (Y \ y_set)) ∪ (X ×ˢ y_set) := by rw [prod_union]
        have h_disjoint : Disjoint (X ×ˢ (Y \ y_set)) (X ×ˢ y_set) := by
          rw [disjoint_iff]
          apply eq_empty_iff_forall_notMem.mpr
          intro z hz
          rw [mem_inter] at hz
          rcases hz with ⟨hz1, hz2⟩
          rw [prod_diff X Y y_set] at hz1
          rw [mem_sdiff] at hz1
          exact hz1.2 hz2
        have h_card_union : (X ×ˢ Y).card = (X ×ˢ (Y \ y_set)).card + (X ×ˢ y_set).card := by
          rw [h_prod_decomp]
          exact card_union_disjoint h_prod_Ydiff_finite h_prod_singleton_finite h_disjoint
        have h_finite : (X ×ˢ Y).finite := by
          rw [h_prod_decomp]
          exact (card_union h_prod_Ydiff_finite h_prod_singleton_finite).1
        have h_card : (X ×ˢ Y).card = X.card * Y.card := by
          calc
            (X ×ˢ Y).card = (X ×ˢ (Y \ y_set)).card + (X ×ˢ y_set).card := h_card_union
            _ = (X.card * (Y \ y_set).card) + (X ×ˢ y_set).card := by rw [h_prod_Ydiff_card]
            _ = (X.card * k) + (X ×ˢ y_set).card := by rw [h_card_Ydiff_val]
            _ = (X.card * k) + X.card := by rw [h_prod_singleton_card]
            _ = X.card * (k + 1) := by rw [Nat.mul_succ]
            _ = X.card * Y.card := by rw [hYcard_val, Nat.succ_eq_add_one]
        exact ⟨h_finite, h_card⟩
  exact h_main n Y hYcard

noncomputable def SetTheory.Set.pow_fun_equiv {A B : Set} : ↑(A ^ B) ≃ (B → A) where
  toFun x :=
    have h := (powerset_axiom x.val).mp x.property
    h.choose
  invFun g :=
    have h : (g : Object) ∈ A ^ B := by
      rw [powerset_axiom]
      exact ⟨g, rfl⟩
    ⟨(g : Object), h⟩
  left_inv x := by
    have h := (powerset_axiom x.val).mp x.property
    ext
    exact h.choose_spec
  right_inv g := by
    have hm : (g : Object) ∈ A ^ B := by
      rw [powerset_axiom]
      exact ⟨g, rfl⟩
    have h := (powerset_axiom (g : Object)).mp hm
    have hspec : (h.choose : Object) = (g : Object) := h.choose_spec
    exact (coe_of_fun_inj h.choose g).mp hspec

lemma SetTheory.Set.pow_fun_eq_iff {A B : Set} (x y : ↑(A ^ B)) : x = y ↔ pow_fun_equiv x = pow_fun_equiv y := by
  rw [←pow_fun_equiv.apply_eq_iff_eq]

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

/-- Proposition 3.6.14 (f) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_pow {X Y:Set} (hY: Y.finite) (hX: X.finite) :
    (Y ^ X).finite ∧ (Y ^ X).card = Y.card ^ X.card := by
  have hX_finite_type : Finite X := (finite_iff_finite.mp hX)
  have hY_finite_type : Finite Y := (finite_iff_finite.mp hY)
  haveI : Finite X := hX_finite_type
  haveI : Finite Y := hY_finite_type
  have h_pow_finite_type : Finite (↑(Y ^ X)) :=
    Finite.of_equiv (X → Y) (pow_fun_equiv (A := Y) (B := X)).symm
  have h_finite : (Y ^ X).finite :=
    (finite_iff_finite.mpr h_pow_finite_type)
  have h_card_eq : (Y ^ X).card = Y.card ^ X.card := by
    calc
      (Y ^ X).card = Nat.card (↑(Y ^ X)) := by
        rw [card_eq_nat_card]
      _ = Nat.card (X → Y) := by
        rw [Nat.card_congr (pow_fun_equiv (A := Y) (B := X))]
      _ = Nat.card Y ^ Nat.card X := by
        rw [Nat.card_fun]
      _ = Y.card ^ X.card := by
        rw [card_eq_nat_card (X := Y), card_eq_nat_card (X := X)]
  exact ⟨h_finite, h_card_eq⟩

/-- Exercise 3.6.5. You might find {name}`SetTheory.Set.prod_commutator` useful. -/
theorem SetTheory.Set.prod_EqualCard_prod (A B:Set) :
    EqualCard (A ×ˢ B) (B ×ˢ A) := by
  use (prod_commutator A B)
  exact (prod_commutator A B).bijective

noncomputable abbrev SetTheory.Set.pow_fun_equiv' (A B : Set) : ↑(A ^ B) ≃ (B → A) :=
  pow_fun_equiv (A:=A) (B:=B)

/-- Exercise 3.6.6. You may find {name}`SetTheory.Set.curry_equiv` useful. -/
theorem SetTheory.Set.pow_pow_EqualCard_pow_prod (A B C:Set) :
    EqualCard ((A ^ B) ^ C) (A ^ (B ×ˢ C)) := by
  let e : ↑((A ^ B) ^ C) ≃ ↑(A ^ (B ×ˢ C)) :=
    (pow_fun_equiv (A := A ^ B) (B := C)).trans
      ((Equiv.piCongrRight fun _ : ↑C => pow_fun_equiv (A := A) (B := B)).trans
        ((curry_equiv (X := C) (Y := B) (Z := A)).trans
          ((Equiv.arrowCongr (prod_commutator C B) (Equiv.refl A)).trans
            (pow_fun_equiv (A := A) (B := B ×ˢ C)).symm)))
  use e
  exact e.bijective

omit [SetTheory] in
theorem SetTheory.Set.pow_pow_eq_pow_mul (a b c:ℕ): (a^b)^c = a^(b*c) := (Nat.pow_mul a b c).symm

theorem SetTheory.Set.pow_prod_pow_EqualCard_pow_union (A B C:Set) (hd: Disjoint B C) :
    EqualCard ((A ^ B) ×ˢ (A ^ C)) (A ^ (B ∪ C)) := by
  let BC : Set := B ∪ C
  have h_equiv : (B → A) × (C → A) ≃ (BC → A) := by
    classical
    let F : (B → A) × (C → A) → (BC → A) := λ ⟨f, g⟩ x =>
      if hB : x.val ∈ B then f ⟨x.val, hB⟩ else
        have hC : x.val ∈ C := by
          have hxBC : x.val ∈ BC := x.property
          dsimp [BC] at hxBC
          have hmem := (mem_union x.val B C).mp hxBC
          rcases hmem with (hB' | hC')
          · exact (hB hB').elim
          · exact hC'
        g ⟨x.val, hC⟩
    let G : (BC → A) → (B → A) × (C → A) := λ h =>
      (λ b => h ⟨b.val, by
        dsimp [BC]
        exact (mem_union b.val B C).mpr (Or.inl b.property)⟩,
       λ c => h ⟨c.val, by
        dsimp [BC]
        exact (mem_union c.val B C).mpr (Or.inr c.property)⟩)
    have h_left : ∀ x, G (F x) = x := by
      intro x
      rcases x with ⟨f, g⟩
      have h1 : (G (F (f, g))).1 = f := by
        funext b
        dsimp [F, G]
        by_cases hB : b.val ∈ B
        · simp [hB]
        · exfalso; exact hB b.property
      have h2 : (G (F (f, g))).2 = g := by
        funext c
        dsimp [F, G]
        have hc_not_B : c.val ∉ B := by
          intro hcB
          have h_inter : c.val ∈ B ∩ C := by
            rw [mem_inter]; exact ⟨hcB, c.property⟩
          have h_inter_eq : B ∩ C = ∅ := (disjoint_iff _ _).mp hd
          rw [h_inter_eq] at h_inter
          exact not_mem_empty _ h_inter
        simp [hc_not_B]
      exact Prod.ext h1 h2
    have h_right : ∀ h, F (G h) = h := by
      intro h
      funext x
      dsimp [F, G]
      by_cases hxB : x.val ∈ B
      · simp [hxB]
      · have hxC : x.val ∈ C := by
          have hxBC : x.val ∈ BC := x.property
          dsimp [BC] at hxBC
          have hmem := (mem_union x.val B C).mp hxBC
          rcases hmem with (hB' | hC')
          · exact (hxB hB').elim
          · exact hC'
        simp [hxB]
    exact ⟨F, G, h_left, h_right⟩
  have h_prod : ↑(A ^ B) × ↑(A ^ C) ≃ ↑((A ^ B) ×ˢ (A ^ C)) :=
    ⟨ λ ⟨x, y⟩ => mk_cartesian x y,
      λ z => (fst z, snd z),
      by
        intro ⟨x, y⟩
        ext <;> simp [fst_of_mk_cartesian, snd_of_mk_cartesian],
      by
        intro z
        exact mk_cartesian_fst_snd_eq z ⟩
  let e : ↑((A ^ B) ×ˢ (A ^ C)) ≃ ↑(A ^ (B ∪ C)) :=
    (h_prod.symm.trans
      (((pow_fun_equiv (A := A) (B := B)).prodCongr (pow_fun_equiv (A := A) (B := C))).trans
        (h_equiv.trans
          (pow_fun_equiv (A := A) (B := BC)).symm)))
  refine ⟨e.toFun, ?_⟩
  exact e.bijective

omit [SetTheory] in
theorem SetTheory.Set.pow_mul_pow_eq_pow_add (a b c:ℕ): (a^b) * a^c = a^(b+c) :=
  (Nat.pow_add a b c).symm

/-- Exercise 3.6.7 -/
theorem SetTheory.Set.injection_iff_card_le {A B:Set} (hA: A.finite) (hB: B.finite) :
    (∃ f:A → B, Function.Injective f) ↔ A.card ≤ B.card := by
  constructor
  · intro ⟨f, hf⟩
    have h_image_sub_B : image f A ⊆ B := image_in_codomain f A
    have h_card_image : (image f A).card = A.card := card_image_inj hA hf
    have h_card_le : (image f A).card ≤ B.card := (card_subset hB h_image_sub_B).2
    calc
      A.card = (image f A).card := by symm; exact h_card_image
      _ ≤ B.card := h_card_le
  · intro hcard
    have hA_has_card : A.has_card (A.card) := has_card_card hA
    have hB_has_card : B.has_card (B.card) := has_card_card hB
    rw [has_card_iff] at hA_has_card hB_has_card
    rcases hA_has_card with ⟨fA, hfA⟩
    rcases hB_has_card with ⟨fB, hfB⟩
    let eA : A ≃ Fin (A.card) := Equiv.ofBijective fA hfA
    let eB : B ≃ Fin (B.card) := Equiv.ofBijective fB hfB
    let i : Fin (A.card) → Fin (B.card) := λ x =>
      Fin_mk (B.card) (x : ℕ) (by
        have hx_lt : (x : ℕ) < A.card := Fin.toNat_lt x
        omega)
    have hi : Function.Injective i := by
      intro x y h
      apply Fin.coe_inj.2
      have h_val : (i x : ℕ) = (i y : ℕ) := congrArg (λ z : Fin (B.card) => (z : ℕ)) h
      simp [i] at h_val
      exact h_val
    let f : A → B := eB.symm ∘ i ∘ eA
    have hf_inj : Function.Injective f :=
      (eB.symm.injective.comp hi).comp eA.injective
    exact ⟨f, hf_inj⟩

/-- Exercise 3.6.8 -/
theorem SetTheory.Set.surjection_from_injection {A B:Set} (hA: A ≠ ∅) (f: A → B)
  (hf: Function.Injective f) : ∃ g:B → A, Function.Surjective g := by
  rcases nonempty_def hA with ⟨x0, hx0⟩
  let x0' : A := ⟨x0, hx0⟩
  classical
  let g : B → A := λ b =>
    if h : ∃ a : A, f a = b then
      Classical.choose h
    else
      x0'
  refine ⟨g, ?_⟩
  intro a
  use f a
  have h_ex : ∃ a' : A, f a' = f a := ⟨a, rfl⟩
  have h_pos : g (f a) = Classical.choose h_ex := by
    dsimp [g]
    simp
  have h_choice_eq : Classical.choose h_ex = a := hf (Classical.choose_spec h_ex)
  calc
    g (f a) = Classical.choose h_ex := h_pos
    _ = a := h_choice_eq

/-- Exercise 3.6.9 -/
theorem SetTheory.Set.card_union_add_card_inter {A B:Set} (hA: A.finite) (hB: B.finite) :
    A.card + B.card = (A ∪ B).card + (A ∩ B).card := by
  have h_sdiff_subset : A \ B ⊆ A := by
    intro x hx; rw [mem_sdiff] at hx; exact hx.1
  have h_finite_I : (A ∩ B).finite := (card_subset hA (inter_subset_left A B)).1
  have h_finite_D : (A \ B).finite := (card_subset hA h_sdiff_subset).1
  have h_disjoint_D_B : Disjoint (A \ B) B := by
    rw [disjoint_iff]
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    rw [mem_inter, mem_sdiff] at hx
    rcases hx with ⟨⟨hxA, hx_notB⟩, hxB⟩
    exact hx_notB hxB
  have h_disjoint_D_I : Disjoint (A \ B) (A ∩ B) := by
    rw [disjoint_iff]
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    rw [mem_inter, mem_sdiff, mem_inter] at hx
    rcases hx with ⟨⟨hxA, hx_notB⟩, ⟨hxA', hxB⟩⟩
    exact hx_notB hxB
  have h_union_eq : (A \ B) ∪ B = A ∪ B := by
    ext x
    constructor
    · intro hx
      rw [mem_union] at hx
      rcases hx with (hx' | hxB)
      · rw [mem_sdiff] at hx'; rw [mem_union]; left; exact hx'.1
      · rw [mem_union]; right; exact hxB
    · intro hx
      rw [mem_union] at hx
      rcases hx with (hxA | hxB)
      · by_cases hxB' : x ∈ B
        · rw [mem_union]; right; exact hxB'
        · rw [mem_union]; left; rw [mem_sdiff]; exact ⟨hxA, hxB'⟩
      · rw [mem_union]; right; exact hxB
  have h_A_decomp : A = (A \ B) ∪ (A ∩ B) := by
    ext x
    constructor
    · intro hx
      rw [mem_union]
      by_cases hxB : x ∈ B
      · right; rw [mem_inter]; exact ⟨hx, hxB⟩
      · left; rw [mem_sdiff]; exact ⟨hx, hxB⟩
    · intro hx
      rw [mem_union] at hx
      rcases hx with (hx' | hx')
      · rw [mem_sdiff] at hx'; exact hx'.1
      · rw [mem_inter] at hx'; exact hx'.1
  have h_card_A : A.card = (A \ B).card + (A ∩ B).card := by
    calc
      A.card = ((A \ B) ∪ (A ∩ B)).card := congrArg (·.card) h_A_decomp
      _ = (A \ B).card + (A ∩ B).card := card_union_disjoint h_finite_D h_finite_I h_disjoint_D_I
  have h_card_union_eq : (A ∪ B).card = (A \ B).card + B.card := by
    calc
      (A ∪ B).card = ((A \ B) ∪ B).card := (congrArg (·.card) h_union_eq).symm
      _ = (A \ B).card + B.card := card_union_disjoint h_finite_D hB h_disjoint_D_B
  calc
    A.card + B.card = ((A \ B).card + (A ∩ B).card) + B.card := by rw [h_card_A]
    _ = (A \ B).card + (B.card + (A ∩ B).card) := by omega
    _ = ((A \ B).card + B.card) + (A ∩ B).card := by omega
    _ = (A ∪ B).card + (A ∩ B).card := by rw [h_card_union_eq]

private theorem SetTheory.Set.pigeonhole_aux {n:ℕ} (A: Fin n → Set) (h_cards : ∀ i, (A i).card ≤ 1) :
    (iUnion (Fin n) A).card ≤ n := by
  induction n with
  | zero =>
    have hFin0empty : (Fin 0 : Set) = ∅ := by
      ext x; simp
    have h_empty : iUnion (Fin 0) A = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      rw [mem_iUnion] at hx
      rcases hx with ⟨i, hi⟩
      have hi_val_in_Fin0 : i.val ∈ (Fin 0 : Set) := i.property
      have : i.val ∉ (Fin 0 : Set) := by
        simpa [hFin0empty] using not_mem_empty i.val
      exact this hi_val_in_Fin0
    simpa [h_empty, empty_card_eq_zero] using Nat.zero_le (0 : ℕ)
  | succ k ih =>
    let last : Fin (k+1) := Fin_mk (k+1) k (by omega)
    let A' : Fin k → Set := λ i => A (Fin_embed k (k+1) (Nat.le_succ k) i)
    have h_cards' : ∀ i, (A' i).card ≤ 1 := λ i => h_cards _
    have h_union_eq : iUnion (Fin (k+1)) A = (iUnion (Fin k) A') ∪ (A last) := by
      ext x; constructor
      · intro hx; rw [mem_iUnion] at hx; rcases hx with ⟨i, hi⟩
        by_cases h_eq : i = last
        · rw [h_eq] at hi; rw [mem_union]; right; exact hi
        · have hi_val_lt_k : (i : ℕ) < k := by
            have hi_lt_succ : (i : ℕ) < k+1 := Fin.toNat_lt i
            have hi_ne_k : (i : ℕ) ≠ k := by
              intro h; apply h_eq
              apply (Fin.coe_inj (i := i) (j := last)).mpr
              calc
                (i : ℕ) = k := h
                _ = (last : ℕ) := by simp [last, Fin_mk]
            omega
          let j : Fin k := Fin_mk k (i : ℕ) hi_val_lt_k
          have h_embed_eq : Fin_embed k (k+1) (Nat.le_succ k) j = i := by
            apply Subtype.val_inj.mp
            simp [j, Fin.coe_toNat i]
          rw [mem_union]; left; rw [mem_iUnion]
          exact ⟨j, by simpa [A', h_embed_eq] using hi⟩
      · intro hx; rw [mem_union] at hx; rcases hx with (hx' | hx_last)
        · rw [mem_iUnion] at hx'; rcases hx' with ⟨j, hj⟩
          rw [mem_iUnion]
          exact ⟨Fin_embed k (k+1) (Nat.le_succ k) j, by simpa [A'] using hj⟩
        · rw [mem_iUnion]
          exact ⟨last, hx_last⟩
    by_cases h_finite : (iUnion (Fin (k+1)) A).finite
    · have h_subset_U' : iUnion (Fin k) A' ⊆ iUnion (Fin (k+1)) A := by
        rw [h_union_eq]; exact subset_union_left _ _
      have h_subset_Alast : A last ⊆ iUnion (Fin (k+1)) A := by
        rw [h_union_eq]; exact subset_union_right _ _
      have h_finite_U' : (iUnion (Fin k) A').finite :=
        (card_subset h_finite h_subset_U').1
      have h_finite_Alast : (A last).finite :=
        (card_subset h_finite h_subset_Alast).1
      have h_card_union : ((iUnion (Fin k) A') ∪ (A last)).card ≤
          (iUnion (Fin k) A').card + (A last).card :=
        (card_union h_finite_U' h_finite_Alast).2
      have h_main : ((iUnion (Fin k) A') ∪ (A last)).card ≤ k+1 := by
        calc
          ((iUnion (Fin k) A') ∪ (A last)).card ≤ (iUnion (Fin k) A').card + (A last).card := h_card_union
          _ ≤ k + 1 := by
            have h_ih_card : (iUnion (Fin k) A').card ≤ k := ih A' h_cards'
            have h_last_card : (A last).card ≤ 1 := h_cards last
            omega
      rw [h_union_eq]
      exact h_main
    · have h_card_infinite : (iUnion (Fin (k+1)) A).card = 0 := by
        rw [card, dif_neg h_finite]
      rw [h_card_infinite]
      omega

/-- Exercise 3.6.10 -/
theorem SetTheory.Set.pigeonhole_principle {n:ℕ} {A: Fin n → Set}
  (_hA: ∀ i, (A i).finite) (hAcard: (iUnion _ A).card > n) : ∃ i, (A i).card ≥ 2 := by
  by_contra! h
  have h_cards : ∀ i, (A i).card ≤ 1 := by
    intro i
    have hi := h i
    omega
  have h_bound : (iUnion (Fin n) A).card ≤ n := pigeonhole_aux A h_cards
  have : (iUnion _ A) = iUnion (Fin n) A := rfl
  rw [this] at hAcard
  omega

/-- Exercise 3.6.11 -/
theorem SetTheory.Set.two_to_two_iff {X Y:Set} (f: X → Y): Function.Injective f ↔
    ∀ S ⊆ X, S.card = 2 → (image f S).card = 2 := by
  constructor
  · intro hf S hS hcard
    have hS_has_card : S.has_card 2 := card_to_has_card (by omega) hcard
    have hS_finite : S.finite := ⟨2, hS_has_card⟩
    let f_S : S → Y := λ x => f ⟨x.val, hS x.val x.property⟩
    have hf_S_inj : Function.Injective f_S := by
      intro a b h
      dsimp [f_S] at h
      have h_pair_eq : (⟨a.val, hS a.val a.property⟩ : X) = (⟨b.val, hS b.val b.property⟩ : X) := hf h
      have h_val_eq : a.val = b.val := congrArg (fun (z : X) => z.val) h_pair_eq
      exact Subtype.val_inj.mp h_val_eq
    have hcard_image_S : (image f_S S).card = S.card := card_image_inj hS_finite hf_S_inj
    have h_image_eq : image f_S S = image f S := by
      ext y
      constructor
      · intro hy
        rw [mem_image] at hy
        rcases hy with ⟨x, hx, hx_eq⟩
        rw [mem_image]
        refine ⟨(⟨x.val, hS x.val x.property⟩ : X), And.intro x.property ?_⟩
        simpa [f_S] using hx_eq
      · intro hy
        rw [mem_image] at hy
        rcases hy with ⟨x, hx, hx_eq⟩
        rw [mem_image]
        refine ⟨(⟨x.val, hx⟩ : S), And.intro hx ?_⟩
        dsimp [f_S]
        have : f ⟨x.val, hS x.val hx⟩ = f x := (congrArg f (Subtype.ext rfl)).symm
        rw [this, hx_eq]
    rw [h_image_eq] at hcard_image_S
    rw [hcard_image_S, hcard]
  · intro h a b h_eq
    by_contra h_ne
    have ha_val_ne_b_val : a.val ≠ b.val := by
      intro h_val_eq; apply h_ne; apply Subtype.val_inj.mp h_val_eq
    let S : Set := {a.val, b.val}
    have hS_sub_X : S ⊆ X := by
      intro x hx
      rw [mem_pair] at hx
      rcases hx with (rfl | rfl)
      · exact a.property
      · exact b.property
    have h_singleton_finite : ({a.val} : Set).finite :=
      ⟨1, Example_3_6_7a a.val⟩
    have h_not_mem : b.val ∉ ({a.val} : Set) := by
      intro h; rw [mem_singleton] at h; apply ha_val_ne_b_val; exact h.symm
    have h_pair_eq : ({a.val} : Set) ∪ {b.val} = S := by
      ext x; simp [S, mem_union, mem_singleton]
    have h_singleton_card : ({a.val} : Set).card = 1 :=
      has_card_to_card (Example_3_6_7a a.val)
    have h_card_S : S.card = 2 := by
      have h_insert := card_insert h_singleton_finite h_not_mem
      calc
        S.card = (({a.val} : Set) ∪ {b.val}).card := by rw [h_pair_eq]
        _ = ({a.val} : Set).card + 1 := h_insert.2
        _ = 1 + 1 := by rw [h_singleton_card]
        _ = 2 := by omega
    have h_card_image : (image f S).card = 2 := h S hS_sub_X h_card_S
    have h_image_singleton : image f S = { (f a).val } := by
      ext y
      constructor
      · intro hy
        rw [mem_image] at hy
        rcases hy with ⟨x, hx, hx_eq⟩
        rw [mem_singleton]
        rw [mem_pair] at hx
        rcases hx with (hx | hx)
        · have hx_eq_x_a : x = a := Subtype.ext hx
          rw [hx_eq_x_a] at hx_eq
          simpa using hx_eq.symm
        · have hx_eq_x_b : x = b := Subtype.ext hx
          rw [hx_eq_x_b] at hx_eq
          rw [← hx_eq, h_eq.symm]
      · intro hy
        rw [mem_singleton] at hy
        subst hy
        rw [mem_image]
        refine ⟨a, ?_, rfl⟩
        rw [mem_pair]; left; rfl
    have h_card_image_singleton : ({ (f a).val } : Set).card = 1 :=
      has_card_to_card (Example_3_6_7a (f a).val)
    rw [h_image_singleton] at h_card_image
    rw [h_card_image_singleton] at h_card_image
    omega

/-- Exercise 3.6.12 -/
def SetTheory.Set.Permutations (n: ℕ): Set := (Fin n ^ Fin n).specify (fun F ↦
    Function.Bijective (pow_fun_equiv F))

/-- Exercise 3.6.12 (i), first part -/
theorem SetTheory.Set.Permutations_finite (n: ℕ): (Permutations n).finite := by
  have h_finite_pow : (Fin n ^ Fin n).finite := (card_pow (Fin_finite n) (Fin_finite n)).1
  have h_subset : Permutations n ⊆ (Fin n ^ Fin n) := specify_subset (fun F ↦ Function.Bijective (pow_fun_equiv F))
  exact (card_subset h_finite_pow h_subset).1

/- To continue Exercise 3.6.12 (i), we'll first develop some theory about `Permutations` and `Fin`. -/

noncomputable def SetTheory.Set.Permutations_toFun {n: ℕ} (p: Permutations n) : (Fin n) → (Fin n) := by
  have := p.property
  simp only [Permutations, specification_axiom'', powerset_axiom] at this
  exact this.choose.choose

theorem SetTheory.Set.Permutations_bijective {n: ℕ} (p: Permutations n) :
    Function.Bijective (Permutations_toFun p) := by
  have h_prop : p.val ∈ Permutations n := p.property
  unfold Permutations at h_prop
  rw [specification_axiom''] at h_prop
  rcases h_prop with ⟨h_mem, h_bij⟩
  have h_fun_eq : Permutations_toFun p = pow_fun_equiv (A := Fin n) (B := Fin n) (⟨p.val, h_mem⟩ : ↑(Fin n ^ Fin n)) := by
    apply (function_to_object (Fin n) (Fin n)).injective
    have h_f1 : function_to_object (Fin n) (Fin n) (Permutations_toFun p) = p.val := by
      have h_spec : p.val ∈ Permutations n := p.property
      simp only [Permutations, specification_axiom'', powerset_axiom] at h_spec
      have h_val : (Permutations_toFun p : Object) = p.val := by
        unfold Permutations_toFun
        simpa using h_spec.choose.choose_spec
      simpa using h_val
    have h_f2 : function_to_object (Fin n) (Fin n) (pow_fun_equiv (A := Fin n) (B := Fin n) (⟨p.val, h_mem⟩ : ↑(Fin n ^ Fin n))) = p.val := by
      have hx := (powerset_axiom (X := Fin n) (Y := Fin n) (F := p.val)).mp h_mem
      calc
        function_to_object (Fin n) (Fin n) (pow_fun_equiv (A := Fin n) (B := Fin n) (⟨p.val, h_mem⟩ : ↑(Fin n ^ Fin n)))
            = function_to_object (Fin n) (Fin n) (hx.choose) := rfl
        _ = (hx.choose : Object) := rfl
        _ = p.val := hx.choose_spec
    calc
      function_to_object (Fin n) (Fin n) (Permutations_toFun p) = p.val := h_f1
      _ = function_to_object (Fin n) (Fin n) (pow_fun_equiv (A := Fin n) (B := Fin n) (⟨p.val, h_mem⟩ : ↑(Fin n ^ Fin n))) := by
        symm; exact h_f2
  rw [h_fun_eq]
  exact h_bij

theorem SetTheory.Set.Permutations_inj {n: ℕ} (p1 p2: Permutations n) :
    Permutations_toFun p1 = Permutations_toFun p2 ↔ p1 = p2 := by
  constructor
  · intro h
    apply Subtype.val_inj.mp
    have h_inj : Function.Injective (function_to_object (Fin n) (Fin n)) :=
      (function_to_object (Fin n) (Fin n)).injective
    have h_f1 : function_to_object (Fin n) (Fin n) (Permutations_toFun p1) = p1.val := by
      have h_spec : p1.val ∈ Permutations n := p1.property
      simp only [Permutations, specification_axiom'', powerset_axiom] at h_spec
      have h_val : (Permutations_toFun p1 : Object) = p1.val := by
        unfold Permutations_toFun
        simpa using h_spec.choose.choose_spec
      simpa using h_val
    have h_f2 : function_to_object (Fin n) (Fin n) (Permutations_toFun p2) = p2.val := by
      have h_spec : p2.val ∈ Permutations n := p2.property
      simp only [Permutations, specification_axiom'', powerset_axiom] at h_spec
      have h_val : (Permutations_toFun p2 : Object) = p2.val := by
        unfold Permutations_toFun
        simpa using h_spec.choose.choose_spec
      simpa using h_val
    calc
      p1.val = function_to_object (Fin n) (Fin n) (Permutations_toFun p1) := by symm; exact h_f1
      _ = function_to_object (Fin n) (Fin n) (Permutations_toFun p2) := by rw [h]
      _ = p2.val := h_f2
  · intro h; rw [h]

/-- This connects our concept of a permutation with Mathlib's {name}`Equiv` between {lean}`Fin n` and {lean}`Fin n`. -/
noncomputable def SetTheory.Set.perm_equiv_equiv {n : ℕ} : Permutations n ≃ (Fin n ≃ Fin n) := {
  toFun := fun p => Equiv.ofBijective (Permutations_toFun p) (Permutations_bijective p)
  invFun := λ e =>
    let obj : Object := function_to_object (Fin n) (Fin n) e
    have h_mem : obj ∈ (Fin n ^ Fin n) :=
      (powerset_axiom (X := Fin n) (Y := Fin n) (F := obj)).mpr ⟨e, rfl⟩
    have h_bijective : Function.Bijective (pow_fun_equiv (A := Fin n) (B := Fin n) ⟨obj, h_mem⟩) := by
      have h_eq : pow_fun_equiv (A := Fin n) (B := Fin n) ⟨obj, h_mem⟩ = e := by
        apply (function_to_object (Fin n) (Fin n)).injective
        have hx := (powerset_axiom (X := Fin n) (Y := Fin n) (F := obj)).mp h_mem
        calc
          function_to_object (Fin n) (Fin n) (pow_fun_equiv (A := Fin n) (B := Fin n) ⟨obj, h_mem⟩)
              = function_to_object (Fin n) (Fin n) (hx.choose) := rfl
          _ = (hx.choose : Object) := rfl
          _ = obj := hx.choose_spec
          _ = function_to_object (Fin n) (Fin n) e := rfl
      simpa [h_eq] using e.bijective
    ⟨obj, by
      unfold Permutations
      rw [specification_axiom'']
      exact ⟨h_mem, h_bijective⟩⟩
  left_inv := by
    intro p
    apply Subtype.val_inj.mp
    have h_f : function_to_object (Fin n) (Fin n) (Permutations_toFun p) = p.val := by
      have h_spec : p.val ∈ Permutations n := p.property
      simp only [Permutations, specification_axiom'', powerset_axiom] at h_spec
      have h_val : (Permutations_toFun p : Object) = p.val := by
        unfold Permutations_toFun
        simpa using h_spec.choose.choose_spec
      simpa using h_val
    calc
      function_to_object (Fin n) (Fin n) (Equiv.ofBijective (Permutations_toFun p) (Permutations_bijective p))
          = function_to_object (Fin n) (Fin n) (Permutations_toFun p) := by
            simp [Equiv.ofBijective]
      _ = p.val := h_f
  right_inv := by
    intro e
    let obj : Object := function_to_object (Fin n) (Fin n) e
    have h_mem : obj ∈ (Fin n ^ Fin n) :=
      (powerset_axiom (X := Fin n) (Y := Fin n) (F := obj)).mpr ⟨e, rfl⟩
    have h_bijective : Function.Bijective (pow_fun_equiv (A := Fin n) (B := Fin n) ⟨obj, h_mem⟩) := by
      have h_eq : pow_fun_equiv (A := Fin n) (B := Fin n) ⟨obj, h_mem⟩ = e := by
        apply (function_to_object (Fin n) (Fin n)).injective
        have hx := (powerset_axiom (X := Fin n) (Y := Fin n) (F := obj)).mp h_mem
        calc
          function_to_object (Fin n) (Fin n) (pow_fun_equiv (A := Fin n) (B := Fin n) ⟨obj, h_mem⟩)
              = function_to_object (Fin n) (Fin n) (hx.choose) := rfl
          _ = (hx.choose : Object) := rfl
          _ = obj := hx.choose_spec
          _ = function_to_object (Fin n) (Fin n) e := rfl
      simpa [h_eq] using e.bijective
    let p : Permutations n := ⟨obj, by
      unfold Permutations
      rw [specification_axiom'']
      exact ⟨h_mem, h_bijective⟩⟩
    have h_p_toFun : Permutations_toFun p = e := by
      apply (function_to_object (Fin n) (Fin n)).injective
      have h_f : function_to_object (Fin n) (Fin n) (Permutations_toFun p) = p.val := by
        have h_spec : p.val ∈ Permutations n := p.property
        simp only [Permutations, specification_axiom'', powerset_axiom] at h_spec
        have h_val : (Permutations_toFun p : Object) = p.val := by
          unfold Permutations_toFun
          simpa using h_spec.choose.choose_spec
        simpa using h_val
      calc
        function_to_object (Fin n) (Fin n) (Permutations_toFun p) = p.val := h_f
        _ = obj := rfl
        _ = function_to_object (Fin n) (Fin n) e := rfl
    have h_equiv : Equiv.ofBijective (Permutations_toFun p) (Permutations_bijective p) = e := by
      apply Equiv.ext
      intro y
      calc
        Equiv.ofBijective (Permutations_toFun p) (Permutations_bijective p) y = Permutations_toFun p y := rfl
        _ = e y := by rw [h_p_toFun]
    simpa [h_p_toFun, h_equiv]
}

/- Exercise 3.6.12 involves a lot of moving between `Fin n` and `Fin (n + 1)` so let's add some conveniences. -/

/-- Any {lean}`Fin n` can be cast to {lean}`Fin (n + 1)`. Compare to Mathlib {name}`Fin.castSucc`. -/
def SetTheory.Set.Fin.castSucc {n} (x : Fin n) : Fin (n + 1) :=
  Fin_embed _ _ (by omega) x

@[simp]
lemma SetTheory.Set.Fin.castSucc_inj {n} {x y : Fin n} : castSucc x = castSucc y ↔ x = y := by
  constructor
  · intro h
    apply Subtype.val_inj.1
    have h_val : (castSucc x).val = (castSucc y).val := congrArg Subtype.val h
    simpa [castSucc, Fin_embed] using h_val
  · intro h; rw [h]

@[simp]
theorem SetTheory.Set.Fin.castSucc_ne {n} (x : Fin n) : castSucc x ≠ n := by
  intro h
  have hx_eq_n : (x : ℕ) = n := by
    simpa [castSucc, Fin_embed] using h
  have hx_lt_n : (x : ℕ) < n := Fin.toNat_lt x
  omega

/-- Any {lean}`Fin (n + 1)` except {lean}`n` can be cast to {lean}`Fin n`. Compare to Mathlib {name}`Fin.castPred`. -/
noncomputable def SetTheory.Set.Fin.castPred {n} (x : Fin (n + 1)) (h : (x : ℕ) ≠ n) : Fin n :=
  Fin_mk _ (x : ℕ) (by have := Fin.toNat_lt x; omega)

@[simp]
theorem SetTheory.Set.Fin.castSucc_castPred {n} (x : Fin (n + 1)) (h : (x : ℕ) ≠ n) :
    castSucc (castPred x h) = x := by
  apply Subtype.val_inj.mp
  simp [castSucc, castPred, Fin_embed, Fin_mk]

@[simp]
theorem SetTheory.Set.Fin.castPred_castSucc {n} (x : Fin n) (h : ((castSucc x : Fin (n + 1)) : ℕ) ≠ n) :
    castPred (castSucc x) h = x := by
  apply Subtype.val_inj.mp
  simp [castSucc, castPred, Fin_embed, Fin_mk]

/-- Any natural {lean}`n` can be cast to {lean}`Fin (n + 1)`. Compare to Mathlib {name}`Fin.last`. -/
def SetTheory.Set.Fin.last (n : ℕ) : Fin (n + 1) := Fin_mk _ n (by omega)

/-- Now is a good time to prove this result, which will be useful for completing Exercise 3.6.12 (i). -/
theorem SetTheory.Set.card_iUnion_card_disjoint {n m: ℕ} {S : Fin n → Set}
    (hSc : ∀ i, (S i).has_card m)
    (hSd : Pairwise fun i j => Disjoint (S i) (S j)) :
    ((Fin n).iUnion S).finite ∧ ((Fin n).iUnion S).card = n * m := by
  induction n with
  | zero =>
    have hFin0empty : (Fin 0 : Set) = ∅ := by
      ext x; simp
    have h_empty : iUnion (Fin 0) S = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      rw [mem_iUnion] at hx
      rcases hx with ⟨i, hi⟩
      have hi_val_in_Fin0 : i.val ∈ (Fin 0 : Set) := i.property
      have : i.val ∉ (Fin 0 : Set) := by
        simpa [hFin0empty] using not_mem_empty i.val
      exact this hi_val_in_Fin0
    have h_finite : (iUnion (Fin 0) S).finite := by
      rw [h_empty]; exact empty_finite
    have h_card : (iUnion (Fin 0) S).card = 0 * m := by
      rw [h_empty, empty_card_eq_zero, zero_mul]
    exact ⟨h_finite, h_card⟩
  | succ k ih =>
    let last : Fin (k+1) := Fin_mk (k+1) k (by omega)
    let S' : Fin k → Set := λ i => S (Fin_embed k (k+1) (Nat.le_succ k) i)
    have hSc' : ∀ i, (S' i).has_card m := λ i => hSc (Fin_embed k (k+1) (Nat.le_succ k) i)
    have h_disjoint' : Pairwise fun i j => Disjoint (S' i) (S' j) := by
      intro i j h_ne
      apply hSd
      intro h_eq
      apply h_ne
      apply Subtype.val_inj.mp
      simpa using congrArg Subtype.val h_eq
    have h_ih : ((Fin k).iUnion S').finite ∧ ((Fin k).iUnion S').card = k * m :=
      ih hSc' h_disjoint'
    rcases h_ih with ⟨h_finite_U', h_card_U'⟩
    have h_union_eq : iUnion (Fin (k+1)) S = (iUnion (Fin k) S') ∪ (S last) := by
      ext x; constructor
      · intro hx; rw [mem_iUnion] at hx; rcases hx with ⟨i, hi⟩
        by_cases h_eq : i = last
        · rw [h_eq] at hi; rw [mem_union]; right; exact hi
        · have hi_val_lt_k : (i : ℕ) < k := by
            have hi_lt_succ : (i : ℕ) < k+1 := Fin.toNat_lt i
            have hi_ne_k : (i : ℕ) ≠ k := by
              intro h; apply h_eq
              apply (Fin.coe_inj (i := i) (j := last)).mpr
              calc
                (i : ℕ) = k := h
                _ = (last : ℕ) := by simp [last, Fin_mk]
            omega
          let j : Fin k := Fin_mk k (i : ℕ) hi_val_lt_k
          have h_embed_eq : Fin_embed k (k+1) (Nat.le_succ k) j = i := by
            apply Subtype.val_inj.mp
            simp [j, Fin.coe_toNat i]
          rw [mem_union]; left; rw [mem_iUnion]
          exact ⟨j, by simpa [S', h_embed_eq] using hi⟩
      · intro hx; rw [mem_union] at hx; rcases hx with (hx' | hx_last)
        · rw [mem_iUnion] at hx'; rcases hx' with ⟨j, hj⟩
          rw [mem_iUnion]
          exact ⟨Fin_embed k (k+1) (Nat.le_succ k) j, by simpa [S'] using hj⟩
        · rw [mem_iUnion]; exact ⟨last, hx_last⟩
    have h_disjoint_union : Disjoint (iUnion (Fin k) S') (S last) := by
      rw [disjoint_iff]
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      rw [mem_inter, mem_iUnion] at hx
      rcases hx with ⟨⟨j, hj⟩, hx_last⟩
      have h_disjoint_Sj_Slast : Disjoint (S' j) (S last) := by
        apply hSd
        intro h_eq
        have h_val_eq : (Fin_embed k (k+1) (Nat.le_succ k) j : ℕ) = (last : ℕ) :=
          congrArg (λ z : Fin (k+1) => (z : ℕ)) h_eq
        have h_embed_val : (Fin_embed k (k+1) (Nat.le_succ k) j : ℕ) = (j : ℕ) := by
          have hx_lt_k : (j : ℕ) < k := Fin.toNat_lt j
          have h_embed_eq : Fin_embed k (k+1) (Nat.le_succ k) j = Fin_mk (k+1) (j : ℕ) (by omega) := by
            apply Subtype.val_inj.mp
            simp [Fin.coe_toNat j]
          rw [h_embed_eq, Fin.toNat_mk]
        have h_last_val : (last : ℕ) = k := by simp [last, Fin_mk]
        rw [h_embed_val, h_last_val] at h_val_eq
        have h_lt : (j : ℕ) < k := Fin.toNat_lt j
        omega
      rw [disjoint_iff] at h_disjoint_Sj_Slast
      have hx_inter : x ∈ (S' j) ∩ (S last) := by
        rw [mem_inter]; exact ⟨hj, hx_last⟩
      rw [h_disjoint_Sj_Slast] at hx_inter
      exact not_mem_empty x hx_inter
    have h_finite_Slast : (S last).finite := ⟨m, hSc last⟩
    have h_card_union : (iUnion (Fin (k+1)) S).card = (iUnion (Fin k) S').card + (S last).card := by
      rw [h_union_eq]
      exact card_union_disjoint h_finite_U' h_finite_Slast h_disjoint_union
    have h_card_Slast : (S last).card = m := has_card_to_card (hSc last)
    have h_finite_union : (iUnion (Fin (k+1)) S).finite := by
      rw [h_union_eq]
      exact (card_union h_finite_U' h_finite_Slast).1
    rw [h_card_U', h_card_Slast] at h_card_union
    have : (k * m) + m = (k+1) * m := by
      simpa [add_comm] using (Nat.succ_mul k m).symm
    rw [this] at h_card_union
    exact ⟨h_finite_union, h_card_union⟩

/- Finally, we'll set up a way to shrink `Fin (n + 1)` into `Fin n` (or expand the latter) by making a hole. -/

/--
  If some {lean}`x : Fin (n+1)` is never equal to {name}`i`, we can shrink it into {lean}`Fin n` by shifting all {lean}`(x : ℕ) > i` down by one.
  Compare to Mathlib {name}`Fin.predAbove`.
-/
noncomputable def SetTheory.Set.Fin.predAbove {n} (i : Fin (n + 1)) (x : Fin (n + 1)) (h : x ≠ i) : Fin n :=
  if hx : (x:ℕ) < i then
    Fin_mk _ (x:ℕ) (by
      have hi_lt_n1 : (i : ℕ) < n + 1 := Fin.toNat_lt i
      omega)
  else
    Fin_mk _ ((x:ℕ) - 1) (by
      have hx_lt_n1 : (x : ℕ) < n + 1 := Fin.toNat_lt x
      have hi_lt_n1 : (i : ℕ) < n + 1 := Fin.toNat_lt i
      have hx_ne_i_val : (x : ℕ) ≠ (i : ℕ) := by
        intro h_eq; apply h; apply (Fin.coe_inj (i := x) (j := i)).mpr h_eq
      have hx_ge_i : (i : ℕ) ≤ (x : ℕ) := by omega
      have hx_gt_i : (i : ℕ) < (x : ℕ) := Nat.lt_of_le_of_ne hx_ge_i hx_ne_i_val.symm
      omega)

/--
  We can expand {lean}`x : Fin n` into {lean}`Fin (n + 1)` by shifting all {lean}`(x : ℕ) ≥ i` up by one.
  The output is never {name}`i`, so it forms an inverse to the shrinking done by {name}`predAbove`.
  Compare to Mathlib {name}`Fin.succAbove`.
-/
noncomputable def SetTheory.Set.Fin.succAbove {n} (i : Fin (n + 1)) (x : Fin n) : Fin (n + 1) :=
  if (x:ℕ) < i then
    Fin_embed _ _ (Nat.le_succ n) x
  else
    Fin_mk _ ((x:ℕ) + 1) (by
      have hx_lt_n : (x : ℕ) < n := Fin.toNat_lt x
      omega)

@[simp]
theorem SetTheory.Set.Fin.succAbove_ne {n} (i : Fin (n + 1)) (x : Fin n) : succAbove i x ≠ i := by
  intro h
  have h_val : (succAbove i x : ℕ) = (i : ℕ) := (Fin.coe_inj (i := succAbove i x) (j := i)).1 h
  dsimp [succAbove] at h_val
  split_ifs at h_val with hx_lt_i
  · have h_embed_val : (Fin_embed n (n+1) (Nat.le_succ n) x : ℕ) = (x : ℕ) := by
      simp
    rw [h_embed_val] at h_val
    omega
  · have hx_lt_n : (x : ℕ) < n := Fin.toNat_lt x
    have hx_succ_lt_n1 : (x : ℕ) + 1 < n + 1 := by omega
    have : (Fin_mk (n+1) ((x:ℕ)+1) hx_succ_lt_n1 : ℕ) = (x : ℕ) + 1 := by simp
    rw [this] at h_val
    have hx_ge_i : (i : ℕ) ≤ (x : ℕ) := by omega
    omega

@[simp]
theorem SetTheory.Set.Fin.succAbove_predAbove {n} (i : Fin (n + 1)) (x : Fin (n + 1)) (h : x ≠ i) :
    (succAbove i) (predAbove i x h) = x := by
  apply Subtype.val_inj.mp
  dsimp [succAbove, predAbove]
  by_cases hx_lt_i : (x : ℕ) < i
  · simp [hx_lt_i]
  · have hx_ne_i_val : (x : ℕ) ≠ (i : ℕ) := by
      intro h_eq; apply h; apply (Fin.coe_inj (i := x) (j := i)).mpr h_eq
    have hx_gt_i : (i : ℕ) < (x : ℕ) := by
      have hx_ge_i : (i : ℕ) ≤ (x : ℕ) := by omega
      exact Nat.lt_of_le_of_ne hx_ge_i hx_ne_i_val.symm
    have h_sub_not_lt_i : ¬ ((x : ℕ) - 1 < i) := by
      omega
    simp [hx_lt_i, h_sub_not_lt_i]
    have hx_pos : 1 ≤ (x : ℕ) := by omega
    have h_sub : ((x : ℕ) - 1) + 1 = (x : ℕ) := by omega
    simp [h_sub]

@[simp]
theorem SetTheory.Set.Fin.predAbove_succAbove {n} (i : Fin (n + 1)) (x : Fin n) :
    (predAbove i) (succAbove i x) (succAbove_ne i x) = x := by
  apply Subtype.val_inj.mp
  dsimp [succAbove, predAbove]
  by_cases hx_lt_i : (x : ℕ) < i
  · simp [hx_lt_i]
  · have hx_ge_i : (i : ℕ) ≤ (x : ℕ) := by omega
    have h_succ_not_lt_i : ¬ ((x : ℕ) + 1 < i) := by omega
    simp [hx_lt_i, h_succ_not_lt_i]

/-- Exercise 3.6.12 (i), second part -/
theorem SetTheory.Set.Permutations_ih (n: ℕ):
    (Permutations (n + 1)).card = (n + 1) * (Permutations n).card := by
  let S i := (Permutations (n + 1)).specify (fun p ↦ perm_equiv_equiv p (Fin.last n) = i)

  have hSe : ∀ i, S i ≈ Permutations n := by
    intro i
    -- Equiv: {e | e(Fin.last n) = i} ≃ (Fin n ≃ Fin n)
    let φ : {e : (Fin (n+1) ≃ Fin (n+1)) // e (Fin.last n) = i} → (Fin n ≃ Fin n) := λ ⟨e, he⟩ => {
      toFun := λ x => Fin.predAbove i (e (Fin.succAbove (Fin.last n) x))
        (by
          have hx_ne : Fin.succAbove (Fin.last n) x ≠ Fin.last n := Fin.succAbove_ne (Fin.last n) x
          have hx_ne_e : e (Fin.succAbove (Fin.last n) x) ≠ e (Fin.last n) := e.injective.ne hx_ne
          rw [he] at hx_ne_e
          exact hx_ne_e)
      invFun := λ y => Fin.predAbove (Fin.last n) (e.symm (Fin.succAbove i y))
        (by
          have hy_ne : Fin.succAbove i y ≠ i := Fin.succAbove_ne i y
          have hy_ne_e : e.symm (Fin.succAbove i y) ≠ e.symm i := e.symm.injective.ne hy_ne
          have h_symm : e.symm i = Fin.last n := by
            calc
              e.symm i = e.symm (e (Fin.last n)) := by rw [he]
              _ = Fin.last n := by simp
          rw [h_symm] at hy_ne_e
          exact hy_ne_e)
      left_inv := λ x => by
        simp
      right_inv := λ y => by
        simp
    }
    -- Define h_equiv_T using Equiv.ofBijective (which needs injectivity and surjectivity of φ)
    have h_φ_inj : Function.Injective φ := by
      intro x y h
      rcases x with ⟨e_x, he_x⟩
      rcases y with ⟨e_y, he_y⟩
      apply Subtype.ext
      ext z
      by_cases hz : z = Fin.last n
      · subst hz; simp [he_x, he_y]
      · set x := Fin.predAbove (Fin.last n) z (by intro h_eq; apply hz; exact h_eq) with hx_def
        have h_succ : Fin.succAbove (Fin.last n) x = z := by
          dsimp [x]; simp
        have hx_ne_i : e_x (Fin.succAbove (Fin.last n) x) ≠ i := by
          intro h_eq
          apply Fin.succAbove_ne (Fin.last n) x
          apply e_x.injective
          calc
            e_x (Fin.succAbove (Fin.last n) x) = i := h_eq
            _ = e_x (Fin.last n) := by symm; exact he_x
        have hy_ne_i : e_y (Fin.succAbove (Fin.last n) x) ≠ i := by
          intro h_eq
          apply Fin.succAbove_ne (Fin.last n) x
          apply e_y.injective
          calc
            e_y (Fin.succAbove (Fin.last n) x) = i := h_eq
            _ = e_y (Fin.last n) := by symm; exact he_y
        have h_eq_pa : Fin.predAbove i (e_x (Fin.succAbove (Fin.last n) x)) hx_ne_i =
          Fin.predAbove i (e_y (Fin.succAbove (Fin.last n) x)) hy_ne_i := by
          calc
            Fin.predAbove i (e_x (Fin.succAbove (Fin.last n) x)) hx_ne_i
                = (φ ⟨e_x, he_x⟩) x := by simp [φ]
            _ = (φ ⟨e_y, he_y⟩) x := by rw [h]
            _ = Fin.predAbove i (e_y (Fin.succAbove (Fin.last n) x)) hy_ne_i := by simp [φ]
        have h_eq_e : (e_x (Fin.succAbove (Fin.last n) x)).val = (e_y (Fin.succAbove (Fin.last n) x)).val := by
          calc
            (e_x (Fin.succAbove (Fin.last n) x)).val
                = (Fin.succAbove i (Fin.predAbove i (e_x (Fin.succAbove (Fin.last n) x)) hx_ne_i)).val := by simp
            _ = (Fin.succAbove i (Fin.predAbove i (e_y (Fin.succAbove (Fin.last n) x)) hy_ne_i)).val := by rw [h_eq_pa]
            _ = (e_y (Fin.succAbove (Fin.last n) x)).val := by simp
        calc
          (e_x z).val = (e_x (Fin.succAbove (Fin.last n) x)).val := by rw [h_succ]
          _ = (e_y (Fin.succAbove (Fin.last n) x)).val := h_eq_e
          _ = (e_y z).val := by rw [h_succ]
    have h_φ_surj : Function.Surjective φ := by
      intro e'
      classical
        let e : Fin (n+1) ≃ Fin (n+1) := {
          toFun := λ y => if h : y = Fin.last n then i else Fin.succAbove i (e' (Fin.predAbove (Fin.last n) y (by
            intro h_eq; apply h; exact h_eq)))
          invFun := λ z => if h : z = i then Fin.last n else Fin.succAbove (Fin.last n) (e'.symm (Fin.predAbove i z (by
            intro h_eq; apply h; exact h_eq)))
          left_inv := by
            intro y
            by_cases hy : y = Fin.last n
            · subst hy; simp
            · simp [hy]
          right_inv := by
            intro z
            by_cases hz : z = i
            · subst hz; simp
            · simp [hz]
        }
        have he : e (Fin.last n) = i := by simp [e]
        refine ⟨⟨e, he⟩, ?_⟩
        ext x
        have h_ne_val : (Fin.succAbove (Fin.last n) x : Object) ≠ (Fin.last n : Object) := by
          intro h_eq
          apply Fin.succAbove_ne (Fin.last n) x
          exact Subtype.val_inj.mp h_eq
        dsimp [φ, e]
        simp [Fin.predAbove_succAbove (Fin.last n) x]
    have h_equiv_T : {e : (Fin (n+1) ≃ Fin (n+1)) // e (Fin.last n) = i} ≃ (Fin n ≃ Fin n) :=
      Equiv.ofBijective φ ⟨h_φ_inj, h_φ_surj⟩
    -- Compose: S i → Permutations n
    refine ⟨λ s => ?_, ?_, ?_⟩
    · -- toFun: S i → Permutations n
      have h_s_mem : s.val ∈ Permutations (n+1) := by
        have h_spec : s.val ∈ (Permutations (n+1)).specify (fun p ↦ perm_equiv_equiv p (Fin.last n) = i) := s.property
        rcases (specification_axiom'' (fun p : Permutations (n+1) ↦ perm_equiv_equiv p (Fin.last n) = i) s.val).mp h_spec with ⟨h_mem, _⟩
        exact h_mem
      let e := perm_equiv_equiv (n := n+1) ⟨s.val, h_s_mem⟩
      have he : e (Fin.last n) = i := by
        have h_spec : s.val ∈ (Permutations (n+1)).specify (fun p ↦ perm_equiv_equiv p (Fin.last n) = i) := s.property
        rcases (specification_axiom'' (fun p : Permutations (n+1) ↦ perm_equiv_equiv p (Fin.last n) = i) s.val).mp h_spec with ⟨_, h_prop⟩
        exact h_prop
      exact (perm_equiv_equiv (n := n)).symm (h_equiv_T ⟨e, he⟩)
    · -- injectivity
      intro a b h
      apply Subtype.val_inj.mp
      have h_a_mem : a.val ∈ Permutations (n+1) := by
        have h_spec : a.val ∈ (Permutations (n+1)).specify (fun p ↦ perm_equiv_equiv p (Fin.last n) = i) := a.property
        rcases (specification_axiom'' (fun p : Permutations (n+1) ↦ perm_equiv_equiv p (Fin.last n) = i) a.val).mp h_spec with ⟨h_mem, _⟩
        exact h_mem
      have h_b_mem : b.val ∈ Permutations (n+1) := by
        have h_spec : b.val ∈ (Permutations (n+1)).specify (fun p ↦ perm_equiv_equiv p (Fin.last n) = i) := b.property
        rcases (specification_axiom'' (fun p : Permutations (n+1) ↦ perm_equiv_equiv p (Fin.last n) = i) b.val).mp h_spec with ⟨h_mem, _⟩
        exact h_mem
      have ha_eq : (perm_equiv_equiv (n := n+1) ⟨a.val, h_a_mem⟩) (Fin.last n) = i := by
        have h_spec : a.val ∈ (Permutations (n+1)).specify (fun p ↦ perm_equiv_equiv p (Fin.last n) = i) := a.property
        rcases (specification_axiom'' (fun p : Permutations (n+1) ↦ perm_equiv_equiv p (Fin.last n) = i) a.val).mp h_spec with ⟨_, h_prop⟩
        exact h_prop
      have hb_eq : (perm_equiv_equiv (n := n+1) ⟨b.val, h_b_mem⟩) (Fin.last n) = i := by
        have h_spec : b.val ∈ (Permutations (n+1)).specify (fun p ↦ perm_equiv_equiv p (Fin.last n) = i) := b.property
        rcases (specification_axiom'' (fun p : Permutations (n+1) ↦ perm_equiv_equiv p (Fin.last n) = i) b.val).mp h_spec with ⟨_, h_prop⟩
        exact h_prop
      let a' : (Permutations (n+1)).toSubtype := ⟨a.val, h_a_mem⟩
      let b' : (Permutations (n+1)).toSubtype := ⟨b.val, h_b_mem⟩
      apply (Subtype.val_inj (a := a') (b := b')).mpr
      apply (perm_equiv_equiv (n := n+1)).injective
      have h_eq_embed : (⟨perm_equiv_equiv (n := n+1) ⟨a.val, h_a_mem⟩, ha_eq⟩ : {e : (Fin (n+1) ≃ Fin (n+1)) // e (Fin.last n) = i}) = ⟨perm_equiv_equiv (n := n+1) ⟨b.val, h_b_mem⟩, hb_eq⟩ := by
        apply h_equiv_T.injective
        calc
          h_equiv_T ⟨perm_equiv_equiv (n := n+1) ⟨a.val, h_a_mem⟩, ha_eq⟩
              = (perm_equiv_equiv (n := n)) ((perm_equiv_equiv (n := n)).symm (h_equiv_T ⟨perm_equiv_equiv (n := n+1) ⟨a.val, h_a_mem⟩, ha_eq⟩)) := by simp
          _ = (perm_equiv_equiv (n := n)) ((perm_equiv_equiv (n := n)).symm (h_equiv_T ⟨perm_equiv_equiv (n := n+1) ⟨b.val, h_b_mem⟩, hb_eq⟩)) := by
            have := congrArg (perm_equiv_equiv (n := n)) h
            simpa using this
          _ = h_equiv_T ⟨perm_equiv_equiv (n := n+1) ⟨b.val, h_b_mem⟩, hb_eq⟩ := by simp
      exact congrArg Subtype.val h_eq_embed
    · -- surjectivity
      intro q
      let e' := perm_equiv_equiv q
      let inv := h_equiv_T.invFun e'
      have h_T_inv : h_equiv_T inv = e' := h_equiv_T.right_inv e'
      let e := inv.1
      have he : e (Fin.last n) = i := inv.2
      let p_val : Permutations (n+1) := (perm_equiv_equiv (n := n+1)).symm e
      have hp_val : p_val.val ∈ S i := by
        have h_mem : p_val.val ∈ Permutations (n+1) := p_val.property
        refine (specification_axiom'' (fun p : Permutations (n+1) ↦ perm_equiv_equiv p (Fin.last n) = i) p_val.val).mpr ⟨h_mem, ?_⟩
        calc
          perm_equiv_equiv p_val (Fin.last n) = e (Fin.last n) := by simp [p_val]
          _ = i := he
      refine ⟨⟨p_val.val, hp_val⟩, ?_⟩
      calc
        (perm_equiv_equiv (n := n)).symm (h_equiv_T ⟨perm_equiv_equiv (n := n+1) ⟨p_val.val, p_val.property⟩, by
          calc
            (perm_equiv_equiv (n := n+1) ⟨p_val.val, p_val.property⟩) (Fin.last n) = e (Fin.last n) := by simp [p_val]
            _ = i := he⟩)
            = (perm_equiv_equiv (n := n)).symm (h_equiv_T inv) := by simp [p_val, inv, e]
        _ = (perm_equiv_equiv (n := n)).symm e' := by rw [h_T_inv]
        _ = q := by rw [show e' = perm_equiv_equiv q from rfl, Equiv.symm_apply_apply (perm_equiv_equiv (n := n)) q]

  have h_disjoint : Pairwise fun i j => Disjoint (S i) (S j) := by
    intro i j h_ne
    rw [disjoint_iff]
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hx_and : x ∈ S i ∧ x ∈ S j := by simpa [mem_inter] using hx
    have hx_i : x ∈ S i := hx_and.1
    have hx_j : x ∈ S j := hx_and.2
    have hspec_i := (specification_axiom'' (fun p : Permutations (n+1) ↦ perm_equiv_equiv p (Fin.last n) = i) x).mp hx_i
    have hspec_j := (specification_axiom'' (fun p : Permutations (n+1) ↦ perm_equiv_equiv p (Fin.last n) = j) x).mp hx_j
    rcases hspec_i with ⟨hmem_i, hprop_i⟩
    rcases hspec_j with ⟨hmem_j, hprop_j⟩
    apply h_ne
    apply (Subtype.val_inj (a := i) (b := j)).mp
    calc
      (i : Object) = ((perm_equiv_equiv (⟨x, hmem_i⟩ : Permutations (n+1))) (Fin.last n) : Object) := by
        simpa using congrArg Subtype.val hprop_i.symm
      _ = (j : Object) := by
        simpa using congrArg Subtype.val hprop_j

  have h_finite_Pn : (Permutations n).finite := Permutations_finite n
  have h_has_card_Pn : (Permutations n).has_card ((Permutations n).card) := has_card_card h_finite_Pn

  have hSc : ∀ i, (S i).has_card (Permutations n).card := by
    intro i
    rcases hSe i with ⟨f, hf⟩
    exact (EquivCard_to_has_card_eq ⟨f, hf⟩).mpr h_has_card_Pn

  have h_union : (Fin (n+1)).iUnion S = Permutations (n+1) := by
    ext p
    constructor
    · intro hp
      rw [mem_iUnion] at hp
      rcases hp with ⟨i, hi⟩
      rcases (specification_axiom'' (fun p' : Permutations (n+1) ↦ perm_equiv_equiv p' (Fin.last n) = i) p).mp hi with ⟨hmem, _⟩
      exact hmem
    · intro hp
      rw [mem_iUnion]
      have h_mem : p ∈ Permutations (n+1) := hp
      let i := perm_equiv_equiv ⟨p, h_mem⟩ (Fin.last n)
      use i
      refine (specification_axiom'' (fun p' : Permutations (n+1) ↦ perm_equiv_equiv p' (Fin.last n) = i) p).mpr ⟨h_mem, ?_⟩
      rfl

  have h_card_iUnion := card_iUnion_card_disjoint hSc h_disjoint
  rcases h_card_iUnion with ⟨h_finite, h_card_eq⟩
  rw [h_union] at h_card_eq
  exact h_card_eq

/-- Exercise 3.6.12 (ii) -/
theorem SetTheory.Set.Permutations_card (n: ℕ):
    (Permutations n).card = n.factorial := by
  induction n with
  | zero =>
    have h_nonempty : Permutations 0 ≠ ∅ := by
      have h_equiv : Permutations 0 ≃ (Fin 0 ≃ Fin 0) := perm_equiv_equiv (n := 0)
      have : Nonempty (Fin 0 ≃ Fin 0) := ⟨Equiv.refl _⟩
      have h_ne : Nonempty (Permutations 0) :=
        Nonempty.map (h_equiv.symm : (Fin 0 ≃ Fin 0) → Permutations 0) this
      intro h_eq
      rw [h_eq] at h_ne
      rcases h_ne with ⟨x⟩
      exact not_mem_empty x.val x.property
    have h_card_le_1 : (Permutations 0).card ≤ 1 := by
      have h_subset : Permutations 0 ⊆ (Fin 0 ^ Fin 0) := specify_subset (fun F ↦ Function.Bijective (pow_fun_equiv F))
      have h_card_pow : (Fin 0 ^ Fin 0).card = 1 := by
        have h := (card_pow (Fin_finite 0) (Fin_finite 0)).2
        calc
          (Fin 0 ^ Fin 0).card = (Fin 0).card ^ (Fin 0).card := h
          _ = 0 ^ 0 := by simp [Fin_card]
          _ = 1 := by norm_num
      have h_finite_pow : (Fin 0 ^ Fin 0).finite := (card_pow (Fin_finite 0) (Fin_finite 0)).1
      have h_card_subset : (Permutations 0).card ≤ (Fin 0 ^ Fin 0).card := (card_subset h_finite_pow h_subset).2
      rw [h_card_pow] at h_card_subset
      exact h_card_subset
    have h_card_ge_1 : 1 ≤ (Permutations 0).card := by
      by_contra! h
      have h_card0 : (Permutations 0).card = 0 := by omega
      have h_empty : Permutations 0 = ∅ :=
        (empty_iff_card_eq_zero (X := Permutations 0)).mpr ⟨Permutations_finite 0, h_card0⟩
      exact h_nonempty h_empty
    have h_eq1 : (Permutations 0).card = 1 := Nat.le_antisymm h_card_le_1 h_card_ge_1
    calc
      (Permutations 0).card = 1 := h_eq1
      _ = Nat.factorial 0 := by norm_num
  | succ k ih =>
    calc
      (Permutations (k+1)).card = (k+1) * (Permutations k).card := Permutations_ih k
      _ = (k+1) * k.factorial := by rw [ih]
      _ = (k+1).factorial := by rw [Nat.factorial_succ]



end Chapter3
