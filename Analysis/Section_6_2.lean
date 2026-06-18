import Mathlib.Tactic
import Analysis.Section_5_5
import Analysis.Section_5_epilogue

/-!
# Analysis I, Section 6.2: The extended real number system

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Some API for Mathlib's extended reals {name}`EReal`, particularly with regard to the supremum
  operation {name}`sSup` and infimum operation {name}`sInf`.

-/

open EReal

/-- Definition 6.2.1 -/
theorem EReal.def (x:EReal) : (∃ (y:Real), y = x) ∨ x = ⊤ ∨ x = ⊥ := by
  revert x
  simp [EReal.forall]

theorem EReal.real_neq_infty (x:ℝ) : (x:EReal) ≠ ⊤ := coe_ne_top _

theorem EReal.real_neq_neg_infty (x:ℝ) : (x:EReal) ≠ ⊥ := coe_ne_bot _

theorem EReal.infty_neq_neg_infty : (⊤:EReal) ≠ (⊥:EReal) := add_top_iff_ne_bot.mp rfl

abbrev EReal.IsFinite (x:EReal) : Prop := ∃ (y:Real), y = x

abbrev EReal.IsInfinite (x:EReal) : Prop := x = ⊤ ∨ x = ⊥

theorem EReal.infinite_iff_not_finite (x:EReal): x.IsInfinite ↔ ¬ x.IsFinite := by
  obtain ⟨ y, rfl ⟩ | rfl | rfl := EReal.def x <;> simp [IsFinite, IsInfinite]

/-- Definition 6.2.2 (Negation of extended reals) -/
theorem EReal.neg_of_real (x:Real) : -(x:EReal) = (-x:ℝ) := rfl

#check EReal.neg_top
#check EReal.neg_bot

/-- Definition 6.2.3 (Ordering of extended reals) -/
theorem EReal.le_iff (x y:EReal) :
    x ≤ y ↔ (∃ (x' y':Real), x = x' ∧ y = y' ∧ x' ≤ y') ∨ y = ⊤ ∨ x = ⊥ := by
  obtain ⟨ x', rfl ⟩ | rfl | rfl := EReal.def x <;> obtain ⟨ y', rfl ⟩ | rfl | rfl := EReal.def y <;> simp <;> tauto

/-- Definition 6.2.3 (Ordering of extended reals) -/
theorem EReal.lt_iff (x y:EReal) : x < y ↔ x ≤ y ∧ x ≠ y := lt_iff_le_and_ne

#check EReal.coe_lt_coe_iff

/-- Examples 6.2.4 -/
example : (3:EReal) ≤ (5:EReal) := by rw [le_iff]; left; use (3:ℝ), (5:ℝ); norm_cast


/-- Examples 6.2.4 -/
example : (3:EReal) < ⊤ := by rw [lt_iff]; exact ⟨le_top, real_neq_infty 3⟩


/-- Examples 6.2.4 -/
example : (⊥:EReal) < ⊤ := bot_lt_top


/-- Examples 6.2.4 -/
example : ¬ (3:EReal) ≤ ⊥ := by
  by_contra h
  simp at h
  exact real_neq_neg_infty 3 h

#check instCompleteLinearOrderEReal

/-- Proposition 6.2.5(a) / Exercise 6.2.1 -/
theorem EReal.refl (x:EReal) : x ≤ x := le_refl x

/-- Proposition 6.2.5(b) / Exercise 6.2.1 -/
theorem EReal.trichotomy (x y:EReal) : x < y ∨ x = y ∨ x > y := lt_trichotomy x y

/-- Proposition 6.2.5(b) / Exercise 6.2.1 -/
theorem EReal.not_lt_and_eq (x y:EReal) : ¬ (x < y ∧ x = y) := fun ⟨h1, h2⟩ => lt_irrefl x (h2 ▸ h1)

/-- Proposition 6.2.5(b) / Exercise 6.2.1 -/
theorem EReal.not_gt_and_eq (x y:EReal) : ¬ (x > y ∧ x = y) := fun ⟨h1, h2⟩ => lt_irrefl x (h2 ▸ h1)

/-- Proposition 6.2.5(b) / Exercise 6.2.1 -/
theorem EReal.not_lt_and_gt (x y:EReal) : ¬ (x < y ∧ x > y) := fun ⟨h1, h2⟩ => lt_asymm h1 h2

/-- Proposition 6.2.5(c) / Exercise 6.2.1 -/
theorem EReal.trans {x y z:EReal} (hxy : x ≤ y) (hyz: y ≤ z) : x ≤ z := le_trans hxy hyz

/-- Proposition 6.2.5(d) / Exercise 6.2.1 -/
theorem EReal.neg_of_lt {x y:EReal} (hxy : x ≤ y): -y ≤ -x := neg_le_neg_iff.mpr hxy

/-- Definition 6.2.6 -/
theorem EReal.sup_of_bounded_nonempty {E: Set ℝ} (hbound: BddAbove E) (hnon: E.Nonempty) :
    sSup ((fun (x:ℝ) ↦ (x:EReal)) '' E) = sSup E := calc
  _ = sSup
      ((fun (x:WithTop ℝ) ↦ (x:WithBot (WithTop ℝ))) '' ((fun (x:ℝ) ↦ (x:WithTop ℝ)) '' E)) := by
    rw [←Set.image_comp]; congr
  _ = sSup ((fun (x:ℝ) ↦ (x:WithTop ℝ)) '' E) := by
    symm; apply WithBot.coe_sSup'
    . simp [hnon]
    exact WithTop.coe_mono.map_bddAbove hbound
  _ = ((sSup E : ℝ) : WithTop ℝ) := by congr; symm; exact WithTop.coe_sSup' hbound
  _ = _ := rfl

/-- Definition 6.2.6 -/
theorem EReal.sup_of_unbounded_nonempty {E: Set ℝ} (hunbound: ¬ BddAbove E) (hnon: E.Nonempty) :
    sSup ((fun (x:ℝ) ↦ (x:EReal)) '' E) = ⊤ := by
  erw [sSup_eq_top]
  intro b hb
  obtain ⟨ y, rfl ⟩ | rfl | rfl := EReal.def b
  . simp; contrapose! hunbound; exact ⟨ y, hunbound ⟩
  . exact absurd hb (lt_irrefl _)
  exact ⟨↑hnon.choose, Set.mem_image_of_mem _ hnon.choose_spec, bot_lt_coe _⟩

/-- Definition 6.2.6 -/
theorem EReal.sup_of_empty : sSup (∅:Set EReal) = ⊥ := sSup_empty

/-- Definition 6.2.6 -/
theorem EReal.sup_of_infty_mem {E: Set EReal} (hE: ⊤ ∈ E) : sSup E = ⊤ := csSup_eq_top_of_top_mem hE

/-- Definition 6.2.6 -/
theorem EReal.sup_of_neg_infty_mem {E: Set EReal} : sSup E = sSup (E \ {⊥}) := (sSup_diff_singleton_bot _).symm

theorem EReal.inf_eq_neg_sup (E: Set EReal) : sInf E = - sSup (-E) := by
  simp_rw [←isGLB_iff_sInf_eq, isGLB_iff_le_iff, EReal.le_neg]
  intro b
  simp [lowerBounds]

/-- Example 6.2.7 -/
abbrev Example_6_2_7 : Set EReal := { x | ∃ n:ℕ, x = -((n+1):EReal)} ∪ {⊥}

example : sSup Example_6_2_7 = -1 := by
  rw [EReal.sup_of_neg_infty_mem]
  apply le_antisymm
  · apply csSup_le'
    intro x hx
    simp only [Set.mem_diff, Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff] at hx
    rcases hx with ⟨⟨n, rfl⟩ | rfl, _⟩
    · simp only [neg_le_neg_iff]; exact_mod_cast Nat.le_add_left 1 n
    · tauto
  · apply le_csSup (OrderTop.bddAbove _)
    simp only [Set.mem_diff, Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff]
    refine ⟨Or.inl ⟨0, by simp⟩, ?_⟩
    simp [show (-1:EReal) ≠ ⊥ from coe_ne_bot _]

example : sInf Example_6_2_7 = ⊥ := by
  rw [EReal.inf_eq_neg_sup]
  have : ⊤ ∈ -Example_6_2_7 := by
    simp only [Set.mem_neg, neg_top]
    right; exact Set.mem_singleton ⊥
  rw [show sSup (-Example_6_2_7) = ⊤ from csSup_eq_top_of_top_mem this]
  simp

/-- Example 6.2.8 -/
abbrev Example_6_2_8 : Set EReal := { x | ∃ n:ℕ, x = (1 - (10:ℝ)^(-(n:ℤ)-1):Real)}

example : sInf Example_6_2_8 = (0.9:ℝ) := by
  apply le_antisymm
  · exact csInf_le (OrderBot.bddBelow _) ⟨0, by norm_cast; norm_num⟩
  · apply le_sInf; intro x hx; obtain ⟨n, rfl⟩ := hx
    simp only [EReal.coe_le_coe_iff]
    have h1 : (10:ℝ)^(-(n:ℤ)-1) ≤ 10^(-(0:ℤ)-1) := by
      gcongr <;> [norm_num; omega]
    simp only [show (-(0:ℤ)-1 : ℤ) = -1 from by norm_num] at h1
    simp only [show (10:ℝ)^(-1:ℤ) = 1/10 from by norm_num] at h1
    linarith

example : sSup Example_6_2_8 = 1 := by
  apply le_antisymm
  · -- sSup ≤ 1: every element ≤ 1
    apply sSup_le
    intro x hx
    obtain ⟨n, rfl⟩ := hx
    show (↑(1 - (10:ℝ)^(-(n:ℤ)-1)) : EReal) ≤ ↑(1:ℝ)
    exact_mod_cast sub_le_self 1 (le_of_lt (by positivity : (0:ℝ) < 10^(-(n:ℤ)-1)))
  · -- 1 ≤ sSup: 1 is a lower bound of all upper bounds
    rw [le_sSup_iff]
    intro b hb
    induction b using EReal.rec with
    | bot =>
      exfalso
      have hmem : (↑(1 - (10:ℝ)^(-(0:ℤ)-1)) : EReal) ∈ Example_6_2_8 := ⟨0, rfl⟩
      exact absurd (hb hmem) (not_le.mpr (EReal.bot_lt_coe _))
    | coe b' =>
      suffices h : (1:ℝ) ≤ b' by exact_mod_cast h
      by_contra h'
      push_neg at h'
      have hpos : (0:ℝ) < 1 - b' := by linarith
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos (by norm_num : (10:ℝ)⁻¹ < 1)
      have hmem : (↑(1 - (10:ℝ)^(-(n:ℤ)-1)) : EReal) ∈ Example_6_2_8 := ⟨n, rfl⟩
      have hle := hb hmem
      rw [EReal.coe_le_coe_iff] at hle
      have hconv : (10:ℝ)^(-(n:ℤ)-1) = (10⁻¹:ℝ)^(n+1) := by
        rw [show -(n:ℤ)-1 = -((n:ℤ)+1) from by ring, zpow_neg,
            show (n:ℤ)+1 = ((n+1:ℕ):ℤ) from by push_cast; ring, zpow_natCast, inv_pow]
      have hsmaller : (10:ℝ)⁻¹^(n+1) ≤ (10:ℝ)⁻¹^n := by
        exact pow_le_pow_of_le_one (by positivity) (by norm_num) (Nat.le_succ n)
      linarith
    | top => exact le_top

/-- Example 6.2.9 -/
abbrev Example_6_2_9 : Set EReal := { x | ∃ n:ℕ, x = n+1}

example : sInf Example_6_2_9 = 1 := by
  apply le_antisymm
  · apply csInf_le (OrderBot.bddBelow _); exact ⟨0, by simp⟩
  · apply le_sInf; intro x hx; obtain ⟨n, rfl⟩ := hx
    exact_mod_cast Nat.le_add_left 1 n

example : sSup Example_6_2_9 = ⊤ := by
  erw [sSup_eq_top]; intro b hb
  induction b using EReal.rec with
  | bot => exact ⟨1, ⟨0, by simp⟩, bot_lt_coe 1⟩
  | top => exact absurd hb (lt_irrefl _)
  | coe r =>
    obtain ⟨n, hn⟩ := exists_nat_gt r
    refine ⟨↑n + 1, ⟨n, rfl⟩, ?_⟩
    calc (r : EReal) < ↑n := by exact_mod_cast hn
    _ ≤ ↑n + 1 := le_add_of_nonneg_right (by positivity)

example : sInf (∅ : Set EReal) = ⊤ := @sInf_empty EReal _

example (E: Set EReal) : sSup E < sInf E ↔ E = ∅ := by
  constructor
  · intro h
    by_contra hne
    have hne' : E.Nonempty := Set.nonempty_iff_ne_empty.mpr hne
    obtain ⟨x, hx⟩ := hne'
    exact not_lt.mpr ((csInf_le (OrderBot.bddBelow E) hx).trans
      (le_csSup (OrderTop.bddAbove E) hx)) h
  · intro h; subst h; simp

/-- Theorem 6.2.11 (a) / Exercise 6.2.2 -/
theorem EReal.mem_le_sup (E: Set EReal) {x:EReal} (hx: x ∈ E) : x ≤ sSup E :=
  le_csSup (OrderTop.bddAbove E) hx

/-- Theorem 6.2.11 (a) / Exercise 6.2.2 -/
theorem EReal.mem_ge_inf (E: Set EReal) {x:EReal} (hx: x ∈ E) : sInf E ≤ x :=
  csInf_le (OrderBot.bddBelow E) hx

/-- Theorem 6.2.11 (b) / Exercise 6.2.2 -/
theorem EReal.sup_le_upper (E: Set EReal) {M:EReal} (hM: M ∈ upperBounds E) : sSup E ≤ M :=
  csSup_le' hM

/-- Theorem 6.2.11 (c) / Exercise 6.2.2 -/
theorem EReal.inf_ge_upper (E: Set EReal) {M:EReal} (hM: M ∈ lowerBounds E) : sInf E ≥ M :=
  le_sInf hM

#check isLUB_iff_sSup_eq
#check isGLB_iff_sInf_eq

/-- Not in textbook: identify the Chapter 5 extended reals with the Mathlib {name}`EReal`.
-/
noncomputable abbrev Chapter5.ExtendedReal.toEReal (x:ExtendedReal) : EReal := match x with
  | real r => ((Real.equivR r):EReal)
  | infty => ⊤
  | neg_infty => ⊥

theorem Chapter5.ExtendedReal.coe_inj : Function.Injective toEReal := by
  intro a b hab
  cases a <;> cases b <;> simp_all [toEReal]
  case neg_infty.infty => exact absurd hab bot_ne_top
  case infty.neg_infty => exact absurd hab top_ne_bot
  case real.real x y => exact Real.equivR.injective hab

theorem Chapter5.ExtendedReal.coe_surj : Function.Surjective toEReal := by
  intro b
  induction b using EReal.rec with
  | bot => exact ⟨.neg_infty, rfl⟩
  | top => exact ⟨.infty, rfl⟩
  | coe r =>
    refine ⟨.real (Real.equivR.symm r), ?_⟩
    show ((Real.equivR (Real.equivR.symm r)):EReal) = r
    rw [Equiv.apply_symm_apply]

noncomputable abbrev Chapter5.ExtendedReal.equivEReal : Chapter5.ExtendedReal ≃ EReal where
  toFun := toEReal
  invFun x := match x with
    | ⊥ => .neg_infty
    | ⊤ => .infty
    | (r : ℝ) => .real (Real.equivR.symm r)
  left_inv x := by
    cases x with
    | real r =>
      show ExtendedReal.real (Real.equivR.symm (Real.equivR r)) = .real r
      rw [Equiv.symm_apply_apply]
    | infty => rfl
    | neg_infty => rfl
  right_inv x := by
    induction x using EReal.rec with
    | bot => rfl
    | top => rfl
    | coe r =>
      show ((Real.equivR (Real.equivR.symm r)):EReal) = r
      rw [Equiv.apply_symm_apply]
