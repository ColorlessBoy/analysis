import Mathlib.Tactic
import Analysis.Section_8_1
import Analysis.Section_8_2

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

/-- Theorem 8.3.1 -/
theorem EqualCard.power_set_false (X:Type) : ¬ EqualCard X (Set X) := by
  -- This proof is written to follow the structure of the original text.
  by_contra!; choose f hf using this
  set A := {x | x ∉ f x }; choose x hx using hf.2 A
  by_cases h : x ∈ A <;> have h' := h
  . simp [A] at h'; simp_all
  rw [←hx] at h'
  have : x ∈ A := by simp [A, h']
  contradiction

theorem Uncountable.iff (X:Type) : Uncountable X ↔ ¬ AtMostCountable X := by
  rw [AtMostCountable.iff, uncountable_iff_not_countable]


theorem Uncountable.equiv {X Y: Type} (hXY : EqualCard X Y) :
  Uncountable X ↔ Uncountable Y := by
    simp [Uncountable.iff, AtMostCountable.equiv hXY]

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
  replace := (equiv this).mp power_set_nat
  contrapose this
  rw [not_uncountable_iff] at this ⊢
  apply SetCoe.countable

/-- Exercise 8.3.1 -/
example {X:Type} [Finite X] : Nat.card (Set X) = 2 ^ Nat.card X := by
  haveI : Fintype X := Fintype.ofFinite _
  calc
    Nat.card (Set X) = Fintype.card (Set X) := by simp
    _ = 2 ^ Fintype.card X := Fintype.card_set
    _ = 2 ^ Nat.card X := by simp

open Classical in
/-- Exercise 8.3.2.  Some subtle type changes due to how sets are implemented in Mathlib. Also we shift the sequence {lit}`D` by one so that we can work in {lean}`Set A` rather than {lean}`Set B`. -/
theorem Schroder_Bernstein_lemma {X: Type} {A B C: Set X} (hAB: A ⊆ B) (hBC: B ⊆ C) (f: C ↪ A) :
  let D : ℕ → Set A := Nat.rec ((f.image ∘ ((B.embeddingOfSubset _ hBC).image)) {x:B | ↑x ∉ A}) (fun _ ↦ (f.image ∘ ((B.embeddingOfSubset _ hBC).image) ∘ (A.embeddingOfSubset _ hAB).image))
  Set.univ.PairwiseDisjoint D ∧
  let g : A → B := fun x ↦ if h: x ∈ ⋃ n, D n ∧ ∃ y:B, f ⟨↑y, hBC y.property⟩ = x then h.2.choose else ⟨ ↑x, hAB x.property ⟩
  Function.Bijective g
  := by
  intro D
  have hD0 : D 0 = f.image ((B.embeddingOfSubset _ hBC).image {x:B | ↑x ∉ A}) := rfl
  have hDstep (n : ℕ) : D (n+1) = f.image ((B.embeddingOfSubset _ hBC).image ((A.embeddingOfSubset _ hAB).image (D n))) := rfl
  have mem_D0_iff (x : A) : x ∈ D 0 ↔ ∃ (b : B), b.val ∉ A ∧ f ((B.embeddingOfSubset _ hBC) b) = x := by
    rw [hD0]
    have h_eq : f.image ((B.embeddingOfSubset _ hBC).image {x:B | ↑x ∉ A}) = f '' ((B.embeddingOfSubset _ hBC) '' {x:B | ↑x ∉ A}) := by
      ext x; simp
    rw [h_eq, Set.mem_image]
    constructor
    · rintro ⟨ c, hc, hc' ⟩
      rw [Set.mem_image] at hc
      rcases hc with ⟨ b, hb, rfl ⟩
      refine ⟨ b, hb, hc' ⟩
    · rintro ⟨ b, hb, hb' ⟩
      refine ⟨ (B.embeddingOfSubset _ hBC) b, ?_, hb' ⟩
      rw [Set.mem_image]
      exact ⟨ b, hb, rfl ⟩
  have mem_Dstep_iff (n : ℕ) (x : A) : x ∈ D (n+1) ↔ ∃ (y : A), y ∈ D n ∧ f ((B.embeddingOfSubset _ hBC) ((A.embeddingOfSubset _ hAB) y)) = x := by
    rw [hDstep n]
    have h_eq : f.image ((B.embeddingOfSubset _ hBC).image ((A.embeddingOfSubset _ hAB).image (D n))) = f '' ((B.embeddingOfSubset _ hBC) '' ((A.embeddingOfSubset _ hAB) '' (D n))) := by
      ext x; simp
    rw [h_eq, Set.mem_image]
    constructor
    · rintro ⟨ c, hc, hc' ⟩
      rw [Set.mem_image] at hc
      rcases hc with ⟨ b, hb, rfl ⟩
      rw [Set.mem_image] at hb
      rcases hb with ⟨ y, hy, rfl ⟩
      refine ⟨ y, hy, hc' ⟩
    · rintro ⟨ y, hy, hy' ⟩
      refine ⟨ (B.embeddingOfSubset _ hBC) ((A.embeddingOfSubset _ hAB) y), ?_, hy' ⟩
      rw [Set.mem_image]
      refine ⟨ (A.embeddingOfSubset _ hAB) y, ?_, rfl ⟩
      rw [Set.mem_image]
      exact ⟨ y, hy, rfl ⟩
  have h_disjoint_lt (i j : ℕ) (hij_lt : i < j) : Disjoint (D i) (D j) := by
    revert j
    induction' i with k ih
    · intro j hj
      apply Set.disjoint_iff_inter_eq_empty.mpr
      rw [← Set.not_nonempty_iff_eq_empty]
      intro h_nonempty
      rcases h_nonempty with ⟨ x, hx ⟩
      rcases hx with ⟨ hxi, hxj ⟩
      rcases mem_D0_iff x |>.mp hxi with ⟨ b, hb, hb' ⟩
      cases' j with j'
      · exfalso; omega
      · rw [mem_Dstep_iff j' x] at hxj
        rcases hxj with ⟨ y, hy, hy' ⟩
        have h_inj : f ((B.embeddingOfSubset _ hBC) b) = f ((B.embeddingOfSubset _ hBC) ((A.embeddingOfSubset _ hAB) y)) := by
          rw [hb', hy']
        have h_emb_inj : (B.embeddingOfSubset _ hBC) b = (B.embeddingOfSubset _ hBC) ((A.embeddingOfSubset _ hAB) y) :=
          f.injective h_inj
        have h_b_eq : b = (A.embeddingOfSubset _ hAB) y :=
          (B.embeddingOfSubset _ hBC).injective h_emb_inj
        have : b.val ∈ A := by
          have hyA : y.val ∈ A := y.property
          have h_val : b.val = y.val :=
            calc
              b.val = ((A.embeddingOfSubset _ hAB) y).val := congr_arg Subtype.val h_b_eq
              _ = y.val := rfl
          rw [h_val]
          exact hyA
        exact hb this
    · intro j hj
      apply Set.disjoint_iff_inter_eq_empty.mpr
      rw [← Set.not_nonempty_iff_eq_empty]
      intro h_nonempty
      rcases h_nonempty with ⟨ x, hx ⟩
      rcases hx with ⟨ hxi, hxj ⟩
      rw [mem_Dstep_iff k x] at hxi
      rcases hxi with ⟨ z, hz, hz' ⟩
      cases' j with j'
      · exfalso; omega
      · rw [mem_Dstep_iff j' x] at hxj
        rcases hxj with ⟨ w, hw, hw' ⟩
        have h_inj : f ((B.embeddingOfSubset _ hBC) ((A.embeddingOfSubset _ hAB) z)) =
            f ((B.embeddingOfSubset _ hBC) ((A.embeddingOfSubset _ hAB) w)) := by
          rw [hz', hw']
        have h_emb_inj : (B.embeddingOfSubset _ hBC) ((A.embeddingOfSubset _ hAB) z) =
            (B.embeddingOfSubset _ hBC) ((A.embeddingOfSubset _ hAB) w) :=
          f.injective h_inj
        have h_AB_z_eq_AB_w : (A.embeddingOfSubset _ hAB) z = (A.embeddingOfSubset _ hAB) w :=
          (B.embeddingOfSubset _ hBC).injective h_emb_inj
        have h_z_eq_w : z = w :=
          (A.embeddingOfSubset _ hAB).injective h_AB_z_eq_AB_w
        have hz_in_Dk : z ∈ D k := hz
        have hz_in_Dj' : z ∈ D j' := by
          rw [h_z_eq_w]
          exact hw
        have hk_lt_j' : k < j' := by omega
        have h_dj : Disjoint (D k) (D j') := ih j' hk_lt_j'
        rw [Set.disjoint_iff_inter_eq_empty] at h_dj
        have : z ∈ (D k) ∩ (D j') := ⟨ hz_in_Dk, hz_in_Dj' ⟩
        rw [h_dj] at this
        simp at this
  have h_disjoint : Set.univ.PairwiseDisjoint D := by
    intro i hi j hj hij
    by_cases hlt : i < j
    · exact h_disjoint_lt i j hlt
    · have hlt' : j < i := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) hij.symm
      have h := h_disjoint_lt j i hlt'
      simpa [Set.disjoint_iff_inter_eq_empty, Set.inter_comm] using h
  let g : A → B := fun x ↦ if h: x ∈ ⋃ n, D n ∧ ∃ y:B, f ⟨↑y, hBC y.property⟩ = x then h.2.choose else ⟨ ↑x, hAB x.property ⟩
  have h_mem_union_imp_preimage (x : A) (hx_union : x ∈ ⋃ n, D n) : ∃ z:B, f ⟨↑z, hBC z.property⟩ = x := by
    rw [Set.mem_iUnion] at hx_union
    rcases hx_union with ⟨ n, hn ⟩
    induction' n with k ih generalizing x
    · rw [mem_D0_iff] at hn; rcases hn with ⟨ z, hz, hz' ⟩; exact ⟨ z, hz' ⟩
    · rw [mem_Dstep_iff k] at hn; rcases hn with ⟨ y, hy, hy' ⟩; exact ⟨ (A.embeddingOfSubset _ hAB) y, hy' ⟩
  have h_preimage_imp_mem_union (y : A) : f ((B.embeddingOfSubset _ hBC) ((A.embeddingOfSubset _ hAB) y)) ∈ ⋃ n, D n → y ∈ ⋃ n, D n := by
    intro h
    rw [Set.mem_iUnion] at h
    rcases h with ⟨ n, hn ⟩
    induction' n with k ih generalizing y
    · rw [mem_D0_iff] at hn
      rcases hn with ⟨ b, hb, hb' ⟩
      have h_emb_inj : (B.embeddingOfSubset _ hBC) ((A.embeddingOfSubset _ hAB) y) = (B.embeddingOfSubset _ hBC) b :=
        f.injective hb'.symm
      have hy_eq_b : (A.embeddingOfSubset _ hAB) y = b := (B.embeddingOfSubset _ hBC).injective h_emb_inj
      have hy_val_eq : y.val = b.val := congr_arg Subtype.val hy_eq_b
      have hyA : y.val ∈ A := y.property
      rw [hy_val_eq] at hyA
      exfalso; exact hb hyA
    · rw [mem_Dstep_iff k] at hn
      rcases hn with ⟨ z, hz, hz' ⟩
      have h_emb_inj : (B.embeddingOfSubset _ hBC) ((A.embeddingOfSubset _ hAB) y) = (B.embeddingOfSubset _ hBC) ((A.embeddingOfSubset _ hAB) z) :=
        f.injective hz'.symm
      have hy_eq_z : y = z :=
        (A.embeddingOfSubset _ hAB).injective ((B.embeddingOfSubset _ hBC).injective h_emb_inj)
      rw [hy_eq_z]
      rw [Set.mem_iUnion]
      exact ⟨ k, hz ⟩
  have h_g_spec (x : A) (hx_cond : x ∈ ⋃ n, D n ∧ ∃ z:B, f ⟨↑z, hBC z.property⟩ = x) :
      f ((B.embeddingOfSubset _ hBC) (g x)) = x := by
    dsimp [g]; simp [hx_cond]; simpa using hx_cond.2.choose_spec
  have h_g_not_union_val (x : A) (hx_not : x ∉ ⋃ n, D n) : (g x).val = x.val := by
    dsimp [g]
    split_ifs with h
    · exfalso; exact hx_not h.1
    · rfl
  have h_bijective : Function.Bijective g := by
    constructor
    · intro x y h_eq
      by_cases hx_union : x ∈ ⋃ n, D n
      · by_cases hy_union : y ∈ ⋃ n, D n
        · have hx_ex : ∃ z:B, f ⟨↑z, hBC z.property⟩ = x := h_mem_union_imp_preimage x hx_union
          have hy_ex : ∃ z:B, f ⟨↑z, hBC z.property⟩ = y := h_mem_union_imp_preimage y hy_union
          have hx_cond : x ∈ ⋃ n, D n ∧ ∃ z:B, f ⟨↑z, hBC z.property⟩ = x := ⟨ hx_union, hx_ex ⟩
          have hy_cond : y ∈ ⋃ n, D n ∧ ∃ z:B, f ⟨↑z, hBC z.property⟩ = y := ⟨ hy_union, hy_ex ⟩
          calc
            x = f ((B.embeddingOfSubset _ hBC) (g x)) := (h_g_spec x hx_cond).symm
            _ = f ((B.embeddingOfSubset _ hBC) (g y)) := by rw [h_eq]
            _ = y := h_g_spec y hy_cond
        · -- x in union, y not in union — impossible
          have hx_ex : ∃ z:B, f ⟨↑z, hBC z.property⟩ = x := h_mem_union_imp_preimage x hx_union
          have hx_cond : x ∈ ⋃ n, D n ∧ ∃ z:B, f ⟨↑z, hBC z.property⟩ = x := ⟨ hx_union, hx_ex ⟩
          have h_gx_spec : f ((B.embeddingOfSubset _ hBC) (g x)) = x := h_g_spec x hx_cond
          have h_val : g y = ⟨ ↑y, hAB y.property ⟩ := by
            dsimp [g]; simp [hy_union]
          have h_eq' : f ((B.embeddingOfSubset _ hBC) ((A.embeddingOfSubset _ hAB) y)) = x := by
            calc
              f ((B.embeddingOfSubset _ hBC) ((A.embeddingOfSubset _ hAB) y)) =
                  f ((B.embeddingOfSubset _ hBC) (⟨ ↑y, hAB y.property ⟩ : B)) := rfl
              _ = f ((B.embeddingOfSubset _ hBC) (g y)) := by rw [h_val]
              _ = f ((B.embeddingOfSubset _ hBC) (g x)) := by rw [h_eq]
              _ = x := h_gx_spec
          have hx_in_union : f ((B.embeddingOfSubset _ hBC) ((A.embeddingOfSubset _ hAB) y)) ∈ ⋃ n, D n := by
            rw [h_eq']; exact hx_union
          have hy_in_union : y ∈ ⋃ n, D n := h_preimage_imp_mem_union y hx_in_union
          exfalso; exact hy_union hy_in_union
      · by_cases hy_union : y ∈ ⋃ n, D n
        · -- x not in union, y in union — impossible (symmetric)
          have hy_ex : ∃ z:B, f ⟨↑z, hBC z.property⟩ = y := h_mem_union_imp_preimage y hy_union
          have hy_cond : y ∈ ⋃ n, D n ∧ ∃ z:B, f ⟨↑z, hBC z.property⟩ = y := ⟨ hy_union, hy_ex ⟩
          have h_gy_spec : f ((B.embeddingOfSubset _ hBC) (g y)) = y := h_g_spec y hy_cond
          have h_val : g x = ⟨ ↑x, hAB x.property ⟩ := by
            dsimp [g]; simp [hx_union]
          have h_eq' : f ((B.embeddingOfSubset _ hBC) ((A.embeddingOfSubset _ hAB) x)) = y := by
            calc
              f ((B.embeddingOfSubset _ hBC) ((A.embeddingOfSubset _ hAB) x)) =
                  f ((B.embeddingOfSubset _ hBC) (⟨ ↑x, hAB x.property ⟩ : B)) := rfl
              _ = f ((B.embeddingOfSubset _ hBC) (g x)) := by rw [h_val]
              _ = f ((B.embeddingOfSubset _ hBC) (g y)) := by rw [h_eq]
              _ = y := h_gy_spec
          have hy_in_union : f ((B.embeddingOfSubset _ hBC) ((A.embeddingOfSubset _ hAB) x)) ∈ ⋃ n, D n := by
            rw [h_eq']; exact hy_union
          have hx_in_union : x ∈ ⋃ n, D n := h_preimage_imp_mem_union x hy_in_union
          exfalso; exact hx_union hx_in_union
        · have hx_val : (g x).val = x.val := h_g_not_union_val x hx_union
          have hy_val : (g y).val = y.val := h_g_not_union_val y hy_union
          rw [h_eq] at hx_val
          have : x.val = y.val := by rw [← hx_val, hy_val]
          exact Subtype.val_injective this
    · -- surjectivity
      intro y
      by_cases hyA : y.val ∈ A
      · let y' : A := ⟨ y.val, hyA ⟩
        by_cases hy'_union : y' ∈ ⋃ n, D n
        · let x : A := f ((B.embeddingOfSubset _ hBC) ((A.embeddingOfSubset _ hAB) y'))
          have hx_union : x ∈ ⋃ n, D n := by
            rw [Set.mem_iUnion]
            rcases (Set.mem_iUnion.mp hy'_union) with ⟨ k, hk ⟩
            refine ⟨ k+1, ?_ ⟩
            rw [mem_Dstep_iff k x]
            exact ⟨ y', hk, rfl ⟩
          have hx_ex : ∃ (z : B), f ⟨↑z, hBC z.property⟩ = x :=
            ⟨ (A.embeddingOfSubset _ hAB) y', rfl ⟩
          have hx_cond : x ∈ ⋃ n, D n ∧ ∃ (z : B), f ⟨↑z, hBC z.property⟩ = x := ⟨ hx_union, hx_ex ⟩
          have h_gx_eq_y' : g x = (A.embeddingOfSubset _ hAB) y' := by
            have h_gx_spec : f ((B.embeddingOfSubset _ hBC) (g x)) = x := h_g_spec x hx_cond
            have hx_def : f ((B.embeddingOfSubset _ hBC) ((A.embeddingOfSubset _ hAB) y')) = x := rfl
            have h_emb_eq : (B.embeddingOfSubset _ hBC) (g x) = (B.embeddingOfSubset _ hBC) ((A.embeddingOfSubset _ hAB) y') :=
              f.injective (by rw [h_gx_spec, hx_def])
            exact (B.embeddingOfSubset _ hBC).injective h_emb_eq
          have h_emb_eq_y : (A.embeddingOfSubset _ hAB) y' = y := by
            ext; rfl
          use x
          rw [h_gx_eq_y', h_emb_eq_y]
        · use y'
          dsimp [g]; simp [hy'_union]
          ext; rfl
      · refine ⟨ f ((B.embeddingOfSubset _ hBC) y), ?_ ⟩
        set x := f ((B.embeddingOfSubset _ hBC) y) with hx_def
        have hx_union : x ∈ ⋃ n, D n := by
          rw [Set.mem_iUnion]
          refine ⟨ 0, ?_ ⟩
          rw [mem_D0_iff x, hx_def]
          exact ⟨ y, hyA, rfl ⟩
        have hx_ex : ∃ (z : B), f ⟨↑z, hBC z.property⟩ = x := ⟨ y, rfl ⟩
        have hx_cond : x ∈ ⋃ n, D n ∧ ∃ (z : B), f ⟨↑z, hBC z.property⟩ = x := ⟨ hx_union, hx_ex ⟩
        have h_gx_spec : f ((B.embeddingOfSubset _ hBC) (g x)) = x := h_g_spec x hx_cond
        have hx_def' : f ((B.embeddingOfSubset _ hBC) y) = x := rfl
        have h_emb_eq : (B.embeddingOfSubset _ hBC) (g x) = (B.embeddingOfSubset _ hBC) y :=
          f.injective (by rw [h_gx_spec, hx_def'])
        exact (B.embeddingOfSubset _ hBC).injective h_emb_eq
  refine ⟨ h_disjoint, ?_ ⟩
  exact h_bijective

abbrev LeCard (X Y: Type) : Prop := ∃ f: X → Y, Function.Injective f

/-- Exercise 8.3.3 -/
theorem Schroder_Bernstein {X Y:Type} (hXY : LeCard X Y) (hYX : LeCard Y X) : EqualCard X Y := by
  rcases hXY with ⟨ f, hf ⟩
  rcases hYX with ⟨ g, hg ⟩
  rcases Function.Embedding.schroeder_bernstein hf hg with ⟨ h, hh ⟩
  exact ⟨ h, hh ⟩

abbrev LtCard (X Y: Type) : Prop := LeCard X Y ∧ ¬ EqualCard X Y

/-- Exercise 8.3.4 -/
example {X:Type} : LtCard X (Set X) := by
  refine ⟨ ?_, ?_ ⟩
  · refine ⟨ fun x => {x}, fun a b h => by simpa using h ⟩
  · exact EqualCard.power_set_false X

example {A B C: Type} (hAB: LtCard A B) (hBC: LtCard B C) :
  LtCard A C := by
  rcases hAB with ⟨ hAB_le, hAB_not_eq ⟩
  rcases hBC with ⟨ hBC_le, hBC_not_eq ⟩
  rcases hAB_le with ⟨ f, hf ⟩
  rcases hBC_le with ⟨ g, hg ⟩
  have hAC_le : LeCard A C := ⟨ g ∘ f, hg.comp hf ⟩
  refine ⟨ hAC_le, ?_ ⟩
  intro hAC_eq
  rcases hAC_eq with ⟨ h, hh ⟩
  have hCA_le : LeCard C A :=
    ⟨ (Equiv.ofBijective h hh).symm, (Equiv.ofBijective h hh).symm.injective ⟩
  rcases hCA_le with ⟨ k, hk ⟩
  have hBA_le : LeCard B A := ⟨ k ∘ g, hk.comp hg ⟩
  have hAB_eq : EqualCard A B := Schroder_Bernstein ⟨ f, hf ⟩ hBA_le
  exact hAB_not_eq hAB_eq

abbrev CardOrder : Preorder Type := {
  le := LeCard
  lt := LtCard
  le_refl := by
    intro X
    refine ⟨ id, ?_ ⟩
    exact Function.injective_id
  le_trans := by
    intro X Y Z ⟨ f, hf ⟩ ⟨ g, hg ⟩
    refine ⟨ g ∘ f, ?_ ⟩
    exact hg.comp hf
  lt_iff_le_not_ge := by
    intro X Y
    constructor
    · rintro ⟨ hXY_le, hXY_not_eq ⟩
      refine ⟨ hXY_le, ?_ ⟩
      intro hYX_le
      have : EqualCard X Y := Schroder_Bernstein hXY_le hYX_le
      exact hXY_not_eq this
    · rintro ⟨ hXY_le, hYX_not_le ⟩
      refine ⟨ hXY_le, ?_ ⟩
      intro hXY_eq
      rcases hXY_eq with ⟨ f, hf ⟩
      have : LeCard Y X :=
        ⟨ (Equiv.ofBijective f hf).symm, (Equiv.ofBijective f hf).symm.injective ⟩
      exact hYX_not_le this
}

/-- Exercise 8.3.5 -/
example (X:Type) : ¬ CountablyInfinite (Set X) := by
  intro h
  have h_inj_singleton : LeCard X (Set X) := ⟨ fun x => {x}, fun a b h => by simpa using h ⟩
  rcases h_inj_singleton with ⟨ f, hf ⟩
  rcases h with ⟨ g, hg ⟩
  have h_inj_X_N : Function.Injective (g ∘ f) := hg.injective.comp hf
  have h_countable_X : Countable X := h_inj_X_N.countable
  have h_atmost : AtMostCountable X := (AtMostCountable.iff X).mpr h_countable_X
  rcases h_atmost with (h_countinf | h_finite)
  · have h_setX_eq_N : EqualCard (Set X) ℕ := ⟨ g, hg ⟩
    have : EqualCard X (Set X) := h_countinf.trans (EqualCard.symm h_setX_eq_N)
    exact EqualCard.power_set_false X this
  · haveI : Finite X := h_finite
    have : Finite (Set X) := by
      haveI : Fintype X := Fintype.ofFinite _
      infer_instance
    have : Infinite (Set X) := CountablyInfinite.toInfinite ⟨ g, hg ⟩
    exact not_finite (Set X)

end Chapter8
