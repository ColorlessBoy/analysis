import Mathlib.Tactic

set_option doc.verso.suggestions false

/-!
# Analysis I, Section 7.1: Finite series

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Technical note: it is convenient in Lean to extend finite sequences (usually by zero) to be
functions on the entire integers.

Main constructions and results of this section:
-/

-- This makes available the convenient notation `∑ n ∈ A, f n` to denote summation of `f n` for
-- `n` ranging over a finite set `A`.
open BigOperators

/-!
- API for summation over finite sets (encoded using Mathlib's {name}`Finset` type), using the
  {name}`Finset.sum` method and the `∑ n ∈ A, f n` notation.
- Fubini's theorem for finite series

We do not attempt to replicate the full API for {name}`Finset.sum` here, but in subsequent sections we
shall make liberal use of this API.

-/

-- This is a technical device to avoid Mathlib's insistence on decidable equality for finite sets.
open Classical

namespace Finset

-- We use `Finset.Icc` to describe finite intervals in the integers. `Finset.mem_Icc` is the
-- standard Mathlib tool for checking membership in such intervals.
#check mem_Icc

/-- Definition 7.1.1 -/
theorem sum_of_empty {n m:ℤ} (h: n < m) (a: ℤ → ℝ) : ∑ i ∈ Icc m n, a i = 0 := by
  rw [sum_eq_zero]; intro _; rw [mem_Icc]; grind

/--
  Definition 7.1.1. This is similar to Mathlib's {name}`Finset.sum_Icc_succ_top` except that the
  latter involves summation over the natural numbers rather than integers.
-/
theorem sum_of_nonempty {n m:ℤ} (h: n ≥ m-1) (a: ℤ → ℝ) :
    ∑ i ∈ Icc m (n+1), a i = ∑ i ∈ Icc m n, a i + a (n+1) := by
  rw [add_comm _ (a (n+1))]
  convert sum_insert _
  . ext; simp; omega
  . infer_instance
  simp

example (a: ℤ → ℝ) (m:ℤ) : ∑ i ∈ Icc m (m-2), a i = 0 := by
  have h : (m-2) < m := by omega
  exact sum_of_empty h a

example (a: ℤ → ℝ) (m:ℤ) : ∑ i ∈ Icc m (m-1), a i = 0 := by
  have h : (m-1) < m := by omega
  exact sum_of_empty h a

example (a: ℤ → ℝ) (m:ℤ) : ∑ i ∈ Icc m m, a i = a m := by
  simp

example (a: ℤ → ℝ) (m:ℤ) : ∑ i ∈ Icc m (m+1), a i = a m + a (m+1) := by
  have h : m ≥ m-1 := by omega
  rw [sum_of_nonempty h a]
  simp

example (a: ℤ → ℝ) (m:ℤ) : ∑ i ∈ Icc m (m+2), a i = a m + a (m+1) + a (m+2) := by
  have hsum_m_plus_1 : ∑ i ∈ Icc m (m+1), a i = a m + a (m+1) := by
    have h : m ≥ m-1 := by omega
    rw [sum_of_nonempty h a]
    simp
  have h_cond : m+1 ≥ m-1 := by omega
  have h_eq : (m+2) = ((m+1)+1) := by omega
  rw [h_eq]
  rw [sum_of_nonempty h_cond a]
  rw [hsum_m_plus_1]

/-- Remark 7.1.3 -/
example (a: ℤ → ℝ) (m n:ℤ) : ∑ i ∈ Icc m n, a i = ∑ j ∈ Icc m n, a j := rfl

/-- Lemma 7.1.4(a) / Exercise 7.1.1 -/
theorem concat_finite_series {m n p:ℤ} (hmn: m ≤ n+1) (hpn : n ≤ p) (a: ℤ → ℝ) :
  ∑ i ∈ Icc m n, a i + ∑ i ∈ Icc (n+1) p, a i = ∑ i ∈ Icc m p, a i := by
  have h_disjoint : Disjoint (Icc m n) (Icc (n+1) p) := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hne
    rcases hne with ⟨x, hx⟩
    rcases Finset.mem_inter.mp hx with ⟨hx1, hx2⟩
    rcases Finset.mem_Icc.mp hx1 with ⟨hx1l, hx1u⟩
    rcases Finset.mem_Icc.mp hx2 with ⟨hx2l, hx2u⟩
    omega
  have h_union : Icc m n ∪ Icc (n+1) p = Icc m p := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_union.mp hx with (hx' | hx')
      · rcases Finset.mem_Icc.mp hx' with ⟨hx1, hx2⟩
        apply Finset.mem_Icc.mpr
        exact ⟨hx1, by omega⟩
      · rcases Finset.mem_Icc.mp hx' with ⟨hx1, hx2⟩
        apply Finset.mem_Icc.mpr
        exact ⟨by omega, hx2⟩
    · intro hx
      rcases Finset.mem_Icc.mp hx with ⟨hx1, hx2⟩
      by_cases h : x ≤ n
      · apply Finset.mem_union_left
        apply Finset.mem_Icc.mpr
        exact ⟨hx1, h⟩
      · apply Finset.mem_union_right
        apply Finset.mem_Icc.mpr
        exact ⟨by omega, hx2⟩
  calc
    ∑ i ∈ Icc m n, a i + ∑ i ∈ Icc (n+1) p, a i = ∑ i ∈ (Icc m n ∪ Icc (n+1) p), a i := by
      rw [Finset.sum_union h_disjoint]
    _ = ∑ i ∈ Icc m p, a i := by rw [h_union]

/-- Lemma 7.1.4(b) / Exercise 7.1.1 -/
theorem shift_finite_series {m n k:ℤ} (a: ℤ → ℝ) :
  ∑ i ∈ Icc m n, a i = ∑ i ∈ Icc (m+k) (n+k), a (i-k) := by
  apply Finset.sum_bij (λ i hi => i + k)
  · intro i hi
    rcases Finset.mem_Icc.mp hi with ⟨hi1, hi2⟩
    apply Finset.mem_Icc.mpr
    constructor <;> omega
  · intro i hi j hj h
    omega
  · intro j hj
    rcases Finset.mem_Icc.mp hj with ⟨hj1, hj2⟩
    refine ⟨j - k, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    omega
  · intro i hi
    simp

/-- Lemma 7.1.4(c) / Exercise 7.1.1 -/
theorem finite_series_add {m n:ℤ} (a b: ℤ → ℝ) :
  ∑ i ∈ Icc m n, (a i + b i) = ∑ i ∈ Icc m n, a i + ∑ i ∈ Icc m n, b i := by
  simp [Finset.sum_add_distrib]

/-- Lemma 7.1.4(d) / Exercise 7.1.1 -/
theorem finite_series_const_mul {m n:ℤ} (a: ℤ → ℝ) (c:ℝ) :
  ∑ i ∈ Icc m n, c * a i = c * ∑ i ∈ Icc m n, a i := by
  simp [Finset.mul_sum]

/-- Lemma 7.1.4(e) / Exercise 7.1.1 -/
theorem abs_finite_series_le {m n:ℤ} (a: ℤ → ℝ) :
  |∑ i ∈ Icc m n, a i| ≤ ∑ i ∈ Icc m n, |a i| :=
  Finset.abs_sum_le_sum_abs a (Icc m n)

/-- Lemma 7.1.4(f) / Exercise 7.1.1 -/
theorem finite_series_of_le {m n:ℤ}  {a b: ℤ → ℝ} (h: ∀ i, m ≤ i → i ≤ n → a i ≤ b i) :
  ∑ i ∈ Icc m n, a i ≤ ∑ i ∈ Icc m n, b i :=
  Finset.sum_le_sum fun i hi => by
    rcases Finset.mem_Icc.mp hi with ⟨hmi, hin⟩
    exact h i hmi hin

#check sum_congr

set_option maxHeartbeats 420000 in
/--
  Proposition 7.1.8.
-/
theorem finite_series_of_rearrange {n:ℕ} {X':Type*} (X: Finset X') (hcard: X.card = n)
  (f: X' → ℝ) (g h: Icc (1:ℤ) n → X) (hg: Function.Bijective g) (hh: Function.Bijective h) :
    ∑ i ∈ Icc (1:ℤ) n, (if hi:i ∈ Icc (1:ℤ) n then f (g ⟨ i, hi ⟩) else 0)
    = ∑ i ∈ Icc (1:ℤ) n, (if hi: i ∈ Icc (1:ℤ) n then f (h ⟨ i, hi ⟩) else 0) := by
  -- This proof is written to broadly follow the structure of the original text.
  revert X n; intro n
  induction' n with n hn
  . simp
  intro X hX g h hg hh
  -- A technical step: we extend g, h to the entire integers using a slightly artificial map π
  set π : ℤ → Icc (1:ℤ) (n+1) :=
    fun i ↦ if hi: i ∈ Icc (1:ℤ) (n+1) then ⟨ i, hi ⟩ else ⟨ 1, by simp ⟩
  have hπ (g : Icc (1:ℤ) (n+1) → X) :
      ∑ i ∈ Icc (1:ℤ) (n+1), (if hi:i ∈ Icc (1:ℤ) (n+1) then f (g ⟨ i, hi ⟩) else 0)
      = ∑ i ∈ Icc (1:ℤ) (n+1), f (g (π i)) := by
    apply sum_congr rfl _
    intro i hi; simp [hi, π, -mem_Icc]
  simp [-mem_Icc, hπ]
  rw [sum_of_nonempty (by linarith) _]
  set x := g (π (n+1))
  have ⟨⟨j, hj'⟩, hj⟩ := hh.surjective x
  simp at hj'; obtain ⟨ hj1, hj2 ⟩ := hj'
  set h' : ℤ → X := fun i ↦ if (i:ℤ) < j then h (π i) else h (π (i+1))
  have : ∑ i ∈ Icc (1:ℤ) (n + 1), f (h (π i)) = ∑ i ∈ Icc (1:ℤ) n, f (h' i) + f x := calc
    _ = ∑ i ∈ Icc (1:ℤ) j, f (h (π i)) + ∑ i ∈ Icc (j+1:ℤ) (n + 1), f (h (π i)) := by
      symm; apply concat_finite_series <;> linarith
    _ = ∑ i ∈ Icc (1:ℤ) (j-1), f (h (π i)) + f ( h (π j) )
        + ∑ i ∈ Icc (j+1:ℤ) (n + 1), f (h (π i)) := by
      congr; convert sum_of_nonempty _ _ <;> simp [hj1]
    _ = ∑ i ∈ Icc (1:ℤ) (j-1), f (h (π i)) + f x + ∑ i ∈ Icc (j:ℤ) n, f (h (π (i+1))) := by
      congr 1
      . simp [←hj, π,hj1, hj2]
      symm; convert shift_finite_series _; simp
    _ = ∑ i ∈ Icc (1:ℤ) (j-1), f (h (π i)) + ∑ i ∈ Icc (j:ℤ) n, f (h (π (i+1))) + f x := by abel
    _ = ∑ i ∈ Icc (1:ℤ) (j-1), f (h' i) + ∑ i ∈ Icc (j:ℤ) n, f (h' i) + f x := by
      congr 2
      all_goals apply sum_congr rfl _; intro i hi; simp [h'] at *
      . simp [show i < j by linarith]
      simp [show ¬ i < j by linarith]
    _ = _ := by congr; convert concat_finite_series _ _ _ <;> linarith
  rw [this]
  congr 1
  have g_ne_x {i:ℤ} (hi : i ∈ Icc (1:ℤ) n) : g (π i) ≠ x := by
    simp at hi
    simp [x, hg.injective.eq_iff, π, hi.1, show i ≤ n+1 by linarith]
    linarith
  have h'_ne_x {i:ℤ} (hi : i ∈ Icc (1:ℤ) n) : h' i ≠ x := by
    simp at hi
    have hi' : 0 ≤ i := by linarith
    have hi'' : i ≤ n+1 := by linarith
    by_cases hlt: i < j <;> by_contra! heq
    all_goals simp [h', hlt, ←hj, hh.injective.eq_iff, ←Subtype.val_inj,
                    π, hi.1, hi.2, hi',hi''] at heq
    . linarith
    contrapose! hlt; linarith
  set gtil : Icc (1:ℤ) n → X.erase x :=
    fun i ↦ ⟨ (g (π i)).val, by simp [mem_erase, g_ne_x] ⟩
  set htil : Icc (1:ℤ) n → X.erase x :=
    fun i ↦ ⟨ (h' i).val, by simp [mem_erase, h'_ne_x] ⟩
  set ftil : X.erase x → ℝ := fun y ↦ f y.val
  have why : Function.Bijective gtil := by
    have hg_inj : Function.Injective g := hg.injective
    have hg_surj : Function.Surjective g := hg.surjective
    refine ⟨?_, ?_⟩
    · intro a b h
      have hg_val_eq : (g (π a)).val = (g (π b)).val := by
        simpa [gtil] using congr_arg Subtype.val h
      have hg_eq : g (π a) = g (π b) := Subtype.ext hg_val_eq
      have hπ_eq : π a = π b := hg_inj hg_eq
      have h_val_eq : a.val = b.val := by
        have htemp := congr_arg Subtype.val hπ_eq
        have hπ_val (x : Icc (1:ℤ) n) : (π x).val = x.val := by
          dsimp [π]
          have hx_mem_np1 : x.val ∈ Icc (1:ℤ) (n+1) :=
            (Finset.Icc_subset_Icc_right (show (n : ℤ) ≤ (n+1 : ℤ) from by omega)) x.property
          simp [hx_mem_np1]
        calc
          a.val = (π a).val := (hπ_val a).symm
          _ = (π b).val := htemp
          _ = b.val := hπ_val b
      exact Subtype.ext h_val_eq
    · intro y
      have hyx_mem := Finset.mem_erase.mp y.property
      rcases hyx_mem with ⟨hyx, hy_mem_X⟩
      rcases hg_surj ⟨y.val, hy_mem_X⟩ with ⟨z, hz⟩
      have hz_val_eq : (g z).val = y.val := congr_arg Subtype.val hz
      have hz_not_np1 : z.val ≠ (n+1 : ℤ) := by
        intro h_eq
        apply hyx
        calc
          y.val = (g z).val := hz_val_eq.symm
          _ = (g (π (n+1))).val := by
            have : z = π (n+1) := Subtype.ext (by simpa [π] using h_eq)
            simp [this]
          _ = x.val := rfl
      have hz_mem_n : z.val ∈ Icc (1:ℤ) n := by
        have hz_mem_Icc := Finset.mem_Icc.mp z.property
        rcases hz_mem_Icc with ⟨hz1, hz2⟩
        have hz_val_le_n : z.val ≤ n := by
          by_contra! H
          have : z.val = (n+1 : ℤ) := by omega
          exact hz_not_np1 this
        exact Finset.mem_Icc.mpr ⟨hz1, hz_val_le_n⟩
      have hπz : π (z.val : ℤ) = z := by
        ext
        dsimp [π]
        have hmem : z.val ∈ Icc (1:ℤ) (n+1) := z.property
        simp [hmem]
      have h_π_eq : π (⟨z.val, hz_mem_n⟩ : Icc (1:ℤ) n) = z :=
        calc
          π (⟨z.val, hz_mem_n⟩ : Icc (1:ℤ) n) = π (z.val : ℤ) := by simp
          _ = z := hπz
      refine ⟨⟨z.val, hz_mem_n⟩, Subtype.ext ?_⟩
      dsimp [gtil]
      rw [h_π_eq]
      exact hz_val_eq
  have why2 : Function.Bijective htil := by
    have hh_inj : Function.Injective h := hh.injective
    have hh_surj : Function.Surjective h := hh.surjective
    have hmem_np1 (x : ℤ) (hx : x ∈ Icc (1:ℤ) n) : x ∈ Icc (1:ℤ) (n+1) :=
      (Finset.Icc_subset_Icc_right (show (n : ℤ) ≤ (n+1 : ℤ) from by omega)) hx
    have hπ_val_int {k : ℤ} (hk : k ∈ Icc (1:ℤ) (n+1)) : (π k).val = k := by
      dsimp [π]; simp [hk]
    have hπ_inj_on_np1 {k₁ k₂ : ℤ} (hk₁ : k₁ ∈ Icc (1:ℤ) (n+1)) (hk₂ : k₂ ∈ Icc (1:ℤ) (n+1))
        (hπ_eq : π k₁ = π k₂) : k₁ = k₂ := by
      simpa [hπ_val_int hk₁, hπ_val_int hk₂] using congr_arg Subtype.val hπ_eq
    refine ⟨?_, ?_⟩
    · intro a b hhtil
      have hh_val_eq : (h' a.val).val = (h' b.val).val := by
        simpa [htil] using congr_arg Subtype.val hhtil
      have hh_eq : h' a.val = h' b.val := Subtype.ext hh_val_eq
      have ha_mem_np1 : a.val ∈ Icc (1:ℤ) (n+1) := hmem_np1 a.val a.property
      have hb_mem_np1 : b.val ∈ Icc (1:ℤ) (n+1) := hmem_np1 b.val b.property
      have ha_succ_mem_np1 : a.val + 1 ∈ Icc (1:ℤ) (n+1) := by
        rcases Finset.mem_Icc.mp a.property with ⟨ha1, ha2⟩
        refine Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have hb_succ_mem_np1 : b.val + 1 ∈ Icc (1:ℤ) (n+1) := by
        rcases Finset.mem_Icc.mp b.property with ⟨hb1, hb2⟩
        refine Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      by_cases ha_lt_j : a.val < j
      · by_cases hb_lt_j : b.val < j
        · -- both < j
          have h_eq : h (π a.val) = h (π b.val) := by
            simpa [h', ha_lt_j, hb_lt_j] using hh_eq
          have hπ_eq : π a.val = π b.val := hh_inj h_eq
          exact Subtype.ext (hπ_inj_on_np1 (k₁ := a.val) (k₂ := b.val) ha_mem_np1 hb_mem_np1 hπ_eq)
        · -- a.val < j ≤ b.val : impossible
          have h_eq : h (π a.val) = h (π (b.val + 1)) := by
            simpa [h', ha_lt_j, hb_lt_j] using hh_eq
          have hπ_eq : π a.val = π (b.val + 1) := hh_inj h_eq
          have : a.val = b.val + 1 := hπ_inj_on_np1 (k₁ := a.val) (k₂ := b.val + 1) ha_mem_np1 hb_succ_mem_np1 hπ_eq
          omega
      · by_cases hb_lt_j : b.val < j
        · -- b.val < j ≤ a.val : impossible
          have h_eq : h (π (a.val + 1)) = h (π b.val) := by
            simpa [h', ha_lt_j, hb_lt_j] using hh_eq
          have hπ_eq : π (a.val + 1) = π b.val := hh_inj h_eq
          have : a.val + 1 = b.val := hπ_inj_on_np1 (k₁ := a.val + 1) (k₂ := b.val) ha_succ_mem_np1 hb_mem_np1 hπ_eq
          omega
        · -- both ≥ j
          have h_eq : h (π (a.val + 1)) = h (π (b.val + 1)) := by
            simpa [h', ha_lt_j, hb_lt_j] using hh_eq
          have hπ_eq : π (a.val + 1) = π (b.val + 1) := hh_inj h_eq
          have ha_val_eq_b_val : a.val = b.val := by
            have htemp := hπ_inj_on_np1 (k₁ := a.val + 1) (k₂ := b.val + 1) ha_succ_mem_np1 hb_succ_mem_np1 hπ_eq
            omega
          exact Subtype.ext ha_val_eq_b_val
    · intro y
      have hyx_mem := Finset.mem_erase.mp y.property
      rcases hyx_mem with ⟨hyx, hy_mem_X⟩
      rcases hh_surj ⟨y.val, hy_mem_X⟩ with ⟨z, hz⟩
      have hz_val_eq : (h z).val = y.val := congr_arg Subtype.val hz
      have hz_not_j : z.val ≠ j := by
        intro h_eq
        apply hyx
        calc
          y.val = (h z).val := hz_val_eq.symm
          _ = (h (π j)).val := by
            have hπj_val : (π j).val = j := by
              dsimp [π]
              simp [hj1, hj2]
            have : z = π j := Subtype.ext (h_eq.trans hπj_val.symm)
            simp [this]
          _ = x.val := by
            have hπj_eq : π j = ⟨j, hj'⟩ := Subtype.ext (by
              dsimp [π]; simp [hj1, hj2])
            simpa [hπj_eq, hj]
      have hπz : π z.val = z := by
        ext; dsimp [π]; simp
      by_cases hz_lt_j : z.val < j
      · have hz_mem_n : z.val ∈ Icc (1:ℤ) n := by
          rcases Finset.mem_Icc.mp z.property with ⟨hz1, hz2⟩
          have hz_val_le_n : z.val ≤ n := by
            by_contra! H
            have : z.val = (n+1 : ℤ) := by omega
            have : z.val = j := by omega
            exact hz_not_j this
          exact Finset.mem_Icc.mpr ⟨hz1, hz_val_le_n⟩
        have h'z : h' z.val = h z := by
          simp [h', hz_lt_j, hπz]
        refine ⟨⟨z.val, hz_mem_n⟩, Subtype.ext ?_⟩
        dsimp [htil]
        simp [h'z, hz_val_eq]
      · have hz_gt_j : j < z.val := by omega
        have hz_pred_mem_n : z.val - 1 ∈ Icc (1:ℤ) n := by
          rcases Finset.mem_Icc.mp z.property with ⟨hz1, hz2⟩
          have hz_pred_ge_one : 1 ≤ z.val - 1 := by
            have : 1 ≤ j := hj1
            omega
          have hz_pred_le_n : z.val - 1 ≤ n := by omega
          exact Finset.mem_Icc.mpr ⟨hz_pred_ge_one, hz_pred_le_n⟩
        have h'z_pred : h' (z.val - 1) = h z := by
          have h_not_lt : ¬ (z.val - 1 < j) := by omega
          simp [h', h_not_lt, hπz]
        refine ⟨⟨z.val - 1, hz_pred_mem_n⟩, Subtype.ext ?_⟩
        dsimp [htil]
        simp [h'z_pred, hz_val_eq]
  calc
    _ = ∑ i ∈ Icc (1:ℤ) n, if hi: i ∈ Icc (1:ℤ) n then ftil (gtil ⟨ i, hi ⟩ ) else 0 := by
      apply sum_congr rfl; grind
    _ = ∑ i ∈ Icc (1:ℤ) n, if hi: i ∈ Icc (1:ℤ) n then ftil (htil ⟨ i, hi ⟩ ) else 0 := by
      convert hn _ _ gtil htil why why2
      rw [Finset.card_erase_of_mem _, hX] <;> simp
    _ = _ := by apply sum_congr rfl; grind

/--
  This fact ensures that Definition 7.1.6 would be well-defined even if we did not appeal to the
  existing {name}`Finset.sum` method.
-/
theorem exist_bijection {n:ℕ} {Y:Type*} (X: Finset Y) (hcard: X.card = n) :
    ∃ g: Icc (1:ℤ) n → X, Function.Bijective g := by
  have := Finset.equivOfCardEq (show (Icc (1:ℤ) n).card = X.card by simp [hcard])
  exact ⟨ this, this.bijective ⟩

/-- Definition 7.1.6 -/
theorem finite_series_eq {n:ℕ} {Y:Type*} (X: Finset Y) (f: Y → ℝ) (g: Icc (1:ℤ) n → X)
  (hg: Function.Bijective g) :
    ∑ i ∈ X, f i = ∑ i ∈ Icc (1:ℤ) n, (if hi:i ∈ Icc (1:ℤ) n then f (g ⟨ i, hi ⟩) else 0) := by
  symm
  convert sum_bij (t:=X) (fun i hi ↦ g ⟨ i, hi ⟩ ) _ _ _ _
  . aesop
  . intro _ _ _ _ h; simpa [Subtype.val_inj, hg.injective.eq_iff] using h
  . intro b hb; have := hg.surjective ⟨ b, hb ⟩; grind
  intros; simp_all

/-- Proposition 7.1.11(a) / Exercise 7.1.2 -/
theorem finite_series_of_empty {X':Type*} (f: X' → ℝ) : ∑ i ∈ ∅, f i = 0 := by
  simp

/-- Proposition 7.1.11(b) / Exercise 7.1.2 -/
theorem finite_series_of_singleton {X':Type*} (f: X' → ℝ) (x₀:X') : ∑ i ∈ {x₀}, f i = f x₀ := by
  simp

/--
  A technical lemma relating a sum over a finset with a sum over a fintype. Combines well with
  tools such as `map_finite_series` below.
-/
theorem finite_series_of_fintype {X':Type*} (f: X' → ℝ) (X: Finset X') :
    ∑ x ∈ X, f x = ∑ x:X, f x.val := (sum_coe_sort X f).symm

/-- Proposition 7.1.11(c) / Exercise 7.1.2 -/
theorem map_finite_series {X:Type*} [Fintype X] [Fintype Y] (f: X → ℝ) {g:Y → X}
  (hg: Function.Bijective g) :
    ∑ x, f x = ∑ y, f (g y) := by
  simpa using (Finset.sum_equiv (Equiv.ofBijective g hg) (by simp) (by simp)).symm

-- Proposition 7.1.11(d) is `rfl` in our formalism and is therefore omitted.

/-- Proposition 7.1.11(e) / Exercise 7.1.2 -/
theorem finite_series_of_disjoint_union {Z:Type*} {X Y: Finset Z} (hdisj: Disjoint X Y) (f: Z → ℝ) :
    ∑ z ∈ X ∪ Y, f z = ∑ z ∈ X, f z + ∑ z ∈ Y, f z := by
  simp [Finset.sum_union, hdisj]

/-- Proposition 7.1.11(f) / Exercise 7.1.2 -/
theorem finite_series_of_add {X':Type*} (f g: X' → ℝ) (X: Finset X') :
    ∑ x ∈ X, (f + g) x = ∑ x ∈ X, f x + ∑ x ∈ X, g x := by
    simp [Finset.sum_add_distrib]

/-- Proposition 7.1.11(g) / Exercise 7.1.2 -/
theorem finite_series_of_const_mul {X':Type*} (f: X' → ℝ) (X: Finset X') (c:ℝ) :
    ∑ x ∈ X, c * f x = c * ∑ x ∈ X, f x := by
    simp [Finset.mul_sum]

/-- Proposition 7.1.11(h) / Exercise 7.1.2 -/
theorem finite_series_of_le' {X':Type*} (f g: X' → ℝ) (X: Finset X') (h: ∀ x ∈ X, f x ≤ g x) :
    ∑ x ∈ X, f x ≤ ∑ x ∈ X, g x := by
  exact Finset.sum_le_sum h

/-- Proposition 7.1.11(i) / Exercise 7.1.2 -/
theorem abs_finite_series_le' {X':Type*} (f: X' → ℝ) (X: Finset X') :
    |∑ x ∈ X, f x| ≤ ∑ x ∈ X, |f x| := Finset.abs_sum_le_sum_abs f X

/-- Lemma 7.1.13 --/
theorem finite_series_of_finite_series {XX YY:Type*} (X: Finset XX) (Y: Finset YY)
  (f: XX × YY → ℝ) :
    ∑ x ∈ X, ∑ y ∈ Y, f (x, y) = ∑ z ∈ X.product Y, f z := by
  generalize h: X.card = n
  revert X; induction' n with n hn
  . intro X hcard
    simp [Finset.card_eq_zero.mp hcard]
  intro X hX
  have hnon : X.Nonempty := by grind [card_ne_zero]
  choose x₀ hx₀ using hnon.exists_mem
  set X' := X.erase x₀
  have hcard : X'.card = n := by simp [X', card_erase_of_mem hx₀, hX]
  have hunion : X = X' ∪ {x₀} := by ext x; by_cases x = x₀ <;> grind
  have hdisj : Disjoint X' {x₀} := by simp [X']
  calc
    _ = ∑ x ∈ X', ∑ y ∈ Y, f (x, y) + ∑ x ∈ {x₀}, ∑ y ∈ Y, f (x, y) := by
      convert finite_series_of_disjoint_union hdisj _
    _ = ∑ x ∈ X', ∑ y ∈ Y, f (x, y) + ∑ y ∈ Y, f (x₀, y) := by
      rw [finite_series_of_singleton]
    _ = ∑ z ∈ X'.product Y, f z + ∑ y ∈ Y, f (x₀, y) := by rw [hn X' hcard]
    _ = ∑ z ∈ X'.product Y, f z + ∑ z ∈ .product {x₀} Y, f z := by
      congr 1
      rw [finite_series_of_fintype, finite_series_of_fintype f]
      set π : Finset.product {x₀} Y → Y :=
        fun z ↦ ⟨ z.val.2, by obtain ⟨ z, hz ⟩ := z; simp at hz ⊢; grind ⟩
      have hπ : Function.Bijective π := by
        constructor
        . intro ⟨ ⟨ x, y ⟩, hz ⟩ ⟨ ⟨ x', y' ⟩, hz' ⟩ hzz'; simp [π] at hz hz' hzz' ⊢; grind
        intro ⟨ y, hy ⟩; use ⟨ (x₀, y), by simp [hy] ⟩
      convert map_finite_series _ hπ with z
      obtain ⟨⟨x, y⟩, hz ⟩ := z
      simp at hz ⊢; grind
    _ = _ := by
      symm; convert finite_series_of_disjoint_union _ _
      . rw [hunion]; ext ⟨x, y⟩; simp [Finset.mem_union, Finset.mem_product]; tauto
      . apply Finset.disjoint_product.mpr; left; exact hdisj

/-- Corollary 7.1.14 (Fubini's theorem for finite series)-/
theorem finite_series_refl {XX YY:Type*} (X: Finset XX) (Y: Finset YY) (f: XX × YY → ℝ) :
    ∑ z ∈ X.product Y, f z = ∑ z ∈ Y.product X, f (z.2, z.1) := by
  set h : Y.product X → X.product Y :=
    fun z ↦ ⟨ (z.val.2, z.val.1), by obtain ⟨ z, hz ⟩ := z; simp at hz ⊢; tauto ⟩
  have hh : Function.Bijective h := by
    constructor
    . intro ⟨ ⟨ _, _ ⟩, _ ⟩ ⟨ ⟨ _, _ ⟩, _ ⟩ _
      simp_all [h]
    intro ⟨ z, hz ⟩; simp at hz
    use ⟨ (z.2, z.1), by simp [hz] ⟩
  rw [finite_series_of_fintype]
  nth_rewrite 2 [finite_series_of_fintype]
  convert map_finite_series _ hh with z

theorem finite_series_comm {XX YY:Type*} (X: Finset XX) (Y: Finset YY) (f: XX × YY → ℝ) :
    ∑ x ∈ X, ∑ y ∈ Y, f (x, y) = ∑ y ∈ Y, ∑ x ∈ X, f (x, y) := by
  rw [finite_series_of_finite_series, finite_series_refl,
      finite_series_of_finite_series _ _ (fun z ↦ f (z.2, z.1))]


-- Exercise 7.1.3 : develop as many analogues as you can of the above theory for finite products
-- instead of finite sums.

#check Nat.factorial_zero
#check Nat.factorial_succ

/--
  Exercise 7.1.4. Note: there may be some technicalities passing back and forth between natural
  numbers and integers. Look into the tactics {tactic}`zify`, {tactic}`norm_cast`, and {tactic}`omega`
-/
theorem binomial_theorem (x y:ℝ) (n:ℕ) :
    (x + y)^n
    = ∑ j ∈ Icc (0:ℤ) n,
    n.factorial / (j.toNat.factorial * (n-j).toNat.factorial) * x^j * y^(n - j) := by
  rw [add_pow x y n]
  have hIcc : Icc (0 : ℤ) (n : ℤ) = map ((Nat.castEmbedding (R := ℤ)).trans (addLeftEmbedding (0 : ℤ))) (range (n + 1)) := by
    simpa using Int.Icc_eq_finset_map (0 : ℤ) (n : ℤ)
  rw [hIcc, Finset.sum_map]
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hk_range : k < n + 1 := Finset.mem_range.1 hk
  have hk_le_n : k ≤ n := by omega
  have h_embed : ((Nat.castEmbedding (R := ℤ)).trans (addLeftEmbedding (0 : ℤ))) k = (k : ℤ) := by simp
  have hy_eq : y ^ (n - k) = y ^ ((n : ℤ) - (k : ℤ)) := by
    calc
      y ^ (n - k) = y ^ (((n - k : ℕ) : ℤ)) := by simp
      _ = y ^ ((n : ℤ) - (k : ℤ)) := by simp [Nat.cast_sub hk_le_n]
  calc
    x ^ k * y ^ (n - k) * (Nat.choose n k : ℝ)
        = x ^ k * y ^ (n - k) * ((n.factorial : ℝ) / ((k.factorial : ℝ) * ((n - k).factorial : ℝ))) := by
          rw [Nat.cast_choose ℝ hk_le_n]
    _ = ((n.factorial : ℝ) / ((k.factorial : ℝ) * ((n - k).factorial : ℝ))) * x ^ k * y ^ (n - k) := by ring
    _ = ((n.factorial : ℝ) / ((k.factorial : ℝ) * ((n - k).factorial : ℝ))) * x ^ k * y ^ ((n : ℤ) - (k : ℤ)) := by
      rw [hy_eq]
    _ = (n.factorial : ℝ) / (((k : ℤ).toNat.factorial : ℝ) * (((n : ℤ) - (k : ℤ)).toNat.factorial : ℝ)) * x ^ (k : ℤ) * y ^ ((n : ℤ) - (k : ℤ)) := by
      simp
  simp [h_embed]

/-- Exercise 7.1.5 -/
theorem lim_of_finite_series {X:Type*} [Fintype X] (a: X → ℕ → ℝ) (L : X → ℝ)
  (h: ∀ x, Filter.atTop.Tendsto (a x) (nhds (L x))) :
    Filter.atTop.Tendsto (fun n ↦ ∑ x, a x n) (nhds (∑ x, L x)) := by
  simpa using tendsto_finset_sum (s := Finset.univ) (f := fun x n => a x n) (a := L)
    (by intro x _; exact h x)

/-- Exercise 7.1.6 -/
theorem sum_union_disjoint {n : ℕ} {S : Type*} [Fintype S]
    (E : Fin n → Finset S)
    (disj : ∀ i j : Fin n, i ≠ j → Disjoint (E i) (E j))
    (cover : ∀ s : S, ∃ i, s ∈ E i)
    (f : S → ℝ) :
    ∑ s, f s = ∑ i, ∑ s ∈ E i, f s := by
  classical
    have huniv : (Finset.univ : Finset S) = (Finset.univ : Finset (Fin n)).biUnion E := by
      ext s
      constructor
      · intro hs
        rcases cover s with ⟨i, hi⟩
        apply Finset.mem_biUnion.mpr
        exact ⟨i, Finset.mem_univ _, hi⟩
      · intro h
        rcases Finset.mem_biUnion.mp h with ⟨i, _, hi⟩
        exact Finset.mem_univ _
    have hdisj : ((Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint E := by
      intro i hi j hj hne
      exact disj i j hne
    calc
      ∑ s, f s = ∑ s ∈ Finset.univ, f s := by simp
      _ = ∑ s ∈ (Finset.univ : Finset (Fin n)).biUnion E, f s := by rw [huniv]
      _ = ∑ i ∈ Finset.univ, ∑ s ∈ E i, f s := by
        rw [Finset.sum_biUnion hdisj]
      _ = ∑ i, ∑ s ∈ E i, f s := by simp

/-- {given}`aᵢ` Exercise 7.1.7. Uses {lean}`Fin m` (so {lean}`aᵢ < m`) instead of the book's {lean}`aᵢ ≤ m`;
  the bound is baked into the type, and {kw (of := «term_<_»)}`<` replaces {kw (of := «term_≤_»)}`≤` to match the 0-indexed shift. -/
theorem sum_finite_col_row_counts {n m : ℕ} (a : Fin n → Fin m) :
    ∑ i, (a i : ℕ) = ∑ j : Fin m, {i : Fin n | j < a i}.toFinset.card := by
  classical
  calc
    ∑ i, (a i : ℕ) = ∑ i, (Finset.Iio (a i)).card := by
      simp [Fin.card_Iio]
    _ = ∑ i, (Finset.filter (λ j : Fin m => j < a i) Finset.univ).card := by
      simp [Finset.filter_gt_eq_Iio]
    _ = ∑ i, ∑ j : Fin m, if j < a i then (1 : ℕ) else 0 := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.card_filter]
    _ = ∑ j : Fin m, ∑ i, if j < a i then (1 : ℕ) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ j : Fin m, (Finset.filter (λ i : Fin n => j < a i) Finset.univ).card := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [← Finset.card_filter]
    _ = ∑ j : Fin m, ({i : Fin n | j < a i}.toFinset : Finset (Fin n)).card := by
      simp

end Finset
