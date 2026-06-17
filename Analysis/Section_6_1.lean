import Mathlib.Tactic
import Analysis.Section_5_1
import Analysis.Section_5_3
import Analysis.Section_5_epilogue

/-!
# Analysis I, Section 6.1: Convergence and limit laws

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of $`ε`-closeness, $`ε`-steadiness, and their eventual counterparts.
- Notion of a Cauchy sequence, convergent sequence, and bounded sequence of reals.

-/


/- Definition 6.1.1 (Distance).  Here we use the Mathlib distance. -/
-- #check Real.dist_eq

abbrev Real.Close (ε x y : ℝ) : Prop := dist x y ≤ ε

/--
  Definition 6.1.2 (ε-close). This is similar to the previous notion of ε-closeness, but where
  all quantities are real instead of rational.
-/
theorem Real.close_def (ε x y : ℝ) : ε.Close x y ↔ dist x y ≤ ε := by rfl

namespace Chapter6

/--
  Definition 6.1.3 (Sequence). This is similar to the Chapter 5 sequence, except that now the
  sequence is real-valued. As with Chapter 5, we start sequences from 0 by default.
-/
@[ext]
structure Sequence where
  m : ℤ
  seq : ℤ → ℝ
  vanish : ∀ n < m, seq n = 0

/-- Sequences can be thought of as functions from {lean}`ℤ` to {lean}`ℝ`. -/
instance Sequence.instCoeFun : CoeFun Sequence (fun _ ↦ ℤ → ℝ) where
  coe a := a.seq

@[coe]
abbrev Sequence.ofNatFun (a:ℕ → ℝ) : Sequence :=
 {
    m := 0
    seq n := if n ≥ 0 then a n.toNat else 0
    vanish := by simp_all
 }

/-- Functions from {lean}`ℕ` to {lean}`ℝ` can be thought of as sequences. -/
instance Sequence.instCoe : Coe (ℕ → ℝ) Sequence where
  coe := ofNatFun

abbrev Sequence.mk' (m:ℤ) (a: { n // n ≥ m } → ℝ) : Sequence where
  m := m
  seq n := if h : n ≥ m then a ⟨n, h⟩ else 0
  vanish := by simp_all

lemma Sequence.eval_mk {n m:ℤ} (a: { n // n ≥ m } → ℝ) (h: n ≥ m) :
    (Sequence.mk' m a) n = a ⟨ n, h ⟩ := by simp [h]

@[simp]
lemma Sequence.eval_coe (n:ℕ) (a: ℕ → ℝ) : (a:Sequence) n = a n := by simp

/--
  {given -show}`n₁, n₀`
  {lean}`a.from n₁` starts {lean}`a : Sequence` from {name}`n₁`.  It is intended for use when {lean}`n₁ ≥ n₀`, but returns
  the "junk" value of the original sequence {name}`a` otherwise.
-/
abbrev Sequence.from (a:Sequence) (m₁:ℤ) : Sequence := mk' (max a.m m₁) (a ↑·)

lemma Sequence.from_eval (a:Sequence) {m₁ n:ℤ} (hn: n ≥ m₁) :
  (a.from m₁) n = a n := by
  simp [hn]; intros; symm; solve_by_elim [a.vanish]

end Chapter6

/-- Definition 6.1.3 (ε-steady) -/
abbrev Real.Steady (ε: ℝ) (a: Chapter6.Sequence) : Prop :=
  ∀ n ≥ a.m, ∀ m ≥ a.m, ε.Close (a n) (a m)

/-- Definition 6.1.3 (ε-steady) -/
lemma Real.steady_def (ε: ℝ) (a: Chapter6.Sequence) :
  ε.Steady a ↔ ∀ n ≥ a.m, ∀ m ≥ a.m, ε.Close (a n) (a m) := by rfl

/-- Definition 6.1.3 (Eventually ε-steady) -/
abbrev Real.EventuallySteady (ε: ℝ) (a: Chapter6.Sequence) : Prop :=
  ∃ N ≥ a.m, ε.Steady (a.from N)

/-- Definition 6.1.3 (Eventually ε-steady) -/
lemma Real.eventuallySteady_def (ε: ℝ) (a: Chapter6.Sequence) :
  ε.EventuallySteady a ↔ ∃ N, (N ≥ a.m) ∧ ε.Steady (a.from N) := by rfl

/-- For fixed {name}`a`, the function `ε ↦ ε.Steady s` is monotone -/
theorem Real.Steady.mono {a: Chapter6.Sequence} {ε₁ ε₂: ℝ} (hε: ε₁ ≤ ε₂) (hsteady: ε₁.Steady a) :
    ε₂.Steady a := by grind

/-- For fixed {name}`a`, the function `ε ↦ ε.EventuallySteady s` is monotone -/
theorem Real.EventuallySteady.mono {a: Chapter6.Sequence} {ε₁ ε₂: ℝ} (hε: ε₁ ≤ ε₂)
  (hsteady: ε₁.EventuallySteady a) :
    ε₂.EventuallySteady a := by peel 2 hsteady; grind [Steady.mono]

namespace Chapter6

/-- Definition 6.1.3 (Cauchy sequence) -/
abbrev Sequence.IsCauchy (a:Sequence) : Prop := ∀ ε > (0:ℝ), ε.EventuallySteady a

/-- Definition 6.1.3 (Cauchy sequence) -/
lemma Sequence.isCauchy_def (a:Sequence) :
  a.IsCauchy ↔ ∀ ε > (0:ℝ), ε.EventuallySteady a := by rfl

/-- This is almost the same as {name}`Chapter5.Sequence.IsCauchy.coe` -/
lemma Sequence.IsCauchy.coe (a:ℕ → ℝ) :
    (a:Sequence).IsCauchy ↔ ∀ ε > 0, ∃ N, ∀ j ≥ N, ∀ k ≥ N, dist (a j) (a k) ≤ ε := by
  peel with ε hε
  constructor
  · rintro ⟨ N, hN, h' ⟩
    lift N to ℕ using hN; use N
    intro j hj k hk
    simp [Real.steady_def] at h'
    specialize h' j ?_ k ?_ <;> try omega
    simp_all
  rintro ⟨ N, h' ⟩; refine ⟨ max N 0, by simp, ?_ ⟩
  intro n hn m hm; simp at hn hm
  have npos : 0 ≤ n := by omega
  have mpos : 0 ≤ m := by omega
  simp [hn, hm, npos, mpos]
  lift n to ℕ using npos
  lift m to ℕ using mpos
  specialize h' n ?_ m ?_ <;> try grind

lemma Sequence.IsCauchy.mk {n₀:ℤ} (a: {n // n ≥ n₀} → ℝ) :
    (mk' n₀ a).IsCauchy
    ↔ ∀ ε > 0, ∃ N ≥ n₀, ∀ j ≥ N, ∀ k ≥ N, dist (mk' n₀ a j) (mk' n₀ a k) ≤ ε := by
  peel with ε hε
  constructor
  · rintro ⟨ N, hN, h' ⟩; refine ⟨ N, hN, ?_ ⟩
    dsimp at hN
    intro j hj k hk
    simp only [Real.Steady, show max n₀ N = N by omega] at h'
    specialize h' j ?_ k ?_ <;> try omega
    simp_all [show n₀ ≤ j by omega, show n₀ ≤ k by omega]
  rintro ⟨ N, _, _ ⟩; use max n₀ N; grind

@[coe]
abbrev Sequence.ofChapter5Sequence (a: Chapter5.Sequence) : Sequence :=
{
  m := a.n₀
  seq n := a n
  vanish n hn := by simp [a.vanish n hn]
}

instance Chapter5.Sequence.inst_coe_sequence : Coe Chapter5.Sequence Sequence where
  coe := Sequence.ofChapter5Sequence

@[simp]
theorem Chapter5.coe_sequence_eval (a: Chapter5.Sequence) (n:ℤ) : (a:Sequence) n = (a n:ℝ) := rfl

theorem Sequence.is_steady_of_rat (ε:ℚ) (a: Chapter5.Sequence) :
    ε.Steady a ↔ (ε:ℝ).Steady (a:Sequence) := by
  peel with Z hZ
  constructor
  · intro h m hm
    specialize h m hm
    rw [Real.close_def, Real.dist_eq, ← Rat.cast_sub, ← Rat.cast_abs, Rat.cast_le]
    exact h
  intro h m hm
  specialize h m hm
  rw [Rat.Close]
  rw [Real.close_def, Real.dist_eq, ← Rat.cast_sub, ← Rat.cast_abs, Rat.cast_le] at h
  exact h

theorem Sequence.is_eventuallySteady_of_rat (ε:ℚ) (a: Chapter5.Sequence) :
    ε.EventuallySteady a ↔ (ε:ℝ).EventuallySteady (a:Sequence) := by
  peel with Z hZ
  constructor
  · intro hsteady N hN M hM
    specialize hsteady N hN M hM
    simp at hM hN
    rw [Real.close_def, Real.dist_eq, Sequence.from_eval _ hN.2, Sequence.from_eval _ hM.2, ← Rat.cast_sub, ← Rat.cast_abs, Rat.cast_le]
    rw [Rat.Close, Chapter5.Sequence.from_eval _ hN.2, Chapter5.Sequence.from_eval _ hM.2] at hsteady
    exact hsteady
  · intro hsteady N hN M hM
    specialize hsteady N hN M hM
    simp at hM hN
    rw [Real.close_def, Real.dist_eq, Sequence.from_eval _ hN.2, Sequence.from_eval _ hM.2, ← Rat.cast_sub, ← Rat.cast_abs, Rat.cast_le] at hsteady
    rw [Rat.Close, Chapter5.Sequence.from_eval _ hN.2, Chapter5.Sequence.from_eval _ hM.2]
    exact hsteady

/-- Proposition 6.1.4 -/
theorem Sequence.isCauchy_of_rat (a: Chapter5.Sequence) : a.IsCauchy ↔ (a:Sequence).IsCauchy := by
  -- This proof is written to follow the structure of the original text.
  constructor
  · intro h
    rw [Chapter5.Sequence.isCauchy_def] at h
    rw [isCauchy_def]
    intro ε hε
    choose ε' hε' hlt using exists_pos_rat_lt hε
    specialize h ε' hε'
    rw [is_eventuallySteady_of_rat] at h
    exact h.mono (le_of_lt hlt)
  . intro h; rw [isCauchy_def] at h
    rw [Chapter5.Sequence.isCauchy_def]
    intro ε hε
    specialize h ε (by positivity)
    rwa [is_eventuallySteady_of_rat]

end Chapter6

/-- Definition 6.1.5 -/
abbrev Real.CloseSeq (ε: ℝ) (a: Chapter6.Sequence) (L:ℝ) : Prop := ∀ n ≥ a.m, ε.Close (a n) L

/-- Definition 6.1.5 -/
theorem Real.closeSeq_def (ε: ℝ) (a: Chapter6.Sequence) (L:ℝ) :
  ε.CloseSeq a L ↔ ∀ n ≥ a.m, dist (a n) L ≤ ε := by rfl

/-- Definition 6.1.5 -/
abbrev Real.EventuallyClose (ε: ℝ) (a: Chapter6.Sequence) (L:ℝ) : Prop :=
  ∃ N ≥ a.m, ε.CloseSeq (a.from N) L

/-- Definition 6.1.5 -/
theorem Real.eventuallyClose_def (ε: ℝ) (a: Chapter6.Sequence) (L:ℝ) :
  ε.EventuallyClose a L ↔ ∃ N, (N ≥ a.m) ∧ ε.CloseSeq (a.from N) L := by rfl

theorem Real.CloseSeq.coe (ε : ℝ) (a : ℕ → ℝ) (L : ℝ):
  (ε.CloseSeq a L) ↔ ∀ n, dist (a n) L ≤ ε := by
  constructor
  . intro h n; specialize h n; grind
  . intro h n hn; lift n to ℕ using (by omega); specialize h n; grind

theorem Real.CloseSeq.mono {a: Chapter6.Sequence} {ε₁ ε₂ L: ℝ} (hε: ε₁ ≤ ε₂)
  (hclose: ε₁.CloseSeq a L) :
    ε₂.CloseSeq a L := by peel 2 hclose; rw [Real.Close, Real.dist_eq] at *; linarith

theorem Real.EventuallyClose.mono {a: Chapter6.Sequence} {ε₁ ε₂ L: ℝ} (hε: ε₁ ≤ ε₂)
  (hclose: ε₁.EventuallyClose a L) :
    ε₂.EventuallyClose a L := by peel 2 hclose; grind [CloseSeq.mono]
namespace Chapter6

abbrev Sequence.TendsTo (a:Sequence) (L:ℝ) : Prop :=
  ∀ ε > (0:ℝ), ε.EventuallyClose a L

theorem Sequence.tendsTo_def (a:Sequence) (L:ℝ) :
  a.TendsTo L ↔ ∀ ε > (0:ℝ), ε.EventuallyClose a L := by rfl

/-- Exercise 6.1.2 -/
theorem Sequence.tendsTo_iff (a:Sequence) (L:ℝ) :
  a.TendsTo L ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - L| ≤ ε := by
  constructor
  · intro h ε hε
    obtain ⟨N, hN, hclose⟩ := h ε hε
    use N; intro n hn
    have hn' : n ≥ (a.from N).m := by unfold Sequence.from; simp; omega
    specialize hclose n hn'
    rw [Real.close_def, Sequence.from_eval _ (show n ≥ N from hn), Real.dist_eq] at hclose
    exact hclose
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨max a.m N, le_max_left _ _, ?_⟩
    intro n hn
    have hn_N : n ≥ max a.m N := by
      unfold Sequence.from Sequence.mk' at hn; simp at hn; omega
    rw [Real.close_def, Sequence.from_eval _ (show n ≥ max a.m N from hn_N), Real.dist_eq]
    exact hN n (by omega)

noncomputable def seq_6_1_6 : Sequence := (fun (n:ℕ) ↦ 1-(10:ℝ)^(-(n:ℤ)-1):Sequence)

/-- Examples 6.1.6 -/
example : (0.1:ℝ).CloseSeq seq_6_1_6 1 := by
  rw [seq_6_1_6, Real.CloseSeq.coe]
  intro n
  rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by
    rw [sub_nonneg]
    rw (occs := .pos [2]) [show (1:ℝ) = 1 - 0 by norm_num]
    gcongr
    positivity
  ), sub_sub_cancel, show (0.1:ℝ) = (10:ℝ)^(-1:ℤ) by norm_num]
  gcongr <;> grind


/-- Examples 6.1.6 -/
example : ¬ (0.01:ℝ).CloseSeq seq_6_1_6 1 := by
  intro h; specialize h 0 (by positivity); simp [seq_6_1_6] at h; norm_num at h

/-- Examples 6.1.6 -/
example : (0.01:ℝ).EventuallyClose seq_6_1_6 1 := by
  refine ⟨1, by simp [seq_6_1_6], ?_⟩
  rw [Real.closeSeq_def]
  intro n hn
  simp [seq_6_1_6] at hn ⊢
  have hn' : n ≥ 1 := by omega
  simp [hn', show (0:ℤ) ≤ n by omega]
  rw [show (0.01:ℝ) = (10:ℝ)^(-2:ℤ) by norm_num]
  gcongr
  · norm_num
  · omega

/-- Examples 6.1.6 -/
example : seq_6_1_6.TendsTo 1 := by
  rw [Sequence.tendsTo_iff, seq_6_1_6]
  intro ε hε
  have h10' : (10:ℝ)⁻¹ < 1 := by norm_num
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε h10'
  refine ⟨(k:ℤ), fun n hn => ?_⟩
  simp [show (0:ℤ) ≤ n by omega]
  show (10:ℝ) ^ (-n - 1) ≤ ε
  calc (10:ℝ) ^ (-n - 1)
      ≤ (10:ℝ) ^ (-(k:ℤ)) := by
        gcongr
        · norm_num
        · omega
    _ = (10:ℝ)⁻¹ ^ k := by
        rw [zpow_neg, zpow_natCast, inv_pow]
    _ ≤ ε := le_of_lt hk

/-- Proposition 6.1.7 (Uniqueness of limits) -/
theorem Sequence.tendsTo_unique (a:Sequence) {L L':ℝ} (h:L ≠ L') :
    ¬ (a.TendsTo L ∧ a.TendsTo L') := by
  -- This proof is written to follow the structure of the original text.
  by_contra this
  choose hL hL' using this
  replace h : L - L' ≠ 0 := by grind
  replace h : |L-L'| > 0 := by positivity
  set ε := |L-L'| / 3
  have hε : ε > 0 := by positivity
  rw [tendsTo_iff] at hL hL'
  specialize hL ε hε; choose N hN using hL
  specialize hL' ε hε; choose M hM using hL'
  set n := max N M
  specialize hN n (by omega)
  specialize hM n (by omega)
  have : |L-L'| ≤ 2 * |L-L'|/3 := calc
    _ = dist L L' := by rw [Real.dist_eq]
    _ ≤ dist L (a.seq n) + dist (a.seq n) L' := dist_triangle _ _ _
    _ ≤ ε + ε := by rw [←Real.dist_eq] at hN hM; rw [dist_comm] at hN; gcongr
    _ = 2 * |L-L'|/3 := by grind
  linarith

/-- Definition 6.1.8 -/
abbrev Sequence.Convergent (a:Sequence) : Prop := ∃ L, a.TendsTo L

/-- Definition 6.1.8 -/
theorem Sequence.convergent_def (a:Sequence) : a.Convergent ↔ ∃ L, a.TendsTo L := by rfl

/-- Definition 6.1.8 -/
abbrev Sequence.Divergent (a:Sequence) : Prop := ¬ a.Convergent

/-- Definition 6.1.8 -/
theorem Sequence.divergent_def (a:Sequence) : a.Divergent ↔ ¬ a.Convergent := by rfl

open Classical in
/--
  Definition 6.1.8.  We give the limit of a sequence the junk value of {lean}`0` if it is not convergent.
-/
noncomputable abbrev lim (a:Sequence) : ℝ := if h: a.Convergent then h.choose else 0

/-- Definition 6.1.8 -/
theorem Sequence.lim_def {a:Sequence} (h: a.Convergent) : a.TendsTo (lim a) := by
  simp [lim, h]; exact h.choose_spec

/-- Definition 6.1.8-/
theorem Sequence.lim_eq {a:Sequence} {L:ℝ} :
a.TendsTo L ↔ a.Convergent ∧ lim a = L := by
  constructor
  . intro h; by_contra! eq
    have : a.Convergent := by rw [convergent_def]; use L
    replace eq := a.tendsTo_unique (eq this)
    apply lim_def at this; tauto
  intro ⟨ h, rfl ⟩; convert lim_def h


/-- Proposition 6.1.11 -/
theorem Sequence.lim_harmonic :
    ((fun (n:ℕ) ↦ (n+1:ℝ)⁻¹):Sequence).Convergent ∧ lim ((fun (n:ℕ) ↦ (n+1:ℝ)⁻¹):Sequence) = 0 := by
  -- This proof is written to follow the structure of the original text.
  rw [←lim_eq, tendsTo_iff]
  intro ε hε
  choose N hN using exists_int_gt (1 / ε); use N; intro n hn
  have hNpos : (N:ℝ) > 0 := by apply LT.lt.trans _ hN; positivity
  simp at hNpos
  have hnpos : n ≥ 0 := by linarith
  simp [hnpos, abs_inv]
  calc
    _ ≤ (N:ℝ)⁻¹ := by
      rw [inv_le_inv₀] <;> try positivity
      calc
        _ ≤ (n:ℝ) := by simp [hn]
        _ = (n.toNat:ℤ) := by simp [hnpos]
        _ = n.toNat := rfl
        _ ≤ (n.toNat:ℝ) + 1 := by linarith
        _ ≤ _ := le_abs_self _
    _ ≤ ε := by
      rw [inv_le_comm₀] <;> try positivity
      rw [←inv_eq_one_div _] at hN; order

/-- Proposition 6.1.12 / Exercise 6.1.5 -/
theorem Sequence.IsCauchy.convergent {a:Sequence} (h:a.Convergent) : a.IsCauchy := by
  rcases h with ⟨L, hL⟩
  rw [isCauchy_def]
  intro ε hε
  have hε2 : ε / 2 > 0 := by linarith
  rw [tendsTo_iff] at hL
  rcases hL (ε / 2) hε2 with ⟨N, hN⟩
  refine ⟨max a.m N, le_max_left _ _, ?_⟩
  intro n hn m hm
  have hn_max : n ≥ max a.m N := by
    simpa [max_eq_right (le_max_left a.m N)] using hn
  have hm_max : m ≥ max a.m N := by
    simpa [max_eq_right (le_max_left a.m N)] using hm
  have hnN : n ≥ N := by omega
  have hmN : m ≥ N := by omega
  rw [Real.close_def, Sequence.from_eval _ hn_max, Sequence.from_eval _ hm_max, Real.dist_eq]
  calc
    |a n - a m| = |(a n - L) - (a m - L)| := by
      have : (a n - L) - (a m - L) = a n - a m := by ring
      simp [this]
    _ ≤ |a n - L| + |a m - L| := abs_sub _ _
    _ ≤ ε / 2 + ε / 2 := by
      gcongr
      · exact hN n hnN
      · exact hN m hmN
    _ = ε := by ring

/-- Example 6.1.13 -/
private theorem not_01_EventuallySteady_neg_one_pow : ¬ (0.1:ℝ).EventuallySteady ((fun n ↦ (-1:ℝ)^n):Sequence) := by
  intro h
  rcases h with ⟨N, hN, hsteady⟩
  lift N to ℕ using hN
  have hfrom : ((fun n : ℕ ↦ (-1 : ℝ)^n : Sequence).from (N : ℤ)).m = (N : ℤ) := by
    simp
  have hclose : (0.1 : ℝ).Close (((fun n : ℕ ↦ (-1 : ℝ)^n : Sequence).from (N : ℤ)) (N : ℤ))
      (((fun n : ℕ ↦ (-1 : ℝ)^n : Sequence).from (N : ℤ)) ((N : ℤ) + 1)) :=
    hsteady (N : ℤ) (by rw [hfrom]) ((N : ℤ) + 1) (by rw [hfrom]; omega)
  have hN_eval : ((fun n : ℕ ↦ (-1 : ℝ)^n : Sequence).from (N : ℤ)) (N : ℤ) = ((fun n : ℕ ↦ (-1 : ℝ)^n : Sequence)) (N : ℤ) :=
    Sequence.from_eval ((fun n : ℕ ↦ (-1 : ℝ)^n : Sequence)) (le_refl (N : ℤ))
  have hNp1_eval : ((fun n : ℕ ↦ (-1 : ℝ)^n : Sequence).from (N : ℤ)) ((N : ℤ) + 1) = ((fun n : ℕ ↦ (-1 : ℝ)^n : Sequence)) ((N : ℤ) + 1) :=
    Sequence.from_eval ((fun n : ℕ ↦ (-1 : ℝ)^n : Sequence)) (by omega)
  rw [hN_eval, hNp1_eval] at hclose
  have hN_val : ((fun n : ℕ ↦ (-1 : ℝ)^n : Sequence)) (N : ℤ) = (-1 : ℝ) ^ N := by
    simp
  have hNp1_val : ((fun n : ℕ ↦ (-1 : ℝ)^n : Sequence)) ((N : ℤ) + 1) = (-1 : ℝ) ^ (N + 1) := by
    have hpos : (N : ℤ) + 1 ≥ 0 := by omega
    simp [hpos]
  rw [hN_val, hNp1_val] at hclose
  rw [Real.Close, Real.dist_eq] at hclose
  have hpowsucc : (-1 : ℝ) ^ (N + 1) = -((-1 : ℝ) ^ N) := by
    simp [pow_succ, mul_comm]
  rw [hpowsucc] at hclose
  have hcalc : ((-1 : ℝ) ^ N - (-((-1 : ℝ) ^ N))) = 2 * ((-1 : ℝ) ^ N) := by ring
  rw [hcalc] at hclose
  have habs : |(2 : ℝ) * ((-1 : ℝ) ^ N)| = (2 : ℝ) := by
    calc
      |(2 : ℝ) * ((-1 : ℝ) ^ N)| = |(2 : ℝ)| * |((-1 : ℝ) ^ N)| := by rw [abs_mul]
      _ = (2 : ℝ) * |((-1 : ℝ) ^ N)| := by norm_num
      _ = (2 : ℝ) * (|(-1 : ℝ)| ^ N) := by rw [abs_pow]
      _ = (2 : ℝ) * ((1 : ℝ) ^ N) := by norm_num
      _ = (2 : ℝ) * 1 := by simp
      _ = (2 : ℝ) := by norm_num
  rw [habs] at hclose
  linarith

/-- Example 6.1.13 -/
example : ¬ ((fun n ↦ (-1:ℝ)^n):Sequence).IsCauchy := by
  intro h
  apply not_01_EventuallySteady_neg_one_pow
  exact h 0.1 (by norm_num)

/-- Example 6.1.13 -/
example : ¬ ((fun n ↦ (-1:ℝ)^n):Sequence).Convergent := by
  intro hconv
  rcases hconv with ⟨L, hL⟩
  rw [Sequence.tendsTo_iff] at hL
  have h05 : (0.5 : ℝ) > 0 := by norm_num
  rcases hL (0.5 : ℝ) h05 with ⟨N, hN⟩
  set N' := max N 0 with hN'def
  have hN'0 : (N' : ℤ) ≥ 0 := le_max_right _ _
  have hN'N : (N' : ℤ) ≥ N := le_max_left _ _
  have hzpow_pow {a : ℝ} {n : ℤ} (hn : n ≥ 0) : a ^ (n : ℤ) = a ^ (n.toNat : ℕ) := by
    calc
      a ^ (n : ℤ) = a ^ ((n.toNat : ℤ) : ℤ) := by rw [show (n.toNat : ℤ) = n from by omega]
      _ = a ^ (n.toNat : ℕ) := by rw [zpow_natCast]
  have ha_eval (n : ℤ) (hn : n ≥ 0) : ((fun n : ℕ ↦ (-1 : ℝ) ^ n : Sequence)) n = (-1 : ℝ) ^ (n : ℤ) := by
    dsimp [Sequence.instCoe, Sequence.ofNatFun]
    simp [hn]
    exact (hzpow_pow hn).symm
  have hN_bound : |((-1 : ℝ) ^ (N' : ℤ)) - L| ≤ (0.5 : ℝ) := by
    rw [← ha_eval (N' : ℤ) hN'0]; exact hN (N' : ℤ) hN'N
  have hNp1_bound : |((-1 : ℝ) ^ ((N' : ℤ) + 1 : ℤ)) - L| ≤ (0.5 : ℝ) := by
    have hpos : (N' : ℤ) + 1 ≥ 0 := by omega
    rw [← ha_eval ((N' : ℤ) + 1) hpos]
    exact hN ((N' : ℤ) + 1) (by omega)
  have hpowsucc : (-1 : ℝ) ^ ((N' : ℤ) + 1 : ℤ) = -((-1 : ℝ) ^ (N' : ℤ)) := by
    have hpos : (N' : ℤ) + 1 ≥ 0 := by omega
    have htoNat_add : ((N' : ℤ) + 1).toNat = (N'.toNat : ℕ) + 1 := by omega
    calc
      (-1 : ℝ) ^ ((N' : ℤ) + 1 : ℤ)
          = (-1 : ℝ) ^ (((N' : ℤ) + 1).toNat : ℕ) := by rw [hzpow_pow hpos]
      _ = (-1 : ℝ) ^ ((N'.toNat : ℕ) + 1 : ℕ) := by rw [htoNat_add]
      _ = -((-1 : ℝ) ^ (N'.toNat : ℕ)) := by simp [pow_succ, mul_comm]
      _ = -((-1 : ℝ) ^ (N' : ℤ)) := by rw [hzpow_pow hN'0]
  rw [hpowsucc] at hNp1_bound
  set x := (-1 : ℝ) ^ (N' : ℤ) with hxdef
  have hx_abs_val : |x - (-x)| = 2 := by
    have hcalc : x - (-x) = (2 : ℝ) * x := by ring
    rw [hcalc]
    have hxpow : |x| = 1 := by
      rw [hxdef]
      calc
        |(-1 : ℝ) ^ (N' : ℤ)| = |(-1 : ℝ)| ^ (N' : ℤ) := by rw [abs_zpow]
        _ = (1 : ℝ) ^ (N' : ℤ) := by norm_num
        _ = 1 := by simp
    calc
      |(2 : ℝ) * x| = |(2 : ℝ)| * |x| := by rw [abs_mul]
      _ = (2 : ℝ) * |x| := by norm_num
      _ = (2 : ℝ) * 1 := by rw [hxpow]
      _ = (2 : ℝ) := by norm_num
  have hx_ineq : |x - (-x)| ≤ 1 := by
    calc
      |x - (-x)| = dist x (-x) := by rw [Real.dist_eq]
      _ ≤ dist x L + dist L (-x) := dist_triangle _ _ _
      _ = dist x L + dist (-x) L := by rw [dist_comm L (-x)]
      _ = |x - L| + |(-x) - L| := by rw [Real.dist_eq, Real.dist_eq]
      _ ≤ (0.5 : ℝ) + (0.5 : ℝ) := by gcongr
      _ = (1 : ℝ) := by norm_num
  rw [hx_abs_val] at hx_ineq
  linarith
/-- Proposition 6.1.15 / Exercise 6.1.6 (Formal limits are genuine limits)-/
theorem Sequence.lim_eq_LIM {a:ℕ → ℚ} (h: (a:Chapter5.Sequence).IsCauchy) :
    ((a:Chapter5.Sequence):Sequence).TendsTo (Chapter5.Real.equivR (Chapter5.LIM a)) := by
  rw [Sequence.tendsTo_iff]
  intro ε hε
  rcases exists_rat_btwn hε with ⟨q, hq1, hq2⟩
  have hq0 : (q : ℚ) > 0 := by exact_mod_cast hq1
  obtain ⟨N, hN⟩ := Chapter5.Sequence.difference_approaches_zero h q hq0
  refine ⟨(N : ℤ), fun n hn => ?_⟩
  have hnpos : (0 : ℤ) ≤ n := by omega
  have hnN : (n.toNat : ℕ) ≥ N := by
    have hn_int : (n : ℤ) ≥ (N : ℤ) := hn
    have h_cast_n : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hnpos
    have h_cast_le : (n.toNat : ℤ) ≥ (N : ℤ) := by rwa [h_cast_n]
    exact Nat.cast_le.mp h_cast_le
  have hN' : |Chapter5.LIM a - a n.toNat| ≤ q := hN n.toNat hnN
  rw [Chapter5.coe_sequence_eval, show (a : Chapter5.Sequence) n = (a n.toNat : ℚ) by
    simp [hnpos, Chapter5.Sequence.eval_coe_at_int]]
  have h_abs_eq (x : Chapter5.Real) : Chapter5.Real.equivR |x| = |Chapter5.Real.equivR x| := by
    by_cases hx : 0 ≤ x
    · have h_abs_x : |x| = x := abs_of_nonneg hx
      have h_abs_ex : |Chapter5.Real.equivR x| = Chapter5.Real.equivR x :=
        abs_of_nonneg ((Chapter5.Real.equivR_map_nonneg.mp hx))
      rw [h_abs_x, h_abs_ex]
    · have hx' : x ≤ 0 := by linarith
      have h_abs_x : |x| = -x := abs_of_nonpos hx'
      have hex_nonpos : Chapter5.Real.equivR x ≤ 0 := by
        calc
          Chapter5.Real.equivR x ≤ Chapter5.Real.equivR (0 : Chapter5.Real) :=
            (Chapter5.Real.equivR_ordered_ring.map_le_map_iff'.mpr hx')
          _ = (0 : ℝ) := by simpa using (@Chapter5.Real.equivR_ratCast (0 : ℚ))
      have h_abs_ex : |Chapter5.Real.equivR x| = -Chapter5.Real.equivR x := abs_of_nonpos hex_nonpos
      calc
        Chapter5.Real.equivR |x| = Chapter5.Real.equivR (-x) := by rw [h_abs_x]
        _ = -Chapter5.Real.equivR x :=
          map_neg (Chapter5.Real.equivR_ordered_ring : Chapter5.Real →+* ℝ) x
        _ = |Chapter5.Real.equivR x| := by rw [h_abs_ex]
  have h_sub : Chapter5.Real.equivR (Chapter5.LIM a - a n.toNat) =
    Chapter5.Real.equivR (Chapter5.LIM a) - (a n.toNat : ℝ) := by
    calc
      Chapter5.Real.equivR (Chapter5.LIM a - a n.toNat)
          = Chapter5.Real.equivR (Chapter5.LIM a) - Chapter5.Real.equivR (a n.toNat) :=
        map_sub (Chapter5.Real.equivR_ordered_ring : Chapter5.Real →+* ℝ) (Chapter5.LIM a) (a n.toNat)
      _ = Chapter5.Real.equivR (Chapter5.LIM a) - (a n.toNat : ℝ) := by
        rw [Chapter5.Real.equivR_ratCast]
  calc
    |(a n.toNat : ℝ) - Chapter5.Real.equivR (Chapter5.LIM a)|
        = |Chapter5.Real.equivR (Chapter5.LIM a) - (a n.toNat : ℝ)| := by rw [abs_sub_comm]
    _ = |Chapter5.Real.equivR (Chapter5.LIM a - a n.toNat)| := by rw [← h_sub]
    _ = Chapter5.Real.equivR |Chapter5.LIM a - a n.toNat| := by rw [h_abs_eq]
    _ ≤ Chapter5.Real.equivR (q : ℚ) :=
      (RelIso.map_rel_iff (Chapter5.Real.equivR_ordered_ring : Chapter5.Real ≃o ℝ)).mpr hN'
    _ = (q : ℝ) := by rw [Chapter5.Real.equivR_ratCast]
    _ ≤ ε := hq2.le

/-- Definition 6.1.16 -/
abbrev Sequence.BoundedBy (a:Sequence) (M:ℝ) : Prop :=
  ∀ n, |a n| ≤ M

/-- Definition 6.1.16 -/
lemma Sequence.boundedBy_def (a:Sequence) (M:ℝ) :
  a.BoundedBy M ↔ ∀ n, |a n| ≤ M := by rfl

/-- Definition 6.1.16 -/
abbrev Sequence.IsBounded (a:Sequence) : Prop := ∃ M ≥ 0, a.BoundedBy M

/-- Definition 6.1.16 -/
lemma Sequence.isBounded_def (a:Sequence) :
  a.IsBounded ↔ ∃ M ≥ 0, a.BoundedBy M := by rfl

theorem Sequence.bounded_of_cauchy {a:Sequence} (h: a.IsCauchy) : a.IsBounded := by
  have h1 : (1:ℝ).EventuallySteady a := h 1 (by norm_num)
  rcases h1 with ⟨N, hN, hsteady⟩
  have hboundN : ∀ n, n ≥ N → |a n - a N| ≤ 1 := by
    intro n hn
    have hmax_eq : max a.m N = N := max_eq_right hN
    have hn' : n ≥ (a.from N).m := by
      dsimp [Sequence.from, Sequence.mk']
      rw [hmax_eq]
      exact hn
    have hN' : N ≥ (a.from N).m := by
      dsimp [Sequence.from, Sequence.mk']
      rw [hmax_eq]
    have hclose : (1:ℝ).Close ((a.from N) n) ((a.from N) N) := hsteady n hn' N hN'
    rw [Real.Close, Real.dist_eq] at hclose
    rw [Sequence.from_eval a hn, Sequence.from_eval a (le_refl N)] at hclose
    exact hclose
  have hboundN_abs : ∀ n, n ≥ N → |a n| ≤ |a N| + 1 := by
    intro n hn
    have h := hboundN n hn
    calc
      |a n| = |(a n - a N) + a N| := by simp
      _ = |(a n - a N) - (-a N)| := by ring_nf
      _ ≤ |a n - a N| + |-a N| := abs_sub _ _
      _ = |a n - a N| + |a N| := by simp
      _ ≤ 1 + |a N| := by gcongr
      _ = |a N| + 1 := by ring_nf
  set S := Finset.Icc a.m N with hS
  have hS_nonempty : S.Nonempty := by
    refine ⟨a.m, ?_⟩
    rw [Finset.mem_Icc]
    exact ⟨le_refl a.m, hN⟩
  set M := max (|a N| + 1) (Finset.sup' S hS_nonempty (fun i ↦ |a i|)) with hM
  refine ⟨M, ?_, ?_⟩
  · have h_nonneg : 0 ≤ |a N| + 1 := by linarith [abs_nonneg (a N)]
    calc
      0 ≤ |a N| + 1 := h_nonneg
      _ ≤ M := by
        rw [hM]
        exact le_max_left _ _
  · intro n
    by_cases hn_a_m : n < a.m
    · have hzero : a n = 0 := a.vanish n hn_a_m
      have hzero_abs : |a n| = 0 := by simp [hzero]
      have hM_nonneg : 0 ≤ M := by
        rw [hM]
        have h_nonneg : 0 ≤ |a N| + 1 := by linarith [abs_nonneg (a N)]
        exact le_trans h_nonneg (le_max_left _ _)
      calc
        |a n| = 0 := hzero_abs
        _ ≤ M := hM_nonneg
    · have hn_am : a.m ≤ n := by omega
      by_cases hn_N : n ≤ N
      · have mem : n ∈ S := by
          rw [Finset.mem_Icc]
          exact ⟨hn_am, hn_N⟩
        have hle : |a n| ≤ Finset.sup' S hS_nonempty (fun i ↦ |a i|) :=
          Finset.le_sup' (fun i ↦ |a i|) mem
        calc
          |a n| ≤ Finset.sup' S hS_nonempty (fun i ↦ |a i|) := hle
          _ ≤ M := by
            rw [hM]
            exact le_max_right _ _
      · have hn_N' : n ≥ N := by omega
        calc
          |a n| ≤ |a N| + 1 := hboundN_abs n hn_N'
          _ ≤ M := by
            rw [hM]
            exact le_max_left _ _

/-- Corollary 6.1.17 -/
theorem Sequence.bounded_of_convergent {a:Sequence} (h: a.Convergent) : a.IsBounded := by
  have h_cauchy : a.IsCauchy := Sequence.IsCauchy.convergent h
  exact bounded_of_cauchy h_cauchy

/-- Example 6.1.18 -/
example : ¬ ((fun (n:ℕ) ↦ (n+1:ℝ)):Sequence).IsBounded := by
  intro h
  rcases h with ⟨M, hM_nonneg, hM⟩
  have hbound' : ∀ (n:ℕ), |(n:ℝ) + 1| ≤ M := by
    intro n
    have h := hM n
    simpa [Sequence.eval_coe] using h
  have hbound_simple : ∀ (n:ℕ), (n:ℝ) + 1 ≤ M := by
    intro n
    have h := hbound' n
    have hpos : (0:ℝ) ≤ (n:ℝ) + 1 := by nlinarith
    rw [abs_of_nonneg hpos] at h
    exact h
  rcases exists_nat_gt M with ⟨k, hk⟩
  have hk_bound : (k:ℝ) + 1 ≤ M := hbound_simple k
  nlinarith

/-- Example 6.1.18 -/
example : ¬ ((fun (n:ℕ) ↦ (n+1:ℝ)):Sequence).Convergent := by
  intro hconv
  have hbounded : ((fun (n:ℕ) ↦ (n+1:ℝ)):Sequence).IsBounded :=
    Sequence.bounded_of_convergent hconv
  rcases hbounded with ⟨M, hM_nonneg, hbound⟩
  rcases exists_nat_gt M with ⟨N, hN⟩
  have hbound_N : |((fun (n:ℕ) ↦ (n+1:ℝ)):Sequence) N| ≤ M := hbound N
  have hpos : 0 ≤ (N : ℝ) + 1 := by
    have hN_nonneg : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hN_val : |((fun (n:ℕ) ↦ (n+1:ℝ)):Sequence) N| = (N + 1 : ℝ) := by
    simp [hpos]
  have : (N + 1 : ℝ) > M := by
    have hN' : (N : ℝ) > M := hN
    linarith
  linarith

instance Sequence.inst_add : Add Sequence where
  add a b := {
    m := min a.m b.m
    seq n := a n + b n
    vanish n hn := by simp [a.vanish n (by grind), b.vanish n (by grind)]
  }

@[simp]
theorem Sequence.add_eval {a b: Sequence} (n:ℤ) : (a + b) n = a n + b n := rfl

theorem Sequence.add_coe (a b: ℕ → ℝ) : (a:Sequence) + (b:Sequence) = (fun n ↦ a n + b n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

/-- Theorem 6.1.19(a) (limit laws).  The {name}`Sequence.TendsTo` version is more usable than the {name}`lim` version
    in applications. -/
theorem Sequence.tendsTo_add {a b:Sequence} {L M:ℝ} (ha: a.TendsTo L) (hb: b.TendsTo M) :
  (a+b).TendsTo (L+M) := by
  rw [Sequence.tendsTo_iff] at ha hb ⊢
  intro ε hε
  have hε2 : ε/2 > 0 := by linarith
  obtain ⟨Na, hNa⟩ := ha (ε/2) hε2
  obtain ⟨Nb, hNb⟩ := hb (ε/2) hε2
  use max Na Nb
  intro n hn
  have hnNa : n ≥ Na := by omega
  have hnNb : n ≥ Nb := by omega
  rw [Sequence.add_eval n]
  calc
    |(a n + b n) - (L + M)| = |(a n - L) + (b n - M)| := by ring_nf
    _ ≤ |a n - L| + |b n - M| := abs_add_le (a n - L) (b n - M)
    _ ≤ (ε/2) + (ε/2) := add_le_add (hNa n hnNa) (hNb n hnNb)
    _ = ε := by ring_nf

theorem Sequence.lim_add {a b:Sequence} (ha: a.Convergent) (hb: b.Convergent) :
    (a + b).Convergent ∧ lim (a + b) = lim a + lim b := by
  have hLa : a.TendsTo (lim a) := Sequence.lim_def ha
  have hLb : b.TendsTo (lim b) := Sequence.lim_def hb
  have hsum : (a + b).TendsTo (lim a + lim b) := Sequence.tendsTo_add hLa hLb
  exact (Sequence.lim_eq.mp hsum)

instance Sequence.inst_mul : Mul Sequence where
  mul a b := {
    m := min a.m b.m
    seq n := a n * b n
    vanish n hn := by simp [a.vanish n (by grind), b.vanish n (by grind)]
  }

@[simp]
theorem Sequence.mul_eval {a b: Sequence} (n:ℤ) : (a * b) n = a n * b n := rfl

theorem Sequence.mul_coe (a b: ℕ → ℝ) : (a:Sequence) * (b:Sequence) = (fun n ↦ a n * b n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

/-- Theorem 6.1.19(b) (limit laws).  The {name}`Sequence.TendsTo` version is more usable than the {name}`lim` version
    in applications. -/
theorem Sequence.tendsTo_mul {a b:Sequence} {L M:ℝ} (ha: a.TendsTo L) (hb: b.TendsTo M) :
    (a * b).TendsTo (L * M) := by
  rw [Sequence.tendsTo_iff] at ha hb ⊢
  intro ε hε
  have ha_conv : a.Convergent := ⟨L, by rwa [Sequence.tendsTo_iff]⟩
  have hbounded : a.IsBounded := Sequence.bounded_of_convergent ha_conv
  rcases hbounded with ⟨B, hB_nonneg, hB⟩
  have hpos_M_abs : |M| + 1 > 0 := by linarith [abs_nonneg M]
  have hpos_B1 : B + 1 > 0 := by linarith
  have hε1 : ε / (2*(|M|+1)) > 0 := div_pos hε (by positivity)
  have hε2 : ε / (2*(B+1)) > 0 := div_pos hε (by positivity)
  obtain ⟨N1, hN1⟩ := ha (ε / (2*(|M|+1))) hε1
  obtain ⟨N2, hN2⟩ := hb (ε / (2*(B+1))) hε2
  use max N1 N2
  intro n hn
  have hnN1 : n ≥ N1 := by omega
  have hnN2 : n ≥ N2 := by omega
  rw [Sequence.mul_eval n]
  calc
    |a n * b n - L * M| = |a n * (b n - M) + (a n - L) * M| := by ring_nf
    _ ≤ |a n * (b n - M)| + |(a n - L) * M| := abs_add_le _ _
    _ = |a n| * |b n - M| + |a n - L| * |M| := by simp [abs_mul]
    _ ≤ B * |b n - M| + |a n - L| * |M| := by
      have hmul : |a n| * |b n - M| ≤ B * |b n - M| :=
        mul_le_mul_of_nonneg_right (hB n) (abs_nonneg _)
      exact add_le_add hmul (le_refl _)
    _ ≤ B * (ε / (2*(B+1))) + (ε / (2*(|M|+1))) * |M| := by
      have hfirst : |b n - M| ≤ ε / (2*(B+1)) := hN2 n hnN2
      have hsecond : |a n - L| ≤ ε / (2*(|M|+1)) := hN1 n hnN1
      have hmul1 : B * |b n - M| ≤ B * (ε / (2*(B+1))) :=
        mul_le_mul_of_nonneg_left hfirst hB_nonneg
      have hmul2 : |a n - L| * |M| ≤ (ε / (2*(|M|+1))) * |M| :=
        mul_le_mul_of_nonneg_right hsecond (abs_nonneg M)
      exact add_le_add hmul1 hmul2
    _ ≤ ε/2 + ε/2 := by
      have hB_ineq : B * (ε / (2*(B+1))) ≤ ε/2 := by
        have hpos_denom : 0 ≤ 2*(B+1) := by nlinarith
        calc
          B * (ε / (2*(B+1))) = (B * ε) / (2*(B+1)) := by ring
          _ ≤ (ε * (B+1)) / (2*(B+1)) :=
            div_le_div_of_nonneg_right (by nlinarith) hpos_denom
          _ = ε/2 := by field_simp [hpos_B1.ne.symm]
      have habsM_ineq : (ε / (2*(|M|+1))) * |M| ≤ ε/2 := by
        have hpos_denom : 0 ≤ 2*(|M|+1) := by nlinarith
        calc
          (ε / (2*(|M|+1))) * |M| = (|M| * ε) / (2*(|M|+1)) := by ring
          _ ≤ ((|M|+1) * ε) / (2*(|M|+1)) :=
            div_le_div_of_nonneg_right (by nlinarith) hpos_denom
          _ = ε/2 := by field_simp [hpos_M_abs.ne.symm]
      nlinarith
    _ = ε := by ring

theorem Sequence.lim_mul {a b:Sequence} (ha: a.Convergent) (hb: b.Convergent) :
    (a * b).Convergent ∧ lim (a * b) = lim a * lim b := by
  have hLa : a.TendsTo (lim a) := Sequence.lim_def ha
  have hLb : b.TendsTo (lim b) := Sequence.lim_def hb
  have hmul : (a * b).TendsTo (lim a * lim b) := Sequence.tendsTo_mul hLa hLb
  exact (Sequence.lim_eq.mp hmul)


instance Sequence.inst_smul : SMul ℝ Sequence where
  smul c a := {
    m := a.m
    seq n := c * a n
    vanish n hn := by simp [a.vanish n hn]
  }

@[simp]
theorem Sequence.smul_eval {a: Sequence} (c: ℝ) (n:ℤ) : (c • a) n = c * a n := rfl

theorem Sequence.smul_coe (c:ℝ) (a:ℕ → ℝ) : (c • (a:Sequence)) = (fun n ↦ c * a n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h, HSMul.hSMul, SMul.smul]

/-- Theorem 6.1.19(c) (limit laws).  The {name}`Sequence.TendsTo` version is more usable than the {name}`lim` version
    in applications. -/
theorem Sequence.tendsTo_smul (c:ℝ) {a:Sequence} {L:ℝ} (ha: a.TendsTo L) :
    (c • a).TendsTo (c * L) := by
  rw [Sequence.tendsTo_iff] at ha ⊢
  intro ε hε
  by_cases hc : c = 0
  · subst c; refine ⟨0, λ n hn => ?_⟩; simpa using hε.le
  · have h_abs_pos : |c| > 0 := abs_pos.mpr hc
    have hdiv : ε / |c| > 0 := div_pos hε h_abs_pos
    obtain ⟨N, hN⟩ := ha (ε / |c|) hdiv
    refine ⟨N, λ n hn => ?_⟩
    calc
      |(c • a) n - (c * L)| = |c * a n - c * L| := by rw [Sequence.smul_eval]
      _ = |c * (a n - L)| := by ring_nf
      _ = |c| * |a n - L| := by rw [abs_mul]
      _ ≤ |c| * (ε / |c|) := mul_le_mul_of_nonneg_left (hN n hn) (abs_nonneg c)
      _ = ε := by field_simp [h_abs_pos.ne']

theorem Sequence.lim_smul (c:ℝ) {a:Sequence} (ha: a.Convergent) :
    (c • a).Convergent ∧ lim (c • a) = c * lim a := by
  have hLa : a.TendsTo (lim a) := Sequence.lim_def ha
  have hsmul : (c • a).TendsTo (c * lim a) := Sequence.tendsTo_smul c hLa
  exact (Sequence.lim_eq.mp hsmul)

instance Sequence.inst_sub : Sub Sequence where
  sub a b := {
    m := min a.m b.m
    seq n := a n - b n
    vanish n hn := by simp [a.vanish n (by grind), b.vanish n (by grind)]
  }

@[simp]
theorem Sequence.sub_eval {a b: Sequence} (n:ℤ) : (a - b) n = a n - b n := rfl

theorem Sequence.sub_coe (a b: ℕ → ℝ) : (a:Sequence) - (b:Sequence) = (fun n ↦ a n - b n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

/-- Theorem 6.1.19(d) (limit laws).  The {name}`Sequence.TendsTo` version is more usable than the {name}`lim` version
    in applications. -/
theorem Sequence.tendsTo_sub {a b:Sequence} {L M:ℝ} (ha: a.TendsTo L) (hb: b.TendsTo M) :
    (a - b).TendsTo (L - M) := by
  rw [Sequence.tendsTo_iff] at ha hb ⊢
  intro ε hε
  have hε2 : ε/2 > 0 := by linarith
  obtain ⟨Na, hNa⟩ := ha (ε/2) hε2
  obtain ⟨Nb, hNb⟩ := hb (ε/2) hε2
  use max Na Nb
  intro n hn
  have hnNa : n ≥ Na := by omega
  have hnNb : n ≥ Nb := by omega
  rw [Sequence.sub_eval n]
  calc
    |(a n - b n) - (L - M)| = |(a n - L) + (-(b n - M))| := by
      have h : (a n - b n) - (L - M) = (a n - L) + (-(b n - M)) := by ring
      rw [h]
    _ ≤ |a n - L| + |-(b n - M)| := abs_add_le (a n - L) (-(b n - M))
    _ = |a n - L| + |b n - M| := by
      rw [abs_neg]
    _ ≤ (ε/2) + (ε/2) := add_le_add (hNa n hnNa) (hNb n hnNb)
    _ = ε := by ring

theorem Sequence.LIM_sub {a b:Sequence} (ha: a.Convergent) (hb: b.Convergent) :
    (a - b).Convergent ∧ lim (a - b) = lim a - lim b := by
  have hLa : a.TendsTo (lim a) := Sequence.lim_def ha
  have hLb : b.TendsTo (lim b) := Sequence.lim_def hb
  have hsub : (a - b).TendsTo (lim a - lim b) := Sequence.tendsTo_sub hLa hLb
  exact (Sequence.lim_eq (a := a - b) (L := lim a - lim b)).mp hsub

noncomputable instance Sequence.inst_inv : Inv Sequence where
  inv a := {
    m := a.m
    seq n := (a n)⁻¹
    vanish n hn := by simp [a.vanish n hn]
  }

@[simp]
theorem Sequence.inv_eval {a: Sequence} (n:ℤ) : (a⁻¹) n = (a n)⁻¹ := rfl

theorem Sequence.inv_coe (a: ℕ → ℝ) : (a:Sequence)⁻¹ = (fun n ↦ (a n)⁻¹) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

/-- Theorem 6.1.19(e) (limit laws).  The {name}`Sequence.TendsTo` version is more usable than the {name}`lim` version
    in applications. -/
theorem Sequence.tendsTo_inv {a:Sequence} {L:ℝ} (ha: a.TendsTo L) (hnon: L ≠ 0) :
    (a⁻¹).TendsTo (L⁻¹) := by
  rw [Sequence.tendsTo_iff] at ha ⊢
  intro ε hε
  have hL_abs_pos : |L| > 0 := abs_pos.mpr hnon
  have hLsq_pos : |L| ^ 2 > 0 := pow_pos hL_abs_pos 2
  have hδ_pos : |L| / 2 > 0 := div_pos hL_abs_pos (by norm_num : (0:ℝ) < 2)
  obtain ⟨N₁, hN₁⟩ := ha (|L| / 2) hδ_pos
  have h_abs_a_ge : ∀ n ≥ N₁, |a n| ≥ |L| / 2 := by
    intro n hn
    have hdist : |a n - L| ≤ |L| / 2 := hN₁ n hn
    have htemp' : |L| - |a n| ≤ |a n - L| := by
      simpa [abs_sub_comm] using abs_sub_abs_le_abs_sub L (a n)
    have : |L| / 2 ≤ |a n| := by
      have hineq : |L| - |a n| ≤ |L| / 2 := le_trans htemp' hdist
      linarith
    exact this
  have ha_nonzero : ∀ n ≥ N₁, a n ≠ 0 := by
    intro n hn
    have hpos : |a n| > 0 := by
      have h_half : |L| / 2 > 0 := div_pos hL_abs_pos (by norm_num : (0:ℝ) < 2)
      exact lt_of_lt_of_le h_half (h_abs_a_ge n hn)
    exact abs_pos.mp hpos
  have h_ineq : ∀ n ≥ N₁, |(a n)⁻¹ - L⁻¹| ≤ (2 / |L| ^ 2) * |a n - L| := by
    intro n hn
    have ha_nz : a n ≠ 0 := ha_nonzero n hn
    have h_eq : (a n)⁻¹ - L⁻¹ = (L - a n) / ((a n) * L) := by
      field_simp [hnon, ha_nz]
    have ha_pos : |a n| > 0 := by
      have h_half : |L| / 2 > 0 := div_pos hL_abs_pos (by norm_num : (0:ℝ) < 2)
      exact lt_of_lt_of_le h_half (h_abs_a_ge n hn)
    have hpos1 : |a n| * |L| > 0 := mul_pos ha_pos hL_abs_pos
    have hpos2 : (|L| / 2) * |L| > 0 :=
      mul_pos (div_pos hL_abs_pos (by norm_num : (0:ℝ) < 2)) hL_abs_pos
    have h_denom_ineq : (|L| / 2) * |L| ≤ |a n| * |L| :=
      mul_le_mul_of_nonneg_right (h_abs_a_ge n hn) (abs_nonneg _)
    calc
      |(a n)⁻¹ - L⁻¹| = |(L - a n) / ((a n) * L)| := by rw [h_eq]
      _ = |(L - a n)| / |(a n) * L| := by rw [abs_div]
      _ = |a n - L| / (|a n| * |L|) := by rw [abs_sub_comm, abs_mul]
      _ = |a n - L| * (1 / (|a n| * |L|)) := by rw [div_eq_mul_inv, inv_eq_one_div]
      _ ≤ |a n - L| * (1 / ((|L| / 2) * |L|)) := by
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        exact (one_div_le_one_div hpos1 hpos2).mpr h_denom_ineq
      _ = |a n - L| / ((|L| / 2) * |L|) := by
        simp [div_eq_mul_inv]
      _ = (2 / |L| ^ 2) * |a n - L| := by
        field_simp [hL_abs_pos.ne']
  have h_eta_pos : ε * |L| ^ 2 / 2 > 0 := by nlinarith
  obtain ⟨N₂, hN₂⟩ := ha (ε * |L| ^ 2 / 2) h_eta_pos
  use max N₁ N₂
  intro n hn
  have hn₁ : n ≥ N₁ := le_trans (le_max_left _ _) hn
  have hn₂ : n ≥ N₂ := le_trans (le_max_right _ _) hn
  calc
    |(a⁻¹) n - L⁻¹| = |(a n)⁻¹ - L⁻¹| := by rw [Sequence.inv_eval]
    _ ≤ (2 / |L| ^ 2) * |a n - L| := h_ineq n hn₁
    _ ≤ (2 / |L| ^ 2) * (ε * |L| ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left (hN₂ n hn₂) (by positivity)
    _ = ε := by
      field_simp [hLsq_pos.ne']

theorem Sequence.lim_inv {a:Sequence} (ha: a.Convergent) (hnon: lim a ≠ 0) :
  (a⁻¹).Convergent ∧ lim (a⁻¹) = (lim a)⁻¹ := by
  have hLa : a.TendsTo (lim a) := Sequence.lim_def ha
  have hinv : (a⁻¹).TendsTo ((lim a)⁻¹) := Sequence.tendsTo_inv hLa hnon
  exact (Sequence.lim_eq.mp hinv)

noncomputable instance Sequence.inst_div : Div Sequence where
  div a b := {
    m := min a.m b.m
    seq n := a n / b n
    vanish n hn := by simp [a.vanish n (by grind), b.vanish n (by grind)]
  }

@[simp]
theorem Sequence.div_eval {a b: Sequence} (n:ℤ) : (a / b) n = a n / b n := rfl

theorem Sequence.div_coe (a b: ℕ → ℝ) : (a:Sequence) / (b:Sequence) = (fun n ↦ a n / b n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

/-- Theorem 6.1.19(f) (limit laws).  The {name}`Sequence.TendsTo` version is more usable than the {name}`lim` version
    in applications. -/
theorem Sequence.tendsTo_div {a b:Sequence} {L M:ℝ} (ha: a.TendsTo L) (hb: b.TendsTo M) (hnon: M ≠ 0) :
    (a / b).TendsTo (L / M) := by
  have hinv : (b⁻¹).TendsTo (M⁻¹) := Sequence.tendsTo_inv hb hnon
  have hmul : (a * b⁻¹).TendsTo (L * M⁻¹) := Sequence.tendsTo_mul ha hinv
  simpa [div_eq_mul_inv] using hmul

theorem Sequence.lim_div {a b:Sequence} (ha: a.Convergent) (hb: b.Convergent) (hnon: lim b ≠ 0) :
  (a / b).Convergent ∧ lim (a / b) = lim a / lim b := by
  have hLa : a.TendsTo (lim a) := Sequence.lim_def ha
  have hLb : b.TendsTo (lim b) := Sequence.lim_def hb
  have hdiv : (a / b).TendsTo (lim a / lim b) := Sequence.tendsTo_div hLa hLb hnon
  exact (Sequence.lim_eq.mp hdiv)

instance Sequence.inst_max : Max Sequence where
  max a b := {
    m := min a.m b.m
    seq n := max (a n) (b n)
    vanish n hn := by simp [a.vanish n (by grind), b.vanish n (by grind)]
  }

@[simp]
theorem Sequence.max_eval {a b: Sequence} (n:ℤ) : (a ⊔ b) n = (a n) ⊔ (b n) := rfl

theorem Sequence.max_coe (a b: ℕ → ℝ) : (a:Sequence) ⊔ (b:Sequence) = (fun n ↦ max (a n) (b n)) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

/-- Theorem 6.1.19(g) (limit laws).  The {name}`Sequence.TendsTo` version is more usable than the {name}`lim` version
    in applications. -/
theorem Sequence.tendsTo_max {a b:Sequence} {L M:ℝ} (ha: a.TendsTo L) (hb: b.TendsTo M) :
    (max a b).TendsTo (max L M) := by
  have h_ineq (x y u v : ℝ) : |max x y - max u v| ≤ |x - u| + |y - v| := by
    set M := max (|x - u|) (|y - v|) with hM
    have hx_sub : x - u ≤ |x - u| := (abs_le.mp (le_refl (|x-u|))).2
    have hx_sub' : u - x ≤ |x - u| := by
      have h := (abs_le.mp (le_refl (|x-u|))).1
      linarith
    have hy_sub : y - v ≤ |y - v| := (abs_le.mp (le_refl (|y-v|))).2
    have hy_sub' : v - y ≤ |y - v| := by
      have h := (abs_le.mp (le_refl (|y-v|))).1
      linarith
    have hxM : x - u ≤ M := le_trans hx_sub (le_max_left _ _)
    have hxM' : u - x ≤ M := le_trans hx_sub' (le_max_left _ _)
    have hyM : y - v ≤ M := le_trans hy_sub (le_max_right _ _)
    have hyM' : v - y ≤ M := le_trans hy_sub' (le_max_right _ _)
    have hx_bound : x ≤ max u v + M := by
      calc
        x = u + (x - u) := by ring
        _ ≤ u + M := by linarith
        _ ≤ max u v + M := by
          have h := le_max_left u v; linarith
    have hy_bound : y ≤ max u v + M := by
      calc
        y = v + (y - v) := by ring
        _ ≤ v + M := by linarith
        _ ≤ max u v + M := by
          have h := le_max_right u v; linarith
    have h_max_xy : max x y ≤ max u v + M := max_le hx_bound hy_bound
    have h1 : max x y - max u v ≤ M := by linarith
    have hu_bound : u ≤ max x y + M := by
      calc
        u = x + (u - x) := by ring
        _ ≤ x + M := by linarith
        _ ≤ max x y + M := by
          have h := le_max_left x y; linarith
    have hv_bound : v ≤ max x y + M := by
      calc
        v = y + (v - y) := by ring
        _ ≤ y + M := by linarith
        _ ≤ max x y + M := by
          have h := le_max_right x y; linarith
    have h_max_uv : max u v ≤ max x y + M := max_le hu_bound hv_bound
    have h2 : max u v - max x y ≤ M := by linarith
    have h_abs : |max x y - max u v| ≤ M :=
      abs_le.mpr ⟨by linarith, h1⟩
    calc
      |max x y - max u v| ≤ M := h_abs
      _ = max (|x - u|) (|y - v|) := rfl
      _ ≤ |x - u| + |y - v| := by
        refine max_le ?_ ?_
        · exact le_add_of_nonneg_right (abs_nonneg (y - v))
        · exact le_add_of_nonneg_left (abs_nonneg (x - u))
  rw [Sequence.tendsTo_iff] at ha hb ⊢
  intro ε hε
  have hε2 : ε/2 > 0 := by linarith
  obtain ⟨Na, hNa⟩ := ha (ε/2) hε2
  obtain ⟨Nb, hNb⟩ := hb (ε/2) hε2
  use max Na Nb
  intro n hn
  have hnNa : n ≥ Na := by omega
  have hnNb : n ≥ Nb := by omega
  rw [Sequence.max_eval n]
  calc
    |(a n ⊔ b n) - (L ⊔ M)| ≤ |(a n) - L| + |(b n) - M| := h_ineq (a n) (b n) L M
    _ ≤ (ε/2) + (ε/2) := add_le_add (hNa n hnNa) (hNb n hnNb)
    _ = ε := by ring

theorem Sequence.lim_max {a b:Sequence} (ha: a.Convergent) (hb: b.Convergent) :
    (max a b).Convergent ∧ lim (max a b) = max (lim a) (lim b) := by
  have hLa : a.TendsTo (lim a) := Sequence.lim_def ha
  have hLb : b.TendsTo (lim b) := Sequence.lim_def hb
  have hmax : (max a b).TendsTo (max (lim a) (lim b)) := Sequence.tendsTo_max hLa hLb
  exact (Sequence.lim_eq.mp hmax)

instance Sequence.inst_min : Min Sequence where
  min a b := {
    m := min a.m b.m
    seq n := min (a n) (b n)
    vanish n hn := by simp [a.vanish n (by grind), b.vanish n (by grind)]
  }

@[simp]
theorem Sequence.min_eval {a b: Sequence} (n:ℤ) : (a ⊓ b) n = (a n) ⊓ (b n) := rfl

theorem Sequence.min_coe (a b: ℕ → ℝ) : (a:Sequence) ⊓ (b:Sequence) = (fun n ↦ min (a n) (b n)) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

/-- Theorem 6.1.19(h) (limit laws) -/
theorem Sequence.tendsTo_min {a b:Sequence} {L M:ℝ} (ha: a.TendsTo L) (hb: b.TendsTo M) :
    (min a b).TendsTo (min L M) := by
  have h_ineq (x y u v : ℝ) : |min x y - min u v| ≤ |x - u| + |y - v| := by
    set M := max (|x - u|) (|y - v|) with hM
    have hx_sub : x - u ≤ |x - u| := (abs_le.mp (le_refl (|x-u|))).2
    have hx_sub' : u - x ≤ |x - u| := by
      have h := (abs_le.mp (le_refl (|x-u|))).1
      linarith
    have hy_sub : y - v ≤ |y - v| := (abs_le.mp (le_refl (|y-v|))).2
    have hy_sub' : v - y ≤ |y - v| := by
      have h := (abs_le.mp (le_refl (|y-v|))).1
      linarith
    have hxM : x - u ≤ M := le_trans hx_sub (le_max_left _ _)
    have hxM' : u - x ≤ M := le_trans hx_sub' (le_max_left _ _)
    have hyM : y - v ≤ M := le_trans hy_sub (le_max_right _ _)
    have hyM' : v - y ≤ M := le_trans hy_sub' (le_max_right _ _)
    have hx_add : x ≤ u + M := by linarith
    have hy_add : y ≤ v + M := by linarith
    have hu_add : u ≤ x + M := by linarith
    have hv_add : v ≤ y + M := by linarith
    have h_min_xy : min x y ≤ min u v + M := by
      calc
        min x y ≤ min (u + M) (v + M) := min_le_min hx_add hy_add
        _ = min u v + M := by
          by_cases h : u ≤ v
          · have h' : u + M ≤ v + M := by simpa [add_comm] using add_le_add_right h M
            simp [h, h']
          · have hvu : v ≤ u := by linarith
            have h' : v + M ≤ u + M := by simpa [add_comm] using add_le_add_right hvu M
            simp [hvu, h']
    have h1 : min x y - min u v ≤ M := by linarith
    have h_min_uv : min u v ≤ min x y + M := by
      calc
        min u v ≤ min (x + M) (y + M) := min_le_min hu_add hv_add
        _ = min x y + M := by
          by_cases h : x ≤ y
          · have h' : x + M ≤ y + M := by simpa [add_comm] using add_le_add_right h M
            simp [h, h']
          · have hyx : y ≤ x := by linarith
            have h' : y + M ≤ x + M := by simpa [add_comm] using add_le_add_right hyx M
            simp [hyx, h']
    have h2 : min u v - min x y ≤ M := by linarith
    have h_abs : |min x y - min u v| ≤ M :=
      abs_le.mpr ⟨by linarith, h1⟩
    calc
      |min x y - min u v| ≤ M := h_abs
      _ = max (|x - u|) (|y - v|) := rfl
      _ ≤ |x - u| + |y - v| := by
        refine max_le ?_ ?_
        · exact le_add_of_nonneg_right (abs_nonneg (y - v))
        · exact le_add_of_nonneg_left (abs_nonneg (x - u))
  rw [Sequence.tendsTo_iff] at ha hb ⊢
  intro ε hε
  have hε2 : ε/2 > 0 := by linarith
  obtain ⟨Na, hNa⟩ := ha (ε/2) hε2
  obtain ⟨Nb, hNb⟩ := hb (ε/2) hε2
  use max Na Nb
  intro n hn
  have hnNa : n ≥ Na := by omega
  have hnNb : n ≥ Nb := by omega
  rw [Sequence.min_eval n]
  calc
    |(a n ⊓ b n) - (L ⊓ M)| ≤ |(a n) - L| + |(b n) - M| := h_ineq (a n) (b n) L M
    _ ≤ (ε/2) + (ε/2) := add_le_add (hNa n hnNa) (hNb n hnNb)
    _ = ε := by ring

theorem Sequence.lim_min {a b:Sequence} (ha: a.Convergent) (hb: b.Convergent) :
    (min a b).Convergent ∧ lim (min a b) = min (lim a) (lim b) := by
  have hLa : a.TendsTo (lim a) := Sequence.lim_def ha
  have hLb : b.TendsTo (lim b) := Sequence.lim_def hb
  have hmin : (min a b).TendsTo (min (lim a) (lim b)) := Sequence.tendsTo_min hLa hLb
  exact (Sequence.lim_eq.mp hmin)

/-- Exercise 6.1.1 -/
theorem Sequence.mono_if {a: ℕ → ℝ} (ha: ∀ n, a (n+1) > a n) {n m:ℕ} (hnm: m > n) : a m > a n := by
  have hbase : a (n+1) > a n := ha n
  have hstep : ∀ k, n+1 ≤ k → (a k > a n) → a (k+1) > a n := by
    intro k hk hk_gt
    have hk_gt' : a (k+1) > a k := ha k
    linarith
  have hm_gt : a m > a n := Nat.le_induction hbase hstep m (by omega)
  exact hm_gt

/-- Exercise 6.1.3 -/
theorem Sequence.tendsTo_of_from {a: Sequence} {c:ℝ} (m:ℤ) :
    a.TendsTo c ↔ (a.from m).TendsTo c := by
  constructor
  · intro h
    rw [Sequence.tendsTo_iff] at h ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨max N m, ?_⟩
    intro n hn
    have hnN : n ≥ N := by omega
    have hnm : n ≥ m := by omega
    rw [Sequence.from_eval _ hnm]
    exact hN n hnN
  · intro h
    rw [Sequence.tendsTo_iff] at h ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨max N m, ?_⟩
    intro n hn
    have hnN : n ≥ N := by omega
    have hnm : n ≥ m := by omega
    rw [← Sequence.from_eval _ hnm]
    exact hN n hnN

/-- Exercise 6.1.4 -/
theorem Sequence.tendsTo_of_shift {a: Sequence} {c:ℝ} (k:ℕ) :
    a.TendsTo c ↔ (Sequence.mk' a.m (fun n : {n // n ≥ a.m} ↦ a (n+k))).TendsTo c := by
  constructor
  · intro h
    rw [Sequence.tendsTo_iff] at h ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨max a.m N, ?_⟩
    intro n hn
    have hn_am : n ≥ a.m := by omega
    have hn_N : n ≥ N := by omega
    rw [Sequence.eval_mk (fun n : {n // n ≥ a.m} ↦ a (n + k)) hn_am]
    have hsum_ge_N : n + (k : ℤ) ≥ N := by omega
    simpa using hN (n + (k : ℤ)) hsum_ge_N
  · intro h
    rw [Sequence.tendsTo_iff] at h ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨max a.m N + (k : ℤ), ?_⟩
    intro n hn
    have hn_ge : n ≥ max a.m N + (k : ℤ) := hn
    set m := n - (k : ℤ) with hm
    have hm_ge_am : m ≥ a.m := by omega
    have hm_ge_N : m ≥ N := by omega
    have hm_add_k_eq_n : m + (k : ℤ) = n := by omega
    have hN_m : |(Sequence.mk' a.m (fun n : {n // n ≥ a.m} ↦ a (n + k))) m - c| ≤ ε :=
      hN m hm_ge_N
    rw [Sequence.eval_mk (fun n : {n // n ≥ a.m} ↦ a (n + k)) hm_ge_am] at hN_m
    simpa [hm_add_k_eq_n] using hN_m

/-- Exercise 6.1.7 -/
theorem Sequence.isBounded_of_rat (a: Chapter5.Sequence) :
    a.IsBounded ↔ (a:Sequence).IsBounded := by
  constructor
  · intro h
    rcases h with ⟨M, hM_nonneg, hM⟩
    refine ⟨(M : ℝ), by exact_mod_cast hM_nonneg, ?_⟩
    intro n
    simpa [Chapter5.coe_sequence_eval] using mod_cast hM n
  · intro h
    rcases h with ⟨M, hM_nonneg, hM⟩
    rcases exists_rat_gt M with ⟨r, hr⟩
    have hr_nonneg : (0 : ℚ) ≤ r := by
      have : (0 : ℝ) ≤ (r : ℝ) := by linarith
      exact_mod_cast this
    refine ⟨r, hr_nonneg, ?_⟩
    intro n
    have hM_n : |(a n : ℝ)| ≤ M := by
      simpa [Chapter5.coe_sequence_eval] using hM n
    have hM_n' : |(a n : ℝ)| ≤ (r : ℝ) := by linarith
    exact_mod_cast hM_n'

/-- Exercise 6.1.9 -/
theorem Sequence.lim_div_fail :
    ∃ a b, a.Convergent
    ∧ b.Convergent
    ∧ lim b = 0
    ∧ ¬ ((a / b).Convergent ∧ lim (a / b) = lim a / lim b) := by
  set a := (fun (n : ℕ) ↦ (1 : ℝ) : Sequence) with ha
  set b := (fun (n : ℕ) ↦ ((n+1 : ℝ)⁻¹) : Sequence) with hb
  have ha_conv : a.Convergent := by
    refine ⟨1, ?_⟩
    rw [Sequence.tendsTo_iff]
    intro ε hε
    refine ⟨0, fun n hn => ?_⟩
    simp [a, hn, hε.le]
  have hb_conv : b.Convergent := (Sequence.lim_harmonic).1
  have hlimb : lim b = 0 := (Sequence.lim_harmonic).2
  have h_not_div : ¬ ((a / b).Convergent ∧ lim (a / b) = lim a / lim b) := by
    intro h
    rcases h with ⟨hconv, _⟩
    have h_eq : (a / b) = (fun (n : ℕ) ↦ (n+1 : ℝ) : Sequence) := by
      apply Sequence.ext
      · calc
          (a / b).m = min a.m b.m := rfl
          _ = min 0 0 := by simp [a, b]
          _ = (0 : ℤ) := by simp
          _ = (fun (n : ℕ) ↦ (n+1 : ℝ) : Sequence).m := by simp
      · ext n
        dsimp [a, b, Sequence.ofNatFun, Sequence.div_eval]
        split_ifs with h
        · simp [div_eq_mul_inv, inv_inv]
        · simp
    rw [h_eq] at hconv
    have hbounded : ((fun (n : ℕ) ↦ (n+1 : ℝ) : Sequence)).IsBounded :=
      Sequence.bounded_of_convergent hconv
    rcases hbounded with ⟨M, hM_nonneg, hbound⟩
    rcases exists_nat_gt M with ⟨N, hN⟩
    have hbound_N : |((fun (n : ℕ) ↦ (n+1 : ℝ) : Sequence)) N| ≤ M := hbound N
    have hpos : 0 ≤ (N : ℝ) + 1 := by
      have hN_nonneg : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
      nlinarith
    have hN_val : |((fun (n : ℕ) ↦ (n+1 : ℝ) : Sequence)) N| = (N + 1 : ℝ) := by
      simp [hpos]
    have : (N + 1 : ℝ) > M := by
      have hN' : (N : ℝ) > M := hN
      nlinarith
    nlinarith
  exact ⟨a, b, ha_conv, hb_conv, hlimb, h_not_div⟩

theorem Chapter5.Sequence.IsCauchy_iff (a:Chapter5.Sequence) :
    a.IsCauchy ↔ ∀ ε > (0:ℝ), ∃ N ≥ a.n₀, ∀ n ≥ N, ∀ m ≥ N, |a n - a m| ≤ ε := by
  set a_seq : {n : ℤ // n ≥ a.n₀} → ℝ := fun x => (a x.val : ℝ) with ha_seq
  rw [Sequence.isCauchy_of_rat]
  have h_eq : (a : Sequence) = Sequence.mk' a.n₀ a_seq := by
    refine Sequence.ext ?_ ?_
    · rfl
    · ext n
      by_cases h : n ≥ a.n₀
      · simp [a_seq, h]
      · simp [h]; exact a.vanish n (by omega)
  rw [h_eq, Sequence.IsCauchy.mk a_seq]
  simp only [Real.dist_eq]
  constructor
  · intro h ε hε
    rcases h ε hε with ⟨N, hN, hdist⟩
    refine ⟨N, hN, ?_⟩
    intro n hn m hm
    have hn0 : n ≥ a.n₀ := by omega
    have hm0 : m ≥ a.n₀ := by omega
    have hdist' := hdist n hn m hm
    simpa [a_seq, hn0, hm0] using hdist'
  · intro h ε hε
    rcases h ε hε with ⟨N, hN, hdist⟩
    refine ⟨N, hN, ?_⟩
    intro n hn m hm
    have hn0 : n ≥ a.n₀ := by omega
    have hm0 : m ≥ a.n₀ := by omega
    have hdist' := hdist n hn m hm
    simpa [a_seq, hn0, hm0] using hdist'
end Chapter6

-- additional definitions for exercise 6.1.10
abbrev Real.SeqCloseSeq (ε: ℝ) (a b: Chapter5.Sequence) : Prop :=
  ∀ n, n ≥ a.n₀ → n ≥ b.n₀ → ε.Close (a n) (b n)

abbrev Real.SeqEventuallyClose (ε: ℝ) (a b: Chapter5.Sequence): Prop :=
  ∃ N, ε.SeqCloseSeq (a.from N) (b.from N)

-- extended definition of rational sequences equivalence but with positive real ε
abbrev Chapter5.Sequence.RatEquiv (a b: ℕ → ℚ) : Prop :=
  ∀ (ε:ℝ), ε > 0 → ε.SeqEventuallyClose (a:Chapter5.Sequence) (b:Chapter5.Sequence)

namespace Chapter6
/-- Exercise 6.1.10 -/
theorem Chapter5.Sequence.equiv_rat (a b: ℕ → ℚ) :
  Chapter5.Sequence.Equiv a b ↔ Chapter5.Sequence.RatEquiv a b := by
  constructor
  · intro h ε hε
    have hq := exists_rat_btwn hε
    rcases hq with ⟨q, hq1, hq2⟩
    have hq0 : (q : ℚ) > 0 := by exact_mod_cast hq1
    rcases h (q : ℚ) hq0 with ⟨N, hN⟩
    use N
    intro n hn1 hn2
    have hN' := hN n hn1 hn2
    rw [Real.Close, Real.dist_eq]
    have hN'_abs : |((a : Chapter5.Sequence).from N) n - ((b : Chapter5.Sequence).from N) n| ≤ (q : ℚ) := hN'
    have h_cast : |(((a : Chapter5.Sequence).from N) n : ℝ) - (((b : Chapter5.Sequence).from N) n : ℝ)|
      = (|((a : Chapter5.Sequence).from N) n - ((b : Chapter5.Sequence).from N) n| : ℝ) := by
      simp
    rw [h_cast]
    have h_rational : (|((a : Chapter5.Sequence).from N) n - ((b : Chapter5.Sequence).from N) n| : ℝ) ≤ (q : ℝ) :=
      by exact_mod_cast hN'_abs
    linarith
  · intro h ε hε
    have hε' : (ε : ℝ) > 0 := by exact_mod_cast hε
    rcases h (ε : ℝ) hε' with ⟨N, hN⟩
    use N
    intro n hn1 hn2
    have hN' := hN n hn1 hn2
    rw [Real.Close, Real.dist_eq] at hN'
    have h_cast : |(((a : Chapter5.Sequence).from N) n : ℝ) - (((b : Chapter5.Sequence).from N) n : ℝ)|
      = (|((a : Chapter5.Sequence).from N) n - ((b : Chapter5.Sequence).from N) n| : ℝ) := by
      simp
    rw [h_cast] at hN'
    exact_mod_cast hN'

end Chapter6
