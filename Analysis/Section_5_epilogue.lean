import Mathlib.Tactic
import Analysis.Section_5_6

/-!
# Analysis I, Chapter 5 epilogue: Isomorphism with the Mathlib real numbers

In this (technical) epilogue, we show that the "Chapter 5" real numbers {name}`Chapter5.Real` are
isomorphic in various standard senses to the standard real numbers {lean}`ℝ`.  This we do by matching
both structures with Dedekind cuts of the (Mathlib) rational numbers {lean}`ℚ`.

From this point onwards, {name}`Chapter5.Real` will be deprecated, and we will use the standard real
numbers {lean}`ℝ` instead.  In particular, one should use the full Mathlib API for {lean}`ℝ` for all
subsequent chapters, in lieu of the {name}`Chapter5.Real` API.

Filling the {syntax term}`sorry`s here requires both the {name}`Chapter5.Real` API and the Mathlib API for the standard
real numbers {lean}`ℝ`.  As such, they are excellent exercises to prepare you for the aforementioned
transition.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter5


@[ext]
structure DedekindCut where
  E : Set ℚ
  nonempty : E.Nonempty
  bounded : BddAbove E
  lower: IsLowerSet E
  nomax : ∀ q ∈ E, ∃ r ∈ E, r > q

theorem isLowerSet_iff (E: Set ℚ) : IsLowerSet E ↔ ∀ q r, r < q → q ∈ E → r ∈ E :=
  isLowerSet_iff_forall_lt

abbrev Real.toSet_Rat (x:Real) : Set ℚ := { q | (q:Real) < x }

/-- Local Archimedean helper: every Chapter 5 real is dominated by some natural. -/
private lemma Real.exists_nat_gt'' (x:Real) : ∃ N:ℕ, x < (N:Real) := by
  rcases lt_or_ge x 0 with h | h
  · refine ⟨1, ?_⟩
    have h1 : ((1:ℕ):Real) = (1:Real) := by norm_num
    rw [h1]
    have : (0:Real) < (1:Real) := by norm_num
    linarith
  · rcases eq_or_lt_of_le h with heq | hlt
    · refine ⟨1, ?_⟩
      have h1 : ((1:ℕ):Real) = (1:Real) := by norm_num
      rw [h1, ← heq]; norm_num
    · exact (Real.exists_rat_le_and_nat_gt ((Real.isPos_iff x).mpr hlt)).2

lemma Real.toSet_Rat_nonempty (x:Real) : x.toSet_Rat.Nonempty := by
  obtain ⟨q, _, hq2⟩ := Real.rat_between (show x - 1 < x by linarith)
  exact ⟨q, hq2⟩

lemma Real.toSet_Rat_bounded (x:Real) : BddAbove x.toSet_Rat := by
  obtain ⟨N, hN⟩ := Real.exists_nat_gt'' x
  refine ⟨(N:ℚ), fun q hq => ?_⟩
  simp only [Real.toSet_Rat, Set.mem_setOf_eq] at hq
  have hqN : (q:Real) < ((N:ℚ):Real) := by
    rw [show (((N:ℚ)):Real) = ((N:ℕ):Real) from by rfl]
    exact lt_trans hq hN
  exact le_of_lt ((Real.lt_of_coe q (N:ℚ)).mpr hqN)

lemma Real.toSet_Rat_lower (x:Real) : IsLowerSet x.toSet_Rat := by
  rw [isLowerSet_iff]
  intro q r hrq hq
  simp only [Real.toSet_Rat, Set.mem_setOf_eq] at *
  have : (r:Real) < (q:Real) := (Real.lt_of_coe r q).mp hrq
  linarith

lemma Real.toSet_Rat_nomax {x:Real} : ∀ q ∈ x.toSet_Rat, ∃ r ∈ x.toSet_Rat, r > q := by
  intro q hq
  simp only [Real.toSet_Rat, Set.mem_setOf_eq] at hq
  obtain ⟨r, hr1, hr2⟩ := Real.rat_between hq
  exact ⟨r, hr2, (Real.lt_of_coe q r).mpr hr1⟩

abbrev Real.toCut (x:Real) : DedekindCut :=
 {
   E := x.toSet_Rat
   nonempty := x.toSet_Rat_nonempty
   bounded := x.toSet_Rat_bounded
   lower := x.toSet_Rat_lower
   nomax := x.toSet_Rat_nomax
 }

abbrev DedekindCut.toSet_Real (c: DedekindCut) : Set Real := (fun (q:ℚ) ↦ (q:Real)) '' c.E

lemma DedekindCut.toSet_Real_nonempty (c: DedekindCut) : c.toSet_Real.Nonempty := by
  obtain ⟨q, hq⟩ := c.nonempty
  exact ⟨(q:Real), q, hq, rfl⟩

lemma DedekindCut.toSet_Real_bounded (c: DedekindCut) : BddAbove c.toSet_Real := by
  obtain ⟨M, hM⟩ := c.bounded
  refine ⟨(M:Real), ?_⟩
  rintro _ ⟨q, hq, rfl⟩
  rcases eq_or_lt_of_le (hM hq) with heq | hlt
  · rw [heq]
  · exact le_of_lt ((Real.lt_of_coe q M).mp hlt)

noncomputable abbrev DedekindCut.toReal (c: DedekindCut) : Real := sSup c.toSet_Real

lemma DedekindCut.toReal_isLUB (c: DedekindCut) : IsLUB c.toSet_Real c.toReal :=
  ExtendedReal.sSup_of_bounded c.toSet_Real_nonempty c.toSet_Real_bounded

/-- Key fact: every real is itself the least upper bound of the rationals it bounds. -/
private lemma Real.x_isLUB_toCut (x: Real) : IsLUB (x.toCut.toSet_Real) x := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨q, hq, rfl⟩
    exact le_of_lt hq
  · intro y hy
    by_contra hyx
    push_neg at hyx
    obtain ⟨q, hq1, hq2⟩ := Real.rat_between hyx
    have hq_mem : q ∈ x.toCut.E := hq2
    have : (q:Real) ≤ y := hy ⟨q, hq_mem, rfl⟩
    linarith

/-- Key fact: any DedekindCut is recovered from its supremum's {lit}`toSet_Rat`. -/
private lemma DedekindCut.E_eq_toSet_Rat (c: DedekindCut) : c.E = c.toReal.toSet_Rat := by
  ext q
  constructor
  · -- q ∈ c.E ⇒ (q:Real) < c.toReal.
    intro hq
    -- By nomax, there's r ∈ c.E with r > q. Then (q:Real) < (r:Real) ≤ sSup.
    obtain ⟨r, hr_mem, hrq⟩ := c.nomax q hq
    have hqr : (q:Real) < (r:Real) := (Real.lt_of_coe q r).mp hrq
    have hrSup : (r:Real) ≤ c.toReal := c.toReal_isLUB.1 ⟨r, hr_mem, rfl⟩
    show (q:Real) < c.toReal
    linarith
  · -- (q:Real) < c.toReal ⇒ q ∈ c.E.
    intro hq
    simp only [Real.toSet_Rat, Set.mem_setOf_eq] at hq
    -- If q ∉ c.E, then since c.E is a lower set, every (r:Real) with r ∈ c.E satisfies r < q
    -- (because if r ≥ q then by lower-set property q ∈ c.E, contradiction).
    -- So (q:Real) is an upper bound for c.toSet_Real, hence c.toReal ≤ (q:Real). Contradiction.
    by_contra hqE
    have hq_ub : (q:Real) ∈ upperBounds c.toSet_Real := by
      rintro _ ⟨r, hr_mem, rfl⟩
      -- need (r:Real) ≤ (q:Real). If r > q, then by lower set q ∈ c.E (since q ≤ r and r ∈ E), contradiction.
      by_contra hlt
      push_neg at hlt
      -- hlt : (q:Real) < (r:Real), so q < r in ℚ, so by lower-set q ∈ c.E.
      have hqr : q < r := (Real.lt_of_coe q r).mpr hlt
      exact hqE (c.lower (le_of_lt hqr) hr_mem)
    have : c.toReal ≤ (q:Real) := c.toReal_isLUB.2 hq_ub
    linarith

noncomputable abbrev Real.equivCut : Real ≃ DedekindCut where
  toFun := toCut
  invFun := DedekindCut.toReal
  left_inv x := by
    -- (x.toCut).toReal = x: use LUB uniqueness.
    exact (DedekindCut.toReal_isLUB x.toCut).unique (Real.x_isLUB_toCut x)
  right_inv c := by
    -- (c.toReal).toCut = c: use ext + E_eq_toSet_Rat.
    apply DedekindCut.ext
    exact (DedekindCut.E_eq_toSet_Rat c).symm

end Chapter5

/-- Now to develop analogous results for the Mathlib reals. -/

abbrev Real.toSet_Rat (x:ℝ) : Set ℚ := { q | (q:ℝ) < x }

lemma Real.toSet_Rat_nonempty (x:ℝ) : x.toSet_Rat.Nonempty := by
  obtain ⟨q, hq⟩ := exists_rat_lt x
  exact ⟨q, hq⟩

lemma Real.toSet_Rat_bounded (x:ℝ) : BddAbove x.toSet_Rat := by
  obtain ⟨q, hq⟩ := exists_rat_gt x
  refine ⟨q, fun r hr => ?_⟩
  simp only [Real.toSet_Rat, Set.mem_setOf_eq] at hr
  exact_mod_cast (lt_trans hr hq).le

lemma Real.toSet_Rat_lower (x:ℝ) : IsLowerSet x.toSet_Rat := by
  intro q r hrq hq
  simp only [Real.toSet_Rat, Set.mem_setOf_eq] at *
  have : (r:ℝ) ≤ (q:ℝ) := by exact_mod_cast hrq
  linarith

lemma Real.toSet_Rat_nomax (x:ℝ) : ∀ q ∈ x.toSet_Rat, ∃ r ∈ x.toSet_Rat, r > q := by
  intro q hq
  simp only [Real.toSet_Rat, Set.mem_setOf_eq] at hq
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hq
  refine ⟨r, hr2, ?_⟩
  exact_mod_cast hr1

abbrev Real.toCut (x:ℝ) : Chapter5.DedekindCut :=
 {
   E := x.toSet_Rat
   nonempty := x.toSet_Rat_nonempty
   bounded := x.toSet_Rat_bounded
   lower := x.toSet_Rat_lower
   nomax := x.toSet_Rat_nomax
 }

namespace Chapter5

abbrev DedekindCut.toSet_R (c: DedekindCut) : Set ℝ := (fun (q:ℚ) ↦ (q:ℝ)) '' c.E

lemma DedekindCut.toSet_R_nonempty (c: DedekindCut) : c.toSet_R.Nonempty := by
  obtain ⟨q, hq⟩ := c.nonempty
  exact ⟨(q:ℝ), q, hq, rfl⟩

lemma DedekindCut.toSet_R_bounded (c: DedekindCut) : BddAbove c.toSet_R := by
  obtain ⟨M, hM⟩ := c.bounded
  refine ⟨(M:ℝ), ?_⟩
  rintro _ ⟨q, hq, rfl⟩
  show (q:ℝ) ≤ (M:ℝ)
  exact_mod_cast hM hq

noncomputable abbrev DedekindCut.toR (c: DedekindCut) : ℝ := sSup c.toSet_R

lemma DedekindCut.toR_isLUB (c: DedekindCut) : IsLUB c.toSet_R c.toR :=
  isLUB_csSup c.toSet_R_nonempty c.toSet_R_bounded

/-- Key fact (ℝ side): every real is itself the LUB of the rationals it bounds. -/
private lemma _root_.Real.x_isLUB_toCut (x: ℝ) : IsLUB (x.toCut.toSet_R) x := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨q, hq, rfl⟩
    exact le_of_lt hq
  · intro y hy
    by_contra hyx
    push_neg at hyx
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hyx
    have hq_mem : q ∈ x.toCut.E := by
      show (q:ℝ) < x; exact hq2
    have : (q:ℝ) ≤ y := hy ⟨q, hq_mem, rfl⟩
    linarith

/-- Key fact (ℝ side): a DedekindCut is recovered from its supremum's {lit}`toSet_Rat`. -/
private lemma DedekindCut.E_eq_toSet_Rat_R (c: DedekindCut) : c.E = c.toR.toSet_Rat := by
  ext q
  constructor
  · intro hq
    obtain ⟨r, hr_mem, hrq⟩ := c.nomax q hq
    have hqr : (q:ℝ) < (r:ℝ) := by exact_mod_cast hrq
    have hrSup : (r:ℝ) ≤ c.toR := c.toR_isLUB.1 ⟨r, hr_mem, rfl⟩
    show (q:ℝ) < c.toR
    linarith
  · intro hq
    simp only [Set.mem_setOf_eq] at hq
    by_contra hqE
    have hq_ub : (q:ℝ) ∈ upperBounds c.toSet_R := by
      rintro _ ⟨r, hr_mem, rfl⟩
      by_contra hlt
      push_neg at hlt
      have hqr : q < r := by exact_mod_cast hlt
      exact hqE (c.lower (le_of_lt hqr) hr_mem)
    have : c.toR ≤ (q:ℝ) := c.toR_isLUB.2 hq_ub
    linarith

end Chapter5

noncomputable abbrev Real.equivCut : ℝ ≃ Chapter5.DedekindCut where
  toFun := _root_.Real.toCut
  invFun := Chapter5.DedekindCut.toR
  left_inv x := by
    exact (Chapter5.DedekindCut.toR_isLUB x.toCut).unique (Real.x_isLUB_toCut x)
  right_inv c := by
    apply Chapter5.DedekindCut.ext
    exact (Chapter5.DedekindCut.E_eq_toSet_Rat_R c).symm

namespace Chapter5

/-- The isomorphism between the {name}`Chapter5.Real` numbers and the Mathlib reals. -/
noncomputable abbrev Real.equivR : Real ≃ ℝ := Real.equivCut.trans _root_.Real.equivCut.symm

lemma Real.equivR_iff (x : Real) (y : ℝ) : y = Real.equivR x ↔ y.toCut = x.toCut := by
  simp only [equivR, Equiv.trans_apply, ←Equiv.apply_eq_iff_eq_symm_apply]
  rfl

-- In order to use this definition, we need some machinery
-----

-- We start by showing it works for ratCasts
theorem Real.equivR_ratCast {q: ℚ} : equivR q = (q: ℝ) := by
  symm
  rw [Real.equivR_iff]
  apply Chapter5.DedekindCut.ext
  show (q:ℝ).toSet_Rat = ((q:Chapter5.Real)).toSet_Rat
  ext r
  show (r:ℝ) < (q:ℝ) ↔ (r:Chapter5.Real) < (q:Chapter5.Real)
  constructor
  · intro h
    have hrq : r < q := by exact_mod_cast h
    exact (Chapter5.Real.lt_of_coe r q).mp hrq
  · intro h
    have : r < q := (Chapter5.Real.lt_of_coe r q).mpr h
    exact_mod_cast this

lemma Real.equivR_nat {n: ℕ} : equivR n = (n: ℝ) := equivR_ratCast
lemma Real.equivR_int {n: ℤ} : equivR n = (n: ℝ) := equivR_ratCast

----

-- We then want to set up a way to convert from the Real `LIM` to the ℝ `Real.mk`
-- To do this we need a few things:

-- Convertion between the notions of Cauchy Sequences
theorem Sequence.IsCauchy.to_IsCauSeq {a: ℕ → ℚ} (ha: IsCauchy a) : IsCauSeq _root_.abs a := by
  rw [Sequence.IsCauchy.coe] at ha
  intro ε hε
  obtain ⟨N, hN⟩ := ha (ε/2) (by linarith)
  refine ⟨N, fun j hj => ?_⟩
  have h1 : Section_4_3.dist (a j) (a N) ≤ ε/2 := hN j hj N (le_refl _)
  rw [Section_4_3.dist] at h1
  have h2 : |a j - a N| ≤ ε/2 := by
    rwa [show Section_4_3.abs (a j - a N) = |a j - a N| from Section_4_3.abs_eq_abs _] at h1
  show |a j - a N| < ε
  linarith

-- Convertion of an `IsCauchy` to a `CauSeq`
abbrev Sequence.IsCauchy.CauSeq {a: ℕ → ℚ} : (ha: IsCauchy a) → CauSeq ℚ _root_.abs :=
  (⟨a, ·.to_IsCauSeq⟩)

-- We then set up the conversion from Sequence.Equiv to CauSeq.LimZero because
-- it is the equivalence relation
example {a b: CauSeq ℚ abs} : a ≈ b ↔ CauSeq.LimZero (a - b) := by rfl

theorem Sequence.Equiv.LimZero {a b: ℕ → ℚ} (ha: IsCauchy a) (hb: IsCauchy b) (h:Equiv a b)
  : CauSeq.LimZero (ha.CauSeq - hb.CauSeq) := by
  intro ε hε
  rw [Sequence.equiv_iff] at h
  obtain ⟨N, hN⟩ := h (ε/2) (by linarith)
  refine ⟨N, fun j hj => ?_⟩
  have h1 := hN j hj
  show |((ha.CauSeq - hb.CauSeq).val j)| < ε
  have hval : (ha.CauSeq - hb.CauSeq).val j = a j - b j := rfl
  rw [hval]
  linarith [abs_nonneg (a j - b j)]

-- We can now use it to convert between different functions in Real.mk
theorem Real.mk_eq_mk {a b: ℕ → ℚ} (ha : Sequence.IsCauchy a) (hb : Sequence.IsCauchy b) (hab: Sequence.Equiv a b)
  : Real.mk ha.CauSeq = Real.mk hb.CauSeq := Real.mk_eq.mpr (hab.LimZero ha hb)

-- Both directions of the equivalence
theorem Sequence.Equiv_iff_LimZero {a b: ℕ → ℚ} (ha: IsCauchy a) (hb: IsCauchy b)
  : Equiv a b ↔ CauSeq.LimZero (ha.CauSeq - hb.CauSeq) := by
    refine ⟨(·.LimZero ha hb), ?_⟩
    intro hlim
    rw [Sequence.equiv_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hlim (ε/2) (by linarith)
    refine ⟨N, fun j hj => ?_⟩
    have h1 := hN j hj
    have hval : (ha.CauSeq - hb.CauSeq).val j = a j - b j := rfl
    rw [hval] at h1
    linarith [abs_nonneg (a j - b j)]

----
-- We create some cauchy sequences with useful properties

/-- Cast respects `≤`. -/
private lemma Real.le_of_coe (q r : ℚ) : q ≤ r ↔ (q:Real) ≤ (r:Real) := by
  constructor
  · intro h
    rcases eq_or_lt_of_le h with heq | hlt
    · rw [heq]
    · exact le_of_lt ((Real.lt_of_coe q r).mp hlt)
  · intro h
    rcases eq_or_lt_of_le h with heq | hlt
    · exact (Real.ratCast_inj q r).mp heq |>.le
    · exact le_of_lt ((Real.lt_of_coe q r).mpr hlt)

-- We show that for any sequence, it will eventually be arbitrarily close to its LIM
theorem Sequence.difference_approaches_zero {a: ℕ → ℚ} (ha: Sequence.IsCauchy a) :
  ∀ε > 0, ∃N, ∀n ≥ N, |LIM a - a n| ≤ (ε: ℚ) := by
  intro ε hε
  have ha_coe := ha
  rw [Sequence.IsCauchy.coe] at ha_coe
  obtain ⟨N, hN⟩ := ha_coe ε hε
  refine ⟨N, fun n hn => ?_⟩
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · have hgoal : ((a n : Real)) - ((ε:ℚ):Real) ≤ LIM a := by
      have hna_cauchy : ((-a : ℕ → ℚ):Sequence).IsCauchy := ha.neg
      have h2 : ∃ N, ∀ n' ≥ N, ((-a : ℕ → ℚ) n' : Real) ≤ -((a n : Real) - ((ε:ℚ):Real)) := by
        refine ⟨N, fun k hk => ?_⟩
        have hN_nk := hN n hn k hk
        rw [Section_4_3.dist, Section_4_3.abs_eq_abs] at hN_nk
        have hbd : a n - a k ≤ ε := le_trans (le_abs_self _) hN_nk
        have hbd2 : a n - ε ≤ a k := by linarith
        have h3 : ((-a : ℕ → ℚ) k : Real) = -(a k : Real) := by
          show (((-(a k):ℚ)):Real) = -((a k:ℚ):Real)
          exact (Real.neg_ratCast (a k)).symm
        rw [h3]
        have hcoe : ((a n - ε : ℚ) : Real) ≤ ((a k : ℚ) : Real) := (Real.le_of_coe _ _).mp hbd2
        have hsub : ((a n - ε : ℚ) : Real) = (a n : Real) - (ε : Real) := by
          rw [show (a n - ε : ℚ) = (a n) - ε from rfl, ← Real.ratCast_sub]
        rw [hsub] at hcoe; linarith
      have h4 : LIM (-a : ℕ → ℚ) ≤ -((a n : Real) - ((ε:ℚ):Real)) := Real.LIM_of_le' hna_cauchy h2
      have h5 : -LIM a ≤ -((a n : Real) - ((ε:ℚ):Real)) := by rw [Real.neg_LIM a ha]; exact h4
      linarith
    linarith
  · have hgoal : LIM a ≤ ((a n : Real)) + ((ε:ℚ):Real) := by
      apply Real.LIM_of_le' ha
      refine ⟨N, fun k hk => ?_⟩
      have hN_kn := hN k hk n hn
      rw [Section_4_3.dist, Section_4_3.abs_eq_abs] at hN_kn
      have hbd : a k - a n ≤ ε := le_trans (le_abs_self _) hN_kn
      have hbd2 : a k ≤ a n + ε := by linarith
      have hcoe : ((a k : ℚ) : Real) ≤ ((a n + ε : ℚ) : Real) := (Real.le_of_coe _ _).mp hbd2
      have hsum : ((a n + ε : ℚ) : Real) = (a n : Real) + (ε : Real) := by
        rw [show (a n + ε : ℚ) = (a n) + ε from rfl, ← Real.ratCast_add]
      rw [hsum] at hcoe; linarith
    linarith

/-- Helper: if `q n` is eventually within ε of `LIM a` (for every ε > 0), then
`q` is itself Cauchy and equivalent to `a`. -/
private lemma cauchy_equiv_of_close {a q : ℕ → ℚ} (ha: Sequence.IsCauchy a)
  (hq_close : ∀ε > (0:ℚ), ∃N, ∀n ≥ N, |LIM a - q n| ≤ (ε:ℚ))
  : Sequence.IsCauchy q ∧ Sequence.Equiv a q := by
  have h_equiv : Sequence.Equiv a q := by
    rw [Sequence.equiv_iff]
    intro ε hε
    obtain ⟨N₁, hN₁⟩ := Sequence.difference_approaches_zero ha (ε/2) (by linarith)
    obtain ⟨N₂, hN₂⟩ := hq_close (ε/2) (by linarith)
    refine ⟨max N₁ N₂, fun n hn => ?_⟩
    have h1 : |LIM a - ((a n :ℚ):Real)| ≤ (((ε/2):ℚ):Real) := hN₁ n (le_of_max_le_left hn)
    have h2 : |LIM a - ((q n :ℚ):Real)| ≤ (((ε/2):ℚ):Real) := hN₂ n (le_of_max_le_right hn)
    -- triangle inequality in Real
    have htri : |((a n :ℚ):Real) - ((q n :ℚ):Real)| ≤
        |LIM a - ((q n:ℚ):Real)| + |LIM a - ((a n:ℚ):Real)| := by
      have eq : ((a n:ℚ):Real) - ((q n:ℚ):Real) =
          (LIM a - ((q n:ℚ):Real)) - (LIM a - ((a n:ℚ):Real)) := by ring
      rw [eq, sub_eq_add_neg]
      calc |(LIM a - ((q n:ℚ):Real)) + -(LIM a - ((a n:ℚ):Real))|
          ≤ |LIM a - ((q n:ℚ):Real)| + |-(LIM a - ((a n:ℚ):Real))| := abs_add_le _ _
        _ = |LIM a - ((q n:ℚ):Real)| + |LIM a - ((a n:ℚ):Real)| := by rw [abs_neg]
    have hsum : (((ε/2):ℚ):Real) + (((ε/2):ℚ):Real) = ((ε:ℚ):Real) := by
      rw [Real.ratCast_add]
      congr 1; ring
    have h_real : |((a n :ℚ):Real) - ((q n :ℚ):Real)| ≤ ((ε:ℚ):Real) := by
      linarith
    rw [abs_le] at h_real
    obtain ⟨h_real_lo, h_real_hi⟩ := h_real
    rw [abs_le]
    have h_cast : ((a n:ℚ):Real) - ((q n:ℚ):Real) = ((a n - q n :ℚ):Real) :=
      Real.ratCast_sub _ _
    rw [h_cast] at h_real_lo h_real_hi
    have h_neg : -((ε:ℚ):Real) = ((-ε:ℚ):Real) := Real.neg_ratCast ε
    rw [h_neg] at h_real_lo
    refine ⟨?_, ?_⟩
    · have := (Real.le_of_coe (-ε) (a n - q n)).mpr h_real_lo
      linarith
    · exact (Real.le_of_coe (a n - q n) ε).mpr h_real_hi
  exact ⟨(Sequence.isCauchy_of_equiv h_equiv).mp ha, h_equiv⟩

-- There exists a Cauchy sequence entirely above the LIM
theorem Real.exists_equiv_above {a: ℕ → ℚ} (ha: Sequence.IsCauchy a)
  : ∃(b: ℕ → ℚ), Sequence.IsCauchy b ∧ Sequence.Equiv a b ∧ ∀n, LIM a ≤ b n := by
  -- For each n, find a rational b n with LIM a < b n ≤ LIM a + 1/(n+1).
  have hexists : ∀ n : ℕ, ∃ q : ℚ,
      LIM a ≤ (q:Real) ∧ |LIM a - (q:Real)| ≤ ((1/((n:ℚ)+1):ℚ):Real) := by
    intro n
    have hposReal : (0:Real) < ((1/((n:ℚ)+1):ℚ):Real) := by
      have hpos : (0:ℚ) < 1/((n:ℚ)+1) := by positivity
      exact (Real.lt_of_coe 0 (1/((n:ℚ)+1))).mp hpos
    have hLIM_lt : LIM a < LIM a + ((1/((n:ℚ)+1):ℚ):Real) := by linarith
    obtain ⟨q, hq1, hq2⟩ := Real.rat_between hLIM_lt
    refine ⟨q, le_of_lt hq1, ?_⟩
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · have : (0:Real) ≤ ((1/((n:ℚ)+1):ℚ):Real) := le_of_lt hposReal
      linarith
    · linarith
  classical
  let b : ℕ → ℚ := fun n => (hexists n).choose
  have hb_spec : ∀ n, LIM a ≤ ((b n):Real) ∧
      |LIM a - ((b n):Real)| ≤ ((1/((n:ℚ)+1):ℚ):Real) := fun n => (hexists n).choose_spec
  have hb_close : ∀ ε > (0:ℚ), ∃ N, ∀ n ≥ N, |LIM a - b n| ≤ (ε:ℚ) := by
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt (show (0:ℚ) < ε from hε)
    refine ⟨N, fun n hn => ?_⟩
    have h1 : |LIM a - ((b n):Real)| ≤ ((1/((n:ℚ)+1):ℚ):Real) := (hb_spec n).2
    -- 1/(n+1) ≤ 1/(N+1) < ε
    have hN_lt : (1:ℚ)/((N:ℚ)+1) < ε := hN
    have hmono : (1:ℚ)/((n:ℚ)+1) ≤ (1:ℚ)/((N:ℚ)+1) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      have hnN : (N:ℚ) ≤ (n:ℚ) := by exact_mod_cast hn
      linarith
    have hbd : (1:ℚ)/((n:ℚ)+1) ≤ ε := le_of_lt (lt_of_le_of_lt hmono hN_lt)
    have hcoe : ((1/((n:ℚ)+1):ℚ):Real) ≤ ((ε:ℚ):Real) :=
      (Real.le_of_coe (1/((n:ℚ)+1)) ε).mp hbd
    linarith
  obtain ⟨hb_cauchy, hab_equiv⟩ := cauchy_equiv_of_close ha hb_close
  refine ⟨b, hb_cauchy, hab_equiv, fun n => ?_⟩
  -- LIM a ≤ ((b n):Real) ⟹ LIM a ≤ b n. Wait, we need LIM a ≤ b n, but LIM a is in Real.
  -- Hmm, the conclusion is LIM a ≤ b n where LIM a : Real. So b n is coerced to Real automatically.
  exact (hb_spec n).1

-- There exists a Cauchy sequence entirely below the LIM
theorem Real.exists_equiv_below {a: ℕ → ℚ} (ha: Sequence.IsCauchy a)
  : ∃(b: ℕ → ℚ), Sequence.IsCauchy b ∧ Sequence.Equiv a b ∧ ∀n, b n ≤ LIM a := by
  have hexists : ∀ n : ℕ, ∃ q : ℚ,
      (q:Real) ≤ LIM a ∧ |LIM a - (q:Real)| ≤ ((1/((n:ℚ)+1):ℚ):Real) := by
    intro n
    have hposReal : (0:Real) < ((1/((n:ℚ)+1):ℚ):Real) := by
      have hpos : (0:ℚ) < 1/((n:ℚ)+1) := by positivity
      exact (Real.lt_of_coe 0 (1/((n:ℚ)+1))).mp hpos
    have hLIM_lt : LIM a - ((1/((n:ℚ)+1):ℚ):Real) < LIM a := by linarith
    obtain ⟨q, hq1, hq2⟩ := Real.rat_between hLIM_lt
    refine ⟨q, le_of_lt hq2, ?_⟩
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · linarith
    · have : (0:Real) ≤ ((1/((n:ℚ)+1):ℚ):Real) := le_of_lt hposReal
      linarith
  classical
  let b : ℕ → ℚ := fun n => (hexists n).choose
  have hb_spec : ∀ n, ((b n):Real) ≤ LIM a ∧
      |LIM a - ((b n):Real)| ≤ ((1/((n:ℚ)+1):ℚ):Real) := fun n => (hexists n).choose_spec
  have hb_close : ∀ ε > (0:ℚ), ∃ N, ∀ n ≥ N, |LIM a - b n| ≤ (ε:ℚ) := by
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt (show (0:ℚ) < ε from hε)
    refine ⟨N, fun n hn => ?_⟩
    have h1 : |LIM a - ((b n):Real)| ≤ ((1/((n:ℚ)+1):ℚ):Real) := (hb_spec n).2
    have hN_lt : (1:ℚ)/((N:ℚ)+1) < ε := hN
    have hmono : (1:ℚ)/((n:ℚ)+1) ≤ (1:ℚ)/((N:ℚ)+1) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      have hnN : (N:ℚ) ≤ (n:ℚ) := by exact_mod_cast hn
      linarith
    have hbd : (1:ℚ)/((n:ℚ)+1) ≤ ε := le_of_lt (lt_of_le_of_lt hmono hN_lt)
    have hcoe : ((1/((n:ℚ)+1):ℚ):Real) ≤ ((ε:ℚ):Real) :=
      (Real.le_of_coe (1/((n:ℚ)+1)) ε).mp hbd
    linarith
  obtain ⟨hb_cauchy, hab_equiv⟩ := cauchy_equiv_of_close ha hb_close
  exact ⟨b, hb_cauchy, hab_equiv, fun n => (hb_spec n).1⟩

----

-- useful theorems for the following proof
#check Real.mk_le
#check Real.mk_le_of_forall_le
#check Real.mk_const

-- Transform a `Real` to an `ℝ` by going through Cauchy Sequences
-- we can use the conversion of Real.mk_eq to use different sequences to show different parts
theorem Real.equivR_eq' {a: ℕ → ℚ} (ha: Sequence.IsCauchy a)
  : (LIM a).equivR = Real.mk ha.CauSeq := by
    by_cases hq: ∃(q: ℚ), q = LIM a
    · obtain ⟨q, hq⟩ := hq
      rw [← hq, Real.equivR_ratCast]
      have hcst : ((fun _:ℕ => q):Sequence).IsCauchy := Sequence.IsCauchy.const q
      have h_equiv : Sequence.Equiv a (fun _:ℕ => q) := by
        rw [← Real.LIM_eq_LIM ha hcst, ← hq]
        exact Real.ratCast_def q
      have hmk : Real.mk ha.CauSeq = Real.mk hcst.CauSeq :=
        Real.mk_eq_mk ha hcst h_equiv
      rw [hmk]
      exact Real.mk_const.symm
    show sSup (Rat.cast '' (LIM a).toSet_Rat) = _
    refine IsLUB.csSup_eq ⟨?_, ?_⟩ (Set.Nonempty.image _ <| Real.toSet_Rat_nonempty _)
    · -- show that `Real.mk ha.CauSeq` is an upper bound
      intro _ hy
      obtain ⟨y, hy, h⟩ := Set.mem_image _ _ _ |>.mp hy
      rw [← h, show (y: ℝ) = Real.mk (CauSeq.const _ y) from rfl]
      -- y ∈ (LIM a).toSet_Rat means (y:Real) < LIM a
      have hyLIM : (y:Real) < LIM a := hy
      -- Pick a rational midpoint m with y < m < LIM a (in ℚ-coerced reals)
      obtain ⟨m, hym, hmLIM⟩ := Real.rat_between hyLIM
      -- Now y < m in ℚ
      have hym_q : y < m := (Real.lt_of_coe y m).mpr hym
      -- ε = m - y > 0 in ℚ
      set ε : ℚ := m - y with hε_def
      have hε_pos : (0:ℚ) < ε := by simp [hε_def]; linarith
      -- Eventually a n is within ε of LIM a (in Real)
      obtain ⟨N, hN⟩ := Sequence.difference_approaches_zero ha ε hε_pos
      apply Real.mk_le.mpr
      apply CauSeq.le_of_exists
      refine ⟨N, fun n hn => ?_⟩
      have h1 : |LIM a - ((a n :ℚ):Real)| ≤ ((ε:ℚ):Real) := hN n hn
      rw [abs_le] at h1
      -- (a n:Real) ≥ LIM a - ((ε:ℚ):Real) > (m:Real) - ((ε:ℚ):Real)
      have h2 : (m:Real) - ((ε:ℚ):Real) < ((a n :ℚ):Real) := by linarith
      -- (m:Real) - ((ε:ℚ):Real) = (y:Real), since m - ε = m - (m-y) = y
      have hsub : ((m:ℚ):Real) - ((ε:ℚ):Real) = ((y:ℚ):Real) := by
        rw [Real.ratCast_sub]
        congr 1
        simp [hε_def]
      rw [hsub] at h2
      -- (y:Real) < (a n:Real), so y < a n, so y ≤ a n
      have h3 : y < a n := (Real.lt_of_coe y (a n)).mpr h2
      show (CauSeq.const _ y).1 n ≤ ha.CauSeq.1 n
      exact le_of_lt h3
    -- show that for any other upper bound, `Real.mk ha.CauSeq` is smaller
    intro M hM
    -- Strategy: use exists_equiv_below to get b ≤ LIM a pointwise (and equiv to a),
    -- then for each b n, (b n:ℝ) is the cast of a rational ≤ LIM a (strictly, since b n is rational
    -- and LIM a is irrational by hypothesis hq).
    -- Then since (b n :Real) ≤ LIM a but ≠, we have (b n :Real) < LIM a, so b n ∈ (LIM a).toSet_Rat,
    -- hence (b n :ℝ) ≤ M. Use Real.mk_le_of_forall_le.
    obtain ⟨b, hb_cauchy, hab_equiv, hb_le⟩ := Real.exists_equiv_below ha
    have hmk_eq : Real.mk ha.CauSeq = Real.mk hb_cauchy.CauSeq :=
      Real.mk_eq_mk ha hb_cauchy hab_equiv
    rw [hmk_eq]
    apply Real.mk_le_of_forall_le
    refine ⟨0, fun n _ => ?_⟩
    -- need ((b n:ℚ):ℝ) ≤ M. We have (b n:Real) ≤ LIM a. Show strict to get b n ∈ toSet_Rat.
    have hbn_lt : ((b n :ℚ):Real) < LIM a := by
      rcases lt_or_eq_of_le (hb_le n) with hlt | heq
      · exact hlt
      · exfalso; exact hq ⟨b n, heq⟩
    have hbn_mem : (b n) ∈ (LIM a).toSet_Rat := hbn_lt
    exact hM ⟨b n, hbn_mem, rfl⟩

lemma Real.equivR_eq (x: Real) : ∃(a : ℕ → ℚ) (ha: Sequence.IsCauchy a),
  x = LIM a ∧ x.equivR = Real.mk ha.CauSeq := by
    obtain ⟨a, ha, rfl⟩ := x.eq_lim
    exact ⟨a, ha, rfl, equivR_eq' ha⟩

/-- The isomorphism preserves order and ring operations. -/
noncomputable abbrev Real.equivR_ordered_ring : Real ≃+*o ℝ where
  toEquiv := equivR
  map_add' := by
    intro x y
    show equivR (x + y) = equivR x + equivR y
    obtain ⟨a, ha, rfl⟩ := x.eq_lim
    obtain ⟨b, hb, rfl⟩ := y.eq_lim
    have hab : ((a + b : ℕ → ℚ):Sequence).IsCauchy := Sequence.IsCauchy.add ha hb
    rw [equivR_eq' ha, equivR_eq' hb, Real.LIM_add ha hb, equivR_eq' hab]
    rw [← Real.mk_add]
    rfl
  map_mul' := by
    intro x y
    show equivR (x * y) = equivR x * equivR y
    obtain ⟨a, ha, rfl⟩ := x.eq_lim
    obtain ⟨b, hb, rfl⟩ := y.eq_lim
    have hab : ((a * b : ℕ → ℚ):Sequence).IsCauchy := Sequence.IsCauchy.mul ha hb
    rw [equivR_eq' ha, equivR_eq' hb, Real.LIM_mul ha hb, equivR_eq' hab]
    rw [← Real.mk_mul]
    rfl
  map_le_map_iff' := by
    intro x y
    show equivR x ≤ equivR y ↔ x ≤ y
    -- Key: (equivR z).toCut = z.toCut, so q ∈ z.toCut ↔ (q:ℝ) < equivR z.
    have hcut : ∀ z : Real, ∀ q : ℚ,
        (q:Real) < z ↔ (q:ℝ) < equivR z := by
      intro z q
      have h1 : equivR z = z.toCut.toR := rfl
      rw [h1]
      have h2 : q ∈ z.toCut.E ↔ (q:Real) < z := by simp [Real.toSet_Rat]
      have h3 : q ∈ z.toCut.toR.toSet_Rat ↔ (q:ℝ) < z.toCut.toR := by
        simp [_root_.Real.toSet_Rat]
      have h4 : z.toCut.E = z.toCut.toR.toSet_Rat :=
        DedekindCut.E_eq_toSet_Rat_R z.toCut
      rw [← h2, h4, h3]
    constructor
    · intro h
      by_contra hxy
      push_neg at hxy
      obtain ⟨q, hyq, hqx⟩ := Real.rat_between hxy
      -- (q:Real) < x, so (q:ℝ) < equivR x ≤ equivR y, so (q:ℝ) < equivR y, so (q:Real) < y.
      have hqx_R : (q:ℝ) < equivR x := (hcut x q).mp hqx
      have hqy_R : (q:ℝ) < equivR y := lt_of_lt_of_le hqx_R h
      have hqy : (q:Real) < y := (hcut y q).mpr hqy_R
      linarith
    · intro h
      -- show equivR x ≤ equivR y by showing every q with (q:ℝ) < equivR x satisfies (q:ℝ) ≤ equivR y
      by_contra hyx
      push_neg at hyx
      obtain ⟨q, hyq, hqx⟩ := exists_rat_btwn hyx
      have hqx_R : (q:ℝ) < equivR x := hqx
      have hqy_R : equivR y < (q:ℝ) := hyq
      have hqx_C : (q:Real) < x := (hcut x q).mpr hqx_R
      -- equivR y < (q:ℝ) means (q:Real) > y by hcut (in reverse)
      -- But that requires (q:ℝ) > equivR y → q > y? Let's argue directly.
      -- Note: ¬((q:Real) < y) ⟹ y ≤ (q:Real). We claim ¬((q:Real) < y).
      have hnyq : ¬ ((q:Real) < y) := by
        intro hyq_C
        have : (q:ℝ) < equivR y := (hcut y q).mp hyq_C
        linarith
      push_neg at hnyq
      -- So y ≤ (q:Real) < x. But h : x ≤ y, so y ≤ q < x ≤ y, contradiction.
      have : (q:Real) < y := lt_of_lt_of_le hqx_C h
      linarith

-- helpers for converting properties between Real and ℝ
lemma Real.equivR_map_mul {x y : Real} : equivR (x * y) = equivR x * equivR y :=
  equivR_ordered_ring.map_mul _ _

lemma Real.equivR_map_inv {x: Real} : equivR (x⁻¹) = (equivR x)⁻¹ :=
  map_inv₀ equivR_ordered_ring _

theorem Real.equivR_map_pos {x: Real} : 0 < x ↔ 0 < equivR x := by
  have h0 : equivR (0:Real) = (0:ℝ) := by
    have := @Real.equivR_ratCast 0
    simpa using this
  rw [show (0:ℝ) = equivR (0:Real) from h0.symm]
  constructor
  · intro h; exact lt_of_le_of_ne
      (equivR_ordered_ring.map_le_map_iff'.mpr h.le)
      (fun heq => h.ne' (equivR.injective heq.symm))
  · intro h; exact lt_of_le_of_ne
      (equivR_ordered_ring.map_le_map_iff'.mp h.le)
      (fun heq => h.ne' (congrArg equivR heq.symm))

theorem Real.equivR_map_nonneg {x: Real} : 0 ≤ x ↔ 0 ≤ equivR x := by
  have h0 : equivR (0:Real) = (0:ℝ) := by
    have := @Real.equivR_ratCast 0
    simpa using this
  rw [show (0:ℝ) = equivR (0:Real) from h0.symm]
  exact ⟨fun h => equivR_ordered_ring.map_le_map_iff'.mpr h,
    fun h => equivR_ordered_ring.map_le_map_iff'.mp h⟩


-- Showing equivalence of the different pows
theorem Real.pow_of_equivR (x:Real) (n:ℕ) : equivR (x^n) = (equivR x)^n := by
  induction n with
  | zero =>
    simp only [pow_zero]
    show equivR (1:Real) = (1:ℝ)
    have := @Real.equivR_ratCast 1
    simpa using this
  | succ k ih =>
    rw [pow_succ, equivR_map_mul, ih]; ring

theorem Real.zpow_of_equivR (x:Real) (n:ℤ) : equivR (x^n) = (equivR x)^n := by
  match n with
  | Int.ofNat m =>
    show equivR (x^(m:ℤ)) = (equivR x)^(m:ℤ)
    rw [zpow_natCast, zpow_natCast]
    exact pow_of_equivR x m
  | Int.negSucc m =>
    show equivR (x^(Int.negSucc m)) = (equivR x)^(Int.negSucc m)
    rw [zpow_negSucc, zpow_negSucc, equivR_map_inv]
    congr 1
    exact pow_of_equivR x (m+1)

theorem Real.ratPow_of_equivR (x:Real) (q:ℚ) (hx : x > 0): equivR (x^q) = (equivR x)^(q:ℝ) := by
  sorry


end Chapter5
