import Mathlib.Tactic
import Analysis.Section_5_3


/-!
# Analysis I, Section 5.4: Ordering the reals

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Ordering on the real line

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter5

/--
  Definition 5.4.1 (sequences bounded away from zero with sign). Sequences are indexed to start
  from zero as this is more convenient for Mathlib purposes.
-/
abbrev BoundedAwayPos (a:ℕ → ℚ) : Prop :=
  ∃ (c:ℚ), c > 0 ∧ ∀ n, a n ≥ c

/-- Definition 5.4.1 (sequences bounded away from zero with sign). -/
abbrev BoundedAwayNeg (a:ℕ → ℚ) : Prop :=
  ∃ (c:ℚ), c > 0 ∧ ∀ n, a n ≤ -c

/-- Definition 5.4.1 (sequences bounded away from zero with sign). -/
theorem boundedAwayPos_def (a:ℕ → ℚ) : BoundedAwayPos a ↔ ∃ (c:ℚ), c > 0 ∧ ∀ n, a n ≥ c := by
  rfl

/-- Definition 5.4.1 (sequences bounded away from zero with sign). -/
theorem boundedAwayNeg_def (a:ℕ → ℚ) : BoundedAwayNeg a ↔ ∃ (c:ℚ), c > 0 ∧ ∀ n, a n ≤ -c := by
  rfl

/-- Examples 5.4.2 -/
example : BoundedAwayPos (fun n ↦ 1 + 10^(-(n:ℤ)-1)) := ⟨ 1, by norm_num, by intros; simp; positivity ⟩

/-- Examples 5.4.2 -/
example : BoundedAwayNeg (fun n ↦ -1 - 10^(-(n:ℤ)-1)) := ⟨ 1, by norm_num, by intros; simp; positivity ⟩

/-- Examples 5.4.2 -/
example : ¬ BoundedAwayPos (fun n ↦ (-1)^n) := by
  intro ⟨ c, h1, h2 ⟩; specialize h2 1; grind

/-- Examples 5.4.2 -/
example : ¬ BoundedAwayNeg (fun n ↦ (-1)^n) := by
  intro ⟨ c, h1, h2 ⟩; specialize h2 0; grind

/-- Examples 5.4.2 -/
example : BoundedAwayZero (fun n ↦ (-1)^n) := ⟨ 1, by norm_num, by intros; simp ⟩

theorem BoundedAwayZero.boundedAwayPos {a:ℕ → ℚ} (ha: BoundedAwayPos a) : BoundedAwayZero a := by
  peel 3 ha with c h1 n h2; rwa [abs_of_nonneg (by linarith)]

theorem BoundedAwayZero.boundedAwayNeg {a:ℕ → ℚ} (ha: BoundedAwayNeg a) : BoundedAwayZero a := by
  peel 3 ha with c h1 n h2; rw [abs_of_neg (by linarith)]; linarith

theorem not_boundedAwayPos_boundedAwayNeg {a:ℕ → ℚ} : ¬ (BoundedAwayPos a ∧ BoundedAwayNeg a) := by
  intro ⟨ ⟨ _, _, h2⟩ , ⟨ _, _, h4 ⟩ ⟩; linarith [h2 0, h4 0]

abbrev Real.IsPos (x:Real) : Prop :=
  ∃ a:ℕ → ℚ, BoundedAwayPos a ∧ (a:Sequence).IsCauchy ∧ x = LIM a

abbrev Real.IsNeg (x:Real) : Prop :=
  ∃ a:ℕ → ℚ, BoundedAwayNeg a ∧ (a:Sequence).IsCauchy ∧ x = LIM a

theorem Real.isPos_def (x:Real) :
    IsPos x ↔ ∃ a:ℕ → ℚ, BoundedAwayPos a ∧ (a:Sequence).IsCauchy ∧ x = LIM a := by rfl

theorem Real.isNeg_def (x:Real) :
    IsNeg x ↔ ∃ a:ℕ → ℚ, BoundedAwayNeg a ∧ (a:Sequence).IsCauchy ∧ x = LIM a := by rfl

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.trichotomous (x:Real) : x = 0 ∨ x.IsPos ∨ x.IsNeg := by
  by_cases hx : x = 0
  · left; exact hx
  · right
    rcases boundedAwayZero_of_nonzero hx with ⟨a, ha_cauchy, ⟨c, hc_pos, ha_bound⟩, rfl⟩
    have ha_cau : ∀ ε > (0 : ℚ), ∃ N, ∀ j ≥ N, ∀ k ≥ N, Section_4_3.dist (a j) (a k) ≤ ε :=
      ((Sequence.IsCauchy.coe a).mp ha_cauchy)
    have hN' := ha_cau (c/2) (half_pos hc_pos)
    rcases hN' with ⟨N, hN⟩
    have hN_dist : ∀ j ≥ N, ∀ k ≥ N, |a j - a k| ≤ c/2 := by
      intro j hj k hk
      have h := hN j hj k hk
      rw [Section_4_3.dist, Section_4_3.abs_eq_abs] at h
      exact h
    by_cases hpos : a N ≥ c
    · -- x is positive
      set b : ℕ → ℚ := fun n ↦ if n < N then c/2 else a n
      have hBoundedAwayPos : BoundedAwayPos b := by
        refine ⟨c/2, half_pos hc_pos, ?_⟩
        intro n
        dsimp [b]
        by_cases hn : n < N
        · simp [hn]
        · simp [hn]
          have hnN : n ≥ N := by omega
          have h_abs : |a N - a n| ≤ c/2 := hN_dist N (le_refl N) n hnN
          have h_sq : a N - a n ≤ c/2 := (abs_le.mp h_abs).2
          nlinarith
      have h_equiv : Sequence.Equiv b a := by
        rw [Sequence.equiv_iff]
        intro ε hε
        refine ⟨N, fun n hn => ?_⟩
        have hn' : ¬ n < N := not_lt.mpr hn
        simp [b, hn', sub_self, abs_zero]
        exact hε.le
      have hCauchy : (b : Sequence).IsCauchy :=
        (Sequence.isCauchy_of_equiv h_equiv).mpr ha_cauchy
      have hLIM : LIM b = LIM a :=
        ((Real.LIM_eq_LIM hCauchy ha_cauchy).mpr h_equiv)
      exact Or.inl ⟨b, hBoundedAwayPos, hCauchy, hLIM.symm⟩
    · -- x is negative
      have hneg : a N ≤ -c := by
        have h_abs_ge : |a N| ≥ c := ha_bound N
        by_cases h_nonneg : a N ≥ 0
        · have : |a N| = a N := abs_of_nonneg h_nonneg
          rw [this] at h_abs_ge
          linarith
        · have : a N < 0 := by linarith
          have : |a N| = -a N := abs_of_neg this
          rw [this] at h_abs_ge
          linarith
      set b : ℕ → ℚ := fun n ↦ if n < N then -c/2 else a n
      have hBoundedAwayNeg : BoundedAwayNeg b := by
        refine ⟨c/2, half_pos hc_pos, ?_⟩
        intro n
        dsimp [b]
        by_cases hn : n < N
        · rw [if_pos hn, neg_div]
        · simp [hn]
          have hnN : n ≥ N := by omega
          have h_abs : |a N - a n| ≤ c/2 := hN_dist N (le_refl N) n hnN
          have h_sq' : -(c/2) ≤ a N - a n := (abs_le.mp h_abs).1
          nlinarith
      have h_equiv : Sequence.Equiv b a := by
        rw [Sequence.equiv_iff]
        intro ε hε
        refine ⟨N, fun n hn => ?_⟩
        have hn' : ¬ n < N := not_lt.mpr hn
        simp [b, hn', sub_self, abs_zero]
        exact hε.le
      have hCauchy : (b : Sequence).IsCauchy :=
        (Sequence.isCauchy_of_equiv h_equiv).mpr ha_cauchy
      have hLIM : LIM b = LIM a :=
        ((Real.LIM_eq_LIM hCauchy ha_cauchy).mpr h_equiv)
      exact Or.inr ⟨b, hBoundedAwayNeg, hCauchy, hLIM.symm⟩

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.not_zero_pos (x:Real) : ¬(x = 0 ∧ x.IsPos) := by
  rintro ⟨hzero, ⟨a, ha_pos, ha_cauchy, hx⟩⟩
  have ha_zero : BoundedAwayZero a := BoundedAwayZero.boundedAwayPos ha_pos
  have hzero_LIM : LIM a = 0 := by
    calc
      LIM a = x := hx.symm
      _ = 0 := hzero
  exact Real.lim_of_boundedAwayZero ha_zero ha_cauchy hzero_LIM

theorem Real.nonzero_of_pos {x:Real} (hx: x.IsPos) : x ≠ 0 := by
  have := not_zero_pos x
  simpa [hx] using this

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.not_zero_neg (x:Real) : ¬(x = 0 ∧ x.IsNeg) := by
  rintro ⟨hzero, ⟨a, ha_neg, ha_cauchy, hx⟩⟩
  have ha_zero : BoundedAwayZero a := BoundedAwayZero.boundedAwayNeg ha_neg
  have hzero_LIM : LIM a = 0 := by
    calc
      LIM a = x := hx.symm
      _ = 0 := hzero
  exact Real.lim_of_boundedAwayZero ha_zero ha_cauchy hzero_LIM

theorem Real.nonzero_of_neg {x:Real} (hx: x.IsNeg) : x ≠ 0 := by
  have := not_zero_neg x
  simpa [hx] using this

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.not_pos_neg (x:Real) : ¬(x.IsPos ∧ x.IsNeg) := by
  rintro ⟨⟨a, ha_pos, ha_cauchy, hx⟩, ⟨b, hb_neg, hb_cauchy, hx'⟩⟩
  have h_eq : LIM a = LIM b := by
    calc
      LIM a = x := hx.symm
      _ = LIM b := hx'
  have h_equiv : Sequence.Equiv a b := ((Real.LIM_eq_LIM ha_cauchy hb_cauchy).mp h_eq)
  rcases ha_pos with ⟨c, hc_pos, ha_bound⟩
  rcases hb_neg with ⟨d, hd_pos, hb_bound⟩
  have h_sum_pos : 0 < c + d := by linarith
  rcases (Sequence.equiv_iff a b).mp h_equiv ((c + d)/2) (by nlinarith) with ⟨N, hN⟩
  have hN_bound : |a N - b N| ≤ (c + d)/2 := hN N (le_refl N)
  have ha_N : a N ≥ c := ha_bound N
  have hb_N : b N ≤ -d := hb_bound N
  have h_diff_nonneg : 0 ≤ a N - b N := by nlinarith
  have h_diff : a N - b N ≥ c + d := by nlinarith
  have h_abs_ge : |a N - b N| ≥ c + d := by
    rw [abs_of_nonneg h_diff_nonneg]
    exact h_diff
  nlinarith

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
@[simp]
theorem Real.neg_iff_pos_of_neg (x:Real) : x.IsNeg ↔ (-x).IsPos := by
  constructor
  · intro ⟨a, ha_neg, ha_cauchy, hx⟩
    have hb_pos : BoundedAwayPos (-a) := by
      rcases ha_neg with ⟨c, hc_pos, ha_bound⟩
      refine ⟨c, hc_pos, ?_⟩
      intro n
      dsimp
      have ha_n : a n ≤ -c := ha_bound n
      linarith
    have hb_cauchy : ((-a : ℕ → ℚ) : Sequence).IsCauchy :=
      Sequence.IsCauchy.neg a ha_cauchy
    have hneg_x : -x = LIM (-a) := by
      calc
        -x = -(LIM a) := by rw [hx]
        _ = LIM (-a) := Real.neg_LIM a ha_cauchy
    exact ⟨-a, hb_pos, hb_cauchy, hneg_x⟩
  · intro ⟨a, ha_pos, ha_cauchy, hx⟩
    have hb_neg : BoundedAwayNeg (-a) := by
      rcases ha_pos with ⟨c, hc_pos, ha_bound⟩
      refine ⟨c, hc_pos, ?_⟩
      intro n
      dsimp
      have ha_n : a n ≥ c := ha_bound n
      linarith
    have hb_cauchy : ((-a : ℕ → ℚ) : Sequence).IsCauchy :=
      Sequence.IsCauchy.neg a ha_cauchy
    have hx' : x = LIM (-a) := by
      calc
        x = -(-x) := by simp
        _ = -(LIM a) := by rw [hx]
        _ = LIM (-a) := Real.neg_LIM a ha_cauchy
    exact ⟨-a, hb_neg, hb_cauchy, hx'⟩

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1-/
theorem Real.pos_add {x y:Real} (hx: x.IsPos) (hy: y.IsPos) : (x+y).IsPos := by
  rcases hx with ⟨a, ha_pos, ha_cauchy, hx⟩
  rcases hy with ⟨b, hb_pos, hb_cauchy, hy⟩
  have hab_pos : BoundedAwayPos (a + b) := by
    rcases ha_pos with ⟨c, hc_pos, ha_bound⟩
    rcases hb_pos with ⟨d, hd_pos, hb_bound⟩
    refine ⟨c, hc_pos, ?_⟩
    intro n
    dsimp
    have ha_n : a n ≥ c := ha_bound n
    have hb_n : b n ≥ d := hb_bound n
    nlinarith
  have hab_cauchy : ((a + b : ℕ → ℚ) : Sequence).IsCauchy :=
    Sequence.IsCauchy.add ha_cauchy hb_cauchy
  have hsum : x + y = LIM (a + b) := by
    calc
      x + y = LIM a + LIM b := by rw [hx, hy]
      _ = LIM (a + b) := Real.LIM_add ha_cauchy hb_cauchy
  exact ⟨a + b, hab_pos, hab_cauchy, hsum⟩

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.pos_mul {x y:Real} (hx: x.IsPos) (hy: y.IsPos) : (x*y).IsPos := by
  rcases hx with ⟨a, ha_pos, ha_cauchy, hx⟩
  rcases hy with ⟨b, hb_pos, hb_cauchy, hy⟩
  have hab_pos : BoundedAwayPos (a * b) := by
    rcases ha_pos with ⟨c, hc_pos, ha_bound⟩
    rcases hb_pos with ⟨d, hd_pos, hb_bound⟩
    refine ⟨c * d, mul_pos hc_pos hd_pos, ?_⟩
    intro n
    dsimp
    have ha_n : a n ≥ c := ha_bound n
    have hb_n : b n ≥ d := hb_bound n
    nlinarith
  have hab_cauchy : ((a * b : ℕ → ℚ) : Sequence).IsCauchy :=
    Sequence.IsCauchy.mul ha_cauchy hb_cauchy
  have hprod : x * y = LIM (a * b) := by
    calc
      x * y = LIM a * LIM b := by rw [hx, hy]
      _ = LIM (a * b) := Real.LIM_mul ha_cauchy hb_cauchy
  exact ⟨a * b, hab_pos, hab_cauchy, hprod⟩

theorem Real.pos_of_coe (q:ℚ) : (q:Real).IsPos ↔ q > 0 := by
  constructor
  · intro h
    rcases h with ⟨a, ha_pos, ha_cauchy, hx⟩
    have hq : LIM a = (q : Real) := hx.symm
    have hq' : LIM a = LIM (fun _ : ℕ ↦ q) :=
      calc
        LIM a = (q : Real) := hq
        _ = LIM (fun _ : ℕ ↦ q) := Real.ratCast_def q
    have h_equiv : Sequence.Equiv a (fun _ : ℕ ↦ q) :=
      ((Real.LIM_eq_LIM ha_cauchy (Sequence.IsCauchy.const q)).mp hq')
    rcases ha_pos with ⟨c, hc_pos, ha_bound⟩
    rcases (Sequence.equiv_iff a (fun _ : ℕ ↦ q)).mp h_equiv (c / 2) (by nlinarith) with ⟨N, hN⟩
    have hN_bound : |a N - q| ≤ c / 2 := hN N (le_refl N)
    have ha_N : a N ≥ c := ha_bound N
    rcases abs_le.mp hN_bound with ⟨hle, hge⟩
    nlinarith
  · intro h
    refine ⟨fun _ ↦ q, ⟨q, h, λ _ => le_rfl⟩, Sequence.IsCauchy.const q, ?_⟩
    exact Real.ratCast_def q

theorem Real.neg_of_coe (q:ℚ) : (q:Real).IsNeg ↔ q < 0 := by
  constructor
  · intro h
    rcases h with ⟨a, ha_neg, ha_cauchy, hx⟩
    have hq : LIM a = (q : Real) := hx.symm
    have hq' : LIM a = LIM (fun _ : ℕ ↦ q) :=
      calc
        LIM a = (q : Real) := hq
        _ = LIM (fun _ : ℕ ↦ q) := Real.ratCast_def q
    have h_equiv : Sequence.Equiv a (fun _ : ℕ ↦ q) :=
      ((Real.LIM_eq_LIM ha_cauchy (Sequence.IsCauchy.const q)).mp hq')
    rcases ha_neg with ⟨c, hc_pos, ha_bound⟩
    rcases (Sequence.equiv_iff a (fun _ : ℕ ↦ q)).mp h_equiv (c / 2) (by nlinarith) with ⟨N, hN⟩
    have hN_bound : |a N - q| ≤ c / 2 := hN N (le_refl N)
    have ha_N : a N ≤ -c := ha_bound N
    rcases abs_le.mp hN_bound with ⟨hle, hge⟩
    nlinarith
  · intro h
    refine ⟨fun _ ↦ q, ⟨-q, by linarith, λ _ => ?_⟩, Sequence.IsCauchy.const q, ?_⟩
    · dsimp; linarith
    · exact Real.ratCast_def q

open Classical in
/-- Need to use classical logic here because {name}`IsPos` and {name}`IsNeg` are not decidable -/
noncomputable abbrev Real.abs (x:Real) : Real := if x.IsPos then x else (if x.IsNeg then -x else 0)

/-- Definition 5.4.5 (absolute value) -/
@[simp]
theorem Real.abs_of_pos (x:Real) (hx: x.IsPos) : abs x = x := by
  simp [abs, hx]

/-- Definition 5.4.5 (absolute value) -/
@[simp]
theorem Real.abs_of_neg (x:Real) (hx: x.IsNeg) : abs x = -x := by
  have : ¬x.IsPos := by have := not_pos_neg x; simpa [hx] using this
  simp [abs, hx, this]

/-- Definition 5.4.5 (absolute value) -/
@[simp]
theorem Real.abs_of_zero : abs 0 = 0 := by
  have hpos: ¬(0:Real).IsPos := by have := not_zero_pos 0; simpa using this
  have hneg: ¬(0:Real).IsNeg := by have := not_zero_neg 0; simpa using this
  simp [abs, hpos, hneg]

/-- Definition 5.4.6 (Ordering of the reals) -/
instance Real.instLT : LT Real where
  lt x y := (x-y).IsNeg

/-- Definition 5.4.6 (Ordering of the reals) -/
instance Real.instLE : LE Real where
  le x y := (x < y) ∨ (x = y)

theorem Real.lt_iff (x y:Real) : x < y ↔ (x-y).IsNeg := by rfl
theorem Real.le_iff (x y:Real) : x ≤ y ↔ (x < y) ∨ (x = y) := by rfl

theorem Real.gt_iff (x y:Real) : x > y ↔ (x-y).IsPos := by
  simp
  rw [lt_iff, Real.neg_iff_pos_of_neg, neg_sub]

theorem Real.ge_iff (x y:Real) : x ≥ y ↔ (x > y) ∨ (x = y) := by
  simp; rw [Eq.comm]; rfl

theorem Real.lt_of_coe (q q':ℚ): q < q' ↔ (q:Real) < (q':Real) := by
  rw [lt_iff, Real.ratCast_sub q q', neg_of_coe, sub_lt_zero]

theorem Real.gt_of_coe (q q':ℚ): q > q' ↔ (q:Real) > (q':Real) := Real.lt_of_coe _ _

theorem Real.isPos_iff (x:Real) : x.IsPos ↔ x > 0 := by
  rw [gt_iff, sub_zero]
theorem Real.isNeg_iff (x:Real) : x.IsNeg ↔ x < 0 := by
  rw [lt_iff, sub_zero]

/-- Proposition 5.4.7(a) (order trichotomy) / Exercise 5.4.2 -/
theorem Real.trichotomous' (x y:Real) : x > y ∨ x < y ∨ x = y := by
  have h := trichotomous (x - y)
  rcases h with (hzero | hpos | hneg)
  · right; right; exact sub_eq_zero.mp hzero
  · left; rw [gt_iff]; exact hpos
  · right; left; rw [lt_iff]; exact hneg

/-- Proposition 5.4.7(a) (order trichotomy) / Exercise 5.4.2 -/
theorem Real.not_gt_and_lt (x y:Real) : ¬ (x > y ∧ x < y) := by
  rintro ⟨hgt, hlt⟩
  rw [gt_iff] at hgt
  rw [lt_iff] at hlt
  exact not_pos_neg (x - y) ⟨hgt, hlt⟩

theorem Real.not_gt_and_eq (x y:Real) : ¬ (x > y ∧ x = y) := by
  rintro ⟨hgt, heq⟩
  rw [gt_iff] at hgt
  rw [heq] at hgt
  have : ¬(y - y).IsPos := by
    have := not_zero_pos (y - y)
    simpa [sub_self] using this
  exact this hgt

theorem Real.not_lt_and_eq (x y:Real) : ¬ (x < y ∧ x = y) := by
  rintro ⟨hlt, heq⟩
  rw [lt_iff] at hlt
  rw [heq] at hlt
  have : ¬(y - y).IsNeg := by
    have := not_zero_neg (y - y)
    simpa [sub_self] using this
  exact this hlt

/-- Proposition 5.4.7(b) (order is anti-symmetric) / Exercise 5.4.2 -/
theorem Real.antisymm (x y:Real) : x < y ↔ y > x := by
  rw [lt_iff, gt_iff, Real.neg_iff_pos_of_neg (x-y), neg_sub x y]

theorem Real.neg_add {x y:Real} (hx: x.IsNeg) (hy: y.IsNeg) : (x + y).IsNeg := by
  have hx' : (-x).IsPos := (Real.neg_iff_pos_of_neg x).mp hx
  have hy' : (-y).IsPos := (Real.neg_iff_pos_of_neg y).mp hy
  have hsum : ((-x) + (-y)).IsPos := Real.pos_add hx' hy'
  have : (-x) + (-y) = -(x + y) := by ring
  rw [this] at hsum
  exact (Real.neg_iff_pos_of_neg (x + y)).mpr hsum

/-- Proposition 5.4.7(c) (order is transitive) / Exercise 5.4.2 -/
theorem Real.lt_trans {x y z:Real} (hxy: x < y) (hyz: y < z) : x < z := by
  rw [lt_iff] at hxy hyz ⊢
  have h : (x - z) = (x - y) + (y - z) := by ring
  rw [h]; exact Real.neg_add hxy hyz

/-- Proposition 5.4.7(d) (addition preserves order) / Exercise 5.4.2 -/
theorem Real.add_lt_add_right {x y:Real} (z:Real) (hxy: x < y) : x + z < y + z := by
  rw [lt_iff] at hxy ⊢
  have : (x + z) - (y + z) = x - y := by ring
  rw [this]
  exact hxy

/-- Proposition 5.4.7(e) (positive multiplication preserves order) / Exercise 5.4.2 -/
theorem Real.mul_lt_mul_right {x y z:Real} (hxy: x < y) (hz: z.IsPos) : x * z < y * z := by
  rw [antisymm, gt_iff] at hxy ⊢; convert pos_mul hxy hz using 1; ring

/-- Proposition 5.4.7(e) (positive multiplication preserves order) / Exercise 5.4.2 -/
theorem Real.mul_le_mul_left {x y z:Real} (hxy: x ≤ y) (hz: z.IsPos) : z * x ≤ z * y := by
  rw [le_iff] at hxy ⊢
  rcases hxy with (hlt | heq)
  · left; rw [mul_comm z x, mul_comm z y]; exact mul_lt_mul_right hlt hz
  · right; rw [heq]

theorem Real.mul_pos_neg {x y:Real} (hx: x.IsPos) (hy: y.IsNeg) : (x * y).IsNeg := by
  have hy' : (-y).IsPos := (Real.neg_iff_pos_of_neg y).mp hy
  have hpos : (x * (-y)).IsPos := Real.pos_mul hx hy'
  have : x * (-y) = -(x * y) := by ring
  rw [this] at hpos
  exact (Real.neg_iff_pos_of_neg (x * y)).mpr hpos

open Classical in
/--
  (Not from textbook) {name}`Real` has the structure of a linear ordering. The order is not computable,
  and so classical logic is required to impose decidability.
-/
noncomputable instance Real.instLinearOrder : LinearOrder Real where
  le_refl := by
    intro x; rw [le_iff]; exact Or.inr rfl
  le_trans := by
    intro x y z hxy hyz
    rw [le_iff] at hxy hyz ⊢
    rcases hxy with (hxy_lt | hxy_eq)
    · rcases hyz with (hyz_lt | hyz_eq)
      · exact Or.inl (lt_trans hxy_lt hyz_lt)
      · exact Or.inl (by rwa [hyz_eq] at hxy_lt)
    · rcases hyz with (hyz_lt | hyz_eq)
      · exact Or.inl (by rwa [hxy_eq])
      · exact Or.inr (hxy_eq.trans hyz_eq)
  lt_iff_le_not_ge := by
    intro x y
    constructor
    · intro hlt
      constructor
      · rw [le_iff]; exact Or.inl hlt
      · intro hle
        rw [le_iff] at hle
        rcases hle with (hlt' | heq)
        · exact not_gt_and_lt y x ⟨hlt, hlt'⟩
        · exact not_lt_and_eq x y ⟨hlt, heq.symm⟩
    · intro ⟨hle, hnge⟩
      rw [le_iff] at hle
      rcases hle with (hlt | heq)
      · exact hlt
      · exfalso; exact hnge (by rw [le_iff]; exact Or.inr heq.symm)
  le_antisymm := by
    intro x y hxy hyx
    rw [le_iff] at hxy hyx
    rcases hxy with (hxy_lt | hxy_eq)
    · rcases hyx with (hyx_lt | hyx_eq)
      · exfalso
        rw [lt_iff] at hxy_lt hyx_lt
        have hyx_lt' : (-(x-y)).IsNeg := by
          rw [neg_sub]; exact hyx_lt
        have hpos : (x-y).IsPos := by
          have := (Real.neg_iff_pos_of_neg (-(x-y))).mp hyx_lt'
          simpa using this
        exact not_pos_neg (x-y) ⟨hpos, hxy_lt⟩
      · exfalso; exact not_lt_and_eq x y ⟨hxy_lt, hyx_eq.symm⟩
    · exact hxy_eq
  le_total := by
    intro x y
    have h := trichotomous' x y
    rcases h with (hgt | hlt | heq)
    · right; rw [le_iff]; exact Or.inl hgt
    · left; rw [le_iff]; exact Or.inl hlt
    · left; rw [le_iff]; exact Or.inr heq
  toDecidableLE := Classical.decRel _

/--
  (Not from textbook) {name}`LinearOrder`s come with a definition of absolute value {lean (type := "Real → Real")}`(|·|)`.
  Show that it agrees with our earlier definition.
-/
theorem Real.abs_eq_abs (x:Real) : |x| = abs x := by
  have h := trichotomous x
  rcases h with (hzero | hpos | hneg)
  · rw [hzero]
    calc
      |(0 : Real)| = max (0 : Real) (-(0 : Real)) := rfl
      _ = max (0 : Real) (0 : Real) := by simp
      _ = (0 : Real) := by simp
      _ = abs (0 : Real) := by symm; exact Real.abs_of_zero
  · have hpos' : 0 < x := (Real.isPos_iff x).mp hpos
    have hnegx_lt_0 : -x < 0 := by
      have : 0 + (-x) < x + (-x) := add_lt_add_right (-x) hpos'
      simpa using this
    have hnegx_lt_x : -x < x := lt_trans hnegx_lt_0 hpos'
    have hnegx_le_x : -x ≤ x := le_of_lt hnegx_lt_x
    calc
      |x| = max x (-x) := rfl
      _ = x := max_eq_left hnegx_le_x
      _ = abs x := (Real.abs_of_pos x hpos).symm
  · have hneg' : x < 0 := (Real.isNeg_iff x).mp hneg
    have h_negx_gt_0 : 0 < -x := by
      have : x + (-x) < 0 + (-x) := add_lt_add_right (-x) hneg'
      simpa using this
    have hx_lt_negx : x < -x := lt_trans hneg' h_negx_gt_0
    have hx_le_negx : x ≤ -x := le_of_lt hx_lt_negx
    calc
      |x| = max x (-x) := rfl
      _ = -x := max_eq_right hx_le_negx
      _ = abs x := (Real.abs_of_neg x hneg).symm

/-- Proposition 5.4.8 -/
theorem Real.inv_of_pos {x:Real} (hx: x.IsPos) : x⁻¹.IsPos := by
  observe hnon: x ≠ 0
  observe hident : x⁻¹ * x = 1
  have hinv_non: x⁻¹ ≠ 0 := by
    intro hzero
    have hcalc : x⁻¹ * x = 0 := by simp [hzero]
    rw [hcalc] at hident
    have h1pos : (1 : Real).IsPos := by
      have := (pos_of_coe (1 : ℚ)).mpr (by norm_num)
      simpa using this
    have h10 : (1 : Real) ≠ 0 := nonzero_of_pos h1pos
    exact h10 hident.symm
  have hnonneg : ¬x⁻¹.IsNeg := by
    intro h
    have : (x * x⁻¹).IsNeg := mul_pos_neg hx h
    rw [self_mul_inv hnon] at this
    have : (1 : ℚ) < 0 := (neg_of_coe (1 : ℚ)).mp (by simpa using this)
    linarith
  have trich := trichotomous x⁻¹
  simpa [hinv_non, hnonneg] using trich

theorem Real.div_of_pos {x y:Real} (hx: x.IsPos) (hy: y.IsPos) : (x/y).IsPos := by
  have hy_inv : y⁻¹.IsPos := Real.inv_of_pos hy
  have : (x * y⁻¹).IsPos := Real.pos_mul hx hy_inv
  simpa [div_eq_mul_inv] using this

theorem Real.inv_of_gt {x y:Real} (hx: x.IsPos) (hy: y.IsPos) (hxy: x > y) : x⁻¹ < y⁻¹ := by
  observe hxnon: x ≠ 0
  observe hynon: y ≠ 0
  observe hxinv : x⁻¹.IsPos
  by_contra! this
  have : (1:Real) > 1 := calc
    1 = x * x⁻¹ := (self_mul_inv hxnon).symm
    _ > y * x⁻¹ := mul_lt_mul_right hxy hxinv
    _ ≥ y * y⁻¹ := mul_le_mul_left this hy
    _ = _ := self_mul_inv hynon
  simp at this

/-- (Not from textbook) {name}`Real` has the structure of a strict ordered ring. -/
instance Real.instIsStrictOrderedRing : IsStrictOrderedRing Real where
  add_le_add_left := by
    intro a b h c
    rw [le_iff] at h ⊢
    rcases h with (hlt | heq)
    · refine Or.inl ?_
      simpa [add_comm] using add_lt_add_right c hlt
    · subst heq; exact Or.inr rfl
  add_le_add_right := by
    intro a b h c
    rw [le_iff] at h ⊢
    rcases h with (hlt | heq)
    · refine Or.inl ?_
      simpa [add_comm] using add_lt_add_right c hlt
    · subst heq; exact Or.inr rfl
  mul_lt_mul_of_pos_left := by
    intro a ha b c hbc
    have ha_pos : a.IsPos := (Real.isPos_iff a).mpr ha
    simpa [mul_comm] using mul_lt_mul_right hbc ha_pos
  mul_lt_mul_of_pos_right := by
    intro c hc a b hab
    have hc_pos : c.IsPos := (Real.isPos_iff c).mpr hc
    exact mul_lt_mul_right hab hc_pos
  le_of_add_le_add_left := by
    intro a b c h
    rw [le_iff] at h ⊢
    rcases h with (hlt | heq)
    · left; rw [lt_iff] at hlt ⊢
      have : (a + b) - (a + c) = b - c := by ring
      rw [this] at hlt; exact hlt
    · right; exact add_left_cancel heq
  zero_le_one := by
    rw [le_iff]
    left
    have h1pos : (1 : Real).IsPos := by
      have := (pos_of_coe (1 : ℚ)).mpr (by norm_num)
      simpa using this
    exact (Real.isPos_iff (1 : Real)).mp h1pos
  exists_pair_ne := ⟨0, 1, by
    have h1pos : (1 : Real).IsPos := by
      have := (pos_of_coe (1 : ℚ)).mpr (by norm_num)
      simpa using this
    exact (nonzero_of_pos h1pos).symm⟩

/-- Proposition 5.4.9 (The non-negative reals are closed)-/
theorem Real.LIM_of_nonneg {a: ℕ → ℚ} (ha: ∀ n, a n ≥ 0) (hcauchy: (a:Sequence).IsCauchy) :
    LIM a ≥ 0 := by
  -- This proof is written to follow the structure of the original text.
  by_contra! hlim
  set x := LIM a
  rw [←isNeg_iff, isNeg_def] at hlim; choose b hb hb_cauchy hlim using hlim
  rw [boundedAwayNeg_def] at hb; choose c cpos hb using hb
  have claim1 : ∀ n, ¬ (c/2).Close (a n) (b n) := by
    intro n; specialize ha n; specialize hb n
    rw [Section_4_3.close_iff]
    have hcalc : c/2 < Section_4_3.abs (a n - b n) := by
      calc
        c/2 < c := by linarith
        _ ≤ a n - b n := by linarith
        _ = Section_4_3.abs (a n - b n) := by
          symm; apply Section_4_3.abs_of_pos; nlinarith
    linarith
  have claim2 : ¬(c/2).EventuallyClose (a:Sequence) (b:Sequence) := by
    contrapose! claim1; rw [Rat.eventuallyClose_iff] at claim1; peel claim1 with N claim1; grind [Section_4_3.close_iff]
  have claim3 : ¬Sequence.Equiv a b := by contrapose! claim2; rw [Sequence.equiv_def] at claim2; solve_by_elim [half_pos]
  simp_rw [x, LIM_eq_LIM hcauchy hb_cauchy] at hlim
  contradiction

/-- Corollary 5.4.10 -/
theorem Real.LIM_mono {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy)
  (hmono: ∀ n, a n ≤ b n) :
    LIM a ≤ LIM b := by
  -- This proof is written to follow the structure of the original text.
  have := LIM_of_nonneg (a := b - a) (by intro n; simp [hmono n]) (Sequence.IsCauchy.sub hb ha)
  rw [←Real.LIM_sub hb ha] at this; linarith

/-- Remark 5.4.11 --/
theorem Real.LIM_mono_fail :
    ∃ (a b:ℕ → ℚ), (a:Sequence).IsCauchy
    ∧ (b:Sequence).IsCauchy
    ∧ (∀ n, a n > b n)
    ∧ ¬LIM a > LIM b := by
  use (fun n ↦ 1 + 1/((n:ℚ) + 1))
  use (fun n ↦ 1 - 1/((n:ℚ) + 1))
  have ha_cauchy : ((fun n : ℕ ↦ 1 + 1/((n:ℚ)+1) : ℕ → ℚ) : Sequence).IsCauchy :=
    Sequence.IsCauchy.add (Sequence.IsCauchy.const 1) Sequence.IsCauchy.harmonic'
  have hb_cauchy : ((fun n : ℕ ↦ 1 - 1/((n:ℚ)+1) : ℕ → ℚ) : Sequence).IsCauchy :=
    Sequence.IsCauchy.sub (Sequence.IsCauchy.const 1) Sequence.IsCauchy.harmonic'
  have h_lt : ∀ n, (fun n : ℕ ↦ 1 + 1/((n:ℚ)+1) : ℕ → ℚ) n > (fun n : ℕ ↦ 1 - 1/((n:ℚ)+1) : ℕ → ℚ) n := by
    intro n; dsimp
    have hpos_div : 0 < 1 / ((n : ℚ) + 1) := div_pos (by norm_num) (by positivity)
    linarith
  have h_lim_one : LIM (fun n : ℕ ↦ 1 + 1/((n:ℚ)+1)) = (1 : Real) := by
    calc
      LIM (fun n : ℕ ↦ 1 + 1/((n:ℚ)+1)) = LIM ((fun _ : ℕ ↦ (1 : ℚ)) + (fun n : ℕ ↦ 1/((n:ℚ)+1))) := by
        apply congrArg LIM; ext n; simp
      _ = LIM (fun _ : ℕ ↦ (1 : ℚ)) + LIM (fun n : ℕ ↦ 1/((n:ℚ)+1)) :=
        (Real.LIM_add (Sequence.IsCauchy.const 1) Sequence.IsCauchy.harmonic').symm
      _ = ((1 : ℚ) : Real) + 0 := by rw [←Real.ratCast_def (1 : ℚ), Real.LIM.harmonic]
      _ = (1 : Real) := by
        calc
          ((1 : ℚ) : Real) + 0 = ((1 : ℚ) : Real) := by simp
          _ = (1 : Real) := rfl
  have h_lim_two : LIM (fun n : ℕ ↦ 1 - 1/((n:ℚ)+1)) = (1 : Real) := by
    calc
      LIM (fun n : ℕ ↦ 1 - 1/((n:ℚ)+1)) = LIM ((fun _ : ℕ ↦ (1 : ℚ)) - (fun n : ℕ ↦ 1/((n:ℚ)+1))) := by
        apply congrArg LIM; ext n; simp
      _ = LIM (fun _ : ℕ ↦ (1 : ℚ)) - LIM (fun n : ℕ ↦ 1/((n:ℚ)+1)) :=
        (Real.LIM_sub (Sequence.IsCauchy.const 1) Sequence.IsCauchy.harmonic').symm
      _ = ((1 : ℚ) : Real) - 0 := by rw [←Real.ratCast_def (1 : ℚ), Real.LIM.harmonic]
      _ = (1 : Real) := by
        calc
          ((1 : ℚ) : Real) - 0 = ((1 : ℚ) : Real) := by simp
          _ = (1 : Real) := rfl
  refine ⟨ha_cauchy, hb_cauchy, h_lt, ?_⟩
  rw [h_lim_one, h_lim_two]
  intro hgt
  linarith

/-- Proposition 5.4.12 (Bounding reals by rationals) -/
theorem Real.exists_rat_le_and_nat_gt {x:Real} (hx: x.IsPos) :
    (∃ q:ℚ, q > 0 ∧ (q:Real) ≤ x) ∧ ∃ N:ℕ, x < (N:Real) := by
  -- This proof is written to follow the structure of the original text.
  rw [isPos_def] at hx; choose a hbound hcauchy heq using hx
  rw [boundedAwayPos_def] at hbound; choose q hq hbound using hbound
  have := Sequence.isBounded_of_isCauchy hcauchy
  rw [Sequence.isBounded_def] at this; choose r hr this using this
  simp [Sequence.boundedBy_def] at this
  refine ⟨ ⟨ q, hq, ?_ ⟩, ?_ ⟩
  . convert LIM_mono (Sequence.IsCauchy.const _) hcauchy hbound
    exact Real.ratCast_def q
  choose N hN using exists_nat_gt r; use N
  calc
    x ≤ r := by
      rw [Real.ratCast_def r]
      convert LIM_mono hcauchy (Sequence.IsCauchy.const r) _
      intro n; specialize this n; simp at this
      exact (le_abs_self _).trans this
    _ < ((N:ℚ):Real) := (Real.lt_of_coe r (N : ℚ)).mp hN
    _ = N := rfl

/-- Corollary 5.4.13 (Archimedean property ) -/
theorem Real.le_mul {ε:Real} (hε: ε.IsPos) (x:Real) : ∃ M:ℕ, M > 0 ∧ M * ε > x := by
  -- This proof is written to follow the structure of the original text.
  obtain rfl | hx | hx := trichotomous x
  . use 1; simpa [isPos_iff] using hε
  . choose N hN using (exists_rat_le_and_nat_gt (div_of_pos hx hε)).2
    set M := N+1; refine ⟨ M, by positivity, ?_ ⟩
    replace hN : x/ε < M := hN.trans (by simp [M])
    have hpos_ε : ε > 0 := by rwa [isPos_iff] at hε
    have hx_eq : x = (x / ε) * ε := by
      calc
        x = x * 1 := by simp
        _ = x * (ε⁻¹ * ε) := by rw [Real.inv_mul_self (ne_of_gt hpos_ε)]
        _ = (x * ε⁻¹) * ε := by ring
        _ = (x / ε) * ε := by rw [Real.div_eq]
    have hineq : x < M * ε := by
      rw [hx_eq]
      exact Real.mul_lt_mul_right hN (by rw [isPos_iff]; exact hpos_ε)
    exact hineq
  use 1; simp_all [isPos_iff]; linarith

private theorem rat_between_pos_y {x y : Real} (hxy : x < y) (hypos : y > 0) :
    ∃ q : ℚ, x < (q : Real) ∧ (q : Real) < y := by
  have hyx_pos : (y-x).IsPos := by
    rw [Real.isPos_iff]; linarith
  have h1pos : (1 : Real).IsPos := by
    have := (Real.pos_of_coe (1 : ℚ)).mpr (by norm_num)
    simpa using this
  rcases Real.le_mul hyx_pos (1 : Real) with ⟨M, hMpos, hM⟩
  have hMpos' : (M : ℚ) > 0 := by exact_mod_cast hMpos
  have hM_pos_real : (M : Real).IsPos := by
    have := (Real.pos_of_coe (M : ℚ)).mpr hMpos'
    simpa using this
  have hM_ne_zero : (M : Real) ≠ 0 := Real.nonzero_of_pos hM_pos_real
  have hM_inv_pos : ((M : Real)⁻¹).IsPos := Real.inv_of_pos hM_pos_real
  have h1_lt_M_diff : (1 : Real) < (M : Real) * (y - x) := hM
  have hM_inv_pos' : 0 < (M : Real)⁻¹ := (Real.isPos_iff _).mp hM_inv_pos
  have hyx_gt_invM : y - x > (M : Real)⁻¹ := by
    have htemp := mul_lt_mul_of_pos_left h1_lt_M_diff hM_inv_pos'
    calc
      y - x = 1 * (y - x) := by simp
      _ = ((M : Real)⁻¹ * (M : Real)) * (y - x) := by rw [Real.inv_mul_self hM_ne_zero]
      _ = (M : Real)⁻¹ * ((M : Real) * (y - x)) := by ring
      _ > (M : Real)⁻¹ * (1 : Real) := htemp
      _ = (M : Real)⁻¹ := by simp [mul_one]
  have hx_add_invM_lt_y : x + (M : Real)⁻¹ < y := by
    linarith
  rcases Real.le_mul h1pos ((M : Real) * x) with ⟨K, hKpos, hK⟩
  have hKdivM_gt_x : (K : Real) / (M : Real) > x := by
    have hMx_lt_K : (M : Real) * x < (K : Real) := by
      simpa [mul_comm, one_mul] using hK
    have htemp := Real.mul_lt_mul_right hMx_lt_K hM_inv_pos
    calc
      x = x * 1 := by simp
      _ = x * ((M : Real) * (M : Real)⁻¹) := by rw [Real.self_mul_inv hM_ne_zero]
      _ = (x * (M : Real)) * (M : Real)⁻¹ := by ring
      _ = (M : Real) * x * (M : Real)⁻¹ := by ring
      _ < (K : Real) * (M : Real)⁻¹ := htemp
      _ = (K : Real) / (M : Real) := by simp [div_eq_mul_inv]
  have h_exists_m : ∃ m : ℕ, (m : Real) / (M : Real) > x := ⟨K, hKdivM_gt_x⟩
  let m := Nat.find h_exists_m
  have hm : (m : Real) / (M : Real) > x := Nat.find_spec h_exists_m
  by_cases hm_zero : m = 0
  · have hx_lt_0 : x < 0 := by
      have : (0 : Real) / (M : Real) = 0 := by simp [div_eq_mul_inv, zero_mul]
      have hm0 : (0 : Real) / (M : Real) > x := by simpa [hm_zero] using hm
      rw [this] at hm0
      exact hm0
    refine ⟨0, ?_, ?_⟩
    · simpa using hx_lt_0
    · simpa using hypos
  · have hm_pos : m > 0 := Nat.pos_of_ne_zero hm_zero
    have hm_pred_divM_le_x : (((m-1 : ℕ) : Real) / (M : Real)) ≤ x := by
      by_cases h : ((m-1 : ℕ) : Real) / (M : Real) > x
      · exfalso
        have hlt : (m-1 : ℕ) < m := Nat.sub_lt hm_pos (by norm_num)
        exact Nat.find_min h_exists_m hlt h
      · exact le_of_not_gt h
    have hm_nat_eq : (m : ℕ) = (m-1 : ℕ) + 1 := by omega
    have hm_eq : (m : Real) = ((m-1 : ℕ) : Real) + 1 := by exact_mod_cast hm_nat_eq
    have hm_divM_lt_y : (m : Real) / (M : Real) < y := by
      have htemp : ((m-1 : ℕ) : Real) / (M : Real) + (1 : Real) / (M : Real) ≤
                  x + (1 : Real) / (M : Real) := by
        have := add_le_add_right hm_pred_divM_le_x ((1 : Real) / (M : Real))
        simpa [add_comm, add_left_comm, add_assoc] using this
      calc
        (m : Real) / (M : Real) = (m : Real) * (M : Real)⁻¹ := by simp [div_eq_mul_inv]
        _ = (((m-1 : ℕ) : Real) + 1) * (M : Real)⁻¹ := by rw [hm_eq]
        _ = ((m-1 : ℕ) : Real) * (M : Real)⁻¹ + 1 * (M : Real)⁻¹ := by ring
        _ = ((m-1 : ℕ) : Real) / (M : Real) + (1 : Real) / (M : Real) := by simp [div_eq_mul_inv]
        _ ≤ x + (1 : Real) / (M : Real) := htemp
        _ = x + (M : Real)⁻¹ := by simp
        _ < y := hx_add_invM_lt_y
    let q : ℚ := (m : ℚ) * (M : ℚ)⁻¹
    have h_eq_q : (q : Real) = (m : Real) / (M : Real) := by
      calc
        (q : Real) = ((m : ℚ) : Real) * ((M : ℚ)⁻¹ : Real) := by
          simpa [q, Real.inv_ratCast] using (Real.ratCast_mul (m : ℚ) ((M : ℚ)⁻¹)).symm
        _ = ((m : ℚ) : Real) * (((M : ℚ) : Real)⁻¹) := by simp
        _ = (m : Real) * ((M : Real)⁻¹) := by
          calc
            ((m : ℚ) : Real) * (((M : ℚ) : Real)⁻¹) = (m : Real) * (((M : ℚ) : Real)⁻¹) := by
              rfl
            _ = (m : Real) * ((M : Real)⁻¹) := by
              rfl
        _ = (m : Real) / (M : Real) := by simp [div_eq_mul_inv]
    have hx_lt_q : x < (q : Real) := by
      calc
        x < (m : Real) / (M : Real) := hm
        _ = (q : Real) := h_eq_q.symm
    have hq_lt_y : (q : Real) < y := by
      calc
        (q : Real) = (m : Real) / (M : Real) := h_eq_q
        _ < y := hm_divM_lt_y
    exact ⟨q, hx_lt_q, hq_lt_y⟩

open Classical in
theorem Real.rat_between {x y:Real} (hxy: x < y) : ∃ q:ℚ, x < (q:Real) ∧ (q:Real) < y := by
  by_cases hypos : y > 0
  · exact rat_between_pos_y hxy hypos
  · have hneg_ineq : -y < -x := by linarith
    have hpos_negx : -x > 0 := by linarith
    rcases rat_between_pos_y hneg_ineq hpos_negx with ⟨q', hq'⟩
    refine ⟨-q', ?_, ?_⟩
    · have : (q' : Real) < -x := hq'.2
      have hx_lt_neg_q' : x < -(q' : Real) := by linarith
      apply lt_of_lt_of_eq hx_lt_neg_q'
      exact (map_neg (Real.ratCast_hom : ℚ →+* Real) q').symm
    · have : -y < (q' : Real) := hq'.1
      have hneg_q'_lt_y : -(q' : Real) < y := by linarith
      apply lt_of_eq_of_lt (map_neg (Real.ratCast_hom : ℚ →+* Real) q')
      exact hneg_q'_lt_y

/-- Exercise 5.4.3 -/
theorem Real.floor_exist (x:Real) : ∃! n:ℤ, (n:Real) ≤ x ∧ x < (n:Real)+1 := by sorry

/-- Exercise 5.4.4 -/
theorem Real.exist_inv_nat_le {x:Real} (hx: x.IsPos) : ∃ N:ℤ, N>0 ∧ (N:Real)⁻¹ < x := by sorry

/-- Exercise 5.4.6 -/
theorem Real.dist_lt_iff (ε x y:Real) : |x-y| < ε ↔ y-ε < x ∧ x < y+ε := by sorry

/-- Exercise 5.4.6 -/
theorem Real.dist_le_iff (ε x y:Real) : |x-y| ≤ ε ↔ y-ε ≤ x ∧ x ≤ y+ε := by sorry

/-- Exercise 5.4.7 -/
theorem Real.le_add_eps_iff (x y:Real) : (∀ ε > 0, x ≤ y+ε) ↔ x ≤ y := by sorry

/-- Exercise 5.4.7 -/
theorem Real.dist_le_eps_iff (x y:Real) : (∀ ε > 0, |x-y| ≤ ε) ↔ x = y := by sorry

/-- Exercise 5.4.8 -/
theorem Real.LIM_of_le {x:Real} {a:ℕ → ℚ} (hcauchy: (a:Sequence).IsCauchy) (h: ∀ n, a n ≤ x) :
    LIM a ≤ x := by sorry

/-- Exercise 5.4.8 -/
theorem Real.LIM_of_ge {x:Real} {a:ℕ → ℚ} (hcauchy: (a:Sequence).IsCauchy) (h: ∀ n, a n ≥ x) :
    LIM a ≥ x := by sorry

theorem Real.max_eq (x y:Real) : max x y = if x ≥ y then x else y := max_def' x y

theorem Real.min_eq (x y:Real) : min x y = if x ≤ y then x else y := rfl

/-- Exercise 5.4.9 -/
theorem Real.neg_max (x y:Real) : max x y = - min (-x) (-y) := by sorry

/-- Exercise 5.4.9 -/
theorem Real.neg_min (x y:Real) : min x y = - max (-x) (-y) := by sorry

/-- Exercise 5.4.9 -/
theorem Real.max_comm (x y:Real) : max x y = max y x := by sorry

/-- Exercise 5.4.9 -/
theorem Real.max_self (x:Real) : max x x = x := by sorry

/-- Exercise 5.4.9 -/
theorem Real.max_add (x y z:Real) : max (x + z) (y + z) = max x y + z := by sorry

/-- Exercise 5.4.9 -/
theorem Real.max_mul (x y :Real) {z:Real} (hz: z.IsPos) : max (x * z) (y * z) = max x y * z := by
  sorry
/- Additional exercise: What happens if z is negative? -/

/-- Exercise 5.4.9 -/
theorem Real.min_comm (x y:Real) : min x y = min y x := by sorry

/-- Exercise 5.4.9 -/
theorem Real.min_self (x:Real) : min x x = x := by sorry

/-- Exercise 5.4.9 -/
theorem Real.min_add (x y z:Real) : min (x + z) (y + z) = min x y + z := by sorry

/-- Exercise 5.4.9 -/
theorem Real.min_mul (x y :Real) {z:Real} (hz: z.IsPos) : min (x * z) (y * z) = min x y * z := by
  sorry

/-- Exercise 5.4.9 -/
theorem Real.inv_max {x y :Real} (hx:x.IsPos) (hy:y.IsPos) : (max x y)⁻¹ = min x⁻¹ y⁻¹ := by sorry

/-- Exercise 5.4.9 -/
theorem Real.inv_min {x y :Real} (hx:x.IsPos) (hy:y.IsPos) : (min x y)⁻¹ = max x⁻¹ y⁻¹ := by sorry

/-- Not from textbook: the rationals map as an ordered ring homomorphism into the reals. -/
abbrev Real.ratCast_ordered_hom : ℚ →+*o Real where
  toRingHom := ratCast_hom
  monotone' := by sorry

end Chapter5
