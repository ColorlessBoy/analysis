import Mathlib.Tactic
import Analysis.Section_4_3

set_option doc.verso.suggestions false

/-!
# Analysis I, Section 5.1: Cauchy sequences

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Notion of a sequence of rationals
- Notions of `ε`-steadiness, eventual `ε`-steadiness, and Cauchy sequences

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter5

/--
  Definition 5.1.1 (Sequence). To avoid some technicalities involving dependent types, we extend
  sequences by zero to the left of the starting point {name (full := Sequence.n₀)}`n₀`.
-/
@[ext]
structure Sequence where
  n₀ : ℤ
  seq : ℤ → ℚ
  vanish : ∀ n < n₀, seq n = 0

/-- Sequences can be thought of as functions from {lean}`ℤ` to {lean}`ℚ`. -/
instance Sequence.instCoeFun : CoeFun Sequence (fun _ ↦ ℤ → ℚ) where
  coe := fun a ↦ a.seq

/--
Functions from {lean}`ℕ` to {lean}`ℚ` can be thought of as sequences starting from 0; {name}`Sequence.ofNatFun` performs this conversion.

The {attr}`coe` attribute allows the delaborator to print {lean}`Sequence.ofNatFun f` as {lit}`↑f`, which is more concise; you may safely remove this if you prefer the more explicit notation.
-/
@[coe]
def Sequence.ofNatFun (f : ℕ → ℚ) : Sequence where
    n₀ := 0
    seq n := if n ≥ 0 then f n.toNat else 0
    vanish := by grind

-- Notice how the delaborator prints this as `↑fun x ↦ ↑x ^ 2 : Sequence`.
#check Sequence.ofNatFun (· ^ 2)

/--
If {given}`a : ℕ → ℚ` is used in a context where a {name}`Sequence` is expected, automatically coerce {name}`a` to {lean}`Sequence.ofNatFun a` (which will be pretty-printed as {lean (type :="Sequence")}`↑a`).
-/
instance : Coe (ℕ → ℚ) Sequence where
  coe := Sequence.ofNatFun

abbrev Sequence.mk' (n₀:ℤ) (a: { n // n ≥ n₀ } → ℚ) : Sequence where
  n₀ := n₀
  seq n := if h : n ≥ n₀ then a ⟨n, h⟩ else 0
  vanish := by grind

lemma Sequence.eval_mk {n n₀:ℤ} (a: { n // n ≥ n₀ } → ℚ) (h: n ≥ n₀) :
    (Sequence.mk' n₀ a) n = a ⟨ n, h ⟩ := by grind

@[simp]
lemma Sequence.eval_coe (n:ℕ) (a: ℕ → ℚ) : (a:Sequence) n = a n := by norm_cast

@[simp]
lemma Sequence.eval_coe_at_int (n:ℤ) (a: ℕ → ℚ) : (a:Sequence) n = if n ≥ 0 then a n.toNat else 0 := by norm_cast

@[simp]
lemma Sequence.n0_coe (a: ℕ → ℚ) : (a:Sequence).n₀ = 0 := by norm_cast

/-- Example 5.1.2 -/
abbrev Sequence.squares : Sequence := ((fun n:ℕ ↦ (n^2:ℚ)):Sequence)

/-- Example 5.1.2 -/
example (n:ℕ) : Sequence.squares n = n^2 := Sequence.eval_coe _ _

/-- Example 5.1.2 -/
abbrev Sequence.three : Sequence := ((fun (_:ℕ) ↦ (3:ℚ)):Sequence)

/-- Example 5.1.2 -/
example (n:ℕ) : Sequence.three n = 3 := Sequence.eval_coe _ (fun (_:ℕ) ↦ (3:ℚ))

/-- Example 5.1.2 -/
abbrev Sequence.squares_from_three : Sequence := mk' 3 (·^2)

/-- Example 5.1.2 -/
example (n:ℤ) (hn: n ≥ 3) : Sequence.squares_from_three n = n^2 := Sequence.eval_mk _ hn

-- need to temporarily leave the `Chapter5` namespace to introduce the following notation

end Chapter5

/--
A slight generalization of Definition 5.1.3 - definition of {name}`ε`-steadiness for a sequence with an
arbitrary starting point {lean}`a.n₀`
-/
abbrev Rat.Steady (ε: ℚ) (a: Chapter5.Sequence) : Prop :=
  ∀ n ≥ a.n₀, ∀ m ≥ a.n₀, ε.Close (a n) (a m)

lemma Rat.steady_def (ε: ℚ) (a: Chapter5.Sequence) :
  ε.Steady a ↔ ∀ n ≥ a.n₀, ∀ m ≥ a.n₀, ε.Close (a n) (a m) := by rfl

namespace Chapter5

/--
Definition 5.1.3 - definition of {name}`ε`-steadiness for a sequence starting at 0
-/
lemma Rat.Steady.coe (ε : ℚ) (a:ℕ → ℚ) :
    ε.Steady a ↔ ∀ n m : ℕ, ε.Close (a n) (a m) := by
  constructor
  · intro h n m; specialize h n ?_ m ?_ <;> simp_all
  intro h n hn m hm
  lift n to ℕ using hn
  lift m to ℕ using hm
  simp [h n m]

/--
Not in textbook: the sequence 3, 3 ... is 1-steady.
Intended as a demonstration of {name}`Rat.Steady.coe`.
-/
example : (1:ℚ).Steady ((fun _:ℕ ↦ (3:ℚ)):Sequence) := by
  simp [Rat.Steady.coe, Rat.Close]

/--
{given -show}`hn : n ≥ 0, hm : m ≥ 0`
Compare: if you need to work with {name}`Rat.Steady` on the coercion directly, there will be side
conditions {lean}`hn : n ≥ 0` and {lean}`hm : m ≥ 0` that you will need to deal with.
-/
example : (1:ℚ).Steady ((fun _:ℕ ↦ (3:ℚ)):Sequence) := by
  intro n _ m _; simp_all [Sequence.n0_coe, Sequence.eval_coe_at_int, Rat.Close]

/--
Example 5.1.5: The sequence `1, 0, 1, 0, ...` is 1-steady.
-/
example : (1:ℚ).Steady ((fun n:ℕ ↦ if Even n then (1:ℚ) else (0:ℚ)):Sequence) := by
  rw [Rat.Steady.coe]
  intro n m
  -- Split into four cases based on whether n and m are even or odd
  -- In each case, we know the exact value of a n and a m
  split_ifs <;> simp [Rat.Close]

/--
Example 5.1.5: The sequence `1, 0, 1, 0, ...` is not ½-steady.
-/
example : ¬ (0.5:ℚ).Steady ((fun n:ℕ ↦ if Even n then (1:ℚ) else (0:ℚ)):Sequence) := by
  rw [Rat.Steady.coe]
  by_contra h; specialize h 0 1; simp [Rat.Close] at h
  norm_num at h

/--
Example 5.1.5: The sequence 0.1, 0.01, 0.001, ... is 0.1-steady.
-/
example : (0.1:ℚ).Steady ((fun n:ℕ ↦ (10:ℚ) ^ (-(n:ℤ)-1) ):Sequence) := by
  rw [Rat.Steady.coe]
  intro n m; unfold Rat.Close
  wlog h : m ≤ n
  · specialize this m n (by linarith); rwa [abs_sub_comm]
  rw [abs_sub_comm, abs_of_nonneg]
  . rw [show (0.1:ℚ) = (10:ℚ)^(-1:ℤ) - 0 by norm_num]
    gcongr <;> try grind
    positivity
  linarith [show (10:ℚ) ^ (-(n:ℤ)-1) ≤ (10:ℚ) ^ (-(m:ℤ)-1) by gcongr; norm_num]

/--
Example 5.1.5: The sequence 0.1, 0.01, 0.001, ... is not 0.01-steady. Left as an exercise.
-/
example : ¬(0.01:ℚ).Steady ((fun n:ℕ ↦ (10:ℚ) ^ (-(n:ℤ)-1) ):Sequence) := by
  rw [Rat.Steady.coe]
  by_contra h; specialize h 0 1; simp [Rat.Close] at h
  norm_num at h

/-- Example 5.1.5: The sequence 1, 2, 4, 8, ... is not ε-steady for any ε. Left as an exercise.
 -/
example (ε:ℚ) : ¬ ε.Steady ((fun n:ℕ ↦ (2 ^ (n+1):ℚ) ):Sequence) := by
  rw [Rat.Steady.coe]
  intro h
  have h_bound : ∀ m : ℕ, (2 : ℚ) ^ (m+1 : ℕ) ≤ ε + 2 := by
    intro m
    have hm := h 0 m
    have h_abs := abs_le.mp hm
    have h_one : (2 : ℚ) ^ (0+1 : ℕ) = (2 : ℚ) := by norm_num
    have h_abs_left : -ε ≤ (2 : ℚ) - (2 : ℚ) ^ (m+1 : ℕ) := by
      simpa [h_one] using h_abs.left
    linarith
  rcases exists_nat_gt (ε + 2) with ⟨N, hN⟩
  have hN_bound := h_bound N
  have h_lt : (N : ℚ) < (2 : ℚ) ^ (N+1 : ℕ) := by
    have h_nat : N < 2 ^ (N+1 : ℕ) :=
      calc
        N < 2 ^ N := N.lt_two_pow_self
        _ ≤ 2 ^ (N+1 : ℕ) := by
          calc
            2 ^ N = 2 ^ N * 1 := by simp
            _ ≤ 2 ^ N * 2 := Nat.mul_le_mul_left _ (by norm_num)
            _ = 2 ^ (N+1 : ℕ) := by rw [Nat.pow_succ]
    simpa using (by exact_mod_cast h_nat : (N : ℚ) < ((2 ^ (N+1 : ℕ) : ℕ) : ℚ))
  linarith

/-- Example 5.1.5:The sequence 2, 2, 2, ... is ε-steady for any ε > 0.
-/
example (ε:ℚ) (hε: ε>0) : ε.Steady ((fun _:ℕ ↦ (2:ℚ) ):Sequence) := by
  rw [Rat.Steady.coe]; simp [Rat.Close]; positivity

/--
The sequence 10, 0, 0, ... is 10-steady.
-/
example : (10:ℚ).Steady ((fun n:ℕ ↦ if n = 0 then (10:ℚ) else (0:ℚ)):Sequence) := by
  rw [Rat.Steady.coe]; intro n m
  -- Split into 4 cases based on whether n and m are 0 or not
  split_ifs <;> simp [Rat.Close]

/--
The sequence 10, 0, 0, ... is not ε-steady for any smaller value of ε.
-/
example (ε:ℚ) (hε:ε<10):  ¬ ε.Steady ((fun n:ℕ ↦ if n = 0 then (10:ℚ) else (0:ℚ)):Sequence) := by
  contrapose! hε; rw [Rat.Steady.coe] at hε; specialize hε 0 1; simpa [Rat.Close] using hε

/--
  {name}`Sequence.from` starts {lean}`a : Sequence` from {name}`n₁`.  It is intended for use when {lean}`n₁ ≥ n₀`, but returns
  the "junk" value of the original sequence {name}`a` otherwise.
-/
abbrev Sequence.from (a:Sequence) (n₁:ℤ) : Sequence :=
  mk' (max a.n₀ n₁) (fun n ↦ a (n:ℤ))

lemma Sequence.from_eval (a:Sequence) {n₁ n:ℤ} (hn: n ≥ n₁) :
  (a.from n₁) n = a n := by simp [hn]; intro h; exact (a.vanish _ h).symm

end Chapter5

/-- Definition 5.1.6 (Eventually ε-steady) -/
abbrev Rat.EventuallySteady (ε: ℚ) (a: Chapter5.Sequence) : Prop := ∃ N ≥ a.n₀, ε.Steady (a.from N)

lemma Rat.eventuallySteady_def (ε: ℚ) (a: Chapter5.Sequence) :
  ε.EventuallySteady a ↔ ∃ N ≥ a.n₀, ε.Steady (a.from N) := by rfl

namespace Chapter5

/--
Example 5.1.7: The sequence 1, 1/2, 1/3, ... is not 0.1-steady
-/
lemma Sequence.ex_5_1_7_a : ¬ (0.1:ℚ).Steady ((fun n:ℕ ↦ (n+1:ℚ)⁻¹ ):Sequence) := by
  intro h; rw [Rat.Steady.coe] at h; specialize h 0 2; simp [Rat.Close] at h; norm_num at h

/--
Example 5.1.7: The sequence `a_10, a_11, a_12, ...` is 0.1-steady
-/
lemma Sequence.ex_5_1_7_b : (0.1:ℚ).Steady (((fun n:ℕ ↦ (n+1:ℚ)⁻¹ ):Sequence).from 10) := by
  rw [Rat.Steady]
  intro n hn m hm; simp at hn hm
  lift n to ℕ using (by omega)
  lift m to ℕ using (by omega)
  simp_all [Rat.Close]
  wlog h : m ≤ n
  · specialize this m n _ _ _ <;> try omega
    rwa [abs_sub_comm] at this
  rw [abs_sub_comm]
  have : ((n:ℚ) + 1)⁻¹ ≤ ((m:ℚ) + 1)⁻¹ := by gcongr
  rw [abs_of_nonneg (by linarith), show (0.1:ℚ) = (10:ℚ)⁻¹ - 0 by norm_num]
  gcongr
  · norm_cast; omega
  positivity

/--
Example 5.1.7: The sequence 1, 1/2, 1/3, ... is eventually 0.1-steady
-/
lemma Sequence.ex_5_1_7_c : (0.1:ℚ).EventuallySteady ((fun n:ℕ ↦ (n+1:ℚ)⁻¹ ):Sequence) :=
  ⟨10, by simp, ex_5_1_7_b⟩

/--
Example 5.1.7

The sequence 10, 0, 0, ... is eventually ε-steady for every ε > 0. Left as an exercise.
-/
lemma Sequence.ex_5_1_7_d {ε:ℚ} (hε:ε>0) :
    ε.EventuallySteady ((fun n:ℕ ↦ if n=0 then (10:ℚ) else (0:ℚ) ):Sequence) := by
    use 1
    constructor
    · simp
    rw [Rat.Steady]
    intro n hn m hm
    rw [Rat.Close]
    simp at hn hm
    have ha_n : ((fun n:ℕ ↦ if n=0 then (10:ℚ) else (0:ℚ) ):Sequence) n = 0 := by
      rw [Sequence.eval_coe_at_int]
      have hn0 : (n : ℤ) ≥ 0 := by omega
      rw [if_pos hn0]
      have hnz : n.toNat ≠ 0 := by omega
      simp [hnz]
    have ha_m : ((fun n:ℕ ↦ if n=0 then (10:ℚ) else (0:ℚ) ):Sequence) m = 0 := by
      rw [Sequence.eval_coe_at_int]
      have hm0 : (m : ℤ) ≥ 0 := by omega
      rw [if_pos hm0]
      have hmz : m.toNat ≠ 0 := by omega
      simp [hmz]
    rw [Sequence.from_eval _ hn, Sequence.from_eval _ hm, ha_n, ha_m, sub_zero, abs_of_nonneg (by norm_num)]
    linarith

abbrev Sequence.IsCauchy (a:Sequence) : Prop := ∀ ε > (0:ℚ), ε.EventuallySteady a

lemma Sequence.isCauchy_def (a:Sequence) :
  a.IsCauchy ↔ ∀ ε > (0:ℚ), ε.EventuallySteady a := by rfl

/-- Definition of Cauchy sequences, for a sequence starting at {lean}`0` -/
lemma Sequence.IsCauchy.coe (a:ℕ → ℚ) :
    (a:Sequence).IsCauchy ↔ ∀ ε > (0:ℚ), ∃ N, ∀ j ≥ N, ∀ k ≥ N,
    Section_4_3.dist (a j) (a k) ≤ ε := by
  constructor <;> intro h ε hε
  · rcases h ε hε with ⟨N, hN, h'⟩
    lift N to ℕ using hN; use N
    intro j hj k hk
    have hj_eval : ((a : Sequence).from N) j = a j := by
      calc
        ((a : Sequence).from N) j = ((a : Sequence).from (N : ℤ)) (j : ℤ) := rfl
        _ = (a : Sequence) (j : ℤ) :=
          Sequence.from_eval (a : Sequence) (by exact_mod_cast hj)
        _ = a j := by simp [Sequence.eval_coe_at_int,
          show (j : ℤ) ≥ (0 : ℤ) from by exact_mod_cast (Nat.zero_le j)]
    have hk_eval : ((a : Sequence).from N) k = a k := by
      calc
        ((a : Sequence).from N) k = ((a : Sequence).from (N : ℤ)) (k : ℤ) := rfl
        _ = (a : Sequence) (k : ℤ) :=
          Sequence.from_eval (a : Sequence) (by exact_mod_cast hk)
        _ = a k := by simp [Sequence.eval_coe_at_int,
          show (k : ℤ) ≥ (0 : ℤ) from by exact_mod_cast (Nat.zero_le k)]
    have h'_close : ε.Close ((a : Sequence).from N j) ((a : Sequence).from N k) := by
      rw [Rat.Steady] at h'
      have h_n₀ : ((a : Sequence).from N).n₀ = (N : ℤ) := by simp
      have hj_n₀ : (j : ℤ) ≥ ((a : Sequence).from N).n₀ := by
        rw [h_n₀]; exact_mod_cast hj
      have hk_n₀ : (k : ℤ) ≥ ((a : Sequence).from N).n₀ := by
        rw [h_n₀]; exact_mod_cast hk
      exact h' (j : ℤ) hj_n₀ (k : ℤ) hk_n₀
    rw [Rat.Close] at h'_close
    rw [hj_eval, hk_eval] at h'_close
    simpa [Section_4_3.dist, Section_4_3.abs_eq_abs] using h'_close
  choose N h' using h ε hε
  refine ⟨ max N 0, by simp, ?_ ⟩
  rw [Rat.Steady]
  intro n hn m hm; simp at hn hm
  have hn0 : (n : ℤ) ≥ (0 : ℤ) := by omega
  have hm0 : (m : ℤ) ≥ (0 : ℤ) := by omega
  have hmax : (max (N : ℤ) 0 : ℤ) = (N : ℤ) := by simp
  have h_ne_from_eval_n : (n : ℤ) ≥ (max (N : ℤ) 0 : ℤ) := by simpa [hmax] using hn
  have h_ne_from_eval_m : (m : ℤ) ≥ (max (N : ℤ) 0 : ℤ) := by simpa [hmax] using hm
  lift n to ℕ using hn0
  lift m to ℕ using hm0
  have hn_nat : n ≥ N := by exact_mod_cast hn
  have hm_nat : m ≥ N := by exact_mod_cast hm
  have h_target := h' n hn_nat m hm_nat
  rw [Rat.Close]
  calc
    |((a : Sequence).from (max N 0)) n - ((a : Sequence).from (max N 0)) m|
        = |(a : Sequence) (n : ℤ) - (a : Sequence) (m : ℤ)| := by
      rw [Sequence.from_eval (a : Sequence) h_ne_from_eval_n,
          Sequence.from_eval (a : Sequence) h_ne_from_eval_m]
    _ = |a n - a m| := by
      simp [Sequence.eval_coe_at_int,
        show (n : ℤ) ≥ (0 : ℤ) from by exact_mod_cast (Nat.zero_le n),
        show (m : ℤ) ≥ (0 : ℤ) from by exact_mod_cast (Nat.zero_le m)]
    _ ≤ ε := by
      simpa [Section_4_3.dist, Section_4_3.abs_eq_abs] using h_target

lemma Sequence.IsCauchy.mk {n₀:ℤ} (a: {n // n ≥ n₀} → ℚ) :
    (mk' n₀ a).IsCauchy ↔ ∀ ε > (0:ℚ), ∃ N ≥ n₀, ∀ j ≥ N, ∀ k ≥ N,
    Section_4_3.dist (mk' n₀ a j) (mk' n₀ a k) ≤ ε := by
  constructor <;> intro h ε hε
  · rcases h ε hε with ⟨N, hN, h'⟩
    have hN_simp : N ≥ n₀ := by simpa using hN
    have hmax_n₀_N : max n₀ N = N := max_eq_right hN_simp
    refine ⟨N, hN_simp, ?_⟩
    intro j hj k hk
    have hj_eval : ((mk' n₀ a).from N) j = (mk' n₀ a) j := by
      simp [hmax_n₀_N, hj]
    have hk_eval : ((mk' n₀ a).from N) k = (mk' n₀ a) k := by
      simp [hmax_n₀_N, hk]
    have h'_close : ε.Close (((mk' n₀ a).from N) j) (((mk' n₀ a).from N) k) := by
      rw [Rat.Steady] at h'
      have h_n₀ : ((mk' n₀ a).from N).n₀ = (N : ℤ) := by
        simp [hmax_n₀_N]
      have hj_n₀ : (j : ℤ) ≥ ((mk' n₀ a).from N).n₀ := by
        rw [h_n₀]; exact hj
      have hk_n₀ : (k : ℤ) ≥ ((mk' n₀ a).from N).n₀ := by
        rw [h_n₀]; exact hk
      exact h' (j : ℤ) hj_n₀ (k : ℤ) hk_n₀
    rw [Rat.Close] at h'_close
    rw [hj_eval, hk_eval] at h'_close
    have h_j_ge_n₀ : j ≥ n₀ := by omega
    have h_k_ge_n₀ : k ≥ n₀ := by omega
    rw [Sequence.eval_mk a h_j_ge_n₀, Sequence.eval_mk a h_k_ge_n₀] at h'_close
    rw [Sequence.eval_mk a h_j_ge_n₀, Sequence.eval_mk a h_k_ge_n₀]
    simpa [Section_4_3.dist, Section_4_3.abs_eq_abs] using h'_close
  · choose N hN h' using h ε hε
    have hmax : max n₀ N = N := max_eq_right hN
    refine ⟨ max n₀ N, by simp, ?_ ⟩
    rw [Rat.Steady]
    intro n hn m hm; simp [hmax] at hn hm
    have h_target := h' n hn m hm
    rw [Rat.Close]
    have h_fn : ((mk' n₀ a).from (max n₀ N)) n = (mk' n₀ a) n := by
      simp [hmax, hn]
    have h_fm : ((mk' n₀ a).from (max n₀ N)) m = (mk' n₀ a) m := by
      simp [hmax, hm]
    rw [h_fn, h_fm]
    have h_ge_n₀_n : n ≥ n₀ := by omega
    have h_ge_n₀_m : m ≥ n₀ := by omega
    rw [Sequence.eval_mk a h_ge_n₀_n, Sequence.eval_mk a h_ge_n₀_m] at h_target
    rw [Sequence.eval_mk a h_ge_n₀_n, Sequence.eval_mk a h_ge_n₀_m]
    simpa [Section_4_3.dist, Section_4_3.abs_eq_abs] using h_target

noncomputable def sqrt_two_fun (n : ℕ) : ℚ := ((⌊ (Real.sqrt 2)*10^n ⌋ / 10^n):ℚ)

noncomputable abbrev Sequence.sqrt_two : Sequence := (sqrt_two_fun : Sequence)

noncomputable def sqrt_two_seq_ℝ (n : ℕ) : ℝ := (⌊(Real.sqrt 2) * (10 : ℝ) ^ n⌋ : ℝ) / ((10 : ℝ) ^ n)

lemma sqrt_two_coe (k : ℕ) : (sqrt_two_fun k : ℝ) = sqrt_two_seq_ℝ k := by
  simp [sqrt_two_fun, sqrt_two_seq_ℝ]

lemma sqrt_two_seq_ℝ_ge_one (k : ℕ) : (1 : ℝ) ≤ sqrt_two_seq_ℝ k := by
  rw [sqrt_two_seq_ℝ]
  have h_sqrt2_ge_one : (1 : ℝ) ≤ Real.sqrt 2 := by
    calc
      (1 : ℝ) = Real.sqrt (1 : ℝ) := by norm_num
      _ ≤ Real.sqrt 2 := Real.sqrt_le_sqrt (by norm_num)
  have h_mul : (1 : ℝ) * ((10 : ℝ) ^ k) ≤ Real.sqrt 2 * ((10 : ℝ) ^ k) :=
    mul_le_mul_of_nonneg_right h_sqrt2_ge_one (by positivity)
  have h_floor : (⌊(1 : ℝ) * ((10 : ℝ) ^ k)⌋ : ℤ) ≤ ⌊Real.sqrt 2 * ((10 : ℝ) ^ k)⌋ :=
    Int.floor_mono h_mul
  have h_floor_one : (⌊(1 : ℝ) * ((10 : ℝ) ^ k)⌋ : ℤ) = (10 : ℤ) ^ k := by
    calc
      (⌊(1 : ℝ) * ((10 : ℝ) ^ k)⌋ : ℤ) = (⌊(10 : ℝ) ^ k⌋ : ℤ) := by norm_num
      _ = (⌊(((10 : ℕ) ^ k : ℕ) : ℝ)⌋ : ℤ) := by norm_num
      _ = ((10 : ℕ) ^ k : ℤ) := by
        simpa using (Int.floor_natCast ((10 : ℕ) ^ k) : (⌊(((10 : ℕ) ^ k : ℕ) : ℝ)⌋ : ℤ) = ((10 : ℕ) ^ k : ℤ))
      _ = (10 : ℤ) ^ k := by norm_num
  have h_ineq_int : (10 : ℤ) ^ k ≤ ⌊Real.sqrt 2 * ((10 : ℝ) ^ k)⌋ := by
    rw [← h_floor_one]; exact h_floor
  have h_ineq_ℝ : ((10 : ℝ) ^ k : ℝ) ≤ (⌊Real.sqrt 2 * ((10 : ℝ) ^ k)⌋ : ℝ) := by exact_mod_cast h_ineq_int
  have h_pos : (0 : ℝ) < (10 : ℝ) ^ k := by positivity
  calc
    (1 : ℝ) = ((10 : ℝ) ^ k : ℝ) / ((10 : ℝ) ^ k : ℝ) := by field_simp [h_pos.ne']
    _ ≤ (⌊Real.sqrt 2 * ((10 : ℝ) ^ k)⌋ : ℝ) / ((10 : ℝ) ^ k : ℝ) := by
      gcongr

lemma sqrt_two_seq_ℝ_le_sqrt2 (k : ℕ) : sqrt_two_seq_ℝ k ≤ Real.sqrt 2 := by
  rw [sqrt_two_seq_ℝ]
  have h_floor_le : (⌊Real.sqrt 2 * ((10 : ℝ) ^ k)⌋ : ℝ) ≤ Real.sqrt 2 * ((10 : ℝ) ^ k) :=
    Int.floor_le _
  have h_pos : (0 : ℝ) < (10 : ℝ) ^ k := by positivity
  calc
    (⌊Real.sqrt 2 * ((10 : ℝ) ^ k)⌋ : ℝ) / ((10 : ℝ) ^ k) ≤ (Real.sqrt 2 * ((10 : ℝ) ^ k)) / ((10 : ℝ) ^ k) := by
      gcongr
    _ = Real.sqrt 2 := by field_simp [h_pos.ne']

lemma sqrt_two_seq_ℝ_sub_lt (k : ℕ) : Real.sqrt 2 - sqrt_two_seq_ℝ k < 1 / ((10 : ℝ) ^ k) := by
  rw [sqrt_two_seq_ℝ]
  have h_lt_floor_add_one : Real.sqrt 2 * ((10 : ℝ) ^ k) < (⌊Real.sqrt 2 * ((10 : ℝ) ^ k)⌋ : ℝ) + 1 :=
    Int.lt_floor_add_one _
  have h_sub : Real.sqrt 2 * ((10 : ℝ) ^ k) - (⌊Real.sqrt 2 * ((10 : ℝ) ^ k)⌋ : ℝ) < 1 := by linarith
  have h_pos : (0 : ℝ) < (10 : ℝ) ^ k := by positivity
  have h_eq : Real.sqrt 2 - ((⌊Real.sqrt 2 * ((10 : ℝ) ^ k)⌋ : ℝ) / ((10 : ℝ) ^ k))
      = ((Real.sqrt 2 * ((10 : ℝ) ^ k) - (⌊Real.sqrt 2 * ((10 : ℝ) ^ k)⌋ : ℝ)) / ((10 : ℝ) ^ k)) := by
    calc
      Real.sqrt 2 - ((⌊Real.sqrt 2 * ((10 : ℝ) ^ k)⌋ : ℝ) / ((10 : ℝ) ^ k))
          = (Real.sqrt 2 * ((10 : ℝ) ^ k) / ((10 : ℝ) ^ k)) - ((⌊Real.sqrt 2 * ((10 : ℝ) ^ k)⌋ : ℝ) / ((10 : ℝ) ^ k)) := by
        field_simp [h_pos.ne']
      _ = ((Real.sqrt 2 * ((10 : ℝ) ^ k) - (⌊Real.sqrt 2 * ((10 : ℝ) ^ k)⌋ : ℝ)) / ((10 : ℝ) ^ k)) := by ring
  rw [h_eq]
  gcongr

lemma sqrt_two_sub_sqrt2_nonneg (k : ℕ) : 0 ≤ (Real.sqrt 2 : ℝ) - sqrt_two_seq_ℝ k := by
  linarith [sqrt_two_seq_ℝ_le_sqrt2 k]

lemma sqrt_two_lt_two_ℝ : Real.sqrt 2 < (2 : ℝ) := by
  calc
    Real.sqrt 2 < Real.sqrt (4 : ℝ) := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    _ = (2 : ℝ) := by norm_num

lemma sqrt_two_fun_ge_one (k : ℕ) : (1 : ℚ) ≤ sqrt_two_fun k := by
  have h : (1 : ℝ) ≤ (sqrt_two_fun k : ℝ) := by
    rw [sqrt_two_coe]
    exact sqrt_two_seq_ℝ_ge_one k
  exact_mod_cast h

lemma sqrt_two_fun_le_two (k : ℕ) : sqrt_two_fun k < (2 : ℚ) := by
  have h : (sqrt_two_fun k : ℝ) < (2 : ℝ) := by
    rw [sqrt_two_coe]
    calc
      sqrt_two_seq_ℝ k ≤ Real.sqrt 2 := sqrt_two_seq_ℝ_le_sqrt2 k
      _ < (2 : ℝ) := sqrt_two_lt_two_ℝ
  exact_mod_cast h

theorem Sequence.ex_5_1_10_a : (1:ℚ).Steady sqrt_two := by
  rw [Rat.Steady.coe]
  intro n m
  have h_eq_n : sqrt_two n = sqrt_two_fun n := by
    simp [sqrt_two, sqrt_two_fun]
  have h_eq_m : sqrt_two m = sqrt_two_fun m := by
    simp [sqrt_two, sqrt_two_fun]
  have h_low_n : (1 : ℚ) ≤ sqrt_two_fun n := sqrt_two_fun_ge_one n
  have h_low_m : (1 : ℚ) ≤ sqrt_two_fun m := sqrt_two_fun_ge_one m
  have h_high_n : sqrt_two_fun n < (2 : ℚ) := sqrt_two_fun_le_two n
  have h_high_m : sqrt_two_fun m < (2 : ℚ) := sqrt_two_fun_le_two m
  have h_goal : |sqrt_two_fun n - sqrt_two_fun m| ≤ (1 : ℚ) := by
    rw [abs_le]
    constructor <;> nlinarith
  simpa [h_eq_n, h_eq_m] using h_goal

theorem Sequence.ex_5_1_10_b : (0.1:ℚ).Steady (sqrt_two.from 1) := by
  rw [Rat.Steady]
  intro n hn m hm; simp at hn hm
  have hn0 : (n : ℤ) ≥ (0 : ℤ) := by omega
  have hm0 : (m : ℤ) ≥ (0 : ℤ) := by omega
  have hn_eval : (sqrt_two.from 1) n = sqrt_two n := Sequence.from_eval sqrt_two hn
  have hm_eval : (sqrt_two.from 1) m = sqrt_two m := Sequence.from_eval sqrt_two hm
  rw [hn_eval, hm_eval, Rat.Close]
  lift n to ℕ using hn0
  lift m to ℕ using hm0
  have hn_nat : n ≥ 1 := by exact_mod_cast hn
  have hm_nat : m ≥ 1 := by exact_mod_cast hm
  have h_eq_n : sqrt_two n = sqrt_two_fun n := by
    simp [sqrt_two, sqrt_two_fun]
  have h_eq_m : sqrt_two m = sqrt_two_fun m := by
    simp [sqrt_two, sqrt_two_fun]
  -- Work in ℝ for the inequality
  have h_sub_n_ℝ : Real.sqrt 2 - (sqrt_two_fun n : ℝ) < 1 / ((10 : ℝ) ^ n) := by
    rw [sqrt_two_coe]
    exact sqrt_two_seq_ℝ_sub_lt n
  have h_sub_m_ℝ : Real.sqrt 2 - (sqrt_two_fun m : ℝ) < 1 / ((10 : ℝ) ^ m) := by
    rw [sqrt_two_coe]
    exact sqrt_two_seq_ℝ_sub_lt m
  have h_nonneg_sub_n_ℝ : 0 ≤ Real.sqrt 2 - (sqrt_two_fun n : ℝ) := by
    rw [sqrt_two_coe]
    exact sqrt_two_sub_sqrt2_nonneg n
  have h_nonneg_sub_m_ℝ : 0 ≤ Real.sqrt 2 - (sqrt_two_fun m : ℝ) := by
    rw [sqrt_two_coe]
    exact sqrt_two_sub_sqrt2_nonneg m
  have h_abs_sub_max (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : |x - y| ≤ max x y := by
    by_cases hxy : x ≤ y
    · have : x - y ≤ 0 := by linarith
      rw [abs_of_nonpos this]
      have : -(x - y) = y - x := by ring
      rw [this]
      have hyx : y - x ≤ y := by nlinarith
      exact le_trans hyx (le_max_right _ _)
    · have hyx : y ≤ x := by linarith
      rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
      have hxy' : x - y ≤ x := by nlinarith
      exact le_trans hxy' (le_max_left _ _)
  have h_diff_ℝ : |(sqrt_two_fun n : ℝ) - (sqrt_two_fun m : ℝ)| < (0.1 : ℝ) := by
    calc
      |(sqrt_two_fun n : ℝ) - (sqrt_two_fun m : ℝ)|
          = |(Real.sqrt 2 - (sqrt_two_fun m : ℝ)) - (Real.sqrt 2 - (sqrt_two_fun n : ℝ))| := by ring_nf
      _ ≤ max (Real.sqrt 2 - (sqrt_two_fun n : ℝ)) (Real.sqrt 2 - (sqrt_two_fun m : ℝ)) := by
        have h := h_abs_sub_max (Real.sqrt 2 - (sqrt_two_fun n : ℝ)) (Real.sqrt 2 - (sqrt_two_fun m : ℝ))
          h_nonneg_sub_n_ℝ h_nonneg_sub_m_ℝ
        simpa [abs_sub_comm] using h
      _ < max (1 / ((10 : ℝ) ^ n)) (1 / ((10 : ℝ) ^ m)) := by
        have h_max1 : Real.sqrt 2 - (sqrt_two_fun n : ℝ) < max (1 / ((10 : ℝ) ^ n)) (1 / ((10 : ℝ) ^ m)) :=
          lt_of_lt_of_le h_sub_n_ℝ (le_max_left _ _)
        have h_max2 : Real.sqrt 2 - (sqrt_two_fun m : ℝ) < max (1 / ((10 : ℝ) ^ n)) (1 / ((10 : ℝ) ^ m)) :=
          lt_of_lt_of_le h_sub_m_ℝ (le_max_right _ _)
        exact max_lt h_max1 h_max2
      _ ≤ (1 / ((10 : ℝ) ^ 1)) := by
        have hpow_n : (10 : ℝ) ^ 1 ≤ (10 : ℝ) ^ n := by
          refine Nat.le_induction ?_ (fun k hk h_ih => ?_) n hn_nat
          · norm_num
          · rw [pow_succ]
            calc
              (10 : ℝ) ^ 1 ≤ (10 : ℝ) ^ k := h_ih
              _ = (10 : ℝ) ^ k * 1 := by ring
              _ ≤ (10 : ℝ) ^ k * 10 := by nlinarith
              _ = (10 : ℝ) ^ (k + 1) := by ring
        have hpow_m : (10 : ℝ) ^ 1 ≤ (10 : ℝ) ^ m := by
          refine Nat.le_induction ?_ (fun k hk h_ih => ?_) m hm_nat
          · norm_num
          · rw [pow_succ]
            calc
              (10 : ℝ) ^ 1 ≤ (10 : ℝ) ^ k := h_ih
              _ = (10 : ℝ) ^ k * 1 := by ring
              _ ≤ (10 : ℝ) ^ k * 10 := by nlinarith
              _ = (10 : ℝ) ^ (k + 1) := by ring
        have hn_pos : 0 < (10 : ℝ) ^ n := pow_pos (by norm_num : (0 : ℝ) < 10) n
        have hm_pos : 0 < (10 : ℝ) ^ m := pow_pos (by norm_num : (0 : ℝ) < 10) m
        have h10_pos : 0 < (10 : ℝ) ^ 1 := pow_pos (by norm_num : (0 : ℝ) < 10) 1
        refine max_le ?_ ?_
        · exact (one_div_le_one_div hn_pos h10_pos).mpr hpow_n
        · exact (one_div_le_one_div hm_pos h10_pos).mpr hpow_m
      _ = (0.1 : ℝ) := by norm_num
  have h_diff_ℚ : |sqrt_two_fun n - sqrt_two_fun m| < (0.1 : ℚ) := by
    have h_temp : (|sqrt_two_fun n - sqrt_two_fun m| : ℝ) < (0.1 : ℝ) := by
      have h_eq : |(sqrt_two_fun n : ℝ) - (sqrt_two_fun m : ℝ)| = (|sqrt_two_fun n - sqrt_two_fun m| : ℝ) := by simp
      rw [h_eq] at h_diff_ℝ
      exact h_diff_ℝ
    have h_temp' : ((|sqrt_two_fun n - sqrt_two_fun m| : ℚ) : ℝ) < ((0.1 : ℚ) : ℝ) := by
      simpa using h_temp
    exact (Rat.cast_lt (K := ℝ)).mp h_temp'
  have h_diff_ℚ' : |sqrt_two_fun n - sqrt_two_fun m| ≤ (0.1 : ℚ) := by linarith
  simpa [h_eq_n, h_eq_m] using h_diff_ℚ'

theorem Sequence.ex_5_1_10_c : (0.1:ℚ).EventuallySteady sqrt_two :=
  ⟨1, by simp, ex_5_1_10_b⟩

/-- Proposition 5.1.11. The harmonic sequence, defined as a₁ = 1, a₂ = 1/2, ... is a Cauchy sequence. -/
theorem Sequence.IsCauchy.harmonic : (mk' 1 (fun n ↦ (1:ℚ)/n)).IsCauchy := by
  rw [IsCauchy.mk]
  intro ε hε
  -- We go by reverse from the book - first choose N such that N > 1/ε
  obtain ⟨ N, hN : N > 1/ε ⟩ := exists_nat_gt (1 / ε)
  have hN' : N > 0 := by
    have hpos : (1/ε : ℚ) > 0 := by
      have : ε > 0 := hε
      positivity
    have hNpos : (N : ℚ) > 0 := by linarith
    exact_mod_cast hNpos
  refine ⟨ N, by norm_cast, ?_ ⟩
  intro j hj k hk
  lift j to ℕ using (by linarith)
  lift k to ℕ using (by linarith)
  norm_cast at hj hk
  simp [show j ≥ 1 by linarith, show k ≥ 1 by linarith]

  have hdist : Section_4_3.dist ((1:ℚ)/j) ((1:ℚ)/k) ≤ (1:ℚ)/N := by
    have h_abs : |((1:ℚ)/j) - ((1:ℚ)/k)| ≤ (1:ℚ)/N := by
      rw [_root_.abs_le]
      have h1 : 1/j ≤ (1:ℚ)/N := by gcongr
      have h1_nonneg : (0 : ℚ) ≤ 1/j := by positivity
      have h2 : 1/k ≤ (1:ℚ)/N := by gcongr
      have h2_nonneg : (0 : ℚ) ≤ 1/k := by positivity
      constructor
      · nlinarith
      · nlinarith
    simpa [Section_4_3.dist_eq, Section_4_3.abs_eq_abs] using h_abs
  have h_mul_ineq : 1 ≤ (N : ℚ) * ε := by
    have hN_rat : (N : ℚ) > 1/ε := hN
    have h_eps_pos : ε > 0 := hε
    have : 1 < (N : ℚ) * ε := by
      calc
        1 = (1 / ε) * ε := by field_simp [h_eps_pos.ne']
        _ < (N : ℚ) * ε := mul_lt_mul_of_pos_right hN_rat h_eps_pos
    exact this.le
  have hN_ge : (1 : ℚ)/N ≤ ε := by
    have h_N_pos : (N : ℚ) > 0 := by exact_mod_cast hN'
    calc
      (1 : ℚ)/N ≤ ((N : ℚ) * ε)/N := by
        gcongr
      _ = ε := by field_simp [h_N_pos.ne']
  simpa using hdist.trans hN_ge

abbrev BoundedBy {n:ℕ} (a: Fin n → ℚ) (M:ℚ) : Prop := ∀ i, |a i| ≤ M

/--
  Definition 5.1.12 (bounded sequences). Here we start sequences from {lean}`0` rather than {lean}`1` to align
  better with Mathlib conventions.
-/
lemma boundedBy_def {n:ℕ} (a: Fin n → ℚ) (M:ℚ) : BoundedBy a M ↔ ∀ i, |a i| ≤ M := by rfl

abbrev Sequence.BoundedBy (a:Sequence) (M:ℚ) : Prop := ∀ n, |a n| ≤ M

/-- Definition 5.1.12 (bounded sequences) -/
lemma Sequence.boundedBy_def (a:Sequence) (M:ℚ) : a.BoundedBy M ↔ ∀ n, |a n| ≤ M := by rfl

abbrev Sequence.IsBounded (a:Sequence) : Prop := ∃ M ≥ 0, a.BoundedBy M

/-- Definition 5.1.12 (bounded sequences) -/
lemma Sequence.isBounded_def (a:Sequence) : a.IsBounded ↔ ∃ M ≥ 0, a.BoundedBy M := by rfl

/-- Example 5.1.13 -/
example : BoundedBy ![1,-2,3,-4] 4 := by intro i; fin_cases i <;> norm_num

/-- Example 5.1.13 -/
example : ¬((fun n:ℕ ↦ (-1)^n * (n+1:ℚ)):Sequence).IsBounded := by
  rw [Sequence.isBounded_def]
  intro h
  rcases h with ⟨M, hM_nonneg, hM⟩
  rcases exists_nat_gt M with ⟨n, hn⟩
  have h_val : |((fun n:ℕ ↦ (-1)^n * (n+1:ℚ)) : Sequence) (n : ℤ)| = (n+1 : ℚ) := by
    calc
      |((fun n:ℕ ↦ (-1)^n * (n+1:ℚ)) : Sequence) (n : ℤ)|
          = |(-1 : ℚ)^n * (n+1 : ℚ)| := by simp [Sequence.eval_coe_at_int]
      _ = |(-1 : ℚ)^n| * |(n+1 : ℚ)| := by rw [abs_mul]
      _ = 1 * |(n+1 : ℚ)| := by simp
      _ = |(n+1 : ℚ)| := by simp
      _ = (n+1 : ℚ) := by
        have : (0 : ℚ) ≤ (n : ℚ) + 1 := by positivity
        simp [this]
  have h_bound := hM (n : ℤ)
  rw [h_val] at h_bound
  have : (n : ℚ) + 1 > M := by linarith
  linarith

/-- Example 5.1.13 -/
example : ((fun n:ℕ ↦ (-1:ℚ)^n):Sequence).IsBounded := by
  refine ⟨ 1, by norm_num, ?_ ⟩; intro i; by_cases h: 0 ≤ i <;> simp [h]

/-- Example 5.1.13 -/
example : ¬((fun n:ℕ ↦ (-1:ℚ)^n):Sequence).IsCauchy := by
  rw [Sequence.IsCauchy.coe]
  by_contra h; specialize h (1/2 : ℚ) (by norm_num)
  choose N h using h; specialize h N _ (N+1) _ <;> try omega
  by_cases h': Even N
  · have h_val : Section_4_3.dist ((-1 : ℚ) ^ N) ((-1 : ℚ) ^ (N+1)) = 2 := by
      calc
        Section_4_3.dist ((-1 : ℚ) ^ N) ((-1 : ℚ) ^ (N+1))
            = Section_4_3.abs (((-1 : ℚ) ^ N) - ((-1 : ℚ) ^ (N+1))) := rfl
        _ = |((-1 : ℚ) ^ N) - ((-1 : ℚ) ^ (N+1))| := by rw [Section_4_3.abs_eq_abs]
        _ = |(1 : ℚ) - (-1 : ℚ)| := by simp [h'.neg_one_pow, (h'.add_one).neg_one_pow]
        _ = |(2 : ℚ)| := by norm_num
        _ = (2 : ℚ) := by norm_num
    rw [h_val] at h
    norm_num at h
  · rcases N.even_or_odd with (h_even | h_odd)
    · exact absurd h_even h'
    · have h_val : Section_4_3.dist ((-1 : ℚ) ^ N) ((-1 : ℚ) ^ (N+1)) = 2 := by
        calc
          Section_4_3.dist ((-1 : ℚ) ^ N) ((-1 : ℚ) ^ (N+1))
              = Section_4_3.abs (((-1 : ℚ) ^ N) - ((-1 : ℚ) ^ (N+1))) := rfl
          _ = |((-1 : ℚ) ^ N) - ((-1 : ℚ) ^ (N+1))| := by rw [Section_4_3.abs_eq_abs]
          _ = |(-1 : ℚ) - (1 : ℚ)| := by simp [h_odd.neg_one_pow, h_odd.add_one.neg_one_pow]
          _ = |(-2 : ℚ)| := by norm_num
          _ = (2 : ℚ) := by norm_num
      rw [h_val] at h
      norm_num at h

/-- Lemma 5.1.14 -/
lemma IsBounded.finite {n:ℕ} (a: Fin n → ℚ) : ∃ M ≥ 0,  BoundedBy a M := by
  -- this proof is written to follow the structure of the original text.
  induction' n with n hn
  . use 0; simp
  set a' : Fin n → ℚ := fun m ↦ a m.castSucc
  choose M hpos hM using hn a'
  have h1 : BoundedBy a' (M + |a (Fin.ofNat _ n)|) := fun m ↦ (hM m).trans (by simp)
  have h2 : |a (Fin.ofNat _ n)| ≤ M + |a (Fin.ofNat _ n)| := by simp [hpos]
  refine ⟨ M + |a (Fin.ofNat _ n)|, by positivity, ?_ ⟩
  intro m; obtain ⟨ j, rfl ⟩ | rfl := Fin.eq_castSucc_or_eq_last m
  . grind
  convert h2; simp

/-- Lemma 5.1.15 (Cauchy sequences are bounded) / Exercise 5.1.1 -/
lemma Sequence.isBounded_of_isCauchy {a:Sequence} (h: a.IsCauchy) : a.IsBounded := by
  rw [Sequence.isBounded_def]
  have h_cauchy := h 1 (by norm_num : (1 : ℚ) > 0)
  rcases h_cauchy with ⟨N, hN, h_steady⟩
  rw [Rat.Steady] at h_steady
  have h_N_n₀ : (a.from N).n₀ = N := by
    simpa using (max_eq_right hN : max a.n₀ N = N)
  rw [h_N_n₀] at h_steady
  have h_eval (n : ℤ) (hn : n ≥ N) : (a.from N) n = a n :=
    Sequence.from_eval a hn
  have h_bound_ge_N (n : ℤ) (hn : n ≥ N) : |a n| ≤ |a N| + 1 := by
    have h_diff := h_steady n hn N (le_refl N)
    rw [h_eval n hn, h_eval N (le_refl N)] at h_diff
    calc
      |a n| = |(a n - a N) + a N| := by ring_nf
      _ = |(a n - a N) - (-a N)| := by ring_nf
      _ ≤ |a n - a N| + |-a N| := abs_sub _ _
      _ = |a n - a N| + |a N| := by simp
      _ ≤ 1 + |a N| := by
        simpa [add_comm] using add_le_add_right h_diff (|a N|)
      _ = |a N| + 1 := by ring_nf
  let S := Finset.Icc a.n₀ N
  have hS_sum_nonneg : 0 ≤ Finset.sum S (fun k ↦ |a k|) := Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)
  have h_mem_N : N ∈ S := Finset.mem_Icc.mpr ⟨hN, le_refl N⟩
  have h_sum_ge (x : ℤ) (hx : x ∈ S) : |a x| ≤ Finset.sum S (fun k ↦ |a k|) := by
    have : Finset.sum S (fun k ↦ |a k|) = |a x| + Finset.sum (S.erase x) (fun k ↦ |a k|) := by
      simpa using (Finset.add_sum_erase S (fun k ↦ |a k|) hx).symm
    rw [this]
    apply le_add_of_nonneg_right
    exact Finset.sum_nonneg (s := S.erase x) (fun y hy ↦ abs_nonneg (a y))
  set M := Finset.sum S (fun k ↦ |a k|) + 1 with hM_def
  refine ⟨M, by nlinarith, ?_⟩
  intro n
  by_cases hn_ge_N : n ≥ N
  · have h_bound := h_bound_ge_N n hn_ge_N
    have : |a N| + 1 ≤ M := by
      have hN_sum : |a N| ≤ Finset.sum S (fun k ↦ |a k|) := h_sum_ge N h_mem_N
      dsimp [M]; nlinarith
    exact le_trans h_bound this
  · by_cases hn_ge_n₀ : n ≥ a.n₀
    · have h_mem_n : n ∈ S := Finset.mem_Icc.mpr ⟨hn_ge_n₀, by omega⟩
      have h_sum_ge_n : |a n| ≤ Finset.sum S (fun k ↦ |a k|) := h_sum_ge n h_mem_n
      dsimp [M]; nlinarith
    · have hn_lt_n₀ : n < a.n₀ := by
        by_contra! h
        exact hn_ge_n₀ (by omega)
      have h_vanish : a n = 0 := by
        simpa using a.vanish n hn_lt_n₀
      have h_abs_zero : |a n| = 0 := by simp [h_vanish]
      dsimp [M]
      nlinarith

/-- Exercise 5.1.2 -/
theorem Sequence.isBounded_add {a b:ℕ → ℚ} (ha: (a:Sequence).IsBounded) (hb: (b:Sequence).IsBounded):
    (a + b:Sequence).IsBounded := by
  rcases ha with ⟨Ma, hMa, ha_bound⟩
  rcases hb with ⟨Mb, hMb, hb_bound⟩
  refine ⟨Ma + Mb, by positivity, ?_⟩
  intro n
  have ha_n : |(a:Sequence) n| ≤ Ma := ha_bound n
  have hb_n : |(b:Sequence) n| ≤ Mb := hb_bound n
  have h_sum : ((a + b : Sequence) n : ℚ) = (a:Sequence) n + (b:Sequence) n := by
    by_cases hn : (0 : ℤ) ≤ n
    · simp [hn, Sequence.eval_coe_at_int]
    · simp [hn, Sequence.eval_coe_at_int]
  rw [h_sum]
  calc
    |(a:Sequence) n + (b:Sequence) n| = |(a:Sequence) n - (-(b:Sequence) n)| := by ring_nf
    _ ≤ |(a:Sequence) n| + |-(b:Sequence) n| := abs_sub _ _
    _ = |(a:Sequence) n| + |(b:Sequence) n| := by simp
    _ ≤ Ma + Mb := by nlinarith

theorem Sequence.isBounded_sub {a b:ℕ → ℚ} (ha: (a:Sequence).IsBounded) (hb: (b:Sequence).IsBounded):
    (a - b:Sequence).IsBounded := by
  rcases ha with ⟨Ma, hMa, ha_bound⟩
  rcases hb with ⟨Mb, hMb, hb_bound⟩
  refine ⟨Ma + Mb, by positivity, ?_⟩
  intro n
  have ha_n : |(a:Sequence) n| ≤ Ma := ha_bound n
  have hb_n : |(b:Sequence) n| ≤ Mb := hb_bound n
  have h_sub : ((a - b : Sequence) n : ℚ) = (a:Sequence) n - (b:Sequence) n := by
    by_cases hn : (0 : ℤ) ≤ n
    · simp [hn, Sequence.eval_coe_at_int]
    · simp [hn, Sequence.eval_coe_at_int]
  rw [h_sub]
  calc
    |(a:Sequence) n - (b:Sequence) n| ≤ |(a:Sequence) n| + |(b:Sequence) n| := abs_sub _ _
    _ ≤ Ma + Mb := by nlinarith

theorem Sequence.isBounded_mul {a b:ℕ → ℚ} (ha: (a:Sequence).IsBounded) (hb: (b:Sequence).IsBounded):
    (a * b:Sequence).IsBounded := by
  rcases ha with ⟨Ma, hMa, ha_bound⟩
  rcases hb with ⟨Mb, hMb, hb_bound⟩
  refine ⟨Ma * Mb, mul_nonneg hMa hMb, ?_⟩
  intro n
  have ha_n : |(a:Sequence) n| ≤ Ma := ha_bound n
  have hb_n : |(b:Sequence) n| ≤ Mb := hb_bound n
  have h_mul : ((a * b : Sequence) n : ℚ) = (a:Sequence) n * (b:Sequence) n := by
    by_cases hn : (0 : ℤ) ≤ n
    · simp [hn, Sequence.eval_coe_at_int]
    · simp [hn, Sequence.eval_coe_at_int]
  rw [h_mul]
  calc
    |(a:Sequence) n * (b:Sequence) n| = |(a:Sequence) n| * |(b:Sequence) n| := abs_mul _ _
    _ ≤ Ma * Mb := mul_le_mul ha_n hb_n (abs_nonneg _) hMa

end Chapter5
