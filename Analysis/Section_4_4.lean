import Mathlib.Tactic

/-!
# Analysis I, Section 4.4: gaps in the rational numbers

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Irrationality of √2, and related facts about the rational numbers

Many of the results here can be established more quickly by relying more heavily on the Mathlib
API; one can set oneself the exercise of doing so.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

/-- Proposition 4.4.1 (Interspersing of integers by rationals) / Exercise 4.4.1 -/
theorem Rat.between_int (x:ℚ) : ∃! n:ℤ, n ≤ x ∧ x < n+1 := by
  have hden_pos_ℤ : 0 < (x.den : ℤ) := by exact_mod_cast x.den_pos
  set q := x.num / (x.den : ℤ) with hq
  set r := x.num % (x.den : ℤ) with hr
  have h_int_eq : (x.den : ℤ) * q + r = x.num := by
    calc
      (x.den : ℤ) * q + r = (x.den : ℤ) * (x.num / (x.den : ℤ)) + (x.num % (x.den : ℤ)) := rfl
      _ = x.num := by rw [Int.mul_ediv_add_emod (x.num) (x.den : ℤ)]
  have h_nonneg_r : 0 ≤ r :=
    Int.emod_nonneg (x.num) (by exact_mod_cast x.den_pos.ne.symm)
  have h_lt_r : r < (x.den : ℤ) := Int.emod_lt_of_pos (x.num) hden_pos_ℤ
  have h_ℚ_eq : (x.den : ℚ) * (q : ℚ) + (r : ℚ) = (x.num : ℚ) := by exact_mod_cast h_int_eq
  have hx_mul_eq : (x.num : ℚ) = x * (x.den : ℚ) := by
    calc
      (x.num : ℚ) = ((x.num : ℚ) / (x.den : ℚ)) * (x.den : ℚ) := by
        field_simp [show (x.den : ℚ) ≠ 0 from by exact_mod_cast x.den_pos.ne.symm]
      _ = x * (x.den : ℚ) := by rw [x.num_div_den]
  have hden_pos_ℚ : 0 < (x.den : ℚ) := by exact_mod_cast x.den_pos
  have h_nonneg_r_ℚ : 0 ≤ (r : ℚ) := by exact_mod_cast h_nonneg_r
  have h_lt_r_ℚ : (r : ℚ) < (x.den : ℚ) := by exact_mod_cast h_lt_r
  have hq_prop : (q : ℚ) ≤ x ∧ x < (q : ℚ) + 1 := by
    have hx_expr : (x - (q : ℚ)) * (x.den : ℚ) = (r : ℚ) := by
      calc
        (x - (q : ℚ)) * (x.den : ℚ) = x * (x.den : ℚ) - (q : ℚ) * (x.den : ℚ) := by ring
        _ = (x.num : ℚ) - (x.den : ℚ) * (q : ℚ) := by
          rw [hx_mul_eq, mul_comm (q : ℚ) (x.den : ℚ)]
        _ = (x.num : ℚ) - ((x.den : ℚ) * (q : ℚ) + (r : ℚ) - (r : ℚ)) := by ring
        _ = (r : ℚ) := by rw [h_ℚ_eq]; ring
    have h_x_sub_q_eq : x - (q : ℚ) = (r : ℚ) / (x.den : ℚ) := by
      apply mul_right_cancel₀ hden_pos_ℚ.ne.symm
      calc
        (x - (q : ℚ)) * (x.den : ℚ) = (r : ℚ) := hx_expr
        _ = ((r : ℚ) / (x.den : ℚ)) * (x.den : ℚ) := by field_simp
    have h_div_nonneg : 0 ≤ (r : ℚ) / (x.den : ℚ) :=
      div_nonneg h_nonneg_r_ℚ (by exact hden_pos_ℚ.le)
    have h_div_lt_one : (r : ℚ) / (x.den : ℚ) < 1 :=
      (div_lt_one hden_pos_ℚ).mpr h_lt_r_ℚ
    constructor
    · -- q ≤ x
      linarith
    · -- x < q + 1
      calc
        x = (q : ℚ) + (x - (q : ℚ)) := by ring
        _ = (q : ℚ) + ((r : ℚ) / (x.den : ℚ)) := by rw [h_x_sub_q_eq]
        _ = ((r : ℚ) / (x.den : ℚ)) + (q : ℚ) := by ring
        _ < 1 + (q : ℚ) := by
          have h := add_lt_add_right h_div_lt_one (q : ℚ)
          simpa [add_comm] using h
        _ = (q : ℚ) + 1 := by ring
  have hq_le_x : (q : ℚ) ≤ x := hq_prop.1
  have hx_lt_q_add_one : x < (q : ℚ) + 1 := hq_prop.2
  use q
  constructor
  · exact hq_prop
  · intro n ⟨hnle, hnlt⟩
    by_cases h_n_lt_q : n < q
    · have h_n_succ_le_q : n + 1 ≤ q := by omega
      have hn_succ_le_q_ℚ : (n + 1 : ℚ) ≤ (q : ℚ) := by exact_mod_cast h_n_succ_le_q
      linarith
    · by_cases h_q_lt_n : q < n
      · have h_q_succ_le_n : q + 1 ≤ n := by omega
        have h_q_succ_le_n_ℚ : (q + 1 : ℚ) ≤ (n : ℚ) := by exact_mod_cast h_q_succ_le_n
        linarith
      · omega

theorem Nat.exists_gt (x:ℚ) : ∃ n:ℕ, n > x := by
  have h := Rat.between_int x
  rcases h with ⟨n, ⟨_, hnlt⟩, _⟩
  set m := n + 1 with hm
  by_cases hm_pos : (0 : ℤ) < m
  · have hm_nonneg : (0 : ℤ) ≤ m := by omega
    have hcast : (m.toNat : ℚ) = (m : ℚ) := by
      exact_mod_cast Int.toNat_of_nonneg hm_nonneg
    have h_eq : (m.toNat : ℚ) = (n : ℚ) + 1 := by
      rw [hcast, hm]
      simp
    refine ⟨m.toNat, ?_⟩
    rw [h_eq]
    exact hnlt
  · have hm_nonpos : m ≤ 0 := by omega
    have hx_nonpos : x ≤ 0 := by
      have hm_nonpos_ℚ : (m : ℚ) ≤ 0 := by exact_mod_cast hm_nonpos
      have hx_lt_m : x < (m : ℚ) := by simpa [hm] using hnlt
      linarith
    refine ⟨1, ?_⟩
    calc
      x ≤ 0 := hx_nonpos
      _ < 1 := by norm_num

/-- Proposition 4.4.3 (Interspersing of rationals) -/
theorem Rat.exists_between_rat {x y:ℚ} (h: x < y) : ∃ z:ℚ, x < z ∧ z < y := by
  -- This proof is written to follow the structure of the original text.
  -- The reader is encouraged to find shorter proofs, for instance
  -- using Mathlib's `linarith` tactic.
  use (x+y)/2
  have h' : x/2 < y/2 := by
    rw [show x/2 = x*(1/2) by ring, show y/2 = y*(1/2) by ring]
    apply mul_lt_mul_of_pos_right h; positivity
  constructor
  . convert add_lt_add_right h' (x/2) using 1 <;> ring
  convert add_lt_add_right h' (y/2) using 1 <;> ring

/-- Exercise 4.4.2 (a) -/
theorem Nat.no_infinite_descent : ¬ ∃ a:ℕ → ℕ, ∀ n, a (n+1) < a n := by
  intro h
  rcases h with ⟨a, ha⟩
  -- wired arbitrary lower bound
  have h_an_ge_k : ∀ k n : ℕ, a n ≥ k := by
    intro k
    induction' k with k ih
    · intro n; exact Nat.zero_le _
    · intro n
      have ha_n : a (n+1) < a n := ha n
      have ih_n1 : a (n+1) ≥ k := ih (n+1)
      omega
  have : a 0 ≥ a 0 + 1 := h_an_ge_k (a 0 + 1) 0
  omega

/-- Exercise 4.4.2 (b) -/
def Int.infinite_descent : Decidable (∃ a:ℕ → ℤ, ∀ n, a (n+1) < a n) := by
  apply isTrue
  refine ⟨λ n => -(n : ℤ), λ n => ?_⟩
  push_cast
  omega

/-- Exercise 4.4.2 (b) -/
def Rat.pos_infinite_descent : Decidable (∃ a:ℕ → {x: ℚ // 0 < x}, ∀ n, a (n+1) < a n) := by
  apply isTrue
  refine ⟨λ n => ⟨1 / ((n.succ : ℕ) : ℚ), by positivity⟩, λ n => ?_⟩
  have hpos1 : 0 < ((n.succ : ℕ) : ℚ) := by positivity
  have hpos2 : 0 < ((n.succ.succ : ℕ) : ℚ) := by positivity
  have h_lt : ((n.succ : ℕ) : ℚ) < ((n.succ.succ : ℕ) : ℚ) := by
    exact_mod_cast Nat.lt_succ_self n.succ
  exact (one_div_lt_one_div hpos2 hpos1).mpr h_lt

#check even_iff_exists_two_mul
#check odd_iff_exists_bit1

theorem Nat.even_or_odd'' (n:ℕ) : Even n ∨ Odd n := by
  induction' n with n ih
  · left; exact ⟨0, by simp⟩
  · rcases ih with (⟨k, hk⟩ | ⟨k, hk⟩)
    · right; use k; omega
    · left; use k+1; omega

theorem Nat.not_even_and_odd (n:ℕ) : ¬ (Even n ∧ Odd n) := by
  rintro ⟨⟨k, hk⟩, ⟨m, hm⟩⟩
  omega

#check Nat.rec

/-- Proposition 4.4.4 / Exercise 4.4.3  -/
theorem Rat.not_exist_sqrt_two : ¬ ∃ x:ℚ, x^2 = 2 := by
  -- This proof is written to follow the structure of the original text.
  by_contra h; choose x hx using h
  have hnon : x ≠ 0 := by aesop
  wlog hpos : x > 0
  . apply this _ _ _ (show -x>0 by simp; order) <;> grind
  have hrep : ∃ p q:ℕ, p > 0 ∧ q > 0 ∧ p^2 = 2*q^2 := by
    use x.num.toNat, x.den
    have hnum_pos : x.num > 0 := by
      have hx_mul_eq' : (x.num : ℚ) = x * (x.den : ℚ) := by
        calc
          (x.num : ℚ) = ((x.num : ℚ) / (x.den : ℚ)) * (x.den : ℚ) := by
            field_simp [show (x.den : ℚ) ≠ 0 from by exact_mod_cast x.den_pos.ne.symm]
          _ = x * (x.den : ℚ) := by rw [x.num_div_den]
      have hpos_ℚ : (x.num : ℚ) > 0 := by
        rw [hx_mul_eq']
        exact mul_pos hpos (by exact_mod_cast x.den_pos)
      exact_mod_cast hpos_ℚ
    have hden_pos : x.den > 0 := x.den_pos
    have hp_pos : x.num.toNat > 0 := by
      by_contra! h
      have hzero : x.num.toNat = 0 := by omega
      have : x.num ≤ 0 := (Int.toNat_eq_zero.mp hzero)
      omega
    refine ⟨hp_pos, hden_pos, ?_⟩
    have hx_sq_eq : (x.num : ℚ)^2 = 2 * (x.den : ℚ)^2 := by
      calc
        (x.num : ℚ)^2 = ((x.num : ℚ) / (x.den : ℚ))^2 * (x.den : ℚ)^2 := by
          field_simp [show (x.den : ℚ) ≠ 0 from by exact_mod_cast x.den_pos.ne.symm]
        _ = x^2 * (x.den : ℚ)^2 := by rw [x.num_div_den]
        _ = 2 * (x.den : ℚ)^2 := by rw [hx]
    have hnum_cast : (x.num : ℚ) = (x.num.toNat : ℚ) := by
      exact_mod_cast (Int.eq_natCast_toNat.mpr (by exact hnum_pos.le))
    have h_goal_ℚ : ((x.num.toNat : ℕ) : ℚ)^2 = 2 * ((x.den : ℕ) : ℚ)^2 := by
      calc
        ((x.num.toNat : ℕ) : ℚ)^2 = (x.num : ℚ)^2 := by rw [hnum_cast]
        _ = 2 * (x.den : ℚ)^2 := hx_sq_eq
        _ = 2 * ((x.den : ℕ) : ℚ)^2 := rfl
    exact_mod_cast h_goal_ℚ
  set P : ℕ → Prop := fun p ↦ p > 0 ∧ ∃ q > 0, p^2 = 2*q^2
  have hP : ∃ p, P p := by aesop
  have hiter (p:ℕ) (hPp: P p) : ∃ q, q < p ∧ P q := by
    obtain hp | hp := p.even_or_odd''
    . rw [even_iff_exists_two_mul] at hp
      obtain ⟨ k, rfl ⟩ := hp
      choose q hpos hq using hPp.2
      have hq_sq_eq : q^2 = 2 * k^2 := by linarith
      have hk_pos : k > 0 := by
        by_contra! hk
        omega
      have hq_lt_p : q < 2*k := by
        have h_sq_lt : q^2 < (2*k)^2 := by
          calc
            q^2 = 2 * k^2 := hq_sq_eq
            _ < 4 * k^2 := by
              have hk_sq_pos : k^2 > 0 := pow_pos hk_pos 2
              have h_two_lt_four : (2 : ℕ) < 4 := by omega
              exact Nat.mul_lt_mul_of_pos_right h_two_lt_four hk_sq_pos
            _ = (2*k)^2 := by nlinarith
        by_contra! hge
        exact (Nat.not_le_of_lt h_sq_lt) (Nat.pow_le_pow_left hge 2)
      refine ⟨q, ?_, ⟨hpos, k, hk_pos, hq_sq_eq⟩⟩
      exact hq_lt_p
    have h1 : Odd (p^2) := by
      rcases hp with ⟨k, hk⟩
      rw [odd_iff_exists_bit1, hk]
      use 2*k^2 + 2*k
      nlinarith
    have h2 : Even (p^2) := by
      choose q hpos hq using hPp.2
      rw [even_iff_exists_two_mul]
      use q^2
    exfalso
    exact (Nat.not_even_and_odd (p ^ 2)) ⟨h2, h1⟩
  classical
  set f : ℕ → ℕ := fun p ↦ if hPp: P p then (hiter p hPp).choose else 0
  have hf (p:ℕ) (hPp: P p) : (f p < p) ∧ P (f p) := by
    simp [f, hPp]; exact (hiter p hPp).choose_spec
  choose p hP using hP
  set a : ℕ → ℕ := Nat.rec p (fun n p ↦ f p)
  have ha (n:ℕ) : P (a n) := by
    induction n with
    | zero => exact hP
    | succ n ih => exact (hf _ ih).2
  have hlt (n:ℕ) : a (n+1) < a n := by
    have : a (n+1) = f (a n) := n.rec_add_one p (fun n p ↦ f p)
    grind
  exact Nat.no_infinite_descent ⟨ a, hlt ⟩


/-- Proposition 4.4.5 -/
theorem Rat.exist_approx_sqrt_two {ε:ℚ} (hε:ε>0) : ∃ x ≥ (0:ℚ), x^2 < 2 ∧ 2 < (x+ε)^2 := by
  -- This proof is written to follow the structure of the original text.
  by_contra! h
  have (n:ℕ): (n*ε)^2 < 2 := by
    induction' n with n hn; simp
    simp [add_mul]
    apply lt_of_le_of_ne (h (n*ε) (by positivity) hn)
    have := not_exist_sqrt_two
    aesop
  choose n hn using Nat.exists_gt (2/ε)
  rw [gt_iff_lt, div_lt_iff₀', mul_comm, ←sq_lt_sq₀] at hn <;> try positivity
  grind

/-- Example 4.4.6 -/
example :
  let ε:ℚ := 1/1000
  let x:ℚ := 1414/1000
  x^2 < 2 ∧ 2 < (x+ε)^2 := by norm_num
