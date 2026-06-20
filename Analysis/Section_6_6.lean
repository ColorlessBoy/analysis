import Mathlib.Tactic
import Analysis.Section_6_5

/-!
# Analysis I, Section 6.6: Subsequences

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of a subsequence.
-/

namespace Chapter6

/-- Definition 6.6.1 -/
abbrev Sequence.subseq (a b: ℕ → ℝ) : Prop := ∃ f : ℕ → ℕ, StrictMono f ∧ ∀ n, b n = a (f n)

/- Example 6.6.2 -/
example (a:ℕ → ℝ) : Sequence.subseq a (fun n ↦ a (2 * n)) := by
  refine ⟨fun n ↦ 2 * n, ?_, λ n ↦ rfl⟩
  intro n m h
  simpa [mul_comm] using Nat.mul_lt_mul_of_pos_right h (by norm_num : 0 < 2)

example {f: ℕ → ℕ} (hf: StrictMono f) : Function.Injective f := hf.injective

example :
    Sequence.subseq (fun n ↦ if Even n then 1 + (10:ℝ)^(-(n/2:ℤ)-1) else (10:ℝ)^(-(n/2:ℤ)-1))
    (fun n ↦ 1 + (10:ℝ)^(-(n:ℤ)-1)) := by
  refine ⟨fun n ↦ 2*n, ?_, λ n ↦ ?_⟩
  · intro n m h
    simpa [mul_comm] using Nat.mul_lt_mul_of_pos_right h (by norm_num : 0 < 2)
  · have h_even : Even (2*n) := ⟨n, by ring⟩
    simp [h_even]

example :
    Sequence.subseq (fun n ↦ if Even n then 1 + (10:ℝ)^(-(n/2:ℤ)-1) else (10:ℝ)^(-(n/2:ℤ)-1))
    (fun n ↦ (10:ℝ)^(-(n:ℤ)-1)) := by
  refine ⟨fun n ↦ 2*n + 1, ?_, λ n ↦ ?_⟩
  · intro n m h
    dsimp
    omega
  · have h_odd : ¬ Even (2*n + 1) := by
      rintro ⟨k, h⟩
      omega
    have h_div : ((2*n + 1 : ℕ) : ℤ) / 2 = (n : ℤ) := by omega
    dsimp
    simp [h_odd]
    simpa [Nat.cast_add, Nat.cast_mul, Nat.cast_one, mul_comm] using h_div.symm

/-- Lemma 6.6.4 / Exercise 6.6.1 -/
theorem Sequence.subseq_self (a:ℕ → ℝ) : Sequence.subseq a a := by
  refine ⟨id, strictMono_id, λ n ↦ rfl⟩

/-- Lemma 6.6.4 / Exercise 6.6.1 -/
theorem Sequence.subseq_trans {a b c:ℕ → ℝ} (hab: Sequence.subseq a b) (hbc: Sequence.subseq b c) :
    Sequence.subseq a c := by
  rcases hab with ⟨f, hf, hab'⟩
  rcases hbc with ⟨g, hg, hbc'⟩
  refine ⟨f ∘ g, hf.comp hg, λ n ↦ ?_⟩
  calc
    c n = b (g n) := hbc' n
    _ = a (f (g n)) := hab' (g n)

/-- Proposition 6.6.5 / Exercise 6.6.4 -/
theorem Sequence.convergent_iff_subseq (a:ℕ → ℝ) (L:ℝ) :
    (a:Sequence).TendsTo L ↔ ∀ b:ℕ → ℝ, Sequence.subseq a b → (b:Sequence).TendsTo L := by
  constructor
  · intro h b hsub
    rcases hsub with ⟨f, hf, hsub'⟩
    rw [Sequence.tendsTo_iff (a : Sequence) L] at h
    rw [Sequence.tendsTo_iff (b : Sequence) L]
    intro ε hε
    obtain ⟨N, hN⟩ := h ε hε
    use max N 0
    intro n' hn'
    have hn0 : (0 : ℤ) ≤ n' := le_trans (by simp) hn'
    have hNn' : N ≤ n' := le_trans (le_max_left _ _) hn'
    have ha_simp : ((a : Sequence) n') = a (n'.toNat) := by simp [hn0]
    have hb_simp : ((b : Sequence) n') = b (n'.toNat) := by simp [hn0]
    rw [hb_simp, hsub' n'.toNat]
    have hn'_eq : (n'.toNat : ℤ) = n' := by exact mod_cast (Int.toNat_of_nonneg hn0)
    have h_f_ge_n : n'.toNat ≤ f n'.toNat := hf.id_le n'.toNat
    have h_f_ge_N : N ≤ (f n'.toNat : ℤ) := by
      calc
        N ≤ n' := hNn'
        _ = (n'.toNat : ℤ) := hn'_eq.symm
        _ ≤ (f n'.toNat : ℤ) := by exact mod_cast h_f_ge_n
    have h_f_nonneg : (0 : ℤ) ≤ (f n'.toNat : ℤ) := Nat.cast_nonneg _
    have hN' := hN (f n'.toNat : ℤ) h_f_ge_N
    have ha_simp' : ((a : Sequence) (f n'.toNat : ℤ)) = a (f n'.toNat) := by simp [h_f_nonneg]
    rw [ha_simp'] at hN'
    exact hN'
  · intro h
    have hself : Sequence.subseq a a := Sequence.subseq_self a
    exact h a hself

/-- Proposition 6.6.6 / Exercise 6.6.5 -/
theorem Sequence.limit_point_iff_subseq (a:ℕ → ℝ) (L:ℝ) :
    (a:Sequence).LimitPoint L ↔ ∃ b:ℕ → ℝ, Sequence.subseq a b ∧ (b:Sequence).TendsTo L := by
  constructor
  · intro h
    rw [Sequence.limit_point_def (a : Sequence) L] at h
    have hm : (a : Sequence).m = 0 := by rfl
    have h_exists : ∀ (ε : ℝ), ε > 0 → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ |a n - L| ≤ ε := by
      intro ε hε N
      obtain ⟨n, hn, hclose⟩ := h ε hε (N : ℤ) (by
        rw [hm]
        exact Nat.cast_nonneg _)
      have hn_nonneg : 0 ≤ n := le_trans (Nat.cast_nonneg _) hn
      refine ⟨n.toNat, ?_, ?_⟩
      · have : (N : ℤ) ≤ n := hn
        omega
      · simpa [hn_nonneg] using hclose
    have hone : (1 : ℝ) > 0 := by norm_num
    have hpos (k : ℕ) : 0 < 1 / ((k : ℝ) + 2) := by positivity
    let f : ℕ → ℕ :=
      Nat.rec
        (Classical.choose (h_exists 1 hone 0))
        (fun k fk => Classical.choose (h_exists (1 / ((k : ℝ) + 2)) (hpos k) (fk + 1)))
    have hf_spec (n : ℕ) : f n + 1 ≤ f (n + 1) := by
      have hk := h_exists (1 / ((n : ℝ) + 2)) (hpos n) (f n + 1)
      have h_choice := Classical.choose_spec hk
      rcases h_choice with ⟨hn_ge, hclose⟩
      simpa [f] using hn_ge
    have hf_strictMono : StrictMono f :=
      strictMono_nat_of_lt_succ (fun n => by
        have h := hf_spec n
        omega)
    let b : ℕ → ℝ := fun n => a (f n)
    have h_bound (n : ℕ) : |b n - L| ≤ 1 / ((n : ℝ) + 1) := by
      dsimp [b]
      induction' n with k ih
      · have h0 := Classical.choose_spec (h_exists 1 hone 0)
        rcases h0 with ⟨hn_ge, hclose⟩
        simpa [f] using hclose
      · have hk := h_exists (1 / ((k : ℝ) + 2)) (hpos k) (f k + 1)
        have h_choice := Classical.choose_spec hk
        rcases h_choice with ⟨hn_ge, hclose⟩
        have h_f_succ : f (k+1) = Classical.choose hk := by simp [f]
        have h_rhs : 1 / ((k : ℝ) + 2) = 1 / (((k + 1 : ℕ) : ℝ) + 1) := by
          push_cast; ring
        rw [h_f_succ]
        simpa [h_rhs] using hclose
    have hb_tendsTo : (b : Sequence).TendsTo L := by
      rw [Sequence.tendsTo_iff (b : Sequence) L]
      intro ε hε
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
      use (N : ℤ)
      intro n hn
      have hn_nonneg : (0 : ℤ) ≤ n := le_trans (by exact_mod_cast (Nat.zero_le N)) hn
      have hb_simp : (b : Sequence) n = b (n.toNat) := by simp [hn_nonneg]
      rw [hb_simp]
      have h_nat : (N : ℕ) ≤ n.toNat := by
        have : (N : ℤ) ≤ n := hn
        omega
      have h_bound_n : |b (n.toNat) - L| ≤ 1 / ((n.toNat : ℝ) + 1) := h_bound n.toNat
      have h_denom_le : ((N : ℝ) + 1) ≤ ((n.toNat : ℝ) + 1) := by
        have : (N : ℝ) ≤ (n.toNat : ℝ) := by exact_mod_cast h_nat
        linarith
      have hpos_N1 : 0 < (N : ℝ) + 1 := by
        have : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
        linarith
      have hpos_n1 : 0 < (n.toNat : ℝ) + 1 := by
        have : 0 ≤ (n.toNat : ℝ) := Nat.cast_nonneg _
        linarith
      have h_one_div : 1 / ((n.toNat : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
        (one_div_le_one_div hpos_n1 hpos_N1).mpr h_denom_le
      have h_lt : 1 / ((N : ℝ) + 1) < ε := hN
      have h_final : |b (n.toNat) - L| ≤ ε := by linarith
      exact h_final
    refine ⟨b, ⟨f, hf_strictMono, λ n => rfl⟩, hb_tendsTo⟩
  · intro h
    rcases h with ⟨b, hsub, hb⟩
    rw [Sequence.limit_point_def (a : Sequence) L]
    rcases hsub with ⟨f, hf, hsub'⟩
    rw [Sequence.tendsTo_iff (b : Sequence) L] at hb
    intro ε hε N hN
    have hm : (a : Sequence).m = 0 := by rfl
    have hN_nonneg : (0 : ℤ) ≤ N := by
      rw [hm] at hN
      exact hN
    obtain ⟨M, hM⟩ := hb ε hε
    set K := max M N with hK_def
    have hK_nonneg : 0 ≤ K := by
      dsimp [K]
      omega
    let k := K.toNat
    have hk_eq : (k : ℤ) = K := by exact mod_cast Int.toNat_of_nonneg hK_nonneg
    have hK_M : M ≤ K := le_max_left _ _
    have hK_N : N ≤ K := le_max_right _ _
    have hk_M : M ≤ (k : ℤ) := by
      calc
        M ≤ K := hK_M
        _ = (k : ℤ) := hk_eq.symm
    have hk_fk : (k : ℤ) ≤ (f k : ℤ) := by exact mod_cast hf.id_le k
    have hN_fk : N ≤ (f k : ℤ) :=
      calc
        N ≤ K := hK_N
        _ = (k : ℤ) := hk_eq.symm
        _ ≤ (f k : ℤ) := hk_fk
    have h_close : |(b : Sequence) (k : ℤ) - L| ≤ ε := hM (k : ℤ) hk_M
    refine ⟨(f k : ℤ), hN_fk, ?_⟩
    simpa [hsub'] using h_close

/-- Theorem 6.6.8 (Bolzano-Weierstrass theorem) -/
theorem Sequence.convergent_of_subseq_of_bounded {a:ℕ→ ℝ} (ha: (a:Sequence).IsBounded) :
    ∃ b:ℕ → ℝ, Sequence.subseq a b ∧ (b:Sequence).Convergent := by
  -- This proof is written to follow the structure of the original text.
  obtain ⟨ ⟨ L_plus, hL_plus ⟩, ⟨ _, _ ⟩ ⟩ := finite_limsup_liminf_of_bounded ha
  have := limit_point_of_limsup hL_plus
  rw [limit_point_iff_subseq] at this; peel 2 this; solve_by_elim

/- Exercise 6.6.2 -/

def Sequence.exist_subseq_of_subseq :
  Decidable (∃ a b : ℕ → ℝ, a ≠ b ∧ Sequence.subseq a b ∧ Sequence.subseq b a) := by
  apply isTrue
  let a := fun n : ℕ ↦ (-1 : ℝ) ^ n
  let b := fun n : ℕ ↦ (-1 : ℝ) ^ (n + 1)
  have h_succ : StrictMono (fun n : ℕ ↦ n + 1) := by
    intro n m h
    dsimp
    omega
  have ha_ne_b : a ≠ b := by
    intro h_eq
    have h0 := congrArg (fun f : ℕ → ℝ ↦ f 0) h_eq
    simp [a, b] at h0
    norm_num at h0
  have ha_sub_b : Sequence.subseq a b := by
    refine ⟨fun n ↦ n + 1, h_succ, ?_⟩
    intro n
    simp [a, b]
  have hb_sub_a : Sequence.subseq b a := by
    refine ⟨fun n ↦ n + 1, h_succ, ?_⟩
    intro n
    calc
      a n = (-1 : ℝ) ^ n := rfl
      _ = (-1 : ℝ) ^ n * 1 := by ring
      _ = (-1 : ℝ) ^ n * (-1 : ℝ) ^ 2 := by norm_num
      _ = (-1 : ℝ) ^ (n + 2) := by
        rw [← pow_add, add_comm n 2]
      _ = (-1 : ℝ) ^ (n + 1 + 1) := by ring
      _ = b (n + 1) := rfl
  refine ⟨a, b, ha_ne_b, ha_sub_b, hb_sub_a⟩

/--
  Exercise 6.6.3.  You may find the API around Mathlib's {name}`Nat.find` to be useful
  (and {syntax command}`open Classical` to avoid any decidability issues)
-/
theorem Sequence.subseq_of_unbounded {a:ℕ → ℝ} (ha: ¬ (a:Sequence).IsBounded) :
    ∃ b:ℕ → ℝ, Sequence.subseq a b ∧ (b:Sequence)⁻¹.TendsTo 0 := by
  have h_abs_all : ∀ M : ℝ, M ≥ 0 → ∃ n : ℤ, |(a : Sequence) n| > M := by
    intro M hM
    by_contra! h
    apply ha
    refine ⟨M, hM, λ n => ?_⟩
    by_contra! h_gt
    have hle := h n
    linarith
  have h_abs_nat : ∀ M ≥ (0 : ℝ), ∃ n : ℕ, |a n| > M := by
    intro M hM
    obtain ⟨n, hn⟩ := h_abs_all M hM
    have hn_nonneg : (0 : ℤ) ≤ n := by
      by_contra! h_neg
      have h_zero : (a : Sequence) n = 0 := (a : Sequence).vanish n (by
        have hm : (a : Sequence).m = (0 : ℤ) := rfl
        rw [hm]
        exact h_neg)
      have : |(a : Sequence) n| = 0 := by
        rw [h_zero]
        simp
      linarith
    refine ⟨n.toNat, ?_⟩
    have h_simp : (a : Sequence) n = a (n.toNat) := by simp [hn_nonneg]
    rw [h_simp] at hn
    exact hn
  have h_abs_nat_ge : ∀ (M : ℝ) (N : ℕ), M ≥ 0 → ∃ n : ℕ, N ≤ n ∧ |a n| > M := by
    intro M N hM
    by_cases h : ∀ n : ℕ, N ≤ n → |a n| ≤ M
    · exfalso
      by_cases hN0 : N = 0
      · subst hN0
        have h_all : ∀ n : ℕ, |a n| ≤ M := by
          intro n; apply h n; exact Nat.zero_le n
        obtain ⟨n, hn⟩ := h_abs_nat M hM
        have := h_all n
        linarith
      · have hN_pos : 0 < N := Nat.pos_of_ne_zero hN0
        have h_range_nonempty : (Finset.image (fun i : ℕ => |a i|) (Finset.range N)).Nonempty := by
          refine ⟨|a 0|, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), rfl⟩⟩
        let B := (Finset.image (fun i : ℕ => |a i|) (Finset.range N)).max' h_range_nonempty
        have hB : ∀ i < N, |a i| ≤ B := by
          intro i hi
          apply Finset.le_max' (Finset.image (fun i : ℕ => |a i|) (Finset.range N)) (|a i|)
          exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩
        have hB_nonneg : 0 ≤ B := by
          have h0 : |a 0| ≤ B := hB 0 (by omega)
          linarith [abs_nonneg (a 0), h0]
        have hM' : ∀ n : ℕ, |a n| ≤ max B M := by
          intro n
          by_cases hn : n < N
          · have hle : |a n| ≤ B := hB n hn
            exact le_trans hle (le_max_left _ _)
          · push_neg at hn
            have hle : |a n| ≤ M := h n hn
            exact le_trans hle (le_max_right _ _)
        have hmax_nonneg : 0 ≤ max B M :=
          le_trans hM (le_max_right _ _)
        obtain ⟨n, hn⟩ := h_abs_nat (max B M) hmax_nonneg
        have := hM' n
        linarith
    · push_neg at h
      rcases h with ⟨n, hnN, hn⟩
      exact ⟨n, hnN, hn⟩
  let f : ℕ → ℕ :=
    Nat.rec
      (Classical.choose (h_abs_nat_ge (1 : ℝ) 0 (by norm_num)))
      (fun k fk => Classical.choose (h_abs_nat_ge ((k + 2 : ℕ) : ℝ) (fk + 1)
        (by exact_mod_cast show (0 : ℕ) ≤ k + 2 from by omega)))
  have hf_spec_base : 0 ≤ f 0 ∧ |a (f 0)| > (1 : ℝ) := by
    have h := Classical.choose_spec (h_abs_nat_ge (1 : ℝ) 0 (by norm_num))
    dsimp [f]
    exact h
  have hf_spec_succ (k : ℕ) : f k + 1 ≤ f (k + 1) ∧ |a (f (k + 1))| > ((k + 2 : ℕ) : ℝ) := by
    have h := Classical.choose_spec (h_abs_nat_ge ((k + 2 : ℕ) : ℝ) (f k + 1)
      (by exact_mod_cast show (0 : ℕ) ≤ k + 2 from by omega))
    dsimp [f]
    exact h
  have hf_val (k : ℕ) : |a (f k)| > (k : ℝ) + 1 := by
    induction' k with k ih
    · simpa using hf_spec_base.2
    · have h := hf_spec_succ k
      have h_val : |a (f (k + 1))| > ((k + 2 : ℕ) : ℝ) := h.2
      have h_eq : ((k + 2 : ℕ) : ℝ) = ((k + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
      simpa [h_eq] using h_val
  have hf_strictMono : StrictMono f :=
    strictMono_nat_of_lt_succ (fun k => by
      have h := hf_spec_succ k
      omega)
  let b := fun n : ℕ => a (f n)
  have hb_tendsto : (b : Sequence)⁻¹.TendsTo 0 := by
    rw [Sequence.tendsTo_iff (b⁻¹ : Sequence) 0]
    intro ε hε
    obtain ⟨K, hK⟩ := exists_nat_one_div_lt hε
    use (K : ℤ)
    intro n hn
    have hn_nonneg : (0 : ℤ) ≤ n := le_trans (by exact_mod_cast (Nat.zero_le K)) hn
    have h_simp : (b⁻¹ : Sequence) n = (b (n.toNat))⁻¹ := by simp [hn_nonneg]
    rw [h_simp, sub_zero]
    dsimp [b]
    have h_nat_ge : (K : ℕ) ≤ n.toNat := by
      have : (K : ℤ) ≤ n := hn
      omega
    have h_val : |a (f (n.toNat))| > (n.toNat : ℝ) + 1 := hf_val (n.toNat)
    have h_pos_val : 0 < |a (f (n.toNat))| := by linarith
    have h_pos_n : 0 < (n.toNat : ℝ) + 1 := by
      have : 0 ≤ (n.toNat : ℝ) := Nat.cast_nonneg _
      nlinarith
    have h_ineq : |a (f (n.toNat))|⁻¹ < ((n.toNat : ℝ) + 1)⁻¹ := by
      have h_lt : (n.toNat : ℝ) + 1 < |a (f (n.toNat))| := h_val
      have h_one_div := (one_div_lt_one_div h_pos_val h_pos_n).mpr h_lt
      simpa [div_eq_inv_mul] using h_one_div
    have h_ineq2 : ((n.toNat : ℝ) + 1)⁻¹ ≤ ((K : ℝ) + 1)⁻¹ := by
      have h_n_ge_K : (n.toNat : ℝ) + 1 ≥ (K : ℝ) + 1 := by
        have h_cast : (n.toNat : ℝ) ≥ (K : ℝ) := by exact_mod_cast h_nat_ge
        nlinarith
      have h_pos_K : 0 < (K : ℝ) + 1 := by
        have : 0 ≤ (K : ℝ) := Nat.cast_nonneg _
        nlinarith
      have h_one_div := (one_div_le_one_div h_pos_n h_pos_K).mpr h_n_ge_K
      simpa [div_eq_inv_mul] using h_one_div
    have h_lt_ε : ((K : ℝ) + 1)⁻¹ < ε := by
      simpa [div_eq_inv_mul] using hK
    have h_main : |(a (f (n.toNat)))⁻¹| < ε := by
      calc
        |(a (f (n.toNat)))⁻¹| = |a (f (n.toNat))|⁻¹ := abs_inv (a (f (n.toNat)))
        _ < ((n.toNat : ℝ) + 1)⁻¹ := h_ineq
        _ ≤ ((K : ℝ) + 1)⁻¹ := h_ineq2
        _ < ε := h_lt_ε
    exact le_of_lt h_main
  refine ⟨b, ⟨f, hf_strictMono, λ n => rfl⟩, hb_tendsto⟩


end Chapter6
