import Mathlib.Tactic
import Analysis.Section_5_1


/-!
# Analysis I, Section 5.2: Equivalent Cauchy sequences

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main constructions and results of this section:

- Notion of an ε-close and eventually ε-close sequences of rationals.
- Notion of an equivalent Cauchy sequence of rationals.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/


abbrev Rat.CloseSeq (ε: ℚ) (a b: Chapter5.Sequence) : Prop :=
  ∀ n, n ≥ a.n₀ → n ≥ b.n₀ → ε.Close (a n) (b n)

abbrev Rat.EventuallyClose (ε: ℚ) (a b: Chapter5.Sequence) : Prop :=
  ∃ N, ε.CloseSeq (a.from N) (b.from N)

namespace Chapter5

/-- Definition 5.2.1 ($ε$-close sequences) -/
lemma Rat.closeSeq_def (ε: ℚ) (a b: Sequence) :
    ε.CloseSeq a b ↔ ∀ n, n ≥ a.n₀ → n ≥ b.n₀ → ε.Close (a n) (b n) := by rfl

/-- Example 5.2.2 -/
example : (0.1:ℚ).CloseSeq ((fun n:ℕ ↦ ((-1)^n:ℚ)):Sequence)
((fun n:ℕ ↦ ((1.1:ℚ) * (-1)^n)):Sequence) := by
  rw [Rat.closeSeq_def]
  intro n ha hb
  rw [Rat.Close]
  simp at ha hb ⊢
  rw [if_pos ha, if_pos hb, ← one_sub_mul]
  simp
  linarith

/-- Example 5.2.2 -/
example : ¬ (0.1:ℚ).Steady ((fun n:ℕ ↦ ((-1)^n:ℚ)):Sequence) := by
  rw [Rat.Steady]
  intro h
  have h' := h 0 (by norm_num) 1 (by norm_num)
  rw [Rat.Close] at h'
  simp at h'
  linarith

/-- Example 5.2.2 -/
example : ¬ (0.1:ℚ).Steady ((fun n:ℕ ↦ ((1.1:ℚ) * (-1)^n)):Sequence) := by
  rw [Rat.Steady]
  intro h
  have h' := h 0 (by norm_num) 1 (by norm_num)
  rw [Rat.Close] at h'
  simp at h'
  linarith

/-- Definition 5.2.3 (Eventually ε-close sequences) -/
lemma Rat.eventuallyClose_def (ε: ℚ) (a b: Sequence) :
    ε.EventuallyClose a b ↔ ∃ N, ε.CloseSeq (a.from N) (b.from N) := by rfl

/-- Definition 5.2.3 (Eventually ε-close sequences) -/
lemma Rat.eventuallyClose_iff (ε: ℚ) (a b: ℕ → ℚ) :
    ε.EventuallyClose (a:Sequence) (b:Sequence) ↔ ∃ N, ∀ n ≥ N, |a n - b n| ≤ ε := by
  simp only [Rat.EventuallyClose, Rat.CloseSeq, Rat.Close, Sequence.ofNatFun]
  constructor
  · rintro ⟨N, h⟩
    use (max 0 N).toNat
    intro n hn
    have hn' : (n:ℤ) ≥ max 0 N := by omega
    have := h n hn' hn'
    simp [show (n:ℤ) ≥ 0 from by omega] at this
    simp [show N ≤ (↑n:ℤ) from by omega] at this
    exact this
  · rintro ⟨N, h⟩
    refine ⟨N, fun n hn1 _ => ?_⟩
    have hn0 : n ≥ 0 := le_trans (le_max_left 0 ↑N) hn1
    simp [show n ≥ 0 from hn0]
    have := h n.toNat (by omega)
    simp [show (↑N:ℤ) ≤ n from by omega]
    exact this

/-- Example 5.2.5 -/
example : ¬ (0.1:ℚ).CloseSeq ((fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)):Sequence)
  ((fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)):Sequence) := by
  rw [Rat.closeSeq_def]
  intro h
  have h' := h 0 (by norm_num) (by norm_num)
  rw [Rat.Close] at h'
  simp at h'
  linarith

example : (0.1:ℚ).EventuallyClose ((fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)):Sequence)
  ((fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)):Sequence) := by
  rw [Rat.eventuallyClose_iff]
  use 1
  intro n hn
  simp
  have h1 : |(10:ℚ)^(-(n:ℤ)-1)| ≤ 0.01 := by
    refine le_trans (le_of_eq (abs_of_nonneg (zpow_nonneg (by norm_num : (0:ℚ) ≤ 10) _))) ?_
    exact le_trans (zpow_le_zpow_right₀ (by norm_num : (1:ℚ) ≤ 10) (by omega : -(↑n:ℤ)-1 ≤ -(1:ℤ)-1)) (by norm_num)
  rw [← two_mul, abs_mul]
  linarith

example : (0.01:ℚ).EventuallyClose ((fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)):Sequence)
  ((fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)):Sequence) := by
  rw [Rat.eventuallyClose_iff]
  use 2; intro n hn; simp
  have h1 : (0:ℚ) ≤ (10:ℚ)^(-(n:ℤ)-1) := zpow_nonneg (by norm_num) _
  have h2 : (10:ℚ)^(-(n:ℤ)-1) ≤ 0.001 :=
    le_trans (zpow_le_zpow_right₀ (by norm_num : (1:ℚ) ≤ 10) (by omega : -(↑n:ℤ)-1 ≤ -(2:ℤ)-1)) (by norm_num)
  rw [abs_of_nonneg (by linarith)]; linarith

/-- Definition 5.2.6 (Equivalent sequences) -/
abbrev Sequence.Equiv (a b: ℕ → ℚ) : Prop :=
  ∀ ε > (0:ℚ), ε.EventuallyClose (a:Sequence) (b:Sequence)

/-- Definition 5.2.6 (Equivalent sequences) -/
lemma Sequence.equiv_def (a b: ℕ → ℚ) :
    Equiv a b ↔ ∀ (ε:ℚ), ε > 0 → ε.EventuallyClose (a:Sequence) (b:Sequence) := by rfl

/-- Definition 5.2.6 (Equivalent sequences) -/
lemma Sequence.equiv_iff (a b: ℕ → ℚ) : Equiv a b ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - b n| ≤ ε := by
  simp only [Sequence.equiv_def, Rat.eventuallyClose_iff]

/-- Proposition 5.2.8 -/
lemma Sequence.equiv_example :
  -- This proof is perhaps more complicated than it needs to be; a shorter version may be
  -- possible that is still faithful to the original text.
  Equiv (fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)) (fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)) := by
  set a := fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)
  set b := fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)
  rw [equiv_iff]
  intro ε hε
  have hab (n:ℕ) : |a n - b n| = 2 * 10 ^ (-(n:ℤ)-1) := calc
    _ = |((1:ℚ) + (10:ℚ)^(-(n:ℤ)-1)) - ((1:ℚ) - (10:ℚ)^(-(n:ℤ)-1))| := rfl
    _ = |2 * (10:ℚ)^(-(n:ℤ)-1)| := by ring_nf
    _ = _ := abs_of_nonneg (by positivity)
  have hab' (N:ℕ) : ∀ n ≥ N, |a n - b n| ≤ 2 * 10 ^(-(N:ℤ)-1) := by
    intro n hn; rw [hab n]; gcongr; norm_num
  have hN : ∃ N:ℕ, 2 * (10:ℚ) ^(-(N:ℤ)-1) ≤ ε := by
    have hN' (N:ℕ) : 2 * (10:ℚ)^(-(N:ℤ)-1) ≤ 2/(N+1) := calc
      _ = 2 / (10:ℚ)^(N+1) := by
        field_simp
        simp [←Section_4_3.pow_eq_zpow, ←zpow_add₀ (show 10 ≠ (0:ℚ) by norm_num)]
      _ ≤ _ := by
        gcongr
        apply le_trans _ (pow_le_pow_left₀ (show 0 ≤ (2:ℚ) by norm_num)
          (show (2:ℚ) ≤ 10 by norm_num) _)
        convert Nat.cast_le.mpr (Section_4_3.two_pow_geq (N+1)) using 1 <;> try infer_instance
        all_goals simp
    choose N hN using exists_nat_gt (2 / ε)
    refine ⟨ N, (hN' N).trans ?_ ⟩
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hε] at hN
    grind [mul_comm]
  choose N hN using hN; use N; intro n hn
  linarith [hab' N n hn]

/-- Exercise 5.2.1 -/
theorem Sequence.isCauchy_of_equiv {a b: ℕ → ℚ} (hab: Equiv a b) :
    (a:Sequence).IsCauchy ↔ (b:Sequence).IsCauchy := by
  suffices h : ∀ {a b : ℕ → ℚ}, Equiv a b → (a:Sequence).IsCauchy → (b:Sequence).IsCauchy from
    ⟨h hab, h ((equiv_iff b a).mpr (fun ε hε => let ⟨N, hN⟩ := (equiv_iff a b).mp hab ε hε;
      ⟨N, fun n hn => by rw [abs_sub_comm]; exact hN n hn⟩))⟩
  intro a b hab hca
  rw [Sequence.IsCauchy.coe] at hca ⊢
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := (equiv_iff a b).mp hab (ε/3) (by linarith)
  obtain ⟨N₂, hN₂⟩ := hca (ε/3) (by linarith)
  refine ⟨max N₁ N₂, fun j hj k hk => ?_⟩
  have hj₁ := hN₁ j (le_of_max_le_left hj)
  have hk₁ := hN₁ k (le_of_max_le_left hk)
  have hjk := hN₂ j (le_of_max_le_right hj) k (le_of_max_le_right hk)
  simp [Section_4_3.dist, Section_4_3.abs_eq_abs] at hjk ⊢
  calc |b j - b k| = |(b j - a j) + (a j - a k) + (a k - b k)| := by ring_nf
    _ ≤ |b j - a j| + |a j - a k| + |a k - b k| :=
      le_trans (abs_add_le _ _) (by linarith [abs_add_le (b j - a j) (a j - a k)])
    _ ≤ ε/3 + ε/3 + ε/3 := by linarith [abs_sub_comm (a j) (b j), abs_sub_comm (a k) (b k)]
    _ = ε := by ring

/-- Exercise 5.2.2 -/
theorem Sequence.isBounded_of_eventuallyClose {ε:ℚ} {a b: ℕ → ℚ} (hab: ε.EventuallyClose a b) :
    (a:Sequence).IsBounded ↔ (b:Sequence).IsBounded := by
  suffices h : ∀ {ε:ℚ} {a b : ℕ → ℚ}, ε.EventuallyClose (a:Sequence) (b:Sequence) →
      (a:Sequence).IsBounded → (b:Sequence).IsBounded from
    ⟨h hab, h ((Rat.eventuallyClose_iff ε a b).mp hab |> fun ⟨N, hN⟩ =>
      (Rat.eventuallyClose_iff ε b a).mpr ⟨N, fun n hn => by rw [abs_sub_comm]; exact hN n hn⟩)⟩
  intro ε a b hab ⟨M, hM0, hMa⟩
  obtain ⟨N, hN⟩ := (Rat.eventuallyClose_iff ε a b).mp hab
  have hb_ge (n:ℕ) (hn : n ≥ N) : |b n| ≤ M + ε := by
    have h1 : |b n - a n| ≤ ε := by rw [abs_sub_comm]; exact hN n hn
    have h2 : |a n| ≤ M := by
      have := hMa n
      simp [Sequence.ofNatFun] at this
      exact this
    calc |b n| = |(b n - a n) + a n| := by ring_nf
      _ ≤ |b n - a n| + |a n| := abs_add_le _ _
      _ ≤ ε + M := by linarith
      _ = M + ε := by ring
  have hb_lt : ∃ M' ≥ 0, ∀ n < N, |b n| ≤ M' := by
    by_cases hN0 : N = 0
    · exact ⟨0, le_refl _, fun n hn => by omega⟩
    · have ⟨M', hM'0, hM'⟩ := IsBounded.finite (fun (i : Fin N) => b i)
      exact ⟨M', hM'0, fun n hn => hM' ⟨n, hn⟩⟩
  obtain ⟨M', hM'0, hM'⟩ := hb_lt
  refine ⟨max (M + ε) M', by positivity, fun n => ?_⟩
  simp only [Sequence.ofNatFun, Sequence.boundedBy_def] at hMa ⊢
  split_ifs with hn0
  · have m := n.toNat
    by_cases hm : n.toNat ≥ N
    · exact (hb_ge n.toNat hm).trans (le_max_left _ _)
    · exact (hM' n.toNat (by omega)).trans (le_max_right _ _)
  · simp; right; exact hM'0

end Chapter5
