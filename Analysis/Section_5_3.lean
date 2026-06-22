import Mathlib.Tactic
import Analysis.Section_5_2
import Mathlib.Algebra.Group.MinimalAxioms


/-!
# Analysis I, Section 5.3: The construction of the real numbers

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Notion of a formal limit of a Cauchy sequence.
- Construction of a real number type `Chapter5.Real`.
- Basic arithmetic operations and properties.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter5

/-- A class of Cauchy sequences that start at zero. -/
@[ext]
class CauchySequence extends Sequence where
  zero : n₀ = 0
  cauchy : toSequence.IsCauchy

theorem CauchySequence.ext' {a b: CauchySequence} (h: a.seq = b.seq) : a = b := by
  apply CauchySequence.ext _ h
  rw [a.zero, b.zero]

/-- A sequence starting at zero that is Cauchy, can be viewed as a {name}`CauchySequence`. -/
abbrev CauchySequence.mk' {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) : CauchySequence where
  n₀ := 0
  seq := (a:Sequence).seq
  vanish := by aesop
  zero := rfl
  cauchy := ha

@[simp]
theorem CauchySequence.coe_eq {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) :
  (mk' ha).toSequence = (a:Sequence) := rfl

instance CauchySequence.instCoeFun : CoeFun CauchySequence (fun _ ↦ ℕ → ℚ) where
  coe a n := a.toSequence (n:ℤ)

@[simp]
theorem CauchySequence.coe_to_sequence (a: CauchySequence) :
    ((a:ℕ → ℚ):Sequence) = a.toSequence := by
  apply Sequence.ext (by simp [Sequence.n0_coe, a.zero])
  ext n; by_cases h:n ≥ 0 <;> simp_all
  rw [a.vanish]; rwa [a.zero]

@[simp]
theorem CauchySequence.coe_coe {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) : mk' ha = a := by rfl

/-- Proposition 5.3.3 / Exercise 5.3.1 -/
theorem Sequence.equiv_trans {a b c:ℕ → ℚ} (hab: Equiv a b) (hbc: Equiv b c) :
  Equiv a c := by
  rw [equiv_iff]
  intro ε hε
  have hε2 : ε/2 > 0 := by linarith
  rcases (equiv_iff a b).mp hab (ε/2) hε2 with ⟨N₁, hN₁⟩
  rcases (equiv_iff b c).mp hbc (ε/2) hε2 with ⟨N₂, hN₂⟩
  use max N₁ N₂
  intro n hn
  have hn₁ : n ≥ N₁ := le_of_max_le_left hn
  have hn₂ : n ≥ N₂ := le_of_max_le_right hn
  calc
    |a n - c n| = |(a n - b n) + (b n - c n)| := by
      simp [sub_add_sub_cancel]
    _ ≤ |a n - b n| + |b n - c n| := abs_add_le _ _
    _ ≤ ε/2 + ε/2 := by
      nlinarith [hN₁ n hn₁, hN₂ n hn₂]
    _ = ε := by ring

/-- Proposition 5.3.3 / Exercise 5.3.1 -/
instance CauchySequence.instSetoid : Setoid CauchySequence where
  r := fun a b ↦ Sequence.Equiv a b
  iseqv := {
     refl := by intro x e he; use 0; intro n hn hn'; simp [Rat.Close]; linarith
     symm := by
      intro x y h e he
      have ⟨N, hN⟩ := h e he
      use N
      intro n hn hn'
      have := hN n hn hn'
      unfold Rat.Close at this ⊢
      simp_all
      rwa [abs_sub_comm]
     trans := by intro x y z h1 h2; apply Sequence.equiv_trans h1 h2
  }

theorem CauchySequence.equiv_iff (a b: CauchySequence) : a ≈ b ↔ Sequence.Equiv a b := by rfl

/-- Every constant sequence is Cauchy. -/
theorem Sequence.IsCauchy.const (a:ℚ) : ((fun _:ℕ ↦ a):Sequence).IsCauchy := by
  intro e he
  use 0
  rw [Rat.Steady]
  simp
  intro n hn m hm
  rw [Rat.Close, if_pos hn, if_pos hn, if_pos hm, if_pos hm, sub_self, abs_zero]
  linarith

instance CauchySequence.instZero : Zero CauchySequence where
  zero := CauchySequence.mk' (a := fun _: ℕ ↦ 0) (Sequence.IsCauchy.const (0:ℚ))

abbrev Real := Quotient CauchySequence.instSetoid

open Classical in
/--
  It is convenient in Lean to assign the "dummy" value of {lean}`0` to {lean}`LIM a` when {lean}`a` is not Cauchy.
  This requires classical logic, because the property of being Cauchy is not computable or
  decidable.
-/
noncomputable abbrev LIM (a:ℕ → ℚ) : Real :=
  Quotient.mk _ (if h : (a:Sequence).IsCauchy then CauchySequence.mk' h else (0:CauchySequence))

theorem LIM_def {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) :
    LIM a = Quotient.mk _ (CauchySequence.mk' ha) := by
  rw [LIM, dif_pos ha]

/-- Definition 5.3.1 (Real numbers) -/
theorem Real.eq_lim (x:Real) : ∃ (a:ℕ → ℚ), (a:Sequence).IsCauchy ∧ x = LIM a := by
  apply Quotient.ind _ x; intro a; use (a:ℕ → ℚ)
  observe : ((a:ℕ → ℚ):Sequence) = a.toSequence
  rw [this, LIM_def (by convert a.cauchy)]
  refine ⟨ a.cauchy, ?_ ⟩
  congr; ext n; simp; replace := congr($this n); simp_all

/-- Definition 5.3.1 (Real numbers) -/
theorem Real.LIM_eq_LIM {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
  LIM a = LIM b ↔ Sequence.Equiv a b := by
  constructor
  . intro h; replace h := Quotient.exact h
    rwa [dif_pos ha, dif_pos hb, CauchySequence.equiv_iff] at h
  intro h; apply Quotient.sound
  rwa [dif_pos ha, dif_pos hb, CauchySequence.equiv_iff]

/--Lemma 5.3.6 (Sum of Cauchy sequences is Cauchy)-/
theorem Sequence.IsCauchy.add {a b:ℕ → ℚ}  (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
    (a + b:Sequence).IsCauchy := by
  -- This proof is written to follow the structure of the original text.
  rw [coe] at *
  intro ε hε
  choose N1 ha using ha _ (half_pos hε)
  choose N2 hb using hb _ (half_pos hε)
  use max N1 N2
  intro j hj k hk
  have h1 := ha j ?_ k ?_ <;> try omega
  have h2 := hb j ?_ k ?_ <;> try omega
  simp [Section_4_3.dist] at *
  calc
    Section_4_3.abs (a j + b j - (a k + b k)) = Section_4_3.abs ((a j - a k) + (b j - b k)) := by ring_nf
    _ ≤ Section_4_3.abs (a j - a k) + Section_4_3.abs (b j - b k) := Section_4_3.abs_add _ _
    _ ≤ ε / 2 + ε / 2 := by nlinarith
    _ = ε := by ring


/--Lemma 5.3.7 (Sum of equivalent sequences is equivalent)-/
theorem Sequence.add_equiv_left {a a':ℕ → ℚ} (b:ℕ → ℚ) (haa': Equiv a a') :
    Equiv (a + b) (a' + b) := by
  -- This proof is written to follow the structure of the original text.
  rw [equiv_def] at *
  peel 2 haa' with ε hε haa'
  rw [Rat.eventuallyClose_def] at *
  choose N haa' using haa'; use N
  simp [Rat.closeSeq_def] at *
  peel 5 haa' with n hn hN _ _ haa'
  simp [hn, hN] at *
  convert Section_4_3.add_close haa' (Section_4_3.close_refl (b n.toNat))
  simp

/--Lemma 5.3.7 (Sum of equivalent sequences is equivalent)-/
theorem Sequence.add_equiv_right {b b':ℕ → ℚ} (a:ℕ → ℚ) (hbb': Equiv b b') :
    Equiv (a + b) (a + b') := by simp_rw [add_comm]; exact add_equiv_left _ hbb'

/--Lemma 5.3.7 (Sum of equivalent sequences is equivalent)-/
theorem Sequence.add_equiv {a b a' b':ℕ → ℚ} (haa': Equiv a a')
  (hbb': Equiv b b') :
    Equiv (a + b) (a' + b') :=
  equiv_trans (add_equiv_left _ haa') (add_equiv_right _ hbb')

/-- Definition 5.3.4 (Addition of reals) -/
noncomputable instance Real.add_inst : Add Real where
  add := fun x y ↦
    Quotient.liftOn₂ x y (fun a b ↦ LIM (a + b)) (by
      intro a b a' b' _ _
      change LIM ((a:ℕ → ℚ) + (b:ℕ → ℚ)) = LIM ((a':ℕ → ℚ) + (b':ℕ → ℚ))
      rw [LIM_eq_LIM]
      . solve_by_elim [Sequence.add_equiv]
      all_goals apply Sequence.IsCauchy.add <;> rw [CauchySequence.coe_to_sequence] <;> convert @CauchySequence.cauchy ?_
      )

/-- Definition 5.3.4 (Addition of reals) -/
theorem Real.LIM_add {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
  LIM a + LIM b = LIM (a + b) := by
  simp_rw [LIM_def ha, LIM_def hb, LIM_def (Sequence.IsCauchy.add ha hb)]
  convert Quotient.liftOn₂_mk _ _ _ _ using 1
  simp [LIM]; grind


/-- Proposition 5.3.10 (Product of Cauchy sequences is Cauchy) -/
theorem Sequence.IsCauchy.mul {a b:ℕ → ℚ}  (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
    (a * b:Sequence).IsCauchy := by
  have ha_bdd : (a:Sequence).IsBounded := Sequence.isBounded_of_isCauchy ha
  have hb_bdd : (b:Sequence).IsBounded := Sequence.isBounded_of_isCauchy hb
  rcases ha_bdd with ⟨Ma, hMa, ha_bound⟩
  rcases hb_bdd with ⟨Mb, hMb, hb_bound⟩
  have ha_bound' (n : ℕ) : |a n| ≤ Ma := by
    have h := ha_bound (n : ℤ)
    simpa [show (a:Sequence) (n:ℤ) = a n by simp] using h
  have hb_bound' (n : ℕ) : |b n| ≤ Mb := by
    have h := hb_bound (n : ℤ)
    simpa [show (b:Sequence) (n:ℤ) = b n by simp] using h
  rw [Sequence.IsCauchy.coe] at *
  intro ε hε
  set M := Ma + Mb + 1 with hM_def
  have hM_pos : M > 0 := by
    dsimp [M]; nlinarith
  have h_div_pos : ε / (2 * M) > 0 := by
    refine div_pos hε ?_
    nlinarith
  choose N1 hN1 using ha _ h_div_pos
  choose N2 hN2 using hb _ h_div_pos
  use max N1 N2
  intro j hj k hk
  have ha_jk : Section_4_3.dist (a j) (a k) ≤ ε / (2 * M) :=
    hN1 j (by omega) k (by omega)
  have hb_jk : Section_4_3.dist (b j) (b k) ≤ ε / (2 * M) :=
    hN2 j (by omega) k (by omega)
  simp [Section_4_3.dist] at *
  have ha_jk_nonneg : Section_4_3.abs (a j - a k) ≥ 0 := Section_4_3.abs_nonneg _
  have hb_jk_nonneg : Section_4_3.abs (b j - b k) ≥ 0 := Section_4_3.abs_nonneg _
  have ha_j_nonneg : Section_4_3.abs (a j) ≥ 0 := Section_4_3.abs_nonneg _
  have ha_k_nonneg : Section_4_3.abs (a k) ≥ 0 := Section_4_3.abs_nonneg _
  have hb_j_nonneg : Section_4_3.abs (b j) ≥ 0 := Section_4_3.abs_nonneg _
  have hb_k_nonneg : Section_4_3.abs (b k) ≥ 0 := Section_4_3.abs_nonneg _
  have ha_bound_s4 (n : ℕ) : Section_4_3.abs (a n) ≤ Ma := by
    rw [Section_4_3.abs_eq_abs]; exact ha_bound' n
  have hb_bound_s4 (n : ℕ) : Section_4_3.abs (b n) ≤ Mb := by
    rw [Section_4_3.abs_eq_abs]; exact hb_bound' n
  calc
    Section_4_3.abs (a j * b j - a k * b k) = Section_4_3.abs ((a j - a k) * b j + a k * (b j - b k)) := by
      have h : a j * b j - a k * b k = (a j - a k) * b j + a k * (b j - b k) := by ring
      rw [h]
    _ ≤ Section_4_3.abs ((a j - a k) * b j) + Section_4_3.abs (a k * (b j - b k)) := Section_4_3.abs_add _ _
    _ = Section_4_3.abs (a j - a k) * Section_4_3.abs (b j) + Section_4_3.abs (a k) * Section_4_3.abs (b j - b k) := by
      simp [Section_4_3.abs_mul]
    _ ≤ (ε / (2 * M)) * Section_4_3.abs (b j) + Section_4_3.abs (a k) * (ε / (2 * M)) := by
      nlinarith
    _ ≤ (ε / (2 * M)) * M + M * (ε / (2 * M)) := by
      nlinarith [ha_bound_s4 j, ha_bound_s4 k, hb_bound_s4 j, hb_bound_s4 k,
        show Ma ≤ M by
          dsimp [M]; nlinarith,
        show Mb ≤ M by
          dsimp [M]; nlinarith]
    _ = ε := by
      have hcalc : (ε / (2 * M)) * M = ε / 2 := by
        field_simp [show M ≠ 0 from by nlinarith]
      calc
        (ε / (2 * M)) * M + M * (ε / (2 * M)) = (ε / 2) + M * (ε / (2 * M)) := by rw [hcalc]
        _ = (ε / 2) + ((ε / (2 * M)) * M) := by ring
        _ = (ε / 2) + (ε / 2) := by rw [hcalc]
        _ = ε := by ring

/-- Proposition 5.3.10 (Product of equivalent sequences is equivalent) / Exercise 5.3.2 -/
theorem Sequence.mul_equiv_left {a a':ℕ → ℚ} (b:ℕ → ℚ) (hb : (b:Sequence).IsCauchy) (haa': Equiv a a') :
  Equiv (a * b) (a' * b) := by
  rw [Sequence.equiv_iff] at *
  intro ε hε
  have hb_bdd : (b:Sequence).IsBounded := Sequence.isBounded_of_isCauchy hb
  rcases hb_bdd with ⟨M, hM, hb_bound⟩
  have hb_bound' (n : ℕ) : |b n| ≤ M := by
    have h := hb_bound (n : ℤ)
    simpa [show (b:Sequence) (n:ℤ) = b n by simp] using h
  by_cases hM0 : M = 0
  · use 0
    intro n hn
    have hb0 : |b n| = 0 := by
      have h := hb_bound' n
      rw [hM0] at h
      have h_nonneg : 0 ≤ |b n| := abs_nonneg _
      nlinarith
    calc
      |(a * b) n - (a' * b) n| = |a n * b n - a' n * b n| := by simp
      _ = |(a n - a' n) * b n| := by
        have h : a n * b n - a' n * b n = (a n - a' n) * b n := by ring
        rw [h]
      _ = |a n - a' n| * |b n| := by rw [abs_mul]
      _ = |a n - a' n| * 0 := by rw [hb0]
      _ = 0 := by ring
      _ ≤ ε := by linarith
  · have hMpos : M > 0 := by
      by_contra! H
      apply hM0
      nlinarith
    have hεM : ε / M > 0 := div_pos hε hMpos
    rcases haa' (ε / M) hεM with ⟨N, hN⟩
    use N
    intro n hn
    have haa'_n : |a n - a' n| ≤ ε / M := hN n hn
    calc
      |(a * b) n - (a' * b) n| = |a n * b n - a' n * b n| := by simp
      _ = |(a n - a' n) * b n| := by
        have h : a n * b n - a' n * b n = (a n - a' n) * b n := by ring
        rw [h]
      _ = |a n - a' n| * |b n| := by rw [abs_mul]
      _ ≤ (ε / M) * M :=
        mul_le_mul haa'_n (hb_bound' n) (abs_nonneg _) (div_nonneg (by linarith) (by linarith))
      _ = ε := by field_simp [hMpos.ne.symm]

/--Proposition 5.3.10 (Product of equivalent sequences is equivalent) / Exercise 5.3.2 -/
theorem Sequence.mul_equiv_right {b b':ℕ → ℚ} (a:ℕ → ℚ)  (ha : (a:Sequence).IsCauchy)  (hbb': Equiv b b') :
  Equiv (a * b) (a * b') := by simp_rw [mul_comm]; exact mul_equiv_left a ha hbb'

/--Proposition 5.3.10 (Product of equivalent sequences is equivalent) / Exercise 5.3.2 -/
theorem Sequence.mul_equiv
  {a b a' b':ℕ → ℚ}
  (ha : (a:Sequence).IsCauchy)
  (hb' : (b':Sequence).IsCauchy)
  (haa': Equiv a a')
  (hbb': Equiv b b') : Equiv (a * b) (a' * b') :=
    equiv_trans (mul_equiv_right _ ha hbb') (mul_equiv_left _ hb' haa')

/-- Definition 5.3.9 (Product of reals) -/
noncomputable instance Real.mul_inst : Mul Real where
  mul := fun x y ↦
    Quotient.liftOn₂ x y (fun a b ↦ LIM (a * b)) (by
      intro a b a' b' haa' hbb'
      change LIM ((a:ℕ → ℚ) * (b:ℕ → ℚ)) = LIM ((a':ℕ → ℚ) * (b':ℕ → ℚ))
      rw [LIM_eq_LIM]
      . exact Sequence.mul_equiv (by rw [CauchySequence.coe_to_sequence]; exact a.cauchy) (by rw [CauchySequence.coe_to_sequence]; exact b'.cauchy) haa' hbb'
      all_goals apply Sequence.IsCauchy.mul <;> rw [CauchySequence.coe_to_sequence] <;> convert @CauchySequence.cauchy ?_
      )

theorem Real.LIM_mul {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
  LIM a * LIM b = LIM (a * b) := by
  simp_rw [LIM_def ha, LIM_def hb, LIM_def (Sequence.IsCauchy.mul ha hb)]
  convert Quotient.liftOn₂_mk _ _ _ _ using 1
  simp [LIM]; grind

instance Real.instRatCast : RatCast Real where
  ratCast := fun q ↦
    Quotient.mk _ (CauchySequence.mk' (a := fun _ ↦ q) (Sequence.IsCauchy.const q))

theorem Real.ratCast_def (q:ℚ) : (q:Real) = LIM (fun _ ↦ q) := by rw [LIM_def]; rfl

/-- Exercise 5.3.3 -/
@[simp]
theorem Real.ratCast_inj (q r:ℚ) : (q:Real) = (r:Real) ↔ q = r := by
  rw [Real.ratCast_def q, Real.ratCast_def r]
  constructor
  · intro h
    have hq_cauchy : ((fun _ : ℕ ↦ q):Sequence).IsCauchy := Sequence.IsCauchy.const q
    have hr_cauchy : ((fun _ : ℕ ↦ r):Sequence).IsCauchy := Sequence.IsCauchy.const r
    rw [Real.LIM_eq_LIM hq_cauchy hr_cauchy] at h
    rw [Sequence.equiv_iff] at h
    by_contra! hne
    have h_abs_pos : |q - r| > 0 := by
      refine abs_pos.mpr ?_
      exact sub_ne_zero.mpr hne
    rcases h (|q - r| / 2) (by nlinarith) with ⟨N, hN⟩
    have hN0 : |q - r| ≤ |q - r| / 2 := hN N (le_refl N)
    nlinarith
  · intro h
    subst h
    rfl

instance Real.instOfNat {n:ℕ} : OfNat Real n where
  ofNat := ((n:ℚ):Real)

instance Real.instNatCast : NatCast Real where
  natCast n := ((n:ℚ):Real)

@[simp]
theorem Real.LIM.zero : LIM (fun _ ↦ (0:ℚ)) = 0 := by rw [←ratCast_def 0]; rfl

instance Real.instIntCast : IntCast Real where
  intCast n := ((n:ℚ):Real)

/-- {name (full := RatCast.ratCast)}`ratCast` distributes over addition -/
theorem Real.ratCast_add (a b:ℚ) : (a:Real) + (b:Real) = (a+b:ℚ) := by
  calc
    (a:Real) + (b:Real) = LIM (fun _ : ℕ ↦ a) + LIM (fun _ : ℕ ↦ b) := by
      simp [Real.ratCast_def]
    _ = LIM ((fun _ : ℕ ↦ a) + (fun _ : ℕ ↦ b)) :=
      Real.LIM_add (Sequence.IsCauchy.const a) (Sequence.IsCauchy.const b)
    _ = LIM (fun _ : ℕ ↦ a + b) := rfl
    _ = (a + b : ℚ) := by
      simp [Real.ratCast_def]

/-- {name (full := RatCast.ratCast)}`ratCast` distributes over multiplication -/
theorem Real.ratCast_mul (a b:ℚ) : (a:Real) * (b:Real) = (a*b:ℚ) := by
  calc
    (a:Real) * (b:Real) = LIM (fun _ : ℕ ↦ a) * LIM (fun _ : ℕ ↦ b) := by
      simp [Real.ratCast_def]
    _ = LIM ((fun _ : ℕ ↦ a) * (fun _ : ℕ ↦ b)) :=
      Real.LIM_mul (Sequence.IsCauchy.const a) (Sequence.IsCauchy.const b)
    _ = LIM (fun _ : ℕ ↦ a * b) := rfl
    _ = (a * b : ℚ) := by
      simp [Real.ratCast_def]

noncomputable instance Real.instNeg : Neg Real where
  neg x := ((-1:ℚ):Real) * x

/-- {name (full := RatCast.ratCast)}`ratCast` commutes with negation -/
theorem Real.neg_ratCast (a:ℚ) : -(a:Real) = (-a:ℚ) := by
  calc
    -(a:Real) = ((-1:ℚ):Real) * (a:Real) := rfl
    _ = ((-1 : ℚ) * a : ℚ) := by rw [Real.ratCast_mul (-1) a]
    _ = (-a : ℚ) := by simp

/-- It may be possible to omit the {name (full := Sequence.IsCauchy)}`IsCauchy` hypothesis here. -/
theorem Real.neg_LIM (a:ℕ → ℚ) (ha: (a:Sequence).IsCauchy) : -LIM a = LIM (-a) := by
  calc
    -LIM a = ((-1:ℚ):Real) * LIM a := rfl
    _ = LIM (fun _ : ℕ ↦ (-1 : ℚ)) * LIM a := by
      simp [Real.ratCast_def]
    _ = LIM ((fun _ : ℕ ↦ (-1 : ℚ)) * a) :=
      Real.LIM_mul (Sequence.IsCauchy.const (-1)) ha
    _ = LIM (-a) := by
      apply congrArg LIM
      ext n
      simp

theorem Sequence.IsCauchy.neg (a:ℕ → ℚ) (ha: (a:Sequence).IsCauchy) :
    ((-a:ℕ → ℚ):Sequence).IsCauchy := by
  rw [Sequence.IsCauchy.coe] at *
  intro ε hε
  rcases ha ε hε with ⟨N, hN⟩
  use N
  intro j hj k hk
  have h := hN j hj k hk
  calc
    Section_4_3.dist ((-a) j) ((-a) k) = Section_4_3.abs ((-a) j - (-a) k) := rfl
    _ = Section_4_3.abs (-(a j) + a k) := by simp [Pi.neg_apply, sub_eq_add_neg]
    _ = Section_4_3.abs (a k - a j) := by
      simp [sub_eq_add_neg, add_comm]
    _ = Section_4_3.abs (a j - a k) := by
      rw [← neg_sub (a j) (a k), Section_4_3.abs_neg]
    _ = Section_4_3.dist (a j) (a k) := rfl
    _ ≤ ε := h

/-- Proposition 5.3.11 (laws of algebra) -/
noncomputable instance Real.addGroup_inst : AddGroup Real where
  add := (· + ·)
  zero := (0 : Real)
  neg := (-·)
  sub := λ x y => x + (-y)
  sub_eq_add_neg := λ _ _ => rfl
  add_assoc := by
    intro a b c
    rcases Real.eq_lim a with ⟨a_seq, ha, ha_eq⟩
    rcases Real.eq_lim b with ⟨b_seq, hb, hb_eq⟩
    rcases Real.eq_lim c with ⟨c_seq, hc, hc_eq⟩
    calc
      a + b + c = (LIM a_seq + LIM b_seq) + LIM c_seq := by simp [ha_eq, hb_eq, hc_eq]
      _ = LIM (a_seq + b_seq) + LIM c_seq := by rw [Real.LIM_add ha hb]
      _ = LIM ((a_seq + b_seq) + c_seq) := Real.LIM_add (Sequence.IsCauchy.add ha hb) hc
      _ = LIM (a_seq + (b_seq + c_seq)) := by simp [add_assoc]
      _ = LIM a_seq + LIM (b_seq + c_seq) := by rw [Real.LIM_add ha (Sequence.IsCauchy.add hb hc)]
      _ = LIM a_seq + (LIM b_seq + LIM c_seq) := by rw [Real.LIM_add hb hc]
      _ = a + (b + c) := by simp [ha_eq, hb_eq, hc_eq]
  zero_add := by
    intro a
    rcases Real.eq_lim a with ⟨a_seq, ha, ha_eq⟩
    calc
      (0 : Real) + a = (0 : Real) + LIM a_seq := by rw [ha_eq]
      _ = LIM (fun _ : ℕ ↦ 0) + LIM a_seq :=
        congrArg (· + LIM a_seq) (Real.ratCast_def (0 : ℚ))
      _ = LIM ((fun _ : ℕ ↦ 0) + a_seq) := Real.LIM_add (Sequence.IsCauchy.const 0) ha
      _ = LIM a_seq := by
        congr; ext n; simp
      _ = a := by rw [← ha_eq]
  add_zero := by
    intro a
    rcases Real.eq_lim a with ⟨a_seq, ha, ha_eq⟩
    calc
      a + (0 : Real) = LIM a_seq + (0 : Real) := by rw [ha_eq]
      _ = LIM a_seq + LIM (fun _ : ℕ ↦ 0) :=
        congrArg (LIM a_seq + ·) (Real.ratCast_def (0 : ℚ))
      _ = LIM (a_seq + (fun _ : ℕ ↦ 0)) := Real.LIM_add ha (Sequence.IsCauchy.const 0)
      _ = LIM a_seq := by
        congr; ext n; simp
      _ = a := by rw [← ha_eq]
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel := by
    intro a
    rcases Real.eq_lim a with ⟨a_seq, ha, ha_eq⟩
    calc
      (-a) + a = (-LIM a_seq) + LIM a_seq := by simp [ha_eq]
      _ = LIM (-a_seq) + LIM a_seq := by rw [Real.neg_LIM a_seq ha]
      _ = LIM ((-a_seq) + a_seq) := Real.LIM_add (Sequence.IsCauchy.neg a_seq ha) ha
      _ = LIM (fun _ : ℕ ↦ 0) := by
        congr; ext n; simp
      _ = (0 : Real) := (Real.ratCast_def 0).symm

theorem Real.sub_eq_add_neg (x y:Real) : x - y = x + (-y) := rfl

theorem Sequence.IsCauchy.sub {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
    ((a-b:ℕ → ℚ):Sequence).IsCauchy := by
  have hneg : ((-b : ℕ → ℚ) : Sequence).IsCauchy := Sequence.IsCauchy.neg b hb
  simpa [sub_eq_add_neg] using Sequence.IsCauchy.add ha hneg

/-- {name}`LIM` distributes over subtraction -/
theorem Real.LIM_sub {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
  LIM a - LIM b = LIM (a - b) := by
  calc
    LIM a - LIM b = LIM a + (-LIM b) := by rw [Real.sub_eq_add_neg]
    _ = LIM a + LIM (-b) := by rw [Real.neg_LIM b hb]
    _ = LIM (a + (-b)) := Real.LIM_add ha (Sequence.IsCauchy.neg b hb)
    _ = LIM (a - b) := by
      congr; ext n; simp [Rat.sub_eq_add_neg]

/-- {name (full := RatCast.ratCast)}`ratCast` distributes over subtraction -/
theorem Real.ratCast_sub (a b:ℚ) : (a:Real) - (b:Real) = (a-b:ℚ) := by
  calc
    (a:Real) - (b:Real) = (a:Real) + (-(b:Real)) := by rw [Real.sub_eq_add_neg]
    _ = (a:Real) + (-b : Real) := by simp
    _ = (a + (-b) : ℚ) := by
      simpa [Real.neg_ratCast] using Real.ratCast_add a (-b)
    _ = (a - b : ℚ) := by rw [Rat.sub_eq_add_neg]

/-- Proposition 5.3.11 (laws of algebra) -/
noncomputable instance Real.instAddCommGroup : AddCommGroup Real where
  add_comm := by
    intro a b
    rcases Real.eq_lim a with ⟨a_seq, ha, ha_eq⟩
    rcases Real.eq_lim b with ⟨b_seq, hb, hb_eq⟩
    calc
      a + b = LIM a_seq + LIM b_seq := by simp [ha_eq, hb_eq]
      _ = LIM (a_seq + b_seq) := Real.LIM_add ha hb
      _ = LIM (b_seq + a_seq) := by simp [add_comm]
      _ = LIM b_seq + LIM a_seq := (Real.LIM_add hb ha).symm
      _ = b + a := by simp [ha_eq, hb_eq]

/-- Proposition 5.3.11 (laws of algebra) -/
noncomputable instance Real.instCommMonoid : CommMonoid Real where
  mul_comm := by
    intro a b
    rcases Real.eq_lim a with ⟨a_seq, ha, ha_eq⟩
    rcases Real.eq_lim b with ⟨b_seq, hb, hb_eq⟩
    calc
      a * b = LIM a_seq * LIM b_seq := by simp [ha_eq, hb_eq]
      _ = LIM (a_seq * b_seq) := Real.LIM_mul ha hb
      _ = LIM (b_seq * a_seq) := by simp [mul_comm]
      _ = LIM b_seq * LIM a_seq := (Real.LIM_mul hb ha).symm
      _ = b * a := by simp [ha_eq, hb_eq]
  mul_assoc := by
    intro a b c
    rcases Real.eq_lim a with ⟨a_seq, ha, ha_eq⟩
    rcases Real.eq_lim b with ⟨b_seq, hb, hb_eq⟩
    rcases Real.eq_lim c with ⟨c_seq, hc, hc_eq⟩
    calc
      (a * b) * c = (LIM a_seq * LIM b_seq) * LIM c_seq := by simp [ha_eq, hb_eq, hc_eq]
      _ = LIM (a_seq * b_seq) * LIM c_seq := by rw [Real.LIM_mul ha hb]
      _ = LIM ((a_seq * b_seq) * c_seq) := Real.LIM_mul (Sequence.IsCauchy.mul ha hb) hc
      _ = LIM (a_seq * (b_seq * c_seq)) := by simp [mul_assoc]
      _ = LIM a_seq * LIM (b_seq * c_seq) := by rw [Real.LIM_mul ha (Sequence.IsCauchy.mul hb hc)]
      _ = LIM a_seq * (LIM b_seq * LIM c_seq) := by rw [Real.LIM_mul hb hc]
      _ = a * (b * c) := by simp [ha_eq, hb_eq, hc_eq]
  one_mul := by
    intro a
    rcases Real.eq_lim a with ⟨a_seq, ha, ha_eq⟩
    calc
      (1 : Real) * a = (1 : Real) * LIM a_seq := by rw [ha_eq]
      _ = LIM (fun _ : ℕ ↦ 1) * LIM a_seq :=
        congrArg (· * LIM a_seq) (Real.ratCast_def 1)
      _ = LIM ((fun _ : ℕ ↦ 1) * a_seq) := Real.LIM_mul (Sequence.IsCauchy.const 1) ha
      _ = LIM a_seq := by
        congr; ext n; simp
      _ = a := ha_eq.symm
  mul_one := by
    intro a
    rcases Real.eq_lim a with ⟨a_seq, ha, ha_eq⟩
    calc
      a * (1 : Real) = LIM a_seq * (1 : Real) := by rw [ha_eq]
      _ = LIM a_seq * LIM (fun _ : ℕ ↦ 1) :=
        congrArg (LIM a_seq * ·) (Real.ratCast_def 1)
      _ = LIM (a_seq * (fun _ : ℕ ↦ 1)) := Real.LIM_mul ha (Sequence.IsCauchy.const 1)
      _ = LIM a_seq := by
        congr; ext n; simp
      _ = a := ha_eq.symm

/-- Proposition 5.3.11 (laws of algebra) -/
noncomputable instance Real.instCommRing : CommRing Real where
  left_distrib := by
    intro a b c
    rcases Real.eq_lim a with ⟨a_seq, ha, ha_eq⟩
    rcases Real.eq_lim b with ⟨b_seq, hb, hb_eq⟩
    rcases Real.eq_lim c with ⟨c_seq, hc, hc_eq⟩
    calc
      a * (b + c) = LIM a_seq * (LIM b_seq + LIM c_seq) := by simp [ha_eq, hb_eq, hc_eq]
      _ = LIM a_seq * LIM (b_seq + c_seq) := by rw [Real.LIM_add hb hc]
      _ = LIM (a_seq * (b_seq + c_seq)) := Real.LIM_mul ha (Sequence.IsCauchy.add hb hc)
      _ = LIM (a_seq * b_seq + a_seq * c_seq) := by simp [left_distrib]
      _ = LIM (a_seq * b_seq) + LIM (a_seq * c_seq) :=
        (Real.LIM_add (Sequence.IsCauchy.mul ha hb) (Sequence.IsCauchy.mul ha hc)).symm
      _ = (LIM a_seq * LIM b_seq) + (LIM a_seq * LIM c_seq) := by
        simp [Real.LIM_mul ha hb, Real.LIM_mul ha hc]
      _ = a * b + a * c := by simp [ha_eq, hb_eq, hc_eq]
  right_distrib := by
    intro a b c
    rcases Real.eq_lim a with ⟨a_seq, ha, ha_eq⟩
    rcases Real.eq_lim b with ⟨b_seq, hb, hb_eq⟩
    rcases Real.eq_lim c with ⟨c_seq, hc, hc_eq⟩
    calc
      (a + b) * c = (LIM a_seq + LIM b_seq) * LIM c_seq := by simp [ha_eq, hb_eq, hc_eq]
      _ = LIM (a_seq + b_seq) * LIM c_seq := by rw [Real.LIM_add ha hb]
      _ = LIM ((a_seq + b_seq) * c_seq) := Real.LIM_mul (Sequence.IsCauchy.add ha hb) hc
      _ = LIM (a_seq * c_seq + b_seq * c_seq) := by simp [right_distrib]
      _ = LIM (a_seq * c_seq) + LIM (b_seq * c_seq) :=
        (Real.LIM_add (Sequence.IsCauchy.mul ha hc) (Sequence.IsCauchy.mul hb hc)).symm
      _ = (LIM a_seq * LIM c_seq) + (LIM b_seq * LIM c_seq) := by
        simp [Real.LIM_mul ha hc, Real.LIM_mul hb hc]
      _ = a * c + b * c := by simp [ha_eq, hb_eq, hc_eq]
  zero_mul := by
    intro a
    rcases Real.eq_lim a with ⟨a_seq, ha, ha_eq⟩
    calc
      (0 : Real) * a = (0 : Real) * LIM a_seq := by rw [ha_eq]
      _ = LIM (fun _ : ℕ ↦ 0) * LIM a_seq :=
        congrArg (· * LIM a_seq) (Real.ratCast_def 0)
      _ = LIM ((fun _ : ℕ ↦ 0) * a_seq) := Real.LIM_mul (Sequence.IsCauchy.const 0) ha
      _ = LIM (fun _ : ℕ ↦ 0) := by
        congr; ext n; simp
      _ = (0 : Real) := (Real.ratCast_def 0).symm
  mul_zero := by
    intro a
    rcases Real.eq_lim a with ⟨a_seq, ha, ha_eq⟩
    calc
      a * (0 : Real) = LIM a_seq * (0 : Real) := by rw [ha_eq]
      _ = LIM a_seq * LIM (fun _ : ℕ ↦ 0) :=
        congrArg (LIM a_seq * ·) (Real.ratCast_def 0)
      _ = LIM (a_seq * (fun _ : ℕ ↦ 0)) := Real.LIM_mul ha (Sequence.IsCauchy.const 0)
      _ = LIM (fun _ : ℕ ↦ 0) := by
        congr; ext n; simp
      _ = (0 : Real) := (Real.ratCast_def 0).symm
  natCast_succ := by
    intro n
    calc
      ((n.succ : ℕ) : Real) = ((n.succ : ℚ) : Real) := rfl
      _ = ((n : ℚ) + 1 : ℚ) := by norm_num
      _ = (n : Real) + 1 := (Real.ratCast_add n 1).symm
  intCast_negSucc := by
    intro n
    calc
      ((-(n.succ : ℕ) : ℤ) : Real) = (((-(n.succ : ℕ) : ℤ) : ℚ) : Real) := rfl
      _ = ((-(n.succ : ℕ) : ℚ) : Real) :=
        congrArg (fun x : ℚ => (x : Real)) (by simp : ((-(n.succ : ℕ) : ℤ) : ℚ) = (-(n.succ : ℕ) : ℚ))
      _ = -(((n.succ : ℕ) : ℚ) : Real) := by rw [← Real.neg_ratCast]
      _ = -((n.succ : ℕ) : Real) := rfl

abbrev Real.ratCast_hom : ℚ →+* Real where
  toFun := RatCast.ratCast
  map_zero' := rfl
  map_one' := rfl
  map_add' := by
    intro x y; exact (Real.ratCast_add x y).symm
  map_mul' := by
    intro x y; exact (Real.ratCast_mul x y).symm

/--
  Definition 5.3.12 (sequences bounded away from zero). Sequences are indexed to start from zero
  as this is more convenient for Mathlib purposes.
-/
abbrev BoundedAwayZero (a:ℕ → ℚ) : Prop :=
  ∃ (c:ℚ), c > 0 ∧ ∀ n, |a n| ≥ c

theorem bounded_away_zero_def (a:ℕ → ℚ) : BoundedAwayZero a ↔
  ∃ (c:ℚ), c > 0 ∧ ∀ n, |a n| ≥ c := by rfl

/-- Examples 5.3.13 -/
example : BoundedAwayZero (fun n ↦ (-1)^n) := by use 1; simp

/-- Examples 5.3.13 -/
private lemma pow_ge_add_one (n : ℕ) : (10 : ℚ) ^ (n+1 : ℕ) ≥ (n : ℚ) + 1 := by
  have h : (10 : ℕ) ^ (n+1) ≥ n+1 := by
    induction' n with k ih
    · omega
    · calc
        (10 : ℕ) ^ (k.succ+1) = (10 : ℕ) ^ (k+1) * 10 := by rw [pow_succ, pow_succ]
        _ ≥ (k+1) * 10 := Nat.mul_le_mul_right 10 ih
        _ = 10*(k+1) := by ring
        _ ≥ k.succ.succ := by omega
  exact_mod_cast h

example : ¬ BoundedAwayZero (fun n ↦ 10^(-(n:ℤ)-1)) := by
  rw [bounded_away_zero_def]
  push_neg
  intro c hc
  have ⟨n, hn⟩ := exists_nat_one_div_lt hc
  use n
  have hz : 10 ^ (-(n : ℤ) - 1) = 1 / ((10 : ℚ) ^ (n+1 : ℕ)) := by
    calc
      10 ^ (-(n : ℤ) - 1) = (10 : ℚ) ^ (-(n+1 : ℤ)) := by ring_nf
      _ = ((10 : ℚ) ^ (n+1 : ℤ))⁻¹ := by rw [zpow_neg]
      _ = ((10 : ℚ) ^ (n+1 : ℕ))⁻¹ := by
        simpa using congrArg (·⁻¹) (zpow_natCast (10 : ℚ) (n+1))
      _ = 1 / ((10 : ℚ) ^ (n+1 : ℕ)) := by norm_num
  have hpos : 0 < 1 / ((10 : ℚ) ^ (n+1 : ℕ)) := by
    refine div_pos (by norm_num) (pow_pos (by norm_num) _)
  have h_abs : |10 ^ (-(n : ℤ) - 1)| = 1 / ((10 : ℚ) ^ (n+1 : ℕ)) := by
    rw [hz, abs_of_pos hpos]
  rw [h_abs]
  have hdiv : 1 / ((10 : ℚ) ^ (n+1 : ℕ)) ≤ 1 / ((n : ℚ) + 1) :=
    (one_div_le_one_div (pow_pos (by norm_num) _) (by positivity)).mpr (pow_ge_add_one n)
  linarith

/-- Examples 5.3.13 -/
example : ¬ BoundedAwayZero (fun n ↦ 1 - 10^(-(n:ℤ))) := by
  rw [bounded_away_zero_def]
  intro h
  rcases h with ⟨c, hc_and_h⟩
  have hc : c > 0 := hc_and_h.1
  have h : ∀ n, |(fun n : ℕ => 1 - 10 ^ (-(n : ℤ))) n| ≥ c := hc_and_h.2
  have h0' : (0 : ℚ) ≥ c := by
    have h0abs : |(fun n : ℕ => 1 - 10 ^ (-(n : ℤ))) 0| = (0 : ℚ) := by
      have h0eq : (fun n : ℕ => 1 - 10 ^ (-(n : ℤ))) 0 = (0 : ℚ) := by norm_num
      calc
        |(fun n : ℕ => 1 - 10 ^ (-(n : ℤ))) 0| = |(0 : ℚ)| := by rw [h0eq]
        _ = (0 : ℚ) := abs_zero
    simpa [h0abs] using h 0
  linarith

/-- Examples 5.3.13 -/
example : BoundedAwayZero (fun n ↦ 10^(n+1)) := by
  use 1, by norm_num
  intro n; dsimp
  rw [abs_of_nonneg (by positivity), show (1:ℚ) = 10^0 by norm_num]
  gcongr <;> grind

/-- Examples 5.3.13 -/
example : ¬ ((fun (n:ℕ) ↦ (10:ℚ)^(n+1)):Sequence).IsBounded := by
  rw [Sequence.isBounded_def]
  intro h
  rcases h with ⟨M, hM_nonneg, hM⟩
  have ⟨K, hK⟩ := exists_nat_gt M
  have hpos : 0 ≤ (10 : ℚ) ^ (K+1 : ℕ) := by positivity
  have habs : |(10 : ℚ) ^ (K+1 : ℕ)| = (10 : ℚ) ^ (K+1 : ℕ) := abs_of_nonneg hpos
  have hpow_ge : (10 : ℚ) ^ (K+1 : ℕ) ≥ (K : ℚ) + 1 := pow_ge_add_one K
  have h_gt : (10 : ℚ) ^ (K+1 : ℕ) > M := by nlinarith
  have h_val : |((fun (n:ℕ) ↦ (10:ℚ)^(n+1)):Sequence) (K : ℤ)| = (10 : ℚ) ^ (K+1 : ℕ) := by
    simp [Sequence.eval_coe_at_int]
  have h_bound := hM (K : ℤ)
  rw [h_val] at h_bound
  linarith

private lemma aux_how' {b : ℕ → ℚ} {ε : ℚ} {N n₀ : ℕ} (hn₀ : n₀ ≥ N) (hx : |b n₀| > ε)
    (hb'_abs : ∀ j ≥ N, ∀ k ≥ N, |b j - b k| ≤ ε/2) : ∀ j ≥ N, |b j| ≥ ε/2 := by
  intro j hj
  have h_small : |b n₀ - b j| ≤ ε/2 := hb'_abs n₀ hn₀ j hj
  have h_tri : |b n₀| ≤ |b n₀ - b j| + |b j| := by
    calc
      |b n₀| = |(b n₀ - b j) + b j| := by rw [sub_add_cancel (b n₀) (b j)]
      _ ≤ |b n₀ - b j| + |b j| := abs_add_le _ _
  have h_small_add : |b j| + |b n₀ - b j| ≤ |b j| + ε/2 := add_le_add_right h_small (|b j|)
  have h_temp : |b n₀ - b j| + |b j| ≤ ε/2 + |b j| := by
    calc
      |b n₀ - b j| + |b j| = |b j| + |b n₀ - b j| := add_comm _ _
      _ ≤ |b j| + ε/2 := h_small_add
      _ = ε/2 + |b j| := add_comm _ _
  have h_ineq : |b n₀| ≤ ε/2 + |b j| := le_trans h_tri h_temp
  have h_sum : ε < ε/2 + |b j| := lt_of_lt_of_le hx h_ineq
  have : ε/2 < |b j| := by
    have h_sum' : ε < |b j| + ε/2 := by rw [add_comm]; exact h_sum
    have h_sub : ε - ε/2 < |b j| := sub_lt_iff_lt_add.mpr h_sum'
    have h_half : ε - ε/2 = ε/2 := by ring
    rw [h_half] at h_sub
    exact h_sub
  exact le_of_lt this

/-- Lemma 5.3.14 -/
theorem Real.boundedAwayZero_of_nonzero {x:Real} (hx: x ≠ 0) :
    ∃ a:ℕ → ℚ, (a:Sequence).IsCauchy ∧ BoundedAwayZero a ∧ x = LIM a := by
  -- This proof is written to follow the structure of the original text.
  obtain ⟨ b, hb, rfl ⟩ := eq_lim x
  simp only [←LIM.zero, ne_eq] at hx
  rw [LIM_eq_LIM hb (by convert Sequence.IsCauchy.const 0), Sequence.equiv_iff] at hx
  simp at hx
  choose ε hε hx using hx
  choose N hb' using (Sequence.IsCauchy.coe _).mp hb _ (half_pos hε)
  choose n₀ hn₀ hx using hx N
  have hb'_abs : ∀ j ≥ N, ∀ k ≥ N, |b j - b k| ≤ ε/2 := by
    intro j hj k hk
    have h := hb' j hj k hk
    rw [Section_4_3.dist, Section_4_3.abs_eq_abs] at h
    exact h
  have how : ∀ j ≥ N, |b j| ≥ ε/2 :=
    aux_how' hn₀ hx hb'_abs
  set a : ℕ → ℚ := fun n ↦ if n < n₀ then ε/2 else b n
  have not_hard : Sequence.Equiv a b := by
    rw [Sequence.equiv_iff]
    intro ε' hε'
    refine ⟨n₀, ?_⟩
    intro n hn
    have hn' : ¬ n < n₀ := not_lt.mpr hn
    simp [a, hn', sub_self, abs_zero]
    exact hε'.le
  have ha := (Sequence.isCauchy_of_equiv not_hard).mpr hb
  refine ⟨ a, ha, ?_, by rw [(LIM_eq_LIM ha hb).mpr not_hard] ⟩
  rw [bounded_away_zero_def]
  use ε/2, half_pos hε
  intro n; by_cases hn: n < n₀ <;> simp [a, hn, le_abs_self _]
  grind

/--
  This result was not explicitly stated in the text, but is needed in the theory. It's a good
  exercise, so I'm setting it as such.
-/
theorem Real.lim_of_boundedAwayZero {a:ℕ → ℚ} (ha: BoundedAwayZero a)
  (ha_cauchy: (a:Sequence).IsCauchy) :
    LIM a ≠ 0 := by
  by_contra! h
  rcases ha with ⟨c, hc, ha_bound⟩
  rw [← Real.LIM.zero] at h
  rw [Real.LIM_eq_LIM ha_cauchy (Sequence.IsCauchy.const (0 : ℚ)), Sequence.equiv_iff] at h
  simp at h
  have hc2 : c / 2 > 0 := half_pos hc
  rcases h (c / 2) hc2 with ⟨N, hN⟩
  have hN_bound : |a N| ≤ c / 2 := hN N (le_refl N)
  have ha_bound_N : |a N| ≥ c := ha_bound N
  nlinarith

theorem Real.nonzero_of_boundedAwayZero {a:ℕ → ℚ} (ha: BoundedAwayZero a) (n: ℕ) : a n ≠ 0 := by
   choose c hc ha using ha; specialize ha n; contrapose! ha; simp [ha, hc]

/-- Lemma 5.3.15 -/
theorem Real.inv_isCauchy_of_boundedAwayZero {a:ℕ → ℚ} (ha: BoundedAwayZero a)
  (ha_cauchy: (a:Sequence).IsCauchy) :
    ((a⁻¹:ℕ → ℚ):Sequence).IsCauchy := by
  -- This proof is written to follow the structure of the original text.
  have ha' (n:ℕ) : a n ≠ 0 := nonzero_of_boundedAwayZero ha n
  rw [bounded_away_zero_def] at ha; choose c hc ha using ha
  simp_rw [Sequence.IsCauchy.coe, Section_4_3.dist_eq] at ha_cauchy ⊢
  intro ε hε; specialize ha_cauchy (c^2 * ε) (by positivity)
  choose N ha_cauchy using ha_cauchy; use N;
  peel 4 ha_cauchy with n hn m hm ha_cauchy
  calc
    Section_4_3.abs ((a⁻¹ : ℕ → ℚ) n - (a⁻¹ : ℕ → ℚ) m) = Section_4_3.abs ((a m - a n) / (a n * a m)) := by
      calc
        Section_4_3.abs ((a⁻¹ : ℕ → ℚ) n - (a⁻¹ : ℕ → ℚ) m)
            = Section_4_3.abs ((a n)⁻¹ - (a m)⁻¹) := by simp
        _ = Section_4_3.abs ((a m - a n) / (a n * a m)) := by
          rw [inv_sub_inv (ha' n) (ha' m)]
    _ = |(a m - a n) / (a n * a m)| := by rw [Section_4_3.abs_eq_abs]
    _ ≤ |a m - a n| / c^2 := by rw [abs_div, abs_mul, sq]; gcongr <;> solve_by_elim
    _ = |a n - a m| / c^2 := by rw [abs_sub_comm]
    _ ≤ (c^2 * ε) / c^2 := by
      gcongr
      simpa [Section_4_3.abs_eq_abs] using ha_cauchy
    _ = ε := by field_simp [hc]

/-- Lemma 5.3.17 (Reciprocation is well-defined) -/
theorem Real.inv_of_equiv {a b:ℕ → ℚ} (ha: BoundedAwayZero a)
  (ha_cauchy: (a:Sequence).IsCauchy) (hb: BoundedAwayZero b)
  (hb_cauchy: (b:Sequence).IsCauchy) (hlim: LIM a = LIM b) :
    LIM a⁻¹ = LIM b⁻¹ := by
  -- This proof is written to follow the structure of the original text.
  set P := LIM a⁻¹ * LIM a * LIM b⁻¹
  have hainv_cauchy := Real.inv_isCauchy_of_boundedAwayZero ha ha_cauchy
  have hbinv_cauchy := Real.inv_isCauchy_of_boundedAwayZero hb hb_cauchy
  have haainv_cauchy := hainv_cauchy.mul ha_cauchy
  have habinv_cauchy := hainv_cauchy.mul hb_cauchy
  have claim1 : P = LIM b⁻¹ := by
    simp only [P, LIM_mul hainv_cauchy ha_cauchy, LIM_mul haainv_cauchy hbinv_cauchy]
    rcongr n; simp [nonzero_of_boundedAwayZero ha n]
  have claim2 : P = LIM a⁻¹ := by
    simp only [P, hlim, LIM_mul hainv_cauchy hb_cauchy, LIM_mul habinv_cauchy hbinv_cauchy]
    rcongr n; simp [nonzero_of_boundedAwayZero hb n]
  grind

open Classical in
/--
  Definition 5.3.16 (Reciprocation of real numbers).  Requires classical logic because we need to
  assign a "junk" value to the inverse of 0.
-/
noncomputable instance Real.instInv : Inv Real where
  inv x := if h: x ≠ 0 then LIM (boundedAwayZero_of_nonzero h).choose⁻¹ else 0

theorem Real.inv_def {a:ℕ → ℚ} (h: BoundedAwayZero a) (hc: (a:Sequence).IsCauchy) :
    (LIM a)⁻¹ = LIM a⁻¹ := by
  observe hx : LIM a ≠ 0
  set x := LIM a
  have ⟨ h1, h2, h3 ⟩ := (boundedAwayZero_of_nonzero hx).choose_spec
  simp [Inv.inv, hx]
  exact inv_of_equiv h2 h1 h hc h3.symm

@[simp]
theorem Real.inv_zero : (0:Real)⁻¹ = 0 := by simp [Inv.inv]

theorem Real.self_mul_inv {x:Real} (hx: x ≠ 0) : x * x⁻¹ = 1 := by
  rcases Real.boundedAwayZero_of_nonzero hx with ⟨a, ha_cauchy, ha_bounded, ha_eq⟩
  rw [ha_eq]
  rw [Real.inv_def ha_bounded ha_cauchy]
  have h_inv_cauchy : ((a⁻¹ : ℕ → ℚ) : Sequence).IsCauchy :=
    Real.inv_isCauchy_of_boundedAwayZero ha_bounded ha_cauchy
  rw [Real.LIM_mul ha_cauchy h_inv_cauchy]
  have h : a * (a⁻¹ : ℕ → ℚ) = fun _ : ℕ ↦ (1 : ℚ) := by
    ext n
    have hn : a n ≠ 0 := Real.nonzero_of_boundedAwayZero ha_bounded n
    have hmul : a n * (a n)⁻¹ = 1 := by
      field_simp [hn]
    simp [hmul]
  rw [h]
  simpa using (Real.ratCast_def (1 : ℚ)).symm

theorem Real.inv_mul_self {x:Real} (hx: x ≠ 0) : x⁻¹ * x = 1 := by
  rw [mul_comm, Real.self_mul_inv hx]

lemma BoundedAwayZero.const {q : ℚ} (hq : q ≠ 0) : BoundedAwayZero fun _ ↦ q := by
  use |q|; simp [hq]

theorem Real.inv_ratCast (q:ℚ) : (q:Real)⁻¹ = (q⁻¹:ℚ) := by
  by_cases h : q = 0
  . rw [h, ← show (0:Real) = (0:ℚ) by norm_cast]; norm_num; norm_cast
  simp_rw [ratCast_def, inv_def (BoundedAwayZero.const h) (by apply Sequence.IsCauchy.const)]; congr

/-- Default definition of division. -/
noncomputable instance Real.instDivInvMonoid : DivInvMonoid Real where

theorem Real.div_eq (x y:Real) : x/y = x * y⁻¹ := rfl

private lemma ratCast_def_aux (q : ℚ) : (q : Real) = (q.num : Real) / (q.den : Real) := by
  calc
    (q : Real) = ((q.num / q.den : ℚ) : Real) := by rw [Rat.num_div_den q]
    _ = (q.num : Real) / (q.den : Real) := by
      calc
        ((q.num / q.den : ℚ) : Real) = ((q.num * ((q.den : ℚ)⁻¹) : ℚ) : Real) := by rw [div_eq_mul_inv]
        _ = ((q.num : ℚ) : Real) * (((q.den : ℚ)⁻¹ : ℚ) : Real) :=
          (Real.ratCast_mul (q.num : ℚ) ((q.den : ℚ)⁻¹)).symm
        _ = ((q.num : ℚ) : Real) * (((q.den : ℚ) : Real)⁻¹) := by
          rw [(Real.inv_ratCast (q.den : ℚ)).symm]
        _ = (q.num : Real) * (q.den : Real)⁻¹ := by
          calc
            ((q.num : ℚ) : Real) * (((q.den : ℚ) : Real)⁻¹)
                = (q.num : Real) * (((q.den : ℚ) : Real)⁻¹) := by
                  have : ((q.num : ℚ) : Real) = (q.num : Real) := by
                    dsimp; rfl
                  rw [this]
            _ = (q.num : Real) * (q.den : Real)⁻¹ := by
              calc
                (q.num : Real) * (((q.den : ℚ) : Real)⁻¹)
                    = (q.num : Real) * (q.den : Real)⁻¹ := by
                  have : ((q.den : ℚ) : Real) = (q.den : Real) := by
                    dsimp; rfl
                  rw [this]
        _ = (q.num : Real) / (q.den : Real) := rfl

noncomputable instance Real.instField : Field Real where
  exists_pair_ne := by
    refine ⟨0, 1, ?_⟩
    intro h
    have h' := (Real.ratCast_inj (0 : ℚ) (1 : ℚ)).mp h
    norm_num at h'
  mul_inv_cancel := fun a hx => Real.self_mul_inv hx
  inv_zero := Real.inv_zero
  ratCast_def := ratCast_def_aux
  nnratCast_def := by
    intro q
    have h := ratCast_def_aux (q : ℚ)
    -- h : ((q : ℚ) : Real) = ((q : ℚ).num : Real) / ((q : ℚ).den : Real)
    -- Goal: (q : Real) = (q.num : Real) / (q.den : Real)
    -- The problem is that (q : Real) and ((q : ℚ) : Real) are syntactically different
    -- But NNRat.cast is defined as (q : ℚ), so they are equal by definition
    -- Let`s use `show` to change the goal
    show ((q : ℚ) : Real) = (q.num : Real) / (q.den : Real)
    -- Now the goal matches h, except for num/den
    calc
      ((q : ℚ) : Real) = ((q : ℚ).num : Real) / ((q : ℚ).den : Real) := h
      _ = (q.num : Real) / (q.den : Real) := by
        have hnum : ((q : ℚ).num : Real) = (q.num : Real) := by
          norm_cast
        have hden : ((q : ℚ).den : Real) = (q.den : Real) := rfl
        rw [hnum, hden]
  qsmul := fun q x => (q : Real) * x
  qsmul_def := fun q a => rfl
  nnqsmul := fun q x => ((q : ℚ) : Real) * x
  nnqsmul_def := fun q a => rfl

theorem Real.mul_right_cancel₀ {x y z:Real} (hz: z ≠ 0) (h: x * z = y * z) : x = y := by
  have h_inv : z * z⁻¹ = 1 := Real.self_mul_inv hz
  have h_one_mul (a : Real) : a * 1 = a := Real.instCommMonoid.mul_one a
  have h1 : x = x * (z * z⁻¹) := by
    rw [h_inv, h_one_mul x]
  have h2 : x * (z * z⁻¹) = y * (z * z⁻¹) := by
    calc
      x * (z * z⁻¹) = (x * z) * z⁻¹ := by rw [mul_assoc]
      _ = (y * z) * z⁻¹ := by rw [h]
      _ = y * (z * z⁻¹) := by rw [mul_assoc]
  have h3 : y * (z * z⁻¹) = y := by
    rw [h_inv, h_one_mul y]
  exact (h1.trans h2).trans h3

theorem Real.mul_right_nocancel : ¬ ∀ (x y z:Real), (hz: z = 0) → (x * z = y * z) → x = y := by
  intro h
  have h01 : (0 : Real) = (1 : Real) := h 0 1 0 rfl (by
    calc
      (0 : Real) * (0 : Real) = (0 : Real) := by simp
      _ = ((1 : ℚ) : Real) * (0 : Real) := by
        simp)
  have : (0 : Real) ≠ (1 : Real) := by
    intro h0
    have := (Real.ratCast_inj (0 : ℚ) (1 : ℚ)).mp h0
    norm_num at this
  exact this h01

/-- Exercise 5.3.4 -/
theorem Real.IsBounded.equiv {a b:ℕ → ℚ} (ha: (a:Sequence).IsBounded) (hab: Sequence.Equiv a b) :
    (b:Sequence).IsBounded := by
  have h1 : (1 : ℚ).EventuallyClose (a:Sequence) (b:Sequence) := hab 1 (by norm_num)
  exact ((Sequence.isBounded_of_eventuallyClose h1).mp ha)

/--
  Same as {name}`Sequence.IsCauchy.harmonic` but reindexing the sequence as a₀ = 1, a₁ = 1/2, ...
  This form is more convenient for the upcoming proof of Theorem 5.5.9.
-/
theorem Sequence.IsCauchy.harmonic' : ((fun n ↦ 1/((n:ℚ)+1): ℕ → ℚ):Sequence).IsCauchy := by
  rw [coe]; intro ε hε; choose N h1 h2 using (mk _).mp harmonic ε hε
  use N.toNat; intro j _ k _; specialize h2 (j+1) _ (k+1) _ <;> try omega
  simp_all

/-- Exercise 5.3.5 -/
theorem Real.LIM.harmonic : LIM (fun n ↦ 1/((n:ℚ)+1)) = 0 := by
  have ha_cauchy : ((fun n : ℕ ↦ 1/((n:ℚ)+1)) : Sequence).IsCauchy := Sequence.IsCauchy.harmonic'
  have hzero_cauchy : ((fun _ : ℕ ↦ (0 : ℚ)) : Sequence).IsCauchy := Sequence.IsCauchy.const 0
  rw [← Real.LIM.zero, Real.LIM_eq_LIM ha_cauchy hzero_cauchy, Sequence.equiv_iff]
  intro ε hε
  have ⟨N, hN⟩ := exists_nat_one_div_lt hε
  use N
  intro n hn
  have hpos : 0 < (n:ℚ) + 1 := by positivity
  calc
    |1 / ((n : ℚ) + 1) - 0| = |1 / ((n : ℚ) + 1)| := by simp
    _ = 1 / ((n : ℚ) + 1) := abs_of_pos (div_pos (by norm_num) hpos)
    _ ≤ 1 / ((N : ℚ) + 1) := by
      refine (one_div_le_one_div ?_ ?_).mpr ?_
      · positivity
      · positivity
      · have hNn : (N : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
        linarith
    _ ≤ ε := by
      exact hN.le

end Chapter5
