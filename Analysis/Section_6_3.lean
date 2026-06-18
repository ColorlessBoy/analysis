import Mathlib.Tactic
import Analysis.Section_6_1
import Analysis.Section_6_2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Analysis I, Section 6.3: Suprema and infima of sequences

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Suprema and infima of sequences.

-/

namespace Chapter6

/-- Definition 6.3.1 -/
noncomputable abbrev Sequence.sup (a:Sequence) : EReal := sSup { x | ∃ n ≥ a.m, x = a n }

/-- Definition 6.3.1 -/
noncomputable abbrev Sequence.inf (a:Sequence) : EReal := sInf { x | ∃ n ≥ a.m, x = a n }

/-- Example 6.3.3 -/
example : ((fun (n:ℕ) ↦ (-1:ℝ)^(n+1)):Sequence).sup = 1 := by
  unfold Sequence.sup Sequence.ofNatFun; simp only [ge_iff_le]
  apply le_antisymm
  · apply sSup_le; rintro x ⟨n, hn, rfl⟩; simp only [hn, ↓reduceIte]
    change _ ≤ ((1:ℝ) : EReal); rw [EReal.coe_le_coe_iff]
    rcases neg_one_pow_eq_or ℝ (n.toNat + 1) with h | h <;> linarith
  · apply le_sSup; exact ⟨1, by omega, by simp⟩

/-- Example 6.3.3 -/
example : ((fun (n:ℕ) ↦ (-1:ℝ)^(n+1)):Sequence).inf = -1 := by
  unfold Sequence.inf Sequence.ofNatFun; simp only [ge_iff_le]
  apply le_antisymm
  · apply sInf_le; exact ⟨0, by omega, by simp⟩
  · apply le_sInf; rintro x ⟨n, hn, rfl⟩; simp only [hn, ↓reduceIte]
    change ((-1:ℝ) : EReal) ≤ _; rw [EReal.coe_le_coe_iff]
    rcases neg_one_pow_eq_or ℝ (n.toNat + 1) with h | h <;> linarith

/-- Example 6.3.4 / Exercise 6.3.1 -/
example : ((fun (n:ℕ) ↦ 1/((n:ℝ)+1)):Sequence).sup = 1 := by
  unfold Sequence.sup Sequence.ofNatFun; simp only [ge_iff_le]
  apply le_antisymm
  · apply sSup_le; rintro x ⟨n, hn, rfl⟩; simp only [hn, ↓reduceIte]
    change _ ≤ ((1:ℝ) : EReal); rw [EReal.coe_le_coe_iff, div_le_one (by positivity)]
    linarith [n.toNat.cast_nonneg (α := ℝ)]
  · apply le_sSup; exact ⟨0, by omega, by simp⟩

/-- Example 6.3.4 / Exercise 6.3.1 -/
example : ((fun (n:ℕ) ↦ 1/((n:ℝ)+1)):Sequence).inf = 0 := by
  unfold Sequence.inf Sequence.ofNatFun; simp only [ge_iff_le]
  set S := {x : EReal | ∃ n : ℤ, 0 ≤ n ∧ x = ↑(if (0:ℤ) ≤ n then 1 / ((n.toNat:ℝ) + 1) else (0:ℝ))}
  apply le_antisymm
  · by_contra hlt; push_neg at hlt
    have h1 : sInf S ≤ ((1:ℝ) : EReal) := csInf_le (OrderBot.bddBelow _) ⟨(0:ℤ), le_refl _, by simp⟩
    set r := (sInf S).toReal
    have hr_eq : sInf S = (r : EReal) :=
      (EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top 1) h1) (ne_bot_of_gt hlt)).symm
    rw [hr_eq] at hlt; have hr_pos : (0:ℝ) < r := by exact_mod_cast hlt
    obtain ⟨N, hN⟩ := exists_nat_gt (1/r)
    have hle : sInf S ≤ ((1/((N:ℝ)+1):ℝ) : EReal) :=
      csInf_le (OrderBot.bddBelow _) ⟨↑N, by omega, by simp⟩
    rw [hr_eq, EReal.coe_le_coe_iff] at hle
    nlinarith [(div_lt_iff₀ hr_pos).mp hN, (le_div_iff₀ (by positivity : (0:ℝ) < (N:ℝ)+1)).mp hle]
  · apply le_sInf; rintro x ⟨n, hn, rfl⟩; simp only [hn, ↓reduceIte]
    change ((0:ℝ) : EReal) ≤ _; rw [EReal.coe_le_coe_iff]; positivity

/-- Example 6.3.5 -/
example : ((fun (n:ℕ) ↦ (n+1:ℝ)):Sequence).sup = ⊤ := by
  unfold Sequence.sup Sequence.ofNatFun; simp only [ge_iff_le]
  erw [sSup_eq_top]; intro b hb
  induction b using EReal.rec with
  | bot => exact ⟨↑(1:ℝ), ⟨0, by omega, by simp⟩, EReal.bot_lt_coe 1⟩
  | top => exact absurd hb (lt_irrefl _)
  | coe r =>
    obtain ⟨n, hn⟩ := exists_nat_gt r
    refine ⟨↑((n:ℝ) + 1), ⟨↑n, by omega, by simp⟩, ?_⟩
    calc (r:EReal) < ↑(n:ℝ) := by exact_mod_cast hn
    _ ≤ ↑((n:ℝ) + 1) := by exact_mod_cast le_of_lt (lt_add_one (n:ℝ))

/-- Example 6.3.5 -/
example : ((fun (n:ℕ) ↦ (n+1:ℝ)):Sequence).inf = 1 := by
  unfold Sequence.inf Sequence.ofNatFun; simp only [ge_iff_le]
  apply le_antisymm
  · apply sInf_le; exact ⟨0, by omega, by simp⟩
  · apply le_sInf; rintro x ⟨n, hn, rfl⟩; simp only [hn, ↓reduceIte]
    exact_mod_cast Nat.le_add_left 1 n.toNat

abbrev Sequence.BddAboveBy (a:Sequence) (M:ℝ) : Prop := ∀ n ≥ a.m, a n ≤ M

abbrev Sequence.BddAbove (a:Sequence) : Prop := ∃ M, a.BddAboveBy M

abbrev Sequence.BddBelowBy (a:Sequence) (M:ℝ) : Prop := ∀ n ≥ a.m, a n ≥ M

abbrev Sequence.BddBelow (a:Sequence) : Prop := ∃ M, a.BddBelowBy M

theorem Sequence.bounded_iff (a:Sequence) : a.IsBounded ↔ a.BddAbove ∧ a.BddBelow := by
  constructor
  · intro ⟨M, hM_pos, hM⟩
    exact ⟨⟨M, fun n _ => (abs_le.mp (hM n)).2⟩,
           ⟨-M, fun n _ => by linarith [(abs_le.mp (hM n)).1]⟩⟩
  · intro ⟨⟨U, hU⟩, ⟨L, hL⟩⟩
    refine ⟨max (max U (-L)) 0, le_max_right _ _, fun n => ?_⟩
    by_cases hn : n ≥ a.m
    · have h1 := hU n hn
      have h2 := hL n hn
      rw [abs_le]
      constructor
      · nlinarith [le_max_left (max U (-L)) 0, le_max_right U (-L)]
      · nlinarith [le_max_left (max U (-L)) 0, le_max_left U (-L)]
    · push_neg at hn
      rw [a.vanish n hn]
      simp

theorem Sequence.sup_of_bounded {a:Sequence} (h: a.IsBounded) : a.sup.IsFinite := by
  obtain ⟨M, hM_pos, hM⟩ := h
  have hle : a.sup ≤ (M : EReal) := by
    apply sSup_le; rintro x ⟨n, hn, rfl⟩; exact_mod_cast (abs_le.mp (hM n)).2
  have hge : a.sup ≥ ((-M : ℝ) : EReal) := by
    calc ((-M : ℝ) : EReal) ≤ ↑(a a.m) := by exact_mod_cast (abs_le.mp (hM a.m)).1
    _ ≤ a.sup := le_sSup ⟨a.m, le_refl _, rfl⟩
  have hne_top : a.sup ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top M) hle
  have hne_bot : a.sup ≠ ⊥ := by intro hbot; rw [hbot] at hge; simp at hge
  by_contra habs
  rw [← EReal.infinite_iff_not_finite] at habs
  rcases habs with htop | hbot
  · exact hne_top htop
  · exact hne_bot hbot

theorem Sequence.inf_of_bounded {a:Sequence} (h: a.IsBounded) : a.inf.IsFinite := by
  obtain ⟨M, hM_pos, hM⟩ := h
  have hge : a.inf ≥ ((-M : ℝ) : EReal) := by
    apply le_sInf; rintro x ⟨n, hn, rfl⟩; exact_mod_cast (abs_le.mp (hM n)).1
  have hle : a.inf ≤ ((M : ℝ) : EReal) := by
    calc a.inf ≤ ↑(a a.m) := sInf_le ⟨a.m, le_refl _, rfl⟩
    _ ≤ (M : EReal) := by exact_mod_cast (abs_le.mp (hM a.m)).2
  have hne_top : a.inf ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top M) hle
  have hne_bot : a.inf ≠ ⊥ := by intro hbot; rw [hbot] at hge; simp at hge
  by_contra habs
  rw [← EReal.infinite_iff_not_finite] at habs
  rcases habs with htop | hbot
  · exact hne_top htop
  · exact hne_bot hbot

/-- Proposition 6.3.6 (Least upper bound property) / Exercise 6.3.2 -/
theorem Sequence.le_sup {a:Sequence} {n:ℤ} (hn: n ≥ a.m) : a n ≤ a.sup :=
  le_sSup ⟨n, hn, rfl⟩

/-- Proposition 6.3.6 (Least upper bound property) / Exercise 6.3.2 -/
theorem Sequence.sup_le_upper {a:Sequence} {M:EReal} (h: ∀ n ≥ a.m, a n ≤ M) : a.sup ≤ M := by
  apply sSup_le; rintro x ⟨n, hn, rfl⟩; exact h n hn

/-- Proposition 6.3.6 (Least upper bound property) / Exercise 6.3.2 -/
theorem Sequence.exists_between_lt_sup {a:Sequence} {y:EReal} (h: y < a.sup ) :
    ∃ n ≥ a.m, y < a n ∧ a n ≤ a.sup := by
  rw [lt_sSup_iff] at h
  obtain ⟨z, ⟨n, hn, rfl⟩, hyz⟩ := h
  exact ⟨n, hn, hyz, le_sup hn⟩

/-- Remark 6.3.7 -/
theorem Sequence.ge_inf {a:Sequence} {n:ℤ} (hn: n ≥ a.m) : a n ≥ a.inf :=
  sInf_le ⟨n, hn, rfl⟩

/-- Remark 6.3.7 -/
theorem Sequence.inf_ge_lower {a:Sequence} {M:EReal} (h: ∀ n ≥ a.m, a n ≥ M) : a.inf ≥ M := by
  apply le_sInf; rintro x ⟨n, hn, rfl⟩; exact h n hn

/-- Remark 6.3.7 -/
theorem Sequence.exists_between_gt_inf {a:Sequence} {y:EReal} (h: y > a.inf ) :
    ∃ n ≥ a.m, y > a n ∧ a n ≥ a.inf := by
  have h' : a.inf < y := h
  rw [sInf_lt_iff] at h'
  obtain ⟨z, ⟨n, hn, rfl⟩, hyz⟩ := h'
  exact ⟨n, hn, hyz, ge_inf hn⟩

abbrev Sequence.IsMonotone (a:Sequence) : Prop := ∀ n ≥ a.m, a (n+1) ≥ a n

abbrev Sequence.IsAntitone (a:Sequence) : Prop := ∀ n ≥ a.m, a (n+1) ≤ a n

/-- Proposition 6.3.8 / Exercise 6.3.3 -/
theorem Sequence.convergent_of_monotone {a:Sequence} (hbound: a.BddAbove) (hmono: a.IsMonotone) :
    a.Convergent := by
  have hbelow : a.BddBelow := by
    use a a.m; intro n hn
    obtain ⟨k, rfl⟩ : ∃ k : ℤ, n = a.m + k := ⟨n - a.m, by omega⟩
    have hk : k ≥ 0 := by omega
    lift k to ℕ using hk
    induction k with
    | zero => simp
    | succ k ih =>
      have := ih (by omega)
      simp only [Nat.cast_succ] at *
      have h_eq : a.m + (↑k + 1) = a.m + ↑k + 1 := by ring
      rw [h_eq]; linarith [hmono (a.m + ↑k) (by omega)]
  have hbounded : a.IsBounded := a.bounded_iff.mpr ⟨hbound, hbelow⟩
  obtain ⟨S, hS⟩ := Sequence.sup_of_bounded hbounded
  use S; rw [a.tendsTo_iff S]; intro ε hε
  have hlt : (S - ε : EReal) < a.sup := by
    rw [← hS]; exact EReal.coe_lt_coe_iff.mpr (by linarith)
  obtain ⟨N, hN_m, hN_lt, hN_le⟩ := Sequence.exists_between_lt_sup hlt
  have mono_helper : ∀ n ≥ N, a.seq n ≥ a.seq N := by
    intro n hn
    obtain ⟨k, rfl⟩ : ∃ k : ℤ, n = N + k := ⟨n - N, by omega⟩
    have hk : k ≥ 0 := by omega
    lift k to ℕ using hk
    induction k with
    | zero => simp
    | succ k ih =>
      have := ih (by omega)
      simp only [Nat.cast_succ] at *
      have h_eq : N + (↑k + 1) = N + ↑k + 1 := by ring
      rw [h_eq]; linarith [hmono (N + ↑k) (by omega)]
  use N; intro n hn
  have hle_S : a n ≤ S := by
    have : (a n : EReal) ≤ a.sup := Sequence.le_sup (by omega)
    rw [← hS] at this; exact_mod_cast this
  rw [abs_le]
  constructor <;> linarith [mono_helper n hn, (show a N > S - ε by exact_mod_cast hN_lt)]

/-- Proposition 6.3.8 / Exercise 6.3.3 -/
theorem Sequence.lim_of_monotone {a:Sequence} (hbound: a.BddAbove) (hmono: a.IsMonotone) :
    lim a = a.sup := by
  have hbelow : a.BddBelow := by
    use a a.m; intro n hn
    obtain ⟨k, rfl⟩ : ∃ k : ℤ, n = a.m + k := ⟨n - a.m, by omega⟩
    have hk : k ≥ 0 := by omega
    lift k to ℕ using hk
    induction k with
    | zero => simp
    | succ k ih =>
      have := ih (by omega)
      simp only [Nat.cast_succ] at *
      have h_eq : a.m + (↑k + 1) = a.m + ↑k + 1 := by ring
      rw [h_eq]; linarith [hmono (a.m + ↑k) (by omega)]
  have hbounded : a.IsBounded := a.bounded_iff.mpr ⟨hbound, hbelow⟩
  obtain ⟨S, hS⟩ := Sequence.sup_of_bounded hbounded
  have htendsTo : a.TendsTo S := by
    rw [a.tendsTo_iff S]; intro ε hε
    have hlt : (S - ε : EReal) < a.sup := by
      rw [← hS]; exact EReal.coe_lt_coe_iff.mpr (by linarith)
    obtain ⟨N, hN_m, hN_lt, hN_le⟩ := Sequence.exists_between_lt_sup hlt
    have mono_helper : ∀ n ≥ N, a.seq n ≥ a.seq N := by
      intro n hn
      obtain ⟨k, rfl⟩ : ∃ k : ℤ, n = N + k := ⟨n - N, by omega⟩
      have hk : k ≥ 0 := by omega
      lift k to ℕ using hk
      induction k with
      | zero => simp
      | succ k ih =>
        have := ih (by omega)
        simp only [Nat.cast_succ] at *
        have h_eq : N + (↑k + 1) = N + ↑k + 1 := by ring
        rw [h_eq]; linarith [hmono (N + ↑k) (by omega)]
    use N; intro n hn
    have hle_S : a n ≤ S := by
      have : (a n : EReal) ≤ a.sup := Sequence.le_sup (by omega)
      rw [← hS] at this; exact_mod_cast this
    rw [abs_le]
    constructor <;> linarith [mono_helper n hn, (show a N > S - ε by exact_mod_cast hN_lt)]
  rw [Sequence.lim_eq] at htendsTo; rw [htendsTo.2, hS]

theorem Sequence.convergent_of_antitone {a:Sequence} (hbound: a.BddBelow) (hmono: a.IsAntitone) :
    a.Convergent := by
  have habove : a.BddAbove := by
    use a a.m; intro n hn
    obtain ⟨k, rfl⟩ : ∃ k : ℤ, n = a.m + k := ⟨n - a.m, by omega⟩
    have hk : k ≥ 0 := by omega
    lift k to ℕ using hk
    induction k with
    | zero => simp
    | succ k ih =>
      have := ih (by omega)
      simp only [Nat.cast_succ] at *
      have h_eq : a.m + (↑k + 1) = a.m + ↑k + 1 := by ring
      rw [h_eq]; linarith [hmono (a.m + ↑k) (by omega)]
  have hbounded : a.IsBounded := a.bounded_iff.mpr ⟨habove, hbound⟩
  obtain ⟨S, hS⟩ := Sequence.inf_of_bounded hbounded
  use S; rw [a.tendsTo_iff S]; intro ε hε
  have hgt : (S + ε : EReal) > a.inf := by
    rw [← hS]; exact EReal.coe_lt_coe_iff.mpr (by linarith)
  obtain ⟨N, hN_m, hN_gt, hN_ge⟩ := Sequence.exists_between_gt_inf hgt
  have anti_helper : ∀ n ≥ N, a.seq n ≤ a.seq N := by
    intro n hn
    obtain ⟨k, rfl⟩ : ∃ k : ℤ, n = N + k := ⟨n - N, by omega⟩
    have hk : k ≥ 0 := by omega
    lift k to ℕ using hk
    induction k with
    | zero => simp
    | succ k ih =>
      have := ih (by omega)
      simp only [Nat.cast_succ] at *
      have h_eq : N + (↑k + 1) = N + ↑k + 1 := by ring
      rw [h_eq]; linarith [hmono (N + ↑k) (by omega)]
  use N; intro n hn
  have hge_S : a n ≥ S := by
    have : (a n : EReal) ≥ a.inf := Sequence.ge_inf (by omega)
    rw [← hS] at this; exact_mod_cast this
  rw [abs_le]
  constructor <;> linarith [anti_helper n hn, (show a N < S + ε by exact_mod_cast hN_gt)]

theorem Sequence.lim_of_antitone {a:Sequence} (hbound: a.BddBelow) (hmono: a.IsAntitone) :
    lim a = a.inf := by
  have habove : a.BddAbove := by
    use a a.m; intro n hn
    obtain ⟨k, rfl⟩ : ∃ k : ℤ, n = a.m + k := ⟨n - a.m, by omega⟩
    have hk : k ≥ 0 := by omega
    lift k to ℕ using hk
    induction k with
    | zero => simp
    | succ k ih =>
      have := ih (by omega)
      simp only [Nat.cast_succ] at *
      have h_eq : a.m + (↑k + 1) = a.m + ↑k + 1 := by ring
      rw [h_eq]; linarith [hmono (a.m + ↑k) (by omega)]
  have hbounded : a.IsBounded := a.bounded_iff.mpr ⟨habove, hbound⟩
  obtain ⟨S, hS⟩ := Sequence.inf_of_bounded hbounded
  have htendsTo : a.TendsTo S := by
    rw [a.tendsTo_iff S]; intro ε hε
    have hgt : (S + ε : EReal) > a.inf := by
      rw [← hS]; exact EReal.coe_lt_coe_iff.mpr (by linarith)
    obtain ⟨N, hN_m, hN_gt, hN_ge⟩ := Sequence.exists_between_gt_inf hgt
    have anti_helper : ∀ n ≥ N, a.seq n ≤ a.seq N := by
      intro n hn
      obtain ⟨k, rfl⟩ : ∃ k : ℤ, n = N + k := ⟨n - N, by omega⟩
      have hk : k ≥ 0 := by omega
      lift k to ℕ using hk
      induction k with
      | zero => simp
      | succ k ih =>
        have := ih (by omega)
        simp only [Nat.cast_succ] at *
        have h_eq : N + (↑k + 1) = N + ↑k + 1 := by ring
        rw [h_eq]; linarith [hmono (N + ↑k) (by omega)]
    use N; intro n hn
    have hge_S : a n ≥ S := by
      have : (a n : EReal) ≥ a.inf := Sequence.ge_inf (by omega)
      rw [← hS] at this; exact_mod_cast this
    rw [abs_le]
    constructor <;> linarith [anti_helper n hn, (show a N < S + ε by exact_mod_cast hN_gt)]
  rw [Sequence.lim_eq] at htendsTo; rw [htendsTo.2, hS]

theorem Sequence.convergent_iff_bounded_of_monotone {a:Sequence} (ha: a.IsMonotone) :
    a.Convergent ↔ a.IsBounded := by
  constructor
  · exact Sequence.bounded_of_convergent
  · intro hbounded
    exact Sequence.convergent_of_monotone (a.bounded_iff.mp hbounded).1 ha

theorem Sequence.bounded_iff_convergent_of_antitone {a:Sequence} (ha: a.IsAntitone) :
    a.Convergent ↔ a.IsBounded := by
  constructor
  · exact Sequence.bounded_of_convergent
  · intro hbounded
    exact Sequence.convergent_of_antitone (a.bounded_iff.mp hbounded).2 ha

/-- Example 6.3.9 -/
noncomputable abbrev Example_6_3_9 (n:ℕ) := ⌊ Real.pi * 10^n ⌋ / (10:ℝ)^n

/-- Example 6.3.9 -/
example : (Example_6_3_9:Sequence).IsMonotone := by
  intro n hn
  change n ≥ 0 at hn
  simp [hn, show (0:ℤ) ≤ n + 1 from by omega]
  rw [show (n + 1).toNat = n.toNat + 1 from by omega]
  set k := n.toNat; unfold Example_6_3_9
  rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 10^k) (by positivity : (0:ℝ) < 10^(k+1))]
  calc (↑⌊Real.pi * 10 ^ k⌋ : ℝ) * 10 ^ (k + 1)
      = (↑⌊Real.pi * 10 ^ k⌋ * 10) * 10^k := by ring
    _ ≤ (↑⌊Real.pi * 10^(k+1)⌋ : ℝ) * 10^k := by
        gcongr
        exact_mod_cast show (⌊Real.pi * 10 ^ k⌋ : ℤ) * 10 ≤ ⌊Real.pi * 10 ^ (k+1)⌋ from by
          rw [show Real.pi * 10^(k+1) = (Real.pi * 10^k) * 10 from by ring]
          exact Int.le_floor.mpr (by push_cast; nlinarith [Int.floor_le (Real.pi * 10^k)])

/-- Example 6.3.9 -/
example : (Example_6_3_9:Sequence).BddAboveBy 4 := by
  intro n hn
  change n ≥ 0 at hn
  simp [hn]; unfold Example_6_3_9; set k := n.toNat
  rw [div_le_iff₀ (by positivity : (0:ℝ) < 10^k)]
  calc (↑⌊Real.pi * 10 ^ k⌋ : ℝ) ≤ Real.pi * 10 ^ k := Int.floor_le _
    _ ≤ 4 * 10^k := by nlinarith [Real.pi_le_four, show (0:ℝ) < 10^k from by positivity]

/-- Example 6.3.9 -/
example : (Example_6_3_9:Sequence).Convergent := by
  have hmono : (Example_6_3_9:Sequence).IsMonotone := by
    intro n hn; change n ≥ 0 at hn
    simp [hn, show (0:ℤ) ≤ n + 1 from by omega]
    rw [show (n + 1).toNat = n.toNat + 1 from by omega]
    set k := n.toNat; unfold Example_6_3_9
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 10^k) (by positivity : (0:ℝ) < 10^(k+1))]
    calc (↑⌊Real.pi * 10 ^ k⌋ : ℝ) * 10 ^ (k + 1)
        = (↑⌊Real.pi * 10 ^ k⌋ * 10) * 10^k := by ring
      _ ≤ (↑⌊Real.pi * 10^(k+1)⌋ : ℝ) * 10^k := by
          gcongr
          exact_mod_cast show (⌊Real.pi * 10 ^ k⌋ : ℤ) * 10 ≤ ⌊Real.pi * 10 ^ (k+1)⌋ from by
            rw [show Real.pi * 10^(k+1) = (Real.pi * 10^k) * 10 from by ring]
            exact Int.le_floor.mpr (by push_cast; nlinarith [Int.floor_le (Real.pi * 10^k)])
  have hbdd : (Example_6_3_9:Sequence).BddAboveBy 4 := by
    intro n hn; change n ≥ 0 at hn; simp [hn]; unfold Example_6_3_9; set k := n.toNat
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 10^k)]
    calc (↑⌊Real.pi * 10 ^ k⌋ : ℝ) ≤ Real.pi * 10 ^ k := Int.floor_le _
      _ ≤ 4 * 10^k := by nlinarith [Real.pi_le_four, show (0:ℝ) < 10^k from by positivity]
  exact Sequence.convergent_of_monotone ⟨4, hbdd⟩ hmono

/-- Example 6.3.9 -/
example : lim (Example_6_3_9:Sequence) ≤ 4 := by
  have hconv : (Example_6_3_9:Sequence).Convergent := by
    have hmono : (Example_6_3_9:Sequence).IsMonotone := by
      intro n hn; change n ≥ 0 at hn
      simp [hn, show (0:ℤ) ≤ n + 1 from by omega]
      rw [show (n + 1).toNat = n.toNat + 1 from by omega]
      set k := n.toNat; unfold Example_6_3_9
      rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 10^k) (by positivity : (0:ℝ) < 10^(k+1))]
      calc (↑⌊Real.pi * 10 ^ k⌋ : ℝ) * 10 ^ (k + 1)
          = (↑⌊Real.pi * 10 ^ k⌋ * 10) * 10^k := by ring
        _ ≤ (↑⌊Real.pi * 10^(k+1)⌋ : ℝ) * 10^k := by
            gcongr
            exact_mod_cast show (⌊Real.pi * 10 ^ k⌋ : ℤ) * 10 ≤ ⌊Real.pi * 10 ^ (k+1)⌋ from by
              rw [show Real.pi * 10^(k+1) = (Real.pi * 10^k) * 10 from by ring]
              exact Int.le_floor.mpr (by push_cast; nlinarith [Int.floor_le (Real.pi * 10^k)])
    have hbdd : (Example_6_3_9:Sequence).BddAboveBy 4 := by
      intro n hn; change n ≥ 0 at hn; simp [hn]; unfold Example_6_3_9; set k := n.toNat
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 10^k)]
      calc (↑⌊Real.pi * 10 ^ k⌋ : ℝ) ≤ Real.pi * 10 ^ k := Int.floor_le _
        _ ≤ 4 * 10^k := by nlinarith [Real.pi_le_four, show (0:ℝ) < 10^k from by positivity]
    exact Sequence.convergent_of_monotone ⟨4, hbdd⟩ hmono
  have hbdd : (Example_6_3_9:Sequence).BddAboveBy 4 := by
    intro n hn; change n ≥ 0 at hn; simp [hn]; unfold Example_6_3_9; set k := n.toNat
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 10^k)]
    calc (↑⌊Real.pi * 10 ^ k⌋ : ℝ) ≤ Real.pi * 10 ^ k := Int.floor_le _
      _ ≤ 4 * 10^k := by nlinarith [Real.pi_le_four, show (0:ℝ) < 10^k from by positivity]
  by_contra h; push_neg at h
  have htends := Sequence.lim_def hconv
  rw [Sequence.tendsTo_iff] at htends
  obtain ⟨N, hN⟩ := htends ((lim (Example_6_3_9:Sequence) - 4) / 2) (by linarith)
  have hN' := hN (max N 0) (by omega)
  have hbdd' := hbdd (max N 0) (show max N 0 ≥ 0 from by omega)
  linarith [(abs_le.mp hN').1]

/-- Proposition 6.3.1-/
theorem lim_of_exp {x:ℝ} (hpos: 0 < x) (hbound: x < 1) :
    ((fun (n:ℕ) ↦ x^n):Sequence).Convergent ∧ lim ((fun (n:ℕ) ↦ x^n):Sequence) = 0 := by
  -- This proof is written to follow the structure of the original text.
  set a := ((fun (n:ℕ) ↦ x^n):Sequence)
  have why : a.IsAntitone := by
    intro n hn; change n ≥ 0 at hn
    simp [a, hn, show (0:ℤ) ≤ n + 1 from by omega]
    rw [show (n + 1).toNat = n.toNat + 1 from by omega, pow_succ]
    exact le_of_eq_of_le (mul_comm _ _) (mul_le_of_le_one_left (pow_nonneg hpos.le _) hbound.le)
  have hbound : a.BddBelowBy 0 := by intro n _; positivity
  have hbound' : a.BddBelow := by use 0
  have hconv := a.convergent_of_antitone hbound' why
  set L := lim a
  have : lim ((fun (n:ℕ) ↦ x^(n+1)):Sequence) = x * L := by
    rw [←(a.lim_smul x hconv).2]; congr; ext n; rfl
    simp [a, pow_succ', HSMul.hSMul, SMul.smul]
  have why2 : lim ((fun (n:ℕ) ↦ x^(n+1)):Sequence) = lim ((fun (n:ℕ) ↦ x^n):Sequence) := by
    have htL := Sequence.lim_def hconv
    rw [Sequence.tendsTo_iff] at htL
    have htends' : ((fun (n:ℕ) ↦ x^(n+1)):Sequence).TendsTo L := by
      rw [Sequence.tendsTo_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := htL ε hε
      use max N 0; intro n hn
      have hn0 : n ≥ 0 := by omega
      have hN' := hN (n + 1) (by omega)
      simp only [a, show (0:ℤ) ≤ n + 1 from by omega,
        show (n+1).toNat = n.toNat + 1 from by omega, show (0:ℤ) ≤ n from hn0] at hN' ⊢
      simp only [ite_true, L] at hN' ⊢; exact hN'
    rw [(Sequence.lim_eq.mp htends').2]
  -- this : lim(x^(n+1)) = x * L, why2 : lim(x^(n+1)) = L, so x * L = L
  have hxL : x * L = L := this.symm.trans why2
  have hx : x ≠ 1 := by linarith [hpos]
  have : L * (x - 1) = 0 := by nlinarith
  have : L = 0 := by
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exfalso; exact hx (by linarith)
  exact ⟨hconv, this ▸ rfl⟩

/-- Exercise 6.3.4 -/
theorem lim_of_exp' {x:ℝ} (hbound: x > 1) : ¬((fun (n:ℕ) ↦ x^n):Sequence).Convergent := by
  intro hconv
  have hbounded := Sequence.bounded_of_convergent hconv
  obtain ⟨M, hM_pos, hM⟩ := hbounded
  have hx_pos : (0:ℝ) < x := by linarith
  have hM_nat : ∀ k : ℕ, x ^ k ≤ M := by
    intro k; have := hM (k : ℤ)
    simp [abs_of_nonneg hx_pos.le] at this; exact this
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt M hbound
  linarith [hM_nat N]

end Chapter6
