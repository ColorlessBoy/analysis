import Mathlib.Tactic
import Analysis.Section_9_8
import Analysis.Section_11_5

/-!
# Analysis I, Section 11.6: Riemann integrability of monotone functions

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Riemann integrability of monotone functions.

-/

namespace Chapter11
open Chapter9 BoundedInterval

set_option maxHeartbeats 300000 in
/-- Proposition 11.6.1 (i) -/
theorem integ_of_monotone {a b:ℝ} {f:ℝ → ℝ} (hf: MonotoneOn f (Icc a b)) :
  IntegrableOn f (Icc a b) := by
  -- This proof is adapted from the structure of the original text.
  by_cases hab : 0 < b-a
  swap
  . apply (integ_on_subsingleton _).1; rw [←BoundedInterval.length_of_subsingleton]; aesop
  have hbound := BddOn.of_monotone hf
  set I := Icc a b
  have hab' : a ≤ b := by linarith
  have (ε:ℝ) (hε: 0 < ε) : upper_integral f I - lower_integral f I ≤ ((f b - f a) * (b-a)) *ε := by
    choose N hN using exists_nat_gt (1/ε)
    have hNpos : 0 < N := by rify; linarith [show 0 < 1/ε by positivity]
    set δ := (b-a)/N
    have hδpos : 0 < δ := by positivity
    have hbeq : b = a + δ*N := by simp [δ]; field_simp; linarith
    set e : ℕ ↪ BoundedInterval := {
      toFun j := Ico (a + δ*j) (a + δ*(j+1))
      inj' j k hjk := by simp at hjk; obtain _ | _ := hjk <;> linarith
    }
    set P : Partition I := {
      intervals := insert (Icc b b) (.map e (.range N))
      exists_unique := by
        intro x hx; simp; by_cases hb: x = b
        . apply ExistsUnique.intro (Icc b b)
          . simp [hb, mem_iff]
          rintro J ⟨ rfl | ⟨ j, hA, rfl ⟩, hJb ⟩; rfl
          simp [e, mem_iff, hb, hbeq] at hJb
          replace hJb := hJb.2
          rw [mul_lt_mul_iff_of_pos_left hδpos] at hJb
          norm_cast at hJb; linarith
        simp [I, mem_iff] at hx
        set j := ⌊ (x-a)/δ ⌋₊
        have hxa : 0 ≤ x-a := by linarith
        have hxaδ : 0 ≤ (x-a)/δ := by positivity
        have hxb : x < b := lt_of_le_of_ne hx.2 hb
        have hxj : x ∈ e j := by
          simp [e, mem_iff, j]; split_ands
          . calc
              _ ≤ a + δ * ((x-a)/δ) := by gcongr; grind [Nat.floor_le]
              _ = x := by grind
          calc
            _ = a + δ * ((x-a)/δ) := by field_simp; linarith
            _ < _ := by gcongr; apply Nat.lt_floor_add_one
        apply ExistsUnique.intro (e j)
        . refine ⟨ ?_, hxj ⟩; right; use j; simp [j, Nat.floor_lt hxaδ, div_lt_iff₀' hδpos]; linarith
        rintro J ⟨ rfl | ⟨ k, hk, rfl ⟩, hxJ ⟩
        . simp [mem_iff] at hxJ; grind
        simp [mem_iff, e] at hxJ hxj
        obtain hjk | rfl | hjk := lt_trichotomy j k
        . replace hjk : δ*((j:ℝ)+1) ≤ δ*(k:ℝ) := by rw [mul_le_mul_iff_of_pos_left hδpos]; norm_cast
          linarith
        . rfl
        replace hjk : δ*((k:ℝ)+1) ≤ δ*(j:ℝ) := by rw [mul_le_mul_iff_of_pos_left hδpos]; norm_cast
        linarith
      contains J hJ := by
        simp at hJ; obtain rfl | ⟨ j, hj, rfl ⟩ := hJ <;> simp [subset_iff, e, I]
        . linarith
        apply Set.Ico_subset_Icc_self.trans (Set.Icc_subset_Icc _ _)
        . simp; positivity
        simp [hbeq]; gcongr; norm_cast
    }
    have hup := calc
      upper_integral f I ≤ ∑ J ∈ P.intervals, (sSup (f '' (J:Set ℝ))) * |J|ₗ := upper_integ_le_upper_sum hbound P
      _ = ∑ j ∈ .range N, (sSup (f '' (Ico (a + δ*j) (a + δ*(j+1))))) * |Ico (a + δ*j) (a + δ*(j+1))|ₗ := by simp [P]; congr
      _ ≤ ∑ j ∈ .range N, f (a + δ*(j+1)) * δ := by
        apply Finset.sum_le_sum; intro j hj
        convert (mul_le_mul_iff_left₀ hδpos).mpr ?_
        . simp [length]; ring_nf; simp [le_of_lt hδpos]
        apply csSup_le
        . simp; grind
        intro y hy; simp at hy; obtain ⟨ x, ⟨ hx1, hx2 ⟩, rfl ⟩ := hy
        have : a + δ*(j+1) ≤ b := by simp [hbeq]; gcongr; norm_cast; grind
        have hδj : 0 ≤ δ*j := by positivity
        have hδj1 : 0 ≤ δ*(j+1) := by positivity
        apply hf _ _ (by order) <;> simp [I, hδj1, this]; grind
    have hdown := calc
      lower_integral f I ≥ ∑ J ∈ P.intervals, (sInf (f '' (J:Set ℝ))) * |J|ₗ :=
        lower_integ_ge_lower_sum hbound P
      _ = ∑ j ∈ .range N, (sInf (f '' (Ico (a + δ*j) (a + δ*(j+1))))) * |Ico (a + δ*j) (a + δ*(j+1))|ₗ := by simp [P]; congr
      _ ≥ ∑ j ∈ .range N, f (a + δ*j) * δ := by
        apply Finset.sum_le_sum; intro j hj
        convert (mul_le_mul_iff_left₀ hδpos).mpr ?_
        . simp [length]; ring_nf; simp [le_of_lt hδpos]
        apply le_csInf
        . simp; grind
        intro y hy; simp at hy; obtain ⟨ x, ⟨ hx1, hx2 ⟩, rfl ⟩ := hy
        have hajb': a + δ*(j+1) ≤ b := by simp [hbeq]; gcongr; norm_cast; grind
        have hδj : 0 ≤ δ*j := by positivity
        have hδj1 : 0 ≤ δ*(j+1) := by positivity
        apply_rules [hf] <;> simp [I, hδj] <;> grind
    calc
      _ ≤ ∑ j ∈ .range N, f (a + δ*(j+1)) * δ - ∑ j ∈ .range N, f (a + δ*j) * δ := by linarith
      _ = (f b - f a) * δ := by
        rw [←Finset.sum_sub_distrib]
        have := Finset.sum_range_sub (fun n ↦ f (a + δ*n) * δ) N
        simp only [Nat.cast_add, Nat.cast_one] at this
        convert this using 1; simp [hbeq]; ring
      _ ≤ _ := by
        have : 0 ≤ f b - f a := by simp; apply hf <;> simp [I, hab']
        simp [mul_assoc, δ]; gcongr
        rw [div_le_iff₀', mul_comm, mul_assoc]
        nth_rewrite 1 [←mul_one (b-a)]
        gcongr; rw [←div_le_iff₀']; linarith
        all_goals positivity
  refine ⟨ hbound, ?_ ⟩
  observe low_le_up : lower_integral f I ≤ upper_integral f I
  linarith [nonneg_of_le_const_mul_eps this]


/-- Proposition 11.6.1 (ii) -/
theorem integ_of_antitone {a b:ℝ} {f:ℝ → ℝ} (hf: AntitoneOn f (Icc a b)) :
  IntegrableOn f (Icc a b) := by
  rw [←neg_neg f]; apply (integ_of_monotone _).neg.1; convert hf.neg using 1

/-- Corollary 11.6.3 (i) / Exercise 11.6.1 -/
theorem integ_of_bdd_monotone {I:BoundedInterval} {f:ℝ → ℝ} (hbound: BddOn f I)
  (hf: MonotoneOn f I) : IntegrableOn f I := by
  by_cases hlen : |I|ₗ = 0
  · exact (integ_on_subsingleton hlen).1
  let a := I.a
  let b := I.b
  have ha_lt_b : a < b := by
    by_contra! h
    have hlen0 : |I|ₗ = 0 := by
      unfold BoundedInterval.length
      have h_nonpos : b - a ≤ 0 := by linarith
      have : max (b - a) 0 = 0 := max_eq_right h_nonpos
      simpa
    exact hlen hlen0
  have h_nonempty : (I : Set ℝ).Nonempty := by
    refine ⟨(a + b) / 2, ?_⟩
    cases I with
    | Ioo a' b' =>
      have h_lt : a' < b' := ha_lt_b
      have h_mem : (a' + b') / 2 ∈ Set.Ioo a' b' := by
        constructor <;> nlinarith
      simpa using h_mem
    | Icc a' b' =>
      have h_lt : a' < b' := ha_lt_b
      have h_mem : (a' + b') / 2 ∈ Set.Icc a' b' := by
        constructor <;> nlinarith
      simpa using h_mem
    | Ioc a' b' =>
      have h_lt : a' < b' := ha_lt_b
      have h_mem : (a' + b') / 2 ∈ Set.Ioc a' b' := by
        constructor <;> nlinarith
      simpa using h_mem
    | Ico a' b' =>
      have h_lt : a' < b' := ha_lt_b
      have h_mem : (a' + b') / 2 ∈ Set.Ico a' b' := by
        constructor <;> nlinarith
      simpa using h_mem
  rcases hbound with ⟨M, hM⟩
  have hM_nonneg : 0 ≤ M := by
    rcases h_nonempty with ⟨x, hx⟩
    have h_abs := hM x hx
    have h_nonneg_abs : 0 ≤ |f x| := abs_nonneg _
    linarith
  let L := -M
  let U := M
  have hLfx (x : ℝ) (hx : x ∈ (I : Set ℝ)) : L ≤ f x := by
    have h_abs := (abs_le.mp (hM x hx)).1
    linarith
  have hfxU (x : ℝ) (hx : x ∈ (I : Set ℝ)) : f x ≤ U := by
    have h_abs := (abs_le.mp (hM x hx)).2
    linarith
  have hLU : L ≤ U := by nlinarith
  classical
  have h_congr {I' : BoundedInterval} {g : ℝ → ℝ} (h_eq : Set.EqOn f g I') (hg : IntegrableOn g I') : IntegrableOn f I' := by
    unfold IntegrableOn
    refine ⟨?_, ?_⟩
    · rcases hg.1 with ⟨M, hM⟩
      refine ⟨M, λ x hx => ?_⟩
      rw [h_eq hx]; exact hM x hx
    · calc
        lower_integral f I' = lower_integral g I' := lower_integral_congr h_eq
        _ = upper_integral g I' := hg.2
        _ = upper_integral f I' := (upper_integral_congr h_eq).symm
  cases I with
  | Icc a b => exact integ_of_monotone hf
  | Ioo a b =>
    let g (x : ℝ) : ℝ :=
      if hxI : x ∈ (Ioo a b : Set ℝ) then f x else if x ≤ a then L else U
    have hg_eq_on : Set.EqOn f g (Ioo a b) := by
      intro x hx; dsimp [g]; rw [if_pos hx]
    have not_mem_or (z : ℝ) (hz : z ∉ (Ioo a b : Set ℝ)) : z ≤ a ∨ b ≤ z := by
      by_cases hzle_a : z ≤ a
      · left; exact hzle_a
      · right
        have haz : a < z := by linarith
        by_contra! hzlt_b
        have hz_mem : z ∈ (Ioo a b : Set ℝ) := by
          simp [Set.mem_Ioo, haz, hzlt_b]
        exact hz hz_mem
    have hg_mono : MonotoneOn g (Icc a b) := by
      intro x hx y hy hxy
      rcases hx with ⟨hxa, hxb⟩; rcases hy with ⟨hya, hyb⟩
      dsimp [g]
      by_cases hx_mem : x ∈ (Ioo a b : Set ℝ)
      · rcases (by simpa [Set.mem_Ioo] using hx_mem) with ⟨hx_gt_a, hx_lt_b⟩
        rw [if_pos hx_mem]
        by_cases hy_mem : y ∈ (Ioo a b : Set ℝ)
        · rw [if_pos hy_mem]
          exact hf hx_mem hy_mem hxy
        · rw [if_neg hy_mem]
          rcases not_mem_or y hy_mem with (hy_not | hy_not)
          · have hy_eq_a : y = a := by linarith
            have hx_eq_a : x = a := by linarith
            linarith
          · have h_not_y_le_a : ¬(y ≤ a) := by linarith
            rw [if_neg h_not_y_le_a]
            exact hfxU x hx_mem
      · rw [if_neg hx_mem]
        rcases not_mem_or x hx_mem with (hx_not | hx_not)
        · rw [if_pos hx_not]
          by_cases hy_mem : y ∈ (Ioo a b : Set ℝ)
          · rw [if_pos hy_mem]
            exact hLfx y hy_mem
          · rw [if_neg hy_mem]
            rcases not_mem_or y hy_mem with (hy_not | hy_not)
            · rw [if_pos hy_not]
            · have h_not_y_le_a : ¬(y ≤ a) := by linarith
              rw [if_neg h_not_y_le_a]
              exact hLU
        · have h_not_x_le_a : ¬(x ≤ a) := by linarith
          rw [if_neg h_not_x_le_a]
          by_cases hy_mem : y ∈ (Ioo a b : Set ℝ)
          · rcases (by simpa [Set.mem_Ioo] using hy_mem) with ⟨hy_gt_a, hy_lt_b⟩
            have hb_le_y : b ≤ y := by linarith
            linarith
          · rw [if_neg hy_mem]
            rcases not_mem_or y hy_mem with (hy_not | hy_not)
            · -- hy_not = y ≤ a, impossible since a < b ≤ x ≤ y
              linarith
            · -- hy_not = b ≤ y, both sides are U
              have h_not_y_le_a : ¬(y ≤ a) := by linarith
              simp [h_not_y_le_a]
    have hg_int : IntegrableOn g (Icc a b) := integ_of_monotone hg_mono
    have hg_int_I : IntegrableOn g (Ioo a b) :=
      IntegrableOn.mono' (BoundedInterval.subset_Icc (Ioo a b)) hg_int
    exact h_congr hg_eq_on hg_int_I
  | Ioc a b =>
    let g (x : ℝ) : ℝ :=
      if hxI : x ∈ (Ioc a b : Set ℝ) then f x else if x ≤ a then L else U
    have hg_eq_on : Set.EqOn f g (Ioc a b) := by
      intro x hx; dsimp [g]; rw [if_pos hx]
    have not_mem_or (z : ℝ) (hz : z ∉ (Ioc a b : Set ℝ)) : z ≤ a ∨ b < z := by
      by_cases hzle_a : z ≤ a
      · left; exact hzle_a
      · right
        have haz : a < z := by linarith
        by_contra! hzle_b
        have hz_mem : z ∈ (Ioc a b : Set ℝ) := by
          simp [Set.mem_Ioc, haz, hzle_b]
        exact hz hz_mem
    have hg_mono : MonotoneOn g (Icc a b) := by
      intro x hx y hy hxy
      rcases hx with ⟨hxa, hxb⟩; rcases hy with ⟨hya, hyb⟩
      dsimp [g]
      by_cases hx_mem : x ∈ (Ioc a b : Set ℝ)
      · rcases (by simpa [Set.mem_Ioc] using hx_mem) with ⟨hx_gt_a, hx_le_b⟩
        rw [if_pos hx_mem]
        by_cases hy_mem : y ∈ (Ioc a b : Set ℝ)
        · rw [if_pos hy_mem]
          exact hf hx_mem hy_mem hxy
        · rw [if_neg hy_mem]
          rcases not_mem_or y hy_mem with (hy_not | hy_not)
          · have hy_eq_a : y = a := by linarith
            have hx_eq_a : x = a := by linarith
            linarith
          · have h_not_y_le_a : ¬(y ≤ a) := by linarith
            rw [if_neg h_not_y_le_a]
            exact hfxU x hx_mem
      · rw [if_neg hx_mem]
        rcases not_mem_or x hx_mem with (hx_not | hx_not)
        · rw [if_pos hx_not]
          by_cases hy_mem : y ∈ (Ioc a b : Set ℝ)
          · rw [if_pos hy_mem]
            exact hLfx y hy_mem
          · rw [if_neg hy_mem]
            rcases not_mem_or y hy_mem with (hy_not | hy_not)
            · rw [if_pos hy_not]
            · have h_not_y_le_a : ¬(y ≤ a) := by linarith
              rw [if_neg h_not_y_le_a]
              exact hLU
        · linarith
    have hg_int : IntegrableOn g (Icc a b) := integ_of_monotone hg_mono
    have hg_int_I : IntegrableOn g (Ioc a b) :=
      IntegrableOn.mono' (BoundedInterval.subset_Icc (Ioc a b)) hg_int
    exact h_congr hg_eq_on hg_int_I
  | Ico a b =>
    let g (x : ℝ) : ℝ :=
      if hxI : x ∈ (Ico a b : Set ℝ) then f x else if x ≤ a then L else U
    have hg_eq_on : Set.EqOn f g (Ico a b) := by
      intro x hx; dsimp [g]; rw [if_pos hx]
    have not_mem_or (z : ℝ) (hz : z ∉ (Ico a b : Set ℝ)) : z < a ∨ b ≤ z := by
      by_cases hzlt_a : z < a
      · left; exact hzlt_a
      · right
        have haz : a ≤ z := by linarith
        by_contra! hzlt_b
        have hz_mem : z ∈ (Ico a b : Set ℝ) := by
          simp [Set.mem_Ico, haz, hzlt_b]
        exact hz hz_mem
    have hg_mono : MonotoneOn g (Icc a b) := by
      intro x hx y hy hxy
      rcases hx with ⟨hxa, hxb⟩; rcases hy with ⟨hya, hyb⟩
      dsimp [g]
      by_cases hx_mem : x ∈ (Ico a b : Set ℝ)
      · rcases (by simpa [Set.mem_Ico] using hx_mem) with ⟨hx_ge_a, hx_lt_b⟩
        rw [if_pos hx_mem]
        by_cases hy_mem : y ∈ (Ico a b : Set ℝ)
        · rw [if_pos hy_mem]
          exact hf hx_mem hy_mem hxy
        · rw [if_neg hy_mem]
          rcases not_mem_or y hy_mem with (hy_not | hy_not)
          · linarith
          · have h_not_y_le_a : ¬(y ≤ a) := by linarith
            rw [if_neg h_not_y_le_a]
            exact hfxU x hx_mem
      · rw [if_neg hx_mem]
        rcases not_mem_or x hx_mem with (hx_not | hx_not)
        · linarith
        · have h_not_x_le_a : ¬(x ≤ a) := by linarith
          rw [if_neg h_not_x_le_a]
          by_cases hy_mem : y ∈ (Ico a b : Set ℝ)
          · rcases (by simpa [Set.mem_Ico] using hy_mem) with ⟨hy_ge_a, hy_lt_b⟩
            have hb_le_y : b ≤ y := by linarith
            linarith
          · rw [if_neg hy_mem]
            rcases not_mem_or y hy_mem with (hy_not | hy_not)
            · -- hy_not = y < a, impossible since a < b ≤ x ≤ y
              linarith
            · -- hy_not = b ≤ y, both sides are U
              have h_not_y_le_a : ¬(y ≤ a) := by linarith
              simp [h_not_y_le_a]
    have hg_int : IntegrableOn g (Icc a b) := integ_of_monotone hg_mono
    have hg_int_I : IntegrableOn g (Ico a b) :=
      IntegrableOn.mono' (BoundedInterval.subset_Icc (Ico a b)) hg_int
    exact h_congr hg_eq_on hg_int_I

/-- Corollary 11.6.3 (ii) / Exercise 11.6.1 -/
theorem integ_of_bdd_antitone {I:BoundedInterval} {f:ℝ → ℝ} (hbound: BddOn f I)
  (hf: AntitoneOn f I) : IntegrableOn f I := by
  have hbound' : BddOn (-f) I := by
    rcases hbound with ⟨M, hM⟩
    refine ⟨M, λ x hx => ?_⟩
    simpa using hM x hx
  have hf' : MonotoneOn (-f) I := by simpa using hf.neg
  have h_int : IntegrableOn (-f) I := integ_of_bdd_monotone hbound' hf'
  simpa [neg_neg] using h_int.neg.1

/-- Proposition 11.6.4 (Integral test) -/
theorem summable_iff_integ_of_antitone {f:ℝ → ℝ} (hnon: ∀ x ≥ 0, f x ≥ 0)
  (hf: AntitoneOn f (.Ici 0)) :
  Summable (fun n:ℕ ↦ f n) ↔ ∃ M, ∀ N ≥ 0, integ f (Icc 0 N) ≤ M := by
  have h_nonneg_nat : ∀ n : ℕ, 0 ≤ f n :=
    λ n => hnon n (by exact mod_cast (Nat.cast_nonneg n : 0 ≤ (n : ℝ)))
  have h_nonneg_re (x : ℝ) (hx : x ≥ 0) : 0 ≤ f x := hnon x hx
  have h_nonneg_n (n : ℕ) : (0 : ℝ) ≤ (n : ℝ) := by exact mod_cast Nat.zero_le n
  have h_Ioc_len_one (n : ℕ) : |(Ioc (n:ℝ) ((n+1 : ℕ):ℝ))|ₗ = (1 : ℝ) := by
    unfold BoundedInterval.length; simp
  have integ_Ioc (n : ℕ) : IntegrableOn f (Ioc (n:ℝ) ((n+1 : ℕ):ℝ)) := by
    apply integ_of_bdd_antitone
    · refine ⟨f n, λ x hx => ?_⟩
      have hx' : (n : ℝ) < x ∧ x ≤ (n+1 : ℝ) := by simpa using hx
      have hx_nonneg : 0 ≤ x := by linarith [h_nonneg_n n]
      have hx_n : (n : ℝ) ≤ x := by linarith
      have h_nonneg_fx : 0 ≤ f x := h_nonneg_re x hx_nonneg
      have h_le : f x ≤ f n := hf (Set.mem_setOf.mpr (h_nonneg_n n)) (Set.mem_setOf.mpr hx_nonneg) hx_n
      calc |f x| = f x := abs_of_nonneg h_nonneg_fx
        _ ≤ f n := h_le
    · refine hf.mono (λ x hx => ?_)
      have hx' : (n : ℝ) < x ∧ x ≤ (n+1 : ℝ) := by simpa using hx
      have hx_nonneg : 0 ≤ x := by linarith [h_nonneg_n n]
      exact hx_nonneg
  have h_integ_Ioc_f_le_f_n (n : ℕ) : integ f (Ioc (n:ℝ) ((n+1 : ℕ):ℝ)) ≤ f n := by
    have h_int_f : IntegrableOn f (Ioc (n:ℝ) ((n+1 : ℕ):ℝ)) := integ_Ioc n
    have h_int_const : IntegrableOn (fun _ : ℝ => f n) (Ioc (n:ℝ) ((n+1 : ℕ):ℝ)) :=
      (IntegrableOn.const (f n) _).1
    have h_maj : MajorizesOn (fun _ : ℝ => f n) f (Ioc (n:ℝ) ((n+1 : ℕ):ℝ)) := by
      intro x hx
      have hx' : (n : ℝ) < x ∧ x ≤ (n+1 : ℝ) := by simpa using hx
      have hx_nonneg : 0 ≤ x := by linarith [h_nonneg_n n]
      have hx_n : (n : ℝ) ≤ x := by linarith
      exact hf (Set.mem_setOf.mpr (h_nonneg_n n)) (Set.mem_setOf.mpr hx_nonneg) hx_n
    have h_m : integ f (Ioc (n:ℝ) ((n+1 : ℕ):ℝ)) ≤ integ (fun _ : ℝ => f n) (Ioc (n:ℝ) ((n+1 : ℕ):ℝ)) :=
      IntegrableOn.mono h_int_f h_int_const h_maj
    calc
      integ f (Ioc (n:ℝ) ((n+1 : ℕ):ℝ)) ≤ integ (fun _ : ℝ => f n) (Ioc (n:ℝ) ((n+1 : ℕ):ℝ)) := h_m
      _ = (f n) * |(Ioc (n:ℝ) ((n+1 : ℕ):ℝ))|ₗ := (IntegrableOn.const (f n) _).2
      _ = (f n) * (1 : ℝ) := by rw [h_Ioc_len_one n]
      _ = f n := by ring
  have h_f_np1_le_integ_Ioc (n : ℕ) : f (n+1) ≤ integ f (Ioc (n:ℝ) ((n+1 : ℕ):ℝ)) := by
    have h_int_f : IntegrableOn f (Ioc (n:ℝ) ((n+1 : ℕ):ℝ)) := integ_Ioc n
    have h_int_const : IntegrableOn (fun _ : ℝ => f (n+1)) (Ioc (n:ℝ) ((n+1 : ℕ):ℝ)) :=
      (IntegrableOn.const (f (n+1)) _).1
    have h_maj : MajorizesOn f (fun _ : ℝ => f (n+1)) (Ioc (n:ℝ) ((n+1 : ℕ):ℝ)) := by
      intro x hx
      have hx' : (n : ℝ) < x ∧ x ≤ (n+1 : ℝ) := by simpa using hx
      have hx_nonneg : 0 ≤ x := by linarith [h_nonneg_n n]
      have hx_np1 : x ≤ (n+1 : ℝ) := by linarith
      have h_np1_nonneg : (0 : ℝ) ≤ (n+1 : ℝ) := by exact mod_cast Nat.zero_le (n+1)
      exact hf (Set.mem_setOf.mpr hx_nonneg) (Set.mem_setOf.mpr h_np1_nonneg) hx_np1
    have h_m : integ (fun _ : ℝ => f (n+1)) (Ioc (n:ℝ) ((n+1 : ℕ):ℝ)) ≤ integ f (Ioc (n:ℝ) ((n+1 : ℕ):ℝ)) :=
      IntegrableOn.mono h_int_const h_int_f h_maj
    calc
      f (n+1) = (f (n+1)) * (1 : ℝ) := by ring
      _ = (f (n+1)) * |(Ioc (n:ℝ) ((n+1 : ℕ):ℝ))|ₗ := by rw [h_Ioc_len_one n]
      _ = integ (fun _ : ℝ => f (n+1)) (Ioc (n:ℝ) ((n+1 : ℕ):ℝ)) :=
        by symm; exact (IntegrableOn.const (f (n+1)) _).2
      _ ≤ integ f (Ioc (n:ℝ) ((n+1 : ℕ):ℝ)) := h_m
  have h_integ_Icc_eq_sum (k : ℕ) : integ f (Icc (0 : ℝ) (k : ℝ)) = ∑ n ∈ Finset.range k, integ f (Ioc (n:ℝ) ((n+1 : ℕ):ℝ)) := by
    induction' k with m ih
    · have h_len : |(Icc (0 : ℝ) (0 : ℝ))|ₗ = (0 : ℝ) := by
        unfold BoundedInterval.length; simp
      have h_zero : integ f (Icc (0 : ℝ) (0 : ℝ)) = 0 := (integ_on_subsingleton h_len).2
      simp [h_zero]
    · have h_join : (Icc (0 : ℝ) ((m+1 : ℕ) : ℝ)).joins (Icc (0 : ℝ) (m : ℝ)) (Ioc (m : ℝ) ((m+1 : ℕ) : ℝ)) :=
        BoundedInterval.join_Icc_Ioc (by exact_mod_cast Nat.zero_le m) (by exact_mod_cast (Nat.le_succ m))
      have h_int_left : IntegrableOn f (Icc (0 : ℝ) (m : ℝ)) :=
        integ_of_antitone (hf.mono (Set.Subset.trans (by
          intro x hx; simpa [Set.mem_Icc] using hx) (by
          intro x hx; exact hx.1)))
      have h_int_right : IntegrableOn f (Ioc (m : ℝ) ((m+1 : ℕ) : ℝ)) := integ_Ioc m
      rcases IntegrableOn.of_join h_join h_int_left h_int_right with ⟨_, h_eq⟩
      rw [h_eq, ih]
      simp [Finset.sum_range_succ]
  have h_integ_Icc_le_sum (k : ℕ) : integ f (Icc (0 : ℝ) (k : ℝ)) ≤ ∑ n ∈ Finset.range k, f n := by
    rw [h_integ_Icc_eq_sum k]
    refine Finset.sum_le_sum (λ n hn => h_integ_Ioc_f_le_f_n n)
  have h_sum_f_np1_le_integ (k : ℕ) : ∑ n ∈ Finset.range k, f (n+1) ≤ integ f (Icc (0 : ℝ) (k : ℝ)) := by
    rw [h_integ_Icc_eq_sum k]
    refine Finset.sum_le_sum (λ n hn => h_f_np1_le_integ_Ioc n)
  have hS_mono : Monotone (λ k : ℕ => ∑ n ∈ Finset.range k, f n) := by
    intro a b h
    have hsub : Finset.range a ⊆ Finset.range b := Finset.range_mono h
    have h_eq := Finset.sum_sdiff (f := fun (x : ℕ) => f (x : ℝ)) hsub
    have h_nonneg_sdiff : 0 ≤ ∑ x ∈ Finset.range b \ Finset.range a, f x :=
      Finset.sum_nonneg (λ x hx => h_nonneg_nat x)
    calc
      (∑ n ∈ Finset.range a, f n) ≤ (∑ x ∈ Finset.range b \ Finset.range a, f x) + (∑ n ∈ Finset.range a, f n) := by linarith
      _ = (∑ n ∈ Finset.range b, f n) := h_eq
  constructor
  · intro hsumm
    have hsumm_hasSum : HasSum (fun n : ℕ => f n) (∑' n : ℕ, f n) := hsumm.hasSum
    have hsumm_range : Filter.Tendsto (fun (k : ℕ) => ∑ n ∈ Finset.range k, f n)
      Filter.atTop (nhds (∑' n : ℕ, f n)) :=
      ((hasSum_iff_tendsto_nat_of_nonneg h_nonneg_nat (∑' n : ℕ, f n)).mp hsumm_hasSum)
    have h_sum_bdd : ∀ k : ℕ, ∑ n ∈ Finset.range k, f n ≤ ∑' n : ℕ, f n := by
      intro k
      have h_eventually : ∀ᶠ (k' : ℕ) in Filter.atTop,
        (∑ n ∈ Finset.range k, f n) ≤ (∑ n ∈ Finset.range k', f n) := by
        apply Filter.eventually_atTop.mpr
        refine ⟨k, λ k' hk' => hS_mono hk'⟩
      exact ge_of_tendsto hsumm_range h_eventually
    refine ⟨∑' n : ℕ, f n, λ N hN_nonneg => ?_⟩
    rcases exists_nat_gt N with ⟨k, hkN⟩
    have h_integ_le_integ_k : integ f (Icc (0 : ℝ) N) ≤ integ f (Icc (0 : ℝ) (k : ℝ)) := by
      have h_join : (Icc (0 : ℝ) (k : ℝ)).joins (Icc (0 : ℝ) N) (Ioc N (k : ℝ)) :=
        BoundedInterval.join_Icc_Ioc (by nlinarith) (by nlinarith)
      have h_int_left : IntegrableOn f (Icc (0 : ℝ) N) :=
        integ_of_antitone (hf.mono (Set.Subset.trans (by
          intro x hx; simpa [Set.mem_Icc] using hx) (by
          intro x hx; exact hx.1)))
      have h_int_right : IntegrableOn f (Ioc N (k : ℝ)) := by
        apply integ_of_bdd_antitone
        · refine ⟨f N, λ x hx => ?_⟩
          have hx' : N < x ∧ x ≤ (k : ℝ) := by simpa using hx
          have hx_nonneg : 0 ≤ x := by linarith
          have h_nonneg_fx : 0 ≤ f x := h_nonneg_re x hx_nonneg
          have h_le : f x ≤ f N :=
            hf (Set.mem_setOf.mpr hN_nonneg) (Set.mem_setOf.mpr hx_nonneg) (by linarith)
          calc |f x| = f x := abs_of_nonneg h_nonneg_fx
            _ ≤ f N := h_le
        · refine hf.mono (λ x hx => ?_)
          have hx' : N < x ∧ x ≤ (k : ℝ) := by simpa using hx
          have hx_nonneg : 0 ≤ x := by linarith
          exact hx_nonneg
      rcases IntegrableOn.of_join h_join h_int_left h_int_right with ⟨_, h_eq⟩
      have h_nonneg_rest : 0 ≤ integ f (Ioc N (k : ℝ)) :=
        IntegrableOn.nonneg h_int_right (λ x hx => h_nonneg_re x (by
          have hx' : N < x ∧ x ≤ (k : ℝ) := by simpa using hx
          linarith))
      linarith
    have h_integ_k_le_sum : integ f (Icc (0 : ℝ) (k : ℝ)) ≤ ∑ n ∈ Finset.range k, f n :=
      h_integ_Icc_le_sum k
    have h_sum_le_tsum : ∑ n ∈ Finset.range k, f n ≤ ∑' n : ℕ, f n := h_sum_bdd k
    calc
      integ f (Icc (0 : ℝ) N) ≤ integ f (Icc (0 : ℝ) (k : ℝ)) := h_integ_le_integ_k
      _ ≤ ∑ n ∈ Finset.range k, f n := h_integ_k_le_sum
      _ ≤ ∑' n : ℕ, f n := h_sum_le_tsum
  · intro ⟨M, hM⟩
    have h_nonneg_M' : 0 ≤ M := by
      have h_len : |(Icc (0 : ℝ) (0 : ℝ))|ₗ = (0 : ℝ) := by
        unfold BoundedInterval.length; simp
      have h_integ0 : integ f (Icc (0 : ℝ) (0 : ℝ)) = 0 := (integ_on_subsingleton h_len).2
      have h0 := hM (0 : ℝ) (by norm_num)
      linarith
    have h_partial_sum_formula (k : ℕ) (hk : 1 ≤ k) : ∑ n ∈ Finset.range k, f n = f 0 + ∑ n ∈ Finset.range (k-1), f (n+1) := by
      rcases Nat.exists_eq_add_of_le hk with ⟨m, hm⟩
      subst hm
      induction' m with m ih
      · simp
      · have hm' : 1 ≤ 1 + m := by omega
        have h_eq : 1 + (m + 1) = (1 + m) + 1 := by omega
        rw [h_eq, Finset.sum_range_succ, ih hm', add_assoc]
        simp [Finset.sum_range_succ, add_comm, add_left_comm]
    have h_bdd_partial : ∀ k : ℕ, ∑ n ∈ Finset.range k, f n ≤ f 0 + M := by
      intro k
      by_cases hk : k = 0
      · subst hk; simp; nlinarith [show 0 ≤ f (0 : ℝ) from by simpa using h_nonneg_nat 0, h_nonneg_M']
      · have hk1 : 1 ≤ k := by omega
        rw [h_partial_sum_formula k hk1]
        have h_sum_le_integ : ∑ n ∈ Finset.range (k-1), f (n+1) ≤ integ f (Icc (0 : ℝ) ((k-1 : ℕ) : ℝ)) := by
          have h_integ := h_sum_f_np1_le_integ (k-1)
          simpa using h_integ
        have h_integ_le_M : integ f (Icc (0 : ℝ) ((k-1 : ℕ) : ℝ)) ≤ M :=
          hM ((k-1 : ℕ) : ℝ) (by exact mod_cast Nat.zero_le (k-1))
        nlinarith
    have hsumm : Summable (fun n : ℕ => f n) := by
      have h_tendsto : Filter.Tendsto (fun (k : ℕ) => ∑ n ∈ Finset.range k, f n) Filter.atTop
        (nhds (⨆ k, ∑ n ∈ Finset.range k, f n)) := by
        let S := fun (k : ℕ) => ∑ n ∈ Finset.range k, f n
        have h_bdd : BddAbove (Set.range S) := by
          refine ⟨f 0 + M, λ y ⟨k, hk⟩ => ?_⟩
          rw [← hk]; exact h_bdd_partial k
        exact tendsto_atTop_ciSup hS_mono h_bdd
      have hsum : HasSum (fun n : ℕ => f n) (⨆ k, ∑ n ∈ Finset.range k, f n) :=
        ((hasSum_iff_tendsto_nat_of_nonneg h_nonneg_nat (⨆ k, ∑ n ∈ Finset.range k, f n)).mpr h_tendsto)
      exact hsum.summable
    exact hsumm

-- Exercise 11.6.2: Formulate a reasonable notion of a piecewise monotone function, and then
-- show that all bounded piecewise monotone functions are Riemann integrable.

/-- Exercise 11.6.4 -/

private lemma integrableOn_of_eq_const (f : ℝ → ℝ) (I : BoundedInterval) (c : ℝ) (h_eq : Set.EqOn f (fun _ => c) I) :
    IntegrableOn f I := by
  have hc_int : IntegrableOn (fun _ : ℝ => c) I := (IntegrableOn.const c I).1
  unfold IntegrableOn
  refine ⟨?_, ?_⟩
  · rcases hc_int.1 with ⟨M, hM⟩
    refine ⟨M, λ x hx => ?_⟩
    rw [h_eq hx]
    exact hM x hx
  · calc
      lower_integral f I = lower_integral (fun _ : ℝ => c) I := lower_integral_congr h_eq
      _ = upper_integral (fun _ : ℝ => c) I := hc_int.2
      _ = upper_integral f I := (upper_integral_congr h_eq).symm

private lemma integ_of_eq_const (f : ℝ → ℝ) (I : BoundedInterval) (c : ℝ) (h_eq : Set.EqOn f (fun _ => c) I) :
    integ f I = c * |I|ₗ := by
  calc
    integ f I = integ (fun _ : ℝ => c) I := integ_congr h_eq
    _ = c * |I|ₗ := (IntegrableOn.const c I).2

/-- First counterexample: series converges but integrals are unbounded. -/
example : ∃ (f:ℝ → ℝ), (∀ x ≥ 0, f x ≥ 0) ∧ Summable (fun n:ℕ ↦ f n) ∧ ¬ ∃ M, ∀ N ≥ 0, integ f (Icc 0 N) ≤ M := by
  let n (x : ℝ) : ℝ := (⌊x⌋₊ : ℕ)
  let f : ℝ → ℝ := λ x =>
    if hx : x ≥ 0 then
      if x = n x then 0
      else if x < n x + 1 / (n x + 1) then n x + 1
      else 0
    else 0
  have h_nonneg : ∀ x ≥ 0, f x ≥ 0 := by
    intro x hx
    dsimp [f, n]
    rw [if_pos hx]
    split <;> positivity
  have h_summable : Summable (fun m : ℕ => f m) := by
    have h_zero : ∀ m : ℕ, f m = 0 := by
      intro m
      dsimp [f, n]
      have hm_nonneg : (m : ℝ) ≥ 0 := by exact mod_cast Nat.zero_le m
      rw [if_pos hm_nonneg]
      simp
    simp [h_zero, summable_zero]
  have h_integ_Ioc (k : ℕ) : IntegrableOn f (Ioc (k : ℝ) ((k : ℝ) + 1)) ∧
      integ f (Ioc (k : ℝ) ((k : ℝ) + 1)) = 1 := by
    let a := (k : ℝ)
    have ha_nonneg : 0 ≤ a := by
      unfold a; exact mod_cast Nat.zero_le k
    let mid := a + 1 / (a + 1)
    let c := a + 1
    have ha1_pos : 0 < a + 1 := by nlinarith
    have ha_lt_mid : a < mid := by
      have hpos_div : 0 < 1 / (a + 1) := div_pos (by norm_num) ha1_pos
      unfold mid
      nlinarith
    have hmid_le_c : mid ≤ c := by
      have h_one_div_le_one : 1 / (a + 1) ≤ 1 := by
        have htemp : 1 / (a + 1) ≤ 1 / 1 :=
          (one_div_le_one_div ha1_pos (by norm_num : 0 < (1 : ℝ))).mpr (by nlinarith)
        simpa using htemp
      unfold mid c
      nlinarith
    have ha_lt_c : a < c := by nlinarith
    -- Piece 1: Ioo a mid, f = a+1
    have h_piece1_eq : Set.EqOn f (fun _ : ℝ => a + 1) (Ioo a mid) := by
      intro x hx
      rcases hx with ⟨hx_left, hx_right⟩
      have hx_nonneg : x ≥ 0 := by nlinarith
      have hn_floor_eq : (⌊x⌋₊ : ℝ) = (k : ℝ) := by
        have hn_eq' : (⌊x⌋₊ : ℕ) = k := by
          have hk1_pos : 0 < (k : ℝ) + 1 := by nlinarith
          have hk_le_x : (k : ℝ) ≤ x := by linarith
          have hx_lt_kp1 : x < (k : ℝ) + 1 := by
            have h_one_div : 1 / ((k : ℝ) + 1) ≤ (1 : ℝ) := by
              have htemp : 1 / ((k : ℝ) + 1) ≤ 1 / (1 : ℝ) :=
                (one_div_le_one_div hk1_pos (by norm_num : 0 < (1 : ℝ))).mpr (by nlinarith)
              simpa using htemp
            nlinarith
          apply Nat.floor_eq_on_Ico k x
          simp [Set.mem_Ico, hk_le_x, hx_lt_kp1]
        exact congrArg (fun t : ℕ => (t : ℝ)) hn_eq'
      have hn_eq : n x = (k : ℝ) := by dsimp [n]; exact hn_floor_eq
      have hx_ne_k : x ≠ (k : ℝ) := by linarith
      have hx_lt_kp1_div : x < (k : ℝ) + 1 / ((k : ℝ) + 1) := by
        dsimp [a, mid] at hx_right
        exact hx_right
      dsimp [f, n, a]
      rw [if_pos hx_nonneg]
      by_cases h_eq : x = n x
      · exfalso; exact hx_ne_k (h_eq.trans hn_eq)
      · rw [if_neg h_eq]
        by_cases h_lt : x < n x + 1 / (n x + 1)
        · rw [if_pos h_lt, hn_floor_eq]
        · exfalso; apply h_lt
          calc
            x < (k : ℝ) + 1 / ((k : ℝ) + 1) := hx_lt_kp1_div
            _ = n x + 1 / (n x + 1) := by rw [hn_eq]

    have h_piece1_int : IntegrableOn f (Ioo a mid) :=
      integrableOn_of_eq_const f (Ioo a mid) (a + 1) h_piece1_eq
    have h_piece1_integ : integ f (Ioo a mid) = 1 := by
      rw [integ_of_eq_const f (Ioo a mid) (a + 1) h_piece1_eq]
      have h_nonneg : 0 ≤ mid - a := by nlinarith
      have h_len : |(Ioo a mid : BoundedInterval)|ₗ = 1 / (a + 1) := by
        calc
          |(Ioo a mid : BoundedInterval)|ₗ = mid - a := by
            unfold BoundedInterval.length; simp [h_nonneg]
          _ = 1 / (a + 1) := by unfold mid; ring
      rw [h_len]
      field_simp [ha1_pos.ne.symm]
    -- Piece 2: Ico mid c, f = 0
    have h_piece2_eq : Set.EqOn f (fun _ : ℝ => 0) (Ico mid c) := by
      intro x hx
      rcases hx with ⟨hx_left, hx_right⟩
      have hx_nonneg : x ≥ 0 := by nlinarith
      have hn_floor_eq : (⌊x⌋₊ : ℝ) = (k : ℝ) := by
        have hn_eq' : (⌊x⌋₊ : ℕ) = k := by
          have hk1_pos : 0 < (k : ℝ) + 1 := by nlinarith
          have hk_le_x : (k : ℝ) ≤ x := by nlinarith
          have hx_lt_kp1 : x < (k : ℝ) + 1 := by nlinarith
          apply Nat.floor_eq_on_Ico k x
          simp [Set.mem_Ico, hk_le_x, hx_lt_kp1]
        exact congrArg (fun t : ℕ => (t : ℝ)) hn_eq'
      have hn_eq : n x = (k : ℝ) := by dsimp [n]; exact hn_floor_eq
      have hx_ne_k : x ≠ (k : ℝ) := by linarith
      have h_not_lt : ¬ x < (k : ℝ) + 1 / ((k : ℝ) + 1) := by
        dsimp [a, mid] at hx_left
        nlinarith
      dsimp [f, n, a]
      rw [if_pos hx_nonneg]
      by_cases h_eq : x = n x
      · rw [if_pos h_eq]
      · rw [if_neg h_eq]
        by_cases h_lt : x < n x + 1 / (n x + 1)
        · rw [if_pos h_lt]
          exfalso; apply h_not_lt
          calc
            x < n x + 1 / (n x + 1) := h_lt
            _ = (k : ℝ) + 1 / ((k : ℝ) + 1) := by rw [hn_eq]
        · rw [if_neg h_lt]
    have h_piece2_int : IntegrableOn f (Ico mid c) :=
      integrableOn_of_eq_const f (Ico mid c) 0 h_piece2_eq
    have h_piece2_integ : integ f (Ico mid c) = 0 := by
      rw [integ_of_eq_const f (Ico mid c) 0 h_piece2_eq, zero_mul]
    -- Piece 3: Icc c c, subsingleton (length 0)
    have h_len_cc : |(Icc c c : BoundedInterval)|ₗ = 0 := by
      unfold BoundedInterval.length; simp
    have h_piece3_int : IntegrableOn f (Icc c c) := (integ_on_subsingleton h_len_cc).1
    have h_piece3_integ : integ f (Icc c c) = 0 := (integ_on_subsingleton h_len_cc).2
    -- Join 1: Ioo a mid + Ico mid c → Ioo a c
    have h_join1 : (Ioo a c).joins (Ioo a mid) (Ico mid c) :=
      BoundedInterval.join_Ioo_Ico ha_lt_mid hmid_le_c
    rcases IntegrableOn.of_join h_join1 h_piece1_int h_piece2_int with ⟨h_int_Ioo_ac, h_eq_join1⟩
    have h_integ_Ioo_ac : integ f (Ioo a c) = 1 := by
      rw [h_eq_join1, h_piece1_integ, h_piece2_integ, add_zero]
    -- Join 2: Ioo a c + Icc c c → Ioc a c
    have h_join2 : (Ioc a c).joins (Ioo a c) (Icc c c) :=
      BoundedInterval.join_Ioo_Icc ha_lt_c (le_refl c)
    rcases IntegrableOn.of_join h_join2 h_int_Ioo_ac h_piece3_int with ⟨h_int_Ioc, h_eq_join2⟩
    have h_integ_Ioc : integ f (Ioc a c) = 1 := by
      rw [h_eq_join2, h_integ_Ioo_ac, h_piece3_integ, add_zero]
    exact ⟨h_int_Ioc, h_integ_Ioc⟩
  have h_integ_Icc_nat (k : ℕ) : IntegrableOn f (Icc (0 : ℝ) (k : ℝ)) ∧
      integ f (Icc (0 : ℝ) (k : ℝ)) = (k : ℝ) := by
    induction' k with m ih
    · -- base k = 0
      have hlen : |(Icc (0 : ℝ) (0 : ℝ))|ₗ = (0 : ℝ) := by
        unfold BoundedInterval.length; simp
      have h_int : IntegrableOn f (Icc (0 : ℝ) (0 : ℝ)) := (integ_on_subsingleton hlen).1
      have h_integ : integ f (Icc (0 : ℝ) (0 : ℝ)) = 0 := (integ_on_subsingleton hlen).2
      simpa using And.intro h_int h_integ
    · rcases ih with ⟨h_int_left, h_integ_left⟩
      rcases h_integ_Ioc m with ⟨h_int_right, h_integ_right⟩
      have h_join : (Icc (0 : ℝ) ((m : ℝ) + 1)).joins (Icc (0 : ℝ) (m : ℝ)) (Ioc (m : ℝ) ((m : ℝ) + 1)) :=
        BoundedInterval.join_Icc_Ioc (by exact_mod_cast Nat.zero_le m) (by nlinarith)
      rcases IntegrableOn.of_join h_join h_int_left h_int_right with ⟨h_int_k, h_eq⟩
      have h_integ_k : integ f (Icc (0 : ℝ) ((m : ℝ) + 1)) = (m : ℝ) + 1 := by
        rw [h_eq, h_integ_left, h_integ_right]
      simpa [Nat.cast_succ] using And.intro h_int_k h_integ_k
  have h_unbounded : ¬ ∃ M, ∀ N ≥ 0, integ f (Icc 0 N) ≤ M := by
    intro h
    rcases h with ⟨M, hM⟩
    rcases exists_nat_gt M with ⟨k, hk⟩
    have ⟨h_int_k, h_integ_k⟩ := h_integ_Icc_nat k
    have hk_bound : (k : ℝ) ≤ M := by
      have htemp := hM (k : ℝ) (by exact mod_cast Nat.zero_le k)
      rw [h_integ_k] at htemp
      exact htemp
    linarith
  exact ⟨f, h_nonneg, h_summable, h_unbounded⟩

/-- Second counterexample: series diverges but integrals are bounded. -/
example : ∃ (f:ℝ → ℝ), (∀ x ≥ 0, f x ≥ 0) ∧ ¬ Summable (fun n:ℕ ↦ f n) ∧ ∃ M, ∀ N ≥ 0, integ f (Icc 0 N) ≤ M := by
  let f : ℝ → ℝ := λ x =>
    if hx : x ≥ 0 then
      if (⌊x⌋ : ℝ) = x then (1 : ℝ) else (0 : ℝ)
    else 0
  have h_nonneg : ∀ x ≥ 0, f x ≥ 0 := by
    intro x hx
    dsimp [f]
    rw [if_pos hx]
    split <;> norm_num
  have h_not_summable : ¬ Summable (fun m : ℕ => f m) := by
    have h_f_m : ∀ m : ℕ, f m = 1 := by
      intro m
      dsimp [f]
      have hm_nonneg : (m : ℝ) ≥ 0 := by exact mod_cast Nat.zero_le m
      rw [if_pos hm_nonneg]
      simp
    have h_const : (fun m : ℕ => f m) = (fun _ : ℕ => (1 : ℝ)) := by ext m; exact h_f_m m
    rw [h_const, summable_const_iff]
    norm_num
  have h_integ_Ioc (k : ℕ) : IntegrableOn f (Ioc (k : ℝ) ((k : ℝ) + 1)) ∧
      integ f (Ioc (k : ℝ) ((k : ℝ) + 1)) = 0 := by
    let a := (k : ℝ)
    have ha_nonneg : 0 ≤ a := by
      unfold a; exact mod_cast Nat.zero_le k
    let c := a + 1
    have ha_lt_c : a < c := by nlinarith
    -- Piece 1: Ioo a c, f = 0 (no integers in the open interval)
    have h_piece1_eq : Set.EqOn f (fun _ : ℝ => 0) (Ioo a c) := by
      intro x hx
      rcases hx with ⟨hx_left, hx_right⟩
      dsimp [f]
      have hx_nonneg : x ≥ 0 := by nlinarith
      rw [if_pos hx_nonneg]
      have h_floor_ne : (⌊x⌋ : ℝ) ≠ x := by
        have h_floor_eq : ⌊x⌋ = (k : ℤ) := by
          apply Int.floor_eq_iff.mpr
          exact ⟨by exact_mod_cast hx_left.le, hx_right⟩
        intro h_eq
        have h_cast : (⌊x⌋ : ℝ) = (k : ℝ) := by exact_mod_cast h_floor_eq
        have : (k : ℝ) = x := h_cast ▸ h_eq
        linarith
      simp [h_floor_ne]
    have h_piece1_int : IntegrableOn f (Ioo a c) :=
      integrableOn_of_eq_const f (Ioo a c) 0 h_piece1_eq
    have h_piece1_integ : integ f (Ioo a c) = 0 := by
      rw [integ_of_eq_const f (Ioo a c) 0 h_piece1_eq, zero_mul]
    -- Piece 2: Icc c c, subsingleton (length 0)
    have h_len_cc : |(Icc c c : BoundedInterval)|ₗ = 0 := by
      unfold BoundedInterval.length; simp
    have h_piece2_int : IntegrableOn f (Icc c c) := (integ_on_subsingleton h_len_cc).1
    have h_piece2_integ : integ f (Icc c c) = 0 := (integ_on_subsingleton h_len_cc).2
    -- Join: Ioo a c + Icc c c → Ioc a c
    have h_join : (Ioc a c).joins (Ioo a c) (Icc c c) :=
      BoundedInterval.join_Ioo_Icc ha_lt_c (le_refl c)
    rcases IntegrableOn.of_join h_join h_piece1_int h_piece2_int with ⟨h_int_Ioc, h_eq⟩
    have h_integ_Ioc : integ f (Ioc a c) = 0 := by
      rw [h_eq, h_piece1_integ, h_piece2_integ, add_zero]
    exact ⟨h_int_Ioc, h_integ_Ioc⟩
  have h_integ_Icc_nat (k : ℕ) : IntegrableOn f (Icc (0 : ℝ) (k : ℝ)) ∧
      integ f (Icc (0 : ℝ) (k : ℝ)) = 0 := by
    induction' k with m ih
    · -- base k = 0
      have hlen : |(Icc (0 : ℝ) (0 : ℝ))|ₗ = (0 : ℝ) := by
        unfold BoundedInterval.length; simp
      have h_int : IntegrableOn f (Icc (0 : ℝ) (0 : ℝ)) := (integ_on_subsingleton hlen).1
      have h_integ : integ f (Icc (0 : ℝ) (0 : ℝ)) = 0 := (integ_on_subsingleton hlen).2
      simpa using And.intro h_int h_integ
    · rcases ih with ⟨h_int_left, h_integ_left⟩
      rcases h_integ_Ioc m with ⟨h_int_right, h_integ_right⟩
      have h_join : (Icc (0 : ℝ) ((m : ℝ) + 1)).joins (Icc (0 : ℝ) (m : ℝ)) (Ioc (m : ℝ) ((m : ℝ) + 1)) :=
        BoundedInterval.join_Icc_Ioc (by exact_mod_cast Nat.zero_le m) (by nlinarith)
      rcases IntegrableOn.of_join h_join h_int_left h_int_right with ⟨h_int_k, h_eq⟩
      have h_integ_k : integ f (Icc (0 : ℝ) ((m : ℝ) + 1)) = 0 := by
        rw [h_eq, h_integ_left, h_integ_right, add_zero]
      simpa [Nat.cast_succ] using And.intro h_int_k h_integ_k
  have h_integ_bound : ∃ M, ∀ N ≥ 0, integ f (Icc 0 N) ≤ M := by
    refine ⟨0, λ N hN => ?_⟩
    rcases exists_nat_ge N with ⟨k, hkN⟩
    have ⟨h_int_k, h_integ_k⟩ := h_integ_Icc_nat k
    have h_int_N : IntegrableOn f (Icc (0 : ℝ) N) := by
      have h_sub : (Icc (0 : ℝ) N) ⊆ (Icc (0 : ℝ) (k : ℝ)) := by
        intro x hx
        have hx_nonneg : 0 ≤ x := hx.1
        have hx_le_k : x ≤ (k : ℝ) := le_trans hx.2 (by exact_mod_cast hkN)
        simpa using And.intro hx_nonneg hx_le_k
      exact IntegrableOn.mono' h_sub h_int_k
    have h_nonneg_N : 0 ≤ integ f (Icc (0 : ℝ) N) := by
      have h_nonneg_on : ∀ x ∈ (Icc (0 : ℝ) N : Set ℝ), 0 ≤ f x := by
        intro x hx; exact h_nonneg x hx.1
      exact IntegrableOn.nonneg h_int_N h_nonneg_on
    have h_integ_N_le_zero : integ f (Icc (0 : ℝ) N) ≤ 0 := by
      have h_join : (Icc (0 : ℝ) (k : ℝ)).joins (Icc (0 : ℝ) N) (Ioc N (k : ℝ)) :=
        BoundedInterval.join_Icc_Ioc hN (by exact_mod_cast hkN)
      have h_int_right : IntegrableOn f (Ioc N (k : ℝ)) := by
        have h_sub : (Ioc N (k : ℝ)) ⊆ (Icc (0 : ℝ) (k : ℝ)) := by
          intro x hx
          have hx_nonneg : 0 ≤ x := by
            have hx_gt_N : N < x := by simpa using hx.1
            nlinarith
          have hx_le_k : x ≤ (k : ℝ) := by
            simpa using hx.2
          simpa using And.intro hx_nonneg hx_le_k
        exact IntegrableOn.mono' h_sub h_int_k
      rcases IntegrableOn.of_join h_join h_int_N h_int_right with ⟨_, h_eq⟩
      have h_eq2 : integ f (Icc (0 : ℝ) N) + integ f (Ioc N (k : ℝ)) = 0 := by
        linarith
      have h_nonneg_right : 0 ≤ integ f (Ioc N (k : ℝ)) :=
        IntegrableOn.nonneg h_int_right (λ x hx => h_nonneg x (by
          have hx_gt_N : N < x := by simpa using hx.1
          nlinarith))
      nlinarith
    nlinarith
  exact ⟨f, h_nonneg, h_not_summable, h_integ_bound⟩

end Chapter11
