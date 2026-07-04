import Mathlib.Tactic
import Analysis.Section_9_6
import Analysis.Section_11_2

/-!
# Analysis I, Section 11.3: Upper and lower Riemann integrals

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- The upper and lower Riemann integral; the Riemann integral.
- Upper and lower Riemann sums.

-/

namespace Chapter11
open BoundedInterval Chapter9

/-- Definition 11.3.1 (Majorization of functions) -/
abbrev MajorizesOn (g f:ℝ → ℝ) (I: BoundedInterval) : Prop := ∀ x ∈ (I:Set ℝ), f x ≤ g x

abbrev MinorizesOn (g f:ℝ → ℝ) (I: BoundedInterval) : Prop := ∀ x ∈ (I:Set ℝ), g x ≤ f x

theorem MinorizesOn.iff (g f:ℝ → ℝ) (I: BoundedInterval) : MinorizesOn g f I ↔ MajorizesOn f g I := by rfl

/-- Definition 11.3.2 (Upper and lower Riemann integrals ). -/
noncomputable abbrev upper_integral (f:ℝ → ℝ) (I: BoundedInterval) : ℝ :=
  sInf ((PiecewiseConstantOn.integ · I) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I})

noncomputable abbrev lower_integral (f:ℝ → ℝ) (I: BoundedInterval) : ℝ :=
  sSup ((PiecewiseConstantOn.integ · I) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I})

theorem upper_integral_congr {f g:ℝ → ℝ} {I: BoundedInterval} (h: Set.EqOn f g I) :
  upper_integral f I = upper_integral g I := by
  simp [upper_integral]; congr! 2; ext; simp; grind

theorem lower_integral_congr {f g:ℝ → ℝ} {I: BoundedInterval} (h: Set.EqOn f g I) :
  lower_integral f I = lower_integral g I := by
  simp [lower_integral]; congr! 2; ext; simp; grind

lemma integral_bound_upper_of_bounded {f:ℝ → ℝ} {M:ℝ} {I: BoundedInterval} (h: ∀ x ∈ (I:Set ℝ), |f x| ≤ M) : M * |I|ₗ ∈ (PiecewiseConstantOn.integ · I) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I} := by
  simp
  refine' ⟨ fun _ ↦ M , ⟨ ⟨ _, _ ⟩, PiecewiseConstantOn.integ_const _ _ ⟩ ⟩
  . grind [abs_le']
  apply (ConstantOn.of_const (c := M) _).piecewiseConstantOn; simp

lemma integral_bound_lower_of_bounded {f:ℝ → ℝ} {M:ℝ} {I: BoundedInterval} (h: ∀ x ∈ (I:Set ℝ), |f x| ≤ M) : -M * |I|ₗ ∈ (PiecewiseConstantOn.integ · I) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I} := by
  simp
  refine' ⟨ fun _ ↦ -M , ⟨ ⟨ _, _ ⟩, by convert PiecewiseConstantOn.integ_const _ _ using 1; simp ⟩ ⟩
  . grind [abs_le']
  exact (ConstantOn.of_const (c := -M) (by simp)).piecewiseConstantOn

lemma integral_bound_upper_nonempty {f:ℝ → ℝ} {I: BoundedInterval} (h: BddOn f I) : ((PiecewiseConstantOn.integ · I) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I}).Nonempty :=
  ⟨ _, integral_bound_upper_of_bounded h.choose_spec ⟩

lemma integral_bound_lower_nonempty {f:ℝ → ℝ} {I: BoundedInterval} (h: BddOn f I) : ((PiecewiseConstantOn.integ · I) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I}).Nonempty :=
  ⟨ _, integral_bound_lower_of_bounded h.choose_spec ⟩

lemma integral_bound_lower_le_upper {f:ℝ → ℝ} {I: BoundedInterval} {a b:ℝ}
  (ha: a ∈ (PiecewiseConstantOn.integ · I) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I})
  (hb: b ∈ (PiecewiseConstantOn.integ · I) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I})
  : b ≤ a:= by
    obtain ⟨ g, ⟨ ⟨ hmaj, hgp⟩, rfl ⟩ ⟩ := ha
    obtain ⟨ h, ⟨ ⟨ hmin, hhp⟩, rfl ⟩ ⟩ := hb
    apply hhp.integ_mono _ hgp; intro x hx; linarith [hmin _ hx, hmaj _ hx]

lemma integral_bound_below {f:ℝ → ℝ} {I: BoundedInterval} (h: BddOn f I) :
  BddBelow ((PiecewiseConstantOn.integ · I) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I}) := by
    rw [bddBelow_def]; use (integral_bound_lower_nonempty h).some
    intro a ha; exact integral_bound_lower_le_upper ha (integral_bound_lower_nonempty h).some_mem

lemma integral_bound_above {f:ℝ → ℝ} {I: BoundedInterval} (h: BddOn f I) :
  BddAbove ((PiecewiseConstantOn.integ · I) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I}) := by
    rw [bddAbove_def]; use (integral_bound_upper_nonempty h).some
    intro b hb; exact integral_bound_lower_le_upper (integral_bound_upper_nonempty h).some_mem hb

/-- Lemma 11.3.3.  The proof has been reorganized somewhat from the textbook. -/
lemma le_lower_integral {f:ℝ → ℝ} {I: BoundedInterval} {M:ℝ} (h: ∀ x ∈ (I:Set ℝ), |f x| ≤ M) :
  -M * |I|ₗ ≤ lower_integral f I :=
  le_csSup (integral_bound_above (BddOn.of_bounded h)) (integral_bound_lower_of_bounded h)

lemma lower_integral_le_upper {f:ℝ → ℝ} {I: BoundedInterval} (h: BddOn f I) :
  lower_integral f I ≤ upper_integral f I := by
  apply csSup_le (integral_bound_lower_nonempty h)
  intros
  apply le_csInf (integral_bound_upper_nonempty h)
  intros
  solve_by_elim [integral_bound_lower_le_upper]

lemma upper_integral_le {f:ℝ → ℝ} {I: BoundedInterval} {M:ℝ} (h: ∀ x ∈ (I:Set ℝ), |f x| ≤ M) :
  upper_integral f I ≤ M * |I|ₗ :=
  csInf_le (integral_bound_below (BddOn.of_bounded h)) (integral_bound_upper_of_bounded h)

lemma upper_integral_le_integ {f g:ℝ → ℝ} {I: BoundedInterval} (hf: BddOn f I)
  (hfg: MajorizesOn g f I) (hg: PiecewiseConstantOn g I) :
  upper_integral f I ≤ hg.integ' := by
  apply csInf_le (integral_bound_below hf) _
  use g; simpa [hg]

lemma integ_le_lower_integral {f h:ℝ → ℝ} {I: BoundedInterval} (hf: BddOn f I)
  (hfh: MinorizesOn h f I) (hg: PiecewiseConstantOn h I) :
  hg.integ' ≤ lower_integral f I := by
  apply le_csSup (integral_bound_above hf) _
  use h; simpa [hg]

lemma lt_of_gt_upper_integral {f:ℝ → ℝ} {I: BoundedInterval} (hf: BddOn f I)
  {X:ℝ} (hX: upper_integral f I < X ) :
  ∃ g, MajorizesOn g f I ∧ PiecewiseConstantOn g I ∧ PiecewiseConstantOn.integ g I < X := by
  choose Y hY hYX using exists_lt_of_csInf_lt (integral_bound_upper_nonempty hf) hX
  simp at hY; peel hY; simp_all; tauto

lemma gt_of_lt_lower_integral {f:ℝ → ℝ} {I: BoundedInterval} (hf: BddOn f I)
  {X:ℝ} (hX: X < lower_integral f I) :
  ∃ h, MinorizesOn h f I ∧ PiecewiseConstantOn h I ∧ X < PiecewiseConstantOn.integ h I := by
  choose Y hY hYX using exists_lt_of_lt_csSup (integral_bound_lower_nonempty hf) hX
  simp at hY; peel hY; simp_all; tauto

/-- Definition 11.3.4 (Riemann integral)
As we permit junk values, the simplest definition for the Riemann integral is the upper integral. -/
noncomputable abbrev integ (f:ℝ → ℝ) (I: BoundedInterval) : ℝ := upper_integral f I

theorem integ_congr {f g:ℝ → ℝ} {I: BoundedInterval} (h: Set.EqOn f g I) :
  integ f I = integ g I := upper_integral_congr h

noncomputable abbrev IntegrableOn (f:ℝ → ℝ) (I: BoundedInterval) : Prop :=
  BddOn f I ∧ lower_integral f I = upper_integral f I

/-- Lemma 11.3.7 / Exercise 11.3.3 -/
theorem integ_of_piecewise_const {f:ℝ → ℝ} {I: BoundedInterval} (hf: PiecewiseConstantOn f I) :
  IntegrableOn f I ∧ integ f I = hf.integ' := by
  have hmaj : MajorizesOn f f I := λ x hx ↦ le_rfl
  have hmin : MinorizesOn f f I := λ x hx ↦ le_rfl
  have hbdd : BddOn f I := by
    rcases hf with ⟨P, hP⟩
    by_cases hI_nonempty : (I : Set ℝ).Nonempty
    · rcases hI_nonempty with ⟨x0, hx0⟩
      rcases P.exists_unique x0 hx0 with ⟨J0, ⟨hJ0mem, _⟩, _⟩
      have h_intervals_nonempty : P.intervals.Nonempty := ⟨J0, hJ0mem⟩
      let vals : Finset ℝ := Finset.image (λ (J : BoundedInterval) => constant_value_on f (J : Set ℝ)) P.intervals
      have h_vals_nonempty : vals.Nonempty := by
        have h_val0 : constant_value_on f (J0 : Set ℝ) ∈ vals :=
          Finset.mem_image.mpr ⟨J0, hJ0mem, rfl⟩
        exact ⟨constant_value_on f (J0 : Set ℝ), h_val0⟩
      use Finset.sup' vals h_vals_nonempty (λ v => |v|)
      intro x hx
      rcases P.exists_unique x hx with ⟨J, ⟨hJmem, hxJ⟩, _⟩
      have h_const : ConstantOn f (J : Set ℝ) := hP J hJmem
      have hfx_eq : f x = constant_value_on f (J : Set ℝ) := h_const.eq hxJ
      rw [hfx_eq]
      have h_val_mem : constant_value_on f (J : Set ℝ) ∈ vals :=
        Finset.mem_image.mpr ⟨J, hJmem, rfl⟩
      exact Finset.le_sup' (λ v : ℝ => |v|) h_val_mem
    · use 0; intro x hx; exfalso; exact hI_nonempty ⟨x, hx⟩
  have hmem_upper : hf.integ' ∈ (PiecewiseConstantOn.integ · I) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I} := by
    refine ⟨f, ⟨hmaj, hf⟩, rfl⟩
  have hmem_lower : hf.integ' ∈ (PiecewiseConstantOn.integ · I) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I} := by
    refine ⟨f, ⟨hmin, hf⟩, rfl⟩
  have h_upper_integ_le : upper_integral f I ≤ hf.integ' :=
    csInf_le (integral_bound_below hbdd) hmem_upper
  have h_lower_integ_ge : hf.integ' ≤ lower_integral f I :=
    le_csSup (integral_bound_above hbdd) hmem_lower
  have h_lower_le_upper : lower_integral f I ≤ upper_integral f I :=
    lower_integral_le_upper hbdd
  have h_eq : lower_integral f I = upper_integral f I := by
    apply le_antisymm h_lower_le_upper
    calc
      upper_integral f I ≤ hf.integ' := h_upper_integ_le
      _ ≤ lower_integral f I := h_lower_integ_ge
  have h_upper_integ_eq : upper_integral f I = hf.integ' :=
    le_antisymm h_upper_integ_le (calc
      hf.integ' ≤ lower_integral f I := h_lower_integ_ge
      _ = upper_integral f I := h_eq)
  have h_integ_eq : integ f I = hf.integ' := calc
    integ f I = upper_integral f I := rfl
    _ = hf.integ' := h_upper_integ_eq
  exact ⟨⟨hbdd, h_eq⟩, h_integ_eq⟩

/-- Remark 11.3.8 -/
theorem integ_on_subsingleton {f:ℝ → ℝ} {I: BoundedInterval} (hI: |I|ₗ = 0) :
  IntegrableOn f I ∧ integ f I = 0 := by
  observe : Subsingleton I.toSet
  observe hconst : ConstantOn f I
  convert integ_of_piecewise_const hconst.piecewiseConstantOn
  simp [PiecewiseConstantOn.integ_const' hconst, hI]

/-- Definition 11.3.9 (Riemann sums).  The restriction to positive length J is not needed thanks to various junk value conventions. -/
noncomputable abbrev upper_riemann_sum (f:ℝ → ℝ) {I: BoundedInterval} (P: Partition I) : ℝ :=
  ∑ J ∈ P.intervals, (sSup (f '' (J:Set ℝ))) * |J|ₗ

noncomputable abbrev lower_riemann_sum (f:ℝ → ℝ) {I: BoundedInterval} (P: Partition I) : ℝ :=
  ∑ J ∈ P.intervals, (sInf (f '' (J:Set ℝ))) * |J|ₗ

/-- Lemma 11.3.11 / Exercise 11.3.4 -/
theorem upper_riemann_sum_le {f g: ℝ → ℝ} {I:BoundedInterval} (P: Partition I)
  (hgf: MajorizesOn g f I) (hg: PiecewiseConstantWith g P) :
  upper_riemann_sum f P ≤ integ g I := by
  have hg_pwc : PiecewiseConstantOn g I := ⟨P, hg⟩
  have h_integ_eq : integ g I = PiecewiseConstantWith.integ g P := by
    have h_eq_upper : integ g I = hg_pwc.integ' := (integ_of_piecewise_const hg_pwc).2
    have h_integ_def : hg_pwc.integ' = PiecewiseConstantOn.integ g I := rfl
    have h_pwc_def : PiecewiseConstantOn.integ g I = PiecewiseConstantWith.integ g P :=
      PiecewiseConstantOn.integ_def hg
    rw [h_eq_upper, h_integ_def, h_pwc_def]
  have h_each_J : ∀ J ∈ P, (sSup (f '' (J : Set ℝ))) * |J|ₗ ≤ (constant_value_on g (J : Set ℝ)) * |J|ₗ := by
    intro J hJ
    by_cases hJ_nonempty : (J : Set ℝ).Nonempty
    · have h_sup_le : sSup (f '' (J : Set ℝ)) ≤ constant_value_on g (J : Set ℝ) := by
        have h_img_nonempty : (f '' (J : Set ℝ)).Nonempty := by
          rcases hJ_nonempty with ⟨x, hx⟩; exact ⟨f x, x, hx, rfl⟩
        have h_bound : ∀ y ∈ f '' (J : Set ℝ), y ≤ constant_value_on g (J : Set ℝ) := by
          intro y hy; rcases hy with ⟨x, hx, rfl⟩
          have h_const : ConstantOn g (J : Set ℝ) := hg J hJ
          have h_gx_eq : g x = constant_value_on g (J : Set ℝ) := h_const.eq hx
          rw [← h_gx_eq]
          exact hgf x ((P.contains J hJ) x hx)
        exact csSup_le h_img_nonempty h_bound
      have h_len_nonneg : 0 ≤ |J|ₗ := BoundedInterval.length_nonneg _
      exact mul_le_mul_of_nonneg_right h_sup_le h_len_nonneg
    · have h_length_zero : |J|ₗ = 0 := BoundedInterval.length_of_empty (Set.not_nonempty_iff_eq_empty.mp hJ_nonempty)
      simp [h_length_zero]
  calc
    upper_riemann_sum f P = ∑ J ∈ P.intervals, (sSup (f '' (J : Set ℝ))) * |J|ₗ := rfl
    _ ≤ ∑ J ∈ P.intervals, (constant_value_on g (J : Set ℝ)) * |J|ₗ := Finset.sum_le_sum h_each_J
    _ = PiecewiseConstantWith.integ g P := rfl
    _ = integ g I := by rw [h_integ_eq]

theorem lower_riemann_sum_ge {f h: ℝ → ℝ} {I:BoundedInterval} (P: Partition I)
  (hfh: MinorizesOn h f I) (hg: PiecewiseConstantWith h P) :
  integ h I ≤ lower_riemann_sum f P := by
  have hh_pwc : PiecewiseConstantOn h I := ⟨P, hg⟩
  have h_integ_eq : integ h I = PiecewiseConstantWith.integ h P := by
    have h_eq_upper : integ h I = hh_pwc.integ' := (integ_of_piecewise_const hh_pwc).2
    have h_integ_def : hh_pwc.integ' = PiecewiseConstantOn.integ h I := rfl
    have h_pwc_def : PiecewiseConstantOn.integ h I = PiecewiseConstantWith.integ h P :=
      PiecewiseConstantOn.integ_def hg
    rw [h_eq_upper, h_integ_def, h_pwc_def]
  have h_each_J : ∀ J ∈ P, (constant_value_on h (J : Set ℝ)) * |J|ₗ ≤ (sInf (f '' (J : Set ℝ))) * |J|ₗ := by
    intro J hJ
    by_cases hJ_nonempty : (J : Set ℝ).Nonempty
    · have h_inf_ge : constant_value_on h (J : Set ℝ) ≤ sInf (f '' (J : Set ℝ)) := by
        have h_img_nonempty : (f '' (J : Set ℝ)).Nonempty := by
          rcases hJ_nonempty with ⟨x, hx⟩; exact ⟨f x, x, hx, rfl⟩
        have h_bound : ∀ y ∈ f '' (J : Set ℝ), constant_value_on h (J : Set ℝ) ≤ y := by
          intro y hy; rcases hy with ⟨x, hx, rfl⟩
          have h_const : ConstantOn h (J : Set ℝ) := hg J hJ
          have h_hx_eq : h x = constant_value_on h (J : Set ℝ) := h_const.eq hx
          rw [← h_hx_eq]
          exact hfh x ((P.contains J hJ) x hx)
        exact le_csInf h_img_nonempty h_bound
      have h_len_nonneg : 0 ≤ |J|ₗ := BoundedInterval.length_nonneg _
      exact mul_le_mul_of_nonneg_right h_inf_ge h_len_nonneg
    · have h_length_zero : |J|ₗ = 0 := BoundedInterval.length_of_empty (Set.not_nonempty_iff_eq_empty.mp hJ_nonempty)
      simp [h_length_zero]
  calc
    integ h I = PiecewiseConstantWith.integ h P := by rw [h_integ_eq]
    _ = ∑ J ∈ P.intervals, (constant_value_on h (J : Set ℝ)) * |J|ₗ := rfl
    _ ≤ ∑ J ∈ P.intervals, (sInf (f '' (J : Set ℝ))) * |J|ₗ := Finset.sum_le_sum h_each_J
    _ = lower_riemann_sum f P := rfl

/-- Proposition 11.3.12 / Exercise 11.3.5 -/
theorem upper_integ_le_upper_sum {f:ℝ → ℝ} {I:BoundedInterval} (hf: BddOn f I)
  (P: Partition I): upper_integral f I ≤ upper_riemann_sum f P := by
  classical
    let g : ℝ → ℝ := λ x ↦
      if hxI : x ∈ (I : Set ℝ) then
        sSup (f '' (((P.exists_unique x hxI).choose) : Set ℝ))
      else 0
    have hg_majorizes : MajorizesOn g f I := by
      intro x hx
      rcases P.exists_unique x hx with ⟨J, ⟨hJ_mem, hxJ⟩, huniq⟩
      have h_fx_img : f x ∈ f '' (J : Set ℝ) := ⟨x, hxJ, rfl⟩
      have h_bdd_above : BddAbove (f '' (J : Set ℝ)) := by
        rcases hf with ⟨M, hM⟩
        refine ⟨M, λ y hy => ?_⟩
        rcases hy with ⟨x', hx', rfl⟩
        have hx'I : x' ∈ (I : Set ℝ) := (P.contains J hJ_mem) x' hx'
        have h_abs : |f x'| ≤ M := hM x' hx'I
        nlinarith [abs_le.mp h_abs]
      have h_fx_le_sup : f x ≤ sSup (f '' (J : Set ℝ)) := le_csSup h_bdd_above h_fx_img
      dsimp [g]
      rw [dif_pos hx]
      have hJ_eq : (P.exists_unique x hx).choose = J :=
        huniq ((P.exists_unique x hx).choose) ((P.exists_unique x hx).choose_spec).1
      rw [hJ_eq]
      exact h_fx_le_sup
    have hg_pwc : PiecewiseConstantWith g P := by
      intro J hJ
      apply ConstantOn.of_const
      intro x hx
      have hxI : x ∈ (I : Set ℝ) := (P.contains J hJ) x hx
      rcases P.exists_unique x hxI with ⟨J', ⟨hJ'_mem, hxJ'⟩, huniq⟩
      have hJ'_eq : J' = J := (huniq J ⟨hJ, hx⟩).symm
      dsimp [g]
      rw [dif_pos hxI]
      have hJ_eq : (P.exists_unique x hxI).choose = J' :=
        huniq ((P.exists_unique x hxI).choose) ((P.exists_unique x hxI).choose_spec).1
      rw [hJ_eq, hJ'_eq]
    have hg_pwc_on : PiecewiseConstantOn g I := ⟨P, hg_pwc⟩
    have h_integ_eq : PiecewiseConstantOn.integ g I = upper_riemann_sum f P := by
      rw [PiecewiseConstantOn.integ_def hg_pwc]
      dsimp [PiecewiseConstantWith.integ, upper_riemann_sum]
      refine Finset.sum_congr rfl (λ J hJ => ?_)
      by_cases hJ_nonempty : (J : Set ℝ).Nonempty
      · have h_const_val : constant_value_on g (J : Set ℝ) = sSup (f '' (J : Set ℝ)) := by
          apply ConstantOn.const_eq hJ_nonempty
          intro x hx
          have hxI : x ∈ (I : Set ℝ) := (P.contains J hJ) x hx
          rcases P.exists_unique x hxI with ⟨J', ⟨hJ'_mem, hxJ'⟩, huniq⟩
          have hJ'_eq : J' = J := (huniq J ⟨hJ, hx⟩).symm
          dsimp [g]
          rw [dif_pos hxI]
          have hJ_eq : (P.exists_unique x hxI).choose = J' :=
            huniq ((P.exists_unique x hxI).choose) ((P.exists_unique x hxI).choose_spec).1
          rw [hJ_eq, hJ'_eq]
        simp [h_const_val]
      · have h_length_zero : |J|ₗ = 0 := BoundedInterval.length_of_empty (Set.not_nonempty_iff_eq_empty.mp hJ_nonempty)
        simp [h_length_zero]
    have hmem : upper_riemann_sum f P ∈ (PiecewiseConstantOn.integ · I) '' {g' | MajorizesOn g' f I ∧ PiecewiseConstantOn g' I} := by
      rw [← h_integ_eq]
      exact ⟨g, ⟨hg_majorizes, hg_pwc_on⟩, rfl⟩
    exact csInf_le (integral_bound_below hf) hmem

theorem upper_integ_eq_inf_upper_sum {f:ℝ → ℝ} {I:BoundedInterval} (hf: BddOn f I) :
  upper_integral f I = sInf (.range (fun P : Partition I ↦ upper_riemann_sum f P)) := by
  set S := Set.range (fun P : Partition I => upper_riemann_sum f P) with hS
  have h_bdd_below : BddBelow S := by
    rcases hf with ⟨M, hM⟩
    refine ⟨-M * |I|ₗ, λ x hx => ?_⟩
    rcases hx with ⟨P, rfl⟩
    have h_term : ∀ J ∈ P, (-M) * |J|ₗ ≤ (sSup (f '' (J : Set ℝ))) * |J|ₗ := by
      intro J hJ
      have h_len_nonneg : 0 ≤ |J|ₗ := BoundedInterval.length_nonneg _
      by_cases hJ_nonempty : (J : Set ℝ).Nonempty
      · rcases hJ_nonempty with ⟨x, hxJ⟩
        have hxI : x ∈ (I : Set ℝ) := (P.contains J hJ) x hxJ
        have h_abs : |f x| ≤ M := hM x hxI
        have h_fx_ge_neg_M : -M ≤ f x := by nlinarith [abs_le.mp h_abs]
        have h_bdd_above : BddAbove (f '' (J : Set ℝ)) := by
          refine ⟨M, λ y hy => ?_⟩
          rcases hy with ⟨x', hx', rfl⟩
          have hx'I : x' ∈ (I : Set ℝ) := (P.contains J hJ) x' hx'
          have h_abs' : |f x'| ≤ M := hM x' hx'I
          nlinarith [abs_le.mp h_abs']
        have h_img_mem : f x ∈ f '' (J : Set ℝ) := ⟨x, hxJ, rfl⟩
        have h_negM_le_sup : -M ≤ sSup (f '' (J : Set ℝ)) :=
          le_trans h_fx_ge_neg_M (le_csSup h_bdd_above h_img_mem)
        exact mul_le_mul_of_nonneg_right h_negM_le_sup h_len_nonneg
      · have h_len_zero : |J|ₗ = 0 := BoundedInterval.length_of_empty (Set.not_nonempty_iff_eq_empty.mp hJ_nonempty)
        simp [h_len_zero]
    calc
      (-M) * |I|ₗ = (-M) * (∑ J ∈ P.intervals, |J|ₗ) := by rw [Partition.sum_of_length I P]
      _ = ∑ J ∈ P.intervals, (-M) * |J|ₗ := by rw [Finset.mul_sum]
      _ ≤ ∑ J ∈ P.intervals, (sSup (f '' (J : Set ℝ))) * |J|ₗ := Finset.sum_le_sum h_term
      _ = upper_riemann_sum f P := rfl
  have h_nonempty : S.Nonempty := by
    refine ⟨upper_riemann_sum f (⊥ : Partition I), ?_⟩
    simp [S]
  apply le_antisymm
  · -- upper_integral f I ≤ sInf S
    apply le_csInf h_nonempty
    intro x hx
    rcases hx with ⟨P, rfl⟩
    exact upper_integ_le_upper_sum hf P
  · -- sInf S ≤ upper_integral f I
    have h_le_all_T : ∀ y ∈ (PiecewiseConstantOn.integ · I) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I}, sInf S ≤ y := by
      intro y hy
      rcases hy with ⟨g, ⟨hmaj, hg⟩, rfl⟩
      rcases hg with ⟨P, hg_pcw⟩
      have hsum : upper_riemann_sum f P ≤ PiecewiseConstantOn.integ g I := by
        have hg_pwc_on : PiecewiseConstantOn g I := ⟨P, hg_pcw⟩
        have hsum' : upper_riemann_sum f P ≤ integ g I :=
          upper_riemann_sum_le P hmaj hg_pcw
        have h_eq : integ g I = PiecewiseConstantOn.integ g I :=
          (integ_of_piecewise_const hg_pwc_on).2
        rw [h_eq] at hsum'
        exact hsum'
      have h_sInf_le_sum : sInf S ≤ upper_riemann_sum f P := csInf_le h_bdd_below (by simp [S])
      calc
        sInf S ≤ upper_riemann_sum f P := h_sInf_le_sum
        _ ≤ PiecewiseConstantOn.integ g I := hsum
    have h_T_nonempty : ((PiecewiseConstantOn.integ · I) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I}).Nonempty :=
      integral_bound_upper_nonempty hf
    have h_eq_ui : upper_integral f I = sInf ((PiecewiseConstantOn.integ · I) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I}) := rfl
    rw [h_eq_ui]
    exact le_csInf h_T_nonempty h_le_all_T

theorem lower_integ_ge_lower_sum {f:ℝ → ℝ} {I:BoundedInterval} (hf: BddOn f I)
  (P: Partition I): lower_riemann_sum f P ≤ lower_integral f I := by
  classical
    let g : ℝ → ℝ := λ x ↦
      if hxI : x ∈ (I : Set ℝ) then
        sInf (f '' (((P.exists_unique x hxI).choose) : Set ℝ))
      else 0
    have hg_minorizes : MinorizesOn g f I := by
      intro x hx
      rcases P.exists_unique x hx with ⟨J, ⟨hJ_mem, hxJ⟩, huniq⟩
      have h_fx_img : f x ∈ f '' (J : Set ℝ) := ⟨x, hxJ, rfl⟩
      have h_bdd_below : BddBelow (f '' (J : Set ℝ)) := by
        rcases hf with ⟨M, hM⟩
        refine ⟨-M, λ y hy => ?_⟩
        rcases hy with ⟨x', hx', rfl⟩
        have hx'I : x' ∈ (I : Set ℝ) := (P.contains J hJ_mem) x' hx'
        have h_abs : |f x'| ≤ M := hM x' hx'I
        nlinarith [abs_le.mp h_abs]
      have h_inf_le_fx : sInf (f '' (J : Set ℝ)) ≤ f x := csInf_le h_bdd_below h_fx_img
      dsimp [g]
      rw [dif_pos hx]
      have hJ_eq : (P.exists_unique x hx).choose = J :=
        huniq ((P.exists_unique x hx).choose) ((P.exists_unique x hx).choose_spec).1
      rw [hJ_eq]
      exact h_inf_le_fx
    have hg_pwc : PiecewiseConstantWith g P := by
      intro J hJ
      apply ConstantOn.of_const
      intro x hx
      have hxI : x ∈ (I : Set ℝ) := (P.contains J hJ) x hx
      rcases P.exists_unique x hxI with ⟨J', ⟨hJ'_mem, hxJ'⟩, huniq⟩
      have hJ'_eq : J' = J := (huniq J ⟨hJ, hx⟩).symm
      dsimp [g]
      rw [dif_pos hxI]
      have hJ_eq : (P.exists_unique x hxI).choose = J' :=
        huniq ((P.exists_unique x hxI).choose) ((P.exists_unique x hxI).choose_spec).1
      rw [hJ_eq, hJ'_eq]
    have hg_pwc_on : PiecewiseConstantOn g I := ⟨P, hg_pwc⟩
    have h_integ_eq : PiecewiseConstantOn.integ g I = lower_riemann_sum f P := by
      rw [PiecewiseConstantOn.integ_def hg_pwc]
      dsimp [PiecewiseConstantWith.integ, lower_riemann_sum]
      refine Finset.sum_congr rfl (λ J hJ => ?_)
      by_cases hJ_nonempty : (J : Set ℝ).Nonempty
      · have h_const_val : constant_value_on g (J : Set ℝ) = sInf (f '' (J : Set ℝ)) := by
          apply ConstantOn.const_eq hJ_nonempty
          intro x hx
          have hxI : x ∈ (I : Set ℝ) := (P.contains J hJ) x hx
          rcases P.exists_unique x hxI with ⟨J', ⟨hJ'_mem, hxJ'⟩, huniq⟩
          have hJ'_eq : J' = J := (huniq J ⟨hJ, hx⟩).symm
          dsimp [g]
          rw [dif_pos hxI]
          have hJ_eq : (P.exists_unique x hxI).choose = J' :=
            huniq ((P.exists_unique x hxI).choose) ((P.exists_unique x hxI).choose_spec).1
          rw [hJ_eq, hJ'_eq]
        simp [h_const_val]
      · have h_length_zero : |J|ₗ = 0 := BoundedInterval.length_of_empty (Set.not_nonempty_iff_eq_empty.mp hJ_nonempty)
        simp [h_length_zero]
    have hmem : lower_riemann_sum f P ∈ (PiecewiseConstantOn.integ · I) '' {g' | MinorizesOn g' f I ∧ PiecewiseConstantOn g' I} := by
      rw [← h_integ_eq]
      exact ⟨g, ⟨hg_minorizes, hg_pwc_on⟩, rfl⟩
    exact le_csSup (integral_bound_above hf) hmem

theorem lower_integ_eq_sup_lower_sum {f:ℝ → ℝ} {I:BoundedInterval} (hf: BddOn f I) :
  lower_integral f I = sSup (.range (fun P : Partition I ↦ lower_riemann_sum f P)) := by
  set S := Set.range (fun P : Partition I => lower_riemann_sum f P) with hS
  have h_bdd_above : BddAbove S := by
    rcases hf with ⟨M, hM⟩
    refine ⟨M * |I|ₗ, λ x hx => ?_⟩
    rcases hx with ⟨P, rfl⟩
    have h_term : ∀ J ∈ P, (sInf (f '' (J : Set ℝ))) * |J|ₗ ≤ M * |J|ₗ := by
      intro J hJ
      have h_len_nonneg : 0 ≤ |J|ₗ := BoundedInterval.length_nonneg _
      by_cases hJ_nonempty : (J : Set ℝ).Nonempty
      · rcases hJ_nonempty with ⟨x, hxJ⟩
        have hxI : x ∈ (I : Set ℝ) := (P.contains J hJ) x hxJ
        have h_abs : |f x| ≤ M := hM x hxI
        have h_fx_le_M : f x ≤ M := by nlinarith [abs_le.mp h_abs]
        have h_bdd_below : BddBelow (f '' (J : Set ℝ)) := by
          refine ⟨-M, λ y hy => ?_⟩
          rcases hy with ⟨x', hx', rfl⟩
          have hx'I : x' ∈ (I : Set ℝ) := (P.contains J hJ) x' hx'
          have h_abs' : |f x'| ≤ M := hM x' hx'I
          nlinarith [abs_le.mp h_abs']
        have h_img_mem : f x ∈ f '' (J : Set ℝ) := ⟨x, hxJ, rfl⟩
        have h_inf_le_fx : sInf (f '' (J : Set ℝ)) ≤ f x := csInf_le h_bdd_below h_img_mem
        exact mul_le_mul_of_nonneg_right (le_trans h_inf_le_fx h_fx_le_M) h_len_nonneg
      · have h_len_zero : |J|ₗ = 0 := BoundedInterval.length_of_empty (Set.not_nonempty_iff_eq_empty.mp hJ_nonempty)
        simp [h_len_zero]
    calc
      lower_riemann_sum f P = ∑ J ∈ P.intervals, (sInf (f '' (J : Set ℝ))) * |J|ₗ := rfl
      _ ≤ ∑ J ∈ P.intervals, M * |J|ₗ := Finset.sum_le_sum h_term
      _ = M * (∑ J ∈ P.intervals, |J|ₗ) := by rw [Finset.mul_sum]
      _ = M * |I|ₗ := by rw [Partition.sum_of_length I P]
  have h_nonempty : S.Nonempty := by
    refine ⟨lower_riemann_sum f (⊥ : Partition I), ?_⟩
    simp [S]
  apply le_antisymm
  · -- lower_integral f I ≤ sSup S
    have h_le_all_T : ∀ y ∈ (PiecewiseConstantOn.integ · I) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I}, y ≤ sSup S := by
      intro y hy
      rcases hy with ⟨h, ⟨hmin, hh⟩, rfl⟩
      rcases hh with ⟨P, hh_pcw⟩
      have hsum : PiecewiseConstantOn.integ h I ≤ lower_riemann_sum f P := by
        have hh_pwc_on : PiecewiseConstantOn h I := ⟨P, hh_pcw⟩
        have hsum' : integ h I ≤ lower_riemann_sum f P :=
          lower_riemann_sum_ge P hmin hh_pcw
        have h_eq : integ h I = PiecewiseConstantOn.integ h I :=
          (integ_of_piecewise_const hh_pwc_on).2
        rw [h_eq] at hsum'
        exact hsum'
      have h_sup_ge_sum : lower_riemann_sum f P ≤ sSup S := le_csSup h_bdd_above (by simp [S])
      calc
        PiecewiseConstantOn.integ h I ≤ lower_riemann_sum f P := hsum
        _ ≤ sSup S := h_sup_ge_sum
    have h_T_nonempty : ((PiecewiseConstantOn.integ · I) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I}).Nonempty :=
      integral_bound_lower_nonempty hf
    have h_eq_li : lower_integral f I = sSup ((PiecewiseConstantOn.integ · I) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I}) := rfl
    rw [h_eq_li]
    have h_sup_T_le_sup_S : sSup ((PiecewiseConstantOn.integ · I) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I}) ≤ sSup S :=
      csSup_le h_T_nonempty h_le_all_T
    exact h_sup_T_le_sup_S
  · -- sSup S ≤ lower_integral f I
    apply csSup_le h_nonempty
    intro x hx
    rcases hx with ⟨P, rfl⟩
    exact lower_integ_ge_lower_sum hf P

/-- Exercise 11.3.1 (i) -/
theorem MajorizesOn.trans {f g h: ℝ → ℝ} {I: BoundedInterval}
  (hfg: MajorizesOn f g I) (hgh: MajorizesOn g h I) : MajorizesOn f h I := by
  intro x hx
  have hgx : g x ≤ f x := hfg x hx
  have hhx : h x ≤ g x := hgh x hx
  exact le_trans hhx hgx

/-- Exercise 11.3.1 (ii) -/
theorem MajorizesOn.anti_symm {f g: ℝ → ℝ} {I: BoundedInterval}:
  (∀ x ∈ (I:Set ℝ), f x = g x) ↔ MajorizesOn f g I ∧ MajorizesOn g f I := by
  constructor
  · intro h
    constructor
    · intro x hx; rw [h x hx]
    · intro x hx; rw [h x hx]
  · intro ⟨hfg, hgf⟩
    intro x hx
    exact le_antisymm (hgf x hx) (hfg x hx)

/-- Exercise 11.3.2 -/
def MajorizesOn.of_add : Decidable ( ∀ (f g h:ℝ → ℝ) (I:BoundedInterval) (hfg: MajorizesOn f g I),
 MajorizesOn (f+h) (g+h) I) := by
  apply isTrue
  intro f g h I hfg x hx
  have hgfx : g x ≤ f x := hfg x hx
  simpa using add_le_add_right hgfx (h x)

def MajorizesOn.of_mul : Decidable ( ∀ (f g h:ℝ → ℝ) (I:BoundedInterval) (hfg: MajorizesOn f g I),
 MajorizesOn (f*h) (g*h) I) := by
  apply isFalse
  intro hAll
  let I : BoundedInterval := Icc (0 : ℝ) 1
  let f : ℝ → ℝ := fun _ ↦ 1
  let g : ℝ → ℝ := fun _ ↦ 0
  let h : ℝ → ℝ := fun _ ↦ -1
  have hfg : MajorizesOn f g I := by
    intro x hx; dsimp [g, f]; nlinarith
  have hbad := hAll f g h I hfg 0 (by norm_num [I])
  dsimp [MajorizesOn, f, g, h] at hbad
  nlinarith

def MajorizesOn.of_smul : Decidable ( ∀ (f g:ℝ → ℝ) (c:ℝ) (I:BoundedInterval) (hfg: MajorizesOn f g I),
 MajorizesOn (c • f) (c • g) I) := by
  apply isFalse
  intro hAll
  let I : BoundedInterval := Icc (0 : ℝ) 1
  let f : ℝ → ℝ := fun _ ↦ 2
  let g : ℝ → ℝ := fun _ ↦ 1
  let c : ℝ := -1
  have hfg : MajorizesOn f g I := by
    intro x hx; dsimp [g, f]; nlinarith
  have hbad := hAll f g c I hfg 0 (by norm_num [I])
  dsimp [MajorizesOn, f, g, c] at hbad
  nlinarith


end Chapter11