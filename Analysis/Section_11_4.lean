import Mathlib.Tactic
import Analysis.Section_9_6
import Analysis.Section_11_3

/-!
# Analysis I, Section 11.4: Basic properties of the Riemann integral

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Basic properties of the Riemann integral.

-/

namespace Chapter11
open Chapter9

/-- Theorem 11.4.1(a) / Exercise 11.4.1 -/
theorem IntegrableOn.add {I: BoundedInterval} {f g:ℝ → ℝ} (hf: IntegrableOn f I) (hg: IntegrableOn g I) :
  IntegrableOn (f + g) I ∧ integ (f + g) I = integ f I + integ g I := by
  unfold IntegrableOn at hf hg
  have hbdd : BddOn (f + g) I := by
    rcases hf.1 with ⟨M, hM⟩; rcases hg.1 with ⟨M', hM'⟩
    use M + M'
    intro x hx
    have hfx : |f x| ≤ M := hM x hx
    have hgx : |g x| ≤ M' := hM' x hx
    have h_abs_add (a b : ℝ) : |a + b| ≤ |a| + |b| := by
      have ha : a ≤ |a| := (abs_le.mp (le_refl _)).2
      have hb' : b ≤ |b| := (abs_le.mp (le_refl _)).2
      have hneg_a : -|a| ≤ a := (abs_le.mp (le_refl _)).1
      have hneg_b : -|b| ≤ b := (abs_le.mp (le_refl _)).1
      have h1 : a + b ≤ |a| + |b| := add_le_add ha hb'
      have hneg1 : -(|a| + |b|) ≤ a + b := by nlinarith
      exact abs_le.mpr ⟨hneg1, h1⟩
    calc
      |(f + g) x| = |f x + g x| := rfl
      _ ≤ |f x| + |g x| := h_abs_add _ _
      _ ≤ M + M' := by nlinarith
  have h_integ_f : integ f I = upper_integral f I := rfl
  have h_integ_g : integ g I = upper_integral g I := rfl
  have h_upper_add_le : upper_integral (f + g) I ≤ integ f I + integ g I := by
    have hx : ∀ ε > 0, upper_integral (f + g) I - (integ f I + integ g I) ≤ 2 * ε := by
      intro ε hε
      have hXf : upper_integral f I < integ f I + ε := by
        rw [h_integ_f]; linarith
      rcases lt_of_gt_upper_integral hf.1 hXf with ⟨u_f, hu_f_maj, hu_f_pwc, hu_f_int⟩
      have hXg : upper_integral g I < integ g I + ε := by
        rw [h_integ_g]; linarith
      rcases lt_of_gt_upper_integral hg.1 hXg with ⟨u_g, hu_g_maj, hu_g_pwc, hu_g_int⟩
      have h_sum_maj : MajorizesOn (u_f + u_g) (f + g) I := by
        intro x hx
        have h_fx : f x ≤ u_f x := hu_f_maj x hx
        have h_gx : g x ≤ u_g x := hu_g_maj x hx
        simp; nlinarith
      have h_sum_pwc : PiecewiseConstantOn (u_f + u_g) I := hu_f_pwc.add hu_g_pwc
      have h_upper_le : upper_integral (f + g) I ≤ PiecewiseConstantOn.integ (u_f + u_g) I :=
        upper_integral_le_integ hbdd h_sum_maj h_sum_pwc
      have h_int_u_f : integ u_f I < integ f I + ε := by
        calc
          integ u_f I = PiecewiseConstantOn.integ u_f I := (integ_of_piecewise_const hu_f_pwc).2
          _ < integ f I + ε := hu_f_int
      have h_int_u_g : integ u_g I < integ g I + ε := by
        calc
          integ u_g I = PiecewiseConstantOn.integ u_g I := (integ_of_piecewise_const hu_g_pwc).2
          _ < integ g I + ε := hu_g_int
      have h_upper_lt : upper_integral (f + g) I < integ f I + integ g I + 2 * ε := by
        calc
          upper_integral (f + g) I ≤ PiecewiseConstantOn.integ (u_f + u_g) I := h_upper_le
          _ = PiecewiseConstantOn.integ u_f I + PiecewiseConstantOn.integ u_g I :=
            PiecewiseConstantOn.integ_add hu_f_pwc hu_g_pwc
          _ = integ u_f I + integ u_g I := by
            simp [(integ_of_piecewise_const hu_f_pwc).2, (integ_of_piecewise_const hu_g_pwc).2]
          _ < (integ f I + ε) + (integ g I + ε) := by nlinarith
          _ = integ f I + integ g I + 2 * ε := by ring
      linarith
    have hx_nonpos : upper_integral (f + g) I - (integ f I + integ g I) ≤ 0 := by
      by_contra! h
      have hpos : 0 < upper_integral (f + g) I - (integ f I + integ g I) := by linarith
      set Δ := upper_integral (f + g) I - (integ f I + integ g I) with hΔ
      have hΔpos : 0 < Δ := hpos
      have hx_Δ : Δ ≤ 2 * (Δ / 4) := hx (Δ / 4) (by nlinarith)
      nlinarith
    linarith
  have h_lower_add_ge : integ f I + integ g I ≤ lower_integral (f + g) I := by
    have hx : ∀ ε > 0, (integ f I + integ g I) - lower_integral (f + g) I ≤ 2 * ε := by
      intro ε hε
      have hXf : integ f I - ε < lower_integral f I := by
        have : lower_integral f I = upper_integral f I := hf.2
        rw [this, h_integ_f]; linarith
      rcases gt_of_lt_lower_integral hf.1 hXf with ⟨l_f, hl_f_min, hl_f_pwc, hl_f_int⟩
      have hXg : integ g I - ε < lower_integral g I := by
        have : lower_integral g I = upper_integral g I := hg.2
        rw [this, h_integ_g]; linarith
      rcases gt_of_lt_lower_integral hg.1 hXg with ⟨l_g, hl_g_min, hl_g_pwc, hl_g_int⟩
      have h_sum_min : MinorizesOn (l_f + l_g) (f + g) I := by
        intro x hx
        have h_fx : l_f x ≤ f x := hl_f_min x hx
        have h_gx : l_g x ≤ g x := hl_g_min x hx
        simp; nlinarith
      have h_sum_pwc : PiecewiseConstantOn (l_f + l_g) I := hl_f_pwc.add hl_g_pwc
      have h_lower_ge : PiecewiseConstantOn.integ (l_f + l_g) I ≤ lower_integral (f + g) I :=
        integ_le_lower_integral hbdd h_sum_min h_sum_pwc
      have h_integ_sum : PiecewiseConstantOn.integ (l_f + l_g) I = integ l_f I + integ l_g I := by
        calc
          PiecewiseConstantOn.integ (l_f + l_g) I = PiecewiseConstantOn.integ l_f I + PiecewiseConstantOn.integ l_g I :=
            PiecewiseConstantOn.integ_add hl_f_pwc hl_g_pwc
          _ = integ l_f I + integ l_g I := by
            simp [(integ_of_piecewise_const hl_f_pwc).2, (integ_of_piecewise_const hl_g_pwc).2]
      have h_lower_gt : integ f I + integ g I - 2 * ε < lower_integral (f + g) I := by
        calc
          integ f I + integ g I - 2 * ε < integ l_f I + integ l_g I := by
            have h_int_l_f : integ f I - ε < integ l_f I := by
              calc
                integ f I - ε < PiecewiseConstantOn.integ l_f I := hl_f_int
                _ = integ l_f I := (integ_of_piecewise_const hl_f_pwc).2.symm
            have h_int_l_g : integ g I - ε < integ l_g I := by
              calc
                integ g I - ε < PiecewiseConstantOn.integ l_g I := hl_g_int
                _ = integ l_g I := (integ_of_piecewise_const hl_g_pwc).2.symm
            nlinarith
          _ = PiecewiseConstantOn.integ (l_f + l_g) I := by symm; exact h_integ_sum
          _ ≤ lower_integral (f + g) I := h_lower_ge
      linarith
    have hx_nonpos : (integ f I + integ g I) - lower_integral (f + g) I ≤ 0 := by
      by_contra! h
      have hpos : 0 < (integ f I + integ g I) - lower_integral (f + g) I := by linarith
      set Δ := (integ f I + integ g I) - lower_integral (f + g) I with hΔ
      have hΔpos : 0 < Δ := hpos
      have hx_Δ : Δ ≤ 2 * (Δ / 4) := hx (Δ / 4) (by nlinarith)
      nlinarith
    linarith
  have h_lower_le_upper : lower_integral (f + g) I ≤ upper_integral (f + g) I :=
    lower_integral_le_upper hbdd
  have h_eq_all : upper_integral (f + g) I = integ f I + integ g I := by
    apply le_antisymm h_upper_add_le
    calc
      integ f I + integ g I ≤ lower_integral (f + g) I := h_lower_add_ge
      _ ≤ upper_integral (f + g) I := h_lower_le_upper
  have h_eq_lower_upper : lower_integral (f + g) I = upper_integral (f + g) I := by
    apply le_antisymm h_lower_le_upper
    calc
      upper_integral (f + g) I = integ f I + integ g I := h_eq_all
      _ ≤ lower_integral (f + g) I := h_lower_add_ge
  have h_integ_eq : integ (f + g) I = integ f I + integ g I := by
    dsimp [integ]
    exact h_eq_all
  exact ⟨⟨hbdd, h_eq_lower_upper⟩, h_integ_eq⟩

/-- Theorem 11.4.1(b) / Exercise 11.4.1 -/
theorem IntegrableOn.smul {I: BoundedInterval} (c:ℝ) {f:ℝ → ℝ} (hf: IntegrableOn f I) :
  IntegrableOn (c • f) I ∧ integ (c • f) I = c * integ f I := by
  unfold IntegrableOn at hf
  rcases hf with ⟨hbdd_f, h_int_f⟩
  have hbdd : BddOn (c • f) I := by
    rcases hbdd_f with ⟨M, hM⟩
    use |c| * M
    intro x hx
    calc
      |(c • f) x| = |c * f x| := rfl
      _ = |c| * |f x| := abs_mul _ _
      _ ≤ |c| * M := mul_le_mul_of_nonneg_left (hM x hx) (abs_nonneg _)
  have hin_f : integ f I = upper_integral f I := rfl
  have hlow_f : lower_integral f I = integ f I := by linarith
  by_cases hc : 0 ≤ c
  · by_cases hc0 : c = 0
    · subst c
      have h_pwc0 : PiecewiseConstantOn (fun _ : ℝ => (0 : ℝ)) I :=
        (ConstantOn.of_const' (0 : ℝ) I).piecewiseConstantOn
      have h_int0_val : PiecewiseConstantOn.integ (fun _ : ℝ => (0 : ℝ)) I = 0 := by
        simpa using PiecewiseConstantOn.integ_const (0 : ℝ) I
      have h_int0 : integ (fun _ : ℝ => (0 : ℝ)) I = (0 : ℝ) * integ f I := by
        calc
          integ (fun _ : ℝ => (0 : ℝ)) I = h_pwc0.integ' := (integ_of_piecewise_const h_pwc0).2
          _ = PiecewiseConstantOn.integ (fun _ : ℝ => (0 : ℝ)) I := rfl
          _ = 0 := h_int0_val
          _ = (0 : ℝ) * integ f I := by ring
      have h_integrable0 : IntegrableOn (fun _ : ℝ => (0 : ℝ)) I :=
        (integ_of_piecewise_const h_pwc0).1
      simpa using And.intro h_integrable0 h_int0
    · have hcpos : 0 < c := by
        by_contra! h; exact hc0 (by linarith)
      have h_upper_smul_le : upper_integral (c • f) I ≤ c * integ f I := by
        have hx : ∀ ε > 0, upper_integral (c • f) I - c * integ f I ≤ ε := by
          intro ε hε
          have hXf : upper_integral f I < integ f I + ε / c := by
            have hpos : ε / c > 0 := div_pos hε hcpos
            nlinarith
          rcases lt_of_gt_upper_integral hbdd_f hXf with ⟨u, hu_maj, hu_pwc, hu_int⟩
          have h_smul_maj : MajorizesOn (c • u) (c • f) I := by
            intro x hx; have h_fx : f x ≤ u x := hu_maj x hx
            simp [Pi.smul_apply, smul_eq_mul]; nlinarith
          have h_smul_pwc : PiecewiseConstantOn (c • u) I := hu_pwc.smul c
          have h_upper_le : upper_integral (c • f) I ≤ PiecewiseConstantOn.integ (c • u) I :=
            upper_integral_le_integ hbdd h_smul_maj h_smul_pwc
          have h_int_u_eq : integ u I = PiecewiseConstantOn.integ u I :=
            (integ_of_piecewise_const hu_pwc).2
          have h_int_smul_u : PiecewiseConstantOn.integ (c • u) I = c * PiecewiseConstantOn.integ u I :=
            hu_pwc.integ_smul c
          have h_temp : upper_integral (c • f) I < c * integ f I + ε := by
            calc
              upper_integral (c • f) I ≤ PiecewiseConstantOn.integ (c • u) I := h_upper_le
              _ = c * PiecewiseConstantOn.integ u I := h_int_smul_u
              _ = c * integ u I := by rw [h_int_u_eq]
              _ < c * (integ f I + ε / c) := by nlinarith
              _ = c * integ f I + ε := by
                field_simp [hcpos.ne.symm]
          nlinarith
        have h_nonpos : upper_integral (c • f) I - c * integ f I ≤ 0 := by
          by_contra! hpos
          set Δ := upper_integral (c • f) I - c * integ f I with hΔ
          have hΔpos : 0 < Δ := hpos
          have hx_Δ : Δ ≤ Δ / 2 := hx (Δ / 2) (by nlinarith)
          nlinarith
        linarith
      have h_lower_smul_ge : c * integ f I ≤ lower_integral (c • f) I := by
        have hx : ∀ ε > 0, c * integ f I - lower_integral (c • f) I ≤ ε := by
          intro ε hε
          have hXf : integ f I - ε / c < lower_integral f I := by
            have hpos : ε / c > 0 := div_pos hε hcpos
            nlinarith
          rcases gt_of_lt_lower_integral hbdd_f hXf with ⟨l, hl_min, hl_pwc, hl_int⟩
          have h_smul_min : MinorizesOn (c • l) (c • f) I := by
            intro x hx; have h_fx : l x ≤ f x := hl_min x hx
            simp [Pi.smul_apply, smul_eq_mul]; nlinarith
          have h_smul_pwc : PiecewiseConstantOn (c • l) I := hl_pwc.smul c
          have h_lower_ge : PiecewiseConstantOn.integ (c • l) I ≤ lower_integral (c • f) I :=
            integ_le_lower_integral hbdd h_smul_min h_smul_pwc
          have h_int_l_eq : integ l I = PiecewiseConstantOn.integ l I :=
            (integ_of_piecewise_const hl_pwc).2
          have h_int_smul_l : PiecewiseConstantOn.integ (c • l) I = c * PiecewiseConstantOn.integ l I :=
            hl_pwc.integ_smul c
          have h_int_l_gt : integ f I - ε / c < PiecewiseConstantOn.integ l I := hl_int
          calc
            c * integ f I - lower_integral (c • f) I
                ≤ c * integ f I - PiecewiseConstantOn.integ (c • l) I := by nlinarith
            _ = c * integ f I - c * PiecewiseConstantOn.integ l I := by rw [h_int_smul_l]
            _ = c * (integ f I - PiecewiseConstantOn.integ l I) := by ring
            _ ≤ c * (ε / c) := by nlinarith
            _ = ε := by field_simp [hcpos.ne.symm]
        have h_nonpos : c * integ f I - lower_integral (c • f) I ≤ 0 := by
          by_contra! hpos
          set Δ := c * integ f I - lower_integral (c • f) I with hΔ
          have hΔpos : 0 < Δ := hpos
          have hx_Δ : Δ ≤ Δ / 2 := hx (Δ / 2) (by nlinarith)
          nlinarith
        linarith
      have h_lower_le_upper : lower_integral (c • f) I ≤ upper_integral (c • f) I :=
        lower_integral_le_upper hbdd
      have h_eq_lower_upper : lower_integral (c • f) I = upper_integral (c • f) I := by
        apply le_antisymm h_lower_le_upper
        nlinarith
      have h_integ_eq : integ (c • f) I = c * integ f I := by
        dsimp [integ]
        apply le_antisymm h_upper_smul_le
        nlinarith
      exact ⟨⟨hbdd, h_eq_lower_upper⟩, h_integ_eq⟩
  · have hc_neg : c < 0 := by linarith
    set d := -c with hd
    have hdpos : 0 < d := by linarith
    have h_upper_smul_le : upper_integral (c • f) I ≤ c * integ f I := by
      have hx : ∀ ε > 0, upper_integral (c • f) I - c * integ f I ≤ ε := by
        intro ε hε
        have hXf : integ f I - ε / d < lower_integral f I := by
          have hpos : ε / d > 0 := div_pos hε hdpos
          rw [hlow_f]; nlinarith
        rcases gt_of_lt_lower_integral hbdd_f hXf with ⟨l, hl_min, hl_pwc, hl_int⟩
        have h_smul_maj : MajorizesOn (c • l) (c • f) I := by
          intro x hx; have h_fx : l x ≤ f x := hl_min x hx
          simp [Pi.smul_apply, smul_eq_mul]; nlinarith
        have h_smul_pwc : PiecewiseConstantOn (c • l) I := hl_pwc.smul c
        have h_upper_le : upper_integral (c • f) I ≤ PiecewiseConstantOn.integ (c • l) I :=
          upper_integral_le_integ hbdd h_smul_maj h_smul_pwc
        have h_int_l_eq : integ l I = PiecewiseConstantOn.integ l I :=
          (integ_of_piecewise_const hl_pwc).2
        have h_int_smul_l : PiecewiseConstantOn.integ (c • l) I = c * PiecewiseConstantOn.integ l I :=
          hl_pwc.integ_smul c
        have h_calc : c * (integ f I - ε / d) = c * integ f I + ε := by
          calc
            c * (integ f I - ε / d) = c * integ f I - c * (ε / d) := by ring
            _ = c * integ f I + d * (ε / d) := by
              dsimp [d]; ring
            _ = c * integ f I + ε := by field_simp [hdpos.ne.symm]
        have h_temp : upper_integral (c • f) I < c * integ f I + ε := by
          calc
            upper_integral (c • f) I ≤ PiecewiseConstantOn.integ (c • l) I := h_upper_le
            _ = c * PiecewiseConstantOn.integ l I := h_int_smul_l
            _ = c * integ l I := by rw [h_int_l_eq]
            _ < c * (integ f I - ε / d) := by nlinarith
            _ = c * integ f I + ε := h_calc
        nlinarith
      have h_nonpos : upper_integral (c • f) I - c * integ f I ≤ 0 := by
        by_contra! hpos
        set Δ := upper_integral (c • f) I - c * integ f I with hΔ
        have hΔpos : 0 < Δ := hpos
        have hx_Δ : Δ ≤ Δ / 2 := hx (Δ / 2) (by nlinarith)
        nlinarith
      linarith
    have h_lower_smul_ge : c * integ f I ≤ lower_integral (c • f) I := by
      have hx : ∀ ε > 0, c * integ f I - lower_integral (c • f) I ≤ ε := by
        intro ε hε
        have hXf : upper_integral f I < integ f I + ε / d := by
          have hpos : ε / d > 0 := div_pos hε hdpos
          nlinarith
        rcases lt_of_gt_upper_integral hbdd_f hXf with ⟨u, hu_maj, hu_pwc, hu_int⟩
        have h_smul_min : MinorizesOn (c • u) (c • f) I := by
          intro x hx; have h_fx : f x ≤ u x := hu_maj x hx
          simp [Pi.smul_apply, smul_eq_mul]; nlinarith
        have h_smul_pwc : PiecewiseConstantOn (c • u) I := hu_pwc.smul c
        have h_lower_ge : PiecewiseConstantOn.integ (c • u) I ≤ lower_integral (c • f) I :=
          integ_le_lower_integral hbdd h_smul_min h_smul_pwc
        have h_int_u_eq : integ u I = PiecewiseConstantOn.integ u I :=
          (integ_of_piecewise_const hu_pwc).2
        have h_int_smul_u : PiecewiseConstantOn.integ (c • u) I = c * PiecewiseConstantOn.integ u I :=
          hu_pwc.integ_smul c
        have h_diff : PiecewiseConstantOn.integ u I - integ f I < ε / d := by
          linarith
        have h_temp : c * integ f I - lower_integral (c • f) I < ε := by
          calc
            c * integ f I - lower_integral (c • f) I
                ≤ c * integ f I - PiecewiseConstantOn.integ (c • u) I := by nlinarith
            _ = c * integ f I - c * PiecewiseConstantOn.integ u I := by rw [h_int_smul_u]
            _ = c * (integ f I - PiecewiseConstantOn.integ u I) := by ring
            _ = d * (PiecewiseConstantOn.integ u I - integ f I) := by
              dsimp [d]; ring
            _ < d * (ε / d) := mul_lt_mul_of_pos_left h_diff hdpos
            _ = ε := by field_simp [hdpos.ne.symm]
        nlinarith
      have h_nonpos : c * integ f I - lower_integral (c • f) I ≤ 0 := by
        by_contra! hpos
        set Δ := c * integ f I - lower_integral (c • f) I with hΔ
        have hΔpos : 0 < Δ := hpos
        have hx_Δ : Δ ≤ Δ / 2 := hx (Δ / 2) (by nlinarith)
        nlinarith
      linarith
    have h_lower_le_upper : lower_integral (c • f) I ≤ upper_integral (c • f) I :=
      lower_integral_le_upper hbdd
    have h_eq_lower_upper : lower_integral (c • f) I = upper_integral (c • f) I := by
      apply le_antisymm h_lower_le_upper
      nlinarith
    have h_integ_eq : integ (c • f) I = c * integ f I := by
      dsimp [integ]
      apply le_antisymm h_upper_smul_le
      nlinarith
    exact ⟨⟨hbdd, h_eq_lower_upper⟩, h_integ_eq⟩

theorem IntegrableOn.neg {I: BoundedInterval} {f:ℝ → ℝ} (hf: IntegrableOn f I) :
  IntegrableOn (-f) I ∧ integ (-f) I = -integ f I := by
  have h := IntegrableOn.smul (-1 : ℝ) hf
  refine ⟨by simpa [smul_eq_mul] using h.1, ?_⟩
  calc
    integ (-f) I = integ ((-1 : ℝ) • f) I := by simp
    _ = (-1 : ℝ) * integ f I := h.2
    _ = -integ f I := by ring

/-- Theorem 11.4.1(c) / Exercise 11.4.1 -/
theorem IntegrableOn.sub {I: BoundedInterval} {f g:ℝ → ℝ} (hf: IntegrableOn f I) (hg: IntegrableOn g I) :
  IntegrableOn (f - g) I ∧ integ (f - g) I = integ f I - integ g I := by
  have hneg := hg.neg
  have hsum := IntegrableOn.add hf hneg.1
  refine ⟨by
    simpa [sub_eq_add_neg] using hsum.1, ?_⟩
  calc
    integ (f - g) I = integ (f + (-g)) I := by simp [sub_eq_add_neg]
    _ = integ f I + integ (-g) I := hsum.2
    _ = integ f I + (-integ g I) := by rw [hneg.2]
    _ = integ f I - integ g I := by ring

/-- Theorem 11.4.1(d) / Exercise 11.4.1 -/
theorem IntegrableOn.nonneg {I: BoundedInterval} {f:ℝ → ℝ} (hf: IntegrableOn f I) (hf_nonneg: ∀ x ∈ I, 0 ≤ f x) :
  0 ≤ integ f I := by
  have hbdd : BddOn f I := hf.1
  have hzero_pwc : PiecewiseConstantOn (fun _ : ℝ => (0 : ℝ)) I :=
    (ConstantOn.of_const' (0 : ℝ) I).piecewiseConstantOn
  have hzero_min : MinorizesOn (fun _ : ℝ => (0 : ℝ)) f I := by
    intro x hx
    exact hf_nonneg x hx
  have hzero_integ : PiecewiseConstantOn.integ (fun _ : ℝ => (0 : ℝ)) I ≤ lower_integral f I :=
    integ_le_lower_integral hbdd hzero_min hzero_pwc
  have hzero_integ_val : PiecewiseConstantOn.integ (fun _ : ℝ => (0 : ℝ)) I = 0 := by
    simpa using PiecewiseConstantOn.integ_const (0 : ℝ) I
  have hlower_eq : lower_integral f I = integ f I := by
    dsimp [integ]
    rw [hf.2]
  calc
    0 = PiecewiseConstantOn.integ (fun _ : ℝ => (0 : ℝ)) I := by symm; exact hzero_integ_val
    _ ≤ lower_integral f I := hzero_integ
    _ = integ f I := hlower_eq

/-- Theorem 11.4.1(e) / Exercise 11.4.1 -/
theorem IntegrableOn.mono {I: BoundedInterval} {f g:ℝ → ℝ} (hf: IntegrableOn f I) (hg: IntegrableOn g I)
  (h: MajorizesOn g f I) :
  integ f I ≤ integ g I := by
  have hsub := hg.sub hf
  have h_nonneg : ∀ x ∈ (I : Set ℝ), 0 ≤ (g - f) x := by
    intro x hx
    dsimp [Pi.sub_apply]
    have hfx : f x ≤ g x := h x hx
    linarith
  have h_nonneg_integ : 0 ≤ integ (g - f) I := IntegrableOn.nonneg hsub.1 h_nonneg
  have h_integ_sub : integ (g - f) I = integ g I - integ f I := hsub.2
  linarith

/-- Theorem 11.4.1(f) / Exercise 11.4.1 -/
theorem IntegrableOn.const (c:ℝ) (I: BoundedInterval) :
  IntegrableOn (fun _ ↦ c) I ∧ integ (fun _ ↦ c) I = c * |I|ₗ := by
  have hconst : ConstantOn (fun _ ↦ c) (I : Set ℝ) := ConstantOn.of_const' c I
  have hpwc : PiecewiseConstantOn (fun _ ↦ c) I := hconst.piecewiseConstantOn
  have h := integ_of_piecewise_const hpwc
  have h_integ_eq : integ (fun _ ↦ c) I = c * |I|ₗ := by
    calc
      integ (fun _ ↦ c) I = PiecewiseConstantOn.integ (fun _ ↦ c) I := h.2
      _ = c * |I|ₗ := PiecewiseConstantOn.integ_const c I
  exact ⟨h.1, h_integ_eq⟩

/-- Theorem 11.4.1(f') / Exercise 11.4.1 -/
theorem IntegrableOn.const' {I: BoundedInterval} {f:ℝ → ℝ} (hf: ConstantOn f I) :
  IntegrableOn f I ∧ integ f I = (constant_value_on f I) * |I|ₗ := by
  have hpwc : PiecewiseConstantOn f I := hf.piecewiseConstantOn
  have h := integ_of_piecewise_const hpwc
  have h_integ_eq : integ f I = (constant_value_on f I) * |I|ₗ := by
    calc
      integ f I = PiecewiseConstantOn.integ f I := h.2
      _ = (constant_value_on f I) * |I|ₗ := PiecewiseConstantOn.integ_const' hf
  exact ⟨h.1, h_integ_eq⟩


theorem IntegrableOn.of_join {I J K : BoundedInterval} (hIJK : K.joins I J)
    {f : ℝ → ℝ} (hI : IntegrableOn f I) (hJ : IntegrableOn f J) :
    IntegrableOn f K ∧ integ f K = integ f I + integ f J := by
  classical
  have h_disjoint : (I : Set ℝ) ∩ (J : Set ℝ) = ∅ := hIJK.1
  have h_union : (K : Set ℝ) = (I : Set ℝ) ∪ (J : Set ℝ) := hIJK.2.1
  have hI_sub_K : (I : Set ℝ) ⊆ (K : Set ℝ) := by
    intro x hx; rw [h_union]; exact Or.inl hx
  have hJ_sub_K : (J : Set ℝ) ⊆ (K : Set ℝ) := by
    intro x hx; rw [h_union]; exact Or.inr hx
  rcases hI with ⟨hbdd_I, h_int_eq_I⟩
  rcases hJ with ⟨hbdd_J, h_int_eq_J⟩
  have hbdd_K : BddOn f K := by
    rcases hbdd_I with ⟨MI, hMI⟩
    rcases hbdd_J with ⟨MJ, hMJ⟩
    use max MI MJ
    intro x hx
    rw [h_union] at hx
    rcases hx with (hxI | hxJ)
    · exact le_trans (hMI x hxI) (le_max_left _ _)
    · exact le_trans (hMJ x hxJ) (le_max_right _ _)
  have h_upper_sum : upper_integral f K ≤ integ f I + integ f J := by
    refine le_of_forall_pos_lt_add ?_
    intro ε hε
    have hI_lt : upper_integral f I < integ f I + ε / 2 := by nlinarith
    rcases lt_of_gt_upper_integral hbdd_I hI_lt with ⟨g_I, hgI_maj, hgI_pc, hgI_int⟩
    have hJ_lt : upper_integral f J < integ f J + ε / 2 := by nlinarith
    rcases lt_of_gt_upper_integral hbdd_J hJ_lt with ⟨g_J, hgJ_maj, hgJ_pc, hgJ_int⟩
    let g : ℝ → ℝ := λ x => if x ∈ (I : Set ℝ) then g_I x else g_J x
    have hg_on_I : ∀ x ∈ (I : Set ℝ), g_I x = g x := by
      intro x hx; dsimp [g]; simp [hx]
    have hg_on_J : ∀ x ∈ (J : Set ℝ), g_J x = g x := by
      intro x hx
      dsimp [g]
      have hx_not_I : x ∉ (I : Set ℝ) := by
        intro hxI
        have hx_both : x ∈ (I : Set ℝ) ∩ (J : Set ℝ) := ⟨hxI, hx⟩
        rw [h_disjoint] at hx_both
        exact hx_both
      simp [hx_not_I]
    have hg_pc_I : PiecewiseConstantOn g I :=
      PiecewiseConstantOn.congr' hgI_pc hg_on_I
    have hg_pc_J : PiecewiseConstantOn g J :=
      PiecewiseConstantOn.congr' hgJ_pc hg_on_J
    have hg_pc_K : PiecewiseConstantOn g K :=
      (PiecewiseConstantOn.of_join hIJK g).mpr ⟨hg_pc_I, hg_pc_J⟩
    have hg_maj_K : MajorizesOn g f K := by
      intro x hx
      rw [h_union] at hx
      rcases hx with (hxI | hxJ)
      · rw [← hg_on_I x hxI]; exact hgI_maj x hxI
      · rw [← hg_on_J x hxJ]; exact hgJ_maj x hxJ
    have h_upper_bound : upper_integral f K ≤ PiecewiseConstantOn.integ g K :=
      upper_integral_le_integ hbdd_K hg_maj_K hg_pc_K
    have h_integ_join_g : PiecewiseConstantOn.integ g K = PiecewiseConstantOn.integ g I + PiecewiseConstantOn.integ g J :=
      PiecewiseConstantOn.integ_of_join hIJK hg_pc_K
    have h_integ_gI : PiecewiseConstantOn.integ g I = PiecewiseConstantOn.integ g_I I :=
      PiecewiseConstantOn.integ_congr (λ x hx => (hg_on_I x hx).symm)
    have h_integ_gJ : PiecewiseConstantOn.integ g J = PiecewiseConstantOn.integ g_J J :=
      PiecewiseConstantOn.integ_congr (λ x hx => (hg_on_J x hx).symm)
    calc
      upper_integral f K ≤ PiecewiseConstantOn.integ g K := h_upper_bound
      _ = PiecewiseConstantOn.integ g I + PiecewiseConstantOn.integ g J := h_integ_join_g
      _ = PiecewiseConstantOn.integ g_I I + PiecewiseConstantOn.integ g_J J := by rw [h_integ_gI, h_integ_gJ]
      _ < (integ f I + ε / 2) + (integ f J + ε / 2) := by nlinarith
      _ = integ f I + integ f J + ε := by ring
  have h_lower_ge : integ f I + integ f J ≤ lower_integral f K := by
    refine le_of_forall_pos_lt_add ?_
    intro ε hε
    have hI_lt : lower_integral f I - ε / 2 < lower_integral f I := by nlinarith
    rcases gt_of_lt_lower_integral hbdd_I hI_lt with ⟨l_I, hlI_min, hlI_pc, hlI_int⟩
    have hJ_lt : lower_integral f J - ε / 2 < lower_integral f J := by nlinarith
    rcases gt_of_lt_lower_integral hbdd_J hJ_lt with ⟨l_J, hlJ_min, hlJ_pc, hlJ_int⟩
    let l : ℝ → ℝ := λ x => if x ∈ (I : Set ℝ) then l_I x else l_J x
    have hl_on_I : ∀ x ∈ (I : Set ℝ), l_I x = l x := by
      intro x hx; dsimp [l]; simp [hx]
    have hl_on_J : ∀ x ∈ (J : Set ℝ), l_J x = l x := by
      intro x hx
      dsimp [l]
      have hx_not_I : x ∉ (I : Set ℝ) := by
        intro hxI
        have hx_both : x ∈ (I : Set ℝ) ∩ (J : Set ℝ) := ⟨hxI, hx⟩
        rw [h_disjoint] at hx_both
        exact hx_both
      simp [hx_not_I]
    have hl_pc_I : PiecewiseConstantOn l I :=
      PiecewiseConstantOn.congr' hlI_pc hl_on_I
    have hl_pc_J : PiecewiseConstantOn l J :=
      PiecewiseConstantOn.congr' hlJ_pc hl_on_J
    have hl_pc_K : PiecewiseConstantOn l K :=
      (PiecewiseConstantOn.of_join hIJK l).mpr ⟨hl_pc_I, hl_pc_J⟩
    have hl_min_K : MinorizesOn l f K := by
      intro x hx
      rw [h_union] at hx
      rcases hx with (hxI | hxJ)
      · rw [← hl_on_I x hxI]; exact hlI_min x hxI
      · rw [← hl_on_J x hxJ]; exact hlJ_min x hxJ
    have h_lower_bound : PiecewiseConstantOn.integ l K ≤ lower_integral f K := by
      simpa using integ_le_lower_integral hbdd_K hl_min_K hl_pc_K
    have h_integ_join_l : PiecewiseConstantOn.integ l K = PiecewiseConstantOn.integ l I + PiecewiseConstantOn.integ l J :=
      PiecewiseConstantOn.integ_of_join hIJK hl_pc_K
    have h_integ_lI : PiecewiseConstantOn.integ l I = PiecewiseConstantOn.integ l_I I :=
      PiecewiseConstantOn.integ_congr (λ x hx => (hl_on_I x hx).symm)
    have h_integ_lJ : PiecewiseConstantOn.integ l J = PiecewiseConstantOn.integ l_J J :=
      PiecewiseConstantOn.integ_congr (λ x hx => (hl_on_J x hx).symm)
    have h_chain : lower_integral f I + lower_integral f J - ε < PiecewiseConstantOn.integ l K := by
      calc
        lower_integral f I + lower_integral f J - ε = (lower_integral f I - ε / 2) + (lower_integral f J - ε / 2) := by ring
        _ < PiecewiseConstantOn.integ l_I I + PiecewiseConstantOn.integ l_J J := by nlinarith
        _ = PiecewiseConstantOn.integ l I + PiecewiseConstantOn.integ l J := by rw [h_integ_lI, h_integ_lJ]
        _ = PiecewiseConstantOn.integ l K := h_integ_join_l.symm
    have h_upper_lower : integ f I + integ f J = lower_integral f I + lower_integral f J := by
      dsimp [integ]
      rw [h_int_eq_I, h_int_eq_J]
    have h_lower_sum_chain : lower_integral f I + lower_integral f J - ε < lower_integral f K :=
      lt_of_lt_of_le h_chain h_lower_bound
    rw [h_upper_lower]
    nlinarith
  have h_lower_le_upper : lower_integral f K ≤ upper_integral f K := lower_integral_le_upper hbdd_K
  have h_eq : lower_integral f K = upper_integral f K := by nlinarith
  have h_integ_eq : integ f K = integ f I + integ f J := by
    dsimp [integ]
    nlinarith
  exact ⟨⟨hbdd_K, h_eq⟩, h_integ_eq⟩


/-- Theorem 11.4.1 (h) (Laws of integration) / Exercise 11.4.1 -/
theorem IntegrableOn.join {I J K: BoundedInterval} (hIJK: K.joins I J)
  {f: ℝ → ℝ} (h: IntegrableOn f K) :
  IntegrableOn f I ∧ IntegrableOn f J ∧ integ f K = integ f I + integ f J := by
  have h_disjoint : (I : Set ℝ) ∩ (J : Set ℝ) = ∅ := hIJK.1
  have h_union : (K : Set ℝ) = (I : Set ℝ) ∪ (J : Set ℝ) := hIJK.2.1
  have h_length : |K|ₗ = |I|ₗ + |J|ₗ := hIJK.2.2
  have hI_sub_K : (I : Set ℝ) ⊆ (K : Set ℝ) := by
    intro x hx; rw [h_union]; exact Or.inl hx
  have hJ_sub_K : (J : Set ℝ) ⊆ (K : Set ℝ) := by
    intro x hx; rw [h_union]; exact Or.inr hx
  rcases h with ⟨hbdd_K, h_int_eq⟩
  have hbdd_I : BddOn f I := by
    rcases hbdd_K with ⟨M, hM⟩
    exact ⟨M, λ x hx => hM x (hI_sub_K hx)⟩
  have hbdd_J : BddOn f J := by
    rcases hbdd_K with ⟨M, hM⟩
    exact ⟨M, λ x hx => hM x (hJ_sub_K hx)⟩

  -- Direction 1: upper_integral f I + upper_integral f J ≤ upper_integral f K
  have h_up_ineq : upper_integral f I + upper_integral f J ≤ upper_integral f K := by
    by_contra! H
    set ε := (upper_integral f I + upper_integral f J - upper_integral f K) / 2 with hε_def
    have hε_pos : 0 < ε := by
      dsimp [ε]; nlinarith
    have hK_lt : upper_integral f K < upper_integral f K + ε := by nlinarith
    rcases lt_of_gt_upper_integral hbdd_K hK_lt with ⟨g, hg_maj, hg_pc, hg_int⟩
    rcases (PiecewiseConstantOn.of_join hIJK g).mp hg_pc with ⟨hg_pc_I, hg_pc_J⟩
    have hg_maj_I : MajorizesOn g f I := λ x hx => hg_maj x (hI_sub_K hx)
    have hg_maj_J : MajorizesOn g f J := λ x hx => hg_maj x (hJ_sub_K hx)
    have h_up_I : upper_integral f I ≤ integ g I := by
      calc
        upper_integral f I ≤ hg_pc_I.integ' := upper_integral_le_integ hbdd_I hg_maj_I hg_pc_I
        _ = PiecewiseConstantOn.integ g I := rfl
        _ = integ g I := (integ_of_piecewise_const hg_pc_I).2.symm
    have h_up_J : upper_integral f J ≤ integ g J := by
      calc
        upper_integral f J ≤ hg_pc_J.integ' := upper_integral_le_integ hbdd_J hg_maj_J hg_pc_J
        _ = PiecewiseConstantOn.integ g J := rfl
        _ = integ g J := (integ_of_piecewise_const hg_pc_J).2.symm
    have h_integ_join : integ g K = integ g I + integ g J := by
      have hI_eq : PiecewiseConstantOn.integ g I = integ g I := by
        simpa using (integ_of_piecewise_const hg_pc_I).2.symm
      have hJ_eq : PiecewiseConstantOn.integ g J = integ g J := by
        simpa using (integ_of_piecewise_const hg_pc_J).2.symm
      calc
        integ g K = PiecewiseConstantOn.integ g K := (integ_of_piecewise_const hg_pc).2
        _ = PiecewiseConstantOn.integ g I + PiecewiseConstantOn.integ g J :=
          PiecewiseConstantOn.integ_of_join hIJK (f := g) hg_pc
        _ = integ g I + integ g J := by rw [hI_eq, hJ_eq]
    have h_sum_lt : upper_integral f I + upper_integral f J < upper_integral f K + ε := by
      calc
        upper_integral f I + upper_integral f J ≤ integ g I + integ g J := add_le_add h_up_I h_up_J
        _ = integ g K := h_integ_join.symm
        _ = PiecewiseConstantOn.integ g K := (integ_of_piecewise_const hg_pc).2
        _ < upper_integral f K + ε := hg_int
    dsimp [ε] at h_sum_lt
    nlinarith

  -- Direction 2: lower_integral f K ≤ lower_integral f I + lower_integral f J
  have h_lo_ineq : lower_integral f K ≤ lower_integral f I + lower_integral f J := by
    by_contra! H
    set ε := (lower_integral f K - (lower_integral f I + lower_integral f J)) / 2 with hε_def
    have hε_pos : 0 < ε := by
      dsimp [ε]; nlinarith
    have hK_lt : lower_integral f K - ε < lower_integral f K := by nlinarith
    rcases gt_of_lt_lower_integral hbdd_K hK_lt with ⟨l, hl_min, hl_pc, hl_int⟩
    rcases (PiecewiseConstantOn.of_join hIJK l).mp hl_pc with ⟨hl_pc_I, hl_pc_J⟩
    have hl_min_I : MinorizesOn l f I := λ x hx => hl_min x (hI_sub_K hx)
    have hl_min_J : MinorizesOn l f J := λ x hx => hl_min x (hJ_sub_K hx)
    have h_lo_I : integ l I ≤ lower_integral f I :=
      calc
        integ l I = PiecewiseConstantOn.integ l I := (integ_of_piecewise_const hl_pc_I).2
        _ = hl_pc_I.integ' := rfl
        _ ≤ lower_integral f I := integ_le_lower_integral hbdd_I hl_min_I hl_pc_I
    have h_lo_J : integ l J ≤ lower_integral f J :=
      calc
        integ l J = PiecewiseConstantOn.integ l J := (integ_of_piecewise_const hl_pc_J).2
        _ = hl_pc_J.integ' := rfl
        _ ≤ lower_integral f J := integ_le_lower_integral hbdd_J hl_min_J hl_pc_J
    have h_integ_join : integ l K = integ l I + integ l J := by
      have hI_eq : PiecewiseConstantOn.integ l I = integ l I := by
        simpa using (integ_of_piecewise_const hl_pc_I).2.symm
      have hJ_eq : PiecewiseConstantOn.integ l J = integ l J := by
        simpa using (integ_of_piecewise_const hl_pc_J).2.symm
      calc
        integ l K = PiecewiseConstantOn.integ l K := (integ_of_piecewise_const hl_pc).2
        _ = PiecewiseConstantOn.integ l I + PiecewiseConstantOn.integ l J :=
          PiecewiseConstantOn.integ_of_join hIJK (f := l) hl_pc
        _ = integ l I + integ l J := by rw [hI_eq, hJ_eq]
    have h_chain : lower_integral f K - ε < lower_integral f I + lower_integral f J := by
      calc
        lower_integral f K - ε < PiecewiseConstantOn.integ l K := hl_int
        _ = integ l K := (integ_of_piecewise_const hl_pc).2.symm
        _ = integ l I + integ l J := h_integ_join
        _ ≤ lower_integral f I + lower_integral f J := add_le_add h_lo_I h_lo_J
    dsimp [ε] at h_chain
    nlinarith

  have h_lower_I_le_up_I : lower_integral f I ≤ upper_integral f I :=
    lower_integral_le_upper hbdd_I
  have h_lower_J_le_up_J : lower_integral f J ≤ upper_integral f J :=
    lower_integral_le_upper hbdd_J

  have h_sum_eq : lower_integral f I + lower_integral f J = upper_integral f I + upper_integral f J := by
    nlinarith

  have h_int_I : IntegrableOn f I := by
    refine ⟨hbdd_I, ?_⟩
    have h_diff : (upper_integral f I - lower_integral f I) + (upper_integral f J - lower_integral f J) = 0 := by
      nlinarith
    have h_nonneg1 : 0 ≤ upper_integral f I - lower_integral f I := by linarith
    have h_nonneg2 : 0 ≤ upper_integral f J - lower_integral f J := by linarith
    have h_zero : upper_integral f I - lower_integral f I = 0 := by nlinarith
    linarith

  have h_int_J : IntegrableOn f J := by
    refine ⟨hbdd_J, ?_⟩
    have h_diff : (upper_integral f I - lower_integral f I) + (upper_integral f J - lower_integral f J) = 0 := by
      nlinarith
    have h_nonneg1 : 0 ≤ upper_integral f I - lower_integral f I := by linarith
    have h_nonneg2 : 0 ≤ upper_integral f J - lower_integral f J := by linarith
    have h_zero : upper_integral f J - lower_integral f J = 0 := by nlinarith
    linarith

  have h_integ_sum : integ f K = integ f I + integ f J := by
    calc
      integ f K = upper_integral f K := rfl
      _ = upper_integral f I + upper_integral f J := by nlinarith
      _ = integ f I + integ f J := rfl

  exact ⟨h_int_I, h_int_J, h_integ_sum⟩

open Classical in
/-- Theorem 11.4.1(g) / Exercise 11.4.1 -/
theorem IntegrableOn.of_extend {I J: BoundedInterval} (hIJ: I ⊆ J)
  {f: ℝ → ℝ} (h: IntegrableOn f I) :
  IntegrableOn (fun x ↦ if x ∈ I then f x else 0) J := by
  set g := fun x ↦ if x ∈ I then f x else 0 with hg_def
  have hg_on_I : Set.EqOn g f I := by
    intro x hx; dsimp [g]; exact if_pos hx
  have hg_int_I : IntegrableOn g I := by
    rcases h with ⟨hbdd, h_eq⟩
    refine ⟨?_, ?_⟩
    · rcases hbdd with ⟨M, hM⟩
      refine ⟨M, λ x hx => ?_⟩
      have hgx : g x = f x := by dsimp [g]; exact if_pos hx
      rw [hgx]
      exact hM x hx
    · rw [lower_integral_congr hg_on_I, upper_integral_congr hg_on_I, h_eq]
  -- helper: if g = 0 on K, then g is integrable on K
  have hg_int_zero_on (K : BoundedInterval) (hg_zero_on_K : ∀ x, x ∈ (K : Set ℝ) → g x = 0) : IntegrableOn g K := by
    have h0_int : IntegrableOn (fun _ : ℝ => 0) K := (IntegrableOn.const 0 K).1
    rcases h0_int with ⟨hbdd, h_eq⟩
    refine ⟨?_, ?_⟩
    · rcases hbdd with ⟨M, hM⟩
      refine ⟨M, λ x hx => ?_⟩
      rw [hg_zero_on_K x hx]
      exact hM x hx
    · have h_g_zero_on_K : Set.EqOn g (fun _ : ℝ => 0) K := hg_zero_on_K
      rw [lower_integral_congr h_g_zero_on_K, upper_integral_congr h_g_zero_on_K, h_eq]
  by_cases hI_empty : (I : Set ℝ) = ∅
  · have hg_zero : g = (fun _ : ℝ => 0) := by
      ext x
      dsimp [g]
      have hx_not_I : x ∉ (I : Set ℝ) := by rw [hI_empty]; simp
      exact if_neg hx_not_I
    rw [hg_zero]
    exact (IntegrableOn.const 0 J).1
  · have hI_nonempty : (I : Set ℝ).Nonempty := Set.nonempty_iff_ne_empty.mpr hI_empty
    rcases hI_nonempty with ⟨x, hx⟩
    have ha_le_b : I.a ≤ I.b := by
      have hx_Icc : x ∈ (BoundedInterval.Icc I.a I.b : Set ℝ) := BoundedInterval.subset_Icc I x hx
      rcases hx_Icc with ⟨hI_a_le_x, hx_le_I_b⟩
      exact hI_a_le_x.trans hx_le_I_b
    -- Prove J.a ≤ I.a
    have ha_ineq : J.a ≤ I.a := by
      by_cases ha_mem : I.a ∈ (I : Set ℝ)
      · have haJ : I.a ∈ (J : Set ℝ) := hIJ _ ha_mem
        exact (BoundedInterval.subset_Icc J _ haJ).1
      · by_contra! H  -- H: J.a > I.a
        have ha_lt_Ja : I.a < J.a := H
        have ha_le_b_J : J.a ≤ I.b := by
          have hxJ : x ∈ (J : Set ℝ) := hIJ x hx
          have hxJ_Icc : x ∈ (BoundedInterval.Icc J.a J.b : Set ℝ) := BoundedInterval.subset_Icc J x hxJ
          have hxI_Icc : x ∈ (BoundedInterval.Icc I.a I.b : Set ℝ) := BoundedInterval.subset_Icc I x hx
          rcases hxJ_Icc with ⟨hJ_a_le_x, _⟩
          rcases hxI_Icc with ⟨_, hx_le_I_b⟩
          exact hJ_a_le_x.trans hx_le_I_b
        have ha_lt_b : I.a < I.b := by
          have hx_Icc : x ∈ (BoundedInterval.Icc I.a I.b : Set ℝ) := BoundedInterval.subset_Icc I x hx
          rcases hx_Icc with ⟨hI_a_le_x, hx_le_I_b⟩
          by_cases ha_eq_b : I.a = I.b
          · exfalso; exact ha_mem (by
              have hx_eq_a : x = I.a := le_antisymm (by linarith) hI_a_le_x
              rw [← hx_eq_a]; exact hx)
          · have : I.a ≤ I.b := hI_a_le_x.trans hx_le_I_b
            by_contra! hge  -- hge: I.b ≤ I.a
            apply ha_eq_b
            linarith
        let y := (I.a + J.a) / 2
        have ha_y : I.a < y := by
          dsimp [y]; nlinarith
        have hy_b : y < I.b := by
          dsimp [y]; nlinarith
        have hy_I : y ∈ (I : Set ℝ) := by
          have hy_Ioo : y ∈ (BoundedInterval.Ioo I.a I.b : Set ℝ) := by
            simp [BoundedInterval.set_Ioo, ha_y, hy_b]
          exact BoundedInterval.Ioo_subset I y hy_Ioo
        have hy_J : y ∈ (J : Set ℝ) := hIJ y hy_I
        have hJ_a_le_y : J.a ≤ y := (BoundedInterval.subset_Icc J y hy_J).1
        have hy_lt_Ja : y < J.a := by
          dsimp [y]; nlinarith
        have : J.a ≤ y := (BoundedInterval.subset_Icc J y hy_J).1
        linarith
    -- Prove I.b ≤ J.b
    have hb_ineq : I.b ≤ J.b := by
      by_cases hb_mem : I.b ∈ (I : Set ℝ)
      · have hbJ : I.b ∈ (J : Set ℝ) := hIJ _ hb_mem
        exact (BoundedInterval.subset_Icc J _ hbJ).2
      · by_contra! H  -- H: J.b < I.b
        have hb_lt : J.b < I.b := H
        have ha_lt_b : I.a < I.b := by
          have hx_Icc : x ∈ (BoundedInterval.Icc I.a I.b : Set ℝ) := BoundedInterval.subset_Icc I x hx
          rcases hx_Icc with ⟨hI_a_le_x, hx_le_I_b⟩
          by_cases ha_eq_b : I.a = I.b
          · exfalso; exact hb_mem (by
              have hx_eq_b : x = I.b := le_antisymm hx_le_I_b (by linarith)
              rw [← hx_eq_b]; exact hx)
          · have : I.a ≤ I.b := hI_a_le_x.trans hx_le_I_b
            by_contra! hge  -- hge: I.b ≤ I.a
            apply ha_eq_b
            linarith
        set m := max I.a J.b with hm_def
        have hm_lt_Ib : m < I.b := max_lt ha_lt_b hb_lt
        let y := (m + I.b) / 2
        have ha_y : I.a < y := by
          dsimp [y, m]
          have : I.a ≤ max I.a J.b := le_max_left _ _
          nlinarith
        have hy_b : y < I.b := by
          dsimp [y, m]
          have : max I.a J.b < I.b := hm_lt_Ib
          nlinarith
        have hy_I : y ∈ (I : Set ℝ) := by
          have hy_Ioo : y ∈ (BoundedInterval.Ioo I.a I.b : Set ℝ) := by
            simp [BoundedInterval.set_Ioo, ha_y, hy_b]
          exact BoundedInterval.Ioo_subset I y hy_Ioo
        have hy_J : y ∈ (J : Set ℝ) := hIJ y hy_I
        have hy_le_Jb : y ≤ J.b := (BoundedInterval.subset_Icc J y hy_J).2
        have Jb_lt_y : J.b < y := by
          have : J.b ≤ m := le_max_right _ _
          dsimp [y]; nlinarith
        linarith
    -- Step 1: g integrable on Icc I.a I.b
    have hg_int_Icc : IntegrableOn g (BoundedInterval.Icc I.a I.b) := by
      revert hg_int_I
      -- Use `cases` to properly substitute I and bring a, b into scope
      cases I with
      | Icc a b =>
        intro hg_int_I
        simpa using hg_int_I
      | Ioc a b =>
        intro hg_int_I
        have ha_lt_b : a < b := by
          have hx' : x ∈ Set.Ioc a b := by simpa [BoundedInterval.set_Ioc] using hx
          exact hx'.1.trans_le hx'.2
        have h_join : (BoundedInterval.Icc a b).joins (BoundedInterval.Icc a a) (BoundedInterval.Ioc a b) :=
          BoundedInterval.join_Icc_Ioc (le_refl a) ha_lt_b.le
        have hg_zero_on_Icc_aa : ∀ x, x ∈ (BoundedInterval.Icc a a : Set ℝ) → g x = 0 := by
          intro x hx'
          have hx_eq_a : x = a := by
            simpa [BoundedInterval.set_Icc] using hx'
          rw [hx_eq_a]
          dsimp [g]
          have ha_not : a ∉ (BoundedInterval.Ioc a b : Set ℝ) := by
            simp
          exact if_neg ha_not
        have hg_int_K : IntegrableOn g (BoundedInterval.Icc a a) :=
          hg_int_zero_on (BoundedInterval.Icc a a) hg_zero_on_Icc_aa
        rcases IntegrableOn.of_join h_join hg_int_K hg_int_I with ⟨hJ, _⟩
        simpa using hJ
      | Ico a b =>
        intro hg_int_I
        have ha_lt_b : a < b := by
          have hx' : x ∈ Set.Ico a b := by simpa [BoundedInterval.set_Ico] using hx
          exact hx'.1.trans_lt hx'.2
        have h_join : (BoundedInterval.Icc a b).joins (BoundedInterval.Ico a b) (BoundedInterval.Icc b b) :=
          BoundedInterval.join_Ico_Icc ha_lt_b.le (le_refl b)
        have hg_zero_on_Icc_bb : ∀ x, x ∈ (BoundedInterval.Icc b b : Set ℝ) → g x = 0 := by
          intro x hx'
          have hx_eq_b : x = b := by
            simpa [BoundedInterval.set_Icc] using hx'
          rw [hx_eq_b]
          dsimp [g]
          have hb_not : b ∉ (BoundedInterval.Ico a b : Set ℝ) := by
            simp
          exact if_neg hb_not
        have hg_int_K : IntegrableOn g (BoundedInterval.Icc b b) :=
          hg_int_zero_on (BoundedInterval.Icc b b) hg_zero_on_Icc_bb
        rcases IntegrableOn.of_join h_join hg_int_I hg_int_K with ⟨hJ, _⟩
        simpa using hJ
      | Ioo a b =>
        intro hg_int_I
        have ha_lt_b : a < b := by
          have hx' : x ∈ Set.Ioo a b := by simpa [BoundedInterval.set_Ioo] using hx
          exact hx'.1.trans hx'.2
        have h_join_left : (BoundedInterval.Ico a b).joins (BoundedInterval.Icc a a) (BoundedInterval.Ioo a b) :=
          BoundedInterval.join_Icc_Ioo (le_refl a) ha_lt_b
        have hg_zero_on_Icc_aa : ∀ x, x ∈ (BoundedInterval.Icc a a : Set ℝ) → g x = 0 := by
          intro x hx'
          have hx_eq_a : x = a := by
            simpa [BoundedInterval.set_Icc] using hx'
          rw [hx_eq_a]
          dsimp [g]
          have ha_not : a ∉ (BoundedInterval.Ioo a b : Set ℝ) := by
            simp
          exact if_neg ha_not
        have hg_int_K_a : IntegrableOn g (BoundedInterval.Icc a a) :=
          hg_int_zero_on (BoundedInterval.Icc a a) hg_zero_on_Icc_aa
        rcases IntegrableOn.of_join h_join_left hg_int_K_a hg_int_I with ⟨hIco, _⟩
        have h_join_right : (BoundedInterval.Icc a b).joins (BoundedInterval.Ico a b) (BoundedInterval.Icc b b) :=
          BoundedInterval.join_Ico_Icc ha_lt_b.le (le_refl b)
        have hg_zero_on_Icc_bb : ∀ x, x ∈ (BoundedInterval.Icc b b : Set ℝ) → g x = 0 := by
          intro x hx'
          have hx_eq_b : x = b := by
            simpa [BoundedInterval.set_Icc] using hx'
          rw [hx_eq_b]
          dsimp [g]
          have hb_not : b ∉ (BoundedInterval.Ioo a b : Set ℝ) := by
            simp
          exact if_neg hb_not
        have hg_int_K_b : IntegrableOn g (BoundedInterval.Icc b b) :=
          hg_int_zero_on (BoundedInterval.Icc b b) hg_zero_on_Icc_bb
        rcases IntegrableOn.of_join h_join_right hIco hg_int_K_b with ⟨hJ, _⟩
        simpa using hJ
    -- Step 2: extend from Icc I.a I.b to Icc J.a J.b
    have hg_int_Icc_JJ : IntegrableOn g (BoundedInterval.Icc J.a J.b) := by
      by_cases ha_lt : J.a < I.a
      · -- left extension needed
        have h_join_left : (BoundedInterval.Icc J.a I.b).joins (BoundedInterval.Ico J.a I.a) (BoundedInterval.Icc I.a I.b) :=
          BoundedInterval.join_Ico_Icc ha_lt.le ha_le_b
        have hg_zero_on_Ico : ∀ x, x ∈ (BoundedInterval.Ico J.a I.a : Set ℝ) → g x = 0 := by
          intro x hx'
          dsimp [g]
          have hxJco : x ∈ Set.Ico J.a I.a := by simpa [BoundedInterval.set_Ico] using hx'
          rcases hxJco with ⟨hJax, hxIa⟩
          refine if_neg ?_
          intro hxI
          have hxIcc : x ∈ (BoundedInterval.Icc I.a I.b : Set ℝ) := BoundedInterval.subset_Icc I x hxI
          rcases hxIcc with ⟨hIax, hxIb⟩
          linarith
        have hg_int_K_left : IntegrableOn g (BoundedInterval.Ico J.a I.a) :=
          hg_int_zero_on (BoundedInterval.Ico J.a I.a) hg_zero_on_Ico
        rcases IntegrableOn.of_join h_join_left hg_int_K_left hg_int_Icc with ⟨hIcc_JI, _⟩
        by_cases hb_lt : I.b < J.b
        · -- both extensions needed
          have h_join_right : (BoundedInterval.Icc J.a J.b).joins (BoundedInterval.Icc J.a I.b) (BoundedInterval.Ioc I.b J.b) :=
            BoundedInterval.join_Icc_Ioc (ha_ineq.trans ha_le_b) hb_lt.le
          have hg_zero_on_Ioc : ∀ x, x ∈ (BoundedInterval.Ioc I.b J.b : Set ℝ) → g x = 0 := by
            intro x hx'
            dsimp [g]
            have hxIoc : x ∈ Set.Ioc I.b J.b := by simpa [BoundedInterval.set_Ioc] using hx'
            rcases hxIoc with ⟨hxIb, hxJb⟩
            refine if_neg ?_
            intro hxI
            have hxIcc : x ∈ (BoundedInterval.Icc I.a I.b : Set ℝ) := BoundedInterval.subset_Icc I x hxI
            rcases hxIcc with ⟨hIax, hxIbb⟩
            linarith
          have hg_int_K_right : IntegrableOn g (BoundedInterval.Ioc I.b J.b) :=
            hg_int_zero_on (BoundedInterval.Ioc I.b J.b) hg_zero_on_Ioc
          rcases IntegrableOn.of_join h_join_right hIcc_JI hg_int_K_right with ⟨hJ, _⟩
          exact hJ
        · -- only left extension needed
          have hb_eq : I.b = J.b := le_antisymm hb_ineq (le_of_not_gt hb_lt)
          rw [hb_eq] at hIcc_JI; exact hIcc_JI
      · -- no left extension needed
        have ha_eq : J.a = I.a := le_antisymm ha_ineq (le_of_not_gt ha_lt)
        have hg_int_Icc_JI : IntegrableOn g (BoundedInterval.Icc J.a I.b) := by
          rw [ha_eq]; exact hg_int_Icc
        by_cases hb_lt : I.b < J.b
        · -- only right extension needed
          have h_join_right : (BoundedInterval.Icc J.a J.b).joins (BoundedInterval.Icc J.a I.b) (BoundedInterval.Ioc I.b J.b) :=
            BoundedInterval.join_Icc_Ioc (ha_ineq.trans ha_le_b) hb_lt.le
          have hg_zero_on_Ioc : ∀ x, x ∈ (BoundedInterval.Ioc I.b J.b : Set ℝ) → g x = 0 := by
            intro x hx'
            dsimp [g]
            have hxIoc : x ∈ Set.Ioc I.b J.b := by simpa [BoundedInterval.set_Ioc] using hx'
            rcases hxIoc with ⟨hxIb, hxJb⟩
            refine if_neg ?_
            intro hxI
            have hxIcc : x ∈ (BoundedInterval.Icc I.a I.b : Set ℝ) := BoundedInterval.subset_Icc I x hxI
            rcases hxIcc with ⟨hIax, hxIbb⟩
            linarith
          have hg_int_K_right : IntegrableOn g (BoundedInterval.Ioc I.b J.b) :=
            hg_int_zero_on (BoundedInterval.Ioc I.b J.b) hg_zero_on_Ioc
          rcases IntegrableOn.of_join h_join_right hg_int_Icc_JI hg_int_K_right with ⟨hJ, _⟩
          exact hJ
        · -- no extension needed
          have hb_eq : I.b = J.b := le_antisymm hb_ineq (le_of_not_gt hb_lt)
          have : BoundedInterval.Icc J.a J.b = BoundedInterval.Icc I.a I.b := by rw [ha_eq, hb_eq]
          rw [this]; exact hg_int_Icc
    -- From g integrable on Icc J.a J.b, get g integrable on J by removing endpoints (reverse of Step 1)
    have hg_int_J : IntegrableOn g J := by
      -- Use `cases` on J to get pattern variables
      revert hg_int_Icc_JJ
      cases J with
      | Icc a b =>
        intro hg_int_Icc_JJ
        exact hg_int_Icc_JJ
      | Ioc a b =>
        intro hg_int_Icc_JJ
        have ha_lt_b : a < b := by
          have hx_J : x ∈ (BoundedInterval.Ioc a b : Set ℝ) := hIJ x hx
          have hx_Icc : x ∈ (BoundedInterval.Icc a b : Set ℝ) :=
            (BoundedInterval.subset_Icc (BoundedInterval.Ioc a b) x hx_J)
          rcases hx_Icc with ⟨h_a_le_x, hx_le_b⟩
          by_cases ha_eq_b : a = b
          · exfalso
            have hx_empty : x ∉ (BoundedInterval.Ioc a b : Set ℝ) := by simp [ha_eq_b]
            exact hx_empty hx_J
          · have : a < b := lt_of_le_of_ne (h_a_le_x.trans hx_le_b) ha_eq_b
            exact this
        have h_join : (BoundedInterval.Icc a b).joins (BoundedInterval.Icc a a) (BoundedInterval.Ioc a b) :=
          BoundedInterval.join_Icc_Ioc (le_refl a) ha_lt_b.le
        rcases IntegrableOn.join h_join hg_int_Icc_JJ with ⟨h_left, hJ, _⟩
        exact hJ
      | Ico a b =>
        intro hg_int_Icc_JJ
        have ha_lt_b : a < b := by
          have hx_J : x ∈ (BoundedInterval.Ico a b : Set ℝ) := hIJ x hx
          have hx_Icc : x ∈ (BoundedInterval.Icc a b : Set ℝ) :=
            (BoundedInterval.subset_Icc (BoundedInterval.Ico a b) x hx_J)
          rcases hx_Icc with ⟨h_a_le_x, hx_le_b⟩
          by_cases ha_eq_b : a = b
          · exfalso
            have hx_empty : x ∉ (BoundedInterval.Ico a b : Set ℝ) := by simp [ha_eq_b]
            exact hx_empty hx_J
          · have : a < b := lt_of_le_of_ne (h_a_le_x.trans hx_le_b) ha_eq_b
            exact this
        have h_join : (BoundedInterval.Icc a b).joins (BoundedInterval.Ico a b) (BoundedInterval.Icc b b) :=
          BoundedInterval.join_Ico_Icc ha_lt_b.le (le_refl b)
        rcases IntegrableOn.join h_join hg_int_Icc_JJ with ⟨hJ, h_right, _⟩
        exact hJ
      | Ioo a b =>
        intro hg_int_Icc_JJ
        have ha_lt_b : a < b := by
          have hx_J : x ∈ (BoundedInterval.Ioo a b : Set ℝ) := hIJ x hx
          have hx_Icc : x ∈ (BoundedInterval.Icc a b : Set ℝ) :=
            (BoundedInterval.subset_Icc (BoundedInterval.Ioo a b) x hx_J)
          rcases hx_Icc with ⟨h_a_le_x, hx_le_b⟩
          by_cases ha_eq_b : a = b
          · exfalso
            have hx_empty : x ∉ (BoundedInterval.Ioo a b : Set ℝ) := by simp [ha_eq_b]
            exact hx_empty hx_J
          · have : a < b := lt_of_le_of_ne (h_a_le_x.trans hx_le_b) ha_eq_b
            exact this
        have h_join1 : (BoundedInterval.Icc a b).joins (BoundedInterval.Icc a a) (BoundedInterval.Ioc a b) :=
          BoundedInterval.join_Icc_Ioc (le_refl a) ha_lt_b.le
        rcases IntegrableOn.join h_join1 hg_int_Icc_JJ with ⟨h_left, h_oc, _⟩
        have h_join2 : (BoundedInterval.Ioc a b).joins (BoundedInterval.Ioo a b) (BoundedInterval.Icc b b) :=
          BoundedInterval.join_Ioo_Icc ha_lt_b (le_refl b)
        rcases IntegrableOn.join h_join2 h_oc with ⟨hJ, h_right, _⟩
        exact hJ
    exact hg_int_J

open Classical in
/-- Theorem 11.4.1(g') / Exercise 11.4.1 -/
theorem IntegrableOn.of_extend' {I J: BoundedInterval} (hIJ: I ⊆ J)
  {f: ℝ → ℝ} (h: IntegrableOn f I) :
  integ (fun x ↦ if x ∈ I then f x else 0) J = integ f I := by
  set g := fun x ↦ if x ∈ I then f x else 0 with hg_def
  have hg_on_I : Set.EqOn g f I := by
    intro x hx; dsimp [g]; exact if_pos hx
  have h_integ_eq_on_I : integ g I = integ f I := integ_congr hg_on_I
  have hg_zero_on : ∀ (K : BoundedInterval), (K : Set ℝ) ∩ (I : Set ℝ) = ∅ → Set.EqOn g (fun _ : ℝ ↦ 0) K := by
    intro K h_disjoint x hx
    have hx_not_I : x ∉ (I : Set ℝ) := by
      intro hxI
      have : x ∈ (K : Set ℝ) ∩ (I : Set ℝ) := ⟨hx, hxI⟩
      rw [h_disjoint] at this; exact this
    dsimp [g]; exact if_neg hx_not_I
  have h_integ_zero_on : ∀ (K : BoundedInterval), (K : Set ℝ) ∩ (I : Set ℝ) = ∅ → integ g K = 0 := by
    intro K h_disjoint
    calc
      integ g K = integ (fun _ : ℝ ↦ 0) K := integ_congr (hg_zero_on K h_disjoint)
      _ = 0 := by simpa using (IntegrableOn.const 0 K).2
  have h_int_g_J : IntegrableOn g J := IntegrableOn.of_extend hIJ h
  have h_int_g_I : IntegrableOn g I := by
    rcases h with ⟨hbdd, h_eq⟩
    refine ⟨?_, ?_⟩
    · rcases hbdd with ⟨M, hM⟩
      refine ⟨M, λ x hx => ?_⟩
      have hgx : g x = f x := by dsimp [g]; exact if_pos hx
      rw [hgx]; exact hM x hx
    · rw [lower_integral_congr hg_on_I, upper_integral_congr hg_on_I, h_eq]
  have hg_int_zero_on (K : BoundedInterval) (h_disjoint : (K : Set ℝ) ∩ (I : Set ℝ) = ∅) : IntegrableOn g K := by
    have hg_zero : Set.EqOn g (fun _ : ℝ => 0) K := hg_zero_on K h_disjoint
    have h0_int : IntegrableOn (fun _ : ℝ => 0) K := (IntegrableOn.const 0 K).1
    rcases h0_int with ⟨hbdd, h_eq⟩
    refine ⟨?_, ?_⟩
    · rcases hbdd with ⟨M, hM⟩
      refine ⟨M, λ x hx => ?_⟩
      rw [hg_zero hx]; exact hM x hx
    · rw [lower_integral_congr hg_zero, upper_integral_congr hg_zero, h_eq]
  by_cases hI_empty : (I : Set ℝ) = ∅
  · have hg_zero : g = (fun _ : ℝ => 0) := by
      ext x
      dsimp [g]
      have hx_not_I : x ∉ (I : Set ℝ) := by rw [hI_empty]; simp
      exact if_neg hx_not_I
    have hzero_I : integ (fun _ : ℝ => 0) I = 0 := by
      simpa using (IntegrableOn.const 0 I).2
    have hzero_J : integ (fun _ : ℝ => 0) J = 0 := by
      simpa using (IntegrableOn.const 0 J).2
    calc
      integ g J = integ (fun _ : ℝ => 0) J := by rw [hg_zero]
      _ = 0 := hzero_J
      _ = integ (fun _ : ℝ => 0) I := by rw [hzero_I]
      _ = integ g I := by rw [hg_zero]
      _ = integ f I := h_integ_eq_on_I
  · have hI_nonempty : (I : Set ℝ).Nonempty := Set.nonempty_iff_ne_empty.mpr hI_empty
    rcases hI_nonempty with ⟨x, hx⟩
    have ha_le_b : I.a ≤ I.b := by
      have hx_Icc : x ∈ (BoundedInterval.Icc I.a I.b : Set ℝ) := BoundedInterval.subset_Icc I x hx
      rcases hx_Icc with ⟨hI_a_le_x, hx_le_I_b⟩
      exact hI_a_le_x.trans hx_le_I_b
    have ha_ineq : J.a ≤ I.a := by
      by_cases ha_mem : I.a ∈ (I : Set ℝ)
      · have haJ : I.a ∈ (J : Set ℝ) := hIJ (I.a) ha_mem
        exact (BoundedInterval.subset_Icc J (I.a) haJ).1
      · by_contra! H
        have ha_lt_Ja : I.a < J.a := H
        have ha_lt_b : I.a < I.b := by
          have hx_Icc : x ∈ (BoundedInterval.Icc I.a I.b : Set ℝ) := BoundedInterval.subset_Icc I x hx
          rcases hx_Icc with ⟨hI_a_le_x, hx_le_I_b⟩
          by_cases ha_eq_b : I.a = I.b
          · exfalso; exact ha_mem (by
              have hx_eq_a : x = I.a := le_antisymm (by linarith) hI_a_le_x
              rw [← hx_eq_a]; exact hx)
          · have : I.a ≤ I.b := hI_a_le_x.trans hx_le_I_b
            by_contra! hge; apply ha_eq_b; linarith
        have ha_le_b_J : J.a ≤ I.b := by
          have hxJ : x ∈ (J : Set ℝ) := hIJ x hx
          have hxJ_Icc : x ∈ (BoundedInterval.Icc J.a J.b : Set ℝ) := BoundedInterval.subset_Icc J x hxJ
          have hxI_Icc : x ∈ (BoundedInterval.Icc I.a I.b : Set ℝ) := BoundedInterval.subset_Icc I x hx
          rcases hxJ_Icc with ⟨hJ_a_le_x, _⟩
          rcases hxI_Icc with ⟨_, hx_le_I_b⟩
          exact hJ_a_le_x.trans hx_le_I_b
        set y := (I.a + J.a) / 2
        have ha_y : I.a < y := by dsimp [y]; nlinarith
        have hy_b : y < I.b := by
          dsimp [y]
          have : J.a ≤ I.b := ha_le_b_J
          nlinarith
        have hy_I : y ∈ (I : Set ℝ) := by
          have hy_Ioo : y ∈ (BoundedInterval.Ioo I.a I.b : Set ℝ) := by
            simp [BoundedInterval.set_Ioo, ha_y, hy_b]
          exact BoundedInterval.Ioo_subset I y hy_Ioo
        have hy_J : y ∈ (J : Set ℝ) := hIJ y hy_I
        have hJ_a_le_y : J.a ≤ y := (BoundedInterval.subset_Icc J y hy_J).1
        have hy_lt_Ja : y < J.a := by
          dsimp [y]; nlinarith
        linarith
    have hb_ineq : I.b ≤ J.b := by
      by_cases hb_mem : I.b ∈ (I : Set ℝ)
      · have hbJ : I.b ∈ (J : Set ℝ) := hIJ (I.b) hb_mem
        exact (BoundedInterval.subset_Icc J (I.b) hbJ).2
      · by_contra! H
        have hb_lt : J.b < I.b := H
        have ha_lt_b : I.a < I.b := by
          have hx_Icc : x ∈ (BoundedInterval.Icc I.a I.b : Set ℝ) := BoundedInterval.subset_Icc I x hx
          rcases hx_Icc with ⟨hI_a_le_x, hx_le_I_b⟩
          by_cases ha_eq_b : I.a = I.b
          · exfalso; exact hb_mem (by
              have hx_eq_b : x = I.b := le_antisymm hx_le_I_b (by linarith)
              rw [← hx_eq_b]; exact hx)
          · have : I.a ≤ I.b := hI_a_le_x.trans hx_le_I_b
            by_contra! hge; apply ha_eq_b; linarith
        set m := max I.a J.b with hm_def
        have hm_lt_Ib : m < I.b := max_lt ha_lt_b hb_lt
        set y := (m + I.b) / 2
        have ha_y : I.a < y := by
          dsimp [y, m]; have : I.a ≤ max I.a J.b := le_max_left _ _; nlinarith
        have hy_b : y < I.b := by dsimp [y, m]; nlinarith
        have hy_I : y ∈ (I : Set ℝ) := by
          have hy_Ioo : y ∈ (BoundedInterval.Ioo I.a I.b : Set ℝ) := by
            simp [BoundedInterval.set_Ioo, ha_y, hy_b]
          exact BoundedInterval.Ioo_subset I y hy_Ioo
        have hy_J : y ∈ (J : Set ℝ) := hIJ y hy_I
        have hy_le_Jb : y ≤ J.b := (BoundedInterval.subset_Icc J y hy_J).2
        have Jb_lt_y : J.b < y := by
          have : J.b ≤ m := le_max_right _ _; dsimp [y]; nlinarith
        linarith
    -- Step 1: integ g (Icc I.a I.b) = integ g I
    have h_step1 : integ g (BoundedInterval.Icc I.a I.b) = integ g I := by
      have h_int_g_Icc_I : IntegrableOn g (BoundedInterval.Icc I.a I.b) :=
        IntegrableOn.of_extend (by
          intro y hy; exact BoundedInterval.subset_Icc I y hy) h
      cases I with
      | Icc a b => rfl
      | Ico a b =>
        have ha_le_b' : a ≤ b := by simpa using ha_le_b
        have h_join : (BoundedInterval.Icc a b).joins (BoundedInterval.Ico a b) (BoundedInterval.Icc b b) :=
          BoundedInterval.join_Ico_Icc ha_le_b' (le_refl b)
        have h_int_g_Ico : IntegrableOn g (BoundedInterval.Ico a b) := by
          simpa using h_int_g_I
        have h_disjoint : (BoundedInterval.Icc b b : Set ℝ) ∩ (BoundedInterval.Ico a b : Set ℝ) = ∅ := by
          ext x; simp [BoundedInterval.set_Icc, BoundedInterval.set_Ico]
        have h_int_g_Icc_bb : IntegrableOn g (BoundedInterval.Icc b b) :=
          hg_int_zero_on (BoundedInterval.Icc b b) h_disjoint
        rcases IntegrableOn.of_join h_join h_int_g_Ico h_int_g_Icc_bb with ⟨_, h_eq⟩
        rw [h_eq, h_integ_zero_on (BoundedInterval.Icc b b) h_disjoint, add_zero]
      | Ioc a b =>
        have ha_le_b' : a ≤ b := by simpa using ha_le_b
        have h_join : (BoundedInterval.Icc a b).joins (BoundedInterval.Icc a a) (BoundedInterval.Ioc a b) :=
          BoundedInterval.join_Icc_Ioc (le_refl a) ha_le_b'
        have h_int_g_Ioc : IntegrableOn g (BoundedInterval.Ioc a b) := by
          simpa using h_int_g_I
        have h_disjoint : (BoundedInterval.Icc a a : Set ℝ) ∩ (BoundedInterval.Ioc a b : Set ℝ) = ∅ := by
          ext x; simp [BoundedInterval.set_Icc, BoundedInterval.set_Ioc]
        have h_int_g_Icc_aa : IntegrableOn g (BoundedInterval.Icc a a) :=
          hg_int_zero_on (BoundedInterval.Icc a a) h_disjoint
        rcases IntegrableOn.of_join h_join h_int_g_Icc_aa h_int_g_Ioc with ⟨_, h_eq⟩
        rw [h_eq, h_integ_zero_on (BoundedInterval.Icc a a) h_disjoint, zero_add]
      | Ioo a b =>
        have ha_lt_b' : a < b := by
          have hx_Ioo : x ∈ Set.Ioo a b := by
            have : x ∈ (BoundedInterval.Ioo a b : Set ℝ) := hx
            simpa [BoundedInterval.set_Ioo] using this
          exact hx_Ioo.1.trans hx_Ioo.2
        have h_join1 : (BoundedInterval.Ico a b).joins (BoundedInterval.Icc a a) (BoundedInterval.Ioo a b) :=
          BoundedInterval.join_Icc_Ioo (le_refl a) ha_lt_b'
        have h_int_g_Ioo : IntegrableOn g (BoundedInterval.Ioo a b) := by
          simpa using h_int_g_I
        have h_disjoint1 : (BoundedInterval.Icc a a : Set ℝ) ∩ (BoundedInterval.Ioo a b : Set ℝ) = ∅ := by
          ext x; simp [BoundedInterval.set_Icc, BoundedInterval.set_Ioo]
        have h_int_g_Icc_aa : IntegrableOn g (BoundedInterval.Icc a a) :=
          hg_int_zero_on (BoundedInterval.Icc a a) h_disjoint1
        rcases IntegrableOn.of_join h_join1 h_int_g_Icc_aa h_int_g_Ioo with ⟨h_int_g_Ico, h_eq1⟩
        have h_join2 : (BoundedInterval.Icc a b).joins (BoundedInterval.Ico a b) (BoundedInterval.Icc b b) :=
          BoundedInterval.join_Ico_Icc (le_of_lt ha_lt_b') (le_refl b)
        have h_disjoint2 : (BoundedInterval.Icc b b : Set ℝ) ∩ (BoundedInterval.Ioo a b : Set ℝ) = ∅ := by
          ext x; simp [BoundedInterval.set_Icc, BoundedInterval.set_Ioo]
        have h_int_g_Icc_bb : IntegrableOn g (BoundedInterval.Icc b b) :=
          hg_int_zero_on (BoundedInterval.Icc b b) h_disjoint2
        rcases IntegrableOn.of_join h_join2 h_int_g_Ico h_int_g_Icc_bb with ⟨_, h_eq2⟩
        rw [h_eq2, h_integ_zero_on (BoundedInterval.Icc b b) h_disjoint2, add_zero, h_eq1,
          h_integ_zero_on (BoundedInterval.Icc a a) h_disjoint1, zero_add]
    -- Step 2: integ g (Icc J.a J.b) = integ g (Icc I.a I.b)
    have h_step2 : integ g (BoundedInterval.Icc J.a J.b) = integ g (BoundedInterval.Icc I.a I.b) := by
      have h_sub_I_IccJ : I ⊆ (BoundedInterval.Icc J.a J.b) := by
        intro y hy
        have hyJ : y ∈ J := hIJ y hy
        exact BoundedInterval.subset_Icc J y hyJ
      have h_int_g_Icc_J : IntegrableOn g (BoundedInterval.Icc J.a J.b) :=
        IntegrableOn.of_extend h_sub_I_IccJ h
      have h_sub_I_IccI : I ⊆ (BoundedInterval.Icc I.a I.b) := by
        intro y hy; exact BoundedInterval.subset_Icc I y hy
      have h_int_g_Icc_I : IntegrableOn g (BoundedInterval.Icc I.a I.b) :=
        IntegrableOn.of_extend h_sub_I_IccI h
      by_cases ha_lt : J.a < I.a
      · by_cases hb_lt : I.b < J.b
        · -- Extend on both sides
          have h_join_left : (BoundedInterval.Icc J.a I.b).joins (BoundedInterval.Ico J.a I.a) (BoundedInterval.Icc I.a I.b) :=
            BoundedInterval.join_Ico_Icc ha_lt.le ha_le_b
          have h_disjoint_left : (BoundedInterval.Ico J.a I.a : Set ℝ) ∩ (I : Set ℝ) = ∅ := by
            apply Set.not_nonempty_iff_eq_empty.mp; intro h_nonempty
            rcases h_nonempty with ⟨y, hyL, hyI⟩
            have hy_lt_Ia : y < I.a := by
              rcases hyL with ⟨_, hy_lt_Ia⟩; exact hy_lt_Ia
            have hy_ge_Ia : I.a ≤ y := by
              have hy_Icc : y ∈ (BoundedInterval.Icc I.a I.b : Set ℝ) := BoundedInterval.subset_Icc I y hyI
              rcases hy_Icc with ⟨hIa_le_y, _⟩; exact hIa_le_y
            linarith
          have h_int_g_L : IntegrableOn g (BoundedInterval.Ico J.a I.a) :=
            hg_int_zero_on (BoundedInterval.Ico J.a I.a) h_disjoint_left
          rcases IntegrableOn.of_join h_join_left h_int_g_L h_int_g_Icc_I with ⟨h_int_g_mid, h_eq_left⟩
          have h_Ja_le_Ib : J.a ≤ I.b := calc
            J.a ≤ I.a := ha_lt.le
            _ ≤ I.b := ha_le_b
          have h_join_right : (BoundedInterval.Icc J.a J.b).joins (BoundedInterval.Icc J.a I.b) (BoundedInterval.Ioc I.b J.b) :=
            BoundedInterval.join_Icc_Ioc h_Ja_le_Ib hb_lt.le
          have h_disjoint_right : (BoundedInterval.Ioc I.b J.b : Set ℝ) ∩ (I : Set ℝ) = ∅ := by
            apply Set.not_nonempty_iff_eq_empty.mp; intro h_nonempty
            rcases h_nonempty with ⟨y, hyR, hyI⟩
            have hy_gt_Ib : I.b < y := by
              rcases hyR with ⟨hIb_lt_y, _⟩; exact hIb_lt_y
            have hy_le_Ib : y ≤ I.b := by
              have hy_Icc : y ∈ (BoundedInterval.Icc I.a I.b : Set ℝ) := BoundedInterval.subset_Icc I y hyI
              rcases hy_Icc with ⟨_, hy_le_Ib⟩; exact hy_le_Ib
            linarith
          have h_int_g_R : IntegrableOn g (BoundedInterval.Ioc I.b J.b) :=
            hg_int_zero_on (BoundedInterval.Ioc I.b J.b) h_disjoint_right
          rcases IntegrableOn.of_join h_join_right h_int_g_mid h_int_g_R with ⟨_, h_eq_right⟩
          rw [h_eq_right, h_eq_left, h_integ_zero_on (BoundedInterval.Ico J.a I.a) h_disjoint_left,
            h_integ_zero_on (BoundedInterval.Ioc I.b J.b) h_disjoint_right]
          simp
        · -- Extend left only
          have h_join : (BoundedInterval.Icc J.a I.b).joins (BoundedInterval.Ico J.a I.a) (BoundedInterval.Icc I.a I.b) :=
            BoundedInterval.join_Ico_Icc ha_lt.le ha_le_b
          have h_disjoint_left : (BoundedInterval.Ico J.a I.a : Set ℝ) ∩ (I : Set ℝ) = ∅ := by
            apply Set.not_nonempty_iff_eq_empty.mp; intro h_nonempty
            rcases h_nonempty with ⟨y, hyL, hyI⟩
            have hy_lt_Ia : y < I.a := by
              rcases hyL with ⟨_, hy_lt_Ia⟩; exact hy_lt_Ia
            have hy_ge_Ia : I.a ≤ y := by
              have hy_Icc : y ∈ (BoundedInterval.Icc I.a I.b : Set ℝ) := BoundedInterval.subset_Icc I y hyI
              rcases hy_Icc with ⟨hIa_le_y, _⟩; exact hIa_le_y
            linarith
          have h_int_g_L : IntegrableOn g (BoundedInterval.Ico J.a I.a) :=
            hg_int_zero_on (BoundedInterval.Ico J.a I.a) h_disjoint_left
          rcases IntegrableOn.of_join h_join h_int_g_L h_int_g_Icc_I with ⟨h_int_g_mid, h_eq⟩
          have hb_eq : I.b = J.b := le_antisymm hb_ineq (le_of_not_gt hb_lt)
          have hJ_eq : BoundedInterval.Icc J.a J.b = BoundedInterval.Icc J.a I.b := by rw [hb_eq]
          rw [hJ_eq, h_eq, h_integ_zero_on (BoundedInterval.Ico J.a I.a) h_disjoint_left]; simp
      · -- No left extension
        have ha_eq : J.a = I.a := le_antisymm ha_ineq (le_of_not_gt ha_lt)
        have hIcc_J_eq : BoundedInterval.Icc J.a J.b = BoundedInterval.Icc I.a J.b := by rw [ha_eq]
        rw [hIcc_J_eq]
        by_cases hb_lt : I.b < J.b
        · -- Extend right only
          have h_join : (BoundedInterval.Icc I.a J.b).joins (BoundedInterval.Icc I.a I.b) (BoundedInterval.Ioc I.b J.b) :=
            BoundedInterval.join_Icc_Ioc ha_le_b hb_lt.le
          have h_disjoint_right : (BoundedInterval.Ioc I.b J.b : Set ℝ) ∩ (I : Set ℝ) = ∅ := by
            apply Set.not_nonempty_iff_eq_empty.mp; intro h_nonempty
            rcases h_nonempty with ⟨y, hyR, hyI⟩
            have hy_gt_Ib : I.b < y := by
              rcases hyR with ⟨hIb_lt_y, _⟩; exact hIb_lt_y
            have hy_le_Ib : y ≤ I.b := by
              have hy_Icc : y ∈ (BoundedInterval.Icc I.a I.b : Set ℝ) := BoundedInterval.subset_Icc I y hyI
              rcases hy_Icc with ⟨_, hy_le_Ib⟩; exact hy_le_Ib
            linarith
          have h_int_g_R : IntegrableOn g (BoundedInterval.Ioc I.b J.b) :=
            hg_int_zero_on (BoundedInterval.Ioc I.b J.b) h_disjoint_right
          rcases IntegrableOn.of_join h_join h_int_g_Icc_I h_int_g_R with ⟨_, h_eq⟩
          rw [h_eq, h_integ_zero_on (BoundedInterval.Ioc I.b J.b) h_disjoint_right, add_zero]
        · -- No extension
          have hb_eq : I.b = J.b := le_antisymm hb_ineq (le_of_not_gt hb_lt)
          rw [hb_eq]
    -- Step 3: integ g J = integ g (Icc J.a J.b)
    have h_step3 : integ g J = integ g (BoundedInterval.Icc J.a J.b) := by
      have h_sub_I_IccJ : I ⊆ (BoundedInterval.Icc J.a J.b) := by
        intro y hy
        have hyJ : y ∈ J := hIJ y hy
        exact BoundedInterval.subset_Icc J y hyJ
      have h_int_g_Icc_J : IntegrableOn g (BoundedInterval.Icc J.a J.b) :=
        IntegrableOn.of_extend h_sub_I_IccJ h
      cases J with
      | Icc a' b' => rfl
      | Ico a' b' =>
        have ha'_le_b' : a' ≤ b' := by
          have hx_Icc : x ∈ (BoundedInterval.Icc a' b' : Set ℝ) := BoundedInterval.subset_Icc (BoundedInterval.Ico a' b') x (hIJ x hx)
          rcases hx_Icc with ⟨ha'_le_x, hx_le_b'⟩; exact ha'_le_x.trans hx_le_b'
        have h_join : (BoundedInterval.Icc a' b').joins (BoundedInterval.Ico a' b') (BoundedInterval.Icc b' b') :=
          BoundedInterval.join_Ico_Icc ha'_le_b' (le_refl b')
        rcases IntegrableOn.join h_join h_int_g_Icc_J with ⟨h_Ico, _, h_eq⟩
        have hb'_not_I : b' ∉ (I : Set ℝ) := by
          intro hb'I
          have hmem : b' ∈ (BoundedInterval.Ico a' b' : Set ℝ) := hIJ b' hb'I
          simp [BoundedInterval.set_Ico] at hmem
        have h_zero : integ g (BoundedInterval.Icc b' b') = 0 := by
          apply h_integ_zero_on (BoundedInterval.Icc b' b')
          apply Set.not_nonempty_iff_eq_empty.mp; intro h_nonempty
          rcases h_nonempty with ⟨y, hy, hyI⟩
          have hy_eq_b' : y = b' := by simpa [BoundedInterval.set_Icc] using hy
          subst hy_eq_b'; exact hb'_not_I hyI
        linarith
      | Ioc a' b' =>
        have ha'_le_b' : a' ≤ b' := by
          have hx_Icc : x ∈ (BoundedInterval.Icc a' b' : Set ℝ) := BoundedInterval.subset_Icc (BoundedInterval.Ioc a' b') x (hIJ x hx)
          rcases hx_Icc with ⟨ha'_le_x, hx_le_b'⟩; exact ha'_le_x.trans hx_le_b'
        have h_join : (BoundedInterval.Icc a' b').joins (BoundedInterval.Icc a' a') (BoundedInterval.Ioc a' b') :=
          BoundedInterval.join_Icc_Ioc (le_refl a') ha'_le_b'
        rcases IntegrableOn.join h_join h_int_g_Icc_J with ⟨h_Icc_aa, h_Ioc, h_eq⟩
        have ha'_not_I : a' ∉ (I : Set ℝ) := by
          intro ha'I
          have hmem : a' ∈ (BoundedInterval.Ioc a' b' : Set ℝ) := hIJ a' ha'I
          simp [BoundedInterval.set_Ioc] at hmem
        have h_zero : integ g (BoundedInterval.Icc a' a') = 0 := by
          apply h_integ_zero_on (BoundedInterval.Icc a' a')
          apply Set.not_nonempty_iff_eq_empty.mp; intro h_nonempty
          rcases h_nonempty with ⟨y, hy, hyI⟩
          have hy_eq_a' : y = a' := by simpa [BoundedInterval.set_Icc] using hy
          subst hy_eq_a'; exact ha'_not_I hyI
        linarith
      | Ioo a' b' =>
        have ha'_lt_b' : a' < b' := by
          have hx_Ioo : x ∈ Set.Ioo a' b' := by
            simpa [BoundedInterval.set_Ioo] using hIJ x hx
          exact hx_Ioo.1.trans hx_Ioo.2
        have ha'_le_b' : a' ≤ b' := le_of_lt ha'_lt_b'
        have h_join2 : (BoundedInterval.Icc a' b').joins (BoundedInterval.Ico a' b') (BoundedInterval.Icc b' b') :=
          BoundedInterval.join_Ico_Icc ha'_le_b' (le_refl b')
        rcases IntegrableOn.join h_join2 h_int_g_Icc_J with ⟨h_Ico, h_Icc_bb, h_eq2⟩
        have h_join1 : (BoundedInterval.Ico a' b').joins (BoundedInterval.Icc a' a') (BoundedInterval.Ioo a' b') :=
          BoundedInterval.join_Icc_Ioo (le_refl a') ha'_lt_b'
        rcases IntegrableOn.join h_join1 h_Ico with ⟨h_Icc_aa, h_Ioo, h_eq1⟩
        have ha'_not_I : a' ∉ (I : Set ℝ) := by
          intro ha'I
          have hmem : a' ∈ (BoundedInterval.Ioo a' b' : Set ℝ) := hIJ a' ha'I
          simp [BoundedInterval.set_Ioo] at hmem
        have hb'_not_I : b' ∉ (I : Set ℝ) := by
          intro hb'I
          have hmem : b' ∈ (BoundedInterval.Ioo a' b' : Set ℝ) := hIJ b' hb'I
          simp [BoundedInterval.set_Ioo] at hmem
        have h_zero_aa : integ g (BoundedInterval.Icc a' a') = 0 := by
          apply h_integ_zero_on (BoundedInterval.Icc a' a')
          apply Set.not_nonempty_iff_eq_empty.mp; intro h_nonempty
          rcases h_nonempty with ⟨y, hy, hyI⟩
          have hy_eq_a' : y = a' := by simpa [BoundedInterval.set_Icc] using hy
          subst hy_eq_a'; exact ha'_not_I hyI
        have h_zero_bb : integ g (BoundedInterval.Icc b' b') = 0 := by
          apply h_integ_zero_on (BoundedInterval.Icc b' b')
          apply Set.not_nonempty_iff_eq_empty.mp; intro h_nonempty
          rcases h_nonempty with ⟨y, hy, hyI⟩
          have hy_eq_b' : y = b' := by simpa [BoundedInterval.set_Icc] using hy
          subst hy_eq_b'; exact hb'_not_I hyI
        nlinarith
    calc
      integ g J = integ g (BoundedInterval.Icc J.a J.b) := h_step3
      _ = integ g (BoundedInterval.Icc I.a I.b) := h_step2
      _ = integ g I := h_step1
      _ = integ f I := h_integ_eq_on_I
/-- A handy little lemma for "epsilon of room" type arguments -/
lemma nonneg_of_le_const_mul_eps {x C:ℝ} (h: ∀ ε>0, x ≤ C * ε) : x ≤ 0 := by
  by_cases hC: C > 0
  . by_contra!
    specialize h (x/(2*C)) (by positivity); convert_to x ≤ x/2 at h; grind
    linarith
  specialize h 1 ?_ <;> grind

lemma a_eq_sInf (I : BoundedInterval) (h_nonempty : (I : Set ℝ).Nonempty) : I.a = sInf (I : Set ℝ) := by
  cases I with
  | Icc a b =>
    have h_ab : a ≤ b := by
      rcases h_nonempty with ⟨x, hx⟩
      have : x ∈ Set.Icc a b := by simpa [BoundedInterval.set_Icc] using hx
      exact this.1.trans this.2
    simp [csInf_Icc h_ab]
  | Ioo a b =>
    have h_ab : a < b := by
      rcases h_nonempty with ⟨x, hx⟩
      have : x ∈ Set.Ioo a b := by simpa [BoundedInterval.set_Ioo] using hx
      exact this.1.trans this.2
    simp [csInf_Ioo h_ab]
  | Ioc a b =>
    have h_ab : a < b := by
      rcases h_nonempty with ⟨x, hx⟩
      have : x ∈ Set.Ioc a b := by simpa [BoundedInterval.set_Ioc] using hx
      exact this.1.trans_le this.2
    simp [csInf_Ioc h_ab]
  | Ico a b =>
    have h_ab : a < b := by
      rcases h_nonempty with ⟨x, hx⟩
      have : x ∈ Set.Ico a b := by simpa [BoundedInterval.set_Ico] using hx
      exact this.1.trans_lt this.2
    simp [csInf_Ico h_ab]

lemma b_eq_sSup (I : BoundedInterval) (h_nonempty : (I : Set ℝ).Nonempty) : I.b = sSup (I : Set ℝ) := by
  cases I with
  | Icc a b =>
    have h_ab : a ≤ b := by
      rcases h_nonempty with ⟨x, hx⟩
      have : x ∈ Set.Icc a b := by simpa [BoundedInterval.set_Icc] using hx
      exact this.1.trans this.2
    simp [csSup_Icc h_ab]
  | Ioo a b =>
    have h_ab : a < b := by
      rcases h_nonempty with ⟨x, hx⟩
      have : x ∈ Set.Ioo a b := by simpa [BoundedInterval.set_Ioo] using hx
      exact this.1.trans this.2
    simp [csSup_Ioo h_ab]
  | Ioc a b =>
    have h_ab : a < b := by
      rcases h_nonempty with ⟨x, hx⟩
      have : x ∈ Set.Ioc a b := by simpa [BoundedInterval.set_Ioc] using hx
      exact this.1.trans_le this.2
    simp [csSup_Ioc h_ab]
  | Ico a b =>
    have h_ab : a < b := by
      rcases h_nonempty with ⟨x, hx⟩
      have : x ∈ Set.Ico a b := by simpa [BoundedInterval.set_Ico] using hx
      exact this.1.trans_lt this.2
    simp [csSup_Ico h_ab]

lemma length_inter_le_length (I J : BoundedInterval) : |I ∩ J|ₗ ≤ |I|ₗ := by
  by_cases h_nonempty : ((I : Set ℝ) ∩ (J : Set ℝ)).Nonempty
  · have hK_nonempty : ((I ∩ J : BoundedInterval) : Set ℝ).Nonempty := by
      simpa [BoundedInterval.inter_eq] using h_nonempty
    have h_subset : ((I ∩ J : BoundedInterval) : Set ℝ) ⊆ (I : Set ℝ) := by
      simp [BoundedInterval.inter_eq]
    have h_bdd_sup : BddAbove (I : Set ℝ) :=
      Bornology.IsBounded.bddAbove (Bornology.IsBounded.of_boundedInterval I)
    have h_bdd_inf : BddBelow (I : Set ℝ) :=
      Bornology.IsBounded.bddBelow (Bornology.IsBounded.of_boundedInterval I)
    have h_sup_K_le_sup_I : sSup ((I ∩ J : BoundedInterval) : Set ℝ) ≤ sSup (I : Set ℝ) :=
      csSup_le_csSup h_bdd_sup hK_nonempty h_subset
    have h_inf_I_le_inf_K : sInf (I : Set ℝ) ≤ sInf ((I ∩ J : BoundedInterval) : Set ℝ) := by
      apply csInf_le_csInf (h_bdd_inf : BddBelow (I : Set ℝ))
      · exact hK_nonempty
      · exact h_subset
    have h_a_K : (I ∩ J : BoundedInterval).a = sInf ((I ∩ J : BoundedInterval) : Set ℝ) :=
      a_eq_sInf (I ∩ J) hK_nonempty
    have h_b_K : (I ∩ J : BoundedInterval).b = sSup ((I ∩ J : BoundedInterval) : Set ℝ) :=
      b_eq_sSup (I ∩ J) hK_nonempty
    have h_sub_nonempty : (I : Set ℝ).Nonempty := by
      rcases hK_nonempty with ⟨x, hx⟩
      exact ⟨x, h_subset hx⟩
    have h_a_I : I.a = sInf (I : Set ℝ) := a_eq_sInf I h_sub_nonempty
    have h_b_I : I.b = sSup (I : Set ℝ) := b_eq_sSup I h_sub_nonempty
    have h_diff_sub : (I ∩ J : BoundedInterval).b - (I ∩ J : BoundedInterval).a ≤ I.b - I.a := by
      rw [h_a_K, h_b_K, h_a_I, h_b_I]
      nlinarith
    calc
      |I ∩ J|ₗ = max ((I ∩ J : BoundedInterval).b - (I ∩ J : BoundedInterval).a) 0 := rfl
      _ ≤ max (I.b - I.a) 0 := by
        apply max_le_max h_diff_sub (le_refl 0)
      _ = |I|ₗ := rfl
  · rw [Set.not_nonempty_iff_eq_empty] at h_nonempty
    have h_len0 : |I ∩ J|ₗ = 0 := by
      apply BoundedInterval.length_of_empty
      simpa [BoundedInterval.inter_eq] using h_nonempty
    rw [h_len0]
    exact BoundedInterval.length_nonneg _

lemma pc_of_subset {I J : BoundedInterval} (hIJ : J ⊆ I) {f : ℝ → ℝ} (hf : PiecewiseConstantOn f I) :
    PiecewiseConstantOn f J := by
  rcases hf with ⟨P, hP⟩
  let P_J : Partition J := {
    intervals := Finset.image (fun (L : BoundedInterval) => L ∩ J) P.intervals
    exists_unique := λ x hx => by
      have hxI : x ∈ I := hIJ x hx
      rcases P.exists_unique x hxI with ⟨L, ⟨hLmem, hxL⟩, huniq⟩
      refine ⟨L ∩ J, ⟨Finset.mem_image.mpr ⟨L, hLmem, rfl⟩, ?_⟩, ?_⟩
      · simpa [BoundedInterval.mem_inter] using And.intro hxL hx
      · intro K' hK'
        rcases hK' with ⟨hK'mem, hxK'⟩
        rcases Finset.mem_image.mp hK'mem with ⟨L', hL'mem, hK'_eq⟩
        subst hK'_eq
        have hxL' : x ∈ (L' : Set ℝ) := by
          have : x ∈ ((L' : Set ℝ) ∩ (J : Set ℝ)) := by
            simpa [BoundedInterval.inter_eq] using hxK'
          exact this.1
        have hL'_eq_L : L' = L := huniq L' ⟨hL'mem, by simpa [BoundedInterval.mem_iff] using hxL'⟩
        subst hL'_eq_L; rfl
    contains := λ L' hL' => by
      rcases Finset.mem_image.mp hL' with ⟨L, hLmem, hL'_eq⟩
      subst hL'_eq
      rw [BoundedInterval.subset_iff, BoundedInterval.inter_eq]
      apply Set.inter_subset_right
  }
  refine ⟨P_J, ?_⟩
  intro L' hL'
  rcases Finset.mem_image.mp hL' with ⟨L, hLmem, hL'_eq⟩
  subst hL'_eq
  rcases hP L hLmem with ⟨c, hc⟩
  refine ⟨c, λ (x : ((L ∩ J : BoundedInterval) : Set ℝ)) => ?_⟩
  have hxL : (x : ℝ) ∈ (L : Set ℝ) := by
    have hx_inter : (x : ℝ) ∈ ((L : Set ℝ) ∩ (J : Set ℝ)) := by
      simpa [BoundedInterval.inter_eq] using x.2
    exact hx_inter.1
  exact hc ⟨x, hxL⟩

lemma integ_nonneg_subset {I J : BoundedInterval} (hIJ : J ⊆ I) {g : ℝ → ℝ}
    (hg : PiecewiseConstantOn g I) (hg_nonneg : ∀ x ∈ I, 0 ≤ g x) : integ g J ≤ integ g I := by
  rcases hg with ⟨P, hP⟩
  let P_J : Partition J := {
    intervals := Finset.image (fun (L : BoundedInterval) => L ∩ J) P.intervals
    exists_unique := λ x hx => by
      have hxI : x ∈ I := hIJ x hx
      rcases P.exists_unique x hxI with ⟨L, ⟨hLmem, hxL⟩, huniq⟩
      refine ⟨L ∩ J, ⟨Finset.mem_image.mpr ⟨L, hLmem, rfl⟩, ?_⟩, ?_⟩
      · simpa [BoundedInterval.mem_inter] using And.intro hxL hx
      · intro K' hK'
        rcases hK' with ⟨hK'mem, hxK'⟩
        rcases Finset.mem_image.mp hK'mem with ⟨L', hL'mem, hK'_eq⟩
        subst hK'_eq
        have hxL' : x ∈ (L' : Set ℝ) := by
          have : x ∈ ((L' : Set ℝ) ∩ (J : Set ℝ)) := by
            simpa [BoundedInterval.inter_eq] using hxK'
          exact this.1
        have hL'_eq_L : L' = L := huniq L' ⟨hL'mem, by simpa [BoundedInterval.mem_iff] using hxL'⟩
        subst hL'_eq_L; rfl
    contains := λ L' hL' => by
      rcases Finset.mem_image.mp hL' with ⟨L, hLmem, hL'_eq⟩
      subst hL'_eq
      rw [BoundedInterval.subset_iff, BoundedInterval.inter_eq]
      apply Set.inter_subset_right
  }
  have hP_J : PiecewiseConstantWith g P_J := by
    intro L' hL'
    rcases Finset.mem_image.mp hL' with ⟨L, hLmem, hL'_eq⟩
    subst hL'_eq
    rcases hP L hLmem with ⟨c, hc⟩
    refine ⟨c, λ (x : ((L ∩ J : BoundedInterval) : Set ℝ)) => ?_⟩
    have hxL : (x : ℝ) ∈ (L : Set ℝ) := by
      have hx_inter : (x : ℝ) ∈ ((L : Set ℝ) ∩ (J : Set ℝ)) := by
        simpa [BoundedInterval.inter_eq] using x.2
      exact hx_inter.1
    exact hc ⟨x, hxL⟩
  have hg' : PiecewiseConstantOn g I := ⟨P, hP⟩
  have h_integ_I : integ g I = PiecewiseConstantWith.integ g P := by
    calc
      integ g I = PiecewiseConstantOn.integ g I := (integ_of_piecewise_const hg').2
      _ = PiecewiseConstantWith.integ g P := PiecewiseConstantOn.integ_def hP
  have h_integ_J : integ g J = PiecewiseConstantWith.integ g P_J := by
    have h_int := integ_of_piecewise_const ⟨P_J, hP_J⟩
    calc
      integ g J = PiecewiseConstantOn.integ g J := h_int.2
      _ = PiecewiseConstantWith.integ g P_J := PiecewiseConstantOn.integ_def hP_J
  rw [h_integ_I, h_integ_J]
  unfold PiecewiseConstantWith.integ
  have h_image : P_J.intervals = Finset.image (fun (L : BoundedInterval) => L ∩ J) P.intervals := rfl
  rw [h_image]
  have h_nonneg_f : ∀ K ∈ Finset.image (fun (L : BoundedInterval) => L ∩ J) P.intervals,
      0 ≤ (constant_value_on g K) * |K|ₗ := by
    intro K hK
    rcases Finset.mem_image.mp hK with ⟨L, hL, hK_eq⟩
    subst hK_eq
    rcases hP L hL with ⟨c, hc⟩
    by_cases h_empty : ((L : Set ℝ) ∩ (J : Set ℝ)).Nonempty
    · have h_nonempty_inter : ((L : Set ℝ) ∩ (J : Set ℝ)).Nonempty := h_empty
      rcases h_empty with ⟨x, hxL, hxJ⟩
      have hxI : x ∈ I := hIJ x hxJ
      have hc_nonneg : 0 ≤ c := by
        have hgx_nonneg : 0 ≤ g x := hg_nonneg x hxI
        have hgx_eq_c : g x = c := hc ⟨x, hxL⟩
        linarith
      have h_const_val_J : constant_value_on g (L ∩ J : BoundedInterval) = c :=
        ConstantOn.const_eq (by
          simpa [BoundedInterval.inter_eq] using h_nonempty_inter)
          (λ y hy => by
            have hy' : y ∈ ((L : Set ℝ) ∩ (J : Set ℝ)) := by
              simpa [BoundedInterval.inter_eq] using hy
            exact hc ⟨y, hy'.1⟩)
      rw [h_const_val_J]
      have h_len_nonneg : 0 ≤ |L ∩ J|ₗ := BoundedInterval.length_nonneg _
      nlinarith
    · rw [Set.not_nonempty_iff_eq_empty] at h_empty
      have h_len0 : |L ∩ J|ₗ = 0 :=
        BoundedInterval.length_of_empty (by simpa [BoundedInterval.inter_eq] using h_empty)
      simp [h_len0]
  have h_image_le : ∑ K ∈ Finset.image (fun (L : BoundedInterval) => L ∩ J) P.intervals,
      (constant_value_on g K) * |K|ₗ
      ≤ ∑ L ∈ P.intervals, (constant_value_on g (L ∩ J : BoundedInterval)) * |(L ∩ J : BoundedInterval)|ₗ :=
    Finset.sum_image_le_of_nonneg h_nonneg_f
  have h_term_eq : ∀ L ∈ P.intervals,
      (constant_value_on g (L ∩ J : BoundedInterval)) * |(L ∩ J : BoundedInterval)|ₗ
      = (constant_value_on g L) * |L ∩ J|ₗ := by
    intro L hL
    rcases hP L hL with ⟨c, hc⟩
    by_cases h_empty : ((L : Set ℝ) ∩ (J : Set ℝ)).Nonempty
    · have h_nonempty_inter : ((L : Set ℝ) ∩ (J : Set ℝ)).Nonempty := h_empty
      rcases h_empty with ⟨x, hxL, hxJ⟩
      have h_const_val : constant_value_on g (L : Set ℝ) = c :=
        ConstantOn.const_eq ⟨x, hxL⟩ (λ y hy => hc ⟨y, hy⟩)
      have h_const_val_J : constant_value_on g (L ∩ J : BoundedInterval) = c :=
        ConstantOn.const_eq (by
          simpa [BoundedInterval.inter_eq] using h_nonempty_inter)
          (λ y hy => by
            have hy' : y ∈ ((L : Set ℝ) ∩ (J : Set ℝ)) := by
              simpa [BoundedInterval.inter_eq] using hy
            exact hc ⟨y, hy'.1⟩)
      rw [h_const_val, h_const_val_J]
    · rw [Set.not_nonempty_iff_eq_empty] at h_empty
      have h_len0 : |L ∩ J|ₗ = 0 :=
        BoundedInterval.length_of_empty (by simpa [BoundedInterval.inter_eq] using h_empty)
      simp [h_len0]
  have h_term_ineq : ∀ L ∈ P.intervals,
      (constant_value_on g L) * |L ∩ J|ₗ ≤ (constant_value_on g L) * |L|ₗ := by
    intro L hL
    rcases hP L hL with ⟨c, hc⟩
    have h_len_ineq : |L ∩ J|ₗ ≤ |L|ₗ := length_inter_le_length L J
    by_cases hL_nonempty : (L : Set ℝ).Nonempty
    · have h_nonneg_cval : 0 ≤ constant_value_on g (L : Set ℝ) := by
        rcases hL_nonempty with ⟨x, hxL⟩
        have hL_sub_I : (L : Set ℝ) ⊆ (I : Set ℝ) := P.contains L hL
        have hxI : x ∈ I := hL_sub_I hxL
        have hgx_nonneg : 0 ≤ g x := hg_nonneg x hxI
        have hgx_eq_c : g x = c := hc ⟨x, hxL⟩
        have h_cval : constant_value_on g (L : Set ℝ) = c :=
          ConstantOn.const_eq ⟨x, hxL⟩ (λ y hy => hc ⟨y, hy⟩)
        rw [h_cval]
        linarith
      apply mul_le_mul_of_nonneg_left h_len_ineq
      exact h_nonneg_cval
    · have hL_empty : (L : Set ℝ) = ∅ := Set.not_nonempty_iff_eq_empty.mp hL_nonempty
      have h_len_L : |L|ₗ = 0 := BoundedInterval.length_of_empty hL_empty
      have h_len_inter : |L ∩ J|ₗ = 0 := by
        apply BoundedInterval.length_of_empty
        calc
          ((L ∩ J : BoundedInterval) : Set ℝ) = ((L : Set ℝ) ∩ (J : Set ℝ)) := by
            simp [BoundedInterval.inter_eq]
          _ = ∅ ∩ (J : Set ℝ) := by rw [hL_empty]
          _ = ∅ := Set.empty_inter _
      rw [h_len_L, h_len_inter]
  calc
    ∑ K ∈ Finset.image (fun (L : BoundedInterval) => L ∩ J) P.intervals, (constant_value_on g K) * |K|ₗ
    ≤ ∑ L ∈ P.intervals, (constant_value_on g (L ∩ J : BoundedInterval)) * |(L ∩ J : BoundedInterval)|ₗ := h_image_le
    _ = ∑ L ∈ P.intervals, (constant_value_on g L) * |L ∩ J|ₗ := by
      refine Finset.sum_congr rfl (λ L hL => ?_)
      rw [h_term_eq L hL]
    _ ≤ ∑ L ∈ P.intervals, (constant_value_on g L) * |L|ₗ :=
      Finset.sum_le_sum (λ L hL => h_term_ineq L hL)

/-- A variant of Theorem 11.4.1(h) that will be useful in later sections. -/
theorem IntegrableOn.mono' {I J: BoundedInterval} (hIJ: J ⊆ I)
  {f: ℝ → ℝ} (h: IntegrableOn f I) : IntegrableOn f J := by
  unfold IntegrableOn
  have hbdd_J : BddOn f J := by
    rcases h.1 with ⟨M, hM⟩
    exact ⟨M, λ x hx => hM x (hIJ x hx)⟩
  have h_diff_nonneg : 0 ≤ upper_integral f J - lower_integral f J := by
    linarith [lower_integral_le_upper hbdd_J]
  have h_nonpos : upper_integral f J - lower_integral f J ≤ 0 := by
    refine nonneg_of_le_const_mul_eps (x := upper_integral f J - lower_integral f J) (C := 2) ?_
    intro ε hε
    have h_up_I : upper_integral f I < integ f I + ε := by
      have : integ f I = upper_integral f I := rfl
      rw [this]; nlinarith
    rcases lt_of_gt_upper_integral h.1 h_up_I with ⟨u, hu_maj, hu_pc, hu_int⟩
    have h_lo_I : integ f I - ε < lower_integral f I := by
      rw [h.2, show integ f I = upper_integral f I from rfl]
      nlinarith
    rcases gt_of_lt_lower_integral h.1 h_lo_I with ⟨l, hl_min, hl_pc, hl_int⟩
    have hu_pc_J : PiecewiseConstantOn u J := pc_of_subset hIJ hu_pc
    have hl_pc_J : PiecewiseConstantOn l J := pc_of_subset hIJ hl_pc
    have hu_maj_J : MajorizesOn u f J := λ x hx => hu_maj x (hIJ x hx)
    have hl_min_J : MinorizesOn l f J := λ x hx => hl_min x (hIJ x hx)
    have h_up_J : upper_integral f J ≤ integ u J := by
      calc
        upper_integral f J ≤ hu_pc_J.integ' := upper_integral_le_integ hbdd_J hu_maj_J hu_pc_J
        _ = PiecewiseConstantOn.integ u J := rfl
        _ = integ u J := (integ_of_piecewise_const hu_pc_J).2.symm
    have h_lo_J : integ l J ≤ lower_integral f J := by
      calc
        integ l J = PiecewiseConstantOn.integ l J := (integ_of_piecewise_const hl_pc_J).2
        _ = hl_pc_J.integ' := rfl
        _ ≤ lower_integral f J := integ_le_lower_integral hbdd_J hl_min_J hl_pc_J
    have h_integ_diff_J : integ u J - integ l J = integ (u - l) J := by
      have h_int_u_J : IntegrableOn u J := (integ_of_piecewise_const hu_pc_J).1
      have h_int_l_J : IntegrableOn l J := (integ_of_piecewise_const hl_pc_J).1
      have h_sub := h_int_u_J.sub h_int_l_J
      exact h_sub.2.symm
    have h_integ_diff_I : integ u I - integ l I = integ (u - l) I := by
      have h_int_u_I : IntegrableOn u I := (integ_of_piecewise_const hu_pc).1
      have h_int_l_I : IntegrableOn l I := (integ_of_piecewise_const hl_pc).1
      have h_sub := h_int_u_I.sub h_int_l_I
      exact h_sub.2.symm
    have h_g_nonneg_I : ∀ x ∈ I, 0 ≤ (u - l) x := by
      intro x hx
      dsimp [Pi.sub_apply]
      have hux : f x ≤ u x := hu_maj x hx
      have hlx : l x ≤ f x := hl_min x hx
      linarith
    have h_g_pc_I : PiecewiseConstantOn (u - l) I := hu_pc.sub hl_pc
    have h_integ_g_J_le_I : integ (u - l) J ≤ integ (u - l) I :=
      integ_nonneg_subset hIJ h_g_pc_I h_g_nonneg_I
    have h_integ_u_I_lt : integ u I < integ f I + ε := by
      calc
        integ u I = hu_pc.integ' := (integ_of_piecewise_const hu_pc).2
        _ < integ f I + ε := hu_int
    have h_integ_l_I_gt : integ f I - ε < integ l I := by
      calc
        integ f I - ε < hl_pc.integ' := hl_int
        _ = integ l I := (integ_of_piecewise_const hl_pc).2.symm
    calc
      upper_integral f J - lower_integral f J ≤ integ u J - integ l J := by nlinarith
      _ = integ (u - l) J := h_integ_diff_J
      _ ≤ integ (u - l) I := h_integ_g_J_le_I
      _ = integ u I - integ l I := h_integ_diff_I.symm
      _ ≤ (integ f I + ε) - (integ f I - ε) := by nlinarith
      _ = 2 * ε := by ring
  have h_eq : lower_integral f J = upper_integral f J := by nlinarith
  exact ⟨hbdd_J, h_eq⟩

/-- A further variant of Theorem 11.4.1(h) that will be useful in later sections. -/
theorem IntegrableOn.eq {I J: BoundedInterval} (hIJ: J ⊆ I)
  (ha: J.a = I.a) (hb: J.b = I.b)
  {f: ℝ → ℝ} (h: IntegrableOn f I) : integ f J = integ f I := by
  have hlen_eq : |I|ₗ = |J|ₗ := by
    rw [BoundedInterval.length, BoundedInterval.length, ha, hb]
  by_cases hlen0 : |I|ₗ = 0
  · rcases integ_on_subsingleton hlen0 with ⟨_, hI⟩
    have hlenJ : |J|ₗ = 0 := by rw [← hlen_eq, hlen0]
    rcases integ_on_subsingleton hlenJ with ⟨_, hJ⟩
    rw [hI, hJ]
  · have ha_lt_b : I.a < I.b := by
      have h_nonneg : 0 ≤ |I|ₗ := BoundedInterval.length_nonneg _
      have hpos : 0 < |I|ₗ := h_nonneg.lt_of_ne (Ne.symm hlen0)
      rw [BoundedInterval.length] at hpos
      rcases lt_max_iff.mp hpos with (h | h)
      · linarith
      · linarith
    revert h
    have ha_lt_b' : I.a < I.b := ha_lt_b
    clear ha_lt_b
    cases I with
    | Icc a b =>
      intro h
      have ha_lt_b : a < b := by simpa using ha_lt_b'
      cases J with
      | Icc a' b' => simp [ha, hb]
      | Ico a' b' =>
        have h_join : (BoundedInterval.Icc a b).joins (BoundedInterval.Ico a b) (BoundedInterval.Icc b b) :=
          BoundedInterval.join_Ico_Icc ha_lt_b.le (le_refl b)
        have h_join_result := IntegrableOn.join h_join h
        rcases h_join_result with ⟨hJ', hK, h_eq⟩
        have h_len_K : |(BoundedInterval.Icc b b : BoundedInterval)|ₗ = 0 := by simp
        rcases integ_on_subsingleton h_len_K with ⟨_, h_integ_K⟩
        have h_final : integ f (BoundedInterval.Ico a b) = integ f (BoundedInterval.Icc a b) := by nlinarith
        simpa [ha, hb] using h_final
      | Ioc a' b' =>
        have h_join : (BoundedInterval.Icc a b).joins (BoundedInterval.Icc a a) (BoundedInterval.Ioc a b) :=
          BoundedInterval.join_Icc_Ioc (le_refl a) ha_lt_b.le
        have h_join_result := IntegrableOn.join h_join h
        rcases h_join_result with ⟨hK, hJ', h_eq⟩
        have h_len_K : |(BoundedInterval.Icc a a : BoundedInterval)|ₗ = 0 := by simp
        rcases integ_on_subsingleton h_len_K with ⟨_, h_integ_K⟩
        have h_final : integ f (BoundedInterval.Ioc a b) = integ f (BoundedInterval.Icc a b) := by nlinarith
        simpa [ha, hb] using h_final
      | Ioo a' b' =>
        have h_join1 : (BoundedInterval.Icc a b).joins (BoundedInterval.Icc a a) (BoundedInterval.Ioc a b) :=
          BoundedInterval.join_Icc_Ioc (le_refl a) ha_lt_b.le
        have h1 := IntegrableOn.join h_join1 h
        rcases h1 with ⟨h_a, h_oc, h_eq1⟩
        have h_len_a : |(BoundedInterval.Icc a a : BoundedInterval)|ₗ = 0 := by simp
        rcases integ_on_subsingleton h_len_a with ⟨_, h_integ_a⟩
        have h_join2 : (BoundedInterval.Ioc a b).joins (BoundedInterval.Ioo a b) (BoundedInterval.Icc b b) :=
          BoundedInterval.join_Ioo_Icc ha_lt_b (le_refl b)
        have h2 := IntegrableOn.join h_join2 h_oc
        rcases h2 with ⟨h_oo, h_b, h_eq2⟩
        have h_len_b : |(BoundedInterval.Icc b b : BoundedInterval)|ₗ = 0 := by simp
        rcases integ_on_subsingleton h_len_b with ⟨_, h_integ_b⟩
        have h_final : integ f (BoundedInterval.Ioo a b) = integ f (BoundedInterval.Icc a b) := by nlinarith
        simpa [ha, hb] using h_final
    | Ioc a b =>
      intro h
      have ha_lt_b : a < b := by simpa using ha_lt_b'
      cases J with
      | Ioc a' b' => simp [ha, hb]
      | Ioo a' b' =>
        have h_join : (BoundedInterval.Ioc a b).joins (BoundedInterval.Ioo a b) (BoundedInterval.Icc b b) :=
          BoundedInterval.join_Ioo_Icc ha_lt_b (le_refl b)
        have h_join_result := IntegrableOn.join h_join h
        rcases h_join_result with ⟨hJ', hK, h_eq⟩
        have h_len_K : |(BoundedInterval.Icc b b : BoundedInterval)|ₗ = 0 := by simp
        rcases integ_on_subsingleton h_len_K with ⟨_, h_integ_K⟩
        have h_final : integ f (BoundedInterval.Ioo a b) = integ f (BoundedInterval.Ioc a b) := by nlinarith
        simpa [ha, hb] using h_final
      | Icc a' b' =>
        have ha_eq : a' = a := by simpa using ha
        have hb_eq : b' = b := by simpa using hb
        have hxJ : a ∈ (BoundedInterval.Icc a' b' : Set ℝ) := by
          have ha'_lt_b' : a' < b' := by
            rw [ha_eq, hb_eq]; exact ha_lt_b
          have hmem : a' ∈ (BoundedInterval.Icc a' b' : Set ℝ) := by simp [ha'_lt_b'.le]
          simpa [ha_eq] using hmem
        have hxI : a ∉ (BoundedInterval.Ioc a b : Set ℝ) := by simp
        exfalso; exact hxI (hIJ a hxJ)
      | Ico a' b' =>
        have ha_eq : a' = a := by simpa using ha
        have hb_eq : b' = b := by simpa using hb
        have hxJ : a ∈ (BoundedInterval.Ico a' b' : Set ℝ) := by
          have ha'_lt_b' : a' < b' := by
            rw [ha_eq, hb_eq]; exact ha_lt_b
          have hmem : a' ∈ (BoundedInterval.Ico a' b' : Set ℝ) := by simp [ha'_lt_b']
          simpa [ha_eq] using hmem
        have hxI : a ∉ (BoundedInterval.Ioc a b : Set ℝ) := by simp
        exfalso; exact hxI (hIJ a hxJ)
    | Ico a b =>
      intro h
      have ha_lt_b : a < b := by simpa using ha_lt_b'
      have ha_le_b : a ≤ b := ha_lt_b.le
      cases J with
      | Ico a' b' => simp [ha, hb]
      | Ioo a' b' =>
        have h_join : (BoundedInterval.Ico a b).joins (BoundedInterval.Ioo a b) (BoundedInterval.Icc a a) := by
          refine ⟨?_, ?_, ?_⟩
          · ext x; simp
          · ext x; constructor
            · intro ⟨hax, hxb⟩
              rcases lt_or_eq_of_le hax with (hx | hx)
              · exact Or.inl ⟨hx, hxb⟩
              · exact Or.inr (by
                  subst hx; simp)
            · rintro (⟨hax, hxb⟩ | ⟨hax, hxa⟩)
              · exact ⟨hax.le, hxb⟩
              · have hx_eq_a : x = a := le_antisymm hxa hax
                rw [hx_eq_a]; exact ⟨le_refl a, ha_lt_b⟩
          · simp
        have h_join_result := IntegrableOn.join h_join h
        rcases h_join_result with ⟨hJ', hK, h_eq⟩
        have h_len_K : |(BoundedInterval.Icc a a : BoundedInterval)|ₗ = 0 := by simp
        rcases integ_on_subsingleton h_len_K with ⟨_, h_integ_K⟩
        have h_final : integ f (BoundedInterval.Ioo a b) = integ f (BoundedInterval.Ico a b) := by nlinarith
        simpa [ha, hb] using h_final
      | Icc a' b' =>
        have ha_eq : a' = a := by simpa using ha
        have hb_eq : b' = b := by simpa using hb
        have hxJ : b ∈ (BoundedInterval.Icc a' b' : Set ℝ) := by
          have ha'_le_b' : a' ≤ b' := by
            rw [ha_eq, hb_eq]; exact ha_le_b
          have hmem : b' ∈ (BoundedInterval.Icc a' b' : Set ℝ) := by simp [ha'_le_b']
          simpa [hb_eq] using hmem
        have hxI : b ∉ (BoundedInterval.Ico a b : Set ℝ) := by simp
        exfalso; exact hxI (hIJ b hxJ)
      | Ioc a' b' =>
        have ha_eq : a' = a := by simpa using ha
        have hb_eq : b' = b := by simpa using hb
        have hxJ : b ∈ (BoundedInterval.Ioc a' b' : Set ℝ) := by
          have ha'_lt_b' : a' < b' := by
            rw [ha_eq, hb_eq]; exact ha_lt_b
          have hmem : b' ∈ (BoundedInterval.Ioc a' b' : Set ℝ) := by simp [ha'_lt_b']
          simpa [hb_eq] using hmem
        have hxI : b ∉ (BoundedInterval.Ico a b : Set ℝ) := by simp
        exfalso; exact hxI (hIJ b hxJ)
    | Ioo a b =>
      intro h
      have ha_lt_b : a < b := by simpa using ha_lt_b'
      cases J with
      | Ioo a' b' => simp [ha, hb]
      | Icc a' b' =>
        have ha_eq : a' = a := by simpa using ha
        have hb_eq : b' = b := by simpa using hb
        have hxJ : a ∈ (BoundedInterval.Icc a' b' : Set ℝ) := by
          have ha'_lt_b' : a' < b' := by
            rw [ha_eq, hb_eq]; exact ha_lt_b
          have hmem : a' ∈ (BoundedInterval.Icc a' b' : Set ℝ) := by simp [ha'_lt_b'.le]
          simpa [ha_eq] using hmem
        have hxI : a ∉ (BoundedInterval.Ioo a b : Set ℝ) := by simp
        exfalso; exact hxI (hIJ a hxJ)
      | Ico a' b' =>
        have ha_eq : a' = a := by simpa using ha
        have hb_eq : b' = b := by simpa using hb
        have hxJ : a ∈ (BoundedInterval.Ico a' b' : Set ℝ) := by
          have ha'_lt_b' : a' < b' := by
            rw [ha_eq, hb_eq]; exact ha_lt_b
          have hmem : a' ∈ (BoundedInterval.Ico a' b' : Set ℝ) := by simp [ha'_lt_b']
          simpa [ha_eq] using hmem
        have hxI : a ∉ (BoundedInterval.Ioo a b : Set ℝ) := by simp
        exfalso; exact hxI (hIJ a hxJ)
      | Ioc a' b' =>
        have ha_eq : a' = a := by simpa using ha
        have hb_eq : b' = b := by simpa using hb
        have hxJ : b ∈ (BoundedInterval.Ioc a' b' : Set ℝ) := by
          have ha'_lt_b' : a' < b' := by
            rw [ha_eq, hb_eq]; exact ha_lt_b
          have hmem : b' ∈ (BoundedInterval.Ioc a' b' : Set ℝ) := by simp [ha'_lt_b']
          simpa [hb_eq] using hmem
        have hxI : b ∉ (BoundedInterval.Ioo a b : Set ℝ) := by simp
        exfalso; exact hxI (hIJ b hxJ)

/-- Theorem 11.4.3 (Max and min preserve integrability)-/

theorem IntegrableOn.max {I: BoundedInterval} {f g:ℝ → ℝ} (hf: IntegrableOn f I) (hg: IntegrableOn g I) :
  IntegrableOn (f ⊔ g) I  := by
  -- This proof is written to follow the structure of the original text.
  unfold IntegrableOn at hf hg
  have hmax_bound : BddOn (f ⊔ g) I := by
    choose M hM using hf.1; choose M' hM' using hg.1
    use M ⊔ M'; peel hM with x hx hM; specialize hM' _ hx
    simp only [Pi.sup_apply]
    exact abs_max_le_max_abs_abs.trans (sup_le_sup hM hM')
  have lower_le_upper : 0 ≤ upper_integral (f ⊔ g) I - lower_integral (f ⊔ g) I := by linarith [lower_integral_le_upper hmax_bound]
  have (ε:ℝ) (hε: 0 < ε) : upper_integral (f ⊔ g) I - lower_integral (f ⊔ g) I ≤ 4*ε := by
    choose f' hf'min hf'const hf'int using gt_of_lt_lower_integral hf.1 (show integ f I - ε < lower_integral f I
    by grind)
    choose g' hg'min hg'const hg'int using gt_of_lt_lower_integral hg.1 (show integ g I - ε < lower_integral g I by grind)
    choose f'' hf''max hf''const hf''int using lt_of_gt_upper_integral hf.1 (show upper_integral f I < integ f I + ε by grind)
    choose g'' hg''max hg''const hg''int using lt_of_gt_upper_integral hg.1 (show upper_integral g I < integ g I + ε by grind)
    set h := (f'' - f') + (g'' - g')
    have hf'_integ := integ_of_piecewise_const hf'const
    have hg'_integ := integ_of_piecewise_const hg'const
    have hf''_integ := integ_of_piecewise_const hf''const
    have hg''_integ := integ_of_piecewise_const hg''const
    have hf''f'_integ := hf''_integ.1.sub hf'_integ.1
    have hg''g'_integ := hg''_integ.1.sub hg'_integ.1
    have hh_IntegrableOn.eq := hf''f'_integ.1.add hg''g'_integ.1
    have hinteg_le : integ h I ≤ 4 * ε := by linarith
    have hf''g''_const := hf''const.max hg''const
    have hf''g''_maj : MajorizesOn (f'' ⊔ g'') (f ⊔ g) I := by
      intro x hx
      simpa [Pi.sup_apply] using sup_le_sup (hf''max x hx) (hg''max x hx)
    have hf'g'_const := hf'const.max hg'const
    have hf'g'_maj : MinorizesOn (f' ⊔ g') (f ⊔ g) I := by
      intro x hx
      simpa [Pi.sup_apply] using sup_le_sup (hf'min x hx) (hg'min x hx)
    have hff'g''_ge := upper_integral_le_integ hmax_bound hf''g''_maj hf''g''_const
    have hf'g'_le := integ_le_lower_integral hmax_bound hf'g'_maj hf'g'_const
    have : MinorizesOn (f'' ⊔ g'') (f' ⊔ g' + h) I := by
      peel hf'min with x hx hf'min; specialize hg'min _ hx; specialize hf''max _ hx; specialize hg''max _ hx
      simp [h]; split_ands <;> linarith [le_max_left (f' x) (g' x), le_max_right (f' x) (g' x)]
    have hf'g'_integ := integ_of_piecewise_const hf'g'_const
    have hf''g''_integ := integ_of_piecewise_const hf''g''_const
    have hf'g'h_integ := hf'g'_integ.1.add hh_IntegrableOn.eq.1
    rw [MinorizesOn.iff] at this
    linarith [hf''g''_integ.1.mono hf'g'h_integ.1 this]
  exact ⟨ hmax_bound, by linarith [nonneg_of_le_const_mul_eps this] ⟩



/-- Theorem 11.4.5 / Exercise 11.4.3.  The objective here is to create a shorter proof than the one above. -/
theorem IntegrableOn.min {I: BoundedInterval} {f g:ℝ → ℝ} (hf: IntegrableOn f I) (hg: IntegrableOn g I) :
  IntegrableOn (f ⊓ g) I  := by
  have hneg_max : IntegrableOn ((-f) ⊔ (-g)) I := (hf.neg).1.max (hg.neg).1
  have hmin : IntegrableOn (-((-f) ⊔ (-g))) I := (hneg_max.neg).1
  convert hmin using 1
  ext x
  by_cases h : f x ≤ g x
  · have h' : -g x ≤ -f x := by linarith
    simp [h, h', Pi.inf_apply, Pi.sup_apply, Pi.neg_apply]
  · have h' : g x ≤ f x := by linarith
    have h'' : -f x ≤ -g x := by linarith
    simp [h', h'', Pi.inf_apply, Pi.sup_apply, Pi.neg_apply]

/-- Corollary 11.4.4 -/
theorem IntegrableOn.abs {I: BoundedInterval} {f:ℝ → ℝ} (hf: IntegrableOn f I) :
  IntegrableOn (abs f) I := by
  have := (IntegrableOn.const 0 I).1
  convert ((hf.max this).sub (hf.min this)).1 using 1
  ext x; obtain h | h := (show f x ≤ 0 ∨ f x ≥ 0 by grind) <;> simp [h]

/-- Theorem 11.4.5 (Products preserve Riemann integrability).
It is convenient to first establish the non-negative case. -/
theorem integ_of_mul_nonneg {I: BoundedInterval} {f g:ℝ → ℝ} (hf: IntegrableOn f I) (hg: IntegrableOn g I)
  (hf_nonneg: MajorizesOn f 0 I) (hg_nonneg: MajorizesOn g 0 I) :
  IntegrableOn (f * g) I := by
  -- This proof is written to follow the structure of the original text.
  by_cases hI : (I:Set ℝ).Nonempty
  swap
  . apply (integ_on_subsingleton _).1
    rw [←BoundedInterval.length_of_subsingleton]
    simp_all [Set.not_nonempty_iff_eq_empty]
  unfold IntegrableOn at hf hg
  choose M₁ hM₁ using hf.1
  choose M₂ hM₂ using hg.1
  have hM₁pos : 0 ≤ M₁ := (abs_nonneg _).trans (hM₁ hI.some hI.some_mem)
  have hM₂pos : 0 ≤ M₂ := (abs_nonneg _).trans (hM₂ hI.some hI.some_mem)
  have hmul_bound : BddOn (f * g) I := by
    use M₁ * M₂; peel hM₁ with x hx hM₁; specialize hM₂ _ hx
    simp [abs_mul]; apply mul_le_mul hM₁ hM₂ <;> positivity
  have lower_le_upper : 0 ≤ upper_integral (f * g) I - lower_integral (f * g) I := by
    linarith [lower_integral_le_upper hmul_bound]
  have (ε:ℝ) (hε: 0 < ε) : upper_integral (f * g) I - lower_integral (f * g) I ≤ 2*(M₁+M₂)*ε := by
    have : ∃ f', MinorizesOn f' f I ∧ PiecewiseConstantOn f' I ∧ integ f I - ε < PiecewiseConstantOn.integ f' I ∧ MajorizesOn f' 0 I := by
      choose f' hf'min hf'const hf'int using gt_of_lt_lower_integral hf.1 (show integ f I - ε < lower_integral f I by linarith)
      use max f' 0
      have hzero := (ConstantOn.of_const' 0 I).piecewiseConstantOn
      split_ands
      . peel hf_nonneg with x hx _; specialize hf'min _ hx; aesop
      . exact hf'const.max hzero
      . apply lt_of_lt_of_le hf'int (hf'const.integ_mono _ (hf'const.max hzero)); simp
      intro _; simp
    choose f' hf'min hf'const hf'int hf'_nonneg using this
    have : ∃ g', MinorizesOn g' g I ∧ PiecewiseConstantOn g' I ∧ integ g I - ε < PiecewiseConstantOn.integ g' I ∧ MajorizesOn g' 0 I := by
      obtain ⟨ g', hg'min, hg'const, hg'int ⟩ := gt_of_lt_lower_integral hg.1 (show integ g I - ε < lower_integral g I by linarith)
      use max g' 0
      have hzero := (ConstantOn.of_const' 0 I).piecewiseConstantOn
      split_ands
      . peel hg_nonneg with x hx _; specialize hg'min _ hx; aesop
      . exact hg'const.max hzero
      . apply lt_of_lt_of_le hg'int (hg'const.integ_mono _ (hg'const.max hzero)); simp
      intro _; simp
    choose g' hg'min hg'const hg'int hg'_nonneg using this
    have : ∃ f'', MajorizesOn f'' f I ∧ PiecewiseConstantOn f'' I ∧ PiecewiseConstantOn.integ f'' I < integ f I + ε ∧ MinorizesOn f'' (fun _ ↦ M₁) I := by
      obtain ⟨ f'', hf''maj, hf''const, hf''int ⟩ := lt_of_gt_upper_integral hf.1 (show upper_integral f I < integ f I + ε  by linarith)
      use min f'' (fun _ ↦ M₁)
      have hM₁_piece := (ConstantOn.of_const' M₁ I).piecewiseConstantOn
      split_ands
      . peel hM₁ with x hx hM₁; rw [abs_le'] at hM₁
        simp [hf''maj _ hx, hM₁.1]
      . exact hf''const.min hM₁_piece
      . apply lt_of_le_of_lt ((hf''const.min hM₁_piece).integ_mono _ hf''const) hf''int
        simp
      intro _; simp
    choose f'' hf''maj hf''const hf''int hf''bound using this
    have : ∃ g'', MajorizesOn g'' g I ∧ PiecewiseConstantOn g'' I ∧ PiecewiseConstantOn.integ g'' I < integ g I + ε ∧ MinorizesOn g'' (fun _ ↦ M₂) I := by
      obtain ⟨ g'', hg''maj, hg''const, hg''int ⟩ := lt_of_gt_upper_integral hg.1 (show upper_integral g I < integ g I + ε by linarith)
      use min g'' (fun _ ↦ M₂)
      have hM₂_piece := (ConstantOn.of_const' M₂ I).piecewiseConstantOn
      split_ands
      . peel hM₂ with x hx hM₂; rw [abs_le'] at hM₂
        simp [hg''maj _ hx, hM₂.1]
      . exact hg''const.min hM₂_piece
      . apply lt_of_le_of_lt ((hg''const.min hM₂_piece).integ_mono _ hg''const) hg''int
        simp
      intro _ _; simp
    choose g'' hg''maj hg''const hg''int hg''bound using this
    have hf'g'_const := hf'const.mul hg'const
    have hf'g'_maj : MinorizesOn (f' * g') (f * g) I := by
      peel hf'min with x hx hf'min; specialize hg'min _ hx;
      specialize hf'_nonneg _ hx; specialize hg'_nonneg _ hx
      simp at *; apply mul_le_mul hf'min hg'min <;> grind
    have hf''g''_const := hf''const.mul hg''const
    have hf''g''_maj : MajorizesOn (f'' * g'') (f * g) I := by
      peel hf''maj with x hx hf''maj; specialize hg''maj _ hx
      specialize hg_nonneg _ hx; specialize hf_nonneg _ hx
      simp at *; apply mul_le_mul hf''maj hg''maj <;> grind
    have hupper_le := upper_integral_le_integ hmul_bound hf''g''_maj hf''g''_const
    have hlower_ge := integ_le_lower_integral hmul_bound hf'g'_maj hf'g'_const
    have hh_const := hf''g''_const.sub hf'g'_const
    have hh_integ := hf''g''_const.integ_sub hf'g'_const
    have hhmin : MinorizesOn (f'' * g'' - f' * g') (M₁ • (g''-g') + M₂ • (f''-f')) I := by
      intro x hx
      simp only [Pi.sub_apply, Pi.mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      calc
        _ = (f'' x) * (g'' x - g' x) + (g' x) * (f'' x - f' x) := by ring
        _ ≤ _ := by gcongr <;> grind
    have hg''g'_const := hg''const.sub hg'const
    have hg''g'_integ := hg''const.integ_sub hg'const
    have hM₁g''g'_const := hg''g'_const.smul M₁
    have hM₁g''g_integ := hg''g'_const.integ_smul M₁
    have hf''f'_const := hf''const.sub hf'const
    have hf''f_integ := hf''const.integ_sub hf'const
    have hM₂f''f'_const := hf''f'_const.smul M₂
    have hM₂f''f_integ := hf''f'_const.integ_smul M₂
    have hsum_const := hM₁g''g'_const.add hM₂f''f'_const
    have hsum_integ := hM₁g''g'_const.integ_add hM₂f''f'_const
    have hsum_bound := hh_const.integ_mono hhmin hsum_const
    calc
      _ ≤ M₁ * PiecewiseConstantOn.integ (g'' - g') I + M₂ * PiecewiseConstantOn.integ (f'' - f') I := by linarith
      _ ≤ M₁ * (2*ε) + M₂ * (2*ε) := by gcongr <;> linarith
      _ = _ := by ring
  exact ⟨ hmul_bound, by linarith [nonneg_of_le_const_mul_eps this] ⟩


theorem integ_of_mul {I: BoundedInterval} {f g:ℝ → ℝ} (hf: IntegrableOn f I) (hg: IntegrableOn g I) :
  IntegrableOn (f * g) I := by
  -- This proof is written to follow the structure of the original text.
  set fplus := max f (fun _ ↦ 0)
  set fminus := -min f (fun _ ↦ 0)
  set gplus := max g (fun _ ↦ 0)
  set gminus := -min g (fun _ ↦ 0)
  have := (IntegrableOn.const 0 I).1
  observe hfplus_integ : IntegrableOn fplus I
  observe hgplus_integ : IntegrableOn gplus I
  have hfminus_integ : IntegrableOn fminus I := (hf.min this).neg.1
  have hgminus_integ : IntegrableOn gminus I := (hg.min this).neg.1
  have hfplus_nonneg : MajorizesOn fplus 0 I := by intro _; simp [fplus]
  have hfminus_nonneg : MajorizesOn fminus 0 I := by intro _; simp [fminus]
  have hgplus_nonneg : MajorizesOn gplus 0 I := by intro _; simp [gplus]
  have hgminus_nonneg : MajorizesOn gminus 0 I := by intro _; simp [gminus]
  have hfplusgplus := integ_of_mul_nonneg hfplus_integ hgplus_integ hfplus_nonneg hgplus_nonneg
  have hfplusgminus := integ_of_mul_nonneg hfplus_integ hgminus_integ hfplus_nonneg hgminus_nonneg
  have hfminusgplus := integ_of_mul_nonneg hfminus_integ hgplus_integ hfminus_nonneg hgplus_nonneg
  have hfminusgminus := integ_of_mul_nonneg hfminus_integ hgminus_integ hfminus_nonneg hgminus_nonneg
  rw [show f = fplus - fminus by ext; simp [fplus, fminus],
      show g = gplus - gminus by ext; simp [gplus, gminus]]
  ring_nf
  exact ((hfplusgplus.add (hfplusgminus.neg.1.sub hfminusgplus).1).1.add hfminusgminus).1
open BoundedInterval

/-- If J ⊆ I, then |J|ₗ ≤ |I|ₗ -/
lemma length_mono {I J : BoundedInterval} (h : J ⊆ I) : |J|ₗ ≤ |I|ₗ := by
  by_cases hJ_nonempty : (J : Set ℝ).Nonempty
  · rcases hJ_nonempty with ⟨x, hx⟩
    have hx_Icc : x ∈ (BoundedInterval.Icc J.a J.b : Set ℝ) := BoundedInterval.subset_Icc J x hx
    have hJ_a_le_x : J.a ≤ x := hx_Icc.1
    have hx_le_J_b : x ≤ J.b := hx_Icc.2
    have hx_I : x ∈ I := h x hx
    have hx_I_Icc : x ∈ (BoundedInterval.Icc I.a I.b : Set ℝ) := BoundedInterval.subset_Icc I x hx_I
    have hI_a_le_x : I.a ≤ x := hx_I_Icc.1
    have hx_le_I_b : x ≤ I.b := hx_I_Icc.2
    -- We have I.a ≤ x ≤ I.b and J.a ≤ x ≤ J.b.
    -- We want to show J.b - J.a ≤ I.b - I.a.
    -- This follows from I.a ≤ J.a (by contradiction: if J.a < I.a then pick y between them)
    -- and J.b ≤ I.b (by contradiction: if I.b < J.b then pick y between them).
    have ha_ineq : I.a ≤ J.a := by
      by_contra! H
      have h_lt : J.a < I.a := H
      let y := (J.a + I.a) / 2
      have hy_J : y ∈ (J : Set ℝ) := by
        have ha_J : J.a < y := by dsimp [y]; nlinarith
        have hb_J : y < J.b := by
          dsimp [y]; nlinarith
        have hy_ioo : y ∈ (BoundedInterval.Ioo J.a J.b : Set ℝ) := by simp [ha_J, hb_J]
        exact BoundedInterval.Ioo_subset J y hy_ioo
      have hy_not_I : y ∉ (I : Set ℝ) := by
        intro hy_I
        have hy_I_Icc : y ∈ (BoundedInterval.Icc I.a I.b : Set ℝ) :=
          BoundedInterval.subset_Icc I y hy_I
        have hI_a_le_y : I.a ≤ y := hy_I_Icc.1
        dsimp [y] at hI_a_le_y
        nlinarith
      exact hy_not_I (h y hy_J)
    have hb_ineq : J.b ≤ I.b := by
      by_contra! H
      have h_lt : I.b < J.b := H
      let y := (I.b + J.b) / 2
      have hy_J : y ∈ (J : Set ℝ) := by
        have ha_J : J.a < y := by
          dsimp [y]; nlinarith
        have hb_J : y < J.b := by dsimp [y]; nlinarith
        have hy_ioo : y ∈ (BoundedInterval.Ioo J.a J.b : Set ℝ) := by simp [ha_J, hb_J]
        exact BoundedInterval.Ioo_subset J y hy_ioo
      have hy_not_I : y ∉ (I : Set ℝ) := by
        intro hy_I
        have hy_I_Icc : y ∈ (BoundedInterval.Icc I.a I.b : Set ℝ) :=
          BoundedInterval.subset_Icc I y hy_I
        have hy_le_I_b : y ≤ I.b := hy_I_Icc.2
        dsimp [y] at hy_le_I_b
        nlinarith
      exact hy_not_I (h y hy_J)
    rw [BoundedInterval.length, BoundedInterval.length]
    have hsub : J.b - J.a ≤ I.b - I.a := by nlinarith
    exact (max_le_max hsub (le_refl 0)).trans_eq (by simp)
  · have hJ_empty : (J : Set ℝ) = ∅ := Set.not_nonempty_iff_eq_empty.mp hJ_nonempty
    have hJ_len0 : |J|ₗ = 0 := BoundedInterval.length_of_empty hJ_empty
    rw [hJ_len0]
    exact BoundedInterval.length_nonneg I

/-- Helper: the right part of I after removing J (which must be the leftmost interval) -/
private def rest_of (I J : BoundedInterval) : BoundedInterval :=
  match I, J with
  | Icc _ c, Icc _ _ => Ioc J.b c
  | Icc _ c, Ico _ _ => Icc J.b c
  | Ico _ c, Icc _ _ => Ioo J.b c
  | Ico _ c, Ico _ _ => Ico J.b c
  | Ioc _ c, Ioc _ _ => Ioc J.b c
  | Ioc _ c, Ioo _ _ => Icc J.b c
  | Ioo _ c, Ioc _ _ => Ioo J.b c
  | Ioo _ c, Ioo _ _ => Ico J.b c
  | _, _ => Ioo 0 0

/- Decomposition of a non-degenerate partition: extract a rightmost interval K
   and a complementary interval L with `I.joins L K`, together with a partition
   P' of L whose intervals are `P.intervals.erase K`.  This is the combinatorial
   core of `Partition.sum_of_length`, factored out for reuse. -/
theorem partition_join_erase {I: BoundedInterval} (P: Partition I)
    (h : ¬ Subsingleton (I:Set ℝ)) :
    ∃ (K L : BoundedInterval), K ∈ P ∧ I.joins L K ∧
      ∃ P' : Partition L, P'.intervals = P.intervals.erase K := by
  simp [length_of_subsingleton, length, -Set.subsingleton_coe] at h
  have hex : ∃ K L : BoundedInterval, K ∈ P ∧ I.joins L K := by
    by_cases hI' : I.b ∈ I
    . choose K hK hbK using (P.exists_unique I.b hI').exists
      observe hKI : K ⊆ I
      by_cases hsub : Subsingleton (K:Set ℝ)
      . simp_all [mem_iff]
        apply hsub.eq_singleton_of_mem at hbK
        have : K = Icc (I.b) (I.b) := by
          have hK_set_eq : (K : Set ℝ) = {I.b} := hbK
          have hmem : I.b ∈ (K : Set ℝ) := by
            simp [hK_set_eq]
          cases K with
          | Ioo a b =>
            rcases Set.mem_Ioo.mp hmem with ⟨ha_lt_Ib, hIb_lt_b⟩
            have ha_lt_b : a < b := lt_trans ha_lt_Ib hIb_lt_b
            have hsub_set : (Ioo a b : Set ℝ).Subsingleton := by
              simpa using hsub
            have hx : (2*a + b)/3 ∈ (Ioo a b : Set ℝ) := by
              apply Set.mem_Ioo.mpr; constructor <;> nlinarith
            have hy : (a + 2*b)/3 ∈ (Ioo a b : Set ℝ) := by
              apply Set.mem_Ioo.mpr; constructor <;> nlinarith
            have h_val_eq : (2*a + b)/3 = (a + 2*b)/3 :=
              hsub_set hx hy
            have hneq : (2*a + b)/3 ≠ (a + 2*b)/3 := by nlinarith
            exfalso; exact hneq h_val_eq
          | Icc a b =>
            have ha_le_Ib : a ≤ I.b := (Set.mem_Icc.mp hmem).1
            have hIb_le_b : I.b ≤ b := (Set.mem_Icc.mp hmem).2
            have hsub_set : (Icc a b : Set ℝ).Subsingleton := by
              simpa using hsub
            have hb_le_a : b ≤ a := by
              have : (Set.Icc a b).Subsingleton := by simpa using hsub_set
              rw [Set.subsingleton_Icc_iff] at this
              exact this
            have ha_eq_Ib : a = I.b := by nlinarith
            have hb_eq_Ib : b = I.b := by nlinarith
            simp [ha_eq_Ib, hb_eq_Ib]
          | Ioc a b =>
            rcases Set.mem_Ioc.mp hmem with ⟨ha_lt_Ib, hIb_le_b⟩
            have ha_lt_b : a < b := lt_of_lt_of_le ha_lt_Ib hIb_le_b
            have hsub_set : (Ioc a b : Set ℝ).Subsingleton := by
              simpa using hsub
            have hx : (2*a + b)/3 ∈ (Ioc a b : Set ℝ) := by
              apply Set.mem_Ioc.mpr; constructor <;> nlinarith
            have hy : (a + 2*b)/3 ∈ (Ioc a b : Set ℝ) := by
              apply Set.mem_Ioc.mpr; constructor <;> nlinarith
            have h_val_eq : (2*a + b)/3 = (a + 2*b)/3 :=
              hsub_set hx hy
            have hneq : (2*a + b)/3 ≠ (a + 2*b)/3 := by nlinarith
            exfalso; exact hneq h_val_eq
          | Ico a b =>
            rcases Set.mem_Ico.mp hmem with ⟨ha_le_Ib, hIb_lt_b⟩
            have ha_lt_b : a < b := lt_of_le_of_lt ha_le_Ib hIb_lt_b
            have hsub_set : (Ico a b : Set ℝ).Subsingleton := by
              simpa using hsub
            have hx : (2*a + b)/3 ∈ (Ico a b : Set ℝ) := by
              apply Set.mem_Ico.mpr; constructor <;> nlinarith
            have hy : (a + 2*b)/3 ∈ (Ico a b : Set ℝ) := by
              apply Set.mem_Ico.mpr; constructor <;> nlinarith
            have h_val_eq : (2*a + b)/3 = (a + 2*b)/3 :=
              hsub_set hx hy
            have hneq : (2*a + b)/3 ≠ (a + 2*b)/3 := by nlinarith
            exfalso; exact hneq h_val_eq
        subst this
        cases I with
        | Ioo _ _ => simp at hI'
        | Icc a b => use (Icc b b), hK, Ico a b; apply join_Ico_Icc <;> order
        | Ioc a b => use (Icc b b), hK, Ioo a b; apply join_Ioo_Icc <;> order
        | Ico _ _ => simp at hI'
      simp [length_of_subsingleton, -Set.subsingleton_coe] at hsub
      have hKI' := (K.Ioo_subset.trans hKI).trans I.subset_Icc
      simp only [subset_iff] at hKI'
      have hKb : K.b = I.b := by
        rw [le_antisymm_iff]; split_ands
        . apply csSup_le_csSup bddAbove_Icc (by simp [hsub]) at hKI'
          simp_all [csSup_Ioo hsub, csSup_Icc (le_of_lt h)]
        have := K.subset_Icc _ hbK; simp [mem_iff] at this; exact this.2
      have hKA : I.a ≤ K.a := by
        apply csInf_le_csInf bddBelow_Icc (by simp [hsub]) at hKI'
        simp_all [csInf_Icc (le_of_lt h), csInf_Ioo]
      cases I with
      | Ioo _ _ => simp [mem_iff] at hI'
      | Icc a₁ b₁ =>
        use K; cases K with
        | Ioo _ _ => simp [mem_iff, subset_iff] at *; grind
        | Icc c₂ b₂ => use Ico a₁ c₂, hK; simp_all; apply join_Ico_Icc <;> order
        | Ioc c₂ b₂ => use Icc a₁ c₂, hK; simp_all; apply join_Icc_Ioc <;> order
        | Ico _ _ => simp [mem_iff] at *; grind
      | Ioc a₁ b₁ =>
        use K; cases K with
        | Ioo _ _ => simp_all [mem_iff]
        | Icc c₂ b₂ =>
          use Ioo a₁ c₂, hK
          simp_all [subset_iff]
          have : c₂ ∈ Set.Icc c₂ b₁ := by grind
          apply hKI at this; grind [join_Ioo_Icc]
        | Ioc c₂ b₂ => use Ioc a₁ c₂, hK; simp_all; apply join_Ioc_Ioc <;> order
        | Ico _ _ => simp [mem_iff, subset_iff] at *; grind
      | Ico _ _ => simp [mem_iff] at hI'
    choose c hc hK using P.exist_right h hI'
    cases I with
    | Ioo a₁ b₁ =>
      obtain hK | hK := hK <;> simp_all [mem_iff]
      . use Ioo c b₁, hK, Ioc a₁ c; apply join_Ioc_Ioo <;> tauto
      use Ico c b₁, hK, Ioo a₁ c
      apply P.contains at hK; simp [subset_iff] at hK
      have : c ∈ Set.Ico c b₁ := by grind
      grind [join_Ioo_Ico]
    | Icc _ _ => simp [mem_iff] at hI' h; order
    | Ioc _ _ => simp [mem_iff] at hI' h; order
    | Ico a₁ b₁ =>
      obtain hK | hK := hK <;> simp_all [mem_iff]
      . use Ioo c b₁, hK, Icc a₁ c; grind [join_Icc_Ioo]
      use Ico c b₁, hK, Ico a₁ c; grind [join_Ico_Ico]
  obtain ⟨ K, L, hK, ⟨ h1, h2, h3 ⟩ ⟩ := hex
  have hP'ex : ∃ P' : Partition L, P'.intervals = P.intervals.erase K := by
    refine ⟨{
      intervals := P.intervals.erase K
      exists_unique := by
        intro x hxL
        have hxI : x ∈ (I : Set ℝ) := by
          rw [h2]
          exact Set.mem_union_left (K : Set ℝ) hxL
        rcases P.exists_unique x hxI with ⟨J, ⟨hJmem, hxJ⟩, huniq⟩
        have hx_not_K : x ∉ (K : Set ℝ) := by
          intro hxK
          have : x ∈ (L : Set ℝ) ∩ (K : Set ℝ) := Set.mem_inter hxL hxK
          rw [h1] at this
          simp at this
        have hJ_ne_K : J ≠ K := by
          intro h_eq
          subst h_eq
          apply hx_not_K
          simpa [mem_iff] using hxJ
        have hJ_mem_erase : J ∈ P.intervals.erase K :=
          Finset.mem_erase.mpr ⟨hJ_ne_K, hJmem⟩
        refine ⟨J, ⟨hJ_mem_erase, hxJ⟩, ?_⟩
        intro J' ⟨hJ'_mem_erase, hxJ'⟩
        have hJ'_mem : J' ∈ P.intervals := (Finset.mem_erase.mp hJ'_mem_erase).2
        exact huniq J' ⟨hJ'_mem, hxJ'⟩
      contains := by
        intro J hJ_erase
        have hJmem : J ∈ P.intervals := (Finset.mem_erase.mp hJ_erase).2
        have hJ_ne_K : J ≠ K := (Finset.mem_erase.mp hJ_erase).1
        intro x hxJ
        have hxI : x ∈ (I : Set ℝ) := (P.contains J hJmem) x hxJ
        rw [h2] at hxI
        rcases hxI with (hxL | hxK)
        · simpa [mem_iff] using hxL
        · exfalso
          have hxI' : x ∈ (I : Set ℝ) := by
            rw [h2]
            exact Set.mem_union_right (L : Set ℝ) hxK
          rcases P.exists_unique x hxI' with ⟨J', ⟨hJ'mem, hxJ'⟩, huniq⟩
          have hJ_eq_K : J = K :=
            (huniq J ⟨hJmem, hxJ⟩).trans (huniq K ⟨hK, by
              simpa [mem_iff] using hxK⟩).symm
          exact hJ_ne_K hJ_eq_K
    }, rfl⟩
  obtain ⟨ P', hP' ⟩ := hP'ex
  exact ⟨K, L, hK, ⟨h1, h2, h3⟩, P', hP'⟩

/-- Exercise 11.4.2 -/
theorem IntegrableOn.split {I: BoundedInterval} {f: ℝ → ℝ} (hf: IntegrableOn f I) (P: Partition I) :
  integ f I = ∑ J ∈ P.intervals, integ f J := by
  generalize hcard : P.intervals.card = n
  revert I; induction' n with n hn <;> intro I hf P hcard
  · -- No intervals: `I` must be empty, so both sides vanish.
    rw [Finset.card_eq_zero] at hcard
    have hIempty : (I : Set ℝ) = ∅ := by
      by_contra! hne
      rcases hne with ⟨x, hx⟩
      rcases P.exists_unique x hx with ⟨J, ⟨hJmem, _⟩, _⟩
      rw [hcard] at hJmem; simp at hJmem
    have hlen0 : |I|ₗ = 0 := BoundedInterval.length_of_empty hIempty
    rw [hcard, Finset.sum_empty]
    exact (integ_on_subsingleton hlen0).2
  by_cases h : Subsingleton (I : Set ℝ)
  · -- `I` is a single point: every interval of the partition is a point, all integrals vanish.
    have hIsub : ∀ J ∈ P.intervals, integ f J = 0 := by
      intro J hJ
      have hJsub : Subsingleton (J : Set ℝ) := by
        apply Subsingleton.intro
        intro a b
        apply Subtype.ext
        have haI : a.val ∈ (I : Set ℝ) := (P.contains J hJ a.val) a.property
        have hbI : b.val ∈ (I : Set ℝ) := (P.contains J hJ b.val) b.property
        have h_eq : (⟨a.val, haI⟩ : (I : Set ℝ)) = (⟨b.val, hbI⟩ : (I : Set ℝ)) :=
          Subsingleton.elim _ _
        injection h_eq
      have hJlen : |J|ₗ = 0 := BoundedInterval.length_of_subsingleton.mp hJsub
      exact (integ_on_subsingleton hJlen).2
    have hIlen : |I|ₗ = 0 := BoundedInterval.length_of_subsingleton.mp h
    rw [(integ_on_subsingleton hIlen).2, Finset.sum_eq_zero hIsub]
  · -- Peel off a rightmost interval `K` with complement `L`; apply the inductive hypothesis to `L`.
    obtain ⟨K, L, hK, hjoin, P', hP'⟩ := partition_join_erase P h
    obtain ⟨hfL, hfK, hIeq⟩ := hf.join hjoin
    have hcardP' : P'.intervals.card = n := by
      rw [hP', Finset.card_erase_of_mem hK, hcard]
      omega
    have hLsum : integ f L = ∑ J ∈ P'.intervals, integ f J := hn hfL P' hcardP'
    rw [hIeq, ← Finset.add_sum_erase _ _ hK, ← hP', ← hLsum]
    exact add_comm _ _

end Chapter11
