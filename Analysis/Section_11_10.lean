import Mathlib.Tactic
import Analysis.Section_9_6
import Analysis.Section_10_3
import Analysis.Section_11_9


/-!
# Analysis I, Section 11.10: Consequences of the fundamental theorems

I have attempted to make the translation as faithful a paraphrasing as possible of the
original text. When there is a choice between a more idiomatic Lean solution and a
more faithful translation, I have generally chosen the latter. In particular, there will
be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I
have consciously avoided doing so.

Main constructions and results of this section:
- Integration by parts

-/

namespace Chapter11

open BoundedInterval Chapter9 Chapter10

/-- Proposition 11.10.1 (Integration by parts formula) / Exercise 11.10.1 -/
theorem integ_of_mul_deriv {a b:ℝ} (hab: a ≤ b) {F G: ℝ → ℝ}
  (hF: DifferentiableOn ℝ F (Icc a b)) (hG : DifferentiableOn ℝ G (Icc a b))
  (hF': IntegrableOn (derivWithin F (Icc a b)) (Icc a b))
  (hG': IntegrableOn (derivWithin G (Icc a b)) (Icc a b)) :
  integ (F * derivWithin G (Icc a b)) (Icc a b) = F b * G b - F a * G a -
    integ (G * derivWithin F (Icc a b)) (Icc a b) := by
  set f := derivWithin F (Icc a b)
  set g := derivWithin G (Icc a b)
  by_cases hab' : a < b
  · have hF_cont : ContinuousOn F (Icc a b) := hF.continuousOn
    have hG_cont : ContinuousOn G (Icc a b) := hG.continuousOn
    have hF_bdd : BddOn F (Icc a b) := BddOn.of_continuous_on_compact hab' hF_cont
    have hG_bdd : BddOn G (Icc a b) := BddOn.of_continuous_on_compact hab' hG_cont
    have hF_int : IntegrableOn F (Icc a b) := integ_of_bdd_cts hF_bdd hF_cont
    have hG_int : IntegrableOn G (Icc a b) := integ_of_bdd_cts hG_bdd hG_cont
    have hFg_int : IntegrableOn (F * g) (Icc a b) := integ_of_mul hF_int hG'
    have hGf_int : IntegrableOn (G * f) (Icc a b) := integ_of_mul hG_int hF'
    have hsum_int : IntegrableOn (F*g + G*f) (Icc a b) := (hFg_int.add hGf_int).1
    have hsum_integ_eq : integ (F*g + G*f) (Icc a b) = integ (F*g) (Icc a b) + integ (G*f) (Icc a b) :=
      (hFg_int.add hGf_int).2
    have hFG_antideriv : AntiderivOn (F*G) (F*g + G*f) (Icc a b) := by
      refine ⟨ hF.mul hG, fun x hx => ?_ ⟩
      have hF_deriv : HasDerivWithinAt F (f x) (Icc a b) x := (hF x hx).hasDerivWithinAt
      have hG_deriv : HasDerivWithinAt G (g x) (Icc a b) x := (hG x hx).hasDerivWithinAt
      simpa [add_comm, mul_comm, f, g] using hF_deriv.mul hG_deriv
    have h_integ_eq : integ (F*g + G*f) (Icc a b) = (F*G) b - (F*G) a :=
      integ_eq_antideriv_sub hab hsum_int hFG_antideriv
    rw [hsum_integ_eq] at h_integ_eq
    simp at h_integ_eq
    linarith
  · have hab_eq : a = b := by linarith
    rw [hab_eq]
    have hlen : |Icc b b|ₗ = 0 := by simp
    have h_integ_any : ∀ (h : ℝ → ℝ), integ h (Icc b b) = 0 :=
      fun h => (integ_on_subsingleton hlen).2
    simp [h_integ_any, sub_self]

/-- Theorem 11.10.2.  Need to add continuity of α due to our conventions on {name}`α_length` -/
theorem PiecewiseConstantOn.RS_integ_eq_integ_of_mul_deriv
  {a b:ℝ} {α f:ℝ → ℝ}
  (hα_diff: DifferentiableOn ℝ α (Icc a b)) (hαcont: Continuous α)
  (hα': IntegrableOn (derivWithin α (Icc a b)) (Icc a b))
  (hf: PiecewiseConstantOn f (Icc a b)) :
  IntegrableOn (f * derivWithin α (Icc a b)) (Icc a b) ∧
  Chapter11.integ (f * derivWithin α (Icc a b)) (Icc a b) = RS_integ f (Icc a b) α := by
  -- This proof is adapted from the structure of the original text.
  set α' := derivWithin α (Icc a b)
  have hf_integ: IntegrableOn f (Icc a b) := (integ_of_piecewise_const hf).1
  observe hfα'_integ: IntegrableOn (f * α') (Icc a b)
  refine ⟨ hfα'_integ, ?_ ⟩
  choose P hP using hf
  rw [PiecewiseConstantOn.RS_integ_def hP α, hfα'_integ.split P]
  apply Finset.sum_congr rfl; intro J hJ
  calc
    _ = Chapter11.integ ((constant_value_on f (J:Set ℝ)) • α') J := by
      apply Chapter11.integ_congr; intro x hx
      simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]; congr
      exact (hP J hJ).eq hx
    _ = constant_value_on f (J:Set ℝ) * Chapter11.integ α' J := ((hα'.mono' (P.contains _ hJ)).smul _).2
    _ = _ := by
      congr
      have hJsub (hJab : J.a ≤ J.b) : J ⊆ Ioo (J.a - 1) (J.b + 1) :=
        (subset_Icc J).trans (by simp [subset_iff, Set.Icc_subset_Ioo_iff hJab])
      obtain hJab | hJab := le_iff_eq_or_lt.mp (length_nonneg J)
      . rw [(integ_on_subsingleton hJab.symm).2]
        simp [le_iff_lt_or_eq] at hJab; obtain hJab | hJab := hJab
        . rw [α_length_of_empty _ (empty_of_lt hJab)]
        rw [α_length_of_cts _ _ _ (hJsub _) hαcont.continuousOn] <;> grind
      simp [length] at hJab
      rw [α_length_of_cts ?_ ?_ ?_ (hJsub ?_) hαcont.continuousOn ]
      . have : Icc J.a J.b ⊆ Icc a b := by
          have := closure_mono $ (subset_iff _ _).mp $ (Ioo_subset J).trans $ P.contains _ hJ
          simpa [closure_Ioo (show J.a ≠ J.b by linarith), subset_iff] using this
        calc
          _ = Chapter11.integ α' (Icc J.a J.b) := (hα'.mono' this).eq (subset_Icc J) rfl rfl
          _ = _ := by
            convert integ_eq_antideriv_sub (by order) (hα'.mono' this) _
            apply AntiderivOn.mono ⟨ hα_diff, _ ⟩ this
            intros; solve_by_elim [DifferentiableWithinAt.hasDerivWithinAt]
      all_goals linarith

/-- Corollary 11.10.3 -/
theorem RS_integ_eq_integ_of_mul_deriv
  {a b:ℝ} (hab: a < b) {α f:ℝ → ℝ} (hα: Monotone α)
  (hα_diff: DifferentiableOn ℝ α (Icc a b)) (hαcont: Continuous α)
  (hα': IntegrableOn (derivWithin α (Icc a b)) (Icc a b))
  (hf: RS_IntegrableOn f (Icc a b) α) :
  IntegrableOn (f * derivWithin α (Icc a b)) (Icc a b) ∧
  integ (f * derivWithin α (Icc a b)) (Icc a b) = RS_integ f (Icc a b) α := by
  -- This proof is adapted from the structure of the original text.
  set α' := derivWithin α (Icc a b)
  have hfα'_bound: BddOn (f * α') (Icc a b) := by
    have ⟨ M, hM ⟩ := hf.1; have ⟨ N, hN ⟩ := hα'.1
    use M * N; intro x hx; specialize hM _ hx; specialize hN _ hx
    simp [abs_mul]; gcongr; linarith [abs_nonneg (f x)]
  have hα'_nonneg : MajorizesOn α' 0 (Icc a b) := by
    intro x hx
    convert ge_iff_le.mp (derivative_of_monotone _ _ hα (hα_diff x hx))
    rw [←mem_closure_iff_clusterPt]
    simp at hx
    obtain h | h := le_iff_lt_or_eq.mp hx.1
    . apply closure_mono (s := .Ico a x) _
      . simp [closure_Ico (show a ≠ x by linarith), hx.1]
      intro _ _; simp_all; grind
    apply closure_mono (s := .Ioc x b) _
    . simp [closure_Ioc (show x ≠ b by linarith), hx.2]
    intro _ _; simp_all
  have h0 := hf.2
  have h1 : RS_integ f (Icc a b) α ≤ lower_integral (f * α') (Icc a b) := by
    apply le_of_forall_sub_le; intro ε hε
    have ⟨ h, hhminor, hhconst, hh ⟩ :=
      gt_of_lt_lower_RS_integral hf.1 hα (show RS_integ f (Icc a b) α - ε < lower_RS_integral f (Icc a b) α by linarith)
    have := hhconst.RS_integ_eq_integ_of_mul_deriv hα_diff hαcont hα'
    rw [←this.2] at hh
    replace : lower_integral (h * α') (Icc a b) = integ (h * α') (Icc a b) := this.1.2
    have why : lower_integral (h * α') (Icc a b) ≤ lower_integral (f * α') (Icc a b) := by
      have hbdd_h : BddOn h (Icc a b) := ((integ_of_piecewise_const hhconst).1).1
      have hbdd_hα' : BddOn (h * α') (Icc a b) := BddOn.mul h α' (Icc a b) hbdd_h hα'.1
      apply csSup_le (integral_bound_lower_nonempty hbdd_hα')
      intro y hy
      rcases hy with ⟨g, ⟨hg_min, hg_pc⟩, rfl⟩
      apply integ_le_lower_integral hfα'_bound ?_ hg_pc
      intro x hx
      have hhx : h x ≤ f x := hhminor x hx
      have hα'x : 0 ≤ α' x := hα'_nonneg x hx
      have hgx : g x ≤ (h * α') x := hg_min x hx
      have hineq : (h * α') x ≤ (f * α') x := by
        dsimp
        nlinarith
      exact le_trans hgx hineq
    linarith

  have h2 : upper_integral (f * α') (Icc a b) ≤ RS_integ f (Icc a b) α := by
    apply le_of_forall_pos_le_add; intro ε hε
    have ⟨ h, hhmajor, hhconst, hh ⟩ :=
      lt_of_gt_upper_RS_integral hf.1 hα (show upper_RS_integral f (Icc a b) α + ε > RS_integ f (Icc a b) α by linarith)
    have := hhconst.RS_integ_eq_integ_of_mul_deriv hα_diff hαcont hα'
    rw [←this.2] at hh
    have why : upper_integral (f * α') (Icc a b) ≤ upper_integral (h * α') (Icc a b) := by
      have hbdd_h : BddOn h (Icc a b) := ((integ_of_piecewise_const hhconst).1).1
      have hbdd_hα' : BddOn (h * α') (Icc a b) := BddOn.mul h α' (Icc a b) hbdd_h hα'.1
      refine csInf_le_csInf (integral_bound_below hfα'_bound) (integral_bound_upper_nonempty hbdd_hα') ?_
      intro y hy
      rcases hy with ⟨g, ⟨hg_maj, hg_pc⟩, rfl⟩
      refine ⟨g, ⟨?_, hg_pc⟩, rfl⟩
      intro x hx
      have hhx : f x ≤ h x := hhmajor x hx
      have hα'x : 0 ≤ α' x := hα'_nonneg x hx
      have hgx : (h * α') x ≤ g x := hg_maj x hx
      have hineq : (f * α') x ≤ (h * α') x := by
        dsimp
        nlinarith
      exact le_trans hineq hgx
    linarith
  have h3 : lower_integral (f * α') (Icc a b) ≤
    upper_integral (f * α') (Icc a b) := lower_integral_le_upper hfα'_bound
  refine ⟨ ⟨ hfα'_bound, ?_ ⟩, ?_ ⟩ <;> linarith

/-- Lemma 11.10.5 / Exercise 11.10.2-/
lemma sInf_BoundedInterval_eq_a (I : BoundedInterval) (h : (I : Set ℝ).Nonempty) : sInf (I : Set ℝ) = I.a := by
  obtain ⟨x, hx⟩ := h
  cases I with
  | Icc a b =>
    have hx' : x ∈ Set.Icc a b := hx
    have hab : a ≤ b := le_trans hx'.1 hx'.2
    simpa using csInf_Icc hab
  | Ioo a b =>
    have hx' : x ∈ Set.Ioo a b := hx
    have hab : a < b := by
      have hx1 : a < x := hx'.1
      have hx2 : x < b := hx'.2
      linarith
    simpa using csInf_Ioo hab
  | Ioc a b =>
    have hx' : x ∈ Set.Ioc a b := hx
    have hab : a < b := by
      have hx1 : a < x := hx'.1
      have hx2 : x ≤ b := hx'.2
      linarith
    simpa using csInf_Ioc hab
  | Ico a b =>
    have hx' : x ∈ Set.Ico a b := hx
    have hab : a < b := by
      have hx1 : a ≤ x := hx'.1
      have hx2 : x < b := hx'.2
      linarith
    simpa using csInf_Ico hab

lemma sSup_BoundedInterval_eq_b (I : BoundedInterval) (h : (I : Set ℝ).Nonempty) : sSup (I : Set ℝ) = I.b := by
  obtain ⟨x, hx⟩ := h
  cases I with
  | Icc a b =>
    have hx' : x ∈ Set.Icc a b := hx
    have hab : a ≤ b := le_trans hx'.1 hx'.2
    simpa using csSup_Icc hab
  | Ioo a b =>
    have hx' : x ∈ Set.Ioo a b := hx
    have hab : a < b := by
      have hx1 : a < x := hx'.1
      have hx2 : x < b := hx'.2
      linarith
    simpa using csSup_Ioo hab
  | Ioc a b =>
    have hx' : x ∈ Set.Ioc a b := hx
    have hab : a < b := by
      have hx1 : a < x := hx'.1
      have hx2 : x ≤ b := hx'.2
      linarith
    simpa using csSup_Ioc hab
  | Ico a b =>
    have hx' : x ∈ Set.Ico a b := hx
    have hab : a < b := by
      have hx1 : a ≤ x := hx'.1
      have hx2 : x < b := hx'.2
      linarith
    simpa using csSup_Ico hab

theorem PiecewiseConstantOn.RS_integ_of_comp {a b:ℝ} (hab: a < b) {φ f:ℝ → ℝ}
  (hφ_cont: Continuous φ) (hφ_mono: Monotone φ) (hf: PiecewiseConstantOn f (Icc (φ a) (φ b))) :
  PiecewiseConstantOn (f ∘ φ) (Icc a b) ∧ RS_integ (f ∘ φ) (Icc a b) φ =
    integ f (Icc (φ a) (φ b)) := by
  -- This proof is adapted from the structure of the original text.
  choose P' hf using hf
  set P := P'.remove_empty
  replace hf : PiecewiseConstantWith f P := by
    intro J hJ; simp [P, (· ∈ ·)] at hJ; exact hf J hJ.1
  rw [integ_def hf]
  unfold PiecewiseConstantWith.integ
  set φ_inv : P.intervals → Set ℝ := fun J ↦ { x:ℝ | x ∈ Set.Icc a b ∧ φ x ∈ (J:Set ℝ) }
  have hφ_inv_bounded (J: P.intervals) : Bornology.IsBounded (φ_inv J) := by
    apply Bornology.IsBounded.subset (Icc_bounded a b); intro _; aesop
  have hφ_inv_connected (J: P.intervals) : (φ_inv J).OrdConnected := by
    refine Set.OrdConnected.mk fun x hx y hy => ?_
    have hx' : x ∈ φ_inv J := hx
    have hy' : y ∈ φ_inv J := hy
    simp [φ_inv] at hx' hy'
    intro z hz
    have hzIcc : z ∈ Set.Icc a b :=
      (Set.ordConnected_Icc.out' (Set.mem_Icc.mpr hx'.1) (Set.mem_Icc.mpr hy'.1)) hz
    have hzJ : φ z ∈ (J : Set ℝ) := by
      have hJord : ((J : Set ℝ) : Set ℝ).OrdConnected :=
        ((BoundedInterval.ordConnected_iff (J : Set ℝ)).mpr ⟨J, rfl⟩).2
      have hφxJ : φ x ∈ (J : Set ℝ) := hx'.2
      have hφyJ : φ y ∈ (J : Set ℝ) := hy'.2
      have hφx_le_φz : φ x ≤ φ z := hφ_mono hz.1
      have hφz_le_φy : φ z ≤ φ y := hφ_mono hz.2
      exact (hJord.out' hφxJ hφyJ) ⟨hφx_le_φz, hφz_le_φy⟩
    exact ⟨hzIcc, hzJ⟩
  set φ_inv' : P.intervals → BoundedInterval := fun J ↦ ((BoundedInterval.ordConnected_iff _).mp ⟨ hφ_inv_bounded J, hφ_inv_connected J ⟩).choose
  have hφ_inv' (J:P.intervals) : φ_inv J = φ_inv' J :=
    ((BoundedInterval.ordConnected_iff _).mp ⟨ hφ_inv_bounded J, hφ_inv_connected J ⟩).choose_spec
  have hφ_inv_nonempty (J:P.intervals) : (φ_inv J).Nonempty := by
    have hJ_nonempty : (J.val : Set ℝ).Nonempty := by
      open Classical in
      have hmem : J.val ∈ P.intervals := J.property
      have hmem' : J.val ∈ (P'.intervals).filter (fun (K : BoundedInterval) ↦ (K : Set ℝ).Nonempty) := by
        simp [P, Partition.remove_empty]
      rcases Finset.mem_filter.1 hmem' with ⟨_, h⟩
      exact h
    obtain ⟨y, hy⟩ := hJ_nonempty
    have hJ_contains : (J.val : Set ℝ) ⊆ Icc (φ a) (φ b) :=
      P.contains J.val J.property
    have hyIcc : y ∈ Set.Icc (φ a) (φ b) := hJ_contains hy
    have ha_le_b : a ≤ b := by linarith
    have h_surj : Set.Icc (φ a) (φ b) ⊆ φ '' (Set.Icc a b) :=
      intermediate_value_Icc ha_le_b hφ_cont.continuousOn
    obtain ⟨x, hxIcc, hx_eq⟩ := h_surj hyIcc
    refine ⟨x, ?_⟩
    simp [φ_inv, hx_eq]
    exact ⟨hxIcc, hy⟩
  have hφ_inv_const {J:P.intervals} : ConstantOn (f ∘ φ) (φ_inv' J) ∧ constant_value_on (f ∘ φ) (φ_inv' J) = constant_value_on f J := by
    have hJ_const : ConstantOn f (J.val : Set ℝ) := hf J.val J.property
    have h_eq_set : (φ_inv' J : Set ℝ) = φ_inv J := (hφ_inv' J).symm
    have h_constant : ConstantOn (f ∘ φ) (φ_inv' J) := by
      apply ConstantOn.of_const
      intro x hx
      have hx' : x ∈ φ_inv J := by
        rw [← h_eq_set]
        exact hx
      simp [φ_inv] at hx'
      calc
        (f ∘ φ) x = f (φ x) := rfl
        _ = constant_value_on f (J.val : Set ℝ) := hJ_const.eq hx'.2
    have h_value : constant_value_on (f ∘ φ) (φ_inv' J) = constant_value_on f J := by
      have h_nonempty : ((φ_inv' J : BoundedInterval) : Set ℝ).Nonempty := by
        rw [h_eq_set]
        exact hφ_inv_nonempty J
      apply ConstantOn.const_eq h_nonempty
      intro x hx
      have hx' : x ∈ φ_inv J := by
        rw [← h_eq_set]
        exact hx
      simp [φ_inv] at hx'
      calc
        (f ∘ φ) x = f (φ x) := rfl
        _ = constant_value_on f (J.val : Set ℝ) := hJ_const.eq hx'.2
    exact ⟨h_constant, h_value⟩
  set Q : Partition (Icc a b) := {
    intervals := Finset.image φ_inv' Finset.univ
    exists_unique := fun x hx => by
      have hx_set : x ∈ Set.Icc a b := hx
      have hφx_Icc : φ x ∈ Set.Icc (φ a) (φ b) :=
        ⟨hφ_mono hx_set.1, hφ_mono hx_set.2⟩
      rcases P.exists_unique (φ x) (by simpa using hφx_Icc) with ⟨J, ⟨hJ_mem, hxJ⟩, huniq⟩
      set J' : P.intervals := ⟨J, hJ_mem⟩
      have hx_in_φ_inv_J' : x ∈ φ_inv J' := by
        simp [φ_inv, J']
        exact ⟨hx, hxJ⟩
      have hx_in_φ_inv'_J' : x ∈ φ_inv' J' := by
        have := hx_in_φ_inv_J'
        rw [hφ_inv' J'] at this
        exact this
      refine ⟨φ_inv' J', ⟨?_, hx_in_φ_inv'_J'⟩, ?_⟩
      · simp [Finset.mem_image, J']
      · intro K hK
        rcases hK with ⟨hK_mem, hxK⟩
        rcases Finset.mem_image.1 hK_mem with ⟨J'', _, hK_eq⟩
        have hx_in_φ_inv'' : x ∈ φ_inv J'' := by
          have hxK' : x ∈ φ_inv' J'' := hK_eq.symm ▸ hxK
          exact (hφ_inv' J'').symm ▸ hxK'
        simp [φ_inv] at hx_in_φ_inv''
        have hφx_in_J'' : φ x ∈ (J''.val : Set ℝ) := hx_in_φ_inv''.2
        have hJ''_val_eq_J : J''.val = J :=
          huniq J''.val ⟨J''.property, hφx_in_J''⟩
        have hJ''_eq_J' : J'' = J' := Subtype.ext hJ''_val_eq_J
        calc
          K = φ_inv' J'' := hK_eq.symm
          _ = φ_inv' J' := by rw [hJ''_eq_J']
    contains := fun K hK => by
      rcases Finset.mem_image.1 hK with ⟨J, _, hK_eq⟩
      rw [← hK_eq]
      intro x hx
      have : x ∈ φ_inv J := (hφ_inv' J).symm ▸ hx
      simp [φ_inv] at this
      exact this.1
  }
  have hfφ_piecewise : PiecewiseConstantWith (f ∘ φ) Q := by
    intro K hK
    rcases Finset.mem_image.1 hK with ⟨J, _, hK_eq⟩
    have hK_eq' : (K : Set ℝ) = (φ_inv' J : Set ℝ) := by
      simp [hK_eq]
    -- rewrite the goal using hK_eq
    have : ConstantOn (f ∘ φ) (K : Set ℝ) := by
      -- using hK_eq, we replace K with φ_inv' J
      have := (hφ_inv_const (J := J)).1
      -- this : ConstantOn (f ∘ φ) (φ_inv' J : Set ℝ)
      -- need to show ConstantOn (f ∘ φ) (K : Set ℝ)
      simpa [hK_eq] using this
    exact this
  have hfφ_piecewise' : PiecewiseConstantOn (f ∘ φ) (Icc a b) := ⟨ Q, hfφ_piecewise ⟩
  refine ⟨ hfφ_piecewise' , ?_ ⟩
  rw [RS_integ_def hfφ_piecewise]
  unfold PiecewiseConstantWith.RS_integ
  rw [Finset.sum_image, ←Finset.sum_coe_sort (s := P.intervals)]
  . apply Finset.sum_congr rfl
    intro J _
    congr 1
    . exact hφ_inv_const.2
    have h_α_len : φ[φ_inv' J]ₗ = |J|ₗ := by
      set K := φ_inv' J
      have hK_nonempty : (K : Set ℝ).Nonempty := by
        have : (K : Set ℝ) = φ_inv J := (hφ_inv' J).symm
        rw [this]
        exact hφ_inv_nonempty J
      have hK_sub_Icc : (K : Set ℝ) ⊆ Set.Icc a b := by
        have : (K : Set ℝ) = φ_inv J := (hφ_inv' J).symm
        rw [this]
        intro x hx; simp [φ_inv] at hx; exact hx.1
      have h_bdd_below : BddBelow (K : Set ℝ) := BddBelow.mono hK_sub_Icc bddBelow_Icc
      have h_bdd_above : BddAbove (K : Set ℝ) := BddAbove.mono hK_sub_Icc bddAbove_Icc
      have hx_in_K_bounds {x : ℝ} (hx : x ∈ (K : Set ℝ)) : K.a ≤ x ∧ x ≤ K.b := by
        have h_sInf_K_eq_Ka : sInf (K : Set ℝ) = K.a := sInf_BoundedInterval_eq_a K hK_nonempty
        have h_sSup_K_eq_Kb : sSup (K : Set ℝ) = K.b := sSup_BoundedInterval_eq_b K hK_nonempty
        have h_sInf_le_x : sInf (K : Set ℝ) ≤ x := csInf_le h_bdd_below hx
        have hx_le_sSup : x ≤ sSup (K : Set ℝ) := le_csSup h_bdd_above hx
        rw [h_sInf_K_eq_Ka] at h_sInf_le_x
        rw [h_sSup_K_eq_Kb] at hx_le_sSup
        exact ⟨h_sInf_le_x, hx_le_sSup⟩
      have hK_ab : K.a ≤ K.b := by
        obtain ⟨x, hx⟩ := hK_nonempty
        obtain ⟨hx1, hx2⟩ := hx_in_K_bounds hx
        exact le_trans hx1 hx2
      have hK_sub_Ioo : (K : Set ℝ) ⊆ Set.Ioo (K.a - 1) (K.b + 1) := by
        intro x hx
        obtain ⟨hx1, hx2⟩ := hx_in_K_bounds hx
        refine ⟨by nlinarith, by nlinarith⟩
      have h_φ_cts : ContinuousOn φ (Set.Ioo (K.a - 1) (K.b + 1)) :=
        hφ_cont.continuousOn.mono (Set.subset_univ _)
      have hK_φ_len : φ[K]ₗ = φ K.b - φ K.a :=
        α_length_of_cts (haa := by nlinarith) (hab := hK_ab) (hbb := by nlinarith)
          (hI := hK_sub_Ioo) (hα := h_φ_cts)
      have hJ_nonempty : (J.val : Set ℝ).Nonempty := by
        classical
        have hmem : J.val ∈ P.intervals := J.property
        have hmem' : J.val ∈ (P'.intervals).filter (fun (K : BoundedInterval) ↦ (K : Set ℝ).Nonempty) := by
          dsimp [P, Partition.remove_empty] at hmem ⊢
          exact hmem
        rcases Finset.mem_filter.1 hmem' with ⟨_, h⟩
        exact h
      have hJ_ab : J.val.a ≤ J.val.b := by
        have hJ_contains : (J.val : Set ℝ) ⊆ (Icc (φ a) (φ b) : Set ℝ) :=
          P.contains J.val J.property
        have h_bdd_below_J : BddBelow (J.val : Set ℝ) :=
          BddBelow.mono hJ_contains bddBelow_Icc
        have h_bdd_above_J : BddAbove (J.val : Set ℝ) :=
          BddAbove.mono hJ_contains bddAbove_Icc
        have h_sInf_J_eq_Ja : sInf (J.val : Set ℝ) = J.val.a :=
          sInf_BoundedInterval_eq_a J.val hJ_nonempty
        have h_sSup_J_eq_Jb : sSup (J.val : Set ℝ) = J.val.b :=
          sSup_BoundedInterval_eq_b J.val hJ_nonempty
        obtain ⟨x, hx⟩ := hJ_nonempty
        have h_sInf_le_x : sInf (J.val : Set ℝ) ≤ x := csInf_le h_bdd_below_J hx
        have hx_le_sSup : x ≤ sSup (J.val : Set ℝ) := le_csSup h_bdd_above_J hx
        rw [h_sInf_J_eq_Ja] at h_sInf_le_x
        rw [h_sSup_J_eq_Jb] at hx_le_sSup
        exact le_trans h_sInf_le_x hx_le_sSup
      have h_len_J : |J|ₗ = J.val.b - J.val.a := by
        simp [BoundedInterval.length, hJ_ab]
      have h_image_sub_J : φ '' (K : Set ℝ) ⊆ (J.val : Set ℝ) := by
        rintro y ⟨x, hx, rfl⟩
        have hx_φ_inv : x ∈ φ_inv J := by
          rw [← (hφ_inv' J).symm]
          exact hx
        simp [φ_inv] at hx_φ_inv
        exact hx_φ_inv.2
      have h_J_sub_image : (J.val : Set ℝ) ⊆ φ '' (K : Set ℝ) := by
        intro y hy
        have hyIcc : y ∈ Set.Icc (φ a) (φ b) := by
          have hJ_contains : (J.val : Set ℝ) ⊆ (Icc (φ a) (φ b) : Set ℝ) :=
            P.contains J.val J.property
          exact hJ_contains hy
        have ha_le_b : a ≤ b := by linarith
        obtain ⟨x, hxIcc, hx_eq⟩ := intermediate_value_Icc ha_le_b hφ_cont.continuousOn hyIcc
        have hxK : x ∈ (K : Set ℝ) := by
          have hx_φ_inv : x ∈ φ_inv J := by
            -- need to show x ∈ Icc a b and φ x ∈ J.val
            -- hxIcc gives x ∈ Icc a b, hx_eq gives φ x = y, hy gives y ∈ J.val
            refine ⟨hxIcc, ?_⟩
            rw [hx_eq]
            exact hy
          -- hφ_inv' J : φ_inv J = φ_inv' J = K
          -- Use (hφ_inv' J).symm to rewrite hx_φ_inv's type
          exact ((hφ_inv' J).symm ▸ hx_φ_inv)
        exact ⟨x, hxK, hx_eq⟩
      have h_image_eq_J : φ '' (K : Set ℝ) = (J.val : Set ℝ) :=
        Set.Subset.antisymm h_image_sub_J h_J_sub_image
      have h_sInf_K_eq_Ka : sInf (K : Set ℝ) = K.a :=
        sInf_BoundedInterval_eq_a K hK_nonempty
      have h_sSup_K_eq_Kb : sSup (K : Set ℝ) = K.b :=
        sSup_BoundedInterval_eq_b K hK_nonempty
      have h_sInf_J_eq_Ja : sInf (J.val : Set ℝ) = J.val.a :=
        sInf_BoundedInterval_eq_a J.val hJ_nonempty
      have h_sSup_J_eq_Jb : sSup (J.val : Set ℝ) = J.val.b :=
        sSup_BoundedInterval_eq_b J.val hJ_nonempty
      have h_φKa_eq_Ja : φ K.a = J.val.a := by
        calc
          φ K.a = φ (sInf (K : Set ℝ)) := by rw [h_sInf_K_eq_Ka]
          _ = sInf (φ '' (K : Set ℝ)) :=
            Monotone.map_csInf_of_continuousAt (hφ_cont.continuousAt (x := sInf (K : Set ℝ))) hφ_mono hK_nonempty
              (A_bdd := h_bdd_below)
          _ = sInf (J.val : Set ℝ) := by rw [h_image_eq_J]
          _ = J.val.a := h_sInf_J_eq_Ja
      have h_φKb_eq_Jb : φ K.b = J.val.b := by
        calc
          φ K.b = φ (sSup (K : Set ℝ)) := by rw [h_sSup_K_eq_Kb]
          _ = sSup (φ '' (K : Set ℝ)) :=
            Monotone.map_csSup_of_continuousAt (hφ_cont.continuousAt (x := sSup (K : Set ℝ))) hφ_mono hK_nonempty
              (A_bdd := h_bdd_above)
          _ = sSup (J.val : Set ℝ) := by rw [h_image_eq_J]
          _ = J.val.b := h_sSup_J_eq_Jb
      calc
        φ[φ_inv' J]ₗ = φ K.b - φ K.a := hK_φ_len
        _ = J.val.b - J.val.a := by rw [h_φKb_eq_Jb, h_φKa_eq_Ja]
        _ = |J|ₗ := by rw [h_len_J]
    exact h_α_len
  intro J _ K _ hJK
  set x := (hφ_inv_nonempty J).some
  have h1 : x ∈ φ_inv J := (hφ_inv_nonempty J).some_mem
  have h2 : x ∈ φ_inv K := by rwa [hφ_inv' J, hJK, ←hφ_inv' K] at h1
  simp [φ_inv] at h1 h2
  have h3 : φ x ∈ Icc (φ a) (φ b) := by
    have := P.contains _ J.property
    simp only [subset_iff, mem_iff] at this ⊢
    exact this h1.2
  ext; apply (P.exists_unique _ h3).unique <;> simp [J.property, K.property, mem_iff, h1, h2]

/-- Proposition 11.10.6 (Change of variables formula II). -/
theorem RS_integ_of_comp {a b:ℝ} (hab: a < b) {φ f: ℝ → ℝ}
  (hφ_cont: Continuous φ) (hφ_mono: Monotone φ) (hf: IntegrableOn f (Icc (φ a) (φ b))) :
  RS_IntegrableOn (f ∘ φ) (Icc a b) φ ∧
  RS_integ (f ∘ φ) (Icc a b) φ = integ f (Icc (φ a) (φ b)) := by
  -- This proof is adapted from the structure of the original text.
  have hf_bdd := hf.1
  have hfφ_bdd : BddOn (f ∘ φ) (Icc a b) := by
    rcases hf_bdd with ⟨M, hM⟩
    use M
    intro x hx
    have hx' : φ x ∈ Icc (φ a) (φ b) := by
      have hax : a ≤ x := hx.1
      have hxb : x ≤ b := hx.2
      exact ⟨hφ_mono hax, hφ_mono hxb⟩
    simpa using hM (φ x) hx'
  have heq : lower_integral f (Icc (φ a) (φ b)) = upper_integral f (Icc (φ a) (φ b)) := hf.2
  have hupper : upper_RS_integral (f ∘ φ) (Icc a b) φ ≤ upper_integral f (Icc (φ a) (φ b)) := by
    apply le_of_forall_pos_le_add
    intro ε hε
    choose f_up hf_upmajor hf_upconst hf_up using lt_of_gt_upper_integral hf.1 (show upper_integral f (Icc (φ a) (φ b)) + ε > integ f (Icc (φ a) (φ b)) by grind)
    have hpc := PiecewiseConstantOn.RS_integ_of_comp hab hφ_cont hφ_mono hf_upconst
    rw [←hpc.2] at hf_up
    have : MajorizesOn (f_up ∘ φ) (f ∘ φ) (Icc a b) := by intro _ _; simp at *; apply hf_upmajor; aesop
    linarith [upper_RS_integral_le_integ hfφ_bdd this hpc.1 hφ_mono]
  have hlower : lower_integral f (Icc (φ a) (φ b)) ≤ lower_RS_integral (f ∘ φ) (Icc a b) φ := by
    apply le_of_forall_sub_le
    intro ε hε
    choose f_low hf_lowminor hf_lowconst hf_low using gt_of_lt_lower_integral hf.1 (show lower_integral f (Icc (φ a) (φ b)) - ε < lower_integral f (Icc (φ a) (φ b)) by grind)
    have hpc := PiecewiseConstantOn.RS_integ_of_comp hab hφ_cont hφ_mono hf_lowconst
    rw [←hpc.2] at hf_low
    have : MinorizesOn (f_low ∘ φ) (f ∘ φ) (Icc a b) := by intro _ _; simp at *; apply hf_lowminor; aesop
    linarith [integ_le_lower_RS_integral hfφ_bdd this hpc.1 hφ_mono]
  have hle : lower_RS_integral (f ∘ φ) (Icc a b) φ ≤ upper_RS_integral (f ∘ φ) (Icc a b) φ :=
    lower_RS_integral_le_upper hfφ_bdd hφ_mono
  refine ⟨ ⟨ hfφ_bdd, ?_ ⟩, ?_ ⟩ <;> linarith

/-- Proposition 11.10.7 (Change of variables formula III). -/
theorem integ_of_comp {a b:ℝ} (hab: a < b) {φ f: ℝ → ℝ}
  (hφ_diff: DifferentiableOn ℝ φ (Icc a b))
  (hφ_cont: Continuous φ) (hφ_mono: Monotone φ)
  (hφ': IntegrableOn (derivWithin φ (Icc a b)) (Icc a b))
  (hf: IntegrableOn f (Icc (φ a) (φ b))) :
  IntegrableOn (f ∘ φ * derivWithin φ (Icc a b)) (Icc a b) ∧
  integ (f ∘ φ * derivWithin φ (Icc a b)) (Icc a b) =
    integ f (Icc (φ a) (φ b)) := by
 have h1 := RS_integ_of_comp hab hφ_cont hφ_mono hf
 have h2 := RS_integ_eq_integ_of_mul_deriv hab hφ_mono hφ_diff hφ_cont hφ' h1.1
 refine ⟨ h2.1, by aesop ⟩

private def reflectInterval (J : BoundedInterval) : BoundedInterval :=
  match J with
  | Ioo a b => Ioo (-b) (-a)
  | Icc a b => Icc (-b) (-a)
  | Ioc a b => Ico (-b) (-a)
  | Ico a b => Ioc (-b) (-a)

private lemma reflectInterval_mem_iff (x : ℝ) (J : BoundedInterval) :
    x ∈ (reflectInterval J : Set ℝ) ↔ -x ∈ (J : Set ℝ) := by
  constructor
  · intro h; cases J with
    | Ioo a b =>
      simp [reflectInterval, Set.mem_Ioo] at h ⊢; rcases h with ⟨h₁, h₂⟩; constructor <;> nlinarith
    | Icc a b =>
      simp [reflectInterval, Set.mem_Icc] at h ⊢; rcases h with ⟨h₁, h₂⟩; constructor <;> nlinarith
    | Ioc a b =>
      simp [reflectInterval, Set.mem_Ico, Set.mem_Ioc] at h ⊢; rcases h with ⟨h₁, h₂⟩; constructor <;> nlinarith
    | Ico a b =>
      simp [reflectInterval, Set.mem_Ioc, Set.mem_Ico] at h ⊢; rcases h with ⟨h₁, h₂⟩; constructor <;> nlinarith
  · intro h; cases J with
    | Ioo a b =>
      simp [reflectInterval, Set.mem_Ioo] at h ⊢; rcases h with ⟨h₁, h₂⟩; constructor <;> nlinarith
    | Icc a b =>
      simp [reflectInterval, Set.mem_Icc] at h ⊢; rcases h with ⟨h₁, h₂⟩; constructor <;> nlinarith
    | Ioc a b =>
      simp [reflectInterval, Set.mem_Ioc, Set.mem_Ico] at h ⊢; rcases h with ⟨h₁, h₂⟩; constructor <;> nlinarith
    | Ico a b =>
      simp [reflectInterval, Set.mem_Ico, Set.mem_Ioc] at h ⊢; rcases h with ⟨h₁, h₂⟩; constructor <;> nlinarith

private lemma reflectInterval_length (J : BoundedInterval) : |reflectInterval J|ₗ = |J|ₗ := by
  cases J <;> dsimp [reflectInterval, BoundedInterval.length] <;> ring_nf

@[simp]
private lemma reflectInterval_reflectInterval (J : BoundedInterval) :
    reflectInterval (reflectInterval J) = J := by
  cases J <;> simp [reflectInterval]

private lemma reflectInterval_injective : Function.Injective (reflectInterval : BoundedInterval → BoundedInterval) := by
  intro J₁ J₂ h
  calc
    J₁ = reflectInterval (reflectInterval J₁) := by simp
    _ = reflectInterval (reflectInterval J₂) := by rw [h]
    _ = J₂ := by simp

private noncomputable def reflectPartition {a b : ℝ} (P : Partition (Icc a b)) : Partition (Icc (-b) (-a)) where
  intervals := Finset.image reflectInterval P.intervals
  exists_unique := by
    intro x hx
    rcases hx with ⟨hx1, hx2⟩
    have h_negx_Icc : -x ∈ (Icc a b : Set ℝ) := by
      refine ⟨by linarith, by linarith⟩
    rcases P.exists_unique (-x) h_negx_Icc with ⟨J, ⟨hJmem, h_negx_J⟩, huniq⟩
    refine ⟨reflectInterval J, ⟨Finset.mem_image.mpr ⟨J, hJmem, rfl⟩, ?_⟩, ?_⟩
    · exact (reflectInterval_mem_iff x J).mpr h_negx_J
    · intro K hK
      rcases hK with ⟨hKmem, hxK⟩
      rcases Finset.mem_image.1 hKmem with ⟨J', hJ'mem, hK_eq⟩
      have hx_reflect : x ∈ reflectInterval J' := by
        simpa [hK_eq] using hxK
      have h_negx_J' : -x ∈ (J' : Set ℝ) :=
        (reflectInterval_mem_iff x J').mp hx_reflect
      have hJ'_eq_J : J' = J := huniq J' ⟨hJ'mem, h_negx_J'⟩
      calc
        K = reflectInterval J' := hK_eq.symm
        _ = reflectInterval J := by rw [hJ'_eq_J]
  contains := by
    intro K hK
    rcases Finset.mem_image.1 hK with ⟨J, hJmem, hK_eq⟩
    subst hK_eq
    intro x hx
    have h_negx_J : -x ∈ (J : Set ℝ) :=
      (reflectInterval_mem_iff x J).mp hx
    have h_sub : (J : Set ℝ) ⊆ (Icc a b : Set ℝ) := by
      simpa [BoundedInterval.subset_iff] using P.contains J hJmem
    have h_negx_Icc : -x ∈ (Icc a b : Set ℝ) := h_sub h_negx_J
    rcases h_negx_Icc with ⟨h_negx1, h_negx2⟩
    refine ⟨by linarith, by linarith⟩

private lemma upper_riemann_sum_reflect {f : ℝ → ℝ} {a b : ℝ} {P : Partition (Icc a b)} :
    upper_riemann_sum (fun x ↦ f (-x)) (reflectPartition P) = upper_riemann_sum f P := by
  classical
    dsimp [upper_riemann_sum, reflectPartition]
    set s := P.intervals
    have h_inj : Set.InjOn reflectInterval (s : Set BoundedInterval) :=
      reflectInterval_injective.injOn (s := (s : Set BoundedInterval))
    have h_image : (∑ K ∈ Finset.image reflectInterval s,
        sSup ((fun x ↦ f (-x)) '' (K : Set ℝ)) * |K|ₗ) =
      (∑ J ∈ s,
        sSup ((fun x ↦ f (-x)) '' (reflectInterval J : Set ℝ)) * |reflectInterval J|ₗ) := by
      apply Finset.sum_image
      exact h_inj
    rw [h_image]
    refine Finset.sum_congr rfl ?_
    intro J hJ
    have h_set : ((fun x ↦ f (-x)) '' (reflectInterval J : Set ℝ)) = f '' (J : Set ℝ) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hx' : -x ∈ (J : Set ℝ) := (reflectInterval_mem_iff x J).mp hx
        exact ⟨-x, hx', by simp⟩
      · rintro ⟨x, hx, rfl⟩
        have hx' : -x ∈ (reflectInterval J : Set ℝ) := by
          rw [reflectInterval_mem_iff]
          simpa using hx
        exact ⟨-x, hx', by simp⟩
    simp [h_set, reflectInterval_length J]

private lemma lower_riemann_sum_reflect {f : ℝ → ℝ} {a b : ℝ} {P : Partition (Icc a b)} :
    lower_riemann_sum (fun x ↦ f (-x)) (reflectPartition P) = lower_riemann_sum f P := by
  classical
    dsimp [lower_riemann_sum, reflectPartition]
    set s := P.intervals
    have h_inj : Set.InjOn reflectInterval (s : Set BoundedInterval) :=
      reflectInterval_injective.injOn (s := (s : Set BoundedInterval))
    have h_image : (∑ K ∈ Finset.image reflectInterval s,
        sInf ((fun x ↦ f (-x)) '' (K : Set ℝ)) * |K|ₗ) =
      (∑ J ∈ s,
        sInf ((fun x ↦ f (-x)) '' (reflectInterval J : Set ℝ)) * |reflectInterval J|ₗ) := by
      apply Finset.sum_image
      exact h_inj
    rw [h_image]
    refine Finset.sum_congr rfl ?_
    intro J hJ
    have h_set : ((fun x ↦ f (-x)) '' (reflectInterval J : Set ℝ)) = f '' (J : Set ℝ) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hx' : -x ∈ (J : Set ℝ) := (reflectInterval_mem_iff x J).mp hx
        exact ⟨-x, hx', by simp⟩
      · rintro ⟨x, hx, rfl⟩
        have hx' : -x ∈ (reflectInterval J : Set ℝ) := by
          rw [reflectInterval_mem_iff]
          simpa using hx
        exact ⟨-x, hx', by simp⟩
    simp [h_set, reflectInterval_length J]

/-- Exercise 11.10.3 -/
example {a b : ℝ} (hab : a < b) {f : ℝ → ℝ} (hf : IntegrableOn f (Icc a b)) :
    IntegrableOn (fun x ↦ f (-x)) (Icc (-b) (-a)) ∧
    integ (fun x ↦ f (-x)) (Icc (-b) (-a)) = integ f (Icc a b) := by
  set g := fun x : ℝ ↦ f (-x) with hg_def
  have hg_bdd : BddOn g (Icc (-b) (-a)) := by
    rcases hf.1 with ⟨M, hM⟩
    refine ⟨M, ?_⟩
    intro x hx
    have h_negx_Icc : -x ∈ (Icc a b : Set ℝ) := by
      rcases hx with ⟨hx₁, hx₂⟩
      refine ⟨by linarith, by linarith⟩
    simpa [hg_def] using hM (-x) h_negx_Icc
  have hnegb_lt_nega : -b < -a := by linarith
  have h_upper_range_eq : Set.range (fun (P : Partition (Icc (-b) (-a))) => upper_riemann_sum g P) =
      Set.range (fun (P : Partition (Icc a b)) => upper_riemann_sum f P) := by
    apply Set.Subset.antisymm
    · rintro x ⟨P, rfl⟩
      have h := upper_riemann_sum_reflect (a := -b) (b := -a) (f := g) (P := P)
      have h' : upper_riemann_sum f (reflectPartition P) = upper_riemann_sum g P := by
        simpa [hg_def] using h
      have h_eq : Icc (-(-a)) (-(-b)) = (Icc a b : BoundedInterval) := by simp
      exact h_eq ▸ Set.mem_range.mpr ⟨reflectPartition P, h'⟩
    · rintro x ⟨P, rfl⟩
      have h := upper_riemann_sum_reflect (f := f) (P := P)
      refine ⟨reflectPartition P, ?_⟩
      simpa [hg_def] using h
  have h_upper_eq : upper_integral g (Icc (-b) (-a)) = upper_integral f (Icc a b) := by
    rw [upper_integ_eq_inf_upper_sum hg_bdd, upper_integ_eq_inf_upper_sum hf.1, h_upper_range_eq]
  have h_lower_range_eq : Set.range (fun (P : Partition (Icc (-b) (-a))) => lower_riemann_sum g P) =
      Set.range (fun (P : Partition (Icc a b)) => lower_riemann_sum f P) := by
    apply Set.Subset.antisymm
    · rintro x ⟨P, rfl⟩
      have h := lower_riemann_sum_reflect (a := -b) (b := -a) (f := g) (P := P)
      have h' : lower_riemann_sum f (reflectPartition P) = lower_riemann_sum g P := by
        simpa [hg_def] using h
      have h_eq : Icc (-(-a)) (-(-b)) = (Icc a b : BoundedInterval) := by simp
      exact h_eq ▸ Set.mem_range.mpr ⟨reflectPartition P, h'⟩
    · rintro x ⟨P, rfl⟩
      have h := lower_riemann_sum_reflect (f := f) (P := P)
      refine ⟨reflectPartition P, ?_⟩
      simpa [hg_def] using h
  have h_lower_eq : lower_integral g (Icc (-b) (-a)) = lower_integral f (Icc a b) := by
    rw [lower_integ_eq_sup_lower_sum hg_bdd, lower_integ_eq_sup_lower_sum hf.1, h_lower_range_eq]
  have h_int : lower_integral g (Icc (-b) (-a)) = upper_integral g (Icc (-b) (-a)) := by
    rw [h_lower_eq, h_upper_eq, hf.2]
  refine ⟨⟨hg_bdd, h_int⟩, ?_⟩
  dsimp [integ, g]
  rw [h_upper_eq]

/- Exercise 11.10.4: state and prove a version of `integ_of_comp` in which `φ` is `Antitone` rather than `Monotone`. -/

end Chapter11
