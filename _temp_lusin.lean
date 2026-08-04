import Analysis.MeasureTheory.Section_1_3_5

open Filter
open scoped Topology

/-- A simple function is relatively continuous on a closed set whose complement inside B has small measure. -/
private lemma coe_sum_eq_sum_coe {m : ℕ} (a : Fin m → ℝ) :
    (↑(∑ i, a i) : EReal) = ∑ i, (↑(a i) : EReal) := by
  induction m with
  | zero => simp [Finset.univ_eq_empty]
  | succ k ih =>
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, EReal.coe_add]
    congr 1
    exact ih (fun i => a i.castSucc)

private lemma fin_union_measurable {d:ℕ} {m : ℕ} (f : Fin m → Set (EuclideanSpace' d))
    (hf : ∀ i, LebesgueMeasurable (f i)) : LebesgueMeasurable (⋃ i : Fin m, f i) := by
  induction m with
  | zero =>
      simp
      exact LebesgueMeasurable.empty
  | succ m ih =>
      rw [show (⋃ i : Fin (m + 1), f i) = (⋃ i : Fin m, f i.castSucc) ∪ f (Fin.last m) from
        Set.iUnion_fin_add_one_eq_iUnion_castSucc f]
      exact (ih (fun i : Fin m => f i.castSucc) (fun i : Fin m => hf i.castSucc)).union (hf (Fin.last m))

private lemma simple_continuousOn_outside_small {d:ℕ} {s : EuclideanSpace' d → ℂ} {n : ℕ}
    {v : Fin n → ℂ} {A : Fin n → Set (EuclideanSpace' d)}
    (hs_eq : s = ∑ i, v i • Complex.indicator (A i))
    (hA_meas : ∀ i, LebesgueMeasurable (A i)) (hA_disj : Set.univ.PairwiseDisjoint A)
    (hA_fin : ∀ i, v i ≠ 0 → Lebesgue_measure (A i) < ⊤)
    {B : Set (EuclideanSpace' d)} (hB : LebesgueMeasurable B) (hBf : Lebesgue_measure B < ⊤)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : Set (EuclideanSpace' d), IsClosed C ∧ LebesgueMeasurable C ∧
      Lebesgue_measure (B \ C) ≤ δ ∧ Continuous (fun x : C => s x.val) := by
  sorry

/-- Multiplying a complex simple function by the indicator of a measurable set gives a simple function. -/
private lemma ComplexSimpleFunction.mul_indicator' {d:ℕ} {s : EuclideanSpace' d → ℂ} (hs : ComplexSimpleFunction s)
    {E : Set (EuclideanSpace' d)} (hE : LebesgueMeasurable E) :
    ComplexSimpleFunction (s * Complex.indicator E) := by
  rcases hs with ⟨k, c, A, hA_meas, heq⟩
  refine ⟨k, c, fun i => A i ∩ E, fun i => LebesgueMeasurable.inter (hA_meas i) hE, ?_⟩
  ext x
  rw [heq]
  simp only [Pi.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hx : x ∈ E
  · simp [Complex.indicator, Real.complex_fun, Set.indicator'_of_mem hx, mul_one]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    by_cases hxi : x ∈ A i
    · have hmem : x ∈ A i ∩ E := Set.mem_inter hxi hx
      simp [Set.indicator'_of_mem hxi, Set.indicator'_of_mem hmem]
    · have hnot : x ∉ A i ∩ E := by
        intro h
        exact hxi h.1
      simp [Set.indicator'_of_notMem hxi, Set.indicator'_of_notMem hnot]
  · simp [Complex.indicator, Real.complex_fun, Set.indicator'_of_notMem hx, mul_zero]
    symm
    apply Finset.sum_eq_zero
    intro i _
    rw [show (A i ∩ E).indicator' x = 0 from Set.indicator'_of_notMem (by
      intro h
      have h2 : x ∈ E := h.2
      exact hx h2)]
    norm_num

/-- The box with sides -N..N is measurable with finite measure. -/
private def lusin_box (d : ℕ) (N : ℕ) : Box d :=
  Box.mk (fun _ : Fin d => (BoundedInterval.Icc (-(N : ℝ)) (N : ℝ) : BoundedInterval))

private def lusin_A {d : ℕ} (N : ℕ) : Set (EuclideanSpace' d) := (lusin_box d N).toSet

private lemma lusin_A_meas {d : ℕ} (N : ℕ) : LebesgueMeasurable (lusin_A (d := d) N) := by
  exact Jordan_measurable.lebesgue (IsElementary.jordanMeasurable (IsElementary.box (lusin_box d N)))

private lemma lusin_A_fin {d : ℕ} (N : ℕ) : Lebesgue_measure (lusin_A (d := d) N) < ⊤ := by
  unfold Lebesgue_measure
  rw [Lebesgue_outer_measure.elementary (lusin_A (d := d) N) (IsElementary.box (lusin_box d N))]
  exact EReal.coe_lt_top _

/-- Theorem 1.3.28 (Lusin's theorem, relative continuity) -/
theorem ComplexAbsolutelyIntegrable.approx_by_continuous_outside_small_134 {d:ℕ} {f : EuclideanSpace' d → ℂ}
  (hf: ComplexAbsolutelyIntegrable f)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (g : EuclideanSpace' d → ℂ) (E: Set (EuclideanSpace' d)), Continuous (fun x : (Eᶜ : Set (EuclideanSpace' d)) => g x.val) ∧ LebesgueMeasurable E ∧
      Lebesgue_measure E ≤ ε ∧
      ∀ x ∉ E, g x = f x := by sorry

/-- Exercise 1.3.23 (Lusin's theorem only requires local absolute integrability) -/
theorem LocallyComplexAbsolutelyIntegrable.approx_by_continuous_outside_small_134 {d:ℕ} {f : EuclideanSpace' d → ℂ}
  (hf: LocallyComplexAbsolutelyIntegrable f)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (g : EuclideanSpace' d → ℂ) (E: Set (EuclideanSpace' d)), Continuous (fun x : (Eᶜ : Set (EuclideanSpace' d)) => g x.val) ∧ LebesgueMeasurable E ∧
      Lebesgue_measure E ≤ ε ∧
      ∀ x ∉ E, g x = f x := by sorry

theorem ComplexMeasurable.approx_by_continuous_outside_small_134 {d:ℕ} {f : EuclideanSpace' d → ℂ}
  (hf: ComplexMeasurable f)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (g : EuclideanSpace' d → ℂ) (E: Set (EuclideanSpace' d)), Continuous (fun x : (Eᶜ : Set (EuclideanSpace' d)) => g x.val) ∧ LebesgueMeasurable E ∧
      Lebesgue_measure E ≤ ε ∧
      ∀ x ∉ E, g x = f x := by sorry
