import Analysis.MeasureTheory.Section_1_1_2

open BoundedInterval
open Pointwise
open MeasureTheory

set_option maxHeartbeats 0

/-- For a box B, the metric entropy at scale n equals the product of 1D interval counts. -/
lemma metric_entropy_lower_box_count {d:ℕ} (B : Box d) (n : ℤ) :
    metric_entropy_lower (B.toSet) n = ∏ j : Fin d, (Finset.Ico ⌈(B.side j).a * 2^n⌉ ⌊(B.side j).b * 2^n⌋).card := by
  sorry

/-- For a box B, the scaled lower dyadic entropy converges to its volume. -/
lemma metric_entropy_lower_box_tendsto {d:ℕ} (B : Box d) :
    Filter.atTop.Tendsto (fun n:ℤ ↦ (2:ℝ)^(-(d*n:ℤ)) * (metric_entropy_lower (B.toSet) n : ℝ)) (nhds |B|ᵥ) := by
  have h_count : ∀ n : ℤ, (metric_entropy_lower (B.toSet) n : ℝ) = ∏ j : Fin d, ((Finset.Ico ⌈(B.side j).a * 2^n⌉ ⌊(B.side j).b * 2^n⌋).card : ℝ) := by
    intro n; exact_mod_cast metric_entropy_lower_box_count B n
  have h_1d (I : BoundedInterval) : Filter.atTop.Tendsto (fun n:ℤ ↦ (2:ℝ)^(-n) * ((Finset.Ico ⌈I.a * 2 ^ n⌉ ⌊I.b * 2 ^ n⌋).card : ℝ)) (nhds |I|ₗ) := by
    simpa [BoundedInterval.length] using dyadic_count_tendsto I.a I.b
  have h_conv : Filter.atTop.Tendsto (fun n:ℤ ↦ ∏ j : Fin d, ((2:ℝ)^(-n) * ((Finset.Ico ⌈(B.side j).a * 2 ^ n⌉ ⌊(B.side j).b * 2 ^ n⌋).card : ℝ))) (nhds (∏ j : Fin d, |B.side j|ₗ)) := by
    refine tendsto_finset_prod (Finset.univ : Finset (Fin d)) (fun j _ => ?_)
    exact (h_1d (B.side j)).comp (show Filter.Tendsto id Filter.atTop Filter.atTop from Filter.tendsto_id)
  have h_factor (n : ℤ) : (2:ℝ)^(-(d*n:ℤ)) * (metric_entropy_lower (B.toSet) n : ℝ) = ∏ j : Fin d, ((2:ℝ)^(-n) * ((Finset.Ico ⌈(B.side j).a * 2 ^ n⌉ ⌊(B.side j).b * 2 ^ n⌋).card : ℝ)) := by
    rw [h_count n]
    calc
      (2 : ℝ) ^ (-(d * n : ℤ)) * ∏ j : Fin d, ((Finset.Ico ⌈(B.side j).a * 2 ^ n⌉ ⌊(B.side j).b * 2 ^ n⌋).card : ℝ)
          = (2 : ℝ) ^ ((-n : ℤ) * (d : ℤ)) * ∏ j : Fin d, ((Finset.Ico ⌈(B.side j).a * 2 ^ n⌉ ⌊(B.side j).b * 2 ^ n⌋).card : ℝ) := by
            have h_exp : -(d * n : ℤ) = (-n : ℤ) * (d : ℤ) := by ring
            rw [h_exp]
      _ = ((2 : ℝ) ^ (-n : ℤ)) ^ (d : ℤ) * ∏ j : Fin d, ((Finset.Ico ⌈(B.side j).a * 2 ^ n⌉ ⌊(B.side j).b * 2 ^ n⌋).card : ℝ) := by
        simp [zpow_mul]
      _ = ((2 : ℝ) ^ (-n : ℤ)) ^ d * ∏ j : Fin d, ((Finset.Ico ⌈(B.side j).a * 2 ^ n⌉ ⌊(B.side j).b * 2 ^ n⌋).card : ℝ) := by
        norm_cast
      _ = (∏ j : Fin d, (2 : ℝ) ^ (-n : ℤ)) * ∏ j : Fin d, ((Finset.Ico ⌈(B.side j).a * 2 ^ n⌉ ⌊(B.side j).b * 2 ^ n⌋).card : ℝ) := by
        simp
      _ = ∏ j : Fin d, ((2 : ℝ) ^ (-n : ℤ) * ((Finset.Ico ⌈(B.side j).a * 2 ^ n⌉ ⌊(B.side j).b * 2 ^ n⌋).card : ℝ)) := by
        simp [Finset.prod_mul_distrib]
  simp_rw [h_factor]
  have h_vol : |B|ᵥ = ∏ j : Fin d, |B.side j|ₗ := rfl
  rw [h_vol]
  exact h_conv

lemma metric_entropy_lower_tendsto {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E) :
    Filter.atTop.Tendsto (fun n:ℤ ↦ (2:ℝ)^(-(d*n:ℤ)) * (metric_entropy_lower E n))
      (nhds (Jordan_inner_measure E)) := by
  set L := Jordan_inner_measure E with hL
  have hpos : ∀ n:ℤ, 0 ≤ (2:ℝ)^(-(d*n:ℤ)) := by intro n; positivity
  apply Metric.tendsto_nhds.mpr; intro ε hε
  have h_ex : ∃ (A : Set (EuclideanSpace' d)) (hA : IsElementary A), A ⊆ E ∧ hA.measure > L - ε / 2 := by
    have h_lt : L - ε / 2 < L := by nlinarith
    obtain ⟨A, hA, hAE, hA_gt⟩ := Jordan_inner_le h_lt
    exact ⟨A, hA, hAE, hA_gt⟩
  obtain ⟨A, hA, hAE, hA_gt⟩ := h_ex
  have hA_upper : ∀ n : ℤ, (2:ℝ)^(-(d*n:ℤ)) * (metric_entropy_lower A n : ℝ) ≤ hA.measure := by
    intro n
    have h_bound := metric_entropy_lower_upper_bound (IsElementary.isBounded hA) n
    have h_eq : Jordan_inner_measure A = hA.measure := by
      apply le_antisymm
      · calc
          Jordan_inner_measure A ≤ Jordan_outer_measure A := Jordan_inner_le_outer (IsElementary.isBounded hA)
          _ ≤ hA.measure := Jordan_outer_le hA (Set.Subset.refl A)
      · exact le_Jordan_inner hA (Set.Subset.refl A)
    rw [h_eq] at h_bound
    exact h_bound
  -- For any elementary A, 2^{-dn} * metric_entropy_lower A n → hA.measure, proved via
  -- metric_entropy_lower_box_tendsto for each box in a partition of A, summing over boxes,
  -- and showing the boundary term (dyadic boxes crossing box boundaries) has volume O(2^{-n}) → 0.
  -- A complete proof uses IsElementary.partition, dyadic_box_disjoint, and the box convergence.
  sorry

lemma metric_entropy_upper_lower_bound {d:ℕ} {E : Set (EuclideanSpace' d)} (hE : Bornology.IsBounded E) (n : ℤ) :
    Jordan_outer_measure E ≤ (2:ℝ)^(-(d*n:ℤ)) * (metric_entropy_upper E n : ℝ) := by
  -- Dual to metric_entropy_lower_upper_bound. The union of dyadic boxes at scale n that intersect E
  -- is an elementary superset of E, and its measure equals metric_entropy_upper E n * 2^{-dn}.
  -- Therefore this measure belongs to the set whose infimum is Jordan_outer_measure E.
  -- The proof parallels metric_entropy_lower_upper_bound: show the index set is finite (E bounded),
  -- construct the union, prove it's elementary and disjoint, compute its measure, then use csInf_le.
  sorry

/-- Scaled upper dyadic entropy converges to the outer Jordan measure (any bounded set). -/
lemma metric_entropy_upper_tendsto {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E) :
    Filter.atTop.Tendsto (fun n:ℤ ↦ (2:ℝ)^(-(d*n:ℤ)) * (metric_entropy_upper E n))
      (nhds (Jordan_outer_measure E)) := by
  set U := Jordan_outer_measure E with hU
  have hpos : ∀ n:ℤ, 0 ≤ (2:ℝ)^(-(d*n:ℤ)) := by intro n; positivity
  apply Metric.tendsto_nhds.mpr; intro ε hε
  have h_ex : ∃ (B : Set (EuclideanSpace' d)) (hB : IsElementary B), E ⊆ B ∧ hB.measure < U + ε / 2 := by
    have h_lt : U < U + ε / 2 := by nlinarith
    obtain ⟨B, hB, hEB, hB_lt⟩ := le_Jordan_outer h_lt hE
    exact ⟨B, hB, hEB, hB_lt⟩
  obtain ⟨B, hB, hEB, hB_lt⟩ := h_ex
  have hB_upper : ∀ n : ℤ, (2:ℝ)^(-(d*n:ℤ)) * (metric_entropy_upper B n : ℝ) ≥ hB.measure := by
    intro n
    have h_ineq : Jordan_outer_measure B ≤ (2:ℝ)^(-(d*n:ℤ)) * (metric_entropy_upper B n : ℝ) := by
      -- Dual to metric_entropy_lower_upper_bound. The union of dyadic boxes at scale n that
      -- intersect B is an elementary superset of B, and its measure = metric_entropy_upper B n * 2^{-dn}.
      -- Therefore this measure is in the set whose infimum is Jordan_outer_measure B.
      -- A full proof mirrors metric_entropy_lower_upper_bound with "(Box.dyadic n i).toSet ⊆ E"
      -- replaced by "(Box.dyadic n i).toSet ∩ B ≠ ∅".
      sorry
    have h_outer_eq : Jordan_outer_measure B = hB.measure := by
      set S := {m | ∃ (A : Set (EuclideanSpace' d)) (hA : IsElementary A), B ⊆ A ∧ m = hA.measure} with hS
      have hS_nonempty : S.Nonempty := ⟨hB.measure, B, hB, Set.Subset.refl B, rfl⟩
      have hBdd : BddBelow S := by
        refine ⟨0, λ m hm => ?_⟩
        obtain ⟨A, hA, _, rfl⟩ := hm
        exact IsElementary.measure_nonneg hA
      have hx_mem : hB.measure ∈ S := ⟨B, hB, Set.Subset.refl B, rfl⟩
      apply le_antisymm
      · calc
          Jordan_outer_measure B = sInf S := rfl
          _ ≤ hB.measure := csInf_le hBdd hx_mem
      · refine le_csInf hS_nonempty ?_
        rintro m ⟨A, hA, hBA, rfl⟩
        exact IsElementary.measure_mono hB hA hBA
    calc
      hB.measure = Jordan_outer_measure B := by symm; exact h_outer_eq
      _ ≤ (2:ℝ)^(-(d*n:ℤ)) * (metric_entropy_upper B n : ℝ) := h_ineq
  -- Then for large n, the scaled upper entropy of B is close to hB.measure, and since E ⊆ B,
  -- the entropy of E is ≤ that of B, giving the upper bound. The lower bound U ≤ scaled_upper
  -- entropy(E) follows from a lemma dual to metric_entropy_lower_upper_bound.
  -- A full proof follows the ε-N argument of metric_entropy_lower_tendsto.
  sorry
