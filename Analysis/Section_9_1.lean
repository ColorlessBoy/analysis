import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Basic
import Analysis.Section_6_4
import Mathlib.Topology.MetricSpace.Sequences
/-!
# Analysis I, Section 9.1: Subsets of the real line

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Review of Mathlib intervals.
- Adherent points, limit points, isolated points.
- Closed sets and closure.
- The Heine-Borel theorem for the real line.

-/

variable (I : Type*)

/- Definition 9.1.1 (Intervals) -/
#check Set.Icc_def
#check Set.Ico_def
#check Set.Ioc_def
#check Set.Ioo_def
#check Set.Ici_def
#check Set.Ioi_def
#check Set.Iic_def
#check Set.Iio_def

#check EReal.image_coe_Icc
#check EReal.image_coe_Ico
#check EReal.image_coe_Ioc
#check EReal.image_coe_Ioo
#check EReal.image_coe_Ici
#check EReal.image_coe_Ioi
#check EReal.image_coe_Iic
#check EReal.image_coe_Iio

/-- Example 9.1.4 -/
example {a b: EReal} (h: a > b) : Set.Icc a b = ∅ :=
  Set.Icc_eq_empty_of_lt h

example {a b: EReal} (h: a ≥ b) : Set.Ico a b = ∅ :=
  Set.Ico_eq_empty_of_le h

example {a b: EReal} (h: a ≥ b) : Set.Ioc a b = ∅ :=
  Set.Ioc_eq_empty_of_le h

example {a b: EReal} (h: a ≥ b) : Set.Ioo a b = ∅ :=
  Set.Ioo_eq_empty (not_lt.mpr h)

example {a b: EReal} (h: a = b) : Set.Icc a b = {a} := by
  subst h; simp

/--
Definition 9.1.5.  Note that a slightly different {name}`Real.Adherent` was defined in
Chapter 6.4
-/
abbrev Real.adherent' (ε:ℝ) (x:ℝ) (X: Set ℝ) := ∃ y ∈ X, |x - y| ≤ ε

/-- Example 9.1.7 -/
example : (0.5:ℝ).adherent' 1.1 (.Ioo 0 1) := by
  use 0.6; constructor <;> norm_num

example : ¬ (0.1:ℝ).adherent' 1.1 (.Ioo 0 1) := by
  intro h; rcases h with ⟨y, hy, h⟩
  have hy' : y < 1 := hy.2
  have hpos : 0 ≤ 1.1 - y := by linarith
  have : |1.1 - y| = 1.1 - y := abs_of_nonneg hpos
  linarith

example : (0.5:ℝ).adherent' 1.1 {1,2,3} := by
  use 1; simp; norm_num


namespace Chapter9

/-- Definition 9.1.-/
abbrev AdherentPt (x:ℝ) (X:Set ℝ) := ∀ ε > (0:ℝ), ε.adherent' x X

example : AdherentPt 1 (.Ioo 0 1) := by
  intro ε hε
  by_cases h : 1 ≤ ε
  · refine ⟨1/2, ⟨by norm_num, by norm_num⟩, ?_⟩
    have : |1 - (1/2 : ℝ)| = (1/2 : ℝ) := by norm_num
    rw [this]
    linarith
  · have hε1 : ε < 1 := by linarith
    use 1 - ε/2
    have hpos : 0 < 1 - ε/2 := by nlinarith
    have hlt : 1 - ε/2 < 1 := by nlinarith
    have hbound : |1 - (1 - ε/2)| ≤ ε := by
      have hpos' : 0 < ε/2 := by nlinarith
      have : |1 - (1 - ε/2)| = ε/2 := by
        have hcalc : 1 - (1 - ε/2) = ε/2 := by ring
        simp [hcalc, abs_of_pos hpos']
      rw [this]
      nlinarith
    exact ⟨⟨hpos, hlt⟩, hbound⟩

example : ¬ AdherentPt 2 (.Ioo 0 1) := by
  intro h
  have h1 := h 1 (by norm_num)
  rcases h1 with ⟨y, hy, h⟩
  have hy' : y < 1 := hy.2
  have : |2 - y| > 1 := by
    have : 2 - y > 1 := by linarith
    rw [abs_of_pos (by linarith : 0 < 2 - y)]
    linarith
  linarith

/-- Definition 9.1.10 (Closure).  Here we identify this definition with the Mathilb version. -/
theorem closure_def (X:Set ℝ) : closure X = { x | AdherentPt x X } := by
  ext; simp [Real.mem_closure_iff, AdherentPt, Real.adherent']
  constructor <;> intro h ε hε
  all_goals choose y hy hxy using h _ (half_pos hε); exact ⟨ _, hy, by rw [abs_sub_comm]; linarith ⟩

theorem closure_def' (X:Set ℝ) (x :ℝ) : x ∈ closure X ↔ AdherentPt x X := by
  simp [closure_def]

/-- identification of {name}`AdherentPt` with Mathlib's {name}`ClusterPt` -/
theorem AdherentPt_def (x:ℝ) (X:Set ℝ) : AdherentPt x X = ClusterPt x (.principal X) := by
  rw [←closure_def', mem_closure_iff_clusterPt]

/-- Lemma 9.1.11 / Exercise 9.1.1 -/
theorem subset_closure (X:Set ℝ): X ⊆ closure X := by
  intro x hx
  rw [closure_def']
  intro ε hε
  use x
  exact ⟨hx, by
    have : |x - x| = 0 := by simp
    rw [this]
    exact hε.le⟩

/-- Lemma 9.1.11 / Exercise 9.1.1 -/
theorem closure_union (X Y:Set ℝ): closure (X ∪ Y) = closure X ∪ closure Y := by
  ext x
  simp [closure_def', Set.mem_union]

/-- Lemma 9.1.11 / Exercise 9.1.1 -/
theorem closure_inter (X Y:Set ℝ): closure (X ∩ Y) ⊆ closure X ∩ closure Y := by
  intro x hx
  have hadh : AdherentPt x (X ∩ Y) := (closure_def' (X ∩ Y) x).mp hx
  have hX : AdherentPt x X := by
    intro ε hε
    rcases hadh ε hε with ⟨y, ⟨hyX, hyY⟩, h⟩
    use y, hyX, h
  have hY : AdherentPt x Y := by
    intro ε hε
    rcases hadh ε hε with ⟨y, ⟨hyX, hyY⟩, h⟩
    use y, hyY, h
  rw [Set.mem_inter_iff, closure_def', closure_def']
  exact ⟨hX, hY⟩

/-- Lemma 9.1.11 / Exercise 9.1.1 -/
theorem closure_subset {X Y:Set ℝ} (h: X ⊆ Y): closure X ⊆ closure Y := by
  intro x hx
  have hadhX : AdherentPt x X := (closure_def' X x).mp hx
  rw [closure_def']
  intro ε hε
  rcases hadhX ε hε with ⟨y, hyX, hdist⟩
  use y
  exact ⟨h hyX, hdist⟩

/-- Exercise 9.1.6 -/
theorem closure_of_subset_closure {X Y:Set ℝ} (h: X ⊆ Y) (h' : Y ⊆ closure X): closure Y = closure X := by
  apply Set.Subset.antisymm
  · calc
      closure Y ⊆ closure (closure X) := closure_subset h'
      _ = closure X := closure_closure
  · exact closure_subset h

/-- Lemma 9.1.12 -/
theorem closure_of_Ioo {a b:ℝ} (h:a < b) : closure (.Ioo a b) = .Icc a b := by
  -- This proof is written to follow the structure of the original text.
  ext x; simp [closure_def, AdherentPt, Real.adherent']
  constructor
  . intro h; contrapose! h
    obtain h' | h' := le_or_gt a x
    . specialize h h'
      use x-b, by linarith
      intro y ⟨ _, _ ⟩; observe : x-y ≤ |x-y|; linarith
    use a-x, by linarith
    intro y ⟨ _, _ ⟩; observe : -(x-y) ≤ |x-y|; linarith
  intro ⟨ h1, h2 ⟩
  by_cases ha : x = a
  · rw [ha]
    intro ε hε
    by_cases hε_small : ε/2 < (b-a)/2
    · use a + ε/2
      have hpos : a < a + ε/2 := by nlinarith
      have hlt : a + ε/2 < b := by nlinarith
      have hdist : |a - (a + ε/2)| ≤ ε := by
        have h_abs : |a - (a + ε/2)| = ε/2 := by
          have : a - (a + ε/2) = -(ε/2) := by ring
          rw [this, abs_neg, abs_of_pos (by nlinarith : 0 < ε/2)]
        rw [h_abs]
        nlinarith
      exact ⟨⟨hpos, hlt⟩, hdist⟩
    · use a + (b-a)/2
      have hpos : a < a + (b-a)/2 := by nlinarith
      have hlt : a + (b-a)/2 < b := by nlinarith
      have hdist : |a - (a + (b-a)/2)| ≤ ε := by
        have h_abs : |a - (a + (b-a)/2)| = (b-a)/2 := by
          have : a - (a + (b-a)/2) = -((b-a)/2) := by ring
          rw [this, abs_neg, abs_of_pos (by nlinarith : 0 < (b-a)/2)]
        rw [h_abs]
        nlinarith
      exact ⟨⟨hpos, hlt⟩, hdist⟩
  by_cases hb : x = b
  · rw [hb]
    intro ε hε
    by_cases hε_small : ε/2 < (b-a)/2
    · use b - ε/2
      have hpos : a < b - ε/2 := by nlinarith
      have hlt : b - ε/2 < b := by nlinarith
      have hdist : |b - (b - ε/2)| ≤ ε := by
        have h_abs : |b - (b - ε/2)| = ε/2 := by
          have : b - (b - ε/2) = ε/2 := by ring
          rw [this, abs_of_pos (by nlinarith : 0 < ε/2)]
        rw [h_abs]
        nlinarith
      exact ⟨⟨hpos, hlt⟩, hdist⟩
    · use b - (b-a)/2
      have hpos : a < b - (b-a)/2 := by nlinarith
      have hlt : b - (b-a)/2 < b := by nlinarith
      have hdist : |b - (b - (b-a)/2)| ≤ ε := by
        have h_abs : |b - (b - (b-a)/2)| = (b-a)/2 := by
          have : b - (b - (b-a)/2) = (b-a)/2 := by ring
          rw [this, abs_of_pos (by nlinarith : 0 < (b-a)/2)]
        rw [h_abs]
        nlinarith
      exact ⟨⟨hpos, hlt⟩, hdist⟩
  intro ε _; use x, (by exact ⟨lt_of_le_of_ne h1 (Ne.symm ha), lt_of_le_of_ne h2 hb⟩); simp; order

theorem closure_of_Ioc {a b:ℝ} (h:a < b) : closure (.Ioc a b) = .Icc a b :=
  closure_Ioc h.ne

theorem closure_of_Ico {a b:ℝ} (h:a < b) : closure (.Ico a b) = .Icc a b :=
  closure_Ico h.ne

theorem closure_of_Icc {a b:ℝ} (_:a ≤ b) : closure (.Icc a b) = .Icc a b :=
  closure_Icc a b

theorem closure_of_Ioi {a:ℝ} : closure (.Ioi a) = .Ici a :=
  closure_Ioi a

theorem closure_of_Ici {a:ℝ} : closure (.Ici a) = .Ici a :=
  closure_Ici a

theorem closure_of_Iio {a:ℝ} : closure (.Iio a) = .Iic a :=
  closure_Iio a

theorem closure_of_Iic {a:ℝ} : closure (.Iic a) = .Iic a :=
  closure_Iic a

theorem closure_of_R : closure (.univ: Set ℝ) = .univ :=
  closure_univ

/-- Lemma 9.1.14 / Exercise 9.1.4-/
theorem limit_of_AdherentPt (X: Set ℝ) (x:ℝ) :
  AdherentPt x X ↔ ∃ a : ℕ → ℝ, (∀ n, a n ∈ X) ∧ Filter.atTop.Tendsto a (nhds x) := by
  constructor
  · intro h
    have h' (n : ℕ) : ∃ y ∈ X, |x - y| ≤ 1 / ((n : ℝ) + 1) :=
      h (1 / ((n : ℝ) + 1)) (by positivity)
    choose a ha hxa using h'
    refine ⟨a, ha, ?_⟩
    rw [Metric.tendsto_atTop]
    intro ε hε
    rcases exists_nat_one_div_lt hε with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    have hxan : |x - a n| ≤ 1 / ((n : ℝ) + 1) := hxa n
    have h1n : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      refine (one_div_le_one_div ?_ ?_).mpr ?_
      · positivity
      · positivity
      · have h' : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        nlinarith
    calc
      dist (a n) x = |a n - x| := by rw [Real.dist_eq]
      _ = |x - a n| := by rw [abs_sub_comm]
      _ ≤ 1 / ((n : ℝ) + 1) := hxan
      _ ≤ 1 / ((N : ℝ) + 1) := h1n
      _ < ε := hN
  · intro h
    rcases h with ⟨a, ha, hconv⟩
    intro ε hε
    rw [Metric.tendsto_atTop] at hconv
    rcases hconv ε hε with ⟨N, hN⟩
    use a N, ha N
    have hdist : dist (a N) x < ε := hN N (le_refl N)
    rw [Real.dist_eq, abs_sub_comm] at hdist
    exact hdist.le

/-- Lemma 9.1.13 / Exercise 9.1.2 -/
theorem closure_of_N :
  closure ((fun n:ℕ ↦ (n:ℝ)) '' .univ) = ((fun n:ℕ ↦ (n:ℝ)) '' .univ) := by
  set S := (fun n:ℕ ↦ (n:ℝ)) '' .univ with hS
  apply Set.Subset.antisymm
  · intro x hx
    have hx_adh : AdherentPt x S := (closure_def' S x).mp hx
    rcases (limit_of_AdherentPt S x).mp hx_adh with ⟨a, ha, hconv⟩
    have ha_nat (n : ℕ) : ∃ k : ℕ, a n = (k : ℝ) := by
      rcases ha n with ⟨k, _, h⟩
      exact ⟨k, h.symm⟩
    have h12 : (0 : ℝ) < 1/2 := by norm_num
    rcases (Metric.tendsto_atTop.mp hconv) (1/2) h12 with ⟨N, hN⟩
    rcases ha_nat N with ⟨k, hk⟩
    have hx_eq : x = (k : ℝ) := by
      have h_eq : ∀ n ≥ N, a n = (k : ℝ) := by
        intro n hn
        rcases ha_nat n with ⟨k', hk'⟩
        have hdist : |(k' : ℝ) - (k : ℝ)| < 1 := by
          calc
            |(k' : ℝ) - (k : ℝ)| = |a n - a N| := by rw [hk', hk]
            _ ≤ |a n - x| + |x - a N| := abs_sub_le _ _ _
            _ = |a n - x| + |a N - x| := by rw [abs_sub_comm x]
            _ < 1/2 + 1/2 := by
              have hn' := hN n hn; have hN' := hN N (le_refl N)
              rw [Real.dist_eq] at hn' hN'; nlinarith
            _ = 1 := by norm_num
        have hk_eq_int : (k' : ℤ) = (k : ℤ) := by
          have : |(k' : ℤ) - (k : ℤ)| < 1 := by exact_mod_cast hdist
          have h_abs_lt := abs_lt.mp this
          omega
        have hk_eq : (k' : ℝ) = (k : ℝ) := by exact_mod_cast hk_eq_int
        rw [hk', hk_eq]
      have h_conv_const : Filter.atTop.Tendsto a (nhds ((k : ℝ))) := by
        refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
        refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
        exact (h_eq n hn).symm
      exact tendsto_nhds_unique hconv h_conv_const
    rw [hS, Set.mem_image]
    exact ⟨k, trivial, hx_eq.symm⟩
  · exact subset_closure S

/-- Lemma 9.1.13 / Exercise 9.1.2 -/
theorem closure_of_Z :
  closure ((fun n:ℤ ↦ (n:ℝ)) '' .univ) = ((fun n:ℤ ↦ (n:ℝ)) '' .univ) := by
  set S := (fun n:ℤ ↦ (n:ℝ)) '' .univ with hS
  apply Set.Subset.antisymm
  · intro x hx
    have hx_adh : AdherentPt x S := (closure_def' S x).mp hx
    rcases (limit_of_AdherentPt S x).mp hx_adh with ⟨a, ha, hconv⟩
    have ha_int (n : ℕ) : ∃ k : ℤ, a n = (k : ℝ) := by
      rcases ha n with ⟨k, _, h⟩
      exact ⟨k, h.symm⟩
    have h12 : (0 : ℝ) < 1/2 := by norm_num
    rcases (Metric.tendsto_atTop.mp hconv) (1/2) h12 with ⟨N, hN⟩
    rcases ha_int N with ⟨k, hk⟩
    have hx_eq : x = (k : ℝ) := by
      have h_eq : ∀ n ≥ N, a n = (k : ℝ) := by
        intro n hn
        rcases ha_int n with ⟨k', hk'⟩
        have hdist : |(k' : ℝ) - (k : ℝ)| < 1 := by
          calc
            |(k' : ℝ) - (k : ℝ)| = |a n - a N| := by rw [hk', hk]
            _ ≤ |a n - x| + |x - a N| := abs_sub_le _ _ _
            _ = |a n - x| + |a N - x| := by rw [abs_sub_comm x]
            _ < 1/2 + 1/2 := by
              have hn' := hN n hn; have hN' := hN N (le_refl N)
              rw [Real.dist_eq] at hn' hN'; nlinarith
            _ = 1 := by norm_num
        have hk_eq_int : (k' : ℤ) = (k : ℤ) := by
          have : |(k' : ℤ) - (k : ℤ)| < 1 := by exact_mod_cast hdist
          have h_abs_lt := abs_lt.mp this
          omega
        have hk_eq : (k' : ℝ) = (k : ℝ) := by exact_mod_cast hk_eq_int
        rw [hk', hk_eq]
      have h_conv_const : Filter.atTop.Tendsto a (nhds ((k : ℝ))) := by
        refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
        refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
        exact (h_eq n hn).symm
      exact tendsto_nhds_unique hconv h_conv_const
    rw [hS, Set.mem_image]
    exact ⟨k, trivial, hx_eq.symm⟩
  · exact subset_closure S

/-- Lemma 9.1.13 / Exercise 9.1.2 -/
theorem closure_of_Q :
  closure ((fun n:ℚ ↦ (n:ℝ)) '' .univ) = .univ := by
  set S := (fun n:ℚ ↦ (n:ℝ)) '' .univ with hS
  apply Set.Subset.antisymm
  · exact Set.subset_univ _
  · intro x hx
    rw [closure_def']
    rw [limit_of_AdherentPt S x]
    have h (n : ℕ) : ∃ q : ℚ, x - 1 / ((n : ℝ) + 1) < (q : ℝ) ∧ (q : ℝ) < x := by
      have hpos : x - 1 / ((n : ℝ) + 1) < x := by
        have : 1 / ((n : ℝ) + 1) > 0 := by positivity
        linarith
      exact exists_rat_btwn hpos
    choose q hq_l hq_r using h
    refine ⟨fun n ↦ (q n : ℝ), ?_, ?_⟩
    · intro n
      simp [hS]
    · rw [Metric.tendsto_atTop]
      intro ε hε
      rcases exists_nat_one_div_lt hε with ⟨N, hN⟩
      refine ⟨N, ?_⟩
      intro n hn
      have hbound : 1 / ((n : ℝ) + 1) < ε := by
        have h_nN : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        have hpos_np1 : 0 < (n : ℝ) + 1 := by positivity
        have hpos_Np1 : 0 < (N : ℝ) + 1 := by positivity
        have h_one_div : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
          (one_div_le_one_div hpos_np1 hpos_Np1).mpr (by nlinarith)
        nlinarith
      rw [Real.dist_eq]
      calc
        |(q n : ℝ) - x| = |x - (q n : ℝ)| := by rw [abs_sub_comm]
        _ = x - (q n : ℝ) := abs_of_pos (sub_pos.mpr (hq_r n))
        _ < 1 / ((n : ℝ) + 1) := by
          nlinarith [hq_l n]
        _ < ε := hbound

theorem AdherentPt.of_mem {X: Set ℝ} {x: ℝ} (h: x ∈ X) : AdherentPt x X := by
  rw [limit_of_AdherentPt]; use fun _ ↦ x; simp [h]

/-- Definition 9.1.15.  Here we use the Mathlib definition. -/
theorem isClosed_def (X:Set ℝ): IsClosed X ↔ closure X = X :=
  closure_eq_iff_isClosed.symm

theorem isClosed_def' (X:Set ℝ): IsClosed X ↔ ∀ x, AdherentPt x X → x ∈ X := by
  simp [isClosed_def, subset_antisymm_iff, subset_closure]; simp [closure_def]; rfl

/-- Examples 9.1.16 -/
theorem Icc_closed {a b:ℝ} : IsClosed (.Icc a b) := isClosed_Icc

/-- Examples 9.1.16 -/
theorem Ici_closed (a:ℝ) : IsClosed (.Ici a) := isClosed_Ici

/-- Examples 9.1.16 -/
theorem Iic_closed (a:ℝ) : IsClosed (.Iic a) := isClosed_Iic

/-- Examples 9.1.16 -/
theorem R_closed : IsClosed (.univ : Set ℝ) := isClosed_univ

/-- Examples 9.1.16 -/
theorem Ico_not_closed {a b:ℝ} (h: a < b) : ¬ IsClosed (Set.Ico a b) := by
  rw [isClosed_def, closure_of_Ico h]
  intro h_eq
  have hb_mem_Icc : b ∈ Set.Icc a b := by
    simp [h.le]
  have hb_not_mem_Ico : b ∉ Set.Ico a b := by
    simp
  rw [h_eq] at hb_mem_Icc
  exact hb_not_mem_Ico hb_mem_Icc

/-- Examples 9.1.16 -/
theorem Ioc_not_closed {a b:ℝ} (h: a < b) : ¬ IsClosed (Set.Ioc a b) := by
  rw [isClosed_def, closure_of_Ioc h]
  intro h_eq
  have ha_mem_Icc : a ∈ Set.Icc a b := by
    simp [h.le]
  have ha_not_mem_Ioc : a ∉ Set.Ioc a b := by
    simp
  rw [h_eq] at ha_mem_Icc
  exact ha_not_mem_Ioc ha_mem_Icc

/-- Examples 9.1.16 -/
theorem Ioo_not_closed {a b:ℝ} (h: a < b) : ¬ IsClosed (Set.Ioo a b) := by
  rw [isClosed_def, closure_of_Ioo h]
  intro h_eq
  have ha_mem_Icc : a ∈ Set.Icc a b := by
    simp [h.le]
  have ha_not_mem_Ioo : a ∉ Set.Ioo a b := by
    simp
  rw [h_eq] at ha_mem_Icc
  exact ha_not_mem_Ioo ha_mem_Icc

/-- Examples 9.1.16 -/
theorem Ioi_not_closed (a:ℝ) : ¬ IsClosed (Set.Ioi a) := by
  rw [isClosed_def, closure_of_Ioi]
  intro h_eq
  have ha_mem_Ici : a ∈ Set.Ici a := by
    simp
  have ha_not_mem_Ioi : a ∉ Set.Ioi a := by
    simp
  rw [h_eq] at ha_mem_Ici
  exact ha_not_mem_Ioi ha_mem_Ici

/-- Examples 9.1.16 -/
theorem Iio_not_closed (a:ℝ) : ¬ IsClosed (Set.Iio a) := by
  rw [isClosed_def, closure_of_Iio]
  intro h_eq
  have ha_mem_Iic : a ∈ Set.Iic a := by
    simp
  have ha_not_mem_Iio : a ∉ Set.Iio a := by
    simp
  rw [h_eq] at ha_mem_Iic
  exact ha_not_mem_Iio ha_mem_Iic

/-- Examples 9.1.16 -/
theorem N_closed : IsClosed ((fun n:ℕ ↦ (n:ℝ)) '' .univ) := by
  rw [isClosed_def, closure_of_N]

/-- Examples 9.1.16 -/
theorem Z_closed : IsClosed ((fun n:ℤ ↦ (n:ℝ)) '' .univ) := by
  rw [isClosed_def, closure_of_Z]

/-- Examples 9.1.16 -/
theorem Q_not_closed : ¬ IsClosed ((fun n:ℚ ↦ (n:ℝ)) '' .univ) := by
  rw [isClosed_def, closure_of_Q]
  intro h_eq
  have h_sqrt2 : Real.sqrt 2 ∉ (fun n : ℚ ↦ (n : ℝ)) '' .univ := by
    intro h
    rcases h with ⟨q, _, hq⟩
    exact irrational_sqrt_two ⟨q, hq⟩
  apply h_sqrt2
  simp [h_eq.symm]

/-- Corollary 9.1.17 -/
theorem isClosed_iff_limits_mem (X: Set ℝ) :
  IsClosed X ↔ ∀ (a:ℕ → ℝ) (L:ℝ), (∀ n, a n ∈ X) → Filter.atTop.Tendsto a (nhds L) → L ∈ X := by
  rw [isClosed_def']
  constructor
  . intro h _ L _ _; apply h L; rw [limit_of_AdherentPt]; solve_by_elim
  intro _ _ hx; rw [limit_of_AdherentPt] at hx; grind

/-- Definition 9.1.18 (Limit points) -/
abbrev LimitPt (x:ℝ) (X: Set ℝ) := AdherentPt x (X \ {x})

/-- Identification with Mathlib's {name}`AccPt`-/
theorem LimitPt.iff_AccPt (x:ℝ) (X: Set ℝ) : LimitPt x X ↔ AccPt x (.principal X) := by
  rw [accPt_principal_iff_clusterPt,←AdherentPt_def]

/-- Definition 9.1.18 (Isolated points) -/
abbrev IsolatedPt (x:ℝ) (X: Set ℝ) := x ∈ X ∧ ∃ ε>0, ∀ y ∈ X \ {x}, |x-y| > ε

/-- Example 9.1.19 -/
example : AdherentPt 3 ((.Ioo 1 2) ∪ {3}) := by
  intro ε hε
  use 3
  simp
  exact hε.le

example : ¬ LimitPt 3 ((.Ioo 1 2) ∪ {3}) := by
  intro h
  have h' : AdherentPt 3 (.Ioo 1 2) := by
    intro ε hε
    rcases h ε hε with ⟨y, hy, hdist⟩
    have hy_mem : y ∈ Set.Ioo 1 2 := by
      have hy_union : y ∈ (Set.Ioo 1 2) ∪ {3} := hy.1
      have hy_not3 : y ∉ ({3} : Set ℝ) := hy.2
      rcases hy_union with (hy_ioo | hy_eq3)
      · exact hy_ioo
      · exfalso; exact hy_not3 (by simpa using hy_eq3)
    exact ⟨y, hy_mem, hdist⟩
  have h1 : (1 : ℝ) > 0 := by norm_num
  rcases h' 1 h1 with ⟨y, hy, hdist⟩
  have hy_lt_2 : y < 2 := hy.2
  have : |3 - y| > 1 := by
    have : 3 - y > 1 := by linarith
    rw [abs_of_pos (sub_pos.mpr (by linarith : y < 3))]
    linarith
  linarith

example : IsolatedPt 3 ((.Ioo 1 2) ∪ {3}) := by
  refine ⟨by simp, 1, by norm_num, ?_⟩
  intro y hy
  have hy_not_3 : y ≠ 3 := hy.2
  rcases hy.1 with (hy_ioo | hy_singleton)
  · have hy_lt_2 : y < 2 := hy_ioo.2
    have : |3 - y| > 1 := by
      have : 3 - y > 1 := by linarith
      rw [abs_of_pos (sub_pos.mpr (by linarith : y < 3))]
      linarith
    exact this
  · exfalso
    exact hy_not_3 hy_singleton

/-- Remark 9.1.20 -/
theorem LimitPt.iff_limit (x:ℝ) (X: Set ℝ) :
  LimitPt x X ↔ ∃ a : ℕ → ℝ, (∀ n, a n ∈ X \ {x}) ∧ Filter.atTop.Tendsto a (nhds x) :=
  limit_of_AdherentPt (X \ {x}) x

/-- Lemma 9.1.21 -/
theorem mem_Icc_isLimit {a b x:ℝ} (h: a < b) (hx: x ∈ Set.Icc a b) : LimitPt x (.Icc a b) := by
  -- This proof is written to follow the structure of the original text, with some slight simplifications.
  simp at hx
  rw [LimitPt.iff_limit]
  obtain hxb | hxb := le_iff_lt_or_eq.1 hx.2
  . use (fun n:ℕ ↦ (x + 1/(n+(b-x)⁻¹)))
    constructor
    . intro n; simp
      have : b - x > 0 := by linarith
      have : (b - x)⁻¹ > 0 := by positivity
      have : n + (b - x)⁻¹ > 0 := by linarith
      have : (n+(b - x)⁻¹)⁻¹ > 0 := by positivity
      have : (b-x)⁻¹ ≤ n + (b - x)⁻¹ := by linarith
      have : (n + (b - x)⁻¹)⁻¹ ≤ b-x := by rwa [inv_le_comm₀ ?_ ?_] <;> positivity
      grind
    convert (Filter.Tendsto.const_add x (a := 0) ?_) using 1; · simp
    convert Filter.Tendsto.comp (f := fun (k:ℕ) ↦ (k:ℝ)) (g := fun k ↦ 1/(k+(b-x)⁻¹)) ?_ tendsto_natCast_atTop_atTop
    convert tendsto_mul_add_inv_atTop_nhds_zero 1 (b - x)⁻¹ (by norm_num) using 2 with n; simp
  · rw [hxb]
    have hpos_diff : 0 < b - a := by linarith
    have h_lim : Filter.atTop.Tendsto (fun n : ℕ ↦ b - (b - a) / ((n : ℝ) + 1)) (nhds b) := by
      have h1 : Filter.atTop.Tendsto (fun n : ℕ ↦ (b - a) / ((n : ℝ) + 1)) (nhds 0) := by
        simpa [div_eq_mul_inv] using
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (b - a)
      simpa using (tendsto_const_nhds.sub h1)
    refine ⟨fun n ↦ b - (b - a) / ((n : ℝ) + 1), ?_, h_lim⟩
    intro n
    have hpos_n : 0 < (n : ℝ) + 1 := by positivity
    have h_one_div : 1 / ((n : ℝ) + 1) ≤ 1 := by
      have h_one_le_np1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
        nlinarith
      have htemp := (one_div_le_one_div hpos_n (by norm_num : (0 : ℝ) < 1)).mpr h_one_le_np1
      simpa using htemp
    have h_div_le : (b - a) / ((n : ℝ) + 1) ≤ b - a := by
      calc
        (b - a) / ((n : ℝ) + 1) = (b - a) * (1 / ((n : ℝ) + 1)) := by ring
        _ ≤ (b - a) * 1 := mul_le_mul_of_nonneg_left h_one_div (by linarith)
        _ = b - a := by ring
    have hpos_div : 0 < (b - a) / ((n : ℝ) + 1) := div_pos hpos_diff hpos_n
    have h_a_le : a ≤ b - (b - a) / ((n : ℝ) + 1) := by
      nlinarith
    have h_le_b : b - (b - a) / ((n : ℝ) + 1) ≤ b := by nlinarith
    have h_ne_b : b - (b - a) / ((n : ℝ) + 1) ≠ b := by nlinarith
    exact ⟨⟨h_a_le, h_le_b⟩, h_ne_b⟩

theorem mem_Ico_isLimit {a b x:ℝ} (hx: x ∈ Set.Ico a b) : LimitPt x (.Ico a b) := by
  simp at hx
  rcases hx with ⟨hx1, hx2⟩
  rw [LimitPt.iff_limit]
  have hpos_diff : 0 < b - x := by linarith
  have hn_nonneg (n : ℕ) : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hpos_n2 (n : ℕ) : 0 < (n : ℝ) + 2 := by nlinarith [hn_nonneg n]
  have hpos_n1 (n : ℕ) : 0 < (n : ℝ) + 1 := by nlinarith [hn_nonneg n]
  refine ⟨fun n ↦ x + (b-x)/((n:ℝ)+2), ?_, ?_⟩
  · intro n
    have hpos_div : 0 < (b-x)/((n:ℝ)+2) := div_pos hpos_diff (hpos_n2 n)
    have hm2 : x + (b-x)/((n:ℝ)+2) < b := by
      have h_one_div : 1/((n:ℝ)+2) < 1 := by
        have htemp := (one_div_lt_one_div (hpos_n2 n) (by norm_num : (0 : ℝ) < 1)).mpr (by
          have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          nlinarith)
        simpa using htemp
      have hdiv_lt : (b-x)/((n:ℝ)+2) < b-x := by
        calc
          (b-x)/((n:ℝ)+2) = (b-x) * (1/((n:ℝ)+2)) := by ring
          _ < (b-x) * 1 := mul_lt_mul_of_pos_left h_one_div hpos_diff
          _ = b-x := by ring
      nlinarith
    have h_a_le : a ≤ x + (b-x)/((n:ℝ)+2) := by nlinarith
    have h_ne : x + (b-x)/((n:ℝ)+2) ≠ x := by nlinarith
    refine ⟨?_, h_ne⟩
    rw [Set.mem_Ico]
    exact ⟨h_a_le, hm2⟩
  · have h_lim_div : Filter.atTop.Tendsto (fun n : ℕ ↦ (b-x)/((n:ℝ)+2)) (nhds 0) := by
      have h_main : Filter.atTop.Tendsto (fun n : ℕ ↦ (b-x)/((n:ℝ)+1)) (nhds 0) := by
        simpa [div_eq_mul_inv] using
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (b-x)
      have h_nonneg : ∀ n : ℕ, 0 ≤ (b-x)/((n:ℝ)+2) := fun n =>
        div_nonneg (by nlinarith) (hpos_n2 n).le
      have h_bound : ∀ n : ℕ, (b-x)/((n:ℝ)+2) ≤ (b-x)/((n:ℝ)+1) := fun n => by
        calc
          (b-x)/((n:ℝ)+2) = (b-x) * (1/((n:ℝ)+2)) := by ring
          _ ≤ (b-x) * (1/((n:ℝ)+1)) :=
            mul_le_mul_of_nonneg_left ((one_div_le_one_div (hpos_n2 n) (hpos_n1 n)).mpr (by nlinarith)) (by nlinarith)
          _ = (b-x)/((n:ℝ)+1) := by ring
      have h0 : Filter.atTop.Tendsto (fun n : ℕ ↦ (0 : ℝ)) (nhds 0) := tendsto_const_nhds
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le h0 h_main h_nonneg h_bound
    simpa using (Filter.Tendsto.const_add x h_lim_div)

theorem mem_Ioc_isLimit {a b x:ℝ} (hx: x ∈ Set.Ioc a b) : LimitPt x (.Ioc a b) := by
  simp at hx
  rcases hx with ⟨hx1, hx2⟩
  rw [LimitPt.iff_limit]
  have hpos_diff : 0 < x - a := by linarith
  have hn_nonneg (n : ℕ) : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hpos_n2 (n : ℕ) : 0 < (n : ℝ) + 2 := by nlinarith [hn_nonneg n]
  have hpos_n1 (n : ℕ) : 0 < (n : ℝ) + 1 := by nlinarith [hn_nonneg n]
  refine ⟨fun n ↦ x - (x-a)/((n:ℝ)+2), ?_, ?_⟩
  · intro n
    have hpos_div : 0 < (x-a)/((n:ℝ)+2) := div_pos hpos_diff (hpos_n2 n)
    have hm1 : a < x - (x-a)/((n:ℝ)+2) := by
      have h_one_div : 1/((n:ℝ)+2) < 1 := by
        have htemp := (one_div_lt_one_div (hpos_n2 n) (by norm_num : (0 : ℝ) < 1)).mpr (by
          have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          nlinarith)
        simpa using htemp
      have hdiv_lt : (x-a)/((n:ℝ)+2) < x-a := by
        calc
          (x-a)/((n:ℝ)+2) = (x-a) * (1/((n:ℝ)+2)) := by ring
          _ < (x-a) * 1 := mul_lt_mul_of_pos_left h_one_div hpos_diff
          _ = x-a := by ring
      nlinarith
    have h_b_ge : x - (x-a)/((n:ℝ)+2) ≤ b := by nlinarith
    have h_ne : x - (x-a)/((n:ℝ)+2) ≠ x := by nlinarith
    refine ⟨?_, h_ne⟩
    rw [Set.mem_Ioc]
    exact ⟨hm1, h_b_ge⟩
  · have h_lim_div : Filter.atTop.Tendsto (fun n : ℕ ↦ (x-a)/((n:ℝ)+2)) (nhds 0) := by
      have h_main : Filter.atTop.Tendsto (fun n : ℕ ↦ (x-a)/((n:ℝ)+1)) (nhds 0) := by
        simpa [div_eq_mul_inv] using
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (x-a)
      have h_nonneg : ∀ n : ℕ, 0 ≤ (x-a)/((n:ℝ)+2) := fun n =>
        div_nonneg (by nlinarith) (hpos_n2 n).le
      have h_bound : ∀ n : ℕ, (x-a)/((n:ℝ)+2) ≤ (x-a)/((n:ℝ)+1) := fun n => by
        calc
          (x-a)/((n:ℝ)+2) = (x-a) * (1/((n:ℝ)+2)) := by ring
          _ ≤ (x-a) * (1/((n:ℝ)+1)) :=
            mul_le_mul_of_nonneg_left ((one_div_le_one_div (hpos_n2 n) (hpos_n1 n)).mpr (by nlinarith)) (by nlinarith)
          _ = (x-a)/((n:ℝ)+1) := by ring
      have h0 : Filter.atTop.Tendsto (fun n : ℕ ↦ (0 : ℝ)) (nhds 0) := tendsto_const_nhds
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le h0 h_main h_nonneg h_bound
    simpa using (tendsto_const_nhds.sub h_lim_div)

theorem mem_Ioo_isLimit {a b x:ℝ} (hx: x ∈ Set.Ioo a b) : LimitPt x (.Ioo a b) := by
  simp at hx
  rcases hx with ⟨hx1, hx2⟩
  rw [LimitPt.iff_limit]
  have hpos_diff : 0 < x - a := by linarith
  have hn_nonneg (n : ℕ) : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hpos_n2 (n : ℕ) : 0 < (n : ℝ) + 2 := by nlinarith [hn_nonneg n]
  have hpos_n1 (n : ℕ) : 0 < (n : ℝ) + 1 := by nlinarith [hn_nonneg n]
  refine ⟨fun n ↦ x - (x-a)/((n:ℝ)+2), ?_, ?_⟩
  · intro n
    have hpos_div : 0 < (x-a)/((n:ℝ)+2) := div_pos hpos_diff (hpos_n2 n)
    have hm1 : a < x - (x-a)/((n:ℝ)+2) := by
      have h_one_div : 1/((n:ℝ)+2) < 1 := by
        have htemp := (one_div_lt_one_div (hpos_n2 n) (by norm_num : (0 : ℝ) < 1)).mpr (by
          have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          nlinarith)
        simpa using htemp
      have hdiv_lt : (x-a)/((n:ℝ)+2) < x-a := by
        calc
          (x-a)/((n:ℝ)+2) = (x-a) * (1/((n:ℝ)+2)) := by ring
          _ < (x-a) * 1 := mul_lt_mul_of_pos_left h_one_div hpos_diff
          _ = x-a := by ring
      nlinarith
    have hm2 : x - (x-a)/((n:ℝ)+2) < b := by nlinarith
    have h_ne : x - (x-a)/((n:ℝ)+2) ≠ x := by nlinarith
    refine ⟨?_, h_ne⟩
    rw [Set.mem_Ioo]
    exact ⟨hm1, hm2⟩
  · have h_lim_div : Filter.atTop.Tendsto (fun n : ℕ ↦ (x-a)/((n:ℝ)+2)) (nhds 0) := by
      have h_main : Filter.atTop.Tendsto (fun n : ℕ ↦ (x-a)/((n:ℝ)+1)) (nhds 0) := by
        simpa [div_eq_mul_inv] using
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (x-a)
      have h_nonneg : ∀ n : ℕ, 0 ≤ (x-a)/((n:ℝ)+2) := fun n =>
        div_nonneg (by nlinarith) (hpos_n2 n).le
      have h_bound : ∀ n : ℕ, (x-a)/((n:ℝ)+2) ≤ (x-a)/((n:ℝ)+1) := fun n => by
        calc
          (x-a)/((n:ℝ)+2) = (x-a) * (1/((n:ℝ)+2)) := by ring
          _ ≤ (x-a) * (1/((n:ℝ)+1)) :=
            mul_le_mul_of_nonneg_left ((one_div_le_one_div (hpos_n2 n) (hpos_n1 n)).mpr (by nlinarith)) (by nlinarith)
          _ = (x-a)/((n:ℝ)+1) := by ring
      have h0 : Filter.atTop.Tendsto (fun n : ℕ ↦ (0 : ℝ)) (nhds 0) := tendsto_const_nhds
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le h0 h_main h_nonneg h_bound
    simpa using (tendsto_const_nhds.sub h_lim_div)

theorem mem_Ici_isLimit {a x:ℝ} (hx: x ∈ Set.Ici a) : LimitPt x (.Ici a) := by
  simp at hx
  rw [LimitPt.iff_limit]
  refine ⟨fun n ↦ x + 1/((n:ℝ)+1), ?_, ?_⟩
  · intro n
    have hpos : 0 < 1/((n:ℝ)+1) := by positivity
    have hmem : a ≤ x + 1/((n:ℝ)+1) := by nlinarith
    have h_ne : x + 1/((n:ℝ)+1) ≠ x := by nlinarith
    refine ⟨?_, h_ne⟩
    rw [Set.mem_Ici]
    exact hmem
  · have h_lim : Filter.atTop.Tendsto (fun n : ℕ ↦ 1/((n:ℝ)+1)) (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa using (Filter.Tendsto.const_add x h_lim)

theorem mem_Ioi_isLimit {a x:ℝ} (hx: x ∈ Set.Ioi a) : LimitPt x (.Ioi a) := by
  simp at hx
  rw [LimitPt.iff_limit]
  refine ⟨fun n ↦ x + 1/((n:ℝ)+1), ?_, ?_⟩
  · intro n
    have hpos : 0 < 1/((n:ℝ)+1) := by positivity
    have hmem : a < x + 1/((n:ℝ)+1) := by nlinarith
    have h_ne : x + 1/((n:ℝ)+1) ≠ x := by nlinarith
    refine ⟨?_, h_ne⟩
    rw [Set.mem_Ioi]
    exact hmem
  · have h_lim : Filter.atTop.Tendsto (fun n : ℕ ↦ 1/((n:ℝ)+1)) (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa using (Filter.Tendsto.const_add x h_lim)

theorem mem_Iic_isLimit {a x:ℝ} (hx: x ∈ Set.Iic a) : LimitPt x (.Iic a) := by
  simp at hx
  rw [LimitPt.iff_limit]
  refine ⟨fun n ↦ x - 1/((n:ℝ)+1), ?_, ?_⟩
  · intro n
    have hpos : 0 < 1/((n:ℝ)+1) := by positivity
    have hmem : x - 1/((n:ℝ)+1) ≤ a := by nlinarith
    have h_ne : x - 1/((n:ℝ)+1) ≠ x := by nlinarith
    refine ⟨?_, h_ne⟩
    rw [Set.mem_Iic]
    exact hmem
  · have h_lim : Filter.atTop.Tendsto (fun n : ℕ ↦ 1/((n:ℝ)+1)) (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa using (tendsto_const_nhds.sub h_lim)

theorem mem_Iio_isLimit {a x:ℝ} (hx: x ∈ Set.Iio a) : LimitPt x (.Iio a) := by
  simp at hx
  rw [LimitPt.iff_limit]
  refine ⟨fun n ↦ x - 1/((n:ℝ)+1), ?_, ?_⟩
  · intro n
    have hpos : 0 < 1/((n:ℝ)+1) := by positivity
    have hmem : x - 1/((n:ℝ)+1) < a := by nlinarith
    have h_ne : x - 1/((n:ℝ)+1) ≠ x := by nlinarith
    refine ⟨?_, h_ne⟩
    rw [Set.mem_Iio]
    exact hmem
  · have h_lim : Filter.atTop.Tendsto (fun n : ℕ ↦ 1/((n:ℝ)+1)) (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa using (tendsto_const_nhds.sub h_lim)

theorem mem_R_isLimit {x:ℝ} : LimitPt x (.univ) := by
  rw [LimitPt.iff_limit]
  refine ⟨fun n ↦ x + 1/((n:ℝ)+1), ?_, ?_⟩
  · intro n
    have hpos : 0 < 1/((n:ℝ)+1) := by positivity
    have h_ne : x + 1/((n:ℝ)+1) ≠ x := by nlinarith
    refine ⟨Set.mem_univ _, h_ne⟩
  · have h_lim : Filter.atTop.Tendsto (fun n : ℕ ↦ 1/((n:ℝ)+1)) (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa using (Filter.Tendsto.const_add x h_lim)

/-- Definition 9.1.22.  We use here Mathlib's {name}`Bornology.IsBounded`-/

theorem isBounded_def (X: Set ℝ) : Bornology.IsBounded X ↔ ∃ M > 0, X ⊆ .Icc (-M) M := by
  simp [isBounded_iff_forall_norm_le]
  constructor
  . intro ⟨ C, hC ⟩; use (max C 1)
    refine ⟨ lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_ ⟩
    peel hC with x hx hC; rw [abs_le'] at hC; simp [hC.1]; linarith [le_max_left C 1]
  intro ⟨ M, hM, hXM ⟩; use M; intro x hx; specialize hXM hx; simp_all [abs_le']; linarith [hXM.1]

/-- Example 9.1.23 -/
theorem Icc_bounded (a b:ℝ) : Bornology.IsBounded (.Icc a b) :=
  Metric.isBounded_Icc a b

/-- Example 9.1.23 -/
theorem Ici_unbounded (a: ℝ) : ¬ Bornology.IsBounded (.Ici a) := by
  rw [isBounded_def]
  intro h; rcases h with ⟨M, hMpos, hIci⟩
  set x := max a (M+1) with hx
  have hx_mem : x ∈ Set.Ici a := by
    have : a ≤ max a (M+1) := le_max_left _ _
    simp [x]
  have hx_not : x ∉ Set.Icc (-M) M := by
    intro hmem; rcases hmem with ⟨h1, h2⟩
    have : x ≥ M + 1 := by
      dsimp [x]; exact le_max_right _ _
    nlinarith
  exact hx_not (hIci hx_mem)

/-- Example 9.1.23 -/
theorem N_unbounded : ¬ Bornology.IsBounded ((fun n:ℕ ↦ (n:ℝ)) '' .univ) := by
  rw [isBounded_def]
  intro h; rcases h with ⟨M, hMpos, hN⟩
  rcases exists_nat_gt M with ⟨n, hn⟩
  have hnmem : (n : ℝ) ∈ (fun n:ℕ ↦ (n:ℝ)) '' Set.univ := Set.mem_image_of_mem (fun n : ℕ ↦ (n : ℝ)) (Set.mem_univ n)
  have : (n : ℝ) ∉ Set.Icc (-M) M := by
    intro hmem; rcases hmem with ⟨h1, h2⟩; nlinarith
  exact this (hN hnmem)

/-- Example 9.1.23 -/
theorem Z_unbounded : ¬ Bornology.IsBounded ((fun n:ℤ ↦ (n:ℝ)) '' .univ) := by
  rw [isBounded_def]
  intro h; rcases h with ⟨M, hMpos, hZ⟩
  rcases exists_nat_gt M with ⟨n, hn⟩
  have hnmem : ((n : ℤ) : ℝ) ∈ (fun n:ℤ ↦ (n:ℝ)) '' Set.univ := Set.mem_image_of_mem (fun n : ℤ ↦ (n : ℝ)) (Set.mem_univ (n : ℤ))
  have : ((n : ℤ) : ℝ) ∉ Set.Icc (-M) M := by
    intro hmem
    have hcast : ((n : ℤ) : ℝ) = (n : ℝ) := by simp
    have hmem' := hmem.2
    rw [hcast] at hmem'
    nlinarith
  exact this (hZ hnmem)

/-- Example 9.1.23 -/
theorem Q_unbounded : ¬ Bornology.IsBounded ((fun n:ℚ ↦ (n:ℝ)) '' .univ) := by
  rw [isBounded_def]
  intro h; rcases h with ⟨M, hMpos, hQ⟩
  rcases exists_nat_gt M with ⟨n, hn⟩
  have hnmem : ((n : ℚ) : ℝ) ∈ (fun n:ℚ ↦ (n:ℝ)) '' Set.univ := Set.mem_image_of_mem (fun n : ℚ ↦ (n : ℝ)) (Set.mem_univ (n : ℚ))
  have : ((n : ℚ) : ℝ) ∉ Set.Icc (-M) M := by
    intro hmem
    have hcast : ((n : ℚ) : ℝ) = (n : ℝ) := by simp
    have hmem' := hmem.2
    rw [hcast] at hmem'
    nlinarith
  exact this (hQ hnmem)

/-- Example 9.1.23 -/
theorem R_unbounded : ¬ Bornology.IsBounded (.univ: Set ℝ) := by
  rw [isBounded_def]
  intro h; rcases h with ⟨M, hMpos, hR⟩
  have hM1 : M + 1 ∈ Set.univ := trivial
  have : (M + 1 : ℝ) ∉ Set.Icc (-M) M := by
    intro hmem; rcases hmem with ⟨h1, h2⟩; nlinarith
  exact this (hR hM1)

/-- Theorem 9.1.24 / Exercise 9.1.13 (Heine-Borel theorem for the line)-/
theorem Heine_Borel (X: Set ℝ) :
  IsClosed X ∧ Bornology.IsBounded X ↔ ∀ a : ℕ → ℝ, (∀ n, a n ∈ X) →
  (∃ n : ℕ → ℕ, StrictMono n
    ∧ ∃ L ∈ X, Filter.atTop.Tendsto (fun j ↦ a (n j)) (nhds L)) := by
  constructor
  · rintro ⟨h_closed, h_bounded⟩ a haX
    rcases tendsto_subseq_of_bounded h_bounded haX with ⟨L, hL_closure, φ, hφ_mono, h⟩
    have hLX : L ∈ X := by
      have h_eq : closure X = X := (isClosed_def X).mp h_closed
      rw [h_eq] at hL_closure
      exact hL_closure
    exact ⟨φ, hφ_mono, L, hLX, h⟩
  · intro h
    constructor
    · rw [isClosed_def']
      intro x hx_adh
      rcases (limit_of_AdherentPt X x).mp hx_adh with ⟨a, haX, ha_conv⟩
      rcases h a haX with ⟨n, hn_mono, ⟨L, hLX, hL_conv⟩⟩
      have h_subseq_conv : Filter.atTop.Tendsto (fun j ↦ a (n j)) (nhds x) :=
        ha_conv.comp hn_mono.tendsto_atTop
      have h_eq : x = L := tendsto_nhds_unique (f := fun j ↦ a (n j)) (l := Filter.atTop) (a := x) (b := L) h_subseq_conv hL_conv
      have hxX : x ∈ X := h_eq ▸ hLX
      exact hxX
    · by_contra! h_not_bounded
      have h_not_bounded' : ∀ M > 0, ∃ x ∈ X, x ∉ Set.Icc (-M) M := by
        intro M hMpos
        by_contra! h
        apply h_not_bounded
        rw [isBounded_def]
        refine ⟨M, hMpos, ?_⟩
        intro x hx
        by_contra! hx_not
        exact hx_not (h x hx)
      have h_seq : ∀ n : ℕ, ∃ x ∈ X, |x| > (n : ℝ) := by
        intro n
        have hpos : ((n : ℝ) + 1) > 0 := by
          exact mod_cast (Nat.succ_pos n)
        rcases h_not_bounded' ((n : ℝ) + 1) hpos with ⟨x, hxX, hx_not⟩
        have hx_not' : x < -((n : ℝ) + 1) ∨ x > (n : ℝ) + 1 := by
          by_contra! h
          apply hx_not
          constructor <;> linarith
        refine ⟨x, hxX, ?_⟩
        rcases hx_not' with (hx_lt | hx_gt)
        · have hx_nonpos : x ≤ 0 := by linarith
          rw [abs_of_nonpos hx_nonpos]
          linarith
        · have hx_nonneg : 0 ≤ x := by linarith
          rw [abs_of_nonneg hx_nonneg]
          linarith
      choose a haX ha_abs using h_seq
      rcases h a haX with ⟨n, hn_mono, ⟨L, hLX, hL_conv⟩⟩
      have h_bounded_range : Bornology.IsBounded (Set.range (fun j ↦ a (n j))) :=
        Metric.isBounded_range_of_tendsto _ hL_conv
      rw [isBounded_def] at h_bounded_range
      rcases h_bounded_range with ⟨M, hMpos, hM⟩
      have h_bound : ∀ j, a (n j) ∈ Set.Icc (-M) M :=
        λ j => hM (Set.mem_range_self j)
      rcases exists_nat_gt M with ⟨k, hk⟩
      have hk_le_nk : (k : ℝ) ≤ (n k : ℝ) := by
        exact mod_cast (hn_mono.id_le k)
      have hnk_gt_M : (n k : ℝ) > M := by
        calc
          (n k : ℝ) ≥ (k : ℝ) := hk_le_nk
          _ > M := hk
      have h_bound_k : a (n k) ∈ Set.Icc (-M) M := h_bound k
      rcases h_bound_k with ⟨h_low, h_high⟩
      have h_abs_k_bound : |a (n k)| ≤ M := by
        rw [abs_le]
        exact ⟨h_low, h_high⟩
      have h_abs_k : |a (n k)| > (n k : ℝ) := ha_abs (n k)
      have : |a (n k)| > M := by linarith
      linarith

/-- Exercise 9.1.3 -/
example : ∃ (X Y:Set ℝ), closure (X ∩ Y) ≠ closure X ∩ closure Y := by
  use Set.Ioo 0 1, Set.Ioo 1 2
  have h_int : Set.Ioo (0 : ℝ) 1 ∩ Set.Ioo (1 : ℝ) 2 = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_empty_iff_false, iff_false]
    intro h; rcases h with ⟨⟨h0, h1⟩, ⟨h1', h2⟩⟩; linarith
  calc
    closure (Set.Ioo (0 : ℝ) 1 ∩ Set.Ioo (1 : ℝ) 2) = closure (∅ : Set ℝ) := by rw [h_int]
    _ = ∅ := closure_empty
    _ ≠ {1} := by
      intro h_eq
      have : 1 ∈ ({1} : Set ℝ) := by simp
      rw [← h_eq] at this
      simp at this
    _ = closure (Set.Ioo (0 : ℝ) 1) ∩ closure (Set.Ioo (1 : ℝ) 2) := by
      have h1 : closure (Set.Ioo (0 : ℝ) 1) = Set.Icc (0 : ℝ) 1 := closure_Ioo (by norm_num : (0:ℝ) ≠ 1)
      have h2 : closure (Set.Ioo (1 : ℝ) 2) = Set.Icc (1 : ℝ) 2 := closure_Ioo (by norm_num : (1:ℝ) ≠ 2)
      rw [h1, h2]
      ext x; simp

/-- Exercise 9.1.5 -/
example (X:Set ℝ) : IsClosed (closure X) := by
  rw [isClosed_def, closure_closure]

/-- Exercise 9.1.6 -/
example {X Y:Set ℝ} (hY: IsClosed Y) (hXY: X ⊆ Y) : closure X ⊆ Y := by
  have h_closure_subset : closure X ⊆ closure Y := closure_subset hXY
  have h_closure_eq : closure Y = Y := (isClosed_def Y).mp hY
  rw [h_closure_eq] at h_closure_subset
  exact h_closure_subset

/-- Exercise 9.1.7 -/
example {n:ℕ} (X: Fin n → Set ℝ) (hX: ∀ i, IsClosed (X i)) :
  IsClosed (⋃ i, X i) :=
  isClosed_iUnion_of_finite hX

/-- Exercise 9.1.8 -/
example {I:Type} (X: I → Set ℝ) (hX: ∀ i, IsClosed (X i)) :
  IsClosed (⋂ i, X i) :=
  isClosed_iInter hX

/-- Exercise 9.1.9 -/
example {X:Set ℝ} {x:ℝ} (hx: AdherentPt x X) : LimitPt x X ∨ IsolatedPt x X := by
  by_cases h : LimitPt x X
  · left; exact h
  · right
    unfold LimitPt AdherentPt Real.adherent' at h
    push_neg at h
    rcases h with ⟨ε, hε, h⟩
    have hxX : x ∈ X := by
      have hx' := hx ε hε
      rcases hx' with ⟨y, hyX, hdist⟩
      by_cases hyx : y = x
      · subst hyx; exact hyX
      · exfalso; exact (not_lt.mpr hdist) (h y ⟨hyX, hyx⟩)
    refine ⟨hxX, ε, hε, ?_⟩
    intro y hy
    exact h y hy

/-- Exercise 9.1.9 -/
example {X:Set ℝ} {x:ℝ} : ¬ (LimitPt x X ∧ IsolatedPt x X) := by
  rintro ⟨h_limit, h_isolated⟩
  rcases h_isolated with ⟨hxX, ε, hε, h_isol⟩
  have h_limit' := h_limit ε hε
  dsimp [Real.adherent'] at h_limit'
  rcases h_limit' with ⟨y, hy, hdist⟩
  exact (not_lt.mpr hdist) (h_isol y hy)

/-- Exercise 9.1.10 -/
example {X:Set ℝ} (hX: X ≠ ∅) : Bornology.IsBounded X ↔
  sSup ((fun x:ℝ ↦ (x:EReal)) '' X) < ⊤ ∧
  sInf ((fun x:ℝ ↦ (x:EReal)) '' X) > ⊥ := by
  rw [isBounded_def]
  have h_nonempty_img : ((fun x : ℝ ↦ (x : EReal)) '' X).Nonempty := by
    rcases Set.nonempty_iff_ne_empty.mpr hX with ⟨x, hx⟩
    exact ⟨(x : EReal), x, hx, rfl⟩
  constructor
  · rintro ⟨M, hMpos, hX⟩
    have h_upper : ∀ x ∈ X, x ≤ M := by
      intro x hx
      exact (hX hx).2
    have h_lower : ∀ x ∈ X, -M ≤ x := by
      intro x hx
      linarith [(hX hx).1]
    constructor
    · have h_sup_le : sSup ((fun x : ℝ ↦ (x : EReal)) '' X) ≤ (M : EReal) := by
        apply csSup_le h_nonempty_img
        rintro y ⟨x, hx, rfl⟩
        simpa using h_upper x hx
      have h_top : (M : EReal) < ⊤ := by simp
      exact h_sup_le.trans_lt h_top
    · have h_inf_ge : sInf ((fun x : ℝ ↦ (x : EReal)) '' X) ≥ (-M : EReal) := by
        apply le_csInf h_nonempty_img
        rintro y ⟨x, hx, rfl⟩
        have h : (-M : EReal) ≤ (x : EReal) := by exact_mod_cast h_lower x hx
        simpa using h
      have h_bot : (⊥ : EReal) < (-M : EReal) := EReal.bot_lt_coe (-M)
      exact h_bot.trans_le h_inf_ge
  · intro ⟨h_sup_lt_top, h_inf_gt_bot⟩
    have h_bdd_above : BddAbove X := by
      by_contra! h_not
      have h_sup_eq_top : sSup ((fun x : ℝ ↦ (x : EReal)) '' X) = ⊤ := by
        apply sSup_eq_top.mpr
        intro a ha
        rcases (EReal.lt_iff_exists_real_btwn.mp ha) with ⟨r, hr, hr'⟩
        have h_not_bdd : ∀ M : ℝ, ∃ x ∈ X, x > M := by
          simpa [bddAbove_def] using h_not
        rcases h_not_bdd r with ⟨x, hx, hx_gt⟩
        refine ⟨(x : EReal), ?_, ?_⟩
        · rw [Set.mem_image]
          exact ⟨x, hx, rfl⟩
        · have : (r : EReal) < (x : EReal) := by exact_mod_cast hx_gt
          exact hr.trans this
      rw [h_sup_eq_top] at h_sup_lt_top
      exact lt_irrefl ⊤ h_sup_lt_top
    have h_bdd_below : BddBelow X := by
      by_contra! h_not
      have h_inf_eq_bot : sInf ((fun x : ℝ ↦ (x : EReal)) '' X) = ⊥ := by
        apply sInf_eq_bot.mpr
        intro b hb
        rcases (EReal.lt_iff_exists_real_btwn.mp hb) with ⟨r, hr, hr'⟩
        have h_not_bdd : ∀ M : ℝ, ∃ x ∈ X, x < M := by
          simpa [bddBelow_def] using h_not
        rcases h_not_bdd r with ⟨x, hx, hx_lt⟩
        refine ⟨(x : EReal), ?_, ?_⟩
        · rw [Set.mem_image]
          exact ⟨x, hx, rfl⟩
        · have h_x_lt_r : (x : EReal) < (r : EReal) := by exact_mod_cast hx_lt
          exact h_x_lt_r.trans hr'
      rw [h_inf_eq_bot] at h_inf_gt_bot
      exact lt_irrefl ⊥ h_inf_gt_bot
    rcases h_bdd_above with ⟨M_u, hM_u⟩
    rcases h_bdd_below with ⟨M_l, hM_l⟩
    set M := max (max 1 (|M_u|)) (|M_l|) with hM_def
    have hMpos : 0 < M := by
      have : (0:ℝ) < 1 := by norm_num
      have hpos_max1 : 0 < max 1 (|M_u|) :=
        lt_of_lt_of_le (by norm_num) (le_max_left _ _)
      exact lt_max_of_lt_left hpos_max1
    refine ⟨M, hMpos, ?_⟩
    intro x hx
    have hx_le_up : x ≤ M_u := hM_u hx
    have hx_ge_low : M_l ≤ x := hM_l hx
    have hM_u_le : M_u ≤ M := by
      have : |M_u| ≤ max 1 (|M_u|) := le_max_right _ _
      have : max 1 (|M_u|) ≤ M := le_max_left _ _
      have hM_u_abs : M_u ≤ |M_u| := le_abs_self M_u
      nlinarith
    have hM_l_ge : -M ≤ M_l := by
      have h_abs_le : |M_l| ≤ M := le_max_right _ _
      have h_neg_abs : -|M_l| ≤ M_l := by
        have : -M_l ≤ |M_l| := by
          simpa using le_abs_self (-M_l)
        nlinarith
      nlinarith
    constructor <;> nlinarith

/-- Exercise 9.1.11 -/
example {X:Set ℝ} (hX: Bornology.IsBounded X) : Bornology.IsBounded (closure X) :=
  Metric.isBounded_closure_of_isBounded hX

/-- Exercise 9.1.12.  As a followup: prove or disprove this exercise with {lean}`[Fintype I]` removed. -/
example {I:Type} [Fintype I] (X: I → Set ℝ) (hX: ∀ i, Bornology.IsBounded (X i)) :
  Bornology.IsBounded (⋃ i, X i) :=
  (Bornology.isBounded_iUnion (ι := I) (s := X)).mpr hX

/-- Exercise 9.1.14 -/
example (I: Finset ℝ) : IsClosed (I:Set ℝ) ∧ Bornology.IsBounded (I:Set ℝ) := by
  have hfinite : Set.Finite (I : Set ℝ) := Finset.finite_toSet _
  constructor
  · exact hfinite.isClosed
  · exact hfinite.isBounded

/-- Exercise 9.1.15 -/
example {E:Set ℝ} (hE: Bornology.IsBounded E) (hnon: E.Nonempty): AdherentPt (sSup E) E ∧ AdherentPt (sSup E) Eᶜ := by
  rcases ((isBounded_def E).mp hE) with ⟨M, hMpos, hE⟩
  have h_bdd_above : BddAbove E := by
    refine ⟨M, ?_⟩
    intro x hx
    exact (hE hx).2
  have h_bdd_below : BddBelow E := by
    refine ⟨-M, ?_⟩
    intro x hx
    linarith [(hE hx).1]
  constructor
  · intro ε hε
    have h_sup_lt : sSup E - ε < sSup E := by nlinarith
    rcases exists_lt_of_lt_csSup hnon h_sup_lt with ⟨y, hyE, hy⟩
    use y
    constructor
    · exact hyE
    · have hy_le_sup : y ≤ sSup E := le_csSup h_bdd_above hyE
      have : |sSup E - y| = sSup E - y :=
        abs_of_nonneg (sub_nonneg.mpr hy_le_sup)
      rw [this]
      nlinarith
  · intro ε hε
    use sSup E + ε / 2
    constructor
    · intro h_mem
      have : sSup E + ε / 2 ≤ sSup E := le_csSup h_bdd_above h_mem
      nlinarith
    · have : |sSup E - (sSup E + ε / 2)| = ε / 2 := by
        simp [abs_of_pos (by nlinarith : (0 : ℝ) < ε / 2)]
      rw [this]
      nlinarith

end Chapter9
