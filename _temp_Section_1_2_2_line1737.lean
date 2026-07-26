import Analysis.MeasureTheory.Section_1_2_1
import Analysis.MeasureTheory.Section_1_2_2

/-- A nonempty countable closed subset of ℝ has an isolated point (Baire category theorem). -/
lemma exists_isolated_point {K : Set ℝ} (hcl : IsClosed K) (hct : K.Countable)
    (hne : K.Nonempty) :
    ∃ x ∈ K, ∃ ε > 0, ∀ y ∈ K, dist x y < ε → y = x := by
  haveI : CompleteSpace ↥K := hcl.isComplete.completeSpace_coe
  haveI : Nonempty ↥K := hne.to_subtype
  haveI : Countable ↥K := hct
  by_contra hcon
  push_neg at hcon
  have hint : ∀ x : ↥K, interior {x} = ∅ := by
    intro x
    by_contra hne'
    obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr hne'
    have hzx : z = x := Set.mem_singleton_iff.mp (interior_subset hz)
    rw [hzx] at hz
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hz
    obtain ⟨y, hyK, hdist, hyne⟩ := hcon x.val x.prop ε hε
    have hmem : (⟨y, hyK⟩ : ↥K) ∈ Metric.ball x ε := by
      rw [Metric.mem_ball, Subtype.dist_eq, dist_comm]; exact hdist
    have heq : (⟨y, hyK⟩ : ↥K) = x :=
      Set.mem_singleton_iff.mp (interior_subset (hball hmem))
    exact hyne (congrArg Subtype.val heq)
  obtain ⟨g, hg⟩ := exists_surjective_nat ↥K
  have hD : Dense (⋂ n, ({g n}ᶜ : Set ↥K)) :=
    BaireSpace.baire_property _ (fun _ ↦ isOpen_compl_singleton)
      (fun n ↦ interior_eq_empty_iff_dense_compl.mp (hint (g n)))
  have hempty : (⋂ n, ({g n}ᶜ : Set ↥K)) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    obtain ⟨n, hn⟩ := hg x
    exact (Set.mem_iInter.mp hx n) (Set.mem_singleton_iff.mpr hn.symm)
  rw [hempty] at hD
  exact Set.not_nonempty_empty hD.nonempty

/-- Exercise 1.2.10 (\[0,1) is not the countable union of pairwise disjoint closed intervals) -/
example : ¬ ∃ (I: ℕ → BoundedInterval), (∀ n, IsClosed (I n).toSet) ∧ (Set.univ.PairwiseDisjoint (fun n ↦ (I n).toSet) ) ∧ (⋃ n, (I n).toSet = Set.Ico 0 1) := by
  rintro ⟨I, hcl, hdisj, hcov⟩
  -- Each interval is of the form `Icc a b` (possibly empty).
  have key : ∀ n, ∃ a b, (I n).toSet = Set.Icc a b := by
    intro n
    rcases closed_eq_Icc_or_empty (hcl n) with ⟨a, b, h⟩ | h
    · exact ⟨a, b, by rw [h]; rfl⟩
    · exact ⟨1, 0, by rw [h]; exact (Set.Icc_eq_empty (by norm_num)).symm⟩
  choose a b hab using key
  have hcov' : ⋃ n, Set.Icc (a n) (b n) = Set.Ico 0 1 := by
    simp_rw [← hab]; exact hcov
  have hsub : ∀ n, Set.Icc (a n) (b n) ⊆ Set.Ico 0 1 := by
    intro n
    have h1 : (I n).toSet ⊆ Set.Ico 0 1 := by
      rw [← hcov]
      exact Set.subset_iUnion (fun n ↦ (I n).toSet) n
    rwa [hab n] at h1
  have hIoo_sub : ∀ n, Set.Ioo (a n) (b n) ⊆ Set.Ico 0 1 :=
    fun n ↦ Set.Ioo_subset_Icc_self.trans (hsub n)
  have hdj : ∀ m n, m ≠ n → Disjoint (Set.Icc (a m) (b m)) (Set.Icc (a n) (b n)) := by
    intro m n hmn
    have h := hdisj (Set.mem_univ m) (Set.mem_univ n) hmn
    change Disjoint (I m).toSet (I n).toSet at h
    rwa [hab m, hab n] at h
  -- K = [0,1] with all open interiors removed: a countable closed set of endpoints.
  set K : Set ℝ := Set.Icc 0 1 \ ⋃ n, Set.Ioo (a n) (b n) with hKdef
  have hKcl : IsClosed K := IsClosed.sdiff isClosed_Icc (isOpen_iUnion fun n ↦ isOpen_Ioo)
  have hKct : K.Countable := by
    have hbig : ({1} ∪ ⋃ n, ({a n} ∪ {b n} : Set ℝ)).Countable := by
      apply Set.Countable.union (Set.countable_singleton 1)
      apply Set.countable_iUnion
      intro n
      exact (Set.countable_singleton _).union (Set.countable_singleton _)
    apply Set.Countable.mono ?_ hbig
    intro x hx
    rw [hKdef] at hx
    obtain ⟨hx01, hxni⟩ := (Set.mem_diff x).mp hx
    by_cases h1 : x = 1
    · exact Set.mem_union_left _ (Set.mem_singleton_iff.mpr h1)
    · have hxI : x ∈ Set.Ico 0 1 := Set.mem_Ico.mpr ⟨hx01.1, lt_of_le_of_ne hx01.2 h1⟩
      rw [← hcov'] at hxI
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hxI
      have hxi : x ∉ Set.Ioo (a n) (b n) := fun h ↦ hxni (Set.mem_iUnion.mpr ⟨n, h⟩)
      rw [Set.mem_Ioo, not_and] at hxi
      refine Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨n, ?_⟩)
      rcases lt_or_eq_of_le (Set.mem_Icc.mp hn).1 with hlt | heq
      · exact Set.mem_union_right _
          (Set.mem_singleton_iff.mpr (le_antisymm (Set.mem_Icc.mp hn).2 (not_lt.mp (hxi hlt))))
      · exact Set.mem_union_left _ (Set.mem_singleton_iff.mpr heq.symm)
  have hKne : K.Nonempty := ⟨1, by
    refine (Set.mem_diff 1).mpr ⟨Set.mem_Icc.mpr ⟨zero_le_one, le_refl 1⟩, ?_⟩
    rw [Set.mem_iUnion]
    push_neg
    intro n hn
    exact lt_irrefl 1 (Set.mem_Ico.mp (hIoo_sub n hn)).2⟩
  have haK : ∀ n, a n ≤ b n → a n ∈ K := by
    intro n hn
    have haI : a n ∈ Set.Ico 0 1 := hsub n (Set.left_mem_Icc.mpr hn)
    refine (Set.mem_diff _).mpr ⟨Set.mem_Icc.mpr ⟨haI.1, le_of_lt haI.2⟩, ?_⟩
    rw [Set.mem_iUnion]
    push_neg
    intro m hm
    by_cases hmn : m = n
    · subst hmn
      exact lt_irrefl _ (Set.mem_Ioo.mp hm).1
    · exact Set.disjoint_left.mp (hdj m n hmn) (Set.Ioo_subset_Icc_self hm)
        (Set.left_mem_Icc.mpr hn)
  have hbK : ∀ n, a n ≤ b n → b n ∈ K := by
    intro n hn
    have hbI : b n ∈ Set.Ico 0 1 := hsub n (Set.right_mem_Icc.mpr hn)
    refine (Set.mem_diff _).mpr ⟨Set.mem_Icc.mpr ⟨hbI.1, le_of_lt hbI.2⟩, ?_⟩
    rw [Set.mem_iUnion]
    push_neg
    intro m hm
    by_cases hmn : m = n
    · subst hmn
      exact lt_irrefl _ (Set.mem_Ioo.mp hm).2
    · exact Set.disjoint_left.mp (hdj m n hmn) (Set.Ioo_subset_Icc_self hm)
        (Set.right_mem_Icc.mpr hn)
  -- A positive isolated point of K leads to a contradiction.
  have hcontra : ∀ x ∈ K, 0 < x → ∀ ε > 0, (∀ y ∈ K, dist x y < ε → y = x) → False := by
    intro x hxK hx0 ε hε hiso
    have hx1 : x ≤ 1 := ((Set.mem_diff x).mp hxK).1.2
    rcases lt_or_eq_of_le hx1 with hxlt | hxeq
    · -- x < 1: x is an endpoint of some interval
      have hxI : x ∈ Set.Ico 0 1 := Set.mem_Ico.mpr ⟨hx0.le, hxlt⟩
      rw [← hcov'] at hxI
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hxI
      have hxni : x ∉ Set.Ioo (a n) (b n) :=
        fun h ↦ ((Set.mem_diff x).mp hxK).2 (Set.mem_iUnion.mpr ⟨n, h⟩)
      rw [Set.mem_Ioo, not_and] at hxni
      rcases lt_or_eq_of_le (Set.mem_Icc.mp hn).1 with hlt | heq
      · -- x = b n, look just to the right
        have hxbn : x = b n := le_antisymm (Set.mem_Icc.mp hn).2 (not_lt.mp (hxni hlt))
        have h1x : 0 < 1 - x := by linarith
        have hδpos : 0 < min ε (1 - x) / 2 := by
          have := lt_min hε h1x; linarith
        have hy : x + min ε (1 - x) / 2 ∈ Set.Ico 0 1 := by
          refine Set.mem_Ico.mpr ⟨by linarith [hx0], ?_⟩
          have h2 : min ε (1 - x) ≤ 1 - x := min_le_right _ _
          linarith
        rw [← hcov'] at hy
        obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hy
        have habm : a m ≤ b m := le_trans (Set.mem_Icc.mp hm).1 (Set.mem_Icc.mp hm).2
        have hxam : x < a m := by
          by_contra hle
          push_neg at hle
          have hxmem : x ∈ Set.Icc (a m) (b m) :=
            ⟨hle, le_trans (by have h3 := le_min hε.le h1x.le; linarith) (Set.mem_Icc.mp hm).2⟩
          by_cases hmn : m = n
          · subst hmn
            linarith [(Set.mem_Icc.mp hm).2]
          · exact Set.disjoint_left.mp (hdj m n hmn) hxmem hn
        have hdist : dist x (a m) < ε := by
          rw [Real.dist_eq, abs_of_neg (by linarith : x - a m < 0)]
          have h2 : min ε (1 - x) ≤ ε := min_le_left _ _
          linarith [(Set.mem_Icc.mp hm).1]
        exact (ne_of_gt hxam) (hiso (a m) (haK m habm) hdist)
      · -- x = a n, look just to the left
        have hxan : x = a n := heq.symm
        have hδpos : 0 < min ε x / 2 := by
          have := lt_min hε hx0; linarith
        have hy : x - min ε x / 2 ∈ Set.Ico 0 1 := by
          refine Set.mem_Ico.mpr ⟨?_, by linarith⟩
          have h2 : min ε x ≤ x := min_le_right _ _
          linarith [hx0.le]
        rw [← hcov'] at hy
        obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hy
        have habm : a m ≤ b m := le_trans (Set.mem_Icc.mp hm).1 (Set.mem_Icc.mp hm).2
        have hbmx : b m < x := by
          by_contra hge
          push_neg at hge
          have hxmem : x ∈ Set.Icc (a m) (b m) :=
            ⟨le_trans (Set.mem_Icc.mp hm).1 (by linarith), hge⟩
          by_cases hmn : m = n
          · subst hmn
            linarith [(Set.mem_Icc.mp hm).1]
          · exact Set.disjoint_left.mp (hdj m n hmn) hxmem hn
        have hdist : dist x (b m) < ε := by
          rw [Real.dist_eq, abs_of_pos (by linarith : 0 < x - b m)]
          have h2 : min ε x ≤ ε := min_le_left _ _
          linarith [(Set.mem_Icc.mp hm).2]
        exact (ne_of_lt hbmx) (hiso (b m) (hbK m habm) hdist)
    · -- x = 1, look just to the left
      subst hxeq
      have hδpos : 0 < min ε 1 / 2 := by
        have := lt_min hε one_pos; linarith
      have hy : 1 - min ε 1 / 2 ∈ Set.Ico 0 1 := by
        refine Set.mem_Ico.mpr ⟨?_, by linarith⟩
        have h2 : min ε 1 ≤ 1 := min_le_right _ _
        linarith
      rw [← hcov'] at hy
      obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hy
      have habm : a m ≤ b m := le_trans (Set.mem_Icc.mp hm).1 (Set.mem_Icc.mp hm).2
      have hbm1 : b m < 1 := (Set.mem_Ico.mp (hsub m (Set.right_mem_Icc.mpr habm))).2
      have hdist : dist 1 (b m) < ε := by
        rw [Real.dist_eq, abs_of_pos (by linarith : (0:ℝ) < 1 - b m)]
        have h2 : min ε 1 ≤ ε := min_le_left _ _
        linarith [(Set.mem_Icc.mp hm).2]
      exact (ne_of_lt hbm1) (hiso (b m) (hbK m habm) hdist)
  -- Apply Baire: K has an isolated point.
  obtain ⟨x, hxK, ε, hε, hiso⟩ := exists_isolated_point hKcl hKct hKne
  have hx01 : 0 ≤ x ∧ x ≤ 1 := Set.mem_Icc.mp ((Set.mem_diff x).mp hxK).1
  by_cases hx0 : x = 0
  · -- x = 0: then K stays away from 0, and we zoom in on [ε₁, 1].
    subst hx0
    have h0I : (0:ℝ) ∈ Set.Ico 0 1 := Set.left_mem_Ico.mpr zero_lt_one
    rw [← hcov'] at h0I
    obtain ⟨n₀, hn₀⟩ := Set.mem_iUnion.mp h0I
    have habn₀ : a n₀ ≤ b n₀ := le_trans (Set.mem_Icc.mp hn₀).1 (Set.mem_Icc.mp hn₀).2
    have han₀ : a n₀ = 0 := by
      have h1 : a n₀ ≤ 0 := (Set.mem_Icc.mp hn₀).1
      have h2 : 0 ≤ a n₀ := (Set.mem_Ico.mp (hsub n₀ (Set.left_mem_Icc.mpr habn₀))).1
      linarith
    set ε₁ := min ε 1 / 2 with hε₁def
    have hε₁pos : 0 < ε₁ := by
      rw [hε₁def]; have := lt_min hε one_pos; linarith
    have hbn₀ : ε₁ ≤ b n₀ := by
      have hy : ε₁ ∈ Set.Ico 0 1 := by
        refine Set.mem_Ico.mpr ⟨le_of_lt hε₁pos, ?_⟩
        rw [hε₁def]; have h2 : min ε 1 ≤ 1 := min_le_right _ _
        linarith
      rw [← hcov'] at hy
      obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hy
      have habm : a m ≤ b m := le_trans (Set.mem_Icc.mp hm).1 (Set.mem_Icc.mp hm).2
      have ham0 : 0 ≤ a m := (Set.mem_Ico.mp (hsub m (Set.left_mem_Icc.mpr habm))).1
      have hdist : dist 0 (a m) < ε := by
        rw [Real.dist_eq, abs_of_nonpos (by linarith : (0:ℝ) - a m ≤ 0)]
        rw [hε₁def] at hm
        have h2 : min ε 1 ≤ ε := min_le_left _ _
        linarith [(Set.mem_Icc.mp hm).1]
      have ham : a m = 0 := hiso (a m) (haK m habm) hdist
      have hmn : m = n₀ := by
        by_contra hmn
        have h0mem : (0:ℝ) ∈ Set.Icc (a m) (b m) := by
          rw [ham]
          exact ⟨le_refl 0, le_of_lt (lt_of_lt_of_le hε₁pos (Set.mem_Icc.mp hm).2)⟩
        exact Set.disjoint_left.mp (hdj m n₀ hmn) h0mem hn₀
      subst hmn
      exact (Set.mem_Icc.mp hm).2
    have hK1cl : IsClosed (K ∩ Set.Icc ε₁ 1) := hKcl.inter isClosed_Icc
    have hK1ct : (K ∩ Set.Icc ε₁ 1).Countable := hKct.mono Set.inter_subset_left
    have hK1ne : (K ∩ Set.Icc ε₁ 1).Nonempty := by
      have hbn1 : b n₀ < 1 := (Set.mem_Ico.mp (hsub n₀ (Set.right_mem_Icc.mpr habn₀))).2
      exact ⟨b n₀, hbK n₀ habn₀, hbn₀, le_of_lt hbn1⟩
    obtain ⟨x', hx'K1, ε', hε', hiso'⟩ := exists_isolated_point hK1cl hK1ct hK1ne
    have hx'K : x' ∈ K := hx'K1.1
    have hx'ge : ε₁ ≤ x' := (Set.mem_Icc.mp hx'K1.2).1
    have hx'pos : 0 < x' := lt_of_lt_of_le hε₁pos hx'ge
    apply hcontra x' hx'K hx'pos (min ε' ε₁) (lt_min hε' hε₁pos)
    intro y hyK hdist
    have hy0' : 0 ≤ y := (Set.mem_Icc.mp ((Set.mem_diff y).mp hyK).1).1
    have hy1' : y ≤ 1 := (Set.mem_Icc.mp ((Set.mem_diff y).mp hyK).1).2
    have hyge : ε₁ ≤ y := by
      by_cases hy0 : y = 0
      · subst hy0
        rw [Real.dist_eq, sub_zero, abs_of_pos hx'pos] at hdist
        exfalso
        linarith [hx'ge, min_le_right ε' ε₁]
      · have hypos : 0 < y := lt_of_le_of_ne hy0' (Ne.symm hy0)
        have h2 : ε ≤ dist 0 y := by
          by_contra hlt
          push_neg at hlt
          exact hy0 (hiso y hyK hlt)
        rw [Real.dist_eq, abs_of_nonpos (by linarith : (0:ℝ) - y ≤ 0)] at h2
        rw [hε₁def]
        have h3 : min ε 1 ≤ ε := min_le_left _ _
        linarith
    exact hiso' y ⟨hyK, hyge, hy1'⟩ (lt_of_lt_of_le hdist (min_le_left _ _))
  · exact hcontra x hxK (lt_of_le_of_ne hx01.1 (Ne.symm hx0)) ε hε hiso
