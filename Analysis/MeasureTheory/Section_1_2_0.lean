import Analysis.MeasureTheory.Section_1_1_3
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.Set.Countable
import Mathlib.Topology.Instances.Irrational
/-!
# Introduction to Measure Theory, Section 1.2: Lebesgue measure

A companion to (the introduction to) Section 1.2 of the book "An introduction to Measure Theory".

-/

open BoundedInterval

/-- Exercise 1.2.1 (countable union) -/
lemma exercise_1_2_1_union :
    ∃ E: ℕ → Set ℝ, (∀ n, Bornology.IsBounded (E n)) ∧
      (∀ n, JordanMeasurable (Real.equiv_EuclideanSpace' '' (E n))) ∧
      (∀ n, E n ⊆ Set.Icc 0 1) ∧
      ¬ JordanMeasurable (⋃ n, Real.equiv_EuclideanSpace' '' (E n)) := by
  -- Strategy: Let E_n = {q_n} where q_n is the nth rational in [0,1]
  -- Each singleton is Jordan measurable with measure 0
  -- But the union is all rationals in [0,1], which is NOT Jordan measurable

  -- Get an enumeration of rationals in [0,1]
  have h_countable : (Set.Icc (0:ℚ) 1).Countable := Set.countable_coe_iff.mp inferInstance
  have h_nonempty : (Set.Icc (0:ℚ) 1).Nonempty := ⟨0, by simp⟩
  obtain ⟨q, hq_surj⟩ := h_countable.exists_surjective h_nonempty

  -- Define E_n = {q_n} (singleton containing the nth rational)
  let E : ℕ → Set ℝ := fun n => {((q n).val : ℝ)}

  use E

  constructor
  -- Part 1: Each E_n is bounded (singleton sets are trivially bounded)
  · intro n
    apply Set.Finite.isBounded
    exact Set.finite_singleton _

  constructor
  -- Part 2: Each E_n is Jordan measurable (singletons have measure 0)
  · intro n
    -- A singleton {x} in ℝ maps to a degenerate box in EuclideanSpace' 1
    -- Specifically, Real.equiv_EuclideanSpace' '' {x} = Icc x x (as a 1D box)
    -- Boxes are elementary, and elementary sets are Jordan measurable
    let x := ((q n).val : ℝ)
    have h_singleton_eq : Real.equiv_EuclideanSpace' '' {x} = (BoundedInterval.Icc x x : Box 1).toSet := by
      rw [BoundedInterval.coe_of_box]
      simp [BoundedInterval.set_Icc]
    rw [h_singleton_eq]
    exact IsElementary.jordanMeasurable (IsElementary.box _)

  constructor
  -- Part 3: Each E_n is contained in [0,1]
  · intro n x hx
    simp [E] at hx
    rcases hx with rfl
    rcases (q n).property with ⟨hq0, hq1⟩
    exact ⟨by exact_mod_cast hq0, by exact_mod_cast hq1⟩

  -- Part 4: The union ⋃_n E_n = rationals in [0,1], which is NOT Jordan measurable
  · intro hJM
    -- The union equals the set of all rationals in [0,1]
    have h_union_eq_rats : (⋃ n, E n) = Set.range (fun r : Set.Icc (0:ℚ) 1 => (r.val : ℝ)) := by
      ext x
      simp only [E, Set.mem_iUnion, Set.mem_singleton_iff, Set.mem_range]
      constructor
      · intro ⟨n, hn⟩
        use q n
        exact hn.symm
      · intro ⟨r, hr⟩
        obtain ⟨n, hn⟩ := hq_surj r
        use n
        rw [hn]
        exact hr.symm

    -- The image of the union under Real.equiv_EuclideanSpace' is the image of rationals
    have hJM' : JordanMeasurable (Real.equiv_EuclideanSpace' '' (⋃ n, E n)) := by
      have : (⋃ n, Real.equiv_EuclideanSpace' '' E n) = Real.equiv_EuclideanSpace' '' (⋃ n, E n) := by
        exact Set.image_iUnion.symm
      rw [← this]
      exact hJM

    -- Let Q = rationals in [0,1]
    let Q := Set.range (fun r : Set.Icc (0:ℚ) 1 => (r.val : ℝ))

    -- Show Q is bounded
    have hQ_bounded : Bornology.IsBounded Q := by
      apply Bornology.IsBounded.subset (Metric.isBounded_Icc (a := 0) (b := 1))
      intro x hx
      obtain ⟨r, hr⟩ := hx
      rw [← hr]
      simp
      have : r.val ∈ Set.Icc (0:ℚ) 1 := r.property
      constructor
      · exact_mod_cast this.1
      · exact_mod_cast this.2

    -- Rewrite hJM' in terms of Q
    rw [h_union_eq_rats] at hJM'

    -- Use Exercise 1.1.18(1): Jordan_outer_measure(closure(Q)) = Jordan_outer_measure(Q)
    have h_outer_eq : Jordan_outer_measure (closure (Real.equiv_EuclideanSpace' '' Q)) =
                      Jordan_outer_measure (Real.equiv_EuclideanSpace' '' Q) := by
      apply JordanMeasurable.outer_measure_of_closure
      have : Bornology.IsBounded (Real.equiv_EuclideanSpace' '' Q) := by
        -- Q ⊆ [0,1] is bounded, so its image under the homeomorphism is bounded
        -- Use that Q is bounded: ∃ M, ∀ x y ∈ Q, dist x y ≤ M
        obtain ⟨c, hc⟩ := Metric.isBounded_iff_subset_ball 0 |>.mp hQ_bounded
        -- Show image is bounded by showing it's in a ball
        rw [Metric.isBounded_iff_subset_ball 0]
        use c
        intro v hv
        obtain ⟨x, hx, rfl⟩ := hv
        -- Show Real.equiv_EuclideanSpace' x ∈ Metric.ball 0 c
        -- Since ‖Real.equiv_EuclideanSpace' x‖ = |x| and x ∈ Metric.ball 0 c
        have hx_ball : x ∈ Metric.ball 0 c := hc hx
        rw [Metric.mem_ball, dist_zero_right] at hx_ball
        rw [Metric.mem_ball, dist_zero_right]
        -- ‖Real.equiv_EuclideanSpace' x‖ = |x|
        have h_norm_eq : ‖Real.equiv_EuclideanSpace' x‖ = |x| := by
          simp [Real.equiv_EuclideanSpace', EuclideanSpace'.equiv_Real]
          rw [PiLp.norm_eq_of_L2]
          simp
          exact Real.sqrt_sq_eq_abs x
        rw [h_norm_eq]
        exact hx_ball
      exact this

    -- Closure of rationals in [0,1] is [0,1] (rationals are dense)
    have h_closure_Q : closure Q = Set.Icc 0 1 := by
      -- Rationals are dense in [0,1]
      -- First show Q ⊆ [0,1]
      have hQ_subset : Q ⊆ Set.Icc 0 1 := by
        intro y hy
        simp [Q] at hy
        obtain ⟨r, ⟨h_bounds, h_eq⟩⟩ := hy
        rw [← h_eq]
        constructor
        · exact_mod_cast h_bounds.1
        · exact_mod_cast h_bounds.2
      -- Show closure Q ⊆ [0,1] (since [0,1] is closed)
      have h_closure_subset : closure Q ⊆ Set.Icc 0 1 :=
        closure_minimal hQ_subset isClosed_Icc
      -- Show [0,1] ⊆ closure Q (using density of rationals)
      have h_subset_closure : Set.Icc 0 1 ⊆ closure Q := by
        -- Q is the set of rationals in [0,1]
        -- Since rationals are dense in ℝ, Q is dense in [0,1]
        -- Therefore closure Q ⊇ [0,1]
        intro x hx
        -- Use DenseRange for rationals
        have h_dense : ∀ ε > 0, ∃ q : ℚ, |(q:ℝ) - x| < ε ∧ (q:ℝ) ∈ Set.Icc 0 1 := by
          intro ε hε
          -- Find a rational within ε of x using density
          have := Rat.denseRange_cast.exists_dist_lt x hε
          obtain ⟨q, hq⟩ := this
          -- Check if q ∈ [0,1]
          by_cases hq_in : (q:ℝ) ∈ Set.Icc 0 1
          · use q
            have : |(q:ℝ) - x| < ε := by
              rw [← Real.dist_eq, dist_comm]
              exact hq
            exact ⟨this, hq_in⟩
          · -- If q ∉ [0,1], need to find a rational in [0,1] close to x
            -- Recursively use density in a smaller neighborhood that stays within [0,1]
            -- Define the interval [a, b] = [max(0, x-ε/2), min(1, x+ε/2)] ⊆ [0,1]
            let a := max (0 : ℝ) (x - ε / 2)
            let b := min (1 : ℝ) (x + ε / 2)
            have ha : 0 ≤ a := le_max_left _ _
            have hb : b ≤ 1 := min_le_left _ _
            have hax : a ≤ x := by
              simp only [a]
              exact max_le (hx.1) (by linarith)
            have hxb : x ≤ b := by
              simp only [b]
              exact le_min (hx.2) (by linarith)
            have hab : a < b := by
              simp only [a, b]
              apply max_lt
              · -- 0 < min 1 (x + ε / 2)
                apply lt_min
                · norm_num
                · linarith [hx.1, hε]
              · apply lt_min
                · linarith [hx.2]
                · linarith
            -- Find a rational in the open interval (a, b) using density
            have : ∃ r : ℚ, a < (r : ℝ) ∧ (r : ℝ) < b := by
              apply exists_rat_btwn
              exact hab
            obtain ⟨r, har, hrb⟩ := this
            use r
            constructor
            · -- |r - x| < ε
              have : (r : ℝ) ∈ Set.Ioo a b := ⟨har, hrb⟩
              simp [a, b] at this
              rw [abs_sub_lt_iff]
              constructor <;> linarith
            · -- r ∈ [0, 1]
              rw [Set.mem_Icc]
              constructor <;> linarith [har, ha, hrb, hb]
        -- Use h_dense to show x ∈ closure Q
        apply Metric.mem_closure_iff.mpr
        intro ε hε
        obtain ⟨q, hq_dist, hq_in⟩ := h_dense ε hε
        use (q:ℝ)
        constructor
        · -- Show (q:ℝ) ∈ Q (first subgoal from "use")
          simp only [Q, Set.mem_range]
          have hq_bounds : q ∈ Set.Icc (0:ℚ) 1 := by
            rw [Set.mem_Icc] at hq_in ⊢
            exact ⟨by exact_mod_cast hq_in.1, by exact_mod_cast hq_in.2⟩
          use ⟨q, hq_bounds⟩
        · -- Show dist (q:ℝ) x < ε (second subgoal from "use")
          rw [Real.dist_eq]
          rw [abs_sub_comm] at hq_dist
          exact hq_dist
      exact Set.Subset.antisymm h_closure_subset h_subset_closure

    -- Use Real.equiv_EuclideanSpace' commutes with closure
    have h_image_closure : Real.equiv_EuclideanSpace' '' closure Q =
                           closure (Real.equiv_EuclideanSpace' '' Q) := by
      -- Real.equiv_EuclideanSpace' is a homeomorphism (continuous bijection with continuous inverse)
      -- Homeomorphisms preserve closure: f(closure A) = closure(f(A))
      -- To prove this formally would require:
      -- 1. Showing Real.equiv_EuclideanSpace' is continuous (it's the coordinate embedding x ↦ (fun _ => x))
      -- 2. Showing its inverse is continuous (it's the projection (f : Fin 1 → ℝ) ↦ f 0)
      -- 3. Applying image_closure_subset_closure_image in both directions
      -- These are all true but require detailed work with the topology API
      classical
      -- Continuity of the forward and inverse maps
      have hf_cont : Continuous (fun x : ℝ => Real.equiv_EuclideanSpace' x) := by
        show Continuous (fun x : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => x))
        exact continuous_induced_rng.mpr (continuous_pi (fun _ => continuous_id))
      have hg_cont : Continuous (fun x : EuclideanSpace' 1 => EuclideanSpace'.equiv_Real x) := by
        exact PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) ⟨0, by decide⟩
      -- Package the equivalence as a homeomorphism to apply the library lemma
      let e : ℝ ≃ₜ EuclideanSpace' 1 :=
        { toEquiv := Real.equiv_EuclideanSpace'
          continuous_toFun := hf_cont
          continuous_invFun := hg_cont }
      simpa using e.image_closure Q

    rw [← h_image_closure] at h_outer_eq
    rw [h_closure_Q] at h_outer_eq

    -- [0,1] is a 1D box with Jordan outer measure 1
    have h_Icc_outer : Jordan_outer_measure (Real.equiv_EuclideanSpace' '' Set.Icc 0 1) = 1 := by
      -- [0,1] maps to a 1D box [0,1] which is elementary with measure 1
      -- First show that the image is a box
      have h_eq_box : Real.equiv_EuclideanSpace' '' Set.Icc 0 1 = (BoundedInterval.Icc 0 1 : Box 1).toSet := by
        rw [BoundedInterval.coe_of_box]
        simp [BoundedInterval.set_Icc]
      rw [h_eq_box]
      -- This is an elementary set (a box)
      let B := (BoundedInterval.Icc 0 1 : Box 1)
      have hB_elem : IsElementary B.toSet := IsElementary.box B
      -- For an elementary set, Jordan_outer_measure = its measure
      have h_outer_eq_measure : Jordan_outer_measure B.toSet = hB_elem.measure := by
        -- Jordan_outer_measure B = sInf { m | ∃ A elementary, B ⊆ A ∧ m = hA.measure }
        -- Since B is elementary and B ⊆ B, we have hB_elem.measure in the set
        -- Need to show: sInf of this set = hB_elem.measure
        apply le_antisymm
        · -- Jordan_outer_measure B ≤ hB_elem.measure
          exact Jordan_outer_le hB_elem (Set.Subset.refl B.toSet)
        · -- hB_elem.measure ≤ Jordan_outer_measure B
          -- For any A elementary with B ⊆ A, we have hB_elem.measure ≤ hA.measure
          unfold Jordan_outer_measure
          apply le_csInf
          · -- Show the set is nonempty
            use hB_elem.measure, B.toSet, hB_elem, Set.Subset.refl B.toSet
          · -- Show hB_elem.measure is a lower bound
            intro m hm
            obtain ⟨A, hA, hB_subset_A, rfl⟩ := hm
            exact IsElementary.measure_mono hB_elem hA hB_subset_A
      rw [h_outer_eq_measure]
      -- The measure of the box [0,1] is 1
      have h_measure_eq_volume : hB_elem.measure = |B|ᵥ := IsElementary.measure_of_box B
      rw [h_measure_eq_volume]
      -- Volume of 1D box is the length of its side
      simp [Box.volume, B, BoundedInterval.length]

    -- So Q has outer measure 1
    rw [h_Icc_outer] at h_outer_eq
    have h_Q_outer : Jordan_outer_measure (Real.equiv_EuclideanSpace' '' Q) = 1 := h_outer_eq.symm

    -- Use Exercise 1.1.18(2): Jordan_inner_measure(interior(Q)) = Jordan_inner_measure(Q)
    have h_inner_eq : Jordan_inner_measure (interior (Real.equiv_EuclideanSpace' '' Q)) =
                      Jordan_inner_measure (Real.equiv_EuclideanSpace' '' Q) := by
      apply JordanMeasurable.inner_measure_of_interior
      have : Bornology.IsBounded (Real.equiv_EuclideanSpace' '' Q) := by
        -- Same proof as for outer measure
        obtain ⟨c, hc⟩ := Metric.isBounded_iff_subset_ball 0 |>.mp hQ_bounded
        rw [Metric.isBounded_iff_subset_ball 0]
        use c
        intro v hv
        obtain ⟨x, hx, rfl⟩ := hv
        have hx_ball : x ∈ Metric.ball 0 c := hc hx
        rw [Metric.mem_ball, dist_zero_right] at hx_ball
        rw [Metric.mem_ball, dist_zero_right]
        have h_norm_eq : ‖Real.equiv_EuclideanSpace' x‖ = |x| := by
          simp [Real.equiv_EuclideanSpace', EuclideanSpace'.equiv_Real]
          rw [PiLp.norm_eq_of_L2]
          simp
          exact Real.sqrt_sq_eq_abs x
        rw [h_norm_eq]
        exact hx_ball
      exact this

    -- Interior of Q (rationals) is empty (rationals have no interior)
    have h_interior_Q : interior Q = ∅ := by
      -- Rationals have empty interior because irrationals are dense
      ext x
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hx
      -- x ∈ interior Q means there's an open neighborhood of x contained in Q
      rw [mem_interior_iff_mem_nhds] at hx
      -- This means Q ∈ nhds x, which means there's an open set U with x ∈ U ⊆ Q
      obtain ⟨U, hU_Q, hU_open, hx_U⟩ := mem_nhds_iff.mp hx
      -- Find an open ball around x contained in U
      obtain ⟨ε, hε, hball_subset⟩ := Metric.isOpen_iff.mp hU_open x hx_U
      -- Use density of irrationals to find an irrational in the ball
      have h_ball_nonempty : (Metric.ball x ε).Nonempty := ⟨x, Metric.mem_ball_self hε⟩
      obtain ⟨y, hy_mem⟩ := Dense.inter_open_nonempty dense_irrational (Metric.ball x ε) Metric.isOpen_ball h_ball_nonempty
      rw [Set.mem_inter_iff] at hy_mem
      -- Components: first is y ∈ {x | Irrational x}, second is y ∈ Metric.ball x ε
      -- But Lean gives them in opposite order
      obtain ⟨hy_ball_mem, hy_irrat_mem⟩ := hy_mem
      -- y is in U (since ball ⊆ U)
      have hy_U : y ∈ U := hball_subset hy_ball_mem
      -- So y ∈ Q (since U ⊆ Q)
      have hy_Q : y ∈ Q := hU_Q hy_U
      -- But Q contains only rationals
      simp only [Q, Set.mem_range] at hy_Q
      obtain ⟨r, hr⟩ := hy_Q
      -- So y is rational: hr shows (r.val : ℝ) = y, so r.val is the rational witness
      have hy_rational : ∃ q : ℚ, (q:ℝ) = y := ⟨r.val, hr⟩
      -- But y is irrational: hy_irrat_mem : y ∈ {x | Irrational x}
      -- This means Irrational y, which contradicts hy_rational
      simp only [Set.mem_setOf_eq] at hy_irrat_mem
      exact hy_irrat_mem hy_rational

    -- Real.equiv_EuclideanSpace' commutes with interior
    have h_image_interior : Real.equiv_EuclideanSpace' '' interior Q =
                             interior (Real.equiv_EuclideanSpace' '' Q) := by
      -- This is a standard fact about homeomorphisms: they preserve interior
      -- The proof requires showing that Real.equiv_EuclideanSpace' and its inverse
      -- are both open maps (they map open sets to open sets)
      -- This is true because Real.equiv_EuclideanSpace' is a homeomorphism
      -- between ℝ and EuclideanSpace' 1
      classical
      -- Continuity of the forward and inverse maps
      have hf_cont : Continuous (fun x : ℝ => Real.equiv_EuclideanSpace' x) := by
        show Continuous (fun x : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => x))
        exact continuous_induced_rng.mpr (continuous_pi (fun _ => continuous_id))
      have hg_cont : Continuous (fun x : EuclideanSpace' 1 => EuclideanSpace'.equiv_Real x) := by
        exact PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) ⟨0, by decide⟩
      -- Package these maps as a homeomorphism and apply the general lemma on interiors
      let e : ℝ ≃ₜ EuclideanSpace' 1 :=
        { toEquiv := Real.equiv_EuclideanSpace'
          continuous_toFun := hf_cont
          continuous_invFun := hg_cont }
      simpa using e.image_interior Q

    rw [← h_image_interior] at h_inner_eq
    rw [h_interior_Q, Set.image_empty] at h_inner_eq

    -- Inner measure of empty set is 0
    have h_empty_inner : Jordan_inner_measure (∅ : Set (EuclideanSpace' 1)) = 0 := by
      -- The only elementary subset of ∅ is ∅, which has measure 0
      unfold Jordan_inner_measure
      -- Jordan_inner_measure ∅ = sSup { m | ∃ A elementary, A ⊆ ∅ ∧ m = hA.measure }
      -- The only A with A ⊆ ∅ is A = ∅, which has measure 0
      -- So the set is (at most) {0}, and sSup {0} = 0
      apply le_antisymm
      · -- sSup ≤ 0: show every element in the set is ≤ 0
        apply csSup_le
        · -- Show the set is nonempty
          use 0, ∅, IsElementary.empty 1
          simp [IsElementary.measure_of_empty]
        · -- Show every element is ≤ 0
          intro m hm
          obtain ⟨A, hA, hA_subset, rfl⟩ := hm
          -- A ⊆ ∅ means A = ∅
          have hA_empty : A = ∅ := Set.subset_empty_iff.mp hA_subset
          -- So hA.measure = (IsElementary.empty 1).measure = 0
          subst hA_empty
          exact le_of_eq (IsElementary.measure_of_empty 1)
      · -- 0 ≤ sSup: 0 is in the set
        apply le_csSup
        · -- Show the set is bounded above
          use 0
          intro m hm
          obtain ⟨A, hA, hA_subset, rfl⟩ := hm
          have hA_empty : A = ∅ := Set.subset_empty_iff.mp hA_subset
          subst hA_empty
          exact le_of_eq (IsElementary.measure_of_empty 1)
        · -- Show 0 is in the set
          use ∅, IsElementary.empty 1
          simp [IsElementary.measure_of_empty]

    rw [h_empty_inner] at h_inner_eq
    have h_Q_inner : Jordan_inner_measure (Real.equiv_EuclideanSpace' '' Q) = 0 := h_inner_eq.symm

    -- But Jordan measurable means inner = outer
    have h_eq : Jordan_inner_measure (Real.equiv_EuclideanSpace' '' Q) =
                Jordan_outer_measure (Real.equiv_EuclideanSpace' '' Q) := by
      exact hJM'.2

    -- This gives 0 = 1, contradiction
    rw [h_Q_inner, h_Q_outer] at h_eq
    exact absurd h_eq (by norm_num)

/-- Exercise 1.2.1 (countable union) -/
example :
    ∃ E: ℕ → Set ℝ, (∀ n, Bornology.IsBounded (E n)) ∧
      (∀ n, JordanMeasurable (Real.equiv_EuclideanSpace' '' (E n)))
      ∧ ¬ JordanMeasurable (⋃ n, Real.equiv_EuclideanSpace' '' (E n)) := by
  obtain ⟨E, hB, hJM, -, h_union⟩ := exercise_1_2_1_union
  exact ⟨E, hB, hJM, h_union⟩

/-- Exercise 1.2.1 (countable intersection) -/
example :
    ∃ E: ℕ → Set ℝ, (∀ n, Bornology.IsBounded (E n)) ∧
      (∀ n, JordanMeasurable (Real.equiv_EuclideanSpace' '' (E n))) ∧
      ¬ JordanMeasurable (⋂ n, Real.equiv_EuclideanSpace' '' (E n)) := by
  classical
  obtain ⟨S, hS_bdd, hS_jm, hS_subset, hS_union_not⟩ := exercise_1_2_1_union
  let I : Set ℝ := Set.Icc 0 1
  let E : ℕ → Set ℝ := fun n => I \ S n
  have hI_image :
      Real.equiv_EuclideanSpace' '' I =
        (BoundedInterval.Icc 0 1 : Box 1).toSet := by
    rw [BoundedInterval.coe_of_box]
    simp [I, BoundedInterval.set_Icc]
  have hI_JM :
      JordanMeasurable (Real.equiv_EuclideanSpace' '' I) := by
    let B : Box 1 := BoundedInterval.Icc 0 1
    simpa [hI_image, B] using
      (IsElementary.jordanMeasurable (IsElementary.box B))
  have h_image_diff :
      ∀ n,
        Real.equiv_EuclideanSpace' '' (E n) =
          (Real.equiv_EuclideanSpace' '' I) \
            (Real.equiv_EuclideanSpace' '' (S n)) := by
    intro n
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, rfl⟩ := hy
      refine ⟨?_, ?_⟩
      · exact Set.mem_image_of_mem _ hx.1
      · intro hyC
        obtain ⟨z, hz, hz_eq⟩ := hyC
        have : z = x := by
          apply Real.equiv_EuclideanSpace'.injective
          simpa using hz_eq
        exact hx.2 (this ▸ hz)
    · intro hy
      rcases hy with ⟨hyA, hy_not⟩
      obtain ⟨x, hxI, rfl⟩ := hyA
      refine ⟨x, ?_, rfl⟩
      constructor
      · exact hxI
      · intro hxS
        exact hy_not ⟨x, hxS, rfl⟩

  refine ⟨E, ?_, ?_, ?_⟩
  · intro n
    apply Bornology.IsBounded.subset (Metric.isBounded_Icc (a := 0) (b := 1))
    exact Set.diff_subset
  ·
    intro n
    have hJ :
        JordanMeasurable
          ((Real.equiv_EuclideanSpace' '' I) \
            (Real.equiv_EuclideanSpace' '' (S n))) :=
      JordanMeasurable.sdiff hI_JM (hS_jm n)
    exact (h_image_diff n).symm ▸ hJ
  ·
    -- De Morgan's law inside the box [0,1]
    let A := Real.equiv_EuclideanSpace' '' I
    let C : ℕ → Set (EuclideanSpace' 1) :=
      fun n => Real.equiv_EuclideanSpace' '' (S n)
    let F : ℕ → Set (EuclideanSpace' 1) :=
      fun n => Real.equiv_EuclideanSpace' '' (E n)
    have hF_eq : ∀ n, F n = A \ C n := by
      intro n
      simpa [F, C, A] using h_image_diff n
    have hC_union_not : ¬ JordanMeasurable (⋃ n, C n) := by
      have h_image_union :
          Real.equiv_EuclideanSpace' '' (⋃ n, S n) =
            ⋃ n, C n := by
        ext y
        constructor
        · intro hy
          obtain ⟨x, hx, rfl⟩ := hy
          obtain ⟨n, hxSn⟩ := Set.mem_iUnion.mp hx
          refine Set.mem_iUnion.mpr ?_
          exact ⟨n, ⟨x, hxSn, rfl⟩⟩
        · intro hy
          obtain ⟨n, hyC⟩ := Set.mem_iUnion.mp hy
          obtain ⟨x, hxSn, rfl⟩ := hyC
          exact Set.mem_image_of_mem _ (Set.mem_iUnion.mpr ⟨n, hxSn⟩)
      simpa [C, h_image_union] using hS_union_not
    have h_inter_eq :
        (⋂ n, F n) = A \ ⋃ n, C n := by
      ext x
      constructor
      · intro hx
        have hx_all : ∀ n, x ∈ A \ C n := by
          have hx_all' := Set.mem_iInter.mp hx
          intro n
          simpa [hF_eq n] using hx_all' n
        have hxA : x ∈ A := (hx_all 0).1
        have hx_not : x ∉ ⋃ n, C n := by
          intro hx_union
          obtain ⟨n, hxC⟩ := Set.mem_iUnion.mp hx_union
          exact (hx_all n).2 hxC
        exact ⟨hxA, hx_not⟩
      · intro hx
        have hxA : x ∈ A := hx.1
        have hx_not : x ∉ ⋃ n, C n := hx.2
        refine Set.mem_iInter.mpr ?_
        intro n
        have : x ∈ A \ C n := by
          refine ⟨hxA, ?_⟩
          intro hxC
          exact hx_not (Set.mem_iUnion.mpr ⟨n, hxC⟩)
        simpa [hF_eq n] using this
    intro hJM_inter
    have hC_subset : ∀ n, C n ⊆ A := by
      intro n x hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact Set.mem_image_of_mem _ (hS_subset n hy)
    have h_union_subset : (⋃ n, C n) ⊆ A := by
      intro x hx
      obtain ⟨n, hxC⟩ := Set.mem_iUnion.mp hx
      exact hC_subset n hxC
    have h_union_JM : JordanMeasurable (⋃ n, C n) := by
      have h_diff :
          JordanMeasurable (A \ (⋂ n, F n)) :=
        JordanMeasurable.sdiff
          (by simpa [A] using hI_JM) hJM_inter
      classical
      have h_congr := congrArg (fun s => A \ s) h_inter_eq
      have h_step :
          A \ (A \ ⋃ n, C n) = A ∩ ⋃ n, C n := by
        ext x
        constructor
        · intro hx
          have hx_union : x ∈ ⋃ n, C n := by
            by_contra hx_not
            exact hx.2 ⟨hx.1, hx_not⟩
          exact ⟨hx.1, hx_union⟩
        · intro hx
          refine ⟨hx.1, ?_⟩
          intro hx_diff
          exact hx_diff.2 hx.2
      have h_eq :
          (A \ (⋂ n, F n)) = A ∩ ⋃ n, C n :=
        h_congr.trans h_step
      have h_eq' : A ∩ ⋃ n, C n = ⋃ n, C n := by
        apply Set.Subset.antisymm
        · intro x hx
          exact hx.2
        · intro x hx
          exact ⟨h_union_subset hx, hx⟩
      have h_target : JordanMeasurable (A ∩ ⋃ n, C n) :=
        by simpa [h_eq] using h_diff
      simpa [h_eq'] using h_target
    exact hC_union_not h_union_JM



lemma tag_contradiction {n : ℕ} (P : TaggedPartition (Icc 0 1) n) (a : ℝ) (i j k : Fin n)
    (hij : i < j) (hjk : j < k) (hi : P.x_tag i = a) (hj : P.x_tag j = a) (hk : P.x_tag k = a) : False := by
  have hi_bound := P.x_tag_between i
  have hj_bound := P.x_tag_between j
  have hk_bound := P.x_tag_between k
  rw [hi] at hi_bound
  rw [hj] at hj_bound
  rw [hk] at hk_bound
  have hx_ij : P.x i.succ ≤ P.x j.castSucc :=
    P.x_mono.monotone (Fin.succ_le_castSucc_iff.mpr hij)
  have ha_eq1 : P.x i.succ = a := by
    rcases hi_bound with ⟨h1, h2⟩
    rcases hj_bound with ⟨h3, h4⟩
    linarith
  have ha_eq2 : P.x j.castSucc = a := by
    rcases hi_bound with ⟨h1, h2⟩
    rcases hj_bound with ⟨h3, h4⟩
    linarith
  have hx_jk : P.x j.succ ≤ P.x k.castSucc :=
    P.x_mono.monotone (Fin.succ_le_castSucc_iff.mpr hjk)
  have ha_eq3 : P.x j.succ = a := by
    rcases hk_bound with ⟨h5, h6⟩
    rcases hj_bound with ⟨h3, h4⟩
    linarith
  have hx_lt : P.x j.castSucc < P.x j.succ := P.x_mono j.castSucc_lt_succ
  linarith

lemma tag_count_singleton {n : ℕ} (P : TaggedPartition (Icc 0 1) n) (a : ℝ) :
    (Finset.filter (fun (i : Fin n) => P.x_tag i = a) Finset.univ).card ≤ 2 := by
  by_contra! h
  let S := Finset.filter (fun (i : Fin n) => P.x_tag i = a) Finset.univ
  have hS_card : 3 ≤ S.card := by
    have : S.card = (Finset.filter (fun (i : Fin n) => P.x_tag i = a) Finset.univ).card := rfl
    have h' : ¬ S.card ≤ 2 := by simpa [S] using h
    omega
  have hS_nonempty : S.Nonempty := by
    by_contra! hempty
    have hcard0 : S.card = 0 := Finset.card_eq_zero.mpr hempty
    omega
  let i := S.min' hS_nonempty
  have hi_mem : i ∈ S := Finset.min'_mem _ hS_nonempty
  have hi_tag : P.x_tag i = a := by simpa [S] using hi_mem
  let S1 := S.erase i
  have hS1_card : 2 ≤ S1.card := by
    have hcard_erase : (S.erase i).card = S.card - 1 := Finset.card_erase_of_mem hi_mem
    dsimp [S1]
    rw [hcard_erase]
    omega
  have hS1_nonempty : S1.Nonempty := by
    apply Finset.one_le_card.mp; omega
  let j := S1.min' hS1_nonempty
  have hj_mem : j ∈ S1 := Finset.min'_mem _ hS1_nonempty
  have hj_tag : P.x_tag j = a := by
    have : j ∈ S := Finset.mem_of_mem_erase hj_mem
    simpa [S] using this
  have hij : i < j := by
    have htmp : S.min' hS_nonempty < j := Finset.min'_lt_of_mem_erase_min' S hS_nonempty hj_mem
    simpa using htmp
  let S2 := S1.erase j
  have hS2_card : 1 ≤ S2.card := by
    have hcard_erase : (S1.erase j).card = S1.card - 1 := Finset.card_erase_of_mem hj_mem
    dsimp [S2]
    rw [hcard_erase]
    omega
  have hS2_nonempty : S2.Nonempty := by
    apply Finset.one_le_card.mp; omega
  let k := S2.min' hS2_nonempty
  have hk_mem : k ∈ S2 := Finset.min'_mem _ hS2_nonempty
  have hk_tag : P.x_tag k = a := by
    have : k ∈ S1 := Finset.mem_of_mem_erase hk_mem
    have : k ∈ S := Finset.mem_of_mem_erase this
    simpa [S] using this
  have hjk : j < k := by
    have htmp : S1.min' hS1_nonempty < k := Finset.min'_lt_of_mem_erase_min' S1 hS1_nonempty hk_mem
    simpa using htmp
  exact tag_contradiction P a i j k hij hjk hi_tag hj_tag hk_tag

lemma singleton_integrable (a : ℝ) : RiemannIntegrableOn (Set.indicator' ({a} : Set ℝ)) (Icc 0 1) := by
  rw [RiemannIntegrableOn.iff_def]
  refine ⟨rfl, ⟨0, by simp⟩, ?_⟩
  have hzero : riemann_integral_eq (Set.indicator' ({a} : Set ℝ)) (Icc 0 1) 0 := by
    rw [riemann_integral_eq_iff 0]
    intro ε hε
    use ε/2
    refine ⟨half_pos hε, ?_⟩
    intro n P hP_norm
    have h_norm_nonneg : 0 ≤ P.norm := by
      by_cases hn : n = 0
      · subst hn; simp [TaggedPartition.norm]
      · have hpos : 0 < n := Nat.pos_of_ne_zero hn
        let i0 : Fin n := ⟨0, hpos⟩
        have h_delta_nonneg : 0 ≤ P.delta i0 := by
          unfold TaggedPartition.delta
          have h_succ_lt : i0.castSucc < i0.succ := i0.castSucc_lt_succ
          have h_lt : P.x i0.castSucc < P.x i0.succ := P.x_mono h_succ_lt
          linarith
        have h_norm_ge_delta : P.delta i0 ≤ P.norm := by
          unfold TaggedPartition.norm
          refine le_ciSup (Set.Finite.bddAbove (Set.finite_range P.delta)) i0
        linarith
    have h_bound : |P.RiemannSum (Set.indicator' ({a} : Set ℝ))| ≤ 2 * P.norm := by
      unfold TaggedPartition.RiemannSum
      let S := Finset.filter (fun (i : Fin n) => P.x_tag i = a) Finset.univ
      have h_sum_split : ∑ i : Fin n, (Set.indicator' ({a} : Set ℝ) (P.x_tag i)) * P.delta i = Finset.sum S (fun i => P.delta i) := by
        calc
          ∑ i : Fin n, (Set.indicator' ({a} : Set ℝ) (P.x_tag i)) * P.delta i
              = ∑ i : Fin n, (if P.x_tag i = a then (1 : ℝ) else 0) * P.delta i := by
                simp [Set.indicator'_apply]
          _ = ∑ i : Fin n, (if P.x_tag i = a then P.delta i else 0) := by
            refine Finset.sum_congr rfl (fun i hi => ?_)
            split <;> simp
          _ = Finset.sum S (fun i => P.delta i) := by
            simp [S, Finset.sum_filter]
      rw [h_sum_split]
      have h_nonneg : 0 ≤ Finset.sum S (fun i => P.delta i) := by
        apply Finset.sum_nonneg
        intro i hi
        unfold TaggedPartition.delta
        have h_lt' : i.castSucc < i.succ := i.castSucc_lt_succ
        have h_lt : P.x i.castSucc < P.x i.succ := P.x_mono h_lt'
        linarith
      rw [abs_of_nonneg h_nonneg]
      have h_card : (S.card : ℝ) ≤ 2 := by
        have h_card_nat : S.card ≤ 2 := tag_count_singleton P a
        exact_mod_cast h_card_nat
      have h_delta_le_norm (i : Fin n) : P.delta i ≤ P.norm := by
        unfold TaggedPartition.norm
        exact le_ciSup (Set.Finite.bddAbove (Set.finite_range P.delta)) i
      calc
        Finset.sum S (fun i => P.delta i) ≤ Finset.sum S (fun i => P.norm) :=
          Finset.sum_le_sum (fun i hi => h_delta_le_norm i)
        _ = (S.card : ℝ) * P.norm := by simp
        _ ≤ 2 * P.norm := by nlinarith
    have h_final : |P.RiemannSum (Set.indicator' ({a} : Set ℝ)) - 0| ≤ ε := by
      have h_sub : P.RiemannSum (Set.indicator' ({a} : Set ℝ)) - 0 = P.RiemannSum (Set.indicator' ({a} : Set ℝ)) := by ring
      rw [h_sub]
      calc
        |P.RiemannSum (Set.indicator' ({a} : Set ℝ))| ≤ 2 * P.norm := h_bound
        _ ≤ 2 * (ε/2) := by nlinarith
        _ = ε := by ring
    exact h_final
  exact ⟨0, hzero⟩

lemma finite_integrable (E : Finset ℝ) : RiemannIntegrableOn (Set.indicator' (E : Set ℝ)) (Icc 0 1) := by
  induction' E using Finset.induction with a s ha ih
  · -- empty set: indicator is zero function (everywhere 0)
    have hzero : RiemannIntegrableOn (fun _ => (0 : ℝ)) (Icc 0 1) := by
      rw [RiemannIntegrableOn.iff_def]
      refine ⟨rfl, ⟨0, by simp⟩, ?_⟩
      have hzero_eq : riemann_integral_eq (fun _ : ℝ => (0 : ℝ)) (Icc 0 1) 0 := by
        rw [riemann_integral_eq_iff 0]
        intro ε hε
        use 1
        refine ⟨by norm_num, ?_⟩
        intro n P hP_norm
        have : P.RiemannSum (fun _ : ℝ => (0 : ℝ)) = 0 := by
          simp [TaggedPartition.RiemannSum]
        simp [this, hε.le]
      exact ⟨0, hzero_eq⟩
    simpa using hzero
  · -- insert a s: indicator = {a}.indicator' + (s : Set ℝ).indicator'
    have h_union : Set.indicator' ((insert a s : Finset ℝ) : Set ℝ) =
        Set.indicator' ({a} : Set ℝ) + Set.indicator' ((s : Finset ℝ) : Set ℝ) := by
      ext x
      classical
      simp only [Set.indicator'_apply, ha, Finset.mem_insert, Pi.add_apply]
      by_cases hx_a : x = a
      · subst x; simp [ha]
      · by_cases hx_s : x ∈ s
        · simp [hx_s, hx_a, ha]
        · simp [hx_s, hx_a, ha]
    rw [h_union]
    apply RiemannIntegrableOn.add
    · exact singleton_integrable a
    · exact ih

lemma finite_jordanMeasurable (E : Finset ℝ) : JordanMeasurable (Real.equiv_EuclideanSpace' '' (E : Set ℝ)) := by
  induction' E using Finset.induction with a s ha ih
  · simp
    exact JordanMeasurable.empty 1
  · have h_set : ((insert a s : Finset ℝ) : Set ℝ) = ({a} : Set ℝ) ∪ (s : Set ℝ) := by
      simp
    rw [h_set, Set.image_union]
    apply JordanMeasurable.union ?_ ih
    have h_singleton_eq : Real.equiv_EuclideanSpace' '' ({a} : Set ℝ) = (BoundedInterval.Icc a a : Box 1).toSet := by
      rw [BoundedInterval.coe_of_box]
      simp [BoundedInterval.set_Icc]
    rw [h_singleton_eq]
    exact IsElementary.jordanMeasurable (IsElementary.box _)

/-- Exercise 1.2.2 -/
-- The pointwise limit of uniformly bounded Riemann integrable functions need not be Riemann integrable.
example : ∃ f: ℕ → ℝ → ℝ, ∃ F: ℝ → ℝ, ∃ M, ∀ n, ∀ x ∈ Set.Icc 0 1, |f n x| ≤ M ∧
    (∀ x ∈ Set.Icc 0 1, Filter.atTop.Tendsto (fun n ↦ f n x) (nhds (F x))) ∧
    (∀ n, RiemannIntegrableOn (f n) (Icc 0 1)) ∧
    ¬ RiemannIntegrableOn F (Icc 0 1) := by
  -- Enumerate the rationals in [0,1]
  have h_countable : (Set.Icc (0:ℚ) 1).Countable := Set.countable_coe_iff.mp inferInstance
  have h_nonempty : (Set.Icc (0:ℚ) 1).Nonempty := ⟨0, by simp⟩
  obtain ⟨q, hq_surj⟩ := h_countable.exists_surjective h_nonempty
  let Q : Set ℝ := Set.range (fun (q' : ℚ) => (q' : ℝ))
  let En (n : ℕ) : Set ℝ := (Finset.image (fun (k : ℕ) => ((q k).val : ℝ)) (Finset.range n) : Set ℝ)
  let f : ℕ → ℝ → ℝ := fun n => (En n).indicator'
  let F : ℝ → ℝ := Q.indicator'
  have h_finite (k : ℕ) : RiemannIntegrableOn (f k) (Icc 0 1) := by
    dsimp [f]
    have hEn : En k = (Finset.image (fun (k' : ℕ) => ((q k').val : ℝ)) (Finset.range k) : Set ℝ) := rfl
    rw [hEn]
    apply finite_integrable
  have h_bound : ∀ n x, |f n x| ≤ 1 := by
    intro n x
    have : f n x = (if x ∈ En n then (1 : ℝ) else 0) := by
      dsimp [f, En]
      classical
      rw [Set.indicator'_apply (En n) x]
    rw [this]
    split <;> norm_num
  have h_limit : ∀ x ∈ Set.Icc 0 1, Filter.atTop.Tendsto (fun n : ℕ => f n x) (nhds (F x)) := by
    intro x hx
    by_cases hx_Q : x ∈ Q
    · -- Rational case: eventually f n x = 1 = F x
      have h_Fx : F x = 1 := by
        dsimp [F]
        classical
        rw [Set.indicator'_apply Q x, if_pos hx_Q]
      rcases hx_Q with ⟨q', hq'⟩
      have hx_eq_q' : x = (q' : ℝ) := hq'.symm
      have hq'_bounds : q' ∈ Set.Icc (0 : ℚ) 1 := by
        have hx0 : (0 : ℝ) ≤ x := hx.1
        have hx1 : x ≤ 1 := hx.2
        rw [hx_eq_q'] at hx0 hx1
        refine ⟨by exact_mod_cast hx0, by exact_mod_cast hx1⟩
      obtain ⟨k, hk⟩ := hq_surj ⟨q', hq'_bounds⟩
      have hx_eq_qk : x = ((q k).val : ℝ) := by
        calc
          x = (q' : ℝ) := hx_eq_q'
          _ = ((q k).val : ℝ) := by
            simp [hk]
      have h_eventually : ∀ n, k < n → f n x = 1 := by
        intro n hn
        have hx_mem : x ∈ En n := by
          dsimp [En]
          have : ((q k).val : ℝ) ∈ Finset.image (fun (k' : ℕ) => ((q k').val : ℝ)) (Finset.range n) := by
            apply Finset.mem_image.mpr
            refine ⟨k, Finset.mem_range.mpr hn, ?_⟩
            rfl
          simpa [hx_eq_qk]
        dsimp [f]
        classical
        rw [Set.indicator'_apply (En n) x]
        simp [hx_mem]
      rw [h_Fx]
      have h_eventually' : ∀ n, n ≥ k+1 → f n x = 1 := by
        intro n hn
        apply h_eventually n
        omega
      exact tendsto_atTop_of_eventually_const h_eventually'
    · -- Irrational case: f n x = 0 = F x for all n
      have h_Fx : F x = 0 := by
        dsimp [F]
        classical
        rw [Set.indicator'_apply Q x, if_neg hx_Q]
      have h_never : ∀ n, f n x = 0 := by
        intro n
        have hx_not_mem : x ∉ En n := by
          intro hx_mem
          have hx_in_Q : x ∈ Q := by
            dsimp [En] at hx_mem
            have hx_mem' : x ∈ (Finset.image (fun (k' : ℕ) => ((q k').val : ℝ)) (Finset.range n) : Set ℝ) := hx_mem
            simp at hx_mem'
            rcases hx_mem' with ⟨k, hk, hx_eq⟩
            refine ⟨(q k).val, ?_⟩
            simpa [hx_eq]
          exact hx_Q hx_in_Q
        dsimp [f]
        classical
        rw [Set.indicator'_apply (En n) x]
        simp [hx_not_mem]
      rw [h_Fx]
      have h_always : (fun n : ℕ => f n x) = fun _ => 0 := by
        ext n; exact h_never n
      rw [h_always]
      exact tendsto_const_nhds
  have h_F_not_integrable : ¬ RiemannIntegrableOn F (Icc 0 1) := by
    intro h
    rcases h with ⟨hI, h_nonempty_I, hR⟩
    rcases hR with ⟨R, hR_eq⟩
    have h_eps_delta := ((riemann_integral_eq_iff R).mp hR_eq)
    have h_13pos : (0 : ℝ) < 1/3 := by norm_num
    rcases h_eps_delta (1/3) h_13pos with ⟨δ, hδ_pos, hδ⟩
    have h_ab : (Icc 0 1).a < (Icc 0 1).b := by simp
    have h_norm_le : (Icc 0 1) = Icc (Icc 0 1).a (Icc 0 1).b := rfl
    have h_exists := TaggedPartition.exists_norm_le (Icc 0 1) h_norm_le h_ab (δ / 2) (half_pos hδ_pos)
    rcases h_exists with ⟨n, P, hP_norm⟩
    have hP_norm_lt : P.norm < δ := by linarith
    -- Since P has strictly monotone division points, all subintervals have positive length
    have h_delta_pos (i : Fin n) : 0 < P.delta i := by
      unfold TaggedPartition.delta
      have h_lt : P.x i.castSucc < P.x i.succ := P.x_mono i.castSucc_lt_succ
      linarith
    -- Construct a partition with all tags rational
    have h_rational_tag (i : Fin n) : ∃ (r : ℚ), P.x i.castSucc ≤ (r : ℝ) ∧ (r : ℝ) ≤ P.x i.succ := by
      have h_lt : P.x i.castSucc < P.x i.succ := P.x_mono i.castSucc_lt_succ
      obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn h_lt
      refine ⟨r, by linarith, by linarith⟩
    choose r_trational hr_tational_l hr_rational_r using h_rational_tag
    let t_rational : Fin n → ℝ := fun i => (r_trational i : ℝ)
    have ht_rational_case (i : Fin n) : Q (t_rational i) := by
      dsimp [t_rational, Q]
      refine ⟨r_trational i, ?_⟩
      simp
    let P_rational : TaggedPartition (Icc 0 1) n :=
      { x := P.x
        x_tag := t_rational
        x_start := P.x_start
        x_end := P.x_end
        x_mono := P.x_mono
        x_tag_between := fun i => ⟨hr_tational_l i, hr_rational_r i⟩
      }
    have h_norm_rational : P_rational.norm = P.norm := rfl
    have h_RS_rational : P_rational.RiemannSum F = 1 := by
      unfold TaggedPartition.RiemannSum
      calc
        ∑ i : Fin n, F (t_rational i) * P_rational.delta i = ∑ i : Fin n, F (t_rational i) * P.delta i := rfl
        _ = ∑ i : Fin n, 1 * P.delta i := by
          refine Finset.sum_congr rfl (fun i hi => ?_)
          have hF : F (t_rational i) = 1 := by
            dsimp [F]
            classical
            calc
              Q.indicator' (t_rational i) = (if t_rational i ∈ Q then (1 : ℝ) else 0) := by
                rw [Set.indicator'_apply Q (t_rational i)]
              _ = 1 := by
                have hmem : t_rational i ∈ Q := ht_rational_case i
                rw [if_pos hmem]
          simp [hF]
        _ = ∑ i : Fin n, P.delta i := by simp
        _ = (Icc 0 1).b - (Icc 0 1).a := P_rational.sum_delta_eq
        _ = 1 := by simp
    have hP_rational_norm : P_rational.norm ≤ δ := by
      linarith
    have h_bound1 : |P_rational.RiemannSum F - R| ≤ 1/3 := hδ n P_rational hP_rational_norm
    have h_eq1 : P_rational.RiemannSum F - R = 1 - R := by rw [h_RS_rational]
    rw [h_eq1] at h_bound1
    -- Construct a partition with all tags irrational
    have h_irrational_tag (i : Fin n) : ∃ (t : ℝ), Irrational t ∧ P.x i.castSucc ≤ t ∧ t ≤ P.x i.succ := by
      have h_lt : P.x i.castSucc < P.x i.succ := P.x_mono i.castSucc_lt_succ
      obtain ⟨r, hr_irrational, hr1, hr2⟩ := exists_irrational_btwn h_lt
      refine ⟨r, hr_irrational, by linarith, by linarith⟩
    choose t_irrational ht_irrational_i ht_irrational_l ht_irrational_r using h_irrational_tag
    have ht_irrational_case (i : Fin n) : ¬ Q (t_irrational i) := ht_irrational_i i
    let P_irrational : TaggedPartition (Icc 0 1) n :=
      { x := P.x
        x_tag := t_irrational
        x_start := P.x_start
        x_end := P.x_end
        x_mono := P.x_mono
        x_tag_between := fun i => ⟨ht_irrational_l i, ht_irrational_r i⟩
      }
    have h_norm_irrational : P_irrational.norm = P.norm := rfl
    have h_RS_irrational : P_irrational.RiemannSum F = 0 := by
      unfold TaggedPartition.RiemannSum
      calc
        ∑ i : Fin n, F (t_irrational i) * P_irrational.delta i = ∑ i : Fin n, F (t_irrational i) * P.delta i := rfl
        _ = ∑ i : Fin n, 0 * P.delta i := by
          refine Finset.sum_congr rfl (fun i hi => ?_)
          have hF : F (t_irrational i) = 0 := by
            dsimp [F]
            classical
            calc
              Q.indicator' (t_irrational i) = (if t_irrational i ∈ Q then (1 : ℝ) else 0) := by
                rw [Set.indicator'_apply Q (t_irrational i)]
              _ = 0 := by
                have hmem : t_irrational i ∉ Q := ht_irrational_case i
                rw [if_neg hmem]
          simp [hF]
        _ = 0 := by simp
    have hP_irrational_norm : P_irrational.norm ≤ δ := by
      linarith
    have h_bound2 : |P_irrational.RiemannSum F - R| ≤ 1/3 := hδ n P_irrational hP_irrational_norm
    have h_eq2 : P_irrational.RiemannSum F - R = 0 - R := by rw [h_RS_irrational]
    rw [h_eq2] at h_bound2
    have h_contra : (1 : ℝ) ≤ 2/3 := by
      have h_sub : (1 - R) - (0 - R) = 1 := by ring
      calc
        (1 : ℝ) = |(1 - R) - (0 - R)| := by
          rw [h_sub]
          simp
        _ ≤ |1 - R| + |0 - R| := abs_sub _ _
        _ ≤ 1/3 + 1/3 := by nlinarith
        _ = 2/3 := by norm_num
    linarith
  refine ⟨f, F, 1, λ n x hx => ?_⟩
  refine ⟨h_bound n x, ?_⟩
  exact ⟨h_limit, h_finite, h_F_not_integrable⟩

/-- Exercise 1.2.2' -/
-- Determine whether uniform convergence of uniformly bounded Riemann integrable functions preserves Riemann integrability (true or false).
def Ex_1_2_2b : Decidable ( ∀ f: ℕ → ℝ → ℝ, ∀ F: ℝ → ℝ, (∃ M, ∀ n, ∀ x ∈ Set.Icc 0 1, |f n x| ≤ M) → (∀ x ∈ Set.Icc 0 1, TendstoUniformly f F Filter.atTop) → (∀ n, RiemannIntegrableOn (f n) (Icc 0 1)) → RiemannIntegrableOn F (Icc 0 1) ) := by
  apply isTrue
  intro f F h_bound h_unif h_int
  let I : BoundedInterval := Icc (0 : ℝ) 1
  have hI : I = Icc I.a I.b := rfl
  have hI_nonempty : I.toSet.Nonempty := by
    refine ⟨(0 : ℝ), ?_⟩
    simp [I, BoundedInterval.toSet]
  have h_ab : I.a < I.b := by
    simp [I]
  have h_unif_global : TendstoUniformly f F Filter.atTop :=
    h_unif 0 (by norm_num)
  have h_unif_eps : ∀ ε > 0, ∀ᶠ n in Filter.atTop, ∀ x : ℝ, |f n x - F x| < ε := by
    have h := (Metric.tendstoUniformly_iff).mp h_unif_global
    intro ε hε
    simpa [Real.dist_eq, abs_sub_comm] using h ε hε
  have h_int_eq : ∀ n, riemann_integral_eq (f n) I (riemannIntegral (f n) I) := by
    intro n
    exact riemann_integral_of_integrable (h_int n)
  set R := fun n : ℕ => riemannIntegral (f n) I with hRdef
  have h_cauchy : CauchySeq R := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have h_ε4 : ε / 4 > 0 := by linarith
    have h_ε8 : ε / 8 > 0 := by linarith
    rcases Filter.mem_atTop_sets.mp (h_unif_eps (ε / 8) h_ε8) with ⟨N, hN⟩
    refine ⟨N, λ m hm n hn => ?_⟩
    have h_diff : ∀ x : ℝ, |f m x - f n x| < ε / 4 := by
      intro x
      have h_eq : f m x - f n x = (f m x - F x) - (f n x - F x) := by ring
      rw [h_eq]
      calc
        |(f m x - F x) - (f n x - F x)| ≤ |f m x - F x| + |f n x - F x| := abs_sub _ _
        _ < ε / 8 + ε / 8 := by
          have hmx := hN m hm x
          have hnx := hN n hn x
          nlinarith
        _ = ε / 4 := by ring
    rcases ((riemann_integral_eq_iff (R m)).mp (h_int_eq m)) (ε / 4) (by linarith) with ⟨δ_m, hδ_m_pos, hδ_m⟩
    rcases ((riemann_integral_eq_iff (R n)).mp (h_int_eq n)) (ε / 4) (by linarith) with ⟨δ_n, hδ_n_pos, hδ_n⟩
    let δ := min δ_m δ_n
    have hδ_pos : 0 < δ := lt_min_iff.mpr ⟨hδ_m_pos, hδ_n_pos⟩
    rcases TaggedPartition.exists_norm_le I hI h_ab δ hδ_pos with ⟨k, P, hP_norm⟩
    have hP_norm_m : P.norm ≤ δ_m := by
      have hδ_le_m : δ ≤ δ_m := min_le_left _ _
      linarith
    have hP_norm_n : P.norm ≤ δ_n := by
      have hδ_le_n : δ ≤ δ_n := min_le_right _ _
      linarith
    have h_RS_m : |P.RiemannSum (f m) - R m| ≤ ε / 4 := hδ_m k P hP_norm_m
    have h_RS_n : |P.RiemannSum (f n) - R n| ≤ ε / 4 := hδ_n k P hP_norm_n
    have h_delta_pos : ∀ i : Fin k, 0 < P.delta i := by
      intro i
      unfold TaggedPartition.delta
      have h_lt : i.castSucc < i.succ := Fin.castSucc_lt_succ
      have h_x_lt : P.x i.castSucc < P.x i.succ := P.x_mono h_lt
      linarith
    have h_delta_nonneg : ∀ i : Fin k, 0 ≤ P.delta i := λ i => le_of_lt (h_delta_pos i)
    have h_RS_diff : |P.RiemannSum (f m) - P.RiemannSum (f n)| < ε / 4 := by
      unfold TaggedPartition.RiemannSum
      have h_eq : (∑ i : Fin k, f m (P.x_tag i) * P.delta i) - (∑ i : Fin k, f n (P.x_tag i) * P.delta i) =
        ∑ i : Fin k, (f m (P.x_tag i) - f n (P.x_tag i)) * P.delta i := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (λ i hi => ?_)
        ring
      rw [h_eq]
      by_cases hk0 : k = 0
      · subst hk0; simp
        nlinarith
      · have hk_pos : k > 0 := Nat.pos_of_ne_zero hk0
        let i0 : Fin k := ⟨0, hk_pos⟩
        calc
          |∑ i : Fin k, (f m (P.x_tag i) - f n (P.x_tag i)) * P.delta i|
              ≤ ∑ i : Fin k, |(f m (P.x_tag i) - f n (P.x_tag i)) * P.delta i| := by
                simpa using Finset.abs_sum_le_sum_abs (fun i : Fin k => (f m (P.x_tag i) - f n (P.x_tag i)) * P.delta i) Finset.univ
          _ = ∑ i : Fin k, |f m (P.x_tag i) - f n (P.x_tag i)| * |P.delta i| := by
            refine Finset.sum_congr rfl (λ i hi => ?_)
            rw [abs_mul]
          _ = ∑ i : Fin k, |f m (P.x_tag i) - f n (P.x_tag i)| * P.delta i := by
            refine Finset.sum_congr rfl (λ i hi => ?_)
            rw [abs_of_pos (h_delta_pos i)]
          _ < ∑ i : Fin k, (ε / 4) * P.delta i := by
            refine Finset.sum_lt_sum (λ i hi => ?_) ⟨i0, Finset.mem_univ _, ?_⟩
            · have h_bound_val : |f m (P.x_tag i) - f n (P.x_tag i)| ≤ ε / 4 :=
                le_of_lt (h_diff (P.x_tag i))
              have h_nonneg_delta : 0 ≤ P.delta i := h_delta_nonneg i
              exact mul_le_mul_of_nonneg_right h_bound_val h_nonneg_delta
            · have h_bound_val : |f m (P.x_tag i0) - f n (P.x_tag i0)| < ε / 4 := h_diff (P.x_tag i0)
              have h_pos_delta : 0 < P.delta i0 := h_delta_pos i0
              nlinarith
          _ = (ε / 4) * ∑ i : Fin k, P.delta i := by
            simp [Finset.mul_sum]
          _ = (ε / 4) * (I.b - I.a) := by rw [P.sum_delta_eq]
          _ = (ε / 4) * (1 : ℝ) := by norm_num
          _ = ε / 4 := by ring
    have h_abs_three : ∀ (a b c : ℝ), |a + b + c| ≤ |a| + |b| + |c| := by
      intro a b c
      calc
        |a + b + c| = |(a + b) + c| := by ring
        _ ≤ |a + b| + |c| := abs_add_le (a + b) c
        _ ≤ |a| + |b| + |c| := by
          have h := abs_add_le a b
          linarith
    have h_sum_le : |R m - P.RiemannSum (f m)| + |P.RiemannSum (f m) - P.RiemannSum (f n)| + |P.RiemannSum (f n) - R n| ≤ 3 * (ε / 4) := by
      have h_RS_diff_le : |P.RiemannSum (f m) - P.RiemannSum (f n)| ≤ ε / 4 := le_of_lt h_RS_diff
      have h_RS_m' : |R m - P.RiemannSum (f m)| ≤ ε / 4 := by
        rw [abs_sub_comm]
        exact h_RS_m
      have h12 : |R m - P.RiemannSum (f m)| + |P.RiemannSum (f m) - P.RiemannSum (f n)| ≤ (ε / 4) + (ε / 4) := add_le_add h_RS_m' h_RS_diff_le
      calc
        |R m - P.RiemannSum (f m)| + |P.RiemannSum (f m) - P.RiemannSum (f n)| + |P.RiemannSum (f n) - R n|
            ≤ ((ε / 4) + (ε / 4)) + (ε / 4) := add_le_add h12 h_RS_n
        _ = 3 * (ε / 4) := by ring
    have h_ring_eq : R m - R n = (R m - P.RiemannSum (f m)) + (P.RiemannSum (f m) - P.RiemannSum (f n)) + (P.RiemannSum (f n) - R n) := by ring
    calc
      |R m - R n| = |(R m - P.RiemannSum (f m)) + (P.RiemannSum (f m) - P.RiemannSum (f n)) + (P.RiemannSum (f n) - R n)| := by rw [h_ring_eq]
      _ ≤ |R m - P.RiemannSum (f m)| + |P.RiemannSum (f m) - P.RiemannSum (f n)| + |P.RiemannSum (f n) - R n| := h_abs_three _ _ _
      _ ≤ 3 * (ε / 4) := h_sum_le
      _ < ε := by nlinarith
  obtain ⟨R_lim, hR_lim⟩ := cauchySeq_tendsto_of_complete h_cauchy
  have hF_riemann : riemann_integral_eq F I R_lim := by
    rw [riemann_integral_eq_iff R_lim]
    intro ε hε
    have h_ε3 : ε / 3 > 0 := by linarith
    have h_R_lim_eventual : ∀ᶠ n in Filter.atTop, |R n - R_lim| < ε / 3 := by
      have := (Metric.tendsto_nhds.mp hR_lim) (ε / 3) h_ε3
      simpa [Real.dist_eq] using this
    rcases Filter.mem_atTop_sets.mp h_R_lim_eventual with ⟨N1, hN1⟩
    rcases Filter.mem_atTop_sets.mp (h_unif_eps (ε / 3) h_ε3) with ⟨N2, hN2⟩
    let N := max N1 N2
    have hN1' : N1 ≤ N := le_max_left _ _
    have hN2' : N2 ≤ N := le_max_right _ _
    have h_R_diff : |R N - R_lim| < ε / 3 := hN1 N hN1'
    have h_unif_N : ∀ x : ℝ, |f N x - F x| < ε / 3 := λ x => hN2 N hN2' x
    rcases ((riemann_integral_eq_iff (R N)).mp (h_int_eq N)) (ε / 3) h_ε3 with ⟨δ, hδ_pos, hδ⟩
    refine ⟨δ, hδ_pos, λ n P hP_norm => ?_⟩
    have h_RS_fN : |P.RiemannSum (f N) - R N| ≤ ε / 3 := hδ n P hP_norm
    have h_RS_diff : |P.RiemannSum F - P.RiemannSum (f N)| ≤ ε / 3 := by
      unfold TaggedPartition.RiemannSum
      have h_eq : (∑ i : Fin n, F (P.x_tag i) * P.delta i) - (∑ i : Fin n, f N (P.x_tag i) * P.delta i) =
        ∑ i : Fin n, (F (P.x_tag i) - f N (P.x_tag i)) * P.delta i := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (λ i hi => ?_)
        ring
      rw [h_eq]
      by_cases hn0 : n = 0
      · subst hn0; simp
        exact le_of_lt h_ε3
      · have hn_pos : n > 0 := Nat.pos_of_ne_zero hn0
        have h_delta_pos : ∀ i : Fin n, 0 < P.delta i := by
          intro i
          unfold TaggedPartition.delta
          have h_lt : i.castSucc < i.succ := Fin.castSucc_lt_succ
          have h_x_lt : P.x i.castSucc < P.x i.succ := P.x_mono h_lt
          linarith
        calc
          |∑ i : Fin n, (F (P.x_tag i) - f N (P.x_tag i)) * P.delta i|
              ≤ ∑ i : Fin n, |(F (P.x_tag i) - f N (P.x_tag i)) * P.delta i| := by
                simpa using Finset.abs_sum_le_sum_abs (fun i : Fin n => (F (P.x_tag i) - f N (P.x_tag i)) * P.delta i) Finset.univ
          _ = ∑ i : Fin n, |F (P.x_tag i) - f N (P.x_tag i)| * |P.delta i| := by
            refine Finset.sum_congr rfl (λ i hi => ?_)
            rw [abs_mul]
          _ = ∑ i : Fin n, |f N (P.x_tag i) - F (P.x_tag i)| * |P.delta i| := by
            refine Finset.sum_congr rfl (λ i hi => ?_)
            rw [abs_sub_comm]
          _ = ∑ i : Fin n, |f N (P.x_tag i) - F (P.x_tag i)| * P.delta i := by
            refine Finset.sum_congr rfl (λ i hi => ?_)
            rw [abs_of_pos (h_delta_pos i)]
          _ ≤ ∑ i : Fin n, (ε / 3) * P.delta i := by
            refine Finset.sum_le_sum (λ i hi => ?_)
            have h_bound_val : |f N (P.x_tag i) - F (P.x_tag i)| < ε / 3 := h_unif_N (P.x_tag i)
            have h_delta_nonneg : 0 ≤ P.delta i := le_of_lt (h_delta_pos i)
            nlinarith
          _ = (ε / 3) * ∑ i : Fin n, P.delta i := by
            simp [Finset.mul_sum]
          _ = (ε / 3) * (I.b - I.a) := by rw [P.sum_delta_eq]
          _ = (ε / 3) * (1 : ℝ) := by norm_num [I]
          _ = ε / 3 := by ring
    have h_abs_three : ∀ (a b c : ℝ), |a + b + c| ≤ |a| + |b| + |c| := by
      intro a b c
      calc
        |a + b + c| = |(a + b) + c| := by ring
        _ ≤ |a + b| + |c| := abs_add_le (a + b) c
        _ ≤ |a| + |b| + |c| := by
          have h := abs_add_le a b
          linarith
    have h_sum : |P.RiemannSum F - P.RiemannSum (f N)| + |P.RiemannSum (f N) - R N| + |R N - R_lim| ≤ ε := by
      have h1 : |P.RiemannSum F - P.RiemannSum (f N)| ≤ ε / 3 := h_RS_diff
      have h2 : |P.RiemannSum (f N) - R N| ≤ ε / 3 := h_RS_fN
      have h3 : |R N - R_lim| ≤ ε / 3 := le_of_lt h_R_diff
      nlinarith
    have h_ring_eq2 : P.RiemannSum F - R_lim = (P.RiemannSum F - P.RiemannSum (f N)) + (P.RiemannSum (f N) - R N) + (R N - R_lim) := by ring
    calc
      |P.RiemannSum F - R_lim| = |(P.RiemannSum F - P.RiemannSum (f N)) + (P.RiemannSum (f N) - R N) + (R N - R_lim)| := by rw [h_ring_eq2]
      _ ≤ |P.RiemannSum F - P.RiemannSum (f N)| + |P.RiemannSum (f N) - R N| + |R N - R_lim| := h_abs_three _ _ _
      _ ≤ ε := h_sum
  exact ⟨hI, hI_nonempty, ⟨R_lim, hF_riemann⟩⟩

-- The Jordan outer measure equals the infimum of sums of box volumes over all finite box covers.
theorem Jordan_outer_eq {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E) : Jordan_outer_measure E = sInf (((fun S: Finset (Box d) ↦ ∑ B ∈ S, |B|ᵥ)) '' { S | E ⊆ ⋃ B ∈ S, B.toSet }) := by
  -- Strategy: Show equality via two inequalities (le_antisymm)
  apply le_antisymm

  -- Part 1 (≤): Jordan_outer_measure E ≤ sInf of box covers
  · -- For any box cover S, show Jordan_outer_measure E ≤ S.sum volume, then take infimum
    apply le_csInf
    -- Show the set of box cover sums is nonempty
    · obtain ⟨A, hA, hE_sub_A⟩ := IsElementary.contains_bounded hE
      obtain ⟨T, hT_disj, hA_eq⟩ := hA.partition
      use ∑ B ∈ T, |B|ᵥ
      use T
      simp
      intro a ha
      have : a ∈ A := hE_sub_A ha
      rw [hA_eq] at this
      exact this
    -- Show Jordan_outer_measure E is a lower bound for all box cover sums
    · intro m hm
      obtain ⟨S, hS_cover, rfl⟩ := hm
      -- The union ⋃ B ∈ S is elementary
      classical
      -- Map S : Finset (Box d) to a finset of sets
      let S_sets : Finset (Set (EuclideanSpace' d)) := S.image (fun B => B.toSet)
      have hS_elem : ∀ E ∈ S_sets, IsElementary E := by
        intro E hE
        simp [S_sets] at hE
        obtain ⟨B, _, rfl⟩ := hE
        exact IsElementary.box B
      -- Apply IsElementary.union' to show the union is elementary
      have h_union_eq : ⋃ E ∈ S_sets, E = ⋃ B ∈ S, B.toSet := by simp [S_sets]
      have hA_elem : IsElementary (⋃ B ∈ S, B.toSet) := by
        rw [←h_union_eq]
        exact IsElementary.union' hS_elem
      -- E ⊆ ⋃ B ∈ S, so Jordan_outer_measure E ≤ hA_elem.measure
      have h_outer_le : Jordan_outer_measure E ≤ hA_elem.measure := by
        unfold Jordan_outer_measure
        apply csInf_le
        · use 0; intro m' hm'; obtain ⟨_, hB, _, rfl⟩ := hm'; exact IsElementary.measure_nonneg hB
        · use ⋃ B ∈ S, B.toSet, hA_elem, hS_cover
      -- hA_elem.measure ≤ ∑ B ∈ S, |B|ᵥ by subadditivity (IsElementary.measure_of_union')
      have h_sub : hA_elem.measure ≤ ∑ B ∈ S, |B|ᵥ := by
        -- Apply IsElementary.measure_of_union' to get subadditivity
        have h1 := IsElementary.measure_of_union' hS_elem
        -- Show hA_elem.measure = (IsElementary.union' hS_elem).measure
        have h_eq : hA_elem.measure = (IsElementary.union' hS_elem).measure := by
          apply IsElementary.measure_eq_of_set_eq
          exact h_union_eq.symm
        -- Convert the sum over S_sets to sum over S
        -- Technical lemma: sum reindexing via Finset.sum_attach and Finset.sum_image
        have h2 : ∑ E : S_sets, (hS_elem E.val E.property).measure = ∑ B ∈ S, |B|ᵥ := by
          -- Define a helper function to detach measure from proof
          let vol (E : Set (EuclideanSpace' d)) := if h : IsElementary E then h.measure else 0

          -- 1. Show RHS equals sum over S'
          let S' := S.filter (fun B => B.toSet.Nonempty)
          have h_rhs : ∑ B ∈ S, |B|ᵥ = ∑ B ∈ S', |B|ᵥ := by
             rw [←Finset.sum_filter_add_sum_filter_not S (fun B => B.toSet.Nonempty) (fun B => |B|ᵥ)]
             suffices ∑ B ∈ S.filter (fun B => ¬B.toSet.Nonempty), |B|ᵥ = 0 by simp [this, S']
             apply Finset.sum_eq_zero
             intro B hB
             rw [Finset.mem_filter] at hB
             exact Box.volume_eq_zero_of_empty B (Set.not_nonempty_iff_eq_empty.mp hB.2)
          rw [h_rhs]

          -- 2. Simplify LHS to use vol and sum over sets
          have h_lhs : ∑ E : S_sets, (hS_elem E.val E.property).measure = ∑ E ∈ S_sets, vol E := by
            -- Congruence to vol
            have h_congr : ∑ E : S_sets, (hS_elem E.val E.property).measure = ∑ E : S_sets, vol E.val := by
              apply Finset.sum_congr rfl
              intro E _
              dsimp [vol]
              rw [dif_pos (hS_elem E.val E.property)]
            rw [h_congr]
            -- Subtype sum to set sum
            change ∑ E ∈ S_sets.attach, vol E.val = ∑ E ∈ S_sets, vol E
            rw [Finset.sum_attach S_sets]
          rw [h_lhs]

          -- 3. Restrict set sum to non-empty sets
          let S_sets' := S'.image Box.toSet
          have h_subset : S_sets' ⊆ S_sets := Finset.image_subset_image (Finset.filter_subset _ _)

          have h_sets_eq : ∑ E ∈ S_sets, vol E = ∑ E ∈ S_sets', vol E := by
             rw [←Finset.sum_sdiff h_subset]
             suffices ∑ E ∈ S_sets \ S_sets', vol E = 0 by simp [this]
             apply Finset.sum_eq_zero
             intro E hE
             rw [Finset.mem_sdiff] at hE
             have hE_empty : E = ∅ := by
               obtain ⟨h_in, h_notin⟩ := hE
               rw [Finset.mem_image] at h_in
               obtain ⟨B, hB, rfl⟩ := h_in
               by_contra h_non
               apply h_notin
               simp [S_sets', S']
               use B
               simp [hB]
               rw [Set.nonempty_iff_ne_empty]
               exact h_non
             dsimp [vol]
             rw [hE_empty]
             rw [dif_pos (IsElementary.empty d)]
             exact IsElementary.measure_of_empty d
          rw [h_sets_eq]

          -- 4. Use sum_image
          rw [Finset.sum_image]
          · -- Match terms
            apply Finset.sum_congr rfl
            intro B hB
            dsimp [vol]
            rw [dif_pos (IsElementary.box B)]
            exact IsElementary.measure_of_box B
          · -- Injectivity
            intro B₁ hB₁ B₂ hB₂ h_eq
            simp [S'] at hB₁ hB₂
            -- Use helper lemma: Box.toSet is injective for non-empty boxes
            exact Box.toSet_injective_of_nonempty hB₁.2 hB₂.2 h_eq
        calc hA_elem.measure
          _ = (IsElementary.union' hS_elem).measure := h_eq
          _ ≤ ∑ E : S_sets, (hS_elem E.val E.property).measure := h1
          _ = ∑ B ∈ S, |B|ᵥ := h2
      linarith

  -- Part 2 (≥): sInf of box covers ≤ Jordan_outer_measure E
  · -- For any elementary A ⊇ E, show sInf(box covers) ≤ hA.measure
    unfold Jordan_outer_measure
    apply le_csInf
    -- Show the set of elementary cover measures is nonempty
    · obtain ⟨A, hA, hE_sub_A⟩ := IsElementary.contains_bounded hE
      use hA.measure
      use A, hA, hE_sub_A
    -- Show sInf(box covers) is a lower bound for all elementary cover measures
    · intro m hm
      obtain ⟨A, hA, hE_sub_A, rfl⟩ := hm
      -- Get partition T of A
      obtain ⟨T, hT_disj, hA_eq⟩ := hA.partition
      -- T is a box cover: E ⊆ A = ⋃ B ∈ T
      have hT_cover : E ⊆ ⋃ B ∈ T, B.toSet := hA_eq ▸ hE_sub_A
      -- T.sum volume = hA.measure
      have hT_sum : ∑ B ∈ T, |B|ᵥ = hA.measure := by
        symm; exact hA.measure_eq hT_disj hA_eq
      -- sInf(box covers) ≤ ∑ B ∈ T, |B|ᵥ (since T is a box cover)
      have h_inf_le : sInf (((fun S: Finset (Box d) ↦ ∑ B ∈ S, |B|ᵥ)) '' { S | E ⊆ ⋃ B ∈ S, B.toSet }) ≤ ∑ B ∈ T, |B|ᵥ := by
        apply csInf_le
        -- Show box covers set is bounded below
        · use 0
          intro m' hm'
          obtain ⟨S, _, rfl⟩ := hm'
          apply Finset.sum_nonneg
          intro B _
          rw [Box.volume]
          apply Finset.prod_nonneg
          intro i _
          rw [BoundedInterval.length]
          exact le_max_right _ _
        -- ∑ B ∈ T, |B|ᵥ is in the box covers set
        · show ∑ B ∈ T, |B|ᵥ ∈ (fun S ↦ ∑ B ∈ S, |B|ᵥ) '' {S | E ⊆ ⋃ B ∈ S, B.toSet}
          simp
          exact ⟨T, hT_cover, rfl⟩
      -- Combine: sInf(box covers) ≤ ∑ B ∈ T, |B|ᵥ = hA.measure
      rw [←hT_sum]; exact h_inf_le

/-- This definition deviates from the text by working with countable families of boxes rather than boxes indexed by the natural numbers.  This becomes important in dimension zero, when all boxes are non-empty. -/
noncomputable def Lebesgue_outer_measure {d:ℕ} (E: Set (EuclideanSpace' d)) : EReal :=
  sInf { V | ∃ (X : Set ℕ) (S: X → Box d), E ⊆ ⋃ n, (S n).toSet ∧ V = ∑' n, (S n).volume.toEReal }

/-- When d > 0, the Lebesgue outer measure can be computed using ℕ-indexed box sequences,
    which is equivalent to the definition using countable families. This is because we can
    pad any countable family with zero-volume boxes (which exist when d > 0). -/
lemma Lebesgue_outer_measure_eq_nat_indexed {d:ℕ} (hd: 0 < d) (E: Set (EuclideanSpace' d)) :
    Lebesgue_outer_measure E =
    sInf (((fun S: ℕ → Box d ↦ ∑' n, (S n).volume.toEReal)) '' { S | E ⊆ ⋃ n, (S n).toSet }) := by
  unfold Lebesgue_outer_measure
  -- Strategy: Show both ≤ directions
  -- (≤): Any ℕ-indexed cover is a countable cover with X = Set.univ
  -- (≥): For any countable cover (X, S), construct ℕ-indexed S' by:
  --      - Use the equivalence Set.univ ≃ ℕ to reindex
  --      - Show sums are equal via Equiv.tsum_eq
  apply le_antisymm

  -- Part 1 (≤): ℕ-indexed covers ≥ countable covers
  · apply le_sInf
    intro b hb
    obtain ⟨S, hS_cover, rfl⟩ := hb
    -- Show ∑' n, (S n).volume.toEReal is in the countable covers set
    apply sInf_le
    show ∑' n, (S n).volume.toEReal ∈ { V | ∃ (X : Set ℕ) (S: X → Box d), E ⊆ ⋃ n, (S n).toSet ∧ V = ∑' n, (S n).volume.toEReal }
    -- Convert S : ℕ → Box d to S' : Set.univ → Box d
    let S' : Set.univ → Box d := fun n => S n.val
    use Set.univ, S'
    constructor
    · -- Covering property: E ⊆ ⋃ n : Set.univ, (S' n).toSet
      have : (⋃ n : Set.univ, (S' n).toSet) = (⋃ n, (S n).toSet) := by
        ext x
        simp [S']
      rw [this]
      exact hS_cover
    · -- Sum equality: ∑' (n : Set.univ), (S' n).volume.toEReal = ∑' n, (S n).volume.toEReal
      -- Strategy: Use Equiv.tsum_eq to reindex from Set.univ to ℕ
      simp only [S']
      -- The equivalence Equiv.Set.univ : Set.univ ≃ ℕ allows us to reindex the sum
      -- We want: ∑' (n : Set.univ), f(n.val) = ∑' (n : ℕ), f(n)
      -- Equiv.tsum_eq gives: ∑' (c : Set.univ), f(e c) = ∑' (b : ℕ), f b
      -- We need to apply it backwards (using symm)
      exact ((Equiv.Set.univ ℕ).tsum_eq (fun n => (S n).volume.toEReal)).symm

  -- Part 2 (≥): Countable covers ≥ ℕ-indexed covers
  · apply le_sInf
    intro b hb
    simp only [Set.mem_setOf_eq] at hb
    obtain ⟨X, S, hS_cover, hb_eq⟩ := hb
    open Classical in

    -- Construct zero-volume box (exists when d > 0)
    have ⟨B₀, hB₀⟩ : ∃ B : Box d, B.volume = 0 := by
      -- When d > 0, we can construct a box with empty interval in first dimension
      use ⟨fun i => BoundedInterval.Ioc 0 0⟩
      simp only [Box.volume, BoundedInterval.length]
      -- The product ∏ i : Fin d, max (0 - 0) 0 = ∏ i : Fin d, 0
      conv_lhs => arg 2; ext i; rw [sub_self, max_eq_right (le_refl 0)]
      -- Now we have ∏ i : Fin d, 0 = 0^d (since d > 0, this is 0)
      rw [Finset.prod_const]
      rw [show Finset.univ.card = d from Fintype.card_fin d]
      exact zero_pow (Nat.pos_iff_ne_zero.mp hd)

    -- Extend S : X → Box d to S' : ℕ → Box d by using B₀ for indices not in X
    let S' : ℕ → Box d := fun n => if h : n ∈ X then S ⟨n, h⟩ else B₀

    -- Show S' is a valid cover
    have hS'_cover : E ⊆ ⋃ n, (S' n).toSet := by
      intro x hx
      have := hS_cover hx
      simp only [Set.mem_iUnion] at this ⊢
      obtain ⟨⟨n, hn⟩, hxn⟩ := this
      use n
      -- At index n, we have n ∈ X, so S' n = S ⟨n, hn⟩
      have : S' n = S ⟨n, hn⟩ := by simp [S', hn]
      rw [this]
      exact hxn

    -- Show sums are equal
    have h_sum : ∑' n, (S' n).volume.toEReal = ∑' (n : X), (S n).volume.toEReal := by
      -- Strategy: Rewrite S' using if-then-else, then show terms outside X contribute 0
      -- Use tsum_congr to match terms inside X with the subtype sum

      -- Step 1: Express the LHS explicitly showing the if-then-else
      have h_S'_eq : ∀ n, (S' n).volume.toEReal =
          if h : n ∈ X then (S ⟨n, h⟩).volume.toEReal else (B₀.volume : EReal) := by
        intro n
        simp only [S']
        split_ifs <;> rfl

      simp_rw [h_S'_eq, hB₀]
      simp only [EReal.coe_zero]

      -- Step 2: The sum ∑' n, (if n ∈ X then f n else 0) = ∑' (n : X), f n
      -- This is the key equality relating the full sum to the subtype sum
      -- Strategy: Show both sums enumerate the same terms via subtype coercion

      -- Both sides sum over the same elements: for each n ∈ X, we add (S n).volume
      -- The LHS uses characteristic function; RHS uses subtype indexing
      -- This is a standard reindexing via the subtype embedding coe : X → ℕ

      -- Show the functions match when properly aligned
      have h_fn_eq : ∀ (x : X), (if h : ↑x ∈ X then (S ⟨↑x, h⟩).volume.toEReal else (0 : EReal)) =
                                 (S x).volume.toEReal := by
        intro ⟨n, hn⟩
        simp only [hn, dite_true]

      -- Now we need: ∑' n : ℕ, (if h : n ∈ X then ... else 0) = ∑' x : X, f x
      -- This is a standard measure theory fact: summing with characteristic function
      -- equals summing over the subtype. Both sums enumerate exactly the same terms

      -- Define g to make the terms clearer
      let g : ℕ → EReal := fun n => if h : n ∈ X then (S ⟨n, h⟩).volume.toEReal else 0

      -- 1. Show LHS equals sum of g
      have h1 : (∑' n, if h : n ∈ X then (S ⟨n, h⟩).volume.toEReal else 0) = ∑' n, g n := rfl

      -- 2. Use tsum_subtype to relate sum over ℕ to sum over X
      have h2 : ∑' n, g n = ∑' (x : X), g x := by
        -- Use classical logic for if-then-else
        classical
        -- tsum_subtype gives: ∑' x:X, f x = ∑' n, if n ∈ X then f n else 0
        -- We rewrite the RHS (sum over X) to sum over ℕ with if-then-else
        rw [tsum_subtype (f := g)]
        -- Now we match the sums term by term
        apply tsum_congr
        intro n
        -- g n is defined exactly to be 0 outside X, matching the if-then-else
        rw [Set.indicator_apply]
        split_ifs with h
        · rfl
        · simp [g, h]

      -- 3. Show g restricted to X equals the RHS term
      have h3 : ∑' (x : X), g x = ∑' (x : X), (S x).volume.toEReal := by
        apply tsum_congr
        intro x
        -- For x ∈ X, g x simplifies to S x.volume
        simp [g, x.property]

      -- Combine steps
      rw [h1, h2, h3]

    -- Apply sInf_le
    calc sInf (((fun S: ℕ → Box d ↦ ∑' n, (S n).volume.toEReal)) '' { S | E ⊆ ⋃ n, (S n).toSet })
        ≤ ∑' n, (S' n).volume.toEReal := by
            apply sInf_le
            use S', hS'_cover
        _ = ∑' (n : X), (S n).volume.toEReal := h_sum
        _ = b := hb_eq.symm

open Classical in
/-- Helper lemma: If X is an infinite subset of ℕ, then the sum of its indicator function
    (mapping elements of X to 1 and others to 0) diverges to ⊤ in {name}`EReal`. -/
lemma hasSum_indicator_top_of_infinite (X : Set ℕ) (hX : ¬X.Finite) :
    HasSum (fun n => if n ∈ X then (1 : EReal) else 0) ⊤ := by
  -- Strategy: Show that finite sums grow unboundedly.
  -- For any n, we can find n elements in X (since X is infinite),
  -- so there exists a finite sum ≥ n. This proves convergence to ⊤.

  unfold HasSum
  rw [EReal.tendsto_nhds_top_iff_real]
  intro r

  -- For any real bound r, we need to show eventually sums exceed r
  -- Choose n > r (using ceiling), then find n elements in X
  obtain ⟨n, hn⟩ := exists_nat_gt r

  -- Since X is infinite, we can extract a finite subset with exactly n elements
  have hX_inf : X.Infinite := hX
  obtain ⟨F, hF_sub, hF_card⟩ := Set.Infinite.exists_subset_card_eq hX_inf n

  -- Show that eventually (in the atTop filter), finite sums are ≥ n
  apply Filter.eventually_atTop.mpr
  use F
  intro s hFs

  -- For any finset s containing F, we have ∑ i ∈ s, (indicator) ≥ n
  calc (r : EReal) < (n : EReal) := EReal.coe_lt_coe_iff.mpr hn
       _ = ↑F.card := by rw [hF_card]
       _ = ∑ i ∈ F, (1 : EReal) := by
           rw [Finset.sum_const, nsmul_one]
       _ = ∑ i ∈ F, if i ∈ X then (1 : EReal) else 0 := by
           apply Finset.sum_congr rfl
           intro i hi
           rw [if_pos]
           exact hF_sub (Finset.mem_coe.mpr hi)
       _ ≤ ∑ i ∈ s, if i ∈ X then (1 : EReal) else 0 := by
           apply Finset.sum_le_sum_of_subset_of_nonneg hFs
           intro i _ _
           split_ifs <;> norm_num

open Classical in
/-- In dimension 0, the Lebesgue outer measure is 1 for non-empty sets and 0 for the empty set.
    This is because all boxes in dimension 0 are singletons with volume 1 (empty product). -/
lemma Lebesgue_outer_measure_of_dim_zero {E: Set (EuclideanSpace' 0)} :
    Lebesgue_outer_measure E = if E.Nonempty then 1 else 0 := by
  unfold Lebesgue_outer_measure

  -- First prove: all boxes in dimension 0 have volume 1 (empty product)
  have h_box_vol : ∀ B : Box 0, B.volume = 1 := by
    intro B
    unfold Box.volume
    -- Fin 0 is empty, so Finset.univ is empty, and empty product = 1
    have : Finset.univ = (∅ : Finset (Fin 0)) := by
      ext i
      exact Fin.elim0 i
    rw [this]
    rfl

  by_cases hE : E.Nonempty

  -- Case 1: E is nonempty → measure = 1
  · simp only [hE, ↓reduceIte]
    apply le_antisymm

    -- Upper bound: show sInf ≤ 1 by exhibiting a cover with sum = 1
    · apply sInf_le
      -- Construct a cover using a singleton set {0}
      let X : Set ℕ := {0}
      let B₀ : Box 0 := ⟨fun i => Fin.elim0 i⟩
      let S : X → Box 0 := fun _ => B₀
      use X, S
      constructor
      · -- Show E ⊆ ⋃ n, (S n).toSet
        intro x _
        simp only [Set.mem_iUnion]
        use ⟨0, Set.mem_singleton 0⟩
        -- All points in EuclideanSpace' 0 are in any box
        unfold Box.toSet
        intro i
        exact Fin.elim0 i
      · -- Show V = ∑' n, (S n).volume.toEReal = 1
        -- S maps every element of X = {0} to B₀, which has volume 1
        have h_vol_eq : ∀ (n : X), (S n).volume.toEReal = (1 : EReal) := by
          intro n
          simp only [S, h_box_vol, EReal.coe_one]
        simp_rw [h_vol_eq]
        -- ∑' (_ : {0}), (1 : EReal) = 1 using tsum over finite type
        rw [tsum_fintype]
        -- Now we have ∑ x ∈ Finset.univ, (1 : EReal) where Finset.univ has card 1
        simp only [Finset.sum_const]
        -- Show Finset.univ.card • 1 = 1 by showing card = 1
        have h_card : Fintype.card X = 1 := Set.card_singleton 0
        simp only [Fintype.card] at h_card
        rw [h_card]
        norm_num

    -- Lower bound: show 1 ≤ sInf (every cover has sum ≥ 1)
    · apply le_sInf
      intro b hb
      simp only [Set.mem_setOf_eq] at hb
      obtain ⟨X, S, hcover, hb_eq⟩ := hb
      -- E is nonempty, so the cover must be nonempty
      have hX_nonempty : X.Nonempty := by
        obtain ⟨x, hx⟩ := hE
        have := hcover hx
        simp only [Set.mem_iUnion] at this
        obtain ⟨⟨n, hn⟩, _⟩ := this
        exact ⟨n, hn⟩
      rw [hb_eq]
      -- Sum of volumes (each = 1) over nonempty set X
      have : ∀ (n : X), (S n).volume.toEReal = (1 : EReal) := by
        intro n
        simp [h_box_vol]
      simp_rw [this]
      -- Need: ∑' (_ : X), (1 : EReal) ≥ 1 when X.Nonempty
      -- Pick an element n₀ from X and show the sum includes at least that term
      obtain ⟨n₀, hn₀⟩ := hX_nonempty
      -- Convert sum over subtype to sum over ℕ with indicator
      classical
      let g : ℕ → EReal := fun n => if h : n ∈ X then (1 : EReal) else (0 : EReal)
      have h1 : ∑' (n : ↑X), (1 : EReal) = ∑' n : ℕ, g n := by
        -- Use tsum_subtype: ∑' (x : X), f x = ∑' n, X.indicator f n
        rw [tsum_subtype (f := fun n => (1 : EReal))]
        apply tsum_congr
        intro n
        -- Show X.indicator (fun n => 1) n = g n
        simp [g, Set.indicator_apply]
      rw [h1]
      -- First show all terms are nonnegative
      have h_nonneg : ∀ n, (0 : EReal) ≤ g n := by
        intro n
        simp [g]
        split_ifs
        · exact EReal.coe_nonneg.mpr (by norm_num)
        · exact EReal.coe_nonneg.mpr (by norm_num)
      -- Show that g n₀ = 1
      have h_gn0 : g n₀ = (1 : EReal) := by
        simp [g, hn₀]
      -- The key: use that for summable nonnegative functions, any term is ≤ the sum
      -- Since g is nonnegative and summable (it's an indicator function with values 0 or 1),
      -- we have g n₀ ≤ ∑' n, g n
      -- For EReal, construct this using HasSum properties
      have h_le : g n₀ ≤ ∑' n : ℕ, g n := by
        -- Use that tsum is the supremum of finite sums
        -- Since {n₀} is a finite subset, ∑ n ∈ {n₀}, g n ≤ ∑' n, g n
        -- And ∑ n ∈ {n₀}, g n = g n₀ = 1
        have h_single : ∑ n ∈ ({n₀} : Finset ℕ), g n = g n₀ := by
          simp [Finset.sum_singleton]
        have : HasSum g (∑' n : ℕ, g n) := by
          by_cases hX : X.Finite
          · -- Case 1: X is finite
            have h_supp : g.support.Finite := by
              dsimp [g, Function.support]
              apply Set.Finite.subset hX
              intro n h
              simp at h
              exact h
            exact (summable_of_hasFiniteSupport h_supp).hasSum
          · -- Case 2: X is infinite
            -- The sum is Top. We prove HasSum g Top.
            have h_top : HasSum g ⊤ := by
              -- Apply helper lemma: infinite indicator sum diverges to ⊤
              -- g and the lemma function are definitionally equal under classical
              convert hasSum_indicator_top_of_infinite X hX using 2
            exact h_top.tsum_eq.symm ▸ h_top
        -- If HasSum g s, then for any finite set F, ∑ n ∈ F, g n ≤ s
        -- Apply this with F = {n₀}
        have h_fin_le : ∑ n ∈ ({n₀} : Finset ℕ), g n ≤ ∑' n : ℕ, g n := by
          rw [Finset.sum_singleton]
          -- Since g is nonnegative, g n₀ ≤ sum over any superset containing n₀
          -- In particular, g n₀ ≤ ∑' n, g n
          trans (∑ n ∈ Finset.range (n₀ + 1), g n)
          · apply Finset.single_le_sum (fun i _ => h_nonneg i)
            simp
          · -- Now show ∑ n ∈ range (n₀+1), g n ≤ tsum
            exact sum_le_hasSum (L := .unconditional ℕ) _ (fun i _ => h_nonneg i) this
        rw [h_single] at h_fin_le
        exact h_fin_le
      rw [h_gn0] at h_le
      exact h_le

  -- Case 2: E is empty → measure = 0
  · simp only [hE, ↓reduceIte]
    apply le_antisymm

    -- Upper bound: show sInf ≤ 0 by exhibiting a cover with sum = 0
    · apply sInf_le
      -- Empty cover: X = ∅
      let X : Set ℕ := ∅
      use X
      -- Need to provide S : X → Box 0, but X is empty so use elim
      refine ⟨fun x => absurd x.2 (Set.notMem_empty x.1), ?_, ?_⟩
      · -- Empty set is covered by empty cover
        intro x hx
        simp only [Set.not_nonempty_iff_eq_empty] at hE
        exact absurd hx (hE ▸ Set.notMem_empty x)
      · -- Sum over empty set = 0
        simp

    -- Lower bound: 0 ≤ sInf (all EReal sums are ≥ 0 when summing volumes)
    · apply le_sInf
      intro b hb
      simp only [Set.mem_setOf_eq] at hb
      obtain ⟨X, S, _, hb_eq⟩ := hb
      rw [hb_eq]
      -- Sum of nonnegative volumes is ≥ 0
      apply tsum_nonneg
      intro n
      apply EReal.coe_nonneg.mpr
      -- Box volume is a product of nonnegative lengths
      unfold Box.volume
      apply Finset.prod_nonneg
      intro i _
      unfold BoundedInterval.length
      exact le_max_right _ _

/-- Coercion {lean}`ℝ → EReal` preserves infimums for nonempty bounded-below sets -/
lemma EReal.sInf_image_coe {s : Set ℝ} (hs : s.Nonempty) (h_bdd : BddBelow s) :
    sInf ((fun x : ℝ => (x : EReal)) '' s) = ↑(sInf s) := by
  -- Strategy: Show both ≤ directions using sInf properties
  apply le_antisymm

  -- Part 1: sInf(↑''s) ≤ ↑(sInf s)
  · -- Key: sInf(↑''s) is a lower bound for ↑''s, so sInf(↑''s) ≤ ↑x for all x ∈ s
    -- We want to show this implies sInf(↑''s) ≤ ↑(sInf s)
    -- Case analysis on whether sInf(↑''s) is ⊥ or a real
    by_cases h_bot : sInf ((fun y : ℝ => (y : EReal)) '' s) = ⊥
    · rw [h_bot]; exact bot_le
    · -- sInf(↑''s) is bounded below (since s is), so it's not ⊥ or ⊤
      -- We have: ∀ x ∈ s, sInf(↑''s) ≤ ↑x
      have h_le_all : ∀ x ∈ s, sInf ((fun y : ℝ => (y : EReal)) '' s) ≤ ↑x := by
        intro x hx; apply sInf_le; exact ⟨x, hx, rfl⟩
      -- Since s is bounded below, there exists m such that m ≤ x for all x ∈ s
      -- This means ↑m is a lower bound for ↑''s, so ↑m ≤ sInf(↑''s)
      -- Combined with sInf(↑''s) ≤ ↑x for all x, we get that sInf(↑''s) is in [↑m, ↑x₀]
      -- where x₀ ∈ s, hence sInf(↑''s) must be a casted real
      -- Then we can extract r := (sInf(↑''s)).toReal and show r ≤ sInf s
      obtain ⟨m, hm⟩ := h_bdd
      have h_bdd_below : (m : EReal) ≤ sInf ((fun y : ℝ => (y : EReal)) '' s) := by
        apply le_sInf
        intro b hb
        obtain ⟨x, hx, rfl⟩ := hb
        exact EReal.coe_le_coe_iff.mpr (hm hx)
      -- Now sInf(↑''s) ∈ [↑m, ↑x₀], so it's a casted real
      -- We want: sInf(↑''s) ≤ ↑(sInf s)
      -- Strategy: Show sInf(↑''s) ≤ ↑x for all x ∈ s, then take inf over x
      -- Apply le_csInf: to show a ≤ sInf s, prove a is a lower bound for s
      obtain ⟨x₀, hx₀⟩ := hs
      have h_le_x0 : sInf ((fun y : ℝ => (y : EReal)) '' s) ≤ ↑x₀ := h_le_all x₀ hx₀
      -- sInf(↑''s) is in [↑m, ↑x₀], so it must be a casted real
      have h_exists_r : ∃ r : ℝ, sInf ((fun y : ℝ => (y : EReal)) '' s) = ↑r := by
        -- Use that sInf(↑''s) is bounded: ↑m ≤ sInf(↑''s) ≤ ↑x₀
        -- If sInf(↑''s) = ⊤, then ↑x₀ ≥ ⊤, contradicting that x₀ is real
        by_cases h_top : sInf ((fun y : ℝ => (y : EReal)) '' s) = ⊤
        · -- Get contradiction: ↑x₀ ≥ ⊤
          have : (x₀ : EReal) ≥ ⊤ := by rw [←h_top]; exact h_le_x0
          simp [not_le.mpr] at this
        · -- sInf(↑''s) is not ⊥ (from h_bot) and not ⊤ (from h_top)
          -- So it must be a casted real
          -- Use EReal trichotomy: either ⊥, ⊤, or casted real
          have h_cases := EReal.def (sInf ((fun y : ℝ => (y : EReal)) '' s))
          cases h_cases with
          | inl h => obtain ⟨r, hr⟩ := h; exact ⟨r, hr.symm⟩
          | inr h => cases h with
            | inl h_eq_top => exact absurd h_eq_top h_top
            | inr h_eq_bot => exact absurd h_eq_bot h_bot
      obtain ⟨r, hr⟩ := h_exists_r
      rw [hr]
      -- Now show: ↑r ≤ ↑(sInf s), i.e., r ≤ sInf s
      apply EReal.coe_le_coe_iff.mpr
      -- Show r ≤ sInf s by showing r is a lower bound for s
      have hs' : s.Nonempty := ⟨x₀, hx₀⟩
      apply le_csInf hs'
      intro x hx
      -- Show r ≤ x for all x ∈ s
      -- We have ↑r = sInf(↑''s) ≤ ↑x
      have : (r : EReal) ≤ ↑x := by rw [←hr]; exact h_le_all x hx
      exact EReal.coe_le_coe_iff.mp this

  -- Part 2: ↑(sInf s) ≤ sInf(↑''s)
  -- Show that ↑(sInf s) is a lower bound for ↑''s
  · apply le_sInf
    intro b hb
    obtain ⟨x, hx_in_s, rfl⟩ := hb
    -- Show: ↑(sInf s) ≤ ↑x
    apply EReal.coe_le_coe_iff.mpr
    -- Show: sInf s ≤ x (true since x ∈ s and sInf s is a lower bound)
    exact csInf_le h_bdd hx_in_s

/-- When enumerating a finset to a sequence padded with empty boxes,
    the infinite sum of volumes equals the finite sum -/
lemma tsum_volume_finset_eq {d : ℕ} (hd : 0 < d) (S : Finset (Box d)) :
    let S_list := S.toList
    let zero_box : Box d := ⟨fun i => if i.val = 0 then ∅ else BoundedInterval.Icc 0 0⟩
    let S_seq : ℕ → Box d := fun n =>
      if h : n < S_list.length then S_list.get ⟨n, h⟩ else zero_box
    ∑' n, (S_seq n).volume.toEReal = (∑ B ∈ S, |B|ᵥ).toEReal := by
  -- Strategy: zero_box has volume 0 (first side is empty), so tsum = sum over finite range
  -- Then relate finite range sum to finset sum via list enumeration
  intro S_list zero_box S_seq

  -- Step 1: Show zero_box has volume 0
  have h_zero_vol : |zero_box|ᵥ = 0 := by
    unfold Box.volume zero_box
    simp only
    -- The first side (index 0) is empty, so product is 0
    apply Finset.prod_eq_zero (Finset.mem_univ (⟨0, hd⟩ : Fin d))
    simp only [ite_true]
    simp [BoundedInterval.length]

  -- Step 2: Use tsum_eq_sum to convert infinite sum to finite sum
  have h_tsum_eq : ∑' n, (S_seq n).volume.toEReal = ∑ n ∈ Finset.range S_list.length, (S_seq n).volume.toEReal := by
    apply tsum_eq_sum
    intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    unfold S_seq
    rw [dif_neg (not_lt_of_ge hn)]
    simp [h_zero_vol]

  -- Step 3: Relate finset.range sum to finset S sum
  rw [h_tsum_eq]
  suffices h : (∑ n ∈ Finset.range S_list.length, (S_seq n).volume) = (∑ B ∈ S, |B|ᵥ) by
    calc ∑ n ∈ Finset.range S_list.length, (S_seq n).volume.toEReal
        = ∑ n ∈ Finset.range S_list.length, ((S_seq n).volume : EReal) := rfl
      _ = (∑ n ∈ Finset.range S_list.length, (S_seq n).volume : ℝ).toEReal := by
        -- Coercion ℝ → EReal commutes with Finset.sum
        -- This follows from EReal.coe_add: (x + y : EReal) = (x : EReal) + (y : EReal)
        -- Prove by induction: empty sum is 0, and for cons, use EReal.coe_add and induction hypothesis
        refine Finset.cons_induction (by simp) ?_ (Finset.range S_list.length)
        intro a s ha ih
        rw [Finset.sum_cons ha]
        conv_rhs => rw [Finset.sum_cons ha, EReal.coe_add]
        -- Now: ↑(S_seq a).volume + ∑ x ∈ s, ↑(S_seq x).volume = ↑(S_seq a).volume + ↑(∑ x ∈ s, (S_seq x).volume)
        -- Use ih: ∑ x ∈ s, ↑(S_seq x).volume = ↑(∑ x ∈ s, (S_seq x).volume)
        rw [ih]
      _ = (∑ B ∈ S, |B|ᵥ).toEReal := by rw [h]

  -- Prove: ∑ n ∈ Finset.range S_list.length, (S_seq n).volume = ∑ B ∈ S, |B|ᵥ
  -- Use Finset.sum_bij to establish bijection between indices and finset elements
  -- sum_bij: (i : α → β) (hi : ∀ a ∈ s, i a ∈ t) (h : ∀ a ∈ s, g (i a) = f a)
  --          (hg : ∀ b ∈ t, ∃ a ∈ s, i a = b) (hh : ∀ a₁ a₂ ∈ s, i a₁ = i a₂ → a₁ = a₂)
  refine Finset.sum_bij (fun n hn => S_list.get ⟨n, Finset.mem_range.mp hn⟩) ?_ ?_ ?_ ?_
  · -- hi: Image is in S
    intro n hn
    have hn_lt := Finset.mem_range.mp hn
    have : S_list.get ⟨n, hn_lt⟩ ∈ S_list := List.get_mem S_list ⟨n, hn_lt⟩
    exact Finset.mem_toList.mp this
  · -- i_inj: Injectivity
    intro n₁ hn₁ n₂ hn₂ heq
    have hn₁_lt := Finset.mem_range.mp hn₁
    have hn₂_lt := Finset.mem_range.mp hn₂
    -- List.get is injective when the list has no duplicates (which holds for Finset.toList)
    -- From heq: S_list[n₁] = S_list[n₂], and S_list.Nodup, deduce n₁ = n₂
    have h_nodup : S_list.Nodup := Finset.nodup_toList S
    -- Simplify heq to get S_list.get ⟨n₁, hn₁_lt⟩ = S_list.get ⟨n₂, hn₂_lt⟩
    have h_get_eq : S_list.get ⟨n₁, hn₁_lt⟩ = S_list.get ⟨n₂, hn₂_lt⟩ := by
      simp at heq
      exact heq
    -- Use nodup to show the indices are equal
    -- List.nodup_iff_injective_get: Nodup l ↔ Function.Injective l.get
    have h_inj : Function.Injective S_list.get := List.nodup_iff_injective_get.mp h_nodup
    -- Apply injectivity: S_list.get ⟨n₁, hn₁_lt⟩ = S_list.get ⟨n₂, hn₂_lt⟩ implies ⟨n₁, hn₁_lt⟩ = ⟨n₂, hn₂_lt⟩
    have h_idx_eq : (⟨n₁, hn₁_lt⟩ : Fin S_list.length) = ⟨n₂, hn₂_lt⟩ := h_inj h_get_eq
    exact congrArg Fin.val h_idx_eq
  · -- i_surj: Surjectivity
    intro b hb
    obtain ⟨i, hi⟩ := List.get_of_mem (Finset.mem_toList.mpr hb)
    -- hi : S.toList.get i = b, and S_list = S.toList, so S_list.get i = b
    -- We need to show (fun n hn ↦ S_list.get ⟨n, ⋯⟩) i.val ... = b
    -- Since i : Fin S_list.length, we have S_list.get ⟨i.val, i.isLt⟩ = S_list.get i = b
    have h_eq : (fun n hn => S_list.get ⟨n, Finset.mem_range.mp hn⟩) i.val (Finset.mem_range.mpr i.isLt) = b := by
      simp
      -- S_list = S.toList, so S_list.get i = S.toList.get i = b
      rw [←hi]
      rfl
    exact ⟨i.val, Finset.mem_range.mpr i.isLt, h_eq⟩
  · -- h: Function preserves summand
    intro n hn
    have hn_lt := Finset.mem_range.mp hn
    simp only [S_seq, dif_pos hn_lt]


-- For any bounded set, the Lebesgue outer measure is at most the Jordan outer measure.
theorem Lebesgue_outer_measure_le_Jordan {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E) : Lebesgue_outer_measure E ≤ Jordan_outer_measure E := by
  -- Strategy: Handle d = 0 separately using Lebesgue_outer_measure_of_dim_zero. For d > 0:
  -- Express Jordan outer measure as infimum over finite covers via Jordan_outer_eq.
  -- Show Lebesgue outer measure (infimum over countable covers) ≤ Jordan by proving
  -- Lebesgue ≤ each finite cover sum: convert finite cover S to countable sequence S_seq
  -- (enumerate via toList, pad with zeros), show S_seq is a countable cover with same sum,
  -- then apply infimum properties to conclude Lebesgue ≤ Jordan.

  by_cases hd : d = 0
  · subst hd
    -- Use the characterization of Lebesgue_outer_measure for d = 0
    rw [Lebesgue_outer_measure_of_dim_zero]
    by_cases hE_ne : E.Nonempty
    · -- Case: E is nonempty, so Lebesgue_outer_measure E = 1
      simp only [hE_ne, ↓reduceIte]
      -- Need to show (1 : EReal) ≤ ↑(Jordan_outer_measure E)
      -- Any elementary set containing nonempty E must be nonempty, hence has measure ≥ 1
      have h : (1 : ℝ) ≤ Jordan_outer_measure E := by
        unfold Jordan_outer_measure
        apply le_csInf
        · -- Show the set is nonempty
          obtain ⟨A, hA, hE_sub_A⟩ := IsElementary.contains_bounded hE
          exact ⟨hA.measure, A, hA, hE_sub_A, rfl⟩
        · -- Show 1 is a lower bound for all measures in the set
          intro m hm
          obtain ⟨A, hA, hE_sub_A, rfl⟩ := hm
          -- A contains E, which is nonempty, so A is nonempty
          have hA_ne : A.Nonempty := hE_ne.mono hE_sub_A
          -- In dimension 0, any nonempty elementary set has measure ≥ 1
          -- This is because elementary sets are finite unions of boxes, and each box has volume 1
          obtain ⟨S, hS_disj, hA_eq⟩ := hA.partition
          -- Find a nonempty box in the partition
          have : ∃ B ∈ S, B.toSet.Nonempty := by
            by_contra h
            push_neg at h
            -- h says: ∀ B, B ∈ S → B.toSet = ∅
            have hA_empty : A = ∅ := by
              rw [hA_eq]
              ext x
              simp only [Set.mem_iUnion, Set.mem_empty_iff_false, iff_false]
              intro ⟨B, hB, hx⟩
              rw [h B hB] at hx
              exact hx
            exact Set.Nonempty.ne_empty hA_ne hA_empty
          obtain ⟨B, hB_in_S, hB_ne⟩ := this
          -- All boxes in dimension 0 have volume 1
          have h_vol : |B|ᵥ = 1 := by
            unfold Box.volume
            have : Finset.univ = (∅ : Finset (Fin 0)) := by ext i; exact Fin.elim0 i
            rw [this]
            rfl
          -- The measure is the sum of volumes, which includes at least one box with volume 1
          have h_measure : hA.measure = ∑ B' ∈ S, |B'|ᵥ := hA.measure_eq hS_disj hA_eq
          -- Each box has volume ≥ 0 (as a product of nonnegative lengths)
          have h_vol_nonneg : ∀ B' : Box 0, 0 ≤ |B'|ᵥ := by
            intro B'
            unfold Box.volume
            apply Finset.prod_nonneg
            intro i _
            unfold BoundedInterval.length
            exact le_max_right _ _
          -- The sum includes B with volume 1, so the total is ≥ 1
          calc hA.measure
            = ∑ B' ∈ S, |B'|ᵥ := h_measure
            _ ≥ |B|ᵥ := by
                classical
                rw [←Finset.sum_erase_add _ _ hB_in_S]
                simp only [le_add_iff_nonneg_left]
                apply Finset.sum_nonneg
                intro B' _
                exact h_vol_nonneg B'
            _ = 1 := h_vol
      exact EReal.coe_le_coe_iff.mpr h
    · -- Case: E is empty, so Lebesgue_outer_measure E = 0
      simp only [hE_ne, ↓reduceIte]
      -- Need to show (0 : EReal) ≤ ↑(Jordan_outer_measure E), which follows from nonnegativity
      exact EReal.coe_nonneg.mpr (Jordan_outer_measure_nonneg E)

  have hd_pos : 0 < d := Nat.pos_of_ne_zero hd

  -- Rewrite Jordan outer measure using Jordan_outer_eq
  rw [Jordan_outer_eq hE]
  unfold Lebesgue_outer_measure

  -- Show sInf (countable covers) ≤ (finite cover sum : EReal) for all finite covers
  -- This implies sInf (countable) ≤ sInf (finite)
  have h_le : ∀ m ∈ (fun S ↦ (∑ B ∈ S, |B|ᵥ : ℝ)) '' {S | E ⊆ ⋃ B ∈ S, B.toSet},
      sInf { V | ∃ (X : Set ℕ) (S: X → Box d), E ⊆ ⋃ n, (S n).toSet ∧ V = ∑' n, (S n).volume.toEReal } ≤ (m : EReal) := by
    intro m hm
    obtain ⟨S, hS_cover, rfl⟩ := hm

    -- Convert finite cover S to countable sequence S_seq
    classical
    let S_list := S.toList
    let zero_box : Box d := ⟨fun i => if i.val = 0 then ∅ else BoundedInterval.Icc 0 0⟩
    have h_card_eq : S_list.length = S.card := Finset.length_toList S
    let S_seq : ℕ → Box d := fun n =>
      if h : n < S_list.length then S_list.get ⟨n, h⟩ else zero_box

    -- Step 1: Covering is preserved
    have h_cover : E ⊆ ⋃ n, (S_seq n).toSet := by
      intro x hx
      -- Need to show: x ∈ ⋃ n, (S_seq n).toSet, i.e., ∃ n, x ∈ (S_seq n).toSet
      simp only [Set.mem_iUnion]
      -- hS_cover : E ⊆ ⋃ B ∈ S, B.toSet, so x is in some box B ∈ S
      have : x ∈ ⋃ B ∈ S, B.toSet := hS_cover hx
      simp only [Set.mem_iUnion] at this
      obtain ⟨B, hB_in_S, hx_in_B⟩ := this
      -- Since B ∈ S, it appears in S_list at some index
      have hB_in_list : B ∈ S_list := Finset.mem_toList.mpr hB_in_S
      -- Get the index i where S_list contains B
      obtain ⟨i, hi_eq⟩ := List.get_of_mem hB_in_list
      -- Provide i.val as the witness
      use i.val
      -- S_seq i.val = S_list.get ⟨i.val, i.isLt⟩ = B by hi_eq
      simp only [S_seq]
      have hi_val_lt : i.val < S_list.length := i.isLt
      rw [dif_pos hi_val_lt]
      -- Show ⟨i.val, hi_val_lt⟩ = i so we can use hi_eq
      have : (⟨i.val, hi_val_lt⟩ : Fin S_list.length) = i := Fin.ext rfl
      rw [this, hi_eq]
      exact hx_in_B

    -- Step 2: Sum equality via tsum_eq_sum
    have h_sum_eq : ∑' n, (S_seq n).volume.toEReal = (∑ B ∈ S, |B|ᵥ).toEReal := by
      exact tsum_volume_finset_eq hd_pos S

    -- Step 3: Apply infimum property
    calc sInf { V | ∃ (X : Set ℕ) (S: X → Box d), E ⊆ ⋃ n, (S n).toSet ∧ V = ∑' n, (S n).volume.toEReal }
        ≤ ∑' n, (S_seq n).volume.toEReal := by
            apply sInf_le
            show ∑' n, (S_seq n).volume.toEReal ∈ { V | ∃ (X : Set ℕ) (S: X → Box d), E ⊆ ⋃ n, (S n).toSet ∧ V = ∑' n, (S n).volume.toEReal }
            use Set.univ, fun (n : Set.univ) => S_seq n.val
            constructor
            · -- Show E ⊆ ⋃ n, (S n).toSet
              convert h_cover using 2
              ext x
              simp
            · -- Show V = ∑' n, (S n).volume.toEReal
              exact ((Equiv.Set.univ ℕ).tsum_eq (fun n => (S_seq n).volume.toEReal)).symm
        _ = (∑ B ∈ S, |B|ᵥ).toEReal := h_sum_eq

  -- Use h_le to show sInf (countable) ≤ sInf (finite)
  -- We have: ∀ m ∈ finite_set, Lebesgue_sInf ≤ ↑m
  -- We need to show: Lebesgue_sInf ≤ ↑(sInf finite_set)
  -- Since finite_set is nonempty and sInf finite_set is the greatest lower bound,
  -- it suffices to show Lebesgue_sInf ≤ ↑m for all m in finite_set
  have h_nonempty : ((fun S ↦ (∑ B ∈ S, |B|ᵥ : ℝ)) '' {S | E ⊆ ⋃ B ∈ S, B.toSet}).Nonempty := by
    obtain ⟨A, hA, hE_sub_A⟩ := IsElementary.contains_bounded hE
    obtain ⟨T, hT_disj, hA_eq⟩ := hA.partition
    use (∑ B ∈ T, |B|ᵥ : ℝ)
    use T
    simp
    intro a ha
    have : a ∈ A := hE_sub_A ha
    rw [hA_eq] at this
    exact this
  -- The goal is to show: Lebesgue_sInf ≤ ↑(sInf(finite))
  -- We have h_le showing: ∀ m ∈ finite_set, Lebesgue_sInf ≤ ↑m
  -- Key insight: ↑(sInf finite_set) = sInf (↑ '' finite_set) (monotone coercion preserves sInf)
  -- Then use le_sInf: if a ≤ b for all b ∈ s, then a ≤ sInf s

  -- First, show that sInf(countable) ≤ sInf(↑ '' finite_set)
  have h_le_coe : sInf { V | ∃ (X : Set ℕ) (S: X → Box d), E ⊆ ⋃ n, (S n).toSet ∧ V = ∑' n, (S n).volume.toEReal }
      ≤ sInf ((fun m : ℝ => (m : EReal)) '' ((fun S ↦ ∑ B ∈ S, |B|ᵥ) '' {S | E ⊆ ⋃ B ∈ S, B.toSet})) := by
    apply le_sInf
    intro b hb
    obtain ⟨m, hm_in, rfl⟩ := hb
    exact h_le m hm_in

  -- Now show that sInf(↑ '' finite_set) = ↑(sInf finite_set) and apply h_le_coe
  -- The set of volumes is bounded below by 0
  have h_bdd : BddBelow ((fun S ↦ ∑ B ∈ S, |B|ᵥ) '' {S | E ⊆ ⋃ B ∈ S, B.toSet}) := by
    use 0
    intro m hm
    obtain ⟨S, _, rfl⟩ := hm
    apply Finset.sum_nonneg
    intro B _
    -- Box volume is a product of interval lengths, which are nonnegative by definition
    simp only [Box.volume]
    apply Finset.prod_nonneg
    intro i _
    simp [BoundedInterval.length]

  -- Apply transitivity: Lebesgue_sInf ≤ sInf(↑ '' finite) = ↑(sInf finite)
  calc sInf { V | ∃ (X : Set ℕ) (S: X → Box d), E ⊆ ⋃ n, (S n).toSet ∧ V = ∑' n, (S n).volume.toEReal }
      ≤ sInf ((fun m : ℝ => (m : EReal)) '' ((fun S ↦ ∑ B ∈ S, |B|ᵥ) '' {S | E ⊆ ⋃ B ∈ S, B.toSet})) := h_le_coe
      _ = ↑(sInf ((fun S ↦ ∑ B ∈ S, |B|ᵥ) '' {S | E ⊆ ⋃ B ∈ S, B.toSet})) := by
          -- Use helper lemma: EReal.sInf_image_coe
          exact EReal.sInf_image_coe h_nonempty h_bdd

/-- Example 1.2.1.  With the junk value conventions of this companion, the Jordan outer measure of the rationals is zero rather than infinite (I think). -/
-- The Jordan outer measure of the rationals in a bounded interval equals the interval length.
example {R:ℝ} (hR: 0 < R) : Jordan_outer_measure (Real.equiv_EuclideanSpace' '' (Set.Icc (-R) R ∩ Set.range (fun q:ℚ ↦ (q:ℝ)))) = 2*R := by
  set Q' := Real.equiv_EuclideanSpace' '' (Set.Icc (-R) R ∩ Set.range (fun q:ℚ ↦ (q:ℝ))) with hQ'
  set B := (BoundedInterval.Icc (-R : ℝ) R : Box 1) with hB
  have h_vol : |B|ᵥ = 2*R := by
    rw [hB, Box.volume_of_interval]
    unfold BoundedInterval.length
    have hpos : 0 < 2*R := mul_pos (by norm_num : (0:ℝ) < 2) hR
    simp [show R - (-R : ℝ) = 2*R by ring, hpos.le]
  have hQ'_subset_B : Q' ⊆ B.toSet := by
    rw [hQ', BoundedInterval.coe_of_box]
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    simpa using ⟨x, hx.1, rfl⟩
  have hB_bounded : Bornology.IsBounded B.toSet :=
    IsElementary.isBounded (IsElementary.box B)
  apply le_antisymm
  · calc
      Jordan_outer_measure Q' ≤ Jordan_outer_measure B.toSet :=
        Jordan_outer_measure_mono_of_subset hQ'_subset_B hB_bounded
      _ = |B|ᵥ := Jordan_outer_measure_of_box B
      _ = 2*R := h_vol
  · have h_2R_le_outer : 2*R ≤ Jordan_outer_measure Q' := by
      rw [Jordan_outer_measure]
      apply le_csInf
      · have hQ'_bounded : Bornology.IsBounded Q' :=
          Bornology.IsBounded.subset hB_bounded hQ'_subset_B
        obtain ⟨A, hA, hQ'_sub_A⟩ := IsElementary.contains_bounded hQ'_bounded
        exact ⟨hA.measure, A, hA, hQ'_sub_A, rfl⟩
      · intro m hm
        obtain ⟨A, hA, hQ'_sub_A, rfl⟩ := hm
        have h_measure_ge_vol : hA.measure ≥ |B|ᵥ := by
          let A' := A ∩ B.toSet
          have hA'_elem : IsElementary A' := IsElementary.inter hA (IsElementary.box B)
          let G := B.toSet \ A'
          have hG_elem : IsElementary G := IsElementary.sdiff (IsElementary.box B) hA'_elem
          have hQ'_sub_A' : Q' ⊆ A' := by
            intro x hx
            exact ⟨hQ'_sub_A hx, hQ'_subset_B hx⟩
          have h_disj : Disjoint A' G := by
            rw [Set.disjoint_iff]
            intro x ⟨hx_A', hx_G⟩
            rcases hx_G with ⟨hx_B, hx_not_A'⟩
            exact hx_not_A' hx_A'
          have h_union_eq : A' ∪ G = B.toSet := by
            ext x; constructor
            · rintro (hx_A' | ⟨hx_B, _⟩); exact hx_A'.2; exact hx_B
            · intro hx_B
              by_cases hx_A' : x ∈ A'; exact Or.inl hx_A'; exact Or.inr ⟨hx_B, hx_A'⟩
          have h_union_meas : (hA'_elem.union hG_elem).measure = hA'_elem.measure + hG_elem.measure :=
            IsElementary.measure_of_disjUnion hA'_elem hG_elem h_disj
          have h_union_eq_meas : (hA'_elem.union hG_elem).measure = |B|ᵥ := by
            calc
              (hA'_elem.union hG_elem).measure = (IsElementary.box B).measure :=
                IsElementary.measure_eq_of_set_eq (hA'_elem.union hG_elem) (IsElementary.box B) h_union_eq
              _ = |B|ᵥ := IsElementary.measure_of_box B
          have h_eq : hA'_elem.measure + hG_elem.measure = |B|ᵥ := by
            linarith
          have hG_measure_zero : hG_elem.measure = 0 := by
            have hG_no_rationals : ∀ q : ℚ, Real.equiv_EuclideanSpace' (q : ℝ) ∉ G := by
              intro q hq
              rcases hq with ⟨hq_B, hq_not_A'⟩
              have hq_Q' : Real.equiv_EuclideanSpace' (q : ℝ) ∈ Q' := by
                have hq_Icc : (q : ℝ) ∈ Set.Icc (-R : ℝ) R := by
                  rw [BoundedInterval.coe_of_box] at hq_B
                  rcases hq_B with ⟨y, hy, hy'⟩
                  have h_y_eq_q : y = (q : ℝ) :=
                    Real.equiv_EuclideanSpace'.injective hy'
                  rw [h_y_eq_q] at hy
                  exact hy
                rw [hQ', Set.mem_image]
                refine ⟨(q : ℝ), ⟨hq_Icc, ⟨q, rfl⟩⟩, rfl⟩
              have hq_A' : Real.equiv_EuclideanSpace' (q : ℝ) ∈ A' := hQ'_sub_A' hq_Q'
              exact hq_not_A' hq_A'
            have box_no_rational_vol_zero (B' : Box 1) (h_no_q : ∀ q : ℚ, Real.equiv_EuclideanSpace' (q : ℝ) ∉ B'.toSet) : |B'|ᵥ = 0 := by
              let I := B'.side 0
              have hB'_eq : B' = (I : Box 1) := by
                ext i; fin_cases i; rfl
              rw [hB'_eq, Box.volume_of_interval]
              unfold BoundedInterval.length
              by_cases h_lt : I.a < I.b
              · exfalso
                obtain ⟨q, hq_a, hq_b⟩ := exists_rat_btwn h_lt
                have hq_mem : (q : ℝ) ∈ (I : Set ℝ) := by
                  match I with
                  | BoundedInterval.Ioo a b =>
                    simpa [BoundedInterval.toSet] using ⟨hq_a, hq_b⟩
                  | BoundedInterval.Icc a b =>
                    simpa [BoundedInterval.toSet] using ⟨by linarith, by linarith⟩
                  | BoundedInterval.Ioc a b =>
                    simpa [BoundedInterval.toSet] using ⟨by linarith, hq_b.le⟩
                  | BoundedInterval.Ico a b =>
                    simpa [BoundedInterval.toSet] using ⟨hq_a.le, by linarith⟩
                have hq_B' : Real.equiv_EuclideanSpace' (q : ℝ) ∈ B'.toSet := by
                  rw [hB'_eq, BoundedInterval.coe_of_box]
                  simpa using ⟨(q : ℝ), hq_mem, rfl⟩
                exact h_no_q q hq_B'
              · simp [not_lt.mp h_lt]
            classical
            obtain ⟨T, hT_disj, hG_eq⟩ := hG_elem.partition
            have hG_eq_measure : hG_elem.measure = ∑ B' ∈ T, |B'|ᵥ :=
              hG_elem.measure_eq hT_disj hG_eq
            have h_vol_zero : ∀ B' ∈ T, |B'|ᵥ = 0 := by
              intro B' hB'
              apply box_no_rational_vol_zero B'
              intro q hq
              have hq_G : Real.equiv_EuclideanSpace' (q : ℝ) ∈ G := by
                rw [hG_eq]
                exact Set.mem_biUnion hB' hq
              exact hG_no_rationals q hq_G
            rw [hG_eq_measure]
            apply Finset.sum_eq_zero
            intro B' hB'
            exact h_vol_zero B' hB'
          have hA'_meas_eq : hA'_elem.measure = |B|ᵥ := by
            linarith
          have h_mono : hA'_elem.measure ≤ hA.measure :=
            IsElementary.measure_mono hA'_elem hA (Set.inter_subset_left (s := A) (t := B.toSet))
          calc |B|ᵥ = hA'_elem.measure := by symm; exact hA'_meas_eq
            _ ≤ hA.measure := h_mono
        calc 2*R = |B|ᵥ := by symm; exact h_vol
          _ ≤ hA.measure := h_measure_ge_vol
    exact h_2R_le_outer

-- Any countable set (in positive dimension) has Lebesgue outer measure zero.
theorem Countable.Lebesgue_measure {d:ℕ} (hd : 0 < d) {E: Set (EuclideanSpace' d)} (hE: E.Countable) : Lebesgue_outer_measure E = 0 := by
  unfold Lebesgue_outer_measure
  -- Strategy: Cover E with singleton boxes, each with volume 0

  -- Get an enumeration: E ⊆ range f for some f : ℕ → EuclideanSpace' d
  haveI : Nonempty (EuclideanSpace' d) := inferInstance
  obtain ⟨f, hf⟩ := Set.countable_iff_exists_subset_range.mp hE

  -- Construct singleton box for each f(n)
  let singleton_box : ℕ → Box d := fun n => ⟨fun i => BoundedInterval.Icc (f n i) (f n i)⟩

  -- Show E is covered by these boxes
  have h_cover : E ⊆ ⋃ n, (singleton_box n).toSet := by
    calc E ⊆ Set.range f := hf
       _ ⊆ ⋃ n, (singleton_box n).toSet := by
         intro x hx
         obtain ⟨n, rfl⟩ := hx
         simp [Set.mem_iUnion]
         use n
         intro i
         simp [BoundedInterval.toSet]
         exact ⟨le_refl _, le_refl _⟩

  -- Each singleton box has volume 0
  have h_vol : ∀ n, (singleton_box n).volume = 0 := by
    intro n
    exact Box.volume_singleton hd (f n)

  -- Sum of volumes is 0
  have h_sum : ∑' n, (singleton_box n).volume.toEReal = 0 := by
    simp only [h_vol]
    simp [EReal.coe_zero, tsum_zero]

  -- Apply this cover to show the infimum is at most 0
  have h_le : sInf { V | ∃ (X : Set ℕ) (S: X → Box d), E ⊆ ⋃ n, (S n).toSet ∧ V = ∑' n, (S n).volume.toEReal } ≤ 0 := by
    apply csInf_le
    · -- Show the set is bounded below by 0
      use 0
      intro V ⟨X, S, _, hV⟩
      rw [hV]
      -- Box volumes are non-negative, so their sum is non-negative
      apply tsum_nonneg
      intro n
      exact EReal.coe_nonneg.mpr (by
        unfold Box.volume
        apply Finset.prod_nonneg
        intro i _
        unfold BoundedInterval.length
        exact le_max_right _ _)
    · -- Show 0 is in the set (via our singleton cover)
      use Set.univ
      use fun (n : Set.univ) => singleton_box n.val
      refine ⟨?_, ?_⟩
      · -- E ⊆ ⋃ n : Set.univ, (singleton_box n.val).toSet
        intro x hx
        simp only [Set.mem_iUnion]
        have : x ∈ ⋃ n, (singleton_box n).toSet := h_cover hx
        simp only [Set.mem_iUnion] at this
        obtain ⟨n, hn⟩ := this
        exact ⟨⟨n, Set.mem_univ n⟩, hn⟩
      · -- ∑' n : Set.univ, (singleton_box n.val).volume.toEReal = 0
        simp only [h_vol, EReal.coe_zero, tsum_zero]

  -- Show the infimum is at least 0
  have h_ge : 0 ≤ sInf { V | ∃ (X : Set ℕ) (S: X → Box d), E ⊆ ⋃ n, (S n).toSet ∧ V = ∑' n, (S n).volume.toEReal } := by
    apply le_csInf
    · -- Show the set is nonempty (we have the singleton cover)
      use 0
      use Set.univ
      use fun (n : Set.univ) => singleton_box n.val
      exact ⟨h_cover.trans (by intro x; simp only [Set.mem_iUnion]; intro ⟨n, hn⟩; exact ⟨⟨n, Set.mem_univ n⟩, hn⟩), by simp only [h_vol, EReal.coe_zero, tsum_zero]⟩
    · -- Show all elements are ≥ 0
      intro V ⟨X, S, _, hV⟩
      rw [hV]
      apply tsum_nonneg
      intro n
      exact EReal.coe_nonneg.mpr (by
        unfold Box.volume
        apply Finset.prod_nonneg
        intro i _
        unfold BoundedInterval.length
        exact le_max_right _ _)

  exact le_antisymm h_le h_ge

-- The Lebesgue outer measure of the rationals in a bounded interval is zero.
example {R:ℝ} : Lebesgue_outer_measure (Real.equiv_EuclideanSpace' '' (Set.Icc (-R) R ∩ Set.range (fun q:ℚ ↦ (q:ℝ)))) = 0 := by
  apply Countable.Lebesgue_measure (by omega : 0 < 1)
  apply Set.Countable.image
  -- The intersection is countable because the right side is countable
  have : (Set.Icc (-R) R ∩ Set.range (fun q:ℚ ↦ (q:ℝ))).Countable := by
    apply Set.Countable.mono (Set.inter_subset_right)
    exact Set.countable_range (fun q:ℚ => (q:ℝ))
  exact this

-- The Lebesgue outer measure of all rationals is zero.
example : Lebesgue_outer_measure (Real.equiv_EuclideanSpace' '' (Set.range (fun q:ℚ ↦ (q:ℝ)))) = 0 := by
  apply Countable.Lebesgue_measure (by omega : 0 < 1)
  apply Set.Countable.image
  exact Set.countable_range (fun q:ℚ => (q:ℝ))

-- A set is Lebesgue measurable if it can be approximated arbitrarily well from the outside by open sets.
def LebesgueMeasurable {d:ℕ} (E: Set (EuclideanSpace' d)) : Prop :=
  ∀ ε > 0, ∃ U: Set (EuclideanSpace' d), IsOpen U ∧ E ⊆ U ∧ Lebesgue_outer_measure (U \ E) ≤ ε

-- The Lebesgue measure of a set (equals its Lebesgue outer measure).
noncomputable def Lebesgue_measure {d:ℕ} (E: Set (EuclideanSpace' d)) : EReal := Lebesgue_outer_measure E
