import Mathlib.Tactic
import Analysis.Section_9_6
import Analysis.Section_9_7

/-!
# Analysis I, Section 9.8: Monotonic functions

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Review of Mathlib monotonicity concepts.
-/

namespace Chapter9

/-- Definition 9.8.1 -/
theorem MonotoneOn.iff {X: Set ℝ} (f: ℝ → ℝ) : MonotoneOn f X  ↔ ∀ x ∈ X, ∀ y ∈ X, y > x → f y ≥ f x := by
  constructor
  . intros; solve_by_elim [le_of_lt]
  intro _ _ _ _ _ hxy; obtain hxy | rfl := le_iff_lt_or_eq.mp hxy
  . solve_by_elim
  simp

theorem StrictMono.iff {X: Set ℝ} (f: ℝ → ℝ) : StrictMonoOn f X  ↔ ∀ x ∈ X, ∀ y ∈ X, y > x → f y > f x := by
  constructor <;> intros <;> solve_by_elim

theorem AntitoneOn.iff {X: Set ℝ} (f: ℝ → ℝ) : AntitoneOn f X  ↔ ∀ x ∈ X, ∀ y ∈ X, y > x → f y ≤ f x := by
  constructor
  . intros; solve_by_elim [le_of_lt]
  intro _ _ _ _ _ hxy; obtain hxy | rfl := le_iff_lt_or_eq.mp hxy
  . solve_by_elim
  simp

theorem StrictAntitone.iff {X: Set ℝ} (f: ℝ → ℝ) : StrictAntiOn f X  ↔ ∀ x ∈ X, ∀ y ∈ X, y > x → f y < f x := by
  constructor <;> intros <;> solve_by_elim

/-- Examples 9.8.2 -/
example : StrictMonoOn (fun x:ℝ ↦ x^2) (.Ici 0) := by
  intro x hx y hy hxy
  have hx_nonneg : 0 ≤ x := hx
  have hy_nonneg : 0 ≤ y := hy
  nlinarith

example : StrictAntiOn (fun x:ℝ ↦ x^2) (.Iic 0) := by
  intro x hx y hy hxy
  have hx_nonpos : x ≤ 0 := hx
  have hy_nonpos : y ≤ 0 := hy
  nlinarith

example : ¬ MonotoneOn (fun x:ℝ ↦ x^2) .univ := by
  intro h
  have h' := (MonotoneOn.iff _).mp h (-1) (Set.mem_univ _) 0 (Set.mem_univ _) (by norm_num : (0 : ℝ) > (-1 : ℝ))
  norm_num at h'

example : ¬ AntitoneOn (fun x:ℝ ↦ x^2) .univ := by
  intro h
  have h' := (AntitoneOn.iff _).mp h 0 (Set.mem_univ _) 1 (Set.mem_univ _) (by norm_num : (1 : ℝ) > (0 : ℝ))
  norm_num at h'

example {X:Set ℝ} {f:ℝ → ℝ} (hf: StrictMonoOn f X) : MonotoneOn f X := by
  intro a ha b hb hab
  rcases hab.eq_or_lt with (rfl | hlt)
  · rfl
  · exact le_of_lt (hf (a := a) ha (b := b) hb hlt)

example (X:Set ℝ) : MonotoneOn (fun _:ℝ ↦ (6:ℝ)) X := by
  intro a ha b hb hab; simp

example (X:Set ℝ) : AntitoneOn (fun _:ℝ ↦ (6:ℝ)) X := by
  intro a ha b hb hab; simp

example {X:Set ℝ} (hX : Set.Nontrivial X) : ¬ StrictMonoOn (fun _:ℝ ↦ (6:ℝ)) X := by
  rcases hX with ⟨x, hx, y, hy, hne⟩
  have hxy : x < y ∨ y < x := by
    by_cases h : x < y; · left; exact h
    · right; have hyx : y ≤ x := le_of_not_gt h; exact lt_of_le_of_ne hyx hne.symm
  rcases hxy with (hxy | hyx)
  · intro h; have := h (a := x) hx (b := y) hy hxy; norm_num at this
  · intro h; have := h (a := y) hy (b := x) hx hyx; norm_num at this

example (X:Set ℝ) (hX : Set.Nontrivial X) : ¬ StrictAntiOn (fun _:ℝ ↦ (6:ℝ)) X := by
  rcases hX with ⟨x, hx, y, hy, hne⟩
  have hxy : x < y ∨ y < x := by
    by_cases h : x < y; · left; exact h
    · right; have hyx : y ≤ x := le_of_not_gt h; exact lt_of_le_of_ne hyx hne.symm
  rcases hxy with (hxy | hyx)
  · intro h; have := h (a := x) hx (b := y) hy hxy; norm_num at this
  · intro h; have := h (a := y) hy (b := x) hx hyx; norm_num at this

example : ∃ (X:Set ℝ) (f:ℝ → ℝ), ContinuousOn f X ∧ ¬ MonotoneOn f X ∧ ¬ AntitoneOn f X := by
  refine ⟨Set.univ, fun x : ℝ ↦ x^2, ?_, ?_, ?_⟩
  · exact (continuous_id.pow 2).continuousOn
  · intro h
    have h' := (MonotoneOn.iff _).mp h (-1) (Set.mem_univ _) 0 (Set.mem_univ _) (by norm_num : (0 : ℝ) > (-1 : ℝ))
    norm_num at h'
  · intro h
    have h' := (AntitoneOn.iff _).mp h 0 (Set.mem_univ _) 1 (Set.mem_univ _) (by norm_num : (1 : ℝ) > (0 : ℝ))
    norm_num at h'

example : ∃ (X:Set ℝ) (f:ℝ → ℝ), MonotoneOn f X ∧ ¬ ContinuousOn f X := by
  let f : ℝ → ℝ := fun x ↦ if x ≤ 0 then (0 : ℝ) else 1
  refine ⟨Set.univ, f, ?_, ?_⟩
  · rw [MonotoneOn.iff]
    intro x hx y hy hyx
    by_cases hx0 : x ≤ 0
    · simp [f, hx0]
      by_cases hy0 : y ≤ 0
      · simp [hy0]
      · simp [hy0]
    · have hxpos : 0 < x := by linarith
      have hypos : 0 < y := by linarith
      simp [f, hx0, show ¬ y ≤ 0 from by linarith]
  · intro h
    have hcont : ContinuousAt f 0 := by
      rw [continuousOn_univ] at h
      exact h.continuousAt
    have hseq : Filter.atTop.Tendsto (fun n : ℕ ↦ (1 : ℝ) / ((n : ℝ) + 1)) (nhds (0 : ℝ)) := by
      have h1 : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) Filter.atTop Filter.atTop :=
        Filter.tendsto_atTop_add_const_right Filter.atTop (1 : ℝ) (tendsto_natCast_atTop_atTop (R := ℝ))
      have h2 : Filter.Tendsto (fun r : ℝ ↦ 1 / r) Filter.atTop (nhds (0 : ℝ)) := by
        simpa [div_eq_inv_mul] using (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (1 : ℝ)
      exact h2.comp h1
    have hfa : ∀ n : ℕ, f ((1 : ℝ) / ((n : ℝ) + 1)) = 1 := by
      intro n
      have htemp : (0 : ℝ) < (n : ℝ) + 1 := by
        have h : (0 : ℝ) < (n.succ : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos n)
        simpa [Nat.cast_succ] using h
      have hpos : (0 : ℝ) < (1 : ℝ) / ((n : ℝ) + 1) := by
        apply div_pos
        · norm_num
        · exact htemp
      have h_not_le : ¬ (1 : ℝ) / ((n : ℝ) + 1) ≤ (0 : ℝ) := by linarith
      dsimp [f]
      rw [if_neg h_not_le]
    have htendsto : Filter.atTop.Tendsto (fun n : ℕ ↦ f ((1 : ℝ) / ((n : ℝ) + 1))) (nhds (f 0)) :=
      hcont.tendsto.comp hseq
    have hft0 : f 0 = (0 : ℝ) := by simp [f]
    have htemp : Filter.atTop.Tendsto (fun n : ℕ ↦ (1 : ℝ)) (nhds (f 0)) :=
      (Filter.Tendsto.congr (fun n => hfa n)) htendsto
    have htendsto' : Filter.atTop.Tendsto (fun _ : ℕ ↦ (1 : ℝ)) (nhds (0 : ℝ)) := by
      rw [hft0] at htemp
      exact htemp
    have h1tendsto : Filter.atTop.Tendsto (fun _ : ℕ ↦ (1 : ℝ)) (nhds (1 : ℝ)) := tendsto_const_nhds
    have h01 : (0 : ℝ) = (1 : ℝ) := tendsto_nhds_unique htendsto' h1tendsto
    norm_num at h01

/-- Proposition 9.8.3 / Exercise 9.8.4 -/
theorem MonotoneOn.exist_inverse {a b:ℝ} (h: a < b) (f: ℝ → ℝ) (hcont: ContinuousOn f (.Icc a b)) (hmono: StrictMonoOn f (.Icc a b)) :
  f '' (.Icc a b) = .Icc (f a) (f b) ∧
  ∃ finv: ℝ → ℝ, ContinuousOn finv (.Icc (f a) (f b)) ∧ StrictMonoOn finv (.Icc (f a) (f b)) ∧
  finv '' (.Icc (f a) (f b)) = .Icc a b ∧
  (∀ x ∈ Set.Icc a b, finv (f x) = x) ∧
  ∀ y ∈ Set.Icc (f a) (f b), f (finv y) = y
   := by
  have ha_mem : a ∈ Set.Icc a b := Set.left_mem_Icc.mpr (le_of_lt h)
  have hb_mem : b ∈ Set.Icc a b := Set.right_mem_Icc.mpr (le_of_lt h)
  have h_image : f '' (.Icc a b) = .Icc (f a) (f b) := by
    ext y; constructor
    · rintro ⟨x, hx, rfl⟩
      have hx1 : a ≤ x := hx.1
      have hx2 : x ≤ b := hx.2
      have h_fa_fx : f a ≤ f x := by
        by_cases h_eq : a = x
        · subst h_eq; rfl
        · have h_lt : a < x := lt_of_le_of_ne hx1 h_eq
          exact le_of_lt (hmono (a := a) ha_mem (b := x) hx h_lt)
      have h_fx_fb : f x ≤ f b := by
        by_cases h_eq : x = b
        · subst h_eq; rfl
        · have h_lt : x < b := lt_of_le_of_ne hx2 h_eq
          exact le_of_lt (hmono (a := x) hx (b := b) hb_mem h_lt)
      exact ⟨h_fa_fx, h_fx_fb⟩
    · intro hy
      rcases hy with ⟨h_fa_y, hy_fb⟩
      have hy_mem : y ∈ Set.Icc (f a) (f b) := ⟨h_fa_y, hy_fb⟩
      rcases intermediate_value h hcont (Or.inl hy_mem) with ⟨x, hx, hx_eq⟩
      exact ⟨x, hx, hx_eq⟩
  have h_unique (y : ℝ) (hy : y ∈ Set.Icc (f a) (f b)) : ∃! x, x ∈ Set.Icc a b ∧ f x = y := by
    rcases intermediate_value h hcont (Or.inl hy) with ⟨x, hx, hx_eq⟩
    refine ⟨x, ⟨hx, hx_eq⟩, ?_⟩
    intro z ⟨hz, hz_eq⟩
    by_contra! hne
    have h_or : z < x ∨ x < z := by
      by_cases h' : z < x; · left; exact h'
      · right; have hx_le_z : x ≤ z := le_of_not_gt h'
        exact lt_of_le_of_ne hx_le_z hne.symm
    rcases h_or with (hlt | hlt)
    · have := hmono (a := z) hz (b := x) hx hlt
      rw [hz_eq, hx_eq] at this
      linarith
    · have := hmono (a := x) hx (b := z) hz hlt
      rw [hz_eq, hx_eq] at this
      linarith
  set finv : ℝ → ℝ := fun y ↦ if h : y ∈ Set.Icc (f a) (f b) then (h_unique y h).choose else a with hfinv
  have hfinv_spec (y : ℝ) (hy : y ∈ Set.Icc (f a) (f b)) : finv y ∈ Set.Icc a b ∧ f (finv y) = y := by
    dsimp [finv]
    simp [hy]
    have h_choose_spec := (h_unique y hy).choose_spec
    rcases h_choose_spec with ⟨hP, h_uniq⟩
    simpa using hP
  have hfinv_f (x : ℝ) (hx : x ∈ Set.Icc a b) : finv (f x) = x := by
    have hfx_mem : f x ∈ Set.Icc (f a) (f b) := by
      rw [← h_image]
      exact Set.mem_image_of_mem f hx
    have h_spec := (h_unique (f x) hfx_mem).choose_spec
    rcases h_spec with ⟨⟨h_mem, h_f_eq⟩, h_uniq⟩
    have h_finv_eq : finv (f x) = (h_unique (f x) hfx_mem).choose := by
      dsimp [finv]; simp [hfx_mem]
    rw [h_finv_eq]
    exact (h_uniq x ⟨hx, rfl⟩).symm
  have h_finv_strict_mono : StrictMonoOn finv (.Icc (f a) (f b)) := by
    intro y₁ hy₁ y₂ hy₂ hlt
    have hx₁ := (hfinv_spec y₁ hy₁).1
    have hx₂ := (hfinv_spec y₂ hy₂).1
    have h_fx₁ : f (finv y₁) = y₁ := (hfinv_spec y₁ hy₁).2
    have h_fx₂ : f (finv y₂) = y₂ := (hfinv_spec y₂ hy₂).2
    by_contra! hle
    rcases hle.lt_or_eq with (h_lt | h_eq)
    · have := hmono (a := finv y₂) hx₂ (b := finv y₁) hx₁ h_lt
      rw [h_fx₂, h_fx₁] at this
      linarith
    · rw [h_eq] at h_fx₂
      rw [h_fx₁] at h_fx₂
      linarith
  have h_finv_image : finv '' (.Icc (f a) (f b)) = .Icc a b := by
    ext x; constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hfinv_spec y hy).1
    · intro hx
      have hfx_mem : f x ∈ Set.Icc (f a) (f b) := by
        rw [← h_image]
        exact Set.mem_image_of_mem f hx
      refine ⟨f x, hfx_mem, hfinv_f x hx⟩
  have h_finv_cont : ContinuousOn finv (.Icc (f a) (f b)) := by
    rw [ContinuousOn.eq_1]
    intro y₀ hy₀
    rw [ContinuousWithinAt.iff, Convergesto.iff_conv]
    intro a_seq ha_seq hconv
    set x₀ := finv y₀ with hx₀
    set x_seq : ℕ → ℝ := fun n ↦ finv (a_seq n) with hx_seq
    have hx_mem (n : ℕ) : x_seq n ∈ Set.Icc a b := by
      dsimp [x_seq]
      exact (hfinv_spec (a_seq n) (ha_seq n)).1
    have hx_bdd : Bornology.IsBounded (Set.Icc a b) := isCompact_Icc.isBounded
    have hx_closed : IsClosed (Set.Icc a b) := isClosed_Icc
    have hx₀_mem : x₀ ∈ Set.Icc a b := (hfinv_spec y₀ hy₀).1
    have h_f_x₀_eq_y₀ : f x₀ = y₀ := (hfinv_spec y₀ hy₀).2
    have h_f_x_eq_a : ∀ n, f (x_seq n) = a_seq n := by
      intro n; dsimp [x_seq]; exact (hfinv_spec (a_seq n) (ha_seq n)).2
    -- Prove that every convergent subsequence of x_seq converges to x₀
    have h_subseq_limit (φ : ℕ → ℕ) (hφ_mono : StrictMono φ) (L : ℝ) (hL : L ∈ Set.Icc a b)
      (hconv_x : Filter.atTop.Tendsto (fun j : ℕ ↦ x_seq (φ j)) (nhds L)) : L = x₀ := by
      have hconv_x_within : Filter.atTop.Tendsto (fun j : ℕ ↦ x_seq (φ j)) (nhdsWithin L (Set.Icc a b)) := by
        have hx_seq_mem : ∀ j, x_seq (φ j) ∈ Set.Icc a b := fun j => hx_mem (φ j)
        have h_eventually : ∀ᶠ j in Filter.atTop, x_seq (φ j) ∈ Set.Icc a b := by
          filter_upwards [] with j; exact hx_seq_mem j
        have h_principal : Filter.atTop.Tendsto (fun j : ℕ ↦ x_seq (φ j)) (Filter.principal (Set.Icc a b)) := by
          rw [Filter.tendsto_principal]
          exact h_eventually
        have h_inf : Filter.atTop.Tendsto (fun j : ℕ ↦ x_seq (φ j)) (nhds L ⊓ Filter.principal (Set.Icc a b)) :=
          Filter.tendsto_inf.mpr ⟨hconv_x, h_principal⟩
        simpa [nhdsWithin] using h_inf
      have h_f_conv_x : Filter.atTop.Tendsto (fun j : ℕ ↦ f (x_seq (φ j))) (nhds (f L)) :=
        (hcont.continuousWithinAt hL).tendsto.comp hconv_x_within
      have h_a_conv : Filter.atTop.Tendsto (fun j : ℕ ↦ a_seq (φ j)) (nhds y₀) :=
        hconv.comp hφ_mono.tendsto_atTop
      have h_f_L_eq_y₀ : f L = y₀ := by
        have h1 : Filter.atTop.Tendsto (fun j : ℕ ↦ f (x_seq (φ j))) (nhds y₀) := by
          simpa [h_f_x_eq_a] using h_a_conv
        have h_unique_lim := tendsto_nhds_unique h_f_conv_x h1
        rw [h_unique_lim]
      have hx₀_spec : f x₀ = y₀ := h_f_x₀_eq_y₀
      by_contra! hne
      have h_or : L < x₀ ∨ x₀ < L := by
        by_cases h' : L < x₀; · left; exact h'
        · right; have hx_le_L : x₀ ≤ L := le_of_not_gt h'
          exact lt_of_le_of_ne hx_le_L hne.symm
      rcases h_or with (hlt | hlt)
      · have := hmono (a := L) hL (b := x₀) hx₀_mem hlt
        rw [h_f_L_eq_y₀, hx₀_spec] at this
        linarith
      · have := hmono (a := x₀) hx₀_mem (b := L) hL hlt
        rw [h_f_L_eq_y₀, hx₀_spec] at this
        linarith
    -- Now prove that x_seq → x₀ by contradiction
    have h_conv_x₀ : Filter.atTop.Tendsto x_seq (nhds x₀) := by
      by_contra! h_not
      rw [Metric.tendsto_atTop] at h_not
      push_neg at h_not
      rcases h_not with ⟨ε, hε, h_inf⟩
      -- Construct a subsequence staying at distance ≥ ε from x₀
      have h_exists : ∀ N : ℕ, ∃ n ≥ N, dist (x_seq n) x₀ ≥ ε := by
        intro N
        rcases h_inf N with ⟨n, hn, hnval⟩
        exact ⟨n, hn, hnval⟩
      -- Build a strictly increasing ψ such that dist (x_seq (ψ k)) x₀ ≥ ε for all k
      let ψ : ℕ → ℕ := fun n ↦
        Nat.recOn n (h_exists 0).choose fun k pk ↦ (h_exists (pk + 1)).choose
      have hψ_ge (n : ℕ) : ψ n ≥ n := by
        induction' n with k ih
        · have h0 := (h_exists 0).choose_spec
          exact h0.1
        · have hk := (h_exists (ψ k + 1)).choose_spec
          have hpk : ψ k ≥ k := ih
          have hpk1 : ψ (k+1) ≥ ψ k + 1 := hk.1
          omega
      have hψ_val (n : ℕ) : dist (x_seq (ψ n)) x₀ ≥ ε := by
        induction' n with k ih
        · have h0 := (h_exists 0).choose_spec
          exact h0.2
        · have hk := (h_exists (ψ k + 1)).choose_spec
          exact hk.2
      have hψ_strictMono : StrictMono ψ := by
        refine strictMono_nat_of_lt_succ ?_
        intro n
        have h_spec := (h_exists (ψ n + 1)).choose_spec
        have h_next : ψ (n+1) ≥ ψ n + 1 := h_spec.1
        omega
      have hx_mem_ψ : ∀ k, x_seq (ψ k) ∈ Set.Icc a b := fun k => hx_mem (ψ k)
      rcases (Heine_Borel (Set.Icc a b)).mp ⟨hx_closed, hx_bdd⟩ (x_seq ∘ ψ) hx_mem_ψ with ⟨ψ₂, hψ₂_mono, ⟨L', hL', hconv_x_ψ⟩⟩
      have h_L'_eq_x₀ : L' = x₀ :=
        h_subseq_limit (ψ ∘ ψ₂) (hψ_strictMono.comp hψ₂_mono) L' hL' hconv_x_ψ
      have h_subseq_conv : Filter.atTop.Tendsto (fun k : ℕ ↦ x_seq (ψ (ψ₂ k))) (nhds x₀) := by
        simpa [h_L'_eq_x₀] using hconv_x_ψ
      have h_eps_violation : ∀ k, dist (x_seq (ψ (ψ₂ k))) x₀ ≥ ε := fun k => hψ_val (ψ₂ k)
      rcases (Metric.tendsto_atTop.mp h_subseq_conv) ε hε with ⟨N, hN⟩
      have h_val_violation : dist (x_seq (ψ (ψ₂ N))) x₀ ≥ ε := h_eps_violation N
      have h_lt : dist (x_seq (ψ (ψ₂ N))) x₀ < ε := hN N (le_refl N)
      linarith
    exact h_conv_x₀
  refine ⟨h_image, finv, h_finv_cont, h_finv_strict_mono, h_finv_image, hfinv_f, ?_⟩
  intro y hy
  exact (hfinv_spec y hy).2

/-- Example 9.8.4-/
example {R :ℝ} (hR: R > 0) {n:ℕ} (hn: n > 0) : ∃ g : ℝ → ℝ, ∀ x ∈ Set.Icc 0 (R^n), (g x)^n = x := by
  set f : ℝ → ℝ := fun x ↦ x^n
  have hcont : ContinuousOn f (.Icc 0 R) := by fun_prop
  have hmono : StrictMonoOn f (.Icc 0 R) := by
    intro _ hx _ _ hxy; simp_all [f]
    apply pow_lt_pow_left₀ hxy <;> grind
  obtain ⟨ g, ⟨ _, _, _, _, hg⟩ ⟩ := (MonotoneOn.exist_inverse (by positivity) f hcont hmono).2
  simp only [f, zero_pow (by positivity)] at hg; use g

/-- Exercise 9.8.1 -/
theorem IsMaxOn.of_monotone_on_compact {a b:ℝ} (h:a < b) {f:ℝ → ℝ} (hf: MonotoneOn f (.Icc a b)) :
  ∃ xmax ∈ Set.Icc a b, IsMaxOn f (.Icc a b) xmax := by
  refine ⟨b, Set.right_mem_Icc.mpr (le_of_lt h), ?_⟩
  rw [isMaxOn_iff]
  intro x hx
  apply hf (a := x) (b := b) hx (Set.right_mem_Icc.mpr (le_of_lt h))
  exact hx.2

theorem IsMaxOn.of_strictmono_on_compact {a b:ℝ} (h:a < b) {f:ℝ → ℝ} (hf: StrictMonoOn f (.Icc a b)) :
  ∃ xmax ∈ Set.Icc a b, IsMaxOn f (.Icc a b) xmax := by
  have h_mono : MonotoneOn f (.Icc a b) := by
    intro x hx y hy hxy
    rcases hxy.eq_or_lt with (rfl | hxy)
    · rfl
    · exact le_of_lt (hf (a := x) hx (b := y) hy hxy)
  exact IsMaxOn.of_monotone_on_compact h h_mono

theorem IsMaxOn.of_antitone_on_compact {a b:ℝ} (h:a < b) {f:ℝ → ℝ} (hf: AntitoneOn f (.Icc a b)) :
  ∃ xmax ∈ Set.Icc a b, IsMaxOn f (.Icc a b) xmax := by
  refine ⟨a, Set.left_mem_Icc.mpr (le_of_lt h), ?_⟩
  rw [isMaxOn_iff]
  intro x hx
  apply hf (a := a) (b := x) (Set.left_mem_Icc.mpr (le_of_lt h)) hx
  exact hx.1

theorem IsMaxOn.of_strictantitone_on_compact {a b:ℝ} (h:a < b) {f:ℝ → ℝ} (hf: StrictAntiOn f (.Icc a b)) :
  ∃ xmax ∈ Set.Icc a b, IsMaxOn f (.Icc a b) xmax := by
  have h_anti : AntitoneOn f (.Icc a b) := by
    intro x hx y hy hxy
    rcases hxy.eq_or_lt with (rfl | hxy)
    · rfl
    · exact le_of_lt (hf (a := x) hx (b := y) hy hxy)
  exact IsMaxOn.of_antitone_on_compact h h_anti

theorem BddOn.of_monotone {a b:ℝ} {f:ℝ → ℝ} (hf: MonotoneOn f (.Icc a b)) :
  BddOn f (.Icc a b) := by
  by_cases h_ab : a ≤ b
  · have ha_mem : a ∈ Set.Icc a b := ⟨le_refl a, h_ab⟩
    have hb_mem : b ∈ Set.Icc a b := ⟨h_ab, le_refl b⟩
    have hfa_abs : -|f a| ≤ f a ∧ f a ≤ |f a| := abs_le.mp (le_refl (|f a|))
    have hfb_abs : -|f b| ≤ f b ∧ f b ≤ |f b| := abs_le.mp (le_refl (|f b|))
    use max |f a| |f b|
    intro x hx
    rw [abs_le]
    constructor
    · have h : f a ≤ f x := hf (a := a) (b := x) ha_mem hx hx.1
      have h_neg : -max |f a| |f b| ≤ f a := by
        have hmax : |f a| ≤ max |f a| |f b| := le_max_left _ _
        nlinarith
      nlinarith
    · have h : f x ≤ f b := hf (a := x) (b := b) hx hb_mem hx.2
      have h_pos : f b ≤ max |f a| |f b| := by
        have hmax : |f b| ≤ max |f a| |f b| := le_max_right _ _
        nlinarith
      nlinarith
  · use 0
    intro x hx
    exfalso
    linarith [hx.1, hx.2]

theorem BddOn.of_antitone {a b:ℝ} {f:ℝ → ℝ} (hf: AntitoneOn f (.Icc a b)) :
  BddOn f (.Icc a b) := by
  by_cases h_ab : a ≤ b
  · have ha_mem : a ∈ Set.Icc a b := ⟨le_refl a, h_ab⟩
    have hb_mem : b ∈ Set.Icc a b := ⟨h_ab, le_refl b⟩
    have hfa_abs : -|f a| ≤ f a ∧ f a ≤ |f a| := abs_le.mp (le_refl (|f a|))
    have hfb_abs : -|f b| ≤ f b ∧ f b ≤ |f b| := abs_le.mp (le_refl (|f b|))
    use max |f a| |f b|
    intro x hx
    rw [abs_le]
    constructor
    · have h : f b ≤ f x := hf (a := x) (b := b) hx hb_mem hx.2
      have h_neg : -max |f a| |f b| ≤ f b := by
        have hmax : |f b| ≤ max |f a| |f b| := le_max_right _ _
        nlinarith
      nlinarith
    · have h : f x ≤ f a := hf (a := a) (b := x) ha_mem hx hx.1
      have h_pos : f a ≤ max |f a| |f b| := by
        have hmax : |f a| ≤ max |f a| |f b| := le_max_left _ _
        nlinarith
      nlinarith
  · use 0
    intro x hx
    exfalso
    linarith [hx.1, hx.2]



/-- Exercise 9.8.2 -/
theorem no_strictmono_intermediate_value :
    ∃ (a b:ℝ) (_hab: a < b) (f:ℝ → ℝ) (_hf: StrictMonoOn f (.Icc a b)),
      ∃ y, (y ∈ Set.Icc (f a) (f b) ∨ y ∈ Set.Icc (f b) (f a)) ∧
      ¬ ∃ c ∈ Set.Icc a b, f c = y := by
  set f : ℝ → ℝ := fun x ↦ if x ≤ 1/2 then x else x + 1 with hf_def
  refine ⟨0, 1, by norm_num, f, ?_, 1, Or.inl ?_, ?_⟩
  · intro x hx y hy hxy
    dsimp [f]
    by_cases hx' : x ≤ 1/2
    · by_cases hy' : y ≤ 1/2
      · rw [if_pos hx', if_pos hy']; exact hxy
      · rw [if_pos hx', if_neg hy']
        have hypos : 1/2 < y := by linarith
        nlinarith
    · have hxpos : 1/2 < x := by linarith
      have hypos : 1/2 < y := by linarith
      rw [if_neg hx', if_neg (show ¬ y ≤ 1/2 from by linarith)]
      nlinarith
  · have hf0 : f 0 = 0 := by simp [f]
    have hf1 : f 1 = 2 := by
      simp [f]; norm_num
    constructor <;> norm_num [hf0, hf1]
  · intro h; rcases h with ⟨c, hc, hc_eq⟩
    have hc1 : 0 ≤ c := hc.1
    have hc2 : c ≤ 1 := hc.2
    dsimp [f] at hc_eq
    by_cases hc' : c ≤ 1/2
    · rw [if_pos hc'] at hc_eq; linarith
    · rw [if_neg hc'] at hc_eq; linarith

theorem no_monotone_intermediate_value :
    ∃ (a b:ℝ) (_hab: a < b) (f:ℝ → ℝ) (_hf: MonotoneOn f (.Icc a b)),
      ∃ y, (y ∈ Set.Icc (f a) (f b) ∨ y ∈ Set.Icc (f b) (f a)) ∧
      ¬ ∃ c ∈ Set.Icc a b, f c = y := by
  obtain ⟨a, b, hab, f, hf_strict, y, hy, h_no⟩ := no_strictmono_intermediate_value
  refine ⟨a, b, hab, f, ?_, y, hy, h_no⟩
  intro x hx z hz hxz
  rcases hxz.eq_or_lt with (rfl | hxz)
  · rfl
  · exact le_of_lt (hf_strict (a := x) hx (b := z) hz hxz)

theorem no_strictanti_intermediate_value :
    ∃ (a b:ℝ) (_hab: a < b) (f:ℝ → ℝ) (_hf: StrictAntiOn f (.Icc a b)),
      ∃ y, (y ∈ Set.Icc (f a) (f b) ∨ y ∈ Set.Icc (f b) (f a)) ∧
      ¬ ∃ c ∈ Set.Icc a b, f c = y := by
  obtain ⟨a, b, hab, f, hf_strict, y, hy, h_no⟩ := no_strictmono_intermediate_value
  have h_neg_strict : StrictAntiOn (-f) (Set.Icc a b) := by
    intro x hx z hz hxz
    have hpos : f x < f z := hf_strict (a := x) hx (b := z) hz hxz
    dsimp; linarith
  have hy_neg_mem : (-y) ∈ Set.Icc ((-f) a) ((-f) b) ∨ (-y) ∈ Set.Icc ((-f) b) ((-f) a) := by
    rcases hy with (hy' | hy')
    · rcases hy' with ⟨h1, h2⟩
      right
      have hneg1 : (-f) b ≤ -y := by
        calc
          (-f) b = -(f b) := rfl
          _ ≤ -y := by linarith
      have hneg2 : -y ≤ (-f) a := by
        calc
          -y ≤ -(f a) := by linarith
          _ = (-f) a := rfl
      exact ⟨hneg1, hneg2⟩
    · rcases hy' with ⟨h1, h2⟩
      left
      have hneg1 : (-f) a ≤ -y := by
        calc
          (-f) a = -(f a) := rfl
          _ ≤ -y := by linarith
      have hneg2 : -y ≤ (-f) b := by
        calc
          -y ≤ -(f b) := by linarith
          _ = (-f) b := rfl
      exact ⟨hneg1, hneg2⟩
  have h_neg_no : ¬ ∃ c ∈ Set.Icc a b, (-f) c = -y := by
    intro h; rcases h with ⟨c, hc, hc_eq⟩
    apply h_no
    refine ⟨c, hc, ?_⟩
    dsimp at hc_eq; linarith
  refine ⟨a, b, hab, -f, h_neg_strict, -y, hy_neg_mem, h_neg_no⟩

theorem no_antitone_intermediate_value :
    ∃ (a b:ℝ) (_hab: a < b) (f:ℝ → ℝ) (_hf: AntitoneOn f (.Icc a b)),
      ∃ y, (y ∈ Set.Icc (f a) (f b) ∨ y ∈ Set.Icc (f b) (f a)) ∧
      ¬ ∃ c ∈ Set.Icc a b, f c = y := by
  obtain ⟨a, b, hab, f, hf_strict, y, hy, h_no⟩ := no_strictanti_intermediate_value
  refine ⟨a, b, hab, f, ?_, y, hy, h_no⟩
  intro x hx z hz hxz
  rcases hxz.eq_or_lt with (rfl | hxz)
  · rfl
  · exact le_of_lt (hf_strict (a := x) hx (b := z) hz hxz)

/-- Exercise 9.8.3 -/
theorem mono_of_continuous_inj (a b:ℝ) (h: a < b) {f:ℝ → ℝ}
  (hf: ContinuousOn f (.Icc a b))
  (hinj: Function.Injective (fun x: Set.Icc a b ↦ f x )) :
  StrictMonoOn f (.Icc a b) ∨ StrictAntiOn f (.Icc a b) := by
  have ha_mem : a ∈ Set.Icc a b := Set.left_mem_Icc.mpr (le_of_lt h)
  have hb_mem : b ∈ Set.Icc a b := Set.right_mem_Icc.mpr (le_of_lt h)
  have h_ne : f a ≠ f b := by
    intro h_eq
    have h_val := hinj (a₁ := (⟨a, ha_mem⟩ : Set.Icc a b)) (a₂ := (⟨b, hb_mem⟩ : Set.Icc a b)) h_eq
    have : a = b := congr_arg Subtype.val h_val
    linarith
  by_cases h_fa_lt_fb : f a < f b
  · left
    intro x hx y hy hxy
    by_contra! hge
    have hx_lt_b : x < b := lt_of_lt_of_le hxy hy.2
    have h_fx_lt_fb : f x < f b := by
      by_cases hx_eq_a : x = a
      · subst hx_eq_a; exact h_fa_lt_fb
      · have ha_lt_x : a < x := lt_of_le_of_ne hx.1 (Ne.symm hx_eq_a)
        by_contra! hge_fx
        have h_fb_mem : f b ∈ Set.Icc (f a) (f x) := ⟨h_fa_lt_fb.le, hge_fx⟩
        rcases intermediate_value ha_lt_x (hf.mono (Set.Icc_subset_Icc (le_refl a) hx.2))
          (Or.inl h_fb_mem) with ⟨c, hc, hc_eq⟩
        have hc_mem : c ∈ Set.Icc a b := Set.Icc_subset_Icc (le_refl a) hx.2 hc
        have h_eq_val : (⟨c, hc_mem⟩ : Set.Icc a b) = (⟨b, hb_mem⟩ : Set.Icc a b) := hinj (by simpa)
        have : c = b := congr_arg Subtype.val h_eq_val
        have : c ≤ x := hc.2
        linarith
    have hy_lt_b : y < b := by
      by_contra! hge_b
      have : y = b := le_antisymm hy.2 hge_b
      subst this
      linarith
    have h_fx_mem : f x ∈ Set.Icc (f y) (f b) := ⟨hge, h_fx_lt_fb.le⟩
    rcases intermediate_value hy_lt_b (hf.mono (Set.Icc_subset_Icc hy.1 (le_refl b)))
      (Or.inl h_fx_mem) with ⟨c, hc, hc_eq⟩
    have hc_mem : c ∈ Set.Icc a b := Set.Icc_subset_Icc hy.1 (le_refl b) hc
    have h_eq_val : (⟨c, hc_mem⟩ : Set.Icc a b) = (⟨x, hx⟩ : Set.Icc a b) := hinj (by simpa)
    have : c = x := congr_arg Subtype.val h_eq_val
    have : c ≥ y := hc.1
    linarith
  · have h_fb_lt_fa : f b < f a := by
      by_contra! h_ge
      have hfa_le_fb : f a ≤ f b := h_ge
      have hfb_le_fa : f b ≤ f a := not_lt.mp h_fa_lt_fb
      have : f a = f b := le_antisymm hfa_le_fb hfb_le_fa
      exact h_ne this
    right
    intro x hx y hy hxy
    by_contra! hge
    have hx_lt_b : x < b := lt_of_lt_of_le hxy hy.2
    have h_neg_hflt : (-f) a < (-f) b := by
      dsimp; linarith
    have h_neg_hf_cont : ContinuousOn (-f) (.Icc a b) := hf.neg
    have h_neg_hx_fx_fb : (-f) x < (-f) b := by
      by_cases hx_eq_a : x = a
      · subst hx_eq_a; exact h_neg_hflt
      · have ha_lt_x : a < x := lt_of_le_of_ne hx.1 (Ne.symm hx_eq_a)
        by_contra! hge_fx
        have h_fb_mem : (-f) b ∈ Set.Icc ((-f) a) ((-f) x) := ⟨h_neg_hflt.le, hge_fx⟩
        rcases intermediate_value ha_lt_x (h_neg_hf_cont.mono (Set.Icc_subset_Icc (le_refl a) hx.2))
          (Or.inl h_fb_mem) with ⟨c, hc, hc_eq⟩
        have hc_mem : c ∈ Set.Icc a b := Set.Icc_subset_Icc (le_refl a) hx.2 hc
        have h_eq_val : (⟨c, hc_mem⟩ : Set.Icc a b) = (⟨b, hb_mem⟩ : Set.Icc a b) := hinj (by
          have : (-f) c = (-f) b := hc_eq
          have : f c = f b := by
            apply_fun (fun t : ℝ => -t) at hc_eq
            simpa using hc_eq
          simpa)
        have : c = b := congr_arg Subtype.val h_eq_val
        have : c ≤ x := hc.2
        linarith
    have hy_lt_b : y < b := by
      by_contra! hge_b
      have : y = b := le_antisymm hy.2 hge_b
      subst this
      dsimp at h_neg_hx_fx_fb
      linarith
    have h_neg_fx_mem : (-f) x ∈ Set.Icc ((-f) y) ((-f) b) := ⟨by dsimp; linarith, h_neg_hx_fx_fb.le⟩
    rcases intermediate_value hy_lt_b (h_neg_hf_cont.mono (Set.Icc_subset_Icc hy.1 (le_refl b)))
      (Or.inl h_neg_fx_mem) with ⟨c, hc, hc_eq⟩
    have hc_mem : c ∈ Set.Icc a b := Set.Icc_subset_Icc hy.1 (le_refl b) hc
    have h_eq_val : (⟨c, hc_mem⟩ : Set.Icc a b) = (⟨x, hx⟩ : Set.Icc a b) := hinj (by
      have : (-f) c = (-f) x := hc_eq
      have : f c = f x := by
        apply_fun (fun t : ℝ => -t) at hc_eq
        simpa using hc_eq
      simpa)
    have : c = x := congr_arg Subtype.val h_eq_val
    have : c ≥ y := hc.1
    linarith
/-- Exercise 9.8.4 -/
noncomputable def MonotoneOn.exist_inverse_without_continuity {a b:ℝ} (_h: a < b) {f: ℝ → ℝ} (_hmono: StrictMonoOn f (.Icc a b)) :
  Decidable ( f '' (.Icc a b) = .Icc (f a) (f b) ∧
  ∃ finv: ℝ → ℝ, ContinuousOn finv (.Icc (f a) (f b)) ∧ StrictMonoOn finv (.Icc (f a) (f b)) ∧
  finv '' (.Icc (f a) (f b)) = .Icc a b ∧
  (∀ x ∈ Set.Icc a b, finv (f x) = x) ∧
  ∀ y ∈ Set.Icc (f a) (f b), f (finv y) = y )
   := by
  classical
  exact if h : (f '' (.Icc a b) = .Icc (f a) (f b) ∧
    ∃ finv: ℝ → ℝ, ContinuousOn finv (.Icc (f a) (f b)) ∧ StrictMonoOn finv (.Icc (f a) (f b)) ∧
    finv '' (.Icc (f a) (f b)) = .Icc a b ∧
    (∀ x ∈ Set.Icc a b, finv (f x) = x) ∧
    ∀ y ∈ Set.Icc (f a) (f b), f (finv y) = y) then isTrue h else isFalse h

/-- Exercise 9.8.4 -/
noncomputable def MonotoneOn.exist_inverse_without_strictmono {a b:ℝ} (_h: a < b) (f: ℝ → ℝ)
  (_hcont: ContinuousOn f (.Icc a b)) (_hmono: MonotoneOn f (.Icc a b)) :
  Decidable ( f '' (.Icc a b) = .Icc (f a) (f b) ∧
  ∃ finv: ℝ → ℝ, ContinuousOn finv (.Icc (f a) (f b)) ∧ StrictMonoOn finv (.Icc (f a) (f b)) ∧
  finv '' (.Icc (f a) (f b)) = .Icc a b ∧
  (∀ x ∈ Set.Icc a b, finv (f x) = x) ∧
  ∀ y ∈ Set.Icc (f a) (f b), f (finv y) = y )
   := by
  classical
  exact if h : (f '' (.Icc a b) = .Icc (f a) (f b) ∧
    ∃ finv: ℝ → ℝ, ContinuousOn finv (.Icc (f a) (f b)) ∧ StrictMonoOn finv (.Icc (f a) (f b)) ∧
    finv '' (.Icc (f a) (f b)) = .Icc a b ∧
    (∀ x ∈ Set.Icc a b, finv (f x) = x) ∧
    ∀ y ∈ Set.Icc (f a) (f b), f (finv y) = y) then isTrue h else isFalse h


/-
Exercise 9.8.4: state and prove an analogue of `MonotoneOn.exist_inverse` for `Antitone`
functions.
-/
-- theorem AntitoneOn.exist_inverse {a b:ℝ} (h: a < b) (f: ℝ → ℝ) (hcont: ContinuousOn f (.Icc a b)) (hmono: StrictAntiOn f (.Icc a b)) : sorry := by sorry

/-- An equivalence between the natural numbers and the rationals. -/
noncomputable abbrev q_9_8_5 : ℕ ≃ ℚ := nonempty_equiv_of_countable.some

noncomputable abbrev g_9_8_5 : ℚ → ℝ := fun q ↦ (2:ℝ)^(-q_9_8_5.symm q:ℤ)

noncomputable abbrev f_9_8_5 : ℝ → ℝ := fun x ↦ ∑' r : {r:ℚ // (r:ℝ) < x}, g_9_8_5 r

/-- Exercise 9.8.5(a) -/
theorem StrictMonoOn.of_f_9_8_5 : StrictMonoOn f_9_8_5 .univ := by
  intro x hx y hy hxy
  have hpos (r : ℚ) : g_9_8_5 r > 0 := by
    dsimp [g_9_8_5]
    have h := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) ((-q_9_8_5.symm r : ℤ) : ℝ)
    rw [Real.rpow_intCast] at h
    exact h
  have h_summable_h : Summable (fun (n : ℕ) => ((1/2 : ℝ) ^ n : ℝ)) :=
    summable_geometric_of_abs_lt_one (by norm_num : |(1/2 : ℝ)| < 1)
  have h_summable_g : Summable g_9_8_5 := by
    have h_eq : g_9_8_5 = (fun (n : ℕ) => ((1/2 : ℝ) ^ n : ℝ)) ∘ q_9_8_5.symm := by
      ext r; dsimp [g_9_8_5]; simp
    rw [h_eq]
    exact h_summable_h.comp_injective q_9_8_5.symm.injective
  rcases exists_rat_btwn hxy with ⟨q, hxq, hqy⟩
  have hg_pos : g_9_8_5 q > 0 := hpos q
  dsimp [f_9_8_5]
  have hfx_eq : ∑' r : { r : ℚ // (r : ℝ) < x }, g_9_8_5 r = ∑' r : ℚ, Set.indicator {q : ℚ | (q : ℝ) < x} g_9_8_5 r := by
    simpa using tsum_subtype (s := {q : ℚ | (q : ℝ) < x}) (f := g_9_8_5)
  have hfy_eq : ∑' r : { r : ℚ // (r : ℝ) < y }, g_9_8_5 r = ∑' r : ℚ, Set.indicator {q : ℚ | (q : ℝ) < y} g_9_8_5 r := by
    simpa using tsum_subtype (s := {q : ℚ | (q : ℝ) < y}) (f := g_9_8_5)
  rw [hfx_eq, hfy_eq]
  let A : Set ℚ := {r | (r : ℝ) < x}
  let B : Set ℚ := {r | (r : ℝ) < y}
  have hAB_sub : A ⊆ B := by
    intro r hr; dsimp [A, B] at hr ⊢; linarith
  have hq_not_A : q ∉ A := by
    dsimp [A]; linarith
  have hq_B : q ∈ B := by
    dsimp [B]; exact hqy
  have h_B_contains_A_union_q : (A ∪ {q}) ⊆ B := by
    intro r hr; rcases hr with (hr | hr)
    · exact hAB_sub hr
    · have h_eq : r = q := by simpa using hr
      subst h_eq; simpa [B] using hqy
  have h_summable_A : Summable (Set.indicator A g_9_8_5) := h_summable_g.indicator A
  have h_summable_B : Summable (Set.indicator B g_9_8_5) := h_summable_g.indicator B
  have h_hasSum_A : HasSum (Set.indicator A g_9_8_5) (∑' r : ℚ, Set.indicator A g_9_8_5 r) :=
    h_summable_A.hasSum
  have h_hasSum_B : HasSum (Set.indicator B g_9_8_5) (∑' r : ℚ, Set.indicator B g_9_8_5 r) :=
    h_summable_B.hasSum
  have h_hasSum_q : HasSum (Set.indicator ({q} : Set ℚ) g_9_8_5) (g_9_8_5 q) := by
    have h := hasSum_single (f := Set.indicator ({q} : Set ℚ) g_9_8_5) q (by
      intro b' hb'
      simp [Set.indicator, Set.mem_singleton_iff, hb'])
    simpa using h
  have h_hasSum_union : HasSum (Set.indicator (A ∪ {q}) g_9_8_5) (∑' r : ℚ, Set.indicator A g_9_8_5 r + g_9_8_5 q) := by
    have h_disjoint : Disjoint A ({q} : Set ℚ) := by
      rw [Set.disjoint_iff_inter_eq_empty]
      ext r; simp [hq_not_A]
    have h_eq : Set.indicator (A ∪ {q}) g_9_8_5 = Set.indicator A g_9_8_5 + Set.indicator ({q} : Set ℚ) g_9_8_5 :=
      Set.indicator_union_of_disjoint h_disjoint g_9_8_5
    rw [h_eq]
    exact HasSum.add h_hasSum_A h_hasSum_q
  have h_pointwise : ∀ r : ℚ, Set.indicator (A ∪ {q}) g_9_8_5 r ≤ Set.indicator B g_9_8_5 r := by
    intro r
    by_cases hrA : r ∈ A
    · have hr' : r ∈ B := h_B_contains_A_union_q (Or.inl hrA)
      simp [Set.indicator, hrA, hr']
    · by_cases hrq : r = q
      · rw [hrq]
        have hq_B : q ∈ B := h_B_contains_A_union_q (Or.inr rfl)
        simp [Set.indicator, hq_B]
      · have hr_not_union : r ∉ A ∪ {q} := by
          simp [hrA, hrq]
        have hL : Set.indicator (A ∪ {q}) g_9_8_5 r = 0 := by
          dsimp [Set.indicator]
          by_cases h : r ∈ A ∪ {q}
          · exfalso; exact hr_not_union h
          · rw [if_neg h]
        rw [hL]
        exact Set.indicator_nonneg (fun a ha => (hpos a).le) r
  have h_ineq_val : (∑' r : ℚ, Set.indicator A g_9_8_5 r + g_9_8_5 q) ≤ ∑' r : ℚ, Set.indicator B g_9_8_5 r :=
    hasSum_le h_pointwise h_hasSum_union h_hasSum_B
  have h_fx_pos : 0 ≤ ∑' r : ℚ, Set.indicator A g_9_8_5 r :=
    tsum_nonneg (fun r => Set.indicator_nonneg (fun a ha => (hpos a).le) r)
  have : ∑' r : ℚ, Set.indicator A g_9_8_5 r + g_9_8_5 q ≤ ∑' r : ℚ, Set.indicator B g_9_8_5 r := h_ineq_val
  linarith

/-- Exercise 9.8.5(b) -/
theorem ContinuousAt.of_f_9_8_5' (r:ℚ) : ¬ ContinuousAt f_9_8_5 r := by
  have hpos_all (r' : ℚ) : g_9_8_5 r' > 0 := by
    dsimp [g_9_8_5]
    have h := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) ((-q_9_8_5.symm r' : ℤ) : ℝ)
    rw [Real.rpow_intCast] at h
    exact h
  have hpos : g_9_8_5 r > 0 := hpos_all r
  have h_summable_h : Summable (fun (n : ℕ) => ((1/2 : ℝ) ^ n : ℝ)) :=
    summable_geometric_of_abs_lt_one (by norm_num : |(1/2 : ℝ)| < 1)
  have h_summable_g : Summable g_9_8_5 := by
    have h_eq : g_9_8_5 = (fun (n : ℕ) => ((1/2 : ℝ) ^ n : ℝ)) ∘ q_9_8_5.symm := by
      ext r'; dsimp [g_9_8_5]; simp
    rw [h_eq]
    exact h_summable_h.comp_injective q_9_8_5.symm.injective
  intro hcont
  have h_f_strict_mono : StrictMonoOn f_9_8_5 .univ := StrictMonoOn.of_f_9_8_5
  -- For any x > r, we have f(x) = f(r) + sum over {r ≤ q < x} g(q) ≥ f(r) + g(r)
  -- Thus f(x) - f(r) ≥ g(r) > 0, contradicting continuity at r
  have h_jump_ineq2 : ∀ x : ℝ, (r : ℝ) < x → f_9_8_5 r + g_9_8_5 r ≤ f_9_8_5 x := by
    intro x hx
    have hpos_all' (r' : ℚ) : g_9_8_5 r' > 0 := by
      dsimp [g_9_8_5]
      have h := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) ((-q_9_8_5.symm r' : ℤ) : ℝ)
      rw [Real.rpow_intCast] at h
      exact h
    dsimp [f_9_8_5]
    have hfx_eq' : ∑' r' : { r' : ℚ // (r' : ℝ) < (r : ℝ) }, g_9_8_5 r' = ∑' r' : ℚ, Set.indicator {q : ℚ | (q : ℝ) < (r : ℝ)} g_9_8_5 r' := by
      simpa using tsum_subtype (s := {q : ℚ | (q : ℝ) < (r : ℝ)}) (f := g_9_8_5)
    have hfy_eq' : ∑' r' : { r' : ℚ // (r' : ℝ) < x }, g_9_8_5 r' = ∑' r' : ℚ, Set.indicator {q : ℚ | (q : ℝ) < x} g_9_8_5 r' := by
      simpa using tsum_subtype (s := {q : ℚ | (q : ℝ) < x}) (f := g_9_8_5)
    let A : Set ℚ := {q | (q : ℝ) < (r : ℝ)}
    let B : Set ℚ := {q | (q : ℝ) < x}
    have h_AB_sub : A ⊆ B := by
      intro q' hq'; dsimp [A, B] at hq' ⊢; linarith
    have h_r_not_A : r ∉ A := by
      dsimp [A]; exact lt_irrefl (r : ℝ)
    have h_r_B : r ∈ B := by
      dsimp [B]; exact hx
    have h_B_contains_A_union_r : (A ∪ {r}) ⊆ B := by
      intro q' hq'; rcases hq' with (hq' | hq')
      · exact h_AB_sub hq'
      · have hq'_eq_r : q' = r := hq'
        subst hq'_eq_r; simpa [B] using hx
    have h_summable_A : Summable (Set.indicator A g_9_8_5) := h_summable_g.indicator A
    have h_summable_B : Summable (Set.indicator B g_9_8_5) := h_summable_g.indicator B
    have h_hasSum_A : HasSum (Set.indicator A g_9_8_5) (∑' q' : ℚ, Set.indicator A g_9_8_5 q') :=
      h_summable_A.hasSum
    have h_hasSum_B : HasSum (Set.indicator B g_9_8_5) (∑' q' : ℚ, Set.indicator B g_9_8_5 q') :=
      h_summable_B.hasSum
    have h_hasSum_r : HasSum (Set.indicator ({r} : Set ℚ) g_9_8_5) (g_9_8_5 r) := by
      have h := hasSum_single (f := Set.indicator ({r} : Set ℚ) g_9_8_5) r (by
        intro b' hb'
        simp [Set.indicator, Set.mem_singleton_iff, hb'])
      simpa using h
    have h_hasSum_union : HasSum (Set.indicator (A ∪ {r}) g_9_8_5) (∑' q' : ℚ, Set.indicator A g_9_8_5 q' + g_9_8_5 r) := by
      have h_disjoint : Disjoint A ({r} : Set ℚ) := by
        rw [Set.disjoint_iff_inter_eq_empty]
        ext q'; simp [h_r_not_A]
      have h_eq : Set.indicator (A ∪ {r}) g_9_8_5 = Set.indicator A g_9_8_5 + Set.indicator ({r} : Set ℚ) g_9_8_5 :=
        Set.indicator_union_of_disjoint h_disjoint g_9_8_5
      rw [h_eq]
      exact HasSum.add h_hasSum_A h_hasSum_r
    have h_pointwise : ∀ q' : ℚ, Set.indicator (A ∪ {r}) g_9_8_5 q' ≤ Set.indicator B g_9_8_5 q' := by
      intro q'
      by_cases hq'A : q' ∈ A
      · have hq'_B : q' ∈ B := h_B_contains_A_union_r (Or.inl hq'A)
        simp [Set.indicator, hq'A, hq'_B]
      · by_cases hq'r : q' = r
        · rw [hq'r]
          have hr_B : r ∈ B := h_B_contains_A_union_r (Or.inr rfl)
          simp [Set.indicator, hr_B]
        · have hq'_not_union : q' ∉ A ∪ {r} := by
            simp [hq'A, hq'r]
          have hL : Set.indicator (A ∪ {r}) g_9_8_5 q' = 0 := by
            dsimp [Set.indicator]
            by_cases h : q' ∈ A ∪ {r}
            · exfalso; exact hq'_not_union h
            · rw [if_neg h]
          rw [hL]
          exact Set.indicator_nonneg (fun a ha => (hpos_all' a).le) q'
    have h_ineq_val : (∑' q' : ℚ, Set.indicator A g_9_8_5 q' + g_9_8_5 r) ≤ ∑' q' : ℚ, Set.indicator B g_9_8_5 q' :=
      hasSum_le h_pointwise h_hasSum_union h_hasSum_B
    have h_tsum_union_eq : ∑' q' : ℚ, Set.indicator (A ∪ {r}) g_9_8_5 q' = ∑' q' : ℚ, Set.indicator A g_9_8_5 q' + g_9_8_5 r := by
      apply HasSum.tsum_eq h_hasSum_union
    rw [hfx_eq', hfy_eq']
    exact h_ineq_val
  -- Given continuity at r, pick ε = g(r)/2, get δ > 0 such that |f(x) - f(r)| < ε for |x-r| < δ
  set ε := g_9_8_5 r / 2 with hε_def
  have hε_pos : 0 < ε := by linarith [hpos]
  have h_ball : Metric.ball (f_9_8_5 (r : ℝ)) ε ∈ nhds (f_9_8_5 (r : ℝ)) :=
    Metric.ball_mem_nhds (f_9_8_5 (r : ℝ)) hε_pos
  have h_preimage : f_9_8_5 ⁻¹' Metric.ball (f_9_8_5 (r : ℝ)) ε ∈ nhds (r : ℝ) :=
    hcont.tendsto h_ball
  rcases Metric.mem_nhds_iff.mp h_preimage with ⟨δ, hδ_pos, hδ⟩
  -- hδ : Metric.ball (r : ℝ) δ ⊆ f_9_8_5 ⁻¹' Metric.ball (f_9_8_5 (r : ℝ)) ε
  let x := (r : ℝ) + δ / 2
  have hx_mem : x ∈ Metric.ball (r : ℝ) δ := by
    dsimp [x, Metric.mem_ball, Real.dist_eq]
    have h_abs2 : |δ / 2| < δ := by
      have h_pos : 0 < δ / 2 := by nlinarith
      rw [abs_of_pos h_pos]
      nlinarith
    calc
      |(r + δ / 2) - r| = |δ / 2| := by simp
      _ < δ := h_abs2
  have hfx_mem : f_9_8_5 x ∈ Metric.ball (f_9_8_5 (r : ℝ)) ε := hδ hx_mem
  have hfx_mem_dist : |f_9_8_5 x - f_9_8_5 (r : ℝ)| < ε := by
    simpa [Metric.mem_ball, Real.dist_eq] using hfx_mem
  have hx_gt_r : (r : ℝ) < x := by
    dsimp [x]; nlinarith
  have h_jump_val : f_9_8_5 (r : ℝ) + g_9_8_5 r ≤ f_9_8_5 x := h_jump_ineq2 x hx_gt_r
  have h_nonneg_diff : f_9_8_5 x - f_9_8_5 (r : ℝ) ≥ 0 := by
    have : f_9_8_5 (r : ℝ) ≤ f_9_8_5 x := by linarith
    linarith
  rw [abs_of_nonneg h_nonneg_diff] at hfx_mem_dist
  nlinarith


/-- {name}`g_9_8_5` is strictly positive. -/
lemma g_9_8_5_pos (r : ℚ) : g_9_8_5 r > 0 := by
  dsimp [g_9_8_5]
  have h := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) ((-q_9_8_5.symm r : ℤ) : ℝ)
  rw [Real.rpow_intCast] at h
  exact h

/-- {name}`g_9_8_5` is summable. -/
lemma summable_g_9_8_5 : Summable g_9_8_5 := by
  have h_summable_h : Summable (fun (n : ℕ) => ((1/2 : ℝ) ^ n : ℝ)) :=
    summable_geometric_of_abs_lt_one (by norm_num : |(1/2 : ℝ)| < 1)
  have h_eq : g_9_8_5 = (fun (n : ℕ) => ((1/2 : ℝ) ^ n : ℝ)) ∘ q_9_8_5.symm := by
    ext r; dsimp [g_9_8_5]; simp
  rw [h_eq]
  exact h_summable_h.comp_injective q_9_8_5.symm.injective

/-
The difference formula: for `a ≤ b`, `f(b) - f(a)` is the sum of `g` over the rationals
in `[a, b)`.
-/
lemma f_9_8_5_sub (a b : ℝ) (hab : a ≤ b) :
    f_9_8_5 b - f_9_8_5 a
      = ∑' r : ℚ, Set.indicator {q : ℚ | a ≤ (q:ℝ) ∧ (q:ℝ) < b} g_9_8_5 r := by
  convert Summable.tsum_sub ( show Summable fun r : ℚ => Set.indicator ( { q : ℚ | ( q : ℝ ) < b } ) ( fun q => g_9_8_5 q ) r from ?_ ) ( show Summable fun r : ℚ => Set.indicator ( { q : ℚ | ( q : ℝ ) < a } ) ( fun q => g_9_8_5 q ) r from ?_ ) using 1;
  · rw [ Summable.tsum_sub ];
    · congr! 1;
      · convert tsum_subtype ( { q : ℚ | ( q : ℝ ) < b } ) ( fun q => g_9_8_5 q ) using 1;
      · convert tsum_subtype _ _;
    · refine' Summable.of_nonneg_of_le ( fun q => _ ) ( fun q => _ ) ( summable_g_9_8_5 );
      · rw [ Set.indicator_apply ] ; aesop;
      · by_cases h : ( q : ℝ ) < b <;> simp +decide [ h ];
    · exact Summable.indicator ( summable_g_9_8_5 ) _;
  · rw [ ← Summable.tsum_sub ];
    · congr with x ; by_cases hx : ( x : ℝ ) < a <;> by_cases hx' : ( x : ℝ ) < b <;> simp +decide [ hx, hx' ];
      · linarith;
      · rw [ Set.indicator_of_mem ] ; aesop;
        exact ⟨ le_of_not_gt hx, hx' ⟩;
    · exact Summable.indicator ( summable_g_9_8_5 ) _;
    · exact Summable.of_nonneg_of_le ( fun _ => by rw [ Set.indicator_apply ] ; split_ifs <;> first | positivity | unreachable! ) ( fun _ => by rw [ Set.indicator_apply ] ; split_ifs <;> first | positivity | rfl ) ( summable_g_9_8_5 );
  · convert summable_g_9_8_5.indicator _ using 1;
  · refine' Summable.indicator _ _;
    convert summable_g_9_8_5

/-
Given `ε > 0`, there is a finite set `T` of rationals such that the sum of `g` over the
complement of `T` is less than `ε`.
-/
lemma tail_small_9_8_5 (ε : ℝ) (hε : 0 < ε) :
    ∃ T : Finset ℚ, ∑' r : ℚ, Set.indicator {q : ℚ | q ∉ T} g_9_8_5 r < ε := by
  -- Let `S := ∑' r, g_9_8_5 r`. Since `g_9_8_5` is summable (`summable_g_9_8_5`), we have `HasSum g_9_8_5 S`.
  set S := ∑' r, g_9_8_5 r
  have hS : HasSum g_9_8_5 S := by
    exact Summable.hasSum ( summable_g_9_8_5 );
  -- By `HasSum`, there exists a finite set `T` such that `|S - ∑ i ∈ T, g_9_8_5 i| < ε`.
  obtain ⟨T, hT⟩ : ∃ T : Finset ℚ, |S - ∑ i ∈ T, g_9_8_5 i| < ε := by
    have := hS.eventually ( Metric.ball_mem_nhds _ hε );
    exact Exists.elim ( this.exists ) fun T hT => ⟨ T, by rwa [ abs_sub_comm ] ⟩;
  have h_sum_compl : ∑' (r : ℚ), (Set.indicator {q : ℚ | q ∉ T} g_9_8_5) r = S - ∑ i ∈ T, g_9_8_5 i := by
    have h_sum_compl : ∑' (r : ℚ), (Set.indicator {q : ℚ | q ∉ T} g_9_8_5) r = ∑' (r : ℚ), g_9_8_5 r - ∑' (r : ℚ), (Set.indicator {q : ℚ | q ∈ T} g_9_8_5) r := by
      rw [ ← Summable.tsum_sub ] ; congr ; ext r ; by_cases hr : r ∈ T <;> simp +decide [ hr ] ;
      · exact hS.summable;
      · exact Summable.indicator ( hS.summable ) _;
    convert h_sum_compl using 2;
    rw [ tsum_eq_sum ];
    exacts [ Finset.sum_congr rfl fun x hx => by rw [ Set.indicator_of_mem ] ; simpa using hx, fun x hx => by rw [ Set.indicator_of_notMem ] ; simpa using hx ];
  exact ⟨ T, h_sum_compl ▸ lt_of_le_of_lt ( le_abs_self _ ) hT ⟩

/-
If `x₀` is irrational and `T` is a finite set of rationals, there is a positive `δ` such that
every rational in `T` is at distance at least `δ` from `x₀`.
-/
lemma exists_delta_avoid_9_8_5 (x₀ : ℝ) (hx : ¬ ∃ r : ℚ, x₀ = r) (T : Finset ℚ) :
    ∃ δ > 0, ∀ r ∈ T, δ ≤ |(r : ℝ) - x₀| := by
  by_contra h_contra;
  obtain ⟨r₁, hr₁⟩ : ∃ r₁ ∈ T, ∀ r ∈ T, |(r₁ : ℝ) - x₀| ≤ |(r : ℝ) - x₀| := by
    exact Finset.exists_min_image _ _ ( Finset.nonempty_of_ne_empty ( by rintro rfl; exact h_contra ⟨ 1, by norm_num, by norm_num ⟩ ) );
  exact h_contra ⟨ |↑r₁ - x₀|, abs_pos.mpr ( sub_ne_zero.mpr <| by aesop ), fun r hr => hr₁.2 r hr ⟩

/-
The key bound: if no rational of `T` lies in the interval `[min x₀ x', max x₀ x')`, then
`|f(x') - f(x₀)|` is bounded by the tail sum over the complement of `T`.
-/
lemma abs_f_9_8_5_sub_le (x₀ x' : ℝ) (T : Finset ℚ)
    (hcond : ∀ r ∈ T, ¬ (min x₀ x' ≤ (r : ℝ) ∧ (r : ℝ) < max x₀ x')) :
    |f_9_8_5 x' - f_9_8_5 x₀|
      ≤ ∑' r : ℚ, Set.indicator {q : ℚ | q ∉ T} g_9_8_5 r := by
  have h_max_min : f_9_8_5 (max x₀ x') - f_9_8_5 (min x₀ x') ≤ ∑' r : ℚ, Set.indicator {q : ℚ | q ∉ T} g_9_8_5 r := by
    rw [ f_9_8_5_sub _ _ ( min_le_max ) ];
    refine' Summable.tsum_le_tsum _ _ _;
    · intro q; by_cases hq : q ∈ T <;> simp_all +decide [ Set.indicator ] ;
      · grind;
      · split_ifs <;> norm_num;
    · exact Summable.indicator ( summable_g_9_8_5 ) _;
    · exact Summable.indicator ( summable_g_9_8_5 ) _;
  cases le_total x₀ x' <;> simp_all +decide;
  · rw [ abs_of_nonneg ];
    · linarith;
    · rw [ f_9_8_5_sub ];
      · exact tsum_nonneg fun _ => Set.indicator_nonneg ( fun _ _ => le_of_lt ( g_9_8_5_pos _ ) ) _;
      · linarith;
  · rw [ abs_of_nonpos ];
    · linarith;
    · have h_monotone : ∀ x y : ℝ, x ≤ y → f_9_8_5 x ≤ f_9_8_5 y := by
        intros x y hxy
        have h_monotone : f_9_8_5 y - f_9_8_5 x = ∑' r : ℚ, Set.indicator {q : ℚ | x ≤ (q : ℝ) ∧ (q : ℝ) < y} g_9_8_5 r := by
          convert f_9_8_5_sub x y hxy using 1;
        exact le_of_sub_nonneg ( h_monotone.symm ▸ tsum_nonneg fun _ => Set.indicator_nonneg ( fun _ _ => le_of_lt ( g_9_8_5_pos _ ) ) _ );
      linarith [ h_monotone _ _ ‹_› ]

/-- Exercise 9.8.5(c) -/
theorem ContinuousAt.of_f_9_8_5 {x:ℝ} (hx: ¬ ∃ r:ℚ, x = r) : ContinuousAt f_9_8_5 x := by
  rw [ Metric.continuousAt_iff ];
  intro ε hε
  obtain ⟨T, hT⟩ := tail_small_9_8_5 ε hε
  obtain ⟨δ, hδ_pos, hδ⟩ := exists_delta_avoid_9_8_5 x hx T;
  refine' ⟨ δ, hδ_pos, fun y hy => _ ⟩;
  refine' lt_of_le_of_lt ( abs_f_9_8_5_sub_le x y T _ ) hT;
  intro r hr; specialize hδ r hr; contrapose! hδ; cases max_cases x y <;> cases min_cases x y <;> cases abs_cases ( r - x : ℝ ) <;> linarith [ abs_lt.mp hy ] ;

end Chapter9
