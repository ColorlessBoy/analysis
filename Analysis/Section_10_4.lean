import Mathlib.Tactic
import Analysis.Section_9_3
import Analysis.Section_9_4
import Analysis.Section_10_1

/-!
# Analysis I, Section 10.4: Inverse functions and derivatives

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- The inverse function theorem.

-/

open Chapter9
namespace Chapter10

/-- Lemma 10.4.1 -/
theorem _root_.HasDerivWithinAt.of_inverse {X Y: Set ℝ} {f: ℝ → ℝ} {g:ℝ → ℝ}
  (hfXY: ∀ x ∈ X, f x ∈ Y) (hgf: ∀ x ∈ X, g (f x) = x)
  {x₀ y₀ f'x₀ g'y₀: ℝ} (hx₀: x₀ ∈ X) (hfx₀: f x₀ = y₀)
  (hcluster: ClusterPt x₀ (.principal (X \ {x₀})))
  (hf: HasDerivWithinAt f f'x₀ X x₀) (hg: HasDerivWithinAt g g'y₀ Y y₀) :
  g'y₀ * f'x₀ = 1 := by
  -- This proof is written to follow the structure of the original text.
  have h1 : HasDerivWithinAt id (g'y₀ * f'x₀) X x₀ := by
    apply (hf.of_comp hfx₀ hfXY _).congr _ (hgf _ hx₀).symm <;> grind
  observe h2 : HasDerivWithinAt id 1 X x₀
  solve_by_elim [derivative_unique]

theorem _root_.HasDerivWithinAt.of_inverse' {X Y: Set ℝ} {f: ℝ → ℝ} {g:ℝ → ℝ}
  (hfXY: ∀ x ∈ X, f x ∈ Y) (hgf: ∀ x ∈ X, g (f x) = x)
  {x₀ y₀ f'x₀ g'y₀: ℝ} (hx₀: x₀ ∈ X) (hfx₀: f x₀ = y₀)
  (hcluster: ClusterPt x₀ (.principal (X \ {x₀})))
  (hf: HasDerivWithinAt f f'x₀ X x₀) (hg: HasDerivWithinAt g g'y₀ Y y₀) :
  g'y₀ = 1/f'x₀ :=
    eq_one_div_of_mul_eq_one_left (hf.of_inverse hfXY hgf hx₀ hfx₀ hcluster hg)

theorem _root_.HasDerivWithinAt.of_inverse_of_zero_deriv {X Y: Set ℝ} {f: ℝ → ℝ} {g:ℝ → ℝ}
  (hfXY: ∀ x ∈ X, f x ∈ Y) (hgf: ∀ x ∈ X, g (f x) = x)
  {x₀ y₀: ℝ} (hx₀: x₀ ∈ X) (hfx₀: f x₀ = y₀)
  (hcluster: ClusterPt x₀ (.principal (X \ {x₀})))
  (hf: HasDerivWithinAt f 0 X x₀) :
  ¬ DifferentiableWithinAt ℝ g Y y₀ := by
  by_contra this; rw [DifferentiableWithinAt.iff] at this; choose _ hg using this
  apply hf.of_inverse at hg <;> grind

example : ¬ DifferentiableWithinAt ℝ (fun x:ℝ ↦ x^(1/3:ℝ)) (.Ici 0) 0 := by
  set X := Set.Ici (0 : ℝ) with hX
  set Y := Set.Ici (0 : ℝ) with hY
  set f : ℝ → ℝ := fun x ↦ x ^ 3 with hf
  set g : ℝ → ℝ := fun x ↦ x ^ (1/3 : ℝ) with hg
  have hfXY : ∀ x ∈ X, f x ∈ Y := by
    intro x hx
    dsimp [Y, f, Set.mem_Ici]
    have hx' : 0 ≤ x := hx
    exact pow_nonneg hx' 3
  have hgf : ∀ x ∈ X, g (f x) = x := by
    intro x hx
    dsimp [g, f]
    have hx_nonneg : 0 ≤ x := hx
    calc
      (x ^ 3) ^ (1/3 : ℝ) = (x ^ (3 : ℝ)) ^ (1/3 : ℝ) := by
        rw [(Real.rpow_natCast x 3).symm]; rfl
      _ = x ^ ((3 : ℝ) * (1/3 : ℝ)) := by rw [Real.rpow_mul hx_nonneg]
      _ = x := by norm_num
  have hx₀ : (0 : ℝ) ∈ X := by
    dsimp [X]
    exact Set.mem_Ici.mpr (le_refl (0 : ℝ))
  have hfx₀ : f (0 : ℝ) = (0 : ℝ) := by simp [f]
  have hcluster : ClusterPt (0 : ℝ) (.principal (X \ {(0 : ℝ)})) := by
    dsimp [X]
    have h_eq : (Set.Ici (0 : ℝ)) \ {(0 : ℝ)} = Set.Ioi (0 : ℝ) := by
      ext x; simp
    rw [h_eq]
    rw [clusterPt_iff_forall_mem_closure]
    intro s hs
    rw [Filter.mem_principal] at hs
    have h0 : (0 : ℝ) ∈ closure (Set.Ioi (0 : ℝ)) := by
      rw [closure_Ioi (0 : ℝ)]
      exact Set.mem_Ici.mpr (le_refl (0 : ℝ))
    exact Set.mem_of_subset_of_mem (closure_mono hs) h0
  have hf_deriv : HasDerivWithinAt f (0 : ℝ) X (0 : ℝ) := by
    dsimp [X, f]
    simpa using (hasDerivAt_pow 3 (0 : ℝ)).hasDerivWithinAt
  exact HasDerivWithinAt.of_inverse_of_zero_deriv hfXY hgf hx₀ hfx₀ hcluster hf_deriv

/-- Theorem 10.4.2 (Inverse function theorem) -/
theorem inverse_function_theorem {X Y: Set ℝ} {f: ℝ → ℝ} {g:ℝ → ℝ}
  (hfXY: ∀ x ∈ X, f x ∈ Y) (hgYX: ∀ y ∈ Y, g y ∈ X)
  (hgf: ∀ x ∈ X, g (f x) = x) (hfg: ∀ y ∈ Y, f (g y) = y)
  {x₀ y₀ f'x₀: ℝ} (hx₀: x₀ ∈ X) (hfx₀: f x₀ = y₀) (hne : f'x₀ ≠ 0)
  (hf: HasDerivWithinAt f f'x₀ X x₀) (hg: ContinuousWithinAt g Y y₀) :
    HasDerivWithinAt g (1/f'x₀) Y y₀ := by
    -- This proof is written to follow the structure of the original text.
    rw [HasDerivWithinAt.iff, ←Convergesto.iff, Convergesto.iff_conv _ _]
    intro y hy hconv
    set x : ℕ → ℝ := fun n ↦ g (y n)
    have hy' : ∀ n, y n ∈ Y := by aesop
    have hy₀: y₀ ∈ Y := by aesop
    have hx : ∀ n, x n ∈ X \ {x₀}:= by
      intro n
      have hxX : x n ∈ X := by
        dsimp [x]
        exact hgYX (y n) (hy' n)
      have hx_ne : x n ≠ x₀ := by
        intro h_eq
        have hy_eq : y n = y₀ := by
          calc
            y n = f (g (y n)) := by symm; apply hfg (y n) (hy' n)
            _ = f x₀ := by simp [x, h_eq]
            _ = y₀ := hfx₀
        have hy_ne : y n ≠ y₀ := by
          have h := ((Set.mem_diff (y n)).mp (hy n)).2
          simpa using h
        exact hy_ne hy_eq
      exact ((Set.mem_diff (x n)).mpr ⟨hxX, hx_ne⟩)
    replace hconv := hconv.comp_of_continuous hg hy'
    have hgy₀ : g y₀ = x₀ := by aesop
    rw [HasDerivWithinAt.iff, ←Convergesto.iff, Convergesto.iff_conv _ _] at hf
    convert (hf _ hx _).inv₀ _ using 2 with n <;> grind

/-- Exercise 10.4.1(a) -/
example {n:ℕ} : ContinuousOn (fun x:ℝ ↦ x^(1/n:ℝ)) (.Ioi 0) := by
  intro x hx
  have hx_pos : 0 < x := hx
  have hx_ne : x ≠ 0 := by linarith
  exact (Real.continuousAt_rpow_const x (1/n : ℝ) (Or.inl hx_ne)).continuousWithinAt

/-- Exercise 10.4.1(b) -/
example {n:ℕ} {x:ℝ} (hx: x ∈ Set.Ioi 0) : HasDerivWithinAt (fun x:ℝ ↦ x^(1/n:ℝ))
  ((n:ℝ)⁻¹ * x^((n:ℝ)⁻¹-1)) (.Ioi 0) x := by
  have hx_pos : 0 < x := hx
  have hx_ne : x ≠ 0 := by linarith
  have hlog : HasDerivAt Real.log (x⁻¹) x := Real.hasDerivAt_log hx_ne
  have hlog_mul : HasDerivAt (fun x : ℝ => (1/n : ℝ) * Real.log x) ((1/n : ℝ) * x⁻¹) x := by
    simpa using (HasDerivAt.const_mul (1/n : ℝ) hlog)
  have hexp_at : HasDerivAt Real.exp (Real.exp ((1/n : ℝ) * Real.log x)) ((1/n : ℝ) * Real.log x) :=
    Real.hasDerivAt_exp ((1/n : ℝ) * Real.log x)
  have hcomp : HasDerivAt (Real.exp ∘ (fun x : ℝ => (1/n : ℝ) * Real.log x))
    (Real.exp ((1/n : ℝ) * Real.log x) * ((1/n : ℝ) * x⁻¹)) x :=
    HasDerivAt.comp x hexp_at hlog_mul
  have heq : (Real.exp ∘ (fun x : ℝ => (1/n : ℝ) * Real.log x)) =ᶠ[nhds x] (fun x : ℝ => x ^ (1/n : ℝ)) := by
    have h_open : Set.Ioi (0 : ℝ) ∈ nhds x := IsOpen.mem_nhds isOpen_Ioi hx_pos
    apply Filter.eventuallyEq_of_mem h_open
    intro y hy
    dsimp
    rw [Real.rpow_def_of_pos hy, mul_comm]
  have h_hasDerivAt : HasDerivAt (fun x : ℝ => x ^ (1/n : ℝ))
    (Real.exp ((1/n : ℝ) * Real.log x) * ((1/n : ℝ) * x⁻¹)) x :=
    hcomp.congr_of_eventuallyEq heq.symm
  have h_simplify : Real.exp ((1/n : ℝ) * Real.log x) * ((1/n : ℝ) * x⁻¹) = (n : ℝ)⁻¹ * x ^ ((n : ℝ)⁻¹ - 1) := by
    calc
      Real.exp ((1/n : ℝ) * Real.log x) * ((1/n : ℝ) * x⁻¹)
          = (x ^ (1/n : ℝ)) * ((1/n : ℝ) * x⁻¹) := by
            rw [Real.rpow_def_of_pos hx_pos, mul_comm (Real.log x) (1/n : ℝ)]
      _ = (1/n : ℝ) * (x ^ (1/n : ℝ) * x⁻¹) := by ring
      _ = (n : ℝ)⁻¹ * (x ^ (1/n : ℝ) * x⁻¹) := by simp [one_div]
      _ = (n : ℝ)⁻¹ * (x ^ (1/n : ℝ) / x) := by rw [div_eq_mul_inv (x ^ (1/n : ℝ)) x]
      _ = (n : ℝ)⁻¹ * (x ^ ((1/n : ℝ) - 1)) := by
        rw [Real.rpow_sub hx_pos (1/n : ℝ) 1, Real.rpow_one x]
      _ = (n : ℝ)⁻¹ * x ^ ((n : ℝ)⁻¹ - 1) := by
        simp [one_div]
  rw [h_simplify] at h_hasDerivAt
  exact h_hasDerivAt.hasDerivWithinAt

/-- Exercise 10.4.2(a) -/
example (q:ℚ) {x:ℝ} (hx: x ∈ Set.Ioi 0) :
  HasDerivWithinAt (fun x:ℝ ↦ x^(q:ℝ)) (q * x^(q-1:ℝ)) (.Ioi 0) x := by
  have hx_pos : 0 < x := Set.mem_Ioi.mp hx
  have hx_ne : x ≠ 0 := by linarith
  have hlog : HasDerivAt Real.log (x⁻¹) x := Real.hasDerivAt_log hx_ne
  have hlog_mul : HasDerivAt (fun x : ℝ => (q : ℝ) * Real.log x) ((q : ℝ) * x⁻¹) x := by
    simpa using (HasDerivAt.const_mul (q : ℝ) hlog)
  have hexp_at : HasDerivAt Real.exp (Real.exp ((q : ℝ) * Real.log x)) ((q : ℝ) * Real.log x) :=
    Real.hasDerivAt_exp ((q : ℝ) * Real.log x)
  have hcomp : HasDerivAt (Real.exp ∘ (fun x : ℝ => (q : ℝ) * Real.log x))
      (Real.exp ((q : ℝ) * Real.log x) * ((q : ℝ) * x⁻¹)) x :=
    HasDerivAt.comp x hexp_at hlog_mul
  have heq : (Real.exp ∘ (fun x : ℝ => (q : ℝ) * Real.log x)) =ᶠ[nhds x] (fun x : ℝ => x ^ (q : ℝ)) := by
    have h_open : Set.Ioi (0 : ℝ) ∈ nhds x := IsOpen.mem_nhds isOpen_Ioi hx_pos
    apply Filter.eventuallyEq_of_mem h_open
    intro y hy
    dsimp
    rw [Real.rpow_def_of_pos hy, mul_comm]
  have h_hasDerivAt : HasDerivAt (fun x : ℝ => x ^ (q : ℝ))
      (Real.exp ((q : ℝ) * Real.log x) * ((q : ℝ) * x⁻¹)) x :=
    hcomp.congr_of_eventuallyEq heq.symm
  have h_simplify : Real.exp ((q : ℝ) * Real.log x) * ((q : ℝ) * x⁻¹) = (q : ℝ) * x ^ ((q : ℝ) - 1) := by
    calc
      Real.exp ((q : ℝ) * Real.log x) * ((q : ℝ) * x⁻¹) = (x ^ (q : ℝ)) * ((q : ℝ) * x⁻¹) := by
        rw [Real.rpow_def_of_pos hx_pos, mul_comm (Real.log x) (q : ℝ)]
      _ = (q : ℝ) * (x ^ (q : ℝ) * x⁻¹) := by ring
      _ = (q : ℝ) * x ^ ((q : ℝ) - 1) := by
        rw [Real.rpow_sub hx_pos (q : ℝ) 1, Real.rpow_one x]
        ring
  rw [h_simplify] at h_hasDerivAt
  exact h_hasDerivAt.hasDerivWithinAt

/-- Exercise 10.4.2(b) -/
example (q:ℚ) : (nhdsWithin 1 (.Ioi 0 \ {1})).Tendsto (fun x:ℝ ↦ (x^(q:ℝ)-1)/(x-1)) (nhds q) := by
  have h_hasDerivAt : HasDerivAt (fun x : ℝ ↦ x ^ (q : ℝ)) (q : ℝ) (1 : ℝ) := by
    have h_one_ne : (1 : ℝ) ≠ 0 := by norm_num
    have hlog : HasDerivAt Real.log ((1 : ℝ)⁻¹) (1 : ℝ) := Real.hasDerivAt_log h_one_ne
    have hlog_mul : HasDerivAt (fun x : ℝ => (q : ℝ) * Real.log x) ((q : ℝ) * ((1 : ℝ)⁻¹)) (1 : ℝ) := by
      simpa using (HasDerivAt.const_mul (q : ℝ) hlog)
    have hexp_at : HasDerivAt Real.exp (Real.exp ((q : ℝ) * Real.log (1 : ℝ))) ((q : ℝ) * Real.log (1 : ℝ)) :=
      Real.hasDerivAt_exp ((q : ℝ) * Real.log (1 : ℝ))
    have hcomp : HasDerivAt (Real.exp ∘ (fun x : ℝ => (q : ℝ) * Real.log x))
      (Real.exp ((q : ℝ) * Real.log (1 : ℝ)) * ((q : ℝ) * ((1 : ℝ)⁻¹))) (1 : ℝ) :=
      HasDerivAt.comp (1 : ℝ) hexp_at hlog_mul
    have heq : (Real.exp ∘ (fun x : ℝ => (q : ℝ) * Real.log x)) =ᶠ[nhds (1 : ℝ)] (fun x : ℝ => x ^ (q : ℝ)) := by
      have h_open : Set.Ioi (0 : ℝ) ∈ nhds (1 : ℝ) := IsOpen.mem_nhds isOpen_Ioi (by norm_num : (0 : ℝ) < 1)
      apply Filter.eventuallyEq_of_mem h_open
      intro y hy
      dsimp
      rw [Real.rpow_def_of_pos hy, mul_comm]
    have h_hasDerivAt' : HasDerivAt (fun x : ℝ => x ^ (q : ℝ))
      (Real.exp ((q : ℝ) * Real.log (1 : ℝ)) * ((q : ℝ) * ((1 : ℝ)⁻¹))) (1 : ℝ) :=
      hcomp.congr_of_eventuallyEq heq.symm
    have h_simplify : Real.exp ((q : ℝ) * Real.log (1 : ℝ)) * ((q : ℝ) * ((1 : ℝ)⁻¹)) = (q : ℝ) := by
      simp
    rw [h_simplify] at h_hasDerivAt'
    exact h_hasDerivAt'
  have h_iff := (HasDerivWithinAt.iff (.Ioi (0 : ℝ)) (1 : ℝ) (fun x : ℝ ↦ x ^ (q : ℝ)) (q : ℝ)).mp
    h_hasDerivAt.hasDerivWithinAt
  simpa [Real.one_rpow] using h_iff

/-- Exercise 10.4.3(a) -/
example (α:ℝ) : (nhdsWithin 1 (.Ioi 0 \ {1})).Tendsto (fun x:ℝ ↦ (x^α-1^α)/(x-1)) (nhds α) := by
  have h_hasDerivAt : HasDerivAt (fun x : ℝ ↦ x ^ α) α (1 : ℝ) := by
    have h_one_ne : (1 : ℝ) ≠ 0 := by norm_num
    have hlog : HasDerivAt Real.log ((1 : ℝ)⁻¹) (1 : ℝ) := Real.hasDerivAt_log h_one_ne
    have hlog_mul : HasDerivAt (fun x : ℝ => α * Real.log x) (α * ((1 : ℝ)⁻¹)) (1 : ℝ) := by
      simpa using (HasDerivAt.const_mul α hlog)
    have hexp_at : HasDerivAt Real.exp (Real.exp (α * Real.log (1 : ℝ))) (α * Real.log (1 : ℝ)) :=
      Real.hasDerivAt_exp (α * Real.log (1 : ℝ))
    have hcomp : HasDerivAt (Real.exp ∘ (fun x : ℝ => α * Real.log x))
      (Real.exp (α * Real.log (1 : ℝ)) * (α * ((1 : ℝ)⁻¹))) (1 : ℝ) :=
      HasDerivAt.comp (1 : ℝ) hexp_at hlog_mul
    have heq : (Real.exp ∘ (fun x : ℝ => α * Real.log x)) =ᶠ[nhds (1 : ℝ)] (fun x : ℝ => x ^ α) := by
      have h_open : Set.Ioi (0 : ℝ) ∈ nhds (1 : ℝ) := IsOpen.mem_nhds isOpen_Ioi (by norm_num : (0 : ℝ) < 1)
      apply Filter.eventuallyEq_of_mem h_open
      intro y hy
      dsimp
      rw [Real.rpow_def_of_pos hy, mul_comm]
    have h_hasDerivAt' : HasDerivAt (fun x : ℝ => x ^ α)
      (Real.exp (α * Real.log (1 : ℝ)) * (α * ((1 : ℝ)⁻¹))) (1 : ℝ) :=
      hcomp.congr_of_eventuallyEq heq.symm
    have h_simplify : Real.exp (α * Real.log (1 : ℝ)) * (α * ((1 : ℝ)⁻¹)) = α := by
      simp
    rw [h_simplify] at h_hasDerivAt'
    exact h_hasDerivAt'
  have h_iff := (HasDerivWithinAt.iff (.Ioi (0 : ℝ)) (1 : ℝ) (fun x : ℝ ↦ x ^ α) α).mp
    h_hasDerivAt.hasDerivWithinAt
  simpa [Real.one_rpow] using h_iff

/-- Exercise 10.4.3(b) -/
example (α:ℝ) {x:ℝ} (hx: x ∈ Set.Ioi 0) : HasDerivWithinAt (fun x:ℝ ↦ x^α) (α * x^(α-1)) (.Ioi 0) x := by
  have hx_pos : 0 < x := Set.mem_Ioi.mp hx
  have hx_ne : x ≠ 0 := by linarith
  have hlog : HasDerivAt Real.log (x⁻¹) x := Real.hasDerivAt_log hx_ne
  have hlog_mul : HasDerivAt (fun x : ℝ => α * Real.log x) (α * x⁻¹) x := by
    simpa using (HasDerivAt.const_mul α hlog)
  have hexp_at : HasDerivAt Real.exp (Real.exp (α * Real.log x)) (α * Real.log x) :=
    Real.hasDerivAt_exp (α * Real.log x)
  have hcomp : HasDerivAt (Real.exp ∘ (fun x : ℝ => α * Real.log x))
    (Real.exp (α * Real.log x) * (α * x⁻¹)) x :=
    HasDerivAt.comp x hexp_at hlog_mul
  have heq : (Real.exp ∘ (fun x : ℝ => α * Real.log x)) =ᶠ[nhds x] (fun x : ℝ => x ^ α) := by
    have h_open : Set.Ioi (0 : ℝ) ∈ nhds x := IsOpen.mem_nhds isOpen_Ioi hx_pos
    apply Filter.eventuallyEq_of_mem h_open
    intro y hy
    dsimp
    rw [Real.rpow_def_of_pos hy, mul_comm]
  have h_hasDerivAt : HasDerivAt (fun x : ℝ => x ^ α)
    (Real.exp (α * Real.log x) * (α * x⁻¹)) x :=
    hcomp.congr_of_eventuallyEq heq.symm
  have h_simplify : Real.exp (α * Real.log x) * (α * x⁻¹) = α * x ^ (α - 1) := by
    calc
      Real.exp (α * Real.log x) * (α * x⁻¹) = (x ^ α) * (α * x⁻¹) := by
        rw [Real.rpow_def_of_pos hx_pos, mul_comm (Real.log x) α]
      _ = α * (x ^ α * x⁻¹) := by ring
      _ = α * x ^ (α - 1) := by
        rw [Real.rpow_sub hx_pos α 1, Real.rpow_one x]
        ring
  rw [h_simplify] at h_hasDerivAt
  exact h_hasDerivAt.hasDerivWithinAt

end Chapter10
