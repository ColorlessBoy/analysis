import Mathlib.Tactic
/-!
# Analysis I, Section 9.10: Limits at infinity

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Bare-bones API for the Mathlib versions of adherent at infinity, and limits at infinity.
-/

namespace Chapter9

/-- Definition 9.10.1 (Infinite adherent point).  We use {lean}`¬ BddAbove X` as our notation for `+∞` being an adherent point -/
theorem BddAbove.unbounded_iff (X:Set ℝ) : ¬ BddAbove X ↔ ∀ M, ∃ x ∈ X, x > M := by
  simp [bddAbove_def]

theorem BddAbove.unbounded_iff' (X:Set ℝ) : ¬ BddAbove X ↔ sSup ((fun x:ℝ ↦ (x:EReal)) '' X) = ⊤ := by
  erw [sSup_eq_top, unbounded_iff]
  constructor
  . intro h M hM; choose x hx hxM using h M.toReal
    use x, ⟨x, hx, rfl⟩; revert M; simp [EReal.forall]; tauto
  intro h M; specialize h (M:EReal) (EReal.coe_lt_top M)
  obtain ⟨_, ⟨x, hx, rfl⟩, hMx⟩ := h; exact ⟨x, hx, EReal.coe_lt_coe_iff.mp hMx⟩

theorem BddBelow.unbounded_iff (X:Set ℝ) : ¬ BddBelow X ↔ ∀ M, ∃ x ∈ X, x < M := by
  simp [bddBelow_def]

theorem BddBelow.unbounded_iff' (X:Set ℝ) : ¬ BddBelow X ↔ sInf ((fun x:ℝ ↦ (x:EReal)) '' X) = ⊥ := by
  simp [sInf_eq_bot, unbounded_iff]
  constructor
  . intro h M hM; choose x hx hxM using h M.toReal
    use x, hx; revert M; simp [EReal.forall]
  intro h M; specialize h (M:EReal) ?_ <;>simp_all

/-- Definition 9.10.13 (Limit at infinity) -/
theorem Filter.Tendsto.AtTop.iff {X: Set ℝ} (f:ℝ → ℝ) (L:ℝ) : Filter.Tendsto f (.atTop ⊓ .principal X) (nhds L) ↔ ∀ ε > (0:ℝ), ∃ M, ∀ x ∈ X ∩ .Ici M, |f x - L| < ε := by
  rw [LinearOrderedAddCommGroup.tendsto_nhds]
  peel with ε hε
  simp [Filter.eventually_inf_principal]
  aesop

/-- Exercise 9.10.4 -/
example : Filter.Tendsto (fun x:ℝ ↦ 1/x) (.atTop ⊓ .principal (.Ioi 0)) (nhds 0) := by
  simpa using (tendsto_inv_atTop_zero (𝕜 := ℝ)).mono_left inf_le_left

open Classical in
/-- Exercise 9.10.1 -/
example (a:ℕ → ℝ) (L:ℝ) : Filter.Tendsto (fun x:ℝ ↦ (if h:(∃ n:ℕ, x = n) then a h.choose else 0)) (.atTop ⊓ .principal ((fun n:ℕ ↦ (n:ℝ)) '' .univ)) (nhds L) ↔ Filter.atTop.Tendsto a (nhds L) := by
  constructor
  · intro h
    have h_incl : Filter.Tendsto (fun (n : ℕ) ↦ (n : ℝ)) Filter.atTop (.atTop ⊓ .principal ((fun n : ℕ ↦ (n : ℝ)) '' Set.univ)) := by
      refine Filter.tendsto_inf.mpr ⟨tendsto_natCast_atTop_atTop (R := ℝ), ?_⟩
      simp
    simpa [Function.comp_def] using h.comp h_incl
  · intro h
    rw [LinearOrderedAddCommGroup.tendsto_nhds] at h ⊢
    intro ε hε
    have hN : ∃ N : ℕ, ∀ n : ℕ, n ≥ N → |a n - L| < ε := by
      simpa [Filter.eventually_atTop] using h ε hε
    rcases hN with ⟨N, hN⟩
    refine Filter.mem_inf_principal.mpr ?_
    refine Filter.mem_atTop_sets.mpr ⟨(N : ℝ), ?_⟩
    intro x hx hx_S
    rcases hx_S with ⟨n, _, hn⟩
    subst hn
    have hn' : n ≥ N := by
      exact_mod_cast (show (n : ℝ) ≥ (N : ℝ) from hx)
    simp [hN n hn']

end Chapter9
