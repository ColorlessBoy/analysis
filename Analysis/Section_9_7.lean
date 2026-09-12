import Mathlib.Tactic
import Analysis.Section_9_3
import Analysis.Section_9_4


/-!
# Analysis I, Section 9.7: The intermediate value theorem

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- The intermediate value theorem.
-/

namespace Chapter9

/-- Theorem 9.7.1 (Intermediate value theorem) -/
private lemma intermediate_value_aux {a b:ℝ} (hab: a < b) {f:ℝ → ℝ} (hf: ContinuousOn f (.Icc a b)) {y:ℝ}
    (hya : f a < y) (hyb : y < f b) : ∃ c ∈ Set.Icc a b, f c = y := by
  set E := {x | x ∈ Set.Icc a b ∧ f x < y}
  have hE : E ⊆ .Icc a b := fun x ⟨hx₁, hx₂⟩ ↦ hx₁
  have hE_bdd : BddAbove E := bddAbove_Icc.mono hE
  have hEa : a ∈ E := by simp [E, hya, le_of_lt hab]
  have hE_nonempty : E.Nonempty := by use a
  set c := sSup E
  have hc : c ∈ Set.Icc a b := by
    simp; split_ands
    . solve_by_elim [le_csSup]
    convert csSup_le_csSup bddAbove_Icc hE_nonempty hE
    grind [csSup_Icc]
  use c, hc
  have hfc_upper : f c ≤ y := by
    have hxe (n:ℕ) : ∃ x ∈ E, c - 1/(n+1:ℝ) < x := by
      have : 1/(n+1:ℝ) > 0 := by positivity
      replace : c - 1/(n+1:ℝ) < sSup E := by linarith
      solve_by_elim [exists_lt_of_lt_csSup]
    set x := fun n ↦ (hxe n).choose
    have hx1 (n:ℕ) : x n ∈ E := (hxe n).choose_spec.1
    have hx2 (n:ℕ) : c - 1/(n+1:ℝ) < x n := (hxe n).choose_spec.2
    have : Filter.atTop.Tendsto x (nhds c) := by
      apply Filter.Tendsto.squeeze (g := fun j ↦ c - 1/(j+1:ℝ)) (h := fun j ↦ c) (f := x)
      . convert tendsto_one_div_add_atTop_nhds_zero_nat.const_sub c;simp
      . exact tendsto_const_nhds
      . exact fun n ↦ le_of_lt (hx2 n)
      exact fun n ↦ le_csSup hE_bdd (hx1 n)
    replace := this.comp_of_continuous (hf.continuousWithinAt hc) (fun n ↦ hE (hx1 n))
    have hfxny (n:ℕ) : f (x n) ≤ y := by specialize hx1 n; simp [E] at hx1; grind
    exact le_of_tendsto' this hfxny
  have hne : c < b := by grind
  have hfc_lower : y ≤ f c := by
    have : ∃ N:ℕ, ∀ n ≥ N, (c+1/(n+1:ℝ)) < b := by
      choose N hN using exists_nat_gt (1/(b-c))
      use N; intro n hn
      have hpos : 0 < b-c := by linarith
      have : 1/(n+1:ℝ) < b-c := by rw [one_div_lt] <;> (try positivity); apply hN.trans; norm_cast; linarith
      linarith
    choose N hN using this
    have hmem : ∀ n ≥ N, (c + 1/(n+1:ℝ)) ∈ Set.Icc a b := by
      intro n hn
      simp [-one_div, le_of_lt (hN n hn)]
      have : 1/(n+1:ℝ) > 0 := by positivity
      replace : c + 1/(n+1:ℝ) > c := by linarith
      grind
    have : ∀ n ≥ N, c + 1/(n+1:ℝ) ∉ E := by
      intro n _
      have : 1/(n+1:ℝ) > 0 := by positivity
      replace : c + 1/(n+1:ℝ) > c := by linarith
      solve_by_elim [notMem_of_csSup_lt]
    replace : ∀ n ≥ N, f (c + 1/(n+1:ℝ)) ≥ y := by
      intro n hn; specialize this n hn; contrapose! this
      simp [E]
      have := hmem n hn
      simp_all
    have hconv : Filter.atTop.Tendsto (fun n:ℕ ↦ c + 1/(n+1:ℝ)) (nhds c) := by
      convert tendsto_one_div_add_atTop_nhds_zero_nat.const_add c; simp
    replace hf := (hf.continuousWithinAt hc).tendsto
    rw [nhdsWithin.eq_1] at hf
    have hconv' : Filter.atTop.Tendsto (fun n:ℕ ↦ c + 1/(n+1:ℝ)) (.principal (.Icc a b)) := by
      simp [-one_div, -Set.mem_Icc]; use N
    replace hconv' := Filter.tendsto_inf.mpr ⟨ hconv, hconv' ⟩
    apply ge_of_tendsto (hf.comp hconv') _
    simp [-one_div]; use N
  linarith

theorem intermediate_value {a b:ℝ} (hab: a < b) {f:ℝ → ℝ} (hf: ContinuousOn f (.Icc a b)) {y:ℝ} (hy: y ∈ Set.Icc (f a) (f b) ∨ y ∈ Set.Icc (f b) (f a)) :
  ∃ c ∈ Set.Icc a b, f c = y := by
  obtain hy_left | hy_right := hy
  · by_cases hya : y = f a; use a; grind
    by_cases hyb : y = f b; use b; grind
    simp at hy_left
    replace hya : f a < y := by grind
    replace hyb : y < f b := by grind
    exact intermediate_value_aux hab hf hya hyb
  · rcases hy_right with ⟨hy1, hy2⟩
    by_cases hya : y = f a; use a; grind
    by_cases hyb : y = f b; use b; grind
    have hya' : y < f a := by exact Ne.lt_of_le hya hy2
    have hyb' : f b < y := by exact Ne.lt_of_le (Ne.symm hyb) hy1
    have h_neg : ContinuousOn (-f) (Set.Icc a b) := hf.neg
    have hy_neg_left : (-f) a < -y := by
      have : (-f) a = -(f a) := rfl
      rw [this]; linarith
    have hy_neg_right : -y < (-f) b := by
      have : (-f) b = -(f b) := rfl
      rw [this]; linarith
    rcases intermediate_value_aux hab h_neg hy_neg_left hy_neg_right with ⟨c, hc, hc_eq⟩
    refine ⟨c, hc, ?_⟩
    simpa using hc_eq

open Classical in
noncomputable abbrev f_9_7_1 : ℝ → ℝ := fun x ↦ if x ≤ 0 then -1 else 1

example : 0 ∈ Set.Icc (f_9_7_1 (-1)) (f_9_7_1 1) ∧ ¬ ∃ x ∈ Set.Icc (-1) 1, f_9_7_1 x = 0 := by
  constructor
  · unfold f_9_7_1; norm_num
  · intro h
    rcases h with ⟨x, ⟨hx1, hx2⟩, hx0⟩
    dsimp [f_9_7_1] at hx0
    split at hx0
    · linarith
    · linarith

/-- Remark 9.7.2 -/
abbrev f_9_7_2 : ℝ → ℝ := fun x ↦ x^3 - x

example : f_9_7_2 (-2) = -6 := by unfold f_9_7_2; norm_num
example : f_9_7_2 2 = 6 := by unfold f_9_7_2; norm_num
example : f_9_7_2 (-1) = 0 := by unfold f_9_7_2; norm_num
example : f_9_7_2 0 = 0 := by unfold f_9_7_2; norm_num
example : f_9_7_2 1 = 0 := by unfold f_9_7_2; norm_num

/-- Remark 9.7.3 -/
example : ∃ x:ℝ, 0 ≤ x ∧ x ≤ 2 ∧ x^2 = 2 := by
  have h_cont : ContinuousOn (fun x : ℝ ↦ x^2) (Set.Icc (0:ℝ) 2) :=
    (continuous_id.pow 2).continuousOn
  have hy : (2:ℝ) ∈ Set.Icc ((fun x : ℝ ↦ x^2) 0) ((fun x : ℝ ↦ x^2) 2) := by
    norm_num
  rcases intermediate_value (by norm_num : (0:ℝ) < 2) h_cont (Or.inl hy) with ⟨c, hc, hc_sq⟩
  exact ⟨c, hc.1, hc.2, hc_sq⟩

/-- Corollary 9.7.4 (Images of continuous functions) / Exercise 9.7.1 -/
theorem continuous_image_Icc {a b:ℝ} (hab: a < b) {f:ℝ → ℝ} (hf: ContinuousOn f (.Icc a b)) {y:ℝ} (hy: sInf (f '' .Icc a b) ≤ y ∧ y ≤ sSup (f '' .Icc a b)) : ∃ c ∈ Set.Icc a b, f c = y := by
  rcases hy with ⟨hy1, hy2⟩
  have h_nonempty : (Set.Icc a b).Nonempty := Set.nonempty_Icc.mpr (le_of_lt hab)
  have h_compact : IsCompact (Set.Icc a b) := isCompact_Icc
  have h_image_nonempty : (f '' Set.Icc a b).Nonempty := Set.image_nonempty.mpr h_nonempty
  have h_bddBelow : BddBelow (f '' Set.Icc a b) := h_compact.bddBelow_image hf
  have h_bddAbove : BddAbove (f '' Set.Icc a b) := h_compact.bddAbove_image hf
  rcases h_compact.exists_isMinOn h_nonempty hf with ⟨c₁, hc₁, hc₁_min⟩
  rcases h_compact.exists_isMaxOn h_nonempty hf with ⟨c₂, hc₂, hc₂_max⟩
  have h_sInf : sInf (f '' Set.Icc a b) = f c₁ := by
    refine le_antisymm (csInf_le h_bddBelow ⟨c₁, hc₁, rfl⟩) ?_
    refine le_csInf h_image_nonempty ?_
    rintro _ ⟨x, hx, rfl⟩; exact hc₁_min hx
  have h_sSup : sSup (f '' Set.Icc a b) = f c₂ := by
    refine le_antisymm (csSup_le h_image_nonempty ?_) (le_csSup h_bddAbove ⟨c₂, hc₂, rfl⟩)
    rintro _ ⟨x, hx, rfl⟩; exact hc₂_max hx
  have hy1' : f c₁ ≤ y := by
    rw [h_sInf] at hy1; exact hy1
  have hy2' : y ≤ f c₂ := by
    rw [h_sSup] at hy2; exact hy2
  by_cases h : c₁ ≤ c₂
  · by_cases h_eq : c₁ = c₂
    · subst h_eq; exact ⟨c₁, hc₁, le_antisymm hy1' hy2'⟩
    · have hf_sub : ContinuousOn f (Set.Icc c₁ c₂) := hf.mono (Set.Icc_subset_Icc hc₁.1 hc₂.2)
      rcases intermediate_value (h.lt_of_ne h_eq) hf_sub (Or.inl ⟨hy1', hy2'⟩) with ⟨c, hc, hc_eq⟩
      exact ⟨c, Set.Icc_subset_Icc hc₁.1 hc₂.2 hc, hc_eq⟩
  · push_neg at h
    by_cases h_eq : c₁ = c₂
    · subst h_eq; exact ⟨c₁, hc₁, le_antisymm hy1' hy2'⟩
    · have hf_sub : ContinuousOn f (Set.Icc c₂ c₁) := hf.mono (Set.Icc_subset_Icc hc₂.1 hc₁.2)
      rcases intermediate_value h hf_sub (Or.inr ⟨hy1', hy2'⟩) with ⟨c, hc, hc_eq⟩
      exact ⟨c, Set.Icc_subset_Icc hc₂.1 hc₁.2 hc, hc_eq⟩

theorem continuous_image_Icc' {a b:ℝ} (hab: a < b) {f:ℝ → ℝ} (hf: ContinuousOn f (.Icc a b)) : f '' .Icc a b = .Icc (sInf (f '' .Icc a b)) (sSup (f '' .Icc a b)) := by
  ext y; constructor
  · rintro ⟨x, hx, rfl⟩
    have h_compact : IsCompact (Set.Icc a b) := isCompact_Icc
    have h_bddBelow : BddBelow (f '' Set.Icc a b) := h_compact.bddBelow_image hf
    have h_bddAbove : BddAbove (f '' Set.Icc a b) := h_compact.bddAbove_image hf
    exact ⟨csInf_le h_bddBelow ⟨x, hx, rfl⟩, le_csSup h_bddAbove ⟨x, hx, rfl⟩⟩
  · intro hy
    rcases hy with ⟨hy1, hy2⟩
    exact continuous_image_Icc hab hf ⟨hy1, hy2⟩

/-- Exercise 9.7.2 -/
theorem exists_fixed_pt {f:ℝ → ℝ} (hf: ContinuousOn f (.Icc 0 1)) (hmap: f '' .Icc 0 1 ⊆ .Icc 0 1) : ∃ x ∈ Set.Icc 0 1, f x = x := by
  have hg : ContinuousOn (fun x : ℝ ↦ f x - x) (Set.Icc (0 : ℝ) 1) := hf.sub continuousOn_id
  have hf0 : f 0 ∈ Set.Icc (0 : ℝ) 1 := hmap ⟨0, Set.left_mem_Icc.mpr (by norm_num), rfl⟩
  have hf1 : f 1 ∈ Set.Icc (0 : ℝ) 1 := hmap ⟨1, Set.right_mem_Icc.mpr (by norm_num), rfl⟩
  have h0 : (0 : ℝ) ∈ Set.Icc ((fun x : ℝ ↦ f x - x) 1) ((fun x : ℝ ↦ f x - x) 0) :=
    ⟨by
      have : f 1 ≤ 1 := hf1.2
      linarith,
     by
      have : f 0 ≥ 0 := hf0.1
      linarith⟩
  rcases intermediate_value (by norm_num : (0 : ℝ) < 1) hg (Or.inr h0) with ⟨c, hc, hc_eq⟩
  refine ⟨c, hc, ?_⟩
  linarith

end Chapter9
