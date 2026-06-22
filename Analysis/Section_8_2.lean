import Mathlib.Tactic
import Analysis.Section_7_2
import Analysis.Section_7_3
import Analysis.Section_7_4
import Analysis.Section_8_1

/-!
# Analysis I, Section 8.2: Summation on infinite sets

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Absolute convergence and summation on countably infinite or general sets.
- Connections with Mathlib's {name}`Summable` and {name}`tsum`.
- The Riemann rearrangement theorem.

Some non-trivial API is provided beyond what is given in the textbook in order connect these
notions with existing summation notions.

After this section, the summation notation developed here will be deprecated in favor of Mathlib's API for {name}`Summable` and {name}`tsum`.

-/

namespace Chapter8
open Chapter7 Chapter7.Series Finset Function Filter

/-- Definition 8.2.1 (Series on countable sets).  Note that with this definition, functions defined
on finite sets will not be absolutely convergent; one should use {lit}`AbsConvergent'` instead for such
cases.-/
abbrev AbsConvergent {X:Type} (f: X → ℝ) : Prop := ∃ g: ℕ → X, Bijective g ∧ (f ∘ g: Series).absConverges

theorem AbsConvergent.mk {X: Type} {f:X → ℝ} {g:ℕ → X} (h: Bijective g) (hfg: (f ∘ g:Series).absConverges) : AbsConvergent f := by use g

open Classical in
/-- The definition has been chosen to give a sensible value when {name}`X` is finite, even though
{name}`AbsConvergent` is by definition false in this context. -/
noncomputable abbrev Sum {X:Type} (f: X → ℝ) : ℝ := if h: AbsConvergent f then (f ∘ h.choose:Series).sum else
  if _hX: Finite X then (∑ x ∈ @univ X (Fintype.ofFinite X), f x) else 0

theorem Sum.of_finite {X:Type} [hX:Finite X] (f:X → ℝ) : Sum f = ∑ x ∈ @Finset.univ X (Fintype.ofFinite X), f x := by
  have : ¬ AbsConvergent f := by
    by_contra!; choose g hg _ using this
    rw [←hg.finite_iff, ←not_infinite_iff_finite] at hX; apply hX; infer_instance
  simp [Sum, this, hX]

theorem AbsConvergent.comp {X: Type} {f:X → ℝ} {g:ℕ → X} (h: Bijective g) (hf: AbsConvergent f) : (f ∘ g:Series).absConverges := by
  choose g' hbij hconv using hf
  choose g'_inv hleft hright using bijective_iff_has_inverse.mp hbij
  have hG : Bijective (g'_inv ∘ g) := .comp ⟨hright.injective, hleft.surjective⟩ h
  convert (absConverges_of_permute hconv hG).1 using 4 with n
  simp [hright (g n.toNat)]

theorem Sum.eq {X: Type} {f:X → ℝ} {g:ℕ → X} (h: Bijective g) (hfg: (f ∘ g:Series).absConverges) : (f ∘ g:Series).convergesTo (Sum f) := by
  have : AbsConvergent f := .mk h hfg
  simp [Sum, this]
  choose hbij hconv using this.choose_spec
  set g' := this.choose
  choose g'_inv hleft hright using bijective_iff_has_inverse.mp hbij
  convert convergesTo_sum (converges_of_absConverges hfg) using 1
  have hG : Bijective (g'_inv ∘ g) := .comp ⟨hright.injective, hleft.surjective⟩ h
  convert (absConverges_of_permute hconv hG).2 using 4 with _ n
  by_cases hn : n ≥ 0 <;> simp [hn, hright (g n.toNat)]

theorem Sum.of_comp {X Y:Type} {f:X → ℝ} (h: AbsConvergent f) {g: Y → X} (hbij: Bijective g) : AbsConvergent (f ∘ g) ∧ Sum f = Sum (f ∘ g) := by
  choose g' hbij' hconv' using h
  choose g_inv hleft hright using bijective_iff_has_inverse.mp hbij
  have hbij_g_inv_g' : Bijective (g_inv ∘ g') := .comp ⟨hright.injective, hleft.surjective⟩ hbij'
  have hident : (f ∘ g) ∘ g_inv ∘ g' = f ∘ g' := by ext n; simp [hright (g' n)]
  refine ⟨ ⟨ g_inv ∘ g', ⟨ hbij_g_inv_g', by convert hconv' ⟩ ⟩, ?_ ⟩
  have h := eq (f := f ∘ g) hbij_g_inv_g' (by convert hconv')
  rw [hident] at h
  solve_by_elim [convergesTo_uniq, eq]

@[simp]
theorem Finset.Icc_eq_cast (N:ℕ) : Icc 0 (N:ℤ) = map Nat.castEmbedding (.Icc 0 N) := by
  ext n; simp; constructor
  . intro ⟨ hn, _ ⟩; lift n to ℕ using hn; use n; simp_all
  rintro ⟨ _, ⟨ _, rfl ⟩ ⟩; simp_all

theorem Finset.Icc_empty {N:ℤ} (h: ¬ N ≥ 0) : Icc 0 N = ∅ := by
  ext; simp; intros; contrapose! h; linarith

/-- Theorem 8.2.2, preliminary version.  The arguments here are rearranged slightly from the text. -/
theorem sum_of_sum_of_AbsConvergent_nonneg {f:ℕ × ℕ → ℝ} (hf:AbsConvergent f) (hpos: ∀ n m, 0 ≤ f (n, m)) :
  (∀ n, ((fun m ↦ f (n, m)):Series).converges) ∧
  (fun n ↦ ((fun m ↦ f (n, m)):Series).sum:Series).convergesTo (Sum f) := by
  set L := Sum f
  set a : ℕ → Series := fun n ↦ ((fun m ↦ f (n, m)):Series)
  have hLpos : 0 ≤ L := by
    simp [L, Sum, hf]; apply sum_of_nonneg; intro n; by_cases h: n ≥ 0 <;> simp [h]; grind
  have hfinsum (X: Finset (ℕ × ℕ)) : ∑ p ∈ X, f p ≤ L := by
    have ⟨ g, hg, hconv ⟩ := hf
    have hsum := Sum.eq hg hconv
    have hnonneg : (f ∘ g : Series).nonneg := by
      intro n; simp [hpos]
    choose g_inv hleft hright using bijective_iff_has_inverse.mp hg
    have hsurj : Function.Surjective g := hg.2
    have hn_of_p (p : ℕ×ℕ) : ℕ := (hsurj p).choose
    have hg_n_of_p (p : ℕ×ℕ) : g (hn_of_p p) = p := (hsurj p).choose_spec
    let N := X.sup hn_of_p
    have hN (p) (hp : p ∈ X) : hn_of_p p ≤ N := Finset.le_sup (s := X) (f := hn_of_p) hp
    have hX_subset : X ⊆ (Finset.Icc 0 (N : ℤ)).image g := by
      intro p hp; apply Finset.mem_image.mpr
      refine ⟨ hn_of_p p, Finset.mem_Icc.mpr ⟨ by omega, by exact_mod_cast hN p hp ⟩, hg_n_of_p p ⟩
    calc
      ∑ p ∈ X, f p ≤ ∑ p ∈ (Finset.Icc 0 (N : ℤ)).image g, f p :=
        Finset.sum_le_sum_of_subset hX_subset
      _ = ∑ n ∈ Finset.Icc 0 (N : ℤ), (f ∘ g) n := by
        symm; apply Finset.sum_image; intro x hx y hy h; exact hg.1 h
      _ = (f ∘ g : Series).partial (N : ℤ) := rfl
      _ ≤ L := partial_le_sum_of_nonneg hnonneg (converges_of_absConverges hconv) (N : ℤ)
  have hfinsum' (n M:ℕ) : (a n).partial M ≤ L := by
    simp [a, Series.partial, Finset.Icc_eq_cast]
    convert_to ∑ x ∈ .map (Embedding.sectR n ℕ) (.Icc 0 M), f x ≤ L
    . simp
    solve_by_elim
  have hnon (n:ℕ) : (a n).nonneg := by
    simp [a, nonneg]; intro m; split_ifs <;> simp [hpos]
  have hconv (n:ℕ) : (a n).converges := by
    rw [converges_of_nonneg_iff (hnon n)]
    use L; intro N; by_cases h: N ≥ 0
    . lift N to ℕ using h; solve_by_elim
    rw [partial_of_lt (by simp [a]; linarith)]; simp [hLpos]
  have (N M:ℤ) : ∑ n ∈ Icc 0 N, (a n.toNat).partial M ≤ L := by
    by_cases hN : N ≥ 0; swap
    . simp [Finset.Icc_empty hN, hLpos]
    lift N to ℕ using hN
    by_cases hM : M ≥ 0; swap
    . convert hLpos; unfold Series.partial
      apply sum_eq_zero; intro n _
      simp [a, Finset.Icc_empty hM]
    lift M to ℕ using hM
    convert_to ∑ x ∈ (Icc 0 N) ×ˢ (.Icc 0 M), f x ≤ L
    . simp [a, sum_product, Series.partial]
    solve_by_elim
  replace (N:ℤ) : ∑ n ∈ Icc 0 N, (a n.toNat).sum ≤ L := by
    apply le_of_tendsto' (x := .atTop) (tendsto_finset_sum _ _) (this N)
    solve_by_elim [convergesTo_sum]
  replace (N:ℤ) : (fun n ↦ (a n).sum:Series).partial N ≤ L := by
    convert this N with n hn; simp_all
  have hnon' : (fun n ↦ (a n).sum:Series).nonneg := by
    intro n; simp; split_ifs
    . exact sum_of_nonneg (hnon n.toNat)
    simp
  have hconv' : (fun n ↦ (a n).sum:Series).converges := by
    rw [converges_of_nonneg_iff hnon']; use L
  replace : (fun n ↦ (a n).sum:Series).sum ≤ L := le_of_tendsto' (convergesTo_sum hconv') this
  replace : (fun n ↦ (a n).sum:Series).sum = L := by
    apply le_antisymm this (le_of_forall_sub_le _); intro ε hε
    replace : ∃ X, ∑ p ∈ X, f p ≥ L - ε := by
      have ⟨ g, hg, hconv ⟩ := hf
      have hsum := Sum.eq hg hconv
      have hLpos : 0 ≤ L := hLpos
      have hconv_nonneg : (f ∘ g : Series).nonneg := by
        intro n; simp [hpos]
      have h_conv_abs := converges_of_absConverges hconv
      have h_partial_tendsto : atTop.Tendsto (λ (N : ℤ) => (f ∘ g : Series).partial N) (nhds L) := hsum
      rcases Metric.tendsto_atTop h_partial_tendsto (Set.mem_setOf_eq.mp (by
        apply Metric.mem_nhds_iff.mpr
        refine ⟨ ε, hε, λ x hx => ?_ ⟩
        linarith)) with ⟨ N, hN ⟩
      have hN' : L - (f ∘ g : Series).partial N < ε := by
        have : |(f ∘ g : Series).partial N - L| < ε := hN N (le_refl N)
        have : L - (f ∘ g : Series).partial N ≤ |(f ∘ g : Series).partial N - L| := by
          nlinarith [h_partial_tendsto, hLpos]
        linarith
      use (Finset.Icc 0 N).image g
      calc
        ∑ p ∈ (Finset.Icc 0 N).image g, f p = ∑ n ∈ Finset.Icc 0 N, (f ∘ g) n := by
          symm; apply Finset.sum_image; intro x hx y hy h; exact hg.1 h
        _ = (f ∘ g : Series).partial N := rfl
        _ ≥ L - ε := by linarith
    choose X hX using this
    have : ∃ N, ∃ M, X ⊆ (Icc 0 N) ×ˢ (Icc 0 M) := by
      have hX_fin : Finset.Nonempty X ∨ X = ∅ := Finset.isEmpty_or_nonempty X
      cases' hX_fin with hne hempty
      · have hmax1 : ∃ N : ℕ, ∀ (p : ℕ×ℕ), p ∈ X → p.1 ≤ N := by
          use X.sup (λ p => p.1)
          intro p hp; exact Finset.le_sup (f := λ p => p.1) hp
        have hmax2 : ∃ M : ℕ, ∀ (p : ℕ×ℕ), p ∈ X → p.2 ≤ M := by
          use X.sup (λ p => p.2)
          intro p hp; exact Finset.le_sup (f := λ p => p.2) hp
        rcases hmax1 with ⟨ N, hN1 ⟩
        rcases hmax2 with ⟨ M, hM2 ⟩
        refine ⟨ N, M, λ p hp => ?_ ⟩
        have hp1_nonneg : 0 ≤ (p.1 : ℤ) := by omega
        have hp2_nonneg : 0 ≤ (p.2 : ℤ) := by omega
        have hp1_le : (p.1 : ℤ) ≤ N := by exact_mod_cast hN1 p hp
        have hp2_le : (p.2 : ℤ) ≤ M := by exact_mod_cast hM2 p hp
        simp; exact ⟨ ⟨ hp1_nonneg, hp1_le ⟩, ⟨ hp2_nonneg, hp2_le ⟩ ⟩
      · subst hempty; use 0, 0; simp
    choose N M hX' using this
    calc
      _ ≤ ∑ p ∈ X, f p := hX
      _ ≤ ∑ p ∈ (Icc 0 N) ×ˢ (Icc 0 M), f p := sum_le_sum_of_subset_of_nonneg hX' (by solve_by_elim)
      _ = ∑ n ∈ Icc 0 N, ∑ m ∈ Icc 0 M, f (n, m) := sum_product _ _ _
      _ ≤ ∑ n ∈ Icc 0 N, (a n).sum := by
        apply sum_le_sum; intro n _
        convert partial_le_sum_of_nonneg (hnon n) (hconv n) M
        simp [a, Series.partial]
      _ = (fun n ↦ (a n).sum:Series).partial N := by simp [Series.partial]
      _ ≤ _ := partial_le_sum_of_nonneg hnon' hconv' _
  simp [a, hconv, ← this, Series.convergesTo_sum hconv']

/-- Theorem 8.2.2, second version -/
theorem sum_of_sum_of_AbsConvergent {f:ℕ × ℕ → ℝ} (hf:AbsConvergent f) :
  (∀ n, ((fun m ↦ f (n, m)):Series).absConverges) ∧
  (fun n ↦ ((fun m ↦ f (n, m)):Series).sum:Series).convergesTo (Sum f) := by
  set fplus := max f 0
  set fminus := max (-f) 0
  have hfplus_nonneg : ∀ n m, 0 ≤ fplus (n, m) := by intro n m; simp [fplus]
  have hfminus_nonneg : ∀ n m, 0 ≤ fminus (n, m) := by intro n m; simp [fminus]
  have hdiff : f = fplus - fminus := by
    ext x; dsimp [fplus, fminus]; by_cases h : f x ≥ 0 <;> simp [h]
  have hfplus_conv : AbsConvergent fplus := by
    have ⟨ g, hg, hconv ⟩ := hf
    refine ⟨ g, hg, ?_ ⟩
    have h_abs_conv : (f ∘ g : Series).absConverges := hconv
    have h_nonneg_fplus : ∀ n, |(fplus ∘ g) n| ≤ |(f ∘ g) n| := by
      intro n; simp [fplus]; by_cases h : f (g n.toNat) ≥ 0 <;> simp [h]
    have h_nonneg_abs : (|(fplus ∘ g)| : Series).nonneg := by
      intro n; simp
    rw [absConverges, converges_of_nonneg_iff h_nonneg_abs]
    use (|(f ∘ g)| : Series).sum
    intro N; by_cases hN : N ≥ 0
    · lift N to ℕ using hN
      calc
        (|(fplus ∘ g)| : Series).partial N = ∑ n ∈ Icc 0 (N : ℤ), |(fplus ∘ g) n| := rfl
        _ ≤ ∑ n ∈ Icc 0 (N : ℤ), |(f ∘ g) n| := Finset.sum_le_sum (λ n hn => h_nonneg_fplus n)
        _ = (|(f ∘ g)| : Series).partial N := rfl
        _ ≤ (|(f ∘ g)| : Series).sum := partial_le_sum_of_nonneg (by intro n; simp) h_abs_conv (N : ℤ)
    · simp [Series.partial, show N < 0 from by omega]
  have hfminus_conv : AbsConvergent fminus := by
    have ⟨ g, hg, hconv ⟩ := hf
    refine ⟨ g, hg, ?_ ⟩
    have h_abs_conv : (f ∘ g : Series).absConverges := hconv
    have h_nonneg_fminus : ∀ n, |(fminus ∘ g) n| ≤ |(f ∘ g) n| := by
      intro n; simp [fminus]; by_cases h : f (g n.toNat) ≥ 0 <;> simp [h]
    have h_nonneg_abs : (|(fminus ∘ g)| : Series).nonneg := by
      intro n; simp
    rw [absConverges, converges_of_nonneg_iff h_nonneg_abs]
    use (|(f ∘ g)| : Series).sum
    intro N; by_cases hN : N ≥ 0
    · lift N to ℕ using hN
      calc
        (|(fminus ∘ g)| : Series).partial N = ∑ n ∈ Icc 0 (N : ℤ), |(fminus ∘ g) n| := rfl
        _ ≤ ∑ n ∈ Icc 0 (N : ℤ), |(f ∘ g) n| := Finset.sum_le_sum (λ n hn => h_nonneg_fminus n)
        _ = (|(f ∘ g)| : Series).partial N := rfl
        _ ≤ (|(f ∘ g)| : Series).sum := partial_le_sum_of_nonneg (by intro n; simp) h_abs_conv (N : ℤ)
    · simp [Series.partial, show N < 0 from by omega]
  choose hfplus_conv' hfplus_sum using sum_of_sum_of_AbsConvergent_nonneg hfplus_conv hfplus_nonneg
  choose hfminus_conv' hfminus_sum using sum_of_sum_of_AbsConvergent_nonneg hfminus_conv hfminus_nonneg
  split_ands
  . intro n
    have hplus_absConv : ((fun m ↦ fplus (n, m)):Series).absConverges := by
      have h_eq : abs ((fun m ↦ fplus (n, m)):Series) = (fun m ↦ fplus (n, m)):Series := by
        ext i; simp; by_cases hi : i ≥ 0 <;> simp [hi, hfplus_nonneg n i.toNat]
      rw [absConverges, h_eq]; exact hfplus_conv' n
    have hminus_absConv : ((fun m ↦ fminus (n, m)):Series).absConverges := by
      have h_eq : abs ((fun m ↦ fminus (n, m)):Series) = (fun m ↦ fminus (n, m)):Series := by
        ext i; simp; by_cases hi : i ≥ 0 <;> simp [hi, hfminus_nonneg n i.toNat]
      rw [absConverges, h_eq]; exact hfminus_conv' n
    have h_nonneg_abs : (abs ((fun m ↦ f (n, m)):Series)).nonneg := by
      intro n'; simp
    rw [absConverges, converges_of_nonneg_iff h_nonneg_abs]
    use (abs ((fun m ↦ fplus (n, m)):Series)).sum + (abs ((fun m ↦ fminus (n, m)):Series)).sum
    intro N; by_cases hN : N ≥ 0
    · lift N to ℕ using hN
      have h_ineq : ∀ (m : ℤ), |f (n, m.toNat)| ≤ |fplus (n, m.toNat)| + |fminus (n, m.toNat)| := by
        intro m; simp [hdiff, fplus, fminus]; by_cases h : f (n, m.toNat) ≥ 0 <;> simp [h]
      calc
        (abs ((fun m ↦ f (n, m)):Series)).partial N = ∑ n' ∈ Icc 0 (N : ℤ), |f (n, n'.toNat)| := by simp
        _ ≤ ∑ n' ∈ Icc 0 (N : ℤ), (|fplus (n, n'.toNat)| + |fminus (n, n'.toNat)|) :=
          Finset.sum_le_sum (λ n' hn' => h_ineq n')
        _ = (∑ n' ∈ Icc 0 (N : ℤ), |fplus (n, n'.toNat)|) + (∑ n' ∈ Icc 0 (N : ℤ), |fminus (n, n'.toNat)|) := by
          simp [Finset.sum_add_distrib]
        _ = (abs ((fun m ↦ fplus (n, m)):Series)).partial N + (abs ((fun m ↦ fminus (n, m)):Series)).partial N := by simp
        _ ≤ (abs ((fun m ↦ fplus (n, m)):Series)).sum + (abs ((fun m ↦ fminus (n, m)):Series)).sum := by
          have hp1 : (abs ((fun m ↦ fplus (n, m)):Series)).partial N ≤ (abs ((fun m ↦ fplus (n, m)):Series)).sum :=
            partial_le_sum_of_nonneg (by intro n'; simp) hplus_absConv (N : ℤ)
          have hp2 : (abs ((fun m ↦ fminus (n, m)):Series)).partial N ≤ (abs ((fun m ↦ fminus (n, m)):Series)).sum :=
            partial_le_sum_of_nonneg (by intro n'; simp) hminus_absConv (N : ℤ)
          nlinarith
    · simp [Series.partial, show N < 0 from by omega]
  convert convergesTo.sub hfplus_sum hfminus_sum using 1
  . -- encountered surprising difficulty with definitional equivalence here
    simp [hdiff]
    change (fun n ↦ ((fun m ↦ (fplus - fminus) (n, m)):Series).sum:Series) =
      (fun n ↦ ((fun m ↦ fplus (n, m)):Series).sum:Series)
      - (fun n ↦ ((fun m ↦ (fminus) (n, m)):Series).sum:Series)
    convert_to (fun n ↦ ((fun m ↦ (fplus - fminus) (n, m)):Series).sum:Series) =
      (((fun n ↦ ((fun m ↦ fplus (n, m)):Series).sum) - (fun n ↦ ((fun m ↦ (fminus) (n, m)):Series).sum):ℕ → ℝ):Series)
    . convert sub_coe _ _
    rcongr _ n; simp
    convert (sub _ _).2 with m; rfl
    split_ifs with h <;> simp [h, HSub.hSub, Sub.sub]
    . solve_by_elim
    convert hfminus_conv' n.toNat
  have ⟨ g, hg, _ ⟩ := hf
  have h1 := Sum.eq hg (hf.comp hg)
  have hplus := Sum.eq hg (hfplus_conv.comp hg)
  have hminus := Sum.eq hg (hfminus_conv.comp hg)
  apply convergesTo_uniq h1 _
  convert (convergesTo.sub hplus hminus) using 3 with n
  split_ifs with h <;> simp [h, hdiff, HSub.hSub, Sub.sub]

/-- Theorem 8.2.2, third version -/
theorem sum_of_sum_of_AbsConvergent' {f:ℕ × ℕ → ℝ} (hf:AbsConvergent f) :
  (∀ m, ((fun n ↦ f (n, m)):Series).absConverges) ∧
  (fun m ↦ ((fun n ↦ f (n, m)):Series).sum:Series).convergesTo (Sum f) := by
  set π: ℕ × ℕ → ℕ × ℕ := fun p ↦ (p.2, p.1)
  have hπ: Bijective π := Involutive.bijective (congrFun rfl)
  have ⟨ g, hg, hconv ⟩ := hf
  convert sum_of_sum_of_AbsConvergent (f := f ∘ π) _ using 2
  . exact (Sum.of_comp hf hπ).2
  refine ⟨ _, hπ.comp hg, ?_ ⟩
  convert hconv using 2

/-- Theorem 8.2.2, fourth version -/
theorem sum_comm {f:ℕ × ℕ → ℝ} (hf:AbsConvergent f) :
  (fun n ↦ ((fun m ↦ f (n, m)):Series).sum:Series).sum = (fun m ↦ ((fun n ↦ f (n, m)):Series).sum:Series).sum := by
  simp [sum_of_converges (sum_of_sum_of_AbsConvergent hf).2,
        sum_of_converges (sum_of_sum_of_AbsConvergent' hf).2]

/-- Lemma 8.2.3 / Exercise 8.2.1 -/
theorem AbsConvergent.iff {X:Type} (hX:CountablyInfinite X) (f : X → ℝ) :
  AbsConvergent f ↔ BddAbove ( (fun A ↦ ∑ x ∈ A, |f x|) '' .univ ) := by
  rw [←AbsConvergent'.of_countable hX, AbsConvergent']

abbrev AbsConvergent' {X:Type} (f: X → ℝ) : Prop := BddAbove ( (fun A ↦ ∑ x ∈ A, |f x|) '' .univ )

theorem AbsConvergent'.of_finite {X:Type} [Finite X] (f:X → ℝ) : AbsConvergent' f := by
  have _ := Fintype.ofFinite X
  simp [bddAbove_def]; use ∑ x, |f x|; intro A; apply Finset.sum_le_univ_sum_of_nonneg; simp

/-- Not in textbook, but should have been included. -/
theorem AbsConvergent'.of_countable {X:Type} (hX:CountablyInfinite X) {f:X → ℝ} :
  AbsConvergent' f ↔ AbsConvergent f := by
  constructor
  . intro hf; simp [bddAbove_def] at hf; choose L hL using hf
    have ⟨ g, hg ⟩ := hX.symm; refine ⟨ g, hg, ?_ ⟩
    unfold absConverges; rw [converges_of_nonneg_iff]
    . use L; intro N; by_cases hN: N ≥ 0
      . lift N to ℕ using hN
        set g':= Embedding.mk g hg.1
        convert hL (map g' (Icc 0 N))
        simp [Series.partial]; rfl
      convert hL ∅
      simp; apply partial_of_lt; grind
    simp [nonneg]
    intro n; by_cases h: n ≥ 0 <;> simp [h]
  intro hf; rwa [AbsConvergent.iff hX f] at hf

/-- Lemma 8.2.5 / Exercise 8.2.2-/
theorem AbsConvergent'.countable_supp {X:Type} {f:X → ℝ} (hf: AbsConvergent' f) :
  AtMostCountable { x | f x ≠ 0 } := by
  have h_summable_abs : Summable (|f|) := by
    rw [← summable_abs_iff, AbsConvergent'.iff_Summable]
    exact hf
  have h_finite (k : ℕ) : Set.Finite { x | |f x| > 1 / ((k : ℝ) + 1) } := by
    rcases (summable_iff_vanishing_norm (|f|)).mp h_summable_abs (1 / ((k : ℝ) + 1)) (by positivity) with ⟨ S, hS ⟩
    have h_subset : { x | |f x| > 1 / ((k : ℝ) + 1) } ⊆ (S : Set X) := by
      intro x hx
      by_contra! hxS
      have h_T : Disjoint ({x} : Finset X) S := by
        simp [Finset.disjoint_singleton_left, hxS]
      have h_sum := hS {x} h_T
      simp at h_sum
      nlinarith
    exact Set.Finite.subset (Finset.finite_toSet S) h_subset
  have h_countable : Set.Countable { x | f x ≠ 0 } := by
    have h_union : { x | f x ≠ 0 } ⊆ ⋃ (k : ℕ), { x | |f x| > 1 / ((k : ℝ) + 1) } := by
      intro x hx
      have hx' : |f x| > 0 := abs_pos.mpr hx
      have : ∃ k : ℕ, 1 / ((k : ℝ) + 1) < |f x| := by
        have hlim : Filter.Tendsto (λ n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (𝓝 0) := by
          simpa [one_div] using (tendsto_one_div_add_atTop_nhds_0_nat.comp
            (tendsto_add_atTop_nat 1))
        have hball : Metric.ball (0 : ℝ) (|f x| / 2) ∈ 𝓝 (0 : ℝ) :=
          Metric.ball_mem_nhds 0 (by nlinarith)
        rcases hlim (Metric.ball (0 : ℝ) (|f x| / 2)) hball with ⟨ N, hN ⟩
        use N
        have hNx : 1 / ((N : ℝ) + 1) < |f x| / 2 := by
          simpa using hN N (le_refl N)
        nlinarith
      rcases this with ⟨ k, hk ⟩
      exact Set.mem_iUnion.mpr ⟨ k, hk ⟩
    refine Set.Countable.mono h_union (Set.countable_iUnion (λ n => ?_))
    exact (h_finite n).countable
  rw [AtMostCountable.iff]; exact h_countable

/-- Compare with Mathlib's {name}`Summable.subtype`-/
theorem AbsConvergent'.subtype {X:Type} {f:X → ℝ} (hf: AbsConvergent' f) (A: Set X) :
  AbsConvergent' (fun x:A ↦ f x) := by
  apply BddAbove.mono _ hf
  intro z hz; simp at *; choose A hA using hz
  use A.map (Embedding.subtype _); simp [hA]

/-- A generalized sum.  Note that this will give junk values if {name}`f` is not {name}`AbsConvergent'`. -/
noncomputable abbrev Sum' {X:Type} (f: X → ℝ) : ℝ := Sum (fun x : { x | f x ≠ 0 } ↦ f x)

/-- Not in textbook, but should have been included (the series laws are significantly harder
to establish without this) -/
theorem Sum'.of_finsupp {X:Type} {f:X → ℝ} {A: Finset X} (h: ∀ x ∉ A, f x = 0) : Sum' f = ∑ x ∈ A, f x := by
  unfold Sum'
  set E := { x | f x ≠ 0 }
  have hE : E ⊆ A := by intro _; simp [E]; grind
  have hfin : Finite E := Finite.Set.subset _ hE
  set E' := E.toFinite.toFinset
  rw [Sum.of_finite (fun x:E ↦ f x), ←E'.sum_subtype (by simp [E'])]
  replace hE : E' ⊆ A := by aesop
  apply sum_subset hE; aesop

/-- Not in textbook, but should have been included (the series laws are significantly harder
to establish without this) -/
theorem Sum'.of_countable_supp {X:Type} {f:X → ℝ} {A: Set X} (hA: CountablyInfinite A)
  (hfA : ∀ x ∉ A, f x = 0) (hconv: AbsConvergent' f):
  AbsConvergent' (fun x:A ↦ f x) ∧ Sum' f = Sum (fun x:A ↦ f x) := by
  -- We can adapt the proof of `AbsConvergent'.of_countable` to establish absolute convergence on A.
  have hconv' : AbsConvergent (fun x:A ↦ f x) :=
    (AbsConvergent'.of_countable hA).mp (hconv.subtype A)
  rw [AbsConvergent'.of_countable hA]
  refine ⟨ hconv', ?_ ⟩
  set E := { x | f x ≠ 0 }
  -- The main challenge here is to relate a sum on E with a sum on A.  First, we show containment.
  have hE : E ⊆ A := by intro _; simp [E]; by_contra!; aesop
  -- Now, we map A back to the natural numbers, thus identifying E with a subset E' of ℕ.
  choose g hg using hA.symm
  have hsum := Sum.eq hg (hconv'.comp hg)
  set E' := { n | ↑(g n) ∈ E }
  set ι : E' → E := fun ⟨ n, hn ⟩ ↦ ⟨ g n, by aesop ⟩
  have hι: Bijective ι := by
    split_ands
    . intro ⟨ _, _ ⟩ ⟨ _, _ ⟩ h; simp [ι, E', Subtype.val_inj] at *; exact hg.1 h
    . intro ⟨ x, hx ⟩; choose n hn using hg.2 ⟨ _, hE hx ⟩; use ⟨ n, by aesop ⟩; grind
  -- The cases of infinite and finite E' are handled separately.
  obtain hE' | hE' := Nat.atMostCountable_subset E'
  . --   use Nat.monotone_enum_of_infinite to enumerate E'
    --   show the partial sums of E' are a subsequence of the partial sums of A
    set hinf : Infinite E' := hE'.toInfinite
    choose a ha_bij ha_mono using (Nat.monotone_enum_of_infinite E').exists
    have : atTop.Tendsto (Nat.cast ∘ Subtype.val ∘ a: ℕ → ℤ) atTop := by
      apply tendsto_natCast_atTop_atTop.comp (StrictMono.tendsto_atTop _)
      intro _ _ hnm; simp [ha_mono hnm]
    apply tendsto_nhds_unique  _ (hsum.comp this)
    have hconv'' : AbsConvergent (fun x:E ↦ f x) := by
      rw [←AbsConvergent'.of_countable]
      . exact hconv.subtype E
      apply (CountablyInfinite.equiv _).mp hE'; use ι
    replace := Sum.eq (hι.comp ha_bij) (hconv''.comp (hι.comp ha_bij))
    convert this.comp tendsto_natCast_atTop_atTop using 1; ext N
    simp [Series.partial, ι]
    calc
      _ = ∑ x ∈ .image (Subtype.val ∘ a) (.Icc 0 N), f ↑(g x) := by
        symm; apply sum_subset
        . intro m hm; simp at hm ⊢; obtain ⟨ n, hn, rfl ⟩ := hm
          simp [ha_mono.monotone hn]
        intro x hx hx'; simp at hx hx'; contrapose! hx'
        choose n hn using (hι.comp ha_bij).2 ⟨ g x, hx' ⟩
        simp [ι, Subtype.val_inj] at hn
        apply hg.1 at hn; subst hn
        use n; simpa [ha_mono.le_iff_le] using hx
      _ = _ := by
        apply sum_image
        intro _ _ _ _ h; simp [Subtype.val_inj] at h; exact ha_bij.1 h
  -- When E' is finite, we show that all sufficiently large partial sums of A are equal to
  -- the sum of E'.
  let hEfin : Finite E := hι.finite_iff.mp hE'
  let hE'fintype : Fintype E' := .ofFinite _
  let hEfintype : Fintype E := .ofFinite _
  apply convergesTo_uniq _ hsum
  simp [Sum.of_finite, Series.convergesTo]
  apply tendsto_nhds_of_eventually_eq
  have hE'bound : BddAbove E' := Set.Finite.bddAbove hE'
  rw [bddAbove_def] at hE'bound; choose N hN using hE'bound
  rw [eventually_atTop]
  use N; intro N' hN'
  lift N' to ℕ using (LE.le.trans (by positivity) hN')
  simp [Series.partial] at hN' ⊢
  calc
    _ = ∑ n ∈ E', f (g n) := by
      symm; apply sum_subset
      . intro x hx; simp at *; linarith [hN _ hx]
      intro _ _ hx'; simpa [E',E] using hx'
    _ = ∑ n:E', f (g n) := by convert (sum_set_coe _).symm
    _ = ∑ n, f (ι n) := sum_congr rfl (by grind)
    _ = _ := hι.sum_comp (g := fun x ↦ f x)

/-- Connection with Mathlib's {name}`Summable` property. Some version of this might be suitable
    for Mathlib? -/
theorem AbsConvergent'.iff_Summable {X:Type} (f:X → ℝ) : AbsConvergent' f ↔ Summable f := by
  simp [←summable_abs_iff, AbsConvergent']
  simp [summable_iff_vanishing_norm]
  classical
  constructor
  . intro h ε hε
    set s := Set.range fun A ↦ ∑ x ∈ A, |f x|
    have hnon : s.Nonempty := by simp [s]; use 0, ∅; simp
    have : (sSup s)-ε < sSup s := by linarith
    simp [lt_csSup_iff h hnon,s] at this; choose S hS using this
    use S; intro T hT
    rw [abs_of_nonneg (by positivity)]
    have : ∑ x ∈ T, |f x| + ∑ x ∈ S, |f x| ≤ sSup s := by
      apply le_csSup h
      simp [s]; exact ⟨ T ∪ S, sum_union hT ⟩
    linarith
  intro h; choose S hS using h 1 (by norm_num)
  rw [bddAbove_def]
  use ∑ x ∈ S, |f x| + 1; simp; intro T
  calc
    _ = ∑ x ∈ (T ∩ S), |f x| + ∑ x ∈ (T \ S), |f x| := (sum_inter_add_sum_diff _ _ _).symm
    _ ≤ _ := by
      gcongr
      . exact inter_subset_right
      apply le_of_lt (lt_of_abs_lt (hS _ disjoint_sdiff_self_left))

/-- Maybe suitable for porting to Mathlib?-/
theorem Filter.Eventually.int_natCast_atTop (p: ℤ → Prop) :
  (∀ᶠ n in .atTop, p n) ↔ ∀ᶠ n:ℕ in .atTop, p ↑n := by
  refine ⟨ Eventually.natCast_atTop, ?_ ⟩
  simp [eventually_atTop]
  intro N hN; use N; intro n hn
  lift n to ℕ using (by omega)
  simp at hn; solve_by_elim

theorem Filter.Tendsto.int_natCast_atTop {R:Type} (f: ℤ → R) (l: Filter R) :
atTop.Tendsto f l ↔ atTop.Tendsto (f ∘ Nat.cast) l := by
  simp [tendsto_iff_eventually]
  peel with p h
  simp [←eventually_atTop]
  convert Eventually.int_natCast_atTop _


/-- Connection with Mathlib's {name}`tsum` (or {kw (of := «termΣ'_,_»)}`Σ'`) operation -/
theorem Sum'.eq_tsum {X:Type} (f:X → ℝ) (h: AbsConvergent' f) :
  Sum' f = ∑' x, f x := by
  set E := {x | f x ≠ 0}
  obtain hE | hE := h.countable_supp
  . simp [Sum']
    choose g hg using hE.symm
    have : ((f ∘ Subtype.val) ∘ g:Series).absConverges := by
      apply AbsConvergent.comp hg
      rw [←AbsConvergent'.of_countable hE]
      exact h.subtype E
    replace this := Sum.eq hg this
    convert convergesTo_uniq this _ using 1
    · replace : ∑' x, f x = ∑' n, f (g n) := calc
        _ = ∑' x:E, f x := by
          exact (tsum_subtype_eq_of_support_subset (fun x hx => hx)).symm
        _ = _ := (Equiv.tsum_eq (Equiv.ofBijective _ hg) _).symm
      rw [this]
      unfold convergesTo; rw [Filter.Tendsto.int_natCast_atTop]
      convert (Summable.tendsto_sum_tsum_nat ?_).comp (tendsto_add_atTop_nat 1) with n
      . ext N; simp [Series.partial, Nat.range_succ_eq_Icc_zero]
      rw [AbsConvergent'.iff_Summable] at h
      exact h.comp_injective (i := Subtype.val ∘ g) (Subtype.val_injective.comp hg.1)
  rw [of_finsupp (A := E.toFinite.toFinset)]; symm; apply tsum_eq_sum
  all_goals simp [E]


/-- Proposition 8.2.6 (a) (Absolutely convergent series laws) / Exercise 8.2.3 -/
theorem Sum'.add {X:Type} {f g:X → ℝ} (hf: AbsConvergent' f) (hg: AbsConvergent' g) :
  AbsConvergent' (f+g) ∧ Sum' (f + g) = Sum' f + Sum' g := by
  have h_sum_f : Summable f := (AbsConvergent'.iff_Summable f).mp hf
  have h_sum_g : Summable g := (AbsConvergent'.iff_Summable g).mp hg
  have h_sum_fg : Summable (f + g) := h_sum_f.add h_sum_g
  have h_abs_conv : AbsConvergent' (f + g) := (AbsConvergent'.iff_Summable (f + g)).mpr h_sum_fg
  have h_sum' : Sum' (f + g) = Sum' f + Sum' g := by
    calc
      Sum' (f + g) = ∑' x, (f + g) x := Sum'.eq_tsum (f + g) h_abs_conv
      _ = (∑' x, f x) + (∑' x, g x) := by rw [tsum_add h_sum_f h_sum_g]
      _ = Sum' f + Sum' g := by rw [Sum'.eq_tsum f hf, Sum'.eq_tsum g hg]
  exact ⟨ h_abs_conv, h_sum' ⟩

/-- Proposition 8.2.6 (b) (Absolutely convergent series laws) / Exercise 8.2.3 -/
theorem Sum'.smul {X:Type} {f:X → ℝ} (hf: AbsConvergent' f) (c: ℝ) :
  AbsConvergent' (c • f) ∧ Sum' (c • f) = c * Sum' f := by
  have h_sum_f : Summable f := (AbsConvergent'.iff_Summable f).mp hf
  have h_sum_cf : Summable (c • f) := h_sum_f.const_smul c
  have h_abs_conv : AbsConvergent' (c • f) := (AbsConvergent'.iff_Summable (c • f)).mpr h_sum_cf
  have h_sum' : Sum' (c • f) = c * Sum' f := by
    calc
      Sum' (c • f) = ∑' x, (c • f) x := Sum'.eq_tsum (c • f) h_abs_conv
      _ = ∑' x, c * f x := rfl
      _ = c * ∑' x, f x := by rw [tsum_mul_left]
      _ = c * Sum' f := by rw [Sum'.eq_tsum f hf]
  exact ⟨ h_abs_conv, h_sum' ⟩

/-- This law is not explicitly stated in Proposition 8.2.6, but follows easily from parts (a) and (b).-/
theorem Sum'.sub {X:Type} {f g:X → ℝ} (hf: AbsConvergent' f) (hg: AbsConvergent' g) :
  AbsConvergent' (f-g) ∧ Sum' (f - g) = Sum' f - Sum' g := by
  convert add hf (smul hg (-1)).1 using 2
  . simp; abel
  . congr; simp; abel
  rw [(smul hg (-1)).2]; ring

/-- Proposition 8.2.6 (c) (Absolutely convergent series laws) / Exercise 8.2.3.  The first
    part of this proposition has been moved to {lean}`AbsConvergent'.subtype`. -/
theorem Sum'.of_disjoint_union {X:Type} {f:X → ℝ} (hf: AbsConvergent' f) {X₁ X₂ : Set X} (hdisj: Disjoint X₁ X₂):
  Sum' (fun x: (X₁ ∪ X₂: Set X) ↦ f x) = Sum' (fun x : X₁ ↦ f x) + Sum' (fun x : X₂ ↦ f x) := by
  have hsum_f : Summable f := (AbsConvergent'.iff_Summable f).mp hf
  have hsum_union : Summable (λ x : (X₁ ∪ X₂ : Set X) => f x) := hsum_f.comp_injective Subtype.val_injective
  have hsum_X1 : Summable (λ x : X₁ => f x) := hsum_f.comp_injective Subtype.val_injective
  have hsum_X2 : Summable (λ x : X₂ => f x) := hsum_f.comp_injective Subtype.val_injective
  have h_abs_conv_union : AbsConvergent' (fun x : (X₁ ∪ X₂ : Set X) ↦ f x) :=
    (AbsConvergent'.iff_Summable _).mpr hsum_union
  calc
    Sum' (fun x : (X₁ ∪ X₂ : Set X) ↦ f x) = ∑' x : (X₁ ∪ X₂ : Set X), f x :=
      Sum'.eq_tsum _ h_abs_conv_union
    _ = (∑' x : X₁, f x) + (∑' x : X₂, f x) := by
      rw [tsum_union_disjoint hdisj hsum_X1 hsum_X2]
    _ = Sum' (fun x : X₁ ↦ f x) + Sum' (fun x : X₂ ↦ f x) := by
      rw [Sum'.eq_tsum (λ x : X₁ => f x) ?_, Sum'.eq_tsum (λ x : X₂ => f x) ?_]
      · exact (AbsConvergent'.iff_Summable _).mpr hsum_X1
      · exact (AbsConvergent'.iff_Summable _).mpr hsum_X2

/-- This technical claim, the analogue of {name}`tsum_univ`, is required due to the way Mathlib handles
    sets.-/
theorem Sum'.of_univ {X:Type} {f:X → ℝ} (hf: AbsConvergent' f) :
  Sum' (fun x: (.univ : Set X) ↦ f x) = Sum' f := by
  have hsum_f : Summable f := (AbsConvergent'.iff_Summable f).mp hf
  have hsum_univ : Summable (λ x : (.univ : Set X) => f x) := hsum_f.comp_injective Subtype.val_injective
  have h_abs_conv_univ : AbsConvergent' (fun x : (.univ : Set X) ↦ f x) :=
    (AbsConvergent'.iff_Summable _).mpr hsum_univ
  calc
    Sum' (fun x : (.univ : Set X) ↦ f x) = ∑' x : (.univ : Set X), f x :=
      Sum'.eq_tsum _ h_abs_conv_univ
    _ = ∑' x : X, f x := by rw [tsum_univ]
    _ = Sum' f := by rw [Sum'.eq_tsum f hf]

theorem Sum'.of_comp {X Y:Type} {f:X → ℝ} (hf: AbsConvergent' f) {φ: Y → X}
  (hφ: Function.Bijective φ) :
  AbsConvergent' (f ∘ φ) ∧ Sum' f = Sum' (f ∘ φ) := by
  have hsum_f : Summable f := (AbsConvergent'.iff_Summable f).mp hf
  have hsum_f_comp : Summable (f ∘ φ) := hsum_f.comp_injective hφ.injective
  have h_abs_conv_comp : AbsConvergent' (f ∘ φ) :=
    (AbsConvergent'.iff_Summable _).mpr hsum_f_comp
  have h_sum' : Sum' f = Sum' (f ∘ φ) := by
    calc
      Sum' f = ∑' x, f x := Sum'.eq_tsum f hf
      _ = ∑' y, f (φ y) := (Equiv.ofBijective φ hφ).tsum_eq.symm
      _ = Sum' (f ∘ φ) := (Sum'.eq_tsum (f ∘ φ) h_abs_conv_comp).symm
  exact ⟨ h_abs_conv_comp, h_sum' ⟩

lemma AbsConvergent.summable_abs' {f : ℕ → ℝ} (h : AbsConvergent f) : Summable (|f|) := by
  rcases h with ⟨ g, hg, hconv ⟩
  have h_nonneg : (|f ∘ g| : Series).nonneg := by
    intro n; simp
  choose g_inv hleft hright using bijective_iff_has_inverse.mp hg
  have h_bound (N : ℕ) : (|f| : Series).partial (N : ℤ) ≤ (|f ∘ g| : Series).sum := by
    let M := (Finset.range (N+1)).sup (λ n => g_inv n)
    have h_subset : (Finset.range (N+1)).image (λ n : ℕ => g_inv n) ⊆ Finset.range (M+1) := by
      intro k hk; simp at hk ⊢
      obtain ⟨ n, hn, rfl ⟩ := hk
      have : g_inv n ≤ M := Finset.le_sup (f := λ n : ℕ => g_inv n) hn
      omega
    calc
      (|f| : Series).partial (N : ℤ) = ∑ n ∈ Icc 0 (N : ℤ), |f n.toNat| := rfl
      _ = ∑ n ∈ Finset.range (N+1), |f n| := by
        simp [Finset.Icc_eq_cast, Finset.map_cast]
      _ = ∑ n ∈ Finset.range (N+1), |f (g (g_inv n))| := by simp [hright]
      _ = ∑ k ∈ (Finset.range (N+1)).image (λ n : ℕ => g_inv n), |f (g k)| := by
        symm; apply Finset.sum_image; intro x hx y hy h; exact hg.1 h
      _ ≤ ∑ k ∈ Finset.range (M+1), |f (g k)| := Finset.sum_le_sum_of_subset h_subset
      _ = (|f ∘ g| : Series).partial (M+1 : ℤ) := by simp
      _ ≤ (|f ∘ g| : Series).sum := partial_le_sum_of_nonneg h_nonneg hconv (M+1 : ℤ)
  have h_conv : (|f| : Series).converges := by
    rw [converges_of_nonneg_iff (by intro n; simp)]
    use (|f ∘ g| : Series).sum
    intro N; by_cases hN : N ≥ 0
    · lift N to ℕ using hN; apply h_bound N
    · simp [Series.partial, show N < 0 from by omega]
  rw [← summable_abs_iff, ← absConverges]; exact h_conv

/-- Lemma 8.2.7 / Exercise 8.2.4 -/
theorem divergent_parts_of_divergent {a: ℕ → ℝ} (ha: (a:Series).converges)
  (ha': ¬ (a:Series).absConverges) :
  ¬ AbsConvergent (fun n : {n | a n ≥ 0} ↦ a n) ∧ ¬ AbsConvergent (fun n : {n | a n < 0} ↦ a n)
  := by
  have ha_not_summable : ¬ Summable (|a|) := by
    intro h; apply ha'; rw [absConverges, ← summable_abs_iff]; exact h
  have h_not_abs (A : Set ℕ) (hA : A = {n | a n ≥ 0} ∨ A = {n | a n < 0}) :
    ¬ AbsConvergent (fun x : A ↦ a x) := by
    intro h
    apply ha_not_summable
    have : Summable (|fun x : A ↦ a x|) := h.summable_abs'
    have h_ext : Summable (|a|) := by
      let g : A → ℕ := Subtype.val
      have h_inj : Function.Injective g := Subtype.val_injective
      exact this.comp_injective h_inj
    exact h_ext
  have h_pos : ¬ AbsConvergent (fun n : {n | a n ≥ 0} ↦ a n) :=
    h_not_abs {n | a n ≥ 0} (Or.inl rfl)
  have h_neg : ¬ AbsConvergent (fun n : {n | a n < 0} ↦ a n) :=
    h_not_abs {n | a n < 0} (Or.inr rfl)
  exact ⟨ h_pos, h_neg ⟩

/-- Theorem 8.2.8 (Riemann rearrangement theorem) / Exercise 8.2.5 -/
theorem permute_convergesTo_of_divergent {a: ℕ → ℝ} (ha: (a:Series).converges)
  (ha': ¬ (a:Series).absConverges) (L:ℝ) :
  ∃ f : ℕ → ℕ, Bijective f ∧ (a ∘ f:Series).convergesTo L
  := by
  -- This proof is written to follow the structure of the original text.
  choose h1 h2 using divergent_parts_of_divergent ha ha'
  set A_plus := { n | a n ≥ 0 }
  set A_minus := {n | a n < 0 }
  have hdisj : Disjoint A_plus A_minus := by
    rw [Set.disjoint_iff_inter_eq_empty]; ext; simp [A_plus, A_minus]
  have hunion : A_plus ∪ A_minus = .univ := by
    ext; simp [A_plus, A_minus]; grind
  have hA_plus_inf : Infinite A_plus := by
    by_contra! h
    have h_fin : Finite A_plus := h
    have h_finset : Finset ℕ := h_fin.toFinset
    let N := h_finset.sup id
    have h_N : ∀ n > N, a n < 0 := by
      intro n hn
      have h_not_mem : n ∉ h_finset := by
        intro hn'; have : n ≤ N := Finset.le_sup (f := id) hn'; omega
      have h_not_plus : n ∉ A_plus := by
        intro hnA; apply h_not_mem; exact h_fin.mem_toFinset.mpr hnA
      simp [A_plus] at h_not_plus; exact lt_of_le_of_ne (le_of_not_gt h_not_plus) (by omega)
    have h_abs_conv : (a : Series).absConverges := by
      rw [absConverges, converges_iff_tail_decay]
      intro ε hε
      rcases (converges_iff_tail_decay a).mp ha ε hε with ⟨ N', hN', hN ⟩
      refine ⟨ max N N', by omega, λ p hp q hq => ?_ ⟩
      have hp' : p ≥ N' := by omega; have hq' : q ≥ N' := by omega
      have h := hN p hp' q hq'
      have h_nonneg : ∀ n ∈ Icc p q, (|a| : Series).seq n = |a n.toNat| := by
        intro n hn; simp
      have h_pos : ∀ n ∈ Icc p q, a n < 0 := by
        intro n hn; apply h_N n.toNat; omega
      simp [h_nonneg, h_pos, abs_of_neg, Series.seq]
      simpa using h
    exact ha' h_abs_conv
  have hA_minus_inf : Infinite A_minus := by
    by_contra! h
    have h_fin : Finite A_minus := h
    have h_finset : Finset ℕ := h_fin.toFinset
    let N := h_finset.sup id
    have h_N : ∀ n > N, a n ≥ 0 := by
      intro n hn
      have h_not_mem : n ∉ h_finset := by
        intro hn'; have : n ≤ N := Finset.le_sup (f := id) hn'; omega
      have h_not_minus : n ∉ A_minus := by
        intro hnA; apply h_not_mem; exact h_fin.mem_toFinset.mpr hnA
      simp [A_minus] at h_not_minus; exact not_lt.mp h_not_minus
    have h_abs_conv : (a : Series).absConverges := by
      rw [absConverges, converges_iff_tail_decay]
      intro ε hε
      rcases (converges_iff_tail_decay a).mp ha ε hε with ⟨ N', hN', hN ⟩
      refine ⟨ max N N', by omega, λ p hp q hq => ?_ ⟩
      have hp' : p ≥ N' := by omega; have hq' : q ≥ N' := by omega
      have h := hN p hp' q hq'
      have h_nonneg : ∀ n ∈ Icc p q, (|a| : Series).seq n = |a n.toNat| := by
        intro n hn; simp
      have h_pos : ∀ n ∈ Icc p q, 0 ≤ a n := by
        intro n hn; apply h_N n.toNat; omega
      simp [h_nonneg, h_pos, abs_of_nonneg, Series.seq]
      simpa using h
    exact ha' h_abs_conv
  obtain ⟨ a_plus, ha_plus_bij, ha_plus_mono ⟩ := (Nat.monotone_enum_of_infinite A_plus).exists
  obtain ⟨ a_minus, ha_minus_bij, ha_minus_mono ⟩ := (Nat.monotone_enum_of_infinite A_minus).exists
  let F : (n : ℕ) → ((m : ℕ) → m < n → ℕ) → ℕ :=
    fun j n' ↦ if ∑ i:Fin j, a (n' i (by simp)) < L then
      Nat.min { n ∈ A_plus | ∀ i:Fin j, n ≠ n' i (by simp) }
    else
      Nat.min { n ∈ A_minus | ∀ i:Fin j, n ≠ n' i (by simp) }
  let n' : ℕ → ℕ := Nat.strongRec F
  have hn' (j:ℕ) : n' j = if ∑ i:Fin j, a (n' i) < L then
      Nat.min { n ∈ A_plus | ∀ i:Fin j, n ≠ n' i }
    else
      Nat.min { n ∈ A_minus | ∀ i:Fin j, n ≠ n' i }
    := Nat.strongRec.eq_def _ j
  have hn'_plus_inf (j:ℕ) : Infinite { n ∈ A_plus | ∀ i:Fin j, n ≠ n' i } := by
    have h_finite_chosen : Set.Finite { n' i | i : Fin j } :=
      Set.toFinite _
    have h_rest : Set.Infinite (A_plus \ { n' i | i : Fin j }) :=
      Set.Infinite.diff hA_plus_inf h_finite_chosen
    have h_eq : { n ∈ A_plus | ∀ i:Fin j, n ≠ n' i } = (A_plus \ { n' i | i : Fin j }) := by
      ext n; simp
    rw [h_eq]; exact Set.infinite_coe_iff.mpr h_rest
  have hn'_minus_inf (j:ℕ) : Infinite { n ∈ A_minus | ∀ i:Fin j, n ≠ n' i } := by
    have h_finite_chosen : Set.Finite { n' i | i : Fin j } :=
      Set.toFinite _
    have h_rest : Set.Infinite (A_minus \ { n' i | i : Fin j }) :=
      Set.Infinite.diff hA_minus_inf h_finite_chosen
    have h_eq : { n ∈ A_minus | ∀ i:Fin j, n ≠ n' i } = (A_minus \ { n' i | i : Fin j }) := by
      ext n; simp
    rw [h_eq]; exact Set.infinite_coe_iff.mpr h_rest
  have hn'_inj : Injective n' := by
    intro x y h
    wlog hxy : x ≤ y
    · apply (this h.symm (le_of_not_le hxy)).symm
    by_cases hx_lt_y : x < y
    · have hx' := hn' y
      have : n' x = n' y := h
      have hmem : n' y ∈ { n ∈ A_plus | ∀ i:Fin y, n ≠ n' i } ∪ { n ∈ A_minus | ∀ i:Fin y, n ≠ n' i } := by
        rw [hx']
        split <;> apply Nat.min_mem_of_nonempty
        · exact (hn'_plus_inf y).nonempty
        · exact (hn'_minus_inf y).nonempty
      rcases hmem with ( ⟨ hy_plus, h_ne ⟩ | ⟨ hy_minus, h_ne ⟩ )
      · apply h_ne (Fin.ofNat x (by omega)); rw [h]
      · apply h_ne (Fin.ofNat x (by omega)); rw [h]
    · omega
  have h_case_I : Infinite { j | ∑ i:Fin j, a (n' i) < L } := by
    by_contra! h
    have h_fin_set : Set.Finite { j | ∑ i:Fin j, a (n' i) < L } := h
    have h_inf_set : Set.Infinite { j | ∑ i:Fin j, a (n' i) ≥ L } := by
      by_contra! hfin2
      have : Set.Finite (Set.univ : Set ℕ) := Set.Finite.union h_fin_set hfin2
      exact Set.infinite_univ this
    have h_all_ge : ∀ j, ∑ i:Fin j, a (n' i) ≥ L := by
      intro j; by_contra! hlt; exact h_fin_set (Set.mem_setOf.mpr hlt)
    have h_eventually_neg : ∀ᶠ j in atTop, n' j ∈ A_minus := by
      apply Filter.eventually_atTop.mpr
      refine ⟨ 0, λ j hj => ?_ ⟩
      rw [hn' j]; simp [h_all_ge j]
    have h_abs_conv : (a : Series).absConverges := by
      rw [absConverges, converges_iff_tail_decay]
      intro ε hε
      rcases (converges_iff_tail_decay a).mp ha ε hε with ⟨ N, hN, hN' ⟩
      rcases Filter.eventually_atTop.mp h_eventually_neg with ⟨ J, hJ ⟩
      refine ⟨ max N J, by omega, λ p hp q hq => ?_ ⟩
      have hp' : p ≥ N := by omega; have hq' : q ≥ N := by omega
      have h_nonneg : ∀ n ∈ Icc p q, (|a| : Series).seq n = |a n.toNat| := λ n hn => by simp
      have h_neg : ∀ n ∈ Icc p q, a n < 0 := by
        intro n hn; apply hJ n.toNat; omega
      simp [h_nonneg, h_neg, abs_of_neg, Series.seq]
      simpa using hN' p hp' q hq'
    exact ha' h_abs_conv
  have h_case_II : Infinite { j | ∑ i:Fin j, a (n' i) ≥ L } := by
    by_contra! h
    have h_fin : Set.Finite { j | ∑ i:Fin j, a (n' i) ≥ L } := h
    have h_inf : Set.Infinite { j | ∑ i:Fin j, a (n' i) < L } := by
      by_contra! hfin2
      have : Set.Finite (Set.univ : Set ℕ) := Set.Finite.union hfin2 h_fin
      exact Set.infinite_univ this
    have : ∀ j, ∑ i:Fin j, a (n' i) < L := by
      intro j; by_contra! hge; exact h_fin (Set.mem_setOf.mpr hge)
    have h_eventually_pos : ∀ᶠ j in atTop, n' j ∈ A_plus := by
      apply Filter.eventually_atTop.mpr
      refine ⟨ 0, λ j hj => ?_ ⟩
      rw [hn' j]; simp [this j]
    have h_abs_conv : (a : Series).absConverges := by
      rw [absConverges, converges_iff_tail_decay]
      intro ε hε
      rcases (converges_iff_tail_decay a).mp ha ε hε with ⟨ N, hN, hN' ⟩
      rcases Filter.eventually_atTop.mp h_eventually_pos with ⟨ J, hJ ⟩
      refine ⟨ max N J, by omega, λ p hp q hq => ?_ ⟩
      have hp' : p ≥ N := by omega; have hq' : q ≥ N := by omega
      have h_nonneg : ∀ n ∈ Icc p q, (|a| : Series).seq n = |a n.toNat| := λ n hn => by simp
      have h_pos : ∀ n ∈ Icc p q, 0 ≤ a n := by
        intro n hn; apply hJ n.toNat; omega
      simp [h_nonneg, h_pos, abs_of_nonneg, Series.seq]
      simpa using hN' p hp' q hq'
    exact ha' h_abs_conv
  have hn'_surj : Surjective n' := by
    intro x
    have hx_univ : x ∈ A_plus ∪ A_minus := by rw [hunion]; trivial
    rcases hx_univ with (hx_plus | hx_minus)
    · by_cases h_used : ∃ j, n' j = x
      · rcases h_used with ⟨ j, hj ⟩; exact ⟨ j, hj ⟩
      · exfalso
        have h_nonempty : { n ∈ A_plus | ∀ i : Fin (x+1), n ≠ n' i }.Nonempty :=
          (hn'_plus_inf (x+1)).nonempty
        have h_candidate_spec := Nat.min_spec h_nonempty
        have hx_mem : x ∈ { n ∈ A_plus | ∀ i : Fin (x+1), n ≠ n' i } := by
          refine ⟨ hx_plus, λ i hi hx_eq => h_used ⟨ i, hx_eq.symm ⟩ ⟩
        have h_min_le_x : Nat.min { n ∈ A_plus | ∀ i : Fin (x+1), n ≠ n' i } ≤ x :=
          Nat.min_le _ hx_mem
        have h_min_mem : Nat.min { n ∈ A_plus | ∀ i : Fin (x+1), n ≠ n' i } ∈
          A_plus ∧ ∀ i : Fin (x+1), Nat.min { n ∈ A_plus | ∀ i : Fin (x+1), n ≠ n' i } ≠ n' i :=
          h_candidate_spec
        exfalso
        apply h_used
        have h_candidate_spec' := h_candidate_spec
        rcases h_candidate_spec with ⟨ h_mem, h_ne ⟩
        -- The minimum M is chosen at some step k, proving x is in the image
        have h_exists_k : ∃ k, n' k = Nat.min { n ∈ A_plus | ∀ i : Fin (x+1), n ≠ n' i } := by
          have : { n ∈ A_plus | ∀ i : Fin (x+1), n ≠ n' i } ⊆ Set.range n' := by
            intro n hn; rcases hn with ⟨ hnA, hn_ne ⟩
            have hn_nonempty : { m ∈ A_plus | ∀ i : Fin n, m ≠ n' i }.Nonempty :=
              (hn'_plus_inf n).nonempty
            sorry
          sorry
        rcases h_exists_k with ⟨ k, hk ⟩
        use k
        have hx_ge_min : x ≥ Nat.min { n ∈ A_plus | ∀ i : Fin (x+1), n ≠ n' i } :=
          h_min_le_x
        have h_min_le_x' : Nat.min { n ∈ A_plus | ∀ i : Fin (x+1), n ≠ n' i } ≤ x :=
          h_min_le_x
        sorry
    · sorry
  have hconv : atTop.Tendsto (a ∘ n') (nhds 0) := by
    have h_tendsto_zero : atTop.Tendsto a (nhds 0) := tendsToZero_of_converges ha
    have h_n'_tendsto : atTop.Tendsto n' atTop := by
      apply StrictMono.tendsto_atTop
      intro i j h
      by_contra! hge
      apply hn'_inj (by omega); omega
    exact h_tendsto_zero.comp h_n'_tendsto
  have hsum : (a ∘ n':Series).convergesTo L := by
    have h_convTo_sum : (a : Series).convergesTo ((a : Series).sum) := convergesTo_sum ha
    sorry
  use n'
  refine ⟨ ⟨ hn'_inj, hn'_surj ⟩, ?_ ⟩; convert hsum

/-- Exercise 8.2.6 -/
theorem permute_diverges_of_divergent {a: ℕ → ℝ} (ha: (a:Series).converges)
  (ha': ¬ (a:Series).absConverges)  :
  ∃ f : ℕ → ℕ,  Bijective f ∧ atTop.Tendsto (fun N ↦ ((a ∘ f:Series).partial N : EReal)) (nhds ⊤) := by
  sorry

theorem permute_diverges_of_divergent' {a: ℕ → ℝ} (ha: (a:Series).converges)
  (ha': ¬ (a:Series).absConverges)  :
  ∃ f : ℕ → ℕ,  Bijective f ∧ atTop.Tendsto (fun N ↦ ((a ∘ f:Series).partial N : EReal)) (nhds ⊥) := by
  sorry

end Chapter8
