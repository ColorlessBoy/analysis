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
    by_cases hX_empty : X = ∅
    · simp [hX_empty, hLpos]
    · rcases hf with ⟨g, hg_bij, hg_conv⟩
      have hconvL : (f ∘ g : Series).convergesTo L := Sum.eq hg_bij hg_conv
      have h_nonneg_g : (f ∘ g : Series).nonneg := by
        intro n
        by_cases hn : (0 : ℤ) ≤ n
        · simp [hn]; exact hpos (g (n.toNat)).1 (g (n.toNat)).2
        · simp [hn]
      have hsum_g : (f ∘ g : Series).converges := ⟨L, hconvL⟩
      have h_sum_g_sum_f : (f ∘ g : Series).sum = L :=
        convergesTo_uniq (convergesTo_sum hsum_g) hconvL
      have h_inj : Function.Injective g := hg_bij.1
      have hX_nonempty : X.Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr hX_empty
      set g_inv := Function.invFun g with hg_inv_def
      have hg_inv_spec (p : ℕ × ℕ) : g (g_inv p) = p :=
        Function.invFun_eq (hg_bij.2 p)
      have h_indices_nonempty : (Finset.image g_inv X).Nonempty :=
        Finset.image_nonempty.mpr hX_nonempty
      set n := (Finset.image g_inv X).max' h_indices_nonempty with hn_def
      have h_le_max (p) (hp : p ∈ X) : g_inv p ≤ n :=
        Finset.le_max' (Finset.image g_inv X) (g_inv p) (by
          apply Finset.mem_image.mpr; exact ⟨p, hp, rfl⟩)
      have h_cover : X ⊆ (Finset.Icc (0 : ℕ) n).image g := by
        intro p hp
        apply Finset.mem_image.mpr
        refine ⟨g_inv p, Finset.mem_Icc.mpr ⟨Nat.zero_le _, h_le_max p hp⟩, hg_inv_spec p⟩
      calc
        ∑ p ∈ X, f p ≤ ∑ p ∈ (Finset.Icc (0 : ℕ) n).image g, f p :=
          Finset.sum_le_sum_of_subset_of_nonneg h_cover (by
            intro p hp hpnX; simpa using hpos p.1 p.2)
        _ = ∑ k ∈ Finset.Icc (0 : ℕ) n, f (g k) :=
          Finset.sum_image (fun x hx y hy h => h_inj h)
        _ = (f ∘ g : Series).partial (n : ℤ) := by
          simp [Series.partial, Finset.Icc_eq_cast]
        _ ≤ (f ∘ g : Series).sum := partial_le_sum_of_nonneg h_nonneg_g hsum_g (n : ℤ)
        _ = L := h_sum_g_sum_f
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
      rcases hf with ⟨g, hg_bij, hg_conv⟩
      have hconvL : (f ∘ g : Series).convergesTo L := Sum.eq hg_bij hg_conv
      have h_event : ∀ᶠ N in atTop, |(f ∘ g : Series).partial N - L| < ε :=
        Metric.tendsto_nhds.mp hconvL ε hε
      rcases h_event.exists_forall_of_atTop with ⟨N, hN⟩
      set N' := max N 0 with hN'_def
      have hN'_pos : 0 ≤ N' := le_max_right N 0
      have hN'_ge_N : N' ≥ N := le_max_left _ _
      have hN'_ge_L : (f ∘ g : Series).partial N' ≥ L - ε := by
        have h_abs : |(f ∘ g : Series).partial N' - L| < ε := hN N' hN'_ge_N
        have h_abs' := abs_lt.mp h_abs
        linarith
      use (Finset.Icc (0 : ℕ) N'.toNat).image g
      calc
        ∑ p ∈ (Finset.Icc (0 : ℕ) N'.toNat).image g, f p
            = ∑ k ∈ Finset.Icc (0 : ℕ) N'.toNat, f (g k) :=
          Finset.sum_image (fun x hx y hy h => hg_bij.1 h)
        _ = (f ∘ g : Series).partial (N'.toNat : ℤ) := by
          rw [Series.partial, Finset.Icc_eq_cast N'.toNat, Finset.sum_map]
          simp
        _ = (f ∘ g : Series).partial N' := by
          simp [hN'_pos]
        _ ≥ L - ε := hN'_ge_L
    choose X hX using this
    have : ∃ N, ∃ M, X ⊆ (Icc (0 : ℕ) N) ×ˢ (Icc (0 : ℕ) M) := by
      by_cases hX_empty : X = ∅
      · use 0, 0; simp [hX_empty]
      · have hX_nonempty : X.Nonempty := Finset.nonempty_iff_ne_empty.mpr hX_empty
        have h_fst_nonempty : (X.image Prod.fst).Nonempty :=
          Finset.image_nonempty.mpr hX_nonempty
        have h_snd_nonempty : (X.image Prod.snd).Nonempty :=
          Finset.image_nonempty.mpr hX_nonempty
        let N := (X.image Prod.fst).max' h_fst_nonempty
        let M := (X.image Prod.snd).max' h_snd_nonempty
        use N, M
        intro p hp
        have h_fst_mem : p.1 ∈ X.image Prod.fst := Finset.mem_image.mpr ⟨p, hp, rfl⟩
        have h_snd_mem : p.2 ∈ X.image Prod.snd := Finset.mem_image.mpr ⟨p, hp, rfl⟩
        have h_fst_le : p.1 ≤ N :=
          Finset.le_max' (X.image Prod.fst) p.1 h_fst_mem
        have h_snd_le : p.2 ≤ M :=
          Finset.le_max' (X.image Prod.snd) p.2 h_snd_mem
        simp [Finset.mem_product, Finset.mem_Icc, h_fst_le, h_snd_le]
    choose N M hX' using this
    calc
      _ ≤ ∑ p ∈ X, f p := hX
      _ ≤ ∑ p ∈ (Icc 0 N) ×ˢ (Icc 0 M), f p :=
        Finset.sum_le_sum_of_subset_of_nonneg hX' (by
          intro p hp hpnX; simpa using hpos p.1 p.2)
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
    ext ⟨n, m⟩
    dsimp [fplus, fminus]
    have hcalc : ∀ x : ℝ, max x 0 - max (-x) 0 = x := by
      intro x
      by_cases hx : 0 ≤ x
      · simp [hx]
      · have hx' : x ≤ 0 := by linarith
        have hnx : 0 ≤ -x := by linarith
        simp [hx', hnx]
    exact (hcalc (f (n, m))).symm
  have hfplus_conv : AbsConvergent fplus := by
    rcases hf with ⟨g, hg_bij, hg_conv⟩
    use g, hg_bij
    have h_ineq (x : ℝ) : |max x 0| ≤ |x| := by
      by_cases hx : 0 ≤ x
      · have : max x 0 = x := max_eq_left hx; simp [this]
      · have hx' : x ≤ 0 := by linarith
        have : max x 0 = 0 := max_eq_right hx'; simp [this, abs_nonneg]
    have hcomp : ∀ n, n ≥ (fplus ∘ g : Series).m → |(fplus ∘ g : Series).seq n| ≤ ((f ∘ g : Series).abs).seq n := by
      intro n hn
      have hnpos : (0 : ℤ) ≤ n := by simpa using hn
      simpa [hnpos, fplus] using h_ineq ((f ∘ g : Series).seq n)
    have hm : (fplus ∘ g : Series).m = ((f ∘ g : Series).abs).m := by simp
    exact (Series.converges_of_le hm hcomp hg_conv).1
  have hfminus_conv : AbsConvergent fminus := by
    rcases hf with ⟨g, hg_bij, hg_conv⟩
    use g, hg_bij
    have h_ineq (x : ℝ) : |max (-x) 0| ≤ |x| := by
      by_cases hx : 0 ≤ x
      · have hx' : -x ≤ 0 := by linarith
        have : max (-x) 0 = 0 := max_eq_right hx'; simp [this, abs_nonneg]
      · have hnx : 0 ≤ -x := by linarith
        have : max (-x) 0 = -x := max_eq_left hnx; simp [this, abs_neg]
    have hcomp : ∀ n, n ≥ (fminus ∘ g : Series).m → |(fminus ∘ g : Series).seq n| ≤ ((f ∘ g : Series).abs).seq n := by
      intro n hn
      have hnpos : (0 : ℤ) ≤ n := by simpa using hn
      simpa [hnpos, fminus] using h_ineq ((f ∘ g : Series).seq n)
    have hm : (fminus ∘ g : Series).m = ((f ∘ g : Series).abs).m := by simp
    exact (Series.converges_of_le hm hcomp hg_conv).1
  choose hfplus_conv' hfplus_sum using sum_of_sum_of_AbsConvergent_nonneg hfplus_conv hfplus_nonneg
  choose hfminus_conv' hfminus_sum using sum_of_sum_of_AbsConvergent_nonneg hfminus_conv hfminus_nonneg
  split_ands
  . intro n
    have h_nonneg_fplus : ((fun m ↦ fplus (n, m)):Series).nonneg := by
      intro m; simp; split_ifs with h
      · exact hfplus_nonneg n m.toNat
      · simp
    have h_nonneg_fminus : ((fun m ↦ fminus (n, m)):Series).nonneg := by
      intro m; simp; split_ifs with h
      · exact hfminus_nonneg n m.toNat
      · simp
    have h_fplus_abs_conv : ((fun m ↦ fplus (n, m)):Series).absConverges := by
      have h_eq : ((fun m ↦ fplus (n, m)):Series).abs = ((fun m ↦ fplus (n, m)):Series) := by
        refine Series.ext rfl (funext fun m => ?_)
        by_cases hm : (0 : ℤ) ≤ m
        · simp [hm, hfplus_nonneg n m.toNat]
        · simp [hm]
      dsimp [Series.absConverges]
      rw [h_eq]
      exact hfplus_conv' n
    have h_fminus_abs_conv : ((fun m ↦ fminus (n, m)):Series).absConverges := by
      have h_eq : ((fun m ↦ fminus (n, m)):Series).abs = ((fun m ↦ fminus (n, m)):Series) := by
        refine Series.ext rfl (funext fun m => ?_)
        by_cases hm : (0 : ℤ) ≤ m
        · simp [hm, hfminus_nonneg n m.toNat]
        · simp [hm]
      dsimp [Series.absConverges]
      rw [h_eq]
      exact hfminus_conv' n
    have h_sum_conv : ((fun m ↦ fplus (n, m) + fminus (n, m)):Series).converges := by
      have h : (((fun m ↦ fplus (n, m)):Series) + ((fun m ↦ fminus (n, m)):Series)).converges :=
        (Series.add (hfplus_conv' n) (hfminus_conv' n)).1
      have h_eq : (((fun m ↦ fplus (n, m)):Series) + ((fun m ↦ fminus (n, m)):Series)) = ((fun m ↦ fplus (n, m) + fminus (n, m)):Series) := by
        apply Series.ext
        · calc
            (((fun m ↦ fplus (n, m)):Series) + ((fun m ↦ fminus (n, m)):Series)).m
                = min ((fun m ↦ fplus (n, m)):Series).m ((fun m ↦ fminus (n, m)):Series).m := rfl
            _ = min 0 0 := by simp
            _ = 0 := by simp
        · ext m
          calc
            (((fun m ↦ fplus (n, m)):Series) + ((fun m ↦ fminus (n, m)):Series)).seq m
                = ((fun m ↦ fplus (n, m)):Series).seq m + ((fun m ↦ fminus (n, m)):Series).seq m := rfl
            _ = ((fun m ↦ fplus (n, m) + fminus (n, m)):Series).seq m := by
              by_cases hm : (0 : ℤ) ≤ m <;> simp [hm]
      rw [h_eq] at h
      exact h
    have hcomp : ∀ m : ℤ,
      |((fun m' ↦ f (n, m')):Series).seq m| ≤ ((fun m' ↦ fplus (n, m') + fminus (n, m')):Series).seq m := by
      intro m
      by_cases hm : (0 : ℤ) ≤ m
      · simp [hm, hdiff]
        have h1 : 0 ≤ fplus (n, m.toNat) := hfplus_nonneg n m.toNat
        have h2 : 0 ≤ fminus (n, m.toNat) := hfminus_nonneg n m.toNat
        calc
          |fplus (n, m.toNat) - fminus (n, m.toNat)| ≤ |fplus (n, m.toNat)| + |fminus (n, m.toNat)| := abs_sub _ _
          _ = fplus (n, m.toNat) + fminus (n, m.toNat) := by rw [abs_of_nonneg h1, abs_of_nonneg h2]
      · simp [hm]
    have hm : ((fun m' ↦ f (n, m')):Series).m = ((fun m' ↦ fplus (n, m') + fminus (n, m')):Series).m := rfl
    exact (Series.converges_of_le hm (fun m hm' => hcomp m) h_sum_conv).1
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

abbrev AbsConvergent' {X:Type} (f: X → ℝ) : Prop := BddAbove ( (fun A ↦ ∑ x ∈ A, |f x|) '' .univ )

theorem AbsConvergent'.of_finite {X:Type} [Finite X] (f:X → ℝ) : AbsConvergent' f := by
  have _ := Fintype.ofFinite X
  simp [bddAbove_def]; use ∑ x, |f x|; intro A; apply Finset.sum_le_univ_sum_of_nonneg; simp

/-- Lemma 8.2.3 / Exercise 8.2.1 -/
theorem AbsConvergent.iff {X:Type} (hX:CountablyInfinite X) (f : X → ℝ) :
  AbsConvergent f ↔ AbsConvergent' f := by
  constructor
  · intro hf
    rcases hf with ⟨g, hg, hconv⟩
    rw [AbsConvergent', bddAbove_def]
    have hpos : ((f ∘ g : Series).abs).nonneg := by
      intro n; by_cases h : (0 : ℤ) ≤ n <;> simp [h]
    have hsum : ((f ∘ g : Series).abs).converges := hconv
    have hsum_val : ((f ∘ g : Series).abs).convergesTo ((f ∘ g : Series).abs).sum :=
      convergesTo_sum hsum
    use ((f ∘ g : Series).abs).sum
    intro z hz
    rcases hz with ⟨A, hA, rfl⟩
    have hinj : Function.Injective g := hg.1
    have hsurj : Function.Surjective g := hg.2
    have h_g_inv_spec (x : X) : g (Function.invFun g x) = x := Function.invFun_eq (hsurj x)
    by_cases hA_empty : A = ∅
    · subst hA_empty; simp; exact Series.sum_of_nonneg hpos
    · have h_nonempty : A.Nonempty := Finset.nonempty_iff_ne_empty.mpr hA_empty
      have h_image_nonempty : (A.image (Function.invFun g)).Nonempty :=
        Finset.image_nonempty.mpr h_nonempty
      set N := (A.image (Function.invFun g)).max' h_image_nonempty
      have hN_bound (x : X) (hxA : x ∈ A) : Function.invFun g x ≤ N :=
        Finset.le_max' _ _ (Finset.mem_image.mpr ⟨x, hxA, rfl⟩)
      calc
        ∑ x ∈ A, |f x| = ∑ x ∈ A, |f (g (Function.invFun g x))| := by simp [h_g_inv_spec]
        _ = ∑ n ∈ A.image (Function.invFun g), |f (g n)| := by
          have h_inj_on_A : ∀ x ∈ A, ∀ y ∈ A, Function.invFun g x = Function.invFun g y → x = y := by
            intro x hx y hy h
            calc
              x = g (Function.invFun g x) := (h_g_inv_spec x).symm
              _ = g (Function.invFun g y) := by rw [h]
              _ = y := h_g_inv_spec y
          rw [Finset.sum_image h_inj_on_A]
        _ ≤ ∑ n ∈ Finset.Icc (0 : ℕ) N, |f (g n)| := by
          have h_subset : A.image (Function.invFun g) ⊆ Finset.Icc (0 : ℕ) N := by
            intro n hn
            rcases Finset.mem_image.mp hn with ⟨x, hx, rfl⟩
            exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, hN_bound x hx⟩
          have h_nonneg : 0 ≤ ∑ n ∈ (Finset.Icc (0 : ℕ) N \ A.image (Function.invFun g)), |f (g n)| :=
            Finset.sum_nonneg (λ n hn => abs_nonneg _)
          calc
            ∑ n ∈ A.image (Function.invFun g), |f (g n)| ≤
              (∑ n ∈ A.image (Function.invFun g), |f (g n)|) +
              (∑ n ∈ (Finset.Icc (0 : ℕ) N \ A.image (Function.invFun g)), |f (g n)|) := by nlinarith
            _ = ∑ n ∈ (A.image (Function.invFun g)) ∪ (Finset.Icc (0 : ℕ) N \ A.image (Function.invFun g)), |f (g n)| := by
              rw [Finset.sum_union (Finset.disjoint_sdiff)]
            _ = ∑ n ∈ Finset.Icc (0 : ℕ) N, |f (g n)| := by
              have h_union : (A.image (Function.invFun g)) ∪ (Finset.Icc (0 : ℕ) N \ A.image (Function.invFun g)) = Finset.Icc (0 : ℕ) N := by
                ext n; constructor
                · intro hn; rcases Finset.mem_union.mp hn with (hn' | hn')
                  · exact h_subset hn'
                  · exact (Finset.mem_sdiff.mp hn').1
                · intro hn
                  by_cases hn_in_A : n ∈ A.image (Function.invFun g)
                  · exact Finset.mem_union_left _ hn_in_A
                  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hn, hn_in_A⟩)
              rw [h_union]
        _ = ((f ∘ g : Series).abs).partial (N : ℤ) := by
          simp [Series.partial, Finset.Icc_eq_cast]
        _ ≤ ((f ∘ g : Series).abs).sum :=
          partial_le_sum_of_nonneg hpos hsum (N : ℤ)
  · intro hf
    have ⟨ g, hg ⟩ := hX.symm
    refine ⟨ g, hg, ?_ ⟩
    simp [bddAbove_def] at hf
    choose L hL using hf
    unfold absConverges; rw [converges_of_nonneg_iff]
    · use L; intro N; by_cases hN : N ≥ 0
      · lift N to ℕ using hN
        set g' := Embedding.mk g hg.1
        convert hL (map g' (Icc 0 N))
        simp [Series.partial]; rfl
      · convert hL ∅
        simp; apply partial_of_lt; grind
    · simp [nonneg]
      intro n; by_cases h : n ≥ 0 <;> simp [h]

/-- Not in textbook, but should have been included. -/
theorem AbsConvergent'.of_countable {X:Type} (hX:CountablyInfinite X) {f:X → ℝ} :
  AbsConvergent' f ↔ AbsConvergent f :=
  (AbsConvergent.iff hX f).symm

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

/-- Lemma 8.2.5 / Exercise 8.2.2-/
theorem AbsConvergent'.countable_supp {X:Type} {f:X → ℝ} (hf: AbsConvergent' f) :
  AtMostCountable { x | f x ≠ 0 } := by
  have h_summable : Summable f := (AbsConvergent'.iff_Summable f).mp hf
  have h_support_countable : Set.Countable (Function.support f) :=
    h_summable.countable_support
  have h_countable_subtype : Countable (Subtype (Function.support f)) :=
    h_support_countable
  have h_at_most : AtMostCountable (Function.support f) :=
    ((AtMostCountable.iff (Function.support f)).mpr h_countable_subtype)
  simpa [Function.support]

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
  have h_add_abs : AbsConvergent' (f+g) := by
    rcases hf with ⟨Mf, hMf⟩
    rcases hg with ⟨Mg, hMg⟩
    refine ⟨Mf + Mg, ?_⟩
    intro z hz
    rcases hz with ⟨A, hA, rfl⟩
    have hz_f : ∑ x ∈ A, |f x| ≤ Mf := hMf ⟨A, hA, rfl⟩
    have hz_g : ∑ x ∈ A, |g x| ≤ Mg := hMg ⟨A, hA, rfl⟩
    calc
      ∑ x ∈ A, |(f + g) x| ≤ ∑ x ∈ A, (|f x| + |g x|) :=
        Finset.sum_le_sum (λ x _ => by simpa using abs_add_three (f x) (g x) 0)
      _ = (∑ x ∈ A, |f x|) + (∑ x ∈ A, |g x|) := by simp [Finset.sum_add_distrib]
      _ ≤ Mf + Mg := by nlinarith
  have h_add_sum : Sum' (f + g) = ∑' x, (f + g) x := Sum'.eq_tsum (f + g) h_add_abs
  have h_f_sum : Sum' f = ∑' x, f x := Sum'.eq_tsum f hf
  have h_g_sum : Sum' g = ∑' x, g x := Sum'.eq_tsum g hg
  have h_sf : Summable f := (AbsConvergent'.iff_Summable f).mp hf
  have h_sg : Summable g := (AbsConvergent'.iff_Summable g).mp hg
  have h_tsum_add : ∑' x, (f + g) x = (∑' x, f x) + (∑' x, g x) := by
    simpa using (h_sf.hasSum.add h_sg.hasSum).tsum_eq
  refine ⟨h_add_abs, ?_⟩
  calc
    Sum' (f + g) = ∑' x, (f + g) x := h_add_sum
    _ = (∑' x, f x) + (∑' x, g x) := h_tsum_add
    _ = Sum' f + Sum' g := by rw [h_f_sum, h_g_sum]

/-- Proposition 8.2.6 (b) (Absolutely convergent series laws) / Exercise 8.2.3 -/
theorem Sum'.smul {X:Type} {f:X → ℝ} (hf: AbsConvergent' f) (c: ℝ) :
  AbsConvergent' (c • f) ∧ Sum' (c • f) = c * Sum' f := by
  have h_smul_abs : AbsConvergent' (c • f) := by
    rcases hf with ⟨M, hM⟩
    refine ⟨|c| * M, ?_⟩
    intro z hz
    rcases hz with ⟨A, hA, rfl⟩
    have hz_f : ∑ x ∈ A, |f x| ≤ M := hM ⟨A, hA, rfl⟩
    calc
      ∑ x ∈ A, |(c • f) x| = ∑ x ∈ A, |c * f x| := rfl
      _ = ∑ x ∈ A, (|c| * |f x|) := by simp
      _ = |c| * (∑ x ∈ A, |f x|) := by simp [Finset.mul_sum]
      _ ≤ |c| * M := mul_le_mul_of_nonneg_left hz_f (abs_nonneg _)
  have h_smul_sum : Sum' (c • f) = ∑' x, (c • f) x := Sum'.eq_tsum (c • f) h_smul_abs
  have h_f_sum : Sum' f = ∑' x, f x := Sum'.eq_tsum f hf
  have h_sf : Summable f := (AbsConvergent'.iff_Summable f).mp hf
  have h_tsum_smul : ∑' x, (c • f) x = c * (∑' x, f x) := by
    simpa [smul_eq_mul] using (h_sf.hasSum.const_smul c).tsum_eq
  refine ⟨h_smul_abs, ?_⟩
  calc
    Sum' (c • f) = ∑' x, (c • f) x := h_smul_sum
    _ = c * (∑' x, f x) := h_tsum_smul
    _ = c * Sum' f := by rw [h_f_sum]

/-- This law is not explicitly stated in Proposition 8.2.6, but follows easily from parts (a) and (b).-/
theorem Sum'.sub {X:Type} {f g:X → ℝ} (hf: AbsConvergent' f) (hg: AbsConvergent' g) :
  AbsConvergent' (f-g) ∧ Sum' (f - g) = Sum' f - Sum' g := by
  convert Sum'.add hf (Sum'.smul hg (-1)).1 using 2
  . simp; abel
  . congr; simp; abel
  rw [(Sum'.smul hg (-1)).2]; ring

/-- Proposition 8.2.6 (c) (Absolutely convergent series laws) / Exercise 8.2.3.  The first
    part of this proposition has been moved to {lean}`AbsConvergent'.subtype`. -/
theorem Sum'.of_disjoint_union {X:Type} {f:X → ℝ} (hf: AbsConvergent' f) {X₁ X₂ : Set X} (hdisj: Disjoint X₁ X₂):
  Sum' (fun x: (X₁ ∪ X₂: Set X) ↦ f x) = Sum' (fun x : X₁ ↦ f x) + Sum' (fun x : X₂ ↦ f x) := by
  have h_abs_union : AbsConvergent' (fun x : (X₁ ∪ X₂ : Set X) ↦ f x) := hf.subtype (X₁ ∪ X₂)
  have h_abs_X₁ : AbsConvergent' (fun x : X₁ ↦ f x) := hf.subtype X₁
  have h_abs_X₂ : AbsConvergent' (fun x : X₂ ↦ f x) := hf.subtype X₂
  have h_union_sum : Sum' (fun x : (X₁ ∪ X₂ : Set X) ↦ f x) = ∑' x : (X₁ ∪ X₂ : Set X), f x :=
    Sum'.eq_tsum _ h_abs_union
  have h_X₁_sum : Sum' (fun x : X₁ ↦ f x) = ∑' x : X₁, f x := Sum'.eq_tsum _ h_abs_X₁
  have h_X₂_sum : Sum' (fun x : X₂ ↦ f x) = ∑' x : X₂, f x := Sum'.eq_tsum _ h_abs_X₂
  have h_tsum_union : ∑' x : (X₁ ∪ X₂ : Set X), f x = (∑' x : X₁, f x) + (∑' x : X₂, f x) := by
    have h_s_f : Summable f := (AbsConvergent'.iff_Summable f).mp hf
    have h_ind₁ : Summable (Set.indicator X₁ f) := Summable.indicator h_s_f X₁
    have h_ind₂ : Summable (Set.indicator X₂ f) := Summable.indicator h_s_f X₂
    calc
      ∑' x : (X₁ ∪ X₂ : Set X), f x = ∑' x : X, Set.indicator (X₁ ∪ X₂) f x := by
        simpa using tsum_subtype (X₁ ∪ X₂) f
      _ = ∑' x : X, (Set.indicator X₁ f + Set.indicator X₂ f) x := by
        simp [Set.indicator_union_of_disjoint hdisj f]
      _ = (∑' x : X, Set.indicator X₁ f x) + (∑' x : X, Set.indicator X₂ f x) := by
        simpa using (h_ind₁.hasSum.add h_ind₂.hasSum).tsum_eq
      _ = (∑' x : X₁, f x) + (∑' x : X₂, f x) := by
        simp [tsum_subtype X₁ f, tsum_subtype X₂ f]
  calc
    Sum' (fun x : (X₁ ∪ X₂ : Set X) ↦ f x) = ∑' x : (X₁ ∪ X₂ : Set X), f x := h_union_sum
    _ = (∑' x : X₁, f x) + (∑' x : X₂, f x) := h_tsum_union
    _ = Sum' (fun x : X₁ ↦ f x) + Sum' (fun x : X₂ ↦ f x) := by rw [h_X₁_sum, h_X₂_sum]

/-- This technical claim, the analogue of {name}`tsum_univ`, is required due to the way Mathlib handles
    sets.-/
theorem Sum'.of_univ {X:Type} {f:X → ℝ} (hf: AbsConvergent' f) :
  Sum' (fun x: (.univ : Set X) ↦ f x) = Sum' f := by
  calc
    Sum' (fun x : (.univ : Set X) ↦ f x) = ∑' x : (.univ : Set X), f x :=
      Sum'.eq_tsum _ (hf.subtype .univ)
    _ = ∑' x : X, f x := by simp
    _ = Sum' f := (Sum'.eq_tsum f hf).symm

theorem Sum'.of_comp {X Y:Type} {f:X → ℝ} (hf: AbsConvergent' f) {φ: Y → X}
  (hφ: Function.Bijective φ) :
  AbsConvergent' (f ∘ φ) ∧ Sum' f = Sum' (f ∘ φ) := by
  classical
  have h_abs_comp : AbsConvergent' (f ∘ φ) := by
    rcases hf with ⟨M, hM⟩
    refine ⟨M, ?_⟩
    intro z hz
    rcases hz with ⟨A, hA, rfl⟩
    have h_φA_mem : (∑ x ∈ A.image φ, |f x|) ∈ (fun A' ↦ ∑ x ∈ A', |f x|) '' .univ :=
      ⟨A.image φ, Set.mem_univ _, rfl⟩
    have h_φA_le : ∑ x ∈ A.image φ, |f x| ≤ M := hM h_φA_mem
    rw [Finset.sum_image (hφ.1.injOn (s := (A : Set Y)))] at h_φA_le
    calc
      ∑ y ∈ A, |(f ∘ φ) y| = ∑ y ∈ A, |f (φ y)| := rfl
      _ ≤ M := h_φA_le
  have h_comp_sum : Sum' (f ∘ φ) = ∑' y, (f ∘ φ) y := Sum'.eq_tsum (f ∘ φ) h_abs_comp
  have h_f_sum : Sum' f = ∑' x, f x := Sum'.eq_tsum f hf
  have h_tsum_comp : ∑' y, (f ∘ φ) y = ∑' x, f x := by
    simpa using (Equiv.ofBijective φ hφ).tsum_eq f
  refine ⟨h_abs_comp, ?_⟩
  rw [h_comp_sum, h_tsum_comp, (h_f_sum).symm]

/-- Lemma 8.2.7 / Exercise 8.2.4 -/
theorem divergent_parts_of_divergent {a: ℕ → ℝ} (ha: (a:Series).converges)
  (ha': ¬ (a:Series).absConverges) :
  ¬ AbsConvergent (fun n : {n | a n ≥ 0} ↦ a n) ∧ ¬ AbsConvergent (fun n : {n | a n < 0} ↦ a n)
  := by
  set a_plus := max a 0 with ha_plus
  set a_minus := max (-a) 0 with ha_minus
  have max_sub_max_eq (x : ℝ) : max x 0 - max (-x) 0 = x := by
    by_cases hx : 0 ≤ x
    · simp [hx]
    · have hx' : x ≤ 0 := by linarith
      simp [hx']
  have h_ineq (x : ℝ) : |max x 0| ≤ |x| := by
    by_cases hx : 0 ≤ x
    · simp [hx]
    · have hx' : x ≤ 0 := by linarith
      simp [hx']
  have h_ineq_neg (x : ℝ) : |max (-x) 0| ≤ |x| :=
    calc
      |max (-x) 0| ≤ |-x| := h_ineq (-x)
      _ = |x| := by simp
  have ha_nonneg_plus : (a_plus : Series).nonneg := by
    intro n
    dsimp [a_plus, Series.nonneg]
    by_cases hn : (0 : ℤ) ≤ n
    · simp [hn]
    · simp [hn]
  have ha_nonneg_minus : (a_minus : Series).nonneg := by
    intro n
    dsimp [a_minus, Series.nonneg]
    by_cases hn : (0 : ℤ) ≤ n
    · simp [hn]
    · simp [hn]
  have hcalc_abs_add (x : ℝ) : |x| = max x 0 + max (-x) 0 := by
    by_cases hx : 0 ≤ x
    · simp [hx]
    · have hx_neg : x < 0 := by linarith
      rw [abs_of_neg hx_neg, max_eq_right (by linarith : x ≤ 0), max_eq_left (by linarith : 0 ≤ -x)]
      simp
  have h_abs_add : (a : Series).abs = (a_plus : Series) + (a_minus : Series) := by
    apply Series.ext
    ·     calc
        (a : Series).abs.m = 0 := by simp
        _ = min (0 : ℤ) 0 := by simp
        _ = min ((a_plus : Series).m) ((a_minus : Series).m) := rfl
        _ = ((a_plus : Series) + (a_minus : Series)).m := rfl
    · ext n
      calc
        ((a : Series).abs).seq n = |(a : Series).seq n| := by
          by_cases hn : n ≥ (0 : ℤ)
          · simp [hn]
          · simp [hn]
        _ = max ((a : Series).seq n) 0 + max (-(a : Series).seq n) 0 :=
          hcalc_abs_add ((a : Series).seq n)
        _ = (a_plus : Series).seq n + (a_minus : Series).seq n := by
          by_cases hn : n ≥ (0 : ℤ)
          · simp [a_plus, a_minus, hn]
          · simp [a_plus, a_minus, hn]
        _ = ((a_plus : Series) + (a_minus : Series)).seq n := rfl
  have nonneg_absConverges_iff_converges {s : Series} (hnon : s.nonneg) : s.absConverges ↔ s.converges := by
    unfold Series.absConverges
    have h : s.abs = s := by
      refine Series.ext rfl (funext fun n => ?_)
      by_cases hn : n ≥ s.m
      · simp [hnon n, hn]
      · have hn' : n < s.m := by omega
        simp [s.vanish n hn']
    simp [h]
  have h_abs_conv_iff : (a : Series).absConverges ↔ ((a_plus : Series).converges ∧ (a_minus : Series).converges) := by
    constructor
    · intro h
      have h_abs_conv : ((a : Series).abs).converges := h
      have h_plus_conv : (a_plus : Series).converges := by
        have hm : (a_plus : Series).m = ((a : Series).abs).m := rfl
        have h_le : ∀ n ≥ (a_plus : Series).m, |(a_plus : Series).seq n| ≤ ((a : Series).abs).seq n := by
          intro n hn
          have hnpos : (0 : ℤ) ≤ n := hn
          have h1 : (a_plus : Series).seq n = max (a n.toNat) 0 := by simp [a_plus, hnpos]
          have h2 : ((a : Series).abs).seq n = |a n.toNat| := by simp [hnpos]
          rw [h1, h2]
          exact h_ineq (a n.toNat)
        have h_abs_conv_plus : (a_plus : Series).absConverges :=
          (Series.converges_of_le hm h_le h_abs_conv).1
        rw [nonneg_absConverges_iff_converges ha_nonneg_plus] at h_abs_conv_plus
        exact h_abs_conv_plus
      have h_minus_conv : (a_minus : Series).converges := by
        have hm : (a_minus : Series).m = ((a : Series).abs).m := rfl
        have h_le : ∀ n ≥ (a_minus : Series).m, |(a_minus : Series).seq n| ≤ ((a : Series).abs).seq n := by
          intro n hn
          have hnpos : (0 : ℤ) ≤ n := hn
          have h1 : (a_minus : Series).seq n = max (-(a n.toNat)) 0 := by simp [a_minus, hnpos]
          have h2 : ((a : Series).abs).seq n = |a n.toNat| := by simp [hnpos]
          rw [h1, h2]
          exact h_ineq_neg (a n.toNat)
        have h_abs_conv_minus : (a_minus : Series).absConverges :=
          (Series.converges_of_le hm h_le h_abs_conv).1
        rw [nonneg_absConverges_iff_converges ha_nonneg_minus] at h_abs_conv_minus
        exact h_abs_conv_minus
      exact ⟨h_plus_conv, h_minus_conv⟩
    · intro ⟨h_plus, h_minus⟩
      have h_add_conv : ((a_plus : Series) + (a_minus : Series)).converges := (Series.add h_plus h_minus).1
      rw [Series.absConverges, h_abs_add]
      exact h_add_conv
  have h_not_both : ¬ ((a_plus : Series).converges ∧ (a_minus : Series).converges) := by
    rw [← h_abs_conv_iff]
    exact ha'
  have ha_eq_sub : (a : Series) = (a_plus : Series) - (a_minus : Series) := by
    apply Series.ext
    · calc
        (a : Series).m = 0 := by simp
        _ = min (0 : ℤ) 0 := by simp
        _ = min ((a_plus : Series).m) ((a_minus : Series).m) := rfl
        _ = ((a_plus : Series) - (a_minus : Series)).m := rfl
    · ext n
      calc
        (a : Series).seq n = (a_plus : Series).seq n - (a_minus : Series).seq n := by
          by_cases hn : n ≥ (0 : ℤ)
          · simp [a_plus, a_minus, max_sub_max_eq, hn]
          · simp [a_plus, a_minus, hn]
        _ = ((a_plus : Series) - (a_minus : Series)).seq n := rfl

  have ha_plus_partial_range (N : ℕ) : ((a_plus : Series).partial (N : ℤ)) = ∑ k ∈ Finset.range (N+1), max (a k) 0 := by
    calc
      ((a_plus : Series).partial (N : ℤ)) = ∑ x ∈ Finset.Icc (0 : ℤ) (N : ℤ), (a_plus : Series).seq x := rfl
      _ = ∑ x ∈ Finset.Icc (0 : ℤ) (N : ℤ), max ((a : Series).seq x) 0 := by
        simp [a_plus]
      _ = ∑ x ∈ Finset.Icc (0 : ℤ) (N : ℤ), max (a x.toNat) 0 := by
        refine Finset.sum_congr rfl (λ x hx => ?_)
        have hx0 : (0 : ℤ) ≤ x := (Finset.mem_Icc.mp hx).1
        simp [hx0]
      _ = ∑ k ∈ (Finset.Icc (0 : ℤ) (N : ℤ)).image (λ (x : ℤ) => x.toNat), max (a k) 0 := by
        rw [Finset.sum_image (λ x hx y hy h => ?_)]
        have hx0 : 0 ≤ x := (Finset.mem_Icc.mp hx).1
        have hy0 : 0 ≤ y := (Finset.mem_Icc.mp hy).1
        have hx_toNat_x : (x.toNat : ℤ) = x := by exact mod_cast Int.toNat_of_nonneg hx0
        have hy_toNat_y : (y.toNat : ℤ) = y := by exact mod_cast Int.toNat_of_nonneg hy0
        calc
          x = (x.toNat : ℤ) := by symm; exact hx_toNat_x
          _ = (y.toNat : ℤ) := by rw [h]
          _ = y := hy_toNat_y
      _ = ∑ k ∈ Finset.range (N+1), max (a k) 0 := by
        have h_range : (Finset.Icc (0 : ℤ) (N : ℤ)).image (λ (x : ℤ) => x.toNat) = Finset.range (N+1) := by
          ext k; constructor
          · intro hk
            rcases Finset.mem_image.mp hk with ⟨x, hx, rfl⟩
            rcases Finset.mem_Icc.mp hx with ⟨hx0, hxn⟩
            have hkn : x.toNat ≤ N := by omega
            exact Finset.mem_range_succ_iff.mpr hkn
          · intro hk
            have hkn : k ≤ N := Finset.mem_range_succ_iff.mp hk
            refine Finset.mem_image.mpr ⟨(k : ℤ), Finset.mem_Icc.mpr ⟨by exact mod_cast (Nat.zero_le k), by exact mod_cast hkn⟩, ?_⟩
            simp
        rw [h_range]

  have ha_minus_partial_range (N : ℕ) : ((a_minus : Series).partial (N : ℤ)) = ∑ k ∈ Finset.range (N+1), max (-(a k)) 0 := by
    calc
      ((a_minus : Series).partial (N : ℤ)) = ∑ x ∈ Finset.Icc (0 : ℤ) (N : ℤ), (a_minus : Series).seq x := rfl
      _ = ∑ x ∈ Finset.Icc (0 : ℤ) (N : ℤ), max (-(a : Series).seq x) 0 := by
        simp [a_minus]
      _ = ∑ x ∈ Finset.Icc (0 : ℤ) (N : ℤ), max (-(a x.toNat)) 0 := by
        refine Finset.sum_congr rfl (λ x hx => ?_)
        have hx0 : (0 : ℤ) ≤ x := (Finset.mem_Icc.mp hx).1
        simp [hx0]
      _ = ∑ k ∈ (Finset.Icc (0 : ℤ) (N : ℤ)).image (λ (x : ℤ) => x.toNat), max (-(a k)) 0 := by
        rw [Finset.sum_image (λ x hx y hy h => ?_)]
        have hx0 : 0 ≤ x := (Finset.mem_Icc.mp hx).1
        have hy0 : 0 ≤ y := (Finset.mem_Icc.mp hy).1
        have hx_toNat_x : (x.toNat : ℤ) = x := by exact mod_cast Int.toNat_of_nonneg hx0
        have hy_toNat_y : (y.toNat : ℤ) = y := by exact mod_cast Int.toNat_of_nonneg hy0
        calc
          x = (x.toNat : ℤ) := by symm; exact hx_toNat_x
          _ = (y.toNat : ℤ) := by rw [h]
          _ = y := hy_toNat_y
      _ = ∑ k ∈ Finset.range (N+1), max (-(a k)) 0 := by
        have h_range : (Finset.Icc (0 : ℤ) (N : ℤ)).image (λ (x : ℤ) => x.toNat) = Finset.range (N+1) := by
          ext k; constructor
          · intro hk
            rcases Finset.mem_image.mp hk with ⟨x, hx, rfl⟩
            rcases Finset.mem_Icc.mp hx with ⟨hx0, hxn⟩
            have hkn : x.toNat ≤ N := by omega
            exact Finset.mem_range_succ_iff.mpr hkn
          · intro hk
            have hkn : k ≤ N := Finset.mem_range_succ_iff.mp hk
            refine Finset.mem_image.mpr ⟨(k : ℤ), Finset.mem_Icc.mpr ⟨by exact mod_cast (Nat.zero_le k), by exact mod_cast hkn⟩, ?_⟩
            simp
        rw [h_range]

  have h_not_abs_conv_plus : ¬ AbsConvergent (fun n : {n | a n ≥ 0} ↦ a n) := by
    classical
    intro hpos
    by_cases hfinite : Finite {n | a n ≥ 0}
    · rcases hpos with ⟨g, hg_bij, _⟩
      have h_infinite : Infinite {n | a n ≥ 0} :=
        Infinite.of_injective g hg_bij.1
      exact hfinite.not_infinite h_infinite
    · haveI hinf : Infinite {n | a n ≥ 0} := ⟨hfinite⟩
      have hcount : CountablyInfinite {n | a n ≥ 0} :=
        Nat.countable_of_infinite (X := {n | a n ≥ 0})
      have h_bdd := ((AbsConvergent.iff hcount (fun n : {n | a n ≥ 0} ↦ a n)).mp hpos)
      rcases h_bdd with ⟨M, hM⟩
      have ha_plus_conv : (a_plus : Series).converges := by
        apply (Series.converges_of_nonneg_iff ha_nonneg_plus).mpr
        use M
        intro N
        by_cases hN : N ≥ (0 : ℤ)
        · have hN_nonneg : (0 : ℤ) ≤ N := hN
          have hN_val : ((Int.toNat N : ℕ) : ℤ) = N := by exact mod_cast Int.toNat_of_nonneg hN_nonneg
          have h_partial_eq : (a_plus : Series).partial (N : ℤ) = ∑ k ∈ ((Finset.range ((Int.toNat N : ℕ)+1 : ℕ)).filter (λ m : ℕ => 0 ≤ a m)), a k := by
            calc
              (a_plus : Series).partial (N : ℤ) = (a_plus : Series).partial ((Int.toNat N : ℕ) : ℤ) := by rw [hN_val]
              _ = ∑ k ∈ Finset.range ((Int.toNat N : ℕ)+1), max (a k) 0 := ha_plus_partial_range (Int.toNat N)
              _ = ∑ k ∈ Finset.range ((Int.toNat N : ℕ)+1), (if 0 ≤ a k then a k else 0) := by
                refine Finset.sum_congr rfl (λ m hm => ?_)
                by_cases hm_nonneg : 0 ≤ a m
                · simp [hm_nonneg]
                · have hm_nonpos : a m ≤ 0 := by linarith
                  simp [hm_nonneg, hm_nonpos]
              _ = ∑ k ∈ (Finset.range ((Int.toNat N : ℕ)+1 : ℕ)).filter (λ m : ℕ => 0 ≤ a m), a k := by
                rw [← Finset.sum_filter]
          rw [h_partial_eq]
          let S := (Finset.range ((Int.toNat N : ℕ)+1 : ℕ)).filter (λ m : ℕ => 0 ≤ a m)
          let A : Finset {n | a n ≥ 0} :=
            S.attach.image (λ (x : S) => ⟨x.val, (Finset.mem_filter.mp x.property).2⟩)
          have h_A_sum : ∑ x ∈ A, |(fun (n : {n | a n ≥ 0}) ↦ a n) x| = ∑ n ∈ S, a n := by
            calc
              ∑ x ∈ A, |(fun (n : {n | a n ≥ 0}) ↦ a n) x| = ∑ x ∈ A, a x := by
                refine Finset.sum_congr rfl (λ x hx => ?_)
                have hx_nonneg : 0 ≤ a x := x.property
                simp [hx_nonneg]
              _ = ∑ n ∈ S, a n := by
                let f : S → {n : ℕ | 0 ≤ a n} := λ x' => ⟨x'.val, (Finset.mem_filter.mp x'.property).2⟩
                have hinj : Set.InjOn f (S.attach : Set S) := by
                  intro x hx y hy h
                  apply Subtype.ext
                  exact congrArg (fun (z : {n : ℕ | 0 ≤ a n}) => z.val) h
                calc
                  ∑ x ∈ A, a x = ∑ x ∈ image f S.attach, a x := rfl
                  _ = ∑ x ∈ S.attach, a (f x) := by rw [Finset.sum_image hinj]
                  _ = ∑ x ∈ S.attach, a x.val := rfl
                  _ = ∑ n ∈ S, a n := by
                    simpa using (Finset.sum_attach S a)
          have h_le_M : ∑ n ∈ S, a n ≤ M := by
            calc
              ∑ n ∈ S, a n = ∑ x ∈ A, |(fun (n : {n | a n ≥ 0}) ↦ a n) x| := by symm; exact h_A_sum
              _ ≤ M := by
                have hval : ∑ x ∈ A, |(fun (n : {n | a n ≥ 0}) ↦ a n) x| ≤ M := by
                  apply hM
                  refine ⟨A, Set.mem_univ A, rfl⟩
                exact hval
          exact h_le_M
        · have hN_lt : N < (0 : ℤ) := by omega
          have h_partial_zero : (a_plus : Series).partial N = 0 := by
            simp [Series.partial, Finset.Icc_eq_empty_of_lt hN_lt]
          have hM_nonneg : 0 ≤ M := by
            have h0 : (∑ x ∈ (∅ : Finset {n | a n ≥ 0}), |(fun (n : {n | a n ≥ 0}) ↦ a n) x|) ≤ M := by
              apply hM
              refine ⟨∅, Set.mem_univ ∅, rfl⟩
            simpa using h0
          simp [h_partial_zero, hM_nonneg]
      have ha_minus_conv : (a_minus : Series).converges := by
        have h_sub_conv : ((a_plus : Series) - (a : Series)).converges := (Series.sub ha_plus_conv ha).1
        have h_eq : (a_minus : Series) = (a_plus : Series) - (a : Series) := by
          apply Series.ext
          · calc
              (a_minus : Series).m = 0 := rfl
              _ = min (0 : ℤ) 0 := by simp
              _ = min ((a_plus : Series).m) ((a : Series).m) := rfl
              _ = ((a_plus : Series) - (a : Series)).m := rfl
          · ext n
            calc
              (a_minus : Series).seq n = max (-(a : Series).seq n) 0 := by
                by_cases hn : n ≥ (0 : ℤ)
                · simp [a_minus, hn]
                · simp [a_minus, hn]
              _ = max ((a_plus : Series).seq n) 0 - (a : Series).seq n := by
                by_cases hn : n ≥ (0 : ℤ)
                · have hnpos : (a : Series).seq n = a n.toNat := by simp [hn]
                  have h_plus_seq : (a_plus : Series).seq n = max (a n.toNat) 0 := by simp [a_plus, hn]
                  rw [hnpos, h_plus_seq]
                  have hmax : max (max (a n.toNat) 0) 0 = max (a n.toNat) 0 := by simp
                  rw [hmax]
                  have h := max_sub_max_eq (a n.toNat)
                  linarith
                · have hn_lt : n < (0 : ℤ) := lt_of_not_ge hn
                  have h_seq_a : (a : Series).seq n = 0 := (a : Series).vanish n hn_lt
                  have h_seq_plus : (a_plus : Series).seq n = 0 :=
                    (a_plus : Series).vanish n hn_lt
                  rw [h_seq_a, h_seq_plus]; simp
              _ = ((a_plus : Series) - (a : Series)).seq n := by
                by_cases hn : n ≥ (0 : ℤ)
                · have h_nonneg_plus_n : (a_plus : Series).seq n ≥ 0 := ha_nonneg_plus n
                  calc
                    max ((a_plus : Series).seq n) 0 - (a : Series).seq n
                        = (a_plus : Series).seq n - (a : Series).seq n := by
                          rw [max_eq_left h_nonneg_plus_n]
                    _ = ((a_plus : Series) - (a : Series)).seq n := by
                      simp [HSub.hSub, Sub.sub, hn]
                · have hn_lt : n < (0 : ℤ) := lt_of_not_ge hn
                  have h_seq_plus : (a_plus : Series).seq n = 0 :=
                    (a_plus : Series).vanish n hn_lt
                  have h_seq_a : (a : Series).seq n = 0 :=
                    (a : Series).vanish n hn_lt
                  have h_sub_val : ((a_plus : Series) - (a : Series)).seq n = 0 :=
                    ((a_plus : Series) - (a : Series)).vanish n (by
                      simp; exact hn_lt)
                  rw [h_sub_val, h_seq_plus, h_seq_a]; simp
        rw [h_eq]
        exact h_sub_conv
      exact h_not_both ⟨ha_plus_conv, ha_minus_conv⟩

  have h_not_abs_conv_minus : ¬ AbsConvergent (fun n : {n | a n < 0} ↦ a n) := by
    classical
    intro hpos
    by_cases hfinite : Finite {n | a n < 0}
    · rcases hpos with ⟨g, hg_bij, _⟩
      have h_infinite : Infinite {n | a n < 0} :=
        Infinite.of_injective g hg_bij.1
      exact hfinite.not_infinite h_infinite
    · haveI hinf : Infinite {n | a n < 0} := ⟨hfinite⟩
      have hcount : CountablyInfinite {n | a n < 0} :=
        Nat.countable_of_infinite (X := {n | a n < 0})
      have h_bdd := ((AbsConvergent.iff hcount (fun n : {n | a n < 0} ↦ a n)).mp hpos)
      rcases h_bdd with ⟨M, hM⟩
      have ha_minus_conv : (a_minus : Series).converges := by
        apply (Series.converges_of_nonneg_iff ha_nonneg_minus).mpr
        use M
        intro N
        by_cases hN : N ≥ (0 : ℤ)
        · have hN_nonneg : (0 : ℤ) ≤ N := hN
          have hN_val : ((Int.toNat N : ℕ) : ℤ) = N := by exact mod_cast Int.toNat_of_nonneg hN_nonneg
          have h_partial_eq : (a_minus : Series).partial (N : ℤ) = ∑ k ∈ ((Finset.range ((Int.toNat N : ℕ)+1 : ℕ)).filter (λ m : ℕ => a m < 0)), -a k := by
            calc
              (a_minus : Series).partial (N : ℤ) = (a_minus : Series).partial ((Int.toNat N : ℕ) : ℤ) := by rw [hN_val]
              _ = ∑ k ∈ Finset.range ((Int.toNat N : ℕ)+1), max (-(a k)) 0 := ha_minus_partial_range (Int.toNat N)
              _ = ∑ k ∈ Finset.range ((Int.toNat N : ℕ)+1), (if a k < 0 then -a k else 0) := by
                refine Finset.sum_congr rfl (λ m hm => ?_)
                by_cases hm_neg : a m < 0
                · have hneg' : -(a m) ≥ 0 := by linarith
                  simp [hm_neg, hneg']
                · have hm_nonneg : 0 ≤ a m := by linarith
                  simp [hm_neg, hm_nonneg]
              _ = ∑ k ∈ (Finset.range ((Int.toNat N : ℕ)+1 : ℕ)).filter (λ m : ℕ => a m < 0), -a k := by
                rw [← Finset.sum_filter]
          rw [h_partial_eq]
          let S := (Finset.range ((Int.toNat N : ℕ)+1 : ℕ)).filter (λ m : ℕ => a m < 0)
          let A : Finset {x : ℕ | a x < 0} :=
            S.attach.image (λ (x : S) => ⟨x.val, (Finset.mem_filter.mp x.property).2⟩)
          have h_A_sum : ∑ x ∈ A, |(fun (n : {n : ℕ | a n < 0}) ↦ a n) x| = ∑ n ∈ S, -a n := by
            calc
              ∑ x ∈ A, |(fun (n : {n : ℕ | a n < 0}) ↦ a n) x| = ∑ x ∈ A, -a x := by
                refine Finset.sum_congr rfl (λ x hx => ?_)
                have ha_neg_x : a x < 0 := x.property
                simp [abs_of_neg ha_neg_x]
              _ = ∑ n ∈ S, -a n := by
                let f : S → {n : ℕ | a n < 0} := λ x' => ⟨x'.val, (Finset.mem_filter.mp x'.property).2⟩
                have hinj : Set.InjOn f (S.attach : Set S) := by
                  intro x hx y hy h
                  apply Subtype.ext
                  exact congrArg (fun (z : {n : ℕ | a n < 0}) => z.val) h
                calc
                  ∑ x ∈ A, -a x = ∑ x ∈ image f S.attach, -a x := rfl
                  _ = ∑ x ∈ S.attach, -a (f x) := by rw [Finset.sum_image hinj]
                  _ = ∑ x ∈ S.attach, -a x.val := rfl
                  _ = ∑ n ∈ S, -a n := by
                    simpa using (Finset.sum_attach S (λ n : ℕ => -a n))
          have h_le_M : ∑ n ∈ S, -a n ≤ M := by
            calc
              ∑ n ∈ S, -a n = ∑ x ∈ A, |(fun (n : {n | a n < 0}) ↦ a n) x| := by symm; exact h_A_sum
              _ ≤ M := by
                apply hM
                refine ⟨A, Set.mem_univ A, rfl⟩
          exact h_le_M
        · have hN_lt : N < (0 : ℤ) := by omega
          have h_partial_zero : (a_minus : Series).partial N = 0 := by
            simp [Series.partial, Finset.Icc_eq_empty_of_lt hN_lt]
          have hM_nonneg : 0 ≤ M := by
            have h0 : (∑ x ∈ (∅ : Finset {n | a n < 0}), |(fun (n : {n | a n < 0}) ↦ a n) x|) ≤ M := by
              apply hM
              refine ⟨∅, Set.mem_univ ∅, rfl⟩
            simpa using h0
          simp [h_partial_zero, hM_nonneg]
      have ha_plus_conv : (a_plus : Series).converges := by
        have h_add_conv : ((a : Series) + (a_minus : Series)).converges := (Series.add ha ha_minus_conv).1
        have h_eq : (a_plus : Series) = (a : Series) + (a_minus : Series) := by
          apply Series.ext
          · calc
              (a_plus : Series).m = 0 := rfl
              _ = max (0 : ℤ) 0 := by simp
              _ = max ((a : Series).m) ((a_minus : Series).m) := rfl
              _ = ((a : Series) + (a_minus : Series)).m := rfl
          · ext n
            calc
              (a_plus : Series).seq n = max ((a : Series).seq n) 0 := by
                by_cases hn : n ≥ (0 : ℤ)
                · simp [a_plus, hn]
                · simp [a_plus, hn]
              _ = (a : Series).seq n + max (-(a : Series).seq n) 0 := by
                have h_eq' (x : ℝ) : max x 0 = x + max (-x) 0 := by
                  by_cases hx : 0 ≤ x
                  · simp [hx]
                  · have hx' : x ≤ 0 := by linarith
                    have hx_nonpos : -x ≥ 0 := by linarith
                    rw [max_eq_right hx', max_eq_left hx_nonpos]
                    ring
                rw [h_eq' ((a : Series).seq n)]
              _ = (a : Series).seq n + (a_minus : Series).seq n := by
                by_cases hn : n ≥ (0 : ℤ)
                · have hn_nonneg : (0 : ℤ) ≤ n := hn
                  simp [a_minus, hn_nonneg]
                · have hn_lt : n < (0 : ℤ) := lt_of_not_ge hn
                  have h_seq_a : (a : Series).seq n = 0 := (a : Series).vanish n hn_lt
                  have h_seq_minus : (a_minus : Series).seq n = 0 :=
                    (a_minus : Series).vanish n hn_lt
                  rw [h_seq_a, h_seq_minus]; simp
              _ = ((a : Series) + (a_minus : Series)).seq n := by
                by_cases hn : n ≥ (0 : ℤ)
                · simp [HAdd.hAdd, Add.add, hn]
                · simp [HAdd.hAdd, Add.add, hn]
        rw [h_eq]
        exact h_add_conv
      exact h_not_both ⟨ha_plus_conv, ha_minus_conv⟩

  exact ⟨h_not_abs_conv_plus, h_not_abs_conv_minus⟩

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
  have hA_plus_inf : Infinite A_plus := sorry
  have hA_minus_inf : Infinite A_minus := sorry
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
  have hn'_plus_inf (j:ℕ) : Infinite { n ∈ A_plus | ∀ i:Fin j, n ≠ n' i } := by sorry
  have hn'_minus_inf (j:ℕ) : Infinite { n ∈ A_minus | ∀ i:Fin j, n ≠ n' i } := by sorry
  have hn'_inj : Injective n' := by sorry
  have h_case_I : Infinite { j | ∑ i:Fin j, a (n' i) < L } := by sorry
  have h_case_II : Infinite { j | ∑ i:Fin j, a (n' i) ≥ L } := by sorry
  have hn'_surj : Surjective n' := by sorry
  have hconv : atTop.Tendsto (a ∘ n') (nhds 0) := by sorry
  have hsum : (a ∘ n':Series).convergesTo L := by sorry
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
