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

/-
If a series converges but not absolutely, the set of indices with nonnegative terms is
infinite.
-/
theorem nonneg_infinite {a:ℕ→ℝ} (ha: (a:Series).converges) (ha': ¬ (a:Series).absConverges) :
    Infinite {n | a n ≥ 0} := by
      refine' Set.infinite_coe_iff.mpr _;
      by_contra h_finite;
      obtain ⟨g, hg⟩ : ∃ g : ℕ → ℝ, g = (fun n => max (a n) 0) ∧ (g: Series).converges := by
        refine' ⟨ _, rfl, _ ⟩;
        obtain ⟨ N, hN ⟩ := Set.Finite.bddAbove ( Classical.not_not.mp h_finite );
        refine' ⟨ _, _ ⟩;
        exact ∑ n ∈ Finset.range ( N + 1 ), max ( a n ) 0;
        refine' Metric.tendsto_atTop.mpr _;
        intro ε hε; use N + 1; intro n hn; simp_all +decide [ Series.partial ] ;
        rw [ show ( Icc 0 n : Finset ℤ ) = Finset.image ( fun x : ℕ => x : ℕ → ℤ ) ( Finset.range ( n.toNat + 1 ) ) from ?_, Finset.sum_image ] <;> norm_num;
        · rw [ dist_eq_norm, Finset.sum_subset ( Finset.range_mono ( by linarith [ Int.toNat_of_nonneg ( by linarith : 0 ≤ n ) ] : N + 1 ≤ n.toNat + 1 ) ) ] <;> norm_num;
          · linarith;
          · exact fun x hx₁ hx₂ => not_lt.1 fun hx₃ => not_lt_of_ge ( hN hx₃.le ) hx₂;
        · ext ( _ | i ) <;> simp +decide [ Int.toNat_of_nonneg ];
          grind;
      obtain ⟨t, ht⟩ : ∃ t : ℕ → ℝ, t = (fun n => -a n + 2 * max (a n) 0) ∧ (t: Series).converges := by
        have := Series.add ( show ( fun n => -a n : Series ).converges from ?_ ) ( show ( fun n => 2 * g n : Series ).converges from ?_ );
        · simp_all +decide [ Series.add ];
          convert this.1 using 1;
          congr with n ; aesop;
        · obtain ⟨ L, hL ⟩ := ha;
          use -L;
          convert hL.neg using 1;
          ext; simp [Series.partial];
          rw [ ← Finset.sum_neg_distrib ] ; congr ; ext ; split_ifs <;> ring;
        · obtain ⟨ l, hl ⟩ := hg.2;
          use 2 * l;
          convert hl.const_mul 2 using 1;
          ext; simp [Series.partial];
          rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_congr rfl fun _ _ => by split_ifs <;> ring;
      refine' ha' _;
      have := Series.converges_of_le ( show ( { m := 0, seq := fun n => if n ≥ 0 then a n.toNat else 0, vanish := by aesop } : Series ).m = ( { m := 0, seq := fun n => if n ≥ 0 then t n.toNat else 0, vanish := by aesop } : Series ).m from rfl ) ( fun n hn => ?_ ) ht.2;
      · exact this.1;
      · grind +qlia

/-
If a series converges but not absolutely, the set of indices with negative terms is
infinite.
-/
theorem neg_infinite {a:ℕ→ℝ} (ha: (a:Series).converges) (ha': ¬ (a:Series).absConverges) :
    Infinite {n | a n < 0} := by
      contrapose! ha';
      have h_abs_conv : ∃ M, ∀ N, ∑ n ∈ Finset.Icc 0 N, |a n| ≤ M := by
        obtain ⟨M, hM⟩ : ∃ M, ∀ N, ∑ n ∈ Finset.Icc 0 N, max (-a n) 0 ≤ M := by
          have h_finite_neg : Set.Finite {n | a n < 0} := by
            exact Set.finite_coe_iff.mp ha';
          use ∑ n ∈ h_finite_neg.toFinset, |a n|;
          intro N;
          refine' le_trans _ ( Finset.sum_le_sum_of_subset_of_nonneg ( show Finset.filter ( fun n => a n < 0 ) ( Finset.Icc 0 N ) ⊆ h_finite_neg.toFinset from fun x hx => by aesop ) fun _ _ _ => abs_nonneg _ );
          rw [ Finset.sum_filter ] ; exact Finset.sum_le_sum fun i hi => by split_ifs <;> cases abs_cases ( a i ) <;> cases max_cases ( -a i ) 0 <;> linarith;
        have h_abs_conv : ∃ M, ∀ N, ∑ n ∈ Finset.Icc 0 N, a n ≤ M := by
          obtain ⟨ M, hM ⟩ := ha;
          obtain ⟨ N, hN ⟩ := Metric.tendsto_atTop.mp hM 1 zero_lt_one;
          use Max.max ( ∑ n ∈ Finset.Icc 0 ( Int.toNat N ), |a n| ) ( M + 1 );
          intro n; by_cases hn : n ≤ Int.toNat N <;> simp_all +decide [ dist_eq_norm ] ;
          · exact Or.inl ( le_trans ( Finset.sum_le_sum fun _ _ => le_abs_self _ ) ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.Icc_subset_Icc_right hn ) fun _ _ _ => abs_nonneg _ ) );
          · have := hN n ( by linarith [ Int.self_le_toNat N ] ) ; simp_all +decide [ abs_lt, Series.partial ] ;
            exact Or.inr ( by linarith );
        obtain ⟨ M', hM' ⟩ := h_abs_conv;
        use M' + 2 * M;
        intro N; specialize hM N; specialize hM' N; simp_all +decide [ Finset.sum_add_distrib, two_mul, abs_of_nonneg ] ;
        exact le_trans ( Finset.sum_le_sum fun i hi => show |a i| ≤ a i + 2 * max ( -a i ) 0 by cases max_cases ( -a i ) 0 <;> cases abs_cases ( a i ) <;> linarith ) ( by simpa [ Finset.sum_add_distrib, two_mul, Finset.mul_sum _ _ _ ] using add_le_add hM' ( add_le_add hM hM ) );
      convert Chapter7.Series.converges_of_nonneg_iff _ |>.2 ⟨ h_abs_conv.choose, fun N => ?_ ⟩;
      · intro n; aesop;
      · by_cases hN : 0 ≤ N;
        · convert h_abs_conv.choose_spec ( Int.toNat N ) using 1;
          convert Chapter7.partial_abs_eq_range ( fun n => |a n| ) ( Int.toNat N ) using 1;
          · grind;
          · rw [ Finset.range_eq_Ico ] ; norm_num [ abs_of_nonneg ];
            rcongr n ; aesop;
        · convert le_trans _ ( h_abs_conv.choose_spec 0 ) using 1;
          unfold Chapter7.Series.partial; aesop;

open Classical in
/-- The recursion functional driving the Riemann rearrangement construction:
given the indices `n'` already chosen for steps `< j`, pick the least not-yet-used index
from the nonnegative-term set when the current partial sum is `< L`, and from the
negative-term set otherwise. -/
noncomputable def rrF (a : ℕ → ℝ) (L : ℝ) : (n : ℕ) → ((m : ℕ) → m < n → ℕ) → ℕ :=
  fun j n' ↦ if ∑ i:Fin j, a (n' i (by simp)) < L then
      Nat.min { n ∈ {n | a n ≥ 0} | ∀ i:Fin j, n ≠ n' i (by simp) }
    else
      Nat.min { n ∈ {n | a n < 0} | ∀ i:Fin j, n ≠ n' i (by simp) }

/-- The Riemann rearrangement permutation associated to `a` and target value `L`. -/
noncomputable def rr (a : ℕ → ℝ) (L : ℝ) : ℕ → ℕ := Nat.strongRec (rrF a L)

/-- Unfolding equation for the Riemann rearrangement permutation. -/
theorem rr_eq (a : ℕ → ℝ) (L : ℝ) (j:ℕ) :
    rr a L j = if ∑ i:Fin j, a (rr a L i) < L then
      Nat.min { n ∈ {n | a n ≥ 0} | ∀ i:Fin j, n ≠ rr a L i }
    else
      Nat.min { n ∈ {n | a n < 0} | ∀ i:Fin j, n ≠ rr a L i }
  := Nat.strongRec.eq_def _ j

/-
At each step, the candidate nonnegative indices not yet chosen form an infinite set.
-/
theorem rr_plus_inf (a : ℕ → ℝ) (L : ℝ) [Infinite {n | a n ≥ 0}] (j:ℕ) :
    Infinite { n ∈ {n | a n ≥ 0} | ∀ i:Fin j, n ≠ rr a L i } := by
      refine Set.infinite_coe_iff.mpr ?_;
      convert Set.Infinite.diff ( Set.infinite_coe_iff.mp ‹_› ) ( Set.toFinite ( Set.range fun i : Fin j => rr a L i ) ) using 1;
      grind

/-
At each step, the candidate negative indices not yet chosen form an infinite set.
-/
theorem rr_minus_inf (a : ℕ → ℝ) (L : ℝ) [Infinite {n | a n < 0}] (j:ℕ) :
    Infinite { n ∈ {n | a n < 0} | ∀ i:Fin j, n ≠ rr a L i } := by
      refine Set.infinite_coe_iff.mpr ?_;
      convert Set.Infinite.diff ( Set.infinite_coe_iff.mp ‹_› ) ( Set.toFinite ( Set.range fun i : Fin j => rr a L i ) ) using 1;
      grind

/-
The Riemann rearrangement permutation is injective.
-/
theorem rr_inj (a : ℕ → ℝ) (L : ℝ) [Infinite {n | a n ≥ 0}] [Infinite {n | a n < 0}] :
    Injective (rr a L) := by
      -- For every `j` and every `i : Fin j`, `rr a L j ≠ rr a L i`.
      have h_ne (j : ℕ) (i : Fin j) : rr a L j ≠ rr a L i := by
        rw [ rr_eq ];
        split_ifs;
        · have := Nat.min_spec ( show { n | n ∈ { n | a n ≥ 0 } ∧ ∀ i : Fin j, n ≠ rr a L i }.Nonempty from ?_ );
          · exact this.1.2 i;
          · convert Set.Infinite.nonempty ( Set.infinite_coe_iff.mp ( rr_plus_inf a L j ) ) using 1;
        · have := Nat.min_spec ( show { n ∈ { n | a n < 0 } | ∀ i : Fin j, n ≠ rr a L i }.Nonempty from ?_ ) ; aesop;
          convert Set.Infinite.nonempty ( Set.infinite_coe_iff.mp ( rr_minus_inf a L j ) ) using 1;
      intro j₁ j₂ h; rcases lt_trichotomy j₁ j₂ with ( H | rfl | H ) <;> simp_all +decide [ Function.Injective ] ;
      · exact False.elim <| h_ne j₂ ⟨ j₁, H ⟩ h.symm;
      · exact False.elim <| h_ne j₁ ⟨ j₂, H ⟩ h

/-
The positive part of a conditionally convergent series diverges.
-/
theorem pos_series_diverges {a:ℕ→ℝ} (ha: (a:Series).converges) (ha': ¬ (a:Series).absConverges) :
    ¬ ((fun n ↦ max (a n) 0):Series).converges := by
      contrapose! ha';
      -- The series `((fun n ↦ max (-(a n)) 0):Series)` converges. Indeed it converges because it is the difference of the (assumed) convergent series `((fun n ↦ max (a n) 0):Series)` and `(a:Series)`: by `Series.sub` the difference converges, and pointwise `max (a n) 0 - a n = max (-(a n)) 0` (case split on `0 ≤ a n`). Use `Series.ext` (both series have `m = 0`, and `seq` agree for `n ≥ 0` by `Series.eval_coe`) to identify the difference series with `((fun n ↦ max (-(a n)) 0):Series)`.
      have h_neg_converge : ((fun n ↦ max (-(a n)) 0):Series).converges := by
        convert ( Series.sub ha' ha ).left using 1;
        congr with n ; by_cases hn : 0 ≤ n <;> simp +decide [ hn ];
        cases max_cases ( -a n.toNat ) 0 <;> cases max_cases ( a n.toNat ) 0 <;> linarith;
      obtain ⟨ L₁, hL₁ ⟩ := ha
      obtain ⟨ L₂, hL₂ ⟩ := ha'
      obtain ⟨ L₃, hL₃ ⟩ := h_neg_converge
      use L₂ + L₃;
      convert Metric.tendsto_atTop.mpr _ using 1;
      · exact ⟨ 0 ⟩;
      · intro ε hε; obtain ⟨ N₁, hN₁ ⟩ := Metric.tendsto_atTop.mp hL₂ ( ε / 2 ) ( half_pos hε ) ; obtain ⟨ N₂, hN₂ ⟩ := Metric.tendsto_atTop.mp hL₃ ( ε / 2 ) ( half_pos hε ) ; use Max.max N₁ N₂; intro n hn; simp_all +decide [ dist_eq_norm, Series.partial ] ;
        rw [ show ( ∑ x ∈ Icc 0 n, if 0 ≤ x then |a x.toNat| else 0 ) = ( ∑ x ∈ Icc 0 n, if 0 ≤ x then max ( a x.toNat ) 0 else 0 ) + ( ∑ x ∈ Icc 0 n, if 0 ≤ x then max ( -a x.toNat ) 0 else 0 ) from ?_ ];
        · grind +qlia;
        · rw [ ← Finset.sum_add_distrib ] ; congr ; ext x ; split_ifs <;> cases max_cases ( a x.toNat ) 0 <;> cases max_cases ( -a x.toNat ) 0 <;> cases abs_cases ( a x.toNat ) <;> linarith;

/-
The negative part of a conditionally convergent series diverges.
-/
theorem neg_series_diverges {a:ℕ→ℝ} (ha: (a:Series).converges) (ha': ¬ (a:Series).absConverges) :
    ¬ ((fun n ↦ max (-(a n)) 0):Series).converges := by
      contrapose! ha';
      -- By definition of `Series.absConverges`, we need to show that the series `((fun n ↦ max (a n) 0):Series)` converges.
      have h_pos_conv : ((fun n ↦ max (a n) 0):Series).converges := by
        obtain ⟨ L₁, hL₁ ⟩ := ha
        obtain ⟨ L₂, hL₂ ⟩ := ha';
        use L₁ + L₂;
        convert hL₁.add hL₂ using 1;
        congr with n ; by_cases hn : 0 ≤ n <;> simp +decide [ hn ];
        cases max_cases ( a n.toNat ) 0 <;> cases max_cases ( -a n.toNat ) 0 <;> linarith;
      have h_abs_conv : ((fun n ↦ max (a n) 0 + max (-(a n)) 0):Series).converges := by
        convert Series.add h_pos_conv ha' |>.1 using 1;
        congr with n ; aesop;
      obtain ⟨ L, hL ⟩ := h_abs_conv;
      refine' ⟨ L, _ ⟩;
      grind +revert

/-
Finite subsets of the nonnegative-term indices, disjoint from any given finite set,
have arbitrarily large sums.
-/
theorem pos_unbounded {a:ℕ→ℝ} (ha: (a:Series).converges) (ha': ¬ (a:Series).absConverges)
    (U : Finset ℕ) (M:ℝ) :
    ∃ F : Finset ℕ, (↑F ⊆ {n | a n ≥ 0}) ∧ Disjoint F U ∧ M < ∑ n ∈ F, a n := by
      have h_pos_div : ¬ ((fun n ↦ max (a n) 0):Series).converges := by
        convert pos_series_diverges ha ha' using 1;
      -- By `Series.converges_of_nonneg_iff`, since `(g:Series).nonneg` (each `max (a n) 0 ≥ 0`, check via `Series.eval_coe`/coe `seq`),
      -- it is NOT the case that `∃ B, ∀ N, (g:Series).partial N ≤ B`. Hence for every bound `B` there exists `N` with `B < (g:Series).partial N`.
      obtain ⟨N, hN⟩ : ∃ N : ℕ, M + ∑ n ∈ U, max (a n) 0 < ∑ n ∈ Finset.range (N + 1), max (a n) 0 := by
        contrapose! h_pos_div;
        convert Chapter7.Series.converges_of_nonneg_iff _ |>.2 ⟨ M + ∑ n ∈ U, max ( a n ) 0, fun N => ?_ ⟩ using 1;
        · intro n; aesop;
        · by_cases hN : N < 0 <;> simp_all +decide [ Chapter7.Series.partial ];
          · exact le_trans ( Finset.sum_nonneg fun _ _ => le_max_right _ _ ) ( h_pos_div 0 );
          · convert h_pos_div ( Int.toNat N ) using 1;
            refine' Finset.sum_bij ( fun x hx => Int.toNat x ) _ _ _ _ <;> simp_all +decide [ Int.toNat_of_nonneg ];
            · grind;
            · exact fun n hn => ⟨ n, ⟨ Nat.cast_nonneg _, hn ⟩, rfl ⟩;
      refine' ⟨ Finset.filter ( fun n => 0 ≤ a n ) ( Finset.range ( N + 1 ) ) \ U, _, _, _ ⟩ <;> simp_all +decide [ Finset.disjoint_left ];
      · exact fun x hx => hx.1.2;
      · have h_sum_filter : ∑ n ∈ Finset.filter (fun n => 0 ≤ a n) (Finset.range (N + 1)) \ U, a n = ∑ n ∈ Finset.filter (fun n => 0 ≤ a n) (Finset.range (N + 1)), max (a n) 0 - ∑ n ∈ Finset.filter (fun n => 0 ≤ a n) (Finset.range (N + 1)) ∩ U, max (a n) 0 := by
          rw [ ← Finset.sum_sdiff ( show { n ∈ range ( N + 1 ) | 0 ≤ a n } ∩ U ⊆ { n ∈ range ( N + 1 ) | 0 ≤ a n } from Finset.inter_subset_left ) ];
          simp +decide [ Finset.sdiff_inter_self_left ];
          exact Finset.sum_congr rfl fun x hx => by rw [ max_eq_left ( Finset.mem_filter.mp ( Finset.mem_sdiff.mp hx |>.1 ) |>.2 ) ] ;
        have h_sum_filter : ∑ n ∈ Finset.filter (fun n => 0 ≤ a n) (Finset.range (N + 1)) ∩ U, max (a n) 0 ≤ ∑ n ∈ U, max (a n) 0 := by
          exact Finset.sum_le_sum_of_subset_of_nonneg ( Finset.inter_subset_right ) fun _ _ _ => le_max_right _ _;
        rw [ Finset.sum_filter ] at *;
        grind +locals

/-
Finite subsets of the negative-term indices, disjoint from any given finite set,
have arbitrarily small (negative) sums.
-/
theorem neg_unbounded {a:ℕ→ℝ} (ha: (a:Series).converges) (ha': ¬ (a:Series).absConverges)
    (U : Finset ℕ) (M:ℝ) :
    ∃ F : Finset ℕ, (↑F ⊆ {n | a n < 0}) ∧ Disjoint F U ∧ ∑ n ∈ F, a n < M := by
      obtain ⟨N, hN⟩ : ∃ N : ℕ, -M + ∑ n ∈ U, max (-(a n)) 0 < ∑ n ∈ Finset.range (N + 1), max (-(a n)) 0 := by
        have h_neg_div : ¬ ((fun n ↦ max (-(a n)) 0):Series).converges := by
          convert neg_series_diverges ha ha' using 1;
        contrapose! h_neg_div;
        convert Chapter7.Series.converges_of_nonneg_iff _ |>.2 ⟨ -M + ∑ n ∈ U, max ( -a n ) 0, fun N => ?_ ⟩ using 1;
        · grind;
        · by_cases hN : N < 0 <;> simp_all +decide [ Chapter7.Series.partial ];
          · exact le_trans ( le_add_of_nonneg_right <| Finset.sum_nonneg fun _ _ => le_max_right _ _ ) ( h_neg_div 0 );
          · convert h_neg_div ( Int.toNat N ) using 1;
            refine' congr rfl ( Finset.sum_bij ( fun x hx => Int.toNat x ) _ _ _ _ ) <;> simp +decide [ Int.toNat_of_nonneg ];
            · exact fun _ _ _ => Or.inl ‹_›;
            · grind;
            · exact fun b hb => ⟨ b, ⟨ Nat.cast_nonneg _, by linarith [ Int.toNat_of_nonneg hN ] ⟩, rfl ⟩;
            · grind;
      refine' ⟨ Finset.filter ( fun n => a n < 0 ) ( Finset.range ( N + 1 ) ) \ U, _, _, _ ⟩ <;> norm_num [ Finset.subset_iff ];
      · exact fun x hx => hx.1.2;
      · exact Finset.sdiff_disjoint;
      · have h_sum_filter : ∑ n ∈ Finset.filter (fun n => a n < 0) (Finset.range (N + 1)) \ U, a n = -∑ n ∈ Finset.filter (fun n => a n < 0) (Finset.range (N + 1)), max (-(a n)) 0 + ∑ n ∈ Finset.filter (fun n => a n < 0) (Finset.range (N + 1)) ∩ U, max (-(a n)) 0 := by
          rw [ ← Finset.sum_sdiff <| show { n ∈ range ( N + 1 ) | a n < 0 } ∩ U ⊆ { n ∈ range ( N + 1 ) | a n < 0 } from Finset.inter_subset_left ];
          simp +decide [ Finset.sdiff_inter_self_left ];
          rw [ ← Finset.sum_neg_distrib ] ; exact Finset.sum_congr rfl fun x hx => by rw [ max_eq_left ( by linarith [ Finset.mem_filter.mp ( Finset.mem_sdiff.mp hx |>.1 ) |>.2 ] ) ] ; ring;
        have h_sum_filter : ∑ n ∈ Finset.filter (fun n => a n < 0) (Finset.range (N + 1)), max (-(a n)) 0 = ∑ n ∈ Finset.range (N + 1), max (-(a n)) 0 := by
          rw [ Finset.sum_filter_of_ne ] ; aesop;
        linarith [ show ∑ n ∈ Finset.filter ( fun n => a n < 0 ) ( Finset.range ( N + 1 ) ) ∩ U, max ( -a n ) 0 ≤ ∑ n ∈ U, max ( -a n ) 0 from Finset.sum_le_sum_of_subset_of_nonneg ( Finset.inter_subset_right ) fun _ _ _ => le_max_right _ _ ]

/-
At a step where the partial sum is `< L`, the chosen index is a nonnegative-term index,
and it is the least available such index.
-/
theorem rr_pick_pos (a : ℕ → ℝ) (L : ℝ) [Infinite {n | a n ≥ 0}] (j:ℕ)
    (h: ∑ i:Fin j, a (rr a L i) < L) :
    0 ≤ a (rr a L j) ∧ ∀ x, 0 ≤ a x → (∀ i:Fin j, x ≠ rr a L i) → rr a L j ≤ x := by
      rw [ rr_eq];
      split_ifs;
      have := Nat.min_spec ( show { n | n ∈ { n | a n ≥ 0 } ∧ ∀ i : Fin j, n ≠ rr a L i }.Nonempty from ?_ );
      · exact ⟨ this.1.1, fun x hx hx' => this.2 x ⟨ hx, hx' ⟩ ⟩;
      · convert Set.Infinite.nonempty ( Set.infinite_coe_iff.mp ( rr_plus_inf a L j ) ) using 1

/-
At a step where the partial sum is `≥ L`, the chosen index is a negative-term index,
and it is the least available such index.
-/
theorem rr_pick_neg (a : ℕ → ℝ) (L : ℝ) [Infinite {n | a n < 0}] (j:ℕ)
    (h: ¬ (∑ i:Fin j, a (rr a L i) < L)) :
    a (rr a L j) < 0 ∧ ∀ x, a x < 0 → (∀ i:Fin j, x ≠ rr a L i) → rr a L j ≤ x := by
      rw [ rr_eq];
      convert Set.Infinite.nonempty ( Set.infinite_coe_iff.mp ( rr_minus_inf a L j ) ) using 1;
      constructor;
      · exact fun h => Set.infinite_coe_iff.mp ( rr_minus_inf a L j ) |> Set.Infinite.nonempty;
      · grind

/-
If from step `J` on the partial sum stays `< L` (so only nonnegative-term indices are chosen),
then every nonnegative-term index is eventually chosen.
-/
theorem rr_exhaust_pos (a : ℕ → ℝ) (L : ℝ) [Infinite {n | a n ≥ 0}] (J:ℕ)
    (hJ : ∀ j, J ≤ j → ∑ i:Fin j, a (rr a L i) < L) :
    ∀ x, 0 ≤ a x → ∃ j, rr a L j = x := by
      intro x hx
      by_contra h_contra;
      have h_bound : ∀ j ≥ J, rr a L j ≤ x := by
        intros j hj
        have h_le : rr a L j ≤ x := by
          have := rr_pick_pos a L j (hJ j hj)
          exact this.2 x hx fun i => fun hi => h_contra ⟨ i, hi.symm ⟩
        exact h_le;
      have h_inj : Set.InjOn (rr a L) (Set.Ici J) := by
        intros j hj k hk h_eq
        have h_ne : ∀ j₁ j₂, j₁ < j₂ → j₁ ≥ J → j₂ ≥ J → rr a L j₂ ≠ rr a L j₁ := by
          intros j₁ j₂ hj₁₂ hj₁ hj₂
          have h_ne : rr a L j₂ ≠ rr a L j₁ := by
            have h_pick : rr a L j₂ = Nat.min { n ∈ { n | a n ≥ 0 } | ∀ i : Fin j₂, n ≠ rr a L i } := by
              rw [ rr_eq ] ; aesop
            have := Nat.min_spec ( show { n | n ∈ { n | a n ≥ 0 } ∧ ∀ i : Fin j₂, n ≠ rr a L i }.Nonempty from ?_ );
            · exact h_pick.symm ▸ this.1.2 ⟨ j₁, by linarith ⟩;
            · convert Set.Infinite.nonempty ( Set.infinite_coe_iff.mp ( rr_plus_inf a L j₂ ) ) using 1;
          exact h_ne;
        grind +qlia;
      exact absurd ( Set.Infinite.image ( show Set.InjOn ( rr a L ) ( Set.Ici J ) from h_inj ) ( Set.Ici_infinite J ) ) ( Set.not_infinite.mpr <| Set.finite_iff_bddAbove.mpr ⟨ x, fun y hy => by aesop ⟩ )

/-
If from step `J` on the partial sum stays `≥ L` (so only negative-term indices are chosen),
then every negative-term index is eventually chosen.
-/
theorem rr_exhaust_neg (a : ℕ → ℝ) (L : ℝ) [Infinite {n | a n < 0}] (J:ℕ)
    (hJ : ∀ j, J ≤ j → L ≤ ∑ i:Fin j, a (rr a L i)) :
    ∀ x, a x < 0 → ∃ j, rr a L j = x := by
      intro x hx_neg
      by_contra h_contra
      push_neg at h_contra
      have h_le : ∀ j ≥ J, rr a L j ≤ x := by
        intros j hj
        have h_le : rr a L j ≤ x := by
          have := rr_pick_neg a L j (by
          exact not_lt_of_ge ( hJ j hj ))
          exact this.2 x hx_neg (fun i => fun hi => h_contra i hi.symm)
        exact h_le;
      have h_inj : Set.InjOn (rr a L) (Set.Ici J) := by
        intros j hj k hk h_eq
        have h_ne : ∀ j₁ j₂, j₁ < j₂ → j₁ ≥ J → j₂ ≥ J → rr a L j₂ ≠ rr a L j₁ := by
          intros j₁ j₂ hj₁₂ hj₁ hj₂
          have h_pick : rr a L j₂ = Nat.min { n ∈ { n | a n < 0 } | ∀ i : Fin j₂, n ≠ rr a L i } := by
            rw [ rr_eq ] ; aesop;
          have := Nat.min_spec ( show { n | n ∈ { n | a n < 0 } ∧ ∀ i : Fin j₂, n ≠ rr a L i }.Nonempty from ?_ );
          · exact h_pick.symm ▸ this.1.2 ⟨ j₁, by linarith ⟩;
          · convert Set.Infinite.nonempty ( Set.infinite_coe_iff.mp ( rr_minus_inf a L j₂ ) ) using 1
        grind;
      exact absurd ( Set.Infinite.image ( show Set.InjOn ( rr a L ) ( Set.Ici J ) from h_inj ) ( Set.Ici_infinite J ) ) ( Set.not_infinite.mpr <| Set.finite_iff_bddAbove.mpr ⟨ x, fun y hy => by aesop ⟩ )

/-
The partial sum drops below `L` infinitely often.
-/
theorem rr_case_I (a : ℕ → ℝ) (L : ℝ) (ha: (a:Series).converges)
    (ha': ¬ (a:Series).absConverges) :
    Infinite { j | ∑ i:Fin j, a (rr a L i) < L } := by
      -- Assume for contradiction that there exists $J$ such that $\forall j \geq J, L \leq \sum_{i=0}^{j-1} a_{\text{rr}(a, L, i)}$.
      by_contra h_contra
      obtain ⟨J, hJ⟩ : ∃ J, ∀ j ≥ J, L ≤ ∑ i : Fin j, a (rr a L i) := by
        simp +zetaDelta at *;
        exact Set.finite_iff_bddAbove.mp ( Set.finite_coe_iff.mp h_contra ) |> fun ⟨ J, hJ ⟩ => ⟨ J + 1, fun j hj => not_lt.1 fun contra => not_lt_of_ge ( hJ contra ) hj ⟩;
      haveI := nonneg_infinite ha ha'; haveI := neg_infinite ha ha';
      obtain ⟨ F, hF₁, hF₂, hF₃ ⟩ := neg_unbounded ha ha' ( Finset.image ( rr a L ) ( Finset.range J ) ) ( L - ∑ i : Fin J, a ( rr a L i ) );
      obtain ⟨ K, hK ⟩ : ∃ K ≥ J, ∀ x ∈ F, ∃ i ∈ Finset.Ico J K, rr a L i = x := by
        obtain ⟨ K, hK ⟩ : ∃ K ≥ J, ∀ x ∈ F, ∃ i < K, rr a L i = x := by
          have hK : ∀ x ∈ F, ∃ i, rr a L i = x := by
            exact fun x hx => rr_exhaust_neg a L J hJ x ( hF₁ hx );
          choose! f hf using hK;
          exact ⟨ Finset.sup F f + J + 1, by linarith, fun x hx => ⟨ f x, by linarith [ Finset.le_sup ( f := f ) hx ], hf x hx ⟩ ⟩;
        use K; simp_all +decide [ Finset.disjoint_left ] ;
        exact fun x hx => by obtain ⟨ i, hi, hi' ⟩ := hK.2 x hx; exact ⟨ i, ⟨ le_of_not_gt fun hi'' => hF₂ hx i hi'' hi', hi ⟩, hi' ⟩ ;
      have h_sum_le : ∑ n ∈ Finset.image (rr a L) (Finset.Ico J K), a n ≤ ∑ n ∈ F, a n := by
        have h_sum_le : ∑ n ∈ Finset.image (rr a L) (Finset.Ico J K), -a n ≥ ∑ n ∈ F, -a n := by
          apply Finset.sum_le_sum_of_subset_of_nonneg;
          · exact fun x hx => by obtain ⟨ i, hi, rfl ⟩ := hK.2 x hx; exact Finset.mem_image_of_mem _ hi;
          · grind +suggestions;
        aesop;
      rw [ Finset.sum_image ] at h_sum_le;
      · have := hJ K hK.1;
        rw [ Finset.sum_Ico_eq_sub _ hK.1 ] at h_sum_le;
        linarith! [ show ∑ i : Fin K, a ( rr a L i ) = ∑ i ∈ Finset.range K, a ( rr a L i ) from by rw [ Finset.sum_range ], show ∑ i : Fin J, a ( rr a L i ) = ∑ i ∈ Finset.range J, a ( rr a L i ) from by rw [ Finset.sum_range ] ];
      · exact fun x hx y hy hxy => by have := rr_inj a L; exact this hxy;

/-
The partial sum is at least `L` infinitely often.
-/
theorem rr_case_II (a : ℕ → ℝ) (L : ℝ) (ha: (a:Series).converges)
    (ha': ¬ (a:Series).absConverges) :
    Infinite { j | ∑ i:Fin j, a (rr a L i) ≥ L } := by
      by_contra h;
      -- By assumption `{ j | L ≤ S j }` is finite. By `Set.Finite.bddAbove`, it is bounded above.
      obtain ⟨J, hJ⟩ : ∃ J : ℕ, ∀ j ≥ J, ¬(∑ i : Fin j, a (rr a L i)) ≥ L := by
        simp +zetaDelta at *;
        exact Set.Finite.bddAbove ( Set.finite_coe_iff.mp h ) |> fun ⟨ J, hJ ⟩ => ⟨ J + 1, fun j hj => lt_of_not_ge fun h' => not_lt_of_ge ( hJ h' ) hj ⟩;
      have h_pos_inf : Infinite {n | a n ≥ 0} := by
        convert nonneg_infinite ha ha' using 1
      have h_neg_inf : Infinite {n | a n < 0} := by
        convert neg_infinite ha ha' using 1;
      obtain ⟨ F, hF₁, hF₂, hF₃ ⟩ := pos_unbounded ha ha' ( Finset.image ( rr a L ) ( Finset.range J ) ) ( L - ∑ i : Fin J, a ( rr a L i ) );
      obtain ⟨ K, hK ⟩ : ∃ K : ℕ, ∀ x ∈ F, ∃ k ∈ Finset.Ico J K, rr a L k = x := by
        have hK : ∀ x ∈ F, ∃ k ≥ J, rr a L k = x := by
          intros x hx
          obtain ⟨ k, hk ⟩ := rr_exhaust_pos a L J (fun j hj => by
            exact lt_of_not_ge ( hJ j hj )) x (hF₁ hx);
          exact ⟨ k, le_of_not_gt fun hk' => Finset.disjoint_left.mp hF₂ hx <| hk ▸ Finset.mem_image.mpr ⟨ k, Finset.mem_range.mpr hk', rfl ⟩, hk ⟩;
        choose! k hk₁ hk₂ using hK;
        exact ⟨ Finset.sup F k + 1, fun x hx => ⟨ k x, Finset.mem_Ico.mpr ⟨ hk₁ x hx, Nat.lt_succ_of_le ( Finset.le_sup ( f := k ) hx ) ⟩, hk₂ x hx ⟩ ⟩;
      have h_sum_le : ∑ n ∈ F, a n ≤ ∑ n ∈ Finset.image (rr a L) (Finset.Ico J K), a n := by
        apply Finset.sum_le_sum_of_subset_of_nonneg;
        · exact fun x hx => by obtain ⟨ k, hk₁, hk₂ ⟩ := hK x hx; exact hk₂ ▸ Finset.mem_image_of_mem _ hk₁;
        · intros i hi hni;
          obtain ⟨ k, hk₁, rfl ⟩ := Finset.mem_image.mp hi;
          exact rr_pick_pos a L k ( not_le.mp ( hJ k ( Finset.mem_Ico.mp hk₁ |>.1 ) ) ) |>.1;
      have h_sum_eq : ∑ n ∈ Finset.image (rr a L) (Finset.Ico J K), a n = ∑ i ∈ Finset.Ico J K, a (rr a L i) := by
        apply Finset.sum_image;
        exact fun x hx y hy hxy => by have := rr_inj a L; have := @this x y; aesop;
      have h_sum_eq : ∑ i ∈ Finset.Ico J K, a (rr a L i) = ∑ i : Fin K, a (rr a L i) - ∑ i : Fin J, a (rr a L i) := by
        cases le_total J K <;> simp_all +decide [ Finset.sum_Ico_eq_sub _ ];
        · simp +decide [ Finset.sum_range, Fin.sum_univ_castSucc ];
        · linarith [ hJ J le_rfl ];
      linarith [ hJ K ( by
        by_cases hF_empty : F = ∅;
        · grind +splitImp;
        · obtain ⟨ x, hx ⟩ := Finset.nonempty_of_ne_empty hF_empty; obtain ⟨ k, hk₁, hk₂ ⟩ := hK x hx; linarith [ Finset.mem_Ico.mp hk₁ ] ; ) ]

/-
The Riemann rearrangement permutation is surjective.
-/
theorem rr_surj (a : ℕ → ℝ) (L : ℝ) (ha: (a:Series).converges)
    (ha': ¬ (a:Series).absConverges) :
    Surjective (rr a L) := by
      have h_nonneg_infinite : Infinite {n | a n ≥ 0} := by
        convert nonneg_infinite ha ha' using 1
      have h_neg_infinite : Infinite {n | a n < 0} := by
        convert neg_infinite _ _;
        · exact ha;
        · convert ha' using 1;
      intro x
      by_contra h_contra
      push_neg at h_contra;
      by_cases hx : 0 ≤ a x;
      · have := rr_case_I a L ha ha';
        have h_image : Set.Infinite (Set.image (rr a L) {j | ∑ i : Fin j, a (rr a L i) < L}) := by
          exact Set.Infinite.image ( fun j => by have := rr_inj a L; aesop ) ( Set.infinite_coe_iff.mp this );
        exact h_image ( Set.Finite.subset ( Set.finite_le_nat x ) <| Set.image_subset_iff.mpr fun j hj => by have := rr_pick_pos a L j hj; exact this.2 x hx fun i => fun hi => h_contra i hi.symm );
      · have := rr_case_II a L ha ha';
        have h_image : Set.Infinite (Set.image (rr a L) {j | ∑ i : Fin j, a (rr a L i) ≥ L}) := by
          exact Set.Infinite.image ( fun j => by have := rr_inj a L; aesop ) ( Set.infinite_coe_iff.mp this );
        exact h_image ( Set.finite_iff_bddAbove.mpr ⟨ x, by rintro y ⟨ j, hj, rfl ⟩ ; exact Nat.le_of_not_lt fun h => by have := rr_pick_neg a L j ( by aesop ) ; exact not_lt_of_ge ( this.2 x ( by aesop ) ( fun i hi => h_contra _ hi.symm ) ) h ⟩ )

/-- The rearranged terms tend to zero. -/
theorem rr_conv (a : ℕ → ℝ) (L : ℝ) (ha: (a:Series).converges)
    (ha': ¬ (a:Series).absConverges) :
    atTop.Tendsto (a ∘ rr a L) (nhds 0) := by
      -- Let's show that the function `rr a L` tends to infinity.
      have h_rr_inf : Filter.Tendsto (rr a L) Filter.atTop Filter.atTop := by
        -- By definition of `rr`, we know that it is injective.
        have h_inj : Function.Injective (rr a L) := by
          convert rr_inj a L;
          · convert nonneg_infinite ha ha' using 1;
          · convert neg_infinite ha ha' using 1;
        exact Injective.nat_tendsto_atTop h_inj;
      refine' Filter.Tendsto.comp _ h_rr_inf;
      have := Series.decay_of_converges ha;
      convert this.comp tendsto_natCast_atTop_atTop using 1

/-
The natural-indexed partial sums of the rearranged series tend to `L`.
-/
theorem rr_partial_tendsto (a : ℕ → ℝ) (L : ℝ) (ha: (a:Series).converges)
    (ha': ¬ (a:Series).absConverges) :
    atTop.Tendsto (fun n:ℕ ↦ ∑ i:Fin n, a (rr a L i)) (nhds L) := by
      -- Define the partial sums of the rearranged series.
      set T : ℕ → ℝ := fun n => ∑ i : Fin n, a (rr a L i);
      -- By definition of $T$, we know that for any $\epsilon > 0$, there exists an $N$ such that for all $n \geq N$, $|T n - L| < \epsilon$.
      have h_tendsto : ∀ ε > 0, ∃ N, ∀ n ≥ N, |T n - L| < ε := by
        intro ε hε_pos
        obtain ⟨D, hD⟩ : ∃ D, ∀ k ≥ D, |a (rr a L k)| < ε := by
          have := rr_conv a L ha ha';
          simpa using Metric.tendsto_atTop.mp this ε hε_pos |> fun ⟨ D, hD ⟩ => ⟨ D, fun k hk => by simpa using hD k hk ⟩
        obtain ⟨D0, hD0⟩ : ∃ D0, D0 ≥ D ∧ T D0 < L := by
          have := rr_case_I a L ha ha';
          exact Exists.elim ( Set.Infinite.exists_gt ( Set.infinite_coe_iff.mp this ) D ) fun x hx => ⟨ x, hx.2.le, hx.1 ⟩
        obtain ⟨p, hp⟩ : ∃ p, D0 < p ∧ L ≤ T p ∧ ∀ j, D0 < j → j < p → T j < L := by
          have h_exists_p : ∃ p, D0 < p ∧ L ≤ T p := by
            have h_exists_p : Set.Infinite {j | L ≤ T j} := by
              convert rr_case_II a L _ _ using 1;
              · exact Iff.symm Set.infinite_coe_iff;
              · convert ha using 1;
              · convert ha' using 1;
            exact Exists.elim ( h_exists_p.exists_gt D0 ) fun p hp => ⟨ p, hp.2, hp.1 ⟩;
          exact ⟨ Nat.find h_exists_p, Nat.find_spec h_exists_p |>.1, Nat.find_spec h_exists_p |>.2, fun j hj₁ hj₂ => not_le.1 fun hj₃ => Nat.find_min h_exists_p hj₂ ⟨ hj₁, hj₃ ⟩ ⟩
        use p
        intro n hn
        induction' n, hn using Nat.le_induction with n hn ih;
        · have hTp : T p = T (p - 1) + a (rr a L (p - 1)) := by
            rcases p <;> simp_all +decide [ Fin.sum_univ_castSucc ];
            exact Fin.sum_univ_castSucc fun i => a (rr a L ↑i);
          by_cases h_cases : p - 1 = D0;
          · simp_all +decide [ abs_lt ];
            constructor <;> linarith [ hD D0 hD0.1 ];
          · grind +revert;
        · have h_sign : (T n < L → 0 ≤ a (rr a L n)) ∧ (L ≤ T n → a (rr a L n) < 0) := by
            have h_sign : (T n < L → 0 ≤ a (rr a L n)) ∧ (L ≤ T n → a (rr a L n) < 0) := by
              have h_nonneg : Infinite {n | a n ≥ 0} := by
                convert nonneg_infinite _ _ using 1;
                · convert ha using 1;
                · convert ha' using 1
              have h_neg : Infinite {n | a n < 0} := by
                convert neg_infinite _ _;
                · convert ha using 1;
                · convert ha' using 1
              exact ⟨fun h => (rr_pick_pos a L n h).left, fun h => (rr_pick_neg a L n (by
              linarith!)).left⟩;
            exact h_sign;
          have h_telescope : T (n + 1) = T n + a (rr a L n) := by
            convert Fin.sum_univ_castSucc _ using 1;
          grind +qlia;
      exact Metric.tendsto_atTop.mpr h_tendsto

/-
The rearranged series converges to `L`.
-/
theorem rr_sum (a : ℕ → ℝ) (L : ℝ) (ha: (a:Series).converges)
    (ha': ¬ (a:Series).absConverges) :
    (a ∘ rr a L:Series).convergesTo L := by
      have h_partial : Filter.Tendsto (fun n : ℕ => ∑ i : Fin (n + 1), a (rr a L i)) Filter.atTop (nhds L) := by
        have h_partial : Filter.Tendsto (fun n : ℕ => ∑ i : Fin n, a (rr a L i)) Filter.atTop (nhds L) := by
          exact rr_partial_tendsto a L ha ha';
        exact h_partial.comp ( Filter.tendsto_add_atTop_nat 1 );
      refine' Metric.tendsto_atTop.mpr _;
      intro ε hε; rcases Metric.tendsto_atTop.mp h_partial ε hε with ⟨ N, hN ⟩ ; use N; intros n hn; simp_all +decide [ Finset.sum_range, Fin.sum_univ_succ ] ;
      rcases n with ( _ | n ) <;> norm_cast at *;
      · convert hN _ ( Nat.cast_le.mp hn ) using 1;
        simp +decide [ Series.partial, Finset.sum_range, Fin.sum_univ_succ ];
        erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ Finset.sum_range, Fin.sum_univ_succ ];
      · linarith [ Int.negSucc_lt_zero n ]

/-- Theorem 8.2.8 (Riemann rearrangement theorem) / Exercise 8.2.5 -/
theorem permute_convergesTo_of_divergent {a: ℕ → ℝ} (ha: (a:Series).converges)
  (ha': ¬ (a:Series).absConverges) (L:ℝ) :
  ∃ f : ℕ → ℕ, Bijective f ∧ (a ∘ f:Series).convergesTo L
  := by
  haveI : Infinite {n | a n ≥ 0} := nonneg_infinite ha ha'
  haveI : Infinite {n | a n < 0} := neg_infinite ha ha'
  exact ⟨rr a L, ⟨rr_inj a L, rr_surj a L ha ha'⟩, rr_sum a L ha ha'⟩

open Classical in
/-- Recursion functional for the divergent (to `+∞`) rearrangement: pick the least unused
nonnegative-term index while the partial sum is below `(number of negative terms used so far) + 1`,
and otherwise pick the least unused negative-term index. -/
noncomputable def rrTopF (a : ℕ → ℝ) : (n : ℕ) → ((m : ℕ) → m < n → ℕ) → ℕ :=
  fun j n' ↦
    if ∑ i:Fin j, a (n' i (by simp))
        < ((Finset.univ.filter (fun i : Fin j => a (n' i (by simp)) < 0)).card : ℝ) + 1 then
      Nat.min { n ∈ {n | a n ≥ 0} | ∀ i:Fin j, n ≠ n' i (by simp) }
    else
      Nat.min { n ∈ {n | a n < 0} | ∀ i:Fin j, n ≠ n' i (by simp) }

/-- The divergent (to `+∞`) rearrangement permutation. -/
noncomputable def rrTop (a : ℕ → ℝ) : ℕ → ℕ := Nat.strongRec (rrTopF a)

/-- Unfolding equation for `rrTop`. -/
theorem rrTop_eq (a : ℕ → ℝ) (j:ℕ) :
    rrTop a j = if ∑ i:Fin j, a (rrTop a i)
        < ((Finset.univ.filter (fun i : Fin j => a (rrTop a i) < 0)).card : ℝ) + 1 then
      Nat.min { n ∈ {n | a n ≥ 0} | ∀ i:Fin j, n ≠ rrTop a i }
    else
      Nat.min { n ∈ {n | a n < 0} | ∀ i:Fin j, n ≠ rrTop a i }
  := Nat.strongRec.eq_def _ j

/-
At each step, the candidate unused nonnegative indices form an infinite set.
-/
theorem rrTop_plus_inf (a : ℕ → ℝ) [Infinite {n | a n ≥ 0}] (j:ℕ) :
    Infinite { n ∈ {n | a n ≥ 0} | ∀ i:Fin j, n ≠ rrTop a i } := by
      refine Set.infinite_coe_iff.mpr ?_;
      convert Set.Infinite.diff ( Set.infinite_coe_iff.mp ‹_› ) ( Set.toFinite ( Set.range fun i : Fin j => rrTop a i ) ) using 1;
      grind

/-
At each step, the candidate unused negative indices form an infinite set.
-/
theorem rrTop_minus_inf (a : ℕ → ℝ) [Infinite {n | a n < 0}] (j:ℕ) :
    Infinite { n ∈ {n | a n < 0} | ∀ i:Fin j, n ≠ rrTop a i } := by
      refine Set.infinite_coe_iff.mpr ?_;
      convert Set.Infinite.diff ( Set.infinite_coe_iff.mp ‹_› ) ( Set.toFinite ( Finset.image ( fun i : Fin j => rrTop a i ) Finset.univ ) ) using 1;
      grind

/-
`rrTop` is injective.
-/
theorem rrTop_inj (a : ℕ → ℝ) [Infinite {n | a n ≥ 0}] [Infinite {n | a n < 0}] :
    Injective (rrTop a) := by
      intro x y hxy;
      -- By definition of `rrTop`, we know that for any `j`, `rrTop a j` is distinct from `rrTop a i` for all `i < j`.
      have h_distinct : ∀ j i : ℕ, i < j → rrTop a j ≠ rrTop a i := by
        intros j i hij
        rw [rrTop_eq a j];
        split_ifs;
        · have := Nat.min_spec ( show { n | n ∈ { n | a n ≥ 0 } ∧ ∀ i : Fin j, n ≠ rrTop a i }.Nonempty from ?_ );
          · exact this.1.2 ⟨ i, hij ⟩;
          · convert Set.Infinite.nonempty ( Set.infinite_coe_iff.mp ( rrTop_plus_inf a j ) ) using 1;
        · have := Nat.min_spec ( show { n | n ∈ { n | a n < 0 } ∧ ∀ i : Fin j, n ≠ rrTop a i }.Nonempty from ?_ );
          · exact this.1.2 ⟨ i, hij ⟩;
          · convert Set.Infinite.nonempty ( Set.infinite_coe_iff.mp ( rrTop_minus_inf a j ) ) using 1;
      grind

/-
When the threshold condition holds, the chosen index is the least available nonnegative-term index.
-/
theorem rrTop_pick_pos (a : ℕ → ℝ) [Infinite {n | a n ≥ 0}] (j:ℕ)
    (h: ∑ i:Fin j, a (rrTop a i)
        < ((Finset.univ.filter (fun i : Fin j => a (rrTop a i) < 0)).card : ℝ) + 1) :
    0 ≤ a (rrTop a j) ∧ ∀ x, 0 ≤ a x → (∀ i:Fin j, x ≠ rrTop a i) → rrTop a j ≤ x := by
      rw [rrTop_eq] at *;
      have := Nat.min_spec ( show { n | n ∈ { n | 0 ≤ a n } ∧ ∀ i : Fin j, n ≠ rrTop a i }.Nonempty from ?_ );
      · grind;
      · convert Set.Infinite.nonempty ( Set.infinite_coe_iff.mp ( rrTop_plus_inf a j ) ) using 1

/-
When the threshold condition fails, the chosen index is the least available negative-term index.
-/
theorem rrTop_pick_neg (a : ℕ → ℝ) [Infinite {n | a n < 0}] (j:ℕ)
    (h: ¬ (∑ i:Fin j, a (rrTop a i)
        < ((Finset.univ.filter (fun i : Fin j => a (rrTop a i) < 0)).card : ℝ) + 1)) :
    a (rrTop a j) < 0 ∧ ∀ x, a x < 0 → (∀ i:Fin j, x ≠ rrTop a i) → rrTop a j ≤ x := by
      convert Set.Infinite.nonempty ( Set.infinite_coe_iff.mp ( rrTop_minus_inf a j ) ) using 1;
      constructor <;> intro h;
      · convert Set.Infinite.nonempty ( Set.infinite_coe_iff.mp ( rrTop_minus_inf a j ) ) using 1;
      · grind +suggestions

set_option maxHeartbeats 1000000 in
/-- Infinitely many steps pick a negative-term index. -/
theorem rrTop_neg_inf (a : ℕ → ℝ) (ha: (a:Series).converges) (ha': ¬ (a:Series).absConverges) :
    Infinite { j | ¬ (∑ i:Fin j, a (rrTop a i)
        < ((Finset.univ.filter (fun i : Fin j => a (rrTop a i) < 0)).card : ℝ) + 1) } := by
          haveI := nonneg_infinite ha ha'
          haveI := neg_infinite ha ha';
          by_contra h_contra
          obtain ⟨J, hJ⟩ : ∃ J, ∀ j ≥ J, ∑ i : Fin j, a (rrTop a i) < ((Finset.univ.filter (fun i : Fin j => a (rrTop a i) < 0)).card : ℝ) + 1 := by
            simp +zetaDelta at *;
            obtain ⟨ J, hJ ⟩ := Set.Finite.bddAbove ( Set.finite_coe_iff.mp h_contra ) ; exact ⟨ J + 1, fun j hj => lt_of_not_ge fun h => not_lt_of_ge ( hJ h ) hj ⟩ ;
          -- Claim `C j = C J` for all `j ≥ J`: for any `i ≥ J`, `S i < (C i)+1`, so `rrTop_pick_pos a i` gives `0 ≤ a (rrTop a i)`, hence `¬ (a (rrTop a i) < 0)`. Therefore no index `i ∈ [J, j)` is counted by the filter, so `C j = C J` (prove by `Nat.le_induction`: `C (j+1) = C j` using `Finset.range_succ`/`Finset.filter_insert` and `¬ (a (rrTop a j) < 0)`). In particular for `j ≥ J`, `S j < (C J : ℝ) + 1`.
          have hC_const : ∀ j ≥ J, ((Finset.univ.filter (fun i : Fin j => a (rrTop a i) < 0)).card : ℝ) = ((Finset.univ.filter (fun i : Fin J => a (rrTop a i) < 0)).card : ℝ) := by
            intro j hj
            induction' hj with j hj ih;
            · rfl;
            · have := rrTop_pick_pos a j ( hJ j hj );
              rw [ Finset.card_filter, Finset.card_filter ] at *;
              rw [ Fin.sum_univ_castSucc ] ; aesop;
          -- Exhaustion: every `x` with `0 ≤ a x` is eventually chosen. Suppose not: `∀ j, rrTop a j ≠ x`. For `j ≥ J`, `S j < (C j)+1` holds, so `rrTop_pick_pos a j` applies; at `x` (using `0 ≤ a x` and `∀ i:Fin j, x ≠ rrTop a i`) it gives `rrTop a j ≤ x`. The values `rrTop a j` for distinct `j ≥ J` are distinct (`rrTop` injective via `rrTop_inj a`), giving an injection of the infinite `Set.Ici J` into `Finset.range (x+1)` — contradiction (`Set.infinite_Ici`).
          have h_exhaust : ∀ x, 0 ≤ a x → ∃ j, rrTop a j = x := by
            intro x hx_nonneg
            by_contra h_contra
            push_neg at h_contra
            have h_le : ∀ j ≥ J, rrTop a j ≤ x := by
              intros j hj
              have := rrTop_pick_pos a j (hJ j hj)
              exact this.2 x hx_nonneg (fun i => fun hi => h_contra i hi.symm)
            have h_inj : Set.InjOn (rrTop a) (Set.Ici J) := by
              exact fun i hi j hj hij => by have := rrTop_inj a; aesop;
            exact absurd ( Set.Infinite.image ( show Set.InjOn ( rrTop a ) ( Set.Ici J ) from h_inj ) ( Set.Ici_infinite J ) ) ( Set.not_infinite.mpr <| Set.finite_iff_bddAbove.mpr ⟨ x, fun y hy => by aesop ⟩ );
          -- Apply `pos_unbounded` to get a finite `F ⊆ {n | a n ≥ 0}`, disjoint from `Finset.image (rrTop a) (Finset.range J)`, with `(C J : ℝ) + 1 - S J < ∑ n ∈ F, a n`.
          obtain ⟨ F, hF₁, hF₂, hF₃ ⟩ := pos_unbounded ha ha' ( Finset.image (rrTop a) (Finset.range J) ) ( ( (Finset.univ.filter (fun i : Fin J => a (rrTop a i) < 0)).card : ℝ) + 1 - ∑ i : Fin J, a (rrTop a i) );
          -- By exhaustion each `x ∈ F` is `rrTop a (g x)` for some `g x`, and `g x ≥ J` (else `x ∈ image (rrTop a) (range J)`, contradicting disjointness). Let `K := (F.sup g) + 1 ⊔ J`.
          obtain ⟨ K, hK ⟩ : ∃ K ≥ J, ∀ x ∈ F, ∃ k ∈ Finset.Ico J K, rrTop a k = x := by
            have hK : ∀ x ∈ F, ∃ k ≥ J, rrTop a k = x := by
              intro x hx; obtain ⟨ k, hk ⟩ := h_exhaust x ( hF₁ hx ) ; use k; simp_all +decide [ Finset.disjoint_left ] ;
              exact le_of_not_gt fun hk' => hF₂ hx k hk' hk;
            choose! k hk₁ hk₂ using hK;
            exact ⟨ Finset.sup F k + J + 1, by linarith, fun x hx => ⟨ k x, Finset.mem_Ico.mpr ⟨ hk₁ x hx, by linarith [ Finset.le_sup ( f := k ) hx ] ⟩, hk₂ x hx ⟩ ⟩;
          have h_sum_le : ∑ n ∈ F, a n ≤ ∑ n ∈ Finset.image (rrTop a) (Finset.Ico J K), a n := by
            apply Finset.sum_le_sum_of_subset_of_nonneg;
            · exact fun x hx => by obtain ⟨ k, hk₁, hk₂ ⟩ := hK.2 x hx; exact hk₂ ▸ Finset.mem_image_of_mem _ hk₁;
            · grind +suggestions;
          rw [ Finset.sum_image ] at h_sum_le;
          · rw [ Finset.sum_Ico_eq_sub _ hK.1 ] at h_sum_le;
            linarith! [ hJ K hK.1, hC_const K hK.1, show ∑ k ∈ Finset.range K, a ( rrTop a k ) = ∑ i : Fin K, a ( rrTop a i ) from by rw [ Finset.sum_range ], show ∑ k ∈ Finset.range J, a ( rrTop a k ) = ∑ i : Fin J, a ( rrTop a i ) from by rw [ Finset.sum_range ] ];
          · exact fun x hx y hy hxy => by have := rrTop_inj a; have := @this x y; aesop;

set_option maxHeartbeats 1000000 in
/-- Infinitely many steps pick a nonnegative-term index. -/
theorem rrTop_pos_inf (a : ℕ → ℝ) (ha: (a:Series).converges) (ha': ¬ (a:Series).absConverges) :
    Infinite { j | ∑ i:Fin j, a (rrTop a i)
        < ((Finset.univ.filter (fun i : Fin j => a (rrTop a i) < 0)).card : ℝ) + 1 } := by
          convert Set.infinite_coe_iff.mpr _;
          by_contra h_contra;
          -- Obtain instances `Infinite {n|a n≥0}`, `Infinite {n|a n<0}` via `nonneg_infinite ha ha'`, `neg_infinite ha ha'` (haveI).
          haveI := nonneg_infinite ha ha'
          haveI := neg_infinite ha ha';
          obtain ⟨J, hJ⟩ : ∃ J, ∀ j ≥ J, ¬(∑ i : Fin j, a (rrTop a i) < ((Finset.univ.filter (fun i : Fin j => a (rrTop a i) < 0)).card : ℝ) + 1) := by
            exact Set.finite_iff_bddAbove.mp ( Classical.not_not.mp h_contra ) |> fun ⟨ J, hJ ⟩ => ⟨ J + 1, fun j hj hj' => not_lt_of_ge ( hJ hj' ) hj ⟩;
          -- By `rrTop_pick_neg a j` (its hypothesis is exactly `¬ (S j < C j + 1)`), `a (rrTop a j) < 0` for all `j ≥ J`.
          have h_neg : ∀ j ≥ J, a (rrTop a j) < 0 := by
            intro j hj; specialize hJ j hj; exact (rrTop_pick_neg a j hJ).left;
          -- By induction, we have $S j \leq S J$ for all $j \geq J$.
          have h_le : ∀ j ≥ J, ∑ i : Fin j, a (rrTop a i) ≤ ∑ i : Fin J, a (rrTop a i) := by
            intro j hj; induction hj <;> simp_all +decide [ Fin.sum_univ_castSucc ] ;
            linarith [ h_neg _ ‹_› ];
          -- By induction, we have $C j = C J + (j - J)$ for all $j \geq J$.
          have h_card : ∀ j ≥ J, ((Finset.univ.filter (fun i : Fin j => a (rrTop a i) < 0)).card : ℝ) = ((Finset.univ.filter (fun i : Fin J => a (rrTop a i) < 0)).card : ℝ) + (j - J) := by
            intro j hj; induction hj <;> simp_all +decide [ Fin.sum_univ_castSucc, Finset.sum_range_succ ] ;
            rw [ Finset.card_filter, Finset.card_filter ] at *;
            rw [ Fin.sum_univ_castSucc ] ; simp_all +decide [ Fin.sum_univ_succ ] ; ring;
          -- Choose $j$ such that $C J + (j - J) > S J - 1$.
          obtain ⟨j, hj⟩ : ∃ j ≥ J, ((Finset.univ.filter (fun i : Fin J => a (rrTop a i) < 0)).card : ℝ) + (j - J) > (∑ i : Fin J, a (rrTop a i)) - 1 := by
            exact ⟨ ⌊ ( ∑ i : Fin J, a ( rrTop a i ) ) - 1 - ( Finset.card ( Finset.filter ( fun i : Fin J => a ( rrTop a i ) < 0 ) Finset.univ ) : ℝ ) + J⌋₊ + J + 1, by linarith, by push_cast; linarith [ Nat.lt_floor_add_one ( ( ∑ i : Fin J, a ( rrTop a i ) ) - 1 - ( Finset.card ( Finset.filter ( fun i : Fin J => a ( rrTop a i ) < 0 ) Finset.univ ) : ℝ ) + J ) ] ⟩;
          linarith [ hJ j hj.1, h_le j hj.1, h_card j hj.1 ]

/-
`rrTop` is surjective.
-/
theorem rrTop_surj (a : ℕ → ℝ) (ha: (a:Series).converges) (ha': ¬ (a:Series).absConverges) :
    Surjective (rrTop a) := by
      intro x;
      by_contra h_contra;
      -- By `rrTop_pos_inf a ha ha'`, the set `P := { j | ∑ i:Fin j, a (rrTop a i) < ((Finset.univ.filter (fun i : Fin j => a (rrTop a i) < 0)).card : ℝ) + 1 }` is infinite.
      have hP_inf : Set.Infinite { j | ∑ i : Fin j, a (rrTop a i) < ((Finset.univ.filter (fun i : Fin j => a (rrTop a i) < 0)).card : ℝ) + 1 } := by
        convert rrTop_pos_inf a ha ha' using 1;
        exact Set.infinite_coe_iff.symm;
      -- By `rrTop_neg_inf a ha ha'`, the set `Q := { j | ¬ (∑ i:Fin j, a (rrTop a i) < ((Finset.univ.filter (fun i : Fin j => a (rrTop a i) < 0)).card : ℝ) + 1) }` is infinite.
      have hQ_inf : Set.Infinite { j | ¬ (∑ i : Fin j, a (rrTop a i) < ((Finset.univ.filter (fun i : Fin j => a (rrTop a i) < 0)).card : ℝ) + 1) } := by
        convert rrTop_neg_inf a _ _ using 1;
        · rw [ Set.infinite_coe_iff ];
        · exact ha;
        · convert ha' using 1;
      have h_nonneg_infinite : Infinite {n | a n ≥ 0} := by
        convert nonneg_infinite ha ha' using 1
      have h_neg_infinite : Infinite {n | a n < 0} := by
        convert neg_infinite _ _ using 1;
        · convert ha using 1;
        · convert ha' using 1;
      by_cases hx : 0 ≤ a x;
      · have h_image : Set.Infinite (Set.image (rrTop a) {j | ∑ i : Fin j, a (rrTop a i) < ((Finset.univ.filter (fun i : Fin j => a (rrTop a i) < 0)).card : ℝ) + 1}) := by
          exact Set.Infinite.image ( fun j => by have := rrTop_inj a; aesop ) hP_inf;
        exact h_image ( Set.Finite.subset ( Set.finite_le_nat x ) <| Set.image_subset_iff.mpr fun j hj => by have := rrTop_pick_pos a j hj; exact this.2 x hx fun i => fun hi => by aesop );
      · have h_image : Set.Infinite (Set.image (rrTop a) {j | ¬ (∑ i : Fin j, a (rrTop a i) < ((Finset.univ.filter (fun i : Fin j => a (rrTop a i) < 0)).card : ℝ) + 1)}) := by
          exact Set.Infinite.image ( fun j => by have := rrTop_inj a; aesop ) hQ_inf;
        exact h_image ( Set.Finite.subset ( Set.finite_le_nat x ) <| Set.image_subset_iff.mpr fun j hj => Nat.le_of_not_lt fun h => by have := rrTop_pick_neg a j hj; exact not_lt_of_ge ( this.2 x ( by linarith ) ( fun i hi => by aesop ) ) h )

/-
The `rrTop`-rearranged terms tend to zero.
-/
theorem rrTop_conv (a : ℕ → ℝ) (ha: (a:Series).converges) (ha': ¬ (a:Series).absConverges) :
    atTop.Tendsto (a ∘ rrTop a) (nhds 0) := by
      have h_tendsto : Filter.Tendsto (fun n => a n) Filter.atTop (nhds 0) := by
        have := Series.decay_of_converges ha;
        convert this.comp tendsto_natCast_atTop_atTop using 1;
      refine' h_tendsto.comp _;
      have h_inj : Function.Injective (rrTop a) := by
        convert rrTop_inj a;
        · convert nonneg_infinite _ _ using 1;
          · exact ha;
          · convert ha' using 1;
        · exact neg_infinite ha ha';
      exact Injective.nat_tendsto_atTop h_inj

/-
The count of negative-term picks increases by one exactly when the current pick is negative.
-/
theorem rrTop_count_succ (a : ℕ → ℝ) (n : ℕ) :
    (Finset.univ.filter (fun i : Fin (n+1) => a (rrTop a i) < 0)).card
      = (Finset.univ.filter (fun i : Fin n => a (rrTop a i) < 0)).card
          + (if a (rrTop a n) < 0 then 1 else 0) := by
            rw [ Finset.card_filter, Finset.card_filter ];
            convert Fin.sum_univ_castSucc _ using 1

set_option maxHeartbeats 1000000 in
/-- Lower bound: past some point, the partial sum is at least (negative-count) − 1. -/
theorem rrTop_lower (a : ℕ → ℝ) (ha: (a:Series).converges) (ha': ¬ (a:Series).absConverges) :
    ∃ d, ∀ n, d ≤ n →
      ((Finset.univ.filter (fun i : Fin n => a (rrTop a i) < 0)).card : ℝ) - 1
        ≤ ∑ i:Fin n, a (rrTop a i) := by
          obtain ⟨D, hD⟩ : ∃ D, ∀ k ≥ D, |a (rrTop a k)| < 1 := by
            have := Metric.tendsto_atTop.mp ( rrTop_conv a ha ha' ) 1 zero_lt_one; aesop;
          obtain ⟨ dd, hdd ⟩ : ∃ dd, dd ≥ D ∧ ¬(∑ i : Fin dd, a (rrTop a i) < ((Finset.univ.filter (fun i : Fin dd => a (rrTop a i) < 0)).card : ℝ) + 1) ∧ a (rrTop a dd) < 0 := by
            have h_neg_inf : Set.Infinite { j | ¬ (∑ i : Fin j, a (rrTop a i) < ((Finset.univ.filter (fun i : Fin j => a (rrTop a i) < 0)).card : ℝ) + 1) } := by
              convert rrTop_neg_inf a _ _ using 1;
              · rw [ Set.infinite_coe_iff ];
              · convert ha using 1;
              · convert ha' using 1;
            obtain ⟨ dd, hdd₁, hdd₂ ⟩ := h_neg_inf.exists_gt D;
            haveI := nonneg_infinite ha ha'
            haveI := neg_infinite ha ha'
            exact ⟨ dd, hdd₂.le, hdd₁, (rrTop_pick_neg a dd hdd₁).left ⟩;
          refine' ⟨ dd + 1, fun n hn => _ ⟩;
          induction' hn with n hn ih <;> simp_all +decide [ Fin.sum_univ_castSucc, Finset.sum_range_succ ];
          · have := rrTop_count_succ a dd;
            simp_all +decide [ Fin.sum_univ_castSucc ];
            linarith [ abs_lt.mp ( hD dd hdd.1 ) ];
          · by_cases h_neg : a (rrTop a n) < 0;
            · have h_card : (Finset.univ.filter (fun i : Fin n => a (rrTop a i) < 0)).card + 1 ≤ ∑ i : Fin n, a (rrTop a i) := by
                contrapose! h_neg;
                convert rrTop_pick_pos a n h_neg |>.1 using 1;
                convert nonneg_infinite ha ( by
                  grind ) using 1;
              have := rrTop_count_succ a n; simp_all +decide [ Finset.sum_range, Fin.sum_univ_castSucc ] ; linarith [ abs_lt.mp ( hD n ( by linarith ) ) ] ;
            · linarith! [ show ( Finset.card ( Finset.filter ( fun i : Fin ( n + 1 ) => a ( rrTop a i ) < 0 ) Finset.univ ) : ℝ ) = Finset.card ( Finset.filter ( fun i : Fin n => a ( rrTop a i ) < 0 ) Finset.univ ) from mod_cast by rw [ Finset.card_filter, Finset.card_filter ] ; rw [ Fin.sum_univ_castSucc ] ; aesop ]

/-
The count of negative-term picks tends to `+∞`.
-/
theorem rrTop_count_tendsto (a : ℕ → ℝ) (ha: (a:Series).converges) (ha': ¬ (a:Series).absConverges) :
    atTop.Tendsto (fun n:ℕ ↦ ((Finset.univ.filter (fun i : Fin n => a (rrTop a i) < 0)).card : ℝ)) atTop := by
      have h_neg_inf : Set.Infinite {j | a (rrTop a j) < 0} := by
        have := @rrTop_neg_inf a ha ha';
        have h_neg_inf : ∀ j ∈ {j | ¬(∑ i : Fin j, a (rrTop a i) < ((Finset.univ.filter (fun i : Fin j => a (rrTop a i) < 0)).card : ℝ) + 1)}, a (rrTop a j) < 0 := by
          haveI := neg_infinite ha ha'
          haveI := nonneg_infinite ha ha'
          exact fun j hj => (rrTop_pick_neg a j hj).left;
        exact Set.Infinite.mono h_neg_inf ( Set.infinite_coe_iff.mp this );
      refine' tendsto_natCast_atTop_atTop.comp ( Filter.tendsto_atTop_atTop.mpr _ );
      intro b
      obtain ⟨s, hs⟩ : ∃ s : Finset ℕ, s.card = b ∧ ∀ j ∈ s, a (rrTop a j) < 0 := by
        have := h_neg_inf.exists_subset_card_eq b; tauto;
      use s.sup id + 1;
      intro n hn
      have h_subset : s ⊆ Finset.image (fun i : Fin n => i.val) (Finset.filter (fun i : Fin n => a (rrTop a i) < 0) Finset.univ) := by
        intro j hj; specialize hs; have := hs.2 j hj; exact Finset.mem_image.mpr ⟨ ⟨ j, by linarith [ show j ≤ s.sup id from Finset.le_sup ( f := id ) hj ] ⟩, by aesop ⟩ ;
      have := Finset.card_le_card h_subset; simp_all +decide [ Finset.card_image_of_injective, Function.Injective ] ;
      exact this.trans ( Finset.card_image_le )

/-
The natural-indexed partial sums of the `rrTop`-rearranged series tend to `+∞`.
-/
theorem rrTop_partial_tendsto (a : ℕ → ℝ) (ha: (a:Series).converges) (ha': ¬ (a:Series).absConverges) :
    atTop.Tendsto (fun n:ℕ ↦ ∑ i:Fin n, a (rrTop a i)) atTop := by
      obtain ⟨ d, hd ⟩ := rrTop_lower a ha ha';
      -- From `rrTop_count_tendsto a ha ha'`, `atTop.Tendsto (fun n ↦ ((... count ...) : ℝ)) atTop`, hence also
      -- `atTop.Tendsto (fun n ↦ ((... count ...) : ℝ) - 1) atTop` (subtracting a constant: `Filter.Tendsto.atTop_add` /
      -- `tendsto_atTop_add_const_right`).
      have h_count_tendsto : Filter.Tendsto (fun n => ((Finset.univ.filter (fun i : Fin n => a (rrTop a i) < 0)).card : ℝ) - 1) Filter.atTop Filter.atTop := by
        convert Filter.tendsto_atTop_add_const_right _ _ ( rrTop_count_tendsto a ( by simpa using ha ) ha' ) using 1;
      exact Filter.tendsto_atTop_mono' Filter.atTop ( Filter.eventually_atTop.mpr ⟨ d, hd ⟩ ) h_count_tendsto

/-
The `rrTop`-rearranged series has partial sums diverging to `⊤` in `EReal`.
-/
theorem rrTop_sum (a : ℕ → ℝ) (ha: (a:Series).converges) (ha': ¬ (a:Series).absConverges) :
    atTop.Tendsto (fun N ↦ ((a ∘ rrTop a:Series).partial N : EReal)) (nhds ⊤) := by
      refine' EReal.tendsto_nhds_top_iff_real.mpr _;
      intro x
      have h_real : Filter.Tendsto (fun n : ℕ => ∑ i : Fin (n + 1), a (rrTop a i)) Filter.atTop Filter.atTop := by
        convert rrTop_partial_tendsto a ( by simpa using ha ) ha' |> Filter.Tendsto.comp <| Filter.tendsto_add_atTop_nat 1 using 1;
      have h_real : ∀ᶠ n : ℤ in Filter.atTop, ∃ m : ℕ, n = m ∧ x < ∑ i : Fin (m + 1), a (rrTop a i) := by
        have := h_real.eventually_gt_atTop x; simp_all +decide [ Filter.eventually_atTop ] ;
        obtain ⟨ N, hN ⟩ := this; exact ⟨ N, fun n hn => ⟨ Int.toNat n, by rw [ Int.toNat_of_nonneg ( by linarith ) ], hN _ ( by linarith [ Int.self_le_toNat n ] ) ⟩ ⟩ ;
      filter_upwards [ h_real, Filter.eventually_ge_atTop 0 ] with n hn hn' ; obtain ⟨ m, rfl, hm ⟩ := hn ; simp_all +decide [ Series.partial ] ;
      convert hm using 1;
      refine' Finset.sum_bij ( fun i hi => ⟨ i, by linarith [ Finset.mem_Icc.mp hi ] ⟩ ) _ _ _ _ <;> simp +decide;
      exact fun b => ⟨ b, Fin.is_le b, rfl ⟩

/-- Exercise 8.2.6 -/
theorem permute_diverges_of_divergent {a: ℕ → ℝ} (ha: (a:Series).converges)
  (ha': ¬ (a:Series).absConverges)  :
  ∃ f : ℕ → ℕ,  Bijective f ∧ atTop.Tendsto (fun N ↦ ((a ∘ f:Series).partial N : EReal)) (nhds ⊤) := by
  haveI : Infinite {n | a n ≥ 0} := nonneg_infinite ha ha'
  haveI : Infinite {n | a n < 0} := neg_infinite ha ha'
  exact ⟨rrTop a, ⟨rrTop_inj a, rrTop_surj a ha ha'⟩, rrTop_sum a ha ha'⟩

theorem permute_diverges_of_divergent' {a: ℕ → ℝ} (ha: (a:Series).converges)
  (ha': ¬ (a:Series).absConverges)  :
  ∃ f : ℕ → ℕ,  Bijective f ∧ atTop.Tendsto (fun N ↦ ((a ∘ f:Series).partial N : EReal)) (nhds ⊥) := by
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℕ, Bijective f ∧ Tendsto (fun N => ((fun n => -a n) ∘ f:Series).partial N : ℤ → EReal) atTop (nhds ⊤) := by
    apply permute_diverges_of_divergent;
    · obtain ⟨ L, hL ⟩ := ha;
      refine' ⟨ -L, _ ⟩
      generalize_proofs at *;
      convert hL.neg using 1;
      ext; simp [Series.partial];
      rw [ ← Finset.sum_neg_distrib ] ; exact Finset.sum_congr rfl fun _ _ => by split_ifs <;> ring;
    · convert ha' using 1;
      simp +decide [ Series.absConverges, Series.abs ];
      unfold Series.mk'; aesop;
  generalize_proofs at *;
  use f;
  norm_num [ Series.partial ] at *;
  simp_all +decide [ Finset.sum_ite ]

end Chapter8
