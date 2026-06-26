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
  have hfinsum (X: Finset (ℕ × ℕ)) : ∑ p ∈ X, f p ≤ L := by sorry
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
      sorry
    choose X hX using this
    have : ∃ N, ∃ M, X ⊆ (Icc 0 N) ×ˢ (Icc 0 M) := by
      sorry
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
  have hdiff : f = fplus - fminus := by sorry
  have hfplus_conv : AbsConvergent fplus := by sorry
  have hfminus_conv : AbsConvergent fminus := by sorry
  choose hfplus_conv' hfplus_sum using sum_of_sum_of_AbsConvergent_nonneg hfplus_conv hfplus_nonneg
  choose hfminus_conv' hfminus_sum using sum_of_sum_of_AbsConvergent_nonneg hfminus_conv hfminus_nonneg
  split_ands
  . intro n
    sorry
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
    sorry

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
    sorry

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
  sorry

/-- Proposition 8.2.6 (b) (Absolutely convergent series laws) / Exercise 8.2.3 -/
theorem Sum'.smul {X:Type} {f:X → ℝ} (hf: AbsConvergent' f) (c: ℝ) :
  AbsConvergent' (c • f) ∧ Sum' (c • f) = c * Sum' f := by
  sorry

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
  sorry

/-- This technical claim, the analogue of {name}`tsum_univ`, is required due to the way Mathlib handles
    sets.-/
theorem Sum'.of_univ {X:Type} {f:X → ℝ} (hf: AbsConvergent' f) :
  Sum' (fun x: (.univ : Set X) ↦ f x) = Sum' f := by
  sorry

theorem Sum'.of_comp {X Y:Type} {f:X → ℝ} (hf: AbsConvergent' f) {φ: Y → X}
  (hφ: Function.Bijective φ) :
  AbsConvergent' (f ∘ φ) ∧ Sum' f = Sum' (f ∘ φ) := by
  sorry

/-- Lemma 8.2.7 / Exercise 8.2.4 -/
theorem divergent_parts_of_divergent {a: ℕ → ℝ} (ha: (a:Series).converges)
  (ha': ¬ (a:Series).absConverges) :
  ¬ AbsConvergent (fun n : {n | a n ≥ 0} ↦ a n) ∧ ¬ AbsConvergent (fun n : {n | a n < 0} ↦ a n)
  := by
  classical
  set a_plus := (fun n : ℕ => max (a n) 0) with ha_plus
  set a_minus := (fun n : ℕ => max (-(a n)) 0) with ha_minus
  have h_sub_eq : (a_plus : Series) - (a : Series) = (a_minus : Series) := by
    have hm : ((a_plus : Series) - (a : Series)).m = (a_minus : Series).m := by
      calc
        ((a_plus : Series) - (a : Series)).m = min ((a_plus : Series).m) ((a : Series).m) := rfl
        _ = min 0 0 := by simp
        _ = 0 := by simp
        _ = (a_minus : Series).m := by simp
    have hseq : ∀ n : ℤ, ((a_plus : Series) - (a : Series)).seq n = (a_minus : Series).seq n := by
      intro n
      by_cases hn : n ≥ 0
      · have h1 : ((a_plus : Series) - (a : Series)).seq n = max (a n.toNat) 0 - a n.toNat := by
          calc
            ((a_plus : Series) - (a : Series)).seq n = ((a_plus : Series).seq n) - ((a : Series).seq n) := by
              rfl
            _ = max (a n.toNat) 0 - a n.toNat := by simp [a_plus, hn]
        have h2 : (a_minus : Series).seq n = max (-(a n.toNat)) 0 := by
          simp [a_minus, hn]
        rw [h1, h2]
        by_cases hx_nonneg : a n.toNat ≥ 0
        · rw [max_eq_left hx_nonneg, max_eq_right (show -(a n.toNat) ≤ 0 from by linarith), sub_self]
        · rw [max_eq_right (show a n.toNat ≤ 0 from by linarith), max_eq_left (show -(a n.toNat) ≥ 0 from by linarith)]
          simp
      · have hzero : ((a_plus : Series) - (a : Series)).seq n = 0 := by
          calc
            ((a_plus : Series) - (a : Series)).seq n = ((a_plus : Series).seq n) - ((a : Series).seq n) := rfl
            _ = 0 - 0 := by simp [hn]
            _ = 0 := by simp
        simp [hzero, hn]
    exact Series.ext hm (funext hseq)
  have h_add_eq : (a : Series).abs = (a_plus : Series) + (a_minus : Series) := by
    have hm : ((a : Series).abs).m = ((a_plus : Series) + (a_minus : Series)).m := by
      calc
        ((a : Series).abs).m = 0 := by simp [Series.abs, Series.mk']
        _ = min 0 0 := by simp
        _ = min ((a_plus : Series).m) ((a_minus : Series).m) := by simp
        _ = ((a_plus : Series) + (a_minus : Series)).m := rfl
    have hseq : ∀ n : ℤ, ((a : Series).abs).seq n = ((a_plus : Series) + (a_minus : Series)).seq n := by
      intro n
      by_cases hn : n ≥ 0
      · have h1 : ((a : Series).abs).seq n = |a n.toNat| := by
          unfold Series.abs
          simp [hn]
        have h2 : ((a_plus : Series) + (a_minus : Series)).seq n = max (a n.toNat) 0 + max (-(a n.toNat)) 0 := by
          calc
            ((a_plus : Series) + (a_minus : Series)).seq n = ((a_plus : Series).seq n) + ((a_minus : Series).seq n) := rfl
            _ = max (a n.toNat) 0 + max (-(a n.toNat)) 0 := by simp [a_plus, a_minus, hn]
        rw [h1, h2]
        by_cases hx_nonneg : a n.toNat ≥ 0
        · simp [hx_nonneg]
        · simp [hx_nonneg]
      · have hzero : ((a : Series).abs).seq n = 0 := by
          unfold Series.abs; simp [hn]
        have hzero' : ((a_plus : Series) + (a_minus : Series)).seq n = 0 := by
          calc
            ((a_plus : Series) + (a_minus : Series)).seq n = ((a_plus : Series).seq n) + ((a_minus : Series).seq n) := rfl
            _ = 0 + 0 := by simp [hn]
            _ = 0 := by simp
        simp [hzero, hzero', hn]
    exact Series.ext hm (funext hseq)
  have hIcc_range (N : ℕ) : Finset.Icc (0 : ℤ) (N : ℤ) = (Finset.range (N+1)).map Nat.castEmbedding := by
    calc
      Finset.Icc (0 : ℤ) (N : ℤ) = (Finset.Icc (0 : ℕ) N).map Nat.castEmbedding := by simp
      _ = (Finset.range (N+1)).map Nat.castEmbedding := by
        have h_eq : (Finset.Icc (0 : ℕ) N : Finset ℕ) = Finset.range (N+1) := by
          ext x; simp [Finset.mem_Icc, Finset.mem_range]
        rw [h_eq]
  have h_partial_range (b : ℕ → ℝ) (M : ℕ) : (b : Series).partial (M : ℤ) = ∑ k ∈ Finset.range (M+1), b k := by
    unfold Series.partial
    have hm : (b : Series).m = 0 := rfl
    calc
      ∑ n ∈ Finset.Icc (0 : ℤ) (M : ℤ), ((b : Series).seq n) = ∑ n ∈ Finset.Icc (0 : ℤ) (M : ℤ), b n.toNat := by
        refine Finset.sum_congr rfl (λ n hn => ?_)
        have hn0 : (0 : ℤ) ≤ n := (Finset.mem_Icc.mp hn).1
        simp [hm, hn0]
      _ = ∑ n ∈ (Finset.range (M+1)).map Nat.castEmbedding, b (Int.toNat n) := by
        rw [hIcc_range M]
      _ = ∑ k ∈ Finset.range (M+1), b (Int.toNat (Nat.castEmbedding k)) := by
        simp [Finset.sum_map]
      _ = ∑ k ∈ Finset.range (M+1), b k := by simp
  have h_plus_conv (hpos : AbsConvergent (fun n : {n | a n ≥ 0} ↦ a n)) : (a_plus : Series).converges := by
    by_cases hfin : Finite {n | a n ≥ 0}
    · rcases hpos with ⟨g, hg_bij, hg_conv⟩
      have hfinite_ℕ : Finite ℕ := Finite.of_injective g hg_bij.1
      have hinfinite_ℕ : Infinite ℕ := by infer_instance
      exfalso; exact hinfinite_ℕ.not_finite hfinite_ℕ
    · have h_inf : Infinite {n | a n ≥ 0} := not_finite_iff_infinite.mp hfin
      have h_countably_inf : CountablyInfinite {n | a n ≥ 0} := Nat.countable_of_infinite {n | a n ≥ 0}
      have hpos' : AbsConvergent' (fun n : {n | a n ≥ 0} ↦ a n) :=
        ((AbsConvergent'.of_countable h_countably_inf).mpr hpos)
      rcases hpos' with ⟨M, hM⟩
      have hM_nonneg : 0 ≤ M := by
        have hzero_sum : ∑ x ∈ (∅ : Finset {n | a n ≥ 0}), |a (x : ℕ)| = (0 : ℝ) := by
          simpa using (Finset.sum_empty (f := λ (x : {n | a n ≥ 0}) => |a (x : ℕ)|))
        have hzero_mem : (0 : ℝ) ∈ (fun A : Finset {n | a n ≥ 0} ↦ ∑ x ∈ A, |(fun n : {n | a n ≥ 0} ↦ a n) x|) '' Set.univ := by
          refine ⟨(∅ : Finset {n | a n ≥ 0}), Set.mem_univ ∅, ?_⟩
          calc
            (fun A : Finset {n | a n ≥ 0} ↦ ∑ x ∈ A, |(fun n : {n | a n ≥ 0} ↦ a n) x|) ∅
                = ∑ x ∈ (∅ : Finset {n | a n ≥ 0}), |a (x : ℕ)| := by
                  simp
            _ = (0 : ℝ) := hzero_sum
        exact hM hzero_mem
      have h_max_bound (N : ℕ) : ∑ k ∈ Finset.range (N+1), a_plus k ≤ M := by
        set F : Finset {n | a n ≥ 0} := (Finset.range (N+1)).subtype (λ n => 0 ≤ a n) with hF
        have hF_nonneg (n' : {n | a n ≥ 0}) (hn' : n' ∈ F) : a n'.val ≥ 0 := n'.property
        have hF_sum_map : ∑ n' ∈ F, a n'.val = ∑ k ∈ (Finset.range (N+1)).filter (λ n => 0 ≤ a n), a k := by
          calc
            ∑ n' ∈ F, a n'.val = ∑ k ∈ F.map (Embedding.subtype (λ n => 0 ≤ a n)), a k := by
              simp [Finset.sum_map]
            _ = ∑ k ∈ (Finset.range (N+1)).filter (λ n => 0 ≤ a n), a k := by
              simp [hF, Finset.subtype_map]
        have hF_bound : ∑ n' ∈ F, a n'.val ≤ M := by
          have htemp : ∑ n' ∈ F, a n'.val = ∑ n' ∈ F, |(fun (n : {n | a n ≥ 0}) ↦ a n.val) n'| := by
            refine Finset.sum_congr rfl (λ n' hn' => ?_)
            have hn_nonneg : a n'.val ≥ 0 := hF_nonneg n' hn'
            rw [abs_of_nonneg hn_nonneg]
          have htemp' : (∑ n' ∈ F, |(fun (n : {n | a n ≥ 0}) ↦ a n.val) n'|) ≤ M :=
            hM ⟨F, Set.mem_univ F, rfl⟩
          linarith
        have h_max_eq_filter : ∑ k ∈ Finset.range (N+1), a_plus k = ∑ k ∈ (Finset.range (N+1)).filter (λ n => 0 ≤ a n), a k := by
          calc
            ∑ k ∈ Finset.range (N+1), a_plus k = ∑ k ∈ Finset.range (N+1), (if 0 ≤ a k then a k else 0) := by
              refine Finset.sum_congr rfl (λ k hk => ?_)
              by_cases h : 0 ≤ a k
              · simp [a_plus, h]
              · simp [a_plus, show max (a k) 0 = 0 from max_eq_right (by linarith), h]
            _ = ∑ k ∈ (Finset.range (N+1)).filter (λ n => 0 ≤ a n), a k := by
              rw [← Finset.sum_filter]
        calc
          ∑ k ∈ Finset.range (N+1), a_plus k = ∑ k ∈ (Finset.range (N+1)).filter (λ n => 0 ≤ a n), a k := h_max_eq_filter
          _ = ∑ n' ∈ F, a n'.val := by symm; exact hF_sum_map
          _ ≤ M := hF_bound
      have h_nonneg_plus : (a_plus : Series).nonneg := by
        intro n
        by_cases hn : n ≥ 0
        · simp [a_plus, hn]
        · simp [a_plus, hn]
      have h_partial_bound (N : ℤ) : (a_plus : Series).partial N ≤ M := by
        by_cases hN : N ≥ 0
        · calc
            (a_plus : Series).partial N = (a_plus : Series).partial ((Int.toNat N : ℤ)) := by
              simp [Int.toNat_of_nonneg hN]
            _ = ∑ k ∈ Finset.range ((Int.toNat N) + 1), a_plus k := h_partial_range a_plus (Int.toNat N)
            _ ≤ M := h_max_bound (Int.toNat N)
        · have hm : (a_plus : Series).m = 0 := rfl
          have h_lt : N < 0 := by omega
          have h_zero : (a_plus : Series).partial N = 0 := Series.partial_of_lt (by rw [hm]; exact h_lt)
          rw [h_zero]
          exact hM_nonneg
      exact ((Series.converges_of_nonneg_iff h_nonneg_plus).mpr ⟨M, h_partial_bound⟩)
  have h_minus_conv (hneg : AbsConvergent (fun n : {n | a n < 0} ↦ a n)) : (a_minus : Series).converges := by
    by_cases hfin : Finite {n | a n < 0}
    · rcases hneg with ⟨g, hg_bij, hg_conv⟩
      have hfinite_ℕ : Finite ℕ := Finite.of_injective g hg_bij.1
      have hinfinite_ℕ : Infinite ℕ := by infer_instance
      exfalso; exact hinfinite_ℕ.not_finite hfinite_ℕ
    · have h_inf : Infinite {n | a n < 0} := not_finite_iff_infinite.mp hfin
      have h_countably_inf : CountablyInfinite {n | a n < 0} := Nat.countable_of_infinite {n | a n < 0}
      have hneg' : AbsConvergent' (fun n : {n | a n < 0} ↦ -(a n)) := by
        have h_smul := Sum'.smul
          (((AbsConvergent'.of_countable h_countably_inf).mpr hneg) : AbsConvergent' (fun n : {n | a n < 0} ↦ a n)) (-1)
        have : (-1 : ℝ) • (fun n : {n | a n < 0} ↦ a n) = (fun n : {n | a n < 0} ↦ -(a n)) := by
          ext n; rw [Pi.smul_apply, smul_eq_mul]; simp
        rw [this] at h_smul
        exact h_smul.1
      rcases hneg' with ⟨M, hM⟩
      have hM_nonneg : 0 ≤ M := by
        have hzero_sum : ∑ x ∈ (∅ : Finset {n | a n < 0}), |a (x : ℕ)| = (0 : ℝ) := by
          simpa using (Finset.sum_empty (f := λ (x : {n | a n < 0}) => |a (x : ℕ)|))
        have hzero_mem : (0 : ℝ) ∈ (fun A : Finset {n | a n < 0} ↦ ∑ x ∈ A, |(fun n : {n | a n < 0} ↦ -(a n)) x|) '' Set.univ := by
          refine ⟨(∅ : Finset {n | a n < 0}), Set.mem_univ ∅, ?_⟩
          calc
            (fun A : Finset {n | a n < 0} ↦ ∑ x ∈ A, |(fun n : {n | a n < 0} ↦ -(a n)) x|) ∅
                = ∑ x ∈ (∅ : Finset {n | a n < 0}), |a (x : ℕ)| := by
                  simp
            _ = (0 : ℝ) := hzero_sum
        exact hM hzero_mem
      have h_max_bound (N : ℕ) : ∑ k ∈ Finset.range (N+1), a_minus k ≤ M := by
        set F : Finset {n | a n < 0} := (Finset.range (N+1)).subtype (λ n => a n < 0) with hF
        have hF_nonneg (n' : {n | a n < 0}) (hn' : n' ∈ F) : -(a n'.val) ≥ 0 := by
          have : a n'.val < 0 := n'.property; linarith
        have hF_sum_map : ∑ n' ∈ F, (-(a n'.val)) = ∑ k ∈ (Finset.range (N+1)).filter (λ n => a n < 0), (-(a k)) := by
          calc
            ∑ n' ∈ F, (-(a n'.val)) = ∑ k ∈ F.map (Embedding.subtype (λ n => a n < 0)), (-(a k)) := by
              simp [Finset.sum_map]
            _ = ∑ k ∈ (Finset.range (N+1)).filter (λ n => a n < 0), (-(a k)) := by
              simp [hF, Finset.subtype_map]
        have hF_bound : ∑ n' ∈ F, (-(a n'.val)) ≤ M := by
          have htemp : ∑ n' ∈ F, (-(a n'.val)) = ∑ n' ∈ F, |(fun (n : {n | a n < 0}) ↦ -(a n.val)) n'| := by
            refine Finset.sum_congr rfl (λ n' hn' => ?_)
            have hn_nonneg : -(a n'.val) ≥ 0 := hF_nonneg n' hn'
            rw [abs_of_nonneg hn_nonneg]
          have htemp' : (∑ n' ∈ F, |(fun (n : {n | a n < 0}) ↦ -(a n.val)) n'|) ≤ M :=
            hM ⟨F, Set.mem_univ F, rfl⟩
          linarith
        have h_max_eq_filter : ∑ k ∈ Finset.range (N+1), a_minus k = ∑ k ∈ (Finset.range (N+1)).filter (λ n => a n < 0), (-(a k)) := by
          calc
            ∑ k ∈ Finset.range (N+1), a_minus k = ∑ k ∈ Finset.range (N+1), (if 0 ≤ -(a k) then -(a k) else 0) := by
              refine Finset.sum_congr rfl (λ k hk => ?_)
              by_cases h : 0 ≤ -(a k)
              · simp [a_minus, h]
              · have h' : a k ≥ 0 := by linarith
                simp [a_minus, h, h']
            _ = ∑ k ∈ Finset.range (N+1), (if a k < 0 then -(a k) else 0) := by
              refine Finset.sum_congr rfl (λ k hk => ?_)
              by_cases h : a k < 0
              · have : 0 ≤ -(a k) := by linarith
                simp [h, this]
              · by_cases hpos : 0 ≤ -(a k)
                · have h_eq : a k = 0 := by linarith
                  simp [h, hpos, h_eq]
                · simp [h, hpos]
            _ = ∑ k ∈ (Finset.range (N+1)).filter (λ n => a n < 0), (-(a k)) := by
              rw [← Finset.sum_filter]
        calc
          ∑ k ∈ Finset.range (N+1), a_minus k = ∑ k ∈ (Finset.range (N+1)).filter (λ n => a n < 0), (-(a k)) := h_max_eq_filter
          _ = ∑ n' ∈ F, (-(a n'.val)) := by symm; exact hF_sum_map
          _ ≤ M := hF_bound
      have h_nonneg_minus : (a_minus : Series).nonneg := by
        intro n
        by_cases hn : n ≥ 0
        · simp [a_minus, hn]
        · simp [a_minus, hn]
      have h_partial_bound (N : ℤ) : (a_minus : Series).partial N ≤ M := by
        by_cases hN : N ≥ 0
        · calc
            (a_minus : Series).partial N = (a_minus : Series).partial ((Int.toNat N : ℤ)) := by
              simp [Int.toNat_of_nonneg hN]
            _ = ∑ k ∈ Finset.range ((Int.toNat N) + 1), a_minus k := h_partial_range a_minus (Int.toNat N)
            _ ≤ M := h_max_bound (Int.toNat N)
        · have hm : (a_minus : Series).m = 0 := rfl
          have h_lt : N < 0 := by omega
          have h_zero : (a_minus : Series).partial N = 0 := Series.partial_of_lt (by rw [hm]; exact h_lt)
          rw [h_zero]
          exact hM_nonneg
      exact ((Series.converges_of_nonneg_iff h_nonneg_minus).mpr ⟨M, h_partial_bound⟩)
  have hpos_not : ¬ AbsConvergent (fun n : {n | a n ≥ 0} ↦ a n) := by
    intro hpos
    have h_plus : (a_plus : Series).converges := h_plus_conv hpos
    have h_neg : (a_minus : Series).converges := by
      have h_sub : ((a_plus : Series) - (a : Series)).converges :=
        (Series.sub h_plus ha).1
      simpa [h_sub_eq] using h_sub
    have h_abs_conv : (a : Series).absConverges := by
      have h_add_conv : ((a_plus : Series) + (a_minus : Series)).converges := (Series.add h_plus h_neg).1
      unfold Series.absConverges
      rw [h_add_eq]
      exact h_add_conv
    exact ha' h_abs_conv
  have hneg_not : ¬ AbsConvergent (fun n : {n | a n < 0} ↦ a n) := by
    intro hneg
    have h_neg : (a_minus : Series).converges := h_minus_conv hneg
    have h_plus : (a_plus : Series).converges := by
      have h_add : ((a : Series) + (a_minus : Series)).converges :=
        (Series.add ha h_neg).1
      have h_identity : (a : Series) + (a_minus : Series) = (a_plus : Series) := by
        have hm : ((a : Series) + (a_minus : Series)).m = (a_plus : Series).m := by
          calc
            ((a : Series) + (a_minus : Series)).m = min ((a : Series).m) ((a_minus : Series).m) := rfl
            _ = min 0 0 := by simp
            _ = 0 := by simp
            _ = (a_plus : Series).m := by simp
        have hseq : ∀ n : ℤ, ((a : Series) + (a_minus : Series)).seq n = (a_plus : Series).seq n := by
          intro n
          by_cases hn : n ≥ 0
          · have h1 : ((a : Series) + (a_minus : Series)).seq n = a n.toNat + max (-(a n.toNat)) 0 := by
              calc
                ((a : Series) + (a_minus : Series)).seq n = ((a : Series).seq n) + ((a_minus : Series).seq n) := rfl
                _ = a n.toNat + max (-(a n.toNat)) 0 := by simp [a_minus, hn]
            have h2 : (a_plus : Series).seq n = max (a n.toNat) 0 := by
              simp [a_plus, hn]
            rw [h1, h2]
            by_cases hx_nonneg : a n.toNat ≥ 0
            · simp [hx_nonneg, show max (-(a n.toNat)) 0 = 0 from max_eq_right (by linarith)]
            · simp [hx_nonneg, show max (a n.toNat) 0 = 0 from max_eq_right (by linarith),
                show max (-(a n.toNat)) 0 = -(a n.toNat) from max_eq_left (by linarith)]
          · have hzero : ((a : Series) + (a_minus : Series)).seq n = 0 := by
              calc
                ((a : Series) + (a_minus : Series)).seq n = ((a : Series).seq n) + ((a_minus : Series).seq n) := rfl
                _ = 0 + 0 := by simp [hn]
                _ = 0 := by simp
            have hzero' : (a_plus : Series).seq n = 0 := by
              simp [hn]
            simp [hzero, hzero', hn]
        exact Series.ext hm (funext hseq)
      rw [h_identity] at h_add
      exact h_add
    have h_abs_conv : (a : Series).absConverges := by
      have h_add_conv : ((a_plus : Series) + (a_minus : Series)).converges := (Series.add h_plus h_neg).1
      unfold Series.absConverges
      rw [h_add_eq]
      exact h_add_conv
    exact ha' h_abs_conv
  exact ⟨hpos_not, hneg_not⟩

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
