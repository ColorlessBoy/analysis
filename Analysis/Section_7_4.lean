import Mathlib.Tactic
import Analysis.Section_7_3
open scoped Topology

namespace Chapter7

theorem Series.sum_eq_sum (b:ℕ → ℝ) {N:ℤ} (hN: N ≥ 0) : ∑ n ∈ .Icc 0 N, (if 0 ≤ n then b n.toNat else 0) = ∑ n ∈ .Iic N.toNat, b n := by
      convert Finset.sum_image (g := Int.ofNat) (by simp)
      ext x; simp; constructor
      . intro ⟨ _, _ ⟩; use x.toNat; omega
      grind

theorem Series.converges_of_permute_nonneg {a:ℕ → ℝ} (ha: (a:Series).nonneg) (hconv: (a:Series).converges)
  {f: ℕ → ℕ} (hf: Function.Bijective f) :
    (fun n ↦ a (f n) : Series).converges ∧ (a:Series).sum = (fun n ↦ a (f n) : Series).sum := by
  set af : ℕ → ℝ := fun n ↦ a (f n)
  have haf : (af:Series).nonneg := by
    intro n; by_cases h : n ≥ 0 <;> simp [h, af]
    specialize ha (f n.toNat); grind
  set S := (a:Series).partial
  set T := (af:Series).partial
  have hSmono : Monotone S := Series.partial_of_nonneg ha
  have hTmono : Monotone T := Series.partial_of_nonneg haf
  set L := iSup S
  set L' := iSup T
  have hSBound : ∃ Q, ∀ N, S N ≤ Q := (converges_of_nonneg_iff ha).mp hconv
  suffices : (∃ Q, ∀ M, T M ≤ Q) ∧ L = L'
  . have Ssum : L = (a:Series).sum := by
      symm; apply sum_of_converges; simp [convergesTo, L]
      apply tendsto_atTop_isLUB hSmono (isLUB_csSup _ _)
      . use (S 0); aesop
      choose Q hQ using hSBound; use Q; simp [upperBounds, hQ]
    have Tsum : L' = (af:Series).sum := by
      symm; apply sum_of_converges; simp [convergesTo, L']
      apply tendsto_atTop_isLUB hTmono (isLUB_csSup _ _)
      . use (T 0); aesop
      choose Q hQ using this.1; use Q; simp [upperBounds, hQ]
    simp [←Ssum, ←Tsum, this.2, converges_of_nonneg_iff haf]
    convert this.1
  have hTL (M:ℤ) : T M ≤ L := by
    by_cases hM : M ≥ 0
    swap
    . have hM' : M < 0 := by linarith
      simp [T, Series.partial, hM']
      convert le_ciSup (f := S) ?_ (-1)
      simp [BddAbove, Set.Nonempty, upperBounds, hSBound]
    set Y := Finset.Iic M.toNat
    have hN : ∃ N, ∀ m ∈ Y, f m ≤ N := by
      use (Y.image f).sup id; intro m hm
      apply Finset.le_sup (f := id); grind
    choose N hN using hN
    calc
      _ = ∑ m ∈ Y, af m := by simp [T, Series.partial, af]; exact sum_eq_sum af hM
      _ = ∑ n ∈ f '' Y, a n := by symm; convert Finset.sum_image (by solve_by_elim [hf.injective]); simp
      _ ≤ ∑ n ∈ .Iic N, a n := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro _ _; aesop
        intro i _ _; specialize ha i; aesop
      _ = S N := by simp [S, Series.partial]; symm; apply sum_eq_sum (N:=N) a; positivity
      _ ≤ L := by apply le_ciSup _ (N:ℤ); simp [BddAbove, Set.Nonempty, upperBounds, hSBound]
  have hTbound : ∃ Q, ∀ M, T M ≤ Q := by use L
  simp [hTbound]
  have hSL' (N:ℤ) : S N ≤ L' := by
    by_cases hN : N ≥ 0
    swap
    . have hN' : N < 0 := by linarith
      simp [S, Series.partial, hN']
      convert le_ciSup (f := T) ?_ (-1)
      simp [BddAbove, Set.Nonempty, upperBounds, hTbound]
    set X := Finset.Iic N.toNat
    have hM : ∃ M, ∀ n ∈ X, ∃ m, f m = n ∧ m ≤ M := by
      use (X.preimage f (Set.injOn_of_injective hf.1)).sup id
      intro n hn; choose m hm using hf.2 n
      refine ⟨ _, hm, ?_ ⟩
      apply Finset.le_sup (f := id)
      simp [Finset.mem_preimage, hm, hn]
    choose M hM using hM
    have sum_eq_sum (b:ℕ → ℝ) {N:ℤ} (hN: N ≥ 0)
      : ∑ n ∈ .Icc 0 N, (if 0 ≤ n then b n.toNat else 0) = ∑ n ∈ .Iic N.toNat, b n := by
      convert Finset.sum_image (g := Int.ofNat) (by simp)
      ext x; simp; constructor
      . intro ⟨ _, _ ⟩; use x.toNat; omega
      grind
    calc
      _ = ∑ n ∈ X, a n := by simp [S, sum_eq_sum, hN, X]
      _ = ∑ n ∈ ((Finset.Iic M).filter (f · ∈ X)).image f, a n := by
        congr; ext; simp; constructor
        . intro h; obtain ⟨ m, rfl, hm' ⟩ := hM _ h; use m
        rintro ⟨ _, ⟨ _, _⟩, rfl ⟩; simp_all
      _ ≤ ∑ m ∈ .Iic M, af m := by
        rw [Finset.sum_image (by solve_by_elim [hf.injective])]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        . aesop
        intro i _ _; specialize haf i; aesop
      _ = T M := by simp [T, Series.partial, af]; symm; apply sum_eq_sum af; positivity
      _ ≤ L' := by apply le_ciSup _ (M:ℤ); simp [BddAbove, Set.Nonempty, upperBounds, hTbound]
  linarith [ciSup_le hSL', ciSup_le hTL]

theorem Series.zeta_2_converges : (fun n:ℕ ↦ 1/(n+1:ℝ)^2 : Series).converges := by
  have h_qseries_conv : (mk' (m := 1) fun n ↦ 1 / (n:ℝ) ^ (2 : ℝ) : Series).converges :=
    (converges_qseries (2 : ℝ) (by norm_num : (2 : ℝ) > 0)).mpr (by norm_num : (2 : ℝ) > 1)
  have h_qseries_convTo : (mk' (m := 1) fun n ↦ 1 / (n:ℝ) ^ (2 : ℝ) : Series).convergesTo
    ((mk' (m := 1) fun n ↦ 1 / (n:ℝ) ^ (2 : ℝ) : Series).sum) :=
    convergesTo_sum h_qseries_conv
  set s := (mk' (m := 1) fun n ↦ 1 / (n:ℝ) ^ (2 : ℝ) : Series) with hs
  have h_shifted : (mk' (m := s.m + (-1 : ℤ)) (fun n ↦ s.seq (n - (-1 : ℤ)))).convergesTo s.sum :=
    shift h_qseries_convTo (-1 : ℤ)
  have h_series_eq : (mk' (m := s.m + (-1 : ℤ)) (fun n ↦ s.seq (n - (-1 : ℤ)))) = (fun n : ℕ ↦ 1/(n+1:ℝ)^2 : Series) := by
    apply Series.ext
    · simp [s]
    · ext n
      by_cases hn : n ≥ 0
      · have hcast : (n.toNat : ℝ) = (n : ℝ) := by exact mod_cast Int.toNat_of_nonneg hn
        simp [s, Series.mk', hn, hcast]
      · simp [s, Series.mk', hn]
  have h_convTo : (fun n : ℕ ↦ 1/(n+1:ℝ)^2 : Series).convergesTo s.sum := by
    rw [h_series_eq] at h_shifted
    exact h_shifted
  exact ⟨s.sum, h_convTo⟩

theorem Series.permuted_zeta_2_converges :
  (fun n:ℕ ↦ if Even n then 1/(n+2:ℝ)^2 else 1/(n:ℝ)^2 : Series).converges := by
  set f : ℕ → ℕ := fun n ↦ if Even n then n+1 else n-1
  set a : ℕ → ℝ := fun n ↦ 1/((n:ℝ)+1)^2
  have hf_bij : Function.Bijective f := by
    have h_invol : ∀ n, f (f n) = n := by
      intro n
      unfold f
      rcases Nat.even_or_odd n with (⟨k, hk⟩ | ⟨k, hk⟩)
      · have h_even : Even n := ⟨k, hk⟩
        have h_not_even_succ : ¬ Even (n+1) := by
          rw [hk]; intro h; rcases h with ⟨m, hm⟩; omega
        simp [h_even, h_not_even_succ]
      · have h_not_even : ¬ Even n := by
          rw [hk]; intro h; rcases h with ⟨m, hm⟩; omega
        have hnpos : 1 ≤ n := by omega
        have h_even_pred : Even (n-1) := by
          rw [hk]; refine ⟨k, ?_⟩; omega
        simp [h_not_even, h_even_pred, Nat.sub_add_cancel hnpos]
    have hinj : Function.Injective f := fun x y h ↦ by
      calc
        x = f (f x) := (h_invol x).symm
        _ = f (f y) := by rw [h]
        _ = y := h_invol y
    have hsurj : Function.Surjective f := fun y ↦ ⟨f y, h_invol y⟩
    exact ⟨hinj, hsurj⟩
  have ha_nonneg : (a:Series).nonneg := by
    intro n; positivity
  have ha_eq : (fun n ↦ a (f n)) = (fun n:ℕ ↦ if Even n then 1/(n+2:ℝ)^2 else 1/(n:ℝ)^2) := by
    ext n; unfold a f; by_cases h : Even n
    · simp [h]; ring
    · have hn : 1 ≤ n := by
        by_contra! H
        have hn0 : n = 0 := by omega
        have : Even n := by subst hn0; exact ⟨0, by simp⟩
        exact h this
      have hcast : ((n-1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
        rw [Nat.cast_sub hn, Nat.cast_one]; ring
      simp [h, hcast]
  have h_conv : (fun n ↦ a (f n) : Series).converges :=
    (converges_of_permute_nonneg ha_nonneg zeta_2_converges hf_bij).1
  have h_eq_series : (fun n ↦ a (f n) : Series) = (fun n:ℕ ↦ if Even n then 1/(n+2:ℝ)^2 else 1/(n:ℝ)^2 : Series) := by
    ext i; dsimp; by_cases hi : i ≥ 0
    · simpa [hi] using congr_fun ha_eq (i.toNat)
    · simp [hi]
  rw [h_eq_series] at h_conv
  exact h_conv

theorem Series.permuted_zeta_2_eq_zeta_2 :
  (fun n:ℕ ↦ if Even n then 1/(n+2:ℝ)^2 else 1/(n:ℝ)^2 : Series).sum = (fun n:ℕ ↦ 1/(n+1:ℝ)^2 : Series).sum := by
  set f : ℕ → ℕ := fun n ↦ if Even n then n+1 else n-1
  set a : ℕ → ℝ := fun n ↦ 1/((n:ℝ)+1)^2
  have hf_bij : Function.Bijective f := by
    have h_invol : ∀ n, f (f n) = n := by
      intro n; unfold f; rcases Nat.even_or_odd n with (⟨k, hk⟩ | ⟨k, hk⟩)
      · have h_even : Even n := ⟨k, hk⟩
        have h_not_even_succ : ¬ Even (n+1) := by
          rw [hk]; intro h; rcases h with ⟨m, hm⟩; omega
        simp [h_even, h_not_even_succ]
      · have h_not_even : ¬ Even n := by
          rw [hk]; intro h; rcases h with ⟨m, hm⟩; omega
        have hnpos : 1 ≤ n := by omega
        have h_even_pred : Even (n-1) := by
          rw [hk]; refine ⟨k, ?_⟩; omega
        simp [h_not_even, h_even_pred, Nat.sub_add_cancel hnpos]
    have hinj : Function.Injective f := fun x y h ↦ by
      calc
        x = f (f x) := (h_invol x).symm
        _ = f (f y) := by rw [h]
        _ = y := h_invol y
    have hsurj : Function.Surjective f := fun y ↦ ⟨f y, h_invol y⟩
    exact ⟨hinj, hsurj⟩
  have ha_nonneg : (a:Series).nonneg := by
    intro n; positivity
  have ha_eq : (fun n ↦ a (f n)) = (fun n:ℕ ↦ if Even n then 1/(n+2:ℝ)^2 else 1/(n:ℝ)^2) := by
    ext n; unfold a f; by_cases h : Even n
    · simp [h]; ring
    · have hn : 1 ≤ n := by
        by_contra! H
        have hn0 : n = 0 := by omega
        have : Even n := by subst hn0; exact ⟨0, by simp⟩
        exact h this
      have hcast : ((n-1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
        rw [Nat.cast_sub hn, Nat.cast_one]; ring
      simp [h, hcast]
  have h_perm := (converges_of_permute_nonneg ha_nonneg zeta_2_converges hf_bij).2
  calc
    (fun n:ℕ ↦ if Even n then 1/(n+2:ℝ)^2 else 1/(n:ℝ)^2 : Series).sum
        = (fun n ↦ a (f n) : Series).sum := by rw [ha_eq]
    _ = (a:Series).sum := h_perm.symm
    _ = (fun n:ℕ ↦ 1/(n+1:ℝ)^2 : Series).sum := by
      simp [a]

theorem Series.absConverges_of_permute {a:ℕ → ℝ} (ha : (a:Series).absConverges)
  {f: ℕ → ℕ} (hf: Function.Bijective f) :
    (fun n ↦ a (f n):Series).absConverges  ∧ (a:Series).sum = (fun n ↦ a (f n) : Series).sum := by
  set L := (a:Series).abs.sum
  have hconv := converges_of_absConverges ha
  unfold absConverges at ha
  have habs : (fun n ↦ |a (f n)| : Series).converges ∧ L = (fun n ↦ |a (f n)| : Series).sum := by
    convert converges_of_permute_nonneg (a := fun n ↦ |a n|) _ _ hf using 3
    . simp; ext n; by_cases n ≥ 0 <;> grind
    . intro n; by_cases h: n ≥ 0 <;> simp [h]
    convert ha with n; by_cases n ≥ 0 <;> grind
  set L' := (a:Series).sum
  set af : ℕ → ℝ := fun n ↦ a (f n)
  suffices : (af:Series).convergesTo L'
  . simp [sum_of_converges this, absConverges]
    convert habs.1 with n; by_cases n ≥ 0 <;> grind
  simp [convergesTo, LinearOrderedAddCommGroup.tendsto_nhds]
  intro ε hε
  rw [converges_iff_tail_decay] at ha
  choose N₁ hN₁ ha using ha _ (half_pos hε); simp at hN₁
  have : ∃ N ≥ N₁, |(a:Series).partial N - L'| < ε/2 := by
    apply convergesTo_sum at hconv
    simp [convergesTo, LinearOrderedAddCommGroup.tendsto_nhds] at hconv
    choose N hN using hconv _ (half_pos hε)
    use max N N₁, (by grind); apply hN; grind
  choose N hN hN2 using this
  have hNpos : N ≥ 0 := by linarith
  let finv : ℕ → ℕ := Function.invFun f
  have : ∃ M, ∀ n ≤ N.toNat, finv n ≤ M := by
    use ((Finset.Iic (N.toNat)).image finv).sup id
    intro n hn
    apply Finset.le_sup (f := id); simp [Finset.mem_image]; use n, hn; rfl
  choose M hM using this; use M; intro M' hM'
  have hM'_pos : M' ≥ 0 := by linarith
  have why : (Finset.Iic M'.toNat).image f ⊇ .Iic N.toNat := by
    intro n hn
    rw [Finset.mem_image]
    have hn' : n ≤ N.toNat := Finset.mem_Iic.mp hn
    have h_finv_le_M : finv n ≤ M := hM n hn'
    have h_finv_le_M' : (finv n : ℤ) ≤ M' := by
      calc
        (finv n : ℤ) ≤ (M : ℤ) := by exact_mod_cast h_finv_le_M
        _ ≤ M' := hM'
    have h_finv_le_M'nat : finv n ≤ M'.toNat := by
      have hM'_nonneg : 0 ≤ M' := by linarith
      omega
    refine ⟨finv n, Finset.mem_Iic.mpr h_finv_le_M'nat, ?_⟩
    exact Function.invFun_eq (hf.2 n)
  set X : Finset ℕ := (Finset.Iic M'.toNat).image f \ .Iic N.toNat
  have claim : ∑ m ∈ .Iic M'.toNat, a (f m) = ∑ n ∈ .Iic N.toNat, a n + ∑ n ∈ X, a n := calc
    _ = ∑ n ∈ (Finset.Iic M'.toNat).image f , a n := by
      symm; apply Finset.sum_image; solve_by_elim [hf.1]
    _ = _ := by
      convert Finset.sum_union _ using 2
      . simp [X, why]
      . infer_instance
      rw [Finset.disjoint_right]; intro n hn; simp only [X, Finset.mem_sdiff] at hn; tauto
  choose q' hq using X.bddAbove
  set q := max q' N.toNat
  have why2 : X ⊆ Finset.Icc (N.toNat+1) q := by
    intro x hx
    rcases Finset.mem_sdiff.mp hx with ⟨hx_image, hx_not⟩
    have hx_gt_N : x > N.toNat := by
      rw [Finset.mem_Iic] at hx_not; omega
    have hx_le_q' : x ≤ q' := hq hx
    have hx_le_q : x ≤ q := le_trans hx_le_q' (by dsimp [q]; exact le_max_left _ _)
    exact Finset.mem_Icc.mpr ⟨by omega, hx_le_q⟩
  have claim2 : |∑ n ∈ X, a n| ≤ ε/2 := calc
    _ ≤ ∑ n ∈ X, |a n| := X.abs_sum_le_sum_abs a
    _ ≤ ∑ n ∈ .Icc (N.toNat+1) q, |a n| := by
      apply Finset.sum_le_sum_of_subset_of_nonneg why2; simp
    _ ≤ ε/2 := by
      convert ha (N.toNat+1) _ q _ <;> try omega
      simp [hNpos]; rw [abs_of_nonneg (by positivity)]; symm
      convert Finset.sum_image (g := fun (n:ℕ) ↦ (n:ℤ)) (by simp) using 2
      ext x; simp; constructor
      . intro ⟨ _, _ ⟩; use x.toNat; omega
      grind
  calc
    _ ≤ |(af:Series).partial M' - (a:Series).partial N| + |(a:Series).partial N - L'| := abs_sub_le _ _ _
    _ < |(af:Series).partial M' - (a:Series).partial N| + ε/2 := by gcongr
    _ ≤ ε/2 + ε/2 := by
      gcongr; convert claim2
      simp [Series.partial, sum_eq_sum _ hM'_pos, sum_eq_sum _ hNpos]; grind
    _ = ε := by ring

noncomputable abbrev Series.a_7_4_4 : ℕ → ℝ := fun n ↦ (-1:ℝ)^n / (n+2)

theorem Series.ex_7_4_4_conv : (a_7_4_4 : Series).converges := by
  set a : { n : ℤ // n ≥ 0 } → ℝ := fun n => 1 / ((n.val : ℝ) + 2)
  have h_nonneg : ∀ n, a n ≥ 0 := by
    intro n
    dsimp [a]
    have hn_nonneg : (0 : ℝ) ≤ (n.val : ℝ) := by exact mod_cast n.property
    positivity
  have h_anti : Antitone a := by
    intro x y h
    have hxpos : 0 < (x.val : ℝ) + 2 := by
      have hx_nonneg : (0 : ℝ) ≤ (x.val : ℝ) := by exact mod_cast x.property
      nlinarith
    have hypos : 0 < (y.val : ℝ) + 2 := by
      have hy_nonneg : (0 : ℝ) ≤ (y.val : ℝ) := by exact mod_cast y.property
      nlinarith
    have hval : (x.val : ℝ) ≤ (y.val : ℝ) := by exact mod_cast h
    rcases hval.eq_or_lt with (h_eq | h_lt)
    · have h_eq' : x = y := Subtype.ext (by exact_mod_cast h_eq)
      rw [h_eq']
    · exact ((one_div_lt_one_div hypos hxpos).mpr (by nlinarith)).le
  have h_tendsto : Filter.atTop.Tendsto a (nhds 0) := by
    haveI : Nonempty { n : ℤ // n ≥ 0 } := ⟨⟨0, le_refl 0⟩⟩
    rw [Metric.tendsto_nhds]
    intro ε hε
    rcases exists_nat_gt (1 / ε) with ⟨K, hK⟩
    have hKpos : (0 : ℝ) < (K : ℝ) := by
      have hpos : 0 < 1 / ε := div_pos (by norm_num) hε
      linarith
    refine Filter.eventually_atTop.mpr ⟨⟨(K : ℤ), by omega⟩, ?_⟩
    intro n hn
    have hn_val : (K : ℤ) ≤ n.val := hn
    have hn_nonneg : (0 : ℝ) ≤ (n.val : ℝ) := by exact mod_cast n.property
    rw [Real.dist_eq, sub_zero]
    have ha_nonneg_n : 0 ≤ a n := h_nonneg n
    rw [abs_of_nonneg ha_nonneg_n]
    dsimp [a]
    have hnpos : (0 : ℝ) < (n.val : ℝ) + 2 := by nlinarith
    have hKpos' : (0 : ℝ) < (K : ℝ) + 2 := by nlinarith
    calc
      1 / ((n.val : ℝ) + 2) ≤ 1 / ((K : ℝ) + 2) := by
        refine (one_div_le_one_div ?_ ?_).mpr ?_
        · exact hnpos
        · exact hKpos'
        · have : (n.val : ℝ) ≥ (K : ℝ) := by exact mod_cast hn_val
          nlinarith
      _ < 1 / (K : ℝ) := by
        refine (one_div_lt_one_div (by nlinarith) (by nlinarith)).mpr (by nlinarith)
      _ < ε := by
        have h_one_div_ε_pos : 0 < 1 / ε := div_pos (by norm_num) hε
        have h_eq' : 1 / (1 / ε) = ε := by field_simp [hε.ne.symm]
        have h_temp : (1 : ℝ) / (K : ℝ) < 1 / (1 / ε) :=
          ((one_div_lt_one_div hKpos h_one_div_ε_pos).mpr hK)
        rw [h_eq'] at h_temp
        exact h_temp
  have h_alt := (converges_of_alternating h_nonneg h_anti).mpr h_tendsto
  have h_eq : (a_7_4_4 : Series) = mk' (fun (n : { n : ℤ // n ≥ 0 }) => (-1 : ℝ) ^ (n : ℤ) * a n) := by
    ext n
    dsimp [a, a_7_4_4, Series.mk']
    by_cases h : n ≥ 0
    · simp [h]
      have h_toNat_eq : ((n : ℤ).toNat : ℝ) = (n : ℝ) := by
        exact mod_cast (Int.toNat_of_nonneg h : ((n : ℤ).toNat : ℤ) = n)
      have h_pow_eq : (-1 : ℝ) ^ ((n : ℤ).toNat) = (-1 : ℝ) ^ (n : ℤ) := by
        calc
          (-1 : ℝ) ^ ((n : ℤ).toNat) = (-1 : ℝ) ^ (((n : ℤ).toNat : ℕ) : ℤ) := by
            symm; exact zpow_natCast (-1 : ℝ) ((n : ℤ).toNat)
          _ = (-1 : ℝ) ^ (n : ℤ) := by
            rw [show (((n : ℤ).toNat : ℕ) : ℤ) = n from by exact_mod_cast Int.toNat_of_nonneg h]
      calc
        (-1 : ℝ) ^ ((n : ℤ).toNat) / (((n : ℤ).toNat : ℝ) + 2) = (-1 : ℝ) ^ ((n : ℤ).toNat) / ((n : ℝ) + 2) := by simp [h_toNat_eq]
        _ = (-1 : ℝ) ^ (n : ℤ) / ((n : ℝ) + 2) := by rw [h_pow_eq]
        _ = (-1 : ℝ) ^ (n : ℤ) * (1 / ((n : ℝ) + 2)) := by ring
    · simp [h]
  rw [← h_eq] at h_alt
  exact h_alt

theorem Series.ex_7_4_4_sum : (a_7_4_4 : Series).sum > 0 := by
  dsimp [Series.a_7_4_4]
  let s : Series := {
    m := 0
    seq := fun n : ℤ => if n ≥ 0 then (-1 : ℝ) ^ (n.toNat : ℕ) / ((n.toNat : ℝ) + 2) else 0
    vanish := by
      intro n hn
      have : ¬(n ≥ 0) := by omega
      simp [this]
  }
  change s.sum > 0
  have hm : s.m = 0 := rfl
  have hconv : s.converges := by
    simpa [Series.a_7_4_4] using ex_7_4_4_conv
  have hconvTo : s.convergesTo s.sum := convergesTo_sum hconv
  have hpartial1 : s.partial (1 : ℤ) = 1/6 := by
    unfold Series.partial
    have hIcc : Finset.Icc (0 : ℤ) (1 : ℤ) = {(0 : ℤ), 1} := by decide
    rw [hIcc]
    simp
    calc
      s.seq (0 : ℤ) + s.seq (1 : ℤ) = (1/2 : ℝ) + (-1/3 : ℝ) := by
        dsimp [s, Series.a_7_4_4]
        norm_num
      _ = 1/6 := by ring
    norm_num
  have hpos1 : s.partial (1 : ℤ) > 0 := by
    rw [hpartial1]; norm_num
  have h_seq_sq2 (k : ℕ) : s.seq (2*(k:ℤ)+2 : ℤ) = 1/((2*(k:ℝ)+4 : ℝ)) := by
    have hpos : 2*(k:ℤ)+2 ≥ (0 : ℤ) := by omega
    have htoNat : ((2*(k:ℤ)+2 : ℤ).toNat : ℕ) = 2*k+2 := by omega
    dsimp [s, Series.a_7_4_4]
    simp [hpos, htoNat]
    have hpower : (-1 : ℝ) ^ (2*k+2 : ℕ) = 1 := by
      calc
        (-1 : ℝ) ^ (2*k+2 : ℕ) = ((-1 : ℝ) ^ (2 : ℕ)) ^ (k+1 : ℕ) := by
          rw [← pow_mul, show (2 : ℕ)*(k+1 : ℕ) = 2*k+2 by omega]
        _ = (1 : ℝ) ^ (k+1 : ℕ) := by norm_num
        _ = 1 := by simp
    rw [hpower]
    ring
  have h_seq_sq3 (k : ℕ) : s.seq (2*(k:ℤ)+3 : ℤ) = -1/((2*(k:ℝ)+5 : ℝ)) := by
    have hpos : 2*(k:ℤ)+3 ≥ (0 : ℤ) := by omega
    have htoNat : ((2*(k:ℤ)+3 : ℤ).toNat : ℕ) = 2*k+3 := by omega
    dsimp [s, Series.a_7_4_4]
    simp [hpos, htoNat]
    have hpower2 : (-1 : ℝ) ^ (2*k+2 : ℕ) = 1 := by
      calc
        (-1 : ℝ) ^ (2*k+2 : ℕ) = ((-1 : ℝ) ^ (2 : ℕ)) ^ (k+1 : ℕ) := by
          rw [← pow_mul, show (2 : ℕ)*(k+1 : ℕ) = 2*k+2 by omega]
        _ = (1 : ℝ) ^ (k+1 : ℕ) := by norm_num
        _ = 1 := by simp
    have hpower3 : (-1 : ℝ) ^ (2*k+3 : ℕ) = -1 := by
      calc
        (-1 : ℝ) ^ (2*k+3 : ℕ) = (-1 : ℝ) ^ (2*k+2 : ℕ) * (-1 : ℝ) := by
          simpa [add_assoc] using pow_succ' (-1 : ℝ) (2*k+2 : ℕ)
        _ = 1 * (-1 : ℝ) := by rw [hpower2]
        _ = -1 := by simp
    rw [hpower3]
    ring
  have h_odd_incr : ∀ (k : ℕ), s.partial (2*(k:ℤ)+1 : ℤ) < s.partial (2*(k:ℤ)+3 : ℤ) := by
    intro k
    have hN1 : (2*(k:ℤ)+1 : ℤ) ≥ s.m - 1 := by rw [hm]; omega
    have hN2 : (2*(k:ℤ)+2 : ℤ) ≥ s.m - 1 := by rw [hm]; omega
    have h_sum_pos : s.seq (2*(k:ℤ)+2 : ℤ) + s.seq (2*(k:ℤ)+3 : ℤ) > 0 := by
      rw [h_seq_sq2 k, h_seq_sq3 k]
      have h_denom1 : (2*(k:ℝ)+4 : ℝ) ≠ 0 := by nlinarith
      have h_denom2 : (2*(k:ℝ)+5 : ℝ) ≠ 0 := by nlinarith
      have h_eq : 1/(2*(k:ℝ)+4) + (-1/(2*(k:ℝ)+5)) = 1 / ((2*(k:ℝ)+4)*(2*(k:ℝ)+5)) := by
        field_simp [h_denom1, h_denom2]
        ring
      rw [h_eq]
      positivity
    calc
      s.partial (2*(k:ℤ)+1 : ℤ) < s.partial (2*(k:ℤ)+1 : ℤ) + (s.seq (2*(k:ℤ)+2 : ℤ) + s.seq (2*(k:ℤ)+3 : ℤ)) := by
        nlinarith
      _ = (s.partial (2*(k:ℤ)+1 : ℤ) + s.seq (2*(k:ℤ)+2 : ℤ)) + s.seq (2*(k:ℤ)+3 : ℤ) := by ring
      _ = s.partial (2*(k:ℤ)+2 : ℤ) + s.seq (2*(k:ℤ)+3 : ℤ) := by
        have htemp : s.partial (2*(k:ℤ)+1 : ℤ) + s.seq (2*(k:ℤ)+2 : ℤ) = s.partial (2*(k:ℤ)+2 : ℤ) := by
          have h_arg : (2*(k:ℤ)+2 : ℤ) = (((2*(k:ℤ)+1 : ℤ) + 1) : ℤ) := by ring
          calc
            s.partial (2*(k:ℤ)+1 : ℤ) + s.seq (2*(k:ℤ)+2 : ℤ)
                = s.partial (2*(k:ℤ)+1 : ℤ) + s.seq (((2*(k:ℤ)+1 : ℤ) + 1) : ℤ) := by rw [h_arg]
            _ = s.partial (((2*(k:ℤ)+1 : ℤ) + 1) : ℤ) := by rw [← Series.partial_succ s hN1]
            _ = s.partial (2*(k:ℤ)+2 : ℤ) := by ring
        rw [htemp]
      _ = s.partial (2*(k:ℤ)+3 : ℤ) := by
        have htemp : s.partial (2*(k:ℤ)+2 : ℤ) + s.seq (2*(k:ℤ)+3 : ℤ) = s.partial (2*(k:ℤ)+3 : ℤ) := by
          have h_arg : (2*(k:ℤ)+3 : ℤ) = (((2*(k:ℤ)+2 : ℤ) + 1) : ℤ) := by ring
          calc
            s.partial (2*(k:ℤ)+2 : ℤ) + s.seq (2*(k:ℤ)+3 : ℤ)
                = s.partial (2*(k:ℤ)+2 : ℤ) + s.seq (((2*(k:ℤ)+2 : ℤ) + 1) : ℤ) := by rw [h_arg]
            _ = s.partial (((2*(k:ℤ)+2 : ℤ) + 1) : ℤ) := by rw [← Series.partial_succ s hN2]
            _ = s.partial (2*(k:ℤ)+3 : ℤ) := by ring
        rw [htemp]
  have h_odd_ge_first : ∀ (k : ℕ), s.partial (1 : ℤ) ≤ s.partial (2*(k:ℤ)+1 : ℤ) := by
    intro k
    induction' k with k ih
    · rfl
    · have h_incr : s.partial (2*(k:ℤ)+1 : ℤ) < s.partial (2*(k:ℤ)+3 : ℤ) := h_odd_incr k
      exact le_trans ih (le_of_lt h_incr)
  have h_odd_conv : Filter.Tendsto (fun (k : ℕ) => s.partial (2*(k:ℤ)+1 : ℤ)) Filter.atTop (nhds s.sum) :=
    hconvTo.comp (by
      refine Filter.tendsto_atTop_atTop.mpr ?_
      intro N
      by_cases hN_nonneg : N ≥ 0
      · use N.toNat
        intro m hm
        have hm' : (m : ℤ) ≥ (N.toNat : ℤ) := by exact mod_cast hm
        have h_eq : (N.toNat : ℤ) = N := by exact mod_cast Int.toNat_of_nonneg hN_nonneg
        nlinarith
      · use 0
        intro m hm
        omega)
  have h_event : ∀ᶠ (k : ℕ) in Filter.atTop, s.partial (1 : ℤ) ≤ s.partial (2*(k:ℤ)+1 : ℤ) := by
    apply Filter.eventually_atTop.mpr
    exact ⟨0, λ k hk => h_odd_ge_first k⟩
  have h_sum_ge_partial1 : s.partial (1 : ℤ) ≤ s.sum :=
    ge_of_tendsto h_odd_conv h_event
  linarith

abbrev Series.f_7_4_4 : ℕ → ℕ := fun n ↦ if n % 3 = 0 then 2 * (n/3) else 4 * (n/3) + 2 * (n % 3) - 1

theorem Series.f_7_4_4_bij : Function.Bijective f_7_4_4 := by
  have hinj : Function.Injective f_7_4_4 := by
    intro x y h
    have hx_cases : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by
      have h := Nat.mod_lt x (by norm_num : 0 < 3); omega
    have hy_cases : y % 3 = 0 ∨ y % 3 = 1 ∨ y % 3 = 2 := by
      have h := Nat.mod_lt y (by norm_num : 0 < 3); omega
    rcases hx_cases with (hx0 | hx1 | hx2)
    · have hfx : f_7_4_4 x = 2*(x/3) := by unfold f_7_4_4; simp [hx0]
      rcases hy_cases with (hy0 | hy1 | hy2)
      · have hfy : f_7_4_4 y = 2*(y/3) := by unfold f_7_4_4; simp [hy0]
        rw [hfx, hfy] at h; omega
      · have hfy : f_7_4_4 y = 4*(y/3) + 1 := by
          unfold f_7_4_4
          rw [if_neg (by omega : y % 3 ≠ 0), hy1]; omega
        rw [hfx, hfy] at h; omega
      · have hfy : f_7_4_4 y = 4*(y/3) + 3 := by
          unfold f_7_4_4
          rw [if_neg (by omega : y % 3 ≠ 0), hy2]; omega
        rw [hfx, hfy] at h; omega
    · have hfx : f_7_4_4 x = 4*(x/3) + 1 := by
        unfold f_7_4_4
        rw [if_neg (by omega : x % 3 ≠ 0), hx1]; omega
      rcases hy_cases with (hy0 | hy1 | hy2)
      · have hfy : f_7_4_4 y = 2*(y/3) := by unfold f_7_4_4; simp [hy0]
        rw [hfx, hfy] at h; omega
      · have hfy : f_7_4_4 y = 4*(y/3) + 1 := by
          unfold f_7_4_4
          rw [if_neg (by omega : y % 3 ≠ 0), hy1]; omega
        rw [hfx, hfy] at h; omega
      · have hfy : f_7_4_4 y = 4*(y/3) + 3 := by
          unfold f_7_4_4
          rw [if_neg (by omega : y % 3 ≠ 0), hy2]; omega
        rw [hfx, hfy] at h; omega
    · have hfx : f_7_4_4 x = 4*(x/3) + 3 := by
        unfold f_7_4_4
        rw [if_neg (by omega : x % 3 ≠ 0), hx2]; omega
      rcases hy_cases with (hy0 | hy1 | hy2)
      · have hfy : f_7_4_4 y = 2*(y/3) := by unfold f_7_4_4; simp [hy0]
        rw [hfx, hfy] at h; omega
      · have hfy : f_7_4_4 y = 4*(y/3) + 1 := by
          unfold f_7_4_4
          rw [if_neg (by omega : y % 3 ≠ 0), hy1]; omega
        rw [hfx, hfy] at h; omega
      · have hfy : f_7_4_4 y = 4*(y/3) + 3 := by
          unfold f_7_4_4
          rw [if_neg (by omega : y % 3 ≠ 0), hy2]; omega
        rw [hfx, hfy] at h; omega
  have hsurj : Function.Surjective f_7_4_4 := by
    intro y
    by_cases hy : y % 2 = 0
    · refine ⟨3*(y/2), ?_⟩
      calc
        f_7_4_4 (3*(y/2)) = 2 * ((3*(y/2))/3) := by
          unfold f_7_4_4
          have hmod : (3*(y/2)) % 3 = 0 := by omega
          simp [hmod]
        _ = 2*(y/2) := by
          have hdiv : (3*(y/2))/3 = y/2 := by omega
          rw [hdiv]
        _ = y := by omega
    · have hy_odd : y % 2 = 1 := by
        have h := Nat.mod_two_eq_zero_or_one y
        rcases h with (h | h)
        · exact absurd h hy
        · exact h
      by_cases hy1 : (y/2) % 2 = 0
      · have hy_mod4 : y % 4 = 1 := by omega
        refine ⟨3*(y/4) + 1, ?_⟩
        calc
          f_7_4_4 (3*(y/4) + 1) = 4 * ((3*(y/4)+1)/3) + 1 := by
            unfold f_7_4_4
            have hmod : (3*(y/4)+1) % 3 = 1 := by omega
            simp [hmod]
          _ = 4*(y/4) + 1 := by
            have hdiv : (3*(y/4)+1)/3 = y/4 := by omega
            rw [hdiv]
          _ = y := by omega
      · have hy_mod4 : y % 4 = 3 := by omega
        refine ⟨3*(y/4) + 2, ?_⟩
        calc
          f_7_4_4 (3*(y/4) + 2) = 4 * ((3*(y/4)+2)/3) + 3 := by
            unfold f_7_4_4
            have hmod : (3*(y/4)+2) % 3 = 2 := by omega
            simp [hmod]
          _ = 4*(y/4) + 3 := by
            have hdiv : (3*(y/4)+2)/3 = y/4 := by omega
            rw [hdiv]
          _ = y := by omega
  exact ⟨hinj, hsurj⟩

set_option maxHeartbeats 400000 in
theorem Series.ex_7_4_4'_conv : (fun n ↦ a_7_4_4 (f_7_4_4 n) :Series).converges := by
  set b : ℕ → ℝ := fun n ↦ a_7_4_4 (f_7_4_4 n)
  set T : ℕ → ℝ := fun k ↦ b (3*k) + b (3*k+1) + b (3*k+2)

  have hT_formula (k : ℕ) : T k = -1 / (((2*k+2 : ℕ) : ℝ) * ((4*k+3 : ℕ) : ℝ) * ((4*k+5 : ℕ) : ℝ)) := by
    dsimp [T, b]
    have ha0 : a_7_4_4 (f_7_4_4 (3*k)) = 1 / ((2*k+2 : ℕ) : ℝ) := by
      simp [a_7_4_4, f_7_4_4, show (3*k) % 3 = 0 by omega, show (3*k)/3 = k by omega]
    have ha1 : a_7_4_4 (f_7_4_4 (3*k+1)) = -1 / ((4*k+3 : ℕ) : ℝ) := by
      dsimp [a_7_4_4, f_7_4_4]
      have hmod : (3*k+1) % 3 = 1 := by omega
      have hdiv : (3*k+1)/3 = k := by omega
      simp [hmod, hdiv]
      have h_pow : (-1 : ℝ) ^ (4*k+1) = -1 := by
        calc
          (-1 : ℝ) ^ (4*k+1) = ((-1 : ℝ)^(2 : ℕ)) ^ (2*k) * (-1 : ℝ) := by
            rw [show 4*k+1 = 2*(2*k)+1 by omega, pow_succ, pow_mul]
          _ = 1 ^ (2*k) * (-1 : ℝ) := by norm_num
          _ = -1 := by simp
      rw [h_pow]
      ring
    have ha2 : a_7_4_4 (f_7_4_4 (3*k+2)) = -1 / ((4*k+5 : ℕ) : ℝ) := by
      dsimp [a_7_4_4, f_7_4_4]
      have hmod : (3*k+2) % 3 = 2 := by omega
      have hdiv : (3*k+2)/3 = k := by omega
      simp [hmod, hdiv]
      have h_pow : (-1 : ℝ) ^ (4*k+3) = -1 := by
        calc
          (-1 : ℝ) ^ (4*k+3) = ((-1 : ℝ)^(2 : ℕ)) ^ (2*k+1) * (-1 : ℝ) := by
            rw [show 4*k+3 = 2*(2*k+1)+1 by omega, pow_succ, pow_mul]
          _ = 1 ^ (2*k+1) * (-1 : ℝ) := by norm_num
          _ = -1 := by simp
      rw [h_pow]
      ring
    rw [ha0, ha1, ha2]
    push_cast
    field_simp
    ring

  have hT_bound (k : ℕ) : |T k| ≤ 1 / (((k : ℕ) : ℝ) + 1)^2 := by
    rw [hT_formula k]
    have hpos_denom : ((2*k+2 : ℕ) : ℝ) * ((4*k+3 : ℕ) : ℝ) * ((4*k+5 : ℕ) : ℝ) > 0 := by positivity
    have h_abs : |-1 / (((2*k+2 : ℕ) : ℝ) * ((4*k+3 : ℕ) : ℝ) * ((4*k+5 : ℕ) : ℝ))|
              = 1 / (((2*k+2 : ℕ) : ℝ) * ((4*k+3 : ℕ) : ℝ) * ((4*k+5 : ℕ) : ℝ)) := by
      rw [abs_div, abs_neg, abs_one, abs_of_pos hpos_denom]
    rw [h_abs]
    have h_denom_bound : ((2*k+2 : ℕ) : ℝ) * ((4*k+3 : ℕ) : ℝ) * ((4*k+5 : ℕ) : ℝ) ≥ (((k : ℕ) : ℝ) + 1)^2 := by
      push_cast
      have h1' : (2*k+2 : ℝ) ≥ (k : ℝ) + 1 := by nlinarith
      have h2' : (4*k+3 : ℝ) ≥ (k : ℝ) + 1 := by nlinarith
      have h3' : (4*k+5 : ℝ) ≥ (k : ℝ) + 1 := by nlinarith
      nlinarith
    have h_pos_rhs : (((k : ℕ) : ℝ) + 1)^2 > 0 := by
      have hk_nonneg : (0 : ℝ) ≤ (k : ℕ) := by exact mod_cast Nat.zero_le _
      nlinarith
    exact (one_div_le_one_div hpos_denom h_pos_rhs).mpr h_denom_bound

  have hT_abs_conv : (T : Series).absConverges := by
    have h_zeta2_conv : (fun n : ℕ ↦ 1 / (((n : ℕ) : ℝ) + 1)^2 : Series).converges := zeta_2_converges
    have hm : (T : Series).m = (fun n : ℕ ↦ 1 / (((n : ℕ) : ℝ) + 1)^2 : Series).m := by simp
    have hcomp : ∀ n ≥ (T : Series).m, |(T : Series).seq n| ≤ (fun n : ℕ ↦ 1 / (((n : ℕ) : ℝ) + 1)^2 : Series).seq n := by
      intro n hn
      have hn_nonneg : n ≥ 0 := by omega
      have hseq_T : (T : Series).seq n = T (Int.toNat n) := by simp [hn_nonneg]
      have hseq_zeta : (fun n : ℕ ↦ 1 / (((n : ℕ) : ℝ) + 1)^2 : Series).seq n = 1 / (((Int.toNat n : ℕ) : ℝ) + 1)^2 := by
        simp [hn_nonneg]
      have h_bound : |T (Int.toNat n)| ≤ 1 / (((Int.toNat n : ℕ) : ℝ) + 1)^2 := hT_bound (Int.toNat n)
      rw [hseq_T, hseq_zeta]
      exact h_bound
    exact (converges_of_le hm hcomp h_zeta2_conv).1

  have hT_conv : (T : Series).converges := converges_of_absConverges hT_abs_conv
  have hT_convTo : (T : Series).convergesTo ((T : Series).sum) := convergesTo_sum hT_conv
  set L := (T : Series).sum with hL_def

  have h_sum_nat (M : ℕ) : ∑ n ∈ Finset.range (3*M+3), b n = ∑ k ∈ Finset.range (M+1), T k := by
    induction' M with M IH
    · simp [T, b, Finset.sum_range_succ, f_7_4_4, a_7_4_4]
    · have h_expand : ∑ n ∈ Finset.range (3*(M+1)+3), b n = (∑ n ∈ Finset.range (3*M+3), b n) + (b (3*M+3) + b (3*M+4) + b (3*M+5)) := by
        calc
          ∑ n ∈ Finset.range (3*(M+1)+3), b n = ∑ n ∈ Finset.range ((3*M+3)+3), b n := by
            have : 3*(M+1)+3 = (3*M+3)+3 := by omega
            rw [this]
          _ = (∑ n ∈ Finset.range ((3*M+3)+2), b n) + b ((3*M+3)+2) := by rw [Finset.sum_range_succ]
          _ = ((∑ n ∈ Finset.range ((3*M+3)+1), b n) + b ((3*M+3)+1)) + b ((3*M+3)+2) := by rw [Finset.sum_range_succ]
          _ = (((∑ n ∈ Finset.range (3*M+3), b n) + b (3*M+3)) + b (3*M+4)) + b (3*M+5) := by
            rw [Finset.sum_range_succ]
          _ = (∑ n ∈ Finset.range (3*M+3), b n) + (b (3*M+3) + b (3*M+4) + b (3*M+5)) := by ring
      have h_T_M1 : T (M+1) = b (3*M+3) + b (3*M+4) + b (3*M+5) := by
        dsimp [T]
        have h1 : 3*(M+1 : ℕ) = 3*M+3 := by omega
        have h2 : 3*(M+1 : ℕ)+1 = 3*M+4 := by omega
        have h3 : 3*(M+1 : ℕ)+2 = 3*M+5 := by omega
        simp [h1, h2, h3]
      rw [h_expand, IH]
      have h_range_eq : Finset.range (M+2) = Finset.range ((M+1 : ℕ)+1) := by
        have h : M+2 = (M+1 : ℕ)+1 := by omega
        rw [h]
      rw [h_range_eq]
      simp [Finset.sum_range_succ, h_T_M1]

  have h_partial_sum_eq (M : ℕ) : (b : Series).partial (3*M+2 : ℤ) = (T : Series).partial (M : ℤ) := by
    have h_nonneg_3M2 : (3*M+2 : ℤ) ≥ 0 := by omega
    have h_nonneg_M : (M : ℤ) ≥ 0 := by exact mod_cast Nat.zero_le M
    have hIic_range (N : ℕ) : (Finset.Iic (N : ℕ) : Finset ℕ) = Finset.range (N+1) := by
      ext n; simp
    have h1 : (b : Series).partial (3*M+2 : ℤ) = ∑ n ∈ Finset.range (3*M+3), b n := by
      unfold Series.partial
      rw [Series.sum_eq_sum b h_nonneg_3M2]
      have h_cast : ((3*M+2 : ℤ).toNat : ℕ) = 3*M+2 := by omega
      rw [h_cast, hIic_range (3*M+2)]
    have h2 : (T : Series).partial (M : ℤ) = ∑ k ∈ Finset.range (M+1), T k := by
      unfold Series.partial
      rw [Series.sum_eq_sum T h_nonneg_M]
      have h_cast : ((M : ℤ).toNat : ℕ) = M := by omega
      rw [h_cast, hIic_range M]
    rw [h1, h2, h_sum_nat M]

  have h_partial_relations (m : ℕ) :
    (b : Series).partial (3*m : ℤ) = (T : Series).partial (m : ℤ) - b (3*m+1) - b (3*m+2) ∧
    (b : Series).partial (3*m+1 : ℤ) = (T : Series).partial (m : ℤ) - b (3*m+2) ∧
    (b : Series).partial (3*m+2 : ℤ) = (T : Series).partial (m : ℤ) := by
    have hm_sm_sub1 : (3*m : ℤ) ≥ (b : Series).m - 1 := by simp; omega
    have hm1_sm_sub1 : (3*m+1 : ℤ) ≥ (b : Series).m - 1 := by simp; omega
    have h_succ1 : (b : Series).partial (3*m+1 : ℤ) = (b : Series).partial (3*m : ℤ) + (b : Series).seq (3*m+1 : ℤ) :=
      partial_succ _ hm_sm_sub1
    have h_succ2 : (b : Series).partial (3*m+2 : ℤ) = (b : Series).partial (3*m+1 : ℤ) + (b : Series).seq (3*m+2 : ℤ) :=
      partial_succ _ hm1_sm_sub1
    have h_seq1 : (b : Series).seq (3*m+1 : ℤ) = b (3*m+1) := by
      have hn : (3*m+1 : ℤ) ≥ 0 := by omega
      simp [hn, show ((3*m+1 : ℤ).toNat : ℕ) = 3*m+1 by omega]
    have h_seq2 : (b : Series).seq (3*m+2 : ℤ) = b (3*m+2) := by
      have hn : (3*m+2 : ℤ) ≥ 0 := by omega
      simp [hn, show ((3*m+2 : ℤ).toNat : ℕ) = 3*m+2 by omega]
    have h_eq3 : (b : Series).partial (3*m+2 : ℤ) = (T : Series).partial (m : ℤ) := h_partial_sum_eq m
    have h_eq1 : (b : Series).partial (3*m : ℤ) = (T : Series).partial (m : ℤ) - b (3*m+1) - b (3*m+2) := by
      have h_sum : (b : Series).partial (3*m+2 : ℤ) = (b : Series).partial (3*m : ℤ) + b (3*m+1) + b (3*m+2) := by
        calc
          (b : Series).partial (3*m+2 : ℤ) = (b : Series).partial (3*m+1 : ℤ) + (b : Series).seq (3*m+2 : ℤ) := h_succ2
          _ = ((b : Series).partial (3*m : ℤ) + (b : Series).seq (3*m+1 : ℤ)) + (b : Series).seq (3*m+2 : ℤ) := by rw [h_succ1]
          _ = (b : Series).partial (3*m : ℤ) + b (3*m+1) + b (3*m+2) := by rw [h_seq1, h_seq2]
      rw [h_eq3] at h_sum
      linarith
    have h_eq2 : (b : Series).partial (3*m+1 : ℤ) = (T : Series).partial (m : ℤ) - b (3*m+2) := by
      have h_sum' : (b : Series).partial (3*m+2 : ℤ) = (b : Series).partial (3*m+1 : ℤ) + b (3*m+2) := by
        calc
          (b : Series).partial (3*m+2 : ℤ) = (b : Series).partial (3*m+1 : ℤ) + (b : Series).seq (3*m+2 : ℤ) := h_succ2
          _ = (b : Series).partial (3*m+1 : ℤ) + b (3*m+2) := by rw [h_seq2]
      rw [h_eq3] at h_sum'
      linarith
    exact ⟨h_eq1, h_eq2, h_eq3⟩

  have hb_bound_simple (n : ℕ) (hn : n ≥ 1) : |b n| ≤ 3 / (n : ℝ) := by
    have h_f_triple_bound : 3 * f_7_4_4 n ≥ n := by
      dsimp [f_7_4_4]
      split <;> omega
    have h1 : |b n| ≤ 1 / ((n : ℝ)/3 + 2) := by
      dsimp [b, a_7_4_4]
      have h_abs_val : |(-1 : ℝ) ^ (f_7_4_4 n) / ((f_7_4_4 n : ℝ) + 2)| = 1 / ((f_7_4_4 n : ℝ) + 2) := by
        have h_abs_pow : |(-1 : ℝ) ^ (f_7_4_4 n)| = 1 := by
          rw [abs_pow, abs_neg, abs_one, one_pow]
        have h_pos_denom : (f_7_4_4 n : ℝ) + 2 > 0 := by positivity
        rw [abs_div, h_abs_pow, abs_of_pos h_pos_denom]
      rw [h_abs_val]
      have hpos_f : 0 < (f_7_4_4 n : ℝ) + 2 := by positivity
      have hpos_div : 0 < (n : ℝ)/3 + 2 := by
        have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := by exact mod_cast Nat.zero_le n
        nlinarith
      apply (one_div_le_one_div hpos_f hpos_div).mpr
      have h_cast : (f_7_4_4 n : ℝ) + 2 ≥ (n : ℝ)/3 + 2 := by
        have : (3 : ℝ) * (f_7_4_4 n : ℝ) ≥ (n : ℝ) := by exact mod_cast h_f_triple_bound
        nlinarith
      exact h_cast
    have h2 : 1 / ((n : ℝ)/3 + 2) ≤ 3 / (n : ℝ) := by
      have hn_pos : (n : ℝ) > 0 := by exact mod_cast hn
      have h_denom_pos : (n : ℝ)/3 + 2 > 0 := by nlinarith
      calc
        1 / ((n : ℝ)/3 + 2) ≤ 1 / ((n : ℝ)/3) := by
          refine (one_div_le_one_div h_denom_pos (by nlinarith)).mpr ?_
          nlinarith
        _ = 3 / (n : ℝ) := by field_simp [hn_pos.ne.symm]
    exact h1.trans h2

  have hb_tendsto_zero : Filter.atTop.Tendsto b (nhds (0 : ℝ)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have h_arch : ∃ N : ℕ, (N : ℝ) > 3 / ε := exists_nat_gt (3 / ε)
    rcases h_arch with ⟨N, hN⟩
    set N' := max N 1 with hN'_def
    have hN'_pos_r : (N' : ℝ) > 0 := by
      dsimp [N']
      have hpos : (1 : ℕ) ≤ max N 1 := le_max_right _ _
      have hpos' : (max N 1 : ℕ) ≥ 1 := by omega
      exact mod_cast hpos'
    have hN'_gt_3_div_eps : (N' : ℝ) > 3 / ε := by
      have hN_gt : (N : ℝ) > 3 / ε := hN
      have hN'_ge_N : (N' : ℝ) ≥ (N : ℝ) := by
        dsimp [N']; exact mod_cast (le_max_left _ _)
      nlinarith
    have h_ineq : ∀ n : ℕ, n ≥ N' → 3 / (n : ℝ) < ε := by
      intro n hn
      have hn_pos : (0 : ℝ) < (n : ℝ) := by
        have hn0 : n ≠ 0 := by
          intro h; subst h; have : N' ≥ 1 := by
            dsimp [N']; omega
          omega
        exact mod_cast Nat.pos_of_ne_zero hn0
      have hN'_le_n : (N' : ℝ) ≤ (n : ℝ) := by exact mod_cast hn
      have h_mul_3_eps_N' : 3 < ε * (N' : ℝ) := by
        calc
          3 = (3 / ε) * ε := by field_simp [hε.ne.symm]
          _ < (N' : ℝ) * ε := by nlinarith
          _ = ε * (N' : ℝ) := mul_comm _ _
      have h_mul_3_eps_n : 3 < ε * (n : ℝ) := by nlinarith
      have hpos_n : (n : ℝ) > 0 := hn_pos
      field_simp [hpos_n.ne.symm]
      nlinarith
    refine Filter.eventually_atTop.mpr ⟨N', λ n hn => ?_⟩
    have hn1 : n ≥ 1 := by omega
    have h_bound : |b n| < ε := by
      calc
        |b n| ≤ 3 / (n : ℝ) := hb_bound_simple n hn1
        _ < ε := h_ineq n hn
    simpa [Real.dist_eq, sub_zero]

  have h_convTo : (b : Series).convergesTo L := by
    unfold Series.convergesTo
    rw [Metric.tendsto_nhds]
    intro ε hε
    have h_ε3 : ε/3 > 0 := by linarith
    have h_event_T : ∀ᶠ n in Filter.atTop, dist ((T : Series).partial n) L < ε/3 :=
      (Metric.tendsto_nhds.mp hT_convTo) (ε/3) h_ε3
    rcases Filter.eventually_atTop.mp h_event_T with ⟨K, hK⟩
    have h_event_b : ∀ᶠ n in Filter.atTop, dist (b n) (0 : ℝ) < ε/3 :=
      (Metric.tendsto_nhds.mp hb_tendsto_zero) (ε/3) h_ε3
    rcases Filter.eventually_atTop.mp h_event_b with ⟨M, hM⟩
    have hK' : ∀ (x : ℤ), K ≤ x → |(T : Series).partial x - L| < ε/3 := by
      intro x hx
      have h := hK x hx
      rw [Real.dist_eq] at h
      exact h
    have hM' : ∀ (x : ℕ), M ≤ x → |b x| < ε/3 := by
      intro x hx
      have h := hM x hx
      rw [Real.dist_eq, sub_zero] at h
      exact h
    set N := max (3*K : ℤ) (M : ℤ) with hN_def
    have hN_nonneg : N ≥ 0 := by
      dsimp [N]; omega
    apply Filter.eventually_atTop.mpr
    refine ⟨N, λ n hn => ?_⟩
    have hn_nonneg : n ≥ 0 := by omega
    set n' : ℕ := Int.toNat n with hn'_def
    have hn'_eq : (n' : ℤ) = n := by exact mod_cast Int.toNat_of_nonneg hn_nonneg
    have hn'_N : (n' : ℕ) ≥ N := by
      have : (n : ℤ) ≥ N := hn
      rw [← hn'_eq] at this
      exact mod_cast this
    set m := n' / 3 with hm_def
    have hm_val_K : (m : ℤ) ≥ K := by
      have h_bound : (n' : ℕ) ≥ 3*K := by
        have h1 : (3*K : ℤ) ≤ N := by
          dsimp [N]; omega
        have h2 : N ≤ (n' : ℤ) := by
          rw [hn'_eq]; exact hn
        omega
      omega
    rcases h_partial_relations m with ⟨h_eq_3m, h_eq_3m1, h_eq_3m2⟩
    have h_mod3 : n' % 3 = 0 ∨ n' % 3 = 1 ∨ n' % 3 = 2 := by omega
    have h_abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
      calc
        |x + y| = |x - (-y)| := by ring
        _ ≤ |x| + |-y| := abs_sub _ _
        _ = |x| + |y| := by simp
    have h_diff : |(b : Series).partial n - L| < ε := by
      rw [← hn'_eq]
      rcases h_mod3 with (h | h | h)
      · -- n' = 3*m
        have hn'_eq_mul : n' = 3*m := by omega
        rw [hn'_eq_mul, show ((3*m : ℕ) : ℤ) = (3 : ℤ) * (m : ℤ) by simp, h_eq_3m]
        have h_target_rewrite : ((T : Series).partial (m : ℤ) - b (3*m+1) - b (3*m+2)) - L =
            ((T : Series).partial (m : ℤ) - L) - b (3*m+1) - b (3*m+2) := by ring_nf
        rw [h_target_rewrite]
        have hST : |(T : Series).partial (m : ℤ) - L| < ε/3 := hK' (m : ℤ) hm_val_K
        have hb1 : |b (3*m+1)| < ε/3 := hM' (3*m+1) (by omega)
        have hb2 : |b (3*m+2)| < ε/3 := hM' (3*m+2) (by omega)
        calc
          |((T : Series).partial (m : ℤ) - L) - b (3*m+1) - b (3*m+2)|
              = |((T : Series).partial (m : ℤ) - L) - (b (3*m+1) + b (3*m+2))| := by ring
          _ ≤ |(T : Series).partial (m : ℤ) - L| + |b (3*m+1) + b (3*m+2)| := abs_sub _ _
          _ ≤ |(T : Series).partial (m : ℤ) - L| + (|b (3*m+1)| + |b (3*m+2)|) := by
            gcongr; exact h_abs_add (b (3*m+1)) (b (3*m+2))
          _ = |(T : Series).partial (m : ℤ) - L| + |b (3*m+1)| + |b (3*m+2)| := by ring
          _ < ε/3 + ε/3 + ε/3 := by nlinarith
          _ = ε := by ring
      · -- n' = 3*m+1
        have hn'_eq_mul : n' = 3*m+1 := by omega
        rw [hn'_eq_mul, show ((3*m+1 : ℕ) : ℤ) = (3 : ℤ) * (m : ℤ) + 1 by simp, h_eq_3m1]
        have h_target_rewrite : ((T : Series).partial (m : ℤ) - b (3*m+2)) - L =
            ((T : Series).partial (m : ℤ) - L) - b (3*m+2) := by ring_nf
        rw [h_target_rewrite]
        have hST : |(T : Series).partial (m : ℤ) - L| < ε/3 := hK' (m : ℤ) hm_val_K
        have hb2 : |b (3*m+2)| < ε/3 := hM' (3*m+2) (by omega)
        calc
          |((T : Series).partial (m : ℤ) - L) - b (3*m+2)|
              ≤ |(T : Series).partial (m : ℤ) - L| + |b (3*m+2)| := abs_sub _ _
          _ < ε/3 + ε/3 := by nlinarith
          _ < ε := by nlinarith
      · -- n' = 3*m+2
        have hn'_eq_mul : n' = 3*m+2 := by omega
        rw [hn'_eq_mul, show ((3*m+2 : ℕ) : ℤ) = (3 : ℤ) * (m : ℤ) + 2 by simp, h_eq_3m2]
        have hST : |(T : Series).partial (m : ℤ) - L| < ε/3 := hK' (m : ℤ) hm_val_K
        nlinarith
    exact h_diff

  exact ⟨L, h_convTo⟩

set_option maxHeartbeats 1600000 in
theorem Series.ex_7_4_4'_sum : (fun n ↦ a_7_4_4 (f_7_4_4 n) :Series).sum < 0 := by
  set b : ℕ → ℝ := fun n ↦ a_7_4_4 (f_7_4_4 n) with hb
  have hb_conv : (b : Series).converges := ex_7_4_4'_conv
  have hb_convTo : (b : Series).convergesTo ((b : Series).sum) := convergesTo_sum hb_conv

  have h_seq (n : ℤ) (hn : n ≥ 0) : (b : Series).seq n = b (n.toNat) := by
    simp [hn]

  have h_block_neg (k : ℕ) : b (3*k) + b (3*k+1) + b (3*k+2) < 0 := by
    dsimp [b, a_7_4_4, f_7_4_4]
    have h0mod : (3*k) % 3 = 0 := by omega
    have h0div : (3*k)/3 = k := by omega
    have h1mod : (3*k+1) % 3 = 1 := by omega
    have h1div : (3*k+1)/3 = k := by omega
    have h2mod : (3*k+2) % 3 = 2 := by omega
    have h2div : (3*k+2)/3 = k := by omega
    simp [h0mod, h0div, h1mod, h1div, h2mod, h2div]
    have h_pow_4k1 : (-1 : ℝ) ^ (4*k+1 : ℕ) = -1 := by
      calc
        (-1 : ℝ) ^ (4*k+1 : ℕ) = ((-1 : ℝ)^(2 : ℕ)) ^ (2*k) * (-1 : ℝ) := by
          rw [show 4*k+1 = 2*(2*k)+1 by omega, pow_succ, pow_mul]
        _ = 1 ^ (2*k) * (-1 : ℝ) := by norm_num
        _ = -1 := by simp
    have h_pow_4k3 : (-1 : ℝ) ^ (4*k+3 : ℕ) = -1 := by
      calc
        (-1 : ℝ) ^ (4*k+3 : ℕ) = ((-1 : ℝ)^(2 : ℕ)) ^ (2*k+1) * (-1 : ℝ) := by
          rw [show 4*k+3 = 2*(2*k+1)+1 by omega, pow_succ, pow_mul]
        _ = 1 ^ (2*k+1) * (-1 : ℝ) := by norm_num
        _ = -1 := by simp
    rw [h_pow_4k1, h_pow_4k3]
    have h_denom1 : (2*k+2 : ℝ) ≠ 0 := by nlinarith
    have h_denom2 : (4*k+1+2 : ℝ) ≠ 0 := by nlinarith
    have h_denom3 : (4*k+3+2 : ℝ) ≠ 0 := by nlinarith
    field_simp [h_denom1, h_denom2, h_denom3]
    ring_nf
    norm_num

  have h_seq_simp (n : ℕ) : (b : Series).seq (n : ℤ) = b n := by
    have hn : (n : ℤ) ≥ 0 := by exact mod_cast (Nat.zero_le n)
    simpa using h_seq (n : ℤ) hn

  have h_partial_add (M : ℕ) : (b : Series).partial (3*M+5 : ℤ) = (b : Series).partial (3*M+2 : ℤ) + b (3*M+3) + b (3*M+4) + b (3*M+5) := by
    have hpos2 : (3*M+2 : ℤ) ≥ (b : Series).m - 1 := by
      rw [show (b : Series).m = 0 from by simp]; omega
    have hpos3 : (3*M+3 : ℤ) ≥ (b : Series).m - 1 := by
      rw [show (b : Series).m = 0 from by simp]; omega
    have hpos4 : (3*M+4 : ℤ) ≥ (b : Series).m - 1 := by
      rw [show (b : Series).m = 0 from by simp]; omega
    have h_sq3 : (b : Series).seq (3*M+3 : ℤ) = b (3*M+3) := by
      simpa using h_seq_simp (3*M+3)
    have h_sq4 : (b : Series).seq (3*M+4 : ℤ) = b (3*M+4) := by
      simpa using h_seq_simp (3*M+4)
    have h_sq5 : (b : Series).seq (3*M+5 : ℤ) = b (3*M+5) := by
      simpa using h_seq_simp (3*M+5)
    calc
      (b : Series).partial (3*M+5 : ℤ) = (b : Series).partial (((3*M+4 : ℤ) + 1 : ℤ)) := by ring
      _ = (b : Series).partial (3*M+4 : ℤ) + (b : Series).seq ((3*M+4 : ℤ) + 1) := Series.partial_succ (b : Series) hpos4
      _ = (b : Series).partial (3*M+4 : ℤ) + (b : Series).seq (3*M+5 : ℤ) := by ring
      _ = (b : Series).partial (((3*M+3 : ℤ) + 1 : ℤ)) + (b : Series).seq (3*M+5 : ℤ) := by ring
      _ = ((b : Series).partial (3*M+3 : ℤ) + (b : Series).seq ((3*M+3 : ℤ) + 1)) + (b : Series).seq (3*M+5 : ℤ) := by rw [Series.partial_succ (b : Series) hpos3]
      _ = ((b : Series).partial (3*M+3 : ℤ) + (b : Series).seq (3*M+4 : ℤ)) + (b : Series).seq (3*M+5 : ℤ) := by ring
      _ = ((b : Series).partial (((3*M+2 : ℤ) + 1 : ℤ)) + (b : Series).seq (3*M+4 : ℤ)) + (b : Series).seq (3*M+5 : ℤ) := by ring
      _ = (((b : Series).partial (3*M+2 : ℤ) + (b : Series).seq ((3*M+2 : ℤ) + 1)) + (b : Series).seq (3*M+4 : ℤ)) + (b : Series).seq (3*M+5 : ℤ) := by rw [Series.partial_succ (b : Series) hpos2]
      _ = (((b : Series).partial (3*M+2 : ℤ) + (b : Series).seq (3*M+3 : ℤ)) + (b : Series).seq (3*M+4 : ℤ)) + (b : Series).seq (3*M+5 : ℤ) := by ring
      _ = (b : Series).partial (3*M+2 : ℤ) + ((b : Series).seq (3*M+3 : ℤ) + (b : Series).seq (3*M+4 : ℤ) + (b : Series).seq (3*M+5 : ℤ)) := by ring
      _ = (b : Series).partial (3*M+2 : ℤ) + (b (3*M+3) + b (3*M+4) + b (3*M+5)) := by rw [h_sq3, h_sq4, h_sq5]
      _ = (b : Series).partial (3*M+2 : ℤ) + b (3*M+3) + b (3*M+4) + b (3*M+5) := by ring

  have h_partial_neg (M : ℕ) : (b : Series).partial (3*M+2 : ℤ) < 0 := by
    induction' M with M ih
    · have h_partial2 : (b : Series).partial (2 : ℤ) = b 0 + b 1 + b 2 := by
        unfold Series.partial
        simp
        have hIcc : Finset.Icc (0 : ℤ) (2 : ℤ) = {(0 : ℤ), 1, 2} := by decide
        rw [hIcc]
        simp
        ring
      have h0 : (3*↑0+2 : ℤ) = (2 : ℤ) := by norm_num
      simpa [h0, h_partial2] using h_block_neg 0
    · have h_target : (b : Series).partial (3*↑(M+1)+2 : ℤ) = (b : Series).partial (3*↑M+5 : ℤ) := by
        push_cast; ring
      rw [h_target, h_partial_add M]
      have h_next : b (3*M+3) + b (3*M+4) + b (3*M+5) < 0 := h_block_neg (M+1)
      nlinarith

  have h_partial_decr (M : ℕ) : (b : Series).partial (3*(M+1)+2 : ℤ) ≤ (b : Series).partial (3*M+2 : ℤ) := by
    have h_eq : (b : Series).partial (3*(M+1)+2 : ℤ) = (b : Series).partial (3*M+5 : ℤ) := by ring
    rw [h_eq, h_partial_add M]
    have h_next : b (3*M+3) + b (3*M+4) + b (3*M+5) < 0 := h_block_neg (M+1)
    nlinarith

  have h_subseq_tendsto : Filter.Tendsto (fun (M : ℕ) => (b : Series).partial (3*M+2 : ℤ)) Filter.atTop (nhds ((b : Series).sum)) :=
    hb_convTo.comp (by
      refine Filter.tendsto_atTop_atTop.mpr ?_
      intro N
      by_cases hN_nonneg : N ≥ 0
      · use N.toNat
        intro m hm
        have hm' : (m : ℤ) ≥ (N.toNat : ℤ) := by exact mod_cast hm
        have h_eq : (N.toNat : ℤ) = N := by exact mod_cast Int.toNat_of_nonneg hN_nonneg
        omega
      · use 0
        intro m hm
        omega)

  have h_all_M (M : ℕ) : (b : Series).partial (3*M+2 : ℤ) ≤ (b : Series).partial (2 : ℤ) := by
    induction M with
    | zero => rfl
    | succ k ih => exact le_trans (h_partial_decr k) ih

  have h_event : ∀ᶠ (M : ℕ) in Filter.atTop, (b : Series).partial (3*M+2 : ℤ) ≤ (b : Series).partial (2 : ℤ) := by
    apply Filter.eventually_atTop.mpr
    exact ⟨0, λ M hM => h_all_M M⟩

  have h_partial2_neg : (b : Series).partial (2 : ℤ) < 0 := h_partial_neg 0
  have h_sum_le_partial2 : (b : Series).sum ≤ (b : Series).partial (2 : ℤ) :=
    le_of_tendsto h_subseq_tendsto h_event
  linarith

lemma partial_abs_subseq_eq_range (a : ℕ → ℝ) (f : ℕ → ℕ) (n : ℕ) :
    ((fun n ↦ a (f n):Series).abs).partial (n : ℤ) = ∑ k ∈ Finset.range (n+1), |a (f k)| := by
  have h_expand : ((fun n ↦ a (f n):Series).abs).partial (n : ℤ) = ∑ x ∈ Finset.Icc (0 : ℤ) (n : ℤ), (if (0 : ℤ) ≤ x then |((fun n ↦ a (f n):Series).seq x)| else 0) := by
    simp [Series.partial]
  have h_simp1 : ∑ x ∈ Finset.Icc (0 : ℤ) (n : ℤ), (if (0 : ℤ) ≤ x then |((fun n ↦ a (f n):Series).seq x)| else 0) = ∑ x ∈ Finset.Icc (0 : ℤ) (n : ℤ), |(if x ≥ 0 then a (f x.toNat) else 0)| := by
    refine Finset.sum_congr rfl (λ x hx => ?_)
    have hx0 : 0 ≤ x := (Finset.mem_Icc.mp hx).1
    dsimp
    simp [hx0]
  have h_simp2 : ∑ x ∈ Finset.Icc (0 : ℤ) (n : ℤ), |(if x ≥ 0 then a (f x.toNat) else 0)| = ∑ x ∈ Finset.Icc (0 : ℤ) (n : ℤ), |a (f x.toNat)| := by
    refine Finset.sum_congr rfl (λ x hx => ?_)
    have hx0 : 0 ≤ x := (Finset.mem_Icc.mp hx).1
    simp [hx0]
  have h_image : ∑ x ∈ Finset.Icc (0 : ℤ) (n : ℤ), |a (f x.toNat)| = ∑ k ∈ (Finset.Icc (0 : ℤ) (n : ℤ)).image (λ (x : ℤ) => x.toNat), |a (f k)| := by
    rw [Finset.sum_image (by
      intro x hx y hy h
      have hx0 : 0 ≤ x := (Finset.mem_Icc.mp hx).1
      have hy0 : 0 ≤ y := (Finset.mem_Icc.mp hy).1
      have hx_toNat_x : (x.toNat : ℤ) = x := by exact mod_cast Int.toNat_of_nonneg hx0
      have hy_toNat_y : (y.toNat : ℤ) = y := by exact mod_cast Int.toNat_of_nonneg hy0
      have hx_toNat_eq_y_toNat : x.toNat = y.toNat := h
      calc
        x = (x.toNat : ℤ) := by symm; exact hx_toNat_x
        _ = (y.toNat : ℤ) := by rw [hx_toNat_eq_y_toNat]
        _ = y := hy_toNat_y)]
  have h_range : (Finset.Icc (0 : ℤ) (n : ℤ)).image (λ (x : ℤ) => x.toNat) = Finset.range (n+1) := by
    ext k; constructor
    · intro hk
      rcases Finset.mem_image.mp hk with ⟨x, hx, rfl⟩
      rcases Finset.mem_Icc.mp hx with ⟨hx0, hxn⟩
      have hkn : x.toNat ≤ n := by omega
      exact Finset.mem_range_succ_iff.mpr hkn
    · intro hk
      have hkn : k ≤ n := Finset.mem_range_succ_iff.mp hk
      refine Finset.mem_image.mpr ⟨(k : ℤ), Finset.mem_Icc.mpr ⟨by exact mod_cast (Nat.zero_le k), by exact mod_cast hkn⟩, ?_⟩
      simp
  calc
    ((fun n ↦ a (f n):Series).abs).partial (n : ℤ) = ∑ x ∈ Finset.Icc (0 : ℤ) (n : ℤ), (if (0 : ℤ) ≤ x then |((fun n ↦ a (f n):Series).seq x)| else 0) := h_expand
    _ = ∑ x ∈ Finset.Icc (0 : ℤ) (n : ℤ), |(if x ≥ 0 then a (f x.toNat) else 0)| := h_simp1
    _ = ∑ x ∈ Finset.Icc (0 : ℤ) (n : ℤ), |a (f x.toNat)| := h_simp2
    _ = ∑ k ∈ (Finset.Icc (0 : ℤ) (n : ℤ)).image (λ (x : ℤ) => x.toNat), |a (f k)| := h_image
    _ = ∑ k ∈ Finset.range (n+1), |a (f k)| := by rw [h_range]

lemma partial_abs_eq_range (a : ℕ → ℝ) (n : ℕ) : ((a : Series).abs).partial (n : ℤ) = ∑ k ∈ Finset.range (n+1), |a k| := by
  have h_expand : ((a : Series).abs).partial (n : ℤ) = ∑ x ∈ Finset.Icc (0 : ℤ) (n : ℤ), (if (0 : ℤ) ≤ x then |((a : Series).seq x)| else 0) := by
    simp [Series.partial]
  have h_simp1 : ∑ x ∈ Finset.Icc (0 : ℤ) (n : ℤ), (if (0 : ℤ) ≤ x then |((a : Series).seq x)| else 0) = ∑ x ∈ Finset.Icc (0 : ℤ) (n : ℤ), |(if x ≥ 0 then a x.toNat else 0)| := by
    refine Finset.sum_congr rfl (λ x hx => ?_)
    have hx0 : 0 ≤ x := (Finset.mem_Icc.mp hx).1
    dsimp
    simp [hx0]
  have h_simp2 : ∑ x ∈ Finset.Icc (0 : ℤ) (n : ℤ), |(if x ≥ 0 then a x.toNat else 0)| = ∑ x ∈ Finset.Icc (0 : ℤ) (n : ℤ), |a x.toNat| := by
    refine Finset.sum_congr rfl (λ x hx => ?_)
    have hx0 : 0 ≤ x := (Finset.mem_Icc.mp hx).1
    simp [hx0]
  have h_image : ∑ x ∈ Finset.Icc (0 : ℤ) (n : ℤ), |a x.toNat| = ∑ k ∈ (Finset.Icc (0 : ℤ) (n : ℤ)).image (λ (x : ℤ) => x.toNat), |a k| := by
    rw [Finset.sum_image (by
      intro x hx y hy h
      have hx0 : 0 ≤ x := (Finset.mem_Icc.mp hx).1
      have hy0 : 0 ≤ y := (Finset.mem_Icc.mp hy).1
      have hx_toNat_x : (x.toNat : ℤ) = x := by exact mod_cast Int.toNat_of_nonneg hx0
      have hy_toNat_y : (y.toNat : ℤ) = y := by exact mod_cast Int.toNat_of_nonneg hy0
      have hx_toNat_eq_y_toNat : x.toNat = y.toNat := h
      calc
        x = (x.toNat : ℤ) := by symm; exact hx_toNat_x
        _ = (y.toNat : ℤ) := by rw [hx_toNat_eq_y_toNat]
        _ = y := hy_toNat_y)]
  have h_range : (Finset.Icc (0 : ℤ) (n : ℤ)).image (λ (x : ℤ) => x.toNat) = Finset.range (n+1) := by
    ext k; constructor
    · intro hk
      rcases Finset.mem_image.mp hk with ⟨x, hx, rfl⟩
      rcases Finset.mem_Icc.mp hx with ⟨hx0, hxn⟩
      have hkn : x.toNat ≤ n := by omega
      exact Finset.mem_range_succ_iff.mpr hkn
    · intro hk
      have hkn : k ≤ n := Finset.mem_range_succ_iff.mp hk
      refine Finset.mem_image.mpr ⟨(k : ℤ), Finset.mem_Icc.mpr ⟨by exact mod_cast (Nat.zero_le k), by exact mod_cast hkn⟩, ?_⟩
      simp
  calc
    ((a : Series).abs).partial (n : ℤ) = ∑ x ∈ Finset.Icc (0 : ℤ) (n : ℤ), (if (0 : ℤ) ≤ x then |((a : Series).seq x)| else 0) := h_expand
    _ = ∑ x ∈ Finset.Icc (0 : ℤ) (n : ℤ), |(if x ≥ 0 then a x.toNat else 0)| := h_simp1
    _ = ∑ x ∈ Finset.Icc (0 : ℤ) (n : ℤ), |a x.toNat| := h_simp2
    _ = ∑ k ∈ (Finset.Icc (0 : ℤ) (n : ℤ)).image (λ (x : ℤ) => x.toNat), |a k| := h_image
    _ = ∑ k ∈ Finset.range (n+1), |a k| := by rw [h_range]

theorem Series.absConverges_of_subseries {a:ℕ → ℝ} (ha: (a:Series).absConverges) {f: ℕ → ℕ} (hf: StrictMono f) :
  (fun n ↦ a (f n):Series).absConverges := by
  have h_nonneg : ((fun n ↦ a (f n):Series).abs).nonneg := by
    intro n
    dsimp [Series.abs, Series.mk']
    by_cases h : (0 : ℤ) ≤ n
    · simp [h]
    · simp [h]
  unfold Series.absConverges
  rw [Series.converges_of_nonneg_iff h_nonneg]
  have h_nonneg_abs : ((a:Series).abs).nonneg := by
    intro n
    dsimp [Series.abs, Series.mk']
    by_cases h : (0 : ℤ) ≤ n
    · simp [h]
    · simp [h]
  have h_abs_conv : (a:Series).abs.converges := ha
  have h_bound : ∀ (N : ℤ), ((a:Series).abs).partial N ≤ ((a:Series).abs).sum :=
    λ N => Series.partial_le_sum_of_nonneg h_nonneg_abs h_abs_conv N
  have h_main : ∀ (n : ℕ), ((fun n' ↦ a (f n'):Series).abs).partial (n : ℤ) ≤ ((a:Series).abs).sum := by
    intro n
    have h_ineq : ∑ k ∈ Finset.range (n+1), |a (f k)| ≤ ∑ k ∈ Finset.range (f n + 1), |a k| := by
      have hsub : Finset.image f (Finset.range (n+1)) ⊆ Finset.range (f n + 1) := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
        have hk_n : k ≤ n := Finset.mem_range_succ_iff.mp hk
        have h_fk_fn : f k ≤ f n := hf.monotone hk_n
        exact Finset.mem_range_succ_iff.mpr h_fk_fn
      calc
        ∑ k ∈ Finset.range (n+1), |a (f k)| = ∑ x ∈ Finset.image f (Finset.range (n+1)), |a x| := by
          rw [Finset.sum_image (by
            intro x hx y hy h
            exact hf.injective h)]
        _ ≤ ∑ x ∈ Finset.range (f n + 1), |a x| := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsub (λ x hx_t hx_s => abs_nonneg (a x))
    calc
      ((fun n' ↦ a (f n'):Series).abs).partial (n : ℤ)
          = ∑ k ∈ Finset.range (n+1), |a (f k)| := by
        rw [partial_abs_subseq_eq_range a f n]
      _ ≤ ∑ k ∈ Finset.range (f n + 1), |a k| := h_ineq
      _ = ((a : Series).abs).partial ((f n : ℕ) : ℤ) := by
        rw [← partial_abs_eq_range a (f n)]
      _ ≤ ((a:Series).abs).sum := h_bound ((f n : ℕ) : ℤ)
  refine ⟨(a:Series).abs.sum, λ N => ?_⟩
  by_cases hN : (0 : ℤ) ≤ N
  · let n : ℕ := Int.toNat N
    have hn_eq : (n : ℤ) = N := by exact mod_cast Int.toNat_of_nonneg hN
    rw [← hn_eq]
    exact h_main n
  · have h_nonneg_sum : 0 ≤ ((a:Series).abs).sum := Series.sum_of_nonneg h_nonneg_abs
    have h_empty : Finset.Icc (0 : ℤ) N = ∅ := by
      refine Finset.not_nonempty_iff_eq_empty.mp ?_
      intro hne
      rcases hne with ⟨x, hx⟩
      have hx0 : 0 ≤ x := (Finset.mem_Icc.mp hx).1
      have hxN : x ≤ N := (Finset.mem_Icc.mp hx).2
      exact hN (hx0.trans hxN)
    simp [Series.partial, Series.abs, h_empty, h_nonneg_sum]

theorem Series.absConverges_of_permute' {a:ℕ → ℝ} (ha : (a:Series).absConverges)
  {f: ℕ → ℕ} (hf: Function.Bijective f) :
    (fun n ↦ a (f n):Series).absConverges  ∧ (a:Series).sum = (fun n ↦ a (f n):Series).sum :=
  absConverges_of_permute ha hf

end Chapter7
