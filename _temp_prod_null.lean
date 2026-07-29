import Analysis.MeasureTheory.Section_1_2_1
open Set
open Box
open Classical
open EReal
open Finset

lemma le_zero_of_forall_lt_pos {a : EReal} (ha_nonneg : 0 ≤ a) (h : ∀ ε : ℝ, 0 < ε → a < (ε : EReal)) : a ≤ 0 := by
  by_cases ha_top : a = ⊤
  · subst ha_top
    have h_top_lt_one : (⊤ : EReal) < (1 : EReal) := h 1 (by norm_num)
    exfalso; exact not_lt.mpr le_top h_top_lt_one
  · by_cases ha_bot : a = ⊥
    · subst ha_bot; exact le_of_lt EReal.bot_lt_zero
    · have ha_real : ∃ (x : ℝ), a = (x : EReal) := by
        refine EReal.rec (motive := fun a' => a' ≠ ⊥ → a' ≠ ⊤ → ∃ (x : ℝ), a' = (x : EReal)) ?_ ?_ ?_ a ha_bot ha_top
        · intro h_bot h_top; exfalso; exact h_bot rfl
        · intro x h_bot h_top; exact ⟨x, rfl⟩
        · intro h_bot h_top; exfalso; exact h_top rfl
      rcases ha_real with ⟨x, hx⟩; subst hx
      by_cases hx_nonpos : x ≤ 0
      · have hzero_eq : (0 : EReal) = ((0 : ℝ) : EReal) := by norm_num
        rw [hzero_eq, EReal.coe_le_coe_iff]; exact hx_nonpos
      · have hx_pos : 0 < x := by linarith
        have hxdiv_pos : 0 < x / 2 := by linarith
        have h_lt : (x : EReal) < ((x / 2 : ℝ) : EReal) := h (x / 2) hxdiv_pos
        rw [EReal.coe_lt_coe_iff] at h_lt; linarith


lemma exists_cover_total_lt {d : ℕ} (hd_pos : 0 < d) {E : Set (EuclideanSpace' d)} (hm : Lebesgue_outer_measure E = 0)
    (η : ℝ) (hη : 0 < η) : ∃ (S : ℕ → Box d), E ⊆ ⋃ n : ℕ, (S n).toSet ∧ ∑' n : ℕ, ((S n).volume.toEReal : EReal) < (η : EReal) := by
  have h_lt : Lebesgue_outer_measure E < (η : EReal) := by rw [hm]; exact_mod_cast hη
  unfold Lebesgue_outer_measure at h_lt
  rcases sInf_lt_iff.mp h_lt with ⟨V, ⟨X, S', h_cover', hV_eq⟩, hV_lt⟩
  let B₀ : Box d := ⟨fun i : Fin d => BoundedInterval.Icc 0 0⟩
  have hB₀_vol : B₀.volume = 0 := by
    unfold Box.volume
    have h_nonempty : Finset.Nonempty (Finset.univ : Finset (Fin d)) := by
      have h : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd_pos
      exact ⟨h.some, Finset.mem_univ _⟩
    rcases h_nonempty with ⟨i, hi⟩
    apply Finset.prod_eq_zero hi; simp [BoundedInterval.length]; norm_num
  let S : ℕ → Box d := fun n => if h : n ∈ X then S' ⟨n, h⟩ else B₀
  have h_cover : E ⊆ ⋃ n : ℕ, (S n).toSet := by
    intro y hy
    have hy' : y ∈ ⋃ (n : X), (S' n).toSet := h_cover' hy
    rcases Set.mem_iUnion.mp hy' with ⟨⟨n, hn⟩, hyn⟩
    refine Set.mem_iUnion.mpr ⟨n, ?_⟩
    have : S n = S' ⟨n, hn⟩ := by simp [S, hn]
    rw [this]; exact hyn
  have h_sum : ∑' n : ℕ, ((S n).volume.toEReal : EReal) < (η : EReal) := by
    let g : ℕ → EReal := fun n => if h : n ∈ X then ((S' ⟨n, h⟩).volume.toEReal : EReal) else 0
    have h_S_eq_g : ∀ n : ℕ, ((S n).volume.toEReal : EReal) = g n := by
      intro n; dsimp [S, g]; split_ifs with h <;> simp [hB₀_vol]
    have h_g_sum : ∑' n : ℕ, g n = ∑' (n : X), ((S' n).volume.toEReal : EReal) := by
      have h_ind : ∀ n : ℕ, g n = Set.indicator (X : Set ℕ) g n := by
        intro n; rw [Set.indicator_apply]; by_cases hn : n ∈ X <;> simp [g, hn]
      calc
        ∑' n : ℕ, g n = ∑' n : ℕ, (Set.indicator (X : Set ℕ) g n : EReal) := by
          refine tsum_congr (fun n => ?_); rw [h_ind n]
        _ = ∑' (n : X), g n := by rw [tsum_subtype]
        _ = ∑' (n : X), ((S' n).volume.toEReal : EReal) := by
          refine tsum_congr (fun ⟨n, hn⟩ => ?_); simp [g, hn]
    calc
      ∑' n : ℕ, ((S n).volume.toEReal : EReal) = ∑' n : ℕ, g n := by
        refine tsum_congr (fun n => ?_); rw [h_S_eq_g n]
      _ = ∑' (n : X), ((S' n).volume.toEReal : EReal) := h_g_sum
      _ = V := hV_eq.symm
      _ < (η : EReal) := hV_lt
  exact ⟨S, h_cover, h_sum⟩


lemma natUnpair_injective : Function.Injective (Nat.unpair : ℕ → ℕ × ℕ) := by
  intro a b h
  have h' : Function.uncurry Nat.pair (Nat.unpair a) = Function.uncurry Nat.pair (Nat.unpair b) := by rw [h]
  simp [Function.uncurry, Nat.pair_unpair] at h'; exact h'

lemma sum_unpair_eq (N : ℕ) (f : ℕ × ℕ → ℝ) : ∑ m ∈ range N, f (Nat.unpair m) = 
    ∑ k ∈ range N, ∑ n ∈ range N, (if (Nat.pair k n) < N then f (k, n) else 0) := by
  calc
    ∑ m ∈ range N, f (Nat.unpair m) = ∑ x ∈ (range N).image (fun m : ℕ => Nat.unpair m), f x := by
      rw [Finset.sum_image (fun x hx y hy h => natUnpair_injective h)]
    _ = ∑ x ∈ filter (fun (x : ℕ × ℕ) => Nat.pair x.1 x.2 < N) ((range N) ×ˢ (range N)), f x := by
      ext ⟨k, n⟩; constructor
      · intro h
        rcases mem_image.mp h with ⟨m, hm, hmn⟩
        have hm_lt : m < N := by simpa using hm
        have hp : Nat.pair k n = m := natUnpair_injective (by
          calc
            Nat.unpair (Nat.pair k n) = (k, n) := Nat.unpair_pair k n
            _ = Nat.unpair m := hmn.symm)
        have h_kn_lt : Nat.pair k n < N := by rw [hp]; exact hm_lt
        have hk : k < N := by
          unfold Nat.pair at h_kn_lt; split_ifs at h_kn_lt with h <;> nlinarith
        have hn : n < N := by
          unfold Nat.pair at h_kn_lt; split_ifs at h_kn_lt with h <;> nlinarith
        refine mem_filter.mpr ⟨?_, h_kn_lt⟩
        exact mem_product.mpr ⟨mem_range.mpr hk, mem_range.mpr hn⟩
      · intro h
        rcases mem_filter.mp h with ⟨hmem, hpair⟩
        rcases mem_product.mp hmem with ⟨hk, hn⟩
        have hm : Nat.pair k n < N := hpair
        refine mem_image.mpr ⟨Nat.pair k n, mem_range.mpr hm, ?_⟩
        simp
    _ = ∑ k ∈ range N, ∑ n ∈ range N, (if (Nat.pair k n) < N then f (k, n) else 0) := by
      simp [Finset.sum_product, Finset.sum_filter]


theorem prod_null_of_null_second {d₁ d₂ : ℕ} {E₁ : Set (EuclideanSpace' d₁)} {E₂ : Set (EuclideanSpace' d₂)}
    (hm₂ : Lebesgue_outer_measure E₂ = 0) : Lebesgue_outer_measure (EuclideanSpace'.prod E₁ E₂) = 0 := by
  by_cases hd₂ : d₂ = 0
  · subst hd₂
    rcases em' (Set.Nonempty E₂) with (hE₂_not_nonempty | hE₂_nonempty)
    · have hE₂_empty' : E₂ = (∅ : Set (EuclideanSpace' 0)) := Set.not_nonempty_iff_eq_empty.mp hE₂_not_nonempty
      have h_empty : EuclideanSpace'.prod (E₁ : Set (EuclideanSpace' d₁)) (E₂ : Set (EuclideanSpace' 0)) = ∅ := by
        simp [EuclideanSpace'.prod, hE₂_empty']
      rw [h_empty]
      have h_nonneg : 0 ≤ Lebesgue_outer_measure (∅ : Set (EuclideanSpace' (d₁ + 0))) := Lebesgue_outer_measure.nonneg _
      apply le_antisymm ?_ h_nonneg
      unfold Lebesgue_outer_measure; apply sInf_le
      refine ⟨(∅ : Set ℕ), (fun (n : (∅ : Set ℕ)) => (Box.unit_cube (d₁ + 0))), ?_, ?_⟩
      · simp; · simp
    · have hm_dim0 : Lebesgue_outer_measure E₂ = 1 := by
        rw [Lebesgue_outer_measure_of_dim_zero]; simp [hE₂_nonempty]
      rw [hm₂] at hm_dim0; exfalso; have : (0 : EReal) ≠ 1 := by norm_num; exact this hm_dim0
  · have hd₂_pos : 0 < d₂ := Nat.pos_of_ne_zero hd₂
    
    have h_forall_lt : ∀ (ε : ℝ), 0 < ε → Lebesgue_outer_measure (EuclideanSpace'.prod E₁ E₂) < (ε : EReal) := by
      intro ε hε
      
      -- Concentric boxes B_k = [-k,k]^d₁ covering EuclideanSpace' d₁
      let B : ℕ → Box d₁ := fun k => ⟨fun _ : Fin d₁ => BoundedInterval.Icc (-(k : ℝ)) (k : ℝ)⟩
      
      -- Every point is in some B_k
      have h_union_B : (⋃ k : ℕ, (B k).toSet) = Set.univ := by
        apply Set.eq_univ_of_forall; intro x
        by_cases hd₁ : d₁ = 0
        · subst hd₁; refine Set.mem_iUnion.mpr ⟨0, ?_⟩; simp [B, Box.mem_toSet]
        · have h_pos : 0 < d₁ := Nat.pos_of_ne_zero hd₁
          have h_nonempty : Nonempty (Fin d₁) := Fin.pos_iff_nonempty.mp h_pos
          let vals : Finset ℝ := Finset.image (fun (i : Fin d₁) => |x i|) Finset.univ
          have h_vals_nonempty : vals.Nonempty := by
            refine ⟨|x h_nonempty.some|, Finset.mem_image.mpr ⟨h_nonempty.some, Finset.mem_univ _, rfl⟩⟩
          let M := vals.max' h_vals_nonempty
          have hM : ∀ i : Fin d₁, |x i| ≤ M := by
            intro i; apply Finset.le_max' vals (|x i|)
            exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
          have hM_real : M ≤ (Nat.ceil M : ℝ) := by
            have h_nat : (Nat.ceil M : ℕ) ≤ (Nat.ceil M : ℕ) := le_refl _
            exact (Nat.ceil_le (a := M) (n := Nat.ceil M)).mp h_nat
          let k := Nat.ceil M
          have hk : ∀ i : Fin d₁, -(k : ℝ) ≤ x i ∧ x i ≤ (k : ℝ) := by
            intro i; have hi_M : |x i| ≤ M := hM i; have hM_k' : M ≤ (k : ℝ) := hM_real
            have hx_abs : |x i| ≤ (k : ℝ) := le_trans hi_M hM_k'
            rcases abs_le.mp hx_abs with ⟨hx1, hx2⟩; constructor <;> linarith
          refine Set.mem_iUnion.mpr ⟨k, ?_⟩; simp [B, Box.mem_toSet, hk]
      
      -- η_k = (ε/4) / (2^(k+1) * max(|B_k|,1)) so Σ_k |B_k| * η_k < ε/4
      let η (k : ℕ) : ℝ := (ε/4) / (((2 : ℝ)^(k+1 : ℕ)) * max ((B k).volume) 1)
      
      have hη_pos : ∀ k : ℕ, 0 < η k := by
        intro k; dsimp [η]
        refine div_pos (by linarith) ?_
        have hpos : 0 < max ((B k).volume) 1 := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
        have : 0 < (2 : ℝ)^(k+1 : ℕ) := pow_pos (by norm_num) (k+1)
        exact mul_pos this hpos
      
      have h_covers : ∀ k : ℕ, ∃ (T : ℕ → Box d₂), E₂ ⊆ ⋃ n : ℕ, (T n).toSet ∧
        ∑' n : ℕ, ((T n).volume.toEReal : EReal) < (η k : EReal) := by
        intro k; apply exists_cover_total_lt hd₂_pos hm₂ (η k) (hη_pos k)
      choose T hT_cover hT_sum using h_covers
      
      -- S enumerates ALL pairs (k,n) via Nat.pair
      let S : ℕ → Box (d₁ + d₂) := fun m =>
        Box.prod (B (Prod.fst (Nat.unpair m))) (T (Prod.fst (Nat.unpair m)) (Prod.snd (Nat.unpair m)))
      
      have hS_cover : EuclideanSpace'.prod E₁ E₂ ⊆ ⋃ m : ℕ, (S m).toSet := by
        intro x hx; rw [EuclideanSpace'.prod, Set.mem_image] at hx
        rcases hx with ⟨⟨z₁, z₂⟩, ⟨hz₁, hz₂⟩, rfl⟩
        have hz₁_in_union : z₁ ∈ ⋃ k : ℕ, (B k).toSet := by rw [h_union_B]; trivial
        rcases Set.mem_iUnion.mp hz₁_in_union with ⟨k, hk⟩
        have hz₂_in_Tk : z₂ ∈ ⋃ n : ℕ, (T k n).toSet := hT_cover k hz₂
        rcases Set.mem_iUnion.mp hz₂_in_Tk with ⟨n, hn⟩
        have hz_in_prod : (EuclideanSpace'.prod_equiv (d₁ := d₁) (d₂ := d₂)).symm (z₁, z₂) ∈ (Box.prod (B k) (T k n)).toSet := by
          rw [Box.prod_toSet, EuclideanSpace'.prod]
          refine (Set.mem_image _ _ _).mpr ⟨(z₁, z₂), ?_, rfl⟩; simp [hk, hn]
        let m := Nat.pair k n
        have hm_unpair : Nat.unpair m = (k, n) := Nat.unpair_pair k n
        have hSm_eq : S m = Box.prod (B k) (T k n) := by dsimp [S]; rw [hm_unpair]
        rw [hSm_eq]; exact Set.mem_iUnion.mpr ⟨m, hz_in_prod⟩
      
      have hS_vol_nonneg : ∀ m : ℕ, 0 ≤ ((S m).volume.toEReal : EReal) := by
        intro m; apply EReal.coe_nonneg.mpr; apply Box.volume_nonneg
      
      have h_vol_prod : ∀ m : ℕ, (S m).volume = (B (Prod.fst (Nat.unpair m))).volume *
          (T (Prod.fst (Nat.unpair m)) (Prod.snd (Nat.unpair m))).volume := by
        intro m; simp [S, Box.volume_prod]
      
      -- Bound: |B_k| * η_k ≤ (ε/4) / 2^(k+1)
      have h_Bk_eta_bound : ∀ k : ℕ, ((B k).volume : ℝ) * η k ≤ (ε/4) / ((2 : ℝ)^(k+1 : ℕ)) := by
        intro k; dsimp [η]
        have hvol_nonneg : 0 ≤ (B k).volume := Box.volume_nonneg _
        have hmax_nonneg : 0 ≤ max ((B k).volume) 1 := le_trans (by norm_num) (le_max_right _ _)
        have hdiv : (B k).volume / max ((B k).volume) 1 ≤ 1 := by
          by_cases hvolz : (B k).volume = 0
          · rw [hvolz]; exact div_nonpos_of_nonpos_of_nonneg (by norm_num) hmax_nonneg
          · by_cases hvol_pos : 0 < (B k).volume
            · have : max ((B k).volume) 1 ≥ (B k).volume := le_max_left _ _
              exact (div_le_one (by exact lt_of_lt_of_le hvol_pos (le_max_left _ _))).mpr this
            · exfalso; linarith
        nlinarith
      
      -- The total tsum is bounded by ε/4 < ε
      have hS_total : ∑' m : ℕ, ((S m).volume.toEReal : EReal) < (ε : EReal) := by
        -- For each M, the partial sum over m<M is bounded by Σ_{k<M} |B_k| * η_k (in EReal)
        have h_partial_ereal : ∀ M : ℕ, ∑ m ∈ range M, ((S m).volume.toEReal : EReal) ≤ (ε/4 : EReal) := by
          intro M
          let f (x : ℕ × ℕ) : ℝ := (B x.1).volume * (T x.1 x.2).volume
          have h_eq_ereal : (∑ m ∈ range M, (S m).volume : EReal) = ∑ m ∈ range M, ((S m).volume : EReal) := by simp
          
          -- Step 1: express the sum using sum_unpair_eq
          have h_eq : ∑ m ∈ range M, (S m).volume = ∑ k ∈ range M, ∑ n ∈ range M, (if (Nat.pair k n) < M then f (k, n) else 0) := by
            calc
              ∑ m ∈ range M, (S m).volume = ∑ m ∈ range M, f (Nat.unpair m) := by
                refine Finset.sum_congr rfl (fun m hm => ?_); rw [h_vol_prod m, f]
              _ = ∑ k ∈ range M, ∑ n ∈ range M, (if (Nat.pair k n) < M then f (k, n) else 0) := sum_unpair_eq M f
          
          -- Step 2: for each k, the inner sum (over n) is bounded by Σ'_n |T_k n| (in EReal)
          have h_inner_bound : ∀ k ∈ range M,
              (∑ n ∈ range M, (if (Nat.pair k n) < M then (T k n).volume else 0) : EReal) ≤ ∑' n : ℕ, ((T k n).volume : EReal) := by
            intro k hk
            have h_filter : (∑ n ∈ range M, (if (Nat.pair k n) < M then (T k n).volume else 0) : EReal) =
                (∑ n ∈ filter (fun n : ℕ => (Nat.pair k n) < M) (range M), (T k n).volume : EReal) := by
              simp [Finset.sum_filter]
            rw [h_filter]
            -- By EReal.finset_sum_le_tsum, the finite sum ≤ the total tsum
            apply EReal.finset_sum_le_tsum (fun n : ℕ => (T k n).volume) (fun n => Box.volume_nonneg _)
              (filter (fun n : ℕ => (Nat.pair k n) < M) (range M))
          
          -- Step 3: multiply by |B_k| (which is ≥ 0) and sum over k
          have h_bound : (∑ m ∈ range M, (S m).volume : EReal) ≤ (∑ k ∈ range M, ((B k).volume : ℝ) * η k : EReal) := by
            calc
              (∑ m ∈ range M, (S m).volume : EReal) = 
                  (∑ k ∈ range M, ∑ n ∈ range M, (if (Nat.pair k n) < M then f (k, n) else 0) : EReal) := by
                exact_mod_cast h_eq
              _ ≤ (∑ k ∈ range M, ((B k).volume : ℝ) * (∑ n ∈ range M, (if (Nat.pair k n) < M then (T k n).volume else 0)) : EReal) := by
                -- Use f(k,n) = |B_k| * |T_k n| and pull out |B_k|
                simp [f, Finset.mul_sum]
                refine Finset.sum_le_sum (fun k hk => ?_)
                apply mul_le_mul_of_nonneg_left ?_ (Box.volume_nonneg _)
                exact h_inner_bound k hk
              _ ≤ (∑ k ∈ range M, ((B k).volume : ℝ) * η k : EReal) := by
                refine Finset.sum_le_sum (fun k hk => ?_)
                have hTsum_ereal : (∑' n : ℕ, ((T k n).volume : EReal) : EReal) < (η k : EReal) := hT_sum k
                have h_inner_lt : (∑ n ∈ range M, (if (Nat.pair k n) < M then (T k n).volume else 0) : EReal) < (η k : EReal) :=
                  lt_of_le_of_lt (h_inner_bound k hk) hTsum_ereal
                -- Convert to ℝ and multiply by |B_k|
                have h_inner_real : (∑ n ∈ range M, (if (Nat.pair k n) < M then (T k n).volume else 0) : ℝ) < η k := by
                  exact_mod_cast h_inner_lt
                have hk_nonneg : 0 ≤ (B k).volume := Box.volume_nonneg _
                have h_mul : (B k).volume * (∑ n ∈ range M, (if (Nat.pair k n) < M then (T k n).volume else 0) : ℝ) ≤ (B k).volume * η k := by
                  nlinarith
                exact_mod_cast h_mul
          
          -- Step 4: the EReal finite sum ≤ ε/4
          calc
            ∑ m ∈ range M, ((S m).volume.toEReal : EReal) = (∑ m ∈ range M, (S m).volume : EReal) := by simp
            _ ≤ (∑ k ∈ range M, ((B k).volume : ℝ) * η k : EReal) := h_bound
            _ ≤ (∑ k ∈ range M, ((ε/4) / ((2 : ℝ)^(k+1 : ℕ)) : ℝ) : EReal) := by
              refine Finset.sum_le_sum (fun k hk => ?_)
              have hk_bound : ((B k).volume : ℝ) * η k ≤ (ε/4) / ((2 : ℝ)^(k+1 : ℕ)) := h_Bk_eta_bound k
              exact_mod_cast hk_bound
            _ = ((ε/4) * ∑ k ∈ range M, (1 / ((2 : ℝ)^(k+1 : ℕ))) : ℝ : EReal) := by ring
            _ < ((ε/4) * 1 : ℝ : EReal) := by
              have h_geom_lt : ∑ k ∈ range M, (1 / ((2 : ℝ)^(k+1 : ℕ))) < 1 := by
                calc
                  ∑ k ∈ range M, (1 / ((2 : ℝ)^(k+1 : ℕ))) = 1 - ((1 : ℝ)/2)^M := by
                    induction' M with M ih
                    · norm_num
                    · rw [sum_range_succ, ih]
                      have h_pow_succ : ((1 : ℝ)/2)^(M+1 : ℕ) = ((1 : ℝ)/2)^M * ((1 : ℝ)/2) := by simp [pow_succ]
                      rw [h_pow_succ]; ring
                  _ < 1 := by
                    have hpos : 0 < ((1 : ℝ)/2)^M := pow_pos (by norm_num) M
                    nlinarith
              have hpos_ε : 0 < (ε/4 : ℝ) := by linarith
              -- Need to apply this in EReal
              have h_ereal : (∑ k ∈ range M, ((ε/4) / ((2 : ℝ)^(k+1 : ℕ)) : ℝ) : EReal) < ((ε/4 : ℝ) : EReal) := by
                have h_real : (∑ k ∈ range M, (ε/4) / ((2 : ℝ)^(k+1 : ℕ)) : ℝ) < ε/4 := by
                  calc
                    (∑ k ∈ range M, (ε/4) / ((2 : ℝ)^(k+1 : ℕ)) : ℝ) = (ε/4) * (∑ k ∈ range M, 1 / ((2 : ℝ)^(k+1 : ℕ))) := by ring
                    _ < (ε/4) * 1 := by
                      refine mul_lt_mul_of_pos_left h_geom_lt (by linarith)
                    _ = ε/4 := by ring
                exact_mod_cast h_real
              -- Combine with the previous inequality
              calc
                (∑ k ∈ range M, ((B k).volume : ℝ) * η k : EReal) ≤ (∑ k ∈ range M, ((ε/4) / ((2 : ℝ)^(k+1 : ℕ)) : ℝ) : EReal) := by
                  simpa
                _ < (ε/4 : EReal) := h_ereal
        
        -- By EReal.tsum_le_of_sum_range_le_of_nonneg, the total tsum ≤ ε/4 < ε
        have h_tsum : ∑' m : ℕ, ((S m).volume.toEReal : EReal) ≤ (ε/4 : EReal) :=
          EReal.tsum_le_of_sum_range_le_of_nonneg hS_vol_nonneg h_partial_ereal
        have h_ε4_lt_ε : (ε/4 : EReal) < (ε : EReal) := by
          have : 0 < ε/4 := by linarith; exact_mod_cast this
        exact lt_of_le_of_lt h_tsum h_ε4_lt_ε
      
      unfold Lebesgue_outer_measure
      apply (sInf_le ?_).trans_lt hS_total
      · refine ⟨Set.univ, (fun (m : Set.univ) => S m.val), ?_, ?_⟩
        · have : (⋃ (m : Set.univ), (S m.val).toSet) = (⋃ m : ℕ, (S m).toSet) := by ext x; simp
          rw [this]; exact hS_cover
        · simp
    
    apply le_antisymm ?_ (Lebesgue_outer_measure.nonneg _)
    apply le_zero_of_forall_lt_pos (Lebesgue_outer_measure.nonneg _)
    exact h_forall_lt
