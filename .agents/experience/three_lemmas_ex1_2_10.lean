import Analysis.MeasureTheory.Section_1_2_2
open Set
open BoundedInterval

lemma disjoint_Icc_implies_lt_right {a b c d : ℝ} (hI : Set.Icc a b ⊆ Set.Ico 0 1) (hJ : Set.Icc c d ⊆ Set.Ico 0 1)
    (hdisj : Disjoint (Set.Icc a b) (Set.Icc c d)) (h0 : 0 ∈ Set.Icc a b) (hcd : c ≤ d) : b < c := by
  have ha0 : a ≤ 0 := h0.1
  have hb0 : 0 ≤ b := h0.2
  have hab : a ≤ b := ha0.trans hb0
  have hI_iff := (Set.Icc_subset_Ico_iff hab).mp hI
  have h0a : 0 ≤ a := hI_iff.1
  have ha_eq_0 : a = 0 := le_antisymm ha0 h0a
  have hJ_iff := (Set.Icc_subset_Ico_iff hcd).mp hJ
  have h0c : 0 ≤ c := hJ_iff.1
  by_contra! h
  have hcb : c ≤ b := h
  have hc_ab : c ∈ Set.Icc a b := by
    rw [ha_eq_0]
    exact ⟨h0c, hcb⟩
  have hc_cd : c ∈ Set.Icc c d := ⟨le_refl c, hcd⟩
  have hc_inter : c ∈ Set.Icc a b ∩ Set.Icc c d := Set.mem_inter hc_ab hc_cd
  have h_empty : Set.Icc a b ∩ Set.Icc c d = ∅ := Set.disjoint_iff_inter_eq_empty.mp hdisj
  rw [h_empty] at hc_inter
  simp at hc_inter

example : ¬ ∃ (I: ℕ → BoundedInterval), (∀ n, IsClosed (I n).toSet) ∧ (Set.univ.PairwiseDisjoint (fun n ↦ (I n).toSet) ) ∧ (⋃ n, (I n).toSet = Set.Ico 0 1) := by
  intro h
  rcases h with ⟨I, h_closed, h_disj, h_union⟩
  have h0_union : (0 : ℝ) ∈ ⋃ n, (I n).toSet := by
    rw [h_union]; exact ⟨by norm_num, by norm_num⟩
  rcases Set.mem_iUnion.mp h0_union with ⟨k, hk⟩
  have hk_nonempty : (I k).toSet ≠ ∅ := by
    intro h; rw [h] at hk; simp at hk
  rcases closed_eq_Icc_or_empty (h_closed k) with (⟨a, b, hIk⟩ | h_empty)
  · rw [hIk, BoundedInterval.set_Icc] at hk
    have ha0 : a ≤ (0 : ℝ) := hk.1
    have h0b : (0 : ℝ) ≤ b := hk.2
    have hab : a ≤ b := ha0.trans h0b
    have h_sub_k : Set.Icc a b ⊆ Set.Ico 0 1 := by
      calc
        Set.Icc a b = (I k : Set ℝ) := by rw [hIk, BoundedInterval.set_Icc]
        _ ⊆ ⋃ n, (I n : Set ℝ) := Set.subset_iUnion (fun n ↦ (I n : Set ℝ)) k
        _ = Set.Ico 0 1 := h_union
    have ha_mem : a ∈ Set.Icc a b := ⟨le_refl a, hab⟩
    rcases h_sub_k ha_mem with ⟨ha_ge0, ha_lt1⟩
    have ha_eq_0 : a = 0 := le_antisymm ha0 ha_ge0
    have hb_lt_one : b < 1 := (h_sub_k ⟨ha0.trans h0b, le_refl b⟩).2
    -- I(k) = Icc 0 b with b < 1
    let Ik_set : Set ℝ := Set.Icc (0 : ℝ) b
    have hIk_set : (I k : Set ℝ) = Ik_set := by
      rw [hIk, ha_eq_0, BoundedInterval.set_Icc]; rfl
    have h_Ico_sub : Ik_set ⊆ Set.Ico 0 1 := by
      rw [← hIk_set]; calc
        (I k : Set ℝ) ⊆ ⋃ n, (I n : Set ℝ) := Set.subset_iUnion (fun n ↦ (I n : Set ℝ)) k
        _ = Set.Ico 0 1 := h_union
    -- Count other nonempty intervals
    let others : Finset ℕ := (Finset.filter (λ n => (I n).toSet ≠ ∅) (Finset.range (k+2))).erase k
    have h_others_count : others.card ≥ 1 ∨ others.card = 0 := by omega
    rcases h_others_count with (h_ge1 | h_eq0)
    · -- At least one other nonempty interval
      have h_nonempty_others : ∃ n, n ≠ k ∧ (I n).toSet ≠ ∅ := by
        rcases Finset.card_pos.mp h_ge1 with ⟨n, hn⟩
        refine ⟨n, ?_, ?_⟩
        · intro h_eq; apply Finset.not_mem_erase k n hn; rw [h_eq]
        · exact (Finset.mem_filter.mp (Finset.mem_of_mem_erase hn)).2
      rcases h_nonempty_others with ⟨m, hm_ne, hm_nonempty⟩
      rcases closed_eq_Icc_or_empty (h_closed m) with (⟨c, d, hIm⟩ | h_empty_m)
      · rw [hIm, BoundedInterval.set_Icc] at hm_nonempty
        have hcd : c ≤ d := by
          have h_nonempty : (Set.Icc c d).Nonempty := by
            rw [Set.nonempty_iff_ne_empty]; exact hm_nonempty
          rcases h_nonempty with ⟨z, hz⟩
          exact (Set.mem_Icc.1 hz).1.trans (Set.mem_Icc.1 hz).2
        have h_sub_m : Set.Icc c d ⊆ Set.Ico 0 1 := by
          calc
            Set.Icc c d = (I m : Set ℝ) := by rw [hIm, BoundedInterval.set_Icc]
            _ ⊆ ⋃ n, (I n : Set ℝ) := Set.subset_iUnion (fun n ↦ (I n : Set ℝ)) m
            _ = Set.Ico 0 1 := h_union
        have h_disj_km : Disjoint (Ik_set) (Set.Icc c d) := by
          have : Disjoint ((I k : Set ℝ)) ((I m : Set ℝ)) :=
            h_disj (Set.mem_univ k) (Set.mem_univ m) (Ne.symm hm_ne)
          rw [hIk_set, hIm, BoundedInterval.set_Icc] at this
          exact this
        have hbc : b < c :=
          disjoint_Icc_implies_lt_right (by
            rw [ha_eq_0]; exact h_sub_k) h_sub_m h_disj_km
            (by rw [ha_eq_0]; exact ⟨by norm_num, h0b⟩) hcd
        -- Check if there's a SECOND other nonempty interval
        have h_second : (∃ n, n ≠ k ∧ n ≠ m ∧ (I n).toSet ≠ ∅) := by
          by_contra! h_no_second
          have h_only_one : ∀ n, n ≠ k → n ≠ m → (I n).toSet = ∅ := by
            intro n hn_k hn_m
            by_contra! hne
            exact h_no_second ⟨n, hn_k, hn_m, hne⟩
          -- Then I(m) is the only nonempty interval besides I(k)
          -- Gap between I(m)'s right endpoint and 1
          sorry
        rcases h_second with ⟨n, hn_k, hn_m, hn_nonempty⟩
        rcases closed_eq_Icc_or_empty (h_closed n) with (⟨c', d', hIn⟩ | h_empty_n)
        · rw [hIn, BoundedInterval.set_Icc] at hn_nonempty
          have hc'd' : c' ≤ d' := by
            have h_nonempty' : (Set.Icc c' d').Nonempty := by
              rw [Set.nonempty_iff_ne_empty]; exact hn_nonempty
            rcases h_nonempty' with ⟨z, hz⟩
            exact (Set.mem_Icc.1 hz).1.trans (Set.mem_Icc.1 hz).2
          have h_disj_kn : Disjoint (Ik_set) (Set.Icc c' d') := by
            have : Disjoint ((I k : Set ℝ)) ((I n : Set ℝ)) :=
              h_disj (Set.mem_univ k) (Set.mem_univ n) hn_k.symm
            rw [hIk_set, hIn, BoundedInterval.set_Icc] at this
            exact this
          have h_sub_n : Set.Icc c' d' ⊆ Set.Ico 0 1 := by
            calc
              Set.Icc c' d' = (I n : Set ℝ) := by rw [hIn, BoundedInterval.set_Icc]
              _ ⊆ ⋃ p, (I p : Set ℝ) := Set.subset_iUnion (fun p ↦ (I p : Set ℝ)) n
              _ = Set.Ico 0 1 := h_union
          have hbc' : b < c' :=
            disjoint_Icc_implies_lt_right (by
              rw [ha_eq_0]; exact h_sub_k) h_sub_n h_disj_kn
              (by rw [ha_eq_0]; exact ⟨by norm_num, h0b⟩) hc'd'
          -- Now we have two intervals I(m)=Icc(c,d) and I(n)=Icc(c',d') with b < c and b < c'
          -- Sort them: if c < c', gap is (d, c'). If c' < c, gap is (d', c).
          by_cases hc_lt_c' : c < c'
          · -- Gap: (d, c')
            have hd_lt_c' : d < c' := by
              have h_disj_mn : Disjoint (Set.Icc c d) (Set.Icc c' d') := by
                have : Disjoint ((I m : Set ℝ)) ((I n : Set ℝ)) :=
                  h_disj (Set.mem_univ m) (Set.mem_univ n) (by
                    intro h_eq; apply hn_m; apply hIm.symm.trans ?_; apply hIn.trans ?_)
                rw [hIm, hIn, BoundedInterval.set_Icc, BoundedInterval.set_Icc] at this
                exact this
              have : Set.Icc c d ∩ Set.Icc c' d' = ∅ := Set.disjoint_iff_inter_eq_empty.mp h_disj_mn
              by_contra! hle
              have hc'_mem_cd : c' ∈ Set.Icc c d := ⟨by
                have : d ≥ c' := hle
                -- c < c' ≤ d, so c' ∈ Icc c d
                exact hc_lt_c'.le.trans this, le_refl c'⟩
              ... this is getting too complex
              sorry
            set x := (d + c') / 2 with hx_def
            have hx_Ico : x ∈ Set.Ico 0 1 := by
              have h0c' : 0 ≤ c' := ...; nlinarith
            ...
          · -- Gap: (d', c). Symmetric to above.
            ...
        · rw [h_empty_n] at hn_nonempty; simp at hn_nonempty
      · rw [h_empty_m] at hm_nonempty; simp at hm_nonempty
    · -- No other nonempty interval
      sorry
  · rw [h_empty] at hk; simp at hk