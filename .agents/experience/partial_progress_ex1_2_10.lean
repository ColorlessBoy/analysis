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
    clear ha_mem ha_ge0 ha_lt1

    by_cases h_others_exist : ∃ n, n ≠ k ∧ (I n).toSet ≠ ∅
    · let A : Set ℝ := {x | ∃ (n : ℕ), n ≠ k ∧ (I n).toSet ≠ ∅ ∧
        ∃ (d : ℝ), I n = BoundedInterval.Icc x d}
      have hA_nonempty : A.Nonempty := by
        rcases h_others_exist with ⟨n, hn_ne, hn_nonempty⟩
        rcases closed_eq_Icc_or_empty (h_closed n) with (⟨c, d, hIn⟩ | h_empty_n)
        · refine ⟨c, n, hn_ne, hn_nonempty, d, hIn⟩
        · rw [h_empty_n] at hn_nonempty; simp at hn_nonempty
      have hA_bdd_below : BddBelow A := by
        refine ⟨b, λ x hx => ?_⟩
        rcases hx with ⟨n, hn_ne, hn_nonempty, d, hIn⟩
        rw [hIn, BoundedInterval.set_Icc] at hn_nonempty
        have hcd : x ≤ d := by
          have h_nonempty : (Set.Icc x d).Nonempty := by
            rw [Set.nonempty_iff_ne_empty]; exact hn_nonempty
          rcases h_nonempty with ⟨z, hz⟩
          exact (Set.mem_Icc.1 hz).1.trans (Set.mem_Icc.1 hz).2
        have h_sub_n : Set.Icc x d ⊆ Set.Ico 0 1 := by
          calc
            Set.Icc x d = (I n : Set ℝ) := by rw [hIn, BoundedInterval.set_Icc]
            _ ⊆ ⋃ m, (I m : Set ℝ) := Set.subset_iUnion (fun m ↦ (I m : Set ℝ)) n
            _ = Set.Ico 0 1 := h_union
        have h_disj_kn : Disjoint (Set.Icc (0 : ℝ) b) (Set.Icc x d) := by
          have : Disjoint ((I k).toSet) ((I n).toSet) :=
            h_disj (Set.mem_univ k) (Set.mem_univ n) (by intro h; apply hn_ne; exact h.symm)
          rw [hIk, hIn, BoundedInterval.set_Icc, BoundedInterval.set_Icc, ha_eq_0] at this
          exact this
        have hbc : b < x :=
          disjoint_Icc_implies_lt_right
            (by simpa [ha_eq_0] using h_sub_k) h_sub_n h_disj_kn
            (by
              have h0_Icc : (0 : ℝ) ∈ Set.Icc (0 : ℝ) b := ⟨by norm_num, h0b⟩
              simpa [ha_eq_0] using h0_Icc) hcd
        exact hbc.le
      set c0 := sInf A with hc0_def
      have hc0_ge_b : b ≤ c0 := le_csInf hA_nonempty (by
        intro y hy; rcases hy with ⟨n, hn_ne, hn_nonempty, d, hIn⟩
        rw [hIn, BoundedInterval.set_Icc] at hn_nonempty
        have hcd : y ≤ d := by
          have h_nonempty : (Set.Icc y d).Nonempty := by
            rw [Set.nonempty_iff_ne_empty]; exact hn_nonempty
          rcases h_nonempty with ⟨z, hz⟩
          exact (Set.mem_Icc.1 hz).1.trans (Set.mem_Icc.1 hz).2
        have h_sub_n : Set.Icc y d ⊆ Set.Ico 0 1 := by
          calc
            Set.Icc y d = (I n : Set ℝ) := by rw [hIn, BoundedInterval.set_Icc]
            _ ⊆ ⋃ m, (I m : Set ℝ) := Set.subset_iUnion (fun m ↦ (I m : Set ℝ)) n
            _ = Set.Ico 0 1 := h_union
        have h_disj_kn : Disjoint (Set.Icc (0 : ℝ) b) (Set.Icc y d) := by
          have : Disjoint ((I k).toSet) ((I n).toSet) :=
            h_disj (Set.mem_univ k) (Set.mem_univ n) (by intro h; apply hn_ne; exact h.symm)
          rw [hIk, hIn, BoundedInterval.set_Icc, BoundedInterval.set_Icc, ha_eq_0] at this
          exact this
        have hby : b < y :=
          disjoint_Icc_implies_lt_right
            (by simpa [ha_eq_0] using h_sub_k) h_sub_n h_disj_kn
            (by
              have h0_Icc : (0 : ℝ) ∈ Set.Icc (0 : ℝ) b := ⟨by norm_num, h0b⟩
              simpa [ha_eq_0] using h0_Icc) hcd
        exact hby.le)
      by_cases hc0_gt_b : b < c0
      · set x := (b + c0) / 2 with hx_def
        have hc0_lt_one : c0 < 1 := by
          rcases hA_nonempty with ⟨a, ha⟩
          rcases ha with ⟨n, hn_ne, hn_nonempty, d, hIn⟩
          rw [hIn, BoundedInterval.set_Icc] at hn_nonempty
          have had : a ≤ d := by
            have h_nonempty : (Set.Icc a d).Nonempty := by
              rw [Set.nonempty_iff_ne_empty]; exact hn_nonempty
            rcases h_nonempty with ⟨z, hz⟩
            exact (Set.mem_Icc.1 hz).1.trans (Set.mem_Icc.1 hz).2
          have h_sub_n : Set.Icc a d ⊆ Set.Ico 0 1 := by
            calc
              Set.Icc a d = (I n : Set ℝ) := by rw [hIn, BoundedInterval.set_Icc]
              _ ⊆ ⋃ m, (I m : Set ℝ) := Set.subset_iUnion (fun m ↦ (I m : Set ℝ)) n
              _ = Set.Ico 0 1 := h_union
          have ha_mem_Icc : a ∈ Set.Icc a d := ⟨le_refl a, had⟩
          have ha_lt_one : a < 1 := (h_sub_n ha_mem_Icc).2
          have hc0_le_a : c0 ≤ a := csInf_le hA_bdd_below ha
          linarith
        have hx_Ico : x ∈ Set.Ico 0 1 := by
          dsimp [x]
          have hc0_nonneg : 0 ≤ c0 := by linarith
          constructor <;> nlinarith
        have hx_not_in_Ik : x ∉ (I k).toSet := by
          rw [hIk, BoundedInterval.set_Icc, ha_eq_0]
          intro hx; rcases hx with ⟨hx1, hx2⟩; nlinarith
        have hx_not_in_any : x ∉ ⋃ n, (I n).toSet := by
          intro hx
          rcases Set.mem_iUnion.mp hx with ⟨n, hn⟩
          by_cases hn_k : n = k
          · subst hn_k; exact hx_not_in_Ik hn
          · have hn_nonempty : (I n).toSet ≠ ∅ := by
              intro h; rw [h] at hn; simp at hn
            rcases closed_eq_Icc_or_empty (h_closed n) with (⟨c', d', hIn⟩ | h_empty_n)
            · have hn_nonempty_Icc : Set.Icc c' d' ≠ ∅ := by
                rw [hIn, BoundedInterval.set_Icc] at hn_nonempty; exact hn_nonempty
              rw [hIn, BoundedInterval.set_Icc] at hn
              have hc'd' : c' ≤ d' := by
                have h_nonempty : (Set.Icc c' d').Nonempty := by
                  rw [Set.nonempty_iff_ne_empty]; exact hn_nonempty_Icc
                rcases h_nonempty with ⟨z, hz⟩
                exact (Set.mem_Icc.1 hz).1.trans (Set.mem_Icc.1 hz).2
              have h_sub_n : Set.Icc c' d' ⊆ Set.Ico 0 1 := by
                calc
                  Set.Icc c' d' = (I n : Set ℝ) := by rw [hIn, BoundedInterval.set_Icc]
                  _ ⊆ ⋃ m, (I m : Set ℝ) := Set.subset_iUnion (fun m ↦ (I m : Set ℝ)) n
                  _ = Set.Ico 0 1 := h_union
              have h_disj_kn : Disjoint (Set.Icc (0 : ℝ) b) (Set.Icc c' d') := by
                have : Disjoint ((I k).toSet) ((I n).toSet) :=
                  h_disj (Set.mem_univ k) (Set.mem_univ n) (by intro h; apply hn_k; exact h.symm)
                rw [hIk, hIn, BoundedInterval.set_Icc, BoundedInterval.set_Icc, ha_eq_0] at this
                exact this
              have hbc' : b < c' :=
                disjoint_Icc_implies_lt_right
                  (by simpa [ha_eq_0] using h_sub_k) h_sub_n h_disj_kn
                  (by
                    have h0_Icc : (0 : ℝ) ∈ Set.Icc (0 : ℝ) b := ⟨by norm_num, h0b⟩
                    simpa [ha_eq_0] using h0_Icc) hc'd'
              have hc'_ge_c0 : c0 ≤ c' := by
                have hc'_mem_A : c' ∈ A := ⟨n, hn_k, hn_nonempty, d', hIn⟩
                exact csInf_le hA_bdd_below hc'_mem_A
              have : x < c' := by nlinarith
              have : x ∉ Set.Icc c' d' := by
                intro hx'; rcases hx' with ⟨hx1, hx2⟩; nlinarith
              exact this hn
            · rw [h_empty_n] at hn_nonempty; simp at hn_nonempty
        have hx_in_union : x ∈ ⋃ n, (I n).toSet := by
          rw [h_union]; exact hx_Ico
        exact hx_not_in_any hx_in_union
      · have hc0_eq_b : c0 = b := by linarith
        rcases hA_nonempty with ⟨c, hc_mem⟩
        rcases hc_mem with ⟨n, hn_ne, hn_nonempty, d, hIn⟩
        rw [hIn, BoundedInterval.set_Icc] at hn_nonempty
        have hcd : c ≤ d := by
          have h_nonempty : (Set.Icc c d).Nonempty := by
            rw [Set.nonempty_iff_ne_empty]; exact hn_nonempty
          rcases h_nonempty with ⟨z, hz⟩
          exact (Set.mem_Icc.1 hz).1.trans (Set.mem_Icc.1 hz).2
        have h_sub_n : Set.Icc c d ⊆ Set.Ico 0 1 := by
          calc
            Set.Icc c d = (I n : Set ℝ) := by rw [hIn, BoundedInterval.set_Icc]
            _ ⊆ ⋃ m, (I m : Set ℝ) := Set.subset_iUnion (fun m ↦ (I m : Set ℝ)) n
            _ = Set.Ico 0 1 := h_union
        have h_disj_kn : Disjoint (Set.Icc (0 : ℝ) b) (Set.Icc c d) := by
          have : Disjoint ((I k).toSet) ((I n).toSet) :=
            h_disj (Set.mem_univ k) (Set.mem_univ n) (by intro h; apply hn_ne; exact h.symm)
          rw [hIk, hIn, BoundedInterval.set_Icc, BoundedInterval.set_Icc, ha_eq_0] at this
          exact this
        have hbc : b < c :=
          disjoint_Icc_implies_lt_right
            (by simpa [ha_eq_0] using h_sub_k) h_sub_n h_disj_kn
            (by
              have h0_Icc : (0 : ℝ) ∈ Set.Icc (0 : ℝ) b := ⟨by norm_num, h0b⟩
              simpa [ha_eq_0] using h0_Icc) hcd
        set x := (b + c) / 2 with hx_def
        have hc_lt_one : c < 1 := by
          have hc_mem_Icc : c ∈ Set.Icc c d := ⟨le_refl c, hcd⟩
          exact (h_sub_n hc_mem_Icc).2
        have hx_Ico : x ∈ Set.Ico 0 1 := by
          dsimp [x]; constructor <;> nlinarith
        have hx_not_in_Ik : x ∉ (I k).toSet := by
          rw [hIk, BoundedInterval.set_Icc, ha_eq_0]
          intro hx; rcases hx with ⟨hx1, hx2⟩; nlinarith
        have hx_not_in_any : x ∉ ⋃ n, (I n).toSet := by
          intro hx
          rcases Set.mem_iUnion.mp hx with ⟨p, hp⟩
          by_cases hp_k : p = k
          · subst hp_k; exact hx_not_in_Ik hp
          · have hp_nonempty : (I p).toSet ≠ ∅ := by
              intro h; rw [h] at hp; simp at hp
            rcases closed_eq_Icc_or_empty (h_closed p) with (⟨c', d', hIp⟩ | h_empty_p)
            · have hp_nonempty_Icc : Set.Icc c' d' ≠ ∅ := by
                rw [hIp, BoundedInterval.set_Icc] at hp_nonempty; exact hp_nonempty
              rw [hIp, BoundedInterval.set_Icc] at hp
              have hc'd' : c' ≤ d' := by
                have h_nonempty : (Set.Icc c' d').Nonempty := by
                  rw [Set.nonempty_iff_ne_empty]; exact hp_nonempty_Icc
                rcases h_nonempty with ⟨z, hz⟩
                exact (Set.mem_Icc.1 hz).1.trans (Set.mem_Icc.1 hz).2
              have h_sub_p : Set.Icc c' d' ⊆ Set.Ico 0 1 := by
                calc
                  Set.Icc c' d' = (I p : Set ℝ) := by rw [hIp, BoundedInterval.set_Icc]
                  _ ⊆ ⋃ m, (I m : Set ℝ) := Set.subset_iUnion (fun m ↦ (I m : Set ℝ)) p
                  _ = Set.Ico 0 1 := h_union
              have h_disj_kp : Disjoint (Set.Icc (0 : ℝ) b) (Set.Icc c' d') := by
                have : Disjoint ((I k).toSet) ((I p).toSet) :=
                  h_disj (Set.mem_univ k) (Set.mem_univ p) (by intro h; apply hp_k; exact h.symm)
                rw [hIk, hIp, BoundedInterval.set_Icc, BoundedInterval.set_Icc, ha_eq_0] at this
                exact this
              have hbc' : b < c' :=
                disjoint_Icc_implies_lt_right
                  (by simpa [ha_eq_0] using h_sub_k) h_sub_p h_disj_kp
                  (by
                    have h0_Icc : (0 : ℝ) ∈ Set.Icc (0 : ℝ) b := ⟨by norm_num, h0b⟩
                    simpa [ha_eq_0] using h0_Icc) hc'd'
              have hc'_ge_c : c ≤ c' := by
                by_contra! hlt
                have hc'_mem_A : c' ∈ A := ⟨p, hp_k, hp_nonempty, d', hIp⟩
                have hc'_le_c0 : sInf A ≤ c' := csInf_le hA_bdd_below hc'_mem_A
                rw [← hc0_def] at hc'_le_c0
                nlinarith
              have : x < c' := by nlinarith
              have : x ∉ Set.Icc c' d' := by
                intro hx'; rcases hx' with ⟨hx1, hx2⟩; nlinarith
              exact this hp
            · rw [h_empty_p] at hp_nonempty; simp at hp_nonempty
        have hx_in_union : x ∈ ⋃ n, (I n).toSet := by
          rw [h_union]; exact hx_Ico
        exact hx_not_in_any hx_in_union
    · set x := (b + 1) / 2 with hx_def
      have hx_Ico : x ∈ Set.Ico 0 1 := by
        dsimp [x]; constructor <;> nlinarith
      have hx_not_in_Ik : x ∉ (I k).toSet := by
        rw [hIk, BoundedInterval.set_Icc, ha_eq_0]
        intro hx; rcases hx with ⟨hx1, hx2⟩; nlinarith
      have hx_not_in_any : x ∉ ⋃ n, (I n).toSet := by
        intro hx
        rcases Set.mem_iUnion.mp hx with ⟨n, hn⟩
        by_cases hn_k : n = k
        · subst hn_k; exact hx_not_in_Ik hn
        · have h_empty_n : (I n).toSet = ∅ := by
            by_contra! hne
            exact h_others_exist ⟨n, hn_k, Set.nonempty_iff_ne_empty.mp hne⟩
          rw [h_empty_n] at hn; simp at hn
      have hx_in_union : x ∈ ⋃ n, (I n).toSet := by
        rw [h_union]; exact hx_Ico
      exact hx_not_in_any hx_in_union
  · rw [h_empty] at hk; simp at hk