import Analysis.MeasureTheory.Section_1_1_2

open BoundedInterval
open Pointwise
open MeasureTheory

set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

/-
The originally proposed `metric_entropy_lower_box_count` used `⌈I.a * 2^n⌉` for
all four kinds of bounded interval.  This is false for intervals open on the left:
for example, at scale zero `[0,1)` is not contained in `(0,1)`, although the
proposed right-hand side counts its index.  We retain the corrected lower index.
-/
noncomputable def BoundedInterval.dyadicLowerIndex (I : BoundedInterval) (n : ℤ) : ℤ :=
  match I with
  | .Ioo a _ | .Ioc a _ => ⌊a * 2^n⌋ + 1
  | .Icc a _ | .Ico a _ => ⌈a * 2^n⌉

lemma dyadic_box_toSet_subset_iff {d : ℕ} (B : Box d) (n : ℤ) (i : Fin d → ℤ) :
    (Box.dyadic n i).toSet ⊆ B.toSet ↔
      ∀ j : Fin d, (Box.dyadic n i).side j ⊆ B.side j := by
  simp +decide [ Set.subset_def, Box.mem_toSet ];
  refine' ⟨ fun h j x hx₁ hx₂ => _, fun h x hx j => _ ⟩;
  · contrapose! h;
    refine' ⟨ .toLp 2 ( fun k => if k = j then x else ( i k : ℝ ) / 2 ^ n ), _, j, _ ⟩ <;> simp_all +decide [ div_eq_mul_inv ];
    grind;
  · exact h j _ ( hx j |>.1 ) ( hx j |>.2 )

lemma dyadic_interval_subset_iff (I : BoundedInterval) (n i : ℤ) :
    BoundedInterval.Ico ((i : ℝ) / 2^n) ((i + 1 : ℤ) / 2^n) ⊆ I ↔
      I.dyadicLowerIndex n ≤ i ∧ i < ⌊I.b * 2^n⌋ := by
  cases' I with a b;
  · constructor <;> intro h <;> simp_all +decide [ div_lt_iff₀, lt_div_iff₀, BoundedInterval.dyadicLowerIndex ];
    · constructor;
      · have := h ( Set.left_mem_Ico.mpr <| by rw [ div_lt_div_iff_of_pos_right ( by positivity ) ] ; linarith ) ; norm_num at this;
        exact Int.floor_lt.mpr ( by rw [ lt_div_iff₀ ( by positivity ) ] at this; linarith );
      · refine' Int.le_floor.2 _;
        have := h ( show ( i : ℝ ) / 2 ^ n ∈ Set.Ico ( ( i : ℝ ) / 2 ^ n ) ( ( i + 1 : ℝ ) / 2 ^ n ) from ⟨ le_rfl, by rw [ div_lt_div_iff_of_pos_right ( by positivity ) ] ; linarith ⟩ ) ; norm_num at *;
        contrapose! h;
        rw [ Set.not_subset ];
        refine' ⟨ ( i + 1 ) / 2 ^ n - ( ( i + 1 ) / 2 ^ n - b ) / 2, _, _ ⟩ <;> norm_num;
        · constructor <;> nlinarith [ show ( 0 : ℝ ) < 2 ^ n by positivity, mul_div_cancel₀ ( ( i : ℝ ) : ℝ ) ( show ( 2 ^ n : ℝ ) ≠ 0 by positivity ), mul_div_cancel₀ ( ( i + 1 : ℝ ) : ℝ ) ( show ( 2 ^ n : ℝ ) ≠ 0 by positivity ), mul_div_cancel₀ ( ( i + 1 : ℝ ) / 2 ^ n - b ) ( show ( 2 : ℝ ) ≠ 0 by positivity ) ];
        · intro h';
          linarith! [ show ( i + 1 : ℝ ) / 2 ^ n ≥ b by exact le_of_lt ( by rw [ lt_div_iff₀ ( by positivity ) ] ; linarith! ) ];
    · intro x hx;
      constructor <;> nlinarith [ hx.1, hx.2, show ( 2 : ℝ ) ^ n > 0 by positivity, mul_div_cancel₀ ( i : ℝ ) ( show ( 2 : ℝ ) ^ n ≠ 0 by positivity ), mul_div_cancel₀ ( i + 1 : ℝ ) ( show ( 2 : ℝ ) ^ n ≠ 0 by positivity ), Int.floor_le ( a * 2 ^ n ), Int.lt_floor_add_one ( a * 2 ^ n ), Int.floor_le ( b * 2 ^ n ), Int.lt_floor_add_one ( b * 2 ^ n ), show ( i : ℝ ) ≥ ⌊a * 2 ^ n⌋ + 1 by exact_mod_cast h.1, show ( i : ℝ ) + 1 ≤ ⌊b * 2 ^ n⌋ by exact_mod_cast h.2 ];
  · constructor <;> intro H <;> simp_all +decide [ div_le_iff₀, le_div_iff₀ ];
    · rename_i a b;
      constructor;
      · have := H ( Set.left_mem_Ico.mpr ?_ ) ; norm_num at *;
        · exact Int.ceil_le.mpr ( by rw [ le_div_iff₀ ( by positivity ) ] at *; linarith );
        · gcongr ; norm_num;
      · refine' Int.le_floor.mpr _;
        have := H ( show ( i : ℝ ) / 2 ^ n ∈ Set.Ico ( ( i : ℝ ) / 2 ^ n ) ( ( i + 1 : ℝ ) / 2 ^ n ) from ⟨ le_rfl, by rw [ div_lt_div_iff_of_pos_right ( by positivity ) ] ; linarith ⟩ ) ; norm_num at *;
        contrapose! H;
        rw [ Set.not_subset ];
        refine' ⟨ ( i + 1 ) / 2 ^ n - ( ( i + 1 ) / 2 ^ n - b ) / 2, _, _ ⟩ <;> norm_num;
        · constructor <;> nlinarith [ show ( 0 : ℝ ) < 2 ^ n by positivity, mul_div_cancel₀ ( ( i : ℝ ) + 1 ) ( by positivity : ( 2 : ℝ ) ^ n ≠ 0 ), mul_div_cancel₀ ( ( i : ℝ ) ) ( by positivity : ( 2 : ℝ ) ^ n ≠ 0 ) ];
        · intro h; nlinarith [ show ( 0 : ℝ ) < 2 ^ n by positivity, mul_div_cancel₀ ( ( i : ℝ ) + 1 ) ( show ( 2 : ℝ ) ^ n ≠ 0 by positivity ), mul_div_cancel₀ ( ( i : ℝ ) ) ( show ( 2 : ℝ ) ^ n ≠ 0 by positivity ) ] ;
    · intro x hx; constructor <;> norm_num [ div_le_iff₀, le_div_iff₀ ] at *;
      · rw [ div_le_iff₀ ( by positivity ) ] at hx;
        rw [ BoundedInterval.dyadicLowerIndex ] at H;
        rw [ Int.ceil_le ] at H ; nlinarith [ show ( 0 : ℝ ) < 2 ^ n by positivity ];
      · rw [ lt_div_iff₀ ( by positivity ) ] at *;
        rw [ Int.lt_iff_add_one_le, Int.le_floor ] at * ; norm_num at * ; nlinarith [ show ( 0 : ℝ ) < 2 ^ n by positivity ];
  · rename_i a b;
    constructor <;> intro h <;> simp_all +decide [ BoundedInterval.dyadicLowerIndex ];
    · constructor;
      · have := @h ( ↑i / 2 ^ n ) ; norm_num at *;
        exact Int.floor_lt.mpr ( by have := this ( by gcongr ; norm_num ) ; rw [ lt_div_iff₀ ( by positivity ) ] at this; linarith );
      · rw [ Int.lt_iff_add_one_le, Int.le_floor ];
        have := h ( show ( i : ℝ ) / 2 ^ n ∈ Set.Ico ( ( i : ℝ ) / 2 ^ n ) ( ( i + 1 : ℝ ) / 2 ^ n ) from ⟨ le_rfl, by rw [ div_lt_div_iff_of_pos_right ( by positivity ) ] ; linarith ⟩ ) ; norm_num at *;
        contrapose! h;
        rw [ Set.not_subset ];
        refine' ⟨ ( i + 1 ) / 2 ^ n - ( ( i + 1 ) / 2 ^ n - b ) / 2, _, _ ⟩ <;> norm_num;
        · constructor <;> nlinarith [ show ( 0 : ℝ ) < 2 ^ n by positivity, mul_div_cancel₀ ( ( i : ℝ ) + 1 ) ( by positivity : ( 2 : ℝ ) ^ n ≠ 0 ), mul_div_cancel₀ ( ( i : ℝ ) ) ( by positivity : ( 2 : ℝ ) ^ n ≠ 0 ), show ( Ioc a b ).b = b by rfl, mul_div_cancel₀ ( ( Ioc a b ).b * 2 ^ n ) ( by positivity : ( 2 : ℝ ) ^ n ≠ 0 ) ];
        · intro h';
          linarith [ show ( i + 1 : ℝ ) / 2 ^ n > b by rw [ gt_iff_lt ] ; rw [ lt_div_iff₀ ( by positivity ) ] ; linarith! ];
    · intro x hx; constructor <;> nlinarith [ hx.1, hx.2, show ( 2 : ℝ ) ^ n > 0 by positivity, mul_div_cancel₀ ( i : ℝ ) ( show ( 2 : ℝ ) ^ n ≠ 0 by positivity ), mul_div_cancel₀ ( i + 1 : ℝ ) ( show ( 2 : ℝ ) ^ n ≠ 0 by positivity ), Int.floor_le ( a * 2 ^ n ), Int.lt_floor_add_one ( a * 2 ^ n ), Int.floor_le ( b * 2 ^ n ), Int.lt_floor_add_one ( b * 2 ^ n ), show ( i : ℝ ) ≥ ⌊a * 2 ^ n⌋ + 1 by exact_mod_cast h.1, show ( i : ℝ ) + 1 ≤ ⌊b * 2 ^ n⌋ by exact_mod_cast h.2 ] ;
  · constructor;
    · intro h;
      simp_all +decide [ Set.Ico_subset_Ico_iff, div_le_iff₀, lt_div_iff₀ ];
      rw [ Set.Ico_subset_Ico_iff ] at h;
      · constructor;
        · exact Int.ceil_le.mpr ( by rw [ le_div_iff₀ ( by positivity ) ] at *; norm_cast at *; linarith );
        · exact Int.le_floor.2 ( by rw [ div_le_iff₀ ( by positivity ) ] at h; norm_num at *; linarith );
      · gcongr ; norm_num;
    · intro h;
      refine' Set.Ico_subset_Ico _ _;
      · rw [ le_div_iff₀ ( by positivity ) ];
        exact le_trans ( Int.le_ceil _ ) ( mod_cast h.1 );
      · rw [ div_le_iff₀ ( by positivity ) ];
        exact le_trans ( mod_cast h.2 ) ( Int.floor_le _ )

lemma dyadic_box_subset_iff {d : ℕ} (B : Box d) (n : ℤ) (i : Fin d → ℤ) :
    (Box.dyadic n i).toSet ⊆ B.toSet ↔
      ∀ j : Fin d, (B.side j).dyadicLowerIndex n ≤ i j ∧ i j < ⌊(B.side j).b * 2^n⌋ := by
  rw [dyadic_box_toSet_subset_iff]
  apply forall_congr'
  intro j
  simpa [Box.dyadic] using dyadic_interval_subset_iff (B.side j) n (i j)

/-
Corrected exact count, accounting for whether each interval is open on the left.
-/
lemma metric_entropy_lower_box_count {d:ℕ} (B : Box d) (n : ℤ) :
    metric_entropy_lower (B.toSet) n =
      ∏ j : Fin d,
        (Finset.Ico ((B.side j).dyadicLowerIndex n) ⌊(B.side j).b * 2^n⌋).card := by
  have h_eq : { i : Fin d → ℤ | (Box.dyadic n i).toSet ⊆ B.toSet } = { i : Fin d → ℤ | ∀ j : Fin d, (B.side j).dyadicLowerIndex n ≤ i j ∧ i j < ⌊(B.side j).b * 2^n⌋ } := by
    exact Set.ext fun x => by simpa using dyadic_box_subset_iff B n x;
  rw [show metric_entropy_lower B.toSet n = Nat.card { i : Fin d → ℤ |
      (Box.dyadic n i).toSet ⊆ B.toSet } from rfl, h_eq]
  let e : { i : Fin d → ℤ | ∀ j : Fin d,
      (B.side j).dyadicLowerIndex n ≤ i j ∧ i j < ⌊(B.side j).b * 2^n⌋ } ≃
      (∀ j : Fin d, Finset.Ico ((B.side j).dyadicLowerIndex n) ⌊(B.side j).b * 2^n⌋) :=
    ⟨fun x j => ⟨x.val j, Finset.mem_Ico.mpr (x.prop j)⟩,
     fun x => ⟨fun j => x j, fun j => Finset.mem_Ico.mp (x j).prop⟩,
     fun _ => rfl, fun _ => rfl⟩
  rw [Nat.card_congr e]
  simp

/-
For a box B, the scaled lower dyadic entropy converges to its volume.
-/
lemma metric_entropy_lower_box_tendsto {d:ℕ} (B : Box d) :
    Filter.atTop.Tendsto (fun n:ℤ ↦ (2:ℝ)^(-(d*n:ℤ)) * (metric_entropy_lower (B.toSet) n : ℝ)) (nhds |B|ᵥ) := by
  have h_count : ∀ n : ℤ, (metric_entropy_lower (B.toSet) n : ℝ) = ∏ j : Fin d, ((Finset.Ico ((B.side j).dyadicLowerIndex n) ⌊(B.side j).b * 2^n⌋).card : ℝ) := by
    intro n; exact_mod_cast metric_entropy_lower_box_count B n
  have h_1d (I : BoundedInterval) : Filter.atTop.Tendsto (fun n:ℤ ↦ (2:ℝ)^(-n) * ((Finset.Ico (I.dyadicLowerIndex n) ⌊I.b * 2 ^ n⌋).card : ℝ)) (nhds |I|ₗ) := by
    rcases I with ( _ | _ | _ | _ ) <;> norm_num [ BoundedInterval.length ];
    · rename_i a b;
      have h_1d : Filter.Tendsto (fun n : ℤ => (2 : ℝ) ^ (-n) * (Finset.Ico (⌊a * 2^n⌋ + 1) ⌊b * 2^n⌋).card) Filter.atTop (nhds (max (b - a) 0)) := by
        have := dyadic_count_tendsto a b;
        have h_1d : ∀ n : ℤ, (Finset.Ico (⌊a * 2^n⌋ + 1) ⌊b * 2^n⌋).card ≤ (Finset.Ico (⌈a * 2^n⌉) ⌊b * 2^n⌋).card ∧ (Finset.Ico (⌈a * 2^n⌉) ⌊b * 2^n⌋).card ≤ (Finset.Ico (⌊a * 2^n⌋ + 1) ⌊b * 2^n⌋).card + 1 := by
          intro n; constructor <;> norm_num [ Int.toNat_of_nonneg ] ;
          · exact Or.inl ( by linarith [ Int.ceil_le_floor_add_one ( a * 2 ^ n ) ] );
          · cases max_cases ( ⌊b * 2 ^ n⌋ - ( ⌊a * 2 ^ n⌋ + 1 ) ) 0 <;> linarith [ Int.floor_le_ceil ( a * 2 ^ n ), Int.ceil_le_floor_add_one ( a * 2 ^ n ) ];
        have h_1d : Filter.Tendsto (fun n : ℤ => (2 : ℝ) ^ (-n) * (Finset.Ico (⌈a * 2^n⌉) ⌊b * 2^n⌋).card - (2 : ℝ) ^ (-n) * (Finset.Ico (⌊a * 2^n⌋ + 1) ⌊b * 2^n⌋).card) Filter.atTop (nhds 0) := by
          have h_1d : ∀ n : ℤ, |(2 : ℝ) ^ (-n) * (Finset.Ico (⌈a * 2^n⌉) ⌊b * 2^n⌋).card - (2 : ℝ) ^ (-n) * (Finset.Ico (⌊a * 2^n⌋ + 1) ⌊b * 2^n⌋).card| ≤ (2 : ℝ) ^ (-n) := by
            intro n; rw [ abs_le ] ; constructor <;> nlinarith [ h_1d n, show ( 0 : ℝ ) ≤ 2 ^ ( -n : ℤ ) by positivity, show ( Finset.card ( Finset.Ico ⌈a * 2 ^ n⌉ ⌊b * 2 ^ n⌋ ) : ℝ ) ≤ Finset.card ( Finset.Ico ( ⌊a * 2 ^ n⌋ + 1 ) ⌊b * 2 ^ n⌋ ) + 1 by exact_mod_cast h_1d n |>.2, show ( Finset.card ( Finset.Ico ( ⌊a * 2 ^ n⌋ + 1 ) ⌊b * 2 ^ n⌋ ) : ℝ ) ≤ Finset.card ( Finset.Ico ⌈a * 2 ^ n⌉ ⌊b * 2 ^ n⌋ ) by exact_mod_cast h_1d n |>.1 ] ;
          refine' squeeze_zero_norm h_1d _;
          norm_num [ ← Real.rpow_intCast, ← Real.rpow_neg ];
          norm_num [ Real.rpow_def_of_pos ];
          exact Filter.Tendsto.const_mul_atTop ( by positivity ) ( tendsto_intCast_atTop_atTop );
        convert this.sub h_1d using 2 <;> ring;
      convert h_1d using 2 ; norm_num [ BoundedInterval.dyadicLowerIndex ];
    · convert dyadic_count_tendsto _ _ using 2 ; norm_num [ BoundedInterval.dyadicLowerIndex ];
    · rename_i a b;
      by_cases hab : a < b;
      · have h_approx : ∀ n : ℤ, n ≥ 0 → |(2 : ℝ) ^ (-n : ℤ) * ((Finset.Ico (⌊a * 2 ^ n⌋ + 1) (⌊b * 2 ^ n⌋)).card : ℝ) - (b - a)| ≤ 2 * (2 : ℝ) ^ (-n : ℤ) := by
          intro n hn; rw [ abs_le ] ; constructor <;> norm_num [ zpow_neg, zpow_ofNat ];
          · field_simp;
            nlinarith [ Int.floor_le ( b * 2 ^ n ), Int.lt_floor_add_one ( b * 2 ^ n ), Int.floor_le ( 2 ^ n * a ), Int.lt_floor_add_one ( 2 ^ n * a ), show ( 2 : ℝ ) ^ n > 0 by positivity, show ( ⌊b * 2 ^ n⌋ : ℝ ) - ( ⌊2 ^ n * a⌋ + 1 ) ≤ ↑ ( Int.toNat ( ⌊b * 2 ^ n⌋ - ( ⌊2 ^ n * a⌋ + 1 ) ) ) by exact_mod_cast Int.self_le_toNat _ ];
          · field_simp;
            rw [ ← Int.cast_natCast ] ; norm_num;
            constructor <;> nlinarith [ Int.floor_le ( ( 2 : ℝ ) ^ n * b ), Int.lt_floor_add_one ( ( 2 : ℝ ) ^ n * b ), Int.floor_le ( ( 2 : ℝ ) ^ n * a ), Int.lt_floor_add_one ( ( 2 : ℝ ) ^ n * a ), show ( 2 : ℝ ) ^ n ≥ 1 by exact one_le_zpow₀ ( by norm_num ) hn ];
        have h_approx : Filter.Tendsto (fun n : ℤ => (2 : ℝ) ^ (-n : ℤ) * ((Finset.Ico (⌊a * 2 ^ n⌋ + 1) (⌊b * 2 ^ n⌋)).card : ℝ)) Filter.atTop (nhds (b - a)) := by
          have h_approx : Filter.Tendsto (fun n : ℤ => (2 : ℝ) ^ (-n : ℤ)) Filter.atTop (nhds 0) := by
            norm_num [ ← Real.rpow_intCast, Real.rpow_def_of_pos ];
            exact tendsto_inv_atTop_zero.comp <| Real.tendsto_exp_atTop.comp <| Filter.Tendsto.const_mul_atTop ( by positivity ) <| tendsto_intCast_atTop_atTop;
          exact tendsto_iff_norm_sub_tendsto_zero.mpr <| squeeze_zero_norm' ( Filter.eventually_atTop.mpr ⟨ 0, fun n hn => by simpa using ‹∀ n : ℤ, n ≥ 0 → |2 ^ ( -n : ℤ ) * ↑ ( Finset.Ico ( ⌊a * 2 ^ n⌋ + 1 ) ⌊b * 2 ^ n⌋ ).card - ( b - a )| ≤ 2 * 2 ^ ( -n : ℤ ) › n hn ⟩ ) <| by simpa using h_approx.const_mul 2;
        convert h_approx using 2 ; norm_num [ BoundedInterval.dyadicLowerIndex ];
        exact max_eq_left ( by linarith! );
      · simp_all +decide [ BoundedInterval.b, BoundedInterval.a, BoundedInterval.dyadicLowerIndex ];
        refine' tendsto_const_nhds.congr' _;
        filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn using by rw [ Int.toNat_of_nonpos ( by linarith [ show ⌊b * 2 ^ n⌋ ≤ ⌊a * 2 ^ n⌋ by exact Int.floor_mono <| by nlinarith [ show ( 2 : ℝ ) ^ n > 0 by positivity ] ] ) ] ; ring;
    · convert dyadic_count_tendsto _ _ using 2;
      norm_num [ zpow_neg, BoundedInterval.dyadicLowerIndex ]
  have h_conv : Filter.atTop.Tendsto (fun n:ℤ ↦ ∏ j : Fin d, ((2:ℝ)^(-n) * ((Finset.Ico ((B.side j).dyadicLowerIndex n) ⌊(B.side j).b * 2 ^ n⌋).card : ℝ))) (nhds (∏ j : Fin d, |B.side j|ₗ)) := by
    refine tendsto_finset_prod (Finset.univ : Finset (Fin d)) (fun j _ => ?_)
    exact (h_1d (B.side j)).comp (show Filter.Tendsto id Filter.atTop Filter.atTop from Filter.tendsto_id)
  have h_factor (n : ℤ) : (2:ℝ)^(-(d*n:ℤ)) * (metric_entropy_lower (B.toSet) n : ℝ) = ∏ j : Fin d, ((2:ℝ)^(-n) * ((Finset.Ico ((B.side j).dyadicLowerIndex n) ⌊(B.side j).b * 2 ^ n⌋).card : ℝ)) := by
    rw [h_count n]
    calc
      (2 : ℝ) ^ (-(d * n : ℤ)) * ∏ j : Fin d, ((Finset.Ico ((B.side j).dyadicLowerIndex n) ⌊(B.side j).b * 2 ^ n⌋).card : ℝ)
          = (2 : ℝ) ^ ((-n : ℤ) * (d : ℤ)) * ∏ j : Fin d, ((Finset.Ico ((B.side j).dyadicLowerIndex n) ⌊(B.side j).b * 2 ^ n⌋).card : ℝ) := by
            have h_exp : -(d * n : ℤ) = (-n : ℤ) * (d : ℤ) := by ring
            rw [h_exp]
      _ = ((2 : ℝ) ^ (-n : ℤ)) ^ (d : ℤ) * ∏ j : Fin d, ((Finset.Ico ((B.side j).dyadicLowerIndex n) ⌊(B.side j).b * 2 ^ n⌋).card : ℝ) := by
        simp [zpow_mul]
      _ = ((2 : ℝ) ^ (-n : ℤ)) ^ d * ∏ j : Fin d, ((Finset.Ico ((B.side j).dyadicLowerIndex n) ⌊(B.side j).b * 2 ^ n⌋).card : ℝ) := by
        norm_cast
      _ = (∏ j : Fin d, (2 : ℝ) ^ (-n : ℤ)) * ∏ j : Fin d, ((Finset.Ico ((B.side j).dyadicLowerIndex n) ⌊(B.side j).b * 2 ^ n⌋).card : ℝ) := by
        simp
      _ = ∏ j : Fin d, ((2 : ℝ) ^ (-n : ℤ) * ((Finset.Ico ((B.side j).dyadicLowerIndex n) ⌊(B.side j).b * 2 ^ n⌋).card : ℝ)) := by
        simp [Finset.prod_mul_distrib]
  simp_rw [h_factor]
  have h_vol : |B|ᵥ = ∏ j : Fin d, |B.side j|ₗ := rfl
  rw [h_vol]
  exact h_conv

lemma metric_entropy_lower_mono {d : ℕ} {E F : Set (EuclideanSpace' d)}
    (hF : Bornology.IsBounded F) (hEF : E ⊆ F) (n : ℤ) :
    metric_entropy_lower E n ≤ metric_entropy_lower F n := by
  refine' Nat.card_mono _ _;
  · obtain ⟨ M, hM ⟩ := hF.exists_pos_norm_le;
    have h_bounded : ∀ i : Fin d → ℤ, (Box.dyadic n i).toSet ⊆ F → ∀ j : Fin d, |(i j : ℝ) / 2^n| ≤ M := by
      intro i hi j; specialize hM; have := hM.2 ( .toLp 2 ( fun k => ( i k : ℝ ) / 2 ^ n ) ) ( hi <| by
        intro k; exact (by
        exact ⟨ by exact le_rfl, by exact div_lt_div_iff_of_pos_right ( by positivity ) |>.2 ( by norm_num ) ⟩) ) ; simp_all +decide [ EuclideanSpace.norm_eq ] ;
      refine' le_trans _ this;
      exact Real.le_sqrt_of_sq_le ( by simpa [ abs_div, abs_of_nonneg ( show ( 0 : ℝ ) ≤ 2 ^ n by positivity ) ] using Finset.single_le_sum ( fun x _ => sq_nonneg ( |( i x : ℝ )| / 2 ^ n ) ) ( Finset.mem_univ j ) );
    have h_bound : ∀ i : Fin d → ℤ, (Box.dyadic n i).toSet ⊆ F → ∀ j : Fin d, |(i j : ℝ)| ≤ M * 2^n := by
      intro i hi j; specialize h_bounded i hi j; rw [ abs_div, abs_of_nonneg ( by positivity : ( 0 : ℝ ) ≤ 2 ^ n ) ] at h_bounded; rw [ div_le_iff₀ ( by positivity ) ] at h_bounded; linarith;
    have h_finite_values : ∀ j : Fin d, Set.Finite {i : ℤ | |(i : ℝ)| ≤ M * 2^n} := by
      exact fun j => Set.Finite.subset ( Set.finite_Icc ( -⌈M * 2 ^ n⌉₊ : ℤ ) ⌈M * 2 ^ n⌉₊ ) fun x hx => ⟨ neg_le_of_abs_le <| by exact_mod_cast hx.out.trans <| Nat.le_ceil _, le_of_abs_le <| by exact_mod_cast hx.out.trans <| Nat.le_ceil _ ⟩;
    exact Set.Finite.subset ( Set.Finite.pi fun j => h_finite_values j ) fun i hi => by aesop;
  · exact fun i hi => Set.Subset.trans hi hEF

lemma metric_entropy_lower_biUnion_box_le {d : ℕ} (T : Finset (Box d))
    (hT : (T : Set (Box d)).PairwiseDisjoint Box.toSet) (n : ℤ) :
    ∑ B ∈ T, metric_entropy_lower B.toSet n ≤
      metric_entropy_lower (⋃ B ∈ T, B.toSet) n := by
  convert Nat.card_le_card_of_injective _ ?_;
  rotate_left;
  exact Σ B : T, { i : Fin d → ℤ // ( Box.dyadic n i ).toSet ⊆ ( B : Box d ).toSet };
  rotate_left;
  exact fun x => ⟨ x.2.val, Set.Subset.trans x.2.2 <| Set.subset_iUnion₂_of_subset _ ( Finset.mem_coe.mpr x.1.2 ) <| by tauto ⟩;
  · intro x y hxy;
    have := hT x.1.2 y.1.2; simp_all +decide [ Set.disjoint_left ] ;
    contrapose! this;
    refine' ⟨ _, _ ⟩;
    · grind +splitImp;
    · use .toLp 2 (fun j => (x.2.val j : ℝ) / 2^n);
      have := x.2.2; have := y.2.2; simp_all +decide [ Set.subset_def ] ;
      exact ⟨ fun i => by simpa using ‹∀ ( x_1 : EuclideanSpace' d ), ( ∀ i : Fin d, ( y.snd.val i : ℝ ) / 2 ^ n ≤ x_1.ofLp i ∧ x_1.ofLp i < ( y.snd.val i + 1 : ℝ ) / 2 ^ n ) → ∀ i : Fin d, x_1.ofLp i ∈ ( x.fst.val.side i : Set ℝ ) › ( .toLp 2 ( fun j => ( y.snd.val j : ℝ ) / 2 ^ n ) ) ( fun j => ⟨ by norm_num, by rw [ div_lt_div_iff_of_pos_right ( by positivity ) ] ; linarith ⟩ ) i, fun i => by simpa using this ( .toLp 2 ( fun j => ( y.snd.val j : ℝ ) / 2 ^ n ) ) ( fun j => ⟨ by norm_num, by rw [ div_lt_div_iff_of_pos_right ( by positivity ) ] ; linarith ⟩ ) i ⟩;
  · convert rfl;
    convert Nat.card_sigma ( α := T ) ( β := fun B => { i : Fin d → ℤ // ( Box.dyadic n i ).toSet ⊆ B.val.toSet } ) using 1;
    · refine' Finset.sum_bij ( fun x hx => ⟨ x, hx ⟩ ) _ _ _ _ <;> aesop;
    · intro B
      have h_finite : Set.Finite { i : Fin d → ℤ | (Box.dyadic n i).toSet ⊆ B.val.toSet } := by
        have h_finite : ∀ j : Fin d, Set.Finite {i : ℤ | (BoundedInterval.Ico ((i : ℝ) / 2^n) ((i + 1 : ℤ) / 2^n)) ⊆ B.val.side j} := by
          intro j
          have h_finite : Set.Finite {i : ℤ | (B.val.side j).dyadicLowerIndex n ≤ i ∧ i < ⌊(B.val.side j).b * 2^n⌋} := by
            exact Set.finite_Ico _ _;
          refine h_finite.subset ?_;
          intro i hi; exact dyadic_interval_subset_iff _ _ _ |>.1 hi;
        convert Set.Finite.pi fun j => h_finite j using 1;
        ext; simp [Box.dyadic];
        convert dyadic_box_toSet_subset_iff _ _ _ using 1
      exact Set.Finite.to_subtype h_finite;
  · have h_finite : Bornology.IsBounded (⋃ B ∈ T, (B : Box d).toSet) := by
      exact isBounded_biUnion_box T ( fun B => B );
    have h_finite : Set.Finite {i : Fin d → ℤ | (Box.dyadic n i).toSet ⊆ ⋃ B ∈ T, (B : Box d).toSet} := by
      have h_bounded : ∃ M : ℝ, ∀ i : Fin d → ℤ, (Box.dyadic n i).toSet ⊆ ⋃ B ∈ T, (B : Box d).toSet → ∀ j, |(i j : ℝ)| ≤ M := by
        obtain ⟨ M, hM ⟩ := h_finite.exists_pos_norm_le;
        use M * 2^n + 1;
        intro i hi j;
        have := hM.2 ( .toLp 2 ( fun k => ( i k : ℝ ) / 2 ^ n ) ) ( hi <| by
          intro k; simp [Box.dyadic];
          gcongr ; norm_num );
        rw [ EuclideanSpace.norm_eq ] at this;
        rw [ Real.sqrt_le_iff ] at this;
        have := this.2.trans' ( Finset.single_le_sum ( fun a _ => sq_nonneg ( ‖( WithLp.toLp 2 fun k => ( i k : ℝ ) / 2 ^ n ).ofLp a‖ ) ) ( Finset.mem_univ j ) ) ; norm_num at this;
        rw [ div_pow, div_le_iff₀ ] at this <;> nlinarith [ show ( 0 : ℝ ) < 2 ^ n by positivity, show ( 0 : ℝ ) < M * 2 ^ n by exact mul_pos hM.1 ( by positivity ), abs_nonneg ( i j : ℝ ), abs_mul_abs_self ( i j : ℝ ) ]
      obtain ⟨ M, hM ⟩ := h_bounded;
      exact Set.Finite.subset ( Set.finite_Icc _ _ ) fun i hi => ⟨ fun j => show i j ≥ -⌈M⌉₊ by exact_mod_cast neg_le_of_abs_le <| le_trans ( hM i hi j ) <| Nat.le_ceil _, fun j => show i j ≤ ⌈M⌉₊ by exact_mod_cast le_of_abs_le <| le_trans ( hM i hi j ) <| Nat.le_ceil _ ⟩;
    exact h_finite.to_subtype

lemma IsElementary.metric_entropy_lower_tendsto {d : ℕ}
    {A : Set (EuclideanSpace' d)} (hA : IsElementary A) :
    Filter.atTop.Tendsto
      (fun n : ℤ ↦ (2 : ℝ)^(-(d*n : ℤ)) * (metric_entropy_lower A n : ℝ))
      (nhds hA.measure) := by
  obtain ⟨ T, hT_disj, hA_eq ⟩ := hA.partition;
  have h_lower_bound : ∀ n : ℤ, (2 : ℝ) ^ (-(d * n : ℤ)) * (metric_entropy_lower A n : ℝ) ≥ ∑ B ∈ T, (2 : ℝ) ^ (-(d * n : ℤ)) * (metric_entropy_lower B.toSet n : ℝ) := by
    intro n
    have h_lower_bound : metric_entropy_lower A n ≥ ∑ B ∈ T, metric_entropy_lower B.toSet n := by
      rw [ hA_eq ] ; exact metric_entropy_lower_biUnion_box_le T hT_disj n;
    simpa only [ ← Finset.mul_sum _ _ _ ] using mul_le_mul_of_nonneg_left ( mod_cast h_lower_bound ) ( by positivity );
  have h_box_tendsto : ∀ B ∈ T, Filter.Tendsto (fun n : ℤ => (2 : ℝ) ^ (-(d * n : ℤ)) * (metric_entropy_lower B.toSet n : ℝ)) Filter.atTop (nhds |B|ᵥ) := by
    intro B hB; convert metric_entropy_lower_box_tendsto B using 1;
  have h_upper_bound : ∀ n : ℤ, (2 : ℝ) ^ (-(d * n : ℤ)) * (metric_entropy_lower A n : ℝ) ≤ hA.measure := by
    intro n;
    convert metric_entropy_lower_upper_bound hA.isBounded n using 1;
    exact Eq.symm (JordanMeasurable.mes_of_elementary hA);
  have h_sum_volume : ∑ B ∈ T, |B|ᵥ = hA.measure := by
    rw [ ← IsElementary.measure_eq hA hT_disj hA_eq ];
  refine' tendsto_of_tendsto_of_tendsto_of_le_of_le' ( by simpa [ h_sum_volume ] using tendsto_finset_sum _ h_box_tendsto ) tendsto_const_nhds _ _;
  · simp_all +decide [ zpow_neg, mul_comm ];
  · exact Filter.Eventually.of_forall h_upper_bound

lemma metric_entropy_lower_tendsto {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E) :
    Filter.atTop.Tendsto (fun n:ℤ ↦ (2:ℝ)^(-(d*n:ℤ)) * (metric_entropy_lower E n))
      (nhds (Jordan_inner_measure E)) := by
  set L := Jordan_inner_measure E with hL
  have hpos : ∀ n:ℤ, 0 ≤ (2:ℝ)^(-(d*n:ℤ)) := by intro n; positivity
  apply Metric.tendsto_nhds.mpr; intro ε hε
  have h_ex : ∃ (A : Set (EuclideanSpace' d)) (hA : IsElementary A), A ⊆ E ∧ hA.measure > L - ε / 2 := by
    have h_lt : L - ε / 2 < L := by nlinarith
    obtain ⟨A, hA, hAE, hA_gt⟩ := Jordan_inner_le h_lt
    exact ⟨A, hA, hAE, hA_gt⟩
  obtain ⟨A, hA, hAE, hA_gt⟩ := h_ex
  have hA_upper : ∀ n : ℤ, (2:ℝ)^(-(d*n:ℤ)) * (metric_entropy_lower A n : ℝ) ≤ hA.measure := by
    intro n
    have h_bound := metric_entropy_lower_upper_bound (IsElementary.isBounded hA) n
    have h_eq : Jordan_inner_measure A = hA.measure := by
      apply le_antisymm
      · calc
          Jordan_inner_measure A ≤ Jordan_outer_measure A := Jordan_inner_le_outer (IsElementary.isBounded hA)
          _ ≤ hA.measure := Jordan_outer_le hA (Set.Subset.refl A)
      · exact le_Jordan_inner hA (Set.Subset.refl A) (IsElementary.isBounded hA)
    rw [h_eq] at h_bound
    exact h_bound
  have hA_lower : Filter.Tendsto (fun n:ℤ ↦ (2:ℝ)^(-(d*n:ℤ)) * (metric_entropy_lower A n : ℝ)) Filter.atTop (nhds (hA.measure)) := by
    convert IsElementary.metric_entropy_lower_tendsto hA using 1;
  filter_upwards [ hA_lower.eventually ( lt_mem_nhds ( show hA.measure > L - ε / 2 by linarith ) ), Filter.eventually_ge_atTop 0 ] with n hn hn';
  refine' abs_lt.mpr ⟨ _, _ ⟩;
  · linarith [ show ( 2 : ℝ ) ^ ( - ( d * n : ℤ ) ) * metric_entropy_lower A n ≤ ( 2 : ℝ ) ^ ( - ( d * n : ℤ ) ) * metric_entropy_lower E n from mul_le_mul_of_nonneg_left ( mod_cast metric_entropy_lower_mono hE hAE n ) ( by positivity ) ];
  · linarith [ show ( 2 : ℝ ) ^ ( - ( d * n : ℤ ) ) * ( metric_entropy_lower E n : ℝ ) ≤ L by exact_mod_cast metric_entropy_lower_upper_bound hE n ]

lemma metric_entropy_upper_lower_bound {d:ℕ} {E : Set (EuclideanSpace' d)} (hE : Bornology.IsBounded E) (n : ℤ) :
    Jordan_outer_measure E ≤ (2:ℝ)^(-(d*n:ℤ)) * (metric_entropy_upper E n : ℝ) := by
  have h_finite : Set.Finite {i : Fin d → ℤ | (Box.dyadic n i).toSet ∩ E ≠ ∅} := by
    obtain ⟨R, hR⟩ : ∃ R > 0, ∀ x ∈ E, ∀ i, |x i| ≤ R := by
      obtain ⟨ R, hR ⟩ := hE.exists_pos_norm_le;
      simp_all +decide [ EuclideanSpace.norm_eq ];
      exact ⟨ R, hR.1, fun x hx i => le_trans ( Real.abs_le_sqrt <| Finset.single_le_sum ( fun a _ => sq_nonneg ( x.ofLp a ) ) ( Finset.mem_univ i ) ) ( hR.2 x hx ) ⟩;
    refine Set.Finite.subset ( Set.finite_Icc ( fun j => ⌊-R * 2 ^ n⌋ ) ( fun j => ⌈R * 2 ^ n⌉ ) ) ?_;
    intro i hi; simp_all +decide [ Set.ext_iff ] ;
    constructor <;> intro j <;> have := hi.choose_spec.1 j <;> have := hR.2 _ hi.choose_spec.2 j <;> rw [ abs_le ] at this <;> rw [ div_le_iff₀ ( by positivity ), lt_div_iff₀ ( by positivity ) ] at * <;> norm_num at *;
    · exact Int.le_of_lt_add_one ( Int.floor_lt.mpr ( by norm_num; nlinarith [ show ( 0 : ℝ ) < 2 ^ n by positivity ] ) );
    · exact Int.le_of_lt_add_one ( by rw [ ← @Int.cast_lt ℝ ] ; push_cast; nlinarith [ Int.le_ceil ( R * 2 ^ n ), show ( 0 : ℝ ) < 2 ^ n by positivity ] );
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin d → ℤ), {i : Fin d → ℤ | (Box.dyadic n i).toSet ∩ E ≠ ∅} = S := by
    exact ⟨ h_finite.toFinset, h_finite.coe_toFinset.symm ⟩;
  refine' le_trans ( le_of_eq _ ) ( le_trans ( Jordan_outer_measure_mono_of_subset ( show E ⊆ ( ⋃ i ∈ S, ( Box.dyadic n i |> Box.toSet ) ) from _ ) _ ) _ );
  · rfl;
  · intro x hx; simp_all +decide [ Set.ext_iff ] ;
    refine' ⟨ fun i => ⌊x.ofLp i * 2 ^ n⌋, hS _ |>.1 ⟨ x, _, hx ⟩, _ ⟩ <;> norm_num [ div_le_iff₀, lt_div_iff₀, zpow_pos ]; all_goals exact fun i => Int.floor_le _;
  · refine' isBounded_biUnion_box _ _;
  · convert Jordan_outer_measure_biUnion_box_le S ( fun i => Box.dyadic n i ) using 1;
    simp +decide [ hS, dyadic_box_volume ];
    ring

lemma metric_entropy_upper_mono {d : ℕ} {E F : Set (EuclideanSpace' d)}
    (hF : Bornology.IsBounded F) (hEF : E ⊆ F) (n : ℤ) :
    metric_entropy_upper E n ≤ metric_entropy_upper F n := by
  refine' Nat.card_mono _ _;
  · obtain ⟨R, hR⟩ : ∃ R > 0, ∀ x ∈ F, ∀ i : Fin d, |x i| ≤ R := by
      obtain ⟨ R, hR ⟩ := hF.exists_pos_norm_le;
      use R;
      simp_all +decide [ EuclideanSpace.norm_eq ];
      exact fun x hx i => le_trans ( Real.abs_le_sqrt <| Finset.single_le_sum ( fun a _ => sq_nonneg ( x.ofLp a ) ) ( Finset.mem_univ i ) ) ( hR.2 x hx );
    refine' Set.Finite.subset ( Set.finite_Icc ( fun i => ⌊ ( -R * 2 ^ n ) ⌋ ) ( fun i => ⌈ ( R * 2 ^ n ) ⌉ ) ) _;
    intro i hi; simp_all +decide [ Set.ext_iff ] ;
    obtain ⟨ x, hx₁, hx₂ ⟩ := hi; refine' ⟨ fun j => _, fun j => _ ⟩ <;> norm_num [ div_le_iff₀, lt_div_iff₀, zpow_pos ] at *;
    · exact Int.le_of_lt_add_one ( Int.floor_lt.mpr ( by norm_num; nlinarith [ abs_le.mp ( hR.2 x hx₂ j ), hx₁ j, show ( 0 : ℝ ) < 2 ^ n by positivity ] ) );
    · exact Int.le_of_lt_add_one ( by rw [ ← @Int.cast_lt ℝ ] ; push_cast; nlinarith [ hx₁ j, abs_le.mp ( hR.2 x hx₂ j ), show ( 0 : ℝ ) < 2 ^ n by positivity, Int.le_ceil ( R * 2 ^ n ) ] );
  · exact fun i hi => Set.Nonempty.ne_empty ( Set.Nonempty.mono ( Set.inter_subset_inter ( Set.Subset.refl _ ) hEF ) ( Set.nonempty_iff_ne_empty.mpr hi ) )

open Classical in
noncomputable def BoundedInterval.dyadicUpperLowerIndex
    (I : BoundedInterval) (n : ℤ) : ℤ :=
  if _ : I.toSet.Nonempty then ⌊I.a * 2^n⌋ else 0

open Classical in
noncomputable def BoundedInterval.dyadicUpperIndex (I : BoundedInterval) (n : ℤ) : ℤ :=
  if _ : I.toSet.Nonempty then
    match I with
    | .Ioo _ b | .Ico _ b => ⌈b * 2^n⌉
    | .Icc _ b | .Ioc _ b => ⌊b * 2^n⌋ + 1
  else 0

lemma Ico_inter_Ioo_nonempty_iff {l r a b : ℝ} (hlr : l < r) (hab : a < b) :
    Set.Ico l r ∩ Set.Ioo a b ≠ ∅ ↔ a < r ∧ l < b := by
  constructor;
  · exact fun h => by obtain ⟨ x, hx₁, hx₂ ⟩ := Set.nonempty_iff_ne_empty.2 h; constructor <;> linarith [ hx₁.1, hx₁.2, hx₂.1, hx₂.2 ] ;
  · simp_all +decide [ Set.ext_iff ];
    exact fun h₁ h₂ => ⟨ ( Max.max l a + Min.min r b ) / 2, by cases max_cases l a <;> cases min_cases r b <;> linarith, by cases max_cases l a <;> cases min_cases r b <;> linarith, by cases max_cases l a <;> cases min_cases r b <;> linarith, by cases max_cases l a <;> cases min_cases r b <;> linarith ⟩

lemma Ico_inter_Icc_nonempty_iff {l r a b : ℝ} (hlr : l < r) (hab : a ≤ b) :
    Set.Ico l r ∩ Set.Icc a b ≠ ∅ ↔ a < r ∧ l ≤ b := by
  simp +decide [ Set.ext_iff ];
  grind

lemma Ico_inter_Ioc_nonempty_iff {l r a b : ℝ} (hlr : l < r) (hab : a < b) :
    Set.Ico l r ∩ Set.Ioc a b ≠ ∅ ↔ a < r ∧ l ≤ b := by
  by_cases h : l = b;
  · simp_all +decide [ Set.ext_iff ];
    grind;
  · cases lt_or_gt_of_ne h <;> simp_all +decide [ Set.ext_iff ];
    · exact ⟨ fun ⟨ x, hx₁, hx₂, hx₃, hx₄ ⟩ => ⟨ by linarith, by linarith ⟩, fun ⟨ hx₁, hx₂ ⟩ => ⟨ Max.max l a + ( Min.min r b - Max.max l a ) / 2, by cases max_cases l a <;> cases min_cases r b <;> linarith, by cases max_cases l a <;> cases min_cases r b <;> linarith, by cases max_cases l a <;> cases min_cases r b <;> linarith, by cases max_cases l a <;> cases min_cases r b <;> linarith ⟩ ⟩;
    · exact iff_of_false ( by rintro ⟨ x, hx₁, hx₂, hx₃, hx₄ ⟩ ; linarith ) ( by rintro ⟨ hx₁, hx₂ ⟩ ; linarith )

lemma Ico_inter_Ico_nonempty_iff {l r a b : ℝ} (hlr : l < r) (hab : a < b) :
    Set.Ico l r ∩ Set.Ico a b ≠ ∅ ↔ a < r ∧ l < b := by
  constructor <;> intro h <;> contrapose! h <;> simp_all +decide [ Set.ext_iff ];
  · exact fun x hx₁ hx₂ hx₃ => by linarith [ h ( by linarith ) ] ;
  · contrapose! h;
    exact ⟨ Max.max l a, le_max_left _ _, by cases max_cases l a <;> linarith, le_max_right _ _, by cases max_cases l a <;> linarith ⟩

lemma dyadic_interval_inter_nonempty_iff (I : BoundedInterval) (n i : ℤ) :
    (BoundedInterval.Ico ((i : ℝ) / 2^n) ((i + 1 : ℤ) / 2^n) : Set ℝ) ∩ I.toSet ≠ ∅ ↔
      I.dyadicUpperLowerIndex n ≤ i ∧ i < I.dyadicUpperIndex n := by
  by_cases h : I.toSet.Nonempty <;> simp_all +decide [ BoundedInterval.dyadicUpperLowerIndex, BoundedInterval.dyadicUpperIndex ];
  · cases' I with a b ha hb ; simp_all +decide [ Set.ext_iff ];
    · constructor <;> intro h';
      · constructor <;> norm_num [ Int.le_floor, Int.lt_ceil ];
        · obtain ⟨ x, hx₁, hx₂, hx₃, hx₄ ⟩ := h';
          exact Int.le_of_lt_add_one ( Int.floor_lt.mpr ( by norm_num; nlinarith [ show ( 0 : ℝ ) < 2 ^ n by positivity, mul_div_cancel₀ ( ( i : ℝ ) : ℝ ) ( show ( 2 ^ n : ℝ ) ≠ 0 by positivity ), mul_div_cancel₀ ( ( i + 1 : ℝ ) : ℝ ) ( show ( 2 ^ n : ℝ ) ≠ 0 by positivity ) ] ) );
        · obtain ⟨ x, hx₁, hx₂, hx₃, hx₄ ⟩ := h'; rw [ div_le_iff₀ ( by positivity ) ] at hx₁; nlinarith [ show ( 2 : ℝ ) ^ n > 0 by positivity ] ;
      · obtain ⟨x, hx⟩ : ∃ x : ℝ, max (i / 2^n : ℝ) a < x ∧ x < min ((i + 1) / 2^n : ℝ) b := by
          refine' exists_between _;
          simp_all +decide [ Int.floor_le_iff, Int.lt_ceil ];
          exact ⟨ ⟨ by rw [ div_lt_div_iff_of_pos_right ( by positivity ) ] ; linarith, by rw [ lt_div_iff₀ ( by positivity ) ] ; linarith! ⟩, by rw [ div_lt_iff₀ ( by positivity ) ] ; linarith! ⟩;
        exact ⟨ x, le_of_lt ( lt_of_le_of_lt ( le_max_left _ _ ) hx.1 ), lt_of_lt_of_le hx.2 ( min_le_left _ _ ), lt_of_le_of_lt ( le_max_right _ _ ) hx.1, lt_of_lt_of_le hx.2 ( min_le_right _ _ ) ⟩;
    · simp +decide [ Set.ext_iff, Int.floor_le_iff, Int.lt_ceil, Int.le_floor, Int.lt_iff_add_one_le, div_lt_iff₀, lt_div_iff₀, zpow_pos ];
      constructor <;> intro h';
      · obtain ⟨ x, hx₁, hx₂, hx₃, hx₄ ⟩ := h';
        constructor <;> nlinarith [ show ( 0 : ℝ ) < 2 ^ n by positivity, mul_div_cancel₀ ( i : ℝ ) ( show ( 2 : ℝ ) ^ n ≠ 0 by positivity ) ];
      · use max (i / 2 ^ n : ℝ) ha;
        cases max_cases ( i / 2 ^ n : ℝ ) ha <;> simp_all +decide [ div_le_iff₀, le_div_iff₀ ];
        exact ⟨ by rw [ div_mul_cancel₀ _ ( by positivity ) ] ; linarith, by rw [ div_le_iff₀ ( by positivity ) ] ; linarith ⟩;
    · rename_i a b;
      have h_empty : Set.Nonempty (Set.Ico (i / 2^n : ℝ) ((i + 1) / 2^n : ℝ) ∩ Set.Ioc a b) ↔ a < (i + 1) / 2^n ∧ i / 2^n ≤ b := by
        convert Ico_inter_Ioc_nonempty_iff _ _ using 1;
        · exact ⟨ fun h => Set.Nonempty.ne_empty h, fun h => Set.nonempty_iff_ne_empty.mpr h ⟩;
        · gcongr ; norm_num;
        · exact Set.nonempty_Ioc.mp h;
      convert h_empty using 1;
      · exact ⟨ fun h => Set.nonempty_iff_ne_empty.mpr h, fun h => Set.Nonempty.ne_empty h ⟩;
      · rw [ lt_div_iff₀ ( by positivity ), div_le_iff₀ ( by positivity ) ];
        constructor <;> intro h <;> constructor <;> norm_num at *;
        · exact lt_of_lt_of_le ( Int.lt_floor_add_one _ ) ( mod_cast by linarith );
        · exact Int.le_floor.mp h.2;
        · exact Int.le_of_lt_add_one ( Int.floor_lt.mpr ( by norm_num; linarith ) );
        · exact Int.le_floor.2 h.2;
    · simp_all +decide [ Set.ext_iff ];
      rename_i a b;
      constructor <;> intro h';
      · constructor <;> norm_num [ Int.le_floor, Int.lt_ceil ] at *;
        · exact Int.le_of_lt_add_one ( Int.floor_lt.mpr ( by norm_num; nlinarith [ h'.choose_spec, show ( 0 : ℝ ) < 2 ^ n by positivity, mul_div_cancel₀ ( ( i : ℝ ) : ℝ ) ( by positivity : ( 2 : ℝ ) ^ n ≠ 0 ), mul_div_cancel₀ ( ( i + 1 : ℝ ) : ℝ ) ( by positivity : ( 2 : ℝ ) ^ n ≠ 0 ) ] ) );
        · obtain ⟨ x, hx₁, hx₂, hx₃, hx₄ ⟩ := h'; rw [ div_le_iff₀ ( by positivity ) ] at hx₁; rw [ lt_div_iff₀ ( by positivity ) ] at hx₂; nlinarith [ ( by positivity : ( 0 : ℝ ) < 2 ^ n ) ] ;
      · refine' ⟨ Max.max ( a : ℝ ) ( i / 2 ^ n ), _, _, _, _ ⟩ <;> norm_num;
        · exact ⟨ by rw [ lt_div_iff₀ ( by positivity ) ] ; linarith [ Int.lt_floor_add_one ( a * 2 ^ n ), show ( i : ℝ ) ≥ ⌊a * 2 ^ n⌋ by exact_mod_cast h'.1 ], by rw [ div_lt_div_iff_of_pos_right ( by positivity ) ] ; linarith ⟩;
        · exact ⟨ by simpa using h, by rw [ div_lt_iff₀ ( by positivity ) ] ; exact lt_of_not_ge fun h'' => h'.2.not_ge <| Int.ceil_le.mpr <| by linarith ⟩;
  · simp_all +decide [ Set.ext_iff, Set.Nonempty ]

lemma dyadic_box_inter_nonempty_iff {d : ℕ} (B : Box d) (n : ℤ) (i : Fin d → ℤ) :
    (Box.dyadic n i).toSet ∩ B.toSet ≠ ∅ ↔
      ∀ j : Fin d, (B.side j).dyadicUpperLowerIndex n ≤ i j ∧ i j < (B.side j).dyadicUpperIndex n := by
  convert Set.nonempty_iff_ne_empty.symm using 1;
  constructor <;> intro h;
  · have h_exists_x : ∀ j : Fin d, ∃ x_j : ℝ, x_j ∈ (B.side j).toSet ∧ (i j : ℝ) / 2^n ≤ x_j ∧ x_j < ((i j + 1) : ℝ) / 2^n := by
      intro j
      specialize h j
      have h_exists_x_j : (BoundedInterval.Ico ((i j : ℝ) / 2^n) ((i j + 1 : ℤ) / 2^n) : Set ℝ) ∩ (B.side j).toSet ≠ ∅ := by
        convert dyadic_interval_inter_nonempty_iff ( B.side j ) n ( i j ) |>.2 h using 1;
      exact Exists.elim ( Set.nonempty_iff_ne_empty.mpr h_exists_x_j ) fun x hx => ⟨ x, hx.2, hx.1.1, hx.1.2.trans_le <| by norm_num ⟩;
    choose f hf using h_exists_x;
    use .toLp 2 f;
    simp_all +decide [ Box.dyadic ];
  · obtain ⟨ x, hx ⟩ := h;
    intro j;
    convert dyadic_interval_inter_nonempty_iff ( B.side j ) n ( i j ) |>.1 _;
    exact Set.Nonempty.ne_empty ⟨ x j, by simpa using hx.1 j, by simpa using hx.2 j ⟩

lemma metric_entropy_upper_box_count {d : ℕ} (B : Box d) (n : ℤ) :
    metric_entropy_upper B.toSet n =
      ∏ j : Fin d,
        (Finset.Ico ((B.side j).dyadicUpperLowerIndex n) ((B.side j).dyadicUpperIndex n)).card := by
  trans;
  rotate_right;
  exact Nat.card { i : Fin d → ℤ // ∀ j, (B.side j).dyadicUpperLowerIndex n ≤ i j ∧ i j < (B.side j).dyadicUpperIndex n };
  · exact congr_arg _ ( congr_arg _ ( Set.ext fun x => by simpa using dyadic_box_inter_nonempty_iff B n x ) );
  · convert Nat.card_congr ?_;
    rotate_left;
    exact Π j, Finset.Ico ((B.side j).dyadicUpperLowerIndex n) ((B.side j).dyadicUpperIndex n);
    · exact ⟨ fun x => fun j => ⟨ x.val j, Finset.mem_Ico.mpr ( x.property j ) ⟩, fun x => ⟨ fun j => x j, fun j => Finset.mem_Ico.mp ( x j |>.2 ) ⟩, fun x => rfl, fun x => rfl ⟩;
    · simp [ Nat.card_pi ]

lemma dyadic_upper_count_tendsto (I : BoundedInterval) :
    Filter.atTop.Tendsto
      (fun n : ℤ ↦ (2 : ℝ)^(-n) *
        ((Finset.Ico (I.dyadicUpperLowerIndex n) (I.dyadicUpperIndex n)).card : ℝ))
      (nhds |I|ₗ) := by
  suffices h_simplify : Filter.Tendsto (fun n : ℤ => ((I.dyadicUpperIndex n : ℝ) - (I.dyadicUpperLowerIndex n : ℝ)) * 2 ^ (-n : ℤ)) Filter.atTop (nhds (max (I.b - I.a) 0)) by
    convert h_simplify using 2 ; norm_num [ mul_comm ];
    exact Or.inl <| mod_cast Int.toNat_of_nonneg <| sub_nonneg_of_le <| by
      cases I <;> simp +decide [ BoundedInterval.dyadicUpperLowerIndex, BoundedInterval.dyadicUpperIndex ];
      · split_ifs <;> norm_num;
        exact Int.floor_le_ceil _ |> le_trans <| Int.ceil_mono <| mul_le_mul_of_nonneg_right ( le_of_lt ‹_› ) <| by positivity;
      · split_ifs <;> norm_num;
        exact le_add_of_le_of_nonneg ( Int.floor_mono <| mul_le_mul_of_nonneg_right ‹_› <| by positivity ) zero_le_one;
      · split_ifs <;> norm_num;
        exact le_add_of_le_of_nonneg ( Int.floor_mono <| mul_le_mul_of_nonneg_right ( by linarith ) <| by positivity ) zero_le_one;
      · split_ifs <;> norm_num;
        exact Int.floor_le_ceil _ |> le_trans <| Int.ceil_mono <| mul_le_mul_of_nonneg_right ( le_of_lt ‹_› ) <| by positivity;
  rcases I with ( _ | _ | _ | _ ) <;> norm_num [ BoundedInterval.dyadicUpperIndex, BoundedInterval.dyadicUpperLowerIndex ] at *;
  · split_ifs <;> simp_all +decide [ max_def ];
    rename_i a b hab;
    rw [ if_neg hab.not_ge ];
    refine' ( tendsto_iff_norm_sub_tendsto_zero.mpr _ );
    refine' squeeze_zero ( fun _ => abs_nonneg _ ) ( fun e => _ ) ( show Filter.Tendsto ( fun e : ℤ => ( 2 : ℝ ) ⁻¹ ^ e * 2 ) Filter.atTop ( nhds 0 ) from _ );
    · erw [ Real.norm_eq_abs, abs_le ] ; constructor <;> norm_num;
      · field_simp;
        norm_num [ mul_assoc, mul_comm, mul_left_comm, ← mul_zpow ];
        linarith [ Int.le_ceil ( ( 2 : ℝ ) ^ e * b ), Int.floor_le ( ( 2 : ℝ ) ^ e * a ), Int.ceil_lt_add_one ( ( 2 : ℝ ) ^ e * b ), Int.lt_floor_add_one ( ( 2 : ℝ ) ^ e * a ) ];
      · rw [ ← div_eq_mul_inv, div_le_iff₀ ];
        · norm_num [ mul_add, mul_assoc, mul_comm, mul_left_comm, ← mul_zpow ];
          linarith! [ Int.ceil_lt_add_one ( b * 2 ^ e ), Int.lt_floor_add_one ( 2 ^ e * a ) ];
        · positivity;
    · norm_num [ ← Real.rpow_intCast, Real.rpow_def_of_pos ];
      simpa using Filter.Tendsto.mul ( Real.tendsto_exp_atBot.comp <| Filter.tendsto_neg_atTop_atBot.comp <| Filter.Tendsto.const_mul_atTop ( Real.log_pos one_lt_two ) <| tendsto_intCast_atTop_atTop ) tendsto_const_nhds;
  · split_ifs <;> simp_all +decide [ sub_mul ];
    · rename_i a b hab;
      refine' ( tendsto_iff_norm_sub_tendsto_zero.mpr _ );
      refine' squeeze_zero ( fun _ => abs_nonneg _ ) ( fun e => _ ) ( show Filter.Tendsto ( fun e : ℤ => ( 2 : ℝ ) ⁻¹ ^ e * 2 ) Filter.atTop ( nhds 0 ) from _ );
      · norm_num [ abs_le ];
        constructor <;> norm_num [ BoundedInterval.b, BoundedInterval.a ];
        · field_simp;
          norm_num [ mul_assoc, mul_comm, mul_left_comm, ← mul_zpow ];
          linarith [ Int.floor_le ( b * 2 ^ e ), Int.lt_floor_add_one ( b * 2 ^ e ), Int.floor_le ( a * 2 ^ e ), Int.lt_floor_add_one ( a * 2 ^ e ), show ( ⌊a * 2 ^ e⌋ : ℝ ) ≤ ⌊b * 2 ^ e⌋ by exact_mod_cast Int.floor_mono <| mul_le_mul_of_nonneg_right hab <| by positivity ];
        · rw [ show ( 1 / 2 : ℝ ) ^ e = ( 2 ^ e ) ⁻¹ by rw [ one_div, inv_zpow ] ] ; ring_nf;
          nlinarith [ Int.floor_le ( b * 2 ^ e ), Int.lt_floor_add_one ( b * 2 ^ e ), Int.floor_le ( 2 ^ e * a ), Int.lt_floor_add_one ( 2 ^ e * a ), show ( 0 : ℝ ) < ( 2 ^ e ) ⁻¹ by positivity, mul_inv_cancel₀ ( show ( 2 ^ e : ℝ ) ≠ 0 by positivity ) ];
      · norm_num [ Metric.tendsto_nhds ];
        intro ε hε; have := Metric.tendsto_atTop.mp ( show Filter.Tendsto ( fun n : ℕ => ( 1 / 2 : ℝ ) ^ n * 2 ) Filter.atTop ( nhds 0 ) from by simpa using tendsto_pow_atTop_nhds_zero_of_lt_one ( by norm_num ) ( by norm_num : ( 1 : ℝ ) / 2 < 1 ) |> Filter.Tendsto.mul_const 2 ) ε hε; rcases this with ⟨ N, hN ⟩ ; exact ⟨ N, fun n hn => by simpa using hN ( Int.toNat n ) ( by linarith [ Int.self_le_toNat n ] ) |> fun h => by simpa [ ← zpow_natCast, Int.toNat_of_nonneg ( by linarith : 0 ≤ n ) ] using h ⟩ ;
    · exact le_of_lt ‹_›;
  · split_ifs <;> simp_all +decide [ BoundedInterval.a, BoundedInterval.b ];
    rename_i a b hab;
    rw [ max_eq_left ( by linarith ) ];
    refine' ( tendsto_iff_norm_sub_tendsto_zero.mpr _ );
    refine' squeeze_zero ( fun _ => abs_nonneg _ ) ( fun e => _ ) ( show Filter.Tendsto ( fun e : ℤ => ( 2 : ℝ ) ⁻¹ ^ e * 2 ) Filter.atTop ( nhds 0 ) from _ );
    · norm_num [ Real.norm_eq_abs, abs_le ];
      field_simp;
      norm_num [ mul_add, mul_assoc, mul_comm, mul_left_comm, ← mul_zpow ];
      constructor <;> linarith [ Int.floor_le ( b * 2 ^ e ), Int.lt_floor_add_one ( b * 2 ^ e ), Int.floor_le ( a * 2 ^ e ), Int.lt_floor_add_one ( a * 2 ^ e ) ];
    · norm_num [ ← Real.rpow_intCast, Real.rpow_def_of_pos ];
      simpa using Filter.Tendsto.mul ( Real.tendsto_exp_atBot.comp <| Filter.tendsto_neg_atTop_atBot.comp <| Filter.Tendsto.const_mul_atTop ( Real.log_pos one_lt_two ) <| tendsto_intCast_atTop_atTop ) tendsto_const_nhds;
  · split_ifs <;> simp_all +decide [ BoundedInterval.a, BoundedInterval.b ];
    rename_i a b hab;
    rw [ max_eq_left ( by linarith ) ];
    refine' ( tendsto_iff_norm_sub_tendsto_zero.mpr _ );
    refine' squeeze_zero ( fun _ => abs_nonneg _ ) ( fun e => _ ) ( show Filter.Tendsto ( fun e : ℤ => ( 2 : ℝ ) ⁻¹ ^ e * 2 ) Filter.atTop ( nhds 0 ) from _ );
    · norm_num [ Real.norm_eq_abs ];
      rw [ abs_le ] ; constructor <;> norm_num [ ← div_eq_mul_inv ];
      · field_simp;
        norm_num [ mul_assoc, mul_comm, mul_left_comm, ← mul_zpow ];
        linarith [ Int.le_ceil ( b * 2 ^ e ), Int.floor_le ( a * 2 ^ e ), Int.ceil_lt_add_one ( b * 2 ^ e ), Int.lt_floor_add_one ( a * 2 ^ e ) ];
      · rw [ div_le_iff₀ ( by positivity ) ];
        norm_num [ zpow_add₀, zpow_sub₀ ] ; ring_nf;
        norm_num [ ← mul_zpow ];
        linarith [ Int.ceil_lt_add_one ( b * 2 ^ e ), Int.floor_le ( 2 ^ e * a ), Int.lt_floor_add_one ( 2 ^ e * a ) ];
    · norm_num [ ← Real.rpow_intCast, Real.rpow_def_of_pos ];
      simpa using Filter.Tendsto.mul ( Real.tendsto_exp_atBot.comp <| Filter.tendsto_neg_atTop_atBot.comp <| Filter.Tendsto.const_mul_atTop ( Real.log_pos one_lt_two ) <| tendsto_intCast_atTop_atTop ) tendsto_const_nhds

lemma metric_entropy_upper_box_tendsto {d : ℕ} (B : Box d) :
    Filter.atTop.Tendsto
      (fun n : ℤ ↦ (2 : ℝ)^(-(d*n : ℤ)) * (metric_entropy_upper B.toSet n : ℝ))
      (nhds |B|ᵥ) := by
  have h_count : Filter.Tendsto (fun n : ℤ => (2 : ℝ)^(-(d*n:ℤ)) * (∏ j : Fin d, (Finset.Ico ((B.side j).dyadicUpperLowerIndex n) ((B.side j).dyadicUpperIndex n)).card : ℝ)) Filter.atTop (nhds B.volume) := by
    convert tendsto_finset_prod _ fun j _ => dyadic_upper_count_tendsto ( B.side j ) using 1;
    norm_num [ zpow_mul', Finset.prod_mul_distrib ];
  convert h_count using 3 ; rw [ metric_entropy_upper_box_count ] ; norm_cast

lemma metric_entropy_upper_biUnion_box_le {d : ℕ} (T : Finset (Box d)) (n : ℤ) :
    metric_entropy_upper (⋃ B ∈ T, B.toSet) n ≤
      ∑ B ∈ T, metric_entropy_upper B.toSet n := by
  classical
  let s : Box d → Set (Fin d → ℤ) :=
    fun B => {i | (Box.dyadic n i).toSet ∩ B.toSet ≠ ∅}
  have hs : {i : Fin d → ℤ |
      (Box.dyadic n i).toSet ∩ (⋃ B ∈ T, B.toSet) ≠ ∅} =
      ⋃ B ∈ T, s B := by
    ext i
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, s]
    constructor
    · intro hi
      obtain ⟨x, hxi, hxU⟩ := Set.nonempty_iff_ne_empty.mpr hi
      simp only [Set.mem_iUnion] at hxU
      obtain ⟨B, hxU⟩ := hxU
      obtain ⟨hBT, hxB⟩ := hxU
      exact ⟨B, hBT, Set.Nonempty.ne_empty ⟨x, hxi, hxB⟩⟩
    · rintro ⟨B, hBT, hi⟩
      obtain ⟨x, hxi, hxB⟩ := Set.nonempty_iff_ne_empty.mpr hi
      exact Set.Nonempty.ne_empty ⟨x, hxi, Set.mem_iUnion₂.mpr ⟨B, hBT, hxB⟩⟩
  change Set.ncard {i : Fin d → ℤ |
      (Box.dyadic n i).toSet ∩ (⋃ B ∈ T, B.toSet) ≠ ∅} ≤
    ∑ B ∈ T, Set.ncard (s B)
  rw [hs]
  exact Finset.set_ncard_biUnion_le T s

lemma IsElementary.metric_entropy_upper_tendsto {d : ℕ}
    {A : Set (EuclideanSpace' d)} (hA : IsElementary A) :
    Filter.atTop.Tendsto
      (fun n : ℤ ↦ (2 : ℝ)^(-(d*n : ℤ)) * (metric_entropy_upper A n : ℝ))
      (nhds hA.measure) := by
  obtain ⟨T, hTdisj, hAeq⟩ := hA.partition
  have hsum : Filter.atTop.Tendsto
      (fun n : ℤ => ∑ B ∈ T,
        (2 : ℝ)^(-(d*n : ℤ)) * (metric_entropy_upper B.toSet n : ℝ))
      (nhds (∑ B ∈ T, |B|ᵥ)) := by
    exact tendsto_finset_sum T (fun B _ => metric_entropy_upper_box_tendsto B)
  have hmeasure : ∑ B ∈ T, |B|ᵥ = hA.measure := by
    exact (IsElementary.measure_eq hA hTdisj hAeq).symm
  have hlower : ∀ n : ℤ, hA.measure ≤
      (2 : ℝ)^(-(d*n : ℤ)) * (metric_entropy_upper A n : ℝ) := by
    intro n
    have h := metric_entropy_upper_lower_bound hA.isBounded n
    have hout : Jordan_outer_measure A = hA.measure := by
      calc
        Jordan_outer_measure A = hA.jordanMeasurable.measure := hA.jordanMeasurable.eq_outer.symm
        _ = hA.measure := JordanMeasurable.mes_of_elementary hA
    rw [hout] at h
    exact h
  have hupper : ∀ n : ℤ,
      (2 : ℝ)^(-(d*n : ℤ)) * (metric_entropy_upper A n : ℝ) ≤
        ∑ B ∈ T, (2 : ℝ)^(-(d*n : ℤ)) *
          (metric_entropy_upper B.toSet n : ℝ) := by
    intro n
    rw [hAeq, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left
      (by exact_mod_cast metric_entropy_upper_biUnion_box_le T n) (by positivity)
  have hsum' : Filter.atTop.Tendsto
      (fun n : ℤ => ∑ B ∈ T,
        (2 : ℝ)^(-(d*n : ℤ)) * (metric_entropy_upper B.toSet n : ℝ))
      (nhds hA.measure) := by
    rw [← hmeasure]
    exact hsum
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum'
    (Filter.Eventually.of_forall hlower) (Filter.Eventually.of_forall hupper)

/-- Scaled upper dyadic entropy converges to the outer Jordan measure (any bounded set). -/
lemma metric_entropy_upper_tendsto {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E) :
    Filter.atTop.Tendsto (fun n:ℤ ↦ (2:ℝ)^(-(d*n:ℤ)) * (metric_entropy_upper E n))
      (nhds (Jordan_outer_measure E)) := by
  set U := Jordan_outer_measure E with hU
  have hpos : ∀ n:ℤ, 0 ≤ (2:ℝ)^(-(d*n:ℤ)) := by intro n; positivity
  apply Metric.tendsto_nhds.mpr; intro ε hε
  have h_ex : ∃ (B : Set (EuclideanSpace' d)) (hB : IsElementary B), E ⊆ B ∧ hB.measure < U + ε / 2 := by
    have h_lt : U < U + ε / 2 := by nlinarith
    obtain ⟨B, hB, hEB, hB_lt⟩ := le_Jordan_outer h_lt hE
    exact ⟨B, hB, hEB, hB_lt⟩
  obtain ⟨B, hB, hEB, hB_lt⟩ := h_ex
  have hB_upper : ∀ n : ℤ, (2:ℝ)^(-(d*n:ℤ)) * (metric_entropy_upper B n : ℝ) ≥ hB.measure := by
    intro n
    have h_ineq : Jordan_outer_measure B ≤ (2:ℝ)^(-(d*n:ℤ)) * (metric_entropy_upper B n : ℝ) := by
      exact metric_entropy_upper_lower_bound hB.isBounded n
    have h_outer_eq : Jordan_outer_measure B = hB.measure := by
      set S := {m | ∃ (A : Set (EuclideanSpace' d)) (hA : IsElementary A), B ⊆ A ∧ m = hA.measure} with hS
      have hS_nonempty : S.Nonempty := ⟨hB.measure, B, hB, Set.Subset.refl B, rfl⟩
      have hBdd : BddBelow S := by
        refine ⟨0, λ m hm => ?_⟩
        obtain ⟨A, hA, _, rfl⟩ := hm
        exact IsElementary.measure_nonneg hA
      have hx_mem : hB.measure ∈ S := ⟨B, hB, Set.Subset.refl B, rfl⟩
      apply le_antisymm
      · calc
          Jordan_outer_measure B = sInf S := rfl
          _ ≤ hB.measure := csInf_le hBdd hx_mem
      · refine le_csInf hS_nonempty ?_
        rintro m ⟨A, hA, hBA, rfl⟩
        exact IsElementary.measure_mono hB hA hBA
    calc
      hB.measure = Jordan_outer_measure B := by symm; exact h_outer_eq
      _ ≤ (2:ℝ)^(-(d*n:ℤ)) * (metric_entropy_upper B n : ℝ) := h_ineq
  have hBt := hB.metric_entropy_upper_tendsto
  filter_upwards [hBt.eventually (Metric.ball_mem_nhds _ (half_pos hε))] with n hn
  have hmono : metric_entropy_upper E n ≤ metric_entropy_upper B n :=
    metric_entropy_upper_mono hB.isBounded hEB n
  have hscaled_mono :
      (2 : ℝ)^(-(d*n : ℤ)) * (metric_entropy_upper E n : ℝ) ≤
      (2 : ℝ)^(-(d*n : ℤ)) * (metric_entropy_upper B n : ℝ) := by
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hmono) (hpos n)
  have hlower : U ≤ (2 : ℝ)^(-(d*n : ℤ)) *
      (metric_entropy_upper E n : ℝ) := by
    exact metric_entropy_upper_lower_bound hE n
  rw [Real.dist_eq] at hn
  change |(2 : ℝ)^(-(d*n : ℤ)) * (metric_entropy_upper E n : ℝ) - U| < ε
  exact abs_lt.mpr ⟨by linarith, by linarith [abs_lt.mp hn]⟩
