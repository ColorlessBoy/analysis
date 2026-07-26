import Analysis.MeasureTheory.Section_1_2_1

-- NOTE: This lemma is FALSE as stated.
-- Counterexample:
--   A = {1/(n+1) : n in Nat} (positive reals approaching 0), B = {infinity}.
--   sInf A = 0, sInf B = infinity, RHS = 0 * infinity = 0
--   But a * infinity = infinity for each positive a in A, so product set = {infinity}
--   sInf product set = infinity != 0 = RHS
-- The equality fails when sInf A = 0 (but 0 not in A) and B has infinity.
-- To fix, require A, B to be sets of finite reals, or 0 in A whenever sInf A = 0.

lemma sInf_image2_mul_eq_mul_sInf {A B : Set EReal} (hA : A.Nonempty) (hB : B.Nonempty)
    (hA_nonneg : ∀ a ∈ A, 0 ≤ a) (hB_nonneg : ∀ b ∈ B, 0 ≤ b) :
    sInf (Set.image2 (· * ·) A B) = (sInf A) * (sInf B) := by
  sorry
