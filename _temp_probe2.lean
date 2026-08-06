import Analysis.MeasureTheory.Section_1_4_2

open MeasureTheory

-- EReal basics
#check EReal.add_comm
#check EReal.add_assoc
#check EReal.zero_add
#check EReal.add_zero
#check EReal.coe_toENNReal
#check EReal.coe_ennreal_add
#check EReal.coe_nonneg
#check EReal.mul_add
#check EReal.add_mul
#check EReal.mul_assoc
#check EReal.mul_comm
#check EReal.one_mul
#check EReal.mul_one
#check EReal.coe_tsum_of_nonneg
#check EReal.tsum_add
#check EReal.mul_lt_top_of_nonneg

-- ENat.card
#check ENat.card
#check ENat.card_empty
#check ENat.card_union
#check ENat.card_iUnion
#check ENat.card_add
#check ENat.card_eq_zero
#check ENat.card_le_card

-- Lebesgue finite additivity
#check Lebesgue_measure.countable_union
#check Lebesgue_measure.empty
#check Lebesgue_measure.additive
#check Lebesgue_outer_measure.mono
#check Lebesgue_outer_measure.union_le
#check Lebesgue_outer_measure.nonneg

-- Measure structure + lemmas
#check Measure.measure_union
#check Measure.iUnion_tsum
#check Measure.measure_iUnion
#check Measure.measure_iUnion_le_tsum
#check Measure.measure_iUnion_eq_iSup
#check Measure.measure_iInter_eq_iInf
#check Measure.measure_nonneg
#check Measure.empty
#check Measure.mono
#check Measure.iUnion_nat
#check Measure.m_iUnion
#check Measure.trim_le
#check Measure.trim
#check Measure.measure_biUnion_finset_le
#check Measure.measure_iUnion
#check ENNReal.tsum_le_tsum
#check ENNReal.tsum_add
#check ENNReal.summable
#check ENNReal.iSup
#check ENNReal.iInf
#check Set.PairwiseDisjoint
#check Set.PairwiseDisjoint.subset

-- measurable sets topology
#check Measurable
#synth TopologicalSpace (Set ℕ)
#synth MeasurableSpace (Set ℕ)
#check Set.Limsup
#check MeasurableSet.iUnion
#check MeasurableSet.iInter
#check MeasurableSet.limsup
#check MeasurableSet.liminf

-- measure completion
#check Measure.completion
#check NullMeasurableSet
#check Measure.IsComplete
#check NullMeasurableSet.measure_compl
#check Measure.completion_apply
#check Measure.equiv
