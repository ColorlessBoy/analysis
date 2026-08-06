import Analysis.MeasureTheory.Section_1_4_2

open MeasureTheory

#synth TopologicalSpace (Set ℕ)
#synth TopologicalSpace (Prop)
#synth TopologicalSpace (Set X)

noncomputable def tst1 {X:Type*} [MeasurableSpace X] (E : ℕ → Set X) (E' : Set X)
    (hlim : PointwiseConvergesTo E E') : Prop := True

noncomputable def tst2 {X:Type*} (E : ℕ → Set X) (E' : Set X)
    (hlim : PointwiseConvergesTo E E') : Prop := True
