import Mathlib.MeasureTheory.MeasurableSpace.Basic

variable {α : Type*} {mα : MeasurableSpace α}

@[simp, measurability]
protected lemma MeasurableSet.disjointed' {f : ℕ → Set α} (h : ∀ i, MeasurableSet (f i)) (n) :
    MeasurableSet (disjointed f n) :=
  disjointedRec (fun _ _ ht => MeasurableSet.diff ht <| h _) (h n)
