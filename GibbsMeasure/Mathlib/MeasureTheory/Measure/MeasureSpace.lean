import Mathlib.MeasureTheory.Measure.MeasureSpace

namespace MeasureTheory.Measure
variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α → β} {μ : Measure α}
  {s : Set β}

-- TODO: Replace `Measure.map_apply`
@[simp] lemma map_apply' (hf : Measurable f) (hs : MeasurableSet s) :
    μ.map f s = μ (f ⁻¹' s) := map_apply hf hs

end MeasureTheory.Measure
