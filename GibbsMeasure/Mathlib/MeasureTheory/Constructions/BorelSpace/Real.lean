import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

variable {α : Type*} {mα : MeasurableSpace α}

-- TODO: Replace `Measurable.ennreal_ofReal`
@[measurability, fun_prop]
lemma Measurable.ennreal_ofReal' {f : α → ℝ} (hf : Measurable f) :
    Measurable fun x ↦ ENNReal.ofReal (f x) := ENNReal.continuous_ofReal.measurable.comp hf
