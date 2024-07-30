import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

namespace MeasureTheory

/-- Notation for `Measure` with respect to a non-standard σ-algebra in the domain. -/
scoped notation "Measure[" mα "]" α:arg => @Measure α mα

end MeasureTheory
