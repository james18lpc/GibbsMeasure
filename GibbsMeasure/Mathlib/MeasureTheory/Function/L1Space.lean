import Mathlib.MeasureTheory.Function.L1Space

namespace MeasureTheory

/-- Notation for `Integrable` with respect to a non-standard σ-algebra.-/
scoped notation "Integrable[" mα "]" => @Integrable _ _ _ mα

end MeasureTheory
