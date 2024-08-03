import Mathlib.MeasureTheory.Measure.Typeclasses

namespace MeasureTheory
variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} [SigmaFinite μ] {m n : ℕ}

@[gcongr]
lemma spanningSets_subset_spanningSets (hmn : m ≤ n) : spanningSets μ m ⊆ spanningSets μ n :=
  monotone_spanningSets _ hmn

attribute [simp] iUnion_spanningSets

end MeasureTheory
