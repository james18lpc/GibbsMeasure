import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Probability.Kernel.Composition
import GibbsMeasure.Mathlib.Probability.Kernel.Basic

open CategoryTheory

namespace ProbabilityTheory
variable {X : Type*} [𝓧 : MeasurableSpace X]

variable (X) in
structure AutKer where
  𝓑 : MeasurableSpace X
  𝓑_le : 𝓑 ≤ 𝓧
  κ : Kernel[𝓑, 𝓧] X X

namespace AutKer

instance instCategory : Category.{0} (AutKer X) where
  Hom κ₁ κ₂ := PLift ((κ₁.κ).comap id _ ∘ₖ κ₂.κ = κ₂.κ)
  id := _
  comp := _

end ProbabilityTheory.AutKer
