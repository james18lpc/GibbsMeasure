import Mathlib.Probability.Kernel.Composition.Basic
import Mathlib.Probability.Process.Filtration

open ProbabilityTheory Set MeasureTheory ENNReal NNReal

namespace MeasureTheory.Filtration
variable {X P S E : Type*} {mX : MeasurableSpace X} {mE : MeasurableSpace E} [PartialOrder P]

/-- A family of kernels `γ` on `X` indexed by a partial order `P` is consistent under conditioning
if `γ p₂ ∘ₖ γ p₁ = γ p₁` whenever `p₁ ≤ p₂`. -/
def IsConsistentKernel (mXs : Filtration P mX) (γ : ∀ p, Kernel[mXs p] X X) : Prop :=
  ∀ ⦃p₁ p₂⦄, p₁ ≤ p₂ → (γ p₂).comap id (mXs.le p₂) ∘ₖ γ p₁ = γ p₁

end MeasureTheory.Filtration
