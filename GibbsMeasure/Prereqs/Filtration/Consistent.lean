import Mathlib.Probability.Kernel.Composition
import Mathlib.Probability.Process.Filtration
import GibbsMeasure.Mathlib.Probability.Kernel.Basic
import GibbsMeasure.Prereqs.CylinderEvent

open ProbabilityTheory Set MeasureTheory ENNReal NNReal

namespace MeasureTheory.Filtration
variable {X P S E : Type*} {mX : MeasurableSpace X} {mE : MeasurableSpace E} [PartialOrder P]

/-- A family of kernels `γ` on `X` indexed by a partial order `P` is consistent under conditioning
if `γ p₂ ∘ₖ γ p₁ = γ p₁` whenever `p₁ ≤ p₂`. -/
def IsConsistentKernel (mXs : Filtration P mX) (γ : ∀ (p : P), Kernel[mXs p] X X) : Prop :=
  ∀ ⦃p₁ p₂⦄, p₁ ≤ p₂ → (γ p₂).comap id (mXs.le p₂) ∘ₖ γ p₁ = γ p₁

/-- The exterior sigma algebras to finite subsets of `S` form a filtration indexed by the
order dual of `Finset S`. -/
def cylinderEventsCompl : Filtration (Finset S)ᵒᵈ (MeasurableSpace.pi (π := fun _ : S ↦ X)) where
  seq Λ := cylinderEvents (↑(OrderDual.ofDual Λ))ᶜ
  mono' _ _ h := cylinderEvents_mono <| compl_subset_compl_of_subset h
  le' _  := cylinderEvents_le_pi

end MeasureTheory.Filtration
