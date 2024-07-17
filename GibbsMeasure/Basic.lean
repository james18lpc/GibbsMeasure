import GibbsMeasure.Prereqs.Extend
import GibbsMeasure.Prereqs.Kernel.Proper
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Kernel.Composition

/-!
# Gibbs measures

This file defines Gibbs measures.
-/

open ProbabilityTheory Set MeasureTheory ENNReal NNReal

lemma something (X : Type*) [𝓧 : MeasurableSpace X] (𝓑 : MeasurableSpace X) (hSub : 𝓑 ≤ 𝓧)
    (μ : Measure X) (π : @kernel X X 𝓑 𝓧) :
    (∀ (f : X → ℝ), Integrable f μ → condexp 𝓑 μ f =ᵐ[μ] (fun x₀ ↦ ∫ x, f x ∂(π x₀)))
    ↔ (∀ (A : Set X), MeasurableSet A → condexp 𝓑 μ (A.indicator (fun _ ↦ (1 : ℝ)))
      =ᵐ[μ] (fun x ↦ (π x A).toReal)) := by
  sorry

variable {S E : Type*} [𝓔 : MeasurableSpace E]

variable (S E) in
/-- A specification from `S` to `E` is a collection of "marginals" on the complement of finite sets,
compatible under restriction.

The marginals are implemented as a collection of kernels, one `Λᶜ`-measurable kernel for each finite
set `Λ`. -/
structure Specification where
  /-- The marginals of a specification. -/
  condKernelCompl (Λ : Finset S) : @kernel (S → E) (S → E) (cylinderEvents Λᶜ) _
  /-- The marginals of a specification are compatible under restriction.

  Morally, the LHS should be thought of as discovering `Λ₁` then `Λ₂`, while the RHS should be
  thought of as discovering `Λ₂`. -/
  condKernelCompl_comp_condKernelCompl (Λ₁ Λ₂) (_ : Λ₁ ⊆ Λ₂) :
    kernel.comap (condKernelCompl Λ₁) (fun x ↦ x) (cylinderEvents_le_pi _) ∘ₖ condKernelCompl Λ₂ =
      condKernelCompl Λ₂

variable (μ : Measure (S → E)) (A : Set (S → E))

/-- For a specification `γ`, a Gibbs measure is a measure whose finite marginals agree with `γ`. -/
def MeasureTheory.Measure.IsGibbs (μ : Measure (S → E)) (γ : Specification S E) : Prop :=
    ∀ (Λ : Finset S) (A : Set (S → E)) (_ : MeasurableSet A),
      condexp (cylinderEvents Λ.toSetᶜ) μ (A.indicator (fun _ ↦ (1 : ℝ)))
        =ᵐ[μ] (fun σ ↦ (γ.condKernelCompl Λ σ A).toReal)


noncomputable section ISSSD
variable {S : Type*}
variable (E : Type*) [𝓔 : MeasurableSpace E] (ν : Measure E) [IsProbabilityMeasure ν]
--variable (Λ : Finset S) [DecidablePred (· ∈ (Λ : Set S))]
variable (η : S → E)

------
lemma isssdProbabilityKernel_is_measurable (Λ : Finset S) [DecidablePred (· ∈ Λ.toSet)] :
    @Measurable (S → E) (Measure (S → E)) (cylinderEvents Λᶜ) _
      (fun (η : S → E) ↦ Measure.map (extend E Λ η) (Measure.pi (fun (_ : Λ) ↦ ν))) := by
  sorry

def isssdProbabilityKernel (Λ : Finset S) [DecidablePred (· ∈ Λ.toSet)] :
    @kernel (S → E) (S → E) (cylinderEvents Λᶜ) _ where
  val := fun (η : S → E) ↦ Measure.map (extend E Λ η) (Measure.pi (fun (_ : Λ) ↦ ν))
  property := by
    exact @isssdProbabilityKernel_is_measurable S E _ ν Λ _



def isssd [∀ (Λ : Finset S), DecidablePred (· ∈ Λ.toSet)] : Specification S E where
  condKernelCompl Λ := isssdProbabilityKernel E ν Λ
  condKernelCompl_comp_condKernelCompl := by sorry



class IsISSSD (γ : Specification S E) : Prop where
  indep : ∀ (Λ : Finset S) (σ : S → E),
    iIndepFun (fun (_ : Λ) ↦ 𝓔) (fun (x : Λ) ↦ (fun (η : S → E) ↦ η x)) (γ.condKernelCompl Λ σ)
  marginal : ∀ Λ (x : S) (_ : x ∈ Λ) (σ : S → E), (γ.condKernelCompl Λ σ).map (fun η ↦ η x) = ν
  exterior : ∀ Λ (σ : S → E),
    (γ.condKernelCompl Λ σ).map (restrict Λ.toSet.compl) = .dirac (fun (x : Λ.toSet.compl) ↦ σ x)

-- class IsISSSD (kernel : Π (Λ : Finset S), @kernel (S → E) (S → E) (cylinderEvents Λᶜ) _) :
--    Prop where
--   indep : ∀ (Λ : Finset S) (σ : S → E),
--     iIndepFun (fun (_ : Λ) ↦ 𝓔) (fun (x : Λ) ↦ (fun η ↦ η x)) (kernel Λ σ)
--   marginal : ∀ Λ (x : S) (_ : x ∈ Λ) (σ : S → E), (kernel Λ σ).map (fun η ↦ η x) = ν
--   exterior : ∀ Λ (σ : S → E),
--     (kernel Λ σ).map (restrict E  Λ.toSet.compl ) = Measure.dirac (fun (x : Λ.toSet.compl) ↦ σ x)

instance  [∀ (Λ : Finset S), DecidablePred (· ∈ Λ.toSet)] : IsISSSD E ν (@isssd S E 𝓔 ν _) where
  indep := by sorry
  marginal := by sorry
  exterior := by sorry

-- lemma IsISSSD.indep_marginal_exterior :

--def isssd (h : ):

end ISSSD
