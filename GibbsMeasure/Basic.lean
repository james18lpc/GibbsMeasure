import GibbsMeasure.Prereqs.Extend
import GibbsMeasure.Prereqs.Kernel.Proper
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Kernel.Composition

/-!
# Properness

We define the notion of properness for measure kernels and highlight important consequences in this
section
-/

open ProbabilityTheory Set MeasureTheory ENNReal NNReal

variable {S E : Type*} [𝓔 : MeasurableSpace E]

section introduction

variable (S E) in
structure Specification where
  toKernel (Λ : Finset S) : @kernel (S → E) (S → E) (cylinderEvents Λᶜ) _
  toKernel_comp_toKernel (Λ₁ Λ₂) (_ : Λ₁ ⊆ Λ₂) :
    kernel.comap (toKernel Λ₁) (fun x ↦ x) (cylinderEvents_le_pi _) ∘ₖ toKernel Λ₂ = toKernel Λ₂

variable (μ : Measure (S → E)) (A : Set (S → E))

def MeasureTheory.Measure.IsGibbsMeasure (μ : Measure (S → E)) (γ : Specification S E) :=
    ∀ (Λ : Finset S) (A : Set (S → E)) (_ : MeasurableSet A),
      condexp (cylinderEvents Λ.toSetᶜ) μ (A.indicator (fun _ ↦ (1 : ℝ)))
        =ᵐ[μ] (fun σ ↦ (γ.toKernel Λ σ A).toReal)

def GibbsMeasure (γ : Specification S E) := {μ : Measure _ // μ.IsGibbsMeasure  γ}

lemma something (X : Type*) [𝓧 : MeasurableSpace X] (𝓑 : MeasurableSpace X) (hSub : 𝓑 ≤ 𝓧)
    (μ : Measure X) (π : @kernel X X 𝓑 𝓧) :
    (∀ (f : X → ℝ), Integrable f μ → condexp 𝓑 μ f =ᵐ[μ] (fun x₀ ↦ ∫ x, f x ∂(π x₀)))
    ↔ (∀ (A : Set X), MeasurableSet A → condexp 𝓑 μ (A.indicator (fun _ ↦ (1 : ℝ)))
      =ᵐ[μ] (fun x ↦ (π x A).toReal)) := by
  sorry

end introduction


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
  toKernel Λ := isssdProbabilityKernel E ν Λ
  toKernel_comp_toKernel := by sorry



class IsISSSD (γ : Specification S E) : Prop where
  indep : ∀ (Λ : Finset S) (σ : S → E),
    iIndepFun (fun (_ : Λ) ↦ 𝓔) (fun (x : Λ) ↦ (fun (η : S → E) ↦ η x)) (γ.toKernel Λ σ)
  marginal : ∀ Λ (x : S) (_ : x ∈ Λ) (σ : S → E), (γ.toKernel Λ σ).map (fun η ↦ η x) = ν
  exterior : ∀ Λ (σ : S → E),
    (γ.toKernel Λ σ).map (restrict Λ.toSet.compl) = .dirac (fun (x : Λ.toSet.compl) ↦ σ x)

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
