import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Ideal
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Kernel.Composition
import GibbsMeasure.Mathlib.Data.Finset.Basic
import GibbsMeasure.Prereqs.Extend
import GibbsMeasure.Prereqs.Kernel.Proper

/-!
# Gibbs measures

This file defines Gibbs measures.
-/

open ProbabilityTheory Set MeasureTheory ENNReal NNReal


variable {S E : Type*} [𝓔 : MeasurableSpace E] {Λ₁ Λ₂ : Finset S}

variable (S E) in
/-- A specification from `S` to `E` is a collection of "marginal kernels" on the complement of
finite sets, compatible under restriction.

The name "marginal kernels" comes from the fact that the marginals of a Gibbs measure following a
specification precisely are the marginal kernels of that specification. -/
structure Specification where
  /-- The marginal kernels of a specification.

  DO NOT USE. Instead use the coercion to function `⇑γ`. Lean should insert it automatically in most
  cases. -/
  toFun (Λ : Finset S) : Kernel[cylinderEvents Λᶜ] (S → E) (S → E)
  /-- The marginal kernels of a specification are compatible under restriction.

  Morally, the LHS should be thought of as discovering `Λ₁` then `Λ₂`, while the RHS should be
  thought of as discovering `Λ₂`.

  DO NOT USE. Instead use the coercion to function `⇑γ`. Lean should insert it automatically in most
  cases. -/
  comp_of_subset' {Λ₁ Λ₂} :
    Λ₁ ⊆ Λ₂ → (toFun Λ₁).comap id cylinderEvents_le_pi ∘ₖ toFun Λ₂ = toFun Λ₂

namespace Specification

instance instDFunLike :
    DFunLike (Specification S E) (Finset S) fun Λ ↦ Kernel[cylinderEvents Λᶜ] (S → E) (S → E)
    where
  coe := toFun
  coe_injective' γ₁ γ₂ h := by cases γ₁; cases γ₂; congr

/-- The marginal kernels of a specification are compatible under restriction.

Morally, the LHS should be thought of as discovering `Λ₁` then `Λ₂`, while the RHS should be
thought of as discovering `Λ₂`. -/
lemma comp_of_subset (γ : Specification S E) (hΛ : Λ₁ ⊆ Λ₂) :
  (γ Λ₁).comap id cylinderEvents_le_pi ∘ₖ γ Λ₂ = γ Λ₂ := γ.comp_of_subset' hΛ

/-- A specification is proper if all its marginal kernels are. -/
def IsProper (γ : Specification S E) : Prop := ∀ Λ : Finset S, (γ Λ).IsProper

/-- For a specification `γ`, a Gibbs measure is a measure whose finite marginals agree with `γ`. -/
def IsGibbsMeasure (γ : Specification S E) (μ : Measure (S → E)) : Prop :=
  ∀ (Λ : Finset S) (A : Set (S → E)), MeasurableSet A →
    condexp (cylinderEvents Λᶜ) μ (A.indicator fun _ ↦ 1) =ᵐ[μ] fun σ ↦ (γ Λ σ A).toReal

noncomputable section ISSSD
variable (ν : Measure E) (η : S → E)

private lemma measurable_isssdFun (Λ : Finset S) :
    Measurable[cylinderEvents Λᶜ]
      fun η : S → E ↦ (Measure.pi fun _ : Λ ↦ ν).map (extend E Λ η) := by
  rintro A hA
  sorry

/-- Auxiliary definition for `Specification.isssd`. -/
def isssdFun (ν : Measure E) (Λ : Finset S) :
    Kernel[cylinderEvents Λᶜ] (S → E) (S → E) :=
  @Kernel.mk _ _ (_) _
    (fun η ↦ Measure.map (extend E Λ η) (Measure.pi fun _ : Λ ↦ ν))
    (measurable_isssdFun ν Λ)

/-- The ISSSD of a measure is strongly consistent. -/
lemma isssdFun_comp_isssdFun [DecidableEq S] (Λ₁ Λ₂ : Finset S) :
    (isssdFun ν Λ₁).comap id cylinderEvents_le_pi ∘ₖ isssdFun ν Λ₂ =
      (isssdFun ν (Λ₁ ∪ Λ₂)).comap id
        (measurable_id'' $ by gcongr; exact Finset.subset_union_right) :=
  sorry

/-- The **Independent Specification with Single Spin Distribution**.

This is the specification corre -/
def isssd : Specification S E where
  toFun := isssdFun ν
  comp_of_subset' := by sorry

/-- The ISSSD of a measure is strongly consistent. -/
lemma isssd_comp_isssd [DecidableEq S] (Λ₁ Λ₂ : Finset S) :
    (isssd ν Λ₁).comap id cylinderEvents_le_pi ∘ₖ isssd ν Λ₂ =
      (isssd ν (Λ₁ ∪ Λ₂)).comap id
        (measurable_id'' $ by gcongr; exact Finset.subset_union_right) := isssdFun_comp_isssdFun ..

end ISSSD
end Specification

lemma something (X : Type*) [𝓧 : MeasurableSpace X] (𝓑 : MeasurableSpace X) (hSub : 𝓑 ≤ 𝓧)
    (μ : @Measure X 𝓧) (π : Kernel[𝓑, 𝓧] X X) :
    (∀ (f : X → ℝ), Integrable f μ → condexp 𝓑 μ f =ᵐ[μ] (fun x₀ ↦ ∫ x, f x ∂(π x₀)))
    ↔ (∀ (A : Set X), MeasurableSet A → condexp 𝓑 μ (A.indicator (fun _ ↦ (1 : ℝ)))
      =ᵐ[μ] (fun x ↦ (π x A).toReal)) := by
  sorry


lemma something2 (X : Type*) [𝓧 : MeasurableSpace X] (𝓑 : MeasurableSpace X) (hSub : 𝓑 ≤ 𝓧)
    (μ : @Measure X 𝓧) (π : Kernel[𝓑, 𝓧] X X) (π_proper : π.IsProper)
    (A : Set X) (A_mble : MeasurableSet A) :
    condexp 𝓑 μ (A.indicator (fun _ ↦ (1 : ℝ)))
      =ᵐ[μ] (fun x ↦ (π x A).toReal) ↔ @Measure.bind X X 𝓧 𝓧 μ π A = μ A :=
  ⟨by
  intro h
  have : μ A = μ A := by
    sorry
  funext
  sorry,
  by sorry⟩

lemma MeasureTheory.Measure.char_Gibbs (μ : Measure (S → E)) (γ : Specification S E) : List.TFAE [
    γ.IsGibbsMeasure μ ,
    ∀ (Λ : Finset S), Measure.bind μ (γ Λ) = μ,
    ∃ (𝓢 : Order.Cofinal (Finset S)), (∀ (Λ : 𝓢.carrier), Measure.bind μ (γ Λ) = μ)
] := by
  tfae_have 1 → 2
  · sorry
  · sorry
