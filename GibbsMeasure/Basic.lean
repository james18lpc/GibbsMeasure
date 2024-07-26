import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Ideal
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Kernel.Composition
import GibbsMeasure.Mathlib.Data.Finset.Basic
import GibbsMeasure.KolmogorovExtension4.ProductMeasure
import GibbsMeasure.Prereqs.Juxt
import GibbsMeasure.Prereqs.Kernel.Proper

/-!
# Gibbs measures

This file defines Gibbs measures.
-/

open ProbabilityTheory Set MeasureTheory ENNReal NNReal


variable {S E : Type*} [𝓔 : MeasurableSpace E] {Λ₁ Λ₂ : Finset S}

/-- A family of kernels `γ` is consistent if `γ Λ₁ ∘ₖ γ Λ₂ = γ Λ₂` for all `Λ₁ ⊆ Λ₂`.

Morally, the LHS should be thought of as discovering `Λ₁` then `Λ₂`, while the RHS should be
thought of as discovering `Λ₂` straight away. -/
def IsConsistent (γ : ∀ Λ : Finset S, Kernel[cylinderEvents Λᶜ] (S → E) (S → E)) : Prop :=
  ∀ ⦃Λ₁ Λ₂⦄, Λ₁ ⊆ Λ₂ → (γ Λ₁).comap id cylinderEvents_le_pi ∘ₖ toFun Λ₂ = toFun Λ₂

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

  DO NOT USE. Instead use `Specification.isConsistent`. -/
  isConsistent' : IsConsistent toFun

namespace Specification

instance instDFunLike :
    DFunLike (Specification S E) (Finset S) fun Λ ↦ Kernel[cylinderEvents Λᶜ] (S → E) (S → E)
    where
  coe := toFun
  coe_injective' γ₁ γ₂ h := by cases γ₁; cases γ₂; congr

/-- The marginal kernels of a specification are consistent. -/
lemma isConsistent (γ : Specification S E) (hΛ : Λ₁ ⊆ Λ₂) :
  (γ Λ₁).comap id cylinderEvents_le_pi ∘ₖ γ Λ₂ = γ Λ₂ := γ.isConsistent' _ _ hΛ

/-- A specification is proper if all its marginal kernels are. -/
def IsProper (γ : Specification S E) : Prop := ∀ Λ : Finset S, (γ Λ).IsProper

variable {γ : Specification S E}

lemma isProper_iff_restrict_eq_indicator_smul :
    γ.IsProper ↔
      ∀ (Λ : Finset S) ⦃B : Set (S → E)⦄ (hB : MeasurableSet[cylinderEvents Λᶜ] B) (x : S → E),
      (γ Λ).restrict (cylinderEvents_le_pi _ hB) x = B.indicator (1 : (S → E) → ℝ≥0∞) x • γ Λ x :=
  forall_congr' fun _ ↦ Kernel.isProper_iff_restrict_eq_indicator_smul _

lemma isProper_iff_restrict_eq_indicator_mul :
    γ.IsProper ↔
      ∀ (Λ : Finset S) ⦃A : Set (S → E)⦄ (_hA : MeasurableSet A) ⦃B : Set (S → E)⦄
        (hB : MeasurableSet[cylinderEvents Λᶜ] B) (x : S → E),
      (γ Λ).restrict (cylinderEvents_le_pi _ hB) x A = B.indicator 1 x * γ Λ x A :=
  forall_congr' fun _ ↦ Kernel.isProper_iff_restrict_eq_indicator_mul _

/-- For a specification `γ`, a Gibbs measure is a measure whose finite marginals agree with `γ`. -/
def IsGibbsMeasure (γ : Specification S E) (μ : Measure (S → E)) : Prop :=
  ∀ (Λ : Finset S) (A : Set (S → E)), MeasurableSet A →
    condexp (cylinderEvents Λᶜ) μ (A.indicator fun _ ↦ 1) =ᵐ[μ] fun σ ↦ (γ Λ σ A).toReal

noncomputable section ISSSD
variable (ν : Measure E) (η : S → E)

-- TODO: Use `measurable_of_measurable_coe'` + measurable rectangles here
private lemma measurable_isssdFun (Λ : Finset S) :
    Measurable[cylinderEvents Λᶜ]
      fun η : S → E ↦ (Measure.pi fun _ : Λ ↦ ν).map (juxt E Λ η) := by
  refine @Measure.measurable_of_measurable_coe _ _ _ (_) _ ?_
  rintro A hA
  simp
  sorry

/-- Auxiliary definition for `Specification.isssd`. -/
@[simps (config := .asFn)]
def isssdFun (ν : Measure E) (Λ : Finset S) :
    Kernel[cylinderEvents Λᶜ] (S → E) (S → E) :=
  @Kernel.mk _ _ (_) _
    (fun η ↦ Measure.map (juxt E Λ η) (Measure.pi fun _ : Λ ↦ ν))
    (measurable_isssdFun ν Λ)

/-- The ISSSD of a measure is strongly consistent. -/
lemma isssdFun_comp_isssdFun [DecidableEq S] (Λ₁ Λ₂ : Finset S) :
    (isssdFun ν Λ₁).comap id cylinderEvents_le_pi ∘ₖ isssdFun ν Λ₂ =
      (isssdFun ν (Λ₁ ∪ Λ₂)).comap id
        (measurable_id'' $ by gcongr; exact Finset.subset_union_right) :=
  sorry

/-- The **Independent Specification with Single Spin Distribution**.

This is the specification corresponding to the product measure -/
@[simps]
def isssd : Specification S E where
  toFun := isssdFun ν
  isConsistent' Λ₁ Λ₂ hΛ := by
    classical
    rw [isssdFun_comp_isssdFun]
    ext a s _
    simp only [Kernel.comap_apply, id_eq, isssdFun_toFun, Finset.coe_sort_coe]
    rw [Finset.union_eq_right.2 hΛ]

/-- The ISSSD of a measure is strongly consistent. -/
lemma isssd_comp_isssd [DecidableEq S] (Λ₁ Λ₂ : Finset S) :
    (isssd ν Λ₁).comap id cylinderEvents_le_pi ∘ₖ isssd ν Λ₂ =
      (isssd ν (Λ₁ ∪ Λ₂)).comap id
        (measurable_id'' $ by gcongr; exact Finset.subset_union_right) := isssdFun_comp_isssdFun ..

protected lemma IsProper.isssd : (isssd (S := S) ν).IsProper := by
  rw [isProper_iff_restrict_eq_indicator_mul]
  rintro Λ A hA B hB x
  rw [Kernel.restrict_apply, Measure.restrict_apply hA]
  simp only [isssd_toFun, isssdFun_toFun, Finset.coe_sort_coe]
  sorry

end ISSSD

section ProductMeasure

/-- The product measure `ν ^ S` is a `isssd μ`-Gibbs measure. -/
lemma isGibbsMeasure_isssd_productMeasure (ν : Measure E) [IsProbabilityMeasure ν] :
    (isssd ν).IsGibbsMeasure (productMeasure fun _ : S ↦  ν) := by
  rintro Λ
  sorry

end ProductMeasure
end Specification

variable (X : Type*) (f : X → ℝ)

-- TODO: add to blueprint
lemma condexp_ae_eq_kernel_apply {X : Type*} [𝓧 : MeasurableSpace X] (𝓑 : MeasurableSpace X)
    --(hSub : 𝓑 ≤ 𝓧)
    (μ : @Measure X 𝓧) [IsFiniteMeasure μ]
    (π : Kernel[𝓑, 𝓧] X X) [∀ (x : X), IsFiniteMeasure (π x)]
    (h : ∀ (f : X → ℝ), Bornology.IsBounded (Set.range f) → Measurable[𝓧] f →
      condexp 𝓑 μ f =ᵐ[μ] (fun x₀ ↦ ∫ x, f x ∂(π x₀)))
    {A : Set X} (A_mble : MeasurableSet[𝓧] A) :
    condexp 𝓑 μ (A.indicator (fun _ ↦ (1 : ℝ))) =ᵐ[μ] (fun x ↦ (π x A).toReal) := by
  have ind_bdd : Bornology.IsBounded (Set.range (A.indicator (fun _ ↦ (1 : ℝ)))) := by
    apply (Metric.isBounded_Icc (0 : ℝ) 1).subset
    rw [range_subset_iff]
    intro x
    by_cases hx : x ∈ A <;> simp [hx]
  have ind_mble : Measurable[𝓧] (A.indicator (fun _ ↦ (1 : ℝ))) := by
    exact (measurable_indicator_const_iff 1).mpr A_mble
  specialize h _ ind_bdd ind_mble
  apply h.trans
  simp_rw [← Pi.one_def, @integral_indicator_one X 𝓧 _ _ A_mble]
  rfl

lemma condexp_indicator_ae_eq_integral_kernel {X : Type*} [𝓧 : MeasurableSpace X] (𝓑 : MeasurableSpace X)
    --(hSub : 𝓑 ≤ 𝓧)
    (μ : @Measure X 𝓧) [IsFiniteMeasure μ]
    (π : Kernel[𝓑, 𝓧] X X) [∀ (x : X), IsFiniteMeasure (π x)]
    {A : Set X} (A_mble : MeasurableSet[𝓧] A)
    (h : condexp 𝓑 μ (A.indicator (fun _ ↦ (1 : ℝ))) =ᵐ[μ] (fun x ↦ (π x A).toReal)) :
    condexp 𝓑 μ (A.indicator (fun _ ↦ (1 : ℝ)))
      =ᵐ[μ] (fun x₀ ↦ ∫ x, A.indicator (fun _ ↦ (1 : ℝ)) x ∂(π x₀)) := by
  apply h.trans
  simp_rw [← Pi.one_def, @integral_indicator_one X 𝓧 _ _ A_mble]
  rfl


lemma condexp_const_indicator_ae_eq_integral_kernel {X : Type*} [𝓧 : MeasurableSpace X] (𝓑 : MeasurableSpace X)
    --(hSub : 𝓑 ≤ 𝓧)
    (μ : @Measure X 𝓧) [IsFiniteMeasure μ]
    (π : Kernel[𝓑, 𝓧] X X) [∀ (x : X), IsFiniteMeasure (π x)]
    (c : ℝ)
    {A : Set X} (A_mble : MeasurableSet[𝓧] A)
    (h : condexp 𝓑 μ (A.indicator (fun _ ↦ (1 : ℝ))) =ᵐ[μ] (fun x ↦ (π x A).toReal)) :
    condexp 𝓑 μ (A.indicator (fun _ ↦ (c : ℝ)))
      =ᵐ[μ] (fun x₀ ↦ ∫ x, A.indicator (fun _ ↦ (c : ℝ)) x ∂(π x₀)) := by
  have smul_eq : A.indicator (fun _ ↦ (c : ℝ)) = c • A.indicator (fun _ ↦ (1 : ℝ)) := by
    sorry
  have foo : c • condexp 𝓑 μ (A.indicator (fun _ ↦ (1 : ℝ)))
     =ᵐ[μ] condexp 𝓑 μ (A.indicator (fun _ ↦ (c : ℝ))) := by
    have := @condexp_smul X ℝ ℝ _ _ _ _ _ 𝓑 𝓧 μ c (A.indicator (fun _ ↦ (1 : ℝ)))
    rw [smul_eq]
    exact Filter.EventuallyEq.symm this
  nth_rw 2 [smul_eq]
  have int_smul (x₀ : X) := @integral_smul X ℝ _ ℝ _ _ 𝓧 (π x₀) _ _ c (A.indicator (fun _ ↦ (1 : ℝ)))
  --simp_rw [@integral_smul X ℝ _ ℝ _ _ 𝓧 (π _) _ _ c (A.indicator (fun _ ↦ (1 : ℝ)))]
  --apply this.symm
  simp at *
  simp_rw [int_smul]
  --rw [smul_eq]
  apply foo.symm.trans
  have : c • (fun x₀ ↦ ∫ (a : X), A.indicator (fun x ↦ (1 : ℝ)) a ∂π x₀)
     = fun x₀ ↦ c * ∫ (a : X), A.indicator (fun x ↦ (1 : ℝ)) a ∂π x₀ := by
    sorry
  rw [← this]
  have := @condexp_indicator_ae_eq_integral_kernel X 𝓧 𝓑 μ _ π _ A A_mble h

  --change c • μ[A.indicator fun x ↦ 1|𝓑] =ᶠ[ae μ] c • (fun x₀ ↦ ∫ (a : X), A.indicator (fun x ↦ 1) a ∂π x₀)
  sorry

lemma condexp_simpleFunc_ae_eq_integral_kernel {X : Type*} [𝓧 : MeasurableSpace X] (𝓑 : MeasurableSpace X)
    --(hSub : 𝓑 ≤ 𝓧)
    (μ : @Measure X 𝓧) [IsFiniteMeasure μ]
    (π : Kernel[𝓑, 𝓧] X X) [∀ (x : X), IsFiniteMeasure (π x)]
    (h : ∀ (A : Set X), MeasurableSet[𝓧] A →
      condexp 𝓑 μ (A.indicator (fun _ ↦ (1 : ℝ))) =ᵐ[μ] (fun x ↦ (π x A).toReal))
    (f : @SimpleFunc X 𝓧 ℝ) :
    condexp 𝓑 μ f =ᵐ[μ] (fun x₀ ↦ ∫ x, f x ∂(π x₀)) := by
  induction' f using SimpleFunc.induction with c A A_mble
  case h_ind =>
    sorry
  case h_add => sorry


lemma bind_eq_self_iff (X : Type*) [𝓧 : MeasurableSpace X] (𝓑 : MeasurableSpace X) (hSub : 𝓑 ≤ 𝓧)
    (μ : @Measure X 𝓧) (π : Kernel[𝓑, 𝓧] X X) (π_proper : π.IsProper)
    (A : Set X) (A_mble : MeasurableSet A) :
    condexp 𝓑 μ (A.indicator (fun _ ↦ (1 : ℝ)))
      =ᵐ[μ] (fun x ↦ (π x A).toReal) ↔ @Measure.bind X X 𝓧 𝓧 μ π A = μ A :=
  ⟨by
  intro h
  have : μ A = μ A := by
    sorry
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
