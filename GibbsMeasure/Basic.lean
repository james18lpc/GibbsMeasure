import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Kernel.Composition

/-!
# Properness

We define the notion of properness for measure kernels and highlight important consequences in this
section
-/

open scoped ProbabilityTheory
open ProbabilityTheory
open scoped Set
open Set
open MeasureTheory ENNReal NNReal



namespace GibbsMeasure



variable {S : Type*}
variable (E : Type*) [𝓔 : MeasurableSpace E]
variable (Δ : Set S)
variable (Λ : Finset S)
section proper

variable {X : Type*} {𝓑 𝓧 : MeasurableSpace X} (hSub : 𝓑 ≤ 𝓧) (π : @kernel X X 𝓑 𝓧) {x₀ : X}

def _root_.ProbabilityTheory.kernel.IsProper : Prop :=
  ∀ (B : Set X) (B_mble : @MeasurableSet X 𝓑 B),
    kernel.restrict π (hSub B B_mble) = (fun x ↦ B.indicator (fun _ ↦ (1 : ℝ≥0∞)) x • π x)

lemma _root_.ProbabilityTheory.kernel.IsProper.def (hProper : kernel.IsProper hSub π)
    {A B : Set X} (A_mble : @MeasurableSet X 𝓧 A) (B_mble : @MeasurableSet X 𝓑 B) (x : X):
    kernel.restrict π (hSub B B_mble) x A = B.indicator (fun _ ↦ (1 : ℝ≥0∞)) x * π x A := by
  sorry

lemma lintegral_indicator_mul_indicator_eq_of_isProper (hProper : kernel.IsProper hSub π)
    {A B : Set X} (A_mble : @MeasurableSet X 𝓧 A) (B_mble : @MeasurableSet X 𝓑 B) :
    ∫⁻ x, B.indicator (fun _ ↦ (1 : ℝ≥0∞)) x * A.indicator (fun _ ↦ (1 : ℝ≥0∞)) x ∂(π x₀) =
      B.indicator (fun _↦ (1 : ℝ≥0∞)) x₀ * ∫⁻ x, A.indicator (fun _ ↦ (1 : ℝ≥0∞)) x ∂(π x₀) := by
  simp_rw [← inter_indicator_mul]
  rw [lintegral_indicator, lintegral_indicator]
  · simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, univ_inter, one_mul]
    rw [←kernel.IsProper.def hSub π hProper A_mble B_mble, inter_comm]
    exact (kernel.restrict_apply' π (hSub B B_mble) x₀ A_mble).symm
  · exact A_mble
  · sorry


lemma lintegral_simple_mul_indicator_eq_of_isProper (hProper : kernel.IsProper hSub π)
    (f : SimpleFunc X ℝ≥0) {B : Set X} (B_mble : @MeasurableSet X 𝓑 B) :
    ∫⁻ x, f x * B.indicator (fun _ ↦ (1 : ℝ≥0∞)) x ∂(π x₀)
        = B.indicator (fun _↦ (1 : ℝ≥0∞)) x₀ * ∫⁻ x, f x ∂(π x₀) := by
  sorry

lemma lintegral_mul_indicator_eq_of_isProper (hProper : kernel.IsProper hSub π)
    {f : X → ℝ≥0∞} (hf : @Measurable _ _ 𝓧 _ f) {B : Set X} (B_mble : @MeasurableSet X 𝓑 B) :
    ∫⁻ x, f x * B.indicator (fun _ ↦ (1 : ℝ≥0∞)) x ∂(π x₀)
        = B.indicator (fun _↦ (1 : ℝ≥0∞)) x₀ * ∫⁻ x, f x ∂(π x₀) := by
  rw [@MeasureTheory.lintegral_eq_nnreal X 𝓧 f (π x₀)]
  sorry


lemma lintegral_mul_eq_of_isProper (hProper : kernel.IsProper hSub π) {f g : X → ℝ≥0∞}
    (hf : @Measurable _ _ 𝓧 _ f) (hg : @Measurable _ _ 𝓑 _ g) (x₀ : X) :
    ∫⁻ x, f x * g x ∂(π x₀) = g x₀ * ∫⁻ x, f x ∂(π x₀) := by
  rw [@lintegral_eq_nnreal X 𝓧 f (π x₀), @lintegral_eq_nnreal X 𝓧 (fun x ↦ f x * g x) (π x₀)]
  sorry

lemma integral_mul_eq_of_isProper (hProper : kernel.IsProper hSub π) (f g : X → ℝ) (x₀ : X)
    (hf : @Integrable _ _ _ 𝓧 f (π x₀))
    (hg : @Integrable _ _ _ 𝓑 (f * g) (@Measure.map _ _ 𝓑 𝓧 id (π x₀))) :
    ∫ x, f x * g x ∂(π x₀) = g x₀ * ∫ x, f x ∂(π x₀) := by
  --Integrable.induction
  sorry

end proper




section introduction

def cylinderEventsIn (Δ : Set S) : MeasurableSpace (S → E) :=
  ⨆ x ∈ Δ, 𝓔.comap fun σ ↦ σ x

lemma cylinderEventsIn_univ_eq :
    cylinderEventsIn E (univ : Set S) = @MeasurableSpace.pi S (fun _ ↦ E) (fun _ ↦ 𝓔) := by
  rw [cylinderEventsIn, MeasurableSpace.pi]
  simp only [mem_univ, iSup_pos]

lemma measurable_coordinate_projection {Δ : Set S} {x : S} (h : x ∈ Δ) :
    @Measurable (S → E) E (cylinderEventsIn E Δ) _ (fun σ ↦ σ x) := by
  have key : @Measurable (S → E) E (𝓔.comap fun σ ↦ σ x) _ (fun σ ↦ σ x) := by
    exact Measurable.of_comap_le fun s a ↦ a
  exact key.mono (le_iSup₂_of_le x h (fun s a ↦ a)) le_rfl

lemma cylinderEventsIn_mono {Δ₁ Δ₂ : Set S} (h : Δ₁ ⊆ Δ₂) :
    cylinderEventsIn E Δ₁ ≤ cylinderEventsIn E Δ₂ := by
  simp only [cylinderEventsIn, iSup_le_iff]
  exact fun i i_1 ↦ le_iSup₂_of_le i (h i_1) fun s a ↦ a

lemma cylinderEventsIn_le (Δ : Set S) :
    cylinderEventsIn E Δ ≤ MeasurableSpace.pi := by
  rw [← cylinderEventsIn_univ_eq]
  apply cylinderEventsIn_mono
  exact subset_univ Δ



example (X Y : Type*) [MeasurableSpace X] (𝓨₁ 𝓨₂: MeasurableSpace Y) (h : 𝓨₁ ≤ 𝓨₂)
    (π : @kernel Y X 𝓨₁ _) :
    @kernel Y X 𝓨₂ _ :=
  kernel.comap π (fun x ↦ x) h


--variable (γ : Π (Λ : Finset S), @kernel (S → E) (S → E) (cylinderEventsIn E Λᶜ) _)
--variable (Λ₁ Λ₂ : Finset S)
--#check cylinderEventsIn_le
--#check (ProbabilityTheory.kernel.comap (γ Λ₁) (fun x ↦ x) (cylinderEventsIn_le _ _)) ∘ₖ (γ Λ₂)

variable (S)
structure Specification where
  kernel : Π (Λ : Finset S), @kernel (S → E) (S → E) (cylinderEventsIn E Λᶜ) _
  consistent : ∀ Λ₁ Λ₂ (_ : Λ₁ ⊆ Λ₂),
    (ProbabilityTheory.kernel.comap (kernel Λ₁) (fun x ↦ x) (cylinderEventsIn_le _ _)) ∘ₖ
      (kernel Λ₂) = kernel Λ₂

variable (μ : Measure (S → E)) (A : Set (S → E))

def _root_.MeasureTheory.Measure.IsGibbsMeasure (μ : Measure (S → E)) (γ : Specification S E) :=
    ∀ (Λ : Finset S) (A : Set (S → E)) (_ : MeasurableSet A),
      condexp (cylinderEventsIn E Λ.toSetᶜ) μ (A.indicator (fun _ ↦ (1 : ℝ)))
        =ᵐ[μ] (fun σ ↦ (γ.kernel Λ σ A).toReal)

#check ProbabilityTheory.condDistrib_ae_eq_condexp
#check ProbabilityTheory.condexp_ae_eq_integral_condDistrib_id

def _root_.GibbsMeasure (γ : Specification S E) :=
  {μ // MeasureTheory.Measure.IsGibbsMeasure S E μ γ}

lemma something (X : Type*) [𝓧 : MeasurableSpace X] (𝓑 : MeasurableSpace X) (hSub : 𝓑 ≤ 𝓧)
    (μ : Measure X) (π : @kernel X X 𝓑 𝓧) :
    (∀ (f : X → ℝ), Integrable f μ → condexp 𝓑 μ f =ᵐ[μ] (fun x₀ ↦ ∫ x, f x ∂(π x₀)))
    ↔ (∀ (A : Set X), MeasurableSet A → condexp 𝓑 μ (A.indicator (fun _ ↦ (1 : ℝ)))
      =ᵐ[μ] (fun x ↦ (π x A).toReal)) := by
  sorry

variable {S}
/-- Restrict `σ : S → E` to a subset `Δ⊆S` to get `σ′ : Δ → E`
-/
def restrict (Δ : Set S) (σ : S → E) : Δ → E :=
  @Subtype.restrict S (fun _ ↦ E) Δ σ

#check @measurable_pi_apply (S → E) (fun _ ↦ E) _
variable (Δ : Set S)
#check restrict E Δ
#check @Measurable (S → E) (Δ → E) (cylinderEventsIn E Δ) MeasurableSpace.pi (restrict E Δ)
#check Measurable (restrict E Δ)
#check @measurable_pi_iff (S → E) Δ (fun _ ↦ E) MeasurableSpace.pi (fun _ ↦ 𝓔) (restrict E Δ)

lemma measurableRestrictEasy (Δ : Set S) : Measurable (restrict E Δ) := by
  rw [measurable_pi_iff]
  intro x
  exact measurable_pi_apply _


lemma measurableRestrict (Δ : Set S) :
    @Measurable (S → E) (Δ → E) (cylinderEventsIn E Δ) MeasurableSpace.pi (restrict E Δ) := by
  rw [@measurable_pi_iff (S → E) Δ (fun _ ↦ E) (cylinderEventsIn E Δ) (fun _ ↦ 𝓔) (restrict E Δ)]
  intro x
  exact measurable_coordinate_projection E x.prop



end introduction







section superposition
variable {S : Type*}
variable (E : Type*) [𝓔 : MeasurableSpace E]
variable (Λ : Set S) [DecidablePred (· ∈ Λ)]
variable (η : S → E)

def superposition (ζ : Λ → E) (x : S) : E :=
  dite (x ∈ Λ) (fun h ↦ ζ ⟨x, h⟩) (fun _ ↦ η x)

lemma superposition_apply_of_mem (ζ : Λ → E) (x : S) (h : x ∈ Λ) :
    superposition E Λ η ζ x = ζ ⟨x, h⟩ := by simp [superposition, h]

lemma superposition_apply_of_not_mem (ζ : Λ → E) (x : S) (h : x ∉ Λ) :
    superposition E Λ η ζ x = η x := by simp [superposition, h]

lemma measurable_coordinate_projection_2 {Δ : Set S} {x : S} (h : x ∈ Δ) :
    @Measurable (S → E) E (cylinderEventsIn E Δ) _ (fun σ ↦ σ x) := by
  have key : @Measurable (S → E) E (𝓔.comap fun σ ↦ σ x) _ (fun σ ↦ σ x) := by
    exact Measurable.of_comap_le fun s a ↦ a
  exact key.mono (le_iSup₂_of_le x h (fun s a ↦ a)) le_rfl

lemma superposition_is_measurable : Measurable (superposition E Λ) := by
  rw [measurable_pi_iff]
  --simp [superposition]
  --intro x

  --exact?
  --exact measurable_pi_apply _
  sorry

#check Measure.pi
#check Measure.map (superposition E Λ η)

end superposition



noncomputable section ISSSD
variable {S : Type*}
variable (E : Type*) [𝓔 : MeasurableSpace E] (ν : Measure E) [IsProbabilityMeasure ν]
--variable (Λ : Finset S) [DecidablePred (· ∈ (Λ : Set S))]
variable (η : S → E)

example : Fintype Λ := by
  infer_instance

--#check Measure.pi (fun (_ : Λ) ↦ ν)
--#check Measure.map (superposition E Λ η) (Measure.pi (fun (_ : Λ) ↦ ν))
--#check @kernel (S → E) (S → E) (cylinderEventsIn E Λᶜ) _

lemma isssdProbabilityKernel_is_measurable (Λ : Finset S) [DecidablePred (· ∈ Λ.toSet)] :
    @Measurable (S → E) (Measure (S → E)) (cylinderEventsIn E Λᶜ) _
      (fun (η : S → E) ↦ Measure.map (superposition E Λ η) (Measure.pi (fun (_ : Λ) ↦ ν))) := by
  sorry

def isssdProbabilityKernel (Λ : Finset S) [DecidablePred (· ∈ Λ.toSet)] :
    @kernel (S → E) (S → E) (cylinderEventsIn E Λᶜ) _ where
  val := fun (η : S → E) ↦ Measure.map (superposition E Λ η) (Measure.pi (fun (_ : Λ) ↦ ν))
  property := by
    exact @isssdProbabilityKernel_is_measurable S E _ ν Λ _



def isssd [∀ (Λ : Finset S), DecidablePred (· ∈ Λ.toSet)] :
    Specification S E where
      kernel := (fun Λ ↦ isssdProbabilityKernel E ν Λ)
      consistent := by sorry

#check Finset.toSet
#check Set.compl
#check @Measure.dirac Λ.toSet.compl
#check ProbabilityTheory.iIndepFun


class IsISSSD (γ : Specification S E) : Prop where
  indep : ∀ (Λ : Finset S) (σ : S → E),
    iIndepFun (fun (_ : Λ) ↦ 𝓔) (fun (x : Λ) ↦ (fun (η : S → E) ↦ η x)) (γ.kernel Λ σ)
  marginal : ∀ Λ (x : S) (_ : x ∈ Λ) (σ : S → E), (γ.kernel Λ σ).map (fun η ↦ η x) = ν
  exterior : ∀ Λ (σ : S → E),
    (γ.kernel Λ σ).map (restrict E  Λ.toSet.compl ) = Measure.dirac (fun (x : Λ.toSet.compl) ↦ σ x)

-- class IsISSSD (kernel : Π (Λ : Finset S), @kernel (S → E) (S → E) (cylinderEventsIn E Λᶜ) _) :
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



lemma _root_.MeasureTheory.Measure.eq_prod_of_dirac_right (X Y : Type*) [MeasurableSpace X]
    [MeasurableSpace Y] (ν : Measure X) (y : Y) (μ : Measure (X × Y))
    (marg_X : Measure.map Prod.fst μ = ν) (marg_Y : Measure.map Prod.snd μ = Measure.dirac y) :
    μ = ν.prod (Measure.dirac y) := by
-- dynkin's pi system lemma
  sorry

lemma _root_.MeasureTheory.Measure.eq_prod_of_dirac_left (X Y : Type*) [MeasurableSpace X]
    [MeasurableSpace Y] (x : X) (ν : Measure Y) (μ : Measure (X × Y))
    (marg_X : Measure.map Prod.fst μ = Measure.dirac x) (marg_Y : Measure.map Prod.snd μ = ν) :
    μ = (Measure.dirac x).prod ν := by

  sorry

-- lemma IsISSSD.indep_marginal_exterior :

--def isssd (h : ):

end ISSSD
end GibbsMeasure

#check Subtype.restrict
