import Mathlib
open scoped ProbabilityTheory
open ProbabilityTheory

open scoped Set
open Set

open MeasureTheory

namespace GibbsMeasure

section introduction

variable {S : Type*}
variable (E : Type*) [𝓔 : MeasurableSpace E]
variable (Λ : Finset S)


#check ProbabilityTheory.kernel.comp


#check MeasurableSpace.comap


--def cylinderEventsIn [m : ∀ a, MeasurableSpace (π a)] : MeasurableSpace (∀ a, π a) :=
  --⨆ a, (m a).comap fun b => b a

#check ‹MeasurableSpace E›



def cylinderEventsIn (Δ : Set S) : MeasurableSpace (S → E) :=
  ⨆ x ∈ Δ, 𝓔.comap fun σ ↦ σ x

lemma cylinderEventsIn_univ_eq :
    cylinderEventsIn E (univ : Set S) = @MeasurableSpace.pi S (fun _ ↦ E) (fun _ ↦ 𝓔) := by
  rw [cylinderEventsIn, MeasurableSpace.pi]
  simp only [mem_univ, iSup_pos]

lemma measurableCoordinateProjection {Δ : Set S} {x : S} (h : x ∈ Δ) :
    @Measurable (S → E) E (cylinderEventsIn E Δ) _ (fun σ ↦ σ x) := by
  have key : @Measurable (S → E) E (𝓔.comap fun σ ↦ σ x) _ (fun σ ↦ σ x) := by
    exact Measurable.of_comap_le fun s a ↦ a
  exact key.mono (le_iSup₂_of_le x h (fun s a ↦ a)) le_rfl

lemma cylinderEventsIn_mono {Δ₁ Δ₂ : Set S} (h : Δ₁ ⊆ Δ₂) : cylinderEventsIn E Δ₁ ≤ cylinderEventsIn E Δ₂ := by
  simp only [cylinderEventsIn, iSup_le_iff]
  exact fun i i_1 ↦ le_iSup₂_of_le i (h i_1) fun s a ↦ a

lemma cylinderEventsIn_le (Δ : Set S) :
    cylinderEventsIn E Δ ≤ MeasurableSpace.pi := by
  rw [← cylinderEventsIn_univ_eq]
  apply cylinderEventsIn_mono
  exact subset_univ Δ



example (X Y : Type*) [𝓧 : MeasurableSpace X] (𝓨₁ 𝓨₂: MeasurableSpace Y) (h : 𝓨₁ ≤ 𝓨₂)
    (π : @kernel Y X 𝓨₁ _) :
    @kernel Y X 𝓨₂ _ :=
  kernel.comap π (fun x ↦ x) h




-- TODO: pull request
lemma iSup_measurable_of_measurable (X Y I : Type*) (sigmaAlgebras : I → MeasurableSpace X) (i₀ : I) (f : X → Y) [MeasurableSpace Y]
    (h : @Measurable X Y (sigmaAlgebras i₀) _ f) :
    @Measurable X Y (⨆ i, sigmaAlgebras i) _ f :=
  h.mono (le_iSup sigmaAlgebras i₀) le_rfl

-- TODO: pull request
lemma sup_measurable_of_measurable (X Y : Type*) (𝓢₁ 𝓢₂ : MeasurableSpace X) (f : X → Y) [MeasurableSpace Y]
    (h : @Measurable X Y 𝓢₁ _ f) :
    @Measurable X Y (𝓢₁ ⊔ 𝓢₂) _ f :=
  h.mono (SemilatticeSup.le_sup_left 𝓢₁ 𝓢₂) le_rfl



#check @ProbabilityTheory.kernel (S → E) (S → E) (cylinderEventsIn E Λᶜ) _
#check Π (Λ : Finset S), @ProbabilityTheory.kernel (S → E) (S → E) (cylinderEventsIn E Λᶜ) _
variable (γ : Π (Λ : Finset S), @ProbabilityTheory.kernel (S → E) (S → E) (cylinderEventsIn E Λᶜ) _)
variable (Λ₁ Λ₂ : Finset S)
#check cylinderEventsIn_le
#check (ProbabilityTheory.kernel.comap (γ Λ₁) (fun x ↦ x) (cylinderEventsIn_le _ _)) ∘ₖ (γ Λ₂)


structure Specification where
  kernel : Π (Λ : Finset S), @kernel (S → E) (S → E) (cylinderEventsIn E Λᶜ) _
  consistent : (ProbabilityTheory.kernel.comap (γ Λ₁) (fun x ↦ x) (cylinderEventsIn_le _ _)) ∘ₖ (γ Λ₂) = γ Λ₂

/-- Restrict `σ : S → E` to a subset `Δ⊆S` to get `σ′ : Δ → E`
-/
def restrict (Δ : Set S) (σ : S → E) : Δ → E :=
  @Subtype.restrict S (fun _ ↦ E) Δ σ

#check @measurable_pi_apply (S → E) (fun _ ↦ E) _
variable (Δ : Set S)
#check restrict E Δ
#check @Measurable (S → E) (Δ → E) (cylinderEventsIn E Δ) MeasurableSpace.pi (restrict E Δ)
#check Measurable (restrict E Δ)
#check Measurable (restrict E Δ) = @Measurable (S → E) (Δ → E) (cylinderEventsIn E Δ) MeasurableSpace.pi (restrict E Δ)
#check @measurable_pi_iff (S → E) Δ (fun _ ↦ E) MeasurableSpace.pi (fun _ ↦ 𝓔) (restrict E Δ)

lemma measurableRestrictEasy (Δ : Set S) : Measurable (restrict E Δ) := by
  rw [measurable_pi_iff]
  intro x
  exact measurable_pi_apply _


lemma measurableRestrict (Δ : Set S) :
    @Measurable (S → E) (Δ → E) (cylinderEventsIn E Δ) MeasurableSpace.pi (restrict E Δ) := by
  rw [@measurable_pi_iff (S → E) Δ (fun _ ↦ E) (cylinderEventsIn E Δ) (fun _ ↦ 𝓔) (restrict E Δ)]
  intro x
  exact measurableCoordinateProjection E x.prop

end introduction

section superposition
variable {S : Type*}
variable (E : Type*) [𝓔 : MeasurableSpace E]
variable (Λ : Set S) [DecidablePred (· ∈ Λ)]
variable (η : S → E)

def superposition (ζ : Λ → E) (x : S) : E :=
  dite (x ∈ Λ) (fun h ↦ ζ ⟨x, h⟩) (fun _ ↦ η x)

lemma superposition_apply_of_mem (ζ : Λ → E) (x : S) (h : x ∈ Λ) : (superposition E Λ η ζ x = ζ ⟨x, h⟩) := by
  simp [superposition, h]

lemma superposition_apply_of_not_mem (ζ : Λ → E) (x : S) (h : x ∉ Λ) : (superposition E Λ η ζ x = η x) := by
  simp [superposition, h]

lemma superposition_is_measurable : Measurable (superposition E Λ) := by
  sorry

#check Measure.pi
#check Measure.map (superposition E Λ η)

end superposition



section ISSSD
variable {S : Type*}
variable (E : Type*) [𝓔 : MeasurableSpace E] (ν : Measure E) [IsProbabilityMeasure ν]
variable (Λ : Finset S) [DecidablePred (· ∈ (Λ : Set S))]
variable (η : S → E)

example : Fintype Λ := by
  infer_instance

#check Measure.pi (fun (_ : Λ) ↦ ν)
#check Measure.map (superposition E Λ η) (Measure.pi (fun (_ : Λ) ↦ ν))
#check @kernel (S → E) (S → E) (cylinderEventsIn E Λᶜ) _
#check @Measurable (S → E) (Measure (S → E)) (cylinderEventsIn E Λᶜ) _ (fun (η : S → E) ↦ Measure.map (superposition E Λ η) (Measure.pi (fun (_ : Λ) ↦ ν)))

lemma isssdProbabilityKernel_is_measurable : @Measurable (S → E) (Measure (S → E)) (cylinderEventsIn E Λᶜ) _ (fun (η : S → E) ↦ Measure.map (superposition E Λ η) (Measure.pi (fun (_ : Λ) ↦ ν))) := by
  sorry

noncomputable def isssdProbabilityKernel : @kernel (S → E) (S → E) (cylinderEventsIn E Λᶜ) _ where
  val := fun (η : S → E) ↦ Measure.map (superposition E Λ η) (Measure.pi (fun (_ : Λ) ↦ ν))
  property := by
    exact @isssdProbabilityKernel_is_measurable S E _ ν Λ _

class IsISSSD : Prop where
  indep : True
  marginal : True
  exterior : True


--def isssd (h : ):

end ISSSD
end GibbsMeasure

#check Subtype.restrict
