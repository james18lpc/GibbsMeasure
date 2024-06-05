import Mathlib
open scoped ProbabilityTheory


namespace GibbsMeasure

variable {S : Type*}
variable (E : Type*) [𝓔 : MeasurableSpace E]

#check MeasureTheory.Measure.condKernel
#check ProbabilityTheory.kernel

#check Finset S

example : PartialOrder (Finset S) := by
  infer_instance

variable (Λ : Finset S)


#check MeasurableSpace.pi

#synth MeasurableSpace (S → E)

--variable (Δ : Set S)

#check ProbabilityTheory.kernel.comp


#check MeasurableSpace.comap


--def cylinderEventsOn [m : ∀ a, MeasurableSpace (π a)] : MeasurableSpace (∀ a, π a) :=
  --⨆ a, (m a).comap fun b => b a

#check ‹MeasurableSpace E›

def cylinderEventsOn (Δ : Set S) : MeasurableSpace (S → E) :=
  ⨆ x ∈ Δ, 𝓔.comap fun σ ↦ σ x

#check @ProbabilityTheory.kernel (S → E) (S → E) (cylinderEventsOn E Λᶜ) _
#check Π (Λ : Finset S), @ProbabilityTheory.kernel (S → E) (S → E) (cylinderEventsOn E Λᶜ) _
variable (γ : Π (Λ : Finset S), @ProbabilityTheory.kernel (S → E) (S → E) (cylinderEventsOn E Λᶜ) _)
variable (γ : Π (Λ : Finset S), @ProbabilityTheory.kernel (S → E) (S → E) (cylinderEventsOn E Λᶜ) _)
variable (Λ₁ Λ₂ : Finset S)

example (X Y : Type*) [𝓧 : MeasurableSpace X] (𝓨₁ 𝓨₂: MeasurableSpace Y) (h : 𝓨₁ ≤ 𝓨₂)
    (π : @ProbabilityTheory.kernel Y X 𝓨₁ _) :
    @ProbabilityTheory.kernel Y X 𝓨₂ _ :=
  ProbabilityTheory.kernel.comap π (fun x ↦ x) h

structure Specification where
  kernel : Π (Λ : Finset S), @ProbabilityTheory.kernel (S → E) (S → E) (cylinderEventsOn E Λᶜ) _
  consistent : sorry


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





lemma cylinderEventsOn_univ_eq :
    cylinderEventsOn E (Set.univ : Set S) = @MeasurableSpace.pi S (fun _ ↦ E) (fun _ ↦ 𝓔) := by
  rw [cylinderEventsOn, MeasurableSpace.pi]
  simp only [Set.mem_univ, iSup_pos]

lemma measurableCoordinateProjection {Δ : Set S} {x : S} (h : x ∈ Δ) :
    @Measurable (S → E) E (cylinderEventsOn E Δ) _ (fun σ ↦ σ x) := by
  have key : @Measurable (S → E) E (𝓔.comap fun σ ↦ σ x) _ (fun σ ↦ σ x) := by
    exact Measurable.of_comap_le fun s a ↦ a
  exact key.mono (le_iSup₂_of_le x h (fun s a ↦ a)) le_rfl

lemma cylinderEventsOn_mono {Δ₁ Δ₂ : Set S} (h : Δ₁ ⊆ Δ₂) : cylinderEventsOn E Δ₁ ≤ cylinderEventsOn E Δ₂ := by
  simp only [cylinderEventsOn, iSup_le_iff]
  exact fun i i_1 ↦ le_iSup₂_of_le i (h i_1) fun s a ↦ a

-- check rw [cylinderEventsOn_univ_eq]
lemma cylinderEventsOn_le (Δ : Set S) :
    cylinderEventsOn E Δ ≤ @MeasurableSpace.pi S (fun _ ↦ E) (fun _ ↦ 𝓔) := by
  apply le_trans (cylinderEventsOn_mono E (Set.subset_univ Δ))
  apply le_of_eq
  exact cylinderEventsOn_univ_eq E

#check cylinderEventsOn_le
#check (ProbabilityTheory.kernel.comap (γ Λ₁) (fun x ↦ x) (cylinderEventsOn_le _ _)) ∘ₖ (γ Λ₂)

def restrict (Δ : Set S) (σ : S → E) : Δ → E :=
  @Subtype.restrict S (fun _ ↦ E) Δ σ

lemma measurableRestrictEasy (Δ : Set S) : Measurable (restrict E Δ) := by

  sorry


lemma measurableRestrict (Δ : Set S) :
    @Measurable (S → E) (Δ → E) (cylinderEventsOn E Δ) MeasurableSpace.pi (restrict E Δ) := by
  --simp only [cylinderEventsOn, MeasurableSpace.pi]
  --have := @measurable_pi_iff (S → E) Δ (fun _ ↦ E) (cylinderEventsOn E Δ) (fun _ ↦ 𝓔) (restrict E Δ)
  rw [@measurable_pi_iff (S → E) Δ (fun _ ↦ E) (cylinderEventsOn E Δ) (fun _ ↦ 𝓔) (restrict E Δ)]
  intro x
  exact measurableCoordinateProjection E x.prop


end GibbsMeasure

#check Subtype.restrict
