import Mathlib

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

variable (Δ : Set S)

#check ProbabilityTheory.kernel.comp

#check MeasurableSpace.comap


--def cylinderEventsOn [m : ∀ a, MeasurableSpace (π a)] : MeasurableSpace (∀ a, π a) :=
  --⨆ a, (m a).comap fun b => b a

#check ‹MeasurableSpace E›

def cylinderEventsOn (Δ : Set S) : MeasurableSpace (S → E) :=
  ⨆ x ∈ Δ, 𝓔.comap fun σ ↦ σ x

--TODO: write lemma about the measurability of coordinate projections in Δ

lemma cylinderEventsOn_mono {Δ₁ Δ₂ : Set S} (h : Δ₁ ⊆ Δ₂) : cylinderEventsOn E Δ₁ ≤ cylinderEventsOn E Δ₂ := by
  simp only [cylinderEventsOn, iSup_le_iff]
  exact fun i i_1 ↦ le_iSup₂_of_le i (h i_1) fun s a ↦ a

lemma cylinderEventsOn_le (Δ : Set S) : cylinderEventsOn E Δ ≤ MeasurableSpace.pi := by
  sorry

def restrict (Δ : Set S) (σ : S → E) : Δ → E :=
  @Subtype.restrict S (fun _ ↦ E) Δ σ

lemma measurableRestrictEasy (Δ : Set S) : Measurable (restrict E Δ) := by

  sorry

#check @Measurable (S → E) (Δ → E) (cylinderEventsOn E Δ) MeasurableSpace.pi (restrict E Δ)

lemma measurableRestrict (Δ : Set S) :
    @Measurable (S → E) (Δ → E) (cylinderEventsOn E Δ) MeasurableSpace.pi (restrict E Δ) := by
  --simp only [cylinderEventsOn, MeasurableSpace.pi]
  have := @measurable_pi_iff (S → E) Δ (fun _ ↦ E) (cylinderEventsOn E Δ) (fun _ ↦ 𝓔) (restrict E Δ)
  rw [this]
  intro x
  simp [restrict]
  measurability
  sorry


end GibbsMeasure

#check Subtype.restrict
