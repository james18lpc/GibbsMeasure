import GibbsMeasure.Prereqs.CylinderEvent

open MeasureTheory

section extend
variable {S : Type*}
variable (E : Type*) [𝓔 : MeasurableSpace E]
variable (Λ : Set S) [DecidablePred (· ∈ Λ)]
variable (η : S → E)

def extend (ζ : Λ → E) (x : S) : E := dite (x ∈ Λ) (fun h ↦ ζ ⟨x, h⟩) (fun _ ↦ η x)

lemma extend_apply_of_mem (ζ : Λ → E) (x : S) (h : x ∈ Λ) :
    extend E Λ η ζ x = ζ ⟨x, h⟩ := by simp [extend, h]

lemma extend_apply_of_not_mem (ζ : Λ → E) (x : S) (h : x ∉ Λ) :
    extend E Λ η ζ x = η x := by simp [extend, h]

lemma measurable_coordinate_projection_2 {Δ : Set S} {x : S} (h : x ∈ Δ) :
    @Measurable (S → E) E (cylinderEvents Δ) _ (fun σ ↦ σ x) := by
  have key : @Measurable (S → E) E (𝓔.comap fun σ ↦ σ x) _ (fun σ ↦ σ x) := by
    exact Measurable.of_comap_le fun s a ↦ a
  exact key.mono (le_iSup₂_of_le x h (fun s a ↦ a)) le_rfl

lemma extend_is_measurable : Measurable (extend E Λ) := by
  rw [measurable_pi_iff]
  --simp [extend]
  --intro x

  --exact?
  --exact measurable_pi_apply _
  sorry

end extend
