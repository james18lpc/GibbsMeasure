import GibbsMeasure.Prereqs.CylinderEvent

open MeasureTheory

section juxt
variable {S : Type*}
variable (E : Type*) [𝓔 : MeasurableSpace E]
variable (Λ : Set S) (η : S → E)

noncomputable def juxt (ζ : Λ → E) (x : S) : E := by
  classical exact dite (x ∈ Λ) (fun h ↦ ζ ⟨x, h⟩) (fun _ ↦ η x)

lemma juxt_apply_of_mem (ζ : Λ → E) (x : S) (h : x ∈ Λ) :
    juxt E Λ η ζ x = ζ ⟨x, h⟩ := by simp [juxt, h]

lemma juxt_apply_of_not_mem (ζ : Λ → E) (x : S) (h : x ∉ Λ) :
    juxt E Λ η ζ x = η x := by simp [juxt, h]

lemma measurable_coordinate_projection_2 {Δ : Set S} {x : S} (h : x ∈ Δ) :
    Measurable[cylinderEvents Δ] (fun σ : S → E ↦ σ x) := by
  have key : @Measurable (S → E) E (𝓔.comap fun σ ↦ σ x) _ (fun σ ↦ σ x) := by
    exact Measurable.of_comap_le fun s a ↦ a
  exact key.mono (le_iSup₂_of_le x h (fun s a ↦ a)) le_rfl

lemma Measurable.juxt : Measurable (juxt E Λ) := by
  rw [measurable_pi_iff]
  --simp [juxt]
  --intro x

  --exact?
  --exact measurable_pi_apply _
  sorry

end juxt
