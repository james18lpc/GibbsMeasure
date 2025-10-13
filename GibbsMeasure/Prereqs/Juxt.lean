import Mathlib.MeasureTheory.Constructions.Cylinders

open MeasureTheory

section juxt
variable {S E : Type*} {𝓔 : MeasurableSpace E} {Λ : Set S} {η : S → E} {x : S}

noncomputable def juxt (Λ : Set S) (η : S → E) (ζ : Λ → E) (x : S) : E := by
  classical exact dite (x ∈ Λ) (fun h ↦ ζ ⟨x, h⟩) (fun _ ↦ η x)

lemma juxt_apply_of_mem (hx : x ∈ Λ) (ζ : Λ → E) : juxt Λ η ζ x = ζ ⟨x, hx⟩ := by simp [juxt, hx]
lemma juxt_apply_of_not_mem (h : x ∉ Λ) (ζ : Λ → E) : juxt Λ η ζ x = η x := by simp [juxt, h]

lemma measurable_coordinate_projection_2 {Δ : Set S} {x : S} (h : x ∈ Δ) :
    Measurable[cylinderEvents Δ] (fun σ : S → E ↦ σ x) := by
  have key : @Measurable (S → E) E (𝓔.comap fun σ ↦ σ x) _ (fun σ ↦ σ x) := by
    exact Measurable.of_comap_le fun s a ↦ a
  exact key.mono (le_iSup₂_of_le x h (fun s a ↦ a)) le_rfl

lemma Measurable.juxt : Measurable (juxt Λ η) := by
  classical
  letI : MeasurableSpace E := 𝓔
  refine (measurable_pi_iff).2 (fun x => ?_)
  by_cases hx : x ∈ Λ
  · have hix : Measurable (fun ζ : Λ → E => ζ ⟨x, hx⟩) :=
      measurable_pi_apply (⟨x, hx⟩ : Λ)
    convert hix using 1
    ext ζ
    exact juxt_apply_of_mem hx ζ
  · have : Measurable (fun _ : Λ → E => η x) := measurable_const
    convert this using 1
    ext ζ
    exact juxt_apply_of_not_mem hx ζ

end juxt
