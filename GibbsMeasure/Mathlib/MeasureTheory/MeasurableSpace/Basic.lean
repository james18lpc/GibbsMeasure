import Mathlib.MeasureTheory.MeasurableSpace.Basic

lemma iSup_measurable_of_measurable (X Y I : Type*) (sigmaAlgebras : I → MeasurableSpace X) (i₀ : I)
    (f : X → Y) [MeasurableSpace Y]
    (h : @Measurable X Y (sigmaAlgebras i₀) _ f) :
    @Measurable X Y (⨆ i, sigmaAlgebras i) _ f :=
  h.mono (le_iSup sigmaAlgebras i₀) le_rfl

lemma sup_measurable_of_measurable (X Y : Type*) (𝓢₁ 𝓢₂ : MeasurableSpace X) (f : X → Y)
    [MeasurableSpace Y] (h : @Measurable X Y 𝓢₁ _ f) :
    @Measurable X Y (𝓢₁ ⊔ 𝓢₂) _ f :=
  h.mono (SemilatticeSup.le_sup_left 𝓢₁ 𝓢₂) le_rfl
