import Mathlib.MeasureTheory.Function.SimpleFunc
import GibbsMeasure.Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

namespace MeasureTheory.SimpleFunc
variable {α β : Type*} {mα : MeasurableSpace α} {mα₀ : MeasurableSpace α} (S : Set α)

scoped infixr:25 " →ₛ " => SimpleFunc
scoped notation:25 α:26 " →ₛ[" mα "] " β:25 => @SimpleFunc α mα β

lemma exists_forall_norm_indicator_le (h : α →ₛ[mα] ℝ) :
    ∃ Cg,∀x,‖S.indicator (⇑h) x‖ ≤ max Cg 0 := by
  have ⟨Cg, hCg⟩ := @h.exists_forall_norm_le α ℝ mα inferInstance
  refine ⟨Cg, fun x ↦ ?_⟩
  by_cases hxA : x ∈ S
  · simpa [hxA] using (hCg x).trans (le_max_left Cg 0)
  · simp [hxA]

lemma integrable_indicator {S : Set α} (h : α →ₛ[mα₀] ℝ) (hS: MeasurableSet[mα] S)
    (μ : @Measure α mα) (hmα : mα₀ ≤ mα) [IsFiniteMeasure μ] :
    Integrable (fun x ↦ S.indicator (⇑h) x) (μ) := by
  obtain ⟨Cf, hCf'⟩ := SimpleFunc.exists_forall_norm_indicator_le (mα := mα₀) S h
  refine ⟨(((h.stronglyMeasurable).mono hmα).indicator hS).aestronglyMeasurable (μ := μ), ?_⟩
  · exact hasFiniteIntegral_of_bounded (μ := μ)
     (f := fun x ↦ S.indicator (⇑h) x) (C := max Cf 0)
     (Filter.Eventually.of_forall hCf')

end MeasureTheory.SimpleFunc
