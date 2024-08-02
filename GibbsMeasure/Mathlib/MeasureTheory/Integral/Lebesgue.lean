import Mathlib.MeasureTheory.Integral.Lebesgue

assert_not_exists NormedSpace

noncomputable section

open Set hiding restrict restrict_apply

open Filter ENNReal

open Function (support)

open scoped Classical
open Topology NNReal ENNReal MeasureTheory

namespace MeasureTheory

local infixr:25 " →ₛ " => SimpleFunc

variable {α β γ δ : Type*}

section Lintegral

open SimpleFunc

variable {m : MeasurableSpace α} {μ ν : Measure α} {f : α → ℝ≥0∞} {s t : Set α}

lemma setLintegral_indicator (f : α → ℝ≥0∞) {s t : Set α} (hs : MeasurableSet s) :
    ∫⁻ a in t, s.indicator f a ∂μ = ∫⁻ a in s ∩ t, f a ∂μ := by
  rw [lintegral_indicator _ hs, Measure.restrict_restrict hs]

lemma setLintegral_indicator₀ (f : α → ℝ≥0∞) {s t : Set α}
    (hs : NullMeasurableSet s (μ.restrict t)) :
    ∫⁻ a in t, s.indicator f a ∂μ = ∫⁻ a in s ∩ t, f a ∂μ := by
  rw [lintegral_indicator₀ _ hs, Measure.restrict_restrict₀ hs]

lemma setLintegral_le_meas (hs : MeasurableSet s) (hf : ∀ a ∈ s, f a ≤ 1)
    (hf' : ∀ a ∈ s \ t, f a = 0) : ∫⁻ a in s, f a ∂μ ≤ μ t := by
  rw [← lintegral_indicator _ hs]
  exact lintegral_le_meas (fun a ↦ by by_cases a ∈ s <;> simp [*]) (by aesop)

end MeasureTheory.Lintegral
