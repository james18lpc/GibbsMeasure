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

variable {m : MeasurableSpace α} {μ ν : Measure α}

lemma setLintegral_indicator (f : α → ℝ≥0∞) {s t : Set α} (hs : MeasurableSet s)
    (ht : MeasurableSet t) :
    ∫⁻ a in t, s.indicator f a ∂μ = ∫⁻ a in s ∩ t, f a ∂μ := by
  rw [← lintegral_indicator, ← lintegral_indicator, indicator_indicator, inter_comm] <;>
     measurability

end MeasureTheory.Lintegral
