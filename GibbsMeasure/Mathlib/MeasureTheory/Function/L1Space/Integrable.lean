import GibbsMeasure.Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Function.L1Space.Integrable

open EMetric ENNReal Filter MeasureTheory NNReal TopologicalSpace Set

variable {α β 𝕜 : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : Measure α}
variable [NormedField 𝕜] {f φ : α → 𝕜}

namespace MeasureTheory

@[simp] lemma Integrable.fun_mul_of_top_right (hf : Integrable f μ) (hφ : MemLp φ ∞ μ) :
    Integrable (fun x ↦ φ x * f x) μ := hf.smul_of_top_right hφ

@[simp] lemma Integrable.fun_mul_of_top_left (hφ : Integrable φ μ) (hf : MemLp f ∞ μ) :
    Integrable (fun x ↦ φ x * f x) μ :=
  hφ.smul_of_top_left hf

@[fun_prop]
lemma Integrable.measurable [TopologicalSpace β] [PseudoMetrizableSpace β] [ContinuousENorm β]
    [μ.IsComplete] {f : α → β} [BorelSpace β] (hf : Integrable f μ) : Measurable f :=
  hf.aemeasurable.measurable

end MeasureTheory
