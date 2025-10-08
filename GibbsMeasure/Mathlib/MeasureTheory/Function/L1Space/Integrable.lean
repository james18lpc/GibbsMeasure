import Mathlib.MeasureTheory.Function.L1Space.Integrable

open EMetric ENNReal Filter MeasureTheory NNReal Set

variable {α β γ δ ε 𝕜 : Type*} {m : MeasurableSpace α} {μ ν : Measure α} [MeasurableSpace δ]
variable [NormedAddCommGroup β] [NormedAddCommGroup γ] [ENorm ε] {𝕜 : Type*} [NormedField 𝕜]
  [NormedSpace 𝕜 β] {f φ : α → 𝕜}

namespace MeasureTheory

@[simp] lemma Integrable.fun_mul_of_top_right (hf : Integrable f μ) (hφ : MemLp φ ∞ μ) :
    Integrable (fun x ↦ φ x * f x) μ := hf.smul_of_top_right hφ

@[simp] lemma Integrable.fun_mul_of_top_left (hφ : Integrable φ μ) (hf : MemLp f ∞ μ) :
    Integrable (fun x ↦ φ x * f x) μ :=
  hφ.smul_of_top_left hf

end MeasureTheory
