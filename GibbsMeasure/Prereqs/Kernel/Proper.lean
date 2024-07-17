import GibbsMeasure.Prereqs.CylinderEvent
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Kernel.Composition

/-!
# Proper kernels

We define the notion of properness for measure kernels and highlight important consequences.
-/

open MeasureTheory ENNReal NNReal Set

namespace ProbabilityTheory.kernel
variable {S : Type*} (E : Type*) [𝓔 : MeasurableSpace E] (Δ : Set S) (Λ : Finset S)

variable {X : Type*} {𝓑 𝓧 : MeasurableSpace X} (hSub : 𝓑 ≤ 𝓧) (π : @kernel X X 𝓑 𝓧) {x₀ : X}

def IsProper : Prop :=
  ∀ (B : Set X) (B_mble : MeasurableSet[𝓑] B),
    kernel.restrict π (hSub B B_mble) = (fun x ↦ B.indicator (fun _ ↦ (1 : ℝ≥0∞)) x • π x)

lemma IsProper.def (hProper : kernel.IsProper hSub π)
    {A B : Set X} (A_mble : MeasurableSet[𝓧] A) (B_mble : @MeasurableSet X 𝓑 B) (x : X):
    kernel.restrict π (hSub B B_mble) x A = B.indicator (fun _ ↦ (1 : ℝ≥0∞)) x * π x A := by
  sorry

lemma IsProper.lintegral_indicator_mul_indicator (hProper : kernel.IsProper hSub π)
    {A B : Set X} (A_mble : MeasurableSet[𝓧] A) (B_mble : @MeasurableSet X 𝓑 B) :
    ∫⁻ x, B.indicator (fun _ ↦ (1 : ℝ≥0∞)) x * A.indicator (fun _ ↦ (1 : ℝ≥0∞)) x ∂(π x₀) =
      B.indicator (fun _↦ (1 : ℝ≥0∞)) x₀ * ∫⁻ x, A.indicator (fun _ ↦ (1 : ℝ≥0∞)) x ∂(π x₀) := by
  simp_rw [← inter_indicator_mul]
  rw [lintegral_indicator, lintegral_indicator]
  · simp only [MeasureTheory.lintegral_const, MeasurableSet.univ, Measure.restrict_apply,
      univ_inter, one_mul]
    rw [← IsProper.def hSub π hProper A_mble B_mble, inter_comm]
    exact (kernel.restrict_apply' π (hSub B B_mble) x₀ A_mble).symm
  · exact A_mble
  · sorry


lemma IsProper.lintegral_simple_mul_indicator (hProper : kernel.IsProper hSub π)
    (f : SimpleFunc X ℝ≥0) {B : Set X} (B_mble : @MeasurableSet X 𝓑 B) :
    ∫⁻ x, f x * B.indicator (fun _ ↦ (1 : ℝ≥0∞)) x ∂(π x₀)
        = B.indicator (fun _↦ (1 : ℝ≥0∞)) x₀ * ∫⁻ x, f x ∂(π x₀) := by
  sorry

lemma IsProper.lintegral_mul_indicator (hProper : kernel.IsProper hSub π)
    {f : X → ℝ≥0∞} (hf : @Measurable _ _ 𝓧 _ f) {B : Set X} (B_mble : @MeasurableSet X 𝓑 B) :
    ∫⁻ x, f x * B.indicator (fun _ ↦ (1 : ℝ≥0∞)) x ∂(π x₀)
        = B.indicator (fun _↦ (1 : ℝ≥0∞)) x₀ * ∫⁻ x, f x ∂(π x₀) := by
  rw [@MeasureTheory.lintegral_eq_nnreal X 𝓧 f (π x₀)]
  sorry


lemma IsProper.lintegral_mul (hProper : kernel.IsProper hSub π) {f g : X → ℝ≥0∞}
    (hf : @Measurable _ _ 𝓧 _ f) (hg : @Measurable _ _ 𝓑 _ g) (x₀ : X) :
    ∫⁻ x, f x * g x ∂(π x₀) = g x₀ * ∫⁻ x, f x ∂(π x₀) := by
  rw [@lintegral_eq_nnreal X 𝓧 f (π x₀), @lintegral_eq_nnreal X 𝓧 (fun x ↦ f x * g x) (π x₀)]
  sorry

lemma IsProper.integral_mul (hProper : kernel.IsProper hSub π) (f g : X → ℝ) (x₀ : X)
    (hf : @Integrable _ _ _ 𝓧 f (π x₀))
    (hg : @Integrable _ _ _ 𝓑 (f * g) (@Measure.map _ _ 𝓑 𝓧 id (π x₀))) :
    ∫ x, f x * g x ∂(π x₀) = g x₀ * ∫ x, f x ∂(π x₀) := by
  --Integrable.induction
  sorry

end ProbabilityTheory.kernel
