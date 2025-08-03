import GibbsMeasure.Mathlib.Data.ENNReal.Basic
import GibbsMeasure.Mathlib.MeasureTheory.Function.SimpleFunc
import GibbsMeasure.Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import GibbsMeasure.Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import GibbsMeasure.Mathlib.MeasureTheory.Integral.Bochner.Basic
import GibbsMeasure.Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Kernel.Proper

/-!
# Proper kernels

We define the notion of properness for measure kernels and highlight important consequences.
-/

open MeasureTheory ENNReal NNReal Set
open scoped ProbabilityTheory

namespace ProbabilityTheory.Kernel
variable {X : Type*} {𝓑 𝓧 : MeasurableSpace X} {π : Kernel[𝓑, 𝓧] X X} {A B : Set X}
  {f g : X → ℝ} {x₀ : X}

private lemma IsProper.integral_indicator_mul_indicator (h𝓑𝓧 : 𝓑 ≤ 𝓧) (hπ : IsProper π)
    (hA : MeasurableSet[𝓧] A) (hB : MeasurableSet[𝓑] B) :
    ∫ x, (B.indicator 1 x * A.indicator 1 x : ℝ) ∂(π x₀) =
      B.indicator 1 x₀ * ∫ x, A.indicator 1 x ∂(π x₀) := by
  calc
        ∫ x, (B.indicator 1 x * A.indicator 1 x : ℝ) ∂(π x₀)
    _ = (∫⁻ x, .ofReal (B.indicator 1 x * A.indicator 1 x) ∂π x₀).toReal :=
      integral_eq_lintegral_of_nonneg_ae (.of_forall <| by simp [indicator_nonneg, mul_nonneg])
        (by measurability)
    _ = (∫⁻ x, B.indicator 1 x * A.indicator 1 x ∂π x₀).toReal := by
      simp [ofReal_mul, indicator_nonneg]
    _ = (B.indicator 1 x₀ * ∫⁻ x, A.indicator 1 x ∂π x₀).toReal := by
      rw [hπ.lintegral_mul h𝓑𝓧 (by measurability) (by measurability)]
    _ = B.indicator 1 x₀ * ∫ x, A.indicator 1 x ∂π x₀ := by
      rw [integral_eq_lilntegral_of_nonneg_ae (.of_forall <| by simp [indicator_nonneg])
        (by measurability)]
      simp [ofReal_mul]

open scoped SimpleFunc in
private lemma IsProper.integral_simpleFunc_mul_indicator (h𝓑𝓧 : 𝓑 ≤ 𝓧) (hπ : IsProper π)
    (hA : MeasurableSet[𝓧] A) (g : X →ₛ[𝓑] ℝ) :
    ∫ x, g x * A.indicator 1 x ∂(π x₀) = g x₀ * ∫ x, A.indicator 1 x ∂(π x₀) := sorry

variable [IsFiniteKernel π]

private lemma IsProper.integral_bdd_mul_indicator (h𝓑𝓧 : 𝓑 ≤ 𝓧) (hπ : IsProper π)
    (hA : MeasurableSet[𝓧] A) (hg : StronglyMeasurable[𝓑] g) (hgbdd : ∃ C, ∀ x, ‖g x‖ ≤ C)
    (x₀ : X) :
    ∫ x, g x * A.indicator 1 x ∂(π x₀) = g x₀ * ∫ x, A.indicator 1 x ∂(π x₀) := by
  obtain ⟨C, hC⟩ := hgbdd
  refine tendsto_nhds_unique ?_ <| (hg.tendsto_approxBounded_of_norm_le <| hC _).mul_const _
  simp_rw [← hπ.integral_simpleFunc_mul_indicator h𝓑𝓧 hA]
  refine tendsto_integral_of_dominated_convergence (fun _ ↦ C) (fun n ↦ ?_) (integrable_const _)
    (fun n ↦ .of_forall fun x ↦ ?_) <| .of_forall fun x ↦ ?_
  · exact (((hg.approxBounded C n).stronglyMeasurable.mono h𝓑𝓧).mul
      (by fun_prop (disch := assumption))).aestronglyMeasurable
  · simpa [-norm_mul] using
      norm_mul_le_of_le (hg.norm_approxBounded_le ((norm_nonneg _).trans <| hC x₀) _ _)
        (norm_indicator_le_norm_self 1 _)
  · exact .mul_const _ <| hg.tendsto_approxBounded_of_norm_le <| hC _

lemma IsProper.integral_bdd_mul (h𝓑𝓧 : 𝓑 ≤ 𝓧) (hπ : IsProper π)
    (hf : Integrable[𝓧] f (π x₀)) (hg : StronglyMeasurable[𝓑] g) (hgbdd : ∃ C, ∀ x, ‖g x‖ ≤ C) :
    ∫ x, g x * f x ∂(π x₀) = g x₀ * ∫ x, f x ∂(π x₀) := by
  induction f, hf using Integrable.induction' with
  | indicator c s hs _ =>
    simp [← smul_indicator_one_apply, mul_left_comm, integral_const_mul,
      hπ.integral_bdd_mul_indicator h𝓑𝓧 hs hg hgbdd]
  | add f₁ f₂ hf₁ hf₂ _ hgf₁ hgf₂ =>
    have : Integrable (fun x ↦ g x * f₁ x) (π x₀) :=
      hf₁.bdd_mul (hg.mono h𝓑𝓧).aestronglyMeasurable hgbdd
    have : Integrable (fun x ↦ g x * f₂ x) (π x₀) :=
      hf₂.bdd_mul (hg.mono h𝓑𝓧).aestronglyMeasurable hgbdd
    simp [mul_add, integral_add, *]
  | isClosed =>
    refine isClosed_eq ?_ <| by fun_prop
    sorry
  | ae_congr f₁ f₂ hf₁ hf hgf₁ =>
    simpa [integral_congr_ae <| .mul .rfl hf, integral_congr_ae hf] using hgf₁

end ProbabilityTheory.Kernel
