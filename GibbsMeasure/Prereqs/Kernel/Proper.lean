import GibbsMeasure.Mathlib.Probability.Kernel.Basic

/-!
# Proper kernels

We define the notion of properness for measure kernels and highlight important consequences.
-/

open MeasureTheory ENNReal NNReal Set

namespace ProbabilityTheory.kernel
variable {S : Type*} (E : Type*) [𝓔 : MeasurableSpace E] (Δ : Set S) (Λ : Finset S)

variable {X : Type*} {𝓑 𝓧 : MeasurableSpace X} {π : kernel[𝓑, 𝓧] X X}{A B : Set X}  {x₀ : X}

/-- For two σ-algebras `𝓑 ≤ 𝓧` on a space `X`, a `𝓑, 𝓧`-kernel `π : X → Measure X` is proper if,
for all `B ∈ 𝓑`, `π` restricted to  is the same as `π` times the indicator of `B`.

To avoid assuming `𝓑 ≤ 𝓧` in the definition, we replace `𝓑` by `𝓑 ⊓ 𝓧` in the restriction. -/
def IsProper (π : kernel[𝓑, 𝓧] X X) : Prop :=
  ∀ ⦃B : Set X⦄ (hB : MeasurableSet[𝓑 ⊓ 𝓧] B) (x : X),
    kernel.restrict π (inf_le_right (b := 𝓧) _ hB) x = B.indicator (fun _ ↦ (1 : ℝ≥0∞)) x • π x

lemma isProper_iff_restrict_eq_indicator_smul (h𝓑𝓧 : 𝓑 ≤ 𝓧) :
    IsProper π ↔ ∀ ⦃B : Set X⦄ (hB : MeasurableSet[𝓑] B) (x : X),
      kernel.restrict π (h𝓑𝓧 _ hB) x = B.indicator (fun _ ↦ (1 : ℝ≥0∞)) x • π x := by
  simp_rw [IsProper, inf_eq_left.2 h𝓑𝓧]

lemma isProper_iff_restrict_eq_indicator_mul (h𝓑𝓧 : 𝓑 ≤ 𝓧) :
    IsProper π ↔
      ∀ ⦃A : Set X⦄ (_hA : MeasurableSet[𝓧] A) ⦃B : Set X⦄ (hB : MeasurableSet[𝓑] B)(x : X),
        kernel.restrict π (h𝓑𝓧 _ hB) x A = B.indicator (fun _ ↦ (1 : ℝ≥0∞)) x * π x A := by
  simp [isProper_iff_restrict_eq_indicator_smul h𝓑𝓧, Measure.ext_iff]; aesop

alias ⟨IsProper.restrict_eq_indicator_smul, IsProper.of_restrict_eq_indicator_smul⟩ :=
  isProper_iff_restrict_eq_indicator_smul

alias ⟨IsProper.restrict_eq_indicator_mul, IsProper.of_restrict_eq_indicator_mul⟩ :=
  isProper_iff_restrict_eq_indicator_mul

lemma IsProper.lintegral_indicator_mul_indicator (hπ : IsProper π) (h𝓑𝓧 : 𝓑 ≤ 𝓧)
    (hA : MeasurableSet[𝓧] A) (hB : MeasurableSet[𝓑] B) :
    ∫⁻ x, B.indicator (fun _ ↦ (1 : ℝ≥0∞)) x * A.indicator (fun _ ↦ (1 : ℝ≥0∞)) x ∂(π x₀) =
      B.indicator (fun _↦ (1 : ℝ≥0∞)) x₀ * ∫⁻ x, A.indicator (fun _ ↦ (1 : ℝ≥0∞)) x ∂(π x₀) := by
  simp_rw [← inter_indicator_mul]
  rw [lintegral_indicator, lintegral_indicator]
  · simp only [MeasureTheory.lintegral_const, MeasurableSet.univ, Measure.restrict_apply,
      univ_inter, one_mul]
    rw [← hπ.restrict_eq_indicator_mul h𝓑𝓧 hA hB, inter_comm]
    exact (kernel.restrict_apply' π (h𝓑𝓧 B hB) x₀ hA).symm
  · exact hA
  · sorry

lemma IsProper.lintegral_simple_mul_indicator (hπ : IsProper π)
    (f : SimpleFunc X ℝ≥0) {B : Set X} (hB : MeasurableSet[𝓑] B) :
    ∫⁻ x, f x * B.indicator (fun _ ↦ (1 : ℝ≥0∞)) x ∂(π x₀)
        = B.indicator (fun _↦ (1 : ℝ≥0∞)) x₀ * ∫⁻ x, f x ∂(π x₀) := by
  sorry

lemma IsProper.lintegral_mul_indicator (hπ : IsProper π)
    {f : X → ℝ≥0∞} (hf : @Measurable _ _ 𝓧 _ f) {B : Set X} (hB : MeasurableSet[𝓑] B) :
    ∫⁻ x, f x * B.indicator (fun _ ↦ (1 : ℝ≥0∞)) x ∂(π x₀)
        = B.indicator (fun _↦ (1 : ℝ≥0∞)) x₀ * ∫⁻ x, f x ∂(π x₀) := by
  rw [@MeasureTheory.lintegral_eq_nnreal X 𝓧 f (π x₀)]
  sorry

lemma IsProper.lintegral_mul (hπ : IsProper π) {f g : X → ℝ≥0∞}
    (hf : @Measurable _ _ 𝓧 _ f) (hg : @Measurable _ _ 𝓑 _ g) (x₀ : X) :
    ∫⁻ x, f x * g x ∂(π x₀) = g x₀ * ∫⁻ x, f x ∂(π x₀) := by
  rw [@lintegral_eq_nnreal X 𝓧 f (π x₀), @lintegral_eq_nnreal X 𝓧 (fun x ↦ f x * g x) (π x₀)]
  sorry

lemma IsProper.integral_mul (hπ : IsProper π) (f g : X → ℝ) (x₀ : X)
    (hf : @Integrable _ _ _ 𝓧 f (π x₀))
    (hg : @Integrable _ _ _ 𝓑 (f * g) (@Measure.map _ _ 𝓑 𝓧 id (π x₀))) :
    ∫ x, f x * g x ∂(π x₀) = g x₀ * ∫ x, f x ∂(π x₀) := by
  --Integrable.induction
  sorry

end ProbabilityTheory.kernel
