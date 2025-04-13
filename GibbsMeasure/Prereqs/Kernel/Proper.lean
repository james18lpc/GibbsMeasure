import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Probability.Kernel.Proper

/-!
# Proper kernels

We define the notion of properness for measure kernels and highlight important consequences.
-/

open MeasureTheory ENNReal NNReal Set
open scoped ProbabilityTheory

namespace ProbabilityTheory.Kernel
variable {X : Type*} {𝓑 𝓧 : MeasurableSpace X} {π : Kernel[𝓑, 𝓧] X X} {A B : Set X}
  {f g : X → ℝ≥0∞} {x₀ : X}

lemma IsProper.integral_indicator_mul_indicator (hπ : IsProper π) (h𝓑𝓧 : 𝓑 ≤ 𝓧)
 (hA : MeasurableSet[𝓧] A) (hB : MeasurableSet[𝓑] B) : (∫ x, (B.indicator 1 x * A.indicator 1 x) ∂(π x₀)
  = ((B.indicator 1 x₀) * (∫ x, A.indicator 1 x ∂(π x₀)) :ℝ))  := by
      rw [integral_eq_lintegral_of_nonneg_ae]
      conv_lhs =>
        rhs
        rhs
        intro a
        rw [←inter_indicator_mul (M₀:=ℝ) (s:=B) (t:=A) 1 1]
      simp
      have:∀a,ENNReal.ofReal ((B ∩ A).indicator (fun j ↦ 1) a) = (B ∩ A).indicator 1 a := by
       intro a
       by_cases h: a ∈ (B ∩ A) <;> simp [h] -- Couldn't figure out another way for it to recognise the two
      conv_lhs =>
        rhs
        rhs
        intro a
        rw [this a]
      have pmul := IsProper.lintegral_mul hπ h𝓑𝓧 (g:= fun x ↦ B.indicator 1 x) (f:= fun x ↦ A.indicator 1 x)
       (by apply Measurable.indicator <;> measurability ) (by
         apply Measurable.indicator;exact @measurable_one ℝ≥0∞ X (inferInstance) 𝓑  (inferInstance);exact hB) x₀
      have: (fun j:X ↦ (1:X →  ℝ≥0∞) j * (1:X →  ℝ≥0∞) j) = 1 := by ext j ; simp
      conv_lhs =>
       rhs
       rhs
       intro a
       rw [←this]
       rw [inter_indicator_mul (M₀:=ℝ≥0∞) (s:=B) (t:=A) 1 1 a]
      rw [pmul]
      rw [lintegral_indicator_one hA,integral_indicator_one hA]
      rw [ENNReal.toReal_mul]
      congr
      by_cases hxB: x₀ ∈ B
      · simp [hxB]
      · simp [hxB]
      · filter_upwards
        intro a
        by_cases h: a ∈ (B ∩ A) ; simp [h.1,h.2] ; simp; simp [indicator_nonneg,mul_nonneg]
      . measurability

lemma IsProper.integral_mul (hπ : IsProper π) (h𝓑𝓧 : 𝓑 ≤ 𝓧) (f g : X → ℝ) (x₀ : X)
    (hf : Integrable[𝓧] f (π x₀)) (hg : Integrable[𝓑] (f * g) (@Measure.map _ _ 𝓧 𝓑 id (π x₀))) :
    ∫ x, f x * g x ∂(π x₀) = g x₀ * ∫ x, f x ∂(π x₀) := by
  --Integrable.induction
  sorry

end ProbabilityTheory.Kernel
