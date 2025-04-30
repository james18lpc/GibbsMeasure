import GibbsMeasure.Mathlib.Data.ENNReal.Basic
import GibbsMeasure.Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Integral.SetIntegral
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

private lemma IsProper.integral_indicator_mul_indicator (hπ : IsProper π) (h𝓑𝓧 : 𝓑 ≤ 𝓧)
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
      rw [integral_eq_lintegral_of_nonneg_ae (.of_forall <| by simp [indicator_nonneg, mul_nonneg])
        (by measurability)]
      simp [ofReal_mul]


lemma indicator_eq_mul_one (f: X → ℝ) (B: Set X): B.indicator f = (B.indicator 1)*f := by
  ext x
  by_cases hxiB:x ∈ B <;> simp [hxiB]

lemma integral_indicator_of_mul_indicator (f: X → ℝ) (B: Set X) {μ : Measure X} :
  ∫ (x : X), (B.indicator 1 x) * f x ∂μ = ∫ (x : X), (B.indicator (1 * f)) x ∂μ := by
   simp
   rw [indicator_eq_mul_one f B]
   rfl


variable {f : X → ℝ}
private lemma IsProper.integral_indicator_mul (hπ : IsProper π) (h𝓑𝓧 : 𝓑 ≤ 𝓧)
    (hf : Integrable[𝓧] f (π x₀)) (hB : MeasurableSet[𝓑] B):
      ∫ x, (B.indicator 1 x) *  (f x)  ∂(π x₀) = 
        (B.indicator 1 x₀) * (∫ x, (f x) ∂(π x₀)) := by
        apply Integrable.induction (μ:=(π x₀)) (fun (h:X→ℝ) ↦ Integrable[𝓧] h (π x₀) →
         ∫ x, (B.indicator 1 x) * (h x) ∂(π x₀) = B.indicator 1 x₀ * ∫ x, h x ∂(π x₀))
        · intro c S hmS bpS _
          rw [integral_indicator_const (μ:= (π x₀)) c (hmS)]
          simp_rw [← smul_indicator_one_apply,  smul_eq_mul, ←mul_assoc]
          simp only [mul_comm,mul_assoc]
          rw [integral_mul_left,integral_indicator_mul_indicator hπ h𝓑𝓧 hmS hB,←mul_assoc]
          rw [integral_indicator_one (μ:= (π x₀)) (hmS)]
          ring
        · intro f g disj intf intg
          simp_all
          intro hp1 hp2
          conv_lhs =>
           rhs
           intro x
           rw [mul_add]
          have disj':  Disjoint (Function.support ((B.indicator 1)*f))
           (Function.support ((B.indicator 1)*g)) := by
            simp
            refine (Disjoint.inter_left' B ?_)
            refine (Disjoint.inter_right' B ?_)
            exact disj
          have intBf: Integrable (μ := (π x₀))  (((B.indicator 1)*f) : X → ℝ ) := by
           have t1 := Integrable.indicator intf (h𝓑𝓧 B hB)
           have t2:B.indicator f = (B.indicator 1)*f := by
            ext x
            by_cases hxiB:x ∈ B
            · simp [hxiB]
            · simp [hxiB]
           rw [t2] at t1
           exact t1
          have intBg: Integrable (μ := (π x₀))  (((B.indicator 1)*g) : X → ℝ ) := by
            have t1 := Integrable.indicator intg (h𝓑𝓧 B hB)
            rw [indicator_eq_mul_one g B] at t1
            exact t1
          rw [integral_add intf intg]
          have fun_add: ∀x, (B.indicator 1 x * f x + B.indicator 1 x * g x
           = (((B.indicator 1)*f):X → ℝ) x + (((B.indicator 1)*g):X → ℝ) x ) := by
            intro x
            simp
          simp [fun_add]
          simp_rw [integral_add intBf intBg]
          simp
          rw [hp1,hp2]
          ring
        · conv =>
           rhs
           rhs
           intro f intf
           rw [←norm_sub_eq_zero_iff]
          simp [L1.integrable_coeFn]
          refine IsClosed.preimage (f := fun g:↥(Lp ℝ 1 (π x₀)) ↦ ∫ (x : X), B.indicator 1 x * g x
           ∂π x₀ - B.indicator 1 x₀ * ∫ (x : X), g x ∂π x₀ ) ?_ (t := {0}) ?_
          · refine Continuous.sub ?_ ?_
            · simp only [integral_indicator_of_mul_indicator]
              simp [integral_indicator (h𝓑𝓧 B hB)]
              refine MeasureTheory.continuous_setIntegral (E:=ℝ) B
            · apply Continuous.comp'
              · apply continuous_mul_left
              · simp only [←L1.integral_eq_integral]
                refine L1.continuous_integral
          · exact isClosed_singleton
        · intro k g hfAEg Intf hfIND
          have t1 := hfIND Intf
          intro intG
          rw [←integral_congr_ae hfAEg]
          have :  B.indicator (1 * g) =ᶠ[ae (π x₀)] (B.indicator 1) *k := by
           simp
           rw [←indicator_eq_mul_one k B]
           exact Filter.EventuallyEq.indicator (id (Filter.EventuallyEq.symm hfAEg))
          rw [integral_indicator_of_mul_indicator g B,←integral_congr_ae this.symm]
          exact t1
        · exact hf
        · exact hf



lemma IsProper.integral_mul (hπ : IsProper π) (h𝓑𝓧 : 𝓑 ≤ 𝓧) (f g : X → ℝ) (x₀ : X)
    (hf : Integrable[𝓧] f (π x₀)) (hg : Integrable[𝓑] (f * g) (@Measure.map _ _ 𝓧 𝓑 id (π x₀))) :
    ∫ x, f x * g x ∂(π x₀) = g x₀ * ∫ x, f x ∂(π x₀) := by
  --Integrable.induction
  sorry

end ProbabilityTheory.Kernel
