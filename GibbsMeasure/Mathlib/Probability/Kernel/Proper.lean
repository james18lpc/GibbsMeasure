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
    _ = (∫⁻ x, B.indicator 1 x * A.indicator 1 x ∂π x₀).toReal := by simp [indicator_nonneg]
    _ = (B.indicator 1 x₀ * ∫⁻ x, A.indicator 1 x ∂π x₀).toReal := by
      rw [hπ.lintegral_mul h𝓑𝓧 (by measurability) (by measurability)]
    _ = B.indicator 1 x₀ * ∫ x, A.indicator 1 x ∂π x₀ := by
      rw [integral_eq_lintegral_of_nonneg_ae (.of_forall <| by simp [indicator_nonneg])
        (by measurability)]
      simp

variable [IsFiniteKernel π]

open SimpleFunc in
private lemma IsProper.integral_simpleFunc_mul_indicator (h𝓑𝓧 : 𝓑 ≤ 𝓧) (hπ : IsProper π)
    (hA : MeasurableSet[𝓧] A) (g : X →ₛ[𝓑] ℝ) :
    ∫ x, g x * A.indicator 1 x ∂(π x₀) = g x₀ * ∫ x, A.indicator 1 x ∂(π x₀) := by
  have hmul_to_indicator :
      (fun x ↦ g x * A.indicator 1 x) = (fun x ↦ A.indicator g x) := by
    ext x; by_cases hxA : x ∈ A <;> simp [hxA]
  rw [hmul_to_indicator]
  refine @SimpleFunc.induction X ℝ 𝓑 inferInstance
      (fun g ↦ ∫ x, A.indicator g x ∂π x₀ = g x₀ * ∫ x, A.indicator 1 x ∂π x₀)
      (fun c S hS ↦ ?_)
      (fun f g disj hf hg ↦ ?_) g
  · calc
      ∫ x, A.indicator (S.indicator (fun _ ↦ c)) x ∂π x₀
        = c * ∫ x, S.indicator 1 x * A.indicator 1 x ∂π x₀ := by
        rw [← integral_const_mul]
        congr! with _ x
        by_cases hxA : x ∈ A <;> by_cases hxS : x ∈ S <;> simp [hxA, hxS]
      _ = c * (S.indicator 1 x₀ * ∫ x, A.indicator 1 x ∂π x₀) := by
        simp [hπ.integral_indicator_mul_indicator h𝓑𝓧 hA hS]
      _ = S.indicator (fun _ ↦ c) x₀ * ∫ x, A.indicator 1 x ∂π x₀ := by
        by_cases hxS : x₀ ∈ S <;> simp [hxS]
  · simp only [SimpleFunc.coe_add, indicator_add', Pi.add_apply, add_mul, ← hf, ← hg]
    apply MeasureTheory.integral_add <;> exact .indicator (integrable_of_isFiniteMeasure' h𝓑𝓧 _) hA

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

lemma IsProper.integral_bdd_mul (h𝓑𝓧 : 𝓑 ≤ 𝓧) (hπ : IsProper π) (hf : Integrable[𝓧] f (π x₀))
    (hg : StronglyMeasurable[𝓑] g) (hgbdd : ∃ C > 0, ∀ x, ‖g x‖ ≤ C) :
    ∫ x, g x * f x ∂(π x₀) = g x₀ * ∫ x, f x ∂(π x₀) := by
  obtain ⟨C, hpC, hC⟩ := hgbdd
  induction f, hf using Integrable.induction' with
  | indicator c s hs _ =>
    simp [← smul_indicator_one_apply, mul_left_comm, integral_const_mul,
      hπ.integral_bdd_mul_indicator h𝓑𝓧 hs hg ⟨C, hC⟩]
  | add f₁ f₂ hf₁ hf₂ _ hgf₁ hgf₂ =>
    have : Integrable (fun x ↦ g x * f₁ x) (π x₀) :=
      hf₁.bdd_mul (hg.mono h𝓑𝓧).aestronglyMeasurable ⟨C, hC⟩
    have : Integrable (fun x ↦ g x * f₂ x) (π x₀) :=
      hf₂.bdd_mul (hg.mono h𝓑𝓧).aestronglyMeasurable ⟨C, hC⟩
    simp [mul_add, integral_add, *]
  | isClosed =>
    refine isClosed_eq ?_ <| by fun_prop
    refine Metric.continuous_iff.mpr fun f2 ε hε ↦ ⟨ε / C, div_pos hε hpC, fun a ha ↦ ?_⟩
    have hInt1 : Integrable (fun x ↦ g x * a x) (π x₀) :=
      (L1.integrable_coeFn a).bdd_mul (hg.mono h𝓑𝓧).aestronglyMeasurable ⟨C, hC⟩
    have hInt2 : Integrable (fun x ↦ g x * f2 x) (π x₀) :=
      (L1.integrable_coeFn f2).bdd_mul (hg.mono h𝓑𝓧).aestronglyMeasurable ⟨C, hC⟩
    have hsub :
        ‖∫ x, g x * a x ∂π x₀ - ∫ x, g x * f2 x ∂π x₀‖ = ‖∫ x, g x * a x - g x * f2 x ∂π x₀‖ := by
      simp [integral_sub hInt1 hInt2]
    have hdiff_ae : (fun x ↦ g x * a x - g x * f2 x) =ᵐ[π x₀] (fun x ↦ g x * (a - f2) x) := by
      filter_upwards [Lp.coeFn_sub a f2] with x hx
      have hmul : g x * (a - f2) x = g x * (a x - f2 x) := by
        simpa [hx] using congrArg (fun t ↦ g x * t) hx
      calc
        g x * a x - g x * f2 x
            = g x * (a x - f2 x) := by simp [mul_sub]
        _ = g x * (a - f2) x := by simp [hmul.symm]
    have hIntDiff : Integrable (fun x ↦ g x * (a - f2) x) (π x₀) :=
      (L1.integrable_coeFn (a - f2)).bdd_mul ((hg.mono h𝓑𝓧).aestronglyMeasurable) ⟨C, hC⟩
    have hdInt : Integrable (fun x ↦ C * ‖(a - f2) x‖) (π x₀) :=
      ((L1.integrable_coeFn (a - f2)).norm.smul C)
    have hle_ae : (fun x ↦ ‖g x * (a - f2) x‖) ≤ᵐ[π x₀] (fun x ↦ C * ‖(a - f2) x‖) :=
      .of_forall fun x ↦ by simpa using mul_le_mul_of_nonneg_right (hC x) (norm_nonneg ((a - f2) x))
    have hle_int : ‖∫ x, g x * (a - f2) x ∂π x₀‖ ≤ C * ‖a - f2‖ := by
      calc
        ‖∫ x, g x * (a - f2) x ∂π x₀‖
            ≤ ∫ x, ‖g x * (a - f2) x‖ ∂π x₀ := norm_integral_le_integral_norm _
        _ ≤ ∫ x, C * ‖(a - f2) x‖ ∂π x₀ := integral_mono_ae hIntDiff.norm hdInt hle_ae
        _ = C * ∫ x, ‖(a - f2) x‖ ∂π x₀ := by simp [integral_const_mul]
        _ = C * ‖a - f2‖ := by rw [(L1.norm_eq_integral_norm (a - f2) (μ := π x₀)).symm]
    have hle : ‖∫ x, g x * a x ∂π x₀ - ∫ x, g x * f2 x ∂π x₀‖ ≤ C * ‖a - f2‖ := by
      have hdiffint : ‖∫ x, g x * a x ∂π x₀ - ∫ x, g x * f2 x ∂π x₀‖
           = ‖∫ x, g x * (a - f2) x ∂π x₀‖ := by
        simpa [integral_congr_ae hdiff_ae,integral_sub hInt1 hInt2] using hsub
      simpa [hdiffint] using hle_int
    have hlt : C * ‖a - f2‖ < ε := by
      have hdist : ‖a - f2‖ < ε / C := by simpa [dist_eq_norm] using ha
      simpa [mul_div,mul_div_cancel_left₀ ε (ne_of_gt hpC)] using (mul_lt_mul_of_pos_left hdist hpC)
    exact lt_of_le_of_lt hle hlt
  | ae_congr f₁ f₂ hf₁ hf hgf₁ =>
    have : (fun x ↦ g x * f₁ x) =ᵐ[π x₀] (fun x ↦ g x * f₂ x) := by
      filter_upwards [hf] with x hx; simp [hx]
    simpa [integral_congr_ae this, integral_congr_ae hf] using hgf₁

end ProbabilityTheory.Kernel
