import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Probability.Kernel.Basic
import GibbsMeasure.Mathlib.MeasureTheory.Function.SimpleFunc
import GibbsMeasure.Mathlib.MeasureTheory.Integral.Lebesgue

/-!
# Proper kernels

We define the notion of properness for measure kernels and highlight important consequences.
-/

open MeasureTheory ENNReal NNReal Set
open scoped ProbabilityTheory

namespace ProbabilityTheory.Kernel
variable {X : Type*} {𝓑 𝓧 : MeasurableSpace X} {π : Kernel[𝓑, 𝓧] X X} {A B : Set X}
  {f g : X → ℝ≥0∞} {x₀ : X}

/-- For two σ-algebras `𝓑 ≤ 𝓧` on a space `X`, a `𝓑, 𝓧`-kernel `π : X → Measure X` is proper if,
for all `B ∈ 𝓑`, `π` restricted to is the same as `π` times the indicator of `B`.

To avoid assuming `𝓑 ≤ 𝓧` in the definition, we replace `𝓑` by `𝓑 ⊓ 𝓧` in the restriction. -/
structure IsProper (π : Kernel[𝓑, 𝓧] X X) : Prop :=
  restrict_eq_indicator_smul' :
    ∀ ⦃B : Set X⦄ (hB : MeasurableSet[𝓑 ⊓ 𝓧] B) (x : X),
      π.restrict (inf_le_right (b := 𝓧) _ hB) x = B.indicator (fun _ ↦ (1 : ℝ≥0∞)) x • π x

lemma isProper_iff_restrict_eq_indicator_smul (h𝓑𝓧 : 𝓑 ≤ 𝓧) :
    IsProper π ↔ ∀ ⦃B : Set X⦄ (hB : MeasurableSet[𝓑] B) (x : X),
      π.restrict (h𝓑𝓧 _ hB) x = B.indicator (fun _ ↦ (1 : ℝ≥0∞)) x • π x := by
  refine ⟨fun ⟨h⟩ ↦ ?_, fun h ↦ ⟨?_⟩⟩ <;> simpa only [inf_eq_left.2 h𝓑𝓧] using h

lemma isProper_iff_inter_eq_indicator_mul (h𝓑𝓧 : 𝓑 ≤ 𝓧) :
    IsProper π ↔
      ∀ ⦃A : Set X⦄ (_hA : MeasurableSet[𝓧] A) ⦃B : Set X⦄ (_hB : MeasurableSet[𝓑] B) (x : X),
        π x (A ∩ B) = B.indicator 1 x * π x A := by
  calc
    _ ↔ ∀ ⦃A : Set X⦄ (_hA : MeasurableSet[𝓧] A) ⦃B : Set X⦄ (hB : MeasurableSet[𝓑] B) (x : X),
          π.restrict (h𝓑𝓧 _ hB) x A = B.indicator 1 x * π x A := by
      simp [isProper_iff_restrict_eq_indicator_smul h𝓑𝓧, Measure.ext_iff]; aesop
    _ ↔ _ := by congr! 5 with A hA B hB x; rw [restrict_apply, Measure.restrict_apply hA]

alias ⟨IsProper.restrict_eq_indicator_smul, IsProper.of_restrict_eq_indicator_smul⟩ :=
  isProper_iff_restrict_eq_indicator_smul

alias ⟨IsProper.inter_eq_indicator_mul, IsProper.of_inter_eq_indicator_mul⟩ :=
  isProper_iff_inter_eq_indicator_mul

lemma IsProper.setLintegral_eq_bind (hπ : IsProper π) (h𝓑𝓧 : 𝓑 ≤ 𝓧) {μ : Measure[𝓧] X}
    (hA : MeasurableSet[𝓧] A) (hB : MeasurableSet[𝓑] B) :
    ∫⁻ a in B, π a A ∂μ = μ.bind π (A ∩ B) := by
  rw [Measure.bind_apply (by measurability) (π.measurable.mono h𝓑𝓧 le_rfl)]
  simp only [hπ.inter_eq_indicator_mul h𝓑𝓧 hA hB, ← indicator_mul_const, Pi.one_apply, one_mul]
  rw [← lintegral_indicator _ (h𝓑𝓧 _ hB)]
  rfl

/-- Auxiliary lemma for `IsProper.lintegral_mul` and
`IsProper.setLintegral_eq_indicator_mul_lintegral`. -/
private lemma IsProper.lintegral_indicator_mul_indicator (hπ : IsProper π) (h𝓑𝓧 : 𝓑 ≤ 𝓧)
    (hA : MeasurableSet[𝓧] A) (hB : MeasurableSet[𝓑] B) :
    ∫⁻ x, B.indicator 1 x * A.indicator 1 x ∂(π x₀) =
      B.indicator 1 x₀ * ∫⁻ x, A.indicator 1 x ∂(π x₀) := by
  simp_rw [← inter_indicator_mul]
  rw [lintegral_indicator _ ((h𝓑𝓧 _ hB).inter hA), lintegral_indicator _ hA]
  simp only [MeasureTheory.lintegral_const, MeasurableSet.univ, Measure.restrict_apply, univ_inter,
    Pi.one_apply, one_mul]
  rw [← hπ.inter_eq_indicator_mul h𝓑𝓧 hA hB, inter_comm]

/-- Auxiliary lemma for `IsProper.lintegral_mul` and
`IsProper.setLintegral_eq_indicator_mul_lintegral`. -/
private lemma IsProper.lintegral_mul_indicator (hπ : IsProper π) (h𝓑𝓧 : 𝓑 ≤ 𝓧)
    (hf : Measurable[𝓧] f) (hB : MeasurableSet[𝓑] B) :
    ∫⁻ x, f x * B.indicator 1 x ∂(π x₀) = B.indicator 1 x₀ * ∫⁻ x, f x ∂(π x₀) := by
  refine hf.ennreal_induction ?_ ?_ ?_
  · rintro c A hA
    simp_rw [← smul_indicator_one_apply, smul_mul_assoc, mul_comm, smul_eq_mul]
    rw [lintegral_const_mul, lintegral_const_mul, hπ.lintegral_indicator_mul_indicator h𝓑𝓧 hA hB,
      mul_left_comm] <;> measurability
  · rintro f₁ f₂ - _ _ hf₁ hf₂
    simp only [Pi.add_apply, add_mul]
    rw [lintegral_add_right, lintegral_add_right, hf₁, hf₂, mul_add] <;> measurability
  · rintro f' hf'_meas hf'_mono hf'
    simp_rw [ENNReal.iSup_mul]
    rw [lintegral_iSup, lintegral_iSup hf'_meas hf'_mono, ENNReal.mul_iSup]
    simp_rw [hf']
    · measurability
    · exact hf'_mono.mul_const (zero_le _)

lemma IsProper.setLintegral_eq_indicator_mul_lintegral (hπ : IsProper π) (h𝓑𝓧 : 𝓑 ≤ 𝓧)
    (hf : Measurable[𝓧] f) (hB : MeasurableSet[𝓑] B) (x₀ : X) :
    ∫⁻ x in B, f x ∂(π x₀) = B.indicator 1 x₀ * ∫⁻ x, f x ∂(π x₀) := by
  simp [← hπ.lintegral_mul_indicator h𝓑𝓧 hf hB, ← indicator_mul_right,
    lintegral_indicator _ (h𝓑𝓧 _ hB)]

lemma IsProper.setLintegral_inter_eq_indicator_mul_setLintegral (hπ : IsProper π) (h𝓑𝓧 : 𝓑 ≤ 𝓧)
    (hf : Measurable[𝓧] f) (hA : MeasurableSet[𝓧] A) (hB : MeasurableSet[𝓑] B) (x₀ : X) :
    ∫⁻ x in A ∩ B, f x ∂(π x₀) = B.indicator 1 x₀ * ∫⁻ x in A, f x ∂(π x₀) := by
  rw [← lintegral_indicator _ hA, ← hπ.setLintegral_eq_indicator_mul_lintegral h𝓑𝓧 _ hB,
    setLintegral_indicator] <;> measurability

lemma IsProper.lintegral_mul (hπ : IsProper π) (h𝓑𝓧 : 𝓑 ≤ 𝓧) (hf : Measurable[𝓧] f)
    (hg : Measurable[𝓑] g) (x₀ : X) :
    ∫⁻ x, f x * g x ∂(π x₀) = g x₀ * ∫⁻ x, f x ∂(π x₀) := by
  refine hg.ennreal_induction' ?_ ?_ ?_
  · rintro c A hA
    simp_rw [← smul_indicator_one_apply, mul_smul_comm, smul_eq_mul]
    rw [lintegral_const_mul, hπ.lintegral_mul_indicator h𝓑𝓧 hf hA, mul_assoc]
    · measurability
  · rintro g₁ g₂ - _ hg₂_meas hg₁ hg₂
    simp only [Pi.add_apply, mul_add, add_mul]
    rw [lintegral_add_right, hg₁, hg₂]
    · exact hf.mul (hg₂_meas.mono h𝓑𝓧 le_rfl)
  · rintro g' hg'_meas hg'_mono hg'
    simp_rw [ENNReal.iSup_mul, ENNReal.mul_iSup]
    rw [lintegral_iSup]
    simp_rw [hg']
    · exact fun n ↦ hf.mul ((hg'_meas _).mono h𝓑𝓧 le_rfl)
    · exact hg'_mono.const_mul (zero_le _)

lemma IsProper.integral_mul (hπ : IsProper π) (h𝓑𝓧 : 𝓑 ≤ 𝓧) (f g : X → ℝ) (x₀ : X)
    (hf : Integrable[𝓧] f (π x₀)) (hg : Integrable[𝓑] (f * g) (@Measure.map _ _ 𝓑 𝓧 id (π x₀))) :
    ∫ x, f x * g x ∂(π x₀) = g x₀ * ∫ x, f x ∂(π x₀) := by
  --Integrable.induction
  sorry

end ProbabilityTheory.Kernel
