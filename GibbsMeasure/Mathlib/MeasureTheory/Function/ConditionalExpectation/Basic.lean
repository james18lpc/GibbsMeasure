import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

open TopologicalSpace MeasureTheory.Lp Filter
open scoped ENNReal Topology MeasureTheory

namespace MeasureTheory
variable {α F F' 𝕜 : Type*} {p : ℝ≥0∞} [RCLike 𝕜]
  [NormedAddCommGroup F]
  [NormedSpace 𝕜 F]
  [NormedAddCommGroup F']
  [NormedSpace 𝕜 F'] [NormedSpace ℝ F'] [CompleteSpace F']

open scoped Classical

variable {m m0 : MeasurableSpace α} {μ : Measure α} {f g : α → F'} {s : Set α}

-- /-- **Uniqueness of the conditional expectation**
-- If a function is a.e. `m`-measurable, verifies an integrability condition and has same integral
-- as `f` on all `m`-measurable sets, then it is a.e. equal to `μ[f|hm]`. -/
-- theorem toReal_ae_eq_condexp_toReal_of_forall_setLIntegral_eq (hm : m ≤ m0)
--     [SigmaFinite (μ.trim hm)] {f g : α → ℝ≥0∞} (hf_meas : AEMeasurable f μ)
--     (hf : ∫⁻ a, f a ∂μ ≠ ⊤)
--     (hg_int_finite : ∀ s, MeasurableSet[m] s → μ s < ∞ → ∫⁻ a in s, g a ∂μ ≠ ⊤)
--     (hg_eq : ∀ s : Set α, MeasurableSet[m] s → μ s < ∞ → ∫⁻ x in s, g x ∂μ = ∫⁻ x in s, f x ∂μ)
--     (hgm : AEStronglyMeasurable' m g μ) :
--     (fun a ↦ (g a).toReal) =ᵐ[μ] μ[fun a ↦ (f a).toReal|m] := by
--   refine ae_eq_condexp_of_forall_setIntegral_eq hm
--     (integrable_toReal_of_lintegral_ne_top hf_meas hf)
--     (fun s hs hs_fin ↦ integrable_toReal_of_lintegral_ne_top _ _) _ _

/-- **Uniqueness of the conditional expectation**
If a function is a.e. `m`-measurable, verifies an integrability condition and has same integral
as `f` on all `m`-measurable sets, then it is a.e. equal to `μ[f|hm]`. -/
theorem toReal_ae_eq_indicator_condexp_of_forall_setLIntegral_eq (hm : m ≤ m0)
    [SigmaFinite (μ.trim hm)] {g : α → ℝ≥0∞} {s : Set α} (hs : μ s ≠ ⊤)
    (hg_int_finite : ∀ t, MeasurableSet[m] t → μ t < ∞ → ∫⁻ a in t, g a ∂μ ≠ ⊤)
    (hg_eq : ∀ t : Set α, MeasurableSet[m] t → μ t < ∞ → ∫⁻ a in t, g a ∂μ = μ (s ∩ t))
    (hgm : AEStronglyMeasurable' m g μ) : (fun a ↦ (g a).toReal) =ᵐ[μ] μ[s.indicator 1|m] := by
  refine ae_eq_condexp_of_forall_setIntegral_eq hm ?_ ?_ ?_ ?_ <;> sorry

lemma toReal_ae_eq_indicator_condexp_iff_forall_meas_inter_eq (hm : m ≤ m0)
    [SigmaFinite (μ.trim hm)] {g : α → ℝ≥0∞} {s : Set α} :
    (fun a ↦ (g a).toReal) =ᵐ[μ] μ[s.indicator 1| m] ↔
      ∀ t, MeasurableSet[m] t → μ (s ∩ t) = ∫⁻ a in t, g a ∂μ := sorry
