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

section
variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- If `μ s < ∞`, then the indicator of a constant function on `s` is integrable. -/
lemma integrable_indicator_const
    (hs : MeasurableSet s) (hμs : μ s < ∞) (c : E) :
    Integrable (s.indicator (fun _ : α => c)) μ := by
  classical
  have hfin : (μ.restrict s) Set.univ < ∞ := by
    simpa [Measure.restrict_apply, Set.univ_inter] using hμs
  have _ : IsFiniteMeasure (μ.restrict s) := ⟨hfin⟩
  have h_int_restrict : Integrable (fun _ : α => c) (μ.restrict s) := integrable_const c
  have h_on : IntegrableOn (fun _ : α => c) s μ := by
    simp [IntegrableOn]
  exact IntegrableOn.integrable_indicator h_int_restrict hs
section
--variable [NormedSpace ℝ E]
open Classical

/-- Set integral of `s.indicator (fun _ ↦ c)` over `t`
is `μ.real (s ∩ t) • c`. -/
lemma setIntegral_indicator_const
    (hs : MeasurableSet s) (t : Set α) (c : E) :
    ∫ x in t, s.indicator (fun _ : α ↦ c) x ∂μ = μ.real (s ∩ t) • c := by
  classical
  have : ∫ x in t, s.indicator (fun _ : α ↦ c) x ∂μ
        = ∫ x, s.indicator (fun _ : α ↦ c) x ∂(μ.restrict t) := rfl
  calc
    ∫ x in t, s.indicator (fun _ : α ↦ c) x ∂μ
        = ∫ x, s.indicator (fun _ : α ↦ c) x ∂(μ.restrict t) := this
    _ = ∫ x in s, (fun _ : α ↦ c) x ∂(μ.restrict t) := by
          simpa using
            (integral_indicator (μ := μ.restrict t) (s := s)
              (f := fun _ : α ↦ c) hs)
    _ = (μ.restrict t).real s • c := setIntegral_const (μ := μ.restrict t) (s := s) (c := c)
    _ = μ.real (s ∩ t) • c := by
          -- `(μ.restrict t) s = μ (s ∩ t)`
          measurability

/-- Specialization: real-valued constant `1`. -/
lemma setIntegral_indicator_one
    (hs : MeasurableSet s) (t : Set α) :
    ∫ x in t, s.indicator (fun _ : α => (1 : ℝ)) x ∂μ = μ.real (s ∩ t) := by
  simpa using
    (setIntegral_indicator_const (μ := μ) (E := ℝ) (s := s) (t := t) (c := (1 : ℝ)) hs)

end

lemma integral_toReal_of_lintegral_ne_top {α} {m : MeasurableSpace α} {μ : Measure α}
    {f : α → ℝ≥0∞} (hf_meas : AEMeasurable f μ)
    (h_fin : (∫⁻ a, f a ∂μ) ≠ ∞) :
    ∫ a, (f a).toReal ∂μ = (∫⁻ a, f a ∂μ).toReal := by
  have h_ae_fin : (∀ᵐ a ∂μ, f a < ∞) := by
    have h_lt : (∫⁻ a, f a ∂μ) < ∞ := by
      have : (∫⁻ a, f a ∂μ) ≤ (∞ : ℝ≥0∞) := le_top
      exact lt_of_le_of_ne this h_fin
    exact ae_lt_top' hf_meas h_fin
  simpa using integral_toReal hf_meas h_ae_fin

namespace AEStronglyMeasurable

/-- Uniqueness for the specific target `ℝ` given a nonnegative function `g : α → ℝ≥0∞` whose
lintegrals over `m`-measurable sets match `μ (s ∩ t)`. -/
theorem toReal_ae_eq_indicator_condExp_of_forall_setLIntegral_eq (hm : m ≤ m0)
  [SigmaFinite (μ.trim hm)] {g : α → ℝ≥0∞} {s : Set α}
  (hs_meas : MeasurableSet s) (hs : μ s ≠ ⊤)
  (hg_int_finite : ∀ t, MeasurableSet[m] t → μ t < ∞ → ∫⁻ a in t, g a ∂μ ≠ ⊤)
  (hg_eq : ∀ t : Set α, MeasurableSet[m] t → μ t < ∞ → ∫⁻ a in t, g a ∂μ = μ (s ∩ t))
  (hgm : AEStronglyMeasurable[m] g μ) :
  (fun a ↦ (g a).toReal) =ᵐ[μ] μ[s.indicator 1|m] := by
  refine ae_eq_condExp_of_forall_setIntegral_eq (m := m) (m₀ := m0) (μ := μ)
    (f := s.indicator fun _ : α => (1 : ℝ))
    hm ?_ ?_ ?_ ?_
  · exact integrable_indicator_const (μ := μ) (s := s) (E := ℝ)
      hs_meas (lt_top_iff_ne_top.mpr hs) (1 : ℝ)
  · intro t ht hμt
    have h_int :
        Integrable (fun a => (g a).toReal) (μ.restrict t) :=
      integrable_toReal_of_lintegral_ne_top
        (μ := μ.restrict t)
        (((hgm.mono hm).aemeasurable).restrict)
        (hg_int_finite t ht hμt)
    simpa [IntegrableOn] using h_int
  · intro t ht hμt
    have h_rhs := setIntegral_indicator_one (μ := μ) (s := s) hs_meas t
    have h_int_ne_top : ∫⁻ a, g a ∂(μ.restrict t) ≠ ⊤ := by
      simpa using (hg_int_finite t ht hμt)
    have h_aemeas : AEMeasurable g (μ.restrict t) :=
      (((hgm.mono hm).aemeasurable).restrict)
    have h_lhs :
        ∫ x in t, (g x).toReal ∂μ
          = (∫⁻ a in t, g a ∂μ).toReal := by
      simpa using
        (integral_toReal_of_lintegral_ne_top (μ := μ.restrict t) h_aemeas h_int_ne_top)
    have h_eq' : ∫⁻ a in t, g a ∂μ = μ (s ∩ t) := hg_eq t ht hμt
    simp [measureReal_def, h_lhs, h_eq', h_rhs]
  · have hmeas_toReal_mk :
        Measurable[m] (fun a => ((hgm.mk g a).toReal)) :=
      ENNReal.measurable_toReal.comp (hgm.stronglyMeasurable_mk.measurable)
    have h_as :
        AEStronglyMeasurable[m] (fun a => ((hgm.mk g a).toReal)) μ :=
      hmeas_toReal_mk.aestronglyMeasurable
    have h_ae :
        (fun a => (g a).toReal) =ᵐ[μ] (fun a => ((hgm.mk g a).toReal)) := by
      filter_upwards [hgm.ae_eq_mk] with a ha
      simp [ha]
    rw [@Metric.toUniformSpace_eq]
    rw [← Metric.toUniformSpace_eq]
    exact (aestronglyMeasurable_congr (id (EventuallyEq.symm h_ae))).mp h_as

/-- Characterization: `g.toReal` equals the conditional expectation of the indicator constant
iff the lintegral of `g` over every `m`-measurable set `t` equals `μ (s ∩ t)`.
We require the natural additional hypothesis that `g < ⊤` a.e. (so that the lintegral on
those sets is finite). -/
lemma toReal_ae_eq_indicator_condExp_iff_forall_meas_inter_eq (hm : m ≤ m0)
  [SigmaFinite (μ.trim hm)] {g : α → ℝ≥0∞} {s : Set α}
  (hs_meas : MeasurableSet s) (hs_finite : μ s ≠ ⊤)
  (hgm : AEStronglyMeasurable[m] g μ)
  (hg_fin : ∀ᵐ a ∂ μ, g a ≠ ⊤) :
  (fun a ↦ (g a).toReal) =ᵐ[μ] μ[s.indicator 1| m] ↔
    ∀ t, MeasurableSet[m] t → μ (s ∩ t) = ∫⁻ a in t, g a ∂μ := by
  constructor
  · intro h_eq t ht
    have h_int_f : Integrable (s.indicator fun _ : α => (1 : ℝ)) μ :=
      integrable_indicator_const (μ := μ) (s := s) (E := ℝ)
        hs_meas (lt_top_iff_ne_top.mpr hs_finite) (1 : ℝ)
    have h_int_eq :=
      setIntegral_condExp (m := m) (m₀ := m0) (μ := μ) hm h_int_f ht
    have h_rhs := setIntegral_indicator_one (μ := μ) (s := s) hs_meas t
    have h_eq_restrict :
        (fun x => (g x).toReal) =ᵐ[μ.restrict t] (fun x => (μ[s.indicator 1|m]) x) := by
      exact EventuallyEq.restrict h_eq
    have h_lhs :
        ∫ x in t, (g x).toReal ∂μ = ∫ x in t, (μ[s.indicator 1|m]) x ∂μ := by
      simpa using (integral_congr_ae (μ := μ.restrict t) h_eq_restrict)
    have h_int_g_toReal_on : IntegrableOn (fun a ↦ (g a).toReal) t μ :=
      (integrable_condExp.integrableOn.congr h_eq_restrict.symm)
    have h_int_g_toReal :
        Integrable (fun a ↦ (g a).toReal) (μ.restrict t) := by
      simpa [IntegrableOn] using h_int_g_toReal_on
    have h_ae_fin : ∀ᵐ a ∂ μ.restrict t, g a ≠ ⊤ :=
      ae_restrict_of_ae hg_fin
    have h_fin_lintegral_g :
        ∫⁻ a, g a ∂(μ.restrict t) ≠ ⊤ :=
      ((integrable_toReal_iff
        (μ := μ.restrict t)
        (((hgm.mono hm).aemeasurable).restrict)) h_ae_fin).1 h_int_g_toReal
    have h_toReal :
        ∫ x in t, (g x).toReal ∂μ
          = (∫⁻ a in t, g a ∂μ).toReal := by
      simpa using
        (integral_toReal_of_lintegral_ne_top (μ := μ.restrict t)
          (((hgm.mono hm).aemeasurable).restrict) h_fin_lintegral_g)
    have h_eq_int :
        ∫ x in t, (g x).toReal ∂μ = μ.real (s ∩ t) := by
      simpa [h_rhs] using h_lhs.trans h_int_eq
    have h_left_ne : ∫⁻ a in t, g a ∂μ ≠ ⊤ := h_fin_lintegral_g
    have h_le : μ (s ∩ t) ≤ μ s := by
      have hsubset : s ∩ t ⊆ s := by intro x hx; exact hx.1
      exact measure_mono hsubset
    have h_right_ne : μ (s ∩ t) ≠ ⊤ := by
      intro htop
      have : (⊤ : ℝ≥0∞) ≤ μ s := by simpa [htop] using h_le
      exact hs_finite (top_unique this)
    have h_toReal' :
        (∫⁻ a in t, g a ∂μ).toReal = μ.real (s ∩ t) := by
      simpa [h_toReal] using h_eq_int
    have h_lintegral_eq_measure :
        ∫⁻ a in t, g a ∂μ = μ (s ∩ t) := by
      have := congrArg ENNReal.ofReal h_toReal'
      simpa [measureReal_def,
             ENNReal.ofReal_toReal h_left_ne,
             ENNReal.ofReal_toReal h_right_ne] using this
    simp [h_lintegral_eq_measure]
  · intro h_eq
    refine
      toReal_ae_eq_indicator_condExp_of_forall_setLIntegral_eq
        (m := m) (m0 := m0) (μ := μ) (g := g) (s := s)
        hm hs_meas hs_finite
        ?hg_int_finite ?hg_eq hgm
    · intro t ht hμt
      have hsubset : s ∩ t ⊆ t := by
        intro x hx; exact hx.2
      have hμst_lt : μ (s ∩ t) < ∞ := (measure_mono hsubset).trans_lt hμt
      have h_id : ∫⁻ a in t, g a ∂μ = μ (s ∩ t) := (h_eq t ht).symm
      simpa [h_id] using hμst_lt.ne
    · intro t ht _hμt
      simpa using (h_eq t ht).symm

end AEStronglyMeasurable
end
end MeasureTheory
