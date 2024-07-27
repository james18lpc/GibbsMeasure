import Mathlib.MeasureTheory.Measure.GiryMonad
import GibbsMeasure.Mathlib.MeasureTheory.Measure.MeasureSpaceDef

open scoped ENNReal

namespace MeasureTheory.Measure
variable {α β : Type*} [MeasurableSpace β]

-- TODO: Make `MeasurableSpace.generateFrom_induction` give me the measurability of the sets in
-- hypotheses
theorem measurable_of_measurable_coe' (t : Set (Set α)) (f : β → Measure[.generateFrom t] α)
    [∀ b, IsProbabilityMeasure (f b)] (h : ∀ s ∈ t, Measurable fun b => f b s) : Measurable f := by
  refine @measurable_of_measurable_coe _ _ (_) _ _ $ fun {s} hs ↦
    MeasurableSpace.generateFrom_induction
      (p := fun s ↦ MeasurableSet[.generateFrom t] s → Measurable fun b ↦ (f b) s) t
      (fun s hs _ ↦ h _ hs) (by simp)
      ?_ ?_ hs hs
  · rintro s hs hs'
    simp_rw [prob_compl_eq_one_sub hs'.of_compl]
    exact (hs hs'.of_compl).const_sub _
  · rintro g hg
    sorry

variable {mα : MeasurableSpace α} {s : Set α}

lemma measurable_restrict (hs : MeasurableSet s) : Measurable fun μ : Measure α ↦ μ.restrict s :=
  measurable_of_measurable_coe _ fun t ht ↦ by
    simp_rw [restrict_apply ht]; exact measurable_coe (ht.inter hs)

lemma measurable_setLintegral {f : α → ℝ≥0∞} (hf : Measurable f) (hs : MeasurableSet s) :
    Measurable fun μ : Measure α ↦ ∫⁻ x in s, f x ∂μ :=
  (measurable_lintegral hf).comp (measurable_restrict hs)

end MeasureTheory.Measure
