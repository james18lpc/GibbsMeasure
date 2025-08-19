import Mathlib.MeasureTheory.Measure.GiryMonad

open scoped ENNReal

namespace MeasureTheory.Measure
variable {α β : Type*} [MeasurableSpace β]

/--
This theorem requires `IsPiSystem t`. Without it, the induction strategy fails because
the predicate `P(s) := Measurable (fun b => μ b s)` is not closed under intersections,
which are needed for the disjointification step in the countable union case.
-/
theorem measurable_of_measurable_coe'
    (t : Set (Set α)) (μ : β → Measure[.generateFrom t] α)
    [∀ b, IsProbabilityMeasure (μ b)]
    (hpi : IsPiSystem t)
    (h : ∀ s ∈ t, Measurable fun b => μ b s) : Measurable μ := by
  let _ : MeasurableSpace α := MeasurableSpace.generateFrom t
  change Measurable (μ : β → Measure α)
  simpa using
    (Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
      (μ := μ) (S := t) (hgen := rfl) (hpi := hpi) (h_basic := h))

variable {mα : MeasurableSpace α} {s : Set α}

lemma measurable_restrict (hs : MeasurableSet s) : Measurable fun μ : Measure α ↦ μ.restrict s :=
  measurable_of_measurable_coe _ fun t ht ↦ by
    simp_rw [restrict_apply ht]; exact measurable_coe (ht.inter hs)

lemma measurable_setLIntegral {f : α → ℝ≥0∞} (hf : Measurable f) (hs : MeasurableSet s) :
    Measurable fun μ : Measure α ↦ ∫⁻ x in s, f x ∂μ :=
  (measurable_lintegral hf).comp (measurable_restrict hs)

end MeasureTheory.Measure
