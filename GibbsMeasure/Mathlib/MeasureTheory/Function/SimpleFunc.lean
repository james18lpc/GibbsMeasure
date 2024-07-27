import Mathlib.MeasureTheory.Function.SimpleFunc

open MeasureTheory MeasureTheory.SimpleFunc Function
open scoped ENNReal

/-- To prove something for an arbitrary measurable function into `ℝ≥0∞`, it suffices to show
that the property holds for (multiples of) characteristic functions and is closed under addition
and supremum of increasing sequences of functions.

It is possible to make the hypotheses in the induction steps a bit stronger, and such conditions
can be added once we need them (for example in `h_add` it is only necessary to consider the sum of
a simple function with a multiple of a characteristic function and that the intersection
of their images is a subset of `{0}`. -/
@[elab_as_elim]
-- TODO: Replace `Measurable.ennreal_induction`
theorem Measurable.ennreal_induction' {α} {mα : MeasurableSpace α} {P : (α → ℝ≥0∞) → Prop}
    (h_ind : ∀ (c : ℝ≥0∞) ⦃s⦄, MeasurableSet s → P (Set.indicator s fun _ => c))
    (h_add :
      ∀ ⦃f g : α → ℝ≥0∞⦄,
        Disjoint (support f) (support g) → Measurable f → Measurable g → P f → P g → P (f + g))
    (h_iSup :
      ∀ ⦃f : ℕ → α → ℝ≥0∞⦄, (∀ n, Measurable (f n)) → Monotone f → (∀ n, P (f n)) →
        P fun x => ⨆ n, f n x)
    ⦃f : α → ℝ≥0∞⦄ (hf : Measurable f) : P f := by
  convert h_iSup (fun n => (eapprox f n).measurable) (monotone_eapprox f) _ using 1
  · ext1 x
    rw [iSup_eapprox_apply f hf]
  · exact fun n =>
      SimpleFunc.induction (fun c s hs => h_ind c hs)
        (fun f g hfg hf hg => h_add hfg f.measurable g.measurable hf hg) (eapprox f n)
