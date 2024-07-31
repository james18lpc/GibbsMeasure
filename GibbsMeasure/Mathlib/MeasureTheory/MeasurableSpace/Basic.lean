import Mathlib.MeasureTheory.MeasurableSpace.Basic

/-!
# TODO

Make the `MeasurableSpace` arguments implicit (instead of instance) in:
* `measurable_zero`
-/

open Set Encodable Function Equiv Filter MeasureTheory

universe uι

variable {α β : Type*} {ι : Sort uι}

section MeasurableFunctions

open MeasurableSpace

lemma Measurable.iSup' {mα : ι → MeasurableSpace α} {_ : MeasurableSpace β} {f : α → β} (i₀ : ι)
    (h : Measurable[mα i₀] f) :
    Measurable[⨆ i, mα i] f :=
  h.mono (le_iSup mα i₀) le_rfl

lemma Measurable.sup_of_left {mα mα' : MeasurableSpace α} {_ : MeasurableSpace β} {f : α → β}
    (h : Measurable[mα] f) :
    Measurable[mα ⊔ mα'] f :=
  h.mono le_sup_left le_rfl

lemma Measurable.sup_of_right {mα mα' : MeasurableSpace α} {_ : MeasurableSpace β} {f : α → β}
    (h : Measurable[mα'] f) :
    Measurable[mα ⊔ mα'] f :=
  h.mono le_sup_right le_rfl

end MeasurableFunctions
