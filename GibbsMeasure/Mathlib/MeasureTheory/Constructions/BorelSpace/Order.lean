import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

variable {α δ : Type*} {mα : MeasurableSpace α} {mδ : MeasurableSpace δ} [TopologicalSpace α]
  [BorelSpace α] [ConditionallyCompleteLinearOrder α] [OrderTopology α] [SecondCountableTopology α]

-- TODO: Replace `measurable_iSup`. Same for `iInf`, `sSup`, `sInf`...
@[measurability]
lemma Measurable.iSup {ι} [Countable ι] {f : ι → δ → α} (hf : ∀ i, Measurable (f i)) :
    Measurable (fun b ↦ ⨆ i, f i b) := measurable_iSup hf
