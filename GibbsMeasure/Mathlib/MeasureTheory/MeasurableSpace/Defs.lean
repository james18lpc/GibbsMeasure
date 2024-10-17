import Mathlib.MeasureTheory.MeasurableSpace.Defs

open MeasureTheory

namespace MeasurableSpace
variable {α : Type*}

@[elab_as_elim]
lemma generateFrom_induction' (p : Set α → Prop) (C : Set (Set α)) (hC : ∀ t ∈ C, p t)
    (h_empty : p ∅) (h_compl : ∀ t, MeasurableSet[generateFrom C] t → p t → p tᶜ)
    (h_Union : ∀ t : ℕ → Set α,
      (∀ n, MeasurableSet[generateFrom C] (t n)) → (∀ n, p (t n)) → p (⋃ i, t i))
    {s : Set α} (hs : MeasurableSet[generateFrom C] s) : p s :=
  And.right $ generateFrom_induction (p := fun t ↦ MeasurableSet[generateFrom C] t ∧ p t) _
    (fun t ht ↦ ⟨measurableSet_generateFrom ht, hC _ ht⟩) (by simpa)
    (fun t ht ↦ ⟨ht.1.compl, h_compl _ ht.1 ht.2⟩)
    (fun t ht ↦ ⟨measurableSet_iUnion _ _ fun n ↦ (ht _).1, h_Union _ (fun n ↦ (ht _).1)
      fun n ↦ (ht _).2⟩) hs

end MeasurableSpace
