import Mathlib.MeasureTheory.Constructions.Pi

open Function Set

namespace MeasurableSpace
variable {ι : Type*} {α : ι → Type*} {mα : ∀ i, MeasurableSpace (α i)}

lemma pi_eq_generateFrom_projections :
    MeasurableSpace.pi =
      generateFrom {B | ∃ (i : ι) (A : Set (α i)), MeasurableSet A ∧ eval i ⁻¹' A = B} := by
  refine le_antisymm ?_ $ generateFrom_mono ?_
  · refine generateFrom_le ?_
    simp only [sSup_eq_sUnion, sUnion_image, mem_range, iUnion_exists, iUnion_iUnion_eq',
      mem_iUnion, mem_setOf_eq, exists_prop, forall_exists_index]
    rintro _ i ⟨A, hA, rfl⟩
    exact measurableSet_generateFrom ⟨i, A, hA, rfl⟩
  · rintro _ ⟨i, A, hA, rfl⟩
    simp only [sSup_eq_sUnion, sUnion_image, mem_range, iUnion_exists, iUnion_iUnion_eq',
      mem_iUnion, mem_setOf_eq]
    exact ⟨i, A, hA, rfl⟩

end MeasurableSpace
