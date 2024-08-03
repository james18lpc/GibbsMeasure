import Mathlib.Algebra.Order.Group.Indicator

namespace Set
variable {ι : Type*} {α M : Type*}

section Preorder
variable [Preorder M] [One M] {s t : Set α} {f g : α → M} {a : α}

@[to_additive (attr := gcongr)]
lemma mulIndicator_mono (h : f ≤ g) : s.mulIndicator f ≤ s.mulIndicator g :=
  fun _ ↦ mulIndicator_le_mulIndicator (h _)

-- TODO: Replace `mulIndicator_le_mulIndicator_of_subset` and rename
@[to_additive]
lemma mulIndicator_le_mulIndicator_apply_of_subset (h : s ⊆ t) (hf : 1 ≤ f a) :
    mulIndicator s f a ≤ mulIndicator t f a :=
  mulIndicator_apply_le'
    (fun ha ↦ le_mulIndicator_apply (fun _ ↦ le_rfl) fun hat ↦ (hat <| h ha).elim) fun _ ↦
    one_le_mulIndicator_apply fun _ ↦ hf

@[to_additive]
lemma mulIndicator_le_mulIndicator_of_subset' (h : s ⊆ t) (hf : ∀ a, 1 ≤ f a) :
    mulIndicator s f ≤ mulIndicator t f :=
  fun _ ↦ mulIndicator_le_mulIndicator_apply_of_subset h (hf _)

end Preorder

section CompleteLattice
variable [Preorder ι] [IsDirected ι (· ≤ ·)] [CompleteLattice M] [One M] {f : ι → α → M}
  {s : ι → Set α}

@[to_additive]
lemma iSup_mulIndicator (h1 : (⊥ : M) = 1) (hf : Monotone f) (hs : Monotone s) :
    ⨆ i, (s i).mulIndicator (f i) = (⋃ i, s i).mulIndicator (⨆ i, f i) := by
  simp only [le_antisymm_iff, iSup_le_iff]
  refine ⟨fun i ↦ (mulIndicator_mono (le_iSup _ _)).trans
    (mulIndicator_le_mulIndicator_of_subset' (subset_iUnion _ _) (by simp [← h1])), fun a ↦ ?_⟩
  by_cases ha : a ∈ ⋃ i, s i
  · obtain ⟨i, hi⟩ : ∃ i, a ∈ s i := by simpa using ha
    rw [mulIndicator_of_mem ha, iSup_apply, iSup_apply]
    refine iSup_le fun j ↦ ?_
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    refine le_iSup_of_le k $ (hf hjk _).trans_eq ?_
    rw [mulIndicator_of_mem (hs hik hi)]
  · rw [mulIndicator_of_not_mem ha, ← h1]
    exact bot_le

end CompleteLattice
end Set
