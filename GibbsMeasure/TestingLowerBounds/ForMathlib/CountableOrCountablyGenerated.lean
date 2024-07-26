import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated

namespace MeasurableSpace

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]


lemma countable_left_of_prod_of_nonempty [Nonempty β] (h : Countable (α × β)) : Countable α := by
  contrapose h
  rw [not_countable_iff] at *
  infer_instance

lemma countable_right_of_prod_of_nonempty [Nonempty α] (h : Countable (α × β)) : Countable β := by
  contrapose h
  rw [not_countable_iff] at *
  infer_instance

lemma countableOrCountablyGenerated_left_of_prod_left_of_nonempty [Nonempty β]
    [h : CountableOrCountablyGenerated (α × β) γ] :
    CountableOrCountablyGenerated α γ := by
  rcases h.countableOrCountablyGenerated with (h | h)
  · have := countable_left_of_prod_of_nonempty h
    infer_instance
  · infer_instance

lemma countableOrCountablyGenerated_right_of_prod_left_of_nonempty [Nonempty α]
    [h : CountableOrCountablyGenerated (α × β) γ] :
    CountableOrCountablyGenerated β γ := by
  rcases h.countableOrCountablyGenerated with (h | h)
  · have := countable_right_of_prod_of_nonempty h
    infer_instance
  · infer_instance

lemma countablyGenerated_left_of_prod_of_nonempty [Nonempty β] (h : CountablyGenerated (α × β)) :
    CountablyGenerated α := by
  -- contrapose h
  sorry

lemma countablyGenerated_right_of_prod_of_nonempty [Nonempty α] (h : CountablyGenerated (α × β)) :
    CountablyGenerated β := by
  -- contrapose h
  sorry

lemma countableOrCountablyGenerated_right_of_prod_right_of_nonempty [Nonempty β]
    [h : CountableOrCountablyGenerated α (β × γ)] :
    CountableOrCountablyGenerated α γ := by
  rcases h.countableOrCountablyGenerated with (h | h)
  · infer_instance
  · have := countablyGenerated_right_of_prod_of_nonempty h
    infer_instance

lemma countableOrCountablyGenerated_left_of_prod_right_of_nonempty [Nonempty γ]
    [h : CountableOrCountablyGenerated α (β × γ)] :
    CountableOrCountablyGenerated α β := by
  rcases h.countableOrCountablyGenerated with (h | h)
  · infer_instance
  · have := countablyGenerated_left_of_prod_of_nonempty h
    infer_instance

instance [Countable (α × β)] : Countable (β × α) :=
  Countable.of_equiv _ (Equiv.prodComm α β)

instance [h : CountableOrCountablyGenerated (α × β) γ] :
    CountableOrCountablyGenerated (β × α) γ := by
  rcases h with (h | h)
  · exact ⟨Or.inl inferInstance⟩
  · exact ⟨Or.inr h⟩

instance [CountablyGenerated (α × β)] : CountablyGenerated (β × α) := by
  sorry

instance [h : CountableOrCountablyGenerated (α × β) γ] :
    CountableOrCountablyGenerated (β × α) γ := by
  rcases h with (h | h)
  · exact ⟨Or.inl inferInstance⟩
  · exact ⟨Or.inr h⟩

end MeasurableSpace
