import Mathlib.Order.Filter.Basic

namespace Filter
variable {α β : Type*} {f : α → β} {g : α → β} {l : Filter α}

theorem Eventually.of_forall {p : α → Prop} {f : Filter α} (hp : ∀ x, p x) : ∀ᶠ x in f, p x :=
  univ_mem' hp

theorem Frequently.of_forall {f : Filter α} [NeBot f] {p : α → Prop} (h : ∀ x, p x) :
    ∃ᶠ x in f, p x :=
  Eventually.frequently (Eventually.of_forall h)

lemma eventuallyEq_comm : f =ᶠ[l] g ↔ g =ᶠ[l] f := ⟨EventuallyEq.symm, EventuallyEq.symm⟩

end Filter
