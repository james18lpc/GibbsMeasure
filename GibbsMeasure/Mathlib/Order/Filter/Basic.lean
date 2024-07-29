import Mathlib.Order.Filter.Basic

namespace Filter
variable {α β : Type*} {f : α → β} {g : α → β} {l : Filter α}

-- TODO: Replace in mathlib
alias Eventually.of_forall := eventually_of_forall
alias Frequently.of_forall := frequently_of_forall

lemma eventuallyEq_comm : f =ᶠ[l] g ↔ g =ᶠ[l] f := ⟨EventuallyEq.symm, EventuallyEq.symm⟩

end Filter
