import Mathlib.Data.Set.Function

namespace Set
variable {α : Type*} {δ : α → Type*} [∀ i, Preorder (δ i)] {s : Set α} [DecidablePred (· ∈ s)]
  {f₁ f₂ g₁ g₂ : ∀ i, δ i}

@[gcongr] lemma piecewise_mono (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) :
    s.piecewise f₁ g₁ ≤ s.piecewise f₂ g₂ :=
  piecewise_le_piecewise (fun _ _ ↦ hf _) (fun _ _ ↦ hg _)

end Set
