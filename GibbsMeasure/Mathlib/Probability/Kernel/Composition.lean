import Mathlib.Probability.Kernel.Composition

namespace ProbabilityTheory.Kernel
variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}

@[simp, norm_cast]
lemma coe_comap (κ : Kernel α β) (g : γ → α) (hg : Measurable g) : κ.comap g hg = κ ∘ g := rfl

end ProbabilityTheory.Kernel
