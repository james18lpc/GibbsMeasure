import Mathlib.Probability.Kernel.Basic

open MeasureTheory

namespace ProbabilityTheory

/-- Notation for `Kernel` with respect to a non-standard σ-algebra in the domain. -/
scoped notation "Kernel[" mα "]" α:arg β:arg => @Kernel α β mα _

/-- Notation for `Kernel` with respect to a non-standard σ-algebra in the domain and codomain. -/
scoped notation "Kernel[" mα ", " mβ "]" α:arg β:arg => @Kernel α β mα mβ

example {α β : Type} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} :
    Kernel[mα, mβ] α β = Kernel[mα] α β := rfl

initialize_simps_projections Kernel (toFun → apply)

namespace Kernel
variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

@[simp, norm_cast] lemma coe_mk (f : α → Measure β) (hf) : mk f hf = f := rfl

end ProbabilityTheory.Kernel
