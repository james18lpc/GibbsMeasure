import Mathlib.Probability.Kernel.Basic

namespace ProbabilityTheory

scoped notation "Kernel[" mα "]" α:arg β:arg => @Kernel α β mα _
scoped notation "Kernel[" mα ", " mβ "]" α:arg β:arg => @Kernel α β mα mβ

example {α β : Type} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} :
    Kernel[mα, mβ] α β = Kernel[mα] α β := sorry

initialize_simps_projections Kernel (toFun → apply)

end ProbabilityTheory
