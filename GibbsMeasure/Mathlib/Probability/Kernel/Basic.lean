import Mathlib.Probability.Kernel.Basic

namespace ProbabilityTheory

scoped notation "kernel[" mα "]" α:arg β:arg => @Kernel α β mα _
scoped notation "kernel[" mα ", " mβ "]" α:arg β:arg => @Kernel α β mα mβ

example {α β : Type} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} :
    kernel[mα, mβ] α β = kernel[mα] α β := sorry

end ProbabilityTheory
