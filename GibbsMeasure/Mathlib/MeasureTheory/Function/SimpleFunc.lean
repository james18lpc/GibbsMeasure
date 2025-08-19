import Mathlib.MeasureTheory.Function.SimpleFunc

namespace MeasureTheory.SimpleFunc
variable {α β : Type*}

scoped infixr:25 " →ₛ " => SimpleFunc
scoped notation:25 α:26 " →ₛ[" mα "] " β:25 => @SimpleFunc α mα β

end MeasureTheory.SimpleFunc
