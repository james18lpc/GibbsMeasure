import Mathlib.Algebra.GroupWithZero.Indicator

/-!
### TODO

The existing lemmas are a mess
-/

namespace Set
variable {ι M₀ : Type*} [MulZeroClass M₀]

lemma indicator_mul' (s : Set ι) (f : ι → M₀) (a : M₀) (i : ι) :
    s.indicator f i * a = s.indicator (fun j ↦ f j * a) i :=
  (Set.indicator_mul_left _ _ fun _ ↦ a).symm

lemma mul_indicator (s : Set ι) (f : ι → M₀) (a : M₀) (i : ι) :
    a * s.indicator f i = s.indicator (fun j ↦ a * f j) i :=
  (Set.indicator_mul_right _ (fun _ ↦ a) _).symm

end Set
