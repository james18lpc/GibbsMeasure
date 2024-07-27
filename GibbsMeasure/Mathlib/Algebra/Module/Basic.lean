import Mathlib.Algebra.Module.Basic

namespace Set
variable {α R M : Type*} [MulZeroOneClass R]

lemma smul_indicator_one_apply (s : Set α) (r : R) (a : α) :
    r • s.indicator (1 : α → R) a = s.indicator (fun _ ↦ r) a := by
  simp_rw [← indicator_const_smul_apply, Pi.one_apply, smul_eq_mul, mul_one]

end Set
