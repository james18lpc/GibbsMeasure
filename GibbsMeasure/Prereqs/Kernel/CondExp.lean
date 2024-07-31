import GibbsMeasure.Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import GibbsMeasure.Mathlib.Order.Filter.Basic
import GibbsMeasure.Prereqs.Kernel.Proper

open MeasureTheory ENNReal NNReal Set

namespace ProbabilityTheory.Kernel
variable {X : Type*} {𝓑 𝓧 : MeasurableSpace X} {π : Kernel[𝓑, 𝓧] X X} {μ : Measure[𝓧] X}
  {A B : Set X} {f g : X → ℝ≥0∞} {x₀ : X}

@[mk_iff]
class IsCondExp (π : Kernel[𝓑, 𝓧] X X) (μ : Measure[𝓧] X) : Prop :=
  condexp_ae_eq_kernel_apply ⦃A⦄ : MeasurableSet[𝓧] A →
    μ[A.indicator 1| 𝓑] =ᵐ[μ] fun a ↦ (π a A).toReal

lemma isCondExp_iff_bind_eq_left (hπ : π.IsProper) (h𝓑𝓧 : 𝓑 ≤ 𝓧) [SigmaFinite (μ.trim h𝓑𝓧)] :
    IsCondExp π μ ↔ μ.bind π = μ := by
  simp_rw [isCondExp_iff, Filter.eventuallyEq_comm,
    toReal_ae_eq_indicator_condexp_iff_forall_meas_inter_eq h𝓑𝓧, Measure.ext_iff]
  refine ⟨fun h A hA ↦ ?_, fun h A hA B hB ↦ ?_⟩
  · rw [eq_comm, Measure.bind_apply hA (π.measurable.mono h𝓑𝓧 le_rfl)]
    simpa using h hA _ .univ
  · rw [hπ.setLintegral_eq_bind h𝓑𝓧 hA hB, eq_comm]
    exact h _ (by measurability)

-- TODO: add to blueprint
lemma condexp_ae_eq_kernel_apply {X : Type*} [𝓧 : MeasurableSpace X] (𝓑 : MeasurableSpace X)
    --(hSub : 𝓑 ≤ 𝓧)
    (μ : Measure[𝓧] X) [IsFiniteMeasure μ]
    (π : Kernel[𝓑, 𝓧] X X) [∀ x, IsFiniteMeasure (π x)]
    (h : ∀ (f : X → ℝ), Bornology.IsBounded (Set.range f) → Measurable[𝓧] f →
      condexp 𝓑 μ f =ᵐ[μ] (fun x₀ ↦ ∫ x, f x ∂(π x₀)))
    {A : Set X} (A_mble : MeasurableSet[𝓧] A) :
    condexp 𝓑 μ (A.indicator (fun _ ↦ (1 : ℝ))) =ᵐ[μ] (fun x ↦ (π x A).toReal) := by
  have ind_bdd : Bornology.IsBounded (Set.range (A.indicator (fun _ ↦ (1 : ℝ)))) := by
    apply (Metric.isBounded_Icc (0 : ℝ) 1).subset
    rw [range_subset_iff]
    intro x
    by_cases hx : x ∈ A <;> simp [hx]
  have ind_mble : Measurable[𝓧] (A.indicator (fun _ ↦ (1 : ℝ))) := by
    exact (measurable_indicator_const_iff 1).mpr A_mble
  specialize h _ ind_bdd ind_mble
  apply h.trans
  simp_rw [← Pi.one_def, @integral_indicator_one X 𝓧 _ _ A_mble]
  rfl

lemma condexp_indicator_ae_eq_integral_kernel {X : Type*} [𝓧 : MeasurableSpace X]
    (𝓑 : MeasurableSpace X)
    --(hSub : 𝓑 ≤ 𝓧)
    (μ : Measure[𝓧] X) [IsFiniteMeasure μ]
    (π : Kernel[𝓑, 𝓧] X X) [∀ x, IsFiniteMeasure (π x)]
    {A : Set X} (A_mble : MeasurableSet[𝓧] A)
    (h : condexp 𝓑 μ (A.indicator (fun _ ↦ (1 : ℝ))) =ᵐ[μ] (fun x ↦ (π x A).toReal)) :
    condexp 𝓑 μ (A.indicator (fun _ ↦ (1 : ℝ)))
      =ᵐ[μ] (fun x₀ ↦ ∫ x, A.indicator (fun _ ↦ (1 : ℝ)) x ∂(π x₀)) := by
  apply h.trans
  simp_rw [← Pi.one_def, @integral_indicator_one X 𝓧 _ _ A_mble]
  rfl


lemma condexp_const_indicator_ae_eq_integral_kernel {X : Type*} [𝓧 : MeasurableSpace X]
    (𝓑 : MeasurableSpace X)
    --(hSub : 𝓑 ≤ 𝓧)
    (μ : Measure[𝓧] X) [IsFiniteMeasure μ]
    (π : Kernel[𝓑, 𝓧] X X) [∀ (x : X), IsFiniteMeasure (π x)]
    (c : ℝ)
    {A : Set X} (A_mble : MeasurableSet[𝓧] A)
    (h : condexp 𝓑 μ (A.indicator (fun _ ↦ (1 : ℝ))) =ᵐ[μ] (fun x ↦ (π x A).toReal)) :
    condexp 𝓑 μ (A.indicator (fun _ ↦ (c : ℝ)))
      =ᵐ[μ] (fun x₀ ↦ ∫ x, A.indicator (fun _ ↦ (c : ℝ)) x ∂(π x₀)) := by
  have smul_eq : A.indicator (fun _ ↦ (c : ℝ)) = c • A.indicator (fun _ ↦ (1 : ℝ)) := by
    sorry
  have foo : c • condexp 𝓑 μ (A.indicator (fun _ ↦ (1 : ℝ)))
     =ᵐ[μ] condexp 𝓑 μ (A.indicator (fun _ ↦ (c : ℝ))) := by
    have := @condexp_smul X ℝ ℝ _ _ _ _ _ 𝓑 𝓧 μ c (A.indicator (fun _ ↦ (1 : ℝ)))
    rw [smul_eq]
    exact Filter.EventuallyEq.symm this
  nth_rw 2 [smul_eq]
  have int_smul (x₀ : X) := @integral_smul X ℝ _ ℝ _ _ 𝓧 (π x₀) _ _ c
    (A.indicator (fun _ ↦ (1 : ℝ)))
  --simp_rw [@integral_smul X ℝ _ ℝ _ _ 𝓧 (π _) _ _ c (A.indicator (fun _ ↦ (1 : ℝ)))]
  --apply this.symm
  simp at *
  simp_rw [int_smul]
  --rw [smul_eq]
  apply foo.symm.trans
  have : c • (fun x₀ ↦ ∫ (a : X), A.indicator (fun x ↦ (1 : ℝ)) a ∂π x₀)
     = fun x₀ ↦ c * ∫ (a : X), A.indicator (fun x ↦ (1 : ℝ)) a ∂π x₀ := by
    sorry
  rw [← this]
  have := @condexp_indicator_ae_eq_integral_kernel X 𝓧 𝓑 μ _ π _ A A_mble h

  -- change c • μ[A.indicator fun x ↦ 1|𝓑] =ᶠ[ae μ]
  --   c • (fun x₀ ↦ ∫ (a : X), A.indicator (fun x ↦ 1) a ∂π x₀)
  sorry

lemma condexp_simpleFunc_ae_eq_integral_kernel {X : Type*} [𝓧 : MeasurableSpace X]
   (𝓑 : MeasurableSpace X)
    --(hSub : 𝓑 ≤ 𝓧)
    (μ : Measure[𝓧] X) [IsFiniteMeasure μ]
    (π : Kernel[𝓑, 𝓧] X X) [∀ (x : X), IsFiniteMeasure (π x)]
    (h : ∀ (A : Set X), MeasurableSet[𝓧] A →
      condexp 𝓑 μ (A.indicator (fun _ ↦ (1 : ℝ))) =ᵐ[μ] (fun x ↦ (π x A).toReal))
    (f : @SimpleFunc X 𝓧 ℝ) :
    condexp 𝓑 μ f =ᵐ[μ] (fun x₀ ↦ ∫ x, f x ∂(π x₀)) := by
  induction' f using SimpleFunc.induction with c A A_mble
  case h_ind =>
    sorry
  case h_add => sorry


lemma bind_eq_self_iff (X : Type*) [𝓧 : MeasurableSpace X] (𝓑 : MeasurableSpace X) (hSub : 𝓑 ≤ 𝓧)
    (μ : Measure[𝓧] X) (π : Kernel[𝓑, 𝓧] X X) (π_proper : π.IsProper)
    (A : Set X) (A_mble : MeasurableSet A) :
    condexp 𝓑 μ (A.indicator (fun _ ↦ (1 : ℝ)))
      =ᵐ[μ] (fun x ↦ (π x A).toReal) ↔ @Measure.bind X X 𝓧 𝓧 μ π A = μ A :=
  ⟨by
  intro h
  have : μ A = μ A := by
    sorry
  sorry,
  by sorry⟩
