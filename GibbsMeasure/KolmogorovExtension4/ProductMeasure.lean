/-
Copyright (c) 2024 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Process.Filtration

open MeasureTheory MeasurableSpace ProbabilityTheory Finset ENNReal Filter Topology Function Kernel

namespace MeasureTheory

section Preliminaries

variable {ι : Type*}

theorem preimage_proj {α : ι → Type*} (I J : Finset ι) [∀ i : ι, Decidable (i ∈ I)]
    (hIJ : I ⊆ J) (s : (i : I) → Set (α i)) :
    (fun t : (∀ j : J, α j) ↦ fun i : I ↦ t ⟨i, hIJ i.2⟩) ⁻¹' (Set.univ.pi s) =
    (@Set.univ J).pi (fun j ↦ if h : j.1 ∈ I then s ⟨j.1, h⟩ else Set.univ) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Subtype.forall]
  refine ⟨fun h i hi ↦ ?_, fun h i i_mem ↦ by simpa [i_mem] using h i (hIJ i_mem)⟩
  split_ifs with i_mem
  · exact h i i_mem
  · trivial

variable {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
variable (μ : (i : ι) → Measure (X i)) [hμ : ∀ i, IsProbabilityMeasure (μ i)]

/-- Consider a family of probability measures. You can take their products for any fimite
subfamily. This gives a projective family of measures, see `IsProjectiveMeasureFamily`. -/
theorem isProjectiveMeasureFamily_pi :
    IsProjectiveMeasureFamily (fun I : Finset ι ↦ (Measure.pi (fun i : I ↦ μ i))) := sorry

end Preliminaries

section Nat

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
variable (μ : (n : ℕ) → Measure (X n)) [hμ : ∀ n, IsProbabilityMeasure (μ n)]

lemma mem_Iic_zero {i : ℕ} (hi : i ∈ Iic 0) : i = 0 := by simpa using hi

/-- `{0} = Ici 0`, version as a measurable equivalence for dependent functions. -/
def zer : (X 0) ≃ᵐ ((i : Iic 0) → X i) := sorry

/-- Infinite product measure indexed by `ℕ`. Use instead `Measure.productMeasure` for the case of a
general index space-/
noncomputable def Measure.infinitePiNat : Measure ((n : ℕ) → X n) := sorry

open Measure

instance {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {κ : Kernel X Y}
    [IsProbabilityMeasure μ] [IsMarkovKernel κ] : IsProbabilityMeasure (μ.bind κ) := by
  constructor
  rw [bind_apply MeasurableSet.univ (Kernel.measurable κ)]
  simp

theorem Measure.map_bind {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z]
    (μ : Measure X) (κ : Kernel X Y) (f : Y → Z) (mf : Measurable f) :
    (μ.bind κ).map f = μ.bind (Kernel.map κ f) := by
  ext s ms
  rw [Measure.map_apply mf ms, Measure.bind_apply ms (Kernel.measurable _),
    Measure.bind_apply (mf ms) (Kernel.measurable _)]
  simp_rw [Kernel.map_apply' _ mf _ ms]

theorem map_bind_eq_bind_comap {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z]
    (μ : Measure X) (κ : Kernel Y Z) (f : X → Y) (mf : Measurable f) :
    (μ.map f).bind κ = μ.bind (Kernel.comap κ f mf) := by
  ext s ms
  rw [Measure.bind_apply ms (Kernel.measurable _), lintegral_map, Measure.bind_apply ms]
  · rfl
  · exact Kernel.measurable _
  · exact Kernel.measurable_coe _ ms
  · exact mf

end Nat

section ProductMeasure

universe u
variable {ι : Type*} {X : ι → Type*}

lemma cast_pi_eval (s : Set ι) (x : (i : s) → X i) (i j : s) (h : i = j) (h' : X i = X j) :
    cast h' (x i) = x j := by
  subst h
  rfl

variable [hX : ∀ i, MeasurableSpace (X i)]
variable (μ : (i : ι) → Measure (X i)) [hμ : ∀ i, IsProbabilityMeasure (μ i)]

lemma cast_mem_cast (α β : Type u) (h : α = β) (a : α) (s : Set α) (h' : Set α = Set β) :
    (cast h a ∈ cast h' s) = (a ∈ s) := by
  subst h
  rfl

lemma HEq_meas {i j : ι} (hij : i = j) :
    HEq (inferInstance : MeasurableSpace (X i)) (inferInstance : MeasurableSpace (X j)) := by
  cases hij; rfl

/-- The product measure of an arbitrary family of probability measures. It is defined as the unique
extension of the function which gives to cylinders the measure given by the associated product
measure. -/
noncomputable def productMeasure : Measure ((i : ι) → X i) := (sorry : (∀ i, Measure (X i)) → _) μ

/-- The product measure is the projective limit of the partial product measures. This ensures
uniqueness and expresses the value of the product measures applied to cylinders. -/
theorem isProjectiveLimit_productMeasure :
    IsProjectiveLimit (productMeasure μ) (fun I : Finset ι ↦ (Measure.pi (fun i : I ↦ μ i))) :=
  sorry

instance : IsProbabilityMeasure (productMeasure μ) := sorry

theorem productMeasure_boxes {s : Finset ι} {t : (i : ι) → Set (X i)}
    (mt : ∀ i ∈ s, MeasurableSet (t i)) :
    productMeasure μ (Set.pi s t) = ∏ i ∈ s, (μ i) (t i) := sorry

theorem productMeasure_cylinder {s : Finset ι} {S : Set ((i : s) → X i)} (mS : MeasurableSet S) :
    productMeasure μ (cylinder s S) = Measure.pi (fun i : s ↦ μ i) S := sorry

theorem integral_dep_productMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Finset ι} {f : ((i : s) → X i) → E} (hf : StronglyMeasurable f) :
    ∫ y, f ((fun x (i : s) ↦ x i) y) ∂productMeasure μ =
    ∫ y, f y ∂Measure.pi (fun i : s ↦ μ i) := sorry

/-- Given a dependent function, evaluate it on a point coming from a subtype associated to a
Finset. -/
abbrev proj (s : Finset ι) (x : (i : ι) → X i) (i : s) := x i

theorem meas_proj (s : Finset ι) : Measurable (proj (X := X) s) :=
  measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)

/-- The canonical filtration on dependent functions indexed by ι, where `𝓕 s` consists of
measurable sets depending only on coordinates is `s`. -/
def ℱ : @Filtration ((i : ι) → X i) (Finset ι) _ inferInstance where
  seq s := (inferInstance : MeasurableSpace ((i : s) → X i)).comap (proj s)
  mono' s t hst := sorry
  le' s := (meas_proj s).comap_le

theorem integral_stronglyMeasurable [DecidableEq ι] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {s : Finset ι} {f : ((i : ι) → X i) → E}
    (mf : @StronglyMeasurable _ _ _ (ℱ s) f) (x : (i : ι) → X i) :
    ∫ y, f y ∂productMeasure μ =
    ∫ y, f (Function.updateFinset x s y) ∂Measure.pi (fun i : s ↦ μ i) := sorry

theorem lintegral_dep {s : Finset ι} {f : ((i : s) → X i) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f ((fun x (i : s) ↦ x i) y) ∂productMeasure μ =
    ∫⁻ y, f y∂Measure.pi (fun i : s ↦ μ i) := sorry

theorem lintegral_measurable [DecidableEq ι] {s : Finset ι}
    {f : ((i : ι) → X i) → ℝ≥0∞} (mf : @Measurable _ _ (ℱ s) _ f)
    (x : (i : ι) → X i) : ∫⁻ y, f y ∂productMeasure μ = (∫⋯∫⁻_s, f ∂μ) x := sorry

end ProductMeasure
end MeasureTheory
