import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.HasLaw

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

open Set
namespace ProbabilityTheory
open MeasureTheory

-- General facts: the total mass of P equals the total mass of the law μ.
section
variable {Ω 𝓧 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝓧]
variable {P : Measure Ω} {μ : Measure 𝓧} {X : Ω → 𝓧} {x : 𝓧}

/-- If `X` has law `μ` under `P`, then `P univ = μ univ`. -/
lemma HasLaw.measure_univ_eq (h : ProbabilityTheory.HasLaw X μ P) : P univ = μ univ := by
  have hmap_congr :
      P.map X = P.map (h.aemeasurable.mk X) := Measure.map_congr h.aemeasurable.ae_eq_mk
  have hmap_univ :
      (P.map (h.aemeasurable.mk X)) univ = P univ := by
    simp [Measure.map_apply h.aemeasurable.measurable_mk MeasurableSet.univ, preimage_univ]
  have hmapX_univ : (P.map X) univ = P univ := by
    simpa using (congrArg (fun m => m univ) hmap_congr).trans hmap_univ
  simpa [h.map_eq] using hmapX_univ.symm

/-- If `X` has Dirac law under `P`, then `P` has total mass `1`. -/
lemma HasLaw.measure_univ_of_dirac (h : ProbabilityTheory.HasLaw X
    (Measure.dirac x) P) : P univ = 1 := by
  have hx : (Measure.dirac x) univ = 1 := by simp
  simpa [hx] using h.measure_univ_eq

end
end ProbabilityTheory

namespace MeasureTheory.Measure

section

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
open Set ProbabilityTheory

-- Total mass from a Dirac marginal
lemma measure_univ_of_marg_snd_dirac
    (μ : Measure (X × Y)) (y : Y)
    (marg_Y : Measure.map Prod.snd μ = Measure.dirac y) :
    μ univ = 1 := by
  have h := congrArg (fun m : Measure Y => m univ) marg_Y
  simpa [Measure.map_apply measurable_snd MeasurableSet.univ, preimage_univ] using h

lemma measure_univ_of_marg_fst_dirac
    (μ : Measure (X × Y)) (x : X)
    (marg_X : Measure.map Prod.fst μ = Measure.dirac x) :
    μ univ = 1 := by
  have h := congrArg (fun m : Measure X => m univ) marg_X
  simpa [Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ] using h

-- New: total mass of the non-Dirac marginal and finiteness
lemma map_fst_univ_of_marg_snd_dirac
    (μ : Measure (X × Y)) (y : Y)
    (marg_Y : Measure.map Prod.snd μ = Measure.dirac y) :
    μ.map Prod.fst univ = 1 := by
  have hμ := measure_univ_of_marg_snd_dirac (μ := μ) (y := y) marg_Y
  simp [Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ, hμ]

lemma map_snd_univ_of_marg_fst_dirac
    (μ : Measure (X × Y)) (x : X)
    (marg_X : μ.map Prod.fst = Measure.dirac x) :
    μ.map Prod.snd univ = 1 := by
  have hμ := measure_univ_of_marg_fst_dirac (μ := μ) (x := x) marg_X
  simp [Measure.map_apply measurable_snd MeasurableSet.univ, preimage_univ, hμ]

lemma isFinite_map_fst_of_marg_snd_dirac
    (μ : Measure (X × Y)) (y : Y)
    (marg_Y : μ.map Prod.snd = Measure.dirac y) :
    IsFiniteMeasure (μ.map Prod.fst) :=
  ⟨by simp [map_fst_univ_of_marg_snd_dirac (μ := μ) (y := y) marg_Y]⟩

lemma isFinite_map_snd_of_marg_fst_dirac
    (μ : Measure (X × Y)) (x : X)
    (marg_X : μ.map Prod.fst = Measure.dirac x) :
    IsFiniteMeasure (Measure.map Prod.snd μ) :=
  ⟨by simp [map_snd_univ_of_marg_fst_dirac (μ := μ) (x := x) marg_X]⟩

-- Rectangle formula from a Dirac marginal on the right
lemma rect_of_marg_snd_dirac
    (μ : Measure (X × Y)) (y : Y)
    (marg_Y : μ.map Prod.snd = Measure.dirac y) :
    ∀ s t, MeasurableSet s → MeasurableSet t →
      μ (s ×ˢ t) = (μ.map Prod.fst) s * (Measure.dirac y) t := by
  intro s t hs ht
  by_cases hyt : y ∈ t
  · have h_univ_tcompl_zero : μ (univ ×ˢ tᶜ) = 0 := by
      have h' := congrArg (fun m : Measure Y => m (tᶜ)) marg_Y
      have hy_not : y ∉ tᶜ := by simpa using hyt
      have hdirac : (Measure.dirac y) (tᶜ) = 0 := by
        rw [← marg_Y]; rw [marg_Y]; rw [← marg_Y]; aesop
      have : μ (Prod.snd ⁻¹' (tᶜ)) = 0 := by
        simpa [Measure.map_apply measurable_snd ht.compl, hdirac] using h'
      simpa only [Set.univ_prod] using this
    have h_stcompl_zero : μ (s ×ˢ tᶜ) = 0 := by
      refine measure_mono_null ?_ h_univ_tcompl_zero
      exact prod_mono (fun ⦃a⦄ a ↦ trivial) fun ⦃a⦄ a ↦ a
    have h_disj : Disjoint (s ×ˢ t) (s ×ˢ tᶜ) := by
      refine disjoint_left.mpr ?_
      intro p hp1 hp2; rcases p with ⟨x, z⟩
      rcases hp1 with ⟨_, hz⟩; rcases hp2 with ⟨_, hz'⟩; exact hz' hz
    have h_union :
        μ ((s ×ˢ t) ∪ (s ×ˢ tᶜ)) = μ (s ×ˢ t) + μ (s ×ˢ tᶜ) := by
      have hst : MeasurableSet (s ×ˢ t) := hs.prod ht
      have hstc : MeasurableSet (s ×ˢ tᶜ) := hs.prod ht.compl
      exact measure_union h_disj hstc
    have h_s_univ_eq :
        μ (Prod.fst ⁻¹' s) = μ (s ×ˢ t) + μ (s ×ˢ tᶜ) := by
      rw [← prod_union, union_compl_self, prod_univ] at h_union
      exact h_union
    have h_s_univ_eq' : μ (s ×ˢ t) = μ (Prod.fst ⁻¹' s) := by
      simp [h_s_univ_eq, h_stcompl_zero, add_comm]
    have : μ (s ×ˢ t) = (μ.map Prod.fst) s := by
      have h_map : μ (Prod.fst ⁻¹' s) = (Measure.map Prod.fst μ) s := by
        rw [Measure.map_apply measurable_fst hs]
      exact h_s_univ_eq'.trans h_map
    simpa [Measure.dirac_apply_of_mem hyt, mul_one] using this
  · have h_univ_t_zero : μ (univ ×ˢ t) = 0 := by
      have h' := congrArg (fun m : Measure Y => m t) marg_Y
      have hdirac : (Measure.dirac y) t = 0 := by
        exact (dirac_eq_zero_iff_not_mem ht).mpr hyt
      have : μ (Prod.snd ⁻¹' t) = 0 := by
        simpa [Measure.map_apply measurable_snd ht, hdirac] using h'
      simpa [Set.univ_prod] using this
    have h_st_zero : μ (s ×ˢ t) = 0 := by
      refine measure_mono_null ?_ h_univ_t_zero
      exact prod_mono (fun ⦃a⦄ a ↦ trivial) fun ⦃a⦄ a ↦ a
    aesop

lemma eq_prod_of_marg_snd_dirac
    (μ : Measure (X × Y)) (y : Y)
    (marg_Y : μ.map Prod.snd = Measure.dirac y) :
    μ = (μ.map Prod.fst).prod (Measure.dirac y) := by
  have hμ_univ : μ univ = 1 := measure_univ_of_marg_snd_dirac (μ := μ) (y := y) marg_Y
  have hνX_univ : (μ.map Prod.fst) univ = 1 := by
    simp [Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ, hμ_univ]
  haveI : IsFiniteMeasure (μ.map Prod.fst) := ⟨by simp [hνX_univ]⟩
  haveI : SigmaFinite (μ.map Prod.fst) := by infer_instance
  haveI : IsFiniteMeasure (Measure.dirac y) := ⟨by simp⟩
  haveI : SigmaFinite (Measure.dirac y) := by infer_instance
  have hrect := rect_of_marg_snd_dirac (μ := μ) (y := y) marg_Y
  have hprod := (Measure.prod_eq
    (μ := μ.map Prod.fst) (ν := Measure.dirac y) (μν := μ) hrect)
  simpa using hprod.symm

-- Factorization as a pushforward from the first marginal
lemma eq_mapMk_of_marg_snd_dirac
    (μ : Measure (X × Y)) (y : Y)
    (marg_Y : μ.map Prod.snd = Measure.dirac y) :
    μ = Measure.map (fun x : X => (x, y)) (μ.map Prod.fst) := by
  have h := eq_prod_of_marg_snd_dirac (μ := μ) (y := y) marg_Y
  haveI : IsFiniteMeasure (Measure.map Prod.fst μ) :=
    isFinite_map_fst_of_marg_snd_dirac (μ := μ) (y := y) marg_Y
  haveI : SigmaFinite (Measure.map Prod.fst μ) := by infer_instance
  haveI : IsFiniteMeasure (Measure.dirac y) := by infer_instance
  haveI : SigmaFinite (Measure.dirac y) := by infer_instance
  have hm :
      (μ.map Prod.fst).prod (Measure.dirac y)
        = Measure.map (fun x : X => (x, y)) (μ.map Prod.fst) := by
    simpa using (Measure.prod_dirac (μ := μ.map Prod.fst) (y := y))
  exact h.trans hm

/-- If a random variable has Dirac law, then the joint measure factors as a pushforward -/
lemma HasLaw.eq_map_mk_of_dirac {P : Measure (X × Y)} {y : Y}
    (h : ProbabilityTheory.HasLaw (Prod.snd : X × Y → Y) (Measure.dirac y) P) :
    P = Measure.map (fun x => (x, y)) (P.map Prod.fst) := by
  simpa [h.map_eq] using
    (eq_mapMk_of_marg_snd_dirac (μ := P) (y := y) (marg_Y := h.map_eq))

lemma eq_prod_of_marg_fst_dirac
    (μ : Measure (X × Y)) (x : X)
    (marg_X : μ.map Prod.fst = Measure.dirac x) :
    μ = (Measure.dirac x).prod (μ.map Prod.snd) := by
  classical
  have h_swap_eq : Measure.map Prod.snd (Measure.map Prod.swap μ) = Measure.dirac x := by
    simpa [Measure.snd, Measure.fst, marg_X] using (Measure.snd_map_swap (ρ := μ))
  have h := eq_prod_of_marg_snd_dirac (μ := Measure.map Prod.swap μ) (y := x) h_swap_eq
  have h_fst_swap : Measure.map Prod.fst (Measure.map Prod.swap μ) = Measure.map Prod.snd μ := by
    simpa [Measure.fst, Measure.snd] using (Measure.fst_map_swap (ρ := μ))
  have h' : Measure.map Prod.swap μ = (Measure.map Prod.snd μ).prod (Measure.dirac x) := by
    simpa [h_fst_swap] using h
  have h'' : μ = Measure.map Prod.swap ((Measure.map Prod.snd μ).prod (Measure.dirac x)) := by
    have := congrArg (fun m => Measure.map Prod.swap m) h'
    simpa [Measure.map_map measurable_swap measurable_swap, Function.comp,
      Prod.swap_swap, Measure.map_id] using this
  haveI : IsFiniteMeasure (Measure.map Prod.snd μ) :=
    isFinite_map_snd_of_marg_fst_dirac (μ := μ) (x := x) marg_X
  haveI : SigmaFinite (μ.map Prod.snd) := by infer_instance
  haveI : IsFiniteMeasure (Measure.dirac x) := by infer_instance
  haveI : SigmaFinite (Measure.dirac x) := by infer_instance
  have hswap := Measure.prod_swap (μ := Measure.map Prod.snd μ) (ν := Measure.dirac x)
  calc
    μ = Measure.map Prod.swap ((Measure.map Prod.snd μ).prod (Measure.dirac x)) := h''
    _ = (Measure.dirac x).prod (Measure.map Prod.snd μ) := by
      simpa using hswap

lemma eq_mapMk_of_marg_fst_dirac
    (μ : Measure (X × Y)) (x : X)
    (marg_X : μ.map Prod.fst = Measure.dirac x) :
    μ = Measure.map (fun y : Y => (x, y)) (μ.map Prod.snd) := by
  have h := eq_prod_of_marg_fst_dirac (μ := μ) (x := x) marg_X
  haveI : IsFiniteMeasure (μ.map Prod.snd) :=
    isFinite_map_snd_of_marg_fst_dirac (μ := μ) (x := x) marg_X
  haveI : SigmaFinite (μ.map Prod.snd) := by infer_instance
  haveI : IsFiniteMeasure (Measure.dirac x) := by infer_instance
  haveI : SigmaFinite (Measure.dirac x) := by infer_instance
  have hm :
      (Measure.dirac x).prod (μ.map Prod.snd)
        = Measure.map (fun y : Y => (x, y)) (μ.map Prod.snd) := by
    simpa using (Measure.dirac_prod (x := x) (ν := μ.map Prod.snd))
  exact h.trans hm

lemma eq_prod_of_dirac_right
    (ν : Measure X) (y : Y) (μ : Measure (X × Y))
    (marg_X : μ.map Prod.fst = ν)
    (marg_Y : μ.map Prod.snd = Measure.dirac y) :
    μ = ν.prod (Measure.dirac y) := by
  simpa [marg_X] using
    eq_prod_of_marg_snd_dirac (μ := μ) (y := y) marg_Y

lemma eq_prod_of_dirac_left
    (x : X) (ν : Measure Y) (μ : Measure (X × Y))
    (marg_X : μ.map Prod.fst = Measure.dirac x)
    (marg_Y : μ.map Prod.snd = ν) :
    μ = (Measure.dirac x).prod ν := by
  simpa [marg_Y] using
    eq_prod_of_marg_fst_dirac (μ := μ) (x := x) marg_X

lemma eq_mapMk_of_dirac_right
    (ν : Measure X) (y : Y) (μ : Measure (X × Y))
    (marg_X : μ.map Prod.fst = ν)
    (marg_Y : μ.map Prod.snd = Measure.dirac y) :
    μ = Measure.map (fun x : X => (x, y)) ν := by
  haveI : IsFiniteMeasure (μ.map Prod.fst) :=
    isFinite_map_fst_of_marg_snd_dirac (μ := μ) (y := y) marg_Y
  haveI : SigmaFinite (μ.map Prod.fst) := by infer_instance
  simpa [marg_X] using
    eq_mapMk_of_marg_snd_dirac (μ := μ) (y := y) marg_Y

lemma eq_mapMk_of_dirac_left
    (x : X) (ν : Measure Y) (μ : Measure (X × Y))
    (marg_X : μ.map Prod.fst = Measure.dirac x)
    (marg_Y : μ.map Prod.snd = ν) :
    μ = Measure.map (fun y : Y => (x, y)) ν := by
  haveI : IsFiniteMeasure (μ.map Prod.snd) :=
    isFinite_map_snd_of_marg_fst_dirac (μ := μ) (x := x) marg_X
  haveI : SigmaFinite (μ.map Prod.snd) := by infer_instance
  simpa [marg_Y] using
    eq_mapMk_of_marg_fst_dirac (μ := μ) (x := x) marg_X

end

namespace ProbabilityTheory
open MeasureTheory

section
variable {Ω X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
variable {P : Measure Ω} {Xf : Ω → X} {Yf : Ω → Y} {μX : Measure X} {μY : Measure Y} {y : Y} {x : X}

/-- If the second coordinate has Dirac law, the joint law is the pushforward of the first law. -/
lemma law_pair_eq_map_mk_of_snd_dirac
    (hX : ProbabilityTheory.HasLaw Xf μX P) (hY : ProbabilityTheory.HasLaw Yf (Measure.dirac y) P) :
    P.map (fun ω => (Xf ω, Yf ω)) = Measure.map (fun x : X => (x, y)) μX := by
  set μ := Measure.map (fun ω => (Xf ω, Yf ω)) P
  have hpair_ae : AEMeasurable (fun ω => (Xf ω, Yf ω)) P :=
    hX.aemeasurable.prodMk hY.aemeasurable
  have hmap_snd :=
    (AEMeasurable.map_map_of_aemeasurable (μ := P)
      (g := Prod.snd) (f := fun ω => (Xf ω, Yf ω))
      (measurable_snd.aemeasurable) hpair_ae)
  have hcomp_snd : (Prod.snd ∘ fun ω => (Xf ω, Yf ω)) = Yf := by
    funext ω; simp
  have margY : μ.map Prod.snd = Measure.dirac y := by
    simpa [μ, hcomp_snd, hY.map_eq] using hmap_snd
  have hmap_fst :=
    (AEMeasurable.map_map_of_aemeasurable (μ := P)
      (g := Prod.fst) (f := fun ω => (Xf ω, Yf ω))
      (measurable_fst.aemeasurable) hpair_ae)
  have hcomp_fst : (Prod.fst ∘ fun ω => (Xf ω, Yf ω)) = Xf := by
    funext ω; simp
  have margX : μ.map Prod.fst = P.map Xf := by
    simpa [μ, hcomp_fst] using hmap_fst
  have hμ :=
    MeasureTheory.Measure.eq_mapMk_of_marg_snd_dirac (μ := μ) (y := y) (marg_Y := margY)
  simpa [μ, margX, hX.map_eq] using hμ

/-- Symmetric version: if the first coordinate has Dirac law, the joint law is a pushforward
from the second law. -/
lemma law_pair_eq_map_mk_of_fst_dirac
    (hY : ProbabilityTheory.HasLaw Yf μY P) (hX : ProbabilityTheory.HasLaw Xf (Measure.dirac x) P) :
    P.map (fun ω => (Xf ω, Yf ω)) = Measure.map (fun z : Y => (x, z)) μY := by
  set μ := Measure.map (fun ω => (Xf ω, Yf ω)) P
  have hpair_ae : AEMeasurable (fun ω => (Xf ω, Yf ω)) P :=
    hX.aemeasurable.prodMk hY.aemeasurable
  have hmap_fst :=
    (AEMeasurable.map_map_of_aemeasurable (μ := P)
      (g := Prod.fst) (f := fun ω => (Xf ω, Yf ω))
      (measurable_fst.aemeasurable) hpair_ae)
  have hcomp_fst : (Prod.fst ∘ fun ω => (Xf ω, Yf ω)) = Xf := by
    funext ω; simp
  have margX : μ.map Prod.fst = Measure.dirac x := by
    simpa [μ, hcomp_fst, hX.map_eq] using hmap_fst
  have hmap_snd :=
    (AEMeasurable.map_map_of_aemeasurable (μ := P)
      (g := Prod.snd) (f := fun ω => (Xf ω, Yf ω))
      (measurable_snd.aemeasurable) hpair_ae)
  have hcomp_snd : (Prod.snd ∘ fun ω => (Xf ω, Yf ω)) = Yf := by
    funext ω; simp
  have margY' : μ.map Prod.snd = P.map Yf := by
    simpa [μ, hcomp_snd] using hmap_snd
  have hμ :=
    MeasureTheory.Measure.eq_mapMk_of_marg_fst_dirac (μ := μ) (x := x) (marg_X := margX)
  simpa [μ, margY', hY.map_eq] using hμ
end
section
variable {Ω X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
variable {P : Measure Ω} {Xf : Ω → X} {Yf : Ω → Y} {μX : Measure X} {μY : Measure Y} {y : Y} {x : X}

/-- HasLaw formulation: if `Yf` has Dirac law, then the pair has law given by pushing `μX`
through `(x ↦ (x,y))`. -/
lemma HasLaw.pair_of_snd_dirac
    (hX : ProbabilityTheory.HasLaw Xf μX P)
    (hY : ProbabilityTheory.HasLaw Yf (Measure.dirac y) P) :
    ProbabilityTheory.HasLaw (fun ω => (Xf ω, Yf ω))
      (Measure.map (fun x : X => (x, y)) μX) P := by
  refine ⟨hX.aemeasurable.prodMk hY.aemeasurable, ?_⟩
  simpa using
    law_pair_eq_map_mk_of_snd_dirac (Xf := Xf) (Yf := Yf) (μX := μX) (y := y) hX hY

/-- Symmetric HasLaw formulation: if `Xf` has Dirac law, then the pair’s law is the pushforward
of `μY` through `(z ↦ (x,z))`. -/
lemma HasLaw.pair_of_fst_dirac
    (hY : ProbabilityTheory.HasLaw Yf μY P)
    (hX : ProbabilityTheory.HasLaw Xf (Measure.dirac x) P) :
    ProbabilityTheory.HasLaw (fun ω => (Xf ω, Yf ω))
      (Measure.map (fun z : Y => (x, z)) μY) P := by
  refine ⟨hX.aemeasurable.prodMk hY.aemeasurable, ?_⟩
  simpa using
    law_pair_eq_map_mk_of_fst_dirac (Xf := Xf) (Yf := Yf) (μY := μY) (x := x) hY hX

end
end ProbabilityTheory
end Measure
end MeasureTheory
