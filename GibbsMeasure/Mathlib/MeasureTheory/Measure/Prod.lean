import Mathlib.MeasureTheory.Measure.Prod

namespace MeasureTheory.Measure
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

open Set

omit [MeasurableSpace X] [MeasurableSpace Y] in
private lemma preimage_fst_prod {X Y} (s : Set X) :
  (Prod.fst : X × Y → X) ⁻¹' s = s ×ˢ (univ : Set Y) := by
  ext p; rcases p with ⟨x, y⟩
  simp [Set.mem_preimage, Set.mem_prod]

omit [MeasurableSpace X] [MeasurableSpace Y] in
private lemma preimage_snd_prod {X Y} (t : Set Y) :
  (Prod.snd : X × Y → Y) ⁻¹' t = (univ : Set X) ×ˢ t := by
  ext p; rcases p with ⟨x, y⟩
  simp [Set.mem_preimage, Set.mem_prod]

section

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
open Set

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
    (Measure.map Prod.fst μ) univ = 1 := by
  have hμ := measure_univ_of_marg_snd_dirac (μ := μ) (y := y) marg_Y
  simp [Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ, hμ]

lemma map_snd_univ_of_marg_fst_dirac
    (μ : Measure (X × Y)) (x : X)
    (marg_X : Measure.map Prod.fst μ = Measure.dirac x) :
    (Measure.map Prod.snd μ) univ = 1 := by
  have hμ := measure_univ_of_marg_fst_dirac (μ := μ) (x := x) marg_X
  simp [Measure.map_apply measurable_snd MeasurableSet.univ, preimage_univ, hμ]

lemma isFinite_map_fst_of_marg_snd_dirac
    (μ : Measure (X × Y)) (y : Y)
    (marg_Y : Measure.map Prod.snd μ = Measure.dirac y) :
    IsFiniteMeasure (Measure.map Prod.fst μ) :=
  ⟨by simp [map_fst_univ_of_marg_snd_dirac (μ := μ) (y := y) marg_Y]⟩

lemma isFinite_map_snd_of_marg_fst_dirac
    (μ : Measure (X × Y)) (x : X)
    (marg_X : Measure.map Prod.fst μ = Measure.dirac x) :
    IsFiniteMeasure (Measure.map Prod.snd μ) :=
  ⟨by simp [map_snd_univ_of_marg_fst_dirac (μ := μ) (x := x) marg_X]⟩

-- Rectangle formula from a Dirac marginal on the right
lemma rect_of_marg_snd_dirac
    (μ : Measure (X × Y)) (y : Y)
    (marg_Y : Measure.map Prod.snd μ = Measure.dirac y) :
    ∀ s t, MeasurableSet s → MeasurableSet t →
      μ (s ×ˢ t) = (Measure.map Prod.fst μ) s * (Measure.dirac y) t := by
  classical
  intro s t hs ht
  by_cases hyt : y ∈ t
  · have h_univ_tcompl_zero : μ (univ ×ˢ tᶜ) = 0 := by
      have h' := congrArg (fun m : Measure Y => m (tᶜ)) marg_Y
      have hy_not : y ∉ tᶜ := by simpa using hyt
      have hdirac : (Measure.dirac y) (tᶜ) = 0 := by
        rw [← marg_Y]; rw [marg_Y]; rw [← marg_Y]; aesop
      have : μ (Prod.snd ⁻¹' (tᶜ)) = 0 := by
        simpa [Measure.map_apply measurable_snd ht.compl, hdirac] using h'
      simpa only [preimage_snd_prod] using this
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
    have : μ (s ×ˢ t) = (Measure.map Prod.fst μ) s := by
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
      simpa [preimage_snd_prod] using this
    have h_st_zero : μ (s ×ˢ t) = 0 := by
      refine measure_mono_null ?_ h_univ_t_zero
      exact prod_mono (fun ⦃a⦄ a ↦ trivial) fun ⦃a⦄ a ↦ a
    aesop

lemma eq_prod_of_marg_snd_dirac
    (μ : Measure (X × Y)) (y : Y)
    (marg_Y : Measure.map Prod.snd μ = Measure.dirac y) :
    μ = (Measure.map Prod.fst μ).prod (Measure.dirac y) := by
  classical
  have hμ_univ : μ univ = 1 := measure_univ_of_marg_snd_dirac (μ := μ) (y := y) marg_Y
  have hνX_univ : (Measure.map Prod.fst μ) univ = 1 := by
    simp [Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ, hμ_univ]
  haveI : IsFiniteMeasure (Measure.map Prod.fst μ) := ⟨by simp [hνX_univ]⟩
  haveI : SigmaFinite (Measure.map Prod.fst μ) := by infer_instance
  haveI : IsFiniteMeasure (Measure.dirac y) := ⟨by simp⟩
  haveI : SigmaFinite (Measure.dirac y) := by infer_instance
  have hrect := rect_of_marg_snd_dirac (μ := μ) (y := y) marg_Y
  have hprod := (Measure.prod_eq
    (μ := Measure.map Prod.fst μ) (ν := Measure.dirac y) (μν := μ) hrect)
  simpa using hprod.symm

lemma eq_mapMk_of_marg_snd_dirac
    (μ : Measure (X × Y)) (y : Y)
    (marg_Y : Measure.map Prod.snd μ = Measure.dirac y) :
    μ = Measure.map (fun x : X => (x, y)) (Measure.map Prod.fst μ) := by
  haveI : IsFiniteMeasure (Measure.map Prod.fst μ) :=
    isFinite_map_fst_of_marg_snd_dirac (μ := μ) (y := y) marg_Y
  haveI : SigmaFinite (Measure.map Prod.fst μ) := by infer_instance
  haveI : IsFiniteMeasure (Measure.dirac y) := by infer_instance
  haveI : SigmaFinite (Measure.dirac y) := by infer_instance
  have h := eq_prod_of_marg_snd_dirac (μ := μ) (y := y) marg_Y
  simpa [Measure.prod_dirac] using h

lemma eq_prod_of_marg_fst_dirac
    (μ : Measure (X × Y)) (x : X)
    (marg_X : Measure.map Prod.fst μ = Measure.dirac x) :
    μ = (Measure.dirac x).prod (Measure.map Prod.snd μ) := by
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
  haveI : SigmaFinite (Measure.map Prod.snd μ) := by infer_instance
  haveI : IsFiniteMeasure (Measure.dirac x) := by infer_instance
  haveI : SigmaFinite (Measure.dirac x) := by infer_instance
  have hswap := Measure.prod_swap (μ := Measure.map Prod.snd μ) (ν := Measure.dirac x)
  calc
    μ = Measure.map Prod.swap ((Measure.map Prod.snd μ).prod (Measure.dirac x)) := h''
    _ = (Measure.dirac x).prod (Measure.map Prod.snd μ) := by
      simpa using hswap

lemma eq_mapMk_of_marg_fst_dirac
    (μ : Measure (X × Y)) (x : X)
    (marg_X : Measure.map Prod.fst μ = Measure.dirac x) :
    μ = Measure.map (fun y : Y => (x, y)) (Measure.map Prod.snd μ) := by
  have h := eq_prod_of_marg_fst_dirac (μ := μ) (x := x) marg_X
  haveI : IsFiniteMeasure (Measure.map Prod.snd μ) :=
    isFinite_map_snd_of_marg_fst_dirac (μ := μ) (x := x) marg_X
  haveI : SigmaFinite (Measure.map Prod.snd μ) := by infer_instance
  haveI : IsFiniteMeasure (Measure.dirac x) := by infer_instance
  haveI : SigmaFinite (Measure.dirac x) := by infer_instance
  have hm :
      (Measure.dirac x).prod (Measure.map Prod.snd μ)
        = Measure.map (fun y : Y => (x, y)) (Measure.map Prod.snd μ) := by
    simpa using (Measure.dirac_prod (x := x) (ν := Measure.map Prod.snd μ))
  exact h.trans hm

lemma eq_prod_of_dirac_right
    (ν : Measure X) (y : Y) (μ : Measure (X × Y))
    (marg_X : Measure.map Prod.fst μ = ν)
    (marg_Y : Measure.map Prod.snd μ = Measure.dirac y) :
    μ = ν.prod (Measure.dirac y) := by
  simpa [marg_X] using
    (eq_prod_of_marg_snd_dirac (μ := μ) (y := y) marg_Y)

lemma eq_prod_of_dirac_left
    (x : X) (ν : Measure Y) (μ : Measure (X × Y))
    (marg_X : Measure.map Prod.fst μ = Measure.dirac x)
    (marg_Y : Measure.map Prod.snd μ = ν) :
    μ = (Measure.dirac x).prod ν := by
  simpa [marg_Y] using
    (eq_prod_of_marg_fst_dirac (μ := μ) (x := x) marg_X)

lemma eq_mapMk_of_dirac_right
    (ν : Measure X) (y : Y) (μ : Measure (X × Y))
    (marg_X : Measure.map Prod.fst μ = ν)
    (marg_Y : Measure.map Prod.snd μ = Measure.dirac y) :
    μ = Measure.map (fun x : X => (x, y)) ν := by
  haveI : IsFiniteMeasure (Measure.map Prod.fst μ) :=
    isFinite_map_fst_of_marg_snd_dirac (μ := μ) (y := y) marg_Y
  haveI : SigmaFinite (Measure.map Prod.fst μ) := by infer_instance
  simpa [marg_X] using
    (eq_mapMk_of_marg_snd_dirac (μ := μ) (y := y) marg_Y)

lemma eq_mapMk_of_dirac_left
    (x : X) (ν : Measure Y) (μ : Measure (X × Y))
    (marg_X : Measure.map Prod.fst μ = Measure.dirac x)
    (marg_Y : Measure.map Prod.snd μ = ν) :
    μ = Measure.map (fun y : Y => (x, y)) ν := by
  haveI : IsFiniteMeasure (Measure.map Prod.snd μ) :=
    isFinite_map_snd_of_marg_fst_dirac (μ := μ) (x := x) marg_X
  haveI : SigmaFinite (Measure.map Prod.snd μ) := by infer_instance
  simpa [marg_Y] using
    (eq_mapMk_of_marg_fst_dirac (μ := μ) (x := x) marg_X)

end

end MeasureTheory.Measure
