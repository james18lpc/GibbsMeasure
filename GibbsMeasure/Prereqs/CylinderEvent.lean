import Mathlib.MeasureTheory.MeasurableSpace.Basic

/-!
# CylindricalEvents
-/

open Function Set
open MeasureTheory

variable {α ι : Type*} {π : ι → Type*} {mα : MeasurableSpace α} [m : ∀ i, MeasurableSpace (π i)]
  {Δ Δ₁ Δ₂ : Set ι} {i : ι}

/-- The σ-algebra of cylindrical events on `Δ`. It is the smallest σ-algebra making by the -/
def cylinderEvents (Δ : Set ι) : MeasurableSpace (∀ i, π i) := ⨆ i ∈ Δ, (m i).comap fun σ ↦ σ i

@[simp] lemma cylinderEvents_univ : cylinderEvents (π := π) univ = MeasurableSpace.pi := by
  simp [cylinderEvents, MeasurableSpace.pi]

@[gcongr]
lemma cylinderEvents_mono (h : Δ₁ ⊆ Δ₂) : cylinderEvents (π := π) Δ₁ ≤ cylinderEvents Δ₂ :=
  biSup_mono h

lemma cylinderEvents_le_pi : cylinderEvents (π := π) Δ ≤ MeasurableSpace.pi := by
  simpa using cylinderEvents_mono (subset_univ _)

lemma measurable_cylinderEvents_iff {g : α → ∀ i, π i} :
    @Measurable _ _ _ (cylinderEvents Δ) g ↔ ∀ ⦃i⦄, i ∈ Δ → Measurable fun a ↦ g a i := by
  simp_rw [measurable_iff_comap_le, cylinderEvents, MeasurableSpace.comap_iSup,
    MeasurableSpace.comap_comp, Function.comp_def, iSup_le_iff]

@[fun_prop, aesop safe 100 apply (rule_sets := [Measurable])]
lemma measurable_cylinderEvent_apply (hi : i ∈ Δ) :
    Measurable[cylinderEvents Δ] fun f : ∀ i, π i => f i :=
  measurable_cylinderEvents_iff.1 measurable_id hi

@[aesop safe 100 apply (rule_sets := [Measurable])]
lemma Measurable.eval_cylinderEvents {g : α → ∀ i, π i} (hi : i ∈ Δ)
    (hg : @Measurable _ _ _ (cylinderEvents Δ) g) : Measurable fun a ↦ g a i :=
  (measurable_cylinderEvent_apply hi).comp hg

@[fun_prop, aesop safe 100 apply (rule_sets := [Measurable])]
lemma measurable_cylinderEvents_lambda (f : α → ∀ i, π i) (hf : ∀ i, Measurable fun a ↦ f a i) :
    Measurable f :=
  measurable_pi_iff.mpr hf

/-- The function `(f, x) ↦ update f a x : (Π a, π a) × π a → Π a, π a` is measurable. -/
lemma measurable_update_cylinderEvents' [DecidableEq ι] :
    @Measurable _ _ (.prod (cylinderEvents Δ) (m i)) (cylinderEvents Δ)
      (fun p : (∀ i, π i) × π i ↦ update p.1 i p.2) := by
  rw [measurable_cylinderEvents_iff]
  intro j hj
  dsimp [update]
  split_ifs with h
  · subst h
    dsimp
    exact measurable_snd
  · exact measurable_cylinderEvents_iff.1 measurable_fst hj

lemma measurable_uniqueElim_cylinderEvents [Unique ι] [∀ i, MeasurableSpace (π i)] :
    Measurable (uniqueElim : π (default : ι) → ∀ i, π i) := by
  simp_rw [measurable_pi_iff, Unique.forall_iff, uniqueElim_default]; exact measurable_id

/-- The function `update f a : π a → Π a, π a` is always measurable.
This doesn't require `f` to be measurable.
This should not be confused with the statement that `update f a x` is measurable. -/
@[measurability]
lemma measurable_update_cylinderEvents (f : ∀ a : ι, π a) {a : ι} [DecidableEq ι] :
    @Measurable _ _ _ (cylinderEvents Δ) (update f a) :=
  measurable_update_cylinderEvents'.comp measurable_prod_mk_left

lemma measurable_update_cylinderEvents_left {a : ι} [DecidableEq ι] {x : π a} :
    @Measurable _ _ (cylinderEvents Δ) (cylinderEvents Δ) (update · a x) :=
  measurable_update_cylinderEvents'.comp measurable_prod_mk_right

lemma measurable_restrict_cylinderEvents (Δ : Set ι) :
    Measurable[cylinderEvents (π := π) Δ] (restrict Δ) := by
  rw [@measurable_pi_iff]; exact fun i ↦ measurable_cylinderEvent_apply i.2
