import Mathlib.MeasureTheory.Function.SimpleFunc

open MeasureTheory MeasureTheory.SimpleFunc Function Set
open scoped ENNReal

local infixr:25 " →ₛ " => SimpleFunc

namespace MeasureTheory
variable {α β γ : Type*} {mα : MeasurableSpace α} {μ : Measure α}

open scoped Classical

namespace SimpleFunc
section piecewise
variable [Preorder β] {s : Set α} {f f₁ f₂ g g₁ g₂ : α →ₛ β} {hs : MeasurableSet s}

-- TODO: Replace in mathlib
@[norm_cast] alias coe_le_coe := coe_le

@[simp, norm_cast] lemma coe_lt_coe : ⇑f < g ↔ f < g := Iff.rfl

@[simp] lemma mk_le_mk {f g : α → β} {hf hg hf' hg'} : mk f hf hf' ≤ mk g hg hg' ↔ f ≤ g := Iff.rfl
@[simp] lemma mk_lt_mk {f g : α → β} {hf hg hf' hg'} : mk f hf hf' < mk g hg hg' ↔ f < g := Iff.rfl

@[gcongr] protected alias ⟨_, GCongr.mk_le_mk⟩ := mk_le_mk
@[gcongr] protected alias ⟨_, GCongr.mk_lt_mk⟩ := mk_lt_mk
@[gcongr] protected alias ⟨_, GCongr.coe_le_coe⟩ := coe_le_coe
@[gcongr] protected alias ⟨_, GCongr.coe_lt_coe⟩ := coe_lt_coe

@[gcongr]
lemma piecewise_mono (hf : ∀ a ∈ s, f₁ a ≤ f₂ a) (hg : ∀ a ∉ s, g₁ a ≤ g₂ a) :
    piecewise s hs f₁ g₁ ≤ piecewise s hs f₂ g₂ := Set.piecewise_mono hf hg

end piecewise

variable [SigmaFinite μ] {f : α → ℝ≥0∞} {n : ℕ} {a : α}

-- TODO: Reprove `iSup_eapprox_apply` using this
lemma iSup_coe_eapprox (hf : Measurable f) : ⨆ n, ⇑(eapprox f n) = f := by
  ext a
  simp only [iSup_apply, eapprox, iSup_approx_apply ennrealRatEmbed f a hf rfl]
  refine le_antisymm (iSup_le fun i => iSup_le fun hi => hi) (le_of_not_gt ?_)
  intro h
  rcases ENNReal.lt_iff_exists_rat_btwn.1 h with ⟨q, _, lt_q, q_lt⟩
  have :
    (Real.toNNReal q : ℝ≥0∞) ≤ ⨆ (k : ℕ) (_ : ennrealRatEmbed k ≤ f a), ennrealRatEmbed k := by
    refine le_iSup_of_le (Encodable.encode q) ?_
    rw [ennrealRatEmbed_encode q]
    exact le_iSup_of_le (le_of_lt q_lt) le_rfl
  exact lt_irrefl _ (lt_of_le_of_lt this lt_q)

@[gcongr]
lemma eapprox_mono {m n : ℕ} (hmn : m ≤ n) : eapprox f m ≤ eapprox f n := monotone_eapprox _ hmn

variable (μ) in
noncomputable def eapproxSigmaFinite (f : α → ℝ≥0∞) (n : ℕ) : α →ₛ ℝ≥0∞ :=
  (eapprox f n).piecewise (spanningSets μ n) (measurableSet_spanningSets ..) 0

lemma eapproxSigmaFinite_le_eapprox : eapproxSigmaFinite μ f n ≤ eapprox f n :=
  fun a ↦ by by_cases ha : a ∈ spanningSets μ n <;> simp [eapproxSigmaFinite, *]

lemma eapproxSigmaFinite_lt_top : eapproxSigmaFinite μ f n a < ∞ :=
  (eapproxSigmaFinite_le_eapprox _).trans_lt (eapprox_lt_top ..)

@[mono]
lemma monotone_eapproxSigmaFinite (f : α → ℝ≥0∞) : Monotone (eapproxSigmaFinite μ f) := by
  rintro m n hmn
  unfold eapproxSigmaFinite SimpleFunc.piecewise
  simp only [coe_zero, piecewise_eq_indicator, mk_le_mk]
  exact (indicator_mono (by gcongr)).trans (indicator_le_indicator_of_subset (by gcongr) (by simp))

lemma iSup_coe_eapproxSigmaFinite (hf : Measurable f) : ⨆ n, ⇑(eapproxSigmaFinite μ f n) = f := by
  simp [eapproxSigmaFinite, coe_piecewise, coe_zero, piecewise_eq_indicator,  iSup_coe_eapprox hf,
    iSup_indicator ENNReal.bot_eq_zero (monotone_eapprox _) (monotone_spanningSets _)]

lemma iSup_eapproxSigmaFinite_apply (hf : Measurable f) (a : α) :
    ⨆ n, eapproxSigmaFinite μ f n a = f a := by
  simpa using congr_fun (iSup_coe_eapproxSigmaFinite hf) a

-- lemma eapproxSigmaFinite_comp [MeasurableSpace γ] {f : γ → ℝ≥0∞} {g : α → γ} {n : ℕ}
--     (hf : Measurable f) (hg : Measurable g) :
--     (eapproxSigmaFinite μ (f ∘ g) n : α → ℝ≥0∞) = (eapproxSigmaFinite μ f n : γ →ₛ ℝ≥0∞) ∘ g :=
--   funext fun a => approx_comp a hf hg

end MeasureTheory.SimpleFunc

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}

/-- To prove something for an arbitrary measurable function into `ℝ≥0∞`, it suffices to show
that the property holds for (multiples of) characteristic functions and is closed under addition
and supremum of increasing sequences of functions.

It is possible to make the hypotheses in the induction steps a bit stronger, and such conditions
can be added once we need them (for example in `h_add` it is only necessary to consider the sum of
a simple function with a multiple of a characteristic function and that the intersection
of their images is a subset of `{0}`. -/
@[elab_as_elim]
-- TODO: Replace `Measurable.ennreal_induction`
theorem Measurable.ennreal_induction' {P : (α → ℝ≥0∞) → Prop}
    (h_ind : ∀ (c : ℝ≥0∞) ⦃s⦄, MeasurableSet s → P (Set.indicator s fun _ => c))
    (h_add :
      ∀ ⦃f g : α → ℝ≥0∞⦄,
        Disjoint (support f) (support g) → Measurable f → Measurable g → P f → P g → P (f + g))
    (h_iSup :
      ∀ ⦃f : ℕ → α → ℝ≥0∞⦄, (∀ n, Measurable (f n)) → Monotone f → (∀ n, P (f n)) →
        P fun x => ⨆ n, f n x)
    ⦃f : α → ℝ≥0∞⦄ (hf : Measurable f) : P f := by
  convert h_iSup (fun n => (eapprox f n).measurable) (monotone_eapprox f) _ using 2
  · rw [iSup_eapprox_apply f hf]
  · exact fun n =>
      SimpleFunc.induction (fun c s hs => h_ind c hs)
        (fun f g hfg hf hg => h_add hfg f.measurable g.measurable hf hg) (eapprox f n)

/-- To prove something for an arbitrary measurable function into `ℝ≥0∞`, it suffices to show
that the property holds for (multiples of) characteristic functions with finite mass according to
some sigma-finite measure and is closed under addition and supremum of increasing sequences of
functions.

It is possible to make the hypotheses in the induction steps a bit stronger, and such conditions
can be added once we need them (for example in `h_add` it is only necessary to consider the sum of
a simple function with a multiple of a characteristic function and that the intersection
of their images is a subset of `{0}`. -/
@[elab_as_elim]
theorem Measurable.ennreal_sigmaFinite_induction [SigmaFinite μ] {P : (α → ℝ≥0∞) → Prop}
    (h_ind : ∀ (c : ℝ≥0∞) ⦃s⦄, MeasurableSet s → μ s < ∞ → P (Set.indicator s fun _ => c))
    (h_add :
      ∀ ⦃f g : α → ℝ≥0∞⦄,
        Disjoint (support f) (support g) → Measurable f → Measurable g → P f → P g → P (f + g))
    (h_iSup :
      ∀ ⦃f : ℕ → α → ℝ≥0∞⦄, (∀ n, Measurable (f n)) → Monotone f → (∀ n, P (f n)) →
        P fun x => ⨆ n, f n x)
    ⦃f : α → ℝ≥0∞⦄ (hf : Measurable f) : P f := by
  refine Measurable.ennreal_induction (fun c s hs ↦ ?_) h_add h_iSup hf
  convert h_iSup (f := fun n ↦ (s ∩ spanningSets μ n).indicator fun _ ↦ c)
    (fun n ↦ measurable_const.indicator (hs.inter (measurableSet_spanningSets ..)))
    (fun m n hmn a ↦ Set.indicator_le_indicator_of_subset (by gcongr) (by simp) _)
    (fun n ↦ h_ind _ (hs.inter (measurableSet_spanningSets ..))
      (measure_inter_lt_top_of_right_ne_top (measure_spanningSets_lt_top ..).ne)) with a
  rw [← Set.indicator_iUnion_apply (M := ℝ≥0∞) rfl, ← Set.inter_iUnion]
  simp
