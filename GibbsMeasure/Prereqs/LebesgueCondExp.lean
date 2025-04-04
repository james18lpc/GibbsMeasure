import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import GibbsMeasure.Mathlib.MeasureTheory.Function.ConditionalExpectation.Unique

open ENNReal NNReal Filter
open scoped Classical Topology

namespace MeasureTheory
variable {α : Type*} {m m₀ : MeasurableSpace α} {μ : Measure[m₀] α} [SigmaFinite μ] {f g : α → ℝ≥0∞}
  {s : Set α}

variable (m μ f) in
/-- Lebesgue conditional expectation of an `ℝ≥0∞`-valued function. It is defined as `0` if any of
the following conditions holds:
* `m` is not a sub-σ-algebra of `m₀`,
* `μ` is not σ-finite with respect to `m`,
* `f` is not `μ`-integrable. -/
noncomputable def lcondExp : α → ℝ≥0∞ :=
  if hm : m ≤ m₀ then
    if _h : SigmaFinite (μ.trim hm) then
      if Measurable[m] f then f
      else if hf : Measurable[m₀] f then
        ENNReal.ofReal ∘
          ⨆ n, μ[ENNReal.toReal ∘ (hf.stronglyMeasurable.finStronglyMeasurable μ).approx n | m]
      else 0
    else 0
  else 0

/-- Lebesgue conditional expectation of an `ℝ≥0∞`-valued function. It is defined as `0` if any of
the following conditions holds:
* `m` is not a sub-σ-algebra of `m₀`,
* `μ` is not σ-finite with respect to `m`. -/
scoped notation μ "⁻[" f "|" m "]" => MeasureTheory.lcondExp m μ f

lemma lcondExp_of_not_le (hm_not : ¬m ≤ m₀) : μ⁻[f|m] = 0 := by rw [lcondExp, dif_neg hm_not]

lemma lcondExp_of_not_sigmaFinite (hm : m ≤ m₀) (hμm_not : ¬SigmaFinite (μ.trim hm)) :
    μ⁻[f|m] = 0 := by rw [lcondExp, dif_pos hm, dif_neg hμm_not]

lemma lcondExp_of_sigmaFinite (hm : m ≤ m₀) [hμm : SigmaFinite (μ.trim hm)] :
    μ⁻[f|m] = if Measurable[m] f then f else if hf : Measurable[m₀] f then
      ENNReal.ofReal ∘
        ⨆ n, μ[ENNReal.toReal ∘ (hf.stronglyMeasurable.finStronglyMeasurable μ).approx n | m]
      else 0 := by
  simp [lcondExp, dif_pos hm, hμm]

lemma lcondExp_of_measurable (hm : m ≤ m₀) [hμm : SigmaFinite (μ.trim hm)] {f : α → ℝ≥0∞}
    (hf : Measurable[m] f) : μ⁻[f|m] = f := by
  rw [lcondExp_of_sigmaFinite hm, if_pos hf]

lemma lcondExp_const (hm : m ≤ m₀) (c : ℝ≥0∞) [IsFiniteMeasure μ] :
    μ⁻[fun _ : α => c|m] = fun _ => c := lcondExp_of_measurable hm measurable_const

@[simp]
lemma lcondExp_zero : μ⁻[(0 : α → ℝ≥0∞)|m] = 0 := by
  by_cases hm : m ≤ m₀
  swap; · rw [lcondExp_of_not_le hm]
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · rw [lcondExp_of_not_sigmaFinite hm hμm]
  haveI : SigmaFinite (μ.trim hm) := hμm
  exact lcondExp_of_measurable hm (@measurable_zero _ _ _ (_) _)

lemma measurable_lcondExp : Measurable[m] (μ⁻[f|m]) := by
  by_cases hm : m ≤ m₀
  swap; · rw [lcondExp_of_not_le hm]; exact @measurable_zero _ _ _ (_) _
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · rw [lcondExp_of_not_sigmaFinite hm hμm]; exact @measurable_zero _ _ _ (_) _
  haveI : SigmaFinite (μ.trim hm) := hμm
  rw [lcondExp_of_sigmaFinite hm]
  split_ifs with hfm
  · exact hfm
  · simp only [Function.comp_def, iSup_apply]
    exact .ennreal_ofReal <| .iSup fun n ↦ stronglyMeasurable_condExp.measurable
  · fun_prop

lemma lcondExp_congr_ae (h : f =ᵐ[μ] g) : μ⁻[f|m] =ᵐ[μ] μ⁻[g|m] := by
  by_cases hm : m ≤ m₀
  swap; · simp_rw [lcondExp_of_not_le hm]; rfl
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · simp_rw [lcondExp_of_not_sigmaFinite hm hμm]; rfl
  haveI : SigmaFinite (μ.trim hm) := hμm
  sorry
  -- exact (lcondExp_ae_eq_lcondExpL1 hm f).trans
  --   (Filter.EventuallyEq.trans (by rw [lcondExpL1_congr_ae hm h])
  --     (lcondExp_ae_eq_lcondExpL1 hm g).symm)

lemma lcondExp_of_aemeasurable (hm : m ≤ m₀) [hμm : SigmaFinite (μ.trim hm)] {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) : μ⁻[f|m] =ᵐ[μ] f := by
  refine ((lcondExp_congr_ae hf.ae_eq_mk).trans ?_).trans hf.ae_eq_mk.symm
  sorry
  -- rw [lcondExp_of_measurable hm hf.measurable_mk
  --   ((integrable_congr hf.ae_eq_mk).mp hfi)]

/-- The lintegral of the conditional expectation `μ⁻[f|hm]` over an `m`-measurable set is equal to
the lintegral of `f` on that set. -/
lemma setLIntegral_lcondExp (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)] (hs : MeasurableSet[m] s) :
    ∫⁻ x in s, (μ⁻[f|m]) x ∂μ = ∫⁻ x in s, f x ∂μ := by
  sorry
  -- rw [setLIntegral_congr_ae (hm s hs) ((lcondExp_ae_eq_lcondExpL1 hm f).mono fun x hx _ => hx)]
  -- exact setLIntegral_lcondExpL1 hf hs

lemma lintegral_lcondExp (hm : m ≤ m₀) [hμm : SigmaFinite (μ.trim hm)] :
    ∫⁻ x, (μ⁻[f|m]) x ∂μ = ∫⁻ x, f x ∂μ := by
  suffices ∫⁻ x in Set.univ, (μ⁻[f|m]) x ∂μ = ∫⁻ x in Set.univ, f x ∂μ by
    simp_rw [setLIntegral_univ] at this; exact this
  exact setLIntegral_lcondExp hm MeasurableSet.univ

/-- Total probability law using `lcondExp` as conditional probability. -/
lemma lintegral_lcondExp_indicator {Y : α → ℝ≥0∞} (hY : Measurable Y)
    [SigmaFinite (μ.trim hY.comap_le)] {A : Set α} (hA : MeasurableSet A) :
    ∫⁻ x, (μ⁻[(A.indicator fun _ ↦ 1) | MeasurableSpace.comap Y inferInstance]) x ∂μ = μ A := by
  rw [lintegral_lcondExp, lintegral_indicator hA, setLIntegral_const, one_mul]

/-- **Uniqueness of the conditional expectation**

If a function is a.e. `m`-measurable, verifies an integrability condition and has same lintegral
as `f` on all `m`-measurable sets, then it is a.e. equal to `μ⁻[f|hm]`. -/
lemma ae_eq_lcondExp_of_forall_setLIntegral_eq (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    {f g : α → ℝ≥0∞}
    (hg_eq : ∀ s : Set α, MeasurableSet[m] s → μ s < ∞ → ∫⁻ x in s, g x ∂μ = ∫⁻ x in s, f x ∂μ)
    (hgm : AEStronglyMeasurable[m] g μ) : g =ᵐ[μ] μ⁻[f|m] := by
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite' hm (fun s hs hμs => ?_) hgm sorry
    -- measurable_lcondExp.aestronglyMeasurable
  rw [hg_eq s hs hμs, setLIntegral_lcondExp hm hs]

lemma lcondExp_bot' [hμ : NeZero μ] (f : α → ℝ≥0∞) :
    μ⁻[f|⊥] = fun _ => (μ Set.univ).toNNReal⁻¹ • ∫⁻ x, f x ∂μ := by
  by_cases hμ_finite : IsFiniteMeasure μ
  swap
  · have h : ¬SigmaFinite (μ.trim bot_le) := by rwa [sigmaFinite_trim_bot_iff]
    rw [not_isFiniteMeasure_iff] at hμ_finite
    rw [lcondExp_of_not_sigmaFinite bot_le h]
    simp only [hμ_finite, ENNReal.toNNReal_top, GroupWithZero.inv_zero, zero_smul]
    rfl
  sorry
  -- have h_meas : Measurable[⊥] (μ⁻[f|⊥]) := measurable_lcondExp
  -- obtain ⟨c, h_eq⟩ := measurable_bot_iff.mp h_meas
  -- rw [h_eq]
  -- have h_lintegral : ∫⁻ x, (μ⁻[f|⊥]) x ∂μ = ∫⁻ x, f x ∂μ := lintegral_lcondExp bot_le
  -- simp_rw [h_eq, lintegral_const] at h_lintegral
  -- rw [← h_lintegral, ← smul_assoc, smul_eq_mul, inv_mul_cancel, one_smul]
  -- rw [Ne, ENNReal.toReal_eq_zero_iff, not_or]
  -- exact ⟨NeZero.ne _, measure_ne_top μ Set.univ⟩

lemma lcondExp_bot_ae_eq (f : α → ℝ≥0∞) :
    μ⁻[f|⊥] =ᵐ[μ] fun _ => (μ Set.univ).toNNReal⁻¹ • ∫⁻ x, f x ∂μ := by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · rw [ae_zero]; exact eventually_bot
  · exact .of_forall <| congr_fun (lcondExp_bot' f)

lemma lcondExp_bot [IsProbabilityMeasure μ] (f : α → ℝ≥0∞) : μ⁻[f|⊥] = fun _ => ∫⁻ x, f x ∂μ := by
  refine (lcondExp_bot' f).trans ?_; rw [measure_univ, ENNReal.toNNReal_one, inv_one, one_smul]

lemma lcondExp_add : μ⁻[f + g|m] =ᵐ[μ] μ⁻[f|m] + μ⁻[g|m] := by
  by_cases hm : m ≤ m₀
  swap; · simp_rw [lcondExp_of_not_le hm]; simp
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · simp_rw [lcondExp_of_not_sigmaFinite hm hμm]; simp
  haveI : SigmaFinite (μ.trim hm) := hμm
  sorry
  -- refine (lcondExp_ae_eq_lcondExpL1 hm _).trans ?_
  -- rw [lcondExpL1_add hf hg]
  -- exact (coeFn_add _ _).trans
  --   ((lcondExp_ae_eq_lcondExpL1 hm _).symm.add (lcondExp_ae_eq_lcondExpL1 hm _).symm)

lemma lcondExp_finset_sum {ι : Type*} {s : Finset ι} {f : ι → α → ℝ≥0∞} :
    μ⁻[∑ i ∈ s, f i|m] =ᵐ[μ] ∑ i ∈ s, μ⁻[f i|m] := by
  induction' s using Finset.induction_on with i s his heq hf
  · rw [Finset.sum_empty, Finset.sum_empty, lcondExp_zero]
  · rw [Finset.sum_insert his, Finset.sum_insert his]
    exact lcondExp_add.trans (EventuallyEq.rfl.add heq)

lemma lcondExp_smul (c : ℝ≥0) (f : α → ℝ≥0∞) : μ⁻[c • f|m] =ᵐ[μ] c • μ⁻[f|m] := by
  by_cases hm : m ≤ m₀
  swap; · simp_rw [lcondExp_of_not_le hm]; simp
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · simp_rw [lcondExp_of_not_sigmaFinite hm hμm]; simp
  haveI : SigmaFinite (μ.trim hm) := hμm
  sorry
  -- refine (lcondExp_ae_eq_lcondExpL1 hm _).trans ?_
  -- rw [lcondExpL1_smul c f]
  -- refine (@lcondExp_ae_eq_lcondExpL1 _ _ _ _ _ m _ _ hm _ f).mp ?_
  -- refine (coeFn_smul c (lcondExpL1 hm μ f)).mono fun x hx1 hx2 => ?_
  -- simp only [hx1, hx2, Pi.smul_apply]

lemma lcondExp_sub : μ⁻[f - g|m] =ᵐ[μ] μ⁻[f|m] - μ⁻[g|m] := by
  sorry
  -- simp_rw [sub_eq_add_neg]
  -- exact (lcondExp_add hf hg.neg).trans (EventuallyEq.rfl.add (lcondExp_neg g))

lemma lcondExp_lcondExp_of_le {m₁ m₂ m₀ : MeasurableSpace α} {μ : Measure α} [SigmaFinite μ]
    (hm₁₂ : m₁ ≤ m₂) (hm₂ : m₂ ≤ m₀) [SigmaFinite (μ.trim hm₂)] :
    μ⁻[μ⁻[f|m₂]|m₁] =ᵐ[μ] μ⁻[f|m₁] := by
  by_cases hμm₁ : SigmaFinite (μ.trim (hm₁₂.trans hm₂))
  swap; · simp_rw [lcondExp_of_not_sigmaFinite (hm₁₂.trans hm₂) hμm₁]; rfl
  haveI : SigmaFinite (μ.trim (hm₁₂.trans hm₂)) := hμm₁
  sorry
  -- refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite' (hm₁₂.trans hm₂)
  --   (fun s _ _ => integrable_lcondExp.integrableOn)
  --   (fun s _ _ => integrable_lcondExp.integrableOn) ?_
  --   (Measurable.aemeasurable' measurable_lcondExp)
  --   (Measurable.aemeasurable' measurable_lcondExp)
  -- intro s hs _
  -- rw [setLIntegral_lcondExp (hm₁₂.trans hm₂) integrable_lcondExp hs]
  -- rw [setLIntegral_lcondExp (hm₁₂.trans hm₂) hf hs, setLIntegral_lcondExp hm₂ hf (hm₁₂ s hs)]

lemma lcondExp_mono (f g : α → ℝ≥0∞) : μ⁻[f|m] ≤ᵐ[μ] μ⁻[g|m] := by
  by_cases hm : m ≤ m₀
  swap; · simp_rw [lcondExp_of_not_le hm]; rfl
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · simp_rw [lcondExp_of_not_sigmaFinite hm hμm]; rfl
  haveI : SigmaFinite (μ.trim hm) := hμm
  sorry
  -- exact (lcondExp_ae_eq_lcondExpL1 hm _).trans_le
  --   ((lcondExpL1_mono hf hg hfg).trans_eq (lcondExp_ae_eq_lcondExpL1 hm _).symm)

-- TODO: We don't have L1 convergence in `ℝ≥0∞`
-- /-- If two sequences of functions have a.e. equal conditional expectations at each step,
-- converge and verify dominated convergence hypotheses, then the conditional expectations of
-- their limits are a.e. equal. -/
-- lemma tendsto_lcondExp_unique (fs gs : ℕ → α → ℝ≥0∞) (f g : α → ℝ≥0∞)
--     (hfs : ∀ᵐ x ∂μ, Tendsto (fun n => fs n x) atTop (𝓝 (f x)))
--     (hgs : ∀ᵐ x ∂μ, Tendsto (fun n => gs n x) atTop (𝓝 (g x))) (bound_fs : α → ℝ)
--     (h_int_bound_fs : Integrable bound_fs μ) (bound_gs : α → ℝ)
--     (h_int_bound_gs : Integrable bound_gs μ) (hfs_bound : ∀ n, ∀ᵐ x ∂μ, ‖fs n x‖ ≤ bound_fs x)
--     (hgs_bound : ∀ n, ∀ᵐ x ∂μ, ‖gs n x‖ ≤ bound_gs x) (hfg : ∀ n, μ⁻[fs n|m] =ᵐ[μ] μ⁻[gs n|m]) :
--     μ⁻[f|m] =ᵐ[μ] μ⁻[g|m] := by
--   by_cases hm : m ≤ m₀; swap; · simp_rw [lcondExp_of_not_le hm]; rfl
--   by_cases hμm : SigmaFinite (μ.trim hm)
--   swap; · simp_rw [lcondExp_of_not_sigmaFinite hm hμm]; rfl
--   haveI : SigmaFinite (μ.trim hm) := hμm
--   refine (lcondExp_ae_eq_lcondExpL1 hm f).trans ((lcondExp_ae_eq_lcondExpL1 hm g).trans ?_).symm
--   rw [← Lp.ext_iff]
--   have hn_eq : ∀ n, lcondExpL1 hm μ (gs n) = lcondExpL1 hm μ (fs n) := by
--     intro n
--     ext1
--     refine (lcondExp_ae_eq_lcondExpL1 hm (gs n)).symm.trans ((hfg n).symm.trans ?_)
--     exact lcondExp_ae_eq_lcondExpL1 hm (fs n)
--   have hcond_fs : Tendsto (fun n => lcondExpL1 hm μ (fs n)) atTop (𝓝 (lcondExpL1 hm μ f)) :=
--     tendsto_lcondExpL1_of_dominated_convergence hm _ (fun n => (hfs_int n).1) h_int_bound_fs
--       hfs_bound hfs
--   have hcond_gs : Tendsto (fun n => lcondExpL1 hm μ (gs n)) atTop (𝓝 (lcondExpL1 hm μ g)) :=
--     tendsto_lcondExpL1_of_dominated_convergence hm _ (fun n => (hgs_int n).1) h_int_bound_gs
--       hgs_bound hgs
--   exact tendsto_nhds_unique_of_eventuallyEq hcond_gs hcond_fs (.of_forall hn_eq)

end MeasureTheory
