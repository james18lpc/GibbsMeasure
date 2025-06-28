import GibbsMeasure.Mathlib.Data.ENNReal.Basic
import GibbsMeasure.Mathlib.MeasureTheory.Function.L1Space.Integrable
import GibbsMeasure.Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import GibbsMeasure.Mathlib.MeasureTheory.Integral.Bochner.Basic
import GibbsMeasure.Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.Kernel.Proper

/-!
# Proper kernels

We define the notion of properness for measure kernels and highlight important consequences.
-/

open MeasureTheory ENNReal NNReal Set Function
open scoped ProbabilityTheory

namespace ProbabilityTheory.Kernel
variable {X : Type*} {𝓑 𝓧 : MeasurableSpace X} {π : Kernel[𝓑, 𝓧] X X} {A B : Set X}
  {f g : X → ℝ≥0∞} {x₀ : X}

private lemma IsProper.integral_indicator_mul_indicator (hπ : IsProper π) (h𝓑𝓧 : 𝓑 ≤ 𝓧)
    (hA : MeasurableSet[𝓧] A) (hB : MeasurableSet[𝓑] B) :
    ∫ x, (B.indicator 1 x * A.indicator 1 x : ℝ) ∂(π x₀) =
      B.indicator 1 x₀ * ∫ x, A.indicator 1 x ∂(π x₀) := by
  calc
        ∫ x, (B.indicator 1 x * A.indicator 1 x : ℝ) ∂(π x₀)
    _ = (∫⁻ x, .ofReal (B.indicator 1 x * A.indicator 1 x) ∂π x₀).toReal :=
      integral_eq_lintegral_of_nonneg_ae (.of_forall <| by simp [indicator_nonneg, mul_nonneg])
        (by measurability)
    _ = (∫⁻ x, B.indicator 1 x * A.indicator 1 x ∂π x₀).toReal := by
      simp [ofReal_mul, indicator_nonneg]
    _ = (B.indicator 1 x₀ * ∫⁻ x, A.indicator 1 x ∂π x₀).toReal := by
      rw [hπ.lintegral_mul h𝓑𝓧 (by measurability) (by measurability)]
    _ = B.indicator 1 x₀ * ∫ x, A.indicator 1 x ∂π x₀ := by
      rw [integral_eq_lintegral_of_nonneg_ae (.of_forall <| by simp [indicator_nonneg, mul_nonneg])
        (by measurability)]
      simp [ofReal_mul]

private lemma IsProper.integral_indicator_mul {f : X → ℝ} (hπ : IsProper π) (h𝓑𝓧 : 𝓑 ≤ 𝓧)
    (hf : Integrable[𝓧] f (π x₀)) (hB : MeasurableSet[𝓑] B) :
    ∫ x, B.indicator 1 x * f x ∂(π x₀) = B.indicator 1 x₀ * ∫ x, f x ∂(π x₀) := by
  refine Integrable.induction _ (fun c S hmS bpS ↦ ?_) (fun f g _ hfint hgint hf hg ↦ ?_) ?_
    (fun f g hfg hfint hf ↦ ?_) hf
  · simp [← smul_indicator_one_apply, mul_left_comm, integral_const_mul,
      integral_indicator_mul_indicator hπ h𝓑𝓧 hmS hB]
  · have : Integrable (fun x ↦ B.indicator 1 x * f x) (π x₀) := by simp [h𝓑𝓧 _ hB, *]
    have : Integrable (fun x ↦ B.indicator 1 x * g x) (π x₀) := by simp [h𝓑𝓧 _ hB, *]
    simp [mul_add, integral_add, *]
  · refine isClosed_eq ?_ <| by fun_prop
    simpa [integral_indicator (h𝓑𝓧 B hB), ← indicator_mul_left] using continuous_setIntegral _
  · simpa [integral_congr_ae <| .mul .rfl hfg, integral_congr_ae hfg] using hf




lemma indicator_const_eq_mul_indicator_one {f: X → ℝ} {c:ℝ} {B: Set X}: ∀x,B.indicator (fun x ↦ c)
 x = c*(B.indicator 1 x) := by intro x; by_cases h:x ∈ B <;> simp [h]

lemma measurable_ofIntegrable{α β} [NormedAddGroup β] [m : MeasurableSpace α] [m0: MeasurableSpace β]
 {μ : Measure α}  {f: α → β} (hc: μ.IsComplete) [BorelSpace β] [SecondCountableTopology β]:
 Integrable f μ → Measurable f := by
   rintro ⟨haes,_⟩
   rw [aestronglyMeasurable_iff_aemeasurable,aemeasurable_iff_measurable] at haes
   assumption

--stated seperately as it is a weaker version of the original
set_option diagnostics true in
private lemma IsProper.integral_mul' (hπ : IsProper π) (h𝓑𝓧 : 𝓑 ≤ 𝓧) {f g : X → ℝ} (x₀ : X)
    (hf : Integrable[𝓑] f ((π x₀).trim h𝓑𝓧)) (hg : Integrable[𝓑] (f * g) ((π x₀).trim h𝓑𝓧))
    [hbμc: ((π x₀).trim h𝓑𝓧).IsComplete]:∫ x, f x * g x ∂(π x₀) = g x₀ * ∫ x, f x ∂(π x₀) := by
      apply @Integrable.induction (α:=X) (E:=ℝ) 𝓑 (inferInstance) (μ:=((π x₀).trim h𝓑𝓧))
       (fun h ↦ Integrable[𝓑] (fun x ↦ f x * h x) ((π x₀).trim h𝓑𝓧) →
       ((π x₀).trim h𝓑𝓧).IsComplete  → ∫ x, (f x * h x) ∂(π x₀) = h x₀ * ∫ x, f x ∂(π x₀))
      · intro c S hmS bT hInt _
        rw [indicator_const_eq_mul_indicator_one (f:=f)]
        conv => --couldnt get past lambda abstraction(?) with simp only; only the first rw
         lhs
         rhs
         intro x
         rw [indicator_const_eq_mul_indicator_one (f:=f),←mul_assoc,mul_comm ((f x)),mul_assoc,
          mul_comm (f x) (S.indicator 1 x)]
        rw [integral_const_mul,IsProper.integral_indicator_mul hπ h𝓑𝓧
        (integrable_of_integrable_trim h𝓑𝓧 hf) hmS,←mul_assoc]
      · intro f1 f2 disj Intf1 Intf2 hind1 hind2 hpos trimcomp
        have disj':Disjoint (Function.support (fun x ↦ ↑(f x) * f1 x)) (Function.support (fun x ↦
        ↑(f x) * f2 x)) := by
         simp
         exact disjoint_of_subset (s₁ := (Function.support fun x ↦ f x) ∩
          Function.support f1) (s₂ := Function.support f1) (by simp) (t₂ := Function.support f2)
           (t₁ := (Function.support fun x ↦ f x) ∩
          Function.support f2) (by simp) disj
        have df_eq_abs1: (fun x ↦ f x * (f1 + f2) x) = ((fun x ↦ (f *f1) x)) + (fun x ↦ (f * f2) x)
        := by
         ext x
         simp [mul_add]
        rw [df_eq_abs1] at hpos
        have df_eq_abs2: (fun x ↦ f x * (f1 + f2) x) = (fun x ↦ (f * f1) x + (f*f2) x) := by trivial
        rw [df_eq_abs2]
        have f_meas: @Measurable X ℝ 𝓑 (inferInstance) f := measurable_ofIntegrable (m:=𝓑) trimcomp hf
        have Intff1: Integrable (f  * f1) ((π x₀).trim h𝓑𝓧) ∧  Integrable (f* f2)
         ((π x₀).trim h𝓑𝓧) := by
           apply (@integrable_add_of_disjoint X ℝ 𝓑 (inferInstance) (μ := (π x₀).trim h𝓑𝓧)
            (f * f1) (f  * f2) disj' ?_ ?_).mp hpos
           · rw [stronglyMeasurable_iff_measurable]
             have f1_meas :=  measurable_ofIntegrable (m:=𝓑) trimcomp Intf1
             have f_meas:@Measurable X ℝ 𝓑 (inferInstance) f := measurable_ofIntegrable (m:=𝓑)
              trimcomp hf
             apply Measurable.mul
             · exact f_meas
             · exact f1_meas
           · rw [stronglyMeasurable_iff_measurable]
             have f2_meas :=  measurable_ofIntegrable (m:=𝓑) trimcomp Intf2
             apply Measurable.mul
             · exact f_meas
             · exact f2_meas
        specialize hind1 Intff1.1 trimcomp
        specialize hind2 Intff1.2 trimcomp
        have Intff2 := And.intro (integrable_of_integrable_trim h𝓑𝓧 Intff1.1)
         (integrable_of_integrable_trim h𝓑𝓧 Intff1.2)
        rw [integral_add Intff2.1 Intff2.2]
        simp [hind1,hind2,add_mul]
      · have (f_1 : ↥(Lp ℝ 1 ((π x₀).trim h𝓑𝓧))): Integrable (fun x ↦ f x * f_1 x) ((π x₀).trim h𝓑𝓧)
         := sorry
        --not sure how to get around this one fast WIP
        simp [hbμc,this]
        refine isClosed_eq (X:=ℝ) (Y:= ↥(Lp ℝ 1 ((π x₀).trim h𝓑𝓧)))
          (g:= fun f_1 ↦ f_1 x₀ * ∫ (x : X), f x ∂π x₀) (f:= fun f_1 ↦ ∫ (x : X), f x * f_1 x ∂π x₀)
          ?_ ?_
        · sorry --fun_prop and continuity failed; WIP
        · sorry
      · intros;expose_names
        have :=  h.symm.mul (ae_eq_refl (μ := ((π x₀).trim h𝓑𝓧)) f)
        simp only [mul_comm] at this
        have hcongr:= integral_congr_ae (ae_eq_of_ae_eq_trim this)
        have := (integrable_congr this).mp (h_3)
        specialize h_2 this h_4
        rw [hcongr,h_2]
        congr
        sorry
      · sorry --seemingly need integrability of g as well. Would suffice to have it from
              --integrability on f anf f*g; but this certainly doesnt look true at least in general.
      · exact hg
      · assumption


lemma IsProper.integral_mul (hπ : IsProper π) (h𝓑𝓧 : 𝓑 ≤ 𝓧) (f g : X → ℝ) (x₀ : X)
    (hf : Integrable[𝓧] f (π x₀)) (hg : Integrable[𝓑] (f * g) (@Measure.map _ _ 𝓧 𝓑 id (π x₀))) :
    ∫ x, f x * g x ∂(π x₀) = g x₀ * ∫ x, f x ∂(π x₀) := by
  --Integrable.induction
  sorry

end ProbabilityTheory.Kernel
