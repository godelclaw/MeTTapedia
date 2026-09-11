import Mettapedia.Analysis.BilinearTranslatedKernel

/-!
# Integrated energy of a family of translated bilinear kernels

A common integrable envelope transfers the finite output-square sum to
the shifted input-product square sum. The individual input suprema are
used only to justify integrability; none appears in the final bound.
No cardinality factor is introduced.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.BilinearTranslatedFamilyEnergy

open MeasureTheory Filter BilinearTranslatedKernel

variable {A X E F G 𝕜 : Type*} [MeasurableSpace A] [MeasurableSpace X]
variable [AddCommGroup X] [MeasurableAdd₂ X] [MeasurableNeg X]
variable {μ : Measure A} {ν : Measure X} [SFinite μ] [SFinite ν] [ν.IsAddRightInvariant]
variable [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable [NormedAddCommGroup G] [NormedSpace 𝕜 G]

local instance : NormedAddCommGroup (F →L[𝕜] G) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace 𝕜 (F →L[𝕜] G) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (E →L[𝕜] F →L[𝕜] G) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ G := NormedSpace.restrictScalars ℝ 𝕜 G

theorem integrable_weighted_input_product (M : A → ℝ) (hM : Integrable M μ) (hMn : ∀ q, 0 ≤ M q)
    (a b : A → X) (ha : Measurable a) (hb : Measurable b)
    (f : X → E) (g : X → F) (hf : MemLp f 2 ν) (hg : AEStronglyMeasurable g ν)
    {D : ℝ} (_hD : 0 ≤ D) (hgb : ∀ x, ‖g x‖ ≤ D) :
    Integrable (fun p : A × X ↦ M p.1 * (‖f (p.2 - a p.1)‖ * ‖g (p.2 - b p.1)‖) ^ 2)
      (μ.prod ν) := by
  have hi := (integrable_weighted_translate M (fun x ↦ ‖f x‖ ^ 2) hM
    hf.norm.integrable_sq a ha).mul_const (D ^ 2)
  apply hi.mono'
    (hM.aestronglyMeasurable.comp_fst.mul
      (((aestronglyMeasurable_translate f hf.aestronglyMeasurable a ha).norm.mul
        (aestronglyMeasurable_translate g hg b hb).norm).pow 2))
  apply Eventually.of_forall
  intro p
  simp only [Pi.mul_apply, Pi.pow_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hMn _) (sq_nonneg _)), mul_pow]
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hgb _) 2)
    (mul_nonneg (hMn _) (sq_nonneg _))

theorem ae_action_energy_le (K : A → E →L[𝕜] F →L[𝕜] G) (hK : Integrable K μ)
    (M : A → ℝ) (hM : Integrable M μ) (hMn : ∀ q, 0 ≤ M q) (hdom : ∀ᵐ q ∂μ, ‖K q‖ ≤ M q)
    (a b : A → X) (ha : Measurable a) (hb : Measurable b)
    (f : X → E) (g : X → F) (hf : MemLp f 2 ν) (hg : AEStronglyMeasurable g ν)
    {D : ℝ} (hD : 0 ≤ D) (hgb : ∀ x, ‖g x‖ ≤ D) :
    ∀ᵐ x ∂ν, ‖action (μ := μ) K a b f g x‖ ^ 2 ≤
      (∫ q, M q ∂μ) * ∫ q, M q * (‖f (x - a q)‖ * ‖g (x - b q)‖) ^ 2 ∂μ := by
  have hi := integrable_weighted_input_product M hM hMn a b ha hb f g hf hg hD hgb
  have hm := aestronglyMeasurable_integrand K hK.aestronglyMeasurable a b ha hb
    f g hf.aestronglyMeasurable hg
  have hp : AEStronglyMeasurable (fun p : A × X ↦
      ‖f (p.2 - a p.1)‖ * ‖g (p.2 - b p.1)‖) (μ.prod ν) :=
    (aestronglyMeasurable_translate f hf.aestronglyMeasurable a ha).norm.mul
      (aestronglyMeasurable_translate g hg b hb).norm
  filter_upwards [hi.prod_left_ae, hm.prodMk_right, hp.prodMk_right] with x hx hmx hpx
  apply (WeightedIntegralEnergy.integrable_and_norm_integral_sq_le M
    (fun q ↦ ‖f (x - a q)‖ * ‖g (x - b q)‖) _ hM hMn hpx
    (fun _ ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _)) hx hmx ?_).2
  filter_upwards [hdom] with q hq
  exact ((K q).le_of_opNorm₂_le_of_le hq le_rfl le_rfl).trans_eq (mul_assoc _ _ _)

theorem integral_sum_action_energy_le {ι : Type*} [Fintype ι]
    (K : ι → A → E →L[𝕜] F →L[𝕜] G) (hK : ∀ i, Integrable (K i) μ)
    (M : A → ℝ) (hM : Integrable M μ) (hMn : ∀ q, 0 ≤ M q)
    (hdom : ∀ᵐ q ∂μ, ∀ i, ‖K i q‖ ≤ M q)
    (a b : A → X) (ha : Measurable a) (hb : Measurable b)
    (f : ι → X → E) (g : ι → X → F) (hf : ∀ i, MemLp (f i) 2 ν)
    (hg : ∀ i, AEStronglyMeasurable (g i) ν) (D : ι → ℝ)
    (hD : ∀ i, 0 ≤ D i) (hgb : ∀ i x, ‖g i x‖ ≤ D i) :
    (∫ x, ∑ i, ‖action (μ := μ) (K i) a b (f i) (g i) x‖ ^ 2 ∂ν) ≤
      (∫ q, M q ∂μ) * ∫ x, ∫ q,
        M q * ∑ i, (‖f i (x - a q)‖ * ‖g i (x - b q)‖) ^ 2 ∂μ ∂ν := by
  have hi (i : ι) := integrable_weighted_input_product M hM hMn a b ha hb
    (f i) (g i) (hf i) (hg i) (hD i) (hgb i)
  have htot : Integrable (fun p : A × X ↦
      M p.1 * ∑ i, (‖f i (p.2 - a p.1)‖ * ‖g i (p.2 - b p.1)‖) ^ 2) (μ.prod ν) := by
    simpa only [Finset.mul_sum] using integrable_finsetSum Finset.univ (fun i _ ↦ hi i)
  have ho (i : ι) := (action_memLp_two_and_energy_le (K i) (hK i) a b ha hb
    (f i) (g i) (hf i) (hg i) (hD i) (hgb i)).2.1.norm.integrable_sq
  have hp : ∀ᵐ x ∂ν, (∑ i, ‖action (μ := μ) (K i) a b (f i) (g i) x‖ ^ 2) ≤
      (∫ q, M q ∂μ) * ∫ q, M q * ∑ i, (‖f i (x - a q)‖ * ‖g i (x - b q)‖) ^ 2 ∂μ := by
    filter_upwards [ae_all_iff.mpr (fun i ↦ ae_action_energy_le (K i) (hK i) M hM hMn
      (hdom.mono (fun q hq ↦ hq i)) a b ha hb (f i) (g i) (hf i) (hg i) (hD i) (hgb i)),
      ae_all_iff.mpr (fun i ↦ (hi i).prod_left_ae)] with x hx hix
    apply (Finset.sum_le_sum (fun i _ ↦ hx i)).trans_eq
    rw [← Finset.mul_sum]
    congr 1
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum Finset.univ (fun i _ ↦ hix i)]
  have h := integral_mono_ae (integrable_finsetSum Finset.univ (fun i _ ↦ ho i))
    (htot.integral_prod_right.const_mul _) hp
  simpa only [integral_const_mul] using h

/-- The right-input version uses the flipped bilinear map, not kernel symmetry. -/
theorem integral_sum_action_energy_le_right {ι : Type*} [Fintype ι]
    (K : ι → A → E →L[𝕜] F →L[𝕜] G) (hK : ∀ i, Integrable (K i) μ)
    (M : A → ℝ) (hM : Integrable M μ) (hMn : ∀ q, 0 ≤ M q)
    (hdom : ∀ᵐ q ∂μ, ∀ i, ‖K i q‖ ≤ M q)
    (a b : A → X) (ha : Measurable a) (hb : Measurable b)
    (f : ι → X → E) (g : ι → X → F) (hg : ∀ i, MemLp (g i) 2 ν)
    (hf : ∀ i, AEStronglyMeasurable (f i) ν) (D : ι → ℝ)
    (hD : ∀ i, 0 ≤ D i) (hfb : ∀ i x, ‖f i x‖ ≤ D i) :
    (∫ x, ∑ i, ‖action (μ := μ) (K i) a b (f i) (g i) x‖ ^ 2 ∂ν) ≤
      (∫ q, M q ∂μ) * ∫ x, ∫ q,
        M q * ∑ i, (‖g i (x - b q)‖ * ‖f i (x - a q)‖) ^ 2 ∂μ ∂ν := by
  have hflip (i : ι) : Integrable (fun q ↦ (K i q).flip) μ :=
    (ContinuousLinearMap.flipₗᵢ 𝕜 E F G).toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp (hK i)
  exact integral_sum_action_energy_le (fun i q ↦ (K i q).flip) hflip M hM hMn
    (by simpa only [ContinuousLinearMap.opNorm_flip] using hdom) b a hb ha g f hg hf D hD hfb

end Mettapedia.Analysis.BilinearTranslatedFamilyEnergy
