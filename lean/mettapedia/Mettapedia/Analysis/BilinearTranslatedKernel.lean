import Mettapedia.Analysis.WeightedIntegralEnergy
import Mettapedia.Analysis.BilinearKernelIntegrability
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Bilinear translated kernels on square-integrable fields

An integrable bilinear kernel acts on one L² input and one bounded
measurable input. Translation invariance controls the spatial energy.
The action is the actual Bochner integral; its integrand is proved
integrable for almost every output point.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.BilinearTranslatedKernel

open MeasureTheory MeasureTheory.Measure Filter

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

theorem measurePreserving_skew_sub (a : A → X) (ha : Measurable a) :
    MeasurePreserving (fun p : A × X ↦ (p.1, p.2 - a p.1)) (μ.prod ν) (μ.prod ν) :=
  (MeasurePreserving.id μ).skew_product (measurable_snd.sub (ha.comp measurable_fst))
    (Eventually.of_forall (fun q ↦ (measurePreserving_sub_right ν (a q)).map_eq))

theorem aestronglyMeasurable_translate (f : X → E) (hf : AEStronglyMeasurable f ν)
    (a : A → X) (ha : Measurable a) :
    AEStronglyMeasurable (fun p : A × X ↦ f (p.2 - a p.1)) (μ.prod ν) :=
  hf.comp_snd.comp_quasiMeasurePreserving (measurePreserving_skew_sub a ha).quasiMeasurePreserving

theorem integrable_weighted_translate (w : A → ℝ) (f : X → ℝ)
    (hw : Integrable w μ) (hf : Integrable f ν) (a : A → X) (ha : Measurable a) :
    Integrable (fun p : A × X ↦ w p.1 * f (p.2 - a p.1)) (μ.prod ν) := by
  have hi := hw.mul_prod hf
  exact ((measurePreserving_skew_sub a ha).integrable_comp hi.aestronglyMeasurable).mpr hi

theorem integral_weighted_translate (w : A → ℝ) (f : X → ℝ)
    (hw : Integrable w μ) (hf : Integrable f ν) (a : A → X) (ha : Measurable a) :
    (∫ x, ∫ q, w q * f (x - a q) ∂μ ∂ν) = (∫ q, w q ∂μ) * ∫ x, f x ∂ν := by
  rw [integral_integral_swap (f := fun x q ↦ w q * f (x - a q))
    (integrable_weighted_translate w f hw hf a ha).swap]
  simp_rw [integral_const_mul, integral_sub_right_eq_self]
  exact integral_mul_const _ _

def action (K : A → E →L[𝕜] F →L[𝕜] G) (a b : A → X)
    (f : X → E) (g : X → F) (x : X) : G :=
  ∫ q, K q (f (x - a q)) (g (x - b q)) ∂μ

theorem aestronglyMeasurable_integrand (K : A → E →L[𝕜] F →L[𝕜] G)
    (hK : AEStronglyMeasurable K μ) (a b : A → X) (ha : Measurable a) (hb : Measurable b)
    (f : X → E) (g : X → F) (hf : AEStronglyMeasurable f ν) (hg : AEStronglyMeasurable g ν) :
    AEStronglyMeasurable
      (fun p : A × X ↦ K p.1 (f (p.2 - a p.1)) (g (p.2 - b p.1))) (μ.prod ν) := by
  have hfu := aestronglyMeasurable_translate f hf a ha (μ := μ)
  have hgu := aestronglyMeasurable_translate g hg b hb (μ := μ)
  exact (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
    (((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hK.comp_fst.prodMk hfu)).prodMk hgu)

theorem aestronglyMeasurable_action (K : A → E →L[𝕜] F →L[𝕜] G)
    (hK : AEStronglyMeasurable K μ) (a b : A → X) (ha : Measurable a) (hb : Measurable b)
    (f : X → E) (g : X → F) (hf : AEStronglyMeasurable f ν) (hg : AEStronglyMeasurable g ν) :
    AEStronglyMeasurable (action (μ := μ) K a b f g) ν :=
  (aestronglyMeasurable_integrand K hK a b ha hb f g hf hg).prod_swap.integral_prod_right'

theorem action_memLp_two_and_energy_le (K : A → E →L[𝕜] F →L[𝕜] G)
    (hK : Integrable K μ) (a b : A → X) (ha : Measurable a) (hb : Measurable b)
    (f : X → E) (g : X → F) (hf : MemLp f 2 ν) (hg : AEStronglyMeasurable g ν)
    {D : ℝ} (hD : 0 ≤ D) (hgb : ∀ x, ‖g x‖ ≤ D) :
    (∀ᵐ x ∂ν, Integrable (fun q ↦ K q (f (x - a q)) (g (x - b q))) μ) ∧
      MemLp (action (μ := μ) K a b f g) 2 ν ∧
        (∫ x, ‖action (μ := μ) K a b f g x‖ ^ 2 ∂ν) ≤
          (∫ q, ‖K q‖ ∂μ) ^ 2 * D ^ 2 * ∫ x, ‖f x‖ ^ 2 ∂ν := by
  have he : Integrable (fun p : A × X ↦ ‖K p.1‖ * (‖f (p.2 - a p.1)‖ * D) ^ 2)
      (μ.prod ν) := by
    simpa only [mul_pow, mul_assoc] using
      (integrable_weighted_translate _ _ hK.norm hf.norm.integrable_sq a ha).mul_const (D ^ 2)
  have hm := aestronglyMeasurable_integrand K hK.aestronglyMeasurable a b ha hb
    f g hf.aestronglyMeasurable hg
  have hmA := aestronglyMeasurable_action K hK.aestronglyMeasurable a b ha hb
    f g hf.aestronglyMeasurable hg
  have hmF : AEStronglyMeasurable (fun p : A × X ↦ ‖f (p.2 - a p.1)‖ * D) (μ.prod ν) :=
    (aestronglyMeasurable_translate f hf.aestronglyMeasurable a ha).norm.mul_const D
  have hp : ∀ᵐ x ∂ν,
      Integrable (fun q ↦ K q (f (x - a q)) (g (x - b q))) μ ∧
        ‖action (μ := μ) K a b f g x‖ ^ 2 ≤
          (∫ q, ‖K q‖ ∂μ) * ∫ q, ‖K q‖ * (‖f (x - a q)‖ * D) ^ 2 ∂μ := by
    filter_upwards [he.prod_left_ae, hm.prodMk_right, hmF.prodMk_right] with x hx hmx hfx
    apply WeightedIntegralEnergy.integrable_and_norm_integral_sq_le
      (fun q ↦ ‖K q‖) (fun q ↦ ‖f (x - a q)‖ * D) _ hK.norm (fun _ ↦ norm_nonneg _)
      hfx (fun _ ↦ mul_nonneg (norm_nonneg _) hD) hx hmx
    apply Eventually.of_forall
    intro q
    simpa only [mul_assoc] using (K q).le_of_opNorm₂_le_of_le le_rfl le_rfl (hgb (x - b q))
  have hB := he.integral_prod_right.const_mul (∫ q, ‖K q‖ ∂μ)
  have hE : Integrable (fun x ↦ ‖action (μ := μ) K a b f g x‖ ^ 2) ν := by
    apply hB.mono' (show AEStronglyMeasurable
      (fun x ↦ ‖action (μ := μ) K a b f g x‖ ^ 2) ν from hmA.norm.pow 2)
    filter_upwards [hp] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖action (μ := μ) K a b f g x‖)]
    exact hx.2
  refine ⟨hp.mono (fun _ hx ↦ hx.1), (memLp_two_iff_integrable_sq_norm hmA).mpr hE, ?_⟩
  calc
    _ ≤ ∫ x, (∫ q, ‖K q‖ ∂μ) * ∫ q, ‖K q‖ * (‖f (x - a q)‖ * D) ^ 2 ∂μ ∂ν :=
      integral_mono_ae hE hB (hp.mono (fun _ hx ↦ hx.2))
    _ = _ := by
      simp_rw [mul_pow, ← mul_assoc, integral_mul_const, integral_const_mul]
      rw [integral_mul_const, integral_weighted_translate _ _ hK.norm hf.norm.integrable_sq a ha]
      ring

theorem action_congr_ae (K L : A → E →L[𝕜] F →L[𝕜] G) (hKL : K =ᵐ[μ] L)
    (a b : A → X) (ha : Measurable a) (hb : Measurable b)
    (f f' : X → E) (g g' : X → F) (hf : f =ᵐ[ν] f') (hg : g =ᵐ[ν] g') :
    action (μ := μ) K a b f g =ᵐ[ν] action (μ := μ) L a b f' g' := by
  have hf0 : ∀ᵐ p : A × X ∂μ.prod ν, f p.2 = f' p.2 :=
    (quasiMeasurePreserving_snd (μ := μ) (ν := ν)).tendsto_ae.eventually hf
  have hg0 : ∀ᵐ p : A × X ∂μ.prod ν, g p.2 = g' p.2 :=
    (quasiMeasurePreserving_snd (μ := μ) (ν := ν)).tendsto_ae.eventually hg
  have hK0 : ∀ᵐ p : A × X ∂μ.prod ν, K p.1 = L p.1 :=
    (quasiMeasurePreserving_fst (μ := μ) (ν := ν)).tendsto_ae.eventually hKL
  have he : ∀ᵐ p : A × X ∂μ.prod ν,
      K p.1 (f (p.2 - a p.1)) (g (p.2 - b p.1)) =
        L p.1 (f' (p.2 - a p.1)) (g' (p.2 - b p.1)) := by
    filter_upwards [hK0,
      (measurePreserving_skew_sub a ha).quasiMeasurePreserving.tendsto_ae.eventually hf0,
      (measurePreserving_skew_sub b hb).quasiMeasurePreserving.tendsto_ae.eventually hg0]
      with p hKp hfp hgp
    rw [hKp, hfp, hgp]
  have hes := (measurePreserving_swap (μ := ν) (ν := μ)).quasiMeasurePreserving.tendsto_ae.eventually he
  filter_upwards [ae_ae_of_ae_prod hes] with x hx
  exact integral_congr_ae hx

theorem action_memLp_two_and_energy_le_right (K : A → E →L[𝕜] F →L[𝕜] G)
    (hK : Integrable K μ) (a b : A → X) (ha : Measurable a) (hb : Measurable b)
    (f : X → E) (g : X → F) (hf : AEStronglyMeasurable f ν) (hg : MemLp g 2 ν)
    {D : ℝ} (hD : 0 ≤ D) (hfb : ∀ x, ‖f x‖ ≤ D) :
    (∀ᵐ x ∂ν, Integrable (fun q ↦ K q (f (x - a q)) (g (x - b q))) μ) ∧
      MemLp (action (μ := μ) K a b f g) 2 ν ∧
        (∫ x, ‖action (μ := μ) K a b f g x‖ ^ 2 ∂ν) ≤
          (∫ q, ‖K q‖ ∂μ) ^ 2 * D ^ 2 * ∫ x, ‖g x‖ ^ 2 ∂ν := by
  have hflip : Integrable (fun q ↦ (K q).flip) μ :=
    (ContinuousLinearMap.flipₗᵢ 𝕜 E F G).toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp hK
  have hact : action (μ := μ) (fun q ↦ (K q).flip) b a g f = action (μ := μ) K a b f g := rfl
  simpa only [hact, ContinuousLinearMap.flip_apply, ContinuousLinearMap.opNorm_flip] using
    action_memLp_two_and_energy_le (fun q ↦ (K q).flip) hflip b a hb ha g f hg hf hD hfb

theorem action_sub_left_ae (K : A → E →L[𝕜] F →L[𝕜] G)
    (hK : Integrable K μ) (a b : A → X) (ha : Measurable a) (hb : Measurable b)
    (f f' : X → E) (g : X → F) (hf : MemLp f 2 ν) (hf' : MemLp f' 2 ν)
    (hg : AEStronglyMeasurable g ν) {D : ℝ} (hD : 0 ≤ D) (hgb : ∀ x, ‖g x‖ ≤ D) :
    action (μ := μ) K a b (fun x ↦ f x - f' x) g =ᵐ[ν]
      fun x ↦ action (μ := μ) K a b f g x - action (μ := μ) K a b f' g x := by
  filter_upwards [(action_memLp_two_and_energy_le K hK a b ha hb f g hf hg hD hgb).1,
    (action_memLp_two_and_energy_le K hK a b ha hb f' g hf' hg hD hgb).1] with x hx hx'
  simp only [action, map_sub, sub_apply]
  exact integral_sub hx hx'

theorem action_sub_left_energy_le (K : A → E →L[𝕜] F →L[𝕜] G)
    (hK : Integrable K μ) (a b : A → X) (ha : Measurable a) (hb : Measurable b)
    (f f' : X → E) (g : X → F) (hf : MemLp f 2 ν) (hf' : MemLp f' 2 ν)
    (hg : AEStronglyMeasurable g ν) {D : ℝ} (hD : 0 ≤ D) (hgb : ∀ x, ‖g x‖ ≤ D) :
    (∫ x, ‖action (μ := μ) K a b f g x - action (μ := μ) K a b f' g x‖ ^ 2 ∂ν) ≤
      (∫ q, ‖K q‖ ∂μ) ^ 2 * D ^ 2 * ∫ x, ‖f x - f' x‖ ^ 2 ∂ν := by
  have he := action_sub_left_ae K hK a b ha hb f f' g hf hf' hg hD hgb
  have h := (action_memLp_two_and_energy_le K hK a b ha hb
    (fun x ↦ f x - f' x) g (hf.sub hf') hg hD hgb).2.2
  convert h using 1
  apply integral_congr_ae
  filter_upwards [he] with x hx
  rw [hx]

end Mettapedia.Analysis.BilinearTranslatedKernel
