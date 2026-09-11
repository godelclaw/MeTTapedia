import Mettapedia.Analysis.BilinearKernelLocalization
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Integrable operator kernels acting on bounded fields

An integrable operator-norm kernel acts on bounded strongly measurable
inputs. Continuity of the kernel is not required. On a compact parameter
space, continuous fields supply the bounds, including the scalar-weight
localization density.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.BilinearKernelIntegrability

open MeasureTheory Filter

variable {𝕜 E F G α : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable [MeasurableSpace α] {μ : Measure α}

local instance : NormedAddCommGroup (E →L[𝕜] F) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedAddCommGroup (F →L[𝕜] G) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace 𝕜 (F →L[𝕜] G) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (E →L[𝕜] F →L[𝕜] G) := ContinuousLinearMap.toNormedAddCommGroup

theorem integrable_clm_apply_bounded (K : α → E →L[𝕜] F) (u : α → E)
    (hK : Integrable K μ) (hu : AEStronglyMeasurable u μ) {C : ℝ}
    (hbound : ∀ᵐ x ∂μ, ‖u x‖ ≤ C) : Integrable (fun x ↦ K x (u x)) μ := by
  have hm : AEStronglyMeasurable (fun x ↦ K x (u x)) μ :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hK.aestronglyMeasurable.prodMk hu)
  apply (hK.norm.mul_const C).mono' hm
  filter_upwards [hbound] with x hx
  exact ((K x).le_opNorm (u x)).trans (mul_le_mul_of_nonneg_left hx (norm_nonneg _))

theorem integrable_bilinear_apply_bounded (K : α → E →L[𝕜] F →L[𝕜] G)
    (u : α → E) (v : α → F) (hK : Integrable K μ)
    (hu : AEStronglyMeasurable u μ) (hv : AEStronglyMeasurable v μ)
    {C D : ℝ} (hC : ∀ᵐ x ∂μ, ‖u x‖ ≤ C) (hD : ∀ᵐ x ∂μ, ‖v x‖ ≤ D) :
    Integrable (fun x ↦ K x (u x) (v x)) μ :=
  integrable_clm_apply_bounded _ v (integrable_clm_apply_bounded K u hK hu hC) hv hD

section Compact

variable [TopologicalSpace α] [CompactSpace α] [BorelSpace α]

theorem integrable_bilinear_apply_continuous (K : α → E →L[𝕜] F →L[𝕜] G)
    (u : α → E) (v : α → F) (hK : Integrable K μ)
    (hu : Continuous u) (hv : Continuous v) : Integrable (fun x ↦ K x (u x) (v x)) μ := by
  exact integrable_bilinear_apply_bounded K u v hK
    (hu.stronglyMeasurable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).aestronglyMeasurable
    (hv.stronglyMeasurable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).aestronglyMeasurable
    (Eventually.of_forall (fun x ↦ (⟨u, hu⟩ : C(α, E)).norm_coe_le_norm x))
    (Eventually.of_forall (fun x ↦ (⟨v, hv⟩ : C(α, F)).norm_coe_le_norm x))

theorem integrable_norm_kernel_mul_continuous (K : α → E →L[𝕜] F →L[𝕜] G)
    (b : α → ℝ) (hK : Integrable K μ) (hb : Continuous b) :
    Integrable (fun x ↦ ‖K x‖ * b x) μ :=
  hK.norm.mul_bdd hb.aestronglyMeasurable
    (Eventually.of_forall (fun x ↦ (⟨b, hb⟩ : C(α, ℝ)).norm_coe_le_norm x))

theorem integrable_localization_density (K : α → E →L[𝕜] F →L[𝕜] G)
    (u : α → E) (v : α → F) (a b : α → 𝕜) (c d : 𝕜)
    (hK : Integrable K μ) (hu : Continuous u) (hv : Continuous v)
    (ha : Continuous a) (hb : Continuous b) :
    Integrable (fun q ↦ ‖K q‖ * (‖d‖ * (‖c - a q‖ * ‖u q‖) * ‖v q‖ +
      ‖a q‖ * ‖u q‖ * (‖d - b q‖ * ‖v q‖))) μ :=
  integrable_norm_kernel_mul_continuous K _ hK (by fun_prop)

end Compact

end Mettapedia.Analysis.BilinearKernelIntegrability
