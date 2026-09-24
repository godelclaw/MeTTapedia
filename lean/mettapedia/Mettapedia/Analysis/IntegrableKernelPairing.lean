import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Integrable kernels acting on continuous scalar fields

The kernel need not be continuous or bounded. Its integrable norm suffices
to define a bounded linear functional and pass through uniformly convergent
field series. This is a fixed-kernel bound, not a uniform kernel-mass claim.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.IntegrableKernelPairing

open MeasureTheory
variable {X 𝕜 : Type*} [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [OpensMeasurableSpace X] [RCLike 𝕜]
  (μ : Measure X) (K : X → 𝕜) (hK : Integrable K μ)

include hK

theorem integrable_mul (f : C(X, 𝕜)) : Integrable (fun x ↦ K x * f x) μ :=
  hK.mul_bdd f.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall f.norm_coe_le_norm)

def pairingLinear : C(X, 𝕜) →ₗ[𝕜] 𝕜 where
  toFun f := ∫ x, K x * f x ∂μ
  map_add' f g := by
    simp only [ContinuousMap.add_apply, mul_add]
    exact integral_add (integrable_mul μ K hK f) (integrable_mul μ K hK g)
  map_smul' a f := by
    simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_left_comm (K _) a,
      integral_const_mul, RingHom.id_apply]

theorem norm_pairingLinear_le (f : C(X, 𝕜)) :
    ‖pairingLinear μ K hK f‖ ≤ (∫ x, ‖K x‖ ∂μ) * ‖f‖ := by
  change ‖∫ x, K x * f x ∂μ‖ ≤ _
  have hb := norm_integral_le_of_norm_le (f := fun x ↦ K x * f x) (hK.norm.mul_const ‖f‖)
    (Filter.Eventually.of_forall (fun x ↦ by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm x) (norm_nonneg _)))
  simpa only [integral_mul_const] using hb

def pairingCLM : C(X, 𝕜) →L[𝕜] 𝕜 :=
  (pairingLinear μ K hK).mkContinuous (∫ x, ‖K x‖ ∂μ) (norm_pairingLinear_le μ K hK)

@[simp] theorem pairingCLM_apply (f : C(X, 𝕜)) :
    pairingCLM μ K hK f = ∫ x, K x * f x ∂μ := rfl

end Mettapedia.Analysis.IntegrableKernelPairing
