import Mettapedia.Analysis.WeightedProjectionVariation

/-! # Smoothness of the weighted regularized projection energy at vorticity zeros -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.WeightedProjectionRegularity

open scoped RealInnerProductSpace
open RegularizedProjection WeightedProjectionParabolic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem contDiff_weightedEnergy (δ : ℝ) (hδ : 0 < δ) :
    ContDiff ℝ 1 (fun p : E × E ↦ weightedEnergy δ p.1 p.2) := by
  have hc : ContDiff ℝ 1 (fun p : E × E ↦ coefficient δ p.1 p.2) :=
    (contDiff_fst.inner ℝ contDiff_snd).div
      (contDiff_const.add (contDiff_fst.norm_sq ℝ)) (fun p ↦ by positivity)
  have hr : ContDiff ℝ 1 (fun p : E × E ↦ residual δ p.1 p.2) :=
    contDiff_snd.sub (hc.smul contDiff_fst)
  have h : ContDiff ℝ 1 (fun p : E × E ↦ (‖p.1‖ ^ 2) ^ 3 *
      (‖residual δ p.1 p.2‖ ^ 2 + δ * coefficient δ p.1 p.2 ^ 2)) :=
    ((contDiff_fst.norm_sq ℝ).pow 3).mul
    ((hr.norm_sq ℝ).add (contDiff_const.mul (hc.pow 2)))
  simpa only [weightedEnergy, energy, ← pow_mul, Nat.reduceMul] using h

theorem contDiff_correctedEnergy (δ κ : ℝ) (hδ : 0 < δ) :
    ContDiff ℝ 1 (fun p : E × E ↦ ‖p.1‖ ^ 8 / 8 - 3 / κ * weightedEnergy δ p.1 p.2) := by
  have h : ContDiff ℝ 1 (fun p : E × E ↦ (‖p.1‖ ^ 2) ^ 4 / 8 -
      3 / κ * weightedEnergy δ p.1 p.2) :=
    (((contDiff_fst.norm_sq ℝ).pow 4).div_const 8).sub
    (contDiff_const.mul (contDiff_weightedEnergy (E := E) δ hδ))
  simpa only [← pow_mul, Nat.reduceMul] using h

end Mettapedia.Analysis.WeightedProjectionRegularity
