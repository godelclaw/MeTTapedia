import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LineProjectorTilt

/-!
# Weighted tilt without a continuous eigenline at zero weight

Continuity of `sqrt(a) P` suffices for continuity of the weighted squared
tilt. At a zero of `a`, the elementary bound by `a * norm(R)^2` supplies
the extension. Away from those zeros the projector is recovered by division.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.WeightedProjectorTilt

open Filter PancakeAnisotropyDepletion SpectralTiltFreezing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem norm_transverse_le (R : E →L[ℝ] E) (e : E) (he : ‖e‖ = 1) :
    ‖lineRemainder e (R e)‖ ≤ ‖R‖ :=
  (norm_lineRemainder_le e (R e) he).trans (by simpa only [he, mul_one] using R.le_opNorm e)

theorem continuous_weighted_transverse_norm_sq {X : Type*} [TopologicalSpace X]
    (a : X → ℝ) (ha : Continuous a) (han : ∀ x, 0 ≤ a x)
    (R : X → E →L[ℝ] E) (hR : Continuous R) (e : X → E) (he : ∀ x, ‖e x‖ = 1)
    (hP : Continuous (fun x ↦ Real.sqrt (a x) • InnerProductSpace.rankOne ℝ (e x) (e x))) :
    Continuous (fun x ↦ a x * ‖lineRemainder (e x) (R x (e x))‖ ^ 2) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hz : a x = 0
  · have hb : Tendsto (fun y ↦ a y * ‖R y‖ ^ 2) (nhds x) (nhds 0) := by
      have hb' : ContinuousAt (fun y ↦ a y * ‖R y‖ ^ 2) x :=
        ha.continuousAt.mul (hR.norm.pow 2).continuousAt
      simpa only [ContinuousAt, hz, zero_mul] using hb'
    have h := squeeze_zero (fun y ↦ mul_nonneg (han y) (sq_nonneg _))
      (fun y ↦ mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (norm_transverse_le (R y) (e y) (he y)) 2) (han y)) hb
    simpa only [ContinuousAt, hz, zero_mul] using h
  · have hp : 0 < a x := lt_of_le_of_ne (han x) (Ne.symm hz)
    have hloc : ∀ᶠ y in nhds x, 0 < a y := ha.continuousAt.eventually (lt_mem_nhds hp)
    have hPi : ContinuousAt (fun y ↦ InnerProductSpace.rankOne ℝ (e y) (e y)) x := by
      have h := ((ha.sqrt.continuousAt).inv₀ (ne_of_gt (Real.sqrt_pos.2 hp))).smul hP.continuousAt
      apply h.congr_of_eventuallyEq
      filter_upwards [hloc] with y hy
      simp only [smul_smul, inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.2 hy)), one_smul]
    have ht : ContinuousAt (fun y ↦ ‖(ContinuousLinearMap.id ℝ E -
        InnerProductSpace.rankOne ℝ (e y) (e y)) * R y *
          InnerProductSpace.rankOne ℝ (e y) (e y)‖ ^ 2) x :=
      (((continuousAt_const.sub hPi).mul hR.continuousAt).mul hPi).norm.pow 2
    have hprod : ContinuousAt (fun y ↦ a y * ‖(ContinuousLinearMap.id ℝ E -
        InnerProductSpace.rankOne ℝ (e y) (e y)) * R y *
          InnerProductSpace.rankOne ℝ (e y) (e y)‖ ^ 2) x := ha.continuousAt.mul ht
    simpa only [LineProjectorTilt.norm_transverse_projector_action _ _ (he _)] using hprod

/-- Replacing exact nonnegative cell weights by approximate weights costs
only their total absolute error times operator energy. -/
theorem weighted_transverse_le_approximation {ι : Type*} [Fintype ι]
    (R : E →L[ℝ] E) (e : E) (f : ι → E) (he : ‖e‖ = 1) (hf : ∀ i, ‖f i‖ = 1)
    (w v : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (a B delta : ℝ)
    (hcover : a ≤ ∑ i, w i) (hframe : (∑ i, w i * lineDistanceSq e (f i)) ≤ B)
    (herror : (∑ i, |v i - w i|) ≤ delta) :
    a * ‖lineRemainder e (R e)‖ ^ 2 ≤
      2 * (∑ i, v i * ‖lineRemainder (f i) (R (f i))‖ ^ 2) +
        (32 * B + 2 * delta) * ‖R‖ ^ 2 := by
  have h := weighted_transverse_action_sq_le R e f w he hf hw a B hcover hframe
  have hcell (i : ι) : w i * ‖lineRemainder (f i) (R (f i))‖ ^ 2 ≤
      v i * ‖lineRemainder (f i) (R (f i))‖ ^ 2 + |v i - w i| * ‖R‖ ^ 2 := by
    have hdiff : w i - v i ≤ |v i - w i| := by simpa only [neg_sub] using neg_le_abs (v i - w i)
    have h1 := mul_le_mul_of_nonneg_right hdiff (sq_nonneg ‖lineRemainder (f i) (R (f i))‖)
    have h2 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (norm_transverse_le R (f i) (hf i)) 2) (abs_nonneg (v i - w i))
    nlinarith only [h1, h2]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ hcell i)
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul] at hs
  have he := mul_le_mul_of_nonneg_right herror (sq_nonneg ‖R‖)
  nlinarith only [h, hs, he]

end Mettapedia.FluidDynamics.NavierStokes.WeightedProjectorTilt
