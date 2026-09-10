import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.AdaptiveLinePartition

/-!
# Freezing a weighted line through a vanishing amplitude

The field `sqrt(a) P` can be continuous even where the unit line has no
continuous extension. Its operator distance controls `a` times the line
error. Thus adaptive cells need not impose a global spectral gap.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.WeightedLineFreezing

open scoped RealInnerProductSpace BigOperators
open PancakeAnisotropyDepletion SpectralTiltFreezing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem sq_mul_lineDistanceSq_le (e f : E) (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (r s : ℝ) :
    r ^ 2 * lineDistanceSq e f ≤
      2 * ‖r • InnerProductSpace.rankOne ℝ e e - s • InnerProductSpace.rankOne ℝ f f‖ ^ 2 := by
  let D := r • InnerProductSpace.rankOne ℝ e e - s • InnerProductSpace.rankOne ℝ f f
  have hid : lineRemainder f (D e) = r • lineRemainder f e := by
    simp only [D, sub_apply, smul_apply, InnerProductSpace.rankOne_apply,
      real_inner_self_eq_norm_sq, he, one_pow, one_smul, lineRemainder,
      inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hf,
      one_pow, mul_one, smul_sub, sub_smul, smul_smul]
    module
  have hn := (norm_lineRemainder_le f (D e) hf).trans (D.le_opNorm e)
  rw [hid, norm_smul, he, mul_one] at hn
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ ‖r‖ * ‖lineRemainder f e‖) hn 2
  rw [mul_pow, Real.norm_eq_abs, sq_abs] at hs
  have hl := mul_le_mul_of_nonneg_left (lineDistanceSq_le_two_mul_remainder_sq e f he hf) (sq_nonneg r)
  nlinarith only [hl, hs]

theorem mul_lineDistanceSq_le (e f : E) (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (a b : ℝ) (ha : 0 ≤ a) :
    a * lineDistanceSq e f ≤
      2 * ‖Real.sqrt a • InnerProductSpace.rankOne ℝ e e -
        Real.sqrt b • InnerProductSpace.rankOne ℝ f f‖ ^ 2 := by
  simpa only [Real.sq_sqrt ha] using sq_mul_lineDistanceSq_le e f he hf (Real.sqrt a) (Real.sqrt b)

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

/-- The active-cell error includes the spatial weight. No regularity of
the signed unit representatives is required, including at zero weight. -/
theorem exists_partition_of_continuous_weighted_projector
    (a : T3 → ℝ) (ha : ∀ x, 0 ≤ a x) (e : T3 → R3) (he : ∀ x, ‖e x‖ = 1)
    (hP : Continuous (fun x ↦ Real.sqrt (a x) • InnerProductSpace.rankOne ℝ (e x) (e x)))
    (rho : ℝ) (hr : 0 < rho) :
    ∃ (centers : Finset T3) (weight : PartitionOfUnity ↑centers T3),
      ∀ i x, weight i x ≠ 0 → a x * lineDistanceSq (e x) (e i.1) ≤ rho ^ 2 := by
  obtain ⟨centers, weight, _, hactive⟩ :=
    PancakeAdaptiveStrainCover.exists_finite_adaptive_spatial_strain_partition _ hP
      (show 0 < rho / 2 by positivity)
  refine ⟨centers, weight, ?_⟩
  intro i x hx
  have h := mul_lineDistanceSq_le (e x) (e i.1) (he x) (he i.1) (a x) (a i.1) (ha x)
  have hc := hactive i x hx
  have hs := pow_le_pow_left₀ (norm_nonneg _) hc.le 2
  nlinarith only [h, hs, sq_nonneg rho]

end Mettapedia.FluidDynamics.NavierStokes.WeightedLineFreezing
