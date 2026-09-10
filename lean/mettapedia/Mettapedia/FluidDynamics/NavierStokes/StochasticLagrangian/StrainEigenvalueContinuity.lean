import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeTopEigenvalueDerivative
import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Continuity of the ordered three-dimensional strain spectrum

The extreme eigenvalues satisfy the existing Weyl bounds. The middle
eigenvalue is the trace minus the extremes, so both adjacent gaps are
continuous through collisions without an eigenvector selection.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.StrainEigenvalueContinuity

open scoped RealInnerProductSpace
open PancakeStrainSpectralFrame PancakeSpectralProjectorRegularity
open PancakeSpectralProjectorRegularity.SymmetricStrain PancakeSpectralClusterDichotomy
open PancakeSpectralClusterDichotomy.SymmetricStrain
open PancakeTopEigenvalueDerivative

local notation "R3" => EuclideanSpace ℝ (Fin 3)

theorem lipschitzWith_thirdEigenvalue : LipschitzWith 1 thirdEigenvalue := by
  apply LipschitzWith.of_dist_le_mul
  intro A B
  simpa only [NNReal.coe_one, one_mul, Subtype.dist_eq, dist_eq_norm,
    Real.norm_eq_abs, thirdEigenvalue]
    using abs_constructedBottomEigenvalue_sub_le A.1 B.1 A.2 B.2

theorem trace_eq_sum_orderedEigenvalues (S : SymmetricStrain) :
    LinearMap.trace ℝ R3 S.1.toLinearMap =
      topEigenvalue S + secondEigenvalue S + thirdEigenvalue S := by
  rw [LinearMap.trace_eq_sum_inner _ (orderedEigenframe S.1 S.2).eigenbasis]
  simp only [ContinuousLinearMap.coe_coe, (orderedEigenframe S.1 S.2).apply_eigenbasis,
    real_inner_smul_right, real_inner_self_eq_norm_sq,
    (orderedEigenframe S.1 S.2).eigenbasis.norm_eq_one, one_pow, mul_one]
  simp [Fin.sum_univ_succ, topEigenvalue, secondEigenvalue, thirdEigenvalue, add_assoc]

theorem continuous_trace : Continuous (fun S : SymmetricStrain ↦
    LinearMap.trace ℝ R3 S.1.toLinearMap) := by
  simp_rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin 3) ℝ)]
  exact continuous_finsetSum _ (fun _ _ ↦ continuous_const.inner
    (continuous_subtype_val.clm_apply continuous_const))

theorem continuous_secondEigenvalue : Continuous secondEigenvalue := by
  have he (S : SymmetricStrain) : secondEigenvalue S =
      LinearMap.trace ℝ R3 S.1.toLinearMap - topEigenvalue S - thirdEigenvalue S := by
    rw [trace_eq_sum_orderedEigenvalues]
    ring
  simp_rw [show secondEigenvalue = fun S ↦
    LinearMap.trace ℝ R3 S.1.toLinearMap - topEigenvalue S - thirdEigenvalue S from funext he]
  exact (continuous_trace.sub lipschitzWith_topEigenvalue.continuous).sub
    lipschitzWith_thirdEigenvalue.continuous

theorem continuous_topGap : Continuous topGap :=
  lipschitzWith_topEigenvalue.continuous.sub continuous_secondEigenvalue

theorem continuous_bottomGap : Continuous bottomGap :=
  continuous_secondEigenvalue.sub lipschitzWith_thirdEigenvalue.continuous

end Mettapedia.FluidDynamics.NavierStokes.StrainEigenvalueContinuity
