import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SpectralCommutatorLimit

/-!
# Commutator-envelope regressions

A source equal to strain has only the quadratic channel on a separated
top eigenspace. At a triple collision, however, even a commuting rank-one
source has nonzero anisotropy. This is an instantaneous operator test,
not a solution of the strain equation or a Navier–Stokes counterexample.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.SpectralSourceCommutatorTests

open scoped RealInnerProductSpace
open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakeSpectralFiniteDifference PancakeSpectralDefectEvolution PancakeStrainSpectralFrame
open PancakeSpectralResidualDepletion SpectralSourceCommutator SpectralDiffusionWeightLimit

local notation "R3" => EuclideanSpace ℝ (Fin 3)

example (S : SymmetricStrain) (w : R3) (hg : 0 < topGap S) :
    SpectralCommutatorLimit.limitingEnvelope S S.1 w ≤ 2 * ‖S.1‖ * limitingWeight S w :=
  SpectralCommutatorLimit.limitingEnvelope_le_quadratic_of_commutator_eq_zero S S.1 w hg (commutator_self S)

private def zeroStrain : SymmetricStrain := ⟨0, fun _ _ ↦ by simp⟩

private theorem zeroStrain_gap : topGap zeroStrain = 0 := by
  have hz (i : Fin 3) : (orderedEigenframe zeroStrain.1 zeroStrain.2).eigenvalue i = 0 := by
    have h := abs_orderedEigenvalue_le_opNorm zeroStrain i
    simpa only [zeroStrain, norm_zero, abs_nonpos_iff] using h
  exact sub_eq_zero.mpr ((hz 0).trans (hz 1).symm)

theorem exists_commuting_zero_gap_source_with_nonzero_anisotropy :
    ∃ (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3),
      topGap S = 0 ∧ commutator S R = 0 ∧ ‖w‖ = 1 ∧
      remainderAnisotropy R (topVector S) w = 1 ∧
      SpectralCommutatorLimit.limitingEnvelope S R w = 2 := by
  let e := topVector zeroStrain
  let w := (orderedEigenframe zeroStrain.1 zeroStrain.2).eigenbasis 1
  let R := InnerProductSpace.rankOne ℝ e e
  have he : ‖e‖ = 1 := topVector_norm _
  have hw : ‖w‖ = 1 := (orderedEigenframe zeroStrain.1 zeroStrain.2).eigenbasis.norm_eq_one 1
  have hew : ⟪e, w⟫ = 0 :=
    (orderedEigenframe zeroStrain.1 zeroStrain.2).eigenbasis.inner_eq_zero (by decide : (0 : Fin 3) ≠ 1)
  have hR : ‖R‖ = 1 := by simp only [R, InnerProductSpace.norm_rankOne, he, mul_one]
  refine ⟨zeroStrain, R, w, zeroStrain_gap, ?_, hw, ?_, ?_⟩
  · change (0 : R3 →L[ℝ] R3) * R - R * 0 = 0
    simp only [zero_mul, mul_zero, sub_self]
  · change ⟪e, R e⟫ * ‖w‖ ^ 2 - ⟪w, R w⟫ = 1
    simp only [R, InnerProductSpace.rankOne_apply, hew, zero_smul, inner_zero_right,
      real_inner_smul_right, real_inner_self_eq_norm_sq, he, hw]
    norm_num
  · rw [SpectralCommutatorLimit.limitingEnvelope_eq_coarse_of_topGap_zero _ _ _ zeroStrain_gap, hR, hw]
    norm_num

end Mettapedia.FluidDynamics.NavierStokes.SpectralSourceCommutatorTests
