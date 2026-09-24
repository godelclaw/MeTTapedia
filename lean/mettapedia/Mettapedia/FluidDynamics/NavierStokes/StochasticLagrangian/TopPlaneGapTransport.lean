import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.StrainEigenvalueRates
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SpectralClusterAnisotropy

/-!
# Spectral-gap evolution and mixing in the expanding plane

The top-plane anisotropy is not small merely because the top gap is small.
Its exact diagonal contribution contains the derivative of that gap; its
off-diagonal contribution contains mixing inside the plane. Only the
remaining transverse part is estimated using the bottom gap.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.TopPlaneGapTransport

open scoped Topology RealInnerProductSpace
open PancakeStrainSpectralFrame PancakeSpectralProjectorRegularity
open PancakeSpectralProjectorRegularity.SymmetricStrain PancakeSpectralClusterDichotomy.SymmetricStrain
open PancakeSpectralFiniteDifference PancakeSpectralDefectEvolution PancakeAnisotropyDepletion
open SpectralClusterAnisotropy StrainEigenvalueRates

local notation "R3" => EuclideanSpace ℝ (Fin 3)

def planeWeight (S : SymmetricStrain) (w : R3) : ℝ :=
  ⟪(orderedEigenframe S.1 S.2).eigenbasis 1, w⟫ ^ 2

def planeMixing (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3) : ℝ :=
  ⟪(orderedEigenframe S.1 S.2).eigenbasis 0, w⟫ *
    ⟪(orderedEigenframe S.1 S.2).eigenbasis 1, w⟫ *
    (⟪(orderedEigenframe S.1 S.2).eigenbasis 0, R ((orderedEigenframe S.1 S.2).eigenbasis 1)⟫ +
      ⟪(orderedEigenframe S.1 S.2).eigenbasis 1, R ((orderedEigenframe S.1 S.2).eigenbasis 0)⟫)

def planeSource (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3) (gapRate : ℝ) : ℝ :=
  planeWeight S w * (gapRate + (topEigenvalue S + secondEigenvalue S) * topGap S) - planeMixing S R w

/-- Top-gap rate prescribed by the strain equation `S' = -S² + R`. -/
def topGapStrainRate (S : SymmetricStrain) (R : R3 →L[ℝ] R3) : ℝ :=
  -(topEigenvalue S + secondEigenvalue S) * topGap S +
    ⟪(orderedEigenframe S.1 S.2).eigenbasis 0, R ((orderedEigenframe S.1 S.2).eigenbasis 0)⟫ -
    ⟪(orderedEigenframe S.1 S.2).eigenbasis 1, R ((orderedEigenframe S.1 S.2).eigenbasis 1)⟫

theorem inner_strainEquation_diagonal (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (i : Fin 3) :
    ⟪(orderedEigenframe S.1 S.2).eigenbasis i,
      (-S.1 * S.1 + R) ((orderedEigenframe S.1 S.2).eigenbasis i)⟫ =
      -(orderedEigenframe S.1 S.2).eigenvalue i ^ 2 +
        ⟪(orderedEigenframe S.1 S.2).eigenbasis i, R ((orderedEigenframe S.1 S.2).eigenbasis i)⟫ := by
  simp only [add_apply, mul_apply_eq_comp, neg_apply, (orderedEigenframe S.1 S.2).apply_eigenbasis,
    map_smul, inner_add_right, inner_neg_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, (orderedEigenframe S.1 S.2).eigenbasis.norm_eq_one]
  ring

theorem hasDerivAt_topGap_strainEquation (S : ℝ → SymmetricStrain)
    (R : R3 →L[ℝ] R3) (t : ℝ)
    (hS : HasDerivAt (fun τ ↦ (S τ).1) (-(S t).1 * (S t).1 + R) t)
    (htop : DifferentiableAt ℝ (fun τ ↦ topEigenvalue (S τ)) t)
    (hbottom : DifferentiableAt ℝ (fun τ ↦ thirdEigenvalue (S τ)) t) :
    HasDerivAt (fun τ ↦ topGap (S τ))
      (-(topEigenvalue (S t) + secondEigenvalue (S t)) * topGap (S t) +
        ⟪(orderedEigenframe (S t).1 (S t).2).eigenbasis 0,
          R ((orderedEigenframe (S t).1 (S t).2).eigenbasis 0)⟫ -
        ⟪(orderedEigenframe (S t).1 (S t).2).eigenbasis 1,
          R ((orderedEigenframe (S t).1 (S t).2).eigenbasis 1)⟫) t := by
  apply (hasDerivAt_topGap S _ t hS htop hbottom).congr_deriv
  rw [inner_strainEquation_diagonal, inner_strainEquation_diagonal]
  simp only [topGap, topEigenvalue, secondEigenvalue]
  ring

theorem remainder_diagonal_difference_eq_gapRate (S : ℝ → SymmetricStrain)
    (R : R3 →L[ℝ] R3) (t : ℝ)
    (hS : HasDerivAt (fun τ ↦ (S τ).1) (-(S t).1 * (S t).1 + R) t)
    (htop : DifferentiableAt ℝ (fun τ ↦ topEigenvalue (S τ)) t)
    (hbottom : DifferentiableAt ℝ (fun τ ↦ thirdEigenvalue (S τ)) t) :
    ⟪(orderedEigenframe (S t).1 (S t).2).eigenbasis 0,
        R ((orderedEigenframe (S t).1 (S t).2).eigenbasis 0)⟫ -
      ⟪(orderedEigenframe (S t).1 (S t).2).eigenbasis 1,
        R ((orderedEigenframe (S t).1 (S t).2).eigenbasis 1)⟫ =
      deriv (fun τ ↦ topGap (S τ)) t +
        (topEigenvalue (S t) + secondEigenvalue (S t)) * topGap (S t) := by
  rw [(hasDerivAt_topGap_strainEquation S R t hS htop hbottom).deriv]
  ring

theorem remainderAnisotropy_expandingPlane_eq (S : SymmetricStrain)
    (R : R3 →L[ℝ] R3) (w : R3) :
    remainderAnisotropy R (topVector S) (expandingPlaneProjector S w) =
      planeWeight S w *
        (⟪(orderedEigenframe S.1 S.2).eigenbasis 0, R ((orderedEigenframe S.1 S.2).eigenbasis 0)⟫ -
          ⟪(orderedEigenframe S.1 S.2).eigenbasis 1, R ((orderedEigenframe S.1 S.2).eigenbasis 1)⟫) -
        planeMixing S R w := by
  rw [expandingPlaneProjector_apply]
  simp only [remainderAnisotropy, topVector, planeWeight, planeMixing, ← real_inner_self_eq_norm_sq,
    map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    (orderedEigenframe S.1 S.2).eigenbasis.inner_eq_ite]
  norm_num
  ring

theorem remainderAnisotropy_expandingPlane_eq_planeSource (S : ℝ → SymmetricStrain)
    (R : R3 →L[ℝ] R3) (t : ℝ)
    (hS : HasDerivAt (fun τ ↦ (S τ).1) (-(S t).1 * (S t).1 + R) t)
    (htop : DifferentiableAt ℝ (fun τ ↦ topEigenvalue (S τ)) t)
    (hbottom : DifferentiableAt ℝ (fun τ ↦ thirdEigenvalue (S τ)) t) (w : R3) :
    remainderAnisotropy R (topVector (S t)) (expandingPlaneProjector (S t) w) =
      planeSource (S t) R w (deriv (fun τ ↦ topGap (S τ)) t) := by
  rw [remainderAnisotropy_expandingPlane_eq, remainder_diagonal_difference_eq_gapRate S R t hS htop hbottom]
  rfl

/-- This estimate also applies for small positive top gaps. The signed
gap-rate and plane-mixing terms remain explicit instead of being discarded. -/
theorem abs_remainderAnisotropy_sub_planeSource_le (S : ℝ → SymmetricStrain)
    (R : R3 →L[ℝ] R3) (t : ℝ)
    (hS : HasDerivAt (fun τ ↦ (S τ).1) (-(S t).1 * (S t).1 + R) t)
    (htop : DifferentiableAt ℝ (fun τ ↦ topEigenvalue (S τ)) t)
    (hbottom : DifferentiableAt ℝ (fun τ ↦ thirdEigenvalue (S τ)) t)
    (hg : 0 < bottomGap (S t)) (w : R3) :
    |remainderAnisotropy R (topVector (S t)) w -
      planeSource (S t) R w (deriv (fun τ ↦ topGap (S τ)) t)| ≤
      4 * ‖R‖ * ‖w‖ * Real.sqrt (topSpectralDefect (S t) w / bottomGap (S t)) := by
  rw [← remainderAnisotropy_expandingPlane_eq_planeSource S R t hS htop hbottom]
  calc
    _ ≤ 2 * ‖R‖ * (‖w‖ + ‖expandingPlaneProjector (S t) w‖) *
        ‖w - expandingPlaneProjector (S t) w‖ :=
      abs_remainderAnisotropy_sub_le R _ _ w (topVector_norm (S t))
    _ ≤ 2 * ‖R‖ * (‖w‖ + ‖w‖) * Real.sqrt (topSpectralDefect (S t) w / bottomGap (S t)) := by
      gcongr
      · exact norm_expandingPlaneProjector_apply_le (S t) w
      · exact norm_sub_expandingPlaneProjector_le (S t) hg w
    _ = _ := by ring

end Mettapedia.FluidDynamics.NavierStokes.TopPlaneGapTransport
