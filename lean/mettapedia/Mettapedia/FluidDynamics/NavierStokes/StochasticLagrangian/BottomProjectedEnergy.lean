import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.BottomProjectorMotion
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FilteredStrainTrace

/-!
# Unnormalized vorticity energy in the bottom strain eigenspace

The energy is a sign-invariant projector quadratic form and remains
defined at vorticity zeros. Its exact rate retains the signed forcing
pairing. Trace-free strain supplies damping before projector motion is paid.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.BottomProjectedEnergy

open scoped RealInnerProductSpace
open PancakeEigenframePerturbation PancakeSpectralProjectorRegularity
open PancakeSpectralProjectorRegularity.SymmetricStrain PancakeSpectralClusterDichotomy.SymmetricStrain
open BottomProjectorMotion RankOneProjectorTangent FilteredStrainTrace

local notation "R3" => EuclideanSpace ℝ (Fin 3)

def energy (S : SymmetricStrain) (w : R3) : ℝ := ‖bottomEigenlineProjector S w‖ ^ 2

theorem energy_nonneg (S : SymmetricStrain) (w : R3) : 0 ≤ energy S w := sq_nonneg _

theorem energy_eq_inner (S : SymmetricStrain) (w : R3) :
    energy S w = ⟪w, bottomEigenlineProjector S w⟫ := by
  change ‖⟪bottomVector S, w⟫ • bottomVector S‖ ^ 2 = ⟪w, ⟪bottomVector S, w⟫ • bottomVector S⟫
  rw [norm_smul, bottomVector_norm, mul_one, Real.norm_eq_abs, sq_abs,
    real_inner_smul_right, real_inner_comm w (bottomVector S)]
  ring

theorem inner_bottomProjector_strain (S : SymmetricStrain) (w : R3) :
    ⟪bottomEigenlineProjector S w, S.1 w⟫ = thirdEigenvalue S * energy S w := by
  have he := congrArg (fun A : R3 →L[ℝ] R3 ↦ A w) (strain_mul_bottomProjector S)
  change S.1 (bottomEigenlineProjector S w) = thirdEigenvalue S • bottomEigenlineProjector S w at he
  calc
    _ = ⟪S.1 (bottomEigenlineProjector S w), w⟫ := S.2 _ _
    _ = thirdEigenvalue S * ⟪bottomEigenlineProjector S w, w⟫ := by rw [he, real_inner_smul_left]
    _ = _ := by
      rw [energy_eq_inner]
      congr 1
      exact real_inner_comm _ _

def rate (S : SymmetricStrain) (w f : R3) (D : R3 →L[ℝ] R3) : ℝ :=
  2 * thirdEigenvalue S * energy S w + 2 * ⟪bottomEigenlineProjector S w, f⟫ + ⟪w, D w⟫

theorem hasDerivAt_energy (S : ℝ → SymmetricStrain) (w : ℝ → R3)
    (D : R3 →L[ℝ] R3) (v : R3) (t : ℝ)
    (hP : HasDerivAt (fun τ ↦ bottomEigenlineProjector (S τ)) D t)
    (hw : HasDerivAt w v t) :
    HasDerivAt (fun τ ↦ energy (S τ) (w τ))
      (2 * ⟪bottomEigenlineProjector (S t) (w t), v⟫ + ⟪w t, D (w t)⟫) t := by
  simp_rw [energy_eq_inner]
  apply (hw.inner ℝ (hP.clm_apply hw)).congr_deriv
  have hs : ⟪bottomEigenlineProjector (S t) (w t), v⟫ =
      ⟪w t, bottomEigenlineProjector (S t) v⟫ :=
    (lineProjector_isSelfAdjoint (bottomVector (S t))).isSymmetric (w t) v
  rw [inner_add_right, ← hs, real_inner_comm v (bottomEigenlineProjector (S t) (w t))]
  ring

theorem hasDerivAt_energy_of_strainEquation (S : ℝ → SymmetricStrain) (w : ℝ → R3)
    (D : R3 →L[ℝ] R3) (f : R3) (t : ℝ)
    (hP : HasDerivAt (fun τ ↦ bottomEigenlineProjector (S τ)) D t)
    (hw : HasDerivAt w ((S t).1 (w t) + f) t) :
    HasDerivAt (fun τ ↦ energy (S τ) (w τ)) (rate (S t) (w t) f D) t := by
  apply (hasDerivAt_energy S w D _ t hP hw).congr_deriv
  rw [inner_add_right, inner_bottomProjector_strain]
  unfold rate
  ring

/-- Only projector transfer is absorbed here. The vector forcing, which
may contain viscosity, remains in its signed pairing. -/
theorem rate_add_gap_damping_le (S : SymmetricStrain) (w f : R3)
    (D : R3 →L[ℝ] R3) (cost : ℝ)
    (htrace : LinearMap.trace ℝ R3 S.1.toLinearMap = 0)
    (hD : |⟪w, D w⟫| ≤ bottomGap S * energy S w + cost) :
    rate S w f D + (bottomGap S / 3) * energy S w ≤
      2 * ⟪bottomEigenlineProjector S w, f⟫ + cost := by
  have hd := mul_le_mul_of_nonneg_right
    (thirdEigenvalue_le_neg_two_thirds_bottomGap S htrace) (energy_nonneg S w)
  have hm := (abs_le.mp hD).2
  unfold rate
  nlinarith

end Mettapedia.FluidDynamics.NavierStokes.BottomProjectedEnergy
