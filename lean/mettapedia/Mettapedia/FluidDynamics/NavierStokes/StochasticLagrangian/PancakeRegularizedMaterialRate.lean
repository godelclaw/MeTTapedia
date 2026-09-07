import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSpectralFiniteDifference

/-!
# The full regularized material energy rate

The linear response is the derivative of the actual regularized spectral
energy whenever its largest eigenvalue is differentiable in time. Its
decomposition retains the regularization's extra stretching and forcing.
The error estimate permits replacing a viscous direction by finite spatial
increments without separately integrating a chosen eigenframe's terms.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeRegularizedMaterialRate

open scoped RealInnerProductSpace
open PancakeSpectralFiniteDifference PancakeRegularizedDiffusion PancakeSpectralDefectEvolution
open PancakeStrainSpectralFrame PancakeSpectralProjectorRegularity
open PancakeSpectralProjectorRegularity.SymmetricStrain

local notation "R3" => EuclideanSpace ℝ (Fin 3)

def linearRate (S : SymmetricStrain) (delta : ℝ) (w : R3)
    (R : R3 →L[ℝ] R3) (f : R3) : ℝ :=
  remainderAnisotropy R (topVector S) w + 2 * ⟪regularizedGap S delta w, f⟫

theorem incrementRate_eq_linearRate (S T : SymmetricStrain) (delta : ℝ) (w v : R3) :
    incrementRate S T delta w v = linearRate S delta w (T.1 - S.1) v := rfl

theorem linearRate_add (S : SymmetricStrain) (delta : ℝ) (w : R3)
    (R T : R3 →L[ℝ] R3) (f g : R3) :
    linearRate S delta w (R + T) (f + g) = linearRate S delta w R f + linearRate S delta w T g := by
  simp only [linearRate, remainderAnisotropy_add, inner_add_right]
  ring

theorem linearRate_smul (S : SymmetricStrain) (delta c : ℝ) (w : R3)
    (R : R3 →L[ℝ] R3) (f : R3) :
    linearRate S delta w (c • R) (c • f) = c * linearRate S delta w R f := by
  simp only [linearRate, remainderAnisotropy, smul_apply, real_inner_smul_right]
  ring

theorem linearRate_sub (S : SymmetricStrain) (delta : ℝ) (w : R3)
    (R T : R3 →L[ℝ] R3) (f g : R3) :
    linearRate S delta w (R - T) (f - g) = linearRate S delta w R f - linearRate S delta w T g := by
  simp only [linearRate, remainderAnisotropy, sub_apply, inner_sub_right]
  ring

theorem abs_linearRate_le (S : SymmetricStrain) (delta : ℝ) (w : R3)
    (R : R3 →L[ℝ] R3) (f : R3) :
    |linearRate S delta w R f| ≤ 2 * ‖R‖ * ‖w‖ ^ 2 + 2 * ‖regularizedGap S delta w‖ * ‖f‖ := by
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hR := abs_remainderAnisotropy_le R (topVector S) w (topVector_norm S)
  have hf := abs_real_inner_le_norm (regularizedGap S delta w) f
  linarith

theorem linearRate_error (S : SymmetricStrain) (delta : ℝ) (w : R3)
    (R T : R3 →L[ℝ] R3) (f g : R3) :
    linearRate S delta w R f ≤ linearRate S delta w T g +
      2 * ‖R - T‖ * ‖w‖ ^ 2 + 2 * ‖regularizedGap S delta w‖ * ‖f - g‖ := by
  have h := abs_linearRate_le S delta w (R - T) (f - g)
  rw [linearRate_sub] at h
  linarith [(le_abs_self (linearRate S delta w R f - linearRate S delta w T g))]

theorem regularizedEnergy_eq (S : SymmetricStrain) (delta : ℝ) (w : R3) :
    regularizedEnergy S delta w = topSpectralDefect S w + delta * ‖w‖ ^ 2 :=
  regularizedGap_energy S delta w

theorem regularizedGap_apply_eq (S : SymmetricStrain) (delta : ℝ) (w : R3) :
    regularizedGap S delta w = spectralResidual S.1 (topEigenvalue S) w + delta • w := by
  simp only [regularizedGap, smul_apply, one_apply_eq_self, sub_apply, spectralResidual, add_smul]
  module

/-- A derivative of the constructed energy, not an assigned eigenvalue rate. -/
theorem hasDerivAt_regularizedEnergy (S : ℝ → SymmetricStrain) (w : ℝ → R3)
    (Sdot : R3 →L[ℝ] R3) (wdot : R3) (delta t : ℝ)
    (hS : HasDerivAt (fun s ↦ (S s).1) Sdot t) (hw : HasDerivAt w wdot t)
    (hlambda : DifferentiableAt ℝ (fun s ↦ topEigenvalue (S s)) t) :
    HasDerivAt (fun s ↦ regularizedEnergy (S s) delta (w s))
      (linearRate (S t) delta (w t) Sdot wdot) t := by
  have hK := hasDerivAt_regularizedGap S Sdot delta t hS hlambda
  have h := hw.inner ℝ (hK.clm_apply hw)
  apply h.congr_deriv
  simp only [linearRate, remainderAnisotropy, gapDerivative, sub_apply, smul_apply,
    one_apply_eq_self, inner_add_right, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, regularizedGap_symmetric,
    real_inner_comm wdot (regularizedGap (S t) delta (w t)), topVector]
  ring

theorem linearRate_strainSquare (S : SymmetricStrain) (delta : ℝ) (w : R3)
    (R : R3 →L[ℝ] R3) (f : R3) :
    linearRate S delta w (-S.1 * S.1 + R) (S.1 w + f) =
      -‖spectralResidual S.1 (topEigenvalue S) w‖ ^ 2 +
        remainderAnisotropy R (topVector S) w + 2 * ⟪spectralResidual S.1 (topEigenvalue S) w, f⟫ +
        2 * delta * ⟪w, S.1 w + f⟫ := by
  have he : S.1 (topVector S) = topEigenvalue S • topVector S :=
    (orderedEigenframe S.1 S.2).apply_eigenbasis 0
  have h := eigenvalueRate_strainSquare S.1 R (topVector S) (topEigenvalue S) (topVector_norm S) he
  rw [linearRate, remainderAnisotropy, h, regularizedGap_apply_eq, norm_spectralResidual_sq]
  simp only [add_apply, mul_apply_eq_comp, neg_apply, inner_add_left, inner_add_right,
    inner_neg_right, real_inner_smul_left, S.2 w (S.1 w), real_inner_self_eq_norm_sq,
    spectralResidual, inner_sub_left, remainderAnisotropy]
  ring

/-- The viscous response is isolated, but its sign is not discarded.
The regularization contributes its own stretching/forcing term. -/
theorem linearRate_viscous_split (S : SymmetricStrain) (delta nu : ℝ) (w : R3)
    (R A : R3 →L[ℝ] R3) (f b : R3) :
    linearRate S delta w (-S.1 * S.1 + R + nu • A) (S.1 w + f + nu • b) =
      -‖spectralResidual S.1 (topEigenvalue S) w‖ ^ 2 +
        remainderAnisotropy R (topVector S) w + 2 * ⟪spectralResidual S.1 (topEigenvalue S) w, f⟫ +
        2 * delta * ⟪w, S.1 w + f⟫ + nu * linearRate S delta w A b := by
  rw [linearRate_add, linearRate_smul, linearRate_strainSquare]

end Mettapedia.FluidDynamics.NavierStokes.PancakeRegularizedMaterialRate
