import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeRegularizedMaterialRate

/-!
# Exact dependence of spectral energy and its rate on regularization

Adding a squared-norm regularizer adds precisely its derivative to the
material rate. Subtracting that derivative recovers the unregularized
rate, not an additional coercive estimate.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.RegularizedSpectralEnergySplitting

open scoped RealInnerProductSpace
open PancakeRegularizedDiffusion PancakeRegularizedMaterialRate PancakeSpectralFiniteDifference
open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain

local notation "R3" => EuclideanSpace ℝ (Fin 3)

theorem regularizedEnergy_eq_zero_add (S : SymmetricStrain) (delta : ℝ) (w : R3) :
    regularizedEnergy S delta w = regularizedEnergy S 0 w + delta * ‖w‖ ^ 2 := by
  simp only [regularizedEnergy_eq, zero_mul, add_zero]

theorem linearRate_eq_zero_add (S : SymmetricStrain) (delta : ℝ) (w : R3)
    (R : R3 →L[ℝ] R3) (f : R3) :
    linearRate S delta w R f = linearRate S 0 w R f + 2 * delta * ⟪w, f⟫ := by
  simp only [linearRate, regularizedGap_apply_eq, inner_add_left, real_inner_smul_left]
  ring

/-- This identity does not require positivity of the regularizer. -/
theorem hasDerivAt_regularizedEnergy_sub_norm_sq (S : ℝ → SymmetricStrain) (w : ℝ → R3)
    (Sdot : R3 →L[ℝ] R3) (wdot : R3) (delta t : ℝ)
    (hS : HasDerivAt (fun s ↦ (S s).1) Sdot t) (hw : HasDerivAt w wdot t)
    (hlambda : DifferentiableAt ℝ (fun s ↦ topEigenvalue (S s)) t) :
    HasDerivAt (fun s ↦ regularizedEnergy (S s) delta (w s) - delta * ‖w s‖ ^ 2)
      (linearRate (S t) 0 (w t) Sdot wdot) t := by
  convert hasDerivAt_regularizedEnergy S w Sdot wdot 0 t hS hw hlambda using 1
  ext s
  rw [regularizedEnergy_eq_zero_add]
  ring

end Mettapedia.FluidDynamics.NavierStokes.RegularizedSpectralEnergySplitting
