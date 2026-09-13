import Mettapedia.Analysis.RegularizedProjectionParabolic
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalHelicityCenterSourceBudget

/-!
# The actual parabolic equation of the regularized helicity center

Viscosity gives an ordinary Laplacian, a coefficient-gradient drift, and
a signed pairing of the first derivatives of vorticity and curl vorticity.
All these derivatives are reconstructed from the same Fourier velocity.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalHelicityCenterParabolic

open scoped RealInnerProductSpace
open Mettapedia.Analysis RegularizedProjectionParabolic
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeGalerkinKineticEnergy PancakeFourierTranslationCurve PancakeHaarTransportRate
open LocalLowDiffusionBudget LocalJointDiffusionBudget LocalSpatialVorticityJets
open LocalWeightedCurlCancellation LocalVariableHelicityCenter LocalHelicityCenterSourceBudget
open PancakeLocalInfiniteVelocity PancakeLocalMaterialTrajectories PancakeFourierMaterialPaths

local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ

theorem regularizedCenterGradient_eq (δ : ℝ) (hδ : 0 < δ)
    (u : FourierVelocity) (j : Fin 3) (x : T3) :
    regularizedCenterGradient δ u j x = coefficientRate δ (fullVorticity u x)
      (fullVorticity (fourierCurl u) x) (fullCurlGradient u j x) (fullCurlGradient (fourierCurl u) j x) := by
  have hd : δ + ‖fullVorticity u x‖ ^ 2 ≠ 0 := by positivity
  simp only [regularizedCenterGradient, coefficientRate, RegularizedProjection.coefficient]
  field_simp

def centerSecond (δ : ℝ) (u : FourierVelocity) (j : Fin 3) (x : T3) : ℝ :=
  coefficientSecondRate δ (fullVorticity u x) (fullVorticity (fourierCurl u) x)
    (fullCurlGradient u j x) (fullCurlGradient (fourierCurl u) j x)
    (fullCurlSecond u j x) (fullCurlSecond (fourierCurl u) j x)

theorem hasDerivAt_regularizedCenter_shift (δ : ℝ) (hδ : 0 < δ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 4 u)) (j : Fin 3) (x : T3) (h : ℝ) :
    HasDerivAt (fun t ↦ regularizedCenter δ u (x + coordinateShift j t))
      (regularizedCenterGradient δ u j (x + coordinateShift j h)) h := by
  rw [regularizedCenterGradient_eq δ hδ]
  exact RegularizedProjectionParabolic.hasDerivAt_coefficient δ hδ
    (hasDerivAt_fullVorticity_shift u (summable_fourierMoment_of_le _ (by omega : 3 ≤ 4) hu) j x h)
    (hasDerivAt_fullVorticity_shift (fourierCurl u) (summable_fourierMoment_curl 3 u hu) j x h)

theorem hasDerivAt_regularizedCenterGradient_shift (δ : ℝ) (hδ : 0 < δ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 4 u)) (j : Fin 3) (x : T3) (h : ℝ) :
    HasDerivAt (fun t ↦ regularizedCenterGradient δ u j (x + coordinateShift j t))
      (centerSecond δ u j (x + coordinateShift j h)) h := by
  have hu3 := summable_fourierMoment_of_le _ (by omega : 3 ≤ 4) hu
  have hw3 := summable_fourierMoment_curl 3 u hu
  simp_rw [regularizedCenterGradient_eq δ hδ]
  exact hasDerivAt_coefficientRate δ hδ
    (hasDerivAt_fullVorticity_shift u hu3 j x h)
    (hasDerivAt_fullVorticity_shift (fourierCurl u) hw3 j x h)
    (hasDerivAt_fullCurlGradient_shift u hu3 j x h)
    (hasDerivAt_fullCurlGradient_shift (fourierCurl u) hw3 j x h)

theorem deriv_deriv_regularizedCenter_shift (δ : ℝ) (hδ : 0 < δ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 4 u)) (j : Fin 3) (x : T3) :
    deriv (deriv (fun h ↦ regularizedCenter δ u (x + coordinateShift j h))) 0 = centerSecond δ u j x := by
  have hd : deriv (fun h ↦ regularizedCenter δ u (x + coordinateShift j h)) =
      fun h ↦ regularizedCenterGradient δ u j (x + coordinateShift j h) :=
    funext (fun h ↦ (hasDerivAt_regularizedCenter_shift δ hδ u hu j x h).deriv)
  rw [hd]
  simpa only [coordinateShift_zero, add_zero] using
    (hasDerivAt_regularizedCenterGradient_shift δ hδ u hu j x 0).deriv

/-- The Laplacian is defined by ordinary second translation derivatives. -/
def centerLaplacian (δ : ℝ) (u : FourierVelocity) (x : T3) : ℝ :=
  ∑ j : Fin 3, deriv (deriv (fun h ↦ regularizedCenter δ u (x + coordinateShift j h))) 0

theorem centerLaplacian_eq_sum (δ : ℝ) (hδ : 0 < δ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 4 u)) (x : T3) :
    centerLaplacian δ u x = ∑ j : Fin 3, centerSecond δ u j x := by
  simp only [centerLaplacian, deriv_deriv_regularizedCenter_shift δ hδ u hu]

def centerDrift (δ : ℝ) (u : FourierVelocity) (x : T3) : ℝ :=
  ∑ j : Fin 3, (4 * ⟪fullVorticity u x, fullCurlGradient u j x⟫ /
    (δ + ‖fullVorticity u x‖ ^ 2)) * regularizedCenterGradient δ u j x

def centerGradientProduction (δ : ℝ) (u : FourierVelocity) (x : T3) : ℝ :=
  2 / (δ + ‖fullVorticity u x‖ ^ 2) * ∑ j : Fin 3,
    (regularizedCenter δ u x * ‖fullCurlGradient u j x‖ ^ 2 -
      ⟪fullCurlGradient u j x, fullCurlGradient (fourierCurl u) j x⟫)

theorem centerViscousRate_eq_sum (δ : ℝ) (hδ : 0 < δ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 4 u)) (x : T3) :
    centerViscousRate δ u x = ∑ j : Fin 3,
      coefficientRate δ (fullVorticity u x) (fullVorticity (fourierCurl u) x)
        (fullCurlSecond u j x) (fullCurlSecond (fourierCurl u) j x) := by
  have hu3 := summable_fourierMoment_of_le _ (by omega : 3 ≤ 4) hu
  have hw3 := summable_fourierMoment_curl 3 u hu
  have hd : δ + ‖fullVorticity u x‖ ^ 2 ≠ 0 := by positivity
  unfold centerViscousRate
  rw [← sum_fullCurlSecond u hu3 x, ← sum_fullCurlSecond (fourierCurl u) hw3 x]
  simp only [coefficientRate, RegularizedProjection.coefficient, Fin.sum_univ_three,
    inner_add_left, inner_add_right]
  field_simp
  ring

/-- Viscosity is not merely a scalar heat operator on this quotient. -/
theorem centerViscousRate_eq (δ : ℝ) (hδ : 0 < δ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 4 u)) (x : T3) :
    centerViscousRate δ u x = centerLaplacian δ u x + centerDrift δ u x +
      centerGradientProduction δ u x := by
  rw [centerViscousRate_eq_sum δ hδ u hu, centerLaplacian_eq_sum δ hδ u hu]
  simp only [centerSecond, centerDrift, centerGradientProduction, coefficientSecondRate,
    regularizedCenterGradient_eq δ hδ, regularizedCenter, RegularizedProjection.coefficient,
    Fin.sum_univ_three]
  ring

theorem hasDerivAt_center_parabolic {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 4 (s.coefficients τ) q ≤ g q)
    (X : ℝ → X3)
    (hX : ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt X (liftedVelocity s τ (X τ)) τ)
    (δ : ℝ) (hδ : 0 < δ) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ regularizedCenter δ (s.coefficients τ) (torusPoint (X τ)))
      (centerSource δ (s.coefficients t) (torusPoint (X t)) +
        centerStretchFeedback δ (s.coefficients t) (torusPoint (X t)) +
        ν * (centerLaplacian δ (s.coefficients t) (torusPoint (X t)) +
          centerDrift δ (s.coefficients t) (torusPoint (X t)) +
          centerGradientProduction δ (s.coefficients t) (torusPoint (X t)))) t := by
  have hm := hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t ⟨ht.1.le, ht.2.le⟩)
  simpa only [centerViscousRate_eq δ hδ _ hm] using
    hasDerivAt_center_decomposed s g hg hSum hu X hX δ hδ t ht

end Mettapedia.FluidDynamics.NavierStokes.LocalHelicityCenterParabolic
