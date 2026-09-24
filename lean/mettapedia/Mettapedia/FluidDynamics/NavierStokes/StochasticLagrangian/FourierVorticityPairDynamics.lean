import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LongitudinalExchangeFluxFourier
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FilteredAngularSourceIntegral

/-!
# Actual dynamics of a vorticity Fourier-pair cross product

The sum of the two input heat rates damps their cross product. The
remaining source is constructed from the complete inviscid velocity RHS,
not a closed Galerkin equation or an externally supplied alignment rate.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierVorticityPairDynamics

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeGalerkinKineticEnergy PancakeGalerkinVorticityBridge
open PancakePeriodicVorticityEquation PancakeFrequencyProjectorCommutator
open PancakeCoefficientLimitEquation PancakeLocalInfiniteVelocity PancakeSignedTransportEnergy
open LocalHelicityCenterEvolution

def modeDamping (ν : ℝ) (k : Wavevector) : ℝ :=
  ν * (2 * Real.pi) ^ 2 * ‖frequencyVec k‖ ^ 2

def pairDamping (ν : ℝ) (l m : Wavevector) : ℝ :=
  modeDamping ν l + modeDamping ν m

def nonlinearCurl (u : FourierVelocity) : FourierVelocity :=
  fourierCurl (infiniteVelocityRHS 0 u)

def pairCross (u : FourierVelocity) (l m : Wavevector) : VelocityCoefficient :=
  coefficientCross (fourierCurl u l) (fourierCurl u m)

def pairSource (u : FourierVelocity) (l m : Wavevector) : VelocityCoefficient :=
  coefficientCross (nonlinearCurl u l) (fourierCurl u m) +
    coefficientCross (fourierCurl u l) (nonlinearCurl u m)

def pairEnergy (u : FourierVelocity) (l m : Wavevector) : ℝ :=
  coefficientEnergy (pairCross u l m)

def pairWork (u : FourierVelocity) (l m : Wavevector) : ℝ :=
  2 * (coefficientHermitian (pairCross u l m) (pairSource u l m)).re

theorem pairEnergy_nonneg (u : FourierVelocity) (l m : Wavevector) :
    0 ≤ pairEnergy u l m := by
  rw [pairEnergy, ← norm_coefficientVec_sq]
  positivity

theorem pairDamping_nonneg {ν : ℝ} (hν : 0 ≤ ν) (l m : Wavevector) :
    0 ≤ pairDamping ν l m := by
  unfold pairDamping modeDamping
  positivity

theorem pairDamping_pos {ν : ℝ} (hν : 0 < ν) (l m : Wavevector)
    (hl : l ≠ 0) : 0 < pairDamping ν l m := by
  have hln : 0 < ‖frequencyVec l‖ := norm_pos_iff.mpr (frequencyVec_ne_zero hl)
  unfold pairDamping modeDamping
  positivity

theorem viscousCoeff_eq_neg_damping (ν : ℝ) (u : FourierVelocity) (k : Wavevector) :
    unitTorusViscousVorticityCoeff ν u k = (-(modeDamping ν k) : ℂ) • u k := by
  rw [unitTorusViscousVorticityCoeff, modeSquare_eq_norm_sq]
  congr 1
  simp [modeDamping, unitTorusDerivativePhase, mul_pow, Complex.I_sq]

theorem curlRHS_eq_nonlinear_add_damping (ν : ℝ) (u : FourierVelocity) (k : Wavevector) :
    fourierCurl (infiniteVelocityRHS ν u) k =
      nonlinearCurl u k + (-(modeDamping ν k) : ℂ) • fourierCurl u k := by
  rw [infiniteVelocityRHS_eq_zero_add_viscous, LocalFilteredVorticity.fourierCurl_add,
    Pi.add_apply, curl_viscous, viscousCoeff_eq_neg_damping]
  rfl

theorem hasDerivAt_cross (a b : ℝ → VelocityCoefficient) (a' b' : VelocityCoefficient) (t : ℝ)
    (ha : ∀ i, HasDerivAt (fun τ ↦ a τ i) (a' i) t)
    (hb : ∀ i, HasDerivAt (fun τ ↦ b τ i) (b' i) t) (i : Fin 3) :
    HasDerivAt (fun τ ↦ coefficientCross (a τ) (b τ) i)
      ((coefficientCross a' (b t) + coefficientCross (a t) b') i) t := by
  fin_cases i
  · apply (((ha 1).mul (hb 2)).sub ((ha 2).mul (hb 1))).congr_deriv
    simp [coefficientCross]
    ring
  · apply (((ha 2).mul (hb 0)).sub ((ha 0).mul (hb 2))).congr_deriv
    simp [coefficientCross]
    ring
  · apply (((ha 0).mul (hb 1)).sub ((ha 1).mul (hb 0))).congr_deriv
    simp [coefficientCross]
    ring

theorem pairRate_eq (ν : ℝ) (u : FourierVelocity) (l m : Wavevector) :
    coefficientCross (fourierCurl (infiniteVelocityRHS ν u) l) (fourierCurl u m) +
      coefficientCross (fourierCurl u l) (fourierCurl (infiniteVelocityRHS ν u) m) =
    pairSource u l m + (-(pairDamping ν l m) : ℂ) • pairCross u l m := by
  rw [curlRHS_eq_nonlinear_add_damping, curlRHS_eq_nonlinear_add_damping]
  ext i
  fin_cases i <;>
    simp [pairSource, pairCross, pairDamping, coefficientCross] <;> ring

variable {ν T B : ℝ} {u₀ : FourierVelocity}

theorem hasDerivAt_pairCross (s : LocalInfiniteVelocitySolution ν u₀ T B)
    (l m : Wavevector) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) (i : Fin 3) :
    HasDerivAt (fun τ ↦ pairCross (s.coefficients τ) l m i)
      ((pairSource (s.coefficients t) l m +
        (-(pairDamping ν l m) : ℂ) • pairCross (s.coefficients t) l m) i) t := by
  have h := hasDerivAt_cross (fun τ ↦ fourierCurl (s.coefficients τ) l)
    (fun τ ↦ fourierCurl (s.coefficients τ) m) _ _ t
    (hasDerivAt_fourierCurl s.coefficients _ t l (s.equation t ht l))
    (hasDerivAt_fourierCurl s.coefficients _ t m (s.equation t ht m)) i
  rw [pairRate_eq] at h
  exact h

theorem hasDerivAt_pairEnergy (s : LocalInfiniteVelocitySolution ν u₀ T B)
    (l m : Wavevector) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ pairEnergy (s.coefficients τ) l m)
      (pairWork (s.coefficients t) l m -
        2 * pairDamping ν l m * pairEnergy (s.coefficients t) l m) t := by
  have h := hasDerivAt_coefficientEnergy (fun τ ↦ pairCross (s.coefficients τ) l m)
    _ t (hasDerivAt_pairCross s l m t ht)
  have hv := hermitian_real_smul_self (pairCross (s.coefficients t) l m) (-pairDamping ν l m)
  simp only [Complex.ofReal_neg] at hv
  simp only [hermitian_add_right, Complex.add_re, hv] at h
  apply h.congr_deriv
  dsimp [pairEnergy, pairWork]
  ring

end Mettapedia.FluidDynamics.NavierStokes.FourierVorticityPairDynamics
