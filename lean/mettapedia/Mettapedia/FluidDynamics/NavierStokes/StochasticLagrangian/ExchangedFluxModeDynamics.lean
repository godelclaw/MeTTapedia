import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierStretchingInteractionBudget

/-!
# Actual damped evolution of the exchanged flux modes

The mode is reconstructed as a fixed linear image of the outer vorticity
times a Leray difference of the inner vorticity cross product. Its source
is constructed from the full nonlinear curl in all three input slots.
The damping rate is the sum of the three physical input heat rates.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 80000
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxModeDynamics

open Mettapedia.Analysis.UnitTorusGradientProjection
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeGalerkinKineticEnergy PancakeGalerkinVorticityBridge PancakeLocalInfiniteVelocity
open PeriodicGradientFluxSymbol PeriodicGradientFluxPair PeriodicGradientFluxTriple
open LongitudinalExchangeFluxFourier LerayStretchExchange
open FourierVorticityPairDynamics FourierStretchingInteractionDynamics

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "Tensor" => Fin 3 → VelocityCoefficient
local notation "H" => TensorL2 (Fin 3) R3

def lerayLinear (k : Wavevector) : VelocityCoefficient →ₗ[ℂ] VelocityCoefficient where
  toFun := lerayMode k
  map_add' a b := by
    by_cases hk : modeSquare k = 0
    · simp [lerayMode, hk]
    · ext i
      simp [lerayMode, hk, modeDot, mul_add, Finset.sum_add_distrib]
      ring
  map_smul' c a := lerayMode_smul k c a

def differenceCLM (p : TripleIndex) : VelocityCoefficient →L[ℂ] VelocityCoefficient :=
  (lerayLinear p.2.1).toContinuousLinearMap - (lerayLinear p.2.2).toContinuousLinearMap

theorem differenceCLM_apply (p : TripleIndex) (a : VelocityCoefficient) :
    differenceCLM p a = lerayMode p.2.1 a - lerayMode p.2.2 a := rfl

def tensorModeCLM (n : Wavevector) : Tensor →L[ℝ] H :=
  (gradientProjectionCLM (d := Fin 3) (E := R3)).comp
    ((tensorEmbedding (d := Fin 3) (E := R3)).comp
      (ContinuousLinearMap.pi (fun j ↦ (realModeCLM n).comp (ContinuousLinearMap.proj j))))

theorem tensorModeCLM_apply (n : Wavevector) (A : Tensor) :
    tensorModeCLM n A = toTensorL2 (fun j ↦ realMode n (projectedCoeff n A j)) :=
  gradientProjection_realMode n A

def tensorCoeff (u : FourierVelocity) (p : TripleIndex) (j : Fin 3) : VelocityCoefficient :=
  (1 / 2 : ℝ) • (fourierCurl u p.1 j • differenceCLM p (pairCross u p.2.1 p.2.2))

def sourceTensor (u : FourierVelocity) (p : TripleIndex) (j : Fin 3) : VelocityCoefficient :=
  (1 / 2 : ℝ) •
    (nonlinearCurl u p.1 j • differenceCLM p (pairCross u p.2.1 p.2.2) +
     fourierCurl u p.1 j • differenceCLM p (pairSource u p.2.1 p.2.2))

def mode (u : FourierVelocity) (p : TripleIndex) : H :=
  tensorModeCLM (tripleFrequency p) (tensorCoeff u p)

def sourceMode (u : FourierVelocity) (p : TripleIndex) : H :=
  tensorModeCLM (tripleFrequency p) (sourceTensor u p)

theorem projected_tensorCoeff (u : FourierVelocity) (p : TripleIndex) (j : Fin 3)
    (hl : modeDot p.2.1 (u p.2.1) = 0) (hm : modeDot p.2.2 (u p.2.2) = 0) :
    projectedCoeff (tripleFrequency p) (tensorCoeff u p) j = exchangeCoeff u p j := by
  rw [exchangeCoeff_eq_projected u p j hl hm]
  change projectedCoeff (tripleFrequency p) (fun i ↦ tensorCoeff u p i) j = _
  simp only [tensorCoeff, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rw [projectedCoeff_smul]
  rfl

theorem mode_eq_exchangeMode (u : FourierVelocity) (p : TripleIndex)
    (hl : modeDot p.2.1 (u p.2.1) = 0) (hm : modeDot p.2.2 (u p.2.2) = 0) :
    mode u p = exchangeMode u p := by
  simp only [mode, tensorModeCLM_apply, projected_tensorCoeff u p _ hl hm, exchangeMode]

variable {ν T B : ℝ} {u₀ : FourierVelocity}

theorem hasDerivAt_tensorCoeff (s : LocalInfiniteVelocitySolution ν u₀ T B)
    (p : TripleIndex) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ tensorCoeff (s.coefficients τ) p)
      (sourceTensor (s.coefficients t) p -
        interactionDamping ν p • tensorCoeff (s.coefficients t) p) t := by
  have hC : HasDerivAt (fun τ ↦ pairCross (s.coefficients τ) p.2.1 p.2.2)
      (pairSource (s.coefficients t) p.2.1 p.2.2 +
        (-(pairDamping ν p.2.1 p.2.2) : ℂ) • pairCross (s.coefficients t) p.2.1 p.2.2) t :=
    hasDerivAt_pi.mpr (hasDerivAt_pairCross s p.2.1 p.2.2 t ht)
  have hD := (differenceCLM p).restrictScalars ℝ |>.hasFDerivAt.comp_hasDerivAt t hC
  change HasDerivAt (fun τ ↦ differenceCLM p (pairCross (s.coefficients τ) p.2.1 p.2.2))
    (differenceCLM p _) t at hD
  rw [map_add, map_smul] at hD
  apply hasDerivAt_pi.mpr
  intro j
  have hw := hasDerivAt_fourierCurl s.coefficients _ t p.1 (s.equation t ht p.1) j
  rw [curlRHS_eq_nonlinear_add_damping] at hw
  have h := (hw.smul hD).const_smul (1 / 2 : ℝ)
  apply h.congr_deriv
  ext i
  simp only [tensorCoeff, sourceTensor, interactionDamping, Pi.sub_apply,
    RCLike.real_smul_eq_coe_smul (K := ℂ), Pi.smul_apply, Pi.add_apply,
    smul_eq_mul, RCLike.ofReal_eq_complex_ofReal]
  push_cast
  ring

theorem hasDerivAt_mode (s : LocalInfiniteVelocitySolution ν u₀ T B)
    (p : TripleIndex) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ mode (s.coefficients τ) p)
      (sourceMode (s.coefficients t) p - interactionDamping ν p • mode (s.coefficients t) p) t := by
  have h := (tensorModeCLM (tripleFrequency p)).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_tensorCoeff s p t ht)
  simpa only [mode, sourceMode, Function.comp_def, map_sub, map_smul] using h

theorem hasDerivAt_exchangeMode (s : LocalInfiniteVelocitySolution ν u₀ T B)
    (p : TripleIndex) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ exchangeMode (s.coefficients τ) p)
      (sourceMode (s.coefficients t) p -
        interactionDamping ν p • exchangeMode (s.coefficients t) p) t := by
  have he (τ : ℝ) := mode_eq_exchangeMode (s.coefficients τ) p
    (s.transverse τ p.2.1) (s.transverse τ p.2.2)
  simpa only [he] using hasDerivAt_mode s p t ht

end Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxModeDynamics
