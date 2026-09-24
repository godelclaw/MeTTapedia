import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ExchangedFluxHeatRepresentation
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Exact velocity-coefficient adjoints of the exchanged stretching flux

Each of the three input slots is a constructed continuous real-linear map
from a velocity coefficient to the projected tensor mode. Its adjoint
retains the input curl, the Leray difference, and the full output gradient
projection. The resulting identities are signed and precede any estimates.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxAdjoint

open scoped RealInnerProductSpace
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeFrequencyProjectorCommutator PancakeGalerkinKineticEnergy
open PancakePeriodicVorticityEquation
open PeriodicGradientFluxTriple ExchangedFluxModeDynamics ExchangedFluxVariation
open LongitudinalExchangeFluxFourier

local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "H" => Mettapedia.Analysis.UnitTorusGradientProjection.TensorL2
  (Fin 3) (EuclideanSpace ℝ (Fin 3))
local notation "Tensor" => Fin 3 → VelocityCoefficient

def curlCoefficientCLM (q : Wavevector) : C3 →L[ℂ] VelocityCoefficient :=
  (unitTorusDerivativePhase • (crossProduct (R := ℂ) (wavevectorCoefficient q)).toContinuousLinearMap).comp
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 ↦ ℂ)).toContinuousLinearMap

theorem curlCoefficientCLM_apply (u : FourierVelocity) (q : Wavevector) :
    curlCoefficientCLM q (coefficientVec (u q)) = fourierCurl u q := rfl

def outerTensorCLM (u : FourierVelocity) (p : TripleIndex) : C3 →L[ℂ] Tensor :=
  ContinuousLinearMap.pi (fun j ↦ (1 / 2 : ℂ) •
    (((ContinuousLinearMap.proj j).comp (curlCoefficientCLM p.1)).smulRight
      (differenceCLM p (coefficientCross (fourierCurl u p.2.1) (fourierCurl u p.2.2)))))

def leftTensorCLM (u : FourierVelocity) (p : TripleIndex) : C3 →L[ℂ] Tensor :=
  ContinuousLinearMap.pi (fun j ↦ ((1 / 2 : ℂ) * fourierCurl u p.1 j) •
    ((differenceCLM p).comp
      (((crossProduct (R := ℂ)).flip (fourierCurl u p.2.2)).toContinuousLinearMap.comp
        (curlCoefficientCLM p.2.1))))

def rightTensorCLM (u : FourierVelocity) (p : TripleIndex) : C3 →L[ℂ] Tensor :=
  ContinuousLinearMap.pi (fun j ↦ ((1 / 2 : ℂ) * fourierCurl u p.1 j) •
    ((differenceCLM p).comp
      ((crossProduct (R := ℂ) (fourierCurl u p.2.1)).toContinuousLinearMap.comp
        (curlCoefficientCLM p.2.2))))

def outerSlot (u : FourierVelocity) (p : TripleIndex) : C3 →L[ℝ] H :=
  (tensorModeCLM (tripleFrequency p)).comp ((outerTensorCLM u p).restrictScalars ℝ)

def leftSlot (u : FourierVelocity) (p : TripleIndex) : C3 →L[ℝ] H :=
  (tensorModeCLM (tripleFrequency p)).comp ((leftTensorCLM u p).restrictScalars ℝ)

def rightSlot (u : FourierVelocity) (p : TripleIndex) : C3 →L[ℝ] H :=
  (tensorModeCLM (tripleFrequency p)).comp ((rightTensorCLM u p).restrictScalars ℝ)

theorem outerSlot_apply (u v : FourierVelocity) (p : TripleIndex) :
    outerSlot u p (coefficientVec (v p.1)) = mixedMode v u u p := by
  change tensorModeCLM (tripleFrequency p) ((outerTensorCLM u p) (coefficientVec (v p.1))) =
    tensorModeCLM (tripleFrequency p) (mixedTensor v u u p)
  apply congrArg (tensorModeCLM (tripleFrequency p))
  ext j i
  simp [outerTensorCLM, mixedTensor, curlCoefficientCLM_apply,
    RCLike.real_smul_eq_coe_smul (K := ℂ)]

theorem leftSlot_apply (u v : FourierVelocity) (p : TripleIndex) :
    leftSlot u p (coefficientVec (v p.2.1)) = mixedMode u v u p := by
  change tensorModeCLM (tripleFrequency p) ((leftTensorCLM u p) (coefficientVec (v p.2.1))) =
    tensorModeCLM (tripleFrequency p) (mixedTensor u v u p)
  apply congrArg (tensorModeCLM (tripleFrequency p))
  ext j i
  simp [leftTensorCLM, mixedTensor, curlCoefficientCLM_apply,
    RCLike.real_smul_eq_coe_smul (K := ℂ), coefficientCross, crossProduct, mul_assoc]

theorem rightSlot_apply (u v : FourierVelocity) (p : TripleIndex) :
    rightSlot u p (coefficientVec (v p.2.2)) = mixedMode u u v p := by
  change tensorModeCLM (tripleFrequency p) ((rightTensorCLM u p) (coefficientVec (v p.2.2))) =
    tensorModeCLM (tripleFrequency p) (mixedTensor u u v p)
  apply congrArg (tensorModeCLM (tripleFrequency p))
  ext j i
  simp [rightTensorCLM, mixedTensor, curlCoefficientCLM_apply,
    RCLike.real_smul_eq_coe_smul (K := ℂ), coefficientCross, crossProduct, mul_assoc]

def outerTest (u : FourierVelocity) (F : H) (p : TripleIndex) : C3 := (outerSlot u p).adjoint F

def leftTest (u : FourierVelocity) (F : H) (p : TripleIndex) : C3 := (leftSlot u p).adjoint F

def rightTest (u : FourierVelocity) (F : H) (p : TripleIndex) : C3 := (rightSlot u p).adjoint F

theorem inner_variationMode_eq (u v : FourierVelocity) (F : H) (p : TripleIndex) :
    ⟪variationMode u v p, F⟫ =
      ⟪coefficientVec (v p.1), outerTest u F p⟫ +
      ⟪coefficientVec (v p.2.1), leftTest u F p⟫ +
      ⟪coefficientVec (v p.2.2), rightTest u F p⟫ := by
  simp only [outerTest, leftTest, rightTest, ContinuousLinearMap.adjoint_inner_right,
    outerSlot_apply, leftSlot_apply, rightSlot_apply, variationMode, inner_add_left]

end Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxAdjoint
