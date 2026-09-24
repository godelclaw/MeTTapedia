import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ExchangedFluxInputExchange
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PeriodicTensorFourierPairing

/-!
# Finite coefficient formulas for the actual seven-input tests

The curl removes the convection Leray projection exactly. The output
gradient projection and the inner Leray difference are retained. This
formula is for the constructed infinite-field interaction, not a test
coefficient supplied independently of the velocity.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxCoefficientFormula

open scoped RealInnerProductSpace ComplexConjugate
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeFrequencyProjectorCommutator PancakeGalerkinKineticEnergy PancakeGalerkinVorticityBridge
open PancakePeriodicVorticityEquation PancakeCurlOutputTail
open PeriodicGradientFluxSymbol PeriodicGradientFluxTriple
open ExchangedFluxModeDynamics ExchangedFluxAdjoint ExchangedFluxSevenInputHeat
open ExchangedFluxInputExchange PeriodicTensorFourierPairing
open ExchangedFluxVariation ExchangedFluxPolarization
open PancakeSobolevFiberEnvelope

def curlConvectionAtom (u : FourierVelocity) (k l : Wavevector) : VelocityCoefficient :=
  unitTorusDerivativePhase • coefficientCross (wavevectorCoefficient (k + l)) (convectionAtom u k l)

theorem curlConvectionAtom_eq (u : FourierVelocity) (k l : Wavevector) :
    curlConvectionAtom u k l =
      (-(unitTorusDerivativePhase ^ 2) * modeDot (k + l) (u k)) •
        coefficientCross (wavevectorCoefficient (k + l)) (u l) := by
  rw [curlConvectionAtom, convectionAtom_eq_transportFactor, coefficientCross_smul_right,
    cross_leray, coefficientCross_smul_right, smul_smul, smul_smul]
  congr 1
  ring

/-- Separate the transported high-input curl and the correction carrying a low frequency. -/
theorem curlConvectionAtom_eq_transport_add (u : FourierVelocity) (k l : Wavevector)
    (hk : modeDot k (u k) = 0) :
    curlConvectionAtom u k l =
      (-(unitTorusDerivativePhase * modeDot l (u k))) • fourierCurl u l +
      (-(unitTorusDerivativePhase ^ 2) * modeDot l (u k)) •
        coefficientCross (wavevectorCoefficient k) (u l) := by
  rw [curlConvectionAtom_eq, modeDot_add_frequency, hk, zero_add]
  ext i
  fin_cases i <;>
    simp [fourierCurl, coefficientCross, wavevectorCoefficient, Pi.add_apply, Int.cast_add] <;> ring

def insertionTensor (inner : Bool) (u : FourierVelocity) (q m n : Wavevector)
    (a : VelocityCoefficient) : Fin 3 → VelocityCoefficient :=
  if inner then fun j ↦ ((1 / 2 : ℂ) * fourierCurl u m j) •
    differenceCLM (m, (q, n)) (coefficientCross a (fourierCurl u n))
  else fun j ↦ ((1 / 2 : ℂ) * a j) •
    differenceCLM (q, (m, n)) (coefficientCross (fourierCurl u m) (fourierCurl u n))

theorem insertionSlot_eq_tensor (inner : Bool) (u : FourierVelocity)
    (q m n : Wavevector) (v : VelocityCoefficient) :
    insertionSlot inner u q m n (coefficientVec v) =
      tensorModeCLM (q + m + n) (insertionTensor inner u q m n
        (unitTorusDerivativePhase • coefficientCross (wavevectorCoefficient q) v)) := by
  cases inner
  · change tensorModeCLM (tripleFrequency (q, (m, n))) _ = _
    have he : tripleFrequency (q, (m, n)) = q + m + n := by simp [tripleFrequency, add_assoc]
    rw [he]
    apply congrArg (tensorModeCLM _)
    ext j i
    simp [outerTensorCLM, insertionTensor, curlCoefficientCLM, coefficientVec,
      coefficientCross, crossProduct, mul_assoc]
  · change tensorModeCLM (tripleFrequency (m, (q, n))) _ = _
    have he : tripleFrequency (m, (q, n)) = q + m + n := by
      simp [tripleFrequency, add_comm, add_left_comm]
    rw [he]
    apply congrArg (tensorModeCLM _)
    ext j i
    rfl

def interactionTensor (inner : Bool) (u : FourierVelocity) (k l m n : Wavevector) :
    Fin 3 → VelocityCoefficient :=
  insertionTensor inner u (k + l) m n (curlConvectionAtom u k l)

theorem interactionTest_eq_coefficients (inner : Bool) (u : FourierVelocity)
    (k l m n : Wavevector) (p : TripleIndex) :
    interactionTest inner u k l m n p =
      ∑ j : Fin 3, ∑ i : Fin 3,
        ((if outputFrequency k l m n = tripleFrequency p then
          (projectedCoeff (outputFrequency k l m n) (interactionTensor inner u k l m n) j i *
            conj (projectedCoeff (tripleFrequency p) (tensorCoeff u p) j i)).re else 0) +
          (if outputFrequency k l m n = -tripleFrequency p then
          (projectedCoeff (outputFrequency k l m n) (interactionTensor inner u k l m n) j i *
            projectedCoeff (tripleFrequency p) (tensorCoeff u p) j i).re else 0)) / 2 := by
  rw [interactionTest, insertionSlot_eq_tensor]
  exact inner_tensorMode _ _ _ _

theorem convectionAtom_neg (u : FourierVelocity) (k l : Wavevector) :
    convectionAtom (-u) k l = convectionAtom u k l := by
  have he : outputFiber (k + l) (-u) k = outputFiber (k + l) u k := by
    ext i
    simp [outputFiber, modeDot, Finset.sum_neg_distrib]
  simp only [convectionAtom, he]

theorem insertionSlot_neg (inner : Bool) (u : FourierVelocity)
    (q m n : Wavevector) (v : VelocityCoefficient) :
    insertionSlot inner (-u) q m n (coefficientVec v) =
      insertionSlot inner u q m n (coefficientVec v) := by
  let w : FourierVelocity := fun _ ↦ v
  cases inner
  · change outerSlot (-u) (q, (m, n)) (coefficientVec (w q)) =
      outerSlot u (q, (m, n)) (coefficientVec (w q))
    rw [outerSlot_apply, outerSlot_apply, mixedMode_neg_second, mixedMode_neg_third, neg_neg]
  · change leftSlot (-u) (m, (q, n)) (coefficientVec (w q)) =
      leftSlot u (m, (q, n)) (coefficientVec (w q))
    rw [leftSlot_apply, leftSlot_apply, mixedMode_neg_first, mixedMode_neg_third, neg_neg]

theorem mode_neg (u : FourierVelocity) (p : TripleIndex) : mode (-u) p = -mode u p := by
  rw [← mixedMode_self, mixedMode_neg_first, mixedMode_neg_second, mixedMode_neg_third,
    neg_neg, mixedMode_self]

theorem interactionTest_neg (inner : Bool) (u : FourierVelocity)
    (k l m n : Wavevector) (p : TripleIndex) :
    interactionTest inner (-u) k l m n p = -interactionTest inner u k l m n p := by
  rw [interactionTest, convectionAtom_neg, insertionSlot_neg, mode_neg, inner_neg_right]
  rfl

theorem heatInteraction_neg (inner : Bool) (ν σ : ℝ) (u : FourierVelocity)
    (k l m n : Wavevector) (p : TripleIndex) :
    heatInteraction inner ν σ (-u) k l m n p = -heatInteraction inner ν σ u k l m n p := by
  simp only [heatInteraction_eq, interactionTest_neg, mul_neg]

end Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxCoefficientFormula
