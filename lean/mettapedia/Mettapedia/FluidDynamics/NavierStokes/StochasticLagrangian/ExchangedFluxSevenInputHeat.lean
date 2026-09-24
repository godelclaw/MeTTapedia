import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ExchangedFluxHeatAdjoint
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierHeatCommutatorReflection

/-!
# Seven-input heat factors in the actual exchanged-flux pairing

The two nonlinear inputs, two remaining variation inputs, and three
projected-flux inputs retain their separate frequencies. The denominator
center is the sum of all seven input damping rates. These identities do
not assert cancellation of the full interaction sum.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxSevenInputHeat

open scoped RealInnerProductSpace
open MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeFrequencyProjectorCommutator PancakeSobolevFiberEnvelope
open PancakeGalerkinKineticEnergy PancakePeriodicVorticityEquation
open PancakeFilteredStrainDynamics
open PeriodicGradientFluxTriple FourierVorticityPairDynamics FourierStretchingInteractionDynamics
open FourierHeatFlow FourierHeatCommutatorKernel FourierHeatCommutatorReflection
open ExchangedFluxModeDynamics ExchangedFluxVariation ExchangedFluxHeatVariation ExchangedFluxAdjoint

local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "H" => Mettapedia.Analysis.UnitTorusGradientProjection.TensorL2
  (Fin 3) (EuclideanSpace ℝ (Fin 3))

theorem outerSlot_heat (ν σ : ℝ) (u : FourierVelocity) (q m n : Wavevector) (v : C3) :
    outerSlot (coefficients ν σ u) (q, (m, n)) v =
      (multiplier ν σ m * multiplier ν σ n) • outerSlot u (q, (m, n)) v := by
  change tensorModeCLM _ ((outerTensorCLM _ _) v) = _ • tensorModeCLM _ ((outerTensorCLM _ _) v)
  rw [← map_smul]
  apply congrArg (tensorModeCLM _)
  ext j i
  simp only [outerTensorCLM, ContinuousLinearMap.pi_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply]
  simp only [fourierCurl_coefficients]
  simp only [coefficients, filteredVelocity,
    coefficientCross_smul_smul, map_smul, Pi.smul_apply, smul_smul,
    RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.ofReal_eq_complex_ofReal, smul_eq_mul]
  push_cast
  simp only [ContinuousLinearMap.pi_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem leftSlot_heat (ν σ : ℝ) (u : FourierVelocity) (q m n : Wavevector) (v : C3) :
    leftSlot (coefficients ν σ u) (m, (q, n)) v =
      (multiplier ν σ m * multiplier ν σ n) • leftSlot u (m, (q, n)) v := by
  change tensorModeCLM _ ((leftTensorCLM _ _) v) = _ • tensorModeCLM _ ((leftTensorCLM _ _) v)
  rw [← map_smul]
  apply congrArg (tensorModeCLM _)
  ext j i
  change ((1 / 2 : ℂ) * fourierCurl (coefficients ν σ u) m j) *
      differenceCLM (m, (q, n))
        (crossProduct ((curlCoefficientCLM q) v) (fourierCurl (coefficients ν σ u) n)) i =
    (multiplier ν σ m * multiplier ν σ n : ℝ) •
      (((1 / 2 : ℂ) * fourierCurl u m j) *
        differenceCLM (m, (q, n)) (crossProduct ((curlCoefficientCLM q) v) (fourierCurl u n)) i)
  simp only [fourierCurl_coefficients]
  simp only [coefficients, filteredVelocity, map_smul, Pi.smul_apply,
    RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.ofReal_eq_complex_ofReal, smul_eq_mul]
  push_cast
  ring

/-- False is the outer insertion; true is one of the two exchanged inner insertions. -/
def insertionSlot (inner : Bool) (u : FourierVelocity) (q m n : Wavevector) : C3 →L[ℝ] H :=
  if inner then leftSlot u (m, (q, n)) else outerSlot u (q, (m, n))

theorem insertionSlot_heat (inner : Bool) (ν σ : ℝ) (u : FourierVelocity)
    (q m n : Wavevector) (v : C3) :
    insertionSlot inner (coefficients ν σ u) q m n v =
      (multiplier ν σ m * multiplier ν σ n) • insertionSlot inner u q m n v := by
  cases inner
  · exact outerSlot_heat ν σ u q m n v
  · exact leftSlot_heat ν σ u q m n v

def remainingDamping (ν : ℝ) (m n : Wavevector) (p : TripleIndex) : ℝ :=
  pairDamping ν m n + interactionDamping ν p

def totalDamping (ν : ℝ) (k l m n : Wavevector) (p : TripleIndex) : ℝ :=
  pairDamping ν k l + remainingDamping ν m n p

theorem centerRate_eq_totalDamping (ν : ℝ) (k l m n : Wavevector) (p : TripleIndex) :
    centerRate ν (remainingDamping ν m n p) k l = totalDamping ν k l m n p := by
  unfold centerRate totalDamping
  ring

theorem totalDamping_exchange (ν : ℝ) (k l m n : Wavevector) (p : TripleIndex) :
    totalDamping ν k l m n p = totalDamping ν k m l n p := by
  unfold totalDamping remainingDamping pairDamping
  ring

/-- One actual ordered convection coefficient, including its Leray projection. -/
def convectionAtom (u : FourierVelocity) (k l : Wavevector) : VelocityCoefficient :=
  lerayMode (k + l) ((-unitTorusDerivativePhase) • outputFiber (k + l) u k)

def interactionTest (inner : Bool) (u : FourierVelocity)
    (k l m n : Wavevector) (p : TripleIndex) : ℝ :=
  ⟪insertionSlot inner u (k + l) m n (coefficientVec (convectionAtom u k l)), mode u p⟫

def heatInteraction (inner : Bool) (ν σ : ℝ) (u : FourierVelocity)
    (k l m n : Wavevector) (p : TripleIndex) : ℝ :=
  ⟪insertionSlot inner (coefficients ν σ u) (k + l) m n
      ((multiplier ν σ (k + l) - multiplier ν σ k * multiplier ν σ l) •
        coefficientVec (convectionAtom u k l)), mode (coefficients ν σ u) p⟫

theorem heatInteraction_eq (inner : Bool) (ν σ : ℝ) (u : FourierVelocity)
    (k l m n : Wavevector) (p : TripleIndex) :
    heatInteraction inner ν σ u k l m n p =
      (Real.exp (-remainingDamping ν m n p * σ) *
        (multiplier ν σ (k + l) - multiplier ν σ k * multiplier ν σ l)) *
          interactionTest inner u k l m n p := by
  rw [heatInteraction, map_smul, insertionSlot_heat, mode_heat,
    real_inner_smul_left, real_inner_smul_left, real_inner_smul_right]
  rw [multiplier_pair ν σ m n]
  have he : Real.exp (-pairDamping ν m n * σ) * Real.exp (-interactionDamping ν p * σ) =
      Real.exp (-remainingDamping ν m n p * σ) := by
    rw [← Real.exp_add]
    congr 1
    unfold remainingDamping
    ring
  unfold interactionTest
  rw [← he]
  ring

/-- Positive remaining damping makes each coefficient absolutely integrable in heat time. -/
theorem integrableOn_heatInteraction (inner : Bool) {ν : ℝ} (hν : 0 ≤ ν)
    (u : FourierVelocity) (k l m n : Wavevector) (p : TripleIndex)
    (hc : 0 < remainingDamping ν m n p) :
    IntegrableOn (fun σ ↦ heatInteraction inner ν σ u k l m n p) (Set.Ioi 0) := by
  have hd : 0 ≤ modeDamping ν (k + l) := by unfold modeDamping; positivity
  have hp := pairDamping_nonneg hν k l
  have he : (fun σ ↦ heatInteraction inner ν σ u k l m n p) = fun σ ↦
      (Real.exp (-(remainingDamping ν m n p + modeDamping ν (k + l)) * σ) -
        Real.exp (-(remainingDamping ν m n p + pairDamping ν k l) * σ)) *
          interactionTest inner u k l m n p := by
    funext σ
    rw [heatInteraction_eq, multiplier_pair]
    unfold multiplier
    rw [mul_sub, ← Real.exp_add, ← Real.exp_add]
    congr 2 <;> congr 1 <;> ring
  rw [he]
  exact ((integrableOn_exp_mul_Ioi (by linarith) 0).sub
    (integrableOn_exp_mul_Ioi (by linarith) 0)).mul_const _

/-- Exact integration of a genuine seven-input coefficient, not a free test field. -/
theorem integral_heatInteraction (inner : Bool) (ν : ℝ) (u : FourierVelocity)
    (k l m n : Wavevector) (p : TripleIndex) :
    (∫ σ : ℝ in Set.Ioi 0, heatInteraction inner ν σ u k l m n p) =
      integratedKernel ν (remainingDamping ν m n p) k l * interactionTest inner u k l m n p := by
  simp only [heatInteraction_eq, integral_mul_const, integratedKernel]

theorem integral_heatInteraction_eq_defect (inner : Bool) {ν : ℝ} (hν : 0 ≤ ν)
    (u : FourierVelocity) (k l m n : Wavevector) (p : TripleIndex)
    (hc : 0 < remainingDamping ν m n p) :
    (∫ σ : ℝ in Set.Ioi 0, heatInteraction inner ν σ u k l m n p) =
      Mettapedia.Analysis.BalancedResolvent.defect (totalDamping ν k l m n p)
        (outputShift ν k l) * interactionTest inner u k l m n p := by
  rw [integral_heatInteraction, integratedKernel_eq_defect hν hc, centerRate_eq_totalDamping]

end Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxSevenInputHeat
