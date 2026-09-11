import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureTwoInputEnergy
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PhysicalPressureLocalization

/-!
# Two-input localization of the actual finite pressure

The pressure sign is inherited from the Galerkin pressure Hessian. For two
copies of one cutoff, the output is the pressure multiplied by its square.
The commutator derivative cost is expressed in physical gradient units.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureTwoInputPhysical

open scoped BigOperators
open MeasureTheory PeriodicFourierTriad PancakeFiniteFourierLocalization PancakeFrequencyProjectorCommutator
open ComplexPressureConvolution PressureBilinearLocalization FiniteCutoffAlgebra
open PressureTwoInputLocalization PressureTwoInputEnergy FourierEllipticProductEnergy
open PhysicalPressureLocalization PhysicalPressurePair PancakeFourierPressureStrain FourierPressureTraceSymbol
open PancakeGalerkinKineticEnergy PancakePeriodicVorticityEquation PancakeZeroModeCurlBridge
open FourierCoordinateDerivatives
open Mettapedia.Analysis.FiniteMultiplierLocalization

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def doublyLocalizedPressure (e : R3) (A D M : Finset Wavevector)
    (c d : Wavevector → ℂ) (u : FourierVelocity) : Wavevector → C3 :=
  vectorConvolution A (finiteCutoffOutputModes D (finiteCutoffOutputModes M M)) c
    (vectorConvolution D (finiteCutoffOutputModes M M) d
      (fun q ↦ (pressureHessianCoeff M u q).trace • complexTiltSymbol e q))

theorem doublyLocalizedPressure_eq_neg (e : R3) (A D M : Finset Wavevector)
    (c d : Wavevector → ℂ) (u : FourierVelocity) (hu : ∀ k ∈ M, modeDot k (u k) = 0)
    (q : Wavevector) : doublyLocalizedPressure e A D M c d u q =
      -doublyLocalizedOutput e A D M M c d (fourierCurl u) (fourierCurl u) q := by
  simp only [doublyLocalizedPressure, doublyLocalizedOutput, localizedOutput,
    vectorConvolution, pressureHessian_tilt_eq_pairConvolution e M u hu,
    smul_neg, Finset.sum_neg_distrib]

theorem doublyLocalizedPressure_add_localizedInputs (e : R3) (A D M : Finset Wavevector)
    (c d : Wavevector → ℂ) (u : FourierVelocity) (hu : ∀ k ∈ M, modeDot k (u k) = 0)
    (q : Wavevector) :
    doublyLocalizedPressure e A D M c d u q +
        localizedInputs e A D M M c d (fourierCurl u) (fourierCurl u) q =
      -twoInputCommutator e A D M M c d (fourierCurl u) (fourierCurl u) q := by
  rw [doublyLocalizedPressure_eq_neg e A D M c d u hu,
    ← doublyLocalizedOutput_sub_localizedInputs]
  abel

theorem twoInputCost_fourierCurl_le (A M : Finset Wavevector) (c : Wavevector → ℂ)
    (u : FourierVelocity) :
    twoInputCost A A M M c c (fourierCurl u) (fourierCurl u) ≤
      4 * (∑ a ∈ A, ‖c a‖) ^ 2 * physicalCommutatorCost M M u (fourierCurl u) *
        (‖unitTorusDerivativePhase‖ ^ 2 * coordinateEnergy A c) := by
  have hs : (∑ p ∈ M, ‖coefficientVec (fourierCurl u p)‖ / ‖frequencyVec p‖) ≤
      ‖unitTorusDerivativePhase‖ * ∑ p ∈ M, ‖coefficientVec (u p)‖ := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun p _ ↦ norm_curl_div_frequency_le u p)
  have hn : 0 ≤ ∑ p ∈ M, ‖coefficientVec (fourierCurl u p)‖ / ‖frequencyVec p‖ :=
    Finset.sum_nonneg (fun _ _ ↦ div_nonneg (norm_nonneg _) (norm_nonneg _))
  have hsq := pow_le_pow_left₀ hn hs 2
  have hG : 0 ≤ coordinateEnergy A c := by unfold coordinateEnergy scalarEnergy; positivity
  have hm := mul_le_mul_of_nonneg_right hsq
    (mul_nonneg (mul_nonneg (sq_nonneg (∑ a ∈ A, ‖c a‖))
      (sq_nonneg (∑ p ∈ M, ‖coefficientVec (fourierCurl u p)‖))) hG)
  unfold twoInputCost physicalCommutatorCost
  nlinarith only [hm]

theorem twoInputCommutator_energy_le_physical_gradient (e : R3) (he : ‖e‖ = 1)
    (A M Q : Finset Wavevector) (c : Wavevector → ℂ) (u : FourierVelocity)
    (hQ : ∀ a ∈ A, ∀ b ∈ A, ∀ p ∈ M, ∀ k ∈ M, a + (b + (p + k)) ∈ Q) :
    (∑ q ∈ Q, ‖twoInputCommutator e A A M M c c (fourierCurl u) (fourierCurl u) q‖ ^ 2) ≤
      4 * (∑ a ∈ A, ‖c a‖) ^ 2 * physicalCommutatorCost M M u (fourierCurl u) *
        (∑ j : Fin 3, ∫ x : T3, ‖polynomialDerivative A c j x‖ ^ 2) := by
  simp only [integral_polynomialDerivative_sq, ← Finset.mul_sum]
  exact (twoInputCommutator_energy_le e he A A M M Q c c (fourierCurl u) (fourierCurl u)
    (fourierCurl_zero u) (fourierCurl_zero u) hQ).trans (twoInputCost_fourierCurl_le A M c u)

end Mettapedia.FluidDynamics.NavierStokes.PressureTwoInputPhysical
