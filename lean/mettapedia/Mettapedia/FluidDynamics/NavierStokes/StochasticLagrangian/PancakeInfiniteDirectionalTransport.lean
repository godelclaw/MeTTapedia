import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLocalMaterialTrajectories

/-!
# Directional Fourier coefficients and actual spatial transport

The character rate along a real velocity is a finite sum of ordinary
coordinate derivative multipliers. Absolute moments justify reconstruction.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeInfiniteDirectionalTransport

open scoped BigOperators
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicVorticityEquation
open PancakeFourierMaterialPaths PancakeFrequencyProjectorCommutator
open PancakeIndexedFourierMoments PancakeInfiniteFourierDerivative PancakeCurlOutputTail
open PancakeInfiniteVelocityLipschitz PancakeInfiniteSpatialLaplacian PancakeInfiniteSpatialCurl
open PancakeIncomingLowSourceEnergy PancakeConcreteSmoothCellCutoff
open PancakeHigherDerivativeMoments PancakeSpatialGradientDifferentiation

local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ

def directionalCoeff (u : FourierVelocity) (v : X3) (q : Wavevector) : VelocityCoefficient :=
  (unitTorusDerivativePhase * (realModeDot q v : ℂ)) • u q

theorem norm_directionalCoeff_le (u : FourierVelocity) (v : X3) (q : Wavevector) :
    ‖directionalCoeff u v q‖ ≤ (3 * (2 * Real.pi) * ‖v‖) * fourierMoment 1 u q := by
  rw [directionalCoeff, norm_smul, norm_mul, norm_derivativePhase, Complex.norm_real]
  calc
    _ ≤ ((2 * Real.pi) * (3 * ‖frequencyVec q‖ * ‖v‖)) * ‖coefficientVec (u q)‖ := by
      gcongr
      · exact norm_realModeDot_le q v
      · exact norm_coefficient_sup_le_euclidean _
    _ ≤ _ := by
      simp only [fourierMoment, pow_one]
      nlinarith [mul_nonneg (norm_nonneg v) (norm_nonneg (coefficientVec (u q))), Real.pi_pos]

theorem summable_norm_directionalCoeff (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (v : X3) :
    Summable (fun q ↦ ‖directionalCoeff u v q‖) :=
  (hu.mul_left _).of_nonneg_of_le (fun _ ↦ norm_nonneg _) (norm_directionalCoeff_le u v)

theorem directionalCoeff_eq_sum (u : FourierVelocity) (v : X3) :
    directionalCoeff u v = fun q ↦ ∑ j : Fin 3, (v j : ℂ) • indexedDerivativeCoeff id j u q := by
  funext q
  ext i
  simp only [directionalCoeff, realModeDot, indexedDerivativeCoeff, id_eq, Complex.ofReal_sum,
    Complex.ofReal_mul, Complex.ofReal_intCast, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem fullFourierField_directionalCoeff (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (v : X3) (x : T3) :
    fullFourierField id (directionalCoeff u v) x =
      ∑ j : Fin 3, (v j : ℂ) • coordinateDerivative (fullFourierField id u) j x := by
  have hm : Summable (indexedFirstMoment id u) := by simpa only [indexedFirstMoment_id] using hu
  rw [directionalCoeff_eq_sum, fullFourierField_finsetSum]
  · simp only [fullFourierField_smul, ContinuousMap.coe_sum, Finset.sum_apply,
      ContinuousMap.coe_smul, Pi.smul_apply,
      coordinateDerivative_fullFourierField id u hm]
  · intro j _
    simpa only [norm_smul] using (summable_norm_derivativeCoefficients id u hm j).mul_left ‖(v j : ℂ)‖

theorem fullFourierField_directionalCoeff_transport (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (U : T3 → VelocityCoefficient)
    (x : T3) (hr : ∀ i, ((U x i).re : ℂ) = U x i) :
    fullFourierField id (directionalCoeff u (fun i ↦ (U x i).re)) x =
      spatialTransport U (fullFourierField id u) x := by
  rw [fullFourierField_directionalCoeff u hu]
  simp only [hr, spatialTransport]

end Mettapedia.FluidDynamics.NavierStokes.PancakeInfiniteDirectionalTransport
