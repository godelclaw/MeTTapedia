import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLocalPressureContinuity

/-!
# Higher absolute moments for ordinary spatial derivatives

One coordinate derivative costs one absolute Fourier moment. These bounds
supply the differentiated viscous equation on the same local interval.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeHigherDerivativeMoments

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeCurlOutputTail PancakeIndexedFourierMoments PancakeInfiniteFourierDerivative
open PancakeInfiniteSpatialCurl PancakeInfiniteSpatialLaplacian PancakePeriodicVorticityEquation
open PancakeIncomingLowSourceEnergy

local notation "T3" => UnitAddTorus (Fin 3)

theorem fourierMoment_mono (u : FourierVelocity) {m n : ℕ} (hmn : m ≤ n) (q : Wavevector) :
    fourierMoment m u q ≤ fourierMoment n u q :=
  mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by linarith [norm_nonneg (frequencyVec q)]) hmn) (norm_nonneg _)

theorem summable_fourierMoment_of_le (u : FourierVelocity) {m n : ℕ}
    (hmn : m ≤ n) (hu : Summable (fourierMoment n u)) :
    Summable (fourierMoment m u) :=
  hu.of_nonneg_of_le (fourierMoment_nonneg _ _) (fourierMoment_mono u hmn)

theorem fourierMoment_derivative_le (m : ℕ) (u : FourierVelocity) (j : Fin 3) (q : Wavevector) :
    fourierMoment m (indexedDerivativeCoeff id j u) q ≤
      (2 * Real.pi) * fourierMoment (m+1) u q := by
  change (1 + ‖frequencyVec q‖)^m *
    ‖(unitTorusDerivativePhase * (q j : ℂ)) • coefficientVec (u q)‖ ≤ _
  rw [norm_smul, norm_mul, norm_derivativePhase]
  calc
    _ ≤ (1 + ‖frequencyVec q‖)^m *
        ((2 * Real.pi) * (1 + ‖frequencyVec q‖) * ‖coefficientVec (u q)‖) := by
      gcongr
      exact (norm_frequency_coordinate_le q j).trans (le_add_of_nonneg_left zero_le_one)
    _ = _ := by
      simp only [fourierMoment, pow_succ]
      ring

theorem summable_fourierMoment_derivative (m : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment (m+1) u)) (j : Fin 3) :
    Summable (fourierMoment m (indexedDerivativeCoeff id j u)) :=
  (hu.mul_left (2 * Real.pi)).of_nonneg_of_le (fourierMoment_nonneg _ _)
    (fourierMoment_derivative_le m u j)

theorem indexedDerivativeCoeff_commute (u : FourierVelocity) (i j : Fin 3) :
    indexedDerivativeCoeff id i (indexedDerivativeCoeff id j u) =
      indexedDerivativeCoeff id j (indexedDerivativeCoeff id i u) := by
  funext q l
  simp only [indexedDerivativeCoeff, Pi.smul_apply, smul_eq_mul]
  ring

theorem coordinateDerivative2_commute (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (i j : Fin 3) (x : T3) :
    coordinateDerivative (fun y ↦ coordinateDerivative (fullFourierField id u) j y) i x =
      coordinateDerivative (fun y ↦ coordinateDerivative (fullFourierField id u) i y) j x := by
  simp only [coordinateDerivative2_fullFourierField u hu, indexedDerivativeCoeff_commute u i j]

theorem coordinateDerivative_fullFourierField_eq (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (j : Fin 3) :
    (fun x ↦ coordinateDerivative (fullFourierField id u) j x) =
      fullFourierField id (indexedDerivativeCoeff id j u) := by
  funext x
  exact coordinateDerivative_fullFourierField id u
    (by simpa only [indexedFirstMoment_id] using hu) j x

end Mettapedia.FluidDynamics.NavierStokes.PancakeHigherDerivativeMoments
