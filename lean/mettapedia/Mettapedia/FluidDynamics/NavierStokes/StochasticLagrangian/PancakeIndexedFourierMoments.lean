import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeInfiniteFourierDerivative
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeCurlOutputTail

/-!
# Absolute moments pay the actual indexed Fourier derivatives

The frequency map permits ordinary velocity modes and nonlinear input
pairs in the same construction. All derivative and curl coefficients
retain the physical factor 2*pi; the coefficient sup norm is bounded
explicitly by its Euclidean norm.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeIndexedFourierMoments

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakePeriodicVorticityEquation PancakeFrequencyProjectorCommutator PancakeIncomingLowSourceEnergy
open PancakeTransverseEnergyFreezing PancakeInfiniteFourierDerivative PancakeCurlOutputTail
open PancakeSameSectorDissipation

variable {ι : Type*}

def indexedFirstMoment (freq : ι → Wavevector) (a : ι → VelocityCoefficient) (n : ι) : ℝ :=
  (1 + ‖frequencyVec (freq n)‖) * ‖coefficientVec (a n)‖

def indexedCurlCoeff (freq : ι → Wavevector) (a : ι → VelocityCoefficient) (n : ι) : VelocityCoefficient :=
  unitTorusDerivativePhase • coefficientCross (wavevectorCoefficient (freq n)) (a n)

theorem indexedFirstMoment_nonneg (freq : ι → Wavevector) (a : ι → VelocityCoefficient) (n : ι) :
    0 ≤ indexedFirstMoment freq a n := by unfold indexedFirstMoment; positivity

theorem norm_coefficient_sup_le_euclidean (v : VelocityCoefficient) : ‖v‖ ≤ ‖coefficientVec v‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  exact PiLp.norm_apply_le (coefficientVec v) i

theorem norm_frequency_coordinate_le (k : Wavevector) (j : Fin 3) :
    ‖(k j : ℂ)‖ ≤ ‖frequencyVec k‖ :=
  PiLp.norm_apply_le (frequencyVec k) j

theorem norm_coefficient_le_indexedFirstMoment (freq : ι → Wavevector)
    (a : ι → VelocityCoefficient) (n : ι) : ‖a n‖ ≤ indexedFirstMoment freq a n := by
  apply (norm_coefficient_sup_le_euclidean (a n)).trans
  unfold indexedFirstMoment
  nlinarith [norm_nonneg (frequencyVec (freq n)), norm_nonneg (coefficientVec (a n))]

theorem norm_indexedDerivative_le_firstMoment (freq : ι → Wavevector)
    (a : ι → VelocityCoefficient) (j : Fin 3) (n : ι) :
    ‖indexedDerivativeCoeff freq j a n‖ ≤ (2 * Real.pi) * indexedFirstMoment freq a n := by
  rw [indexedDerivativeCoeff, norm_smul, norm_mul, norm_derivativePhase]
  calc
    _ ≤ (2 * Real.pi) * ‖frequencyVec (freq n)‖ * ‖coefficientVec (a n)‖ := by
      gcongr
      · exact norm_frequency_coordinate_le _ _
      · exact norm_coefficient_sup_le_euclidean _
    _ ≤ _ := by
      unfold indexedFirstMoment
      nlinarith [norm_nonneg (coefficientVec (a n)), Real.pi_pos]

theorem norm_indexedCurl_le_firstMoment (freq : ι → Wavevector)
    (a : ι → VelocityCoefficient) (n : ι) :
    ‖indexedCurlCoeff freq a n‖ ≤ (2 * Real.pi) * indexedFirstMoment freq a n := by
  apply (norm_coefficient_sup_le_euclidean _).trans
  change ‖unitTorusDerivativePhase • coefficientVec (coefficientCross (wavevectorCoefficient (freq n)) (a n))‖ ≤ _
  rw [norm_smul, norm_derivativePhase]
  apply (mul_le_mul_of_nonneg_left (norm_cross_le (freq n) (a n)) (by positivity)).trans
  unfold indexedFirstMoment
  nlinarith [norm_nonneg (coefficientVec (a n)), Real.pi_pos]

theorem summable_norm_coefficients (freq : ι → Wavevector) (a : ι → VelocityCoefficient)
    (ha : Summable (indexedFirstMoment freq a)) : Summable (fun n ↦ ‖a n‖) :=
  Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (norm_coefficient_le_indexedFirstMoment freq a) ha

theorem summable_norm_derivativeCoefficients (freq : ι → Wavevector) (a : ι → VelocityCoefficient)
    (ha : Summable (indexedFirstMoment freq a)) (j : Fin 3) :
    Summable (fun n ↦ ‖indexedDerivativeCoeff freq j a n‖) :=
  Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (norm_indexedDerivative_le_firstMoment freq a j)
    (ha.mul_left (2 * Real.pi))

theorem summable_norm_curlCoefficients (freq : ι → Wavevector) (a : ι → VelocityCoefficient)
    (ha : Summable (indexedFirstMoment freq a)) : Summable (fun n ↦ ‖indexedCurlCoeff freq a n‖) :=
  Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (norm_indexedCurl_le_firstMoment freq a)
    (ha.mul_left (2 * Real.pi))

theorem indexedFirstMoment_id (u : FourierVelocity) : indexedFirstMoment id u = fourierMoment 1 u := by
  funext k
  simp [indexedFirstMoment, fourierMoment]

end Mettapedia.FluidDynamics.NavierStokes.PancakeIndexedFourierMoments
