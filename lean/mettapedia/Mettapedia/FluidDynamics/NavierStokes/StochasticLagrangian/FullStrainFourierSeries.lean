import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalAlignmentForcing
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeFourierStrainGradient

/-!
# The Fourier series of the full physical strain

One absolute velocity moment suffices to identify the Fourier strain
series with the symmetric derivative of the full velocity field.
Finite reconstructions converge to that actual operator. The domination
bound below is used for passage to the limit, not as a dynamical estimate.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FullStrainFourierSeries

open scoped Matrix.Norms.Elementwise Topology
open Filter PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFrequencyProjectorCommutator PancakePeriodicVorticityEquation
open PancakeFourierTranslationCurve PancakeInfiniteFourierDerivative PancakeIndexedFourierMoments
open PancakeInfiniteSpatialCurl
open PancakeLocalVelocityGradientTime PancakeLocalGradientEquation
open PancakeFourierPressureStrain PancakeFourierMaterialPaths PancakeFourierStrainGradient
open LocalAlignmentForcing

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

theorem summable_norm_strainCoeff (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) :
    Summable (fun k ↦ ‖strainCoeff u k‖) := by
  apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) _
    (hu.mul_left ‖unitTorusDerivativePhase‖)
  intro k
  apply (norm_strainCoeff_le u k).trans
  unfold fourierMoment
  simp only [pow_one]
  nlinarith [norm_nonneg (coefficientVec (u k)), norm_nonneg (frequencyVec k),
    norm_nonneg unitTorusDerivativePhase]

theorem hasSum_coordinateDerivative (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (j : Fin 3) (x : T3) :
    HasSum (fun k ↦ UnitAddTorus.mFourier k x • indexedDerivativeCoeff id j u k)
      (coordinateDerivative (fullFourierField id u) j x) := by
  have hm : Summable (indexedFirstMoment id u) := by
    simpa only [indexedFirstMoment_id] using hu
  rw [coordinateDerivative_fullFourierField id u hm]
  exact (ContinuousMap.evalCLM (R := ℂ) (M := VelocityCoefficient) x).hasSum
    (summable_modeField id _ (summable_norm_derivativeCoefficients id u hm j)).hasSum

theorem hasSum_strain_matrix (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (x : T3) :
    HasSum (fun k ↦ UnitAddTorus.mFourier k x • strainCoeff u k)
      (PancakeLocalStrainEquation.spatialStrain (fullFourierField id u) x) := by
  apply Pi.hasSum.mpr
  intro i
  apply Pi.hasSum.mpr
  intro j
  have hi := (Pi.hasSum.mp (hasSum_coordinateDerivative u hu j x)) i
  have hj := (Pi.hasSum.mp (hasSum_coordinateDerivative u hu i x)) j
  have h := (hi.add hj).mul_left (1 / 2 : ℂ)
  change HasSum _ ((1 / 2 : ℂ) *
    (coordinateDerivative (fullFourierField id u) j x i +
      coordinateDerivative (fullFourierField id u) i x j))
  apply h.congr_fun
  intro k
  simp only [strainCoeff, gradientCoeff, indexedDerivativeCoeff, id_eq,
    Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem fullStrainOperator_eq_fourierSeries (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (x : T3) :
    fullStrainOperator u x = realMatrixOperator (fullFourierField id (strainCoeff u) x) := by
  apply congrArg realMatrixOperator
  exact (hasSum_strain_matrix u hu x).unique
    ((ContinuousMap.evalCLM (R := ℂ) (M := MatrixCoefficient) x).hasSum
      (summable_modeField id _ (summable_norm_strainCoeff u hu)).hasSum)

theorem tendsto_spatialStrain (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (x : T3) :
    Tendsto (fun modes : Finset Wavevector ↦ (spatialStrain modes u x).1)
      atTop (𝓝 (fullStrainOperator u x)) := by
  have h := realMatrixOperatorCLM.hasSum (hasSum_strain_matrix u hu x)
  change Tendsto (fun modes : Finset Wavevector ↦
    realMatrixOperatorCLM (∑ k ∈ modes, UnitAddTorus.mFourier k x • strainCoeff u k))
    atTop (𝓝 (fullStrainOperator u x))
  simpa only [HasSum, map_sum, realMatrixOperatorCLM_apply, fullStrainOperator,
    SummationFilter.unconditional] using h

theorem norm_spatialStrain_le (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (x : T3) :
    ‖(spatialStrain modes u x).1‖ ≤ 9 * ∑' k, ‖strainCoeff u k‖ := by
  apply (norm_realMatrixOperator_le _).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact (norm_matrixReconstruction_le modes _ x).trans
    ((summable_norm_strainCoeff u hu).sum_le_tsum modes (fun _ _ ↦ norm_nonneg _))

end Mettapedia.FluidDynamics.NavierStokes.FullStrainFourierSeries
