import Mettapedia.Analysis.VorticityJetSource
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.HelicityAngularSource

/-!
# Actual strain–rotation splitting of the curl-vorticity source

The rotational contribution is the ordinary gradient of half the squared
vorticity magnitude. The symmetric contribution retains the actual strain
rows and vorticity derivatives. No source term is bounded or discarded.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.HelicitySourceStrainSplit

open scoped RealInnerProductSpace
open Mettapedia.Analysis VorticityJetSource
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeBlockReality PancakeInfiniteFourierDerivative PancakeInfiniteSpatialCurl
open PancakeDyadicDirectionEvolution PancakeTransverseEnergyFreezing
open LocalLowDiffusionBudget LocalSpatialVorticityJets LocalWeightedCurlCancellation
open HelicityAngularSource

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def strainSource (u : FourierVelocity) (x : T3) : R3 :=
  VorticityJetSource.source (strainRows (fun m ↦ realComponentGradient u m x))
    (fun j ↦ fullCurlGradient u j x)

def rotationSource (u : FourierVelocity) (x : T3) : R3 :=
  amplitudeGradient (fullVorticity u x) (fun j ↦ fullCurlGradient u j x)

theorem axialVector_componentGradient (u : FourierVelocity) (x : T3) :
    axialVector (fun m ↦ realComponentGradient u m x) = fullVorticity u x := by
  ext i
  fin_cases i <;>
    simp [axialVector, realComponentGradient, componentGradient, fullVorticity, spatialCurl,
      complexRealPartEuclideanCLM_apply, complexRealPartEuclidean, Matrix.cons_val_two]

/-- The source uses the same symmetric strain operator as the material
vorticity equation, expressed by its rows in the standard basis. -/
theorem strainRows_componentGradient (u : FourierVelocity) (m : Fin 3) (x : T3) :
    strainRows (fun k ↦ realComponentGradient u k x) m =
      WithLp.toLp 2 (fun j ↦ LocalAlignmentForcing.fullStrainOperator u x (EuclideanSpace.single j 1) m) := by
  ext j
  fin_cases m <;> fin_cases j <;>
    simp [strainRows, realComponentGradient, componentGradient,
      LocalAlignmentForcing.fullStrainOperator, PancakeFourierMaterialPaths.realMatrixOperator_apply,
      PancakeLocalStrainEquation.spatialStrain, PancakeFilteredStrainDynamics.symmetrize,
      PancakeLocalGradientEquation.spatialVelocityGradient, complexRealPartEuclideanCLM_apply,
      complexRealPartEuclidean]
  all_goals ring

theorem source_eq_strain_add_rotation (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (x : T3) :
    LocalHelicitySourceEvolution.source u x = strainSource u x + rotationSource u x := by
  rw [source_eq_cross u (summable_fourierMoment_of_le _ (by omega : 2 ≤ 3) hu) hd hr]
  change VorticityJetSource.source _ _ = _
  rw [VorticityJetSource.source_eq_strain_add_amplitudeGradient _ _
    (sum_fullCurlGradient_diagonal_eq_zero u hu x), axialVector_componentGradient]
  rfl

/-- This component is the actual first translation derivative of the
half-squared vorticity magnitude. -/
theorem hasDerivAt_half_vorticity_norm_sq (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (j : Fin 3) (x : T3) (h : ℝ) :
    HasDerivAt (fun t ↦ ‖fullVorticity u
      (x + PancakeFourierTranslationCurve.coordinateShift j t)‖ ^ 2 / 2)
      (rotationSource u (x + PancakeFourierTranslationCurve.coordinateShift j h) j) h := by
  simpa only [rotationSource, amplitudeGradient, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using
    (hasDerivAt_fullVorticity_shift u hu j x h).norm_sq.div_const 2

end Mettapedia.FluidDynamics.NavierStokes.HelicitySourceStrainSplit
