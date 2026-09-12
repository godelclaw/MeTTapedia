import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSpatialVorticityJets

/-! # Negation of the actual full Fourier vorticity and its spatial gradient -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalVorticityNegation

open PeriodicFourierTriad PancakeGalerkinKineticEnergy PancakePeriodicVorticityEquation
open PancakePeriodicComplexStretch
open PancakeInfiniteFourierDerivative PancakeInfiniteSpatialCurl PancakeInfiniteSpatialLaplacian
open LocalLowDiffusionBudget LocalSpatialVorticityJets PancakeDyadicDirectionEvolution

local notation "T3" => UnitAddTorus (Fin 3)

theorem fullFourierField_neg (u : FourierVelocity) :
    fullFourierField id (-u) = -fullFourierField id u := by
  simpa only [neg_one_smul, Pi.neg_def] using fullFourierField_smul (-1) u

theorem coordinateDerivative_neg (f : T3 → VelocityCoefficient) (j : Fin 3) (x : T3) :
    coordinateDerivative (-f) j x = -coordinateDerivative f j x := by
  change deriv (fun h : ℝ ↦ -f (x + PancakeFourierTranslationCurve.coordinateShift j h)) 0 = _
  exact deriv.fun_neg

theorem spatialCurl_neg (f : T3 → VelocityCoefficient) : spatialCurl (-f) = -spatialCurl f := by
  funext x i
  fin_cases i <;> simp [spatialCurl, coordinateDerivative_neg] <;> ring

theorem fullVorticity_neg (u : FourierVelocity) (x : T3) :
    fullVorticity (-u) x = -fullVorticity u x := by
  simp only [fullVorticity, fullFourierField_neg, ContinuousMap.coe_neg, spatialCurl_neg,
    Pi.neg_apply, map_neg]

theorem fourierCurl_neg (u : FourierVelocity) : fourierCurl (-u) = -fourierCurl u := by
  funext q i
  fin_cases i <;> simp [fourierCurl, coefficientCross] <;> ring

theorem fullCurlGradient_neg (u : FourierVelocity) (j : Fin 3) (x : T3) :
    fullCurlGradient (-u) j x = -fullCurlGradient u j x := by
  have he : indexedDerivativeCoeff id j (fourierCurl (-u)) =
      -indexedDerivativeCoeff id j (fourierCurl u) := by
    funext q
    simp only [indexedDerivativeCoeff, fourierCurl_neg, Pi.neg_apply, smul_neg]
  simp only [fullCurlGradient, he, fullFourierField_neg, ContinuousMap.neg_apply, map_neg]

end Mettapedia.FluidDynamics.NavierStokes.LocalVorticityNegation
