import Mettapedia.Analysis.CurlCrossProduct
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FullAngularSourceAdjoint
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeFullAnalyticNonlinearity

/-!
# The full inviscid vorticity source as curl of velocity cross vorticity

All derivative jets come from the same infinite Fourier velocity. Both
divergences vanish by Fourier incompressibility; the antisymmetric
gradient annihilates its own axial vorticity. No strain or transport
term is estimated separately in this identity.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FullLambVector

open scoped RealInnerProductSpace ComplexConjugate
open MeasureTheory Mettapedia.Analysis EuclideanCrossProduct WeightedCurlCancellation
open PeriodicFourierTriad PancakeCurlOutputTail PancakeBlockReality
open PancakeHigherDerivativeMoments PancakeIndexedFourierMoments PancakeInfiniteFourierDerivative
open PancakeInfiniteSpatialCurl PancakeInfiniteRealCurl PancakeDyadicDirectionEvolution
open PancakeTransverseEnergyFreezing PancakeFourierTranslationCurve PancakeHaarTransportRate
open PancakeLocalGradientEquation PancakeLocalProjectedEquation PancakeFourierMaterialPaths
open PancakeGalerkinKineticEnergy PancakeCoefficientLimitEquation PancakePeriodicCoherentSplit
open LocalLowDiffusionBudget LocalSpatialVorticityJets LocalWeightedCurlCancellation
open LocalVorticitySeparation LocalAlignmentForcing LocalProjectionTransport
open SpatialVorticityInviscidRate

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def velocityJet (u : FourierVelocity) (j : Fin 3) (x : T3) : R3 :=
  complexRealPartEuclideanCLM (fullFourierField id (indexedDerivativeCoeff id j u) x)

theorem continuous_velocityJet (u : FourierVelocity) (j : Fin 3) : Continuous (velocityJet u j) :=
  complexRealPartEuclideanCLM.continuous.comp (fullFourierField id _).continuous

theorem continuous_realFullField (u : FourierVelocity) : Continuous (realFullField u) :=
  complexRealPartEuclideanCLM.continuous.comp (fullFourierField id u).continuous

theorem hasDerivAt_realFullField_shift (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (j : Fin 3) (x : T3) (h : ℝ) :
    HasDerivAt (fun t ↦ realFullField u (x + coordinateShift j t))
      (velocityJet u j (x + coordinateShift j h)) h := by
  have hm : Summable (indexedFirstMoment id u) := by simpa only [indexedFirstMoment_id] using hu
  exact complexRealPartEuclideanCLM.hasFDerivAt.comp_hasDerivAt h
    (hasDerivAt_fullFourierField_shift id u (summable_norm_coefficients id u hm) j
      (summable_norm_derivativeCoefficients id u hm j) h x)

theorem sum_velocityJet_diagonal (u : FourierVelocity) (hu : Summable (fourierMoment 2 u))
    (hd : ∀ q, modeDot q (u q) = 0) (x : T3) : (∑ j : Fin 3, velocityJet u j x j) = 0 := by
  have hm : Summable (indexedFirstMoment id u) := by
    simpa only [indexedFirstMoment_id] using summable_firstMoment_of_second u hu
  have h := congrArg Complex.re (spatialDivergence_fullFourierField u hu hd x)
  simpa only [spatialDivergence, coordinateDerivative_fullFourierField _ _ hm,
    Complex.re_sum, Complex.zero_re, velocityJet, complexRealPartEuclideanCLM_apply,
    complexRealPartEuclidean, PiLp.toLp_apply] using h

theorem directional_velocityJet (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (x : T3) (a : R3) : (∑ j : Fin 3, a j • velocityJet u j x) = gradient u x a := by
  have hm : Summable (indexedFirstMoment id u) := by simpa only [indexedFirstMoment_id] using hu
  change _ = realMatrixOperator (spatialVelocityGradient (fullFourierField id u) x) a
  ext i
  rw [realMatrixOperator_apply]
  simp [velocityJet, spatialVelocityGradient, coordinateDerivative_fullFourierField _ _ hm,
    complexRealPartEuclideanCLM_apply, complexRealPartEuclidean, mul_comm]

def lambVector (u : FourierVelocity) (x : T3) : R3 := cross (realFullField u x) (fullVorticity u x)

def lambDerivative (u : FourierVelocity) (j : Fin 3) (x : T3) : R3 :=
  cross (velocityJet u j x) (fullVorticity u x) + cross (realFullField u x) (fullCurlGradient u j x)

theorem continuous_lambVector (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) :
    Continuous (lambVector u) :=
  contDiff_cross.continuous.comp ((continuous_realFullField u).prodMk (continuous_fullVorticity u hu))

theorem continuous_lambDerivative (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (j : Fin 3) : Continuous (lambDerivative u j) :=
  (contDiff_cross.continuous.comp ((continuous_velocityJet u j).prodMk
    (continuous_fullVorticity u hu))).add
      (contDiff_cross.continuous.comp ((continuous_realFullField u).prodMk
        (LocalSquaredGapGradient.continuous_fullCurlGradient u j)))

theorem hasDerivAt_lambVector_shift (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (j : Fin 3) (x : T3) (h : ℝ) :
    HasDerivAt (fun t ↦ lambVector u (x + coordinateShift j t))
      (lambDerivative u j (x + coordinateShift j h)) h :=
  hasDerivAt_cross (hasDerivAt_realFullField_shift u
    (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu) j x h)
    (hasDerivAt_fullVorticity_shift u hu j x h)

theorem curlJet_lambDerivative (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (hd : ∀ q, modeDot q (u q) = 0) (x : T3) :
    curlJet (fun j ↦ lambDerivative u j x) =
      fullStrainOperator u x (fullVorticity u x) - transportVorticity u u x := by
  unfold lambDerivative
  rw [curlJet_cross_of_divergence_zero _ _ _ _
    (sum_velocityJet_diagonal u (summable_fourierMoment_of_le u (by omega : 2 ≤ 3) hu) hd x)
    (sum_fullCurlGradient_diagonal_eq_zero u hu x),
    directional_velocityJet u (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu),
    gradient_vorticity]
  rfl

theorem realSpatialCurl_lambVector (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (x : T3) : realSpatialCurl (lambVector u) x = curlJet (fun j ↦ lambDerivative u j x) := by
  have hd (j : Fin 3) : realCoordinateDerivative (lambVector u) j x = lambDerivative u j x := by
    simpa only [realCoordinateDerivative, coordinateShift_zero, add_zero] using
      (hasDerivAt_lambVector_shift u hu j x 0).deriv
  simp only [realSpatialCurl, hd, curlJet]

theorem fullVorticity_inviscidRHS_eq_curl_lambVector (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (x : T3) :
    fullVorticity (infiniteVelocityRHS 0 u) x = realSpatialCurl (lambVector u) x := by
  rw [realSpatialCurl_lambVector u hu, curlJet_lambDerivative u hu hd]
  exact eq_sub_iff_add_eq.mpr (fullVorticity_inviscidRHS u hu hd hr x)

end Mettapedia.FluidDynamics.NavierStokes.FullLambVector
