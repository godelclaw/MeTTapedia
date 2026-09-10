import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeInfiniteVelocityLipschitz
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeWeakIncompressibleTransport

/-!
# Weak incompressible transport by the full Fourier velocity

The velocity has no receiver or advector cutoff. Its ordinary coordinate
derivatives agree with the reconstructed derivatives, so Fourier
incompressibility gives zero mean transport of every periodic locally
Lipschitz scalar. This includes energies with spectral collisions.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.InfiniteFourierTransport

open scoped NNReal
open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit
open PancakeFrequencyProjectorCommutator PancakeCurlOutputTail
open PancakeIndexedFourierMoments PancakeInfiniteFourierDerivative
open PancakeInfiniteVelocityLipschitz PancakeFourierMaterialPaths
open PancakeFourierTranslationCurve PancakeHaarTransportRate
open PancakeInfiniteSpatialCurl PancakeLocalProjectedEquation
open PancakeWeakIncompressibleTransport

local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- An absolute first moment controls the entire real lift. -/
theorem lipschitzWith_fullFourierField_lift (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) :
    LipschitzWith (Real.toNNReal (3 * (2 * Real.pi) * ∑' q, fourierMoment 1 u q))
      (fun r : X3 ↦ fullFourierField id u (torusPoint r)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _
    (mul_nonneg (by positivity) (tsum_nonneg (fourierMoment_nonneg _ _)))]
  exact norm_fullFourierField_lift_sub_le u (fourierMoment 1 u)
    (fourierMoment_nonneg _ _) hu (fun _ ↦ le_rfl) x y

def velocityComponent (u : FourierVelocity) (j : Fin 3) (x : T3) : ℝ :=
  (fullFourierField id u x j).re

theorem continuous_velocityComponent (u : FourierVelocity) (j : Fin 3) :
    Continuous (velocityComponent u j) :=
  Complex.continuous_re.comp ((continuous_apply j).comp (fullFourierField id u).continuous)

theorem locallyLipschitz_velocityComponent (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (j : Fin 3) :
    LocallyLipschitz (fun r : X3 ↦ velocityComponent u j (torusPoint r)) := by
  exact Complex.reCLM.lipschitz.locallyLipschitz.comp
    ((ContinuousLinearMap.proj j : VelocityCoefficient →L[ℝ] ℂ).lipschitz.locallyLipschitz.comp
      (lipschitzWith_fullFourierField_lift u hu).locallyLipschitz)

theorem shiftRate_velocityComponent (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (j k : Fin 3) (x : T3) :
    shiftRate (velocityComponent u k) (coordinateShift j) x =
      (coordinateDerivative (fullFourierField id u) j x k).re := by
  have hm : Summable (indexedFirstMoment id u) := by
    simpa only [indexedFirstMoment_id] using hu
  have hd := hasDerivAt_fullFourierField_shift id u
    (summable_norm_coefficients id u hm) j
    (summable_norm_derivativeCoefficients id u hm j) 0 x
  have hk := (ContinuousLinearMap.proj k : VelocityCoefficient →L[ℝ] ℂ).hasFDerivAt.comp_hasDerivAt 0 hd
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 hk
  simpa only [shiftRate, velocityComponent, Function.comp_def, Complex.reCLM_apply,
    ContinuousLinearMap.proj_apply, coordinateShift_zero, add_zero,
    coordinateDerivative_fullFourierField id u hm] using hr.deriv

theorem coordinateDivergence_velocity_zero (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (hd : ∀ q, modeDot q (u q) = 0) (x : T3) :
    coordinateDivergence (velocityComponent u) x = 0 := by
  simp only [coordinateDivergence,
    shiftRate_velocityComponent u (summable_firstMoment_of_second u hu), ← Complex.re_sum]
  change (spatialDivergence (fullFourierField id u) x).re = 0
  rw [spatialDivergence_fullFourierField u hu hd x, Complex.zero_re]

/-- No differentiability of the transported scalar is required everywhere. -/
theorem integral_coordinateTransport_zero (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (f : T3 → ℝ) (hf : Continuous f)
    (hfL : LocallyLipschitz (fun r : X3 ↦ f (torusPoint r))) :
    Integrable (coordinateTransport f (velocityComponent u)) ∧
      (∫ x : T3, coordinateTransport f (velocityComponent u) x) = 0 :=
  PancakeWeakIncompressibleTransport.integral_coordinateTransport_zero f _ hf
    (continuous_velocityComponent u) hfL
    (locallyLipschitz_velocityComponent u (summable_firstMoment_of_second u hu))
    (Filter.Eventually.of_forall (coordinateDivergence_velocity_zero u hu hd))

end Mettapedia.FluidDynamics.NavierStokes.InfiniteFourierTransport
