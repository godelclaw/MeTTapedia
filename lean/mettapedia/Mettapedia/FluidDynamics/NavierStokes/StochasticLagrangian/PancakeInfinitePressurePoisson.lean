import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeInfinitePressureHessian

/-!
# The ordinary pressure Poisson equation

The trace of the actual pressure Hessian is negative divergence of the
actual advection. Both sides are differentiated convergent fields.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeInfinitePressurePoisson

open scoped BigOperators
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeCurlOutputTail PancakeIndexedFourierMoments PancakeCoefficientLimitEquation
open PancakeInfinitePressureCoefficients PancakeInfiniteSpatialPressure PancakeInfinitePressureHessian
open PancakeInfiniteFourierDerivative PancakeInfiniteSpatialCurl PancakeLocalProjectedEquation
open PancakePhysicalConvectionCoefficients PancakePeriodicVorticityEquation
open PancakeIncomingLowSourceEnergy PancakePhysicalFourierDerivative

local notation "T3" => UnitAddTorus (Fin 3)

theorem summable_firstMoment_infiniteConvection (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) :
    Summable (fourierMoment 1 (infiniteConvection u)) := by
  convert (summable_norm_infiniteConvection u hu).add
    (summable_frequency_norm_infiniteConvection u hu) using 1
  funext q
  simp only [fourierMoment, pow_one]
  ring

theorem summable_firstMoment_advectionCoeff (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) :
    Summable (indexedFirstMoment id
      (fun q ↦ unitTorusDerivativePhase • infiniteConvection u q)) := by
  have hs := (summable_firstMoment_infiniteConvection u hu).mul_left (2 * Real.pi)
  have he : indexedFirstMoment id (fun q ↦ unitTorusDerivativePhase • infiniteConvection u q) =
      fun q ↦ (2 * Real.pi) * fourierMoment 1 (infiniteConvection u) q := by
    funext q
    change (1 + ‖frequencyVec q‖) *
      ‖unitTorusDerivativePhase • coefficientVec (infiniteConvection u q)‖ = _
    rw [norm_smul, norm_derivativePhase]
    simp only [fourierMoment, pow_one]
    ring
  rw [he]
  exact hs

def scalarLaplacian (f : T3 → ℂ) (x : T3) : ℂ :=
  ∑ j : Fin 3, scalarCoordinateDerivative (fun y ↦ scalarCoordinateDerivative f j y) j x

theorem scalarLaplacian_eq_trace (f : T3 → ℂ) (x : T3) :
    scalarLaplacian f x = (spatialHessian f x).trace := rfl

theorem spatialPressure_poisson (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (hd : ∀ q, modeDot q (u q) = 0) (x : T3) :
    scalarLaplacian (spatialPressure u) x =
      -spatialDivergence (spatialAdvection (fullFourierField id u)) x := by
  let a : FourierVelocity := fun q ↦ unitTorusDerivativePhase • infiniteConvection u q
  have ha : Summable (indexedFirstMoment id a) := summable_firstMoment_advectionCoeff u hu
  have hda (j : Fin 3) := summable_norm_derivativeCoefficients id a ha j
  have hdpa (j : Fin 3) := summable_norm_infinitePressureSecondDerivative u hu j j
  have hsp (j : Fin 3) : Summable (fun q ↦ UnitAddTorus.mFourier q x *
      indexedDerivativeCoeff id j (indexedDerivativeCoeff id j (infinitePressureCoeff u)) q) := by
    apply (hdpa j).of_norm_bounded
    intro q
    rw [norm_mul, norm_character, one_mul]
  have hsa (j : Fin 3) : Summable (fun q ↦
      UnitAddTorus.mFourier q x * indexedDerivativeCoeff id j a q j) :=
    Pi.summable.mp (summable_pointwise_modes id _ (hda j) x) j
  have hadv : spatialAdvection (fullFourierField id u) = fullFourierField id a :=
    (fullFourierField_advection u hu hd).symm
  simp only [scalarLaplacian, scalarCoordinateDerivative2_spatialPressure u hu,
    fullFourierField_apply id _ (hdpa _), smul_eq_mul, id_eq,
    hadv, spatialDivergence, coordinateDerivative_fullFourierField id a ha,
    fullFourierField_component id _ (hda _)]
  rw [← Summable.tsum_finsetSum (fun j _ ↦ hsp j),
    ← Summable.tsum_finsetSum (fun j _ ↦ hsa j), ← tsum_neg]
  apply tsum_congr
  intro q
  calc
    _ = UnitAddTorus.mFourier q x * unitTorusDerivativePhase^2 *
        (modeSquare q * infinitePressureCoeff u q) := by
      simp only [indexedDerivativeCoeff, smul_eq_mul, id_eq,
        modeSquare, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = -UnitAddTorus.mFourier q x * unitTorusDerivativePhase^2 *
        modeDot q (infiniteConvection u q) := by
      rw [infinitePressureCoeff_poisson]
      ring
    _ = _ := by
      simp only [indexedDerivativeCoeff, a, Pi.smul_apply, smul_eq_mul, id_eq,
        modeDot, Finset.mul_sum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring

end Mettapedia.FluidDynamics.NavierStokes.PancakeInfinitePressurePoisson
