import Mettapedia.Analysis.PeriodicRadialRieszSolenoidal
import Mettapedia.Analysis.SolenoidalCrossIncrement
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSpatialVorticityJets
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FullVorticityFourierCoefficients
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSquaredGapGradient

/-!
# Radial solenoidal cancellation for the full vorticity and its derivatives

The fields are the actual full Fourier curl and coordinate derivatives.
Transversality is proved from their coefficients; annihilation is not an
assumed field-transfer condition. The variable-background identity retains
its signed increment and does not bound the remaining amplitude channel.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalRadialSolenoidal

open MeasureTheory Mettapedia.Analysis EuclideanCrossProduct
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeGalerkinKineticEnergy PancakeDyadicDirectionEvolution
open PancakeInfiniteFourierDerivative PancakeInfiniteSpatialLaplacian PancakeIndexedFourierMoments
open PancakeInfiniteSpatialCurl PancakeHigherDerivativeMoments PancakeFourierTranslationCurve
open LocalLowDiffusionBudget LocalJointDiffusionBudget LocalSpatialVorticityJets
open scoped RealInnerProductSpace
local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem integral_tensor_fullFourierField_eq_zero (N : ℕ) (a : FourierVelocity)
    (ha : Summable (fun k ↦ ‖a k‖)) (hd : ∀ k, modeDot k (a k) = 0) (x : T3) :
    (∫ h : T3, PeriodicRadialRiesz.tensor N h
      (complexRealPartEuclideanCLM (fullFourierField id a (x - h)))) = 0 := by
  let f (j : Fin 3) : C(T3, ℂ) :=
    (ContinuousLinearMap.proj j : VelocityCoefficient →L[ℂ] ℂ).compLeftContinuous ℂ T3
      (fullFourierField id a)
  have hs (j : Fin 3) : HasSum (fun k ↦ a k j • UnitAddTorus.mFourier k) (f j) := by
    have h := ((ContinuousLinearMap.proj j : VelocityCoefficient →L[ℂ] ℂ).compLeftContinuous ℂ T3).hasSum
      (summable_modeField id a ha).hasSum
    apply h.congr_fun
    intro k
    ext y
    change a k j * UnitAddTorus.mFourier k y = UnitAddTorus.mFourier k y * a k j
    ring
  exact PeriodicRadialRiesz.integral_tensor_realPart_eq_zero N f a hs hd
    (fun y ↦ complexRealPartEuclideanCLM (fullFourierField id a y))
    (complexRealPartEuclideanCLM.continuous.comp (fullFourierField id a).continuous)
    (fun _ _ ↦ rfl) x

theorem integral_tensor_fullVorticity_eq_zero (N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (x : T3) :
    (∫ h : T3, PeriodicRadialRiesz.tensor N h (fullVorticity u (x - h))) = 0 := by
  simp only [fullVorticity, spatialCurl_velocity u hu]
  exact integral_tensor_fullFourierField_eq_zero N (fourierCurl u)
    (FullVorticityFourierCoefficients.summable_norm_fourierCurl u hu)
    (fun k ↦ fourierCurl_transverse k u) x

theorem derivative_curl_transverse (u : FourierVelocity) (j : Fin 3) (k : Wavevector) :
    modeDot k (indexedDerivativeCoeff id j (fourierCurl u) k) = 0 := by
  change (∑ i : Fin 3, (k i : ℂ) *
    ((PancakePeriodicVorticityEquation.unitTorusDerivativePhase * (k j : ℂ)) * fourierCurl u k i)) = 0
  calc
    _ = (PancakePeriodicVorticityEquation.unitTorusDerivativePhase * (k j : ℂ)) *
        modeDot k (fourierCurl u k) := by
      simp only [modeDot, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 0 := by rw [fourierCurl_transverse, mul_zero]

theorem integral_tensor_fullCurlGradient_eq_zero (N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (j : Fin 3) (x : T3) :
    (∫ h : T3, PeriodicRadialRiesz.tensor N h (fullCurlGradient u j (x - h))) = 0 := by
  have hw1 : Summable (indexedFirstMoment id (fourierCurl u)) := by
    simpa only [indexedFirstMoment_id] using
      summable_firstMoment_of_second _ (summable_secondMoment_curl u hu)
  exact integral_tensor_fullFourierField_eq_zero N (indexedDerivativeCoeff id j (fourierCurl u))
    (summable_norm_derivativeCoefficients id _ hw1 j) (derivative_curl_transverse u j) x

theorem integral_gradient_cross_eq_background_increment (N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (j : Fin 3) (q : T3 → R3) (hq : Continuous q) :
    (∫ x : T3, ∫ y : T3,
      ⟪cross (fullCurlGradient u j x - fullCurlGradient u j y) (q x),
        PeriodicRadialRiesz.tensor N (x - y) (fullCurlGradient u j x - fullCurlGradient u j y)⟫) =
      ∫ x : T3, ∫ y : T3,
        ⟪cross (fullCurlGradient u j x) (q y - q x),
          PeriodicRadialRiesz.tensor N (x - y) (fullCurlGradient u j x - fullCurlGradient u j y)⟫ :=
  SolenoidalCrossIncrement.integral_cross_increment_eq_background_increment _
    (PeriodicRadialRiesz.continuous_tensor N) (PeriodicRadialRiesz.tensor_neg N)
    (PeriodicRadialRiesz.integral_tensor_eq_zero N) _ q
    (LocalSquaredGapGradient.continuous_fullCurlGradient u j) hq
    (integral_tensor_fullCurlGradient_eq_zero N u hu j)

theorem integral_gradient_cross_constant_eq_zero (N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (j : Fin 3) (q : R3) :
    (∫ x : T3, ∫ y : T3,
      ⟪cross (fullCurlGradient u j x - fullCurlGradient u j y) q,
        PeriodicRadialRiesz.tensor N (x - y) (fullCurlGradient u j x - fullCurlGradient u j y)⟫) = 0 :=
  SolenoidalCrossIncrement.integral_cross_increment_constant_eq_zero _
    (PeriodicRadialRiesz.continuous_tensor N) (PeriodicRadialRiesz.tensor_neg N)
    (PeriodicRadialRiesz.integral_tensor_eq_zero N) _
    (LocalSquaredGapGradient.continuous_fullCurlGradient u j)
    (integral_tensor_fullCurlGradient_eq_zero N u hu j) q

end Mettapedia.FluidDynamics.NavierStokes.LocalRadialSolenoidal
