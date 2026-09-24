import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeInfinitePressureCoefficients

/-!
# The actual scalar pressure and its spatial gradient

The pressure is an absolutely convergent scalar Fourier field. Its ordinary
coordinate derivatives reconstruct the pressure-gradient coefficients.
Its Fourier integrals recover the defining coefficients, including zero mean.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeInfiniteSpatialPressure

open scoped BigOperators ComplexConjugate
open MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeInfiniteFourierDerivative PancakeInfiniteSpatialCurl PancakeInfinitePressureCoefficients
open PancakeIndexedFourierMoments PancakeCurlOutputTail PancakeCoefficientLimitEquation
open PancakeFourierTranslationCurve PancakePhysicalFourierDerivative PancakePeriodicOperatorKernel
open PancakePhysicalConvectionCoefficients PancakePhysicalFieldReconstruction
open PancakeInfiniteSpatialLaplacian PancakePeriodicVorticityEquation
open PancakeHaarTransportRate

local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def spatialPressure (u : FourierVelocity) : C(T3, ℂ) :=
  fullFourierField id (infinitePressureCoeff u)

def scalarCoordinateDerivative (f : T3 → ℂ) (j : Fin 3) (x : T3) : ℂ :=
  deriv (fun h : ℝ ↦ f (x + coordinateShift j h)) 0

def spatialGradient (f : T3 → ℂ) (x : T3) : VelocityCoefficient :=
  fun j ↦ scalarCoordinateDerivative f j x

theorem scalarCoordinateDerivative_fullFourierField (a : Wavevector → ℂ)
    (ha : Summable (fun q ↦ ‖a q‖)) (j : Fin 3)
    (hd : Summable (fun q ↦ ‖indexedDerivativeCoeff id j a q‖)) (x : T3) :
    scalarCoordinateDerivative (fullFourierField id a) j x =
      fullFourierField id (indexedDerivativeCoeff id j a) x := by
  simpa only [scalarCoordinateDerivative, coordinateShift_zero, add_zero] using
    (hasDerivAt_fullFourierField_shift id a ha j hd 0 x).deriv

theorem spatialPressure_hasDerivAt_shift (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (j : Fin 3) (h : ℝ) (x : T3) :
    HasDerivAt (fun t ↦ spatialPressure u (x + coordinateShift j t))
      (fullFourierField id (indexedDerivativeCoeff id j (infinitePressureCoeff u))
        (x + coordinateShift j h)) h :=
  hasDerivAt_fullFourierField_shift id _ (summable_norm_infinitePressure u hu) j
    (summable_norm_infinitePressureDerivative u hu j) h x

theorem spatialGradient_spatialPressure (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) :
    spatialGradient (spatialPressure u) =
      fullFourierField id (infinitePressureGradientCoeff u) := by
  funext x j
  simp only [spatialGradient, spatialPressure,
    scalarCoordinateDerivative_fullFourierField _ (summable_norm_infinitePressure u hu) j
      (summable_norm_infinitePressureDerivative u hu j) x,
    fullFourierField_apply id _ (summable_norm_infinitePressureDerivative u hu j),
    fullFourierField_component id _ (summable_norm_infinitePressureGradient u hu)]
  rfl

theorem continuous_spatialGradient_pressure (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) :
    Continuous (spatialGradient (spatialPressure u)) := by
  rw [spatialGradient_spatialPressure u hu]
  exact (fullFourierField id _).continuous

theorem scalarFullFourierField_conj (a : Wavevector → ℂ)
    (ha : Summable (fun q ↦ ‖a q‖)) (hr : ∀ q, a (-q) = conj (a q)) (x : T3) :
    conj (fullFourierField id a x) = fullFourierField id a x := by
  rw [fullFourierField_apply id a ha, Complex.conj_tsum]
  simp only [smul_eq_mul, id_eq]
  calc
    _ = ∑' q, UnitAddTorus.mFourier (-q) x * a (-q) := by
      apply tsum_congr
      intro q
      simp [UnitAddTorus.mFourier_neg, hr]
    _ = _ := (Equiv.neg Wavevector).tsum_eq (fun q ↦ UnitAddTorus.mFourier q x * a q)

theorem spatialPressure_reality (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u))
    (hr : ∀ k, u (-k) = PancakeBlockReality.coefficientConjugate (u k)) (x : T3) :
    conj (spatialPressure u x) = spatialPressure u x :=
  scalarFullFourierField_conj _ (summable_norm_infinitePressure u hu)
    (infinitePressureCoeff_conjugate u hr) x

theorem mFourierCoeff_scalarFullFourierField (a : Wavevector → ℂ)
    (ha : Summable (fun k ↦ ‖a k‖)) (q : Wavevector) :
    UnitAddTorus.mFourierCoeff (fullFourierField id a) q = a q := by
  have hint (k : Wavevector) :
      Integrable (fun x : T3 ↦ UnitAddTorus.mFourier (-q+k) x * a k) := by
    have hc : Continuous (fun x : T3 ↦ UnitAddTorus.mFourier (-q+k) x * a k) := by fun_prop
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hn (k : Wavevector) :
      (∫ x : T3, ‖UnitAddTorus.mFourier (-q+k) x * a k‖) = ‖a k‖ := by
    simp only [norm_mul, norm_character, one_mul, integral_const, probReal_univ, one_smul]
  have he := integral_tsum_of_summable_integral_norm hint (by simpa only [hn] using ha)
  have hchar (k : Wavevector) (x : T3) :
      UnitAddTorus.mFourier (-q) x * UnitAddTorus.mFourier k x =
        UnitAddTorus.mFourier (-q+k) x := UnitAddTorus.mFourier_add.symm
  unfold UnitAddTorus.mFourierCoeff
  simp_rw [fullFourierField_apply id a ha, smul_eq_mul, id_eq,
    ← tsum_mul_left, ← mul_assoc, hchar]
  rw [← he]
  simp_rw [integral_mul_const, integral_mFourier]
  simp [neg_add_eq_zero]

theorem mFourierCoeff_spatialPressure (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (q : Wavevector) :
    UnitAddTorus.mFourierCoeff (spatialPressure u) q = infinitePressureCoeff u q :=
  mFourierCoeff_scalarFullFourierField _ (summable_norm_infinitePressure u hu) q

theorem spatialPressure_mean_zero (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) :
    (∫ x : T3, spatialPressure u x) = 0 := by
  have h := mFourierCoeff_spatialPressure u hu 0
  simpa [UnitAddTorus.mFourierCoeff, infinitePressureCoeff_zero,
    UnitAddTorus.mFourier] using h

theorem continuous_spatialAdvection (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) :
    Continuous (spatialAdvection (fullFourierField id u)) := by
  have hu1 : Summable (indexedFirstMoment id u) := by
    simpa only [indexedFirstMoment_id] using summable_firstMoment_of_second u hu
  change Continuous (fun x ↦ ∑ j : Fin 3,
    fullFourierField id u x j • coordinateDerivative (fullFourierField id u) j x)
  simp only [coordinateDerivative_fullFourierField id u hu1]
  fun_prop

theorem fullFourierField_advection (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (hd : ∀ q, modeDot q (u q) = 0) :
    fullFourierField id (fun q ↦ unitTorusDerivativePhase • infiniteConvection u q) =
      spatialAdvection (fullFourierField id u) := by
  have hs : Summable (fun q ↦ ‖unitTorusDerivativePhase • infiniteConvection u q‖) := by
    simp only [norm_smul]
    exact ((summable_norm_infiniteConvection u hu).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
      (fun _ ↦ norm_coefficient_sup_le_euclidean _)).mul_left _
  rw [← torusFourierVelocity_spatialAdvection u hu hd]
  apply fullFourierField_torusFourierVelocity (spatialAdvection (fullFourierField id u))
    (fun i ↦ (continuous_apply i).comp (continuous_spatialAdvection u hu))
  simpa only [torusFourierVelocity_spatialAdvection u hu hd] using hs

end Mettapedia.FluidDynamics.NavierStokes.PancakeInfiniteSpatialPressure
