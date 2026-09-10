import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalAlignmentForcing

/-!
# Finite-support specialization of the full physical Fourier fields

The infinite-series definitions agree with finite reconstruction whenever
the input is finitely supported. In particular, the vorticity identity
identifies the ordinary spatial curl, not a separately prescribed receiver.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierFiniteSupport

open scoped BigOperators
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFourierTranslationCurve
open PancakeInfiniteFourierDerivative PancakeCurlOutputTail PancakeGalerkinKineticEnergy
open PancakeInfiniteSpatialCurl PancakePhysicalSpectralDefect LocalLowDiffusionBudget
open PancakeFrequencyProjectorCommutator PancakePeriodicComplexStretch
open PancakeFourierMaterialPaths PancakeFourierPressureStrain PancakeIndexedFourierMoments
open PancakeLocalVelocityGradientTime PancakeLocalGradientEquation
open LocalAlignmentForcing

local notation "T3" => UnitAddTorus (Fin 3)

theorem fullFourierField_eq_sum {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (modes : Finset Wavevector) (a : Wavevector → E)
    (hs : ∀ q, q ∉ modes → a q = 0) (x : T3) :
    fullFourierField id a x = ∑ q ∈ modes, UnitAddTorus.mFourier q x • a q := by
  have hz (q : Wavevector) (hq : q ∉ modes) : modeField q (a q) = 0 := by
    ext y
    simp [modeField, hs q hq]
  unfold fullFourierField
  have he : (∑' q, modeField q (a q)) = ∑ q ∈ modes, modeField q (a q) :=
    tsum_eq_sum hz
  change (∑' q, modeField q (a q)) x = _
  rw [he]
  simp [modeField]

theorem summable_fourierMoment (modes : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ modes → u q = 0) (s : ℕ) : Summable (fourierMoment s u) := by
  apply summable_of_ne_finset_zero (s := modes)
  intro q hq
  simp [fourierMoment, hs q hq, coefficientVec]

theorem fourierCurl_eq_zero (modes : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ modes → u q = 0) (q : Wavevector) (hq : q ∉ modes) :
    fourierCurl u q = 0 := by
  ext i
  fin_cases i <;> simp [fourierCurl, hs q hq, coefficientCross]

theorem fullVorticity_eq_spatialVorticity (modes : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ modes → u q = 0) (x : T3) :
    fullVorticity u x = spatialVorticity modes u x := by
  rw [fullVorticity, spatialCurl_velocity u (summable_fourierMoment modes u hs 1),
    fullFourierField_eq_sum modes (fourierCurl u) (fourierCurl_eq_zero modes u hs)]
  rfl

theorem coordinateDerivative_eq_sum (modes : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ modes → u q = 0) (j : Fin 3) (x : T3) :
    coordinateDerivative (fullFourierField id u) j x =
      ∑ q ∈ modes, UnitAddTorus.mFourier q x • indexedDerivativeCoeff id j u q := by
  have hm : Summable (indexedFirstMoment id u) := by
    simpa only [indexedFirstMoment_id] using summable_fourierMoment modes u hs 1
  rw [coordinateDerivative_fullFourierField id u hm j x]
  exact fullFourierField_eq_sum modes _ (fun q hq ↦ by
    simp [indexedDerivativeCoeff, hs q hq]) x

theorem fullStrainOperator_eq_spatialStrain (modes : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ modes → u q = 0) (x : T3) :
    fullStrainOperator u x = (spatialStrain modes u x).1 := by
  apply congrArg realMatrixOperator
  ext i j
  change (1 / 2 : ℂ) *
    (coordinateDerivative (fullFourierField id u) j x i +
      coordinateDerivative (fullFourierField id u) i x j) = _
  rw [coordinateDerivative_eq_sum modes u hs j, coordinateDerivative_eq_sum modes u hs i]
  simp only [matrixReconstruction_apply, strainCoeff, gradientCoeff,
    Finset.sum_apply, Pi.smul_apply, indexedDerivativeCoeff, id_eq,
    Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul,
    ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  ring

end Mettapedia.FluidDynamics.NavierStokes.FourierFiniteSupport
