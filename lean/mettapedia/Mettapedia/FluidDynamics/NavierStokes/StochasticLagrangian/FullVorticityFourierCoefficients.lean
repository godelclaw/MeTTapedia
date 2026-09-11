import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSpatialCoefficientRecovery
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalLowDiffusionBudget
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierPressureTraceSymbol
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeInfiniteRealCurl

/-!
# Fourier coefficients of the actual real vorticity

The first absolute velocity moment justifies the spatial curl series.
The original coefficient reality symmetry is used explicitly when
complexifying that real field; no reality claim is made for arbitrary
complex coefficient arrays.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FullVorticityFourierCoefficients

open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit
open PancakeFrequencyProjectorCommutator PancakeGalerkinKineticEnergy PancakeCurlOutputTail
open PancakeInfiniteFourierDerivative PancakeIndexedFourierMoments PancakeInfiniteSpatialCurl
open PancakeInfiniteRealCurl PancakeSpatialCoefficientRecovery PancakeBlockReality
open PancakeDyadicDirectionEvolution PancakeTransverseEnergyFreezing
open FourierPressureTraceSymbol LocalLowDiffusionBudget

local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)

local instance : CompleteSpace C3 := PiLp.completeSpace 2 (fun _ : Fin 3 ↦ ℂ)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem mFourierCoeff_coefficientVec (f : T3 → VelocityCoefficient) (hf : Continuous f)
    (k : Wavevector) :
    UnitAddTorus.mFourierCoeff (fun x ↦ coefficientVec (f x)) k =
      coefficientVec (fun i ↦ UnitAddTorus.mFourierCoeff (fun x ↦ f x i) k) := by
  have hc : Continuous (fun x ↦ UnitAddTorus.mFourier (-k) x • coefficientVec (f x)) := by
    unfold coefficientVec
    fun_prop
  have hi : Integrable (fun x ↦ UnitAddTorus.mFourier (-k) x • coefficientVec (f x)) :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  ext i
  exact ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 3 ↦ ℂ) i : C3 →L[ℂ] ℂ).integral_comp_comm hi).symm

theorem summable_norm_fourierCurl (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) :
    Summable (fun k ↦ ‖fourierCurl u k‖) :=
  summable_norm_curlCoefficients id u (by simpa only [indexedFirstMoment_id] using hu)

theorem complexify_fullVorticity (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k)) (x : T3) :
    complexifyVector (fullVorticity u x) = coefficientVec (fullFourierField id (fourierCurl u) x) := by
  unfold fullVorticity
  rw [spatialCurl_velocity u hu]
  ext i
  change (((fullFourierField id (fourierCurl u) x i).re : ℝ) : ℂ) = _
  exact Complex.ext (by rfl)
    (by simpa only [coefficientVec, PiLp.toLp_apply, Complex.ofReal_im] using (fullFourierField_im_zero (fourierCurl u)
      (summable_norm_fourierCurl u hu) (fourierCurl_real u hr) x i).symm)

theorem mFourierCoeff_fullVorticity (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k)) (k : Wavevector) :
    UnitAddTorus.mFourierCoeff (fun x ↦ complexifyVector (fullVorticity u x)) k =
      coefficientVec (fourierCurl u k) := by
  simp_rw [complexify_fullVorticity u hu hr]
  rw [mFourierCoeff_coefficientVec _ (fullFourierField id (fourierCurl u)).continuous]
  simp_rw [mFourierCoeff_fullFourierField_component (fourierCurl u) (summable_norm_fourierCurl u hu)]

end Mettapedia.FluidDynamics.NavierStokes.FullVorticityFourierCoefficients
