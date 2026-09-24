import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeInfiniteSpatialPressure
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.InfiniteKineticCancellation
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLowDiffusionBudget

/-!
# Parseval for the actual infinite Fourier reconstruction

Absolute summability identifies the continuous reconstruction with its
Fourier coefficients. Scalar Hilbert-space Parseval then gives the full
vector energy, without a receiver cutoff or a cardinality factor.
The curl corollary concerns the ordinary spatial derivative of the field.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.InfiniteFourierParseval

open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit
open PancakeInfiniteFourierDerivative PancakeInfiniteSpatialCurl PancakeInfiniteSpatialPressure
open PancakeFrequencyProjectorCommutator PancakeGalerkinKineticEnergy InfiniteConvectionEnergy
open InfiniteKineticCancellation PancakeCurlOutputTail PancakeIndexedFourierMoments
open PancakeDyadicDirectionEvolution PancakeTransverseEnergyFreezing

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem hasSum_norm_scalarFullFourierField_sq (a : Wavevector → ℂ)
    (ha : Summable (fun q ↦ ‖a q‖)) :
    HasSum (fun q ↦ ‖a q‖ ^ 2) (∫ x : T3, ‖fullFourierField id a x‖ ^ 2) := by
  let f := fullFourierField id a
  have h := UnitAddTorus.hasSum_sq_mFourierCoeff (f.toLp 2 volume ℂ)
  simp only [UnitAddTorus.mFourierCoeff_toLp, f,
    mFourierCoeff_scalarFullFourierField a ha] at h
  convert h using 1
  apply integral_congr_ae
  filter_upwards [f.coeFn_toAEEqFun volume] with x hx
  exact congrArg (fun z : ℂ ↦ ‖z‖ ^ 2) hx.symm

theorem fullFourierField_component_eq (u : FourierVelocity)
    (hu : Summable (fun q ↦ ‖u q‖)) (i : Fin 3) (x : T3) :
    fullFourierField id u x i = fullFourierField id (fun q ↦ u q i) x := by
  have hi : Summable (fun q ↦ ‖u q i‖) :=
    hu.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun q ↦ norm_le_pi_norm (u q) i)
  rw [fullFourierField_component id u hu, fullFourierField_apply id _ hi]
  rfl

/-- Full vector Parseval in the Euclidean coefficient norm. -/
theorem hasSum_coefficientEnergy (u : FourierVelocity)
    (hu : Summable (fun q ↦ ‖u q‖)) :
    HasSum (fun q ↦ coefficientEnergy (u q))
      (∫ x : T3, ‖coefficientVec (fullFourierField id u x)‖ ^ 2) := by
  have hs (i : Fin 3) : HasSum (fun q ↦ ‖u q i‖ ^ 2)
      (∫ x : T3, ‖fullFourierField id u x i‖ ^ 2) := by
    simp_rw [fullFourierField_component_eq u hu]
    exact hasSum_norm_scalarFullFourierField_sq _
      (hu.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun q ↦ norm_le_pi_norm (u q) i))
  have hi (i : Fin 3) : Integrable (fun x : T3 ↦ ‖fullFourierField id u x i‖ ^ 2) :=
    (((continuous_apply i).comp (fullFourierField id u).continuous).norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h := (hs 0).add (hs 1) |>.add (hs 2)
  have h01 : Integrable (fun x : T3 ↦
      ‖fullFourierField id u x 0‖ ^ 2 + ‖fullFourierField id u x 1‖ ^ 2) volume :=
    (hi 0).add (hi 1)
  simp only [norm_coefficientVec_sq, coefficientEnergy, Fin.sum_univ_three,
    Complex.normSq_eq_norm_sq]
  rw [integral_add h01 (hi 2), integral_add (hi 0) (hi 1)]
  exact h

theorem integral_norm_fullFourierField_sq (u : FourierVelocity)
    (hu : Summable (fun q ↦ ‖u q‖)) :
    (∫ x : T3, ‖coefficientVec (fullFourierField id u x)‖ ^ 2) = kineticEnergy u := by
  rw [kineticEnergy_eq_tsum_coefficientEnergy]
  exact (hasSum_coefficientEnergy u hu).tsum_eq.symm

theorem integral_norm_realPart_fullFourierField_sq_le (u : FourierVelocity)
    (hu : Summable (fun q ↦ ‖u q‖)) :
    (∫ x : T3, ‖complexRealPartEuclidean (fullFourierField id u x)‖ ^ 2) ≤ kineticEnergy u := by
  have hc : Continuous (fun x : T3 ↦ coefficientVec (fullFourierField id u x)) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin 3 ↦ ℂ)).comp (fullFourierField id u).continuous
  have hi : Integrable (fun x : T3 ↦ ‖coefficientVec (fullFourierField id u x)‖ ^ 2) volume :=
    (hc.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hm := integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun x : T3 ↦ sq_nonneg
      ‖complexRealPartEuclidean (fullFourierField id u x)‖))
    hi
    (Filter.Eventually.of_forall (fun x : T3 ↦
      PancakeLowDiffusionBudget.norm_realPart_sq_le (fullFourierField id u x)))
  rwa [integral_norm_fullFourierField_sq u hu] at hm

/-- No finite vorticity reconstruction is substituted for the actual curl. -/
theorem integral_norm_spatialCurl_sq_le (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) :
    (∫ x : T3, ‖complexRealPartEuclidean (spatialCurl (fullFourierField id u) x)‖ ^ 2) ≤
      kineticEnergy (fourierCurl u) := by
  rw [spatialCurl_velocity u hu]
  apply integral_norm_realPart_fullFourierField_sq_le
  exact summable_norm_curlCoefficients id u (by simpa only [indexedFirstMoment_id] using hu)

end Mettapedia.FluidDynamics.NavierStokes.InfiniteFourierParseval
