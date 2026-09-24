import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeCompactJetEnvelope
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeFullAnalyticNonlinearity

/-!
# Reconstruction of the original physical field and its nonlinearity

The coefficients are taken from the input field by the actual Fourier
integral. Summability reconstructs that same field, and reality of the
input gives coefficient conjugacy. The full nonlinear identity therefore
acts on the original physical field, not only a field defined by a series.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakePhysicalFieldReconstruction

open scoped ComplexConjugate
open MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeArbitraryDataBlocks PancakeBlockReality
open PancakeCurlOutputTail PancakeIndexedFourierMoments PancakeInfiniteFourierDerivative
open PancakeInfiniteSpatialCurl PancakeInfiniteRealCurl PancakeFullAnalyticNonlinearity
open PancakeFullNonlinearConsistency PancakeDyadicDirectionEvolution

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem fullFourierField_torusFourierVelocity (f : T3 → VelocityCoefficient)
    (hc : ∀ i, Continuous (fun x ↦ f x i))
    (hs : Summable (fun k ↦ ‖torusFourierVelocity f k‖)) :
    fullFourierField id (torusFourierVelocity f) = f := by
  funext x i
  rw [fullFourierField_component id _ hs]
  have hi : Summable (UnitAddTorus.mFourierCoeff (fun x ↦ f x i)) :=
    Pi.summable.mp hs.of_norm i
  have h := UnitAddTorus.hasSum_mFourier_series_apply_of_summable
    (f := (⟨fun x ↦ f x i, hc i⟩ : C(T3, ℂ))) hi x
  simpa only [ContinuousMap.coe_mk, smul_eq_mul, torusFourierVelocity, id_eq, mul_comm] using h.tsum_eq

theorem torusFourierVelocity_conjugate (f : T3 → VelocityCoefficient)
    (hr : ∀ x i, conj (f x i) = f x i) (k : Wavevector) :
    torusFourierVelocity f (-k) = coefficientConjugate (torusFourierVelocity f k) := by
  funext i
  simp only [torusFourierVelocity, coefficientConjugate, UnitAddTorus.mFourierCoeff, smul_eq_mul]
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  simp [map_mul, UnitAddTorus.mFourier_neg, hr]

theorem realFullField_torusFourierVelocity (f : T3 → VelocityCoefficient)
    (hc : ∀ i, Continuous (fun x ↦ f x i))
    (hs : Summable (fourierMoment 2 (torusFourierVelocity f))) :
    realFullField (torusFourierVelocity f) = fun x ↦ complexRealPartEuclideanCLM (f x) := by
  have hnorm := summable_norm_coefficients id (torusFourierVelocity f)
    (by simpa only [indexedFirstMoment_id] using summable_firstMoment_of_second _ hs)
  unfold realFullField
  rw [fullFourierField_torusFourierVelocity f hc hnorm]

theorem fullCurlNonlinearity_torusFourierVelocity (f : T3 → VelocityCoefficient)
    (hc : ∀ i, Continuous (fun x ↦ f x i))
    (hs : Summable (fourierMoment 2 (torusFourierVelocity f)))
    (hr : ∀ x i, conj (f x i) = f x i) :
    fullCurlNonlinearity (torusFourierVelocity f) =
      realSpatialCurl (fun x ↦ realCross (complexRealPartEuclideanCLM (f x))
        (realSpatialCurl (fun y ↦ complexRealPartEuclideanCLM (f y)) x)) := by
  rw [← physicalFullNonlinearity_eq_fullCurlNonlinearity _ hs (torusFourierVelocity_conjugate f hr),
    physicalFullNonlinearity, realFullField_torusFourierVelocity f hc hs]

end Mettapedia.FluidDynamics.NavierStokes.PancakePhysicalFieldReconstruction
