import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeMeanMaterialBalance
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakePhysicalTransportCancellation

/-!
# The actual periodic alignment energy has a material time balance

For a supplied finite Fourier coefficient path, the actual frozen material
rate integrates to the change in spatial mean energy. Incompressibility
discharges the transport term, and local Lipschitz regularity includes
eigenvalue collisions. The retained velocity equation supplies the required
coefficient regularity in the final theorem; existence of that path is not
asserted here.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakePhysicalMeanBalance

open MeasureTheory
open PeriodicFourierTriad PancakePeriodicVorticityEquation PancakeGalerkinKineticEnergy
open PancakeMeasurableMaterialRate PancakePhysicalViscousSplit PancakeLocallyLipschitzEnergy
open PancakePhysicalTransportCancellation PancakeMeanMaterialBalance PancakeMaterialSpatialEstimate
open PancakeMappedFourierDiffusion PancakeMaterialChainRule
open PancakeFrequencyProjectorCommutator

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem continuous_spatialVelocity (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) : Continuous (spatialVelocity chi modes u) := by
  rw [← mappedField_velocity]
  exact continuous_mappedField _ _ _

def meanAlignmentEnergy (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) : ℝ :=
  ∫ x : T3, physicalRegularizedEnergy chi modes u delta x

theorem ae_hasDerivAt_meanAlignmentEnergy
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : ℝ → FourierVelocity) (delta : ℝ)
    (hc : ∀ q ∈ modes, ∀ i, ContDiff ℝ 1 (fun t ↦ u t q i))
    (hu : ∀ t, ∀ q ∈ modes, modeDot q (u t q) = 0) :
    ∀ᵐ t : ℝ, Integrable (frozenMaterialRate chi modes u delta t) ∧
      HasDerivAt (fun s ↦ meanAlignmentEnergy chi modes (u s) delta)
        (∫ x : T3, frozenMaterialRate chi modes u delta t x) t := by
  exact ae_hasDerivAt_mean_materialRate
    (fun t x ↦ physicalRegularizedEnergy chi modes (u t) delta x)
    (fun t x ↦ spatialVelocity chi modes (u t) x)
    (continuous_parametric_regularizedEnergy modes chi u delta (fun q hq i ↦ (hc q hq i).continuous))
    (fun t ↦ continuous_spatialVelocity chi modes (u t))
    (locallyLipschitz_real_energy chi modes u delta hc)
    (fun t j ↦ (contDiff_real_velocityComponent chi modes (u t) j).locallyLipschitz)
    (fun t ↦ Filter.Eventually.of_forall (coordinateDivergence_velocity_zero chi modes (u t) (hu t)))

theorem intervalIntegral_frozenMaterialRate_eq_energy
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : ℝ → FourierVelocity) (delta a b : ℝ)
    (hc : ∀ q ∈ modes, ∀ i, ContDiff ℝ 1 (fun t ↦ u t q i))
    (hu : ∀ t, ∀ q ∈ modes, modeDot q (u t q) = 0) :
    IntervalIntegrable (fun t ↦ ∫ x : T3, frozenMaterialRate chi modes u delta t x) volume a b ∧
      (∫ t in a..b, ∫ x : T3, frozenMaterialRate chi modes u delta t x) =
        meanAlignmentEnergy chi modes (u b) delta - meanAlignmentEnergy chi modes (u a) delta := by
  exact intervalIntegral_materialRate_eq
    (fun t x ↦ physicalRegularizedEnergy chi modes (u t) delta x)
    (fun t x ↦ spatialVelocity chi modes (u t) x)
    (continuous_parametric_regularizedEnergy modes chi u delta (fun q hq i ↦ (hc q hq i).continuous))
    (fun t ↦ continuous_spatialVelocity chi modes (u t))
    (locallyLipschitz_real_energy chi modes u delta hc)
    (fun t j ↦ (contDiff_real_velocityComponent chi modes (u t) j).locallyLipschitz)
    (fun t ↦ Filter.Eventually.of_forall (coordinateDivergence_velocity_zero chi modes (u t) (hu t))) a b

theorem intervalIntegral_frozenMaterialRate_eq_energy_of_velocityRHS
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : ℝ → FourierVelocity) (delta nu a b : ℝ)
    (hk : ∀ q ∈ modes, frequencyVec q ≠ 0)
    (hu : ∀ t, ∀ q ∈ modes, modeDot q (u t q) = 0)
    (hd : ∀ t, ∀ q ∈ modes, ∀ i,
      HasDerivAt (fun s ↦ u s q i) (velocityRHS modes (u t) nu q i) t) :
    IntervalIntegrable (fun t ↦ ∫ x : T3, frozenMaterialRate chi modes u delta t x) volume a b ∧
      (∫ t in a..b, ∫ x : T3, frozenMaterialRate chi modes u delta t x) =
        meanAlignmentEnergy chi modes (u b) delta - meanAlignmentEnergy chi modes (u a) delta :=
  intervalIntegral_frozenMaterialRate_eq_energy chi modes u delta a b
    (contDiff_coefficients_of_velocityRHS modes u nu hk hu hd) hu

end Mettapedia.FluidDynamics.NavierStokes.PancakePhysicalMeanBalance
