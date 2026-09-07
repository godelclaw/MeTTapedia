import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeBoundaryFreezingError
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakePhysicalWeightedTransport

/-!
# Alignment-depleted boundary field of the actual retained vorticity

Frozen operators are sampled from the actual filtered strain. The squared
norm of their complete exterior sum is bounded by the actual spectral
residual plus an explicit quadratic strain-freezing error. The exact
nonlinear pairing still includes freezing and coverage errors.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakePhysicalBoundaryDepletion

open MeasureTheory
open scoped RealInnerProductSpace
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeDyadicDirectionEvolution
open PancakeQuadraticFourierSupport PancakeQuadraticProjectionLocalization
open PancakeWeightedBoundaryAssembly PancakeWeightedBoundaryDepletion PancakeBoundaryFreezingError
open PancakeRegularizedDiffusion PancakeRegularizedMaterialRate PancakeSpectralDefectEvolution
open PancakeSpectralResidualDepletion PancakePhysicalWeightedTransport PancakePhysicalSpectralDefect
open PancakeFourierMaterialPaths PancakeFilteredStrainDynamics PancakeMaterialDiffusionBudget
open PancakeGalerkinKineticEnergy PancakeBlockReality
open PancakeRetainedProjectionDefect PancakeLocalizedProjectionBoundary
open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def physicalBoundaryField {ι : Type*} [Fintype ι] (c : ι → FourierCoeff (Fin 3))
    (center : ι → T3) (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity) : T3 → R3 :=
  assembledBoundaryField c (fun i ↦ physicalGapWeight chi modes u 0 (center i)) modes (fourierCurl u)

theorem continuous_physicalBoundaryField {ι : Type*} [Fintype ι] (c : ι → FourierCoeff (Fin 3))
    (center : ι → T3) (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity) :
    Continuous (physicalBoundaryField c center chi modes u) :=
  continuous_assembledBoundaryField c _ modes (fourierCurl u)

theorem integral_physicalBoundary_energy_depleted {ι : Type*} [Fintype ι]
    (c : ι → FourierCoeff (Fin 3)) (center : ι → T3) (chi : Wavevector → ℂ)
    (modes : Finset Wavevector) (u : FourierVelocity) (C : ℝ)
    (hs : ∀ q, -q ∈ modes ↔ q ∈ modes)
    (hC : ∀ x : T3, ∑ i : ι, quadraticWeight (c i) x ≤ C) :
    (∫ x : T3, ‖physicalBoundaryField c center chi modes u x‖ ^ 2) ≤
      C * ∫ x : T3, ∑ i : ι, quadraticWeight (c i) x *
        spectralWidth (spatialStrain modes (filteredVelocity chi u) (center i)) *
        topSpectralDefect (spatialStrain modes (filteredVelocity chi u) (center i)) (spatialVorticity modes u x) :=
  integral_gapBoundary_energy_le_width_defect c
    (fun i ↦ spatialStrain modes (filteredVelocity chi u) (center i)) modes (fourierCurl u) C hs hC

theorem integral_physicalBoundary_energy_unfrozen {ι : Type*} [Fintype ι]
    (c : ι → FourierCoeff (Fin 3)) (center : ι → T3) (chi : Wavevector → ℂ)
    (modes : Finset Wavevector) (u : FourierVelocity) (C : ℝ)
    (hs : ∀ q, -q ∈ modes ↔ q ∈ modes)
    (hC : ∀ x : T3, ∑ i : ι, quadraticWeight (c i) x ≤ C) :
    (∫ x : T3, ‖physicalBoundaryField c center chi modes u x‖ ^ 2) ≤
      2 * C ^ 2 * (∫ x : T3, ‖spectralResidual (spatialStrain modes (filteredVelocity chi u) x).1
        (topEigenvalue (spatialStrain modes (filteredVelocity chi u) x)) (spatialVorticity modes u x)‖ ^ 2) +
      8 * C * ∫ x : T3, ∑ i : ι, quadraticWeight (c i) x *
        ‖(spatialStrain modes (filteredVelocity chi u) (center i)).1 -
          (spatialStrain modes (filteredVelocity chi u) x).1‖ ^ 2 * ‖spatialVorticity modes u x‖ ^ 2 := by
  have h := integral_assembled_gapBoundary_energy_unfrozen c
    (fun i ↦ spatialStrain modes (filteredVelocity chi u) (center i))
    (spatialStrain modes (filteredVelocity chi u)) modes (fourierCurl u) C 0
    (continuous_strain _ _) hs hC
  simpa only [physicalBoundaryField, physicalGapWeight, spatialVorticity,
    regularizedGap_apply_eq, zero_smul, add_zero] using h

theorem integral_physicalBoundary_pairing_decomposition {ι : Type*} [Fintype ι]
    (c : ι → FourierCoeff (Fin 3)) (center : ι → T3) (chi : Wavevector → ℂ)
    (modes outputs : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, -q ∈ modes ↔ q ∈ modes) :
    (∫ x : T3, ⟪physicalGapWeight chi modes u 0 x (spatialVorticity modes u x),
      discardedNonlinearField modes outputs u x⟫) =
    (∫ x : T3, ∑ i : ι, quadraticWeight (c i) x *
      ⟪(physicalGapWeight chi modes u 0 x - physicalGapWeight chi modes u 0 (center i))
        (spatialVorticity modes u x), discardedNonlinearField modes outputs u x⟫) +
    (∫ x : T3, ⟪physicalBoundaryField c center chi modes u x, discardedNonlinearField modes outputs u x⟫) +
    ∫ x : T3, (1 - ∑ i : ι, quadraticWeight (c i) x) *
      ⟪physicalGapWeight chi modes u 0 x (spatialVorticity modes u x), discardedNonlinearField modes outputs u x⟫ := by
  have hi (i : ι) : Integrable (fun x : T3 ↦
      ⟪physicalGapWeight chi modes u 0 (center i) (quadraticBoundaryField (c i) modes (fourierCurl u) x),
        discardedNonlinearField modes outputs u x⟫) :=
    (((physicalGapWeight chi modes u 0 (center i)).continuous.comp
      (continuous_localizedBoundaryField _ _ _ _)).inner (continuous_discardedNonlinearField _ _ _)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have he : (∫ x : T3, ⟪physicalBoundaryField c center chi modes u x, discardedNonlinearField modes outputs u x⟫) =
      ∑ i : ι, ∫ x : T3,
        ⟪physicalGapWeight chi modes u 0 (center i) (quadraticBoundaryField (c i) modes (fourierCurl u) x),
          discardedNonlinearField modes outputs u x⟫ := by
    simp only [physicalBoundaryField, assembledBoundaryField, sum_inner]
    exact integral_finsetSum Finset.univ (fun i _ ↦ hi i)
  rw [he]
  exact integral_quadratic_freezing_decomposition c modes outputs u (physicalGapWeight chi modes u 0)
    (fun i ↦ physicalGapWeight chi modes u 0 (center i)) (continuous_physicalGapWeight _ _ _ _) hs

end Mettapedia.FluidDynamics.NavierStokes.PancakePhysicalBoundaryDepletion
