import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SpectralGapTiltWeight
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.WeightedFourierPressurePatch
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalTiltSource

/-!
# Weighted pressure localization for the physical filtered strain

The weight and expanding line are computed from the actual filtered
strain and full vorticity. The Fourier coefficients of pressure are those
of the same full velocity. Finite patches are constructed, not assumed;
there is no hypothesis that the top gap is everywhere positive.

The joint-source bound retains the collision remainder. Bounding the
weighted pressure patch energies over time and scale, together with the
other source channels, remains a separate dynamical problem.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalWeightedPressurePatch

open scoped BigOperators
open MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeFourierMaterialPaths PancakeHigherDerivativeMoments PancakeCurlOutputTail
open PancakeFilteredStrainDynamics LocalAlignmentForcing
open PancakeSpectralFiniteDifference PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakeAnisotropyDepletion SpectralGapTiltWeight
open PancakeQuadraticFourierSupport PancakeQuadraticProjectionLocalization
open FourierPressureTiltEnergy FourierPressurePatchEnergy LocalPressureCommutator
open LocalLowDiffusionBudget LocalJointSourceTilt

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def localTiltWeight (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3) : ℝ :=
  tiltWeight gamma (spatialStrain modes (filteredVelocity chi u) x) (fullVorticity u x)

theorem continuous_localTiltWeight (gamma : ℝ) (hg : 0 < gamma) (chi : Wavevector → ℂ)
    (modes : Finset Wavevector) (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) :
    Continuous (localTiltWeight gamma chi modes u) :=
  continuous_tiltWeight gamma hg _ _
    (PancakeMaterialDiffusionBudget.continuous_strain modes (filteredVelocity chi u))
    (continuous_fullVorticity u hu)

/-- Construct a single family that works for every negation-closed finite
pressure output set, using this velocity's actual vorticity/gap weight. -/
theorem exists_local_weighted_pressure_patches (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (rho delta : ℝ) (hr : 0 < rho) (hd : 0 < delta) :
    let e := fun x ↦ topVector (spatialStrain modes (filteredVelocity chi u) x)
    ∃ (centers : Finset T3) (c : ↑centers → FourierCoeff (Fin 3)),
      (∀ x, |(∑ i, quadraticWeight (c i) x) - localTiltWeight gamma chi modes u x| ≤ delta) ∧
      ∀ (outputs : Finset Wavevector), (∀ q, -q ∈ outputs ↔ q ∈ outputs) →
        (∫ x : T3, localTiltWeight gamma chi modes u x *
          ‖lineRemainder (e x) (filteredPressureOperator chi outputs u x (e x))‖ ^ 2) ≤
            2 * (∑ i, frozenPatchEnergy (c i) chi outputs u (e i.1)) +
              (32 * rho ^ 2 + 2 * delta) * hessianEnergy chi outputs u := by
  dsimp only
  have hS := PancakeMaterialDiffusionBudget.continuous_strain modes (filteredVelocity chi u)
  have hw := continuous_fullVorticity u hu
  obtain ⟨centers, c, hmass, henergy⟩ := WeightedFourierPressurePatch.exists_weighted_pressure_patches
    (localTiltWeight gamma chi modes u) (continuous_localTiltWeight gamma hg chi modes u hu)
    (fun _ ↦ tiltWeight_nonneg _ _ _) _ (fun _ ↦ topVector_norm _)
    (continuous_weighted_projector gamma hg _ _ hS hw) rho delta hr hd
  exact ⟨centers, c, hmass, fun outputs hs ↦ henergy chi outputs u hs⟩

theorem sourceExcess_le_weighted_jointTilt_add_collision (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector) (u : FourierVelocity) (x : T3) :
    let S := spatialStrain modes (filteredVelocity chi u) x
    LocalTiltSource.sourceExcess chi modes outputs u x ≤
      gapCutoff gamma (topGap S) *
        (max (2 * ‖nonviscousRemainder chi modes outputs u x‖ - topGap S ^ 2 / 8) 0 *
          SpectralDiffusionWeightLimit.limitingWeight S (fullVorticity u x)) +
      8 * localTiltWeight gamma chi modes u x * ‖jointTilt chi modes outputs u x‖ ^ 2 +
      collisionCost gamma S (nonviscousRemainder chi modes outputs u x) (fullVorticity u x) := by
  simpa only [LocalTiltSource.sourceExcess, localTiltWeight, SpectralTiltExcess.tiltNorm_eq, jointTilt] using
    excess_le_weighted_tilt_add_collision gamma hg (spatialStrain modes (filteredVelocity chi u) x)
      (nonviscousRemainder chi modes outputs u x) (fullVorticity u x)

theorem sourceExcess_le_capped_weighted_jointTilt_add_collision (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector) (u : FourierVelocity) (x : T3) :
    let S := spatialStrain modes (filteredVelocity chi u) x
    LocalTiltSource.sourceExcess chi modes outputs u x ≤
      gapCutoff gamma (topGap S) *
        (max (2 * ‖nonviscousRemainder chi modes outputs u x‖ - topGap S ^ 2 / 8) 0 *
          SpectralDiffusionWeightLimit.limitingWeight S (fullVorticity u x)) +
      min (2 * ‖nonviscousRemainder chi modes outputs u x‖ * ‖fullVorticity u x‖ ^ 2)
        (8 * localTiltWeight gamma chi modes u x * ‖jointTilt chi modes outputs u x‖ ^ 2) +
      collisionCost gamma S (nonviscousRemainder chi modes outputs u x) (fullVorticity u x) := by
  simpa only [LocalTiltSource.sourceExcess, localTiltWeight, SpectralTiltExcess.tiltNorm_eq, jointTilt] using
    excess_le_capped_weighted_tilt_add_collision gamma hg (spatialStrain modes (filteredVelocity chi u) x)
      (nonviscousRemainder chi modes outputs u x) (fullVorticity u x)

end Mettapedia.FluidDynamics.NavierStokes.LocalWeightedPressurePatch
