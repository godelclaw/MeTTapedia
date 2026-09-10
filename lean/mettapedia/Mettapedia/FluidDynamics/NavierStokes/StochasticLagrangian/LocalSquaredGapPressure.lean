import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SquaredGapTiltWeight
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalPressureAngularBudget
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSpaceTimeExtension
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSpatialBottomProjector

/-!
# Collision-safe Lipschitz geometry for physical pressure patches

The squared-ramp weight and its projector are computed from the actual
filtered strain and full vorticity. Their real spatial and local
space-time lifts are locally Lipschitz, with no positive-gap hypothesis.
The angular pressure theorem and the actual source split retain the
complementary transition/collision cost.

These are regularity and finite-increment estimates. They do not bound
the patch Fourier moments or the dynamical budget uniformly in scale.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalSquaredGapPressure

open scoped BigOperators
open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit
open PancakeFourierMaterialPaths PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeFilteredStrainDynamics PancakeSpectralFiniteDifference
open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakeAnisotropyDepletion SpectralGapTiltWeight SpectralDiffusionWeightLimit
open LocalLowDiffusionBudget LocalAlignmentForcing LocalJointSourceTilt
open PancakeQuadraticFourierSupport PancakeQuadraticProjectionLocalization
open FourierPressureTiltEnergy FourierPressureLocalization PressureTracePatchEnergy LocalPressureCommutator
open PancakeLocalInfiniteVelocity

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "X3" => Fin 3 → ℝ

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def localWeight (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3) : ℝ :=
  SquaredGapTiltWeight.weight gamma (spatialStrain modes (filteredVelocity chi u) x) (fullVorticity u x)

def localProjector (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3) : R3 →L[ℝ] R3 :=
  SquaredGapTiltWeight.weightedProjector gamma (spatialStrain modes (filteredVelocity chi u) x) (fullVorticity u x)

theorem continuous_localProjector (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) : Continuous (localProjector gamma chi modes u) :=
  SquaredGapTiltWeight.continuous_weightedProjector gamma hg _ _
    (PancakeMaterialDiffusionBudget.continuous_strain modes (filteredVelocity chi u))
    (continuous_fullVorticity u hu)

theorem locallyLipschitz_localProjector (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) :
    LocallyLipschitz (fun r : X3 ↦ localProjector gamma chi modes u (torusPoint r)) :=
  SquaredGapTiltWeight.locallyLipschitz_weightedProjector gamma hg _ _
    (LocalSpatialBottomProjector.contDiff_spatialStrain (n := 1) chi modes u).locallyLipschitz
    (LocalAlignmentTransport.locallyLipschitz_fullVorticity u hu)

/-- Clamping supplies only a regular extension of local data, not a
global solution of the PDE. On the interior interval it is the solution. -/
theorem locallyLipschitz_localProjector_spaceTime {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B) (hB : 0 ≤ B)
    (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)
    (g : Wavevector → ℝ) (hgn : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients t) q ≤ g q)
    (gamma : ℝ) (hg : 0 < gamma) (chi : Wavevector → ℂ) (modes : Finset Wavevector) :
    LocallyLipschitz (fun z : ℝ × X3 ↦ localProjector gamma chi modes
      (LocalSpaceTimeExtension.coefficients s a b hab z.1) (torusPoint z.2)) :=
  SquaredGapTiltWeight.locallyLipschitz_weightedProjector gamma hg _ _
    (LocalSpaceTimeExtension.locallyLipschitz_strain s a b hab hI hB chi modes)
    (LocalSpaceTimeExtension.locallyLipschitz_fullVorticity s a b hab hI g hgn hSum hu)

theorem exists_pressure_angular_budget (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (rho delta : ℝ) (hr : 0 < rho) (hd : 0 < delta) :
    let a := localWeight gamma chi modes u
    let e := fun x ↦ topVector (spatialStrain modes (filteredVelocity chi u) x)
    ∃ (centers : Finset T3) (c : ↑centers → FourierCoeff (Fin 3)),
      (∀ x, |(∑ i, quadraticWeight (c i) x) - a x| ≤ delta) ∧
      ∀ (outputs : Finset Wavevector), (∀ q, -q ∈ outputs ↔ q ∈ outputs) →
        ∀ eta : ℝ, 0 ≤ eta →
        (∫ x : T3, a x *
          ‖lineRemainder (e x) (filteredPressureOperator chi outputs u x (e x))‖ ^ 2) ≤
            4 * eta ^ 2 * (∫ x : T3, a x * realPressureTrace chi outputs u x ^ 2) +
              4 * (∑ i, tiltTailTraceEnergy (c i) chi outputs u (e i.1) eta) +
              4 * (∑ i, tiltCommutatorEnergy (c i) chi outputs u (e i.1)) +
              (32 * rho ^ 2 + 2 * delta + 4 * eta ^ 2 * delta) * hessianEnergy chi outputs u := by
  dsimp only
  have hS := PancakeMaterialDiffusionBudget.continuous_strain modes (filteredVelocity chi u)
  have hw := continuous_fullVorticity u hu
  have hP := SquaredGapTiltWeight.continuous_weightedProjector gamma hg _ _ hS hw
  simp_rw [SquaredGapTiltWeight.weightedProjector_eq gamma hg] at hP
  obtain ⟨centers, c, hmass, henergy⟩ :=
    WeightedPressureAngularBudget.exists_weighted_pressure_angular_budget
      (localWeight gamma chi modes u)
      (SquaredGapTiltWeight.continuous_weight gamma hg _ _ hS hw)
      (fun _ ↦ sq_nonneg _) _ (fun _ ↦ topVector_norm _) hP rho delta hr hd
  exact ⟨centers, c, hmass, fun outputs hs eta heta ↦ henergy chi outputs u hs eta heta⟩

theorem sourceExcess_le_weighted_jointTilt_add_collision (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector) (u : FourierVelocity) (x : T3) :
    let S := spatialStrain modes (filteredVelocity chi u) x
    LocalTiltSource.sourceExcess chi modes outputs u x ≤
      gapCutoff gamma (topGap S) ^ 2 *
        (max (2 * ‖nonviscousRemainder chi modes outputs u x‖ - topGap S ^ 2 / 8) 0 *
          limitingWeight S (fullVorticity u x)) +
      8 * localWeight gamma chi modes u x * ‖jointTilt chi modes outputs u x‖ ^ 2 +
      SquaredGapTiltWeight.collisionCost gamma S (nonviscousRemainder chi modes outputs u x)
        (fullVorticity u x) := by
  simpa only [LocalTiltSource.sourceExcess, localWeight, SpectralTiltExcess.tiltNorm_eq, jointTilt] using
    SquaredGapTiltWeight.excess_le_weighted_tilt_add_collision gamma hg
      (spatialStrain modes (filteredVelocity chi u) x)
      (nonviscousRemainder chi modes outputs u x) (fullVorticity u x)

end Mettapedia.FluidDynamics.NavierStokes.LocalSquaredGapPressure
