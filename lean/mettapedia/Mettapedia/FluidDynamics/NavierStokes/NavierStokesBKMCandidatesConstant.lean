import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMCandidatesCore
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityConstantCandidates

/-!
# Constant-field BKM candidates
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section BKMContinuation

/-- A nonzero constant velocity field is an exact smooth incompressible
Navier--Stokes candidate on every nonnegative slab with the explicit zero BKM
envelope; the only missing finite-time witness slot is bounded kinetic energy
on `ℝ^3`. -/
theorem constantVelocityField_exhibits_BKMCandidate_except_boundedEnergy
    {ν T : ℝ} {c : NSSpace}
    (hc : c ≠ 0)
    (hT : 0 ≤ T) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (constantInitialVelocity c) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T := by
  exact
    exhibits_BKMCandidate_except_boundedEnergy_of_uniformCandidate
      (u₀ := constantInitialVelocity c) hT
      (constantVelocityField_exhibits_uniformCandidate_except_boundedEnergy
        (ν := ν) (T := T) (c := c) hc hT)

/-- The same nonzero constant-field BKM candidate remains valid after adding
any smooth slice-wise zero-spatial-gradient pressure gauge. The only missing
finite-time witness slot on `ℝ^3` is still bounded kinetic energy. -/
theorem constantVelocityField_exhibits_BKMCandidate_except_boundedEnergy_addPressureOfZeroSpatialGradient
    {ν T : ℝ} {c : NSSpace}
    (hc : c ≠ 0)
    (hT : 0 ≤ T)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (constantInitialVelocity c) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T := by
  exact
    exhibits_BKMCandidate_except_boundedEnergy_of_uniformCandidate
      (u₀ := constantInitialVelocity c) hT
      (constantVelocityField_exhibits_uniformCandidate_except_boundedEnergy_addPressureOfZeroSpatialGradient
        (ν := ν) (T := T) (c := c) hc hT q hq hq_zero)

/-- Constant initial data expose the same honest BKM-side gap as the shear
families: there is an explicit smooth incompressible candidate with an
integrable zero vorticity envelope, but the finite-time witness type is still
empty because bounded kinetic energy fails on `ℝ^3`. -/
theorem constantInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness
    {ν T : ℝ} {c : NSSpace}
    (hc : c ≠ 0)
    (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (constantInitialVelocity c) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty (ExplicitFiniteTimeRegularityWitness ν (constantInitialVelocity c) T) := by
  refine ⟨?_, ?_⟩
  · exact constantVelocityField_exhibits_BKMCandidate_except_boundedEnergy
      (ν := ν) (T := T) hc hT
  · exact not_nonempty_ExplicitFiniteTimeRegularityWitness_constantInitialVelocity
      (ν := ν) (T := T) hc hT

/-- The same honest constant-data BKM gap persists after adding any smooth
zero-spatial-gradient pressure gauge to the explicit constant-field candidate.
-/
theorem constantInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness_addPressureOfZeroSpatialGradient
    {ν T : ℝ} {c : NSSpace}
    (hc : c ≠ 0)
    (hT : 0 ≤ T)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (constantInitialVelocity c) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty (ExplicitFiniteTimeRegularityWitness ν (constantInitialVelocity c) T) := by
  refine ⟨?_, ?_⟩
  · exact
      constantVelocityField_exhibits_BKMCandidate_except_boundedEnergy_addPressureOfZeroSpatialGradient
        (ν := ν) (T := T) hc hT q hq hq_zero
  · exact not_nonempty_ExplicitFiniteTimeRegularityWitness_constantInitialVelocity
      (ν := ν) (T := T) hc hT

end BKMContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
