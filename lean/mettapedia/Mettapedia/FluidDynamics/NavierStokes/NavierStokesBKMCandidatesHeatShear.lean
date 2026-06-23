import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMCandidatesCore
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityBaseShearWitnessObstructions

/-!
# Heat-shear BKM candidates
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section BKMContinuation

/-- The damped sinusoidal heat-shear field is likewise an exact smooth
incompressible NS candidate on every nonnegative slab with the explicit
constant BKM envelope `Ω(t) = |a * k|`; bounded kinetic energy is still the
only missing witness slot. -/
theorem heatShearVelocityField_exhibits_BKMCandidate_except_boundedEnergy
    {ν T a k : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearInitialVelocity a k) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T := by
  rcases heatShearInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
      (ν := ν) (T := T) (a := a) (k := k) ha hk hν hT with
    ⟨⟨u, p, B, hu, hp, hmom, hdiv, hinit, hω, hE⟩, _⟩
  have hBKM :
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
        integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) :=
    uniformVorticityBoundUpTo_implies_constantBKMEnvelope
      (u := u) (T := T) (B := B) hT hω
  exact ⟨u, p, B, hu, hp, hmom, hdiv, hinit, hBKM.1, hBKM.2, hE⟩

/-- Heat shear exposes the same exact BKM-side gap: there is an explicit smooth
incompressible candidate with an integrable constant vorticity envelope, but
the finite-time witness type is still empty because bounded kinetic energy
fails on `ℝ^3`. -/
theorem heatShearInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness
    {ν T a k : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearInitialVelocity a k) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty (ExplicitFiniteTimeRegularityWitness ν (heatShearInitialVelocity a k) T) := by
  refine ⟨?_, ?_⟩
  · exact heatShearVelocityField_exhibits_BKMCandidate_except_boundedEnergy
      (ν := ν) (T := T) (a := a) (k := k) ha hk hν hT
  · exact not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) ha hk hT

end BKMContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
