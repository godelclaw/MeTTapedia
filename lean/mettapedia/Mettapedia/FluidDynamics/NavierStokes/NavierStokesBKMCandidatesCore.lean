import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMConcreteEnvelopes

/-!
# Uniform-candidate to BKM-candidate repackaging
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section BKMContinuation

/-- Any explicit slab candidate with a uniform-vorticity bound and missing only
the bounded-energy slot can be repackaged as a BKM candidate by choosing the
constant envelope `Ω(t) = B`. -/
theorem exhibits_BKMCandidate_except_boundedEnergy_of_uniformCandidate
    {ν T : ℝ} {u₀ : NSInitialVelocity}
    (hT : 0 ≤ T)
    (h :
      ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
        smoothSpaceTimeVelocity u ∧
        smoothSpaceTimePressure p ∧
        (∀ t x, 0 ≤ t → t ≤ T →
          timeVelocityDerivative u t x + spatialConvection u t x +
              spatialPressureGradient p t x =
            ν • spatialLaplacian u t x) ∧
        (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
        MatchesInitialVelocity u₀ u ∧
        uniformVorticityBoundUpTo u T B ∧
        ¬ boundedKineticEnergyUpTo u T) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x +
            spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity u₀ u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T := by
  rcases h with ⟨u, p, B, hu, hp, hmom, hdiv, hinit, hω, hE⟩
  have hBKM :
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
        integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) :=
    uniformVorticityBoundUpTo_implies_constantBKMEnvelope
      (u := u) (T := T) (B := B) hT hω
  exact ⟨u, p, B, hu, hp, hmom, hdiv, hinit, hBKM.1, hBKM.2, hE⟩

end BKMContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
