import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMCandidatesCore
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityBaseShearWitnessObstructions
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityLinearShearCandidates

/-!
# Affine-shear BKM candidates
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section BKMContinuation

/-- The steady linear shear field is an exact smooth incompressible NS candidate
on every nonnegative slab with an explicit constant BKM envelope; the only
missing finite-time witness slot is bounded kinetic energy. -/
theorem linearShearVelocityField_exhibits_BKMCandidate_except_boundedEnergy
    {ν T a : ℝ} (ha : a ≠ 0) (hT : 0 ≤ T) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearInitialVelocity a) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T := by
  rcases linearShearVelocityField_exhibits_uniformCandidate_except_boundedEnergy
      (ν := ν) (T := T) (a := a) ha hT with
    ⟨u, p, B, hu, hp, hmom, hdiv, hinit, hω, hE⟩
  have hBKM :
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
        integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) :=
    uniformVorticityBoundUpTo_implies_constantBKMEnvelope
      (u := u) (T := T) (B := B) hT hω
  exact ⟨u, p, B, hu, hp, hmom, hdiv, hinit, hBKM.1, hBKM.2, hE⟩

/-- The steady field `u(t,x) = (a * x₁, 0, b)` is likewise an exact smooth
incompressible NS candidate on every nonnegative slab with the explicit
constant BKM envelope `Ω(t) = |a|`; bounded kinetic energy is again the only
missing witness slot. -/
theorem linearShearVerticalDriftVelocityField_exhibits_BKMCandidate_except_boundedEnergy
    {ν T a b : ℝ} (ha : a ≠ 0) (hT : 0 ≤ T) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearVerticalDriftInitialVelocity a b) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T := by
  rcases linearShearVerticalDriftVelocityField_exhibits_uniformCandidate_except_boundedEnergy
      (ν := ν) (T := T) (a := a) (b := b) ha hT with
    ⟨u, p, B, hu, hp, hmom, hdiv, hinit, hω, hE⟩
  have hBKM :
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
        integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) :=
    uniformVorticityBoundUpTo_implies_constantBKMEnvelope
      (u := u) (T := T) (B := B) hT hω
  exact ⟨u, p, B, hu, hp, hmom, hdiv, hinit, hBKM.1, hBKM.2, hE⟩

/-- Linear shear exposes the exact BKM-side gap in the current witness surface:
there is an explicit smooth incompressible candidate with a constant integrable
vorticity envelope, but the concrete finite-time witness type is still empty
because bounded kinetic energy fails on `ℝ^3`. -/
theorem linearShearInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness
    {ν T a : ℝ} (ha : a ≠ 0) (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearInitialVelocity a) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty (ExplicitFiniteTimeRegularityWitness ν (linearShearInitialVelocity a) T) := by
  refine ⟨?_, ?_⟩
  · exact linearShearVelocityField_exhibits_BKMCandidate_except_boundedEnergy
      (ν := ν) (T := T) (a := a) ha hT
  · exact not_nonempty_ExplicitFiniteTimeRegularityWitness_linearShearInitialVelocity
      (ν := ν) (T := T) ha hT

/-- The same BKM-side gap persists for the affine shear datum
`x ↦ (a * x₁, 0, b)`: an explicit smooth incompressible candidate with constant
integrable vorticity envelope exists, but the finite-time witness type is still
empty because bounded kinetic energy fails on `ℝ^3`. -/
theorem linearShearVerticalDriftInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness
    {ν T a b : ℝ} (ha : a ≠ 0) (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearVerticalDriftInitialVelocity a b) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν (linearShearVerticalDriftInitialVelocity a b) T) := by
  refine ⟨?_, ?_⟩
  · exact linearShearVerticalDriftVelocityField_exhibits_BKMCandidate_except_boundedEnergy
      (ν := ν) (T := T) (a := a) (b := b) ha hT
  · exact
      not_nonempty_ExplicitFiniteTimeRegularityWitness_linearShearVerticalDriftInitialVelocity
        (ν := ν) (T := T) (a := a) (b := b) ha hT

/-- The steady field `u(t,x) = (a * x₁, b, 0)` is likewise an exact smooth
incompressible NS candidate on every nonnegative slab with the explicit
constant BKM envelope `Ω(t) = |a|`; bounded kinetic energy is again the only
missing witness slot.  In this branch the affine pressure field is essential. -/
theorem linearShearHorizontalDriftVelocityField_exhibits_BKMCandidate_except_boundedEnergy
    {ν T a b : ℝ} (ha : a ≠ 0) (hT : 0 ≤ T) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearHorizontalDriftInitialVelocity a b) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T := by
  rcases linearShearHorizontalDriftVelocityField_exhibits_uniformCandidate_except_boundedEnergy
      (ν := ν) (T := T) (a := a) (b := b) ha hT with
    ⟨u, p, B, hu, hp, hmom, hdiv, hinit, hω, hE⟩
  have hBKM :
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
        integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) :=
    uniformVorticityBoundUpTo_implies_constantBKMEnvelope
      (u := u) (T := T) (B := B) hT hω
  exact ⟨u, p, B, hu, hp, hmom, hdiv, hinit, hBKM.1, hBKM.2, hE⟩

/-- The same horizontal affine-shear BKM candidate remains valid after adding
any smooth slice-wise zero-spatial-gradient pressure gauge.  The bounded-energy
slot on `ℝ^3` is still the only missing witness component. -/
theorem linearShearHorizontalDriftVelocityField_exhibits_BKMCandidate_except_boundedEnergy_addPressureOfZeroSpatialGradient
    {ν T a b : ℝ} (ha : a ≠ 0) (hT : 0 ≤ T)
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
      MatchesInitialVelocity (linearShearHorizontalDriftInitialVelocity a b) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T := by
  exact
    exhibits_BKMCandidate_except_boundedEnergy_of_uniformCandidate
      (u₀ := linearShearHorizontalDriftInitialVelocity a b) hT
      (linearShearHorizontalDriftVelocityField_exhibits_uniformCandidate_except_boundedEnergy_addPressureOfZeroSpatialGradient
        (ν := ν) (T := T) (a := a) (b := b) ha hT q hq hq_zero)

/-- Time-only special case of the horizontal affine-shear pressure-gauge
transport on the explicit BKM candidate surface. -/
theorem linearShearHorizontalDriftVelocityField_exhibits_BKMCandidate_except_boundedEnergy_addTimeOnlyPressure
    {ν T a b : ℝ} (ha : a ≠ 0) (hT : 0 ≤ T)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearHorizontalDriftInitialVelocity a b) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T := by
  exact
    linearShearHorizontalDriftVelocityField_exhibits_BKMCandidate_except_boundedEnergy_addPressureOfZeroSpatialGradient
      (ν := ν) (T := T) (a := a) (b := b) ha hT
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)

/-- The same BKM-side gap persists for the affine shear datum
`x ↦ (a * x₁, b, 0)`: an explicit smooth incompressible candidate with constant
integrable vorticity envelope exists, but the finite-time witness type is still
empty because bounded kinetic energy fails on `ℝ^3`. -/
theorem linearShearHorizontalDriftInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness
    {ν T a b : ℝ} (ha : a ≠ 0) (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearHorizontalDriftInitialVelocity a b) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν (linearShearHorizontalDriftInitialVelocity a b) T) := by
  refine ⟨?_, ?_⟩
  · exact linearShearHorizontalDriftVelocityField_exhibits_BKMCandidate_except_boundedEnergy
      (ν := ν) (T := T) (a := a) (b := b) ha hT
  · exact
      not_nonempty_ExplicitFiniteTimeRegularityWitness_linearShearHorizontalDriftInitialVelocity
        (ν := ν) (T := T) (a := a) (b := b) ha hT

/-- The same horizontal affine-shear BKM gap persists after adding any smooth
slice-wise zero-spatial-gradient pressure gauge to the explicit slab
candidate. -/
theorem linearShearHorizontalDriftInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness_addPressureOfZeroSpatialGradient
    {ν T a b : ℝ} (ha : a ≠ 0) (hT : 0 ≤ T)
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
      MatchesInitialVelocity (linearShearHorizontalDriftInitialVelocity a b) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν (linearShearHorizontalDriftInitialVelocity a b) T) := by
  refine ⟨?_, ?_⟩
  · exact
      linearShearHorizontalDriftVelocityField_exhibits_BKMCandidate_except_boundedEnergy_addPressureOfZeroSpatialGradient
        (ν := ν) (T := T) (a := a) (b := b) ha hT q hq hq_zero
  · exact
      not_nonempty_ExplicitFiniteTimeRegularityWitness_linearShearHorizontalDriftInitialVelocity
        (ν := ν) (T := T) (a := a) (b := b) ha hT

/-- Time-only special case of the horizontal affine-shear pressure-gauge gap on
the explicit BKM continuation surface. -/
theorem linearShearHorizontalDriftInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness_addTimeOnlyPressure
    {ν T a b : ℝ} (ha : a ≠ 0) (hT : 0 ≤ T)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearHorizontalDriftInitialVelocity a b) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν (linearShearHorizontalDriftInitialVelocity a b) T) := by
  exact
    linearShearHorizontalDriftInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness_addPressureOfZeroSpatialGradient
      (ν := ν) (T := T) (a := a) (b := b) ha hT
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)

/-- The steady field `u(t,x) = (a * x₁, b, c)` is likewise an exact smooth
incompressible NS candidate on every nonnegative slab with the explicit
constant BKM envelope `Ω(t) = |a|`; bounded kinetic energy is again the only
missing witness slot.  The same affine pressure as in the horizontal-drift
branch remains sufficient. -/
theorem linearShearFullDriftVelocityField_exhibits_BKMCandidate_except_boundedEnergy
    {ν T a b c : ℝ} (ha : a ≠ 0) (hT : 0 ≤ T) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearFullDriftInitialVelocity a b c) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T := by
  rcases linearShearFullDriftVelocityField_exhibits_uniformCandidate_except_boundedEnergy
      (ν := ν) (T := T) (a := a) (b := b) (c := c) ha hT with
    ⟨u, p, B, hu, hp, hmom, hdiv, hinit, hω, hE⟩
  have hBKM :
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
        integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) :=
    uniformVorticityBoundUpTo_implies_constantBKMEnvelope
      (u := u) (T := T) (B := B) hT hω
  exact ⟨u, p, B, hu, hp, hmom, hdiv, hinit, hBKM.1, hBKM.2, hE⟩

/-- The same BKM-side gap persists for the affine shear datum
`x ↦ (a * x₁, b, c)`: an explicit smooth incompressible candidate with constant
integrable vorticity envelope exists, but the finite-time witness type is still
empty because bounded kinetic energy fails on `ℝ^3`. -/
theorem linearShearFullDriftInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness
    {ν T a b c : ℝ} (ha : a ≠ 0) (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearFullDriftInitialVelocity a b c) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν (linearShearFullDriftInitialVelocity a b c) T) := by
  refine ⟨?_, ?_⟩
  · exact linearShearFullDriftVelocityField_exhibits_BKMCandidate_except_boundedEnergy
      (ν := ν) (T := T) (a := a) (b := b) (c := c) ha hT
  · exact
      not_nonempty_ExplicitFiniteTimeRegularityWitness_linearShearFullDriftInitialVelocity
        (ν := ν) (T := T) (a := a) (b := b) (c := c) ha hT

end BKMContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
