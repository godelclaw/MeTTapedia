import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMInitialVelocityExamplesCore

/-!
# Heat-shear and transported heat-shear initial-velocity BKM examples
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section BKMContinuation

/-- The same BKM-side vacuity caveat holds for nontrivial heat-shear initial
data: on nonnegative slabs the clause is true because the finite-time witness
type is already empty there. -/
theorem ExplicitBKMContinuationClause_heatShearInitialVelocity
    {ν T : ℝ} {a k : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (heatShearInitialVelocity a k) T := by
  exact
    ExplicitBKMContinuationClause_of_not_nonempty_finiteTimeWitness
      (u₀ := heatShearInitialVelocity a k)
      (not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearInitialVelocity
        (ν := ν) (T := T) (a := a) (k := k) ha hk hT)

/-- The BKM continuation clause can therefore also be true on nontrivial
heat-shear data while the concrete regularity clause is false there. -/
theorem ExplicitBKMContinuationClause_heatShearInitialVelocity_without_regularity
    {ν T : ℝ} {a k : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (heatShearInitialVelocity a k) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν (heatShearInitialVelocity a k) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitBKMContinuationClause_heatShearInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) ha hk hT
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearInitialVelocity hν ha hk

/-- The repaired BKM continuation clause is also vacuous on nontrivial
heat-shear data because the repaired finite-energy hypothesis already fails. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_heatShearInitialVelocity
    {ν T : ℝ} {a k : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause ν (heatShearInitialVelocity a k) T := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearInitialVelocity a k)
      (not_finiteInitialKineticEnergy_heatShearInitialVelocity ha hk)

/-- The repaired BKM continuation clause can therefore also be true on
nontrivial heat-shear data while the concrete regularity clause is false
there. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_heatShearInitialVelocity_without_regularity
    {ν T : ℝ} {a k : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) (hk : k ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause ν (heatShearInitialVelocity a k) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν (heatShearInitialVelocity a k) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitFiniteEnergyBKMContinuationClause_heatShearInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) ha hk
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearInitialVelocity hν ha hk

/-- The damped sinusoidal heat-shear field with constant streamwise drift is
likewise an exact smooth incompressible NS candidate on every nonnegative slab
with the explicit constant BKM envelope `Ω(t) = |a * k|`; bounded kinetic
energy is still the only missing witness slot. -/
theorem heatShearStreamwiseDriftVelocityField_exhibits_BKMCandidate_except_boundedEnergy
    {ν T a k d : ℝ}
    (hd : d ≠ 0)
    (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearStreamwiseDriftInitialVelocity a k d) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T := by
  rcases heatShearStreamwiseDriftInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
      (ν := ν) (T := T) (a := a) (k := k) (d := d) hd hν hT with
    ⟨⟨u, p, B, hu, hp, hmom, hdiv, hinit, hω, hE⟩, _⟩
  have hBKM :
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
        integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) :=
    uniformVorticityBoundUpTo_implies_constantBKMEnvelope
      (u := u) (T := T) (B := B) hT hω
  exact ⟨u, p, B, hu, hp, hmom, hdiv, hinit, hBKM.1, hBKM.2, hE⟩

/-- Heat shear with constant streamwise drift exposes the same exact BKM-side
gap: there is an explicit smooth incompressible candidate with an integrable
constant vorticity envelope, but the finite-time witness type is still empty
because bounded kinetic energy fails on `ℝ^3`. -/
theorem heatShearStreamwiseDriftInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness
    {ν T a k d : ℝ}
    (hd : d ≠ 0)
    (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearStreamwiseDriftInitialVelocity a k d) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν (heatShearStreamwiseDriftInitialVelocity a k d) T) := by
  refine ⟨?_, ?_⟩
  · exact heatShearStreamwiseDriftVelocityField_exhibits_BKMCandidate_except_boundedEnergy
      (ν := ν) (T := T) (a := a) (k := k) (d := d) hd hν hT
  · exact not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearStreamwiseDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (d := d) hd hT

/-- The same BKM-side vacuity caveat holds for heat-shear initial data with
nonzero constant streamwise drift: on nonnegative slabs the clause is true
because the finite-time witness type is already empty there. -/
theorem ExplicitBKMContinuationClause_heatShearStreamwiseDriftInitialVelocity
    {ν T : ℝ} {a k d : ℝ}
    (hd : d ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (heatShearStreamwiseDriftInitialVelocity a k d) T := by
  exact
    ExplicitBKMContinuationClause_of_not_nonempty_finiteTimeWitness
      (u₀ := heatShearStreamwiseDriftInitialVelocity a k d)
      (not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearStreamwiseDriftInitialVelocity
        (ν := ν) (T := T) (a := a) (k := k) (d := d) hd hT)

/-- The BKM continuation clause can therefore also be true on heat-shear data
with nonzero constant streamwise drift while the concrete regularity clause is
false there. -/
theorem ExplicitBKMContinuationClause_heatShearStreamwiseDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a k d : ℝ}
    (hν : 0 < ν)
    (hd : d ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (heatShearStreamwiseDriftInitialVelocity a k d) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (heatShearStreamwiseDriftInitialVelocity a k d) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitBKMContinuationClause_heatShearStreamwiseDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (d := d) hd hT
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearStreamwiseDriftInitialVelocity
      hν hd

/-- The repaired BKM continuation clause is also vacuous on heat-shear data
with nonzero constant streamwise drift because the repaired finite-energy
hypothesis already fails. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_heatShearStreamwiseDriftInitialVelocity
    {ν T : ℝ} {a k d : ℝ}
    (hd : d ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause
      ν (heatShearStreamwiseDriftInitialVelocity a k d) T := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearStreamwiseDriftInitialVelocity a k d)
      (not_finiteInitialKineticEnergy_heatShearStreamwiseDriftInitialVelocity hd)

/-- The repaired BKM continuation clause can therefore also be true on
heat-shear data with nonzero constant streamwise drift while the concrete
regularity clause is false there. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_heatShearStreamwiseDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a k d : ℝ}
    (hν : 0 < ν)
    (hd : d ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause
        ν (heatShearStreamwiseDriftInitialVelocity a k d) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (heatShearStreamwiseDriftInitialVelocity a k d) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitFiniteEnergyBKMContinuationClause_heatShearStreamwiseDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (d := d) hd
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearStreamwiseDriftInitialVelocity
      hν hd

/-- The damped sinusoidal heat-shear field with constant vertical drift is
likewise an exact smooth incompressible NS candidate on every nonnegative slab
with the explicit constant BKM envelope `Ω(t) = |a * k|`; bounded kinetic
energy is still the only missing witness slot. -/
theorem heatShearVerticalDriftVelocityField_exhibits_BKMCandidate_except_boundedEnergy
    {ν T a k c : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearVerticalDriftInitialVelocity a k c) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T := by
  rcases heatShearVerticalDriftInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
      (ν := ν) (T := T) (a := a) (k := k) (c := c) ha hk hν hT with
    ⟨⟨u, p, B, hu, hp, hmom, hdiv, hinit, hω, hE⟩, _⟩
  have hBKM :
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
        integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) :=
    uniformVorticityBoundUpTo_implies_constantBKMEnvelope
      (u := u) (T := T) (B := B) hT hω
  exact ⟨u, p, B, hu, hp, hmom, hdiv, hinit, hBKM.1, hBKM.2, hE⟩

/-- Heat shear with constant vertical drift exposes the same exact BKM-side
gap: there is an explicit smooth incompressible candidate with an integrable
constant vorticity envelope, but the finite-time witness type is still empty
because bounded kinetic energy fails on `ℝ^3`. -/
theorem heatShearVerticalDriftInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness
    {ν T a k c : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearVerticalDriftInitialVelocity a k c) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν (heatShearVerticalDriftInitialVelocity a k c) T) := by
  refine ⟨?_, ?_⟩
  · exact heatShearVerticalDriftVelocityField_exhibits_BKMCandidate_except_boundedEnergy
      (ν := ν) (T := T) (a := a) (k := k) (c := c) ha hk hν hT
  · exact not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearVerticalDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (c := c) ha hk hT

/-- The same BKM-side vacuity caveat holds for nontrivial heat-shear initial
data with vertical drift: on nonnegative slabs the clause is true because the
finite-time witness type is already empty there. -/
theorem ExplicitBKMContinuationClause_heatShearVerticalDriftInitialVelocity
    {ν T : ℝ} {a k c : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (heatShearVerticalDriftInitialVelocity a k c) T := by
  exact
    ExplicitBKMContinuationClause_of_not_nonempty_finiteTimeWitness
      (u₀ := heatShearVerticalDriftInitialVelocity a k c)
      (not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearVerticalDriftInitialVelocity
        (ν := ν) (T := T) (a := a) (k := k) (c := c) ha hk hT)

/-- The BKM continuation clause can therefore also be true on nontrivial
heat-shear data with vertical drift while the concrete regularity clause is
false there. -/
theorem ExplicitBKMContinuationClause_heatShearVerticalDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a k c : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (heatShearVerticalDriftInitialVelocity a k c) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (heatShearVerticalDriftInitialVelocity a k c) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitBKMContinuationClause_heatShearVerticalDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (c := c) ha hk hT
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearVerticalDriftInitialVelocity
      hν ha hk

/-- The repaired BKM continuation clause is also vacuous on nontrivial
heat-shear data with vertical drift because the repaired finite-energy
hypothesis already fails. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_heatShearVerticalDriftInitialVelocity
    {ν T : ℝ} {a k c : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause
      ν (heatShearVerticalDriftInitialVelocity a k c) T := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearVerticalDriftInitialVelocity a k c)
      (not_finiteInitialKineticEnergy_heatShearVerticalDriftInitialVelocity ha hk)

/-- The repaired BKM continuation clause can therefore also be true on
nontrivial heat-shear data with vertical drift while the concrete regularity
clause is false there. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_heatShearVerticalDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a k c : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) (hk : k ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause
        ν (heatShearVerticalDriftInitialVelocity a k c) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (heatShearVerticalDriftInitialVelocity a k c) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitFiniteEnergyBKMContinuationClause_heatShearVerticalDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (c := c) ha hk
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearVerticalDriftInitialVelocity
      hν ha hk

/-- The damped sinusoidal heat-shear field with full constant drift is likewise
an exact smooth incompressible NS candidate on every nonnegative slab with the
explicit constant BKM envelope `Ω(t) = |a * k|`; bounded kinetic energy is
still the only missing witness slot. -/
theorem heatShearFullDriftVelocityField_exhibits_BKMCandidate_except_boundedEnergy
    {ν T a k d c : ℝ}
    (hd : d ≠ 0)
    (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearFullDriftInitialVelocity a k d c) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T := by
  rcases heatShearFullDriftInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
      (ν := ν) (T := T) (a := a) (k := k) (d := d) (c := c) hd hν hT with
    ⟨⟨u, p, B, hu, hp, hmom, hdiv, hinit, hω, hE⟩, _⟩
  have hBKM :
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
        integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) :=
    uniformVorticityBoundUpTo_implies_constantBKMEnvelope
      (u := u) (T := T) (B := B) hT hω
  exact ⟨u, p, B, hu, hp, hmom, hdiv, hinit, hBKM.1, hBKM.2, hE⟩

/-- Heat shear with full constant drift exposes the same exact BKM-side gap:
there is an explicit smooth incompressible candidate with an integrable
constant vorticity envelope, but the finite-time witness type is still empty
because bounded kinetic energy fails on `ℝ^3`. -/
theorem heatShearFullDriftInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness
    {ν T a k d c : ℝ}
    (hd : d ≠ 0)
    (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearFullDriftInitialVelocity a k d c) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν (heatShearFullDriftInitialVelocity a k d c) T) := by
  refine ⟨?_, ?_⟩
  · exact heatShearFullDriftVelocityField_exhibits_BKMCandidate_except_boundedEnergy
      (ν := ν) (T := T) (a := a) (k := k) (d := d) (c := c) hd hν hT
  · exact not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearFullDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (d := d) (c := c) hd hT

/-- The same BKM-side vacuity caveat holds for full-drift heat-shear initial
data with nonzero streamwise drift: on nonnegative slabs the clause is true
because the finite-time witness type is already empty there. -/
theorem ExplicitBKMContinuationClause_heatShearFullDriftInitialVelocity
    {ν T : ℝ} {a k d c : ℝ}
    (hd : d ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (heatShearFullDriftInitialVelocity a k d c) T := by
  exact
    ExplicitBKMContinuationClause_of_not_nonempty_finiteTimeWitness
      (u₀ := heatShearFullDriftInitialVelocity a k d c)
      (not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearFullDriftInitialVelocity
        (ν := ν) (T := T) (a := a) (k := k) (d := d) (c := c) hd hT)

/-- The BKM continuation clause can therefore also be true on full-drift
heat-shear data with nonzero streamwise drift while the concrete regularity
clause is false there. -/
theorem ExplicitBKMContinuationClause_heatShearFullDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a k d c : ℝ}
    (hν : 0 < ν)
    (hd : d ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (heatShearFullDriftInitialVelocity a k d c) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (heatShearFullDriftInitialVelocity a k d c) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitBKMContinuationClause_heatShearFullDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (d := d) (c := c) hd hT
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearFullDriftInitialVelocity
      hν hd

/-- The repaired BKM continuation clause is also vacuous on full-drift
heat-shear data with nonzero streamwise drift because the repaired finite-energy
hypothesis already fails. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_heatShearFullDriftInitialVelocity
    {ν T : ℝ} {a k d c : ℝ}
    (hd : d ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause
      ν (heatShearFullDriftInitialVelocity a k d c) T := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearFullDriftInitialVelocity a k d c)
      (not_finiteInitialKineticEnergy_heatShearFullDriftInitialVelocity hd)

/-- The repaired BKM continuation clause can therefore also be true on
full-drift heat-shear data with nonzero streamwise drift while the concrete
regularity clause is false there. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_heatShearFullDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a k d c : ℝ}
    (hν : 0 < ν)
    (hd : d ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause
        ν (heatShearFullDriftInitialVelocity a k d c) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (heatShearFullDriftInitialVelocity a k d c) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitFiniteEnergyBKMContinuationClause_heatShearFullDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (d := d) (c := c) hd
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearFullDriftInitialVelocity
      hν hd

/-- The transported heat-shear field is likewise an exact smooth incompressible
NS candidate on every nonnegative slab with the explicit constant BKM envelope
`Ω(t) = |a * k|`; bounded kinetic energy is still the only missing witness
slot. -/
theorem heatShearTransportVelocityField_exhibits_BKMCandidate_except_boundedEnergy
    {ν T a k b : ℝ}
    (hb : b ≠ 0)
    (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearTransportInitialVelocity a k b) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T := by
  rcases heatShearTransportInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
      (ν := ν) (T := T) (a := a) (k := k) (b := b) hb hν hT with
    ⟨⟨u, p, B, hu, hp, hmom, hdiv, hinit, hω, hE⟩, _⟩
  have hBKM :
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
        integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) :=
    uniformVorticityBoundUpTo_implies_constantBKMEnvelope
      (u := u) (T := T) (B := B) hT hω
  exact ⟨u, p, B, hu, hp, hmom, hdiv, hinit, hBKM.1, hBKM.2, hE⟩

/-- Transported heat shear exposes the same exact BKM-side gap: there is an
explicit smooth incompressible candidate with an integrable constant vorticity
envelope, but the finite-time witness type is still empty because bounded
kinetic energy fails on `ℝ^3`. -/
theorem heatShearTransportInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness
    {ν T a k b : ℝ}
    (hb : b ≠ 0)
    (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearTransportInitialVelocity a k b) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν (heatShearTransportInitialVelocity a k b) T) := by
  refine ⟨?_, ?_⟩
  · exact heatShearTransportVelocityField_exhibits_BKMCandidate_except_boundedEnergy
      (ν := ν) (T := T) (a := a) (k := k) (b := b) hb hν hT
  · exact not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearTransportInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (b := b) hb hT

/-- The same BKM-side vacuity caveat holds for transported heat-shear initial
data with nonzero transport speed: on nonnegative slabs the clause is true
because the finite-time witness type is already empty there. -/
theorem ExplicitBKMContinuationClause_heatShearTransportInitialVelocity
    {ν T : ℝ} {a k b : ℝ}
    (hb : b ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (heatShearTransportInitialVelocity a k b) T := by
  exact
    ExplicitBKMContinuationClause_of_not_nonempty_finiteTimeWitness
      (u₀ := heatShearTransportInitialVelocity a k b)
      (not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearTransportInitialVelocity
        (ν := ν) (T := T) (a := a) (k := k) (b := b) hb hT)

/-- The BKM continuation clause can therefore also be true on transported
heat-shear data with nonzero transport speed while the concrete regularity
clause is false there. -/
theorem ExplicitBKMContinuationClause_heatShearTransportInitialVelocity_without_regularity
    {ν T : ℝ} {a k b : ℝ}
    (hν : 0 < ν)
    (hb : b ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (heatShearTransportInitialVelocity a k b) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (heatShearTransportInitialVelocity a k b) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitBKMContinuationClause_heatShearTransportInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (b := b) hb hT
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearTransportInitialVelocity
      hν hb

/-- The repaired BKM continuation clause is also vacuous on transported
heat-shear data with nonzero transport speed because the repaired finite-energy
hypothesis already fails. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_heatShearTransportInitialVelocity
    {ν T : ℝ} {a k b : ℝ}
    (hb : b ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause
      ν (heatShearTransportInitialVelocity a k b) T := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearTransportInitialVelocity a k b)
      (not_finiteInitialKineticEnergy_heatShearTransportInitialVelocity hb)

/-- The repaired BKM continuation clause can therefore also be true on
transported heat-shear data with nonzero transport speed while the concrete
regularity clause is false there. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_heatShearTransportInitialVelocity_without_regularity
    {ν T : ℝ} {a k b : ℝ}
    (hν : 0 < ν)
    (hb : b ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause
        ν (heatShearTransportInitialVelocity a k b) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (heatShearTransportInitialVelocity a k b) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitFiniteEnergyBKMContinuationClause_heatShearTransportInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (b := b) hb
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearTransportInitialVelocity
      hν hb

/-- The transported full-drift heat-shear field is likewise an exact smooth
incompressible NS candidate on every nonnegative slab with the explicit
constant BKM envelope `Ω(t) = |a * k|`; bounded kinetic energy is still the
only missing witness slot. -/
theorem heatShearTransportFullDriftVelocityField_exhibits_BKMCandidate_except_boundedEnergy
    {ν T a k b d c : ℝ}
    (hb : b ≠ 0)
    (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearTransportFullDriftInitialVelocity a k b d c) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T := by
  rcases heatShearTransportFullDriftInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
      (ν := ν) (T := T) (a := a) (k := k) (b := b) (d := d) (c := c) hb hν hT with
    ⟨⟨u, p, B, hu, hp, hmom, hdiv, hinit, hω, hE⟩, _⟩
  have hBKM :
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
        integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) :=
    uniformVorticityBoundUpTo_implies_constantBKMEnvelope
      (u := u) (T := T) (B := B) hT hω
  exact ⟨u, p, B, hu, hp, hmom, hdiv, hinit, hBKM.1, hBKM.2, hE⟩

/-- Transported full-drift heat shear exposes the same exact BKM-side gap:
there is an explicit smooth incompressible candidate with an integrable
constant vorticity envelope, but the finite-time witness type is still empty
because bounded kinetic energy fails on `ℝ^3`. -/
theorem heatShearTransportFullDriftInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness
    {ν T a k b d c : ℝ}
    (hb : b ≠ 0)
    (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearTransportFullDriftInitialVelocity a k b d c) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν (heatShearTransportFullDriftInitialVelocity a k b d c) T) := by
  refine ⟨?_, ?_⟩
  · exact heatShearTransportFullDriftVelocityField_exhibits_BKMCandidate_except_boundedEnergy
      (ν := ν) (T := T) (a := a) (k := k) (b := b) (d := d) (c := c) hb hν hT
  · exact not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearTransportFullDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (b := b) (d := d) (c := c) hb hT

/-- The same BKM-side vacuity caveat holds for transported full-drift
heat-shear initial data with nonzero transport speed: on nonnegative slabs the
clause is true because the finite-time witness type is already empty there. -/
theorem ExplicitBKMContinuationClause_heatShearTransportFullDriftInitialVelocity
    {ν T : ℝ} {a k b d c : ℝ}
    (hb : b ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (heatShearTransportFullDriftInitialVelocity a k b d c) T := by
  exact
    ExplicitBKMContinuationClause_of_not_nonempty_finiteTimeWitness
      (u₀ := heatShearTransportFullDriftInitialVelocity a k b d c)
      (not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearTransportFullDriftInitialVelocity
        (ν := ν) (T := T) (a := a) (k := k) (b := b) (d := d) (c := c) hb hT)

/-- The BKM continuation clause can therefore also be true on transported
full-drift heat-shear data with nonzero transport speed while the concrete
regularity clause is false there. -/
theorem ExplicitBKMContinuationClause_heatShearTransportFullDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a k b d c : ℝ}
    (hν : 0 < ν)
    (hb : b ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (heatShearTransportFullDriftInitialVelocity a k b d c) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (heatShearTransportFullDriftInitialVelocity a k b d c) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitBKMContinuationClause_heatShearTransportFullDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (b := b) (d := d) (c := c) hb hT
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearTransportFullDriftInitialVelocity
      hν hb

/-- The repaired BKM continuation clause is also vacuous on transported
full-drift heat-shear data with nonzero transport speed because the repaired
finite-energy hypothesis already fails. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_heatShearTransportFullDriftInitialVelocity
    {ν T : ℝ} {a k b d c : ℝ}
    (hb : b ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause
      ν (heatShearTransportFullDriftInitialVelocity a k b d c) T := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearTransportFullDriftInitialVelocity a k b d c)
      (not_finiteInitialKineticEnergy_heatShearTransportFullDriftInitialVelocity hb)

/-- The repaired BKM continuation clause can therefore also be true on
transported full-drift heat-shear data with nonzero transport speed while the
concrete regularity clause is false there. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_heatShearTransportFullDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a k b d c : ℝ}
    (hν : 0 < ν)
    (hb : b ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause
        ν (heatShearTransportFullDriftInitialVelocity a k b d c) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (heatShearTransportFullDriftInitialVelocity a k b d c) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitFiniteEnergyBKMContinuationClause_heatShearTransportFullDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (b := b) (d := d) (c := c) hb
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearTransportFullDriftInitialVelocity
      hν hb

end BKMContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
