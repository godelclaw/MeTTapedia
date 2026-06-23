import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityHeatShearExactnessVertical

/-!
# Full Drift Heat-Shear Exactness

This module contains full constant-drift heat-shear exactness, derived base/vertical/streamwise iff surfaces, and uniform-vorticity clauses.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section UniformVorticityContinuation

/-- The damped sinusoidal heat-shear field with full constant drift is likewise
an honest exact candidate on the global explicit theorem surface; the only
missing slot is bounded kinetic energy on `ℝ^3`. -/
theorem heatShearFullDriftVelocityField_exhibits_concreteCandidate_except_boundedEnergy
    {ν a k d c : ℝ} (hd : d ≠ 0) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearFullDriftInitialVelocity a k d c) u ∧
      ¬ boundedKineticEnergy u := by
  refine ⟨heatShearFullDriftVelocityField ν a k d c, 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact smoothSpaceTimeVelocity_heatShearFullDriftVelocityField ν a k d c
  · simpa [smoothSpaceTimePressure, spaceTimePressureMap] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => (0 : ℝ)))
  · intro t x
    simpa using momentumEquation_heatShearFullDriftVelocityField_zeroPressure ν a k d c t x
  · intro t x
    simpa using spatialDivergence_heatShearFullDriftVelocityField ν a k d c t x
  · exact matchesInitialVelocity_heatShearFullDriftVelocityField ν a k d c
  · exact not_boundedKineticEnergy_heatShearFullDriftVelocityField
      (ν := ν) (a := a) (k := k) (d := d) (c := c) hd

/-- Heat shear with full constant drift therefore exhibits the same exact
mismatch on the global explicit theorem surface: an honest smooth PDE-side
candidate exists, but the explicit global-output proposition is still false
because bounded kinetic energy fails. -/
theorem heatShearFullDriftInitialVelocity_exhibits_concreteCandidate_without_globalOutput
    {ν a k d c : ℝ} (hd : d ≠ 0) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearFullDriftInitialVelocity a k d c) u ∧
      ¬ boundedKineticEnergy u) ∧
      ¬ ExplicitConcreteNavierStokesGlobalOutput ν
        (heatShearFullDriftInitialVelocity a k d c) := by
  refine ⟨?_, ?_⟩
  · exact heatShearFullDriftVelocityField_exhibits_concreteCandidate_except_boundedEnergy
      (ν := ν) (a := a) (k := k) (d := d) (c := c) hd
  · intro hOut
    rcases hOut with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
    exact
      not_boundedKineticEnergy_of_matchesInitialVelocity_heatShearFullDriftInitialVelocity
        (u := u) hd hinit hbd

/-- The fully explicit global-output surface is likewise impossible for
heat-shear initial data with full constant drift whenever the streamwise drift
is nonzero. -/
theorem not_ExplicitConcreteNavierStokesGlobalOutput_heatShearFullDriftInitialVelocity
    {ν : ℝ} {a k d c : ℝ}
    (hd : d ≠ 0) :
    ¬ ExplicitConcreteNavierStokesGlobalOutput ν
      (heatShearFullDriftInitialVelocity a k d c) := by
  intro hOut
  rcases hOut with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
  exact
    not_boundedKineticEnergy_of_matchesInitialVelocity_heatShearFullDriftInitialVelocity
      (u := u) hd hinit hbd

/-- The fully explicit global-output surface is exact on the full-drift
heat-shear family: it is inhabited precisely when both constant drifts vanish
and the oscillatory part degenerates. -/
theorem ExplicitConcreteNavierStokesGlobalOutput_heatShearFullDriftInitialVelocity_iff
    {ν : ℝ} {a k d c : ℝ} :
    ExplicitConcreteNavierStokesGlobalOutput ν
        (heatShearFullDriftInitialVelocity a k d c) ↔
      d = 0 ∧ c = 0 ∧ a * k = 0 := by
  constructor
  · intro hOut
    have hd : d = 0 := by
      by_contra hd
      exact not_ExplicitConcreteNavierStokesGlobalOutput_heatShearFullDriftInitialVelocity hd hOut
    subst hd
    have hak : a * k = 0 := by
      by_contra hak
      have ha : a ≠ 0 := by
        intro ha
        exact hak (by simp [ha])
      have hk : k ≠ 0 := by
        intro hk
        exact hak (by simp [hk])
      exact
        not_ExplicitConcreteNavierStokesGlobalOutput_heatShearVerticalDriftInitialVelocity ha hk
          (by
            simpa [heatShearFullDriftInitialVelocity_zero_streamwiseDrift]
              using hOut)
    have hc : c = 0 := by
      rcases mul_eq_zero.mp hak with ha | hk
      · have hconst :
            EuclideanSpace.single nsCoord2 c = (0 : NSSpace) := by
          exact
            (ExplicitConcreteNavierStokesGlobalOutput_constantInitialVelocity_iff
              (ν := ν) (c := EuclideanSpace.single nsCoord2 c)).1
              (by
                simpa [heatShearFullDriftInitialVelocity_zero_streamwiseDrift,
                  heatShearVerticalDriftInitialVelocity, constantInitialVelocity_add, ha,
                  heatShearInitialVelocity_zero_of_amplitude_zero]
                  using hOut)
        have hc' := congrArg (fun v : NSSpace => v nsCoord2) hconst
        simpa using hc'
      · have hconst :
            EuclideanSpace.single nsCoord2 c = (0 : NSSpace) := by
          exact
            (ExplicitConcreteNavierStokesGlobalOutput_constantInitialVelocity_iff
              (ν := ν) (c := EuclideanSpace.single nsCoord2 c)).1
              (by
                simpa [heatShearFullDriftInitialVelocity_zero_streamwiseDrift,
                  heatShearVerticalDriftInitialVelocity, constantInitialVelocity_add, hk,
                  heatShearInitialVelocity_zero_of_wavenumber_zero]
                  using hOut)
        have hc' := congrArg (fun v : NSSpace => v nsCoord2) hconst
        simpa using hc'
    exact ⟨rfl, hc, hak⟩
  · rintro ⟨rfl, rfl, hak⟩
    have hzero : EuclideanSpace.single nsCoord2 0 = (0 : NSSpace) := by
      ext i
      fin_cases i <;> simp [nsCoord2]
    rcases mul_eq_zero.mp hak with ha | hk
    · simpa [heatShearFullDriftInitialVelocity_zero_streamwiseDrift,
        heatShearVerticalDriftInitialVelocity, constantInitialVelocity_add, ha,
        heatShearInitialVelocity_zero_of_amplitude_zero] using
        ((ExplicitConcreteNavierStokesGlobalOutput_constantInitialVelocity_iff
          (ν := ν) (c := EuclideanSpace.single nsCoord2 0)).2 hzero)
    · simpa [heatShearFullDriftInitialVelocity_zero_streamwiseDrift,
        heatShearVerticalDriftInitialVelocity, constantInitialVelocity_add, hk,
        heatShearInitialVelocity_zero_of_wavenumber_zero] using
        ((ExplicitConcreteNavierStokesGlobalOutput_constantInitialVelocity_iff
          (ν := ν) (c := EuclideanSpace.single nsCoord2 0)).2 hzero)

/-- At positive viscosity, the explicit concrete regularity clause is therefore
also impossible for heat-shear initial data with full constant drift on `ℝ^3`
whenever the streamwise drift is nonzero. -/
theorem not_ExplicitConcreteNavierStokesRegularityClause_heatShearFullDriftInitialVelocity
    {ν : ℝ} {a k d c : ℝ}
    (hν : 0 < ν)
    (hd : d ≠ 0) :
    ¬ ExplicitConcreteNavierStokesRegularityClause ν
      (heatShearFullDriftInitialVelocity a k d c) := by
  intro hClause
  have hsmooth : smoothInitialVelocityData (heatShearFullDriftInitialVelocity a k d c) :=
    smoothInitialVelocityData_heatShearFullDriftInitialVelocity a k d c
  have hdiv : ∀ x, initialSpatialDivergence (heatShearFullDriftInitialVelocity a k d c) x = 0 := by
    intro x
    simpa using initialSpatialDivergence_heatShearFullDriftInitialVelocity a k d c x
  rcases hClause hν hsmooth hdiv with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
  exact
    not_ExplicitConcreteNavierStokesGlobalOutput_heatShearFullDriftInitialVelocity hd
      ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩

/-- At positive viscosity, the explicit concrete regularity clause is exact on
the full-drift heat-shear family. -/
theorem ExplicitConcreteNavierStokesRegularityClause_heatShearFullDriftInitialVelocity_iff
    {ν : ℝ} (hν : 0 < ν) {a k d c : ℝ} :
    ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearFullDriftInitialVelocity a k d c) ↔
      d = 0 ∧ c = 0 ∧ a * k = 0 := by
  constructor
  · intro hClause
    have hsmooth : smoothInitialVelocityData (heatShearFullDriftInitialVelocity a k d c) :=
      smoothInitialVelocityData_heatShearFullDriftInitialVelocity a k d c
    have hdiv : ∀ x, initialSpatialDivergence (heatShearFullDriftInitialVelocity a k d c) x = 0 := by
      intro x
      simpa using initialSpatialDivergence_heatShearFullDriftInitialVelocity a k d c x
    exact
      (ExplicitConcreteNavierStokesGlobalOutput_heatShearFullDriftInitialVelocity_iff
        (ν := ν) (a := a) (k := k) (d := d) (c := c)).1
        (hClause hν hsmooth hdiv)
  · intro hcond
    exact
      ExplicitConcreteNavierStokesGlobalOutput_implies_ExplicitConcreteNavierStokesRegularityClause
        ((ExplicitConcreteNavierStokesGlobalOutput_heatShearFullDriftInitialVelocity_iff
          (ν := ν) (a := a) (k := k) (d := d) (c := c)).2 hcond)

/-- The same witness-level obstruction applies to the full-drift heat-shear
datum on every nonnegative slab whenever the streamwise drift is nonzero. -/
theorem not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearFullDriftInitialVelocity
    {ν T : ℝ} {a k d c : ℝ}
    (hd : d ≠ 0)
    (hT : 0 ≤ T) :
    ¬ Nonempty
      (ExplicitFiniteTimeRegularityWitness ν (heatShearFullDriftInitialVelocity a k d c) T) := by
  exact
    not_nonempty_ExplicitFiniteTimeRegularityWitness_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearFullDriftInitialVelocity a k d c)
      (not_finiteInitialKineticEnergy_heatShearFullDriftInitialVelocity hd)
      hT

/-- On every nonnegative slab with nonnegative viscosity, the full-drift
heat-shear field is an exact smooth incompressible candidate with explicit slab
vorticity bound `|a * k|`; bounded kinetic energy is the only missing witness
slot. -/
theorem heatShearFullDriftVelocityField_exhibits_uniformCandidate_except_boundedEnergy
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
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T := by
  refine ⟨heatShearFullDriftVelocityField ν a k d c, 0, |a * k|, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact smoothSpaceTimeVelocity_heatShearFullDriftVelocityField ν a k d c
  · simpa [smoothSpaceTimePressure, spaceTimePressureMap] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => (0 : ℝ)))
  · intro t x ht0 htT
    simpa using momentumEquation_heatShearFullDriftVelocityField_zeroPressure ν a k d c t x
  · intro t x ht0 htT
    simpa using spatialDivergence_heatShearFullDriftVelocityField ν a k d c t x
  · exact matchesInitialVelocity_heatShearFullDriftVelocityField ν a k d c
  · exact uniformVorticityBoundUpTo_heatShearFullDriftVelocityField ν a k d c T hν
  · exact not_boundedKineticEnergyUpTo_heatShearFullDriftVelocityField
      (ν := ν) (a := a) (k := k) (d := d) (c := c) hd hT

/-- Heat shear with full constant drift exposes the same exact gap on the
explicit uniform-vorticity surface: there is an exact smooth incompressible
candidate with a uniform slab vorticity bound, but the finite-time witness
type is still empty because bounded kinetic energy fails on `ℝ^3`. -/
theorem heatShearFullDriftInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
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
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν (heatShearFullDriftInitialVelocity a k d c) T) := by
  refine ⟨?_, ?_⟩
  · exact heatShearFullDriftVelocityField_exhibits_uniformCandidate_except_boundedEnergy
      (ν := ν) (T := T) (a := a) (k := k) (d := d) (c := c) hd hν hT
  · exact not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearFullDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (d := d) (c := c) hd hT

/-- The repaired explicit regularity clause is likewise vacuous on full-drift
heat-shear data with nonzero streamwise drift because the repaired finite-energy
hypothesis already fails. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearFullDriftInitialVelocity
    {ν : ℝ} {a k d c : ℝ}
    (hd : d ≠ 0) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
      ν (heatShearFullDriftInitialVelocity a k d c) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearFullDriftInitialVelocity a k d c)
      (not_finiteInitialKineticEnergy_heatShearFullDriftInitialVelocity hd)

/-- The repaired explicit regularity clause can therefore also be true on
full-drift heat-shear data with nonzero streamwise drift while the unrepaired
concrete regularity clause is false there. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearFullDriftInitialVelocity_without_regularity
    {ν : ℝ} {a k d c : ℝ}
    (hν : 0 < ν)
    (hd : d ≠ 0) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
        ν (heatShearFullDriftInitialVelocity a k d c) ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (heatShearFullDriftInitialVelocity a k d c) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearFullDriftInitialVelocity
      (ν := ν) (a := a) (k := k) (d := d) (c := c) hd
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearFullDriftInitialVelocity
      hν hd

/-- The structured fully concrete clause also rejects full-drift heat-shear
initial data with nonzero streamwise drift. -/
theorem not_concreteNavierStokesGlobalRegularityClause_heatShearFullDriftInitialVelocity
    {ν : ℝ} {a k d c : ℝ}
    (hν : 0 < ν)
    (hd : d ≠ 0) :
    ¬ NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := heatShearFullDriftInitialVelocity a k d c
          smooth_initial := smoothInitialVelocityData_heatShearFullDriftInitialVelocity a k d c
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_heatShearFullDriftInitialVelocity a k d c x } := by
  intro hClause
  exact
    not_ExplicitConcreteNavierStokesGlobalOutput_heatShearFullDriftInitialVelocity hd
      ((concreteNavierStokesGlobalRegularityClause_iff
        (ν := ν) (u₀ := heatShearFullDriftInitialVelocity a k d c)
        hν
        (smoothInitialVelocityData_heatShearFullDriftInitialVelocity a k d c)
        (by
          intro x
          simpa using initialSpatialDivergence_heatShearFullDriftInitialVelocity a k d c x)).mp
        hClause)

/-- The structured fully concrete clause is exact on the full-drift heat-shear
family. -/
theorem concreteNavierStokesGlobalRegularityClause_heatShearFullDriftInitialVelocity_iff
    {ν : ℝ} (hν : 0 < ν) {a k d c : ℝ} :
    NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := heatShearFullDriftInitialVelocity a k d c
          smooth_initial := smoothInitialVelocityData_heatShearFullDriftInitialVelocity a k d c
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_heatShearFullDriftInitialVelocity a k d c x } ↔
      d = 0 ∧ c = 0 ∧ a * k = 0 := by
  constructor
  · intro hClause
    exact
      (concreteNavierStokesGlobalRegularityClause_iff
        (ν := ν) (u₀ := heatShearFullDriftInitialVelocity a k d c)
        hν
        (smoothInitialVelocityData_heatShearFullDriftInitialVelocity a k d c)
        (by
          intro x
          simpa using initialSpatialDivergence_heatShearFullDriftInitialVelocity a k d c x)).mp
          hClause
        |> (ExplicitConcreteNavierStokesGlobalOutput_heatShearFullDriftInitialVelocity_iff
              (ν := ν) (a := a) (k := k) (d := d) (c := c)).1
  · intro hcond
    exact
      ExplicitConcreteNavierStokesGlobalOutput_implies_concreteNavierStokesGlobalRegularityClause
        hν
        (smoothInitialVelocityData_heatShearFullDriftInitialVelocity a k d c)
        (by
          intro x
          simpa using initialSpatialDivergence_heatShearFullDriftInitialVelocity a k d c x)
        ((ExplicitConcreteNavierStokesGlobalOutput_heatShearFullDriftInitialVelocity_iff
          (ν := ν) (a := a) (k := k) (d := d) (c := c)).2 hcond)

/-- The fully explicit global-output surface is exact on the vertical-drift
heat-shear family. -/
theorem ExplicitConcreteNavierStokesGlobalOutput_heatShearInitialVelocity_iff
    {ν : ℝ} {a k : ℝ} :
    ExplicitConcreteNavierStokesGlobalOutput ν
        (heatShearInitialVelocity a k) ↔
      a * k = 0 := by
  simpa [heatShearFullDriftInitialVelocity_zero_drifts] using
    (ExplicitConcreteNavierStokesGlobalOutput_heatShearFullDriftInitialVelocity_iff
      (ν := ν) (a := a) (k := k) (d := 0) (c := 0))

/-- At positive viscosity, the explicit concrete regularity clause is exact on
the base heat-shear family. -/
theorem ExplicitConcreteNavierStokesRegularityClause_heatShearInitialVelocity_iff
    {ν : ℝ} (hν : 0 < ν) {a k : ℝ} :
    ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearInitialVelocity a k) ↔
      a * k = 0 := by
  simpa [heatShearFullDriftInitialVelocity_zero_drifts] using
    (ExplicitConcreteNavierStokesRegularityClause_heatShearFullDriftInitialVelocity_iff
      (ν := ν) hν (a := a) (k := k) (d := 0) (c := 0))

/-- The structured fully concrete clause is exact on the base heat-shear
family. -/
theorem concreteNavierStokesGlobalRegularityClause_heatShearInitialVelocity_iff
    {ν : ℝ} (hν : 0 < ν) {a k : ℝ} :
    NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := heatShearInitialVelocity a k
          smooth_initial := smoothInitialVelocityData_heatShearInitialVelocity a k
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_heatShearInitialVelocity a k x } ↔
      a * k = 0 := by
  constructor
  · intro hClause
    exact
      (concreteNavierStokesGlobalRegularityClause_iff
        (ν := ν) (u₀ := heatShearInitialVelocity a k)
        hν
        (smoothInitialVelocityData_heatShearInitialVelocity a k)
        (by
          intro x
          simpa using initialSpatialDivergence_heatShearInitialVelocity a k x)).mp
          hClause
        |> (ExplicitConcreteNavierStokesGlobalOutput_heatShearInitialVelocity_iff
              (ν := ν) (a := a) (k := k)).1
  · intro hcond
    exact
      ExplicitConcreteNavierStokesGlobalOutput_implies_concreteNavierStokesGlobalRegularityClause
        hν
        (smoothInitialVelocityData_heatShearInitialVelocity a k)
        (by
          intro x
          simpa using initialSpatialDivergence_heatShearInitialVelocity a k x)
        ((ExplicitConcreteNavierStokesGlobalOutput_heatShearInitialVelocity_iff
          (ν := ν) (a := a) (k := k)).2 hcond)

/-- The fully explicit global-output surface is exact on the vertical-drift
heat-shear family. -/
theorem ExplicitConcreteNavierStokesGlobalOutput_heatShearVerticalDriftInitialVelocity_iff
    {ν : ℝ} {a k c : ℝ} :
    ExplicitConcreteNavierStokesGlobalOutput ν
        (heatShearVerticalDriftInitialVelocity a k c) ↔
      c = 0 ∧ a * k = 0 := by
  simpa [heatShearFullDriftInitialVelocity_zero_streamwiseDrift] using
    (ExplicitConcreteNavierStokesGlobalOutput_heatShearFullDriftInitialVelocity_iff
      (ν := ν) (a := a) (k := k) (d := 0) (c := c))

/-- At positive viscosity, the explicit concrete regularity clause is exact on
the vertical-drift heat-shear family. -/
theorem ExplicitConcreteNavierStokesRegularityClause_heatShearVerticalDriftInitialVelocity_iff
    {ν : ℝ} (hν : 0 < ν) {a k c : ℝ} :
    ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearVerticalDriftInitialVelocity a k c) ↔
      c = 0 ∧ a * k = 0 := by
  simpa [heatShearFullDriftInitialVelocity_zero_streamwiseDrift] using
    (ExplicitConcreteNavierStokesRegularityClause_heatShearFullDriftInitialVelocity_iff
      (ν := ν) hν (a := a) (k := k) (d := 0) (c := c))

/-- The fully explicit global-output surface is exact on the streamwise-drift
heat-shear family. -/
theorem ExplicitConcreteNavierStokesGlobalOutput_heatShearStreamwiseDriftInitialVelocity_iff
    {ν : ℝ} {a k d : ℝ} :
    ExplicitConcreteNavierStokesGlobalOutput ν
        (heatShearStreamwiseDriftInitialVelocity a k d) ↔
      d = 0 ∧ a * k = 0 := by
  simpa [heatShearFullDriftInitialVelocity_zero_verticalDrift] using
    (ExplicitConcreteNavierStokesGlobalOutput_heatShearFullDriftInitialVelocity_iff
      (ν := ν) (a := a) (k := k) (d := d) (c := 0))

/-- At positive viscosity, the explicit concrete regularity clause is exact on
the streamwise-drift heat-shear family. -/
theorem ExplicitConcreteNavierStokesRegularityClause_heatShearStreamwiseDriftInitialVelocity_iff
    {ν : ℝ} (hν : 0 < ν) {a k d : ℝ} :
    ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearStreamwiseDriftInitialVelocity a k d) ↔
      d = 0 ∧ a * k = 0 := by
  simpa [heatShearFullDriftInitialVelocity_zero_verticalDrift] using
    (ExplicitConcreteNavierStokesRegularityClause_heatShearFullDriftInitialVelocity_iff
      (ν := ν) hν (a := a) (k := k) (d := d) (c := 0))

/-- The structured fully concrete clause is exact on the streamwise-drift
heat-shear family. -/
theorem concreteNavierStokesGlobalRegularityClause_heatShearStreamwiseDriftInitialVelocity_iff
    {ν : ℝ} (hν : 0 < ν) {a k d : ℝ} :
    NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := heatShearStreamwiseDriftInitialVelocity a k d
          smooth_initial := smoothInitialVelocityData_heatShearStreamwiseDriftInitialVelocity a k d
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_heatShearStreamwiseDriftInitialVelocity a k d x } ↔
      d = 0 ∧ a * k = 0 := by
  constructor
  · intro hClause
    exact
      (concreteNavierStokesGlobalRegularityClause_iff
        (ν := ν) (u₀ := heatShearStreamwiseDriftInitialVelocity a k d)
        hν
        (smoothInitialVelocityData_heatShearStreamwiseDriftInitialVelocity a k d)
        (by
          intro x
          simpa using initialSpatialDivergence_heatShearStreamwiseDriftInitialVelocity a k d x)).mp
          hClause
        |> (ExplicitConcreteNavierStokesGlobalOutput_heatShearStreamwiseDriftInitialVelocity_iff
              (ν := ν) (a := a) (k := k) (d := d)).1
  · intro hcond
    exact
      ExplicitConcreteNavierStokesGlobalOutput_implies_concreteNavierStokesGlobalRegularityClause
        hν
        (smoothInitialVelocityData_heatShearStreamwiseDriftInitialVelocity a k d)
        (by
          intro x
          simpa using initialSpatialDivergence_heatShearStreamwiseDriftInitialVelocity a k d x)
        ((ExplicitConcreteNavierStokesGlobalOutput_heatShearStreamwiseDriftInitialVelocity_iff
          (ν := ν) (a := a) (k := k) (d := d)).2 hcond)

/-- The structured fully concrete clause is exact on the vertical-drift
heat-shear family. -/
theorem concreteNavierStokesGlobalRegularityClause_heatShearVerticalDriftInitialVelocity_iff
    {ν : ℝ} (hν : 0 < ν) {a k c : ℝ} :
    NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := heatShearVerticalDriftInitialVelocity a k c
          smooth_initial := smoothInitialVelocityData_heatShearVerticalDriftInitialVelocity a k c
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_heatShearVerticalDriftInitialVelocity a k c x } ↔
      c = 0 ∧ a * k = 0 := by
  constructor
  · intro hClause
    exact
      (concreteNavierStokesGlobalRegularityClause_iff
        (ν := ν) (u₀ := heatShearVerticalDriftInitialVelocity a k c)
        hν
        (smoothInitialVelocityData_heatShearVerticalDriftInitialVelocity a k c)
        (by
          intro x
          simpa using initialSpatialDivergence_heatShearVerticalDriftInitialVelocity a k c x)).mp
          hClause
        |> (ExplicitConcreteNavierStokesGlobalOutput_heatShearVerticalDriftInitialVelocity_iff
              (ν := ν) (a := a) (k := k) (c := c)).1
  · intro hcond
    exact
      ExplicitConcreteNavierStokesGlobalOutput_implies_concreteNavierStokesGlobalRegularityClause
        hν
        (smoothInitialVelocityData_heatShearVerticalDriftInitialVelocity a k c)
        (by
          intro x
          simpa using initialSpatialDivergence_heatShearVerticalDriftInitialVelocity a k c x)
        ((ExplicitConcreteNavierStokesGlobalOutput_heatShearVerticalDriftInitialVelocity_iff
          (ν := ν) (a := a) (k := k) (c := c)).2 hcond)

/-- On nonnegative slabs, the explicit uniform-vorticity continuation clause is
also vacuous for full-drift heat-shear initial data with nonzero streamwise
drift because the finite-time witness type is already empty there. -/
theorem ExplicitUniformVorticityContinuationClause_heatShearFullDriftInitialVelocity
    {ν T : ℝ} {a k d c : ℝ}
    (hd : d ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause
      ν (heatShearFullDriftInitialVelocity a k d c) T := by
  exact
    ExplicitUniformVorticityContinuationClause_of_not_nonempty_finiteTimeWitness
      (u₀ := heatShearFullDriftInitialVelocity a k d c)
      (not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearFullDriftInitialVelocity
        (ν := ν) (T := T) (a := a) (k := k) (d := d) (c := c) hd hT)

/-- The explicit uniform-vorticity continuation clause can therefore be true on
full-drift heat-shear data with nonzero streamwise drift while the concrete
regularity clause is false there. -/
theorem ExplicitUniformVorticityContinuationClause_heatShearFullDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a k d c : ℝ}
    (hν : 0 < ν)
    (hd : d ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause
        ν (heatShearFullDriftInitialVelocity a k d c) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (heatShearFullDriftInitialVelocity a k d c) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitUniformVorticityContinuationClause_heatShearFullDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (d := d) (c := c) hd hT
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearFullDriftInitialVelocity
      hν hd

/-- The repaired uniform-vorticity continuation clause is also vacuous on
full-drift heat-shear data with nonzero streamwise drift because the repaired
finite-energy hypothesis already fails. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_heatShearFullDriftInitialVelocity
    {ν T : ℝ} {a k d c : ℝ}
    (hd : d ≠ 0) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
      ν (heatShearFullDriftInitialVelocity a k d c) T := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearFullDriftInitialVelocity a k d c)
      (not_finiteInitialKineticEnergy_heatShearFullDriftInitialVelocity hd)

/-- The repaired uniform-vorticity clause can therefore also be true on
full-drift heat-shear data with nonzero streamwise drift while the concrete
regularity clause is false there. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_heatShearFullDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a k d c : ℝ}
    (hν : 0 < ν)
    (hd : d ≠ 0) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
        ν (heatShearFullDriftInitialVelocity a k d c) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (heatShearFullDriftInitialVelocity a k d c) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitFiniteEnergyUniformVorticityContinuationClause_heatShearFullDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (d := d) (c := c) hd
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearFullDriftInitialVelocity
      hν hd

end UniformVorticityContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
