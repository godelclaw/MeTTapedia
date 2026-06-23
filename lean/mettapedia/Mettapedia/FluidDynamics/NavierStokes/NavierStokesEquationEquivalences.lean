import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEquationFiniteEnergy

/-!
# Concrete and Explicit Navier-Stokes Target Equivalences

This module proves equivalences and implications between structured concrete
problem-data clauses, explicit clauses, repaired finite-energy targets, and
restricted input classes.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section ConcreteEquationTarget

open scoped Laplacian ContDiff

/-- The fully concrete structured clause is equivalent to the fully explicit
PDE statement for the same viscosity and initial data. -/
theorem concreteNavierStokesGlobalRegularityClause_iff
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0) :
    NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := u₀
          smooth_initial := hsmooth
          divergence_free_initial := hdiv }
      ↔
        ∃ u : NSVelocityField, ∃ p : NSPressureField,
          smoothSpaceTimeVelocity u ∧
          smoothSpaceTimePressure p ∧
          (∀ t x,
            timeVelocityDerivative u t x + spatialConvection u t x +
                spatialPressureGradient p t x =
              ν • spatialLaplacian u t x) ∧
          (∀ t x, spatialDivergence u t x = 0) ∧
          MatchesInitialVelocity u₀ u ∧
          boundedKineticEnergy u := by
  constructor
  · intro h
    rcases h with ⟨W⟩
    refine ⟨W.velocity, W.pressure, ?_⟩
    exact ⟨W.smooth_velocity, W.smooth_pressure, W.momentum_equation,
      W.incompressible, W.initial_condition, W.bounded_energy⟩
  · intro h
    rcases h with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
    refine ⟨({
      velocity := u
      pressure := p
      smooth_velocity := hu
      smooth_pressure := hp
      momentum_equation := hmom
      incompressible := hinc
      initial_condition := hinit
      bounded_energy := hbd
    } : NavierStokesGlobalRegularityWitness
          mkFullyConcreteNavierStokesSurface
          { viscosity := ν
            viscosity_pos := hν
            initialVelocity := u₀
            smooth_initial := hsmooth
            divergence_free_initial := hdiv })⟩

/-- On a fixed finite-energy datum, the repaired structured fully concrete
clause is equivalent to the repaired explicit regularity clause. -/
theorem finiteEnergyConcreteNavierStokesGlobalRegularityClause_iff
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (hfinite : finiteInitialKineticEnergy u₀) :
    NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        ({ viscosity := ν
           viscosity_pos := hν
           initialVelocity := u₀
           smooth_initial := hsmooth
           divergence_free_initial := hdiv
           finite_initial_energy := hfinite } :
          FiniteEnergyAdmissibleNavierStokesProblemData).toNavierStokesProblemData
      ↔
        ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause ν u₀ := by
  constructor
  · intro h _hν _hsmooth _hdiv _hfinite
    exact
      (concreteNavierStokesGlobalRegularityClause_iff
        (ν := ν) (u₀ := u₀) hν hsmooth hdiv).mp h
  · intro h
    exact
      (concreteNavierStokesGlobalRegularityClause_iff
        (ν := ν) (u₀ := u₀) hν hsmooth hdiv).mpr
        (h hν hsmooth hdiv hfinite)

/-- On a fixed finite-energy datum, the repaired structured fully concrete
clause can be read directly as the unrepaired structured clause. -/
theorem finiteEnergyConcreteNavierStokesGlobalRegularityClause_implies_concreteNavierStokesGlobalRegularityClause_of_finiteInitialKineticEnergy
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (hfinite : finiteInitialKineticEnergy u₀)
    (h :
      NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        ({ viscosity := ν
           viscosity_pos := hν
           initialVelocity := u₀
           smooth_initial := hsmooth
           divergence_free_initial := hdiv
           finite_initial_energy := hfinite } :
          FiniteEnergyAdmissibleNavierStokesProblemData).toNavierStokesProblemData) :
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      { viscosity := ν
        viscosity_pos := hν
        initialVelocity := u₀
        smooth_initial := hsmooth
        divergence_free_initial := hdiv } := by
  have hRepaired :
      ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause ν u₀ :=
    (finiteEnergyConcreteNavierStokesGlobalRegularityClause_iff
      hν hsmooth hdiv hfinite).mp h
  have hExplicit :
      ExplicitConcreteNavierStokesRegularityClause ν u₀ :=
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_implies_ExplicitConcreteNavierStokesRegularityClause_of_finiteInitialKineticEnergy
      hRepaired hfinite
  exact
    (concreteNavierStokesGlobalRegularityClause_iff
      (ν := ν) (u₀ := u₀) hν hsmooth hdiv).mpr
      (hExplicit hν hsmooth hdiv)

/-- Conversely, on a fixed finite-energy datum, the unrepaired structured fully
concrete clause directly implies the repaired one. -/
theorem concreteNavierStokesGlobalRegularityClause_implies_finiteEnergyConcreteNavierStokesGlobalRegularityClause_of_finiteInitialKineticEnergy
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (hfinite : finiteInitialKineticEnergy u₀)
    (h :
      NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := u₀
          smooth_initial := hsmooth
          divergence_free_initial := hdiv }) :
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      ({ viscosity := ν
         viscosity_pos := hν
         initialVelocity := u₀
         smooth_initial := hsmooth
         divergence_free_initial := hdiv
         finite_initial_energy := hfinite } :
        FiniteEnergyAdmissibleNavierStokesProblemData).toNavierStokesProblemData := by
  have hExplicit : ExplicitConcreteNavierStokesRegularityClause ν u₀ := by
    intro _hν _hsmooth _hdiv
    exact
      (concreteNavierStokesGlobalRegularityClause_iff
        (ν := ν) (u₀ := u₀) hν hsmooth hdiv).mp h
  have hRepaired :
      ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause ν u₀ :=
    ExplicitConcreteNavierStokesRegularityClause_implies_finiteEnergy hExplicit
  exact
    (finiteEnergyConcreteNavierStokesGlobalRegularityClause_iff
      hν hsmooth hdiv hfinite).mpr hRepaired

/-- On a fixed finite-energy datum, the repaired structured fully concrete
clause is equivalent to the unrepaired one. -/
theorem finiteEnergyConcreteNavierStokesGlobalRegularityClause_iff_of_finiteInitialKineticEnergy
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (hfinite : finiteInitialKineticEnergy u₀) :
    NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        ({ viscosity := ν
           viscosity_pos := hν
           initialVelocity := u₀
           smooth_initial := hsmooth
           divergence_free_initial := hdiv
           finite_initial_energy := hfinite } :
          FiniteEnergyAdmissibleNavierStokesProblemData).toNavierStokesProblemData
      ↔
        NavierStokesGlobalRegularityClause
          mkFullyConcreteNavierStokesSurface
          { viscosity := ν
            viscosity_pos := hν
            initialVelocity := u₀
            smooth_initial := hsmooth
            divergence_free_initial := hdiv } := by
  constructor
  · intro h
    exact
      finiteEnergyConcreteNavierStokesGlobalRegularityClause_implies_concreteNavierStokesGlobalRegularityClause_of_finiteInitialKineticEnergy
        hν hsmooth hdiv hfinite h
  · intro h
    exact
      concreteNavierStokesGlobalRegularityClause_implies_finiteEnergyConcreteNavierStokesGlobalRegularityClause_of_finiteInitialKineticEnergy
        hν hsmooth hdiv hfinite h

/-- The structured fully concrete target is equivalent to the literal explicit
NS theorem statement on `ℝ × ℝ^3`. -/
theorem ConcreteNavierStokesMillenniumTarget_iff_explicit :
    ConcreteNavierStokesMillenniumTarget ↔
      ExplicitConcreteNavierStokesMillenniumTarget := by
  constructor
  · intro h ν u₀ hν hsmooth hdiv
    simpa [ConcreteNavierStokesMillenniumTarget,
      ExplicitConcreteNavierStokesMillenniumTarget,
      ExplicitConcreteNavierStokesRegularityClause]
      using (concreteNavierStokesGlobalRegularityClause_iff
        (ν := ν) (u₀ := u₀) hν hsmooth hdiv).mp
          (h { viscosity := ν
               viscosity_pos := hν
               initialVelocity := u₀
               smooth_initial := hsmooth
               divergence_free_initial := hdiv })
  · intro h P
    have hExplicit := h P.viscosity P.initialVelocity P.viscosity_pos
      P.smooth_initial P.divergence_free_initial
    exact (concreteNavierStokesGlobalRegularityClause_iff
      (ν := P.viscosity) (u₀ := P.initialVelocity)
      P.viscosity_pos P.smooth_initial P.divergence_free_initial).mpr hExplicit

/-- The structured fully concrete theorem target directly implies the literal
explicit NS theorem statement on `ℝ × ℝ^3`. -/
theorem ConcreteNavierStokesMillenniumTarget_implies_ExplicitConcreteNavierStokesMillenniumTarget
    (h : ConcreteNavierStokesMillenniumTarget) :
    ExplicitConcreteNavierStokesMillenniumTarget := by
  exact (ConcreteNavierStokesMillenniumTarget_iff_explicit).mp h

/-- The repaired structured whole-space theorem target is equivalent to the
corresponding fully explicit statement with finite-energy admissibility on the
input side. -/
theorem FiniteEnergyConcreteNavierStokesMillenniumTarget_iff_explicit :
    FiniteEnergyConcreteNavierStokesMillenniumTarget ↔
      ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget := by
  constructor
  · intro h ν u₀ hν hsmooth hdiv hfinite
    simpa [ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause]
      using
        (concreteNavierStokesGlobalRegularityClause_iff
          (ν := ν) (u₀ := u₀) hν hsmooth hdiv).mp
            (h { viscosity := ν
                 viscosity_pos := hν
                 initialVelocity := u₀
                 smooth_initial := hsmooth
                 divergence_free_initial := hdiv
                 finite_initial_energy := hfinite })
  · intro h P
    have hExplicit :=
      h P.viscosity P.initialVelocity P.viscosity_pos
        P.smooth_initial P.divergence_free_initial P.finite_initial_energy
    exact
      (concreteNavierStokesGlobalRegularityClause_iff
        (ν := P.viscosity) (u₀ := P.initialVelocity)
        P.viscosity_pos P.smooth_initial P.divergence_free_initial).mpr hExplicit

/-- The repaired structured whole-space theorem target directly implies the
corresponding repaired explicit statement with finite-energy admissibility on
the input side. -/
theorem FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget := by
  exact (FiniteEnergyConcreteNavierStokesMillenniumTarget_iff_explicit).mp h

/-- The unrepaired structured whole-space theorem target also directly implies
the repaired explicit theorem surface, by first forgetting to the unrepaired
explicit target and then using the finite-energy subsumption theorem there. -/
theorem ConcreteNavierStokesMillenniumTarget_implies_ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget
    (h : ConcreteNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget := by
  exact
    ExplicitConcreteNavierStokesMillenniumTarget_implies_finiteEnergy
      (ConcreteNavierStokesMillenniumTarget_implies_ExplicitConcreteNavierStokesMillenniumTarget
        h)

/-- Likewise, the unrepaired structured whole-space theorem target subsumes the
repaired structured finite-energy target. -/
theorem ConcreteNavierStokesMillenniumTarget_implies_finiteEnergy
    (h : ConcreteNavierStokesMillenniumTarget) :
    FiniteEnergyConcreteNavierStokesMillenniumTarget := by
  exact
    (FiniteEnergyConcreteNavierStokesMillenniumTarget_iff_explicit).mpr
      (ConcreteNavierStokesMillenniumTarget_implies_ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget
        h)

/-- Any restricted whole-space input class whose members all have finite
initial kinetic energy inherits the repaired explicit theorem surface.  This
packages later manuscript-compatible `ℝ^3` routes, such as Schwartz-style
initial data, without fixing a decay notion in this file. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_apply_of_inputClass
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {InputClass : NSInitialVelocity → Prop}
    (hfinite : ∀ ⦃u₀ : NSInitialVelocity⦄, InputClass u₀ → finiteInitialKineticEnergy u₀)
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (hu₀ : InputClass u₀)
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x +
            spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity u₀ u ∧
      boundedKineticEnergy u := by
  exact h ν u₀ hν hsmooth hdiv (hfinite hu₀)

end ConcreteEquationTarget

end NavierStokes
end FluidDynamics
end Mettapedia
