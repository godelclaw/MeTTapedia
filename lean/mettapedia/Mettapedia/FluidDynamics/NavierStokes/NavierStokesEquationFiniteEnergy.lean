import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEquationProblemData

/-!
# Finite-Energy Navier-Stokes Target Lemmas

This module records the logical relationships between unrepaired concrete
regularity clauses and repaired finite-energy problem data/targets.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section ConcreteEquationTarget

open scoped Laplacian ContDiff

/-- The unrepaired explicit regularity clause immediately implies the repaired
finite-energy version, since the extra input hypothesis only narrows the class
of admissible data. -/
theorem ExplicitConcreteNavierStokesRegularityClause_implies_finiteEnergy
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (h : ExplicitConcreteNavierStokesRegularityClause ν u₀) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause ν u₀ := by
  intro hν hsmooth hdiv _hfinite
  exact h hν hsmooth hdiv

/-- The repaired explicit regularity clause is vacuous outside the finite-energy
input domain: if `u₀` fails finite initial kinetic energy, the clause holds for
purely logical reasons. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_of_not_finiteInitialKineticEnergy
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (hfinite : ¬ finiteInitialKineticEnergy u₀) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause ν u₀ := by
  intro _hν _hsmooth _hdiv hE
  exact False.elim (hfinite hE)

/-- The repaired structured whole-space input domain is also empty on any
initial datum that fails finite initial kinetic energy. -/
theorem not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_of_not_finiteInitialKineticEnergy
    {u₀ : NSInitialVelocity}
    (hfinite : ¬ finiteInitialKineticEnergy u₀) :
    ¬ Nonempty { P : FiniteEnergyAdmissibleNavierStokesProblemData //
        P.initialVelocity = u₀ } := by
  intro hP
  rcases hP with ⟨⟨P, hinit⟩⟩
  exact hfinite (hinit ▸ P.finite_initial_energy)

/-- For fixed positive viscosity and smooth divergence-free initial data, the
repaired structured whole-space input domain is inhabited exactly when the
datum has finite initial kinetic energy. -/
theorem nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_iff
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0) :
    Nonempty { P : FiniteEnergyAdmissibleNavierStokesProblemData //
        P.viscosity = ν ∧ P.initialVelocity = u₀ } ↔
      finiteInitialKineticEnergy u₀ := by
  constructor
  · intro hP
    rcases hP with ⟨⟨P, hPν, hPu₀⟩⟩
    exact hPu₀ ▸ P.finite_initial_energy
  · intro hfinite
    refine ⟨⟨{ viscosity := ν
               viscosity_pos := hν
               initialVelocity := u₀
               smooth_initial := hsmooth
               divergence_free_initial := hdiv
               finite_initial_energy := hfinite }, ?_⟩⟩
    exact ⟨rfl, rfl⟩

/-- On a fixed finite-energy datum, the repaired and unrepaired explicit
regularity clauses are equivalent. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_iff_of_finiteInitialKineticEnergy
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (hfinite : finiteInitialKineticEnergy u₀) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause ν u₀ ↔
      ExplicitConcreteNavierStokesRegularityClause ν u₀ := by
  constructor
  · intro h hν hsmooth hdiv
    exact h hν hsmooth hdiv hfinite
  · intro h
    exact ExplicitConcreteNavierStokesRegularityClause_implies_finiteEnergy h

/-- On a fixed finite-energy datum, the repaired explicit regularity clause can
be read directly as the unrepaired explicit clause. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_implies_ExplicitConcreteNavierStokesRegularityClause_of_finiteInitialKineticEnergy
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause ν u₀)
    (hfinite : finiteInitialKineticEnergy u₀) :
    ExplicitConcreteNavierStokesRegularityClause ν u₀ := by
  exact
    (ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_iff_of_finiteInitialKineticEnergy
      hfinite).mp h

/-- Therefore the unrepaired explicit whole-space theorem target immediately
subsumes the repaired finite-energy explicit target. -/
theorem ExplicitConcreteNavierStokesMillenniumTarget_implies_finiteEnergy
    (h : ExplicitConcreteNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget := by
  intro ν u₀
  exact ExplicitConcreteNavierStokesRegularityClause_implies_finiteEnergy (h ν u₀)

end ConcreteEquationTarget

end NavierStokes
end FluidDynamics
end Mettapedia
