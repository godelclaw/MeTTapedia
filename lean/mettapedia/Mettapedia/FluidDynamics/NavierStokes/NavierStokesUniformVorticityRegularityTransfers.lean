import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityContinuationSurface

/-!
# Uniform-vorticity regularity-clause transfers

Reusable transfers from whole-space concrete regularity clauses to the
uniform-vorticity continuation clause surfaces.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section UniformVorticityContinuation

/-- A fully explicit whole-space regularity clause subsumes the
uniform-vorticity continuation clause at a fixed horizon. -/
theorem ExplicitConcreteNavierStokesRegularityClause_implies_ExplicitUniformVorticityContinuationClause
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (h : ExplicitConcreteNavierStokesRegularityClause ν u₀) :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  intro hν hsmooth hdiv _W _hω
  exact h hν hsmooth hdiv

/-- The repaired explicit whole-space regularity clause likewise yields the
repaired fixed-horizon uniform-vorticity continuation clause on the same datum.
-/
theorem
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_implies_ExplicitFiniteEnergyUniformVorticityContinuationClause
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause ν u₀) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  intro hν hsmooth hdiv hfinite _W _hω
  exact h hν hsmooth hdiv hfinite

/-- The same explicit whole-space regularity clause also yields the whole
fixed-datum family of uniform-vorticity continuation clauses, one for each
horizon. -/
theorem ExplicitConcreteNavierStokesRegularityClause_implies_ExplicitUniformVorticityContinuationClause_allHorizons
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (h : ExplicitConcreteNavierStokesRegularityClause ν u₀) :
    ∀ T : ℝ, ExplicitUniformVorticityContinuationClause ν u₀ T := by
  intro T
  exact
    ExplicitConcreteNavierStokesRegularityClause_implies_ExplicitUniformVorticityContinuationClause
      (T := T) h

/-- Likewise, the repaired explicit whole-space regularity clause yields the
whole fixed-datum family of repaired uniform-vorticity continuation clauses. -/
theorem
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_implies_ExplicitFiniteEnergyUniformVorticityContinuationClause_allHorizons
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause ν u₀) :
    ∀ T : ℝ, ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  intro T
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_implies_ExplicitFiniteEnergyUniformVorticityContinuationClause
      (T := T) h

end UniformVorticityContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
