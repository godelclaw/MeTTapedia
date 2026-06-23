import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityContinuationSurface

/-!
# Uniform-vorticity clause transfers

Reusable transfers between the unrepaired and finite-energy uniform-vorticity
continuation clause surfaces.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section UniformVorticityContinuation

/-- The original continuation clause immediately implies the repaired
finite-energy version, since the extra input hypothesis is only a restriction
on admissible data. -/
theorem ExplicitUniformVorticityContinuationClause_implies_finiteEnergy
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hClause : ExplicitUniformVorticityContinuationClause ν u₀ T) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  intro hν hsmooth hdiv _hfinite W hω
  exact hClause hν hsmooth hdiv W hω

end UniformVorticityContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
