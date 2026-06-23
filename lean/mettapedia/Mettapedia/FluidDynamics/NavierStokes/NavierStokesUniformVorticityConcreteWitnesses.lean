import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityZeroPressureGaugeWitnesses
/-!
# Uniform-vorticity concrete witnesses

Concrete finite-energy and zero-data witness clauses for the uniform-vorticity
Navier-Stokes continuation surface.  Zero-output consequences and theorem-surface
transfers live in later modules.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section UniformVorticityContinuation

/-- The current fully explicit concrete local surrogate millennium target is
already false: nonzero linear shear initial data are admitted as smooth
divergence-free input, but cannot satisfy the bounded-energy output slot.  This
refutes the over-broad local `ℝ^3` surrogate only; it is kept as a regression
guard against reintroducing that theorem-shape bug, not as a refutation of
narrower manuscript-compatible input surfaces. -/
theorem not_ExplicitConcreteNavierStokesMillenniumTarget :
    ¬ ExplicitConcreteNavierStokesMillenniumTarget := by
  intro hTarget
  have hν : 0 < (1 : ℝ) := by positivity
  exact
    not_ExplicitConcreteNavierStokesRegularityClause_linearShearInitialVelocity
      (ν := 1) (a := 1) hν one_ne_zero
      (hTarget 1 (linearShearInitialVelocity 1))

/-- Hence the structured fully concrete theorem target is also false.  The bug
is in the chosen admissible-data surface, not in the equivalence theorem. -/
theorem not_ConcreteNavierStokesMillenniumTarget :
    ¬ ConcreteNavierStokesMillenniumTarget := by
  intro hTarget
  exact
    not_ExplicitConcreteNavierStokesMillenniumTarget
      (ConcreteNavierStokesMillenniumTarget_implies_ExplicitConcreteNavierStokesMillenniumTarget
        hTarget)

end UniformVorticityContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
