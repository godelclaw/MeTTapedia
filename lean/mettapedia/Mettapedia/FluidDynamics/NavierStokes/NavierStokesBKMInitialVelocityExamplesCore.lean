import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMZeroOutput

/-!
# Generic BKM initial-velocity clause helper
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section BKMContinuation

/-- If the concrete finite-time witness type is empty on a slab, then the
BKM continuation clause is true there only vacuously. -/
theorem ExplicitBKMContinuationClause_of_not_nonempty_finiteTimeWitness
    {ν T : ℝ} {u₀ : NSInitialVelocity}
    (hEmpty : ¬ Nonempty (ExplicitFiniteTimeRegularityWitness ν u₀ T)) :
    ExplicitBKMContinuationClause ν u₀ T := by
  intro hν hsmooth hdiv W hEnv
  exfalso
  exact hEmpty ⟨W⟩

end BKMContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
