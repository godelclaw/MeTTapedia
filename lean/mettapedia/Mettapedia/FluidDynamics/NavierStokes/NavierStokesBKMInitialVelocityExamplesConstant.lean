import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMInitialVelocityExamplesCore

/-!
# Constant initial-velocity BKM examples
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section BKMContinuation

/-- On nonnegative slabs, the explicit BKM continuation clause is likewise
trivially satisfied for nonzero constant initial data because it quantifies over
the same finite-time witness type, which is already uninhabited there. -/
theorem ExplicitBKMContinuationClause_constantInitialVelocity
    {ν T : ℝ} {c : NSSpace}
    (hc : c ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (constantInitialVelocity c) T := by
  exact
    ExplicitBKMContinuationClause_of_not_nonempty_finiteTimeWitness
      (u₀ := constantInitialVelocity c)
      (not_nonempty_ExplicitFiniteTimeRegularityWitness_constantInitialVelocity
        (ν := ν) (T := T) hc hT)

/-- The same vacuity caveat holds on the BKM surface: the clause can be true on
nonzero constant initial data while the concrete regularity clause remains
false. -/
theorem ExplicitBKMContinuationClause_constantInitialVelocity_without_regularity
    {ν T : ℝ} {c : NSSpace}
    (hν : 0 < ν)
    (hc : c ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (constantInitialVelocity c) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν (constantInitialVelocity c) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitBKMContinuationClause_constantInitialVelocity
      (ν := ν) (T := T) hc hT
  · exact not_ExplicitConcreteNavierStokesRegularityClause_constantInitialVelocity hν hc

/-- The repaired BKM continuation clause is also vacuous on nonzero constant
initial data because the repaired finite-energy input hypothesis already fails.
No horizon sign condition is needed. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_constantInitialVelocity
    {ν T : ℝ} {c : NSSpace}
    (hc : c ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause ν (constantInitialVelocity c) T := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_of_not_finiteInitialKineticEnergy
      (u₀ := constantInitialVelocity c)
      (not_finiteInitialKineticEnergy_constantInitialVelocity hc)

/-- The repaired BKM continuation clause can therefore also be true on nonzero
constant initial data while the concrete regularity clause is false there. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_constantInitialVelocity_without_regularity
    {ν T : ℝ} {c : NSSpace}
    (hν : 0 < ν)
    (hc : c ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause ν (constantInitialVelocity c) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν (constantInitialVelocity c) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitFiniteEnergyBKMContinuationClause_constantInitialVelocity
      (ν := ν) (T := T) hc
  · exact not_ExplicitConcreteNavierStokesRegularityClause_constantInitialVelocity hν hc

end BKMContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
