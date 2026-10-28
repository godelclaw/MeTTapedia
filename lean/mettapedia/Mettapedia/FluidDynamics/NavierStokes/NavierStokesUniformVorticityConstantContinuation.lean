import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityConstantCandidates

/-!
# Constant-Field Uniform-Continuation Clauses

This module contains the constant-field uniform-vorticity continuation
clauses and their without-regularity witnesses for nonzero constant data.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section UniformVorticityContinuation

/-- On nonnegative slabs, the explicit uniform-vorticity continuation clause is
trivially satisfied for nonzero constant initial data because the quantified
finite-time witness type is already uninhabited there.  This records a genuine
target-shape caveat, not analytic progress. -/
theorem ExplicitUniformVorticityContinuationClause_constantInitialVelocity
    {ν T : ℝ} {c : NSSpace}
    (hc : c ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν (constantInitialVelocity c) T := by
  exact
    ExplicitUniformVorticityContinuationClause_of_not_nonempty_finiteTimeWitness
      (u₀ := constantInitialVelocity c)
      (not_nonempty_ExplicitFiniteTimeRegularityWitness_constantInitialVelocity
        (ν := ν) (T := T) hc hT)

/-- The uniform continuation clause can therefore be true on nonzero constant
initial data even though the concrete regularity clause is false there. -/
theorem ExplicitUniformVorticityContinuationClause_constantInitialVelocity_without_regularity
    {ν T : ℝ} {c : NSSpace}
    (hν : 0 < ν)
    (hc : c ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν (constantInitialVelocity c) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν (constantInitialVelocity c) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitUniformVorticityContinuationClause_constantInitialVelocity
      (ν := ν) (T := T) hc hT
  · exact not_ExplicitConcreteNavierStokesRegularityClause_constantInitialVelocity hν hc

/-- The repaired uniform-vorticity continuation clause is also vacuous on
nonzero constant initial data because the repaired finite-energy hypothesis
already fails.  Again, no horizon sign condition is needed. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_constantInitialVelocity
    {ν T : ℝ} {c : NSSpace}
    (hc : c ≠ 0) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
      ν (constantInitialVelocity c) T := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_of_not_finiteInitialKineticEnergy
      (u₀ := constantInitialVelocity c)
      (not_finiteInitialKineticEnergy_constantInitialVelocity hc)

/-- The repaired uniform-vorticity continuation clause can therefore also be
true on nonzero constant initial data while the concrete regularity clause is
false there. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_constantInitialVelocity_without_regularity
    {ν T : ℝ} {c : NSSpace}
    (hν : 0 < ν)
    (hc : c ≠ 0) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
        ν (constantInitialVelocity c) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν (constantInitialVelocity c) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitFiniteEnergyUniformVorticityContinuationClause_constantInitialVelocity
      (ν := ν) (T := T) hc
  · exact not_ExplicitConcreteNavierStokesRegularityClause_constantInitialVelocity hν hc



end UniformVorticityContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
