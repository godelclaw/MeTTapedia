import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityLinearShearExactness

/-!
# Linear-Shear Uniform-Continuation Clauses

This module contains the linear-shear uniform-vorticity continuation
clauses and their without-regularity witnesses.  The global-output and
regularity exactness lemmas live in the linear-shear exactness module.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section UniformVorticityContinuation

/-- On nonnegative slabs, the explicit uniform-vorticity continuation clause is
also trivially satisfied for nonzero linear shear initial data because the
quantified finite-time witness type is already uninhabited there. -/
theorem ExplicitUniformVorticityContinuationClause_linearShearInitialVelocity
    {ν T : ℝ} {a : ℝ}
    (ha : a ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν (linearShearInitialVelocity a) T := by
  exact
    ExplicitUniformVorticityContinuationClause_of_not_nonempty_finiteTimeWitness
      (u₀ := linearShearInitialVelocity a)
      (not_nonempty_ExplicitFiniteTimeRegularityWitness_linearShearInitialVelocity
        (ν := ν) (T := T) ha hT)

/-- The uniform continuation clause can therefore be true on nonzero linear
shear initial data even though the concrete regularity clause is false there.
-/
theorem ExplicitUniformVorticityContinuationClause_linearShearInitialVelocity_without_regularity
    {ν T : ℝ} {a : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν (linearShearInitialVelocity a) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν (linearShearInitialVelocity a) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitUniformVorticityContinuationClause_linearShearInitialVelocity
      (ν := ν) (T := T) ha hT
  · exact not_ExplicitConcreteNavierStokesRegularityClause_linearShearInitialVelocity hν ha

/-- The repaired uniform-vorticity continuation clause is also vacuous on
nonzero linear shear data, now for the stronger reason that the finite-energy
input hypothesis itself already fails.  No horizon sign condition is needed. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_linearShearInitialVelocity
    {ν T : ℝ} {a : ℝ}
    (ha : a ≠ 0) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
      ν (linearShearInitialVelocity a) T := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_of_not_finiteInitialKineticEnergy
      (u₀ := linearShearInitialVelocity a)
      (not_finiteInitialKineticEnergy_linearShearInitialVelocity ha)

/-- The repaired uniform-vorticity clause can therefore also be true on
nonzero linear shear data while the concrete regularity clause is false there.
-/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_linearShearInitialVelocity_without_regularity
    {ν T : ℝ} {a : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
        ν (linearShearInitialVelocity a) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν (linearShearInitialVelocity a) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitFiniteEnergyUniformVorticityContinuationClause_linearShearInitialVelocity
      (ν := ν) (T := T) ha
  · exact not_ExplicitConcreteNavierStokesRegularityClause_linearShearInitialVelocity hν ha

/-- On nonnegative slabs, the explicit uniform-vorticity continuation clause is
also trivially satisfied for nonzero affine shear initial data because the
finite-time witness type is already empty there. -/
theorem ExplicitUniformVorticityContinuationClause_linearShearVerticalDriftInitialVelocity
    {ν T : ℝ} {a b : ℝ}
    (ha : a ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause
      ν (linearShearVerticalDriftInitialVelocity a b) T := by
  exact
    ExplicitUniformVorticityContinuationClause_of_not_nonempty_finiteTimeWitness
      (u₀ := linearShearVerticalDriftInitialVelocity a b)
      (not_nonempty_ExplicitFiniteTimeRegularityWitness_linearShearVerticalDriftInitialVelocity
        (ν := ν) (T := T) (a := a) (b := b) ha hT)

/-- On nonnegative slabs, the explicit uniform-vorticity continuation clause is
also trivially satisfied for nonzero affine shear initial data
`x ↦ (a * x₁, b, 0)` because the finite-time witness type is already empty
there. -/
theorem ExplicitUniformVorticityContinuationClause_linearShearHorizontalDriftInitialVelocity
    {ν T : ℝ} {a b : ℝ}
    (ha : a ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause
      ν (linearShearHorizontalDriftInitialVelocity a b) T := by
  exact
    ExplicitUniformVorticityContinuationClause_of_not_nonempty_finiteTimeWitness
      (u₀ := linearShearHorizontalDriftInitialVelocity a b)
      (not_nonempty_ExplicitFiniteTimeRegularityWitness_linearShearHorizontalDriftInitialVelocity
        (ν := ν) (T := T) (a := a) (b := b) ha hT)

/-- On nonnegative slabs, the explicit uniform-vorticity continuation clause is
also trivially satisfied for nonzero affine shear initial data
`x ↦ (a * x₁, b, c)` because the finite-time witness type is already empty
there. -/
theorem ExplicitUniformVorticityContinuationClause_linearShearFullDriftInitialVelocity
    {ν T : ℝ} {a b c : ℝ}
    (ha : a ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause
      ν (linearShearFullDriftInitialVelocity a b c) T := by
  exact
    ExplicitUniformVorticityContinuationClause_of_not_nonempty_finiteTimeWitness
      (u₀ := linearShearFullDriftInitialVelocity a b c)
      (not_nonempty_ExplicitFiniteTimeRegularityWitness_linearShearFullDriftInitialVelocity
        (ν := ν) (T := T) (a := a) (b := b) (c := c) ha hT)

/-- The uniform continuation clause can therefore also be true on nonzero
affine shear initial data even though the concrete regularity clause is false
there. -/
theorem ExplicitUniformVorticityContinuationClause_linearShearVerticalDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a b : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause
        ν (linearShearVerticalDriftInitialVelocity a b) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (linearShearVerticalDriftInitialVelocity a b) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitUniformVorticityContinuationClause_linearShearVerticalDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (b := b) ha hT
  · exact
      not_ExplicitConcreteNavierStokesRegularityClause_linearShearVerticalDriftInitialVelocity
        hν ha

/-- The uniform continuation clause can therefore also be true on nonzero
affine shear initial data `x ↦ (a * x₁, b, 0)` even though the concrete
regularity clause is false there. -/
theorem ExplicitUniformVorticityContinuationClause_linearShearHorizontalDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a b : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause
        ν (linearShearHorizontalDriftInitialVelocity a b) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (linearShearHorizontalDriftInitialVelocity a b) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitUniformVorticityContinuationClause_linearShearHorizontalDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (b := b) ha hT
  · exact
      not_ExplicitConcreteNavierStokesRegularityClause_linearShearHorizontalDriftInitialVelocity
        hν ha

/-- The uniform continuation clause can therefore also be true on nonzero
affine shear initial data `x ↦ (a * x₁, b, c)` even though the concrete
regularity clause is false there. -/
theorem ExplicitUniformVorticityContinuationClause_linearShearFullDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a b c : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause
        ν (linearShearFullDriftInitialVelocity a b c) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (linearShearFullDriftInitialVelocity a b c) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitUniformVorticityContinuationClause_linearShearFullDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (b := b) (c := c) ha hT
  · exact
      not_ExplicitConcreteNavierStokesRegularityClause_linearShearFullDriftInitialVelocity
        hν ha

/-- The repaired uniform-vorticity continuation clause is also vacuous on
nonzero affine shear data because the finite-energy input hypothesis already
fails. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_linearShearVerticalDriftInitialVelocity
    {ν T : ℝ} {a b : ℝ}
    (ha : a ≠ 0) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
      ν (linearShearVerticalDriftInitialVelocity a b) T := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_of_not_finiteInitialKineticEnergy
      (u₀ := linearShearVerticalDriftInitialVelocity a b)
      (not_finiteInitialKineticEnergy_linearShearVerticalDriftInitialVelocity
        (a := a) (b := b) ha)

/-- The repaired uniform-vorticity continuation clause is also vacuous on
nonzero affine shear data `x ↦ (a * x₁, b, 0)` because the finite-energy input
hypothesis already fails. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_linearShearHorizontalDriftInitialVelocity
    {ν T : ℝ} {a b : ℝ}
    (ha : a ≠ 0) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
      ν (linearShearHorizontalDriftInitialVelocity a b) T := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_of_not_finiteInitialKineticEnergy
      (u₀ := linearShearHorizontalDriftInitialVelocity a b)
      (not_finiteInitialKineticEnergy_linearShearHorizontalDriftInitialVelocity
        (a := a) (b := b) ha)

/-- The repaired uniform-vorticity continuation clause is also vacuous on
nonzero affine shear data `x ↦ (a * x₁, b, c)` because the finite-energy input
hypothesis already fails. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_linearShearFullDriftInitialVelocity
    {ν T : ℝ} {a b c : ℝ}
    (ha : a ≠ 0) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
      ν (linearShearFullDriftInitialVelocity a b c) T := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_of_not_finiteInitialKineticEnergy
      (u₀ := linearShearFullDriftInitialVelocity a b c)
      (not_finiteInitialKineticEnergy_linearShearFullDriftInitialVelocity
        (a := a) (b := b) (c := c) ha)

/-- The repaired uniform-vorticity clause can therefore also be true on
nonzero affine shear data while the concrete regularity clause is false there.
-/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_linearShearVerticalDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a b : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
        ν (linearShearVerticalDriftInitialVelocity a b) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (linearShearVerticalDriftInitialVelocity a b) := by
  refine ⟨?_, ?_⟩
  · exact
      ExplicitFiniteEnergyUniformVorticityContinuationClause_linearShearVerticalDriftInitialVelocity
        (ν := ν) (T := T) (a := a) (b := b) ha
  · exact
      not_ExplicitConcreteNavierStokesRegularityClause_linearShearVerticalDriftInitialVelocity
        hν ha

/-- The repaired uniform-vorticity clause can therefore also be true on
nonzero affine shear data `x ↦ (a * x₁, b, 0)` while the concrete regularity
clause is false there. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_linearShearHorizontalDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a b : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
        ν (linearShearHorizontalDriftInitialVelocity a b) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (linearShearHorizontalDriftInitialVelocity a b) := by
  refine ⟨?_, ?_⟩
  · exact
      ExplicitFiniteEnergyUniformVorticityContinuationClause_linearShearHorizontalDriftInitialVelocity
        (ν := ν) (T := T) (a := a) (b := b) ha
  · exact
      not_ExplicitConcreteNavierStokesRegularityClause_linearShearHorizontalDriftInitialVelocity
        hν ha

/-- The repaired uniform-vorticity clause can therefore also be true on
nonzero affine shear data `x ↦ (a * x₁, b, c)` while the concrete regularity
clause is false there. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_linearShearFullDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a b c : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
        ν (linearShearFullDriftInitialVelocity a b c) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (linearShearFullDriftInitialVelocity a b c) := by
  refine ⟨?_, ?_⟩
  · exact
      ExplicitFiniteEnergyUniformVorticityContinuationClause_linearShearFullDriftInitialVelocity
        (ν := ν) (T := T) (a := a) (b := b) (c := c) ha
  · exact
      not_ExplicitConcreteNavierStokesRegularityClause_linearShearFullDriftInitialVelocity
        hν ha



end UniformVorticityContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
