import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMInitialVelocityExamplesCore

/-!
# Affine-shear initial-velocity BKM examples
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section BKMContinuation

theorem ExplicitBKMContinuationClause_linearShearInitialVelocity
    {ν T : ℝ} {a : ℝ}
    (ha : a ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (linearShearInitialVelocity a) T := by
  exact
    ExplicitBKMContinuationClause_of_not_nonempty_finiteTimeWitness
      (u₀ := linearShearInitialVelocity a)
      (not_nonempty_ExplicitFiniteTimeRegularityWitness_linearShearInitialVelocity
        (ν := ν) (T := T) ha hT)

/-- The BKM continuation clause can therefore also be true on nonzero linear
shear initial data while the concrete regularity clause is false there. -/
theorem ExplicitBKMContinuationClause_linearShearInitialVelocity_without_regularity
    {ν T : ℝ} {a : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (linearShearInitialVelocity a) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν (linearShearInitialVelocity a) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitBKMContinuationClause_linearShearInitialVelocity
      (ν := ν) (T := T) ha hT
  · exact not_ExplicitConcreteNavierStokesRegularityClause_linearShearInitialVelocity hν ha

/-- The repaired BKM continuation clause is also vacuous on nonzero linear
shear data because the repaired finite-energy input hypothesis already fails.
Again, no horizon sign condition is needed. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_linearShearInitialVelocity
    {ν T : ℝ} {a : ℝ}
    (ha : a ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause ν (linearShearInitialVelocity a) T := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_of_not_finiteInitialKineticEnergy
      (u₀ := linearShearInitialVelocity a)
      (not_finiteInitialKineticEnergy_linearShearInitialVelocity ha)

/-- The repaired BKM continuation clause can therefore also be true on
nonzero linear shear data while the concrete regularity clause is false there.
-/
theorem ExplicitFiniteEnergyBKMContinuationClause_linearShearInitialVelocity_without_regularity
    {ν T : ℝ} {a : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause ν (linearShearInitialVelocity a) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν (linearShearInitialVelocity a) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitFiniteEnergyBKMContinuationClause_linearShearInitialVelocity
      (ν := ν) (T := T) ha
  · exact not_ExplicitConcreteNavierStokesRegularityClause_linearShearInitialVelocity hν ha

/-- The same BKM-side vacuity caveat holds for nonzero affine shear initial
data `x ↦ (a * x₁, 0, b)`: on nonnegative slabs the clause is true because the
finite-time witness type is already empty there. -/
theorem ExplicitBKMContinuationClause_linearShearVerticalDriftInitialVelocity
    {ν T : ℝ} {a b : ℝ}
    (ha : a ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (linearShearVerticalDriftInitialVelocity a b) T := by
  exact
    ExplicitBKMContinuationClause_of_not_nonempty_finiteTimeWitness
      (u₀ := linearShearVerticalDriftInitialVelocity a b)
      (not_nonempty_ExplicitFiniteTimeRegularityWitness_linearShearVerticalDriftInitialVelocity
        (ν := ν) (T := T) (a := a) (b := b) ha hT)

/-- The BKM continuation clause can therefore also be true on nonzero affine
shear data while the concrete regularity clause is false there. -/
theorem ExplicitBKMContinuationClause_linearShearVerticalDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a b : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (linearShearVerticalDriftInitialVelocity a b) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (linearShearVerticalDriftInitialVelocity a b) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitBKMContinuationClause_linearShearVerticalDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (b := b) ha hT
  · exact
      not_ExplicitConcreteNavierStokesRegularityClause_linearShearVerticalDriftInitialVelocity
        hν ha

/-- The repaired BKM continuation clause is also vacuous on nonzero affine
shear data because the repaired finite-energy input hypothesis already fails. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_linearShearVerticalDriftInitialVelocity
    {ν T : ℝ} {a b : ℝ}
    (ha : a ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause ν
      (linearShearVerticalDriftInitialVelocity a b) T := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_of_not_finiteInitialKineticEnergy
      (u₀ := linearShearVerticalDriftInitialVelocity a b)
      (not_finiteInitialKineticEnergy_linearShearVerticalDriftInitialVelocity
        (a := a) (b := b) ha)

/-- The repaired BKM continuation clause can therefore also be true on nonzero
affine shear data while the concrete regularity clause is false there. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_linearShearVerticalDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a b : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause ν
        (linearShearVerticalDriftInitialVelocity a b) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (linearShearVerticalDriftInitialVelocity a b) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitFiniteEnergyBKMContinuationClause_linearShearVerticalDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (b := b) ha
  · exact
      not_ExplicitConcreteNavierStokesRegularityClause_linearShearVerticalDriftInitialVelocity
        hν ha

/-- The same BKM-side vacuity caveat holds for nonzero affine shear initial
data `x ↦ (a * x₁, b, 0)`: on nonnegative slabs the clause is true because the
finite-time witness type is already empty there. -/
theorem ExplicitBKMContinuationClause_linearShearHorizontalDriftInitialVelocity
    {ν T : ℝ} {a b : ℝ}
    (ha : a ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (linearShearHorizontalDriftInitialVelocity a b) T := by
  exact
    ExplicitBKMContinuationClause_of_not_nonempty_finiteTimeWitness
      (u₀ := linearShearHorizontalDriftInitialVelocity a b)
      (not_nonempty_ExplicitFiniteTimeRegularityWitness_linearShearHorizontalDriftInitialVelocity
        (ν := ν) (T := T) (a := a) (b := b) ha hT)

/-- The BKM continuation clause can therefore also be true on nonzero affine
shear data `x ↦ (a * x₁, b, 0)` while the concrete regularity clause is false
there. -/
theorem ExplicitBKMContinuationClause_linearShearHorizontalDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a b : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (linearShearHorizontalDriftInitialVelocity a b) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (linearShearHorizontalDriftInitialVelocity a b) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitBKMContinuationClause_linearShearHorizontalDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (b := b) ha hT
  · exact
      not_ExplicitConcreteNavierStokesRegularityClause_linearShearHorizontalDriftInitialVelocity
        hν ha

/-- The repaired BKM continuation clause is also vacuous on nonzero affine
shear data `x ↦ (a * x₁, b, 0)` because the repaired finite-energy input
hypothesis already fails. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_linearShearHorizontalDriftInitialVelocity
    {ν T : ℝ} {a b : ℝ}
    (ha : a ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause ν
      (linearShearHorizontalDriftInitialVelocity a b) T := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_of_not_finiteInitialKineticEnergy
      (u₀ := linearShearHorizontalDriftInitialVelocity a b)
      (not_finiteInitialKineticEnergy_linearShearHorizontalDriftInitialVelocity
        (a := a) (b := b) ha)

/-- The repaired BKM continuation clause can therefore also be true on nonzero
affine shear data `x ↦ (a * x₁, b, 0)` while the concrete regularity clause is
false there. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_linearShearHorizontalDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a b : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause ν
        (linearShearHorizontalDriftInitialVelocity a b) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (linearShearHorizontalDriftInitialVelocity a b) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitFiniteEnergyBKMContinuationClause_linearShearHorizontalDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (b := b) ha
  · exact
      not_ExplicitConcreteNavierStokesRegularityClause_linearShearHorizontalDriftInitialVelocity
        hν ha

/-- The same BKM-side vacuity caveat holds for nonzero affine shear initial
data `x ↦ (a * x₁, b, c)`: on nonnegative slabs the clause is true because the
finite-time witness type is already empty there. -/
theorem ExplicitBKMContinuationClause_linearShearFullDriftInitialVelocity
    {ν T : ℝ} {a b c : ℝ}
    (ha : a ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (linearShearFullDriftInitialVelocity a b c) T := by
  exact
    ExplicitBKMContinuationClause_of_not_nonempty_finiteTimeWitness
      (u₀ := linearShearFullDriftInitialVelocity a b c)
      (not_nonempty_ExplicitFiniteTimeRegularityWitness_linearShearFullDriftInitialVelocity
        (ν := ν) (T := T) (a := a) (b := b) (c := c) ha hT)

/-- The BKM continuation clause can therefore also be true on nonzero affine
shear data `x ↦ (a * x₁, b, c)` while the concrete regularity clause is false
there. -/
theorem ExplicitBKMContinuationClause_linearShearFullDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a b c : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (linearShearFullDriftInitialVelocity a b c) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (linearShearFullDriftInitialVelocity a b c) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitBKMContinuationClause_linearShearFullDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (b := b) (c := c) ha hT
  · exact
      not_ExplicitConcreteNavierStokesRegularityClause_linearShearFullDriftInitialVelocity
        hν ha

/-- The repaired BKM continuation clause is also vacuous on nonzero affine
shear data `x ↦ (a * x₁, b, c)` because the repaired finite-energy input
hypothesis already fails. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_linearShearFullDriftInitialVelocity
    {ν T : ℝ} {a b c : ℝ}
    (ha : a ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause ν
      (linearShearFullDriftInitialVelocity a b c) T := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_of_not_finiteInitialKineticEnergy
      (u₀ := linearShearFullDriftInitialVelocity a b c)
      (not_finiteInitialKineticEnergy_linearShearFullDriftInitialVelocity
        (a := a) (b := b) (c := c) ha)

/-- The repaired BKM continuation clause can therefore also be true on nonzero
affine shear data `x ↦ (a * x₁, b, c)` while the concrete regularity clause is
false there. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_linearShearFullDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a b c : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause ν
        (linearShearFullDriftInitialVelocity a b c) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (linearShearFullDriftInitialVelocity a b c) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitFiniteEnergyBKMContinuationClause_linearShearFullDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (b := b) (c := c) ha
  · exact
      not_ExplicitConcreteNavierStokesRegularityClause_linearShearFullDriftInitialVelocity
        hν ha

end BKMContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
