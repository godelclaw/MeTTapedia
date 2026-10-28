import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEquationEquivalences
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityClauseTransfers
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityEnergyObstructions
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityRegularityTransfers

/-!
# Uniform-vorticity target-surface transfers

Transfer lemmas between the concrete Navier-Stokes theorem surfaces and the
uniform-vorticity continuation clauses/targets.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section UniformVorticityContinuation

/-- The fully explicit NS theorem target subsumes the uniform-vorticity
continuation target.  This is only a one-way sanity theorem: the current proof
reuses the global theorem target directly and does not yet use the finite-time
witness or vorticity-bound hypothesis analytically. -/
theorem ExplicitConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationTarget
    (h : ExplicitConcreteNavierStokesMillenniumTarget) :
    ExplicitUniformVorticityContinuationTarget := by
  intro ν u₀
  exact
    ExplicitConcreteNavierStokesRegularityClause_implies_ExplicitUniformVorticityContinuationClause_allHorizons
      (h ν u₀)

/-- The same unrepaired explicit theorem surface also exports the whole
fixed-datum family of uniform-vorticity continuation clauses directly. -/
theorem ExplicitConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_allHorizons
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ T : ℝ, ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitConcreteNavierStokesRegularityClause_implies_ExplicitUniformVorticityContinuationClause_allHorizons
      (h ν u₀)

/-- The same unrepaired explicit theorem surface also gives the corresponding
fixed-horizon uniform-vorticity continuation clause directly. -/
theorem ExplicitConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    (ExplicitConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) h) T

/-- The same lift also holds on the theorem surface: an unrepaired
uniform-vorticity target immediately implies the repaired one, because the
extra finite-energy input is only an admissibility restriction. -/
theorem ExplicitUniformVorticityContinuationTarget_implies_finiteEnergyUniformVorticityContinuationTarget
    (hUniform : ExplicitUniformVorticityContinuationTarget) :
    ExplicitFiniteEnergyUniformVorticityContinuationTarget := by
  intro ν u₀ T
  exact ExplicitUniformVorticityContinuationClause_implies_finiteEnergy (hUniform ν u₀ T)

/-- On a nonnegative slab, the repaired and unrepaired uniform-vorticity
continuation clauses coincide: any actual finite-time witness already forces
finite initial kinetic energy. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_iff_of_nonneg_horizon
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T ↔
      ExplicitUniformVorticityContinuationClause ν u₀ T := by
  constructor
  · intro hClause hν hsmooth hdiv W hω
    exact hClause hν hsmooth hdiv (W.finiteInitialKineticEnergy hT) W hω
  · intro hClause
    exact ExplicitUniformVorticityContinuationClause_implies_finiteEnergy hClause

/-- The repaired explicit finite-energy theorem surface directly implies the
repaired uniform-vorticity continuation target. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationTarget
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyUniformVorticityContinuationTarget := by
  intro ν u₀
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_implies_ExplicitFiniteEnergyUniformVorticityContinuationClause_allHorizons
      (h ν u₀)

/-- The repaired explicit finite-energy theorem surface also exports the whole
fixed-datum family of repaired uniform-vorticity continuation clauses. -/
theorem
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ T : ℝ, ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_implies_ExplicitFiniteEnergyUniformVorticityContinuationClause_allHorizons
      (h ν u₀)

/-- On a nonnegative slab, the repaired uniform-vorticity clause can be read as
the original unrepaired clause, because any actual finite-time witness already
supplies the missing finite-energy hypothesis. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_implies_uniformVorticityContinuationClause_of_nonneg_horizon
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hClause : ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T)
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    (ExplicitFiniteEnergyUniformVorticityContinuationClause_iff_of_nonneg_horizon hT).mp
      hClause

/-- Hence the repaired uniform-vorticity target also forgets directly to the
unrepaired clause at each fixed nonnegative horizon. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationTarget_implies_uniformVorticityContinuationClause_of_nonneg_horizon
    (hUniform : ExplicitFiniteEnergyUniformVorticityContinuationTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_implies_uniformVorticityContinuationClause_of_nonneg_horizon
      (hClause := hUniform ν u₀ T) hT

/-- The repaired uniform-vorticity target also forgets to the unrepaired
uniform clause family on every nonnegative horizon. -/
theorem
    ExplicitFiniteEnergyUniformVorticityContinuationTargetOnNonnegHorizons_implies_uniformVorticityContinuationClause_allNonnegHorizons
    (hUniform : ExplicitFiniteEnergyUniformVorticityContinuationTargetOnNonnegHorizons)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ ⦃T : ℝ⦄, 0 ≤ T → ExplicitUniformVorticityContinuationClause ν u₀ T := by
  intro T hT
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_implies_uniformVorticityContinuationClause_of_nonneg_horizon
      (hClause := hUniform ν u₀ hT) hT

/-- The repaired explicit finite-energy theorem surface proves the corrected
nonnegative-horizon continuation target directly. -/
theorem
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationTargetOnNonnegHorizons
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyUniformVorticityContinuationTargetOnNonnegHorizons := by
  intro ν u₀ T _hT
  exact
    (ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_implies_ExplicitFiniteEnergyUniformVorticityContinuationClause_allHorizons
      (h ν u₀)) T

/-- The repaired uniform-vorticity target also forgets to the unrepaired
uniform clause family on every nonnegative horizon. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationTarget_implies_uniformVorticityContinuationClause_allNonnegHorizons
    (hUniform : ExplicitFiniteEnergyUniformVorticityContinuationTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ ⦃T : ℝ⦄, 0 ≤ T → ExplicitUniformVorticityContinuationClause ν u₀ T := by
  intro T hT
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationTarget_implies_uniformVorticityContinuationClause_of_nonneg_horizon
      (ν := ν) (u₀ := u₀) (T := T) hUniform hT

/-- The repaired explicit finite-energy theorem surface also directly implies
the repaired uniform-vorticity continuation clause at each fixed horizon. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    (ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) h) T

/-- Likewise for the structured repaired finite-energy theorem surface. -/
theorem FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationTarget
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyUniformVorticityContinuationTarget := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationTarget
      (FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget
        h)

/-- Likewise for the structured repaired finite-energy theorem surface as a
fixed-datum all-horizons family. -/
theorem FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ T : ℝ, ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀)
      (FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget
        h)

/-- Likewise for the structured repaired finite-energy theorem surface at a
fixed horizon. -/
theorem FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    (FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) h) T

/-- Since the unrepaired explicit theorem surface subsumes the repaired
finite-energy theorem surface, it also directly subsumes the repaired
uniform-vorticity continuation target. -/
theorem ExplicitConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationTarget
    (h : ExplicitConcreteNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyUniformVorticityContinuationTarget := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationTarget
      (ExplicitConcreteNavierStokesMillenniumTarget_implies_finiteEnergy h)

/-- The same unrepaired explicit theorem surface also exports the whole
fixed-datum family of repaired uniform-vorticity continuation clauses. -/
theorem ExplicitConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ T : ℝ, ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀)
      (ExplicitConcreteNavierStokesMillenniumTarget_implies_finiteEnergy h)

/-- Likewise, the unrepaired explicit theorem surface directly subsumes the
repaired uniform-vorticity continuation clause at each fixed horizon. -/
theorem ExplicitConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    (ExplicitConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) h) T

/-- Likewise for the structured unrepaired whole-space theorem surface. -/
theorem ConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationTarget
    (h : ConcreteNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyUniformVorticityContinuationTarget := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationTarget
      (ConcreteNavierStokesMillenniumTarget_implies_ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget
        h)

/-- Likewise for the structured unrepaired whole-space theorem surface as a
fixed-datum all-horizons family of repaired uniform clauses. -/
theorem ConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons
    (h : ConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ T : ℝ, ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀)
      (ConcreteNavierStokesMillenniumTarget_implies_ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget
        h)

/-- Likewise for the structured unrepaired whole-space theorem surface at a
fixed horizon. -/
theorem ConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause
    (h : ConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    (ConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) h) T

/-- The repaired explicit finite-energy theorem surface still implies the
uniform-vorticity continuation clause on every nonnegative slab.  Finite-energy
inputs are handled by the repaired target directly; non-finite-energy inputs
cannot support a finite-time witness there in the first place. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_allNonnegHorizons
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ ⦃T : ℝ⦄, 0 ≤ T → ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationTargetOnNonnegHorizons_implies_uniformVorticityContinuationClause_allNonnegHorizons
      (ν := ν) (u₀ := u₀)
      (ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationTargetOnNonnegHorizons
        h)

/-- The repaired explicit finite-energy theorem surface still implies the
uniform-vorticity continuation clause on every nonnegative slab.  Finite-energy
inputs are handled by the repaired target directly; non-finite-energy inputs
cannot support a finite-time witness there in the first place. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_of_nonneg_horizon
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_allNonnegHorizons
      (ν := ν) (u₀ := u₀) h hT

/-- Likewise, the repaired structured finite-energy theorem surface implies the
same continuation clause on every nonnegative slab. -/
theorem FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_allNonnegHorizons
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ ⦃T : ℝ⦄, 0 ≤ T → ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_allNonnegHorizons
      (ν := ν) (u₀ := u₀)
      (FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget
        h)

/-- Likewise, the repaired structured finite-energy theorem surface implies the
same continuation clause on every nonnegative slab. -/
theorem FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_of_nonneg_horizon
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_allNonnegHorizons
      (ν := ν) (u₀ := u₀) h hT

/-- Likewise, the structured fully concrete theorem target subsumes the same
uniform-vorticity continuation target via the explicit-target equivalence.
Again, this is only a subsumption theorem, not a continuation proof. -/
theorem ConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationTarget
    (h : ConcreteNavierStokesMillenniumTarget) :
    ExplicitUniformVorticityContinuationTarget := by
  exact (ExplicitConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationTarget
      (ConcreteNavierStokesMillenniumTarget_implies_ExplicitConcreteNavierStokesMillenniumTarget
        h))

/-- Likewise for the structured unrepaired whole-space theorem surface as a
fixed-datum all-horizons family of unrepaired uniform clauses. -/
theorem ConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_allHorizons
    (h : ConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ T : ℝ, ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀)
      (ConcreteNavierStokesMillenniumTarget_implies_ExplicitConcreteNavierStokesMillenniumTarget
        h)

/-- Likewise for the structured unrepaired whole-space theorem surface at a
fixed horizon. -/
theorem ConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause
    (h : ConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    (ConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) h) T

end UniformVorticityContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
