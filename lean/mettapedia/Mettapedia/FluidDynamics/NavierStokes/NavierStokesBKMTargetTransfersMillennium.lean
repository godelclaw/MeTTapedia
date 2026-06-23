import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMTargetTransfersApplications

/-!
# Millennium-to-BKM Target Transfers

This module transfers explicit and structured Millennium theorem surfaces into BKM continuation targets and clauses.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section BKMContinuation

/-- The fully explicit NS theorem target subsumes the BKM-style continuation
target.  This is only a one-way sanity theorem: the current proof reuses the
global theorem target directly and does not yet use the envelope/integrability
hypothesis analytically. -/
theorem ExplicitConcreteNavierStokesMillenniumTarget_implies_BKMContinuationTarget
    (h : ExplicitConcreteNavierStokesMillenniumTarget) :
    ExplicitBKMContinuationTarget := by
  intro ν u₀
  exact
    ExplicitConcreteNavierStokesRegularityClause_implies_ExplicitBKMContinuationClause_allHorizons
      (h ν u₀)

/-- The same unrepaired explicit theorem surface also exports the whole
fixed-datum family of BKM continuation clauses directly. -/
theorem ExplicitConcreteNavierStokesMillenniumTarget_implies_BKMContinuationClause_allHorizons
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ T : ℝ, ExplicitBKMContinuationClause ν u₀ T := by
  exact
    ExplicitConcreteNavierStokesRegularityClause_implies_ExplicitBKMContinuationClause_allHorizons
      (h ν u₀)

/-- The same unrepaired explicit theorem surface also gives the corresponding
fixed-horizon BKM continuation clause directly. -/
theorem ExplicitConcreteNavierStokesMillenniumTarget_implies_BKMContinuationClause
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitBKMContinuationClause ν u₀ T := by
  exact
    (ExplicitConcreteNavierStokesMillenniumTarget_implies_BKMContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) h) T

/-- The original BKM continuation clause immediately implies the repaired
finite-energy version, since the extra input hypothesis only narrows the
admissible initial data. -/
theorem ExplicitBKMContinuationClause_implies_finiteEnergy
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hClause : ExplicitBKMContinuationClause ν u₀ T) :
    ExplicitFiniteEnergyBKMContinuationClause ν u₀ T := by
  intro hν hsmooth hdiv _hfinite W hBKM
  exact hClause hν hsmooth hdiv W hBKM

/-- The same lift also holds on the theorem surface: an unrepaired BKM target
immediately implies the repaired one, because the extra finite-energy input is
only an admissibility restriction. -/
theorem ExplicitBKMContinuationTarget_implies_finiteEnergyBKMContinuationTarget
    (hBKM : ExplicitBKMContinuationTarget) :
    ExplicitFiniteEnergyBKMContinuationTarget := by
  intro ν u₀ T
  exact ExplicitBKMContinuationClause_implies_finiteEnergy (hBKM ν u₀ T)

/-- The all-horizons repaired BKM target immediately yields the corrected
nonnegative-horizon repaired target. -/
theorem
    ExplicitFiniteEnergyBKMContinuationTarget_implies_finiteEnergyBKMContinuationTargetOnNonnegHorizons
    (hBKM : ExplicitFiniteEnergyBKMContinuationTarget) :
    ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons := by
  intro ν u₀ T _hT
  exact hBKM ν u₀ T

/-- On a nonnegative slab, the repaired and unrepaired BKM continuation clauses
coincide because any actual finite-time witness already carries finite initial
kinetic energy. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_iff_of_nonneg_horizon
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitFiniteEnergyBKMContinuationClause ν u₀ T ↔
      ExplicitBKMContinuationClause ν u₀ T := by
  constructor
  · intro hClause hν hsmooth hdiv W hBKM
    exact hClause hν hsmooth hdiv (W.finiteInitialKineticEnergy hT) W hBKM
  · intro hClause
    exact ExplicitBKMContinuationClause_implies_finiteEnergy hClause

/-- On a nonnegative slab, the repaired BKM clause can first be read as the
original unrepaired BKM clause, because any actual finite-time witness already
supplies the missing finite-energy hypothesis. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_implies_BKMContinuationClause_of_nonneg_horizon
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hClause : ExplicitFiniteEnergyBKMContinuationClause ν u₀ T)
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν u₀ T := by
  exact
    (ExplicitFiniteEnergyBKMContinuationClause_iff_of_nonneg_horizon hT).mp hClause

/-- Hence the repaired BKM target also forgets directly to the unrepaired BKM
clause at each fixed nonnegative horizon. -/
theorem ExplicitFiniteEnergyBKMContinuationTarget_implies_BKMContinuationClause_of_nonneg_horizon
    (hBKM : ExplicitFiniteEnergyBKMContinuationTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_implies_BKMContinuationClause_of_nonneg_horizon
      (hClause := hBKM ν u₀ T) hT

/-- The corrected nonnegative-horizon repaired BKM target forgets to the
unrepaired BKM clause at each fixed nonnegative horizon. -/
theorem
    ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons_implies_BKMContinuationClause_of_nonneg_horizon
    (hBKM : ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_implies_BKMContinuationClause_of_nonneg_horizon
      (hClause := hBKM ν u₀ hT) hT

/-- The repaired BKM target also forgets to the unrepaired BKM clause family
on every nonnegative horizon. -/
theorem ExplicitFiniteEnergyBKMContinuationTarget_implies_BKMContinuationClause_allNonnegHorizons
    (hBKM : ExplicitFiniteEnergyBKMContinuationTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ ⦃T : ℝ⦄, 0 ≤ T → ExplicitBKMContinuationClause ν u₀ T := by
  intro T hT
  exact
    ExplicitFiniteEnergyBKMContinuationTarget_implies_BKMContinuationClause_of_nonneg_horizon
      (ν := ν) (u₀ := u₀) (T := T) hBKM hT

/-- The corrected nonnegative-horizon repaired BKM target forgets to the
unrepaired BKM clause family on every nonnegative horizon. -/
theorem
    ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons_implies_BKMContinuationClause_allNonnegHorizons
    (hBKM : ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ ⦃T : ℝ⦄, 0 ≤ T → ExplicitBKMContinuationClause ν u₀ T := by
  intro T hT
  exact
    ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons_implies_BKMContinuationClause_of_nonneg_horizon
      (ν := ν) (u₀ := u₀) (T := T) hBKM hT

/-- The repaired explicit finite-energy theorem surface directly implies the
repaired BKM-style continuation target. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationTarget
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyBKMContinuationTarget := by
  intro ν u₀
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_implies_ExplicitFiniteEnergyBKMContinuationClause_allHorizons
      (h ν u₀)

/-- The repaired explicit finite-energy theorem surface also proves the
corrected nonnegative-horizon BKM continuation target. -/
theorem
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationTargetOnNonnegHorizons
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons := by
  exact
    ExplicitFiniteEnergyBKMContinuationTarget_implies_finiteEnergyBKMContinuationTargetOnNonnegHorizons
      (ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationTarget h)

/-- The repaired explicit finite-energy theorem surface also exports the whole
fixed-datum family of repaired BKM continuation clauses. -/
theorem
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationClause_allHorizons
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ T : ℝ, ExplicitFiniteEnergyBKMContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_implies_ExplicitFiniteEnergyBKMContinuationClause_allHorizons
      (h ν u₀)

/-- The repaired explicit finite-energy theorem surface also directly implies
the repaired BKM-style continuation clause at each fixed horizon. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationClause
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyBKMContinuationClause ν u₀ T := by
  exact
    (ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) h) T

/-- Likewise for the structured repaired finite-energy theorem surface. -/
theorem FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationTarget
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyBKMContinuationTarget := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationTarget
      (FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget
        h)

/-- Likewise for the structured repaired finite-energy theorem surface as a
fixed-datum all-horizons family. -/
theorem FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationClause_allHorizons
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ T : ℝ, ExplicitFiniteEnergyBKMContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀)
      (FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget
        h)

/-- Likewise for the structured repaired finite-energy theorem surface at a
fixed horizon. -/
theorem FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationClause
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyBKMContinuationClause ν u₀ T := by
  exact
    (FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) h) T

/-- Since the unrepaired explicit theorem surface subsumes the repaired
finite-energy theorem surface, it also directly subsumes the repaired
BKM-style continuation target. -/
theorem ExplicitConcreteNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationTarget
    (h : ExplicitConcreteNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyBKMContinuationTarget := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationTarget
      (ExplicitConcreteNavierStokesMillenniumTarget_implies_finiteEnergy h)

/-- The same unrepaired explicit theorem surface also exports the whole
fixed-datum family of repaired BKM continuation clauses. -/
theorem ExplicitConcreteNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationClause_allHorizons
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ T : ℝ, ExplicitFiniteEnergyBKMContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀)
      (ExplicitConcreteNavierStokesMillenniumTarget_implies_finiteEnergy h)

/-- Likewise, the unrepaired explicit theorem surface directly subsumes the
repaired BKM-style continuation clause at each fixed horizon. -/
theorem ExplicitConcreteNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationClause
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyBKMContinuationClause ν u₀ T := by
  exact
    (ExplicitConcreteNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) h) T

/-- Likewise for the structured unrepaired whole-space theorem surface. -/
theorem ConcreteNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationTarget
    (h : ConcreteNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyBKMContinuationTarget := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationTarget
      (ConcreteNavierStokesMillenniumTarget_implies_ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget
        h)

/-- Likewise for the structured unrepaired whole-space theorem surface as a
fixed-datum all-horizons family of repaired BKM clauses. -/
theorem ConcreteNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationClause_allHorizons
    (h : ConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ T : ℝ, ExplicitFiniteEnergyBKMContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀)
      (ConcreteNavierStokesMillenniumTarget_implies_ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget
        h)

/-- Likewise for the structured unrepaired whole-space theorem surface at a
fixed horizon. -/
theorem ConcreteNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationClause
    (h : ConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyBKMContinuationClause ν u₀ T := by
  exact
    (ConcreteNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) h) T

/-- The repaired explicit finite-energy theorem surface still implies the
BKM-style continuation clause on every nonnegative slab.  If the input datum is
not finite-energy, the finite-time witness type is already empty there. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_BKMContinuationClause_allNonnegHorizons
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ ⦃T : ℝ⦄, 0 ≤ T → ExplicitBKMContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyBKMContinuationTarget_implies_BKMContinuationClause_allNonnegHorizons
      (ν := ν) (u₀ := u₀)
      (ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationTarget
        h)

/-- The repaired explicit finite-energy theorem surface still implies the
BKM-style continuation clause on every nonnegative slab.  If the input datum is
not finite-energy, the finite-time witness type is already empty there. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_BKMContinuationClause_of_nonneg_horizon
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_BKMContinuationClause_allNonnegHorizons
      (ν := ν) (u₀ := u₀) h hT

/-- Likewise, the repaired structured finite-energy theorem surface implies the
same BKM continuation clause on every nonnegative slab. -/
theorem FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_BKMContinuationClause_allNonnegHorizons
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ ⦃T : ℝ⦄, 0 ≤ T → ExplicitBKMContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_BKMContinuationClause_allNonnegHorizons
      (ν := ν) (u₀ := u₀)
      (FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget
        h)

/-- Likewise, the repaired structured finite-energy theorem surface implies the
same BKM continuation clause on every nonnegative slab. -/
theorem FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_BKMContinuationClause_of_nonneg_horizon
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν u₀ T := by
  exact
    FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_BKMContinuationClause_allNonnegHorizons
      (ν := ν) (u₀ := u₀) h hT

/-- Therefore the structured fully concrete theorem target subsumes the same
BKM-style continuation target via the explicit-equivalence theorem.  Again,
this is only a subsumption theorem, not a BKM continuation proof. -/
theorem ConcreteNavierStokesMillenniumTarget_implies_BKMContinuationTarget
    (h : ConcreteNavierStokesMillenniumTarget) :
    ExplicitBKMContinuationTarget := by
  exact ExplicitConcreteNavierStokesMillenniumTarget_implies_BKMContinuationTarget
    (ConcreteNavierStokesMillenniumTarget_implies_ExplicitConcreteNavierStokesMillenniumTarget
      h)

/-- Likewise for the structured unrepaired whole-space theorem surface as a
fixed-datum all-horizons family of unrepaired BKM clauses. -/
theorem ConcreteNavierStokesMillenniumTarget_implies_BKMContinuationClause_allHorizons
    (h : ConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ T : ℝ, ExplicitBKMContinuationClause ν u₀ T := by
  exact
    ExplicitConcreteNavierStokesMillenniumTarget_implies_BKMContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀)
      (ConcreteNavierStokesMillenniumTarget_implies_ExplicitConcreteNavierStokesMillenniumTarget
        h)

/-- Likewise for the structured unrepaired whole-space theorem surface at a
fixed horizon. -/
theorem ConcreteNavierStokesMillenniumTarget_implies_BKMContinuationClause
    (h : ConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitBKMContinuationClause ν u₀ T := by
  exact
    (ConcreteNavierStokesMillenniumTarget_implies_BKMContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) h) T


end BKMContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
