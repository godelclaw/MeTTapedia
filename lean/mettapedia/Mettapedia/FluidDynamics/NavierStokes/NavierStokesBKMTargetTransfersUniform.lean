import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMTargetTransfersMillennium
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityClauseTransfers

/-!
# BKM-to-Uniform-Vorticity Target Transfers

This module transfers BKM continuation targets and Millennium surfaces into uniform-vorticity continuation targets and clauses.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section BKMContinuation

/-- Clause-level bridge: a BKM-style continuation clause at horizon `T` implies
the uniform-vorticity continuation clause at the same horizon. -/
theorem ExplicitBKMContinuationClause_implies_uniformVorticityContinuationClause
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hClause : ExplicitBKMContinuationClause ν u₀ T) :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  intro hν hsmooth hdiv W hω
  rcases hω with ⟨B, hbound⟩
  have hEnv :
      ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
        vorticityEnvelopeOn W.velocity T Ω ∧
          integrableVorticityEnvelopeOn Ω T Bint := by
    exact uniformVorticityBoundUpTo_implies_BKMEnvelope (u := W.velocity) (T := T) (B := B) hbound
  exact hClause hν hsmooth hdiv W hEnv

/-- Since the unrepaired uniform-vorticity clause already implies its repaired
finite-energy version, the unrepaired BKM clause also lands directly on the
repaired uniform surface at the same horizon. -/
theorem ExplicitBKMContinuationClause_implies_finiteEnergyUniformVorticityContinuationClause
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hClause : ExplicitBKMContinuationClause ν u₀ T) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitUniformVorticityContinuationClause_implies_finiteEnergy
      (ExplicitBKMContinuationClause_implies_uniformVorticityContinuationClause hClause)

/-- The unrepaired BKM clause on a smaller slab also yields the repaired
uniform clause on any larger slab: first pass to the repaired uniform clause on
the smaller slab, then restrict larger-slab witnesses back down. -/
theorem ExplicitBKMContinuationClause_implies_finiteEnergyUniformVorticityContinuationClause_mono_horizon
    {ν : ℝ} {u₀ : NSInitialVelocity} {Tsmall Tlarge : ℝ}
    (hClause : ExplicitBKMContinuationClause ν u₀ Tsmall)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ Tlarge := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_mono_horizon
      (ExplicitBKMContinuationClause_implies_finiteEnergyUniformVorticityContinuationClause
        hClause) hT

/-- The same bridge also holds on the repaired finite-energy continuation
surface.  No new analytic work is needed: the repaired BKM clause simply
forgets no information on actual witnesses, because a BKM envelope still
converts directly into a uniform-vorticity bound on the same slab. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_implies_finiteEnergyUniformVorticityContinuationClause
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hClause : ExplicitFiniteEnergyBKMContinuationClause ν u₀ T) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  intro hν hsmooth hdiv hfinite W hω
  rcases hω with ⟨B, hbound⟩
  have hEnv :
      ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
        vorticityEnvelopeOn W.velocity T Ω ∧
          integrableVorticityEnvelopeOn Ω T Bint := by
    exact uniformVorticityBoundUpTo_implies_BKMEnvelope (u := W.velocity) (T := T) (B := B) hbound
  exact hClause hν hsmooth hdiv hfinite W hEnv

/-- Likewise, a repaired BKM clause on a smaller slab yields the repaired
uniform clause on any larger slab via witness restriction. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_implies_finiteEnergyUniformVorticityContinuationClause_mono_horizon
    {ν : ℝ} {u₀ : NSInitialVelocity} {Tsmall Tlarge : ℝ}
    (hClause : ExplicitFiniteEnergyBKMContinuationClause ν u₀ Tsmall)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ Tlarge := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_mono_horizon
      (ExplicitFiniteEnergyBKMContinuationClause_implies_finiteEnergyUniformVorticityContinuationClause
        hClause) hT

/-- Therefore the unrepaired BKM target also implies the repaired
uniform-vorticity continuation target. -/
theorem ExplicitBKMContinuationTarget_implies_finiteEnergyUniformVorticityContinuationTarget
    (hBKM : ExplicitBKMContinuationTarget) :
    ExplicitFiniteEnergyUniformVorticityContinuationTarget := by
  intro ν u₀ T
  exact
    ExplicitFiniteEnergyBKMContinuationClause_implies_finiteEnergyUniformVorticityContinuationClause
      (ExplicitBKMContinuationTarget_implies_finiteEnergyBKMContinuationTarget hBKM ν u₀ T)

/-- The unrepaired BKM target also exports the whole fixed-datum family of
repaired uniform-vorticity continuation clauses. -/
theorem ExplicitBKMContinuationTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons
    (hBKM : ExplicitBKMContinuationTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ T : ℝ, ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  intro T
  exact
    ExplicitFiniteEnergyBKMContinuationClause_implies_finiteEnergyUniformVorticityContinuationClause
      (ExplicitBKMContinuationTarget_implies_finiteEnergyBKMContinuationTarget hBKM ν u₀ T)

/-- Hence the unrepaired BKM target also implies the repaired uniform clause at
each fixed horizon directly. -/
theorem ExplicitBKMContinuationTarget_implies_finiteEnergyUniformVorticityContinuationClause
    (hBKM : ExplicitBKMContinuationTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    (ExplicitBKMContinuationTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) hBKM) T

/-- Therefore the repaired BKM target implies the repaired uniform-vorticity
target. -/
theorem ExplicitFiniteEnergyBKMContinuationTarget_implies_finiteEnergyUniformVorticityContinuationTarget
    (hBKM : ExplicitFiniteEnergyBKMContinuationTarget) :
    ExplicitFiniteEnergyUniformVorticityContinuationTarget := by
  intro ν u₀ T
  exact
    ExplicitFiniteEnergyBKMContinuationClause_implies_finiteEnergyUniformVorticityContinuationClause
      (hClause := hBKM ν u₀ T)

/-- The repaired BKM target also exports the whole fixed-datum family of
repaired uniform-vorticity continuation clauses. -/
theorem ExplicitFiniteEnergyBKMContinuationTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons
    (hBKM : ExplicitFiniteEnergyBKMContinuationTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ T : ℝ, ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  intro T
  exact
    ExplicitFiniteEnergyBKMContinuationClause_implies_finiteEnergyUniformVorticityContinuationClause
      (hClause := hBKM ν u₀ T)

/-- Hence the repaired BKM target implies the repaired uniform clause at each
fixed horizon directly. -/
theorem ExplicitFiniteEnergyBKMContinuationTarget_implies_finiteEnergyUniformVorticityContinuationClause
    (hBKM : ExplicitFiniteEnergyBKMContinuationTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    (ExplicitFiniteEnergyBKMContinuationTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) hBKM) T

/-- On a nonnegative slab, the repaired BKM clause also implies the unrepaired
uniform-vorticity clause: once an actual witness exists, the repaired/unrepaired
uniform clauses coincide on that slab. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_implies_uniformVorticityContinuationClause_of_nonneg_horizon
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hClause : ExplicitFiniteEnergyBKMContinuationClause ν u₀ T)
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitBKMContinuationClause_implies_uniformVorticityContinuationClause
      (hClause :=
        ExplicitFiniteEnergyBKMContinuationClause_implies_BKMContinuationClause_of_nonneg_horizon
          hClause hT)

/-- Hence the repaired BKM target gives the unrepaired uniform-vorticity clause
on every fixed nonnegative horizon. -/
theorem ExplicitFiniteEnergyBKMContinuationTarget_implies_uniformVorticityContinuationClause_of_nonneg_horizon
    (hBKM : ExplicitFiniteEnergyBKMContinuationTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitBKMContinuationClause_implies_uniformVorticityContinuationClause
      (hClause :=
        ExplicitFiniteEnergyBKMContinuationTarget_implies_BKMContinuationClause_of_nonneg_horizon
          hBKM hT)

/-- The corrected nonnegative-horizon repaired BKM target gives the unrepaired
uniform-vorticity clause on every fixed nonnegative horizon. -/
theorem
    ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons_implies_uniformVorticityContinuationClause_of_nonneg_horizon
    (hBKM : ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitBKMContinuationClause_implies_uniformVorticityContinuationClause
      (hClause :=
        ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons_implies_BKMContinuationClause_of_nonneg_horizon
          hBKM hT)

/-- The repaired BKM target also gives the unrepaired uniform clause family on
every nonnegative horizon. -/
theorem ExplicitFiniteEnergyBKMContinuationTarget_implies_uniformVorticityContinuationClause_allNonnegHorizons
    (hBKM : ExplicitFiniteEnergyBKMContinuationTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ ⦃T : ℝ⦄, 0 ≤ T → ExplicitUniformVorticityContinuationClause ν u₀ T := by
  intro T hT
  exact
    ExplicitFiniteEnergyBKMContinuationTarget_implies_uniformVorticityContinuationClause_of_nonneg_horizon
      (ν := ν) (u₀ := u₀) (T := T) hBKM hT

/-- The corrected nonnegative-horizon repaired BKM target gives the unrepaired
uniform-vorticity clause family on every nonnegative horizon. -/
theorem
    ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons_implies_uniformVorticityContinuationClause_allNonnegHorizons
    (hBKM : ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ ⦃T : ℝ⦄, 0 ≤ T → ExplicitUniformVorticityContinuationClause ν u₀ T := by
  intro T hT
  exact
    ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons_implies_uniformVorticityContinuationClause_of_nonneg_horizon
      (ν := ν) (u₀ := u₀) (T := T) hBKM hT

/-- The BKM-style target implies the uniform-vorticity continuation target.
Unlike the global-theorem subsumption lemmas, this proof uses the continuation
hypothesis by converting a uniform slab bound into an explicit integrable
envelope. -/
theorem ExplicitBKMContinuationTarget_implies_uniformVorticityContinuationTarget
    (hBKM : ExplicitBKMContinuationTarget) :
    ExplicitUniformVorticityContinuationTarget := by
  intro ν u₀ T
  exact ExplicitBKMContinuationClause_implies_uniformVorticityContinuationClause
    (hClause := hBKM ν u₀ T)

/-- The unrepaired BKM target also exports the whole fixed-datum family of
unrepaired uniform-vorticity continuation clauses. -/
theorem ExplicitBKMContinuationTarget_implies_uniformVorticityContinuationClause_allHorizons
    (hBKM : ExplicitBKMContinuationTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ T : ℝ, ExplicitUniformVorticityContinuationClause ν u₀ T := by
  intro T
  exact ExplicitBKMContinuationClause_implies_uniformVorticityContinuationClause
    (hClause := hBKM ν u₀ T)

/-- Hence the unrepaired BKM target implies the unrepaired uniform clause at
each fixed horizon directly. -/
theorem ExplicitBKMContinuationTarget_implies_uniformVorticityContinuationClause
    (hBKM : ExplicitBKMContinuationTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    (ExplicitBKMContinuationTarget_implies_uniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) hBKM) T

/-- The unrepaired explicit whole-space theorem surface therefore also implies
the unrepaired uniform-vorticity continuation target through the BKM route. -/
theorem ExplicitConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationTarget_via_BKM
    (h : ExplicitConcreteNavierStokesMillenniumTarget) :
    ExplicitUniformVorticityContinuationTarget := by
  exact
    ExplicitBKMContinuationTarget_implies_uniformVorticityContinuationTarget
      (ExplicitConcreteNavierStokesMillenniumTarget_implies_BKMContinuationTarget h)

/-- The same unrepaired explicit theorem surface also exports the whole
fixed-datum family of unrepaired uniform clauses explicitly through the BKM
route. -/
theorem ExplicitConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_allHorizons_via_BKM
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ T : ℝ, ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitBKMContinuationTarget_implies_uniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀)
      (ExplicitConcreteNavierStokesMillenniumTarget_implies_BKMContinuationTarget h)

/-- Hence the same theorem surface reaches each fixed unrepaired uniform clause
directly through the BKM route. -/
theorem ExplicitConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_via_BKM
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    (ExplicitConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_allHorizons_via_BKM
      (ν := ν) (u₀ := u₀) h) T

/-- The same unrepaired explicit theorem surface also reaches the repaired
uniform-vorticity continuation target through the repaired BKM route. -/
theorem ExplicitConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationTarget_via_BKM
    (h : ExplicitConcreteNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyUniformVorticityContinuationTarget := by
  exact
    ExplicitBKMContinuationTarget_implies_finiteEnergyUniformVorticityContinuationTarget
      (ExplicitConcreteNavierStokesMillenniumTarget_implies_BKMContinuationTarget h)

/-- The same unrepaired explicit theorem surface also exports the whole
fixed-datum family of repaired uniform clauses through the repaired BKM route. -/
theorem ExplicitConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons_via_BKM
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ T : ℝ, ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitBKMContinuationTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀)
      (ExplicitConcreteNavierStokesMillenniumTarget_implies_BKMContinuationTarget h)

/-- Hence the same theorem surface reaches each fixed repaired uniform clause
directly through the BKM route. -/
theorem ExplicitConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_via_BKM
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    (ExplicitConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons_via_BKM
      (ν := ν) (u₀ := u₀) h) T

/-- The repaired explicit finite-energy theorem surface reaches the repaired
uniform-vorticity continuation target through the repaired BKM target. -/
theorem
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationTarget_via_BKM
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyUniformVorticityContinuationTarget := by
  exact
    ExplicitFiniteEnergyBKMContinuationTarget_implies_finiteEnergyUniformVorticityContinuationTarget
      (ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationTarget
        h)

/-- The repaired explicit finite-energy theorem surface also exports the whole
fixed-datum family of repaired uniform clauses through the repaired BKM route. -/
theorem
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons_via_BKM
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ T : ℝ, ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyBKMContinuationTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀)
      (ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationTarget
        h)

/-- Hence the repaired explicit theorem surface reaches each fixed repaired
uniform clause directly through the same BKM route. -/
theorem
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_via_BKM
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    (ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons_via_BKM
      (ν := ν) (u₀ := u₀) h) T

/-- Likewise for the structured repaired finite-energy theorem surface. -/
theorem FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationTarget_via_BKM
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyUniformVorticityContinuationTarget := by
  exact
    ExplicitFiniteEnergyBKMContinuationTarget_implies_finiteEnergyUniformVorticityContinuationTarget
      (FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationTarget h)

/-- Likewise for the structured repaired theorem surface as a fixed-datum
all-horizons family of repaired uniform clauses through the BKM route. -/
theorem FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons_via_BKM
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ T : ℝ, ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyBKMContinuationTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀)
      (FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationTarget h)

/-- Likewise for the structured repaired theorem surface at each fixed horizon
through the BKM route. -/
theorem FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_via_BKM
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    (FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons_via_BKM
      (ν := ν) (u₀ := u₀) h) T

/-- Likewise for the structured unrepaired whole-space theorem surface on the
unrepaired uniform target. -/
theorem ConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationTarget_via_BKM
    (h : ConcreteNavierStokesMillenniumTarget) :
    ExplicitUniformVorticityContinuationTarget := by
  exact
    ExplicitBKMContinuationTarget_implies_uniformVorticityContinuationTarget
      (ConcreteNavierStokesMillenniumTarget_implies_BKMContinuationTarget h)

/-- Likewise for the structured unrepaired theorem surface as a fixed-datum
all-horizons family of unrepaired uniform clauses through the BKM route. -/
theorem ConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_allHorizons_via_BKM
    (h : ConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ T : ℝ, ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitBKMContinuationTarget_implies_uniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀)
      (ConcreteNavierStokesMillenniumTarget_implies_BKMContinuationTarget h)

/-- Likewise for the structured unrepaired theorem surface at each fixed
unrepaired uniform horizon through the BKM route. -/
theorem ConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_via_BKM
    (h : ConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    (ConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_allHorizons_via_BKM
      (ν := ν) (u₀ := u₀) h) T

/-- Likewise for the structured unrepaired whole-space theorem surface on the
repaired uniform target. -/
theorem ConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationTarget_via_BKM
    (h : ConcreteNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyUniformVorticityContinuationTarget := by
  exact
    ExplicitBKMContinuationTarget_implies_finiteEnergyUniformVorticityContinuationTarget
      (ConcreteNavierStokesMillenniumTarget_implies_BKMContinuationTarget h)

/-- Likewise for the structured unrepaired theorem surface as a fixed-datum
all-horizons family of repaired uniform clauses through the BKM route. -/
theorem ConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons_via_BKM
    (h : ConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ T : ℝ, ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitBKMContinuationTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀)
      (ConcreteNavierStokesMillenniumTarget_implies_BKMContinuationTarget h)

/-- Likewise for the structured unrepaired theorem surface at each fixed
repaired uniform horizon through the BKM route. -/
theorem ConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_via_BKM
    (h : ConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    (ConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons_via_BKM
      (ν := ν) (u₀ := u₀) h) T

/-- The repaired explicit finite-energy theorem surface also exports the
unrepaired uniform clause family on every nonnegative horizon through the
repaired BKM target. -/
theorem
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_allNonnegHorizons_via_BKM
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ ⦃T : ℝ⦄, 0 ≤ T → ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyBKMContinuationTarget_implies_uniformVorticityContinuationClause_allNonnegHorizons
      (ν := ν) (u₀ := u₀)
      (ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationTarget
        h)

/-- Hence the repaired explicit finite-energy theorem surface reaches the
unrepaired uniform clause at each fixed nonnegative horizon through the same
BKM route. -/
theorem
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_of_nonneg_horizon_via_BKM
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_allNonnegHorizons_via_BKM
      (ν := ν) (u₀ := u₀) h hT

/-- Likewise for the structured repaired finite-energy theorem surface. -/
theorem FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_allNonnegHorizons_via_BKM
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ ⦃T : ℝ⦄, 0 ≤ T → ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyBKMContinuationTarget_implies_uniformVorticityContinuationClause_allNonnegHorizons
      (ν := ν) (u₀ := u₀)
      (FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationTarget h)

/-- Likewise for the structured repaired finite-energy theorem surface at each
fixed nonnegative horizon. -/
theorem FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_of_nonneg_horizon_via_BKM
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_allNonnegHorizons_via_BKM
      (ν := ν) (u₀ := u₀) h hT

end BKMContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
