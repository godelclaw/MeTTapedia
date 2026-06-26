import Mettapedia.FluidDynamics.NavierStokes.ContinuationRegressionTargetTransfersPart1

/-!
# Continuation target transfer, BKM/uniform, repaired/unrepaired, and zero-output regression checks.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace ContinuationRegression


theorem repaired_uniform_clause_iff_unrepaired_of_nonneg_horizon_regression
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T ↔
      ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact ExplicitFiniteEnergyUniformVorticityContinuationClause_iff_of_nonneg_horizon hT

theorem repaired_uniform_clause_unrepaired_uniform_clause_of_nonneg_horizon_regression
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (h : ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T)
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_implies_uniformVorticityContinuationClause_of_nonneg_horizon
      h hT

theorem repaired_uniform_target_unrepaired_uniform_clause_of_nonneg_horizon_regression
    (h : ExplicitFiniteEnergyUniformVorticityContinuationTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationTarget_implies_uniformVorticityContinuationClause_of_nonneg_horizon
      h hT

theorem repaired_uniform_target_unrepaired_uniform_allNonnegHorizons_regression
    (h : ExplicitFiniteEnergyUniformVorticityContinuationTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationTarget_implies_uniformVorticityContinuationClause_allNonnegHorizons
      (ν := ν) (u₀ := u₀) h hT

theorem repaired_uniform_clause_mono_horizon_regression
    {ν : ℝ} {u₀ : NSInitialVelocity} {Tsmall Tlarge : ℝ}
    (h : ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ Tsmall)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ Tlarge := by
  exact ExplicitFiniteEnergyUniformVorticityContinuationClause_mono_horizon h hT

theorem repaired_BKM_clause_iff_unrepaired_of_nonneg_horizon_regression
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitFiniteEnergyBKMContinuationClause ν u₀ T ↔
      ExplicitBKMContinuationClause ν u₀ T := by
  exact ExplicitFiniteEnergyBKMContinuationClause_iff_of_nonneg_horizon hT

theorem repaired_BKM_clause_mono_horizon_regression
    {ν : ℝ} {u₀ : NSInitialVelocity} {Tsmall Tlarge : ℝ}
    (h : ExplicitFiniteEnergyBKMContinuationClause ν u₀ Tsmall)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitFiniteEnergyBKMContinuationClause ν u₀ Tlarge := by
  exact ExplicitFiniteEnergyBKMContinuationClause_mono_horizon h hT

theorem BKM_clause_repaired_uniform_clause_regression
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (h : ExplicitBKMContinuationClause ν u₀ T) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitBKMContinuationClause_implies_finiteEnergyUniformVorticityContinuationClause h

theorem BKM_clause_repaired_uniform_clause_mono_horizon_regression
    {ν : ℝ} {u₀ : NSInitialVelocity} {Tsmall Tlarge : ℝ}
    (h : ExplicitBKMContinuationClause ν u₀ Tsmall)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ Tlarge := by
  exact
    ExplicitBKMContinuationClause_implies_finiteEnergyUniformVorticityContinuationClause_mono_horizon
      h hT

theorem repaired_BKM_clause_repaired_uniform_clause_mono_horizon_regression
    {ν : ℝ} {u₀ : NSInitialVelocity} {Tsmall Tlarge : ℝ}
    (h : ExplicitFiniteEnergyBKMContinuationClause ν u₀ Tsmall)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ Tlarge := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_implies_finiteEnergyUniformVorticityContinuationClause_mono_horizon
      h hT

theorem BKM_target_uniform_target_regression
    (h : ExplicitBKMContinuationTarget) :
    ExplicitUniformVorticityContinuationTarget := by
  exact ExplicitBKMContinuationTarget_implies_uniformVorticityContinuationTarget h

theorem BKM_target_uniform_allHorizons_regression
    (h : ExplicitBKMContinuationTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    (ExplicitBKMContinuationTarget_implies_uniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) h) T

theorem BKM_target_repaired_uniform_target_regression
    (h : ExplicitBKMContinuationTarget) :
    ExplicitFiniteEnergyUniformVorticityContinuationTarget := by
  exact ExplicitBKMContinuationTarget_implies_finiteEnergyUniformVorticityContinuationTarget h

theorem BKM_target_repaired_uniform_allHorizons_regression
    (h : ExplicitBKMContinuationTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    (ExplicitBKMContinuationTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) h) T

theorem repaired_BKM_target_uniform_target_regression
    (h : ExplicitFiniteEnergyBKMContinuationTarget) :
    ExplicitFiniteEnergyUniformVorticityContinuationTarget := by
  exact ExplicitFiniteEnergyBKMContinuationTarget_implies_finiteEnergyUniformVorticityContinuationTarget h

theorem repaired_BKM_target_repaired_uniform_allHorizons_regression
    (h : ExplicitFiniteEnergyBKMContinuationTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    (ExplicitFiniteEnergyBKMContinuationTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) h) T

theorem explicit_target_uniform_target_via_BKM_regression
    (h : ExplicitConcreteNavierStokesMillenniumTarget) :
    ExplicitUniformVorticityContinuationTarget := by
  exact
    ExplicitConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationTarget_via_BKM
      h

theorem explicit_target_repaired_uniform_target_via_BKM_regression
    (h : ExplicitConcreteNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyUniformVorticityContinuationTarget := by
  exact
    ExplicitConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationTarget_via_BKM
      h

theorem explicit_repaired_target_repaired_uniform_target_via_BKM_regression
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyUniformVorticityContinuationTarget := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationTarget_via_BKM
      h

theorem concrete_repaired_target_repaired_uniform_target_via_BKM_regression
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyUniformVorticityContinuationTarget := by
  exact
    FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationTarget_via_BKM
      h

theorem concrete_target_uniform_target_via_BKM_regression
    (h : ConcreteNavierStokesMillenniumTarget) :
    ExplicitUniformVorticityContinuationTarget := by
  exact
    ConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationTarget_via_BKM
      h

theorem concrete_target_repaired_uniform_target_via_BKM_regression
    (h : ConcreteNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyUniformVorticityContinuationTarget := by
  exact
    ConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationTarget_via_BKM
      h

theorem explicit_target_uniform_allHorizons_via_BKM_regression
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    (ExplicitConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_allHorizons_via_BKM
      (ν := ν) (u₀ := u₀) h) T

theorem explicit_target_repaired_uniform_allHorizons_via_BKM_regression
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    (ExplicitConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons_via_BKM
      (ν := ν) (u₀ := u₀) h) T

theorem explicit_repaired_target_repaired_uniform_allHorizons_via_BKM_regression
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    (ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons_via_BKM
      (ν := ν) (u₀ := u₀) h) T

theorem concrete_repaired_target_repaired_uniform_allHorizons_via_BKM_regression
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    (FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons_via_BKM
      (ν := ν) (u₀ := u₀) h) T

theorem concrete_target_uniform_allHorizons_via_BKM_regression
    (h : ConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    (ConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_allHorizons_via_BKM
      (ν := ν) (u₀ := u₀) h) T

theorem concrete_target_repaired_uniform_allHorizons_via_BKM_regression
    (h : ConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    (ConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons_via_BKM
      (ν := ν) (u₀ := u₀) h) T

theorem repaired_BKM_clause_unrepaired_BKM_clause_of_nonneg_horizon_regression
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (h : ExplicitFiniteEnergyBKMContinuationClause ν u₀ T)
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_implies_BKMContinuationClause_of_nonneg_horizon
      h hT

theorem repaired_BKM_target_unrepaired_BKM_clause_of_nonneg_horizon_regression
    (h : ExplicitFiniteEnergyBKMContinuationTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyBKMContinuationTarget_implies_BKMContinuationClause_of_nonneg_horizon
      h hT

theorem repaired_BKM_target_unrepaired_BKM_allNonnegHorizons_regression
    (h : ExplicitFiniteEnergyBKMContinuationTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyBKMContinuationTarget_implies_BKMContinuationClause_allNonnegHorizons
      (ν := ν) (u₀ := u₀) h hT

theorem repaired_BKM_clause_uniform_clause_of_nonneg_horizon_regression
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (h : ExplicitFiniteEnergyBKMContinuationClause ν u₀ T)
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_implies_uniformVorticityContinuationClause_of_nonneg_horizon
      h hT

theorem repaired_BKM_target_uniform_clause_of_nonneg_horizon_regression
    (h : ExplicitFiniteEnergyBKMContinuationTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyBKMContinuationTarget_implies_uniformVorticityContinuationClause_of_nonneg_horizon
      h hT

theorem repaired_BKM_target_uniform_allNonnegHorizons_regression
    (h : ExplicitFiniteEnergyBKMContinuationTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyBKMContinuationTarget_implies_uniformVorticityContinuationClause_allNonnegHorizons
      (ν := ν) (u₀ := u₀) h hT

theorem explicit_repaired_target_uniform_clause_of_nonneg_horizon_regression
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_of_nonneg_horizon
      h hT

theorem explicit_repaired_target_uniform_allNonnegHorizons_regression
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_allNonnegHorizons
      (ν := ν) (u₀ := u₀) h hT

theorem concrete_repaired_target_uniform_clause_of_nonneg_horizon_regression
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_of_nonneg_horizon
      h hT

theorem concrete_repaired_target_uniform_allNonnegHorizons_regression
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_allNonnegHorizons
      (ν := ν) (u₀ := u₀) h hT

theorem explicit_repaired_target_uniform_clause_of_nonneg_horizon_via_BKM_regression
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_of_nonneg_horizon_via_BKM
      (ν := ν) (u₀ := u₀) h hT

theorem explicit_repaired_target_uniform_allNonnegHorizons_via_BKM_regression
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_allNonnegHorizons_via_BKM
      (ν := ν) (u₀ := u₀) h hT

theorem concrete_repaired_target_uniform_clause_of_nonneg_horizon_via_BKM_regression
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_of_nonneg_horizon_via_BKM
      (ν := ν) (u₀ := u₀) h hT

theorem concrete_repaired_target_uniform_allNonnegHorizons_via_BKM_regression
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_allNonnegHorizons_via_BKM
      (ν := ν) (u₀ := u₀) h hT

theorem explicit_repaired_target_BKM_clause_of_nonneg_horizon_regression
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_BKMContinuationClause_of_nonneg_horizon
      h hT

theorem explicit_repaired_target_BKM_allNonnegHorizons_regression
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_BKMContinuationClause_allNonnegHorizons
      (ν := ν) (u₀ := u₀) h hT

theorem concrete_repaired_target_BKM_clause_of_nonneg_horizon_regression
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν u₀ T := by
  exact
    FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_BKMContinuationClause_of_nonneg_horizon
      h hT

theorem concrete_repaired_target_BKM_allNonnegHorizons_regression
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν u₀ T := by
  exact
    FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_BKMContinuationClause_allNonnegHorizons
      (ν := ν) (u₀ := u₀) h hT

theorem uniform_clause_zero_output_regression
    {ν T : ℝ}
    (h : ExplicitUniformVorticityContinuationClause ν (0 : NSInitialVelocity) T)
    (hν : 0 < ν) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact ExplicitUniformVorticityContinuationClause_implies_zeroGlobalOutput h hν

theorem uniform_clause_zero_output_timeOnlyPressure_regression
    {ν Tsmall Tlarge : ℝ}
    (h : ExplicitUniformVorticityContinuationClause ν (0 : NSInitialVelocity) Tsmall)
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact ExplicitUniformVorticityContinuationClause_implies_zeroGlobalOutput_timeOnlyPressure
    (Tsmall := Tsmall) (Tlarge := Tlarge) h hν π hπ hT

theorem uniform_clause_zero_output_constantPressure_regression
    {ν T : ℝ}
    (h : ExplicitUniformVorticityContinuationClause ν (0 : NSInitialVelocity) T)
    (hν : 0 < ν)
    (c : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact ExplicitUniformVorticityContinuationClause_implies_zeroGlobalOutput_constantPressure
    (T := T) h hν c

theorem repaired_uniform_clause_zero_output_regression
    {ν T : ℝ}
    (h : ExplicitFiniteEnergyUniformVorticityContinuationClause ν (0 : NSInitialVelocity) T)
    (hν : 0 < ν) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact ExplicitFiniteEnergyUniformVorticityContinuationClause_implies_zeroGlobalOutput h hν

theorem repaired_uniform_clause_zero_output_timeOnlyPressure_regression
    {ν Tsmall Tlarge : ℝ}
    (h : ExplicitFiniteEnergyUniformVorticityContinuationClause ν (0 : NSInitialVelocity) Tsmall)
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_implies_zeroGlobalOutput_timeOnlyPressure
      (Tsmall := Tsmall) (Tlarge := Tlarge) h hν π hπ hT

theorem repaired_uniform_clause_zero_output_constantPressure_regression
    {ν T : ℝ}
    (h : ExplicitFiniteEnergyUniformVorticityContinuationClause ν (0 : NSInitialVelocity) T)
    (hν : 0 < ν)
    (c : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact ExplicitFiniteEnergyUniformVorticityContinuationClause_implies_zeroGlobalOutput_constantPressure
    (T := T) h hν c

theorem BKM_clause_zero_output_regression
    {ν T : ℝ}
    (h : ExplicitBKMContinuationClause ν (0 : NSInitialVelocity) T)
    (hν : 0 < ν) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact ExplicitBKMContinuationClause_implies_zeroGlobalOutput h hν

theorem BKM_clause_zero_output_timeOnlyPressure_regression
    {ν Tsmall Tlarge : ℝ}
    (h : ExplicitBKMContinuationClause ν (0 : NSInitialVelocity) Tsmall)
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact ExplicitBKMContinuationClause_implies_zeroGlobalOutput_timeOnlyPressure
    (Tsmall := Tsmall) (Tlarge := Tlarge) h hν π hπ hT

theorem BKM_clause_zero_output_constantPressure_regression
    {ν T : ℝ}
    (h : ExplicitBKMContinuationClause ν (0 : NSInitialVelocity) T)
    (hν : 0 < ν)
    (c : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact ExplicitBKMContinuationClause_implies_zeroGlobalOutput_constantPressure
    (T := T) h hν c

theorem repaired_BKM_clause_zero_output_regression
    {ν T : ℝ}
    (h : ExplicitFiniteEnergyBKMContinuationClause ν (0 : NSInitialVelocity) T)
    (hν : 0 < ν) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact ExplicitFiniteEnergyBKMContinuationClause_implies_zeroGlobalOutput h hν

theorem repaired_BKM_clause_zero_output_timeOnlyPressure_regression
    {ν Tsmall Tlarge : ℝ}
    (h : ExplicitFiniteEnergyBKMContinuationClause ν (0 : NSInitialVelocity) Tsmall)
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact ExplicitFiniteEnergyBKMContinuationClause_implies_zeroGlobalOutput_timeOnlyPressure
    (Tsmall := Tsmall) (Tlarge := Tlarge) h hν π hπ hT

theorem repaired_BKM_clause_zero_output_constantPressure_regression
    {ν T : ℝ}
    (h : ExplicitFiniteEnergyBKMContinuationClause ν (0 : NSInitialVelocity) T)
    (hν : 0 < ν)
    (c : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact ExplicitFiniteEnergyBKMContinuationClause_implies_zeroGlobalOutput_constantPressure
    (T := T) h hν c

theorem uniform_target_zero_output_regression
    (h : ExplicitUniformVorticityContinuationTarget)
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact ExplicitUniformVorticityContinuationTarget_implies_zeroGlobalOutput
    (T := T) h hν

theorem uniform_target_zero_output_timeOnlyPressure_regression
    (h : ExplicitUniformVorticityContinuationTarget)
    {ν Tsmall Tlarge : ℝ}
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitUniformVorticityContinuationTarget_implies_zeroGlobalOutput_timeOnlyPressure
      (Tsmall := Tsmall) (Tlarge := Tlarge) h hν π hπ hT

theorem uniform_target_zero_output_constantPressure_regression
    (h : ExplicitUniformVorticityContinuationTarget)
    {ν T : ℝ} (hν : 0 < ν) (c : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact ExplicitUniformVorticityContinuationTarget_implies_zeroGlobalOutput_constantPressure
    (T := T) h hν c

theorem repaired_uniform_target_zero_output_regression
    (h : ExplicitFiniteEnergyUniformVorticityContinuationTarget)
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact ExplicitFiniteEnergyUniformVorticityContinuationTarget_implies_zeroGlobalOutput
    (T := T) h hν

theorem repaired_uniform_target_zero_output_constantPressure_regression
    (h : ExplicitFiniteEnergyUniformVorticityContinuationTarget)
    {ν T : ℝ} (hν : 0 < ν) (c : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationTarget_implies_zeroGlobalOutput_constantPressure
      (T := T) h hν c

theorem repaired_uniform_target_zero_output_timeOnlyPressure_regression
    (h : ExplicitFiniteEnergyUniformVorticityContinuationTarget)
    {ν Tsmall Tlarge : ℝ}
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationTarget_implies_zeroGlobalOutput_timeOnlyPressure
      (Tsmall := Tsmall) (Tlarge := Tlarge) h hν π hπ hT

theorem BKM_target_zero_output_timeOnlyPressure_regression
    (h : ExplicitBKMContinuationTarget)
    {ν Tsmall Tlarge : ℝ}
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitBKMContinuationTarget_implies_zeroGlobalOutput_timeOnlyPressure
      (Tsmall := Tsmall) (Tlarge := Tlarge) h hν π hπ hT

theorem BKM_target_zero_output_regression
    (h : ExplicitBKMContinuationTarget)
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact ExplicitBKMContinuationTarget_implies_zeroGlobalOutput
    (T := T) h hν

theorem BKM_target_zero_output_constantPressure_regression
    (h : ExplicitBKMContinuationTarget)
    {ν T : ℝ} (hν : 0 < ν) (c : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact ExplicitBKMContinuationTarget_implies_zeroGlobalOutput_constantPressure
    (T := T) h hν c

theorem repaired_BKM_target_zero_output_constantPressure_regression
    (h : ExplicitFiniteEnergyBKMContinuationTarget)
    {ν T : ℝ} (hν : 0 < ν) (c : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact ExplicitFiniteEnergyBKMContinuationTarget_implies_zeroGlobalOutput_constantPressure
    (T := T) h hν c

theorem repaired_BKM_target_zero_output_regression
    (h : ExplicitFiniteEnergyBKMContinuationTarget)
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact ExplicitFiniteEnergyBKMContinuationTarget_implies_zeroGlobalOutput
    (T := T) h hν

theorem repaired_BKM_target_zero_output_timeOnlyPressure_regression
    (h : ExplicitFiniteEnergyBKMContinuationTarget)
    {ν Tsmall Tlarge : ℝ}
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitFiniteEnergyBKMContinuationTarget_implies_zeroGlobalOutput_timeOnlyPressure
      (Tsmall := Tsmall) (Tlarge := Tlarge) h hν π hπ hT

end ContinuationRegression
end NavierStokes
end FluidDynamics
end Mettapedia
