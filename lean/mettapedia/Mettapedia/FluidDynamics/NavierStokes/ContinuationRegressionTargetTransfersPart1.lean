import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMZeroOutput
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEquationComponentBridge
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEquationEquivalences
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityTargetSurfaceTransfers
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityTargetZeroOutputTransfers

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


theorem repaired_regularity_implies_unrepaired_of_finiteInitialKineticEnergy_regression
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause ν u₀)
    (hfinite : finiteInitialKineticEnergy u₀) :
    ExplicitConcreteNavierStokesRegularityClause ν u₀ := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_implies_ExplicitConcreteNavierStokesRegularityClause_of_finiteInitialKineticEnergy
      h hfinite

theorem repaired_concrete_clause_iff_regression
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (hfinite : finiteInitialKineticEnergy u₀) :
    NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        ({ viscosity := ν
           viscosity_pos := hν
           initialVelocity := u₀
           smooth_initial := hsmooth
           divergence_free_initial := hdiv
           finite_initial_energy := hfinite } :
          FiniteEnergyAdmissibleNavierStokesProblemData).toNavierStokesProblemData
      ↔
        ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause ν u₀ := by
  exact finiteEnergyConcreteNavierStokesGlobalRegularityClause_iff hν hsmooth hdiv hfinite

theorem repaired_unrepaired_concrete_clause_iff_of_finiteInitialKineticEnergy_regression
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (hfinite : finiteInitialKineticEnergy u₀) :
    NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        ({ viscosity := ν
           viscosity_pos := hν
           initialVelocity := u₀
           smooth_initial := hsmooth
           divergence_free_initial := hdiv
           finite_initial_energy := hfinite } :
          FiniteEnergyAdmissibleNavierStokesProblemData).toNavierStokesProblemData
      ↔
        NavierStokesGlobalRegularityClause
          mkFullyConcreteNavierStokesSurface
          { viscosity := ν
            viscosity_pos := hν
            initialVelocity := u₀
            smooth_initial := hsmooth
            divergence_free_initial := hdiv } := by
  exact
    finiteEnergyConcreteNavierStokesGlobalRegularityClause_iff_of_finiteInitialKineticEnergy
      hν hsmooth hdiv hfinite

theorem repaired_concrete_clause_implies_unrepaired_of_finiteInitialKineticEnergy_regression
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (hfinite : finiteInitialKineticEnergy u₀)
    (h :
      NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        ({ viscosity := ν
           viscosity_pos := hν
           initialVelocity := u₀
           smooth_initial := hsmooth
           divergence_free_initial := hdiv
           finite_initial_energy := hfinite } :
          FiniteEnergyAdmissibleNavierStokesProblemData).toNavierStokesProblemData) :
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      { viscosity := ν
        viscosity_pos := hν
        initialVelocity := u₀
        smooth_initial := hsmooth
        divergence_free_initial := hdiv } := by
  exact
    finiteEnergyConcreteNavierStokesGlobalRegularityClause_implies_concreteNavierStokesGlobalRegularityClause_of_finiteInitialKineticEnergy
      hν hsmooth hdiv hfinite h

theorem unrepaired_concrete_clause_implies_repaired_of_finiteInitialKineticEnergy_regression
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (hfinite : finiteInitialKineticEnergy u₀)
    (h :
      NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := u₀
          smooth_initial := hsmooth
          divergence_free_initial := hdiv }) :
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      ({ viscosity := ν
         viscosity_pos := hν
         initialVelocity := u₀
         smooth_initial := hsmooth
         divergence_free_initial := hdiv
         finite_initial_energy := hfinite } :
        FiniteEnergyAdmissibleNavierStokesProblemData).toNavierStokesProblemData := by
  exact
    concreteNavierStokesGlobalRegularityClause_implies_finiteEnergyConcreteNavierStokesGlobalRegularityClause_of_finiteInitialKineticEnergy
      hν hsmooth hdiv hfinite h

theorem explicit_target_implies_finiteEnergy_regression
    (h : ExplicitConcreteNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget := by
  exact ExplicitConcreteNavierStokesMillenniumTarget_implies_finiteEnergy h

theorem concrete_target_iff_explicit_regression :
    ConcreteNavierStokesMillenniumTarget ↔ ExplicitConcreteNavierStokesMillenniumTarget := by
  exact ConcreteNavierStokesMillenniumTarget_iff_explicit

theorem repaired_concrete_target_iff_explicit_regression :
    FiniteEnergyConcreteNavierStokesMillenniumTarget ↔
      ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget := by
  exact FiniteEnergyConcreteNavierStokesMillenniumTarget_iff_explicit

theorem concrete_target_implies_explicit_regression
    (h : ConcreteNavierStokesMillenniumTarget) :
    ExplicitConcreteNavierStokesMillenniumTarget := by
  exact
    ConcreteNavierStokesMillenniumTarget_implies_ExplicitConcreteNavierStokesMillenniumTarget
      h

theorem repaired_concrete_target_implies_explicit_regression
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget := by
  exact
    FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget
      h

theorem concrete_target_implies_repaired_explicit_regression
    (h : ConcreteNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget := by
  exact
    ConcreteNavierStokesMillenniumTarget_implies_ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget
      h

theorem concrete_target_implies_finiteEnergy_regression
    (h : ConcreteNavierStokesMillenniumTarget) :
    FiniteEnergyConcreteNavierStokesMillenniumTarget := by
  exact ConcreteNavierStokesMillenniumTarget_implies_finiteEnergy h

theorem witness_component_shadow_regression
    {D : NavierStokesDifferentialKit} {P : NavierStokesProblemData D}
    (W : NavierStokesGlobalRegularityWitness D P)
    (i : Fin 3) :
    Nonempty (FeffermanGlobalRegularityOutput (D.toComponentPredicateKit P i)) := by
  exact ⟨W.toComponentFeffermanOutput i⟩

theorem clause_component_shadow_regression
    {D : NavierStokesDifferentialKit} {P : NavierStokesProblemData D}
    (h : NavierStokesGlobalRegularityClause D P)
    (i : Fin 3) :
    FeffermanGlobalRegularityClause (D.toComponentPredicateKit P i) := by
  exact NavierStokesGlobalRegularityClause.implies_componentFeffermanClause h i

theorem target_component_shadow_regression
    {D : NavierStokesDifferentialKit}
    (h : NavierStokesMillenniumTarget D)
    (i : Fin 3) :
    ∀ P : NavierStokesProblemData D,
      FeffermanGlobalRegularityClause (D.toComponentPredicateKit P i) := by
  exact NavierStokesMillenniumTarget.implies_componentFeffermanTarget h i

theorem explicit_target_uniform_clause_regression
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact ExplicitConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause h

theorem explicit_target_BKM_clause_regression
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitBKMContinuationClause ν u₀ T := by
  exact ExplicitConcreteNavierStokesMillenniumTarget_implies_BKMContinuationClause h

theorem explicit_target_repaired_uniform_clause_regression
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause
      h

theorem explicit_target_repaired_BKM_clause_regression
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyBKMContinuationClause ν u₀ T := by
  exact ExplicitConcreteNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationClause h

theorem concrete_target_uniform_clause_regression
    (h : ConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact ConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause h

theorem concrete_target_BKM_clause_regression
    (h : ConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitBKMContinuationClause ν u₀ T := by
  exact ConcreteNavierStokesMillenniumTarget_implies_BKMContinuationClause h

theorem concrete_target_repaired_uniform_clause_regression
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause
      h

theorem concrete_target_repaired_BKM_clause_regression
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyBKMContinuationClause ν u₀ T := by
  exact FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationClause h

theorem uniform_clause_implies_finiteEnergy_regression
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (h : ExplicitUniformVorticityContinuationClause ν u₀ T) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact ExplicitUniformVorticityContinuationClause_implies_finiteEnergy h

theorem uniform_target_implies_finiteEnergy_regression
    (h : ExplicitUniformVorticityContinuationTarget) :
    ExplicitFiniteEnergyUniformVorticityContinuationTarget := by
  exact
    ExplicitUniformVorticityContinuationTarget_implies_finiteEnergyUniformVorticityContinuationTarget
      h

theorem BKM_clause_implies_finiteEnergy_regression
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (h : ExplicitBKMContinuationClause ν u₀ T) :
    ExplicitFiniteEnergyBKMContinuationClause ν u₀ T := by
  exact ExplicitBKMContinuationClause_implies_finiteEnergy h

theorem BKM_target_implies_finiteEnergy_regression
    (h : ExplicitBKMContinuationTarget) :
    ExplicitFiniteEnergyBKMContinuationTarget := by
  exact ExplicitBKMContinuationTarget_implies_finiteEnergyBKMContinuationTarget h

theorem BKM_clause_uniform_clause_regression
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (h : ExplicitBKMContinuationClause ν u₀ T) :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact ExplicitBKMContinuationClause_implies_uniformVorticityContinuationClause h

theorem repaired_BKM_clause_repaired_uniform_clause_regression
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (h : ExplicitFiniteEnergyBKMContinuationClause ν u₀ T) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact ExplicitFiniteEnergyBKMContinuationClause_implies_finiteEnergyUniformVorticityContinuationClause h

theorem explicit_target_to_uniform_target_regression
    (h : ExplicitConcreteNavierStokesMillenniumTarget) :
    ExplicitUniformVorticityContinuationTarget := by
  exact ExplicitConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationTarget h

theorem explicit_target_to_uniform_allHorizons_regression
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    (ExplicitConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) h) T

theorem explicit_target_to_BKM_target_regression
    (h : ExplicitConcreteNavierStokesMillenniumTarget) :
    ExplicitBKMContinuationTarget := by
  exact ExplicitConcreteNavierStokesMillenniumTarget_implies_BKMContinuationTarget h

theorem explicit_target_to_BKM_allHorizons_regression
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitBKMContinuationClause ν u₀ T := by
  exact
    (ExplicitConcreteNavierStokesMillenniumTarget_implies_BKMContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) h) T

theorem explicit_target_to_repaired_uniform_target_regression
    (h : ExplicitConcreteNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyUniformVorticityContinuationTarget := by
  exact
    ExplicitConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationTarget
      h

theorem explicit_target_to_repaired_uniform_allHorizons_regression
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    (ExplicitConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) h) T

theorem explicit_repaired_target_to_repaired_uniform_allHorizons_regression
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    (ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) h) T

theorem explicit_target_to_repaired_BKM_target_regression
    (h : ExplicitConcreteNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyBKMContinuationTarget := by
  exact ExplicitConcreteNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationTarget h

theorem explicit_target_to_repaired_BKM_allHorizons_regression
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyBKMContinuationClause ν u₀ T := by
  exact
    (ExplicitConcreteNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) h) T

theorem explicit_repaired_target_to_repaired_BKM_allHorizons_regression
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyBKMContinuationClause ν u₀ T := by
  exact
    (ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) h) T

theorem concrete_target_to_uniform_target_regression
    (h : ConcreteNavierStokesMillenniumTarget) :
    ExplicitUniformVorticityContinuationTarget := by
  exact ConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationTarget h

theorem concrete_target_to_uniform_allHorizons_regression
    (h : ConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    (ConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) h) T

theorem concrete_target_to_BKM_target_regression
    (h : ConcreteNavierStokesMillenniumTarget) :
    ExplicitBKMContinuationTarget := by
  exact ConcreteNavierStokesMillenniumTarget_implies_BKMContinuationTarget h

theorem concrete_target_to_BKM_allHorizons_regression
    (h : ConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitBKMContinuationClause ν u₀ T := by
  exact
    (ConcreteNavierStokesMillenniumTarget_implies_BKMContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) h) T

theorem concrete_target_to_repaired_uniform_target_regression
    (h : ConcreteNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyUniformVorticityContinuationTarget := by
  exact ConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationTarget h

theorem concrete_target_to_repaired_uniform_allHorizons_regression
    (h : ConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    (ConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) h) T

theorem concrete_target_to_repaired_BKM_target_regression
    (h : ConcreteNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyBKMContinuationTarget := by
  exact ConcreteNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationTarget h

theorem concrete_target_to_repaired_BKM_allHorizons_regression
    (h : ConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyBKMContinuationClause ν u₀ T := by
  exact
    (ConcreteNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) h) T

theorem explicit_repaired_target_to_repaired_uniform_target_regression
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyUniformVorticityContinuationTarget := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationTarget
      h

theorem explicit_repaired_target_to_repaired_BKM_target_regression
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyBKMContinuationTarget := by
  exact ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationTarget h

theorem concrete_repaired_target_to_repaired_uniform_target_regression
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyUniformVorticityContinuationTarget := by
  exact
    FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationTarget
      h

theorem concrete_repaired_target_to_repaired_uniform_allHorizons_regression
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    (FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) h) T

theorem concrete_repaired_target_to_repaired_BKM_target_regression
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyBKMContinuationTarget := by
  exact FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationTarget h

theorem concrete_repaired_target_to_repaired_BKM_allHorizons_regression
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyBKMContinuationClause ν u₀ T := by
  exact
    (FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) h) T

theorem explicit_target_zero_output_regression
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} (hν : 0 < ν) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact ExplicitConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput h hν

theorem explicit_target_zero_output_timeOnlyPressure_regression
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ}
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput_timeOnlyPressure
      h hν π hπ

theorem explicit_target_zero_output_constantPressure_regression
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ}
    (hν : 0 < ν)
    (c : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput_constantPressure
      h hν c

theorem concrete_target_zero_output_regression
    (h : ConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} (hν : 0 < ν) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact ConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput h hν

theorem concrete_target_zero_output_timeOnlyPressure_regression
    (h : ConcreteNavierStokesMillenniumTarget)
    {ν : ℝ}
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact ConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput_timeOnlyPressure h hν π hπ

theorem concrete_target_zero_output_constantPressure_regression
    (h : ConcreteNavierStokesMillenniumTarget)
    {ν : ℝ}
    (hν : 0 < ν)
    (c : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact ConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput_constantPressure h hν c

theorem explicit_repaired_target_zero_output_regression
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ} (hν : 0 < ν) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_zeroGlobalOutput h hν

theorem explicit_repaired_target_zero_output_timeOnlyPressure_regression
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ}
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_zeroGlobalOutput_timeOnlyPressure
      h hν π hπ

theorem explicit_repaired_target_zero_output_constantPressure_regression
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ}
    (hν : 0 < ν)
    (c : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_zeroGlobalOutput_constantPressure
      h hν c

theorem concrete_repaired_target_zero_output_regression
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} (hν : 0 < ν) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput h hν

theorem concrete_repaired_target_zero_output_timeOnlyPressure_regression
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ}
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput_timeOnlyPressure
      h hν π hπ

theorem concrete_repaired_target_zero_output_constantPressure_regression
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ}
    (hν : 0 < ν)
    (c : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput_constantPressure h hν c
end ContinuationRegression
end NavierStokes
end FluidDynamics
end Mettapedia
