import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityConcreteWitnesses

/-!
# Basic Continuation Counterexample Regressions

This module checks the old explicit/concrete target failures, constant and
linear-shear finite-energy exclusions, and the constant-velocity repaired clause
and time-only-pressure candidate gap.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace ContinuationRegression

theorem old_explicit_target_false_regression :
    ¬ ExplicitConcreteNavierStokesMillenniumTarget := by
  exact not_ExplicitConcreteNavierStokesMillenniumTarget

theorem old_concrete_target_false_regression :
    ¬ ConcreteNavierStokesMillenniumTarget := by
  exact not_ConcreteNavierStokesMillenniumTarget

def nonzeroConstantVelocity : NSSpace :=
  EuclideanSpace.single nsCoord0 (1 : ℝ)

theorem nonzeroConstantVelocity_ne_zero :
    nonzeroConstantVelocity ≠ 0 := by
  intro h
  simp [nonzeroConstantVelocity, EuclideanSpace.single_eq_zero_iff] at h

theorem constant_velocity_not_finiteInitialKineticEnergy_regression :
    ¬ finiteInitialKineticEnergy (constantInitialVelocity nonzeroConstantVelocity) := by
  exact not_finiteInitialKineticEnergy_constantInitialVelocity nonzeroConstantVelocity_ne_zero

theorem linear_shear_not_finiteInitialKineticEnergy_regression :
    ¬ finiteInitialKineticEnergy (linearShearInitialVelocity 1) := by
  exact
    not_finiteInitialKineticEnergy_linearShearInitialVelocity
      (a := 1) (by simp)

theorem repaired_structured_domain_exclusion_of_not_finiteInitialKineticEnergy_regression
    {u₀ : NSInitialVelocity}
    (hfinite : ¬ finiteInitialKineticEnergy u₀) :
    ¬ Nonempty { P : FiniteEnergyAdmissibleNavierStokesProblemData //
        P.initialVelocity = u₀ } := by
  exact
    not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_of_not_finiteInitialKineticEnergy
      hfinite

theorem repaired_structured_domain_nonempty_iff_finiteInitialKineticEnergy_regression
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0) :
    Nonempty { P : FiniteEnergyAdmissibleNavierStokesProblemData //
        P.viscosity = ν ∧ P.initialVelocity = u₀ } ↔
      finiteInitialKineticEnergy u₀ := by
  exact
    nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_iff hν hsmooth hdiv

theorem zero_data_repaired_structured_domain_regression
    {ν : ℝ} (hν : 0 < ν) :
    Nonempty { P : FiniteEnergyAdmissibleNavierStokesProblemData //
        P.viscosity = ν ∧ P.initialVelocity = (0 : NSInitialVelocity) } := by
  exact
    (nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_iff
      (ν := ν) (u₀ := (0 : NSInitialVelocity))
      hν smoothInitialVelocityData_zero (by
        intro x
        simpa using (initialSpatialDivergence_zero x))).2
      finiteInitialKineticEnergy_zero

theorem constant_velocity_not_in_repaired_structured_domain_regression :
    ¬ Nonempty { P : FiniteEnergyAdmissibleNavierStokesProblemData //
        P.initialVelocity = constantInitialVelocity nonzeroConstantVelocity } := by
  exact
    not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_constantInitialVelocity
      nonzeroConstantVelocity_ne_zero

theorem linear_shear_not_in_repaired_structured_domain_regression :
    ¬ Nonempty { P : FiniteEnergyAdmissibleNavierStokesProblemData //
        P.initialVelocity = linearShearInitialVelocity 1 } := by
  exact
    not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_linearShearInitialVelocity
      (by simp)

theorem constant_velocity_repaired_regularity_without_regularity_regression
    {ν : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
        ν (constantInitialVelocity nonzeroConstantVelocity) ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (constantInitialVelocity nonzeroConstantVelocity) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_constantInitialVelocity_without_regularity
      (ν := ν) hν nonzeroConstantVelocity_ne_zero

theorem constant_velocity_time_only_pressure_candidate_without_finiteTimeWitness_regression :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ 1 →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          (1 : ℝ) • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ 1 → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (constantInitialVelocity nonzeroConstantVelocity) u ∧
      uniformVorticityBoundUpTo u 1 B ∧
      ¬ boundedKineticEnergyUpTo u 1) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness 1 (constantInitialVelocity nonzeroConstantVelocity) 1) := by
  exact
    constantInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness_addPressureOfZeroSpatialGradient
      (ν := 1) (T := 1)
      nonzeroConstantVelocity_ne_zero
      (by norm_num)
      (fun t : NSTime => fun _ : NSSpace => t + 1)
      (smoothSpaceTimePressure_timeOnly (by simpa using
        (contDiff_id.add contDiff_const : ContDiff ℝ ∞ (fun s : NSTime => s + 1))))
      (fun t x => spatialPressureGradient_timeOnly (fun s : NSTime => s + 1) t x)


end ContinuationRegression
end NavierStokes
end FluidDynamics
end Mettapedia
