import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityRepairedFiniteEnergyWitnesses

/-!
# Zero-data pressure-gauge witnesses for uniform-vorticity examples

This module contains zero initial-data global-output, regularity-clause, and
finite-energy witnesses, including constant and time-only pressure gauges.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section UniformVorticityContinuation

/-- Concrete nonzero-pressure baseline: zero velocity with any constant
pressure still gives a global explicit Navier--Stokes output. -/
theorem ExplicitConcreteNavierStokesGlobalOutput_zero_addPressureOfZeroSpatialGradient
    (ν : ℝ)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitConcreteNavierStokesGlobalOutput.addPressureOfZeroSpatialGradient
      (h := ExplicitConcreteNavierStokesGlobalOutput_zero ν) q hq hq_zero

/-- Constant-pressure special case of the generic zero-data zero-gradient
pressure transport on the explicit whole-space output layer. -/
theorem ExplicitConcreteNavierStokesGlobalOutput_zero_constantPressure
    (ν c : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitConcreteNavierStokesGlobalOutput_zero_addPressureOfZeroSpatialGradient
      ν
      (fun _ : NSTime => fun _ : NSSpace => c)
      (smoothSpaceTimePressure_const c)
      (fun t x => spatialPressureGradient_const c t x)

/-- Concrete time-gauge baseline: zero velocity with any smooth time-only
pressure still gives a global explicit Navier--Stokes output. -/
theorem ExplicitConcreteNavierStokesGlobalOutput_zero_timeOnlyPressure
    (ν : ℝ) (π : NSTime → ℝ) (hπ : ContDiff ℝ ∞ π) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitConcreteNavierStokesGlobalOutput_zero_addPressureOfZeroSpatialGradient
      ν
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)

/-- The concrete regularity clause is directly inhabitable at zero initial data.
-/
theorem ExplicitConcreteNavierStokesRegularityClause_zero
    (ν : ℝ) :
    ExplicitConcreteNavierStokesRegularityClause ν (0 : NSInitialVelocity) := by
  exact
    ExplicitConcreteNavierStokesGlobalOutput_implies_ExplicitConcreteNavierStokesRegularityClause
      (ExplicitConcreteNavierStokesGlobalOutput_zero ν)

/-- Generic zero-data pressure-gauge transport on the explicit unrepaired
regularity-clause surface. -/
theorem ExplicitConcreteNavierStokesRegularityClause_zero_addPressureOfZeroSpatialGradient
    (ν : ℝ)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    ExplicitConcreteNavierStokesRegularityClause ν (0 : NSInitialVelocity) := by
  exact
    ExplicitConcreteNavierStokesRegularityClause_addPressureOfZeroSpatialGradient
      (ExplicitConcreteNavierStokesRegularityClause_zero ν) q hq hq_zero

/-- The concrete regularity clause remains directly inhabitable at zero initial
data after adding any constant pressure gauge. -/
theorem ExplicitConcreteNavierStokesRegularityClause_zero_constantPressure
    (ν c : ℝ) :
    ExplicitConcreteNavierStokesRegularityClause ν (0 : NSInitialVelocity) := by
  exact
    ExplicitConcreteNavierStokesRegularityClause_zero_addPressureOfZeroSpatialGradient
      ν
      (fun _ : NSTime => fun _ : NSSpace => c)
      (smoothSpaceTimePressure_const c)
      (fun t x => spatialPressureGradient_const c t x)

/-- The concrete regularity clause remains directly inhabitable at zero initial
data after adding any smooth time-only pressure gauge. -/
theorem ExplicitConcreteNavierStokesRegularityClause_zero_timeOnlyPressure
    (ν : ℝ) (π : NSTime → ℝ) (hπ : ContDiff ℝ ∞ π) :
    ExplicitConcreteNavierStokesRegularityClause ν (0 : NSInitialVelocity) := by
  exact
    ExplicitConcreteNavierStokesRegularityClause_zero_addPressureOfZeroSpatialGradient
      ν
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)

/-- The structured fully concrete clause is directly inhabitable at zero
initial data by converting the explicit zero solution through the concrete
equivalence theorem. -/
theorem concreteNavierStokesGlobalRegularityClause_zero
    {ν : ℝ} (hν : 0 < ν) :
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      { viscosity := ν
        viscosity_pos := hν
        initialVelocity := (0 : NSInitialVelocity)
        smooth_initial := smoothInitialVelocityData_zero
        divergence_free_initial := by
          intro x
          simpa using (initialSpatialDivergence_zero x) } := by
  exact
    ExplicitConcreteNavierStokesGlobalOutput_implies_concreteNavierStokesGlobalRegularityClause
      hν smoothInitialVelocityData_zero
      (by
        intro x
        simpa using (initialSpatialDivergence_zero x))
      (ExplicitConcreteNavierStokesGlobalOutput_zero ν)

/-- Generic zero-data pressure-gauge transport on the structured fully
concrete whole-space clause. -/
theorem concreteNavierStokesGlobalRegularityClause_zero_addPressureOfZeroSpatialGradient
    {ν : ℝ} (hν : 0 < ν)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      { viscosity := ν
        viscosity_pos := hν
        initialVelocity := (0 : NSInitialVelocity)
        smooth_initial := smoothInitialVelocityData_zero
        divergence_free_initial := by
          intro x
          simpa using (initialSpatialDivergence_zero x) } := by
  exact
    concreteNavierStokesGlobalRegularityClause_addPressureOfZeroSpatialGradient
      hν smoothInitialVelocityData_zero
      (by
        intro x
        simpa using (initialSpatialDivergence_zero x))
      (concreteNavierStokesGlobalRegularityClause_zero hν)
      q hq hq_zero

/-- The repaired explicit finite-energy theorem surface is likewise directly
inhabited at zero initial data. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_zero
    (ν : ℝ) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause ν (0 : NSInitialVelocity) := by
  exact
    ExplicitConcreteNavierStokesGlobalOutput_implies_ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
      (ExplicitConcreteNavierStokesGlobalOutput_zero ν)

/-- Generic zero-data pressure-gauge transport on the repaired explicit
finite-energy regularity-clause surface. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_zero_addPressureOfZeroSpatialGradient
    (ν : ℝ)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause ν (0 : NSInitialVelocity) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_addPressureOfZeroSpatialGradient
      (ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_zero ν) q hq hq_zero

/-- The repaired explicit finite-energy regularity clause remains directly
inhabitable at zero initial data after adding any constant pressure gauge. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_zero_constantPressure
    (ν c : ℝ) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause ν (0 : NSInitialVelocity) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_zero_addPressureOfZeroSpatialGradient
      ν
      (fun _ : NSTime => fun _ : NSSpace => c)
      (smoothSpaceTimePressure_const c)
      (fun t x => spatialPressureGradient_const c t x)

/-- The repaired explicit finite-energy regularity clause remains directly
inhabitable at zero initial data after adding any smooth time-only pressure
gauge. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_zero_timeOnlyPressure
    (ν : ℝ) (π : NSTime → ℝ) (hπ : ContDiff ℝ ∞ π) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause ν (0 : NSInitialVelocity) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_zero_addPressureOfZeroSpatialGradient
      ν
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)

/-- The repaired structured fully concrete clause is likewise directly
inhabitable at zero initial data. -/
theorem finiteEnergyConcreteNavierStokesGlobalRegularityClause_zero
    {ν : ℝ} (hν : 0 < ν) :
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      ({ viscosity := ν
         viscosity_pos := hν
         initialVelocity := (0 : NSInitialVelocity)
         smooth_initial := smoothInitialVelocityData_zero
         divergence_free_initial := by
           intro x
           simpa using (initialSpatialDivergence_zero x)
         finite_initial_energy := finiteInitialKineticEnergy_zero } :
        FiniteEnergyAdmissibleNavierStokesProblemData).toNavierStokesProblemData := by
  exact
    ExplicitConcreteNavierStokesGlobalOutput_implies_finiteEnergyConcreteNavierStokesGlobalRegularityClause_of_finiteInitialKineticEnergy
      (ν := ν) (u₀ := (0 : NSInitialVelocity))
      hν smoothInitialVelocityData_zero
      (by
        intro x
        simpa using (initialSpatialDivergence_zero x))
      finiteInitialKineticEnergy_zero
      (ExplicitConcreteNavierStokesGlobalOutput_zero ν)

/-- Generic zero-data pressure-gauge transport on the repaired structured fully
concrete whole-space clause. -/
theorem finiteEnergyConcreteNavierStokesGlobalRegularityClause_zero_addPressureOfZeroSpatialGradient
    {ν : ℝ} (hν : 0 < ν)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      ({ viscosity := ν
         viscosity_pos := hν
         initialVelocity := (0 : NSInitialVelocity)
         smooth_initial := smoothInitialVelocityData_zero
         divergence_free_initial := by
           intro x
           simpa using (initialSpatialDivergence_zero x)
         finite_initial_energy := finiteInitialKineticEnergy_zero } :
        FiniteEnergyAdmissibleNavierStokesProblemData).toNavierStokesProblemData := by
  exact
    finiteEnergyConcreteNavierStokesGlobalRegularityClause_addPressureOfZeroSpatialGradient
      hν smoothInitialVelocityData_zero
      (by
        intro x
        simpa using (initialSpatialDivergence_zero x))
      finiteInitialKineticEnergy_zero
      (finiteEnergyConcreteNavierStokesGlobalRegularityClause_zero hν)
      q hq hq_zero

end UniformVorticityContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
