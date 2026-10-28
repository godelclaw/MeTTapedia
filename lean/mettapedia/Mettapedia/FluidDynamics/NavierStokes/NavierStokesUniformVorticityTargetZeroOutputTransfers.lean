import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityTargetSurfaceTransfers
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityZeroOutput

/-!
# Uniform-vorticity target zero-output transfers

Zero-data global-output consequences of the concrete Navier-Stokes theorem
surfaces.  These sit above the target-surface transfer layer because they use
the operational zero-output witnesses and pressure-gauge transport lemmas.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section UniformVorticityContinuation

/-- The explicit whole-space theorem target is operational at zero initial
data: positive viscosity and the canonical zero datum satisfy the input side
directly, so the target yields a concrete global output there. -/
theorem ExplicitConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} (hν : 0 < ν) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  have hdiv0 : ∀ x, initialSpatialDivergence (0 : NSInitialVelocity) x = 0 := by
    intro x
    simpa using (initialSpatialDivergence_zero x)
  exact h ν (0 : NSInitialVelocity) hν smoothInitialVelocityData_zero hdiv0

/-- Zero-data pressure-gauge transport on the explicit whole-space theorem
surface: once the theorem target yields the canonical zero global output, any
smooth slice-wise zero-spatial-gradient pressure gauge may be added directly. -/
theorem ExplicitConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ}
    (hν : 0 < ν)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitConcreteNavierStokesGlobalOutput.addPressureOfZeroSpatialGradient
      (h := ExplicitConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput h hν)
      q hq hq_zero

/-- Time-only pressure-gauge special case of the explicit whole-space theorem
target at zero initial data. -/
theorem ExplicitConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput_timeOnlyPressure
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ}
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      h hν
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)

/-- Constant-pressure special case of the explicit whole-space theorem target
at zero initial data. -/
theorem ExplicitConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput_constantPressure
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ}
    (hν : 0 < ν)
    (c : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      h hν
      (fun _ : NSTime => fun _ : NSSpace => c)
      (smoothSpaceTimePressure_const c)
      (fun t x => spatialPressureGradient_const c t x)

/-- The structured whole-space theorem target has the same zero-data
operational consequence via the explicit equivalence theorem. -/
theorem ConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput
    (h : ConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} (hν : 0 < ν) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput
      (ConcreteNavierStokesMillenniumTarget_implies_ExplicitConcreteNavierStokesMillenniumTarget
        h) hν

/-- Zero-data pressure-gauge transport on the structured unrepaired
whole-space theorem surface. -/
theorem ConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
    (h : ConcreteNavierStokesMillenniumTarget)
    {ν : ℝ}
    (hν : 0 < ν)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      (ConcreteNavierStokesMillenniumTarget_implies_ExplicitConcreteNavierStokesMillenniumTarget
        h) hν q hq hq_zero

/-- Time-only pressure-gauge special case of the structured whole-space theorem
target at zero initial data. -/
theorem ConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput_timeOnlyPressure
    (h : ConcreteNavierStokesMillenniumTarget)
    {ν : ℝ}
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      h hν
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)

/-- Constant-pressure special case of the structured whole-space theorem target
at zero initial data. -/
theorem ConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput_constantPressure
    (h : ConcreteNavierStokesMillenniumTarget)
    {ν : ℝ}
    (hν : 0 < ν)
    (c : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      h hν
      (fun _ : NSTime => fun _ : NSSpace => c)
      (smoothSpaceTimePressure_const c)
      (fun t x => spatialPressureGradient_const c t x)

/-- The repaired explicit finite-energy theorem target is likewise operational
at zero initial data, since the zero datum is finite-energy. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_zeroGlobalOutput
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ} (hν : 0 < ν) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  have hdiv0 : ∀ x, initialSpatialDivergence (0 : NSInitialVelocity) x = 0 := by
    intro x
    simpa using (initialSpatialDivergence_zero x)
  exact
    h ν (0 : NSInitialVelocity) hν smoothInitialVelocityData_zero hdiv0
      finiteInitialKineticEnergy_zero

/-- Zero-data pressure-gauge transport on the repaired explicit whole-space
theorem surface. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ}
    (hν : 0 < ν)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitConcreteNavierStokesGlobalOutput.addPressureOfZeroSpatialGradient
      (h := ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_zeroGlobalOutput
        h hν)
      q hq hq_zero

/-- Time-only pressure-gauge special case of the repaired explicit finite-energy
theorem target at zero initial data. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_zeroGlobalOutput_timeOnlyPressure
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ}
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      h hν
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)

/-- Constant-pressure special case of the repaired explicit finite-energy
theorem target at zero initial data. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_zeroGlobalOutput_constantPressure
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ}
    (hν : 0 < ν)
    (c : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      h hν
      (fun _ : NSTime => fun _ : NSSpace => c)
      (smoothSpaceTimePressure_const c)
      (fun t x => spatialPressureGradient_const c t x)

/-- The structured repaired finite-energy theorem target has the same zero-data
operational consequence via the explicit equivalence theorem. -/
theorem FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} (hν : 0 < ν) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_zeroGlobalOutput
      (FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget
        h) hν

/-- Zero-data pressure-gauge transport on the structured repaired
whole-space theorem surface. -/
theorem FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ}
    (hν : 0 < ν)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      (FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget
        h) hν q hq hq_zero

/-- Time-only pressure-gauge special case of the structured repaired
finite-energy theorem target at zero initial data. -/
theorem FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput_timeOnlyPressure
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ}
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      h hν
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)

/-- Constant-pressure special case of the structured repaired finite-energy
theorem target at zero initial data. -/
theorem FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput_constantPressure
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ}
    (hν : 0 < ν)
    (c : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      h hν
      (fun _ : NSTime => fun _ : NSSpace => c)
      (smoothSpaceTimePressure_const c)
      (fun t x => spatialPressureGradient_const c t x)

end UniformVorticityContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
