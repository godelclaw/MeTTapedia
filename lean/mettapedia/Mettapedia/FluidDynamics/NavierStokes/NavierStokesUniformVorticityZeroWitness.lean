import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityHeatShearExactnessCore
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityHeatShearExactnessStreamwise
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityHeatShearExactnessVertical
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityHeatShearExactnessFull
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityHeatShearExactnessTransport
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityPressureGauge

/-!
# Zero Witnesses for Uniform-Vorticity Continuation

This module contains the zero initial-data witness, zero-data global output,
and the heat-shear finite-time witness inhabitedness lemmas that reduce to
the zero witness.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section UniformVorticityContinuation

/-- Zero initial velocity data are smooth on `ℝ^3`. -/
theorem smoothInitialVelocityData_zero :
    smoothInitialVelocityData (0 : NSInitialVelocity) := by
  change ContDiff ℝ ∞ (fun _ : NSSpace => (0 : NSSpace))
  exact contDiff_const

/-- Canonical finite-time witness on any slab for zero initial data. -/
def zeroFiniteTimeRegularityWitness (ν T : ℝ) :
    ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T where
  velocity := 0
  pressure := 0
  smooth_velocity := smoothSpaceTimeVelocity_zero
  smooth_pressure := smoothSpaceTimePressure_zero
  momentum_equation_on := by
    intro t x ht0 htT
    have hu0 : ContDiffAt ℝ 2 (fun y : NSSpace => (0 : NSSpace)) x := by
      simpa using
        (contDiffAt_const : ContDiffAt ℝ 2 (fun y : NSSpace => (0 : NSSpace)) x)
    have hlap0 : spatialLaplacian (0 : NSVelocityField) t x = 0 := by
      simpa using
        (spatialLaplacian_const_smul (a := (0 : ℝ)) (u := (0 : NSVelocityField))
          (t := t) (x := x) hu0)
    simp [hlap0, timeVelocityDerivative_zero, spatialPressureGradient_zero,
      spatialConvection, spatialFDeriv]
  incompressible_on := by
    intro t x ht0 htT
    simpa using (spatialDivergence_zero t x)
  initial_condition := by
    intro x
    rfl
  bounded_energy_on := by
    refine ⟨0, le_rfl, ?_⟩
    intro t ht0 htT
    constructor
    · have hk :
        kineticEnergyDensity (0 : NSVelocityField) t =
          (fun _ : NSSpace => (0 : ℝ)) := by
        funext x
        simp [kineticEnergyDensity]
      rw [hk]
      exact
        (MeasureTheory.integrable_zero NSSpace ℝ
          (MeasureTheory.volume : MeasureTheory.Measure NSSpace))
    · have hE0 : kineticEnergyAt (0 : NSVelocityField) t = 0 := by
        simp [kineticEnergyAt, kineticEnergyDensity]
      simp [hE0]

/-- On nonnegative slabs, the full-drift heat-shear witness type is inhabited
exactly in the zero-data case. -/
theorem nonempty_ExplicitFiniteTimeRegularityWitness_heatShearFullDriftInitialVelocity_iff
    {ν T : ℝ} (hT : 0 ≤ T) {a k d c : ℝ} :
    Nonempty (ExplicitFiniteTimeRegularityWitness
        ν (heatShearFullDriftInitialVelocity a k d c) T) ↔
      d = 0 ∧ c = 0 ∧ a * k = 0 := by
  constructor
  · intro hW
    rcases hW with ⟨W⟩
    exact
      (finiteInitialKineticEnergy_heatShearFullDriftInitialVelocity_iff
        (a := a) (k := k) (d := d) (c := c)).1
        (finiteInitialKineticEnergy_of_matchesInitialVelocity_of_boundedKineticEnergyUpTo
          W.initial_condition W.bounded_energy_on hT)
  · intro hcond
    rcases hcond with ⟨rfl, rfl, hak⟩
    have hzeroConst :
        constantInitialVelocity (EuclideanSpace.single nsCoord2 0) = (0 : NSInitialVelocity) := by
      funext x
      ext i
      fin_cases i <;> simp [constantInitialVelocity, nsCoord2]
    rcases mul_eq_zero.mp hak with ha | hk
    · simpa [heatShearFullDriftInitialVelocity_zero_streamwiseDrift,
        heatShearVerticalDriftInitialVelocity, constantInitialVelocity_add, hzeroConst, ha,
        heatShearInitialVelocity_zero_of_amplitude_zero] using
        (show Nonempty (ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T) from
          ⟨zeroFiniteTimeRegularityWitness ν T⟩)
    · simpa [heatShearFullDriftInitialVelocity_zero_streamwiseDrift,
        heatShearVerticalDriftInitialVelocity, constantInitialVelocity_add, hzeroConst, hk,
        heatShearInitialVelocity_zero_of_wavenumber_zero] using
        (show Nonempty (ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T) from
          ⟨zeroFiniteTimeRegularityWitness ν T⟩)

/-- On nonnegative slabs, the vertical-drift heat-shear witness type is
inhabited exactly in the zero-data case. -/
theorem nonempty_ExplicitFiniteTimeRegularityWitness_heatShearInitialVelocity_iff
    {ν T : ℝ} (hT : 0 ≤ T) {a k : ℝ} :
    Nonempty (ExplicitFiniteTimeRegularityWitness
        ν (heatShearInitialVelocity a k) T) ↔
      a * k = 0 := by
  simpa [heatShearFullDriftInitialVelocity_zero_drifts] using
    (nonempty_ExplicitFiniteTimeRegularityWitness_heatShearFullDriftInitialVelocity_iff
      (ν := ν) (T := T) hT (a := a) (k := k) (d := 0) (c := 0))

/-- On nonnegative slabs, the vertical-drift heat-shear witness type is
inhabited exactly in the zero-data case. -/
theorem nonempty_ExplicitFiniteTimeRegularityWitness_heatShearVerticalDriftInitialVelocity_iff
    {ν T : ℝ} (hT : 0 ≤ T) {a k c : ℝ} :
    Nonempty (ExplicitFiniteTimeRegularityWitness
        ν (heatShearVerticalDriftInitialVelocity a k c) T) ↔
      c = 0 ∧ a * k = 0 := by
  simpa [heatShearFullDriftInitialVelocity_zero_streamwiseDrift] using
    (nonempty_ExplicitFiniteTimeRegularityWitness_heatShearFullDriftInitialVelocity_iff
      (ν := ν) (T := T) hT (a := a) (k := k) (d := 0) (c := c))

/-- On nonnegative slabs, the streamwise-drift heat-shear witness type is
inhabited exactly in the zero-data case. -/
theorem nonempty_ExplicitFiniteTimeRegularityWitness_heatShearStreamwiseDriftInitialVelocity_iff
    {ν T : ℝ} (hT : 0 ≤ T) {a k d : ℝ} :
    Nonempty (ExplicitFiniteTimeRegularityWitness
        ν (heatShearStreamwiseDriftInitialVelocity a k d) T) ↔
      d = 0 ∧ a * k = 0 := by
  simpa [heatShearFullDriftInitialVelocity_zero_verticalDrift] using
    (nonempty_ExplicitFiniteTimeRegularityWitness_heatShearFullDriftInitialVelocity_iff
      (ν := ν) (T := T) hT (a := a) (k := k) (d := d) (c := 0))

/-- On nonnegative slabs, the transported full-drift heat-shear witness type
is inhabited exactly in the zero-data case. -/
theorem nonempty_ExplicitFiniteTimeRegularityWitness_heatShearTransportFullDriftInitialVelocity_iff
    {ν T : ℝ} (hT : 0 ≤ T) {a k b d c : ℝ} :
    Nonempty (ExplicitFiniteTimeRegularityWitness
        ν (heatShearTransportFullDriftInitialVelocity a k b d c) T) ↔
      b = 0 ∧ d = 0 ∧ c = 0 ∧ a * k = 0 := by
  constructor
  · intro hW
    rcases hW with ⟨W⟩
    exact
      (finiteInitialKineticEnergy_heatShearTransportFullDriftInitialVelocity_iff
        (a := a) (k := k) (b := b) (d := d) (c := c)).1
        (finiteInitialKineticEnergy_of_matchesInitialVelocity_of_boundedKineticEnergyUpTo
          W.initial_condition W.bounded_energy_on hT)
  · intro hcond
    rcases hcond with ⟨rfl, rfl, rfl, hak⟩
    have hzeroConst :
        constantInitialVelocity (EuclideanSpace.single nsCoord2 0) = (0 : NSInitialVelocity) := by
      funext x
      ext i
      fin_cases i <;> simp [constantInitialVelocity, nsCoord2]
    rcases mul_eq_zero.mp hak with ha | hk
    · simpa [heatShearTransportFullDriftInitialVelocity_zero_transport,
        heatShearFullDriftInitialVelocity_zero_streamwiseDrift,
        heatShearVerticalDriftInitialVelocity, constantInitialVelocity_add, hzeroConst, ha,
        heatShearInitialVelocity_zero_of_amplitude_zero] using
        (show Nonempty (ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T) from
          ⟨zeroFiniteTimeRegularityWitness ν T⟩)
    · simpa [heatShearTransportFullDriftInitialVelocity_zero_transport,
        heatShearFullDriftInitialVelocity_zero_streamwiseDrift,
        heatShearVerticalDriftInitialVelocity, constantInitialVelocity_add, hzeroConst, hk,
        heatShearInitialVelocity_zero_of_wavenumber_zero] using
        (show Nonempty (ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T) from
          ⟨zeroFiniteTimeRegularityWitness ν T⟩)

/-- On nonnegative slabs, the transported heat-shear witness type is inhabited
exactly in the zero-data case. -/
theorem nonempty_ExplicitFiniteTimeRegularityWitness_heatShearTransportInitialVelocity_iff
    {ν T : ℝ} (hT : 0 ≤ T) {a k b : ℝ} :
    Nonempty (ExplicitFiniteTimeRegularityWitness
        ν (heatShearTransportInitialVelocity a k b) T) ↔
      b = 0 ∧ a * k = 0 := by
  simpa [heatShearTransportFullDriftInitialVelocity_zero_drifts] using
    (nonempty_ExplicitFiniteTimeRegularityWitness_heatShearTransportFullDriftInitialVelocity_iff
      (ν := ν) (T := T) hT (a := a) (k := k) (b := b) (d := 0) (c := 0))

/-- The canonical zero witness has a uniform zero vorticity bound on every slab.
-/
theorem zeroFiniteTimeRegularityWitness_has_uniformVorticityBound
    (ν T : ℝ) :
    ∃ B : ℝ,
      uniformVorticityBoundUpTo (zeroFiniteTimeRegularityWitness ν T).velocity T B := by
  refine ⟨0, ?_⟩
  simpa [zeroFiniteTimeRegularityWitness] using (uniformVorticityBoundUpTo_zero T)

/-- The zero witness gives an honest inhabited premise for the concrete uniform
continuation clause on every slab.  This is the basic nonvacuity baseline that
contrasts with the impossible nonzero constant-initial-data cases. -/
theorem zeroFiniteTimeRegularityWitness_exhibits_uniformContinuationPremise
    (ν T : ℝ) :
    ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
      ∃ B : ℝ, uniformVorticityBoundUpTo W.velocity T B := by
  refine ⟨zeroFiniteTimeRegularityWitness ν T, ?_⟩
  exact zeroFiniteTimeRegularityWitness_has_uniformVorticityBound ν T

/-- Concrete finite-slab gauge baseline: after adding any smooth time-only
pressure to the zero witness on a larger slab and restricting to a shorter one,
the resulting witness still carries the explicit zero uniform-vorticity bound.
-/
theorem zeroFiniteTimeRegularityWitness_addPressureOfZeroSpatialGradient_restrict_has_uniformVorticityBound
    (ν Tsmall Tlarge : ℝ)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0)
    (hT : Tsmall ≤ Tlarge) :
    ∃ B : ℝ,
      uniformVorticityBoundUpTo
        (((zeroFiniteTimeRegularityWitness ν Tlarge).addPressureOfZeroSpatialGradient q hq hq_zero).restrict hT).velocity
        Tsmall B := by
  refine ⟨0, ?_⟩
  exact
    (zeroFiniteTimeRegularityWitness ν Tlarge).uniformVorticityBound_addPressureOfZeroSpatialGradient_restrict
      (by
        simpa [zeroFiniteTimeRegularityWitness] using
          (uniformVorticityBoundUpTo_zero Tlarge))
      q hq hq_zero hT

/-- Time-only special case of the zero-data zero-spatial-gradient gauge
baseline on restricted slabs. -/
theorem zeroFiniteTimeRegularityWitness_addTimeOnlyPressure_restrict_has_uniformVorticityBound
    (ν Tsmall Tlarge : ℝ)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    (hT : Tsmall ≤ Tlarge) :
    ∃ B : ℝ,
      uniformVorticityBoundUpTo
        (((zeroFiniteTimeRegularityWitness ν Tlarge).addTimeOnlyPressure π hπ).restrict hT).velocity
        Tsmall B := by
  exact
    zeroFiniteTimeRegularityWitness_addPressureOfZeroSpatialGradient_restrict_has_uniformVorticityBound
      ν Tsmall Tlarge
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)
      hT

/-- Concrete bottom-up baseline: zero initial data provides an explicit global
smooth Navier--Stokes witness (the zero velocity/pressure pair). -/
theorem ExplicitConcreteNavierStokesGlobalOutput_zero
    (ν : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  refine ⟨0, 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact smoothSpaceTimeVelocity_zero
  · exact smoothSpaceTimePressure_zero
  · intro t x
    have hu0 : ContDiffAt ℝ 2 (fun y : NSSpace => (0 : NSSpace)) x := by
      simpa using
        (contDiffAt_const : ContDiffAt ℝ 2 (fun y : NSSpace => (0 : NSSpace)) x)
    have hlap0 : spatialLaplacian (0 : NSVelocityField) t x = 0 := by
      simpa using
        (spatialLaplacian_const_smul (a := (0 : ℝ)) (u := (0 : NSVelocityField))
          (t := t) (x := x) hu0)
    simp [hlap0, timeVelocityDerivative_zero, spatialPressureGradient_zero,
      spatialConvection, spatialFDeriv]
  · intro t x
    simpa using (spatialDivergence_zero t x)
  · intro x
    rfl
  · refine ⟨0, le_rfl, ?_⟩
    intro t
    constructor
    · have hk :
        kineticEnergyDensity (0 : NSVelocityField) t =
          (fun _ : NSSpace => (0 : ℝ)) := by
        funext x
        simp [kineticEnergyDensity]
      rw [hk]
      exact
        (MeasureTheory.integrable_zero NSSpace ℝ
          (MeasureTheory.volume : MeasureTheory.Measure NSSpace))
    · have hE0 : kineticEnergyAt (0 : NSVelocityField) t = 0 := by
        simp [kineticEnergyAt, kineticEnergyDensity]
      simp [hE0]



end UniformVorticityContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
