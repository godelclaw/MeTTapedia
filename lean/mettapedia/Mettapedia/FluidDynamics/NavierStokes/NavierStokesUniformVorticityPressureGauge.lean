import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityBounds
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityEnergyObstructions

/-!
# Pressure-Gauge Utilities for Uniform-Vorticity Continuation

This module contains pressure-gauge transport lemmas for finite-time
witnesses, global outputs, concrete regularity clauses, and applications of
uniform-vorticity continuation clauses.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section UniformVorticityContinuation

/-- Any fully explicit global smooth solution yields a finite-time witness on
every slab `0 ≤ t ≤ T`. -/
theorem ExplicitConcreteNavierStokesGlobalOutput.implies_finiteTimeWitness
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (h : ExplicitConcreteNavierStokesGlobalOutput ν u₀) :
    Nonempty (ExplicitFiniteTimeRegularityWitness ν u₀ T) := by
  rcases h with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
  refine ⟨{
    velocity := u
    pressure := p
    smooth_velocity := hu
    smooth_pressure := hp
    momentum_equation_on := ?_
    incompressible_on := ?_
    initial_condition := hinit
    bounded_energy_on := boundedKineticEnergy_implies_boundedKineticEnergyUpTo hbd
  }⟩
  · intro t x ht0 htT
    exact hmom t x
  · intro t x ht0 htT
    exact hinc t x

/-- Pressure-gauge symmetry on finite-time witnesses: adding a spatially and
slice-wise zero-gradient pressure field leaves the witness valid on the same
slab. -/
def ExplicitFiniteTimeRegularityWitness.addPressureOfZeroSpatialGradient
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    ExplicitFiniteTimeRegularityWitness ν u₀ T where
  velocity := W.velocity
  pressure := W.pressure + q
  smooth_velocity := W.smooth_velocity
  smooth_pressure := smoothSpaceTimePressure_add W.smooth_pressure hq
  momentum_equation_on := by
    intro t x ht0 htT
    have hp :
        DifferentiableAt ℝ (fun y : NSSpace => W.pressure t y) x :=
      smoothSpaceTimePressure_differentiableAt_spatialSlice W.smooth_pressure t x
    have hq' :
        DifferentiableAt ℝ (fun y : NSSpace => q t y) x :=
      smoothSpaceTimePressure_differentiableAt_spatialSlice hq t x
    rw [spatialPressureGradient_add hp hq', hq_zero]
    simpa using W.momentum_equation_on t x ht0 htT
  incompressible_on := W.incompressible_on
  initial_condition := W.initial_condition
  bounded_energy_on := W.bounded_energy_on

/-- Pressure-gauge symmetry on finite-time witnesses: adding a spatially and
temporally constant pressure leaves the witness valid on the same slab. -/
def ExplicitFiniteTimeRegularityWitness.addConstantPressure
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (c : ℝ) :
    ExplicitFiniteTimeRegularityWitness ν u₀ T :=
  W.addPressureOfZeroSpatialGradient
    (fun _ : NSTime => fun _ : NSSpace => c)
    (smoothSpaceTimePressure_const c)
    (fun t x => spatialPressureGradient_const c t x)

/-- Pressure-gauge symmetry on finite-time witnesses: adding any smooth
time-only pressure leaves the witness valid on the same slab. -/
def ExplicitFiniteTimeRegularityWitness.addTimeOnlyPressure
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    ExplicitFiniteTimeRegularityWitness ν u₀ T :=
  W.addPressureOfZeroSpatialGradient
    (fun t : NSTime => fun _ : NSSpace => π t)
    (smoothSpaceTimePressure_timeOnly hπ)
    (fun t x => spatialPressureGradient_timeOnly π t x)

/-- Uniform vorticity control is unchanged under adding any smooth pressure
gauge with zero spatial gradient on each slice, since the velocity field is
unchanged. -/
theorem ExplicitFiniteTimeRegularityWitness.uniformVorticityBound_addPressureOfZeroSpatialGradient
    {ν : ℝ} {u₀ : NSInitialVelocity} {T B : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hω : uniformVorticityBoundUpTo W.velocity T B)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    uniformVorticityBoundUpTo
      (W.addPressureOfZeroSpatialGradient q hq hq_zero).velocity T B := by
  simpa [ExplicitFiniteTimeRegularityWitness.addPressureOfZeroSpatialGradient] using hω

/-- Uniform vorticity control is unchanged under adding a smooth time-only
pressure gauge to a finite-time witness, since the velocity field is unchanged.
-/
theorem ExplicitFiniteTimeRegularityWitness.uniformVorticityBound_addTimeOnlyPressure
    {ν : ℝ} {u₀ : NSInitialVelocity} {T B : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hω : uniformVorticityBoundUpTo W.velocity T B)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    uniformVorticityBoundUpTo (W.addTimeOnlyPressure π hπ).velocity T B := by
  exact
    W.uniformVorticityBound_addPressureOfZeroSpatialGradient hω
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)

/-- Uniform vorticity control remains available after adding a smooth
zero-spatial-gradient pressure gauge and then restricting to a shorter slab. -/
theorem ExplicitFiniteTimeRegularityWitness.uniformVorticityBound_addPressureOfZeroSpatialGradient_restrict
    {ν : ℝ} {u₀ : NSInitialVelocity} {T T' B : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hω : uniformVorticityBoundUpTo W.velocity T B)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0)
    (hT : T' ≤ T) :
    uniformVorticityBoundUpTo
      ((W.addPressureOfZeroSpatialGradient q hq hq_zero).restrict hT).velocity T' B := by
  simpa [ExplicitFiniteTimeRegularityWitness.addPressureOfZeroSpatialGradient,
    ExplicitFiniteTimeRegularityWitness.restrict] using
    (uniformVorticityBoundUpTo_restrict
      (u := W.velocity) (T := T) (T' := T') (B := B) hω hT)

/-- Uniform vorticity control remains available after adding a smooth time-only
pressure gauge and then restricting to a shorter slab. -/
theorem ExplicitFiniteTimeRegularityWitness.uniformVorticityBound_addTimeOnlyPressure_restrict
    {ν : ℝ} {u₀ : NSInitialVelocity} {T T' B : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hω : uniformVorticityBoundUpTo W.velocity T B)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    (hT : T' ≤ T) :
    uniformVorticityBoundUpTo ((W.addTimeOnlyPressure π hπ).restrict hT).velocity T' B := by
  exact
    W.uniformVorticityBound_addPressureOfZeroSpatialGradient_restrict hω
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)
      hT

/-- Pressure-gauge symmetry on the explicit global output surface: adding a
slice-wise zero-gradient pressure field preserves a global solution. -/
theorem ExplicitConcreteNavierStokesGlobalOutput.addPressureOfZeroSpatialGradient
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (h : ExplicitConcreteNavierStokesGlobalOutput ν u₀)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    ExplicitConcreteNavierStokesGlobalOutput ν u₀ := by
  rcases h with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
  refine ⟨u, p + q, hu, ?_, ?_, hinc, hinit, hbd⟩
  · exact smoothSpaceTimePressure_add hp hq
  · intro t x
    have hp' :
        DifferentiableAt ℝ (fun y : NSSpace => p t y) x :=
      smoothSpaceTimePressure_differentiableAt_spatialSlice hp t x
    have hq' :
        DifferentiableAt ℝ (fun y : NSSpace => q t y) x :=
      smoothSpaceTimePressure_differentiableAt_spatialSlice hq t x
    rw [spatialPressureGradient_add hp' hq', hq_zero]
    simpa using hmom t x

/-- Pressure-gauge symmetry on the explicit global output surface: adding a
spatially and temporally constant pressure preserves a global solution. -/
theorem ExplicitConcreteNavierStokesGlobalOutput.addConstantPressure
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (h : ExplicitConcreteNavierStokesGlobalOutput ν u₀)
    (c : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput ν u₀ := by
  exact h.addPressureOfZeroSpatialGradient
    (fun _ : NSTime => fun _ : NSSpace => c)
    (smoothSpaceTimePressure_const c)
    (fun t x => spatialPressureGradient_const c t x)

/-- Pressure-gauge symmetry on the explicit global output surface: adding any
smooth time-only pressure preserves a global solution. -/
theorem ExplicitConcreteNavierStokesGlobalOutput.addTimeOnlyPressure
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (h : ExplicitConcreteNavierStokesGlobalOutput ν u₀)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    ExplicitConcreteNavierStokesGlobalOutput ν u₀ := by
  exact h.addPressureOfZeroSpatialGradient
    (fun t : NSTime => fun _ : NSSpace => π t)
    (smoothSpaceTimePressure_timeOnly hπ)
    (fun t x => spatialPressureGradient_timeOnly π t x)

/-- Pressure-gauge symmetry on the explicit whole-space regularity clause:
adding a slice-wise zero-gradient pressure field preserves the clause on the
same initial datum. -/
theorem ExplicitConcreteNavierStokesRegularityClause_addPressureOfZeroSpatialGradient
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (h : ExplicitConcreteNavierStokesRegularityClause ν u₀)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    ExplicitConcreteNavierStokesRegularityClause ν u₀ := by
  intro hν hsmooth hdiv
  exact
    ExplicitConcreteNavierStokesGlobalOutput.addPressureOfZeroSpatialGradient
      (h hν hsmooth hdiv) q hq hq_zero

/-- Pressure-gauge symmetry on the repaired explicit whole-space regularity
clause: adding a slice-wise zero-gradient pressure field preserves the clause
on the same finite-energy datum. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_addPressureOfZeroSpatialGradient
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause ν u₀)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause ν u₀ := by
  intro hν hsmooth hdiv hfinite
  exact
    ExplicitConcreteNavierStokesGlobalOutput.addPressureOfZeroSpatialGradient
      (h hν hsmooth hdiv hfinite) q hq hq_zero

/-- Pressure-gauge symmetry on the structured fully concrete whole-space
clause: adding a slice-wise zero-gradient pressure field preserves the clause
on the same datum. -/
theorem concreteNavierStokesGlobalRegularityClause_addPressureOfZeroSpatialGradient
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (h :
      NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := u₀
          smooth_initial := hsmooth
          divergence_free_initial := hdiv })
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      { viscosity := ν
        viscosity_pos := hν
        initialVelocity := u₀
        smooth_initial := hsmooth
        divergence_free_initial := hdiv } := by
  have hGlobal : ExplicitConcreteNavierStokesGlobalOutput ν u₀ :=
    (concreteNavierStokesGlobalRegularityClause_iff
      (ν := ν) (u₀ := u₀) hν hsmooth hdiv).mp h
  exact
    ExplicitConcreteNavierStokesGlobalOutput_implies_concreteNavierStokesGlobalRegularityClause
      hν hsmooth hdiv
      (hGlobal.addPressureOfZeroSpatialGradient q hq hq_zero)

/-- Pressure-gauge symmetry on the repaired structured fully concrete
whole-space clause: adding a slice-wise zero-gradient pressure field preserves
the clause on the same finite-energy datum. -/
theorem finiteEnergyConcreteNavierStokesGlobalRegularityClause_addPressureOfZeroSpatialGradient
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
          FiniteEnergyAdmissibleNavierStokesProblemData).toNavierStokesProblemData)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      ({ viscosity := ν
         viscosity_pos := hν
         initialVelocity := u₀
         smooth_initial := hsmooth
         divergence_free_initial := hdiv
         finite_initial_energy := hfinite } :
        FiniteEnergyAdmissibleNavierStokesProblemData).toNavierStokesProblemData := by
  have hGlobal : ExplicitConcreteNavierStokesGlobalOutput ν u₀ :=
    (finiteEnergyConcreteNavierStokesGlobalRegularityClause_iff
      hν hsmooth hdiv hfinite).mp h hν hsmooth hdiv hfinite
  exact
    ExplicitConcreteNavierStokesGlobalOutput_implies_finiteEnergyConcreteNavierStokesGlobalRegularityClause_of_finiteInitialKineticEnergy
      hν hsmooth hdiv hfinite
      (hGlobal.addPressureOfZeroSpatialGradient q hq hq_zero)

/-- A uniform-vorticity continuation clause can be applied equally well after
changing the witness by any smooth pressure gauge with zero spatial gradient,
since the carried uniform vorticity bound is pressure-invariant. -/
theorem ExplicitUniformVorticityContinuationClause_apply_of_uniformVorticityBound_addPressureOfZeroSpatialGradient
    {ν : ℝ} {u₀ : NSInitialVelocity} {T B : ℝ}
    (hClause : ExplicitUniformVorticityContinuationClause ν u₀ T)
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hω : uniformVorticityBoundUpTo W.velocity T B)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    ExplicitConcreteNavierStokesGlobalOutput ν u₀ := by
  have hω' :
      ∃ B' : ℝ,
        uniformVorticityBoundUpTo
          (W.addPressureOfZeroSpatialGradient q hq hq_zero).velocity T B' := by
    refine ⟨B, ?_⟩
    exact W.uniformVorticityBound_addPressureOfZeroSpatialGradient hω q hq hq_zero
  exact hClause hν hsmooth hdiv (W.addPressureOfZeroSpatialGradient q hq hq_zero) hω'

/-- A uniform-vorticity continuation clause can be applied equally well after
changing the witness by a smooth time-only pressure gauge, since the carried
uniform vorticity bound is pressure-invariant. -/
theorem ExplicitUniformVorticityContinuationClause_apply_of_uniformVorticityBound_addTimeOnlyPressure
    {ν : ℝ} {u₀ : NSInitialVelocity} {T B : ℝ}
    (hClause : ExplicitUniformVorticityContinuationClause ν u₀ T)
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hω : uniformVorticityBoundUpTo W.velocity T B)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    ExplicitConcreteNavierStokesGlobalOutput ν u₀ := by
  exact
    ExplicitUniformVorticityContinuationClause_apply_of_uniformVorticityBound_addPressureOfZeroSpatialGradient
      (hClause := hClause) hν hsmooth hdiv W hω
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)

/-- A uniform-vorticity continuation clause at horizon `T'` can be applied
after first changing a larger-slab witness by a smooth zero-spatial-gradient
pressure gauge and then restricting to `0 ≤ t ≤ T' ≤ T`. -/
theorem ExplicitUniformVorticityContinuationClause_apply_of_uniformVorticityBound_addPressureOfZeroSpatialGradient_restrict
    {ν : ℝ} {u₀ : NSInitialVelocity} {T T' B : ℝ}
    (hClause : ExplicitUniformVorticityContinuationClause ν u₀ T')
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hω : uniformVorticityBoundUpTo W.velocity T B)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0)
    (hT : T' ≤ T) :
    ExplicitConcreteNavierStokesGlobalOutput ν u₀ := by
  simpa [ExplicitFiniteTimeRegularityWitness.restrict,
    ExplicitFiniteTimeRegularityWitness.addPressureOfZeroSpatialGradient] using
    (ExplicitUniformVorticityContinuationClause_apply_of_uniformVorticityBound_addPressureOfZeroSpatialGradient
      (hClause := hClause) hν hsmooth hdiv (W := W.restrict hT)
      (hω := W.uniformVorticityBound_restrict hω hT) q hq hq_zero)

/-- A uniform-vorticity continuation clause at horizon `T'` can be applied
after first changing a larger-slab witness by a smooth time-only pressure gauge
and then restricting to `0 ≤ t ≤ T' ≤ T`. -/
theorem ExplicitUniformVorticityContinuationClause_apply_of_uniformVorticityBound_addTimeOnlyPressure_restrict
    {ν : ℝ} {u₀ : NSInitialVelocity} {T T' B : ℝ}
    (hClause : ExplicitUniformVorticityContinuationClause ν u₀ T')
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hω : uniformVorticityBoundUpTo W.velocity T B)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    (hT : T' ≤ T) :
    ExplicitConcreteNavierStokesGlobalOutput ν u₀ := by
  exact
    ExplicitUniformVorticityContinuationClause_apply_of_uniformVorticityBound_addPressureOfZeroSpatialGradient_restrict
      (hClause := hClause) hν hsmooth hdiv W hω
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)
      hT



end UniformVorticityContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
