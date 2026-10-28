import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityContinuationSurface

/-!
# Uniform-Vorticity Bounds and Witness Restriction Toolkit

This module contains reusable vorticity-bound algebra, concrete field
bounds, finite-time witness restriction, and horizon-monotonicity lemmas for
the concrete uniform-vorticity continuation surface.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section UniformVorticityContinuation

/-- Direct zero-field uniform vorticity bound on every slab. -/
theorem uniformVorticityBoundUpTo_zero
    (T : ℝ) :
    uniformVorticityBoundUpTo (0 : NSVelocityField) T 0 := by
  constructor
  · exact le_rfl
  · intro t x ht0 htT
    simp [spatialVorticity_zero]

/-- Constant velocity fields carry the explicit zero vorticity bound on every
slab.  This is a real differential-side nonzero family, although it will later
be blocked by the bounded-energy surface unless the constant is zero. -/
theorem uniformVorticityBoundUpTo_constantVelocityField
    (c : NSSpace) (T : ℝ) :
    uniformVorticityBoundUpTo (constantVelocityField c) T 0 := by
  constructor
  · exact le_rfl
  · intro t x ht0 htT
    simp [spatialVorticity_constantVelocityField]

/-- The steady linear shear field carries the explicit constant vorticity bound
`B = |a|` on every slab. -/
theorem uniformVorticityBoundUpTo_linearShearVelocityField
    (a T : ℝ) :
    uniformVorticityBoundUpTo (linearShearVelocityField a) T |a| := by
  constructor
  · exact abs_nonneg a
  · intro t x ht0 htT
    simp [spatialVorticity_linearShearVelocityField]

/-- The steady field `u(t,x) = (a * x₁, 0, b)` carries the same explicit
constant vorticity bound `B = |a|` as pure linear shear on every slab. -/
theorem uniformVorticityBoundUpTo_linearShearVerticalDriftVelocityField
    (a b T : ℝ) :
    uniformVorticityBoundUpTo (linearShearVerticalDriftVelocityField a b) T |a| := by
  constructor
  · exact abs_nonneg a
  · intro t x ht0 htT
    simp [spatialVorticity_linearShearVerticalDriftVelocityField]

/-- The steady field `u(t,x) = (a * x₁, b, 0)` carries the same explicit
constant vorticity bound `B = |a|` as pure linear shear on every slab. -/
theorem uniformVorticityBoundUpTo_linearShearHorizontalDriftVelocityField
    (a b T : ℝ) :
    uniformVorticityBoundUpTo (linearShearHorizontalDriftVelocityField a b) T |a| := by
  constructor
  · exact abs_nonneg a
  · intro t x ht0 htT
    simp [spatialVorticity_linearShearHorizontalDriftVelocityField]

/-- The steady field `u(t,x) = (a * x₁, b, c)` carries the same explicit
constant vorticity bound `B = |a|` as pure linear shear on every slab. -/
theorem uniformVorticityBoundUpTo_linearShearFullDriftVelocityField
    (a b c T : ℝ) :
    uniformVorticityBoundUpTo (linearShearFullDriftVelocityField a b c) T |a| := by
  constructor
  · exact abs_nonneg a
  · intro t x ht0 htT
    simp [spatialVorticity_linearShearFullDriftVelocityField]

/-- The damped sinusoidal heat-shear field carries the explicit slab vorticity
bound `B = |a * k|` whenever the viscosity is nonnegative. -/
theorem uniformVorticityBoundUpTo_heatShearVelocityField
    (ν a k T : ℝ)
    (hν : 0 ≤ ν) :
    uniformVorticityBoundUpTo (heatShearVelocityField ν a k) T |a * k| := by
  constructor
  · exact abs_nonneg (a * k)
  · intro t x ht0 htT
    rw [spatialVorticity_heatShearVelocityField]
    have hexp_le : Real.exp (-(ν * k ^ (2 : ℕ)) * t) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have hk2 : 0 ≤ k ^ (2 : ℕ) := by positivity
      have hprod : 0 ≤ ν * k ^ (2 : ℕ) := mul_nonneg hν hk2
      nlinarith
    calc
      ‖EuclideanSpace.single nsCoord2
          (-(a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.cos (k * x nsCoord1) * k))‖
          = |a| * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * |Real.cos (k * x nsCoord1)| * |k| := by
            simp [mul_assoc, mul_left_comm, mul_comm]
      _ ≤ |a| * 1 * |Real.cos (k * x nsCoord1)| * |k| := by
            gcongr
      _ ≤ |a| * 1 * 1 * |k| := by
            gcongr
            simpa using Real.abs_cos_le_one (k * x nsCoord1)
      _ = |a * k| := by
            rw [abs_mul]
            ring

/-- The heat-shear family with constant streamwise drift carries the same slab
vorticity bound `B = |a * k|` as pure heat shear whenever the viscosity is
nonnegative. -/
theorem uniformVorticityBoundUpTo_heatShearStreamwiseDriftVelocityField
    (ν a k d T : ℝ)
    (hν : 0 ≤ ν) :
    uniformVorticityBoundUpTo (heatShearStreamwiseDriftVelocityField ν a k d) T |a * k| := by
  constructor
  · exact abs_nonneg (a * k)
  · intro t x ht0 htT
    rw [spatialVorticity_heatShearStreamwiseDriftVelocityField]
    have hexp_le : Real.exp (-(ν * k ^ (2 : ℕ)) * t) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have hk2 : 0 ≤ k ^ (2 : ℕ) := by positivity
      have hprod : 0 ≤ ν * k ^ (2 : ℕ) := mul_nonneg hν hk2
      nlinarith
    calc
      ‖EuclideanSpace.single nsCoord2
          (-(a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.cos (k * x nsCoord1) * k))‖
          = |a| * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * |Real.cos (k * x nsCoord1)| * |k| := by
            simp [mul_assoc, mul_left_comm, mul_comm]
      _ ≤ |a| * 1 * |Real.cos (k * x nsCoord1)| * |k| := by
            gcongr
      _ ≤ |a| * 1 * 1 * |k| := by
            gcongr
            simpa using Real.abs_cos_le_one (k * x nsCoord1)
      _ = |a * k| := by
            rw [abs_mul]
            ring

/-- The heat-shear family with vertical drift carries the same slab vorticity
bound `B = |a * k|` as pure heat shear whenever the viscosity is
nonnegative. -/
theorem uniformVorticityBoundUpTo_heatShearVerticalDriftVelocityField
    (ν a k c T : ℝ)
    (hν : 0 ≤ ν) :
    uniformVorticityBoundUpTo (heatShearVerticalDriftVelocityField ν a k c) T |a * k| := by
  constructor
  · exact abs_nonneg (a * k)
  · intro t x ht0 htT
    rw [spatialVorticity_heatShearVerticalDriftVelocityField]
    have hexp_le : Real.exp (-(ν * k ^ (2 : ℕ)) * t) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have hk2 : 0 ≤ k ^ (2 : ℕ) := by positivity
      have hprod : 0 ≤ ν * k ^ (2 : ℕ) := mul_nonneg hν hk2
      nlinarith
    calc
      ‖EuclideanSpace.single nsCoord2
          (-(a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.cos (k * x nsCoord1) * k))‖
          = |a| * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * |Real.cos (k * x nsCoord1)| * |k| := by
            simp [mul_assoc, mul_left_comm, mul_comm]
      _ ≤ |a| * 1 * |Real.cos (k * x nsCoord1)| * |k| := by
            gcongr
      _ ≤ |a| * 1 * 1 * |k| := by
            gcongr
            simpa using Real.abs_cos_le_one (k * x nsCoord1)
      _ = |a * k| := by
            rw [abs_mul]
            ring

/-- The heat-shear family with full constant drift carries the same slab
vorticity bound `B = |a * k|` as pure heat shear whenever the viscosity is
nonnegative. -/
theorem uniformVorticityBoundUpTo_heatShearFullDriftVelocityField
    (ν a k d c T : ℝ)
    (hν : 0 ≤ ν) :
    uniformVorticityBoundUpTo (heatShearFullDriftVelocityField ν a k d c) T |a * k| := by
  constructor
  · exact abs_nonneg (a * k)
  · intro t x ht0 htT
    rw [spatialVorticity_heatShearFullDriftVelocityField]
    have hexp_le : Real.exp (-(ν * k ^ (2 : ℕ)) * t) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have hk2 : 0 ≤ k ^ (2 : ℕ) := by positivity
      have hprod : 0 ≤ ν * k ^ (2 : ℕ) := mul_nonneg hν hk2
      nlinarith
    calc
      ‖EuclideanSpace.single nsCoord2
          (-(a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.cos (k * x nsCoord1) * k))‖
          = |a| * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * |Real.cos (k * x nsCoord1)| * |k| := by
            simp [mul_assoc, mul_left_comm, mul_comm]
      _ ≤ |a| * 1 * |Real.cos (k * x nsCoord1)| * |k| := by
            gcongr
      _ ≤ |a| * 1 * 1 * |k| := by
            gcongr
            simpa using Real.abs_cos_le_one (k * x nsCoord1)
      _ = |a * k| := by
            rw [abs_mul]
            ring

/-- The transported heat-shear family carries the same slab vorticity bound
`B = |a * k|` as pure heat shear whenever the viscosity is nonnegative. -/
theorem uniformVorticityBoundUpTo_heatShearTransportVelocityField
    (ν a k b T : ℝ)
    (hν : 0 ≤ ν) :
    uniformVorticityBoundUpTo (heatShearTransportVelocityField ν a k b) T |a * k| := by
  constructor
  · exact abs_nonneg (a * k)
  · intro t x ht0 htT
    rw [spatialVorticity_heatShearTransportVelocityField]
    have hexp_le : Real.exp (-(ν * k ^ (2 : ℕ)) * t) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have hk2 : 0 ≤ k ^ (2 : ℕ) := by positivity
      have hprod : 0 ≤ ν * k ^ (2 : ℕ) := mul_nonneg hν hk2
      nlinarith
    calc
      ‖EuclideanSpace.single nsCoord2
          (-(a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
            Real.cos (k * (x nsCoord1 - b * t)) * k))‖
          = |a| * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
              |Real.cos (k * (x nsCoord1 - b * t))| * |k| := by
            simp [mul_assoc, mul_left_comm, mul_comm]
      _ ≤ |a| * 1 * |Real.cos (k * (x nsCoord1 - b * t))| * |k| := by
            gcongr
      _ ≤ |a| * 1 * 1 * |k| := by
            gcongr
            simpa using Real.abs_cos_le_one (k * (x nsCoord1 - b * t))
      _ = |a * k| := by
            rw [abs_mul]
            ring

/-- The transported full-drift heat-shear family carries the same slab
vorticity bound `B = |a * k|` as pure heat shear whenever the viscosity is
nonnegative. -/
theorem uniformVorticityBoundUpTo_heatShearTransportFullDriftVelocityField
    (ν a k b d c T : ℝ)
    (hν : 0 ≤ ν) :
    uniformVorticityBoundUpTo (heatShearTransportFullDriftVelocityField ν a k b d c) T |a * k| := by
  constructor
  · exact abs_nonneg (a * k)
  · intro t x ht0 htT
    rw [spatialVorticity_heatShearTransportFullDriftVelocityField]
    have hexp_le : Real.exp (-(ν * k ^ (2 : ℕ)) * t) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have hk2 : 0 ≤ k ^ (2 : ℕ) := by positivity
      have hprod : 0 ≤ ν * k ^ (2 : ℕ) := mul_nonneg hν hk2
      nlinarith
    calc
      ‖EuclideanSpace.single nsCoord2
          (-(a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
            Real.cos (k * (x nsCoord1 - b * t)) * k))‖
          = |a| * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
              |Real.cos (k * (x nsCoord1 - b * t))| * |k| := by
            simp [mul_assoc, mul_left_comm, mul_comm]
      _ ≤ |a| * 1 * |Real.cos (k * (x nsCoord1 - b * t))| * |k| := by
            gcongr
      _ ≤ |a| * 1 * 1 * |k| := by
            gcongr
            simpa using Real.abs_cos_le_one (k * (x nsCoord1 - b * t))
      _ = |a * k| := by
            rw [abs_mul]
            ring

/-- Uniform slab vorticity bounds are stable under constant velocity rescaling:
if `‖ω_u‖ ≤ B`, then `‖ω_{a•u}‖ ≤ |a| * B` on the same slab. -/
theorem uniformVorticityBoundUpTo_const_smul
    {u : NSVelocityField} {T B : ℝ}
    (a : ℝ)
    (hω : uniformVorticityBoundUpTo u T B) :
    uniformVorticityBoundUpTo (a • u) T (|a| * B) := by
  rcases hω with ⟨hB, hbound⟩
  constructor
  · exact mul_nonneg (abs_nonneg a) hB
  · intro t x ht0 htT
    have hωtx : ‖spatialVorticity u t x‖ ≤ B := hbound t x ht0 htT
    have hsmul :
        spatialVorticity (a • u) t x = a • spatialVorticity u t x := by
      ext i
      fin_cases i <;>
        simp [spatialVorticity, spatialDerivativeComponent_const_smul, mul_sub]
    rw [hsmul]
    calc
      ‖a • spatialVorticity u t x‖ = ‖a‖ * ‖spatialVorticity u t x‖ := by
        simp [norm_smul]
      _ ≤ ‖a‖ * B := mul_le_mul_of_nonneg_left hωtx (norm_nonneg a)
      _ = |a| * B := by simp [Real.norm_eq_abs]

/-- Uniform slab vorticity bounds are monotone in the bound parameter. -/
theorem uniformVorticityBoundUpTo_mono
    {u : NSVelocityField} {T B B' : ℝ}
    (hω : uniformVorticityBoundUpTo u T B)
    (hBB' : B ≤ B') :
    uniformVorticityBoundUpTo u T B' := by
  rcases hω with ⟨hB, hbound⟩
  constructor
  · exact le_trans hB hBB'
  · intro t x ht0 htT
    exact le_trans (hbound t x ht0 htT) hBB'

/-- Uniform slab vorticity bounds add for smooth space-time velocity fields. -/
theorem uniformVorticityBoundUpTo_add
    {u v : NSVelocityField} {T B B' : ℝ}
    (hu : smoothSpaceTimeVelocity u)
    (hv : smoothSpaceTimeVelocity v)
    (hω : uniformVorticityBoundUpTo u T B)
    (hω' : uniformVorticityBoundUpTo v T B') :
    uniformVorticityBoundUpTo (u + v) T (B + B') := by
  rcases hω with ⟨hB, hbound⟩
  rcases hω' with ⟨hB', hbound'⟩
  constructor
  · exact add_nonneg hB hB'
  · intro t x ht0 htT
    rw [spatialVorticity_add
      (u := u) (v := v) (t := t) (x := x)
      (smoothSpaceTimeVelocity_differentiableAt_spatialSlice hu t x)
      (smoothSpaceTimeVelocity_differentiableAt_spatialSlice hv t x)]
    calc
      ‖spatialVorticity u t x + spatialVorticity v t x‖ ≤
          ‖spatialVorticity u t x‖ + ‖spatialVorticity v t x‖ := norm_add_le _ _
      _ ≤ B + B' := add_le_add (hbound t x ht0 htT) (hbound' t x ht0 htT)

/-- Uniform slab vorticity bounds are stable under sign flip of the velocity
field. -/
theorem uniformVorticityBoundUpTo_neg
    {u : NSVelocityField} {T B : ℝ}
    (hω : uniformVorticityBoundUpTo u T B) :
    uniformVorticityBoundUpTo (-u) T B := by
  have hsmul :
      uniformVorticityBoundUpTo ((-1 : ℝ) • u) T (|(-1 : ℝ)| * B) :=
    uniformVorticityBoundUpTo_const_smul (a := (-1 : ℝ)) hω
  simpa using hsmul

/-- Uniform slab vorticity bounds are stable under subtraction for smooth
space-time velocity fields. -/
theorem uniformVorticityBoundUpTo_sub
    {u v : NSVelocityField} {T B B' : ℝ}
    (hu : smoothSpaceTimeVelocity u)
    (hv : smoothSpaceTimeVelocity v)
    (hω : uniformVorticityBoundUpTo u T B)
    (hω' : uniformVorticityBoundUpTo v T B') :
    uniformVorticityBoundUpTo (u - v) T (B + B') := by
  simpa [sub_eq_add_neg] using
    (uniformVorticityBoundUpTo_add
      (u := u) (v := -v) (T := T) (B := B) (B' := B')
      hu (smoothSpaceTimeVelocity_neg hv) hω (uniformVorticityBoundUpTo_neg hω'))

/-- Uniform slab vorticity bounds are stable under linear combinations for
smooth space-time velocity fields. -/
theorem uniformVorticityBoundUpTo_linearCombination
    {u v : NSVelocityField} {T B B' : ℝ}
    (hu : smoothSpaceTimeVelocity u)
    (hv : smoothSpaceTimeVelocity v)
    (hω : uniformVorticityBoundUpTo u T B)
    (hω' : uniformVorticityBoundUpTo v T B')
    (a b : ℝ) :
    uniformVorticityBoundUpTo (a • u + b • v) T (|a| * B + |b| * B') := by
  exact
    uniformVorticityBoundUpTo_add
      (u := a • u) (v := b • v) (T := T)
      (B := |a| * B) (B' := |b| * B')
      (smoothSpaceTimeVelocity_const_smul a hu)
      (smoothSpaceTimeVelocity_const_smul b hv)
      (uniformVorticityBoundUpTo_const_smul (a := a) hω)
      (uniformVorticityBoundUpTo_const_smul (a := b) hω')

/-- Uniform slab vorticity bounds restrict from a larger time horizon `T` to
any smaller one `T' ≤ T`. -/
theorem uniformVorticityBoundUpTo_restrict
    {u : NSVelocityField} {T T' B : ℝ}
    (hω : uniformVorticityBoundUpTo u T B)
    (hT : T' ≤ T) :
    uniformVorticityBoundUpTo u T' B := by
  rcases hω with ⟨hB, hbound⟩
  constructor
  · exact hB
  · intro t x ht0 htT'
    exact hbound t x ht0 (le_trans htT' hT)

/-- Uniform slab kinetic-energy bounds restrict from a larger time horizon `T`
to any smaller one `T' ≤ T`. -/
theorem boundedKineticEnergyUpTo_restrict
    {u : NSVelocityField} {T T' : ℝ}
    (hE : boundedKineticEnergyUpTo u T)
    (hT : T' ≤ T) :
    boundedKineticEnergyUpTo u T' := by
  rcases hE with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro t ht0 htT'
  exact hbound t ht0 (le_trans htT' hT)

/-- Restrict an explicit finite-time witness from a slab `0 ≤ t ≤ T` to any
shorter slab `0 ≤ t ≤ T'` with `T' ≤ T`. -/
def ExplicitFiniteTimeRegularityWitness.restrict
    {ν : ℝ} {u₀ : NSInitialVelocity} {T T' : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hT : T' ≤ T) :
    ExplicitFiniteTimeRegularityWitness ν u₀ T' where
  velocity := W.velocity
  pressure := W.pressure
  smooth_velocity := W.smooth_velocity
  smooth_pressure := W.smooth_pressure
  momentum_equation_on := by
    intro t x ht0 htT'
    exact W.momentum_equation_on t x ht0 (le_trans htT' hT)
  incompressible_on := by
    intro t x ht0 htT'
    exact W.incompressible_on t x ht0 (le_trans htT' hT)
  initial_condition := W.initial_condition
  bounded_energy_on := boundedKineticEnergyUpTo_restrict W.bounded_energy_on hT

/-- Uniform slab vorticity control transports along witness restriction. -/
theorem ExplicitFiniteTimeRegularityWitness.uniformVorticityBound_restrict
    {ν : ℝ} {u₀ : NSInitialVelocity} {T T' B : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hω : uniformVorticityBoundUpTo W.velocity T B)
    (hT : T' ≤ T) :
    uniformVorticityBoundUpTo (W.restrict hT).velocity T' B := by
  simpa [ExplicitFiniteTimeRegularityWitness.restrict] using
    (uniformVorticityBoundUpTo_restrict (u := W.velocity) (T := T) (T' := T') (B := B) hω hT)

/-- Witness-level transport of uniform vorticity control under linear
combination of slab velocities. -/
theorem ExplicitFiniteTimeRegularityWitness.uniformVorticityBound_linearCombination
    {ν ν' : ℝ} {u₀ u₀' : NSInitialVelocity} {T B B' : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (W' : ExplicitFiniteTimeRegularityWitness ν' u₀' T)
    (hω : uniformVorticityBoundUpTo W.velocity T B)
    (hω' : uniformVorticityBoundUpTo W'.velocity T B')
    (a b : ℝ) :
    uniformVorticityBoundUpTo (a • W.velocity + b • W'.velocity) T (|a| * B + |b| * B') := by
  exact uniformVorticityBoundUpTo_linearCombination
    W.smooth_velocity W'.smooth_velocity hω hω' a b

/-- Witness-level transport of uniform vorticity control under linear
combination followed by restriction to a shorter slab `0 ≤ t ≤ T'` with
`T' ≤ T`. -/
theorem ExplicitFiniteTimeRegularityWitness.uniformVorticityBound_linearCombination_restrict
    {ν ν' : ℝ} {u₀ u₀' : NSInitialVelocity} {T T' B B' : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (W' : ExplicitFiniteTimeRegularityWitness ν' u₀' T)
    (hω : uniformVorticityBoundUpTo W.velocity T B)
    (hω' : uniformVorticityBoundUpTo W'.velocity T B')
    (a b : ℝ)
    (hT : T' ≤ T) :
    uniformVorticityBoundUpTo
      (a • (W.restrict hT).velocity + b • (W'.restrict hT).velocity) T'
      (|a| * B + |b| * B') := by
  simpa [ExplicitFiniteTimeRegularityWitness.restrict] using
    (uniformVorticityBoundUpTo_restrict
      (u := a • W.velocity + b • W'.velocity) (T := T) (T' := T')
      (B := |a| * B + |b| * B')
      (W.uniformVorticityBound_linearCombination W' hω hω' a b) hT)

/-- A uniform-vorticity continuation clause at horizon `T'` can be applied to
any larger-slab witness by restricting the witness and its uniform bound from
`0 ≤ t ≤ T` down to `0 ≤ t ≤ T' ≤ T`. -/
theorem ExplicitUniformVorticityContinuationClause_apply_of_uniformVorticityBound_restrict
    {ν : ℝ} {u₀ : NSInitialVelocity} {T T' B : ℝ}
    (hClause : ExplicitUniformVorticityContinuationClause ν u₀ T')
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hω : uniformVorticityBoundUpTo W.velocity T B)
    (hT : T' ≤ T) :
    ExplicitConcreteNavierStokesGlobalOutput ν u₀ := by
  have hω' :
      ∃ B' : ℝ,
        uniformVorticityBoundUpTo (W.restrict hT).velocity T' B' := by
    refine ⟨B, ?_⟩
    exact W.uniformVorticityBound_restrict hω hT
  exact hClause hν hsmooth hdiv (W.restrict hT) hω'

/-- Horizon monotonicity for the uniform-vorticity continuation clause:
if the clause is available on a smaller slab `0 ≤ t ≤ Tsmall`, then it is also
available on every larger slab `0 ≤ t ≤ Tlarge` with `Tsmall ≤ Tlarge`, by
restricting any larger-slab witness to the smaller slab. -/
theorem ExplicitUniformVorticityContinuationClause_mono_horizon
    {ν : ℝ} {u₀ : NSInitialVelocity} {Tsmall Tlarge : ℝ}
    (hClauseSmall : ExplicitUniformVorticityContinuationClause ν u₀ Tsmall)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitUniformVorticityContinuationClause ν u₀ Tlarge := by
  intro hν hsmooth hdiv W hω
  rcases hω with ⟨B, hbound⟩
  exact
    ExplicitUniformVorticityContinuationClause_apply_of_uniformVorticityBound_restrict
      hClauseSmall hν hsmooth hdiv W hbound hT

/-- The repaired uniform-vorticity continuation clause at horizon `T'` can be
applied to any larger-slab witness by restricting the witness and its uniform
bound from `0 ≤ t ≤ T` down to `0 ≤ t ≤ T' ≤ T`. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_apply_of_uniformVorticityBound_restrict
    {ν : ℝ} {u₀ : NSInitialVelocity} {T T' B : ℝ}
    (hClause : ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T')
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (hfinite : finiteInitialKineticEnergy u₀)
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hω : uniformVorticityBoundUpTo W.velocity T B)
    (hT : T' ≤ T) :
    ExplicitConcreteNavierStokesGlobalOutput ν u₀ := by
  have hω' :
      ∃ B' : ℝ,
        uniformVorticityBoundUpTo (W.restrict hT).velocity T' B' := by
    refine ⟨B, ?_⟩
    exact W.uniformVorticityBound_restrict hω hT
  exact hClause hν hsmooth hdiv hfinite (W.restrict hT) hω'

/-- Horizon monotonicity for the repaired uniform-vorticity continuation
clause: if the clause is available on a smaller slab `0 ≤ t ≤ Tsmall`, then it
is also available on every larger slab `0 ≤ t ≤ Tlarge` with
`Tsmall ≤ Tlarge`, by restricting any larger-slab witness to the smaller slab.
-/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_mono_horizon
    {ν : ℝ} {u₀ : NSInitialVelocity} {Tsmall Tlarge : ℝ}
    (hClauseSmall : ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ Tsmall)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ Tlarge := by
  intro hν hsmooth hdiv hfinite W hω
  rcases hω with ⟨B, hbound⟩
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_apply_of_uniformVorticityBound_restrict
      hClauseSmall hν hsmooth hdiv hfinite W hbound hT


end UniformVorticityContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
