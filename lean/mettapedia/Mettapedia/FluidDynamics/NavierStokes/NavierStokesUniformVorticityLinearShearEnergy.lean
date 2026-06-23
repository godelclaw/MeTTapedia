import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityEnergyObstructions
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3Basic
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3LocalOperators
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3Smoothness
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3FirstOrder
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3PressureObstructions
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3Laplacian
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3Momentum
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3Vorticity
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3TransportProfiles
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3TransportDerivatives
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3TransportLaplacian
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3TransportMomentum
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3TransportVorticity
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3VorticityNorms
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Linear-Shear Energy Obstructions for Uniform-Vorticity Continuation

This module contains the reusable kinetic-energy identities and finite-energy
obstructions for steady linear-shear initial data and its constant-drift variants.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section UniformVorticityContinuation

/-- Kinetic-energy density carried by the linear shear initial profile
`x ↦ (a * x₁, 0, 0)`. -/
def linearShearKineticEnergyDensity (a : ℝ) : NSSpace → ℝ :=
  fun x => (a * x nsCoord1) * (a * x nsCoord1)

/-- The linear shear kinetic-energy density is continuous on `ℝ^3`. -/
theorem continuous_linearShearKineticEnergyDensity
    (a : ℝ) :
    Continuous (linearShearKineticEnergyDensity a) := by
  have hcoord : Continuous fun x : NSSpace => x nsCoord1 := by
    simpa using (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ).continuous
  exact (continuous_const.mul hcoord).mul (continuous_const.mul hcoord)

/-- Nonzero linear shear initial data have nonintegrable kinetic-energy density
on `ℝ^3`.  The proof uses the exact Haar-scaling identity on `ℝ^3`: if this
density were integrable, scaling by `x ↦ 2x` would force its integral to be
both `4I` and `I/8`, hence zero, contradicting positivity. -/
theorem not_integrable_linearShearKineticEnergyDensity
    {a : ℝ} (ha : a ≠ 0) :
    ¬ MeasureTheory.Integrable (linearShearKineticEnergyDensity a) := by
  intro hInt
  let x1 : NSSpace := EuclideanSpace.single nsCoord1 (1 : ℝ)
  have hnonneg : ∀ x, 0 ≤ linearShearKineticEnergyDensity a x := by
    intro x
    dsimp [linearShearKineticEnergyDensity]
    nlinarith [sq_nonneg (a * x nsCoord1)]
  have hx1 : linearShearKineticEnergyDensity a x1 ≠ 0 := by
    dsimp [x1, linearShearKineticEnergyDensity]
    simp [nsCoord1, ha]
  have hpos : 0 < ∫ x, linearShearKineticEnergyDensity a x := by
    exact MeasureTheory.integral_pos_of_integrable_nonneg_nonzero
      (x := x1)
      (continuous_linearShearKineticEnergyDensity a)
      hInt hnonneg hx1
  let I : ℝ := ∫ x, linearShearKineticEnergyDensity a x
  have hcomp :
      ∫ x, linearShearKineticEnergyDensity a ((2 : ℝ) • x) = (4 : ℝ) * I := by
    calc
      ∫ x, linearShearKineticEnergyDensity a ((2 : ℝ) • x)
          = ∫ x, (4 : ℝ) * linearShearKineticEnergyDensity a x := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with x
              simp [linearShearKineticEnergyDensity]
              ring
      _ = (4 : ℝ) * I := by
            simp [I, MeasureTheory.integral_const_mul]
  have hchange :
      ∫ x, linearShearKineticEnergyDensity a ((2 : ℝ) • x) =
        ((2 : ℝ) ^ Module.finrank ℝ NSSpace)⁻¹ * I := by
    simpa [smul_eq_mul, I] using
      (MeasureTheory.Measure.integral_comp_smul_of_nonneg
        (μ := (MeasureTheory.volume : MeasureTheory.Measure NSSpace))
        (f := linearShearKineticEnergyDensity a) (R := (2 : ℝ)) (hR := by positivity))
  have hEq :
      (4 : ℝ) * I = ((2 : ℝ) ^ Module.finrank ℝ NSSpace)⁻¹ * I := by
    rw [← hcomp]
    exact hchange
  have hzero : I = 0 := by
    norm_num at hEq
    linarith
  have : 0 < I := by
    simpa [I] using hpos
  linarith

/-- Kinetic-energy density of the steady linear shear field is exactly the
quadratic shear profile on every time slice. -/
theorem kineticEnergyDensity_linearShearVelocityField
    (a : ℝ) (t : NSTime) :
    kineticEnergyDensity (linearShearVelocityField a) t =
      linearShearKineticEnergyDensity a := by
  funext x
  rw [kineticEnergyDensity, linearShearVelocityField, linearShearInitialVelocity_apply]
  simpa [linearShearKineticEnergyDensity, pow_two] using
    (sq_abs (a * x nsCoord1))

/-- A steady linear shear field with nonzero shear coefficient is not spatially
integrable on `ℝ^3` with respect to the kinetic-energy density on any time
slice. -/
theorem not_integrable_kineticEnergyDensity_linearShearVelocityField
    {a : ℝ} (ha : a ≠ 0) (t : NSTime) :
    ¬ MeasureTheory.Integrable (kineticEnergyDensity (linearShearVelocityField a) t) := by
  intro hInt
  have hIntShear : MeasureTheory.Integrable (linearShearKineticEnergyDensity a) := by
    simpa [kineticEnergyDensity_linearShearVelocityField a t] using hInt
  exact not_integrable_linearShearKineticEnergyDensity ha hIntShear

/-- Therefore a steady linear shear field with nonzero shear coefficient never
satisfies the concrete global bounded-energy predicate on `ℝ^3`. -/
theorem not_boundedKineticEnergy_linearShearVelocityField
    {a : ℝ} (ha : a ≠ 0) :
    ¬ boundedKineticEnergy (linearShearVelocityField a) := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_linearShearVelocityField
      (a := a) ha 0 (hbound 0).1

/-- On every nonnegative slab, a steady linear shear field with nonzero shear
coefficient also fails the finite-time bounded-energy predicate. -/
theorem not_boundedKineticEnergyUpTo_linearShearVelocityField
    {a T : ℝ}
    (ha : a ≠ 0)
    (hT : 0 ≤ T) :
    ¬ boundedKineticEnergyUpTo (linearShearVelocityField a) T := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_linearShearVelocityField
      (a := a) ha 0 ((hbound 0 le_rfl hT).1)

/-- Kinetic-energy density of the steady affine shear field `u(t,x) = (a * x₁,
0, b)` is the linear-shear density plus the constant drift contribution `b²`
on every time slice. -/
theorem kineticEnergyDensity_linearShearVerticalDriftVelocityField
    (a b : ℝ) (t : NSTime) :
    kineticEnergyDensity (linearShearVerticalDriftVelocityField a b) t =
      fun x => linearShearKineticEnergyDensity a x + b ^ (2 : ℕ) := by
  funext x
  have hs : (|a| * |x.ofLp 1|) ^ (2 : ℕ) = linearShearKineticEnergyDensity a x := by
    rw [linearShearKineticEnergyDensity]
    calc
      (|a| * |x.ofLp 1|) ^ (2 : ℕ) = |a * x.ofLp 1| ^ (2 : ℕ) := by rw [abs_mul]
      _ = a * x.ofLp 1 * (a * x.ofLp 1) := by
        simpa [pow_two] using (sq_abs (a * x.ofLp 1))
  rw [kineticEnergyDensity, linearShearVerticalDriftVelocityField_apply]
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
  simp [nsCoord0, nsCoord1, nsCoord2, hs]

/-- A steady affine shear field with nonzero shear coefficient is not spatially
integrable on `ℝ^3` with respect to the kinetic-energy density on any time
slice. -/
theorem not_integrable_kineticEnergyDensity_linearShearVerticalDriftVelocityField
    {a b : ℝ} (ha : a ≠ 0) (t : NSTime) :
    ¬ MeasureTheory.Integrable
      (kineticEnergyDensity (linearShearVerticalDriftVelocityField a b) t) := by
  intro hInt
  have hIntDrift :
      MeasureTheory.Integrable (fun x => linearShearKineticEnergyDensity a x + b ^ (2 : ℕ)) := by
    simpa [kineticEnergyDensity_linearShearVerticalDriftVelocityField a b t] using hInt
  have hIntShear : MeasureTheory.Integrable (linearShearKineticEnergyDensity a) := by
    refine MeasureTheory.Integrable.mono' hIntDrift
      (continuous_linearShearKineticEnergyDensity a).aestronglyMeasurable ?_
    filter_upwards with x
    have hx : 0 ≤ linearShearKineticEnergyDensity a x := by
      dsimp [linearShearKineticEnergyDensity]
      nlinarith [sq_nonneg (a * x nsCoord1)]
    rw [Real.norm_of_nonneg hx]
    exact le_add_of_nonneg_right (by positivity)
  exact not_integrable_linearShearKineticEnergyDensity ha hIntShear

/-- Therefore a steady affine shear field with nonzero shear coefficient never
satisfies the concrete global bounded-energy predicate on `ℝ^3`. -/
theorem not_boundedKineticEnergy_linearShearVerticalDriftVelocityField
    {a b : ℝ} (ha : a ≠ 0) :
    ¬ boundedKineticEnergy (linearShearVerticalDriftVelocityField a b) := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_linearShearVerticalDriftVelocityField
      (a := a) (b := b) ha 0 (hbound 0).1

/-- On every nonnegative slab, a steady affine shear field with nonzero shear
coefficient also fails the finite-time bounded-energy predicate. -/
theorem not_boundedKineticEnergyUpTo_linearShearVerticalDriftVelocityField
    {a b T : ℝ}
    (ha : a ≠ 0)
    (hT : 0 ≤ T) :
    ¬ boundedKineticEnergyUpTo (linearShearVerticalDriftVelocityField a b) T := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_linearShearVerticalDriftVelocityField
      (a := a) (b := b) ha 0 ((hbound 0 le_rfl hT).1)

/-- Kinetic-energy density of the steady affine shear field `u(t,x) = (a * x₁,
b, 0)` is the linear-shear density plus the constant drift contribution `b²`
on every time slice. -/
theorem kineticEnergyDensity_linearShearHorizontalDriftVelocityField
    (a b : ℝ) (t : NSTime) :
    kineticEnergyDensity (linearShearHorizontalDriftVelocityField a b) t =
      fun x => linearShearKineticEnergyDensity a x + b ^ (2 : ℕ) := by
  funext x
  have hs : (|a| * |x.ofLp 1|) ^ (2 : ℕ) = linearShearKineticEnergyDensity a x := by
    rw [linearShearKineticEnergyDensity]
    calc
      (|a| * |x.ofLp 1|) ^ (2 : ℕ) = |a * x.ofLp 1| ^ (2 : ℕ) := by rw [abs_mul]
      _ = a * x.ofLp 1 * (a * x.ofLp 1) := by
        simpa [pow_two] using (sq_abs (a * x.ofLp 1))
  rw [kineticEnergyDensity, linearShearHorizontalDriftVelocityField_apply]
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
  simp [nsCoord0, nsCoord1, hs]

/-- A steady affine shear field with nonzero shear coefficient is not spatially
integrable on `ℝ^3` with respect to the kinetic-energy density on any time
slice. -/
theorem not_integrable_kineticEnergyDensity_linearShearHorizontalDriftVelocityField
    {a b : ℝ} (ha : a ≠ 0) (t : NSTime) :
    ¬ MeasureTheory.Integrable
      (kineticEnergyDensity (linearShearHorizontalDriftVelocityField a b) t) := by
  intro hInt
  have hIntDrift :
      MeasureTheory.Integrable (fun x => linearShearKineticEnergyDensity a x + b ^ (2 : ℕ)) := by
    simpa [kineticEnergyDensity_linearShearHorizontalDriftVelocityField a b t] using hInt
  have hIntShear : MeasureTheory.Integrable (linearShearKineticEnergyDensity a) := by
    refine MeasureTheory.Integrable.mono' hIntDrift
      (continuous_linearShearKineticEnergyDensity a).aestronglyMeasurable ?_
    filter_upwards with x
    have hx : 0 ≤ linearShearKineticEnergyDensity a x := by
      dsimp [linearShearKineticEnergyDensity]
      nlinarith [sq_nonneg (a * x nsCoord1)]
    rw [Real.norm_of_nonneg hx]
    exact le_add_of_nonneg_right (by positivity)
  exact not_integrable_linearShearKineticEnergyDensity ha hIntShear

/-- Therefore a steady affine shear field with nonzero shear coefficient never
satisfies the concrete global bounded-energy predicate on `ℝ^3`. -/
theorem not_boundedKineticEnergy_linearShearHorizontalDriftVelocityField
    {a b : ℝ} (ha : a ≠ 0) :
    ¬ boundedKineticEnergy (linearShearHorizontalDriftVelocityField a b) := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_linearShearHorizontalDriftVelocityField
      (a := a) (b := b) ha 0 (hbound 0).1

/-- On every nonnegative slab, a steady affine shear field with nonzero shear
coefficient also fails the finite-time bounded-energy predicate. -/
theorem not_boundedKineticEnergyUpTo_linearShearHorizontalDriftVelocityField
    {a b T : ℝ}
    (ha : a ≠ 0)
    (hT : 0 ≤ T) :
    ¬ boundedKineticEnergyUpTo (linearShearHorizontalDriftVelocityField a b) T := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_linearShearHorizontalDriftVelocityField
      (a := a) (b := b) ha 0 ((hbound 0 le_rfl hT).1)

/-- Kinetic-energy density of the steady affine shear field `u(t,x) = (a * x₁,
b, c)` is the linear-shear density plus the constant drift contribution
`b² + c²` on every time slice. -/
theorem kineticEnergyDensity_linearShearFullDriftVelocityField
    (a b c : ℝ) (t : NSTime) :
    kineticEnergyDensity (linearShearFullDriftVelocityField a b c) t =
      fun x => linearShearKineticEnergyDensity a x + b ^ (2 : ℕ) + c ^ (2 : ℕ) := by
  funext x
  have hs : (|a| * |x.ofLp 1|) ^ (2 : ℕ) = linearShearKineticEnergyDensity a x := by
    rw [linearShearKineticEnergyDensity]
    calc
      (|a| * |x.ofLp 1|) ^ (2 : ℕ) = |a * x.ofLp 1| ^ (2 : ℕ) := by rw [abs_mul]
      _ = a * x.ofLp 1 * (a * x.ofLp 1) := by
        simpa [pow_two] using (sq_abs (a * x.ofLp 1))
  rw [kineticEnergyDensity, linearShearFullDriftVelocityField_apply]
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
  simp [nsCoord0, nsCoord1, nsCoord2, hs]

/-- A steady affine shear field with full constant drift and nonzero shear
coefficient is not spatially integrable on `ℝ^3` with respect to the
kinetic-energy density on any time slice. -/
theorem not_integrable_kineticEnergyDensity_linearShearFullDriftVelocityField
    {a b c : ℝ} (ha : a ≠ 0) (t : NSTime) :
    ¬ MeasureTheory.Integrable
      (kineticEnergyDensity (linearShearFullDriftVelocityField a b c) t) := by
  intro hInt
  have hIntDrift :
      MeasureTheory.Integrable
        (fun x => linearShearKineticEnergyDensity a x + b ^ (2 : ℕ) + c ^ (2 : ℕ)) := by
    simpa [kineticEnergyDensity_linearShearFullDriftVelocityField a b c t] using hInt
  have hIntShear : MeasureTheory.Integrable (linearShearKineticEnergyDensity a) := by
    refine MeasureTheory.Integrable.mono' hIntDrift
      (continuous_linearShearKineticEnergyDensity a).aestronglyMeasurable ?_
    filter_upwards with x
    have hx : 0 ≤ linearShearKineticEnergyDensity a x := by
      dsimp [linearShearKineticEnergyDensity]
      nlinarith [sq_nonneg (a * x nsCoord1)]
    rw [Real.norm_of_nonneg hx]
    have hbc : 0 ≤ b ^ (2 : ℕ) + c ^ (2 : ℕ) := by positivity
    nlinarith
  exact not_integrable_linearShearKineticEnergyDensity ha hIntShear

/-- Therefore a steady affine shear field with full constant drift and nonzero
shear coefficient never satisfies the concrete global bounded-energy predicate
on `ℝ^3`. -/
theorem not_boundedKineticEnergy_linearShearFullDriftVelocityField
    {a b c : ℝ} (ha : a ≠ 0) :
    ¬ boundedKineticEnergy (linearShearFullDriftVelocityField a b c) := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_linearShearFullDriftVelocityField
      (a := a) (b := b) (c := c) ha 0 (hbound 0).1

/-- On every nonnegative slab, a steady affine shear field with full constant
drift and nonzero shear coefficient also fails the finite-time bounded-energy
predicate. -/
theorem not_boundedKineticEnergyUpTo_linearShearFullDriftVelocityField
    {a b c T : ℝ}
    (ha : a ≠ 0)
    (hT : 0 ≤ T) :
    ¬ boundedKineticEnergyUpTo (linearShearFullDriftVelocityField a b c) T := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_linearShearFullDriftVelocityField
      (a := a) (b := b) (c := c) ha 0 ((hbound 0 le_rfl hT).1)

/-- If a velocity field matches linear shear initial data at time `0`, then its
initial kinetic-energy density is exactly the linear shear density. -/
theorem kineticEnergyDensity_zero_eq_of_matchesInitialVelocity_linearShearInitialVelocity
    {u : NSVelocityField} {a : ℝ}
    (hinit : MatchesInitialVelocity (linearShearInitialVelocity a) u) :
    kineticEnergyDensity u 0 = linearShearKineticEnergyDensity a := by
  funext x
  rw [kineticEnergyDensity, hinit x, linearShearInitialVelocity_apply]
  simpa [linearShearKineticEnergyDensity, pow_two] using
    (sq_abs (a * x nsCoord1))

/-- The initial kinetic-energy density of linear shear is exactly the same
quadratic profile used in the time-zero obstruction lemmas above. -/
theorem initialKineticEnergyDensity_linearShearInitialVelocity
    (a : ℝ) :
    initialKineticEnergyDensity (linearShearInitialVelocity a) =
      linearShearKineticEnergyDensity a := by
  funext x
  rw [initialKineticEnergyDensity, linearShearInitialVelocity_apply]
  simpa [linearShearKineticEnergyDensity, pow_two] using
    (sq_abs (a * x nsCoord1))

/-- Therefore any velocity field matching nonzero linear shear initial data
already fails the integrability requirement at time `0`. -/
theorem not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_linearShearInitialVelocity
    {u : NSVelocityField} {a : ℝ}
    (ha : a ≠ 0)
    (hinit : MatchesInitialVelocity (linearShearInitialVelocity a) u) :
    ¬ MeasureTheory.Integrable (kineticEnergyDensity u 0) := by
  intro hInt
  have hIntShear : MeasureTheory.Integrable (linearShearKineticEnergyDensity a) := by
    simpa [kineticEnergyDensity_zero_eq_of_matchesInitialVelocity_linearShearInitialVelocity hinit]
      using hInt
  exact not_integrable_linearShearKineticEnergyDensity ha hIntShear

/-- If a velocity field matches the initial data `x ↦ (a * x₁, 0, b)` at time
`0`, then its time-zero kinetic-energy density is the linear-shear density plus
the constant drift contribution `b²`. -/
theorem kineticEnergyDensity_zero_eq_of_matchesInitialVelocity_linearShearVerticalDriftInitialVelocity
    {u : NSVelocityField} {a b : ℝ}
    (hinit : MatchesInitialVelocity (linearShearVerticalDriftInitialVelocity a b) u) :
    kineticEnergyDensity u 0 = fun x => linearShearKineticEnergyDensity a x + b ^ (2 : ℕ) := by
  funext x
  have hs : (|a| * |x.ofLp 1|) ^ (2 : ℕ) = linearShearKineticEnergyDensity a x := by
    rw [linearShearKineticEnergyDensity]
    calc
      (|a| * |x.ofLp 1|) ^ (2 : ℕ) = |a * x.ofLp 1| ^ (2 : ℕ) := by rw [abs_mul]
      _ = a * x.ofLp 1 * (a * x.ofLp 1) := by
        simpa [pow_two] using (sq_abs (a * x.ofLp 1))
  have hb : ‖b‖ ^ (2 : ℕ) = b ^ (2 : ℕ) := by
    simp [pow_two]
  rw [kineticEnergyDensity, hinit x, linearShearVerticalDriftInitialVelocity_apply]
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
  simp [nsCoord0, nsCoord1, nsCoord2, hs]

/-- Therefore any velocity field matching nonzero initial data
`x ↦ (a * x₁, 0, b)` already fails the integrability requirement at time `0`.
-/
theorem not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_linearShearVerticalDriftInitialVelocity
    {u : NSVelocityField} {a b : ℝ}
    (ha : a ≠ 0)
    (hinit : MatchesInitialVelocity (linearShearVerticalDriftInitialVelocity a b) u) :
    ¬ MeasureTheory.Integrable (kineticEnergyDensity u 0) := by
  intro hInt
  have hIntDrift :
      MeasureTheory.Integrable (fun x => linearShearKineticEnergyDensity a x + b ^ (2 : ℕ)) := by
    simpa [kineticEnergyDensity_zero_eq_of_matchesInitialVelocity_linearShearVerticalDriftInitialVelocity
      hinit] using hInt
  have hIntShear : MeasureTheory.Integrable (linearShearKineticEnergyDensity a) := by
    refine MeasureTheory.Integrable.mono' hIntDrift
      (continuous_linearShearKineticEnergyDensity a).aestronglyMeasurable ?_
    filter_upwards with x
    have hx : 0 ≤ linearShearKineticEnergyDensity a x := by
      dsimp [linearShearKineticEnergyDensity]
      nlinarith [sq_nonneg (a * x nsCoord1)]
    rw [Real.norm_of_nonneg hx]
    exact le_add_of_nonneg_right (by positivity)
  exact not_integrable_linearShearKineticEnergyDensity ha hIntShear

/-- If a velocity field matches the initial data `x ↦ (a * x₁, b, 0)` at time
`0`, then its time-zero kinetic-energy density is the linear-shear density plus
the constant drift contribution `b²`. -/
theorem kineticEnergyDensity_zero_eq_of_matchesInitialVelocity_linearShearHorizontalDriftInitialVelocity
    {u : NSVelocityField} {a b : ℝ}
    (hinit : MatchesInitialVelocity (linearShearHorizontalDriftInitialVelocity a b) u) :
    kineticEnergyDensity u 0 = fun x => linearShearKineticEnergyDensity a x + b ^ (2 : ℕ) := by
  funext x
  have hs : (|a| * |x.ofLp 1|) ^ (2 : ℕ) = linearShearKineticEnergyDensity a x := by
    rw [linearShearKineticEnergyDensity]
    calc
      (|a| * |x.ofLp 1|) ^ (2 : ℕ) = |a * x.ofLp 1| ^ (2 : ℕ) := by rw [abs_mul]
      _ = a * x.ofLp 1 * (a * x.ofLp 1) := by
        simpa [pow_two] using (sq_abs (a * x.ofLp 1))
  rw [kineticEnergyDensity, hinit x, linearShearHorizontalDriftInitialVelocity_apply]
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
  simp [nsCoord0, nsCoord1, hs]

/-- Therefore any velocity field matching nonzero initial data
`x ↦ (a * x₁, b, 0)` already fails the integrability requirement at time `0`.
-/
theorem not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_linearShearHorizontalDriftInitialVelocity
    {u : NSVelocityField} {a b : ℝ}
    (ha : a ≠ 0)
    (hinit : MatchesInitialVelocity (linearShearHorizontalDriftInitialVelocity a b) u) :
    ¬ MeasureTheory.Integrable (kineticEnergyDensity u 0) := by
  intro hInt
  have hIntDrift :
      MeasureTheory.Integrable (fun x => linearShearKineticEnergyDensity a x + b ^ (2 : ℕ)) := by
    simpa [kineticEnergyDensity_zero_eq_of_matchesInitialVelocity_linearShearHorizontalDriftInitialVelocity
      hinit] using hInt
  have hIntShear : MeasureTheory.Integrable (linearShearKineticEnergyDensity a) := by
    refine MeasureTheory.Integrable.mono' hIntDrift
      (continuous_linearShearKineticEnergyDensity a).aestronglyMeasurable ?_
    filter_upwards with x
    have hx : 0 ≤ linearShearKineticEnergyDensity a x := by
      dsimp [linearShearKineticEnergyDensity]
      nlinarith [sq_nonneg (a * x nsCoord1)]
    rw [Real.norm_of_nonneg hx]
    exact le_add_of_nonneg_right (by positivity)
  exact not_integrable_linearShearKineticEnergyDensity ha hIntShear

/-- If a velocity field matches the initial data `x ↦ (a * x₁, b, c)` at time
`0`, then its time-zero kinetic-energy density is the linear-shear density plus
the constant drift contribution `b² + c²`. -/
theorem kineticEnergyDensity_zero_eq_of_matchesInitialVelocity_linearShearFullDriftInitialVelocity
    {u : NSVelocityField} {a b c : ℝ}
    (hinit : MatchesInitialVelocity (linearShearFullDriftInitialVelocity a b c) u) :
    kineticEnergyDensity u 0 =
      fun x => linearShearKineticEnergyDensity a x + b ^ (2 : ℕ) + c ^ (2 : ℕ) := by
  funext x
  have hs : (|a| * |x.ofLp 1|) ^ (2 : ℕ) = linearShearKineticEnergyDensity a x := by
    rw [linearShearKineticEnergyDensity]
    calc
      (|a| * |x.ofLp 1|) ^ (2 : ℕ) = |a * x.ofLp 1| ^ (2 : ℕ) := by rw [abs_mul]
      _ = a * x.ofLp 1 * (a * x.ofLp 1) := by
        simpa [pow_two] using (sq_abs (a * x.ofLp 1))
  rw [kineticEnergyDensity, hinit x, linearShearFullDriftInitialVelocity_apply]
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
  simp [nsCoord0, nsCoord1, nsCoord2, hs]

/-- Therefore any velocity field matching nonzero initial data
`x ↦ (a * x₁, b, c)` already fails the integrability requirement at time `0`.
-/
theorem not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_linearShearFullDriftInitialVelocity
    {u : NSVelocityField} {a b c : ℝ}
    (ha : a ≠ 0)
    (hinit : MatchesInitialVelocity (linearShearFullDriftInitialVelocity a b c) u) :
    ¬ MeasureTheory.Integrable (kineticEnergyDensity u 0) := by
  intro hInt
  have hIntDrift :
      MeasureTheory.Integrable
        (fun x => linearShearKineticEnergyDensity a x + b ^ (2 : ℕ) + c ^ (2 : ℕ)) := by
    simpa [kineticEnergyDensity_zero_eq_of_matchesInitialVelocity_linearShearFullDriftInitialVelocity
      hinit] using hInt
  have hIntShear : MeasureTheory.Integrable (linearShearKineticEnergyDensity a) := by
    refine MeasureTheory.Integrable.mono' hIntDrift
      (continuous_linearShearKineticEnergyDensity a).aestronglyMeasurable ?_
    filter_upwards with x
    have hx : 0 ≤ linearShearKineticEnergyDensity a x := by
      dsimp [linearShearKineticEnergyDensity]
      nlinarith [sq_nonneg (a * x nsCoord1)]
    rw [Real.norm_of_nonneg hx]
    have hbc : 0 ≤ b ^ (2 : ℕ) + c ^ (2 : ℕ) := by positivity
    nlinarith
  exact not_integrable_linearShearKineticEnergyDensity ha hIntShear

/-- Nonzero linear shear initial data are therefore not finite-energy
admissible on `ℝ^3`. -/
theorem not_finiteInitialKineticEnergy_linearShearInitialVelocity
    {a : ℝ}
    (ha : a ≠ 0) :
    ¬ finiteInitialKineticEnergy (linearShearInitialVelocity a) := by
  intro hE
  have hIntShear : MeasureTheory.Integrable (linearShearKineticEnergyDensity a) := by
    simpa [finiteInitialKineticEnergy,
      initialKineticEnergyDensity_linearShearInitialVelocity a] using hE
  exact not_integrable_linearShearKineticEnergyDensity ha hIntShear

/-- The initial kinetic-energy density of the affine shear datum
`x ↦ (a * x₁, 0, b)` is the linear-shear density plus the constant drift term
`b²`. -/
theorem initialKineticEnergyDensity_linearShearVerticalDriftInitialVelocity
    (a b : ℝ) :
    initialKineticEnergyDensity (linearShearVerticalDriftInitialVelocity a b) =
      fun x => linearShearKineticEnergyDensity a x + b ^ (2 : ℕ) := by
  funext x
  have hs : (|a| * |x.ofLp 1|) ^ (2 : ℕ) = linearShearKineticEnergyDensity a x := by
    rw [linearShearKineticEnergyDensity]
    calc
      (|a| * |x.ofLp 1|) ^ (2 : ℕ) = |a * x.ofLp 1| ^ (2 : ℕ) := by rw [abs_mul]
      _ = a * x.ofLp 1 * (a * x.ofLp 1) := by
        simpa [pow_two] using (sq_abs (a * x.ofLp 1))
  have hb : ‖b‖ ^ (2 : ℕ) = b ^ (2 : ℕ) := by
    simp [pow_two]
  rw [initialKineticEnergyDensity, linearShearVerticalDriftInitialVelocity_apply]
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
  simp [nsCoord0, nsCoord1, nsCoord2, hs]

/-- Nonzero affine shear initial data `x ↦ (a * x₁, 0, b)` are likewise not
finite-energy admissible on `ℝ^3`. -/
theorem not_finiteInitialKineticEnergy_linearShearVerticalDriftInitialVelocity
    {a b : ℝ}
    (ha : a ≠ 0) :
    ¬ finiteInitialKineticEnergy (linearShearVerticalDriftInitialVelocity a b) := by
  intro hE
  have hIntDrift :
      MeasureTheory.Integrable (fun x => linearShearKineticEnergyDensity a x + b ^ (2 : ℕ)) := by
    simpa [finiteInitialKineticEnergy,
      initialKineticEnergyDensity_linearShearVerticalDriftInitialVelocity a b] using hE
  have hIntShear : MeasureTheory.Integrable (linearShearKineticEnergyDensity a) := by
    refine MeasureTheory.Integrable.mono' hIntDrift
      (continuous_linearShearKineticEnergyDensity a).aestronglyMeasurable ?_
    filter_upwards with x
    have hx : 0 ≤ linearShearKineticEnergyDensity a x := by
      dsimp [linearShearKineticEnergyDensity]
      nlinarith [sq_nonneg (a * x nsCoord1)]
    rw [Real.norm_of_nonneg hx]
    exact le_add_of_nonneg_right (by positivity)
  exact not_integrable_linearShearKineticEnergyDensity ha hIntShear

/-- The initial kinetic-energy density of the affine shear datum
`x ↦ (a * x₁, b, 0)` is the linear-shear density plus the constant drift term
`b²`. -/
theorem initialKineticEnergyDensity_linearShearHorizontalDriftInitialVelocity
    (a b : ℝ) :
    initialKineticEnergyDensity (linearShearHorizontalDriftInitialVelocity a b) =
      fun x => linearShearKineticEnergyDensity a x + b ^ (2 : ℕ) := by
  funext x
  have hs : (|a| * |x.ofLp 1|) ^ (2 : ℕ) = linearShearKineticEnergyDensity a x := by
    rw [linearShearKineticEnergyDensity]
    calc
      (|a| * |x.ofLp 1|) ^ (2 : ℕ) = |a * x.ofLp 1| ^ (2 : ℕ) := by rw [abs_mul]
      _ = a * x.ofLp 1 * (a * x.ofLp 1) := by
        simpa [pow_two] using (sq_abs (a * x.ofLp 1))
  rw [initialKineticEnergyDensity, linearShearHorizontalDriftInitialVelocity_apply]
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
  simp [nsCoord0, nsCoord1, hs]

/-- Nonzero affine shear initial data `x ↦ (a * x₁, b, 0)` are likewise not
finite-energy admissible on `ℝ^3`. -/
theorem not_finiteInitialKineticEnergy_linearShearHorizontalDriftInitialVelocity
    {a b : ℝ}
    (ha : a ≠ 0) :
    ¬ finiteInitialKineticEnergy (linearShearHorizontalDriftInitialVelocity a b) := by
  intro hE
  have hIntDrift :
      MeasureTheory.Integrable (fun x => linearShearKineticEnergyDensity a x + b ^ (2 : ℕ)) := by
    simpa [finiteInitialKineticEnergy,
      initialKineticEnergyDensity_linearShearHorizontalDriftInitialVelocity a b] using hE
  have hIntShear : MeasureTheory.Integrable (linearShearKineticEnergyDensity a) := by
    refine MeasureTheory.Integrable.mono' hIntDrift
      (continuous_linearShearKineticEnergyDensity a).aestronglyMeasurable ?_
    filter_upwards with x
    have hx : 0 ≤ linearShearKineticEnergyDensity a x := by
      dsimp [linearShearKineticEnergyDensity]
      nlinarith [sq_nonneg (a * x nsCoord1)]
    rw [Real.norm_of_nonneg hx]
    exact le_add_of_nonneg_right (by positivity)
  exact not_integrable_linearShearKineticEnergyDensity ha hIntShear

/-- The initial kinetic-energy density of the affine shear datum
`x ↦ (a * x₁, b, c)` is the linear-shear density plus the constant drift term
`b² + c²`. -/
theorem initialKineticEnergyDensity_linearShearFullDriftInitialVelocity
    (a b c : ℝ) :
    initialKineticEnergyDensity (linearShearFullDriftInitialVelocity a b c) =
      fun x => linearShearKineticEnergyDensity a x + b ^ (2 : ℕ) + c ^ (2 : ℕ) := by
  funext x
  have hs : (|a| * |x.ofLp 1|) ^ (2 : ℕ) = linearShearKineticEnergyDensity a x := by
    rw [linearShearKineticEnergyDensity]
    calc
      (|a| * |x.ofLp 1|) ^ (2 : ℕ) = |a * x.ofLp 1| ^ (2 : ℕ) := by rw [abs_mul]
      _ = a * x.ofLp 1 * (a * x.ofLp 1) := by
        simpa [pow_two] using (sq_abs (a * x.ofLp 1))
  rw [initialKineticEnergyDensity, linearShearFullDriftInitialVelocity_apply]
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
  simp [nsCoord0, nsCoord1, nsCoord2, hs]

/-- Nonzero affine shear initial data `x ↦ (a * x₁, b, c)` are likewise not
finite-energy admissible on `ℝ^3`. -/
theorem not_finiteInitialKineticEnergy_linearShearFullDriftInitialVelocity
    {a b c : ℝ}
    (ha : a ≠ 0) :
    ¬ finiteInitialKineticEnergy (linearShearFullDriftInitialVelocity a b c) := by
  intro hE
  have hIntDrift :
      MeasureTheory.Integrable
        (fun x => linearShearKineticEnergyDensity a x + b ^ (2 : ℕ) + c ^ (2 : ℕ)) := by
    simpa [finiteInitialKineticEnergy,
      initialKineticEnergyDensity_linearShearFullDriftInitialVelocity a b c] using hE
  have hIntShear : MeasureTheory.Integrable (linearShearKineticEnergyDensity a) := by
    refine MeasureTheory.Integrable.mono' hIntDrift
      (continuous_linearShearKineticEnergyDensity a).aestronglyMeasurable ?_
    filter_upwards with x
    have hx : 0 ≤ linearShearKineticEnergyDensity a x := by
      dsimp [linearShearKineticEnergyDensity]
      nlinarith [sq_nonneg (a * x nsCoord1)]
    rw [Real.norm_of_nonneg hx]
    have hbc : 0 ≤ b ^ (2 : ℕ) + c ^ (2 : ℕ) := by positivity
    nlinarith
  exact not_integrable_linearShearKineticEnergyDensity ha hIntShear

end UniformVorticityContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
