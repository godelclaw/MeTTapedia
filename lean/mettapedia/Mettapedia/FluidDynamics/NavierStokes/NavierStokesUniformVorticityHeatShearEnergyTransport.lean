import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityHeatShearFullDriftEnergy

/-!
# Transported Heat-Shear Energy Obstructions for Uniform-Vorticity Continuation

This module contains transported and transported-full-drift kinetic-energy
identities and finite-energy obstructions for heat-shear data.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section UniformVorticityContinuation

/-- The initial kinetic-energy density of the transported heat-shear datum is
the heat-shear density plus the constant transport-speed contribution `b²`. -/
theorem initialKineticEnergyDensity_heatShearTransportInitialVelocity
    (a k b : ℝ) :
    initialKineticEnergyDensity (heatShearTransportInitialVelocity a k b) =
      fun x => heatShearKineticEnergyDensity a k x + b ^ (2 : ℕ) := by
  funext x
  have hs :
      |a| * |Real.sin (k * x.ofLp 1)| * (|a| * |Real.sin (k * x.ofLp 1)|) =
        a * Real.sin (k * x.ofLp 1) * (a * Real.sin (k * x.ofLp 1)) := by
    simpa [pow_two, abs_mul, mul_assoc, mul_left_comm, mul_comm] using
      (sq_abs (a * Real.sin (k * x.ofLp 1)))
  rw [initialKineticEnergyDensity, heatShearTransportInitialVelocity_apply]
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
  simp [nsCoord0, nsCoord1, heatShearKineticEnergyDensity, pow_two]
  simpa using congrArg (fun r : ℝ => r + b ^ (2 : ℕ)) hs

/-- On each time slice, the transported heat-shear field carries the transported
oscillatory energy density plus the constant transport-speed contribution
`b²`. -/
theorem kineticEnergyDensity_heatShearTransportVelocityField
    (ν a k b : ℝ) (t : NSTime) :
    kineticEnergyDensity (heatShearTransportVelocityField ν a k b) t =
      fun x =>
        (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
            Real.sin (k * (x nsCoord1 - b * t))) *
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
            Real.sin (k * (x nsCoord1 - b * t))) +
        b ^ (2 : ℕ) := by
  funext x
  have hexp :
      0 ≤ Real.exp (-(ν * k ^ (2 : ℕ)) * t) := by
    exact le_of_lt (Real.exp_pos _)
  have hs :
      |a| *
          (Real.exp (-(ν * (k * (k * t)))) *
            (|Real.sin (k * (x.ofLp 1 - b * t))| *
              (|a| *
                (Real.exp (-(ν * (k * (k * t)))) *
                  |Real.sin (k * (x.ofLp 1 - b * t))|)))) =
        a *
          (Real.exp (-(ν * (k * (k * t)))) *
            (Real.sin (k * (x.ofLp 1 - b * t)) *
              (a *
                (Real.exp (-(ν * (k * (k * t)))) *
                  Real.sin (k * (x.ofLp 1 - b * t)))))) := by
    simpa [pow_two, abs_mul, abs_of_nonneg hexp, mul_assoc, mul_left_comm, mul_comm] using
      (sq_abs (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
        Real.sin (k * (x.ofLp 1 - b * t))))
  rw [kineticEnergyDensity, heatShearTransportVelocityField_apply]
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
  simp [nsCoord0, nsCoord1, pow_two, mul_assoc]
  simpa using congrArg (fun r : ℝ => r + b ^ (2 : ℕ)) hs

/-- A transported heat-shear field with nonzero transport speed has
nonintegrable kinetic-energy density on every time slice because it dominates
the nonzero constant field `(0, b, 0)`. -/
theorem not_integrable_kineticEnergyDensity_heatShearTransportVelocityField
    {ν a k b : ℝ} (hb : b ≠ 0) (t : NSTime) :
    ¬ MeasureTheory.Integrable
      (kineticEnergyDensity (heatShearTransportVelocityField ν a k b) t) := by
  intro hInt
  have hIntTransport :
      MeasureTheory.Integrable
        (fun x : NSSpace =>
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
              Real.sin (k * (x nsCoord1 - b * t))) *
            (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
              Real.sin (k * (x nsCoord1 - b * t))) +
          b ^ (2 : ℕ)) := by
    simpa [kineticEnergyDensity_heatShearTransportVelocityField ν a k b t] using hInt
  have hIntConst : MeasureTheory.Integrable (fun _ : NSSpace => b ^ (2 : ℕ)) := by
    refine MeasureTheory.Integrable.mono' hIntTransport
      (continuous_const.aestronglyMeasurable) ?_
    filter_upwards with x
    have hsq :
        0 ≤
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
              Real.sin (k * (x nsCoord1 - b * t))) *
            (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
              Real.sin (k * (x nsCoord1 - b * t))) := by
      nlinarith [sq_nonneg
        (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
          Real.sin (k * (x nsCoord1 - b * t)))]
    have hsum :
        0 ≤
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
              Real.sin (k * (x nsCoord1 - b * t))) *
            (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
              Real.sin (k * (x nsCoord1 - b * t))) +
          b ^ (2 : ℕ) := by
      nlinarith
    have hbound :
        ‖b ^ (2 : ℕ)‖ ≤
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
              Real.sin (k * (x nsCoord1 - b * t))) *
            (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
              Real.sin (k * (x nsCoord1 - b * t))) +
          b ^ (2 : ℕ) := by
      rw [Real.norm_of_nonneg (by positivity)]
      nlinarith
    exact hbound
  have hconstNe : EuclideanSpace.single nsCoord1 b ≠ (0 : NSSpace) := by
    simpa using hb
  have hIntConstField :
      MeasureTheory.Integrable
        (kineticEnergyDensity (constantVelocityField (EuclideanSpace.single nsCoord1 b)) 0) := by
    simpa [kineticEnergyDensity_constantVelocityField, PiLp.norm_sq_eq_of_L2,
      Fin.sum_univ_three, nsCoord0, nsCoord1, nsCoord2, pow_two] using hIntConst
  exact
    not_integrable_kineticEnergyDensity_constantVelocityField
      (c := EuclideanSpace.single nsCoord1 b) hconstNe 0 hIntConstField

/-- Therefore a transported heat-shear field with nonzero transport speed never
satisfies the global bounded-energy predicate on `ℝ^3`. -/
theorem not_boundedKineticEnergy_heatShearTransportVelocityField
    {ν a k b : ℝ} (hb : b ≠ 0) :
    ¬ boundedKineticEnergy (heatShearTransportVelocityField ν a k b) := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_heatShearTransportVelocityField
      (ν := ν) (a := a) (k := k) (b := b) hb 0 (hbound 0).1

/-- On every nonnegative slab, a transported heat-shear field with nonzero
transport speed also fails the finite-time bounded-energy predicate. -/
theorem not_boundedKineticEnergyUpTo_heatShearTransportVelocityField
    {ν a k b T : ℝ}
    (hb : b ≠ 0)
    (hT : 0 ≤ T) :
    ¬ boundedKineticEnergyUpTo (heatShearTransportVelocityField ν a k b) T := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_heatShearTransportVelocityField
      (ν := ν) (a := a) (k := k) (b := b) hb 0 ((hbound 0 le_rfl hT).1)

/-- Any field matching the transported heat-shear datum at time `0` has the
same time-zero kinetic-energy density as that explicit initial profile. -/
theorem kineticEnergyDensity_zero_eq_of_matchesInitialVelocity_heatShearTransportInitialVelocity
    {u : NSVelocityField} {a k b : ℝ}
    (hinit : MatchesInitialVelocity (heatShearTransportInitialVelocity a k b) u) :
    kineticEnergyDensity u 0 =
      fun x => heatShearKineticEnergyDensity a k x + b ^ (2 : ℕ) := by
  calc
    kineticEnergyDensity u 0 =
        initialKineticEnergyDensity (heatShearTransportInitialVelocity a k b) := by
          symm
          exact initialKineticEnergyDensity_eq_of_matchesInitialVelocity hinit
    _ = fun x => heatShearKineticEnergyDensity a k x + b ^ (2 : ℕ) :=
      initialKineticEnergyDensity_heatShearTransportInitialVelocity a k b

/-- Therefore any velocity field matching transported heat-shear initial data
with nonzero transport speed already fails the time-zero integrability
requirement. -/
theorem not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_heatShearTransportInitialVelocity
    {u : NSVelocityField} {a k b : ℝ}
    (hb : b ≠ 0)
    (hinit : MatchesInitialVelocity (heatShearTransportInitialVelocity a k b) u) :
    ¬ MeasureTheory.Integrable (kineticEnergyDensity u 0) := by
  intro hInt
  have hIntTransport :
      MeasureTheory.Integrable
        (fun x : NSSpace => heatShearKineticEnergyDensity a k x + b ^ (2 : ℕ)) := by
    simpa
      [kineticEnergyDensity_zero_eq_of_matchesInitialVelocity_heatShearTransportInitialVelocity
        hinit] using hInt
  have hIntConst : MeasureTheory.Integrable (fun _ : NSSpace => b ^ (2 : ℕ)) := by
    refine MeasureTheory.Integrable.mono' hIntTransport
      (continuous_const.aestronglyMeasurable) ?_
    filter_upwards with x
    have hheat : 0 ≤ heatShearKineticEnergyDensity a k x := by
      dsimp [heatShearKineticEnergyDensity]
      nlinarith [sq_nonneg (a * Real.sin (k * x nsCoord1))]
    have hsum : 0 ≤ heatShearKineticEnergyDensity a k x + b ^ (2 : ℕ) := by
      nlinarith
    have hbound : ‖b ^ (2 : ℕ)‖ ≤ heatShearKineticEnergyDensity a k x + b ^ (2 : ℕ) := by
      rw [Real.norm_of_nonneg (by positivity)]
      nlinarith
    exact hbound
  have hconstNe : EuclideanSpace.single nsCoord1 b ≠ (0 : NSSpace) := by
    simpa using hb
  have hIntConstField :
      MeasureTheory.Integrable
        (kineticEnergyDensity (constantVelocityField (EuclideanSpace.single nsCoord1 b)) 0) := by
    simpa [kineticEnergyDensity_constantVelocityField, PiLp.norm_sq_eq_of_L2,
      Fin.sum_univ_three, nsCoord0, nsCoord1, nsCoord2, pow_two] using hIntConst
  exact
    not_integrable_kineticEnergyDensity_constantVelocityField
      (c := EuclideanSpace.single nsCoord1 b) hconstNe 0 hIntConstField

/-- On every nonnegative slab, transported heat-shear initial data with nonzero
transport speed rule out the bounded-energy witness slot regardless of later
dynamics. -/
theorem not_boundedKineticEnergyUpTo_of_matchesInitialVelocity_heatShearTransportInitialVelocity
    {u : NSVelocityField} {a k b T : ℝ}
    (hb : b ≠ 0)
    (hT : 0 ≤ T)
    (hinit : MatchesInitialVelocity (heatShearTransportInitialVelocity a k b) u) :
    ¬ boundedKineticEnergyUpTo u T := by
  exact
    not_boundedKineticEnergyUpTo_of_not_integrable_kineticEnergyDensity_zero
      (u := u)
      (not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_heatShearTransportInitialVelocity
        (u := u) hb hinit)
      hT

/-- The same obstruction rules out global bounded kinetic energy for any field
matching transported heat-shear initial data with nonzero transport speed. -/
theorem not_boundedKineticEnergy_of_matchesInitialVelocity_heatShearTransportInitialVelocity
    {u : NSVelocityField} {a k b : ℝ}
    (hb : b ≠ 0)
    (hinit : MatchesInitialVelocity (heatShearTransportInitialVelocity a k b) u) :
    ¬ boundedKineticEnergy u := by
  exact
    not_boundedKineticEnergy_of_not_integrable_kineticEnergyDensity_zero
      (u := u)
      (not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_heatShearTransportInitialVelocity
        (u := u) hb hinit)

/-- Transported heat-shear initial data with nonzero transport speed are not
finite-energy admissible on `ℝ^3`. -/
theorem not_finiteInitialKineticEnergy_heatShearTransportInitialVelocity
    {a k b : ℝ}
    (hb : b ≠ 0) :
    ¬ finiteInitialKineticEnergy (heatShearTransportInitialVelocity a k b) := by
  intro hE
  have hIntTransport :
      MeasureTheory.Integrable
        (fun x : NSSpace => heatShearKineticEnergyDensity a k x + b ^ (2 : ℕ)) := by
    simpa [finiteInitialKineticEnergy,
      initialKineticEnergyDensity_heatShearTransportInitialVelocity a k b] using hE
  have hIntConst : MeasureTheory.Integrable (fun _ : NSSpace => b ^ (2 : ℕ)) := by
    refine MeasureTheory.Integrable.mono' hIntTransport
      (continuous_const.aestronglyMeasurable) ?_
    filter_upwards with x
    have hheat : 0 ≤ heatShearKineticEnergyDensity a k x := by
      dsimp [heatShearKineticEnergyDensity]
      nlinarith [sq_nonneg (a * Real.sin (k * x nsCoord1))]
    have hsum : 0 ≤ heatShearKineticEnergyDensity a k x + b ^ (2 : ℕ) := by
      nlinarith
    have hbound : ‖b ^ (2 : ℕ)‖ ≤ heatShearKineticEnergyDensity a k x + b ^ (2 : ℕ) := by
      rw [Real.norm_of_nonneg (by positivity)]
      nlinarith
    exact hbound
  have hconstNe : EuclideanSpace.single nsCoord1 b ≠ (0 : NSSpace) := by
    simpa using hb
  have hIntConstField :
      MeasureTheory.Integrable
        (kineticEnergyDensity (constantVelocityField (EuclideanSpace.single nsCoord1 b)) 0) := by
    simpa [kineticEnergyDensity_constantVelocityField, PiLp.norm_sq_eq_of_L2,
      Fin.sum_univ_three, nsCoord0, nsCoord1, nsCoord2, pow_two] using hIntConst
  exact
    not_integrable_kineticEnergyDensity_constantVelocityField
      (c := EuclideanSpace.single nsCoord1 b) hconstNe 0 hIntConstField

/-- The repaired structured whole-space input domain contains no problem datum
whose initial velocity is a transported heat-shear profile with nonzero
transport speed. -/
theorem not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_heatShearTransportInitialVelocity
    {a k b : ℝ}
    (hb : b ≠ 0) :
    ¬ Nonempty { P : FiniteEnergyAdmissibleNavierStokesProblemData //
        P.initialVelocity = heatShearTransportInitialVelocity a k b } := by
  exact
    not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearTransportInitialVelocity a k b)
      (not_finiteInitialKineticEnergy_heatShearTransportInitialVelocity hb)

/-- The initial kinetic-energy density of the transported full-drift
heat-shear datum is the full-drift heat-shear density plus the constant
transport-speed contribution `b²`. -/
theorem initialKineticEnergyDensity_heatShearTransportFullDriftInitialVelocity
    (a k b d c : ℝ) :
    initialKineticEnergyDensity (heatShearTransportFullDriftInitialVelocity a k b d c) =
      fun x => heatShearStreamwiseDriftKineticEnergyDensity a k d x + b ^ (2 : ℕ) + c ^ (2 : ℕ) := by
  funext x
  rw [initialKineticEnergyDensity, heatShearTransportFullDriftInitialVelocity_apply]
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
  simp [nsCoord0, nsCoord1, nsCoord2, heatShearStreamwiseDriftKineticEnergyDensity, pow_two]

/-- On each time slice, the transported full-drift heat-shear field carries
the transported full-drift oscillatory density together with the constant
transport and vertical drift contributions `b² + c²`. -/
theorem kineticEnergyDensity_heatShearTransportFullDriftVelocityField
    (ν a k b d c : ℝ) (t : NSTime) :
    kineticEnergyDensity (heatShearTransportFullDriftVelocityField ν a k b d c) t =
      fun x =>
        (d + a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
            Real.sin (k * (x nsCoord1 - b * t))) *
          (d + a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
            Real.sin (k * (x nsCoord1 - b * t))) +
        b ^ (2 : ℕ) + c ^ (2 : ℕ) := by
  funext x
  rw [kineticEnergyDensity, heatShearTransportFullDriftVelocityField_apply]
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
  simp [nsCoord0, nsCoord1, nsCoord2, pow_two, mul_assoc]

/-- A transported full-drift heat-shear field with nonzero transport speed has
nonintegrable kinetic-energy density on every time slice because it still
dominates the nonzero constant field `(0, b, 0)`. -/
theorem not_integrable_kineticEnergyDensity_heatShearTransportFullDriftVelocityField
    {ν a k b d c : ℝ} (hb : b ≠ 0) (t : NSTime) :
    ¬ MeasureTheory.Integrable
      (kineticEnergyDensity (heatShearTransportFullDriftVelocityField ν a k b d c) t) := by
  intro hInt
  have hIntTransport :
      MeasureTheory.Integrable
        (fun x : NSSpace =>
          (d + a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
              Real.sin (k * (x nsCoord1 - b * t))) *
            (d + a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
              Real.sin (k * (x nsCoord1 - b * t))) +
          b ^ (2 : ℕ) + c ^ (2 : ℕ)) := by
    simpa [kineticEnergyDensity_heatShearTransportFullDriftVelocityField ν a k b d c t] using hInt
  have hIntConst : MeasureTheory.Integrable (fun _ : NSSpace => b ^ (2 : ℕ)) := by
    refine MeasureTheory.Integrable.mono' hIntTransport
      (continuous_const.aestronglyMeasurable) ?_
    filter_upwards with x
    have hsq :
        0 ≤
          (d + a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
              Real.sin (k * (x nsCoord1 - b * t))) *
            (d + a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
              Real.sin (k * (x nsCoord1 - b * t))) := by
      nlinarith [sq_nonneg
        (d + a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
          Real.sin (k * (x nsCoord1 - b * t)))]
    have hsum :
        0 ≤
          (d + a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
              Real.sin (k * (x nsCoord1 - b * t))) *
            (d + a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
              Real.sin (k * (x nsCoord1 - b * t))) +
          b ^ (2 : ℕ) + c ^ (2 : ℕ) := by
      nlinarith
    have hbound :
        ‖b ^ (2 : ℕ)‖ ≤
          (d + a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
              Real.sin (k * (x nsCoord1 - b * t))) *
            (d + a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
              Real.sin (k * (x nsCoord1 - b * t))) +
          b ^ (2 : ℕ) + c ^ (2 : ℕ) := by
      rw [Real.norm_of_nonneg (by positivity)]
      nlinarith
    exact hbound
  have hconstNe : EuclideanSpace.single nsCoord1 b ≠ (0 : NSSpace) := by
    simpa using hb
  have hIntConstField :
      MeasureTheory.Integrable
        (kineticEnergyDensity (constantVelocityField (EuclideanSpace.single nsCoord1 b)) 0) := by
    simpa [kineticEnergyDensity_constantVelocityField, PiLp.norm_sq_eq_of_L2,
      Fin.sum_univ_three, nsCoord0, nsCoord1, nsCoord2, pow_two] using hIntConst
  exact
    not_integrable_kineticEnergyDensity_constantVelocityField
      (c := EuclideanSpace.single nsCoord1 b) hconstNe 0 hIntConstField

/-- Therefore a transported full-drift heat-shear field with nonzero transport
speed never satisfies the global bounded-energy predicate on `ℝ^3`. -/
theorem not_boundedKineticEnergy_heatShearTransportFullDriftVelocityField
    {ν a k b d c : ℝ} (hb : b ≠ 0) :
    ¬ boundedKineticEnergy (heatShearTransportFullDriftVelocityField ν a k b d c) := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_heatShearTransportFullDriftVelocityField
      (ν := ν) (a := a) (k := k) (b := b) (d := d) (c := c) hb 0 (hbound 0).1

/-- On every nonnegative slab, a transported full-drift heat-shear field with
nonzero transport speed also fails the finite-time bounded-energy predicate. -/
theorem not_boundedKineticEnergyUpTo_heatShearTransportFullDriftVelocityField
    {ν a k b d c T : ℝ}
    (hb : b ≠ 0)
    (hT : 0 ≤ T) :
    ¬ boundedKineticEnergyUpTo (heatShearTransportFullDriftVelocityField ν a k b d c) T := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_heatShearTransportFullDriftVelocityField
      (ν := ν) (a := a) (k := k) (b := b) (d := d) (c := c) hb 0 ((hbound 0 le_rfl hT).1)

/-- Any field matching the transported full-drift heat-shear datum at time `0`
has the same time-zero kinetic-energy density as that explicit initial profile.
-/
theorem kineticEnergyDensity_zero_eq_of_matchesInitialVelocity_heatShearTransportFullDriftInitialVelocity
    {u : NSVelocityField} {a k b d c : ℝ}
    (hinit : MatchesInitialVelocity (heatShearTransportFullDriftInitialVelocity a k b d c) u) :
    kineticEnergyDensity u 0 =
      fun x => heatShearStreamwiseDriftKineticEnergyDensity a k d x + b ^ (2 : ℕ) + c ^ (2 : ℕ) := by
  calc
    kineticEnergyDensity u 0 =
        initialKineticEnergyDensity (heatShearTransportFullDriftInitialVelocity a k b d c) := by
          symm
          exact initialKineticEnergyDensity_eq_of_matchesInitialVelocity hinit
    _ = fun x => heatShearStreamwiseDriftKineticEnergyDensity a k d x + b ^ (2 : ℕ) + c ^ (2 : ℕ) :=
      initialKineticEnergyDensity_heatShearTransportFullDriftInitialVelocity a k b d c

/-- Therefore any velocity field matching transported full-drift heat-shear
initial data with nonzero transport speed already fails the time-zero
integrability requirement. -/
theorem not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_heatShearTransportFullDriftInitialVelocity
    {u : NSVelocityField} {a k b d c : ℝ}
    (hb : b ≠ 0)
    (hinit : MatchesInitialVelocity (heatShearTransportFullDriftInitialVelocity a k b d c) u) :
    ¬ MeasureTheory.Integrable (kineticEnergyDensity u 0) := by
  intro hInt
  have hIntTransport :
      MeasureTheory.Integrable
        (fun x : NSSpace => heatShearStreamwiseDriftKineticEnergyDensity a k d x +
          b ^ (2 : ℕ) + c ^ (2 : ℕ)) := by
    simpa
      [kineticEnergyDensity_zero_eq_of_matchesInitialVelocity_heatShearTransportFullDriftInitialVelocity
        hinit] using hInt
  have hIntConst : MeasureTheory.Integrable (fun _ : NSSpace => b ^ (2 : ℕ)) := by
    refine MeasureTheory.Integrable.mono' hIntTransport
      (continuous_const.aestronglyMeasurable) ?_
    filter_upwards with x
    have hheat : 0 ≤ heatShearStreamwiseDriftKineticEnergyDensity a k d x := by
      dsimp [heatShearStreamwiseDriftKineticEnergyDensity]
      nlinarith [sq_nonneg (d + a * Real.sin (k * x nsCoord1))]
    have hsum :
        0 ≤ heatShearStreamwiseDriftKineticEnergyDensity a k d x + b ^ (2 : ℕ) + c ^ (2 : ℕ) := by
      nlinarith
    have hbound :
        ‖b ^ (2 : ℕ)‖ ≤ heatShearStreamwiseDriftKineticEnergyDensity a k d x + b ^ (2 : ℕ) +
          c ^ (2 : ℕ) := by
      rw [Real.norm_of_nonneg (by positivity)]
      nlinarith
    exact hbound
  have hconstNe : EuclideanSpace.single nsCoord1 b ≠ (0 : NSSpace) := by
    simpa using hb
  have hIntConstField :
      MeasureTheory.Integrable
        (kineticEnergyDensity (constantVelocityField (EuclideanSpace.single nsCoord1 b)) 0) := by
    simpa [kineticEnergyDensity_constantVelocityField, PiLp.norm_sq_eq_of_L2,
      Fin.sum_univ_three, nsCoord0, nsCoord1, nsCoord2, pow_two] using hIntConst
  exact
    not_integrable_kineticEnergyDensity_constantVelocityField
      (c := EuclideanSpace.single nsCoord1 b) hconstNe 0 hIntConstField

/-- On every nonnegative slab, transported full-drift heat-shear initial data
with nonzero transport speed rule out the bounded-energy witness slot
regardless of later dynamics. -/
theorem not_boundedKineticEnergyUpTo_of_matchesInitialVelocity_heatShearTransportFullDriftInitialVelocity
    {u : NSVelocityField} {a k b d c T : ℝ}
    (hb : b ≠ 0)
    (hT : 0 ≤ T)
    (hinit : MatchesInitialVelocity (heatShearTransportFullDriftInitialVelocity a k b d c) u) :
    ¬ boundedKineticEnergyUpTo u T := by
  exact
    not_boundedKineticEnergyUpTo_of_not_integrable_kineticEnergyDensity_zero
      (u := u)
      (not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_heatShearTransportFullDriftInitialVelocity
        (u := u) hb hinit)
      hT

/-- The same obstruction rules out global bounded kinetic energy for any field
matching transported full-drift heat-shear initial data with nonzero
transport speed. -/
theorem not_boundedKineticEnergy_of_matchesInitialVelocity_heatShearTransportFullDriftInitialVelocity
    {u : NSVelocityField} {a k b d c : ℝ}
    (hb : b ≠ 0)
    (hinit : MatchesInitialVelocity (heatShearTransportFullDriftInitialVelocity a k b d c) u) :
    ¬ boundedKineticEnergy u := by
  exact
    not_boundedKineticEnergy_of_not_integrable_kineticEnergyDensity_zero
      (u := u)
      (not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_heatShearTransportFullDriftInitialVelocity
        (u := u) hb hinit)

/-- Transported full-drift heat-shear initial data with nonzero transport
speed are not finite-energy admissible on `ℝ^3`. -/
theorem not_finiteInitialKineticEnergy_heatShearTransportFullDriftInitialVelocity
    {a k b d c : ℝ}
    (hb : b ≠ 0) :
    ¬ finiteInitialKineticEnergy (heatShearTransportFullDriftInitialVelocity a k b d c) := by
  intro hE
  have hIntTransport :
      MeasureTheory.Integrable
        (fun x : NSSpace => heatShearStreamwiseDriftKineticEnergyDensity a k d x +
          b ^ (2 : ℕ) + c ^ (2 : ℕ)) := by
    simpa [finiteInitialKineticEnergy,
      initialKineticEnergyDensity_heatShearTransportFullDriftInitialVelocity a k b d c] using hE
  have hIntConst : MeasureTheory.Integrable (fun _ : NSSpace => b ^ (2 : ℕ)) := by
    refine MeasureTheory.Integrable.mono' hIntTransport
      (continuous_const.aestronglyMeasurable) ?_
    filter_upwards with x
    have hheat : 0 ≤ heatShearStreamwiseDriftKineticEnergyDensity a k d x := by
      dsimp [heatShearStreamwiseDriftKineticEnergyDensity]
      nlinarith [sq_nonneg (d + a * Real.sin (k * x nsCoord1))]
    have hsum :
        0 ≤ heatShearStreamwiseDriftKineticEnergyDensity a k d x + b ^ (2 : ℕ) + c ^ (2 : ℕ) := by
      nlinarith
    have hbound :
        ‖b ^ (2 : ℕ)‖ ≤ heatShearStreamwiseDriftKineticEnergyDensity a k d x + b ^ (2 : ℕ) +
          c ^ (2 : ℕ) := by
      rw [Real.norm_of_nonneg (by positivity)]
      nlinarith
    exact hbound
  have hconstNe : EuclideanSpace.single nsCoord1 b ≠ (0 : NSSpace) := by
    simpa using hb
  have hIntConstField :
      MeasureTheory.Integrable
        (kineticEnergyDensity (constantVelocityField (EuclideanSpace.single nsCoord1 b)) 0) := by
    simpa [kineticEnergyDensity_constantVelocityField, PiLp.norm_sq_eq_of_L2,
      Fin.sum_univ_three, nsCoord0, nsCoord1, nsCoord2, pow_two] using hIntConst
  exact
    not_integrable_kineticEnergyDensity_constantVelocityField
      (c := EuclideanSpace.single nsCoord1 b) hconstNe 0 hIntConstField

/-- Transported full-drift heat-shear initial data have finite whole-space
kinetic energy exactly in the zero-data case. -/
theorem finiteInitialKineticEnergy_heatShearTransportFullDriftInitialVelocity_iff
    {a k b d c : ℝ} :
    finiteInitialKineticEnergy (heatShearTransportFullDriftInitialVelocity a k b d c) ↔
      b = 0 ∧ d = 0 ∧ c = 0 ∧ a * k = 0 := by
  constructor
  · intro hE
    have hb : b = 0 := by
      by_contra hb
      exact
        (not_finiteInitialKineticEnergy_heatShearTransportFullDriftInitialVelocity
          (a := a) (k := k) (b := b) (d := d) (c := c) hb) hE
    subst hb
    have hd : d = 0 := by
      by_contra hd
      exact
        (not_finiteInitialKineticEnergy_heatShearFullDriftInitialVelocity
          (a := a) (k := k) (d := d) (c := c) hd)
          (by
            simpa [heatShearTransportFullDriftInitialVelocity_zero_transport] using hE)
    subst hd
    have hak : a * k = 0 := by
      by_contra hak
      have ha : a ≠ 0 := by
        intro ha
        exact hak (by simp [ha])
      have hk : k ≠ 0 := by
        intro hk
        exact hak (by simp [hk])
      exact
        (not_finiteInitialKineticEnergy_heatShearVerticalDriftInitialVelocity
          (a := a) (k := k) (c := c) ha hk)
          (by
            simpa [heatShearTransportFullDriftInitialVelocity_zero_transport,
              heatShearFullDriftInitialVelocity_zero_streamwiseDrift] using hE)
    have hc : c = 0 := by
      rcases mul_eq_zero.mp hak with ha | hk
      · by_contra hc
        have hcvec : EuclideanSpace.single nsCoord2 c ≠ (0 : NSSpace) := by
          intro hzero
          exact hc (by simpa [nsCoord2] using congrArg (fun v : NSSpace => v nsCoord2) hzero)
        exact
          (not_finiteInitialKineticEnergy_constantInitialVelocity
            (c := EuclideanSpace.single nsCoord2 c) hcvec)
            (by
              simpa [heatShearTransportFullDriftInitialVelocity_zero_transport,
                heatShearFullDriftInitialVelocity_zero_streamwiseDrift,
                heatShearVerticalDriftInitialVelocity, constantInitialVelocity_add, ha,
                heatShearInitialVelocity_zero_of_amplitude_zero] using hE)
      · by_contra hc
        have hcvec : EuclideanSpace.single nsCoord2 c ≠ (0 : NSSpace) := by
          intro hzero
          exact hc (by simpa [nsCoord2] using congrArg (fun v : NSSpace => v nsCoord2) hzero)
        exact
          (not_finiteInitialKineticEnergy_constantInitialVelocity
            (c := EuclideanSpace.single nsCoord2 c) hcvec)
            (by
              simpa [heatShearTransportFullDriftInitialVelocity_zero_transport,
                heatShearFullDriftInitialVelocity_zero_streamwiseDrift,
                heatShearVerticalDriftInitialVelocity, constantInitialVelocity_add, hk,
                heatShearInitialVelocity_zero_of_wavenumber_zero] using hE)
    exact ⟨rfl, rfl, hc, hak⟩
  · rintro ⟨rfl, rfl, rfl, hak⟩
    have hzeroFinite : finiteInitialKineticEnergy (0 : NSInitialVelocity) := by
      have hzeroDensity :
          initialKineticEnergyDensity (0 : NSInitialVelocity) =
            (fun _ : NSSpace => (0 : ℝ)) := by
        funext x
        simp [initialKineticEnergyDensity]
      rw [finiteInitialKineticEnergy, hzeroDensity]
      exact
        MeasureTheory.integrable_zero NSSpace ℝ
          (MeasureTheory.volume : MeasureTheory.Measure NSSpace)
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
        hzeroFinite
    · simpa [heatShearTransportFullDriftInitialVelocity_zero_transport,
        heatShearFullDriftInitialVelocity_zero_streamwiseDrift,
        heatShearVerticalDriftInitialVelocity, constantInitialVelocity_add, hzeroConst, hk,
        heatShearInitialVelocity_zero_of_wavenumber_zero] using
        hzeroFinite

/-- Transported heat-shear initial data have finite whole-space kinetic energy
exactly in the zero-data case. -/
theorem finiteInitialKineticEnergy_heatShearTransportInitialVelocity_iff
    {a k b : ℝ} :
    finiteInitialKineticEnergy (heatShearTransportInitialVelocity a k b) ↔
      b = 0 ∧ a * k = 0 := by
  simpa [heatShearTransportFullDriftInitialVelocity_zero_drifts] using
    (finiteInitialKineticEnergy_heatShearTransportFullDriftInitialVelocity_iff
      (a := a) (k := k) (b := b) (d := 0) (c := 0))

/-- The repaired structured whole-space input domain contains no problem datum
whose initial velocity is a transported full-drift heat-shear profile with
nonzero transport speed. -/
theorem not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_heatShearTransportFullDriftInitialVelocity
    {a k b d c : ℝ}
    (hb : b ≠ 0) :
    ¬ Nonempty { P : FiniteEnergyAdmissibleNavierStokesProblemData //
        P.initialVelocity = heatShearTransportFullDriftInitialVelocity a k b d c } := by
  exact
    not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearTransportFullDriftInitialVelocity a k b d c)
      (not_finiteInitialKineticEnergy_heatShearTransportFullDriftInitialVelocity hb)


end UniformVorticityContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
