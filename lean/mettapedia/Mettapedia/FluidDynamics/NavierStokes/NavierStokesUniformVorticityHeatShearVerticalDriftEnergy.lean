import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityHeatShearEnergyCore

/-!
# Vertical-drift heat-shear finite-energy obstructions

Kinetic-energy identities and finite-energy obstructions for pure heat-shear
data and heat-shear data with constant vertical drift.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section UniformVorticityContinuation

/-- The initial kinetic-energy density of the heat-shear datum with added
constant vertical drift is the heat-shear density plus the constant drift term
`c²`. -/
theorem initialKineticEnergyDensity_heatShearVerticalDriftInitialVelocity
    (a k c : ℝ) :
    initialKineticEnergyDensity (heatShearVerticalDriftInitialVelocity a k c) =
      fun x => heatShearKineticEnergyDensity a k x + c ^ (2 : ℕ) := by
  funext x
  have hs :
      (|a| * |Real.sin (k * x.ofLp 1)|) ^ (2 : ℕ) =
        heatShearKineticEnergyDensity a k x := by
    rw [heatShearKineticEnergyDensity]
    calc
      (|a| * |Real.sin (k * x.ofLp 1)|) ^ (2 : ℕ) =
          |a * Real.sin (k * x.ofLp 1)| ^ (2 : ℕ) := by
            rw [abs_mul]
      _ = a * Real.sin (k * x.ofLp 1) * (a * Real.sin (k * x.ofLp 1)) := by
            simpa [pow_two] using (sq_abs (a * Real.sin (k * x.ofLp 1)))
  rw [initialKineticEnergyDensity, heatShearVerticalDriftInitialVelocity_apply]
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
  simp [nsCoord0, nsCoord1, nsCoord2, hs]

/-- On each time slice, the damped heat-shear field with additional constant
vertical drift carries the heat-shear energy density plus the constant drift
contribution `c²`. -/
theorem kineticEnergyDensity_heatShearVerticalDriftVelocityField
    (ν a k c : ℝ) (t : NSTime) :
    kineticEnergyDensity (heatShearVerticalDriftVelocityField ν a k c) t =
      fun x =>
        heatShearKineticEnergyDensity
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t)) k x + c ^ (2 : ℕ) := by
  let A : ℝ := a * Real.exp (-(ν * k ^ (2 : ℕ)) * t)
  calc
    kineticEnergyDensity (heatShearVerticalDriftVelocityField ν a k c) t =
      initialKineticEnergyDensity (heatShearVerticalDriftInitialVelocity A k c) := by
        funext x
        simp [kineticEnergyDensity, initialKineticEnergyDensity, A,
          heatShearVerticalDriftVelocityField_apply, heatShearVerticalDriftInitialVelocity_apply]
    _ = fun x => heatShearKineticEnergyDensity A k x + c ^ (2 : ℕ) :=
      initialKineticEnergyDensity_heatShearVerticalDriftInitialVelocity A k c
    _ = fun x =>
        heatShearKineticEnergyDensity
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t)) k x + c ^ (2 : ℕ) := by
        simp [A]

/-- A nontrivial damped heat-shear field with vertical drift is not spatially
integrable on `ℝ^3` with respect to the kinetic-energy density on any time
slice. -/
theorem not_integrable_kineticEnergyDensity_heatShearVerticalDriftVelocityField
    {ν a k c : ℝ} (ha : a ≠ 0) (hk : k ≠ 0) (t : NSTime) :
    ¬ MeasureTheory.Integrable
      (kineticEnergyDensity (heatShearVerticalDriftVelocityField ν a k c) t) := by
  intro hInt
  have hA :
      a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) ≠ 0 := by
    exact mul_ne_zero ha (Real.exp_ne_zero _)
  have hIntDrift :
      MeasureTheory.Integrable
        (fun x =>
          heatShearKineticEnergyDensity
            (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t)) k x + c ^ (2 : ℕ)) := by
    simpa [kineticEnergyDensity_heatShearVerticalDriftVelocityField ν a k c t] using hInt
  have hIntHeat :
      MeasureTheory.Integrable
        (heatShearKineticEnergyDensity
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t)) k) := by
    refine MeasureTheory.Integrable.mono' hIntDrift
      (continuous_heatShearKineticEnergyDensity
        (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t)) k).aestronglyMeasurable ?_
    filter_upwards with x
    have hx :
        0 ≤ heatShearKineticEnergyDensity
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t)) k x := by
      dsimp [heatShearKineticEnergyDensity]
      nlinarith [sq_nonneg
        ((a * Real.exp (-(ν * k ^ (2 : ℕ)) * t)) * Real.sin (k * x nsCoord1))]
    rw [Real.norm_of_nonneg hx]
    exact le_add_of_nonneg_right (by positivity)
  exact not_integrable_heatShearKineticEnergyDensity hA hk hIntHeat

/-- Therefore a nontrivial damped heat-shear field with vertical drift never
satisfies the concrete global bounded-energy predicate on `ℝ^3`. -/
theorem not_boundedKineticEnergy_heatShearVerticalDriftVelocityField
    {ν a k c : ℝ} (ha : a ≠ 0) (hk : k ≠ 0) :
    ¬ boundedKineticEnergy (heatShearVerticalDriftVelocityField ν a k c) := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_heatShearVerticalDriftVelocityField
      (ν := ν) (a := a) (k := k) (c := c) ha hk 0 (hbound 0).1

/-- On every nonnegative slab, a nontrivial damped heat-shear field with
vertical drift also fails the finite-time bounded-energy predicate. -/
theorem not_boundedKineticEnergyUpTo_heatShearVerticalDriftVelocityField
    {ν a k c T : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hT : 0 ≤ T) :
    ¬ boundedKineticEnergyUpTo (heatShearVerticalDriftVelocityField ν a k c) T := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_heatShearVerticalDriftVelocityField
      (ν := ν) (a := a) (k := k) (c := c) ha hk 0 ((hbound 0 le_rfl hT).1)

/-- Any field matching the heat-shear initial datum at time `0` has the same
time-zero kinetic-energy density as that explicit initial profile. -/
theorem kineticEnergyDensity_zero_eq_of_matchesInitialVelocity_heatShearInitialVelocity
    {u : NSVelocityField} {a k : ℝ}
    (hinit : MatchesInitialVelocity (heatShearInitialVelocity a k) u) :
    kineticEnergyDensity u 0 = heatShearKineticEnergyDensity a k := by
  calc
    kineticEnergyDensity u 0 = initialKineticEnergyDensity (heatShearInitialVelocity a k) := by
      symm
      exact initialKineticEnergyDensity_eq_of_matchesInitialVelocity hinit
    _ = heatShearKineticEnergyDensity a k :=
      initialKineticEnergyDensity_heatShearInitialVelocity a k

/-- Therefore any velocity field matching nontrivial heat-shear initial data
already fails the time-zero integrability requirement. -/
theorem not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_heatShearInitialVelocity
    {u : NSVelocityField} {a k : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hinit : MatchesInitialVelocity (heatShearInitialVelocity a k) u) :
    ¬ MeasureTheory.Integrable (kineticEnergyDensity u 0) := by
  intro hInt
  have hIntHeat :
      MeasureTheory.Integrable (heatShearKineticEnergyDensity a k) := by
    simpa [kineticEnergyDensity_zero_eq_of_matchesInitialVelocity_heatShearInitialVelocity hinit]
      using hInt
  exact not_integrable_heatShearKineticEnergyDensity ha hk hIntHeat

/-- On every nonnegative slab, nontrivial heat-shear initial data rule out the
bounded-energy witness slot regardless of later dynamics. -/
theorem not_boundedKineticEnergyUpTo_of_matchesInitialVelocity_heatShearInitialVelocity
    {u : NSVelocityField} {a k T : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hT : 0 ≤ T)
    (hinit : MatchesInitialVelocity (heatShearInitialVelocity a k) u) :
    ¬ boundedKineticEnergyUpTo u T := by
  exact
    not_boundedKineticEnergyUpTo_of_not_integrable_kineticEnergyDensity_zero
      (u := u)
      (not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_heatShearInitialVelocity
        (u := u) ha hk hinit)
      hT

/-- The same obstruction rules out global bounded kinetic energy for any field
matching nontrivial heat-shear initial data. -/
theorem not_boundedKineticEnergy_of_matchesInitialVelocity_heatShearInitialVelocity
    {u : NSVelocityField} {a k : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hinit : MatchesInitialVelocity (heatShearInitialVelocity a k) u) :
    ¬ boundedKineticEnergy u := by
  exact
    not_boundedKineticEnergy_of_not_integrable_kineticEnergyDensity_zero
      (u := u)
      (not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_heatShearInitialVelocity
        (u := u) ha hk hinit)

/-- Nontrivial heat-shear initial data are not finite-energy admissible on
`ℝ^3`. -/
theorem not_finiteInitialKineticEnergy_heatShearInitialVelocity
    {a k : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0) :
    ¬ finiteInitialKineticEnergy (heatShearInitialVelocity a k) := by
  intro hE
  have hIntHeat : MeasureTheory.Integrable (heatShearKineticEnergyDensity a k) := by
    simpa [finiteInitialKineticEnergy,
      initialKineticEnergyDensity_heatShearInitialVelocity a k] using hE
  exact not_integrable_heatShearKineticEnergyDensity ha hk hIntHeat

/-- The repaired structured whole-space input domain contains no problem datum
whose initial velocity is a nontrivial heat-shear profile. -/
theorem not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_heatShearInitialVelocity
    {a k : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0) :
    ¬ Nonempty { P : FiniteEnergyAdmissibleNavierStokesProblemData //
        P.initialVelocity = heatShearInitialVelocity a k } := by
  exact
    not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearInitialVelocity a k)
      (not_finiteInitialKineticEnergy_heatShearInitialVelocity ha hk)

/-- If a velocity field matches the initial data
`x ↦ (a * sin (k * x₁), 0, c)` at time `0`, then its time-zero kinetic-energy
density is the heat-shear density plus the constant vertical drift
contribution `c²`. -/
theorem kineticEnergyDensity_zero_eq_of_matchesInitialVelocity_heatShearVerticalDriftInitialVelocity
    {u : NSVelocityField} {a k c : ℝ}
    (hinit : MatchesInitialVelocity (heatShearVerticalDriftInitialVelocity a k c) u) :
    kineticEnergyDensity u 0 =
      fun x => heatShearKineticEnergyDensity a k x + c ^ (2 : ℕ) := by
  funext x
  have hs :
      (|a| * |Real.sin (k * x.ofLp 1)|) ^ (2 : ℕ) =
        heatShearKineticEnergyDensity a k x := by
    rw [heatShearKineticEnergyDensity]
    calc
      (|a| * |Real.sin (k * x.ofLp 1)|) ^ (2 : ℕ) =
          |a * Real.sin (k * x.ofLp 1)| ^ (2 : ℕ) := by
            rw [abs_mul]
      _ = a * Real.sin (k * x.ofLp 1) * (a * Real.sin (k * x.ofLp 1)) := by
            simpa [pow_two] using (sq_abs (a * Real.sin (k * x.ofLp 1)))
  rw [kineticEnergyDensity, hinit x, heatShearVerticalDriftInitialVelocity_apply]
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
  simp [nsCoord0, nsCoord1, nsCoord2, hs]

/-- Therefore any velocity field matching nontrivial heat-shear initial data
with vertical drift already fails the time-zero integrability requirement. -/
theorem not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_heatShearVerticalDriftInitialVelocity
    {u : NSVelocityField} {a k c : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hinit : MatchesInitialVelocity (heatShearVerticalDriftInitialVelocity a k c) u) :
    ¬ MeasureTheory.Integrable (kineticEnergyDensity u 0) := by
  intro hInt
  have hIntDrift :
      MeasureTheory.Integrable
        (fun x => heatShearKineticEnergyDensity a k x + c ^ (2 : ℕ)) := by
    simpa
      [kineticEnergyDensity_zero_eq_of_matchesInitialVelocity_heatShearVerticalDriftInitialVelocity
        hinit] using hInt
  have hIntHeat : MeasureTheory.Integrable (heatShearKineticEnergyDensity a k) := by
    refine MeasureTheory.Integrable.mono' hIntDrift
      (continuous_heatShearKineticEnergyDensity a k).aestronglyMeasurable ?_
    filter_upwards with x
    have hx : 0 ≤ heatShearKineticEnergyDensity a k x := by
      dsimp [heatShearKineticEnergyDensity]
      nlinarith [sq_nonneg (a * Real.sin (k * x nsCoord1))]
    rw [Real.norm_of_nonneg hx]
    exact le_add_of_nonneg_right (by positivity)
  exact not_integrable_heatShearKineticEnergyDensity ha hk hIntHeat

/-- On every nonnegative slab, nontrivial heat-shear initial data with vertical
drift rule out the bounded-energy witness slot regardless of later dynamics. -/
theorem not_boundedKineticEnergyUpTo_of_matchesInitialVelocity_heatShearVerticalDriftInitialVelocity
    {u : NSVelocityField} {a k c T : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hT : 0 ≤ T)
    (hinit : MatchesInitialVelocity (heatShearVerticalDriftInitialVelocity a k c) u) :
    ¬ boundedKineticEnergyUpTo u T := by
  exact
    not_boundedKineticEnergyUpTo_of_not_integrable_kineticEnergyDensity_zero
      (u := u)
      (not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_heatShearVerticalDriftInitialVelocity
        (u := u) ha hk hinit)
      hT

/-- The same obstruction rules out global bounded kinetic energy for any field
matching nontrivial heat-shear initial data with vertical drift. -/
theorem not_boundedKineticEnergy_of_matchesInitialVelocity_heatShearVerticalDriftInitialVelocity
    {u : NSVelocityField} {a k c : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hinit : MatchesInitialVelocity (heatShearVerticalDriftInitialVelocity a k c) u) :
    ¬ boundedKineticEnergy u := by
  exact
    not_boundedKineticEnergy_of_not_integrable_kineticEnergyDensity_zero
      (u := u)
      (not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_heatShearVerticalDriftInitialVelocity
        (u := u) ha hk hinit)

/-- Nontrivial heat-shear initial data with vertical drift are not
finite-energy admissible on `ℝ^3`. -/
theorem not_finiteInitialKineticEnergy_heatShearVerticalDriftInitialVelocity
    {a k c : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0) :
    ¬ finiteInitialKineticEnergy (heatShearVerticalDriftInitialVelocity a k c) := by
  intro hE
  have hIntDrift :
      MeasureTheory.Integrable
        (fun x => heatShearKineticEnergyDensity a k x + c ^ (2 : ℕ)) := by
    simpa [finiteInitialKineticEnergy,
      initialKineticEnergyDensity_heatShearVerticalDriftInitialVelocity a k c] using hE
  have hIntHeat : MeasureTheory.Integrable (heatShearKineticEnergyDensity a k) := by
    refine MeasureTheory.Integrable.mono' hIntDrift
      (continuous_heatShearKineticEnergyDensity a k).aestronglyMeasurable ?_
    filter_upwards with x
    have hx : 0 ≤ heatShearKineticEnergyDensity a k x := by
      dsimp [heatShearKineticEnergyDensity]
      nlinarith [sq_nonneg (a * Real.sin (k * x nsCoord1))]
    rw [Real.norm_of_nonneg hx]
    exact le_add_of_nonneg_right (by positivity)
  exact not_integrable_heatShearKineticEnergyDensity ha hk hIntHeat

/-- The repaired structured whole-space input domain contains no problem datum
whose initial velocity is a nontrivial heat-shear profile with vertical drift.
-/
theorem not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_heatShearVerticalDriftInitialVelocity
    {a k c : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0) :
    ¬ Nonempty { P : FiniteEnergyAdmissibleNavierStokesProblemData //
        P.initialVelocity = heatShearVerticalDriftInitialVelocity a k c } := by
  exact
    not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearVerticalDriftInitialVelocity a k c)
      (not_finiteInitialKineticEnergy_heatShearVerticalDriftInitialVelocity ha hk)

end UniformVorticityContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
