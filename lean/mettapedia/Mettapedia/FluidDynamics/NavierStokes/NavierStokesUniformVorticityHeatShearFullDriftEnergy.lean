import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityHeatShearStreamwiseDriftEnergy
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityHeatShearVerticalDriftEnergy

/-!
# Full-drift heat-shear finite-energy classifications

Kinetic-energy identities, finite-energy obstructions, and exact finite-energy
classification lemmas for heat-shear data with both streamwise and vertical
constant drift.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section UniformVorticityContinuation

/-- The initial kinetic-energy density of the heat-shear datum with full
constant drift is the streamwise-drift density plus the constant vertical drift
term `c²`. -/
theorem initialKineticEnergyDensity_heatShearFullDriftInitialVelocity
    (a k d c : ℝ) :
    initialKineticEnergyDensity (heatShearFullDriftInitialVelocity a k d c) =
      fun x => heatShearStreamwiseDriftKineticEnergyDensity a k d x + c ^ (2 : ℕ) := by
  funext x
  rw [initialKineticEnergyDensity, heatShearFullDriftInitialVelocity_apply]
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
  simp [nsCoord0, nsCoord1, nsCoord2, heatShearStreamwiseDriftKineticEnergyDensity, pow_two]

/-- On each time slice, the damped heat-shear field with full constant drift
carries the streamwise-drift density plus the constant vertical drift
contribution `c²`. -/
theorem kineticEnergyDensity_heatShearFullDriftVelocityField
    (ν a k d c : ℝ) (t : NSTime) :
    kineticEnergyDensity (heatShearFullDriftVelocityField ν a k d c) t =
      fun x =>
        heatShearStreamwiseDriftKineticEnergyDensity
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t)) k d x + c ^ (2 : ℕ) := by
  let A : ℝ := a * Real.exp (-(ν * k ^ (2 : ℕ)) * t)
  calc
    kineticEnergyDensity (heatShearFullDriftVelocityField ν a k d c) t =
      initialKineticEnergyDensity (heatShearFullDriftInitialVelocity A k d c) := by
        funext x
        simp [kineticEnergyDensity, initialKineticEnergyDensity, A,
          heatShearFullDriftVelocityField_apply, heatShearFullDriftInitialVelocity_apply]
    _ = fun x => heatShearStreamwiseDriftKineticEnergyDensity A k d x + c ^ (2 : ℕ) :=
      initialKineticEnergyDensity_heatShearFullDriftInitialVelocity A k d c
    _ = fun x =>
        heatShearStreamwiseDriftKineticEnergyDensity
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t)) k d x + c ^ (2 : ℕ) := by
        simp [A]

/-- A heat-shear field with nonzero constant streamwise drift remains
nonintegrable on `ℝ^3` even after adding an arbitrary constant vertical drift. -/
theorem not_integrable_kineticEnergyDensity_heatShearFullDriftVelocityField
    {ν a k d c : ℝ} (hd : d ≠ 0) (t : NSTime) :
    ¬ MeasureTheory.Integrable
      (kineticEnergyDensity (heatShearFullDriftVelocityField ν a k d c) t) := by
  intro hInt
  let A : ℝ := a * Real.exp (-(ν * k ^ (2 : ℕ)) * t)
  have hIntDrift :
      MeasureTheory.Integrable
        (fun x => heatShearStreamwiseDriftKineticEnergyDensity A k d x + c ^ (2 : ℕ)) := by
    simpa [kineticEnergyDensity_heatShearFullDriftVelocityField ν a k d c t, A] using hInt
  have hIntStreamwise :
      MeasureTheory.Integrable (heatShearStreamwiseDriftKineticEnergyDensity A k d) := by
    refine MeasureTheory.Integrable.mono' hIntDrift
      (continuous_heatShearStreamwiseDriftKineticEnergyDensity A k d).aestronglyMeasurable ?_
    filter_upwards with x
    have hx : 0 ≤ heatShearStreamwiseDriftKineticEnergyDensity A k d x := by
      dsimp [heatShearStreamwiseDriftKineticEnergyDensity]
      nlinarith [sq_nonneg (d + A * Real.sin (k * x nsCoord1))]
    rw [Real.norm_of_nonneg hx]
    exact le_add_of_nonneg_right (by positivity)
  exact
    not_integrable_heatShearStreamwiseDriftKineticEnergyDensity
      (a := A) (k := k) (d := d) hd hIntStreamwise

/-- Therefore a heat-shear field with nonzero streamwise drift still fails the
global bounded-energy predicate after any added constant vertical drift. -/
theorem not_boundedKineticEnergy_heatShearFullDriftVelocityField
    {ν a k d c : ℝ} (hd : d ≠ 0) :
    ¬ boundedKineticEnergy (heatShearFullDriftVelocityField ν a k d c) := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_heatShearFullDriftVelocityField
      (ν := ν) (a := a) (k := k) (d := d) (c := c) hd 0 (hbound 0).1

/-- On every nonnegative slab, the full-drift heat-shear family also fails the
finite-time bounded-energy predicate whenever the streamwise drift is nonzero.
-/
theorem not_boundedKineticEnergyUpTo_heatShearFullDriftVelocityField
    {ν a k d c T : ℝ}
    (hd : d ≠ 0)
    (hT : 0 ≤ T) :
    ¬ boundedKineticEnergyUpTo (heatShearFullDriftVelocityField ν a k d c) T := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_heatShearFullDriftVelocityField
      (ν := ν) (a := a) (k := k) (d := d) (c := c) hd 0 ((hbound 0 le_rfl hT).1)

/-- Any field matching the full-drift heat-shear datum at time `0` has the
same time-zero kinetic-energy density as that explicit initial profile. -/
theorem kineticEnergyDensity_zero_eq_of_matchesInitialVelocity_heatShearFullDriftInitialVelocity
    {u : NSVelocityField} {a k d c : ℝ}
    (hinit : MatchesInitialVelocity (heatShearFullDriftInitialVelocity a k d c) u) :
    kineticEnergyDensity u 0 =
      fun x => heatShearStreamwiseDriftKineticEnergyDensity a k d x + c ^ (2 : ℕ) := by
  calc
    kineticEnergyDensity u 0 =
        initialKineticEnergyDensity (heatShearFullDriftInitialVelocity a k d c) := by
          symm
          exact initialKineticEnergyDensity_eq_of_matchesInitialVelocity hinit
    _ = fun x => heatShearStreamwiseDriftKineticEnergyDensity a k d x + c ^ (2 : ℕ) :=
      initialKineticEnergyDensity_heatShearFullDriftInitialVelocity a k d c

/-- Therefore any velocity field matching full-drift heat-shear initial data
with nonzero streamwise drift already fails the time-zero integrability
requirement. -/
theorem not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_heatShearFullDriftInitialVelocity
    {u : NSVelocityField} {a k d c : ℝ}
    (hd : d ≠ 0)
    (hinit : MatchesInitialVelocity (heatShearFullDriftInitialVelocity a k d c) u) :
    ¬ MeasureTheory.Integrable (kineticEnergyDensity u 0) := by
  intro hInt
  have hIntDrift :
      MeasureTheory.Integrable
        (fun x => heatShearStreamwiseDriftKineticEnergyDensity a k d x + c ^ (2 : ℕ)) := by
    simpa
      [kineticEnergyDensity_zero_eq_of_matchesInitialVelocity_heatShearFullDriftInitialVelocity
        hinit] using hInt
  have hIntStreamwise :
      MeasureTheory.Integrable (heatShearStreamwiseDriftKineticEnergyDensity a k d) := by
    refine MeasureTheory.Integrable.mono' hIntDrift
      (continuous_heatShearStreamwiseDriftKineticEnergyDensity a k d).aestronglyMeasurable ?_
    filter_upwards with x
    have hx : 0 ≤ heatShearStreamwiseDriftKineticEnergyDensity a k d x := by
      dsimp [heatShearStreamwiseDriftKineticEnergyDensity]
      nlinarith [sq_nonneg (d + a * Real.sin (k * x nsCoord1))]
    rw [Real.norm_of_nonneg hx]
    exact le_add_of_nonneg_right (by positivity)
  exact
    not_integrable_heatShearStreamwiseDriftKineticEnergyDensity
      (a := a) (k := k) (d := d) hd hIntStreamwise

/-- On every nonnegative slab, full-drift heat-shear initial data with nonzero
streamwise drift rule out the bounded-energy witness slot regardless of later
dynamics. -/
theorem not_boundedKineticEnergyUpTo_of_matchesInitialVelocity_heatShearFullDriftInitialVelocity
    {u : NSVelocityField} {a k d c T : ℝ}
    (hd : d ≠ 0)
    (hT : 0 ≤ T)
    (hinit : MatchesInitialVelocity (heatShearFullDriftInitialVelocity a k d c) u) :
    ¬ boundedKineticEnergyUpTo u T := by
  exact
    not_boundedKineticEnergyUpTo_of_not_integrable_kineticEnergyDensity_zero
      (u := u)
      (not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_heatShearFullDriftInitialVelocity
        (u := u) hd hinit)
      hT

/-- The same obstruction rules out global bounded kinetic energy for any field
matching full-drift heat-shear initial data with nonzero streamwise drift. -/
theorem not_boundedKineticEnergy_of_matchesInitialVelocity_heatShearFullDriftInitialVelocity
    {u : NSVelocityField} {a k d c : ℝ}
    (hd : d ≠ 0)
    (hinit : MatchesInitialVelocity (heatShearFullDriftInitialVelocity a k d c) u) :
    ¬ boundedKineticEnergy u := by
  exact
    not_boundedKineticEnergy_of_not_integrable_kineticEnergyDensity_zero
      (u := u)
      (not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_heatShearFullDriftInitialVelocity
        (u := u) hd hinit)

/-- Full-drift heat-shear initial data with nonzero streamwise drift are not
finite-energy admissible on `ℝ^3`. -/
theorem not_finiteInitialKineticEnergy_heatShearFullDriftInitialVelocity
    {a k d c : ℝ}
    (hd : d ≠ 0) :
    ¬ finiteInitialKineticEnergy (heatShearFullDriftInitialVelocity a k d c) := by
  intro hE
  have hIntDrift :
      MeasureTheory.Integrable
        (fun x => heatShearStreamwiseDriftKineticEnergyDensity a k d x + c ^ (2 : ℕ)) := by
    simpa [finiteInitialKineticEnergy,
      initialKineticEnergyDensity_heatShearFullDriftInitialVelocity a k d c] using hE
  have hIntStreamwise :
      MeasureTheory.Integrable (heatShearStreamwiseDriftKineticEnergyDensity a k d) := by
    refine MeasureTheory.Integrable.mono' hIntDrift
      (continuous_heatShearStreamwiseDriftKineticEnergyDensity a k d).aestronglyMeasurable ?_
    filter_upwards with x
    have hx : 0 ≤ heatShearStreamwiseDriftKineticEnergyDensity a k d x := by
      dsimp [heatShearStreamwiseDriftKineticEnergyDensity]
      nlinarith [sq_nonneg (d + a * Real.sin (k * x nsCoord1))]
    rw [Real.norm_of_nonneg hx]
    exact le_add_of_nonneg_right (by positivity)
  exact
    not_integrable_heatShearStreamwiseDriftKineticEnergyDensity
      (a := a) (k := k) (d := d) hd hIntStreamwise

/-- Full-drift heat-shear initial data have finite whole-space kinetic energy
exactly in the zero-data case. -/
theorem finiteInitialKineticEnergy_heatShearFullDriftInitialVelocity_iff
    {a k d c : ℝ} :
    finiteInitialKineticEnergy (heatShearFullDriftInitialVelocity a k d c) ↔
      d = 0 ∧ c = 0 ∧ a * k = 0 := by
  constructor
  · intro hE
    have hd : d = 0 := by
      by_contra hd
      exact
        (not_finiteInitialKineticEnergy_heatShearFullDriftInitialVelocity
          (a := a) (k := k) (d := d) (c := c) hd) hE
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
            simpa [heatShearFullDriftInitialVelocity_zero_streamwiseDrift] using hE)
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
              simpa [heatShearFullDriftInitialVelocity_zero_streamwiseDrift,
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
              simpa [heatShearFullDriftInitialVelocity_zero_streamwiseDrift,
                heatShearVerticalDriftInitialVelocity, constantInitialVelocity_add, hk,
                heatShearInitialVelocity_zero_of_wavenumber_zero] using hE)
    exact ⟨rfl, hc, hak⟩
  · rintro ⟨rfl, rfl, hak⟩
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
    · simpa [heatShearFullDriftInitialVelocity_zero_streamwiseDrift,
        heatShearVerticalDriftInitialVelocity, constantInitialVelocity_add, hzeroConst, ha,
        heatShearInitialVelocity_zero_of_amplitude_zero] using
        hzeroFinite
    · simpa [heatShearFullDriftInitialVelocity_zero_streamwiseDrift,
        heatShearVerticalDriftInitialVelocity, constantInitialVelocity_add, hzeroConst, hk,
        heatShearInitialVelocity_zero_of_wavenumber_zero] using
        hzeroFinite

/-- Heat-shear initial data with constant vertical drift have finite whole-space
kinetic energy exactly in the zero-data case. -/
theorem finiteInitialKineticEnergy_heatShearInitialVelocity_iff
    {a k : ℝ} :
    finiteInitialKineticEnergy (heatShearInitialVelocity a k) ↔
      a * k = 0 := by
  simpa [heatShearFullDriftInitialVelocity_zero_drifts] using
    (finiteInitialKineticEnergy_heatShearFullDriftInitialVelocity_iff
      (a := a) (k := k) (d := 0) (c := 0))

/-- Heat-shear initial data with constant vertical drift have finite whole-space
kinetic energy exactly in the zero-data case. -/
theorem finiteInitialKineticEnergy_heatShearVerticalDriftInitialVelocity_iff
    {a k c : ℝ} :
    finiteInitialKineticEnergy (heatShearVerticalDriftInitialVelocity a k c) ↔
      c = 0 ∧ a * k = 0 := by
  simpa [heatShearFullDriftInitialVelocity_zero_streamwiseDrift] using
    (finiteInitialKineticEnergy_heatShearFullDriftInitialVelocity_iff
      (a := a) (k := k) (d := 0) (c := c))

/-- Heat-shear initial data with constant streamwise drift have finite whole-space
kinetic energy exactly in the zero-data case. -/
theorem finiteInitialKineticEnergy_heatShearStreamwiseDriftInitialVelocity_iff
    {a k d : ℝ} :
    finiteInitialKineticEnergy (heatShearStreamwiseDriftInitialVelocity a k d) ↔
      d = 0 ∧ a * k = 0 := by
  simpa [heatShearFullDriftInitialVelocity_zero_verticalDrift] using
    (finiteInitialKineticEnergy_heatShearFullDriftInitialVelocity_iff
      (a := a) (k := k) (d := d) (c := 0))

/-- The repaired structured whole-space input domain contains no problem datum
whose initial velocity is a full-drift heat-shear profile with nonzero
streamwise drift. -/
theorem not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_heatShearFullDriftInitialVelocity
    {a k d c : ℝ}
    (hd : d ≠ 0) :
    ¬ Nonempty { P : FiniteEnergyAdmissibleNavierStokesProblemData //
        P.initialVelocity = heatShearFullDriftInitialVelocity a k d c } := by
  exact
    not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearFullDriftInitialVelocity a k d c)
      (not_finiteInitialKineticEnergy_heatShearFullDriftInitialVelocity hd)

end UniformVorticityContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
