import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityHeatShearEnergyCore

/-!
# Streamwise-drift heat-shear finite-energy obstructions

Kinetic-energy identities and finite-energy obstructions for heat-shear data
with constant streamwise drift.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section UniformVorticityContinuation

/-- Kinetic-energy density carried by the heat-shear initial profile with
constant streamwise drift
`x ↦ (d + a * sin (k * x₁), 0, 0)`. -/
def heatShearStreamwiseDriftKineticEnergyDensity (a k d : ℝ) : NSSpace → ℝ :=
  fun x =>
    (d + a * Real.sin (k * x nsCoord1)) *
      (d + a * Real.sin (k * x nsCoord1))

/-- The heat-shear kinetic-energy density with constant streamwise drift is
continuous on `ℝ^3`. -/
theorem continuous_heatShearStreamwiseDriftKineticEnergyDensity
    (a k d : ℝ) :
    Continuous (heatShearStreamwiseDriftKineticEnergyDensity a k d) := by
  have hcoord : Continuous fun x : NSSpace => x nsCoord1 := by
    simpa using (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ).continuous
  have hsin : Continuous fun x : NSSpace => Real.sin (k * x nsCoord1) := by
    change Continuous (Real.sin ∘ fun x : NSSpace => k * x nsCoord1)
    exact Real.continuous_sin.comp (continuous_const.mul hcoord)
  have hbase : Continuous fun x : NSSpace => d + a * Real.sin (k * x nsCoord1) := by
    exact continuous_const.add (continuous_const.mul hsin)
  exact hbase.mul hbase

/-- The heat-shear kinetic-energy density with streamwise drift is invariant
under the same lateral scaling that stretches only `x₀` and `x₂`. -/
theorem heatShearStreamwiseDriftKineticEnergyDensity_comp_heatShearLateralScaling
    (a k d : ℝ) :
    (fun x => heatShearStreamwiseDriftKineticEnergyDensity a k d (heatShearLateralScaling x)) =
      heatShearStreamwiseDriftKineticEnergyDensity a k d := by
  funext x
  simp [heatShearStreamwiseDriftKineticEnergyDensity, heatShearLateralScaling_apply_coord1]

/-- Any heat-shear profile with nonzero constant streamwise drift has
nonintegrable kinetic-energy density on `ℝ^3`.  The proof uses the same
determinant-`4` lateral scaling as pure heat shear, but now the witness point
is the origin where the density equals `d²`. -/
theorem not_integrable_heatShearStreamwiseDriftKineticEnergyDensity
    {a k d : ℝ} (hd : d ≠ 0) :
    ¬ MeasureTheory.Integrable (heatShearStreamwiseDriftKineticEnergyDensity a k d) := by
  intro hInt
  let x0 : NSSpace := 0
  have hnonneg : ∀ x, 0 ≤ heatShearStreamwiseDriftKineticEnergyDensity a k d x := by
    intro x
    dsimp [heatShearStreamwiseDriftKineticEnergyDensity]
    nlinarith [sq_nonneg (d + a * Real.sin (k * x nsCoord1))]
  have hx0 : heatShearStreamwiseDriftKineticEnergyDensity a k d x0 ≠ 0 := by
    have hd2 : d * d ≠ 0 := mul_ne_zero hd hd
    simpa [x0, heatShearStreamwiseDriftKineticEnergyDensity] using hd2
  have hpos : 0 < ∫ x, heatShearStreamwiseDriftKineticEnergyDensity a k d x := by
    exact MeasureTheory.integral_pos_of_integrable_nonneg_nonzero
      (x := x0)
      (continuous_heatShearStreamwiseDriftKineticEnergyDensity a k d)
      hInt hnonneg hx0
  let I : ℝ := ∫ x, heatShearStreamwiseDriftKineticEnergyDensity a k d x
  have hcomp :
      ∫ x, heatShearStreamwiseDriftKineticEnergyDensity a k d (heatShearLateralScaling x) = I := by
    calc
      ∫ x, heatShearStreamwiseDriftKineticEnergyDensity a k d (heatShearLateralScaling x)
          = ∫ x, heatShearStreamwiseDriftKineticEnergyDensity a k d x := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with x
              exact congrArg (fun f : NSSpace → ℝ => f x)
                (heatShearStreamwiseDriftKineticEnergyDensity_comp_heatShearLateralScaling a k d)
      _ = I := by rfl
  have hdet : LinearMap.det heatShearLateralScaling ≠ 0 := by
    rw [det_heatShearLateralScaling]
    norm_num
  have hmap :
      MeasureTheory.Measure.map heatShearLateralScaling
          (MeasureTheory.volume : MeasureTheory.Measure NSSpace) =
        ENNReal.ofReal ((4 : ℝ)⁻¹) •
          (MeasureTheory.volume : MeasureTheory.Measure NSSpace) := by
    rw [MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
      (μ := (MeasureTheory.volume : MeasureTheory.Measure NSSpace)) (f := heatShearLateralScaling)
      hdet]
    simp [det_heatShearLateralScaling]
  have hchange :
      ∫ x, heatShearStreamwiseDriftKineticEnergyDensity a k d (heatShearLateralScaling x) =
        ((4 : ℝ)⁻¹) * I := by
    calc
      ∫ x : NSSpace, heatShearStreamwiseDriftKineticEnergyDensity a k d (heatShearLateralScaling x)
          = ∫ y : NSSpace, heatShearStreamwiseDriftKineticEnergyDensity a k d y ∂
              MeasureTheory.Measure.map heatShearLateralScaling
                (MeasureTheory.volume : MeasureTheory.Measure NSSpace) := by
              symm
              exact MeasureTheory.integral_map
                (μ := (MeasureTheory.volume : MeasureTheory.Measure NSSpace))
                (heatShearLateralScaling.continuous_of_finiteDimensional.aemeasurable)
                ((continuous_heatShearStreamwiseDriftKineticEnergyDensity a k d).aestronglyMeasurable)
      _ = ((4 : ℝ)⁻¹) * I := by
            rw [hmap, MeasureTheory.integral_smul_measure]
            simp [I]
  have hEq : I = ((4 : ℝ)⁻¹) * I := by
    simpa [hcomp] using hchange
  have hzero : I = 0 := by
    norm_num at hEq
    linarith
  linarith

/-- The initial kinetic-energy density of the heat-shear datum with constant
streamwise drift is the explicit oscillatory density
`(d + a * sin (k * x₁))²`. -/
theorem initialKineticEnergyDensity_heatShearStreamwiseDriftInitialVelocity
    (a k d : ℝ) :
    initialKineticEnergyDensity (heatShearStreamwiseDriftInitialVelocity a k d) =
      heatShearStreamwiseDriftKineticEnergyDensity a k d := by
  funext x
  rw [initialKineticEnergyDensity, heatShearStreamwiseDriftInitialVelocity_apply]
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
  simp [nsCoord0, nsCoord1, heatShearStreamwiseDriftKineticEnergyDensity, pow_two]

/-- On each time slice, the damped heat-shear field with constant streamwise
drift carries the same oscillatory density with the amplitude rescaled by the
heat factor `exp (-(ν * k²) * t)`. -/
theorem kineticEnergyDensity_heatShearStreamwiseDriftVelocityField
    (ν a k d : ℝ) (t : NSTime) :
    kineticEnergyDensity (heatShearStreamwiseDriftVelocityField ν a k d) t =
      heatShearStreamwiseDriftKineticEnergyDensity
        (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t)) k d := by
  let A : ℝ := a * Real.exp (-(ν * k ^ (2 : ℕ)) * t)
  calc
    kineticEnergyDensity (heatShearStreamwiseDriftVelocityField ν a k d) t =
      initialKineticEnergyDensity (heatShearStreamwiseDriftInitialVelocity A k d) := by
        funext x
        simp [kineticEnergyDensity, initialKineticEnergyDensity, A,
          heatShearStreamwiseDriftVelocityField_apply, heatShearStreamwiseDriftInitialVelocity_apply]
    _ = heatShearStreamwiseDriftKineticEnergyDensity A k d :=
      initialKineticEnergyDensity_heatShearStreamwiseDriftInitialVelocity A k d
    _ = heatShearStreamwiseDriftKineticEnergyDensity
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t)) k d := by
        simp [A]

/-- A heat-shear field with nonzero constant streamwise drift is never spatially
integrable on `ℝ^3` with respect to the kinetic-energy density on any time
slice. -/
theorem not_integrable_kineticEnergyDensity_heatShearStreamwiseDriftVelocityField
    {ν a k d : ℝ} (hd : d ≠ 0) (t : NSTime) :
    ¬ MeasureTheory.Integrable
      (kineticEnergyDensity (heatShearStreamwiseDriftVelocityField ν a k d) t) := by
  intro hInt
  have hIntDrift :
      MeasureTheory.Integrable
        (heatShearStreamwiseDriftKineticEnergyDensity
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t)) k d) := by
    simpa [kineticEnergyDensity_heatShearStreamwiseDriftVelocityField ν a k d t] using hInt
  exact
    not_integrable_heatShearStreamwiseDriftKineticEnergyDensity
      (a := a * Real.exp (-(ν * k ^ (2 : ℕ)) * t)) (k := k) (d := d) hd hIntDrift

/-- Therefore a heat-shear field with nonzero constant streamwise drift never
satisfies the concrete global bounded-energy predicate on `ℝ^3`. -/
theorem not_boundedKineticEnergy_heatShearStreamwiseDriftVelocityField
    {ν a k d : ℝ} (hd : d ≠ 0) :
    ¬ boundedKineticEnergy (heatShearStreamwiseDriftVelocityField ν a k d) := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_heatShearStreamwiseDriftVelocityField
      (ν := ν) (a := a) (k := k) (d := d) hd 0 (hbound 0).1

/-- On every nonnegative slab, a heat-shear field with nonzero constant
streamwise drift also fails the finite-time bounded-energy predicate. -/
theorem not_boundedKineticEnergyUpTo_heatShearStreamwiseDriftVelocityField
    {ν a k d T : ℝ}
    (hd : d ≠ 0)
    (hT : 0 ≤ T) :
    ¬ boundedKineticEnergyUpTo (heatShearStreamwiseDriftVelocityField ν a k d) T := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_heatShearStreamwiseDriftVelocityField
      (ν := ν) (a := a) (k := k) (d := d) hd 0 ((hbound 0 le_rfl hT).1)

/-- Any field matching the heat-shear initial datum with nonzero constant
streamwise drift at time `0` has the same time-zero kinetic-energy density as
that explicit initial profile. -/
theorem kineticEnergyDensity_zero_eq_of_matchesInitialVelocity_heatShearStreamwiseDriftInitialVelocity
    {u : NSVelocityField} {a k d : ℝ}
    (hinit : MatchesInitialVelocity (heatShearStreamwiseDriftInitialVelocity a k d) u) :
    kineticEnergyDensity u 0 = heatShearStreamwiseDriftKineticEnergyDensity a k d := by
  calc
    kineticEnergyDensity u 0 =
        initialKineticEnergyDensity (heatShearStreamwiseDriftInitialVelocity a k d) := by
          symm
          exact initialKineticEnergyDensity_eq_of_matchesInitialVelocity hinit
    _ = heatShearStreamwiseDriftKineticEnergyDensity a k d :=
      initialKineticEnergyDensity_heatShearStreamwiseDriftInitialVelocity a k d

/-- Therefore any velocity field matching heat-shear initial data with nonzero
constant streamwise drift already fails the time-zero integrability
requirement. -/
theorem not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_heatShearStreamwiseDriftInitialVelocity
    {u : NSVelocityField} {a k d : ℝ}
    (hd : d ≠ 0)
    (hinit : MatchesInitialVelocity (heatShearStreamwiseDriftInitialVelocity a k d) u) :
    ¬ MeasureTheory.Integrable (kineticEnergyDensity u 0) := by
  intro hInt
  have hIntDrift :
      MeasureTheory.Integrable (heatShearStreamwiseDriftKineticEnergyDensity a k d) := by
    simpa
      [kineticEnergyDensity_zero_eq_of_matchesInitialVelocity_heatShearStreamwiseDriftInitialVelocity
        hinit] using hInt
  exact not_integrable_heatShearStreamwiseDriftKineticEnergyDensity (a := a) (k := k) hd hIntDrift

/-- On every nonnegative slab, heat-shear initial data with nonzero constant
streamwise drift rule out the bounded-energy witness slot regardless of later
dynamics. -/
theorem not_boundedKineticEnergyUpTo_of_matchesInitialVelocity_heatShearStreamwiseDriftInitialVelocity
    {u : NSVelocityField} {a k d T : ℝ}
    (hd : d ≠ 0)
    (hT : 0 ≤ T)
    (hinit : MatchesInitialVelocity (heatShearStreamwiseDriftInitialVelocity a k d) u) :
    ¬ boundedKineticEnergyUpTo u T := by
  exact
    not_boundedKineticEnergyUpTo_of_not_integrable_kineticEnergyDensity_zero
      (u := u)
      (not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_heatShearStreamwiseDriftInitialVelocity
        (u := u) hd hinit)
      hT

/-- The same obstruction rules out global bounded kinetic energy for any field
matching heat-shear initial data with nonzero constant streamwise drift. -/
theorem not_boundedKineticEnergy_of_matchesInitialVelocity_heatShearStreamwiseDriftInitialVelocity
    {u : NSVelocityField} {a k d : ℝ}
    (hd : d ≠ 0)
    (hinit : MatchesInitialVelocity (heatShearStreamwiseDriftInitialVelocity a k d) u) :
    ¬ boundedKineticEnergy u := by
  exact
    not_boundedKineticEnergy_of_not_integrable_kineticEnergyDensity_zero
      (u := u)
      (not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_heatShearStreamwiseDriftInitialVelocity
        (u := u) hd hinit)

/-- Heat-shear initial data with nonzero constant streamwise drift are not
finite-energy admissible on `ℝ^3`. -/
theorem not_finiteInitialKineticEnergy_heatShearStreamwiseDriftInitialVelocity
    {a k d : ℝ}
    (hd : d ≠ 0) :
    ¬ finiteInitialKineticEnergy (heatShearStreamwiseDriftInitialVelocity a k d) := by
  intro hE
  have hIntDrift :
      MeasureTheory.Integrable (heatShearStreamwiseDriftKineticEnergyDensity a k d) := by
    simpa [finiteInitialKineticEnergy,
      initialKineticEnergyDensity_heatShearStreamwiseDriftInitialVelocity a k d] using hE
  exact not_integrable_heatShearStreamwiseDriftKineticEnergyDensity (a := a) (k := k) hd hIntDrift

/-- The repaired structured whole-space input domain contains no problem datum
whose initial velocity is a heat-shear profile with nonzero constant
streamwise drift. -/
theorem not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_heatShearStreamwiseDriftInitialVelocity
    {a k d : ℝ}
    (hd : d ≠ 0) :
    ¬ Nonempty { P : FiniteEnergyAdmissibleNavierStokesProblemData //
        P.initialVelocity = heatShearStreamwiseDriftInitialVelocity a k d } := by
  exact
    not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearStreamwiseDriftInitialVelocity a k d)
      (not_finiteInitialKineticEnergy_heatShearStreamwiseDriftInitialVelocity hd)

end UniformVorticityContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
