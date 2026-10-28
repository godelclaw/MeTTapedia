import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergyZero

/-!
# Navier-Stokes Energy: ConstantCounterexamples

Constant-field counterexamples showing why finite-energy guards are mathematically necessary.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open MeasureTheory
open scoped ContDiff Laplacian RealInnerProductSpace LineDeriv SchwartzMap

/-- A nonzero constant velocity field is not spatially integrable on `ℝ^3`
with respect to the kinetic-energy density. This is the concrete obstruction
behind the vacuous energy identity phenomenon for unguarded `∫`-based
statements. -/
theorem not_integrable_kineticEnergyDensity_constantVelocityField_of_ne_zero
    {c : NSSpace} (hc : c ≠ 0) (t : NSTime) :
    ¬ MeasureTheory.Integrable (kineticEnergyDensity (constantVelocityField c) t) := by
  have hconst : (‖c‖ ^ (2 : ℕ) : ℝ) ≠ 0 := by
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hc)
  have hnotfinite :
      ¬ MeasureTheory.IsFiniteMeasure (MeasureTheory.volume : MeasureTheory.Measure NSSpace) := by
    rw [MeasureTheory.not_isFiniteMeasure_iff]
    exact MeasureTheory.measure_univ_of_isAddLeftInvariant
      (μ := (MeasureTheory.volume : MeasureTheory.Measure NSSpace))
  intro hInt
  have hfinite :
      MeasureTheory.IsFiniteMeasure (MeasureTheory.volume : MeasureTheory.Measure NSSpace) := by
    have hEq :
        kineticEnergyDensity (constantVelocityField c) t = fun _ : NSSpace => ‖c‖ ^ (2 : ℕ) := by
      funext x
      simp [kineticEnergyDensity, constantVelocityField]
    rw [hEq] at hInt
    exact (MeasureTheory.integrable_const_iff_isFiniteMeasure hconst).mp hInt
  exact hnotfinite hfinite

/-- The concrete spatial kinetic energy of a constant velocity field collapses
to `0` because the integral is undefined on nonintegrable nonzero slices and
therefore evaluates to `0` in mathlib's Bochner integral. -/
theorem kineticEnergyAt_constantVelocityField
    (c : NSSpace) :
    kineticEnergyAt (constantVelocityField c) = fun _ : NSTime => 0 := by
  funext t
  by_cases hc : c = 0
  · subst hc
    simp [kineticEnergyAt, kineticEnergyDensity, constantVelocityField]
  · rw [kineticEnergyAt]
    exact MeasureTheory.integral_undef
      (not_integrable_kineticEnergyDensity_constantVelocityField_of_ne_zero hc t)

/-- The normalized kinetic energy of any constant velocity field is identically
zero on the current unguarded concrete NS surface. -/
theorem normalizedKineticEnergy_constantVelocityField
    (c : NSSpace) :
    normalizedKineticEnergy (constantVelocityField c) = fun _ : NSTime => 0 := by
  funext t
  rw [normalizedKineticEnergy, kineticEnergyAt_constantVelocityField]
  simp

/-- The coordinatewise enstrophy density of a constant velocity field is zero on
every time slice. -/
theorem coordinateEnstrophyDensity_constantVelocityField_zero
    (c : NSSpace) (t : NSTime) :
    coordinateEnstrophyDensity (constantVelocityField c) t = fun _ : NSSpace => 0 := by
  funext x
  simp [coordinateEnstrophyDensity, spatialFDeriv_constantVelocityField]

/-- Constant velocity fields have zero total coordinatewise enstrophy. -/
theorem coordinateEnstrophyAt_constantVelocityField_zero
    (c : NSSpace) :
    coordinateEnstrophyAt (constantVelocityField c) = fun _ : NSTime => 0 := by
  funext t
  rw [coordinateEnstrophyAt, coordinateEnstrophyDensity_constantVelocityField_zero]
  simp

/-- Constant velocity fields have zero corrected dissipation rate. -/
theorem coordinateEnergyDissipationRate_constantVelocityField_zero
    (c : NSSpace) (ν : ℝ) :
    coordinateEnergyDissipationRate (constantVelocityField c) ν = fun _ : NSTime => 0 := by
  funext t
  rw [coordinateEnergyDissipationRate, coordinateEnstrophyAt_constantVelocityField_zero]
  simp

/-- The time energy pairing of a constant velocity field vanishes. -/
theorem timeEnergyPairing_constantVelocityField_zero
    (c : NSSpace) (t : NSTime) :
    timeEnergyPairing (constantVelocityField c) t = fun _ : NSSpace => 0 := by
  funext x
  simp [timeEnergyPairing, timeVelocityDerivative_constantVelocityField]

/-- The convection energy pairing of a constant velocity field vanishes. -/
theorem convectionEnergyPairing_constantVelocityField_zero
    (c : NSSpace) (t : NSTime) :
    convectionEnergyPairing (constantVelocityField c) t = fun _ : NSSpace => 0 := by
  funext x
  simp [convectionEnergyPairing, spatialConvection_constantVelocityField]

/-- The pressure energy pairing of a constant velocity field against zero
pressure vanishes. -/
theorem pressureEnergyPairing_constantVelocityField_zeroPressure
    (c : NSSpace) (t : NSTime) :
    pressureEnergyPairing (constantVelocityField c) (0 : NSPressureField) t =
      fun _ : NSSpace => 0 := by
  funext x
  simp [pressureEnergyPairing, spatialPressureGradient_zero]

/-- The viscous energy pairing of a constant velocity field vanishes. -/
theorem laplacianEnergyPairing_constantVelocityField_zero
    (c : NSSpace) (t : NSTime) :
    laplacianEnergyPairing (constantVelocityField c) t = fun _ : NSSpace => 0 := by
  funext x
  simp [laplacianEnergyPairing, spatialLaplacian_constantVelocityField]

/-- The derivative-under-the-integral seam holds for constant velocity fields,
but only because the unguarded kinetic-energy integral itself collapses to
zero. -/
theorem EnergyDerivativeFormula_constantVelocityField
    (c : NSSpace) :
    EnergyDerivativeFormula (constantVelocityField c) := by
  intro t
  rw [normalizedKineticEnergy_constantVelocityField]
  have hPairIntegral :
      ∫ x, timeEnergyPairing (constantVelocityField c) t x ∂volume = 0 := by
    rw [timeEnergyPairing_constantVelocityField_zero]
    simp
  rw [hPairIntegral]
  simpa using (hasDerivAt_const t (0 : ℝ))

/-- The corrected viscous pairing seam holds for constant velocity fields. -/
theorem CoordinateViscousEnergyPairingFormula_constantVelocityField
    (c : NSSpace) :
    CoordinateViscousEnergyPairingFormula (constantVelocityField c) := by
  intro t
  rw [laplacianEnergyPairing_constantVelocityField_zero,
    coordinateEnstrophyAt_constantVelocityField_zero]
  simp

/-- All three space pairings are integrable for a constant velocity field with
zero pressure because each pairing vanishes identically. -/
theorem EnergyPairingIntegrable_constantVelocityField_zeroPressure
    (c : NSSpace) :
    EnergyPairingIntegrable (constantVelocityField c) (0 : NSPressureField) := by
  intro t
  constructor
  · rw [laplacianEnergyPairing_constantVelocityField_zero]
    exact integrable_zero NSSpace ℝ (volume : Measure NSSpace)
  constructor
  · rw [convectionEnergyPairing_constantVelocityField_zero]
    exact integrable_zero NSSpace ℝ (volume : Measure NSSpace)
  · rw [pressureEnergyPairing_constantVelocityField_zeroPressure]
    exact integrable_zero NSSpace ℝ (volume : Measure NSSpace)

/-- Every constant velocity field satisfies the current corrected energy
identity surface, even when the spatial kinetic energy is not integrable. -/
theorem coordinateEnergyDissipationIdentity_smooth_constantVelocityField
    (ν : ℝ) (c : NSSpace) :
    ∀ t,
      HasDerivAt (normalizedKineticEnergy (constantVelocityField c))
        (-(coordinateEnergyDissipationRate (constantVelocityField c) ν t)) t := by
  exact
    coordinateEnergyDissipationIdentity_smooth
      (u := constantVelocityField c)
      (p := (0 : NSPressureField))
      (ν := ν)
      (EnergyDerivativeFormula_constantVelocityField c)
      (fun t x => momentumEquation_constantVelocityField_zeroPressure ν c t x)
      (EnergyPairingIntegrable_constantVelocityField_zeroPressure c)
      (CoordinateViscousEnergyPairingFormula_constantVelocityField c)
      (by
        intro t
        rw [pressureEnergyPairing_constantVelocityField_zeroPressure]
        simp)
      (by
        intro t
        rw [convectionEnergyPairing_constantVelocityField_zero]
        simp)

/-- A nonzero constant velocity field still fails the bounded-energy predicate,
so the current unguarded energy identity surface is underpowered as a
finite-energy theorem target. -/
theorem not_boundedKineticEnergy_constantVelocityField_of_ne_zero
    {c : NSSpace} (hc : c ≠ 0) :
    ¬ boundedKineticEnergy (constantVelocityField c) := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact not_integrable_kineticEnergyDensity_constantVelocityField_of_ne_zero hc 0 (hbound 0).1

/-- Checked obstruction: the current coordinatewise energy identity does not by
itself encode finite-energy control, because a nonzero constant velocity field
satisfies the identity while failing `boundedKineticEnergy`. -/
theorem exists_nonzero_constantVelocityField_coordinateEnergyIdentity_without_boundedEnergy
    (ν : ℝ) :
    ∃ c : NSSpace,
      c ≠ 0 ∧
      (∀ t,
        HasDerivAt (normalizedKineticEnergy (constantVelocityField c))
          (-(coordinateEnergyDissipationRate (constantVelocityField c) ν t)) t) ∧
      ¬ boundedKineticEnergy (constantVelocityField c) := by
  let c : NSSpace := EuclideanSpace.single nsCoord0 (1 : ℝ)
  have hc : c ≠ 0 := by
    intro hzero
    have hcoord := congrArg (fun v : NSSpace => v nsCoord0) hzero
    simp [c, nsCoord0] at hcoord
  refine ⟨c, hc, coordinateEnergyDissipationIdentity_smooth_constantVelocityField ν c, ?_⟩
  exact not_boundedKineticEnergy_constantVelocityField_of_ne_zero hc
end NavierStokes
end FluidDynamics
end Mettapedia
