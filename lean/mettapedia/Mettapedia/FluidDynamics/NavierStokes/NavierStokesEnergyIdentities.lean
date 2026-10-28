import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergyInterfaces

/-!
# Navier-Stokes Energy: Identities

Abstract energy-dissipation identity reductions and finite-energy guarded consequences.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open MeasureTheory
open scoped ContDiff Laplacian RealInnerProductSpace LineDeriv SchwartzMap

/-- Honest energy-identity reduction for smooth Navier-Stokes: once the two
analytic seams are supplied as explicit hypotheses, the concrete momentum
equation implies the dissipation law

`d/dt ((1/2) ∫ |u|²) = -ν ∫ ‖∇u‖²`.

This theorem proves the PDE-to-energy algebra directly on the current concrete
`ℝ × ℝ^3` surface and isolates the exact remaining analytic obligations rather
than hiding them behind placeholders. -/
theorem energyDissipationIdentity_smooth
    (u : NSVelocityField) (p : NSPressureField) (ν : ℝ)
    (hderiv : EnergyDerivativeFormula u)
    (heq : ∀ t x,
      timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
        (ν : ℝ) • spatialLaplacian u t x)
    (hintegrable : EnergyPairingIntegrable u p)
    (hviscous : ViscousEnergyPairingFormula u)
    (hboundary : ∀ t, ∫ x, pressureEnergyPairing u p t x ∂volume = 0)
    (hnonlinear : ∀ t, ∫ x, convectionEnergyPairing u t x ∂volume = 0) :
    ∀ t, HasDerivAt (normalizedKineticEnergy u) (-(energyDissipationRate u ν t)) t := by
  intro t
  let viscousContribution : NSSpace → ℝ :=
    fun x => ⟪u t x, (ν : ℝ) • spatialLaplacian u t x⟫
  have hIntL : Integrable (laplacianEnergyPairing u t) := (hintegrable t).1
  have hIntN : Integrable (convectionEnergyPairing u t) := (hintegrable t).2.1
  have hIntP : Integrable (pressureEnergyPairing u p t) := (hintegrable t).2.2
  have hViscousContribution :
      viscousContribution = fun x => (ν : ℝ) * laplacianEnergyPairing u t x := by
    funext x
    simpa [viscousContribution, laplacianEnergyPairing] using
      (real_inner_smul_right (u t x) (spatialLaplacian u t x) (ν : ℝ))
  have hIntViscous : Integrable viscousContribution := by
    rw [hViscousContribution]
    exact hIntL.const_mul ν
  have hPointwise :
      timeEnergyPairing u t =
        viscousContribution - convectionEnergyPairing u t - pressureEnergyPairing u p t := by
    funext x
    have hInnerEq :
        ⟪u t x, timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x⟫ =
          ⟪u t x, (ν : ℝ) • spatialLaplacian u t x⟫ := by
      exact congrArg (fun v : NSSpace => ⟪u t x, v⟫) (heq t x)
    have hExpanded :
        ⟪u t x, timeVelocityDerivative u t x⟫ +
            ⟪u t x, spatialConvection u t x⟫ +
              ⟪u t x, spatialPressureGradient p t x⟫ =
          ⟪u t x, (ν : ℝ) • spatialLaplacian u t x⟫ := by
      simpa [inner_add_right, add_assoc] using hInnerEq
    calc
      timeEnergyPairing u t x
          = ⟪u t x, timeVelocityDerivative u t x⟫ := by rfl
      _ = ⟪u t x, (ν : ℝ) • spatialLaplacian u t x⟫ -
            ⟪u t x, spatialConvection u t x⟫ -
              ⟪u t x, spatialPressureGradient p t x⟫ := by
            linarith
      _ = viscousContribution x - convectionEnergyPairing u t x - pressureEnergyPairing u p t x := by
            rfl
  have hMomentumIntegral :
      ∫ x, timeEnergyPairing u t x ∂volume =
        ∫ x, viscousContribution x ∂volume -
          ∫ x, convectionEnergyPairing u t x ∂volume -
            ∫ x, pressureEnergyPairing u p t x ∂volume := by
    rw [hPointwise]
    have hOuter :
        ∫ x, ((viscousContribution - convectionEnergyPairing u t) - pressureEnergyPairing u p t) x ∂volume =
          ∫ x, (viscousContribution - convectionEnergyPairing u t) x ∂volume -
            ∫ x, pressureEnergyPairing u p t x ∂volume := by
      simpa [Pi.sub_apply] using integral_sub (hIntViscous.sub hIntN) hIntP
    have hInner :
        ∫ x, (viscousContribution - convectionEnergyPairing u t) x ∂volume =
          ∫ x, viscousContribution x ∂volume - ∫ x, convectionEnergyPairing u t x ∂volume := by
      simpa [Pi.sub_apply] using integral_sub hIntViscous hIntN
    rw [hOuter, hInner]
  have hViscousIntegral :
      ∫ x, viscousContribution x ∂volume =
        (ν : ℝ) * ∫ x, laplacianEnergyPairing u t x ∂volume := by
    rw [hViscousContribution]
    simpa using integral_const_mul (ν : ℝ) (fun x => laplacianEnergyPairing u t x)
  have hEnergySlope :
      ∫ x, timeEnergyPairing u t x ∂volume = -(energyDissipationRate u ν t) := by
    calc
      ∫ x, timeEnergyPairing u t x ∂volume
          = ∫ x, viscousContribution x ∂volume -
              ∫ x, convectionEnergyPairing u t x ∂volume -
                ∫ x, pressureEnergyPairing u p t x ∂volume := hMomentumIntegral
      _ = (ν : ℝ) * ∫ x, laplacianEnergyPairing u t x ∂volume -
            ∫ x, convectionEnergyPairing u t x ∂volume -
              ∫ x, pressureEnergyPairing u p t x ∂volume := by
            rw [hViscousIntegral]
      _ = (ν : ℝ) * ∫ x, laplacianEnergyPairing u t x ∂volume - 0 - 0 := by
            rw [hnonlinear t, hboundary t]
      _ = (ν : ℝ) * ∫ x, laplacianEnergyPairing u t x ∂volume := by ring
      _ = (ν : ℝ) * (-enstrophyAt u t) := by rw [hviscous t]
      _ = -(energyDissipationRate u ν t) := by
            unfold energyDissipationRate
            ring
  have hd := hderiv t
  rw [hEnergySlope] at hd
  exact hd

/-- Honest corrected energy-identity reduction for smooth Navier-Stokes: once
the derivative-under-the-integral seam and the coordinatewise viscous pairing
formula are supplied, the concrete momentum equation implies the corrected
dissipation law

`d/dt ((1/2) ∫ |u|²) = -ν ∫ Σᵢ |∂ᵢu|²`. -/
theorem coordinateEnergyDissipationIdentity_smooth
    (u : NSVelocityField) (p : NSPressureField) (ν : ℝ)
    (hderiv : EnergyDerivativeFormula u)
    (heq : ∀ t x,
      timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
        (ν : ℝ) • spatialLaplacian u t x)
    (hintegrable : EnergyPairingIntegrable u p)
    (hviscous : CoordinateViscousEnergyPairingFormula u)
    (hboundary : ∀ t, ∫ x, pressureEnergyPairing u p t x ∂volume = 0)
    (hnonlinear : ∀ t, ∫ x, convectionEnergyPairing u t x ∂volume = 0) :
    ∀ t, HasDerivAt (normalizedKineticEnergy u)
      (-(coordinateEnergyDissipationRate u ν t)) t := by
  intro t
  let viscousContribution : NSSpace → ℝ :=
    fun x => ⟪u t x, (ν : ℝ) • spatialLaplacian u t x⟫
  have hIntL : Integrable (laplacianEnergyPairing u t) := (hintegrable t).1
  have hIntN : Integrable (convectionEnergyPairing u t) := (hintegrable t).2.1
  have hIntP : Integrable (pressureEnergyPairing u p t) := (hintegrable t).2.2
  have hViscousContribution :
      viscousContribution = fun x => (ν : ℝ) * laplacianEnergyPairing u t x := by
    funext x
    simpa [viscousContribution, laplacianEnergyPairing] using
      (real_inner_smul_right (u t x) (spatialLaplacian u t x) (ν : ℝ))
  have hIntViscous : Integrable viscousContribution := by
    rw [hViscousContribution]
    exact hIntL.const_mul ν
  have hPointwise :
      timeEnergyPairing u t =
        viscousContribution - convectionEnergyPairing u t - pressureEnergyPairing u p t := by
    funext x
    have hInnerEq :
        ⟪u t x, timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x⟫ =
          ⟪u t x, (ν : ℝ) • spatialLaplacian u t x⟫ := by
      exact congrArg (fun v : NSSpace => ⟪u t x, v⟫) (heq t x)
    have hExpanded :
        ⟪u t x, timeVelocityDerivative u t x⟫ +
            ⟪u t x, spatialConvection u t x⟫ +
              ⟪u t x, spatialPressureGradient p t x⟫ =
          ⟪u t x, (ν : ℝ) • spatialLaplacian u t x⟫ := by
      simpa [inner_add_right, add_assoc] using hInnerEq
    calc
      timeEnergyPairing u t x
          = ⟪u t x, timeVelocityDerivative u t x⟫ := by rfl
      _ = ⟪u t x, (ν : ℝ) • spatialLaplacian u t x⟫ -
            ⟪u t x, spatialConvection u t x⟫ -
              ⟪u t x, spatialPressureGradient p t x⟫ := by
            linarith
      _ = viscousContribution x - convectionEnergyPairing u t x - pressureEnergyPairing u p t x := by
            rfl
  have hMomentumIntegral :
      ∫ x, timeEnergyPairing u t x ∂volume =
        ∫ x, viscousContribution x ∂volume -
          ∫ x, convectionEnergyPairing u t x ∂volume -
            ∫ x, pressureEnergyPairing u p t x ∂volume := by
    rw [hPointwise]
    have hOuter :
        ∫ x, ((viscousContribution - convectionEnergyPairing u t) - pressureEnergyPairing u p t) x ∂volume =
          ∫ x, (viscousContribution - convectionEnergyPairing u t) x ∂volume -
            ∫ x, pressureEnergyPairing u p t x ∂volume := by
      simpa [Pi.sub_apply] using integral_sub (hIntViscous.sub hIntN) hIntP
    have hInner :
        ∫ x, (viscousContribution - convectionEnergyPairing u t) x ∂volume =
          ∫ x, viscousContribution x ∂volume - ∫ x, convectionEnergyPairing u t x ∂volume := by
      simpa [Pi.sub_apply] using integral_sub hIntViscous hIntN
    rw [hOuter, hInner]
  have hViscousIntegral :
      ∫ x, viscousContribution x ∂volume =
        (ν : ℝ) * ∫ x, laplacianEnergyPairing u t x ∂volume := by
    rw [hViscousContribution]
    simpa using integral_const_mul (ν : ℝ) (fun x => laplacianEnergyPairing u t x)
  have hEnergySlope :
      ∫ x, timeEnergyPairing u t x ∂volume = -(coordinateEnergyDissipationRate u ν t) := by
    calc
      ∫ x, timeEnergyPairing u t x ∂volume
          = ∫ x, viscousContribution x ∂volume -
              ∫ x, convectionEnergyPairing u t x ∂volume -
                ∫ x, pressureEnergyPairing u p t x ∂volume := hMomentumIntegral
      _ = (ν : ℝ) * ∫ x, laplacianEnergyPairing u t x ∂volume -
            ∫ x, convectionEnergyPairing u t x ∂volume -
              ∫ x, pressureEnergyPairing u p t x ∂volume := by
            rw [hViscousIntegral]
      _ = (ν : ℝ) * ∫ x, laplacianEnergyPairing u t x ∂volume - 0 - 0 := by
            rw [hnonlinear t, hboundary t]
      _ = (ν : ℝ) * ∫ x, laplacianEnergyPairing u t x ∂volume := by ring
      _ = (ν : ℝ) * (-coordinateEnstrophyAt u t) := by rw [hviscous t]
      _ = -(coordinateEnergyDissipationRate u ν t) := by
            unfold coordinateEnergyDissipationRate
            ring
  have hd := hderiv t
  rw [hEnergySlope] at hd
  exact hd

/-- The corrected coordinatewise energy identity gives monotone decay of the
normalized kinetic energy whenever the viscosity is nonnegative.  This is the
calculus bridge from the exact dissipation identity to the energy-inequality
shape. -/
theorem coordinateEnergyDissipationIdentity_smooth_antitone_normalizedKineticEnergy
    (u : NSVelocityField) (p : NSPressureField) {ν : ℝ}
    (hν : 0 ≤ ν)
    (hderiv : EnergyDerivativeFormula u)
    (heq : ∀ t x,
      timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
        (ν : ℝ) • spatialLaplacian u t x)
    (hintegrable : EnergyPairingIntegrable u p)
    (hviscous : CoordinateViscousEnergyPairingFormula u)
    (hboundary : ∀ t, ∫ x, pressureEnergyPairing u p t x ∂volume = 0)
    (hnonlinear : ∀ t, ∫ x, convectionEnergyPairing u t x ∂volume = 0) :
    Antitone (normalizedKineticEnergy u) := by
  refine
    antitone_of_hasDerivAt_nonpos
      (f' := fun t => -(coordinateEnergyDissipationRate u ν t))
      ?_ ?_
  · exact
      coordinateEnergyDissipationIdentity_smooth
        (u := u)
        (p := p)
        (ν := ν)
        hderiv
        heq
        hintegrable
        hviscous
        hboundary
        hnonlinear
  · intro t
    exact neg_coordinateEnergyDissipationRate_nonpos u hν t

/-- Two-time energy inequality extracted from the corrected coordinatewise
energy identity: later normalized kinetic energy is bounded by earlier
normalized kinetic energy. -/
theorem coordinateEnergyDissipationIdentity_smooth_normalizedKineticEnergy_le_of_le
    (u : NSVelocityField) (p : NSPressureField) {ν : ℝ}
    (hν : 0 ≤ ν)
    (hderiv : EnergyDerivativeFormula u)
    (heq : ∀ t x,
      timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
        (ν : ℝ) • spatialLaplacian u t x)
    (hintegrable : EnergyPairingIntegrable u p)
    (hviscous : CoordinateViscousEnergyPairingFormula u)
    (hboundary : ∀ t, ∫ x, pressureEnergyPairing u p t x ∂volume = 0)
    (hnonlinear : ∀ t, ∫ x, convectionEnergyPairing u t x ∂volume = 0)
    {t₀ t₁ : NSTime} (ht : t₀ ≤ t₁) :
    normalizedKineticEnergy u t₁ ≤ normalizedKineticEnergy u t₀ := by
  exact
    (coordinateEnergyDissipationIdentity_smooth_antitone_normalizedKineticEnergy
      (u := u)
      (p := p)
      (ν := ν)
      hν
      hderiv
      heq
      hintegrable
      hviscous
      hboundary
      hnonlinear) ht

/-- The corrected coordinatewise energy identity places every later normalized
kinetic energy between zero and its earlier value. -/
theorem coordinateEnergyDissipationIdentity_smooth_normalizedKineticEnergy_between_zero_and_initial
    (u : NSVelocityField) (p : NSPressureField) {ν : ℝ}
    (hν : 0 ≤ ν)
    (hderiv : EnergyDerivativeFormula u)
    (heq : ∀ t x,
      timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
        (ν : ℝ) • spatialLaplacian u t x)
    (hintegrable : EnergyPairingIntegrable u p)
    (hviscous : CoordinateViscousEnergyPairingFormula u)
    (hboundary : ∀ t, ∫ x, pressureEnergyPairing u p t x ∂volume = 0)
    (hnonlinear : ∀ t, ∫ x, convectionEnergyPairing u t x ∂volume = 0)
    {t₀ t₁ : NSTime} (ht : t₀ ≤ t₁) :
    0 ≤ normalizedKineticEnergy u t₁ ∧
      normalizedKineticEnergy u t₁ ≤ normalizedKineticEnergy u t₀ := by
  exact
    ⟨normalizedKineticEnergy_nonneg u t₁,
      coordinateEnergyDissipationIdentity_smooth_normalizedKineticEnergy_le_of_le
        (u := u)
        (p := p)
        (ν := ν)
        hν
        hderiv
        heq
        hintegrable
        hviscous
        hboundary
        hnonlinear
        ht⟩

/-- Standard kinetic-energy form of the corrected two-time energy inequality:
the unnormalized spatial kinetic energy at a later time is bounded by the
earlier one. -/
theorem coordinateEnergyDissipationIdentity_smooth_kineticEnergyAt_le_of_le
    (u : NSVelocityField) (p : NSPressureField) {ν : ℝ}
    (hν : 0 ≤ ν)
    (hderiv : EnergyDerivativeFormula u)
    (heq : ∀ t x,
      timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
        (ν : ℝ) • spatialLaplacian u t x)
    (hintegrable : EnergyPairingIntegrable u p)
    (hviscous : CoordinateViscousEnergyPairingFormula u)
    (hboundary : ∀ t, ∫ x, pressureEnergyPairing u p t x ∂volume = 0)
    (hnonlinear : ∀ t, ∫ x, convectionEnergyPairing u t x ∂volume = 0)
    {t₀ t₁ : NSTime} (ht : t₀ ≤ t₁) :
    kineticEnergyAt u t₁ ≤ kineticEnergyAt u t₀ := by
  have hnorm :
      normalizedKineticEnergy u t₁ ≤ normalizedKineticEnergy u t₀ :=
    coordinateEnergyDissipationIdentity_smooth_normalizedKineticEnergy_le_of_le
      (u := u)
      (p := p)
      (ν := ν)
      hν
      hderiv
      heq
      hintegrable
      hviscous
      hboundary
      hnonlinear
      ht
  unfold normalizedKineticEnergy at hnorm
  nlinarith

/-- Standard kinetic-energy estimate extracted from the corrected coordinatewise
energy identity: later kinetic energy lies between zero and the earlier kinetic
energy. -/
theorem coordinateEnergyDissipationIdentity_smooth_kineticEnergyAt_between_zero_and_initial
    (u : NSVelocityField) (p : NSPressureField) {ν : ℝ}
    (hν : 0 ≤ ν)
    (hderiv : EnergyDerivativeFormula u)
    (heq : ∀ t x,
      timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
        (ν : ℝ) • spatialLaplacian u t x)
    (hintegrable : EnergyPairingIntegrable u p)
    (hviscous : CoordinateViscousEnergyPairingFormula u)
    (hboundary : ∀ t, ∫ x, pressureEnergyPairing u p t x ∂volume = 0)
    (hnonlinear : ∀ t, ∫ x, convectionEnergyPairing u t x ∂volume = 0)
    {t₀ t₁ : NSTime} (ht : t₀ ≤ t₁) :
    0 ≤ kineticEnergyAt u t₁ ∧
      kineticEnergyAt u t₁ ≤ kineticEnergyAt u t₀ := by
  exact
    ⟨kineticEnergyAt_nonneg u t₁,
      coordinateEnergyDissipationIdentity_smooth_kineticEnergyAt_le_of_le
        (u := u)
        (p := p)
        (ν := ν)
        hν
        hderiv
        heq
        hintegrable
        hviscous
        hboundary
        hnonlinear
        ht⟩

/-- Repaired coordinatewise energy identity on the concrete finite-energy
surface: if the velocity field already satisfies the global bounded-energy
predicate used elsewhere in the concrete NS route, then every time slice has
honest integrable kinetic-energy density and the corrected dissipation identity
holds on that meaningful domain. -/
theorem meaningfulCoordinateEnergyDissipationIdentity_smooth_of_boundedKineticEnergy
    (u : NSVelocityField) (p : NSPressureField) (ν : ℝ)
    (henergy : boundedKineticEnergy u)
    (hderiv : EnergyDerivativeFormula u)
    (heq : ∀ t x,
      timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
        (ν : ℝ) • spatialLaplacian u t x)
    (hintegrable : EnergyPairingIntegrable u p)
    (hviscous : CoordinateViscousEnergyPairingFormula u)
    (hboundary : ∀ t, ∫ x, pressureEnergyPairing u p t x ∂volume = 0)
    (hnonlinear : ∀ t, ∫ x, convectionEnergyPairing u t x ∂volume = 0) :
    ∀ t,
      MeasureTheory.Integrable (kineticEnergyDensity u t) ∧
        HasDerivAt (normalizedKineticEnergy u)
          (-(coordinateEnergyDissipationRate u ν t)) t := by
  rcases henergy with ⟨C, hC, hbound⟩
  intro t
  refine ⟨(hbound t).1, ?_⟩
  exact
    coordinateEnergyDissipationIdentity_smooth
      (u := u)
      (p := p)
      (ν := ν)
      hderiv
      heq
      hintegrable
      hviscous
      hboundary
      hnonlinear
      t
end NavierStokes
end FluidDynamics
end Mettapedia
