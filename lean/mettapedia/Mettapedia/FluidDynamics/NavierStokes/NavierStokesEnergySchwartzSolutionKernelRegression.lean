import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergySchwartzSolutionKernel

/-!
# Regression checks for the nonzero slice-Schwartz energy kernel
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open MeasureTheory
open scoped ContDiff Laplacian RealInnerProductSpace LineDeriv SchwartzMap

namespace Regression

theorem nonzero_schwartz_solution_kernel_regression
    {ν : ℝ} (S : NonzeroSchwartzConcreteNavierStokesSolution ν) :
    (∃ t x, S.velocity t x ≠ 0) ∧
      SchwartzEnergyIdentityKernel ν S.velocity S.pressure := by
  exact S.nonzero_and_energyIdentityKernel

theorem schwartz_solution_momentum_closure_kernel_regression
    {ν : ℝ} (S : SchwartzConcreteNavierStokesSolution ν) :
    SchwartzMomentumClosureKernel ν S.velocity S.pressure := by
  exact S.momentumClosureKernel

theorem nonzero_schwartz_solution_concrete_kernel_regression
    {ν : ℝ} (S : NonzeroSchwartzConcreteNavierStokesSolution ν) :
    (∃ t x, S.velocity t x ≠ 0) ∧
      SchwartzConcreteSolutionKernel ν S.velocity S.pressure := by
  exact S.nonzero_and_concreteSolutionKernel

theorem stationary_inviscid_schwartz_pressure_slice_kernel_regression
    (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (q : 𝓢(NSSpace, ℝ))
    (hnonzero : ∃ x : NSSpace, u₀.1 x ≠ 0)
    (hstationary : ∀ t x,
      spatialConvection (timeIndependentVelocity (u₀.1 : NSInitialVelocity)) t x +
          spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) t x =
        0) :
    (∃ t x, timeIndependentVelocity (u₀.1 : NSInitialVelocity) t x ≠ 0) ∧
      SchwartzConcreteSolutionKernel 0
        (timeIndependentVelocity (u₀.1 : NSInitialVelocity))
        (fun _ : NSTime => fun y : NSSpace => q y) := by
  exact
    stationaryInviscidSchwartzPressureSlice_nonzero_concreteSolutionKernel
      u₀ q hnonzero hstationary

theorem stationary_inviscid_schwartz_pressure_slice_energy_canary_regression
    (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (q : 𝓢(NSSpace, ℝ))
    (hnonzero : ∃ x : NSSpace, u₀.1 x ≠ 0)
    (hstationary : ∀ t x,
      spatialConvection (timeIndependentVelocity (u₀.1 : NSInitialVelocity)) t x +
          spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) t x =
        0) :
    ∃ S : NonzeroSchwartzConcreteNavierStokesSolution 0,
      S.velocity = timeIndependentVelocity (u₀.1 : NSInitialVelocity) ∧
        S.pressure = (fun _ : NSTime => fun y : NSSpace => q y) ∧
        (∃ t x, S.velocity t x ≠ 0) ∧
        SchwartzEnergyIdentityKernel 0 S.velocity S.pressure ∧
        SchwartzConcreteSolutionKernel 0 S.velocity S.pressure ∧
        (∀ t, ∫ x, pressureEnergyPairing S.velocity S.pressure t x ∂volume = 0) ∧
        (∀ t, ∫ x, convectionEnergyPairing S.velocity t x ∂volume = 0) ∧
        CoordinateViscousEnergyPairingFormula S.velocity ∧
        (∀ t, HasDerivAt (normalizedKineticEnergy S.velocity) 0 t) ∧
        (∀ t,
          Integrable (kineticEnergyDensity S.velocity t) ∧
            HasDerivAt (normalizedKineticEnergy S.velocity) 0 t) := by
  exact
    stationaryInviscidSchwartzPressureSlice_nonzero_energyIdentityCanary_packet
      u₀ q hnonzero hstationary

theorem twoMode_nonzero_schwartz_pressure_slice_kernel_regression
    {a b : NSTime → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (f g : NSSchwartzInitialVelocity) (A B : ℝ)
    (q : NSTime → 𝓢(NSSpace, ℝ)) {ν : ℝ}
    (hp : smoothSpaceTimePressure (fun s : NSTime => fun y : NSSpace => q s y))
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (hnonzero : ∃ t x, twoModeSchwartzVelocity a b f g t x ≠ 0)
    (heq : ∀ t x,
      timeVelocityDerivative (twoModeSchwartzVelocity a b f g) t x +
          spatialConvection (twoModeSchwartzVelocity a b f g) t x +
          spatialPressureGradient (fun s : NSTime => fun y : NSSpace => q s y) t x =
        (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a b f g) t x) :
    (∃ t x, twoModeSchwartzVelocity a b f g t x ≠ 0) ∧
      SchwartzEnergyIdentityKernel ν
        (twoModeSchwartzVelocity a b f g)
        (fun s : NSTime => fun y : NSSpace => q s y) := by
  exact
    twoModeSchwartzPressureSlice_nonzero_energyIdentityKernel_of_momentumEquation
      ha hb f g A B q hp haBound hbBound hfDiv hgDiv hnonzero heq

end Regression

end NavierStokes
end FluidDynamics
end Mettapedia
