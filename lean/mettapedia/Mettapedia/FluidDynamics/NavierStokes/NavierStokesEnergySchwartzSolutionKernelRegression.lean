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
