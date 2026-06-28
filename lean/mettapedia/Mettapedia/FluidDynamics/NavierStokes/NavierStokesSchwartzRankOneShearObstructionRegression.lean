import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzRankOneShearObstruction

/-!
# Regression checks for rank-one Schwartz shear obstruction
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace Regression

open scoped ContDiff LineDeriv SchwartzMap

theorem rankOne_convection_formula_regression
    (φ : NSSchwartzScalar) (v : NSSpace) (t : NSTime) (x : NSSpace) :
    spatialConvection
        (timeIndependentVelocity (rankOneSchwartzVelocity φ v : NSInitialVelocity)) t x =
      (φ x * fderiv ℝ (fun y : NSSpace => φ y) x v) • v := by
  exact spatialConvection_timeIndependent_rankOneSchwartzVelocity φ v t x

theorem rankOne_zero_convection_forces_zero_regression
    (φ : NSSchwartzScalar) {v : NSSpace} (hv : v ≠ 0) {t : NSTime}
    (hconv : ∀ x : NSSpace,
      spatialConvection
          (timeIndependentVelocity (rankOneSchwartzVelocity φ v : NSInitialVelocity)) t x =
        0) :
    (rankOneSchwartzVelocity φ v : NSInitialVelocity) = 0 := by
  exact rankOneSchwartzVelocity_eq_zero_of_spatialConvection_zero_at φ hv hconv

theorem rankOne_no_nonzero_zero_convection_regression
    {v : NSSpace} (hv : v ≠ 0) {t : NSTime} :
    ¬ ∃ φ : NSSchwartzScalar,
      (rankOneSchwartzVelocity φ v : NSInitialVelocity) ≠ 0 ∧
        ∀ x : NSSpace,
          spatialConvection
              (timeIndependentVelocity (rankOneSchwartzVelocity φ v : NSInitialVelocity))
              t x = 0 := by
  exact not_exists_nonzero_rankOneSchwartzVelocity_with_zero_spatialConvection hv

end Regression
end NavierStokes
end FluidDynamics
end Mettapedia
