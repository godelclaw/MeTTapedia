import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzLocalizedStreamFunction

/-!
# Regression checks for localized Schwartz stream-function data
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace Regression

open scoped LineDeriv SchwartzMap

theorem localizedStream_initialDivergence_regression
    (φ : NSSchwartzScalar) (x : NSSpace) :
    initialSpatialDivergence (streamFunctionVelocity φ : NSInitialVelocity) x = 0 := by
  exact initialSpatialDivergence_streamFunctionVelocity φ x

theorem localizedStream_concrete_nonzero_regression :
    ∃ x : NSSpace, nsLocalizedStreamDivergenceFreeInitialVelocity.1 x ≠ 0 := by
  exact nsLocalizedStreamDivergenceFreeInitialVelocity_nonzero

theorem localizedStream_origin_value_regression :
    streamFunctionVelocity nsLocalizedStreamFunction (0 : NSSpace) =
      EuclideanSpace.single nsCoord0 (1 : ℝ) := by
  exact nsLocalizedStreamVelocity_value_origin

end Regression
end NavierStokes
end FluidDynamics
end Mettapedia
