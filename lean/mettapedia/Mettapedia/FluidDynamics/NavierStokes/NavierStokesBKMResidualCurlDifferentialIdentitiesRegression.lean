import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMResidualCurlDifferentialIdentities

/-!
# Regression checks for BKM residual-curl differential identities
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section BKMContinuation

theorem timeVelocityDerivativeField_differentiableAt_of_smooth_regression
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) (x : NSSpace) :
    DifferentiableAt ℝ (fun y : NSSpace => timeVelocityDerivativeField u t y) x := by
  exact timeVelocityDerivativeField_differentiableAt_of_smooth hu t x

theorem spatialConvectionField_differentiableAt_of_smooth_regression
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) (x : NSSpace) :
    DifferentiableAt ℝ (fun y : NSSpace => spatialConvectionField u t y) x := by
  exact spatialConvectionField_differentiableAt_of_smooth hu t x

theorem residualCurlLinearityDifferentiableAt_of_smooth_laplacian_regression
    {u : NSVelocityField} {t : NSTime} {x : NSSpace}
    (hu : smoothSpaceTimeVelocity u)
    (hlap : DifferentiableAt ℝ (fun y : NSSpace => spatialLaplacianField u t y) x) :
    residualCurlLinearityDifferentiableAt u t x := by
  exact residualCurlLinearityDifferentiableAt_of_smooth_laplacian hu hlap

theorem residualCurlLinearityDifferentiableOn_of_smooth_laplacian_regression
    {T : ℝ} {u : NSVelocityField}
    (hu : smoothSpaceTimeVelocity u)
    (hLap : residualCurlLinearityLaplacianDifferentiableOn u T) :
    residualCurlLinearityDifferentiableOn u T := by
  exact residualCurlLinearityDifferentiableOn_of_smooth_laplacian hu hLap

theorem residualCurlLinearityClosedOn_of_smooth_laplacian_regression
    {ν T : ℝ} {u : NSVelocityField}
    (hu : smoothSpaceTimeVelocity u)
    (hLap : residualCurlLinearityLaplacianDifferentiableOn u T) :
    residualCurlLinearityClosedOn ν u T := by
  exact residualCurlLinearityClosedOn_of_smooth_laplacian hu hLap

theorem residualCurlLinearityDefect_eq_zero_of_differentiableAt_regression
    {ν : ℝ} {u : NSVelocityField} {t : NSTime} {x : NSSpace}
    (hDiff : residualCurlLinearityDifferentiableAt u t x) :
    residualCurlLinearityDefect ν u t x = 0 := by
  exact residualCurlLinearityDefect_eq_zero_of_differentiableAt hDiff

theorem residualCurlLinearityClosedOn_of_differentiableOn_regression
    {ν T : ℝ} {u : NSVelocityField}
    (hDiff : residualCurlLinearityDifferentiableOn u T) :
    residualCurlLinearityClosedOn ν u T := by
  exact residualCurlLinearityClosedOn_of_differentiableOn hDiff

theorem residualCurlDifferentialIdentitiesClosedOn_of_linearityDifferentiableOn_regression
    {ν T : ℝ} {u : NSVelocityField}
    (hLin : residualCurlLinearityDifferentiableOn u T)
    (hTime : vorticityTimeCommutationClosedOn u T)
    (hLap : vorticityLaplacianCommutationClosedOn u T)
    (hConv : vorticityConvectionExpansionClosedOn u T) :
    residualCurlDifferentialIdentitiesClosedOn ν u T := by
  exact residualCurlDifferentialIdentitiesClosedOn_of_linearityDifferentiableOn
    hLin hTime hLap hConv

theorem residualCurlExpansionDefect_eq_differentialIdentityDefects_regression
    (ν : ℝ) (u : NSVelocityField) (t : NSTime) (x : NSSpace) :
    residualCurlExpansionDefect ν u t x =
      residualCurlLinearityDefect ν u t x +
        ν • vorticityLaplacianCommutationDefect u t x -
          vorticityTimeCommutationDefect u t x -
            vorticityConvectionExpansionDefect u t x := by
  exact residualCurlExpansionDefect_eq_differentialIdentityDefects ν u t x

theorem residualCurlExpansionClosedOn_of_differentialIdentitiesClosedOn_regression
    {ν T : ℝ} {u : NSVelocityField}
    (hIds : residualCurlDifferentialIdentitiesClosedOn ν u T) :
    residualCurlExpansionClosedOn ν u T := by
  exact residualCurlExpansionClosedOn_of_differentialIdentitiesClosedOn hIds

theorem BKMResidualCurlDifferentialIdentitiesClosed_implies_residualCurlExpansionDefectVanishes_regression
    (hIds : BKMResidualCurlDifferentialIdentitiesClosed) :
    BKMResidualCurlExpansionDefectVanishes := by
  exact hIds.implies_residualCurlExpansionDefectVanishes

theorem BKMAnalyticComponentsClosed_of_residualCurlDifferentialIdentities_regression
    (hIds : BKMResidualCurlDifferentialIdentitiesClosed)
    (hLog : BKMLogSobolevGradientControlFromEnvelope)
    (hHigh : BKMHighNormContinuationFromLogControl) :
    BKMAnalyticComponentsClosed := by
  exact BKMAnalyticComponentsClosed_of_residualCurlDifferentialIdentities hIds hLog hHigh

end BKMContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
