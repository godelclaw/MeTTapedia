import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMResidualCurlDifferentialIdentities

/-!
# Regression checks for BKM residual-curl differential identities
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open MeasureTheory
open scoped ContDiff
open scoped Laplacian

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

theorem spatialLaplacianField_differentiableAt_of_smooth_regression
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) (x : NSSpace) :
    DifferentiableAt ℝ (fun y : NSSpace => spatialLaplacianField u t y) x := by
  exact spatialLaplacianField_differentiableAt_of_smooth hu t x

theorem smoothSpaceTimeVelocity_isSymmSndFDerivAt_regression
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (tx : NSSpacetime) :
    IsSymmSndFDerivAt ℝ (spaceTimeVelocityMap u) tx := by
  exact smoothSpaceTimeVelocity_isSymmSndFDerivAt hu tx

theorem smoothSpaceTimeVelocity_fderiv_fderiv_swap_regression
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (tx v w : NSSpacetime) :
    ((fderiv ℝ (fderiv ℝ (spaceTimeVelocityMap u)) tx) v) w =
      ((fderiv ℝ (fderiv ℝ (spaceTimeVelocityMap u)) tx) w) v := by
  exact smoothSpaceTimeVelocity_fderiv_fderiv_swap hu tx v w

theorem spatialDerivativeComponent_contDiff_time_of_smooth_regression
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (x : NSSpace) (coord comp : Fin 3) :
    ContDiff ℝ ∞ (fun s : NSTime => spatialDerivativeComponent u s x coord comp) := by
  exact spatialDerivativeComponent_contDiff_time_of_smooth hu x coord comp

theorem spatialDerivativeComponent_differentiableAt_time_of_smooth_regression
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) (x : NSSpace) (coord comp : Fin 3) :
    DifferentiableAt ℝ (fun s : NSTime => spatialDerivativeComponent u s x coord comp) t := by
  exact spatialDerivativeComponent_differentiableAt_time_of_smooth hu t x coord comp

theorem spatialDerivativeComponent_contDiff_spacetime_of_smooth_regression
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (coord comp : Fin 3) :
    ContDiff ℝ ∞
      (fun tx : NSSpacetime => spatialDerivativeComponent u tx.1 tx.2 coord comp) := by
  exact spatialDerivativeComponent_contDiff_spacetime_of_smooth hu coord comp

theorem spatialVorticity_smoothSpaceTimeVelocity_of_smooth_regression
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u) :
    smoothSpaceTimeVelocity (fun t x => spatialVorticity u t x) := by
  exact spatialVorticity_smoothSpaceTimeVelocity_of_smooth hu

theorem timeVelocityDerivativeField_smoothSpaceTimeVelocity_of_smooth_regression
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u) :
    smoothSpaceTimeVelocity (timeVelocityDerivativeField u) := by
  exact timeVelocityDerivativeField_smoothSpaceTimeVelocity_of_smooth hu

theorem timeVorticityDerivative_smoothSpaceTimeVelocity_of_smooth_regression
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u) :
    smoothSpaceTimeVelocity (fun t x => timeVorticityDerivative u t x) := by
  exact timeVorticityDerivative_smoothSpaceTimeVelocity_of_smooth hu

theorem spatialVorticity_timeVelocityDerivativeField_smoothSpaceTimeVelocity_of_smooth_regression
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u) :
    smoothSpaceTimeVelocity (fun t x => spatialVorticity (timeVelocityDerivativeField u) t x) := by
  exact spatialVorticity_timeVelocityDerivativeField_smoothSpaceTimeVelocity_of_smooth hu

theorem fderiv_prodMk_right_const_eq_inr_regression
    (t : NSTime) (x : NSSpace) :
    fderiv ℝ (fun y : NSSpace => (t, y)) x =
      ContinuousLinearMap.inr ℝ NSTime NSSpace := by
  exact fderiv_prodMk_right_const_eq_inr t x

theorem fderiv_prodMk_left_const_eq_inl_regression
    (t : NSTime) (x : NSSpace) :
    fderiv ℝ (fun s : NSTime => (s, x)) t =
      ContinuousLinearMap.inl ℝ NSTime NSSpace := by
  exact fderiv_prodMk_left_const_eq_inl t x

theorem spatialSlice_fderiv_eq_spaceTime_fderiv_inr_of_smooth_regression
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) (x : NSSpace) :
    fderiv ℝ (fun y : NSSpace => u t y) x =
      (fderiv ℝ (spaceTimeVelocityMap u) (t, x)).comp
        (ContinuousLinearMap.inr ℝ NSTime NSSpace) := by
  exact spatialSlice_fderiv_eq_spaceTime_fderiv_inr_of_smooth hu t x

theorem timeSlice_fderiv_eq_spaceTime_fderiv_inl_of_smooth_regression
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) (x : NSSpace) :
    fderiv ℝ (fun s : NSTime => u s x) t =
      (fderiv ℝ (spaceTimeVelocityMap u) (t, x)).comp
        (ContinuousLinearMap.inl ℝ NSTime NSSpace) := by
  exact timeSlice_fderiv_eq_spaceTime_fderiv_inl_of_smooth hu t x

theorem smoothSpaceTimeVelocity_hasFDerivAt_fderiv_apply_const_regression
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (tx v : NSSpacetime) :
    HasFDerivAt (fun p : NSSpacetime => (fderiv ℝ (spaceTimeVelocityMap u) p) v)
      ((fderiv ℝ (fderiv ℝ (spaceTimeVelocityMap u)) tx).flip v) tx := by
  exact smoothSpaceTimeVelocity_hasFDerivAt_fderiv_apply_const hu tx v

theorem spatialDerivativeComponent_time_derivative_eq_spacetime_second_regression
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) (x : NSSpace) (coord comp : Fin 3) :
    fderiv ℝ (fun s : NSTime => spatialDerivativeComponent u s x coord comp) t (1 : ℝ) =
      (((fderiv ℝ (fderiv ℝ (spaceTimeVelocityMap u)) (t, x))
          (ContinuousLinearMap.inl ℝ NSTime NSSpace (1 : NSTime)))
        (ContinuousLinearMap.inr ℝ NSTime NSSpace
          (EuclideanSpace.single coord (1 : ℝ)))) comp := by
  exact spatialDerivativeComponent_time_derivative_eq_spacetime_second
    hu t x coord comp

theorem spatialDerivativeComponent_timeVelocityDerivativeField_eq_spacetime_second_regression
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) (x : NSSpace) (coord comp : Fin 3) :
    spatialDerivativeComponent (timeVelocityDerivativeField u) t x coord comp =
      (((fderiv ℝ (fderiv ℝ (spaceTimeVelocityMap u)) (t, x))
          (ContinuousLinearMap.inr ℝ NSTime NSSpace
            (EuclideanSpace.single coord (1 : ℝ))))
        (ContinuousLinearMap.inl ℝ NSTime NSSpace (1 : NSTime))) comp := by
  exact spatialDerivativeComponent_timeVelocityDerivativeField_eq_spacetime_second
    hu t x coord comp

theorem spatialDerivativeComponent_time_derivative_eq_timeVelocityDerivativeField_regression
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) (x : NSSpace) (coord comp : Fin 3) :
    fderiv ℝ (fun s : NSTime => spatialDerivativeComponent u s x coord comp) t (1 : ℝ) =
      spatialDerivativeComponent (timeVelocityDerivativeField u) t x coord comp := by
  exact spatialDerivativeComponent_time_derivative_eq_timeVelocityDerivativeField
    hu t x coord comp

theorem timeVorticityDerivative_component_eq_fderiv_coordinate_regression
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) (x : NSSpace) (i : Fin 3) :
    (timeVorticityDerivative u t x) i =
      fderiv ℝ (fun s : NSTime => (spatialVorticity u s x) i) t (1 : ℝ) := by
  exact timeVorticityDerivative_component_eq_fderiv_coordinate hu t x i

theorem timeVorticityDerivative_eq_spatialVorticity_timeVelocityDerivativeField_regression
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) (x : NSSpace) :
    timeVorticityDerivative u t x =
      spatialVorticity (timeVelocityDerivativeField u) t x := by
  exact timeVorticityDerivative_eq_spatialVorticity_timeVelocityDerivativeField hu t x

theorem spatialDerivativeComponent_spatialConvectionField_eq_productRule_of_smooth_regression
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) (x : NSSpace) (coord comp : Fin 3) :
    spatialDerivativeComponent (spatialConvectionField u) t x coord comp =
      (spatialFDeriv u t x
        (spatialFDeriv u t x (EuclideanSpace.single coord (1 : ℝ)))) comp +
        ((fderiv ℝ (fun y : NSSpace => spatialFDeriv u t y) x
          (EuclideanSpace.single coord (1 : ℝ))) (u t x)) comp := by
  exact spatialDerivativeComponent_spatialConvectionField_eq_productRule_of_smooth
    hu t x coord comp

theorem spatialFDeriv_fderiv_apply_swap_of_smooth_regression
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) (x v w : NSSpace) :
    ((fderiv ℝ (fun y : NSSpace => spatialFDeriv u t y) x) v) w =
      ((fderiv ℝ (fun y : NSSpace => spatialFDeriv u t y) x) w) v := by
  exact spatialFDeriv_fderiv_apply_swap_of_smooth hu t x v w

theorem fderiv_spatialDerivativeComponent_eq_fderiv_spatialFDeriv_apply_of_smooth_regression
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) (x v : NSSpace) (coord comp : Fin 3) :
    fderiv ℝ (fun y : NSSpace => spatialDerivativeComponent u t y coord comp) x v =
      ((fderiv ℝ (fun y : NSSpace => spatialFDeriv u t y) x v)
        (EuclideanSpace.single coord (1 : ℝ))) comp := by
  exact fderiv_spatialDerivativeComponent_eq_fderiv_spatialFDeriv_apply_of_smooth
    hu t x v coord comp

theorem spatialDerivativeComponent_differentiableAt_spatial_of_smooth_regression
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) (x : NSSpace) (coord comp : Fin 3) :
    DifferentiableAt ℝ (fun y : NSSpace =>
      spatialDerivativeComponent u t y coord comp) x := by
  exact spatialDerivativeComponent_differentiableAt_spatial_of_smooth
    hu t x coord comp

theorem vorticityTransportTerm_component_eq_fderiv_coordinate_regression
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) (x : NSSpace) (i : Fin 3) :
    (vorticityTransportTerm u t x) i =
      fderiv ℝ (fun y : NSSpace => (spatialVorticity u t y) i) x (u t x) := by
  exact vorticityTransportTerm_component_eq_fderiv_coordinate hu t x i

theorem spatialVorticity_spatialConvectionField_eq_transport_sub_stretching_add_divergence_regression
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) (x : NSSpace) :
    spatialVorticity (spatialConvectionField u) t x =
      vorticityTransportTerm u t x - vorticityStretchingTerm u t x +
        spatialDivergence u t x • spatialVorticity u t x := by
  exact spatialVorticity_spatialConvectionField_eq_transport_sub_stretching_add_divergence
    hu t x

theorem vorticityConvectionExpansionDefect_eq_divergence_smul_vorticity_of_smooth_regression
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) (x : NSSpace) :
    vorticityConvectionExpansionDefect u t x =
      spatialDivergence u t x • spatialVorticity u t x := by
  exact vorticityConvectionExpansionDefect_eq_divergence_smul_vorticity_of_smooth
    hu t x

theorem vorticityConvectionExpansionDefect_eq_zero_of_smooth_divergence_regression
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    {t : NSTime} {x : NSSpace} (hdiv : spatialDivergence u t x = 0) :
    vorticityConvectionExpansionDefect u t x = 0 := by
  exact vorticityConvectionExpansionDefect_eq_zero_of_smooth_divergence hu hdiv

theorem fderiv_laplacian_apply_eq_laplacian_fderiv_apply_of_contDiff_regression
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : NSSpace → F} (hf : ContDiff ℝ ∞ f)
    (x e : NSSpace) :
    fderiv ℝ (fun y : NSSpace => Δ f y) x e =
      Δ (fun y : NSSpace => fderiv ℝ f y e) x := by
  exact fderiv_laplacian_apply_eq_laplacian_fderiv_apply_of_contDiff hf x e

theorem spatialDerivativeComponent_spatialLaplacianField_eq_laplacian_spatialDerivativeComponent_regression
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) (x : NSSpace) (coord comp : Fin 3) :
    spatialDerivativeComponent (spatialLaplacianField u) t x coord comp =
      Δ (fun y : NSSpace => spatialDerivativeComponent u t y coord comp) x := by
  exact spatialDerivativeComponent_spatialLaplacianField_eq_laplacian_spatialDerivativeComponent
    hu t x coord comp

theorem spatialVorticity_spatialLaplacianField_eq_vorticityDiffusionTerm_of_smooth_regression
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) (x : NSSpace) :
    spatialVorticity (spatialLaplacianField u) t x =
      vorticityDiffusionTerm u t x := by
  exact spatialVorticity_spatialLaplacianField_eq_vorticityDiffusionTerm_of_smooth
    hu t x

theorem vorticityTimeCommutationDefect_eq_zero_of_smooth_regression
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) (x : NSSpace) :
    vorticityTimeCommutationDefect u t x = 0 := by
  exact vorticityTimeCommutationDefect_eq_zero_of_smooth hu t x

theorem vorticityTimeCommutationClosedOn_of_smooth_regression
    {u : NSVelocityField} {T : ℝ} (hu : smoothSpaceTimeVelocity u) :
    vorticityTimeCommutationClosedOn u T := by
  exact vorticityTimeCommutationClosedOn_of_smooth hu

theorem vorticityLaplacianCommutationDefect_eq_zero_of_smooth_regression
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) (x : NSSpace) :
    vorticityLaplacianCommutationDefect u t x = 0 := by
  exact vorticityLaplacianCommutationDefect_eq_zero_of_smooth hu t x

theorem vorticityLaplacianCommutationClosedOn_of_smooth_regression
    {u : NSVelocityField} {T : ℝ} (hu : smoothSpaceTimeVelocity u) :
    vorticityLaplacianCommutationClosedOn u T := by
  exact vorticityLaplacianCommutationClosedOn_of_smooth hu

theorem residualCurlLinearityDifferentiableAt_of_smooth_laplacian_regression
    {u : NSVelocityField} {t : NSTime} {x : NSSpace}
    (hu : smoothSpaceTimeVelocity u)
    (hlap : DifferentiableAt ℝ (fun y : NSSpace => spatialLaplacianField u t y) x) :
    residualCurlLinearityDifferentiableAt u t x := by
  exact residualCurlLinearityDifferentiableAt_of_smooth_laplacian hu hlap

theorem residualCurlLinearityDifferentiableAt_of_smooth_regression
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) (x : NSSpace) :
    residualCurlLinearityDifferentiableAt u t x := by
  exact residualCurlLinearityDifferentiableAt_of_smooth hu t x

theorem residualCurlLinearityDifferentiableOn_of_smooth_laplacian_regression
    {T : ℝ} {u : NSVelocityField}
    (hu : smoothSpaceTimeVelocity u)
    (hLap : residualCurlLinearityLaplacianDifferentiableOn u T) :
    residualCurlLinearityDifferentiableOn u T := by
  exact residualCurlLinearityDifferentiableOn_of_smooth_laplacian hu hLap

theorem residualCurlLinearityDifferentiableOn_of_smooth_regression
    {T : ℝ} {u : NSVelocityField}
    (hu : smoothSpaceTimeVelocity u) :
    residualCurlLinearityDifferentiableOn u T := by
  exact residualCurlLinearityDifferentiableOn_of_smooth hu

theorem residualCurlLinearityClosedOn_of_smooth_laplacian_regression
    {ν T : ℝ} {u : NSVelocityField}
    (hu : smoothSpaceTimeVelocity u)
    (hLap : residualCurlLinearityLaplacianDifferentiableOn u T) :
    residualCurlLinearityClosedOn ν u T := by
  exact residualCurlLinearityClosedOn_of_smooth_laplacian hu hLap

theorem residualCurlLinearityClosedOn_of_smooth_regression
    {ν T : ℝ} {u : NSVelocityField}
    (hu : smoothSpaceTimeVelocity u) :
    residualCurlLinearityClosedOn ν u T := by
  exact residualCurlLinearityClosedOn_of_smooth hu

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

theorem residualCurlDifferentialIdentitiesClosedOn_of_smooth_commutationExpansion_regression
    {ν T : ℝ} {u : NSVelocityField}
    (hu : smoothSpaceTimeVelocity u)
    (hComm : residualCurlCommutationExpansionClosedOn u T) :
    residualCurlDifferentialIdentitiesClosedOn ν u T := by
  exact residualCurlDifferentialIdentitiesClosedOn_of_smooth_commutationExpansion
    hu hComm

theorem residualCurlCommutationExpansionClosedOn_of_smooth_convection_regression
    {T : ℝ} {u : NSVelocityField}
    (hu : smoothSpaceTimeVelocity u)
    (hConv : vorticityConvectionExpansionClosedOn u T) :
    residualCurlCommutationExpansionClosedOn u T := by
  exact residualCurlCommutationExpansionClosedOn_of_smooth_convection hu hConv

theorem vorticityConvectionExpansionClosedOn_of_smooth_divergence_regression
    {T : ℝ} {u : NSVelocityField}
    (hu : smoothSpaceTimeVelocity u)
    (hdiv : ∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) :
    vorticityConvectionExpansionClosedOn u T := by
  exact vorticityConvectionExpansionClosedOn_of_smooth_divergence hu hdiv

theorem residualCurlCommutationExpansionClosedOn_of_smooth_divergence_regression
    {T : ℝ} {u : NSVelocityField}
    (hu : smoothSpaceTimeVelocity u)
    (hdiv : ∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) :
    residualCurlCommutationExpansionClosedOn u T := by
  exact residualCurlCommutationExpansionClosedOn_of_smooth_divergence hu hdiv

theorem residualCurlExpansionClosedOn_of_smooth_commutationExpansion_regression
    {ν T : ℝ} {u : NSVelocityField}
    (hu : smoothSpaceTimeVelocity u)
    (hComm : residualCurlCommutationExpansionClosedOn u T) :
    residualCurlExpansionClosedOn ν u T := by
  exact residualCurlExpansionClosedOn_of_smooth_commutationExpansion hu hComm

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

theorem BKMResidualCurlDifferentialIdentitiesClosed_of_commutationExpansion_regression
    (hComm : BKMResidualCurlCommutationExpansionClosed) :
    BKMResidualCurlDifferentialIdentitiesClosed := by
  exact BKMResidualCurlDifferentialIdentitiesClosed_of_commutationExpansion hComm

theorem BKMResidualCurlCommutationExpansionClosed_proved_regression :
    BKMResidualCurlCommutationExpansionClosed := by
  exact BKMResidualCurlCommutationExpansionClosed_proved

theorem BKMResidualCurlDifferentialIdentitiesClosed_proved_regression :
    BKMResidualCurlDifferentialIdentitiesClosed := by
  exact BKMResidualCurlDifferentialIdentitiesClosed_proved

theorem BKMResidualCurlExpansionDefectVanishes_proved_regression :
    BKMResidualCurlExpansionDefectVanishes := by
  exact BKMResidualCurlExpansionDefectVanishes_proved

theorem vorticityEnstrophyGradientControlledAt_of_finiteTimeWitness_residualCurl_affinePointwiseInequality_regression
    {ν T C0 C1 : ℝ} {u₀ : NSInitialVelocity}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    {Ω H : NSTime → ℝ} {t : NSTime}
    (hν : 0 ≤ ν)
    (hVelocitySlices : finiteTimeWitnessVelocitySchwartzSlices W)
    (hVorticitySlices : finiteTimeWitnessVorticitySchwartzSlices W)
    (hInt : vorticityRawBalanceIntegralComponentsIntegrableAt W.velocity t)
    (hTime : vorticityEnstrophyTimePairingDerivativeAt W.velocity t)
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1)
    (hΩ : ∀ s, 0 ≤ s → s ≤ T → 0 ≤ Ω s)
    (hH : ∀ s, 0 ≤ s → s ≤ T → 0 ≤ H s)
    (hAffine : BKMLogSobolevAffinePointwiseInequalityOn
      W.velocity T C0 C1 Ω H)
    (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hEnstrophyInt :
      Integrable (fun x => vorticityEnstrophyDensity W.velocity t x)) :
    vorticityEnstrophyGradientControlledAt ν W.velocity t
      (C0 + C1 * bkmLogSobolevLogFactor Ω H t) := by
  exact
    vorticityEnstrophyGradientControlledAt_of_finiteTimeWitness_residualCurl_affinePointwiseInequality
      W hν hVelocitySlices hVorticitySlices hInt hTime hC0 hC1 hΩ hH hAffine
      ht0 htT hEnstrophyInt

theorem BKMVorticityFiniteTimeWitnessResidualCurlAffineLogGrowthClosed_proved_regression :
    BKMVorticityFiniteTimeWitnessResidualCurlAffineLogGrowthClosed := by
  exact BKMVorticityFiniteTimeWitnessResidualCurlAffineLogGrowthClosed_proved

theorem BKMContinuation_reduced_to_affineLogHighNorm_after_residualCurl_regression :
    BKMResidualCurlExpansionDefectVanishes ∧
      BKMVorticityFiniteTimeWitnessResidualCurlAffineLogGrowthClosed ∧
        (BKMLogSobolevAffinePointwiseFromEnvelope →
          BKMHighNormContinuationFromLogControl →
            ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons) := by
  exact BKMContinuation_reduced_to_affineLogHighNorm_after_residualCurl

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
