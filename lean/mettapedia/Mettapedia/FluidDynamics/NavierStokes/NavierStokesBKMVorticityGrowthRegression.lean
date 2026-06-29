import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMVorticityGrowth

/-!
# Regression checks for BKM vorticity-growth estimates
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open MeasureTheory
open scoped RealInnerProductSpace SchwartzMap

namespace Regression

theorem bkm_material_diffusion_remainder_uniform_bound_regression
    {ν T G B : ℝ} {u : NSVelocityField}
    (hEq : concreteVorticityEquationOn ν u T)
    (hG : uniformSpatialGradientOperatorBoundUpTo u T G)
    (hω : uniformVorticityBoundUpTo u T B) :
    0 ≤ G * B ∧
      ∀ t x, 0 ≤ t → t ≤ T →
        ‖vorticityMaterialDiffusionRemainder ν u t x‖ ≤ G * B :=
  uniform_vorticityMaterialDiffusionRemainder_boundUpTo hEq hG hω

theorem bkm_material_diffusion_power_uniform_bound_regression
    {ν T G B : ℝ} {u : NSVelocityField}
    (hEq : concreteVorticityEquationOn ν u T)
    (hG : uniformSpatialGradientOperatorBoundUpTo u T G)
    (hω : uniformVorticityBoundUpTo u T B) :
    0 ≤ G * (B * B) ∧
      ∀ t x, 0 ≤ t → t ≤ T →
        |vorticityMaterialDiffusionPower ν u t x| ≤ G * (B * B) :=
  uniform_vorticityMaterialDiffusionPower_boundUpTo hEq hG hω

theorem bkm_standard_vorticity_growth_estimate_closed_regression :
    BKMStandardVorticityGrowthEstimateClosed :=
  BKMStandardVorticityGrowthEstimateClosed_proved

theorem bkm_vorticity_enstrophy_apriori_estimate_closed_regression :
    BKMVorticityEnstrophyAprioriEstimateClosed :=
  BKMVorticityEnstrophyAprioriEstimateClosed_proved

theorem bkm_pointwise_normalized_vorticity_enstrophy_density_derivative_regression
    {u : NSVelocityField} {t : NSTime} {x : NSSpace}
    (hω : vorticityTimeDerivativeRepresentedAt u t x) :
    HasDerivAt (fun s => normalizedVorticityEnstrophyDensity u s x)
      (vorticityEnstrophyDensityTimeDerivativeIntegrand u t x) t :=
  hasDerivAt_normalizedVorticityEnstrophyDensity_of_timeDerivativeRepresented hω

theorem bkm_vorticity_pointwise_enstrophy_derivative_closed_regression :
    BKMVorticityPointwiseEnstrophyDerivativeClosed :=
  BKMVorticityPointwiseEnstrophyDerivativeClosed_proved

theorem bkm_vorticity_stretching_integral_gradient_control_regression
    {u : NSVelocityField} {t : NSTime} {G : ℝ}
    (hG : 0 ≤ G)
    (hGrad : ∀ x, ‖spatialFDeriv u t x‖ ≤ G)
    (hStretchInt : Integrable (fun x => vorticityStretchingPower u t x))
    (hEnstrophyInt : Integrable (fun x => vorticityEnstrophyDensity u t x)) :
    vorticityStretchingPowerIntegral u t ≤ G * vorticityEnstrophyAt u t :=
  vorticityStretchingPowerIntegral_le_gradient_mul_enstrophyAt
    hG hGrad hStretchInt hEnstrophyInt

theorem bkm_vorticity_enstrophy_controlled_from_balance_regression
    {ν : ℝ} {u : NSVelocityField} {t : NSTime}
    (hν : 0 ≤ ν) (hBal : vorticityEnstrophyBalanceAt ν u t) :
    vorticityEnstrophyStretchingControlledAt ν u t :=
  vorticityEnstrophyStretchingControlledAt_of_balance hν u hBal

theorem bkm_vorticity_enstrophy_gradient_controlled_from_balance_regression
    {ν G : ℝ} {u : NSVelocityField} {t : NSTime}
    (hν : 0 ≤ ν)
    (hBal : vorticityEnstrophyBalanceAt ν u t)
    (hG : 0 ≤ G)
    (hGrad : ∀ x, ‖spatialFDeriv u t x‖ ≤ G)
    (hStretchInt : Integrable (fun x => vorticityStretchingPower u t x))
    (hEnstrophyInt : Integrable (fun x => vorticityEnstrophyDensity u t x)) :
    vorticityEnstrophyGradientControlledAt ν u t G :=
  vorticityEnstrophyGradientControlledAt_of_balance_gradient_bound
    hν hBal hG hGrad hStretchInt hEnstrophyInt

theorem bkm_vorticity_enstrophy_gradient_growth_closed_regression :
    BKMVorticityEnstrophyGradientGrowthClosed :=
  BKMVorticityEnstrophyGradientGrowthClosed_proved

theorem bkm_vorticity_transport_power_pointwise_algebra_regression
    {u : NSVelocityField} {t : NSTime} {x : NSSpace}
    (hω : vorticitySpatialDerivativeRepresentedAt u t x) :
    normalizedVorticityEnstrophyDensityTransport u t x =
      ⟪spatialVorticity u t x, vorticityTransportTerm u t x⟫ :=
  normalizedVorticityEnstrophyDensityTransport_eq_transportPower hω

theorem bkm_vorticity_transport_power_integral_algebra_regression
    {u : NSVelocityField} {t : NSTime}
    (hω : ∀ x, vorticitySpatialDerivativeRepresentedAt u t x) :
    vorticityTransportPowerIntegral u t =
      normalizedVorticityEnstrophyDensityTransportIntegral u t :=
  vorticityTransportPowerIntegral_eq_normalizedDensityTransportIntegral hω

theorem bkm_vorticity_transport_cancellation_from_density_transport_zero_regression
    {u : NSVelocityField} {t : NSTime}
    (hω : ∀ x, vorticitySpatialDerivativeRepresentedAt u t x)
    (hZero : normalizedVorticityEnstrophyDensityTransportIntegral u t = 0) :
    vorticityTransportCancellationAt u t :=
  vorticityTransportCancellationAt_of_normalizedDensityTransportIntegral_zero
    hω hZero

theorem bkm_vorticity_transport_cancellation_algebra_closed_regression :
    BKMVorticityTransportCancellationAlgebraClosed :=
  BKMVorticityTransportCancellationAlgebraClosed_proved

theorem bkm_schwartz_scalar_directional_derivative_transport_zero_regression
    (u : NSVelocityField) (t : NSTime)
    (v : 𝓢(NSSpace, NSSpace)) (φ : 𝓢(NSSpace, ℝ))
    (hslice : ∀ x, u t x = v x)
    (hdiv : ∀ x, spatialDivergence u t x = 0) :
    ∫ x, fderiv ℝ (φ : NSSpace → ℝ) x (u t x) ∂volume = 0 :=
  integral_schwartzScalar_directionalDerivative_of_schwartzVectorSlice_spatialDivergence_zero
    u t v φ hslice hdiv

theorem bkm_vorticity_spatial_derivative_represented_from_schwartz_slice_regression
    (u : NSVelocityField) (t : NSTime) (ω : 𝓢(NSSpace, NSSpace))
    (hω : ∀ x, spatialVorticity u t x = ω x) :
    ∀ x, vorticitySpatialDerivativeRepresentedAt u t x :=
  vorticitySpatialDerivativeRepresentedAt_of_schwartzVorticitySlice
    u t ω hω

theorem bkm_normalized_vorticity_enstrophy_transport_zero_schwartz_regression
    (u : NSVelocityField) (t : NSTime)
    (v ω : 𝓢(NSSpace, NSSpace))
    (hu : ∀ x, u t x = v x)
    (hω : ∀ x, spatialVorticity u t x = ω x)
    (hdiv : ∀ x, spatialDivergence u t x = 0) :
    normalizedVorticityEnstrophyDensityTransportIntegral u t = 0 :=
  normalizedVorticityEnstrophyDensityTransportIntegral_eq_zero_of_schwartzVelocitySlice_schwartzVorticitySlice_spatialDivergence_zero
    u t v ω hu hω hdiv

theorem bkm_vorticity_transport_cancellation_schwartz_slice_regression
    (u : NSVelocityField) (t : NSTime)
    (v ω : 𝓢(NSSpace, NSSpace))
    (hu : ∀ x, u t x = v x)
    (hω : ∀ x, spatialVorticity u t x = ω x)
    (hdiv : ∀ x, spatialDivergence u t x = 0) :
    vorticityTransportCancellationAt u t :=
  vorticityTransportCancellationAt_of_schwartzVelocitySlice_schwartzVorticitySlice_spatialDivergence_zero
    u t v ω hu hω hdiv

theorem bkm_vorticity_transport_cancellation_schwartz_closed_regression :
    BKMVorticityTransportCancellationSchwartzClosed :=
  BKMVorticityTransportCancellationSchwartzClosed_proved

theorem bkm_vorticity_diffusion_dissipation_density_coordinate_regression
    (u : NSVelocityField) (t : NSTime) :
    vorticityDiffusionDissipationDensity u t =
      coordinateEnstrophyDensity (fun s y => spatialVorticity u s y) t :=
  vorticityDiffusionDissipationDensity_eq_coordinateEnstrophyDensity_vorticityField
    u t

theorem bkm_vorticity_diffusion_dissipation_coordinate_regression
    (u : NSVelocityField) (t : NSTime) :
    vorticityDiffusionDissipationAt u t =
      coordinateEnstrophyAt (fun s y => spatialVorticity u s y) t :=
  vorticityDiffusionDissipationAt_eq_coordinateEnstrophyAt_vorticityField u t

theorem bkm_vorticity_diffusion_ibp_schwartz_slice_regression
    (u : NSVelocityField) (t : NSTime) (ω : 𝓢(NSSpace, NSSpace))
    (hω : ∀ x, spatialVorticity u t x = ω x) :
    vorticityDiffusionIntegrationByPartsAt u t :=
  vorticityDiffusionIntegrationByPartsAt_of_schwartzVorticitySlice u t ω hω

theorem bkm_vorticity_diffusion_ibp_schwartz_closed_regression :
    BKMVorticityDiffusionIntegrationByPartsSchwartzClosed :=
  BKMVorticityDiffusionIntegrationByPartsSchwartzClosed_proved

theorem bkm_finite_time_witness_vorticity_schwartz_slice_diffusion_ibp_regression
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hSlices : finiteTimeWitnessVorticitySchwartzSlices W)
    {t : NSTime} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    vorticityDiffusionIntegrationByPartsAt W.velocity t :=
  vorticityDiffusionIntegrationByPartsAt_of_finiteTimeWitnessVorticitySchwartzSlices
    W hSlices ht0 htT

theorem bkm_finite_time_witness_velocity_vorticity_schwartz_transport_regression
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hVelocitySlices : finiteTimeWitnessVelocitySchwartzSlices W)
    (hVorticitySlices : finiteTimeWitnessVorticitySchwartzSlices W)
    {t : NSTime} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    vorticityTransportCancellationAt W.velocity t :=
  vorticityTransportCancellationAt_of_finiteTimeWitnessVelocityVorticitySchwartzSlices
    W hVelocitySlices hVorticitySlices ht0 htT

theorem bkm_finite_time_witness_vorticity_schwartz_slices_from_velocity_regression
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hVelocitySlices : finiteTimeWitnessVelocitySchwartzSlices W) :
    finiteTimeWitnessVorticitySchwartzSlices W :=
  finiteTimeWitnessVorticitySchwartzSlices_of_velocitySchwartzSlices
    W hVelocitySlices

theorem bkm_finite_time_witness_velocity_schwartz_transport_regression
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hVelocitySlices : finiteTimeWitnessVelocitySchwartzSlices W)
    {t : NSTime} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    vorticityTransportCancellationAt W.velocity t :=
  vorticityTransportCancellationAt_of_finiteTimeWitnessVelocitySchwartzSlices
    W hVelocitySlices ht0 htT

theorem bkm_finite_time_witness_vorticity_schwartz_slice_balance_regression
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hSlices : finiteTimeWitnessVorticitySchwartzSlices W)
    {t : NSTime}
    (hRaw : vorticityEnstrophyRawBalanceAt ν W.velocity t)
    (hTransport : vorticityTransportCancellationAt W.velocity t)
    (ht0 : 0 ≤ t) (htT : t ≤ T) :
    vorticityEnstrophyBalanceAt ν W.velocity t :=
  vorticityEnstrophyBalanceAt_of_rawBalance_transportCancellation_finiteTimeWitnessVorticitySchwartzSlices
    W hSlices hRaw hTransport ht0 htT

theorem bkm_finite_time_witness_vorticity_schwartz_slice_apriori_regression
    {ν : ℝ} (hν : 0 ≤ ν) {u₀ : NSInitialVelocity} {T : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hSlices : finiteTimeWitnessVorticitySchwartzSlices W)
    {t : NSTime}
    (hRaw : vorticityEnstrophyRawBalanceAt ν W.velocity t)
    (hTransport : vorticityTransportCancellationAt W.velocity t)
    (ht0 : 0 ≤ t) (htT : t ≤ T) :
    vorticityEnstrophyStretchingControlledAt ν W.velocity t :=
  vorticityEnstrophyStretchingControlledAt_of_rawBalance_transportCancellation_finiteTimeWitnessVorticitySchwartzSlices
    hν W hSlices hRaw hTransport ht0 htT

theorem bkm_finite_time_witness_vorticity_schwartz_slice_apriori_closed_regression :
    BKMVorticityFiniteTimeWitnessSchwartzSliceAprioriClosed :=
  BKMVorticityFiniteTimeWitnessSchwartzSliceAprioriClosed_proved

theorem bkm_finite_time_witness_velocity_vorticity_schwartz_slice_balance_regression
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hVelocitySlices : finiteTimeWitnessVelocitySchwartzSlices W)
    (hVorticitySlices : finiteTimeWitnessVorticitySchwartzSlices W)
    {t : NSTime}
    (hRaw : vorticityEnstrophyRawBalanceAt ν W.velocity t)
    (ht0 : 0 ≤ t) (htT : t ≤ T) :
    vorticityEnstrophyBalanceAt ν W.velocity t :=
  vorticityEnstrophyBalanceAt_of_rawBalance_finiteTimeWitnessVelocityVorticitySchwartzSlices
    W hVelocitySlices hVorticitySlices hRaw ht0 htT

theorem bkm_finite_time_witness_velocity_vorticity_schwartz_slice_apriori_regression
    {ν : ℝ} (hν : 0 ≤ ν) {u₀ : NSInitialVelocity} {T : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hVelocitySlices : finiteTimeWitnessVelocitySchwartzSlices W)
    (hVorticitySlices : finiteTimeWitnessVorticitySchwartzSlices W)
    {t : NSTime}
    (hRaw : vorticityEnstrophyRawBalanceAt ν W.velocity t)
    (ht0 : 0 ≤ t) (htT : t ≤ T) :
    vorticityEnstrophyStretchingControlledAt ν W.velocity t :=
  vorticityEnstrophyStretchingControlledAt_of_rawBalance_finiteTimeWitnessVelocityVorticitySchwartzSlices
    hν W hVelocitySlices hVorticitySlices hRaw ht0 htT

theorem bkm_finite_time_witness_velocity_vorticity_schwartz_slice_apriori_closed_regression :
    BKMVorticityFiniteTimeWitnessVelocityVorticitySchwartzAprioriClosed :=
  BKMVorticityFiniteTimeWitnessVelocityVorticitySchwartzAprioriClosed_proved

theorem bkm_finite_time_witness_velocity_schwartz_slice_balance_regression
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hVelocitySlices : finiteTimeWitnessVelocitySchwartzSlices W)
    {t : NSTime}
    (hRaw : vorticityEnstrophyRawBalanceAt ν W.velocity t)
    (ht0 : 0 ≤ t) (htT : t ≤ T) :
    vorticityEnstrophyBalanceAt ν W.velocity t :=
  vorticityEnstrophyBalanceAt_of_rawBalance_finiteTimeWitnessVelocitySchwartzSlices
    W hVelocitySlices hRaw ht0 htT

theorem bkm_finite_time_witness_velocity_schwartz_slice_apriori_regression
    {ν : ℝ} (hν : 0 ≤ ν) {u₀ : NSInitialVelocity} {T : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hVelocitySlices : finiteTimeWitnessVelocitySchwartzSlices W)
    {t : NSTime}
    (hRaw : vorticityEnstrophyRawBalanceAt ν W.velocity t)
    (ht0 : 0 ≤ t) (htT : t ≤ T) :
    vorticityEnstrophyStretchingControlledAt ν W.velocity t :=
  vorticityEnstrophyStretchingControlledAt_of_rawBalance_finiteTimeWitnessVelocitySchwartzSlices
    hν W hVelocitySlices hRaw ht0 htT

theorem bkm_finite_time_witness_velocity_schwartz_slice_apriori_closed_regression :
    BKMVorticityFiniteTimeWitnessVelocitySchwartzAprioriClosed :=
  BKMVorticityFiniteTimeWitnessVelocitySchwartzAprioriClosed_proved

theorem bkm_vorticity_enstrophy_balance_assembly_closed_regression :
    BKMVorticityEnstrophyBalanceAssemblyClosed :=
  BKMVorticityEnstrophyBalanceAssemblyClosed_proved

theorem bkm_vorticity_enstrophy_balance_from_raw_regression
    {ν : ℝ} {u : NSVelocityField} {t : NSTime}
    (hRaw : vorticityEnstrophyRawBalanceAt ν u t)
    (hTransport : vorticityTransportCancellationAt u t)
    (hDiffusion : vorticityDiffusionIntegrationByPartsAt u t) :
    vorticityEnstrophyBalanceAt ν u t :=
  vorticityEnstrophyBalanceAt_of_rawBalance_transportCancellation_diffusionIBP
    hRaw hTransport hDiffusion

theorem bkm_vorticity_enstrophy_controlled_from_raw_regression
    {ν : ℝ} {u : NSVelocityField} {t : NSTime}
    (hν : 0 ≤ ν)
    (hRaw : vorticityEnstrophyRawBalanceAt ν u t)
    (hTransport : vorticityTransportCancellationAt u t)
    (hDiffusion : vorticityDiffusionIntegrationByPartsAt u t) :
    vorticityEnstrophyStretchingControlledAt ν u t :=
  vorticityEnstrophyStretchingControlledAt_of_rawBalance_transportCancellation_diffusionIBP
    hν hRaw hTransport hDiffusion

theorem bkm_vorticity_time_pairing_pointwise_regression
    {ν T : ℝ} {u : NSVelocityField}
    (hEq : concreteVorticityEquationOn ν u T)
    {t : NSTime} {x : NSSpace} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ⟪spatialVorticity u t x, timeVorticityDerivative u t x⟫ =
      -⟪spatialVorticity u t x, vorticityTransportTerm u t x⟫ +
        ν * ⟪spatialVorticity u t x, vorticityDiffusionTerm u t x⟫ +
          vorticityStretchingPower u t x :=
  vorticityTimePairing_eq_rawBalanceIntegrand_of_concreteVorticityEquationOn
    hEq ht0 htT

theorem bkm_vorticity_time_power_integral_raw_balance_regression
    {ν T : ℝ} {u : NSVelocityField} {t : NSTime}
    (hEq : concreteVorticityEquationOn ν u T)
    (hInt : vorticityRawBalanceIntegralComponentsIntegrableAt u t)
    (ht0 : 0 ≤ t) (htT : t ≤ T) :
    vorticityTimePowerIntegral u t =
      vorticityEnstrophyRawBalanceDerivative ν u t :=
  vorticityTimePowerIntegral_eq_rawBalanceDerivative_of_concreteVorticityEquationOn
    hEq hInt ht0 htT

theorem bkm_vorticity_raw_balance_from_standard_equation_closed_regression :
    BKMVorticityRawBalanceFromStandardEquationClosed :=
  BKMVorticityRawBalanceFromStandardEquationClosed_proved

theorem bkm_vorticity_raw_balance_from_standard_equation_regression
    {ν T : ℝ} {u : NSVelocityField} {t : NSTime}
    (hEq : concreteVorticityEquationOn ν u T)
    (hInt : vorticityRawBalanceIntegralComponentsIntegrableAt u t)
    (hTime : vorticityEnstrophyTimePairingDerivativeAt u t)
    (ht0 : 0 ≤ t) (htT : t ≤ T) :
    vorticityEnstrophyRawBalanceAt ν u t :=
  vorticityEnstrophyRawBalanceAt_of_timePairingDerivative_concreteVorticityEquationOn
    hEq hInt hTime ht0 htT

theorem bkm_vorticity_raw_balance_integrability_schwartz_closed_regression :
    BKMVorticityRawBalanceIntegrabilitySchwartzClosed :=
  BKMVorticityRawBalanceIntegrabilitySchwartzClosed_proved

theorem bkm_vorticity_scalar_schwartz_time_pairing_closed_regression :
    BKMVorticityScalarSchwartzTimePairingDerivativeClosed :=
  BKMVorticityScalarSchwartzTimePairingDerivativeClosed_proved

theorem bkm_vorticity_two_profile_schwartz_time_pairing_closed_regression :
    BKMVorticityTwoProfileSchwartzTimePairingDerivativeClosed :=
  BKMVorticityTwoProfileSchwartzTimePairingDerivativeClosed_proved

theorem bkm_vorticity_finite_family_schwartz_time_pairing_closed_regression :
    BKMVorticityFiniteFamilySchwartzTimePairingDerivativeClosed :=
  BKMVorticityFiniteFamilySchwartzTimePairingDerivativeClosed_proved

theorem bkm_vorticity_velocity_schwartz_enstrophy_integrable_closed_regression :
    BKMVorticityFiniteTimeWitnessVelocitySchwartzEnstrophyIntegrableClosed :=
  BKMVorticityFiniteTimeWitnessVelocitySchwartzEnstrophyIntegrableClosed_proved

theorem bkm_vorticity_velocity_schwartz_raw_balance_integrability_closed_regression :
    BKMVorticityFiniteTimeWitnessVelocitySchwartzRawBalanceIntegrabilityClosed :=
  BKMVorticityFiniteTimeWitnessVelocitySchwartzRawBalanceIntegrabilityClosed_proved

end Regression

end NavierStokes
end FluidDynamics
end Mettapedia
