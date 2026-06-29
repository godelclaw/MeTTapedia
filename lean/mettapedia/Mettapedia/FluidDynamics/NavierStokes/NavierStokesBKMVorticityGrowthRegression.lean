import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMVorticityGrowth

/-!
# Regression checks for BKM vorticity-growth estimates
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open scoped RealInnerProductSpace

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

theorem bkm_vorticity_enstrophy_controlled_from_balance_regression
    {ν : ℝ} {u : NSVelocityField} {t : NSTime}
    (hν : 0 ≤ ν) (hBal : vorticityEnstrophyBalanceAt ν u t) :
    vorticityEnstrophyStretchingControlledAt ν u t :=
  vorticityEnstrophyStretchingControlledAt_of_balance hν u hBal

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

end Regression

end NavierStokes
end FluidDynamics
end Mettapedia
