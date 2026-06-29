import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMLogSobolevControl

/-!
# Regression checks for the BKM log-Sobolev gradient-control interface
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open MeasureTheory

namespace Regression

theorem bkm_logSobolev_envelope_nonneg_regression
    {C : ℝ} {Ω H : NSTime → ℝ} {t : NSTime}
    (hC : 0 ≤ C) (hΩ : 0 ≤ Ω t) (hH : 0 ≤ H t) :
    0 ≤ bkmLogSobolevGradientEnvelope C Ω H t :=
  bkmLogSobolevGradientEnvelope_nonneg_of_nonneg hC hΩ hH

theorem bkm_logSobolev_log_factor_nonneg_regression
    {Ω H : NSTime → ℝ} {t : NSTime}
    (hΩ : 0 ≤ Ω t) (hH : 0 ≤ H t) :
    0 ≤ bkmLogSobolevLogFactor Ω H t :=
  bkmLogSobolevLogFactor_nonneg_of_nonneg hΩ hH

theorem bkm_logSobolev_envelope_dominates_affineLog_regression
    {C C0 C1 : ℝ} {Ω H : NSTime → ℝ} {t : NSTime}
    (hC0 : C0 ≤ C) (hC1 : C1 ≤ C)
    (hΩ : 0 ≤ Ω t) (hH : 0 ≤ H t) :
    C0 + C1 * bkmLogSobolevLogFactor Ω H t ≤
      bkmLogSobolevGradientEnvelope C Ω H t :=
  bkmLogSobolevGradientEnvelope_dominates_affineLog hC0 hC1 hΩ hH

theorem bkm_logSobolev_pointwise_to_control_regression
    {u : NSVelocityField} {T C : ℝ} {Ω H : NSTime → ℝ}
    (hC : 0 ≤ C)
    (hΩ : ∀ t, 0 ≤ t → t ≤ T → 0 ≤ Ω t)
    (hH : ∀ t, 0 ≤ t → t ≤ T → 0 ≤ H t)
    (hIneq : BKMLogSobolevPointwiseInequalityOn u T C Ω H) :
    BKMLogSobolevGradientControlOn u T C Ω H :=
  BKMLogSobolevGradientControlOn.of_pointwiseInequality hC hΩ hH hIneq

theorem bkm_logSobolev_affine_pointwise_to_pointwise_regression
    {u : NSVelocityField} {T C C0 C1 : ℝ} {Ω H : NSTime → ℝ}
    (hC0 : C0 ≤ C) (hC1 : C1 ≤ C)
    (hΩ : ∀ t, 0 ≤ t → t ≤ T → 0 ≤ Ω t)
    (hH : ∀ t, 0 ≤ t → t ≤ T → 0 ≤ H t)
    (hAffine : BKMLogSobolevAffinePointwiseInequalityOn u T C0 C1 Ω H) :
    BKMLogSobolevPointwiseInequalityOn u T C Ω H :=
  BKMLogSobolevPointwiseInequalityOn.of_affinePointwiseInequality
    hC0 hC1 hΩ hH hAffine

theorem bkm_logSobolev_affine_pointwise_to_control_regression
    {u : NSVelocityField} {T C C0 C1 : ℝ} {Ω H : NSTime → ℝ}
    (hC : 0 ≤ C)
    (hC0 : C0 ≤ C) (hC1 : C1 ≤ C)
    (hΩ : ∀ t, 0 ≤ t → t ≤ T → 0 ≤ Ω t)
    (hH : ∀ t, 0 ≤ t → t ≤ T → 0 ≤ H t)
    (hAffine : BKMLogSobolevAffinePointwiseInequalityOn u T C0 C1 Ω H) :
    BKMLogSobolevGradientControlOn u T C Ω H :=
  BKMLogSobolevGradientControlOn.of_affinePointwiseInequality
    hC hC0 hC1 hΩ hH hAffine

theorem bkm_logSobolev_affine_pointwise_to_control_max_regression
    {u : NSVelocityField} {T C0 C1 : ℝ} {Ω H : NSTime → ℝ}
    (hC0_nonneg : 0 ≤ C0) (hC1_nonneg : 0 ≤ C1)
    (hΩ : ∀ t, 0 ≤ t → t ≤ T → 0 ≤ Ω t)
    (hH : ∀ t, 0 ≤ t → t ≤ T → 0 ≤ H t)
    (hAffine : BKMLogSobolevAffinePointwiseInequalityOn u T C0 C1 Ω H) :
    BKMLogSobolevGradientControlOn u T (max C0 C1) Ω H :=
  BKMLogSobolevGradientControlOn.of_affinePointwiseInequality_max
    hC0_nonneg hC1_nonneg hΩ hH hAffine

theorem bkm_logSobolev_control_to_gradient_envelope_regression
    {u : NSVelocityField} {T C : ℝ} {Ω H : NSTime → ℝ}
    (hLog : BKMLogSobolevGradientControlOn u T C Ω H) :
    spatialGradientOperatorEnvelopeOn u T
      (bkmLogSobolevGradientEnvelope C Ω H) :=
  BKMLogSobolevGradientControlOn.to_spatialGradientOperatorEnvelopeOn hLog

theorem bkm_logSobolev_control_to_enstrophy_growth_regression
    {ν T C : ℝ} {u : NSVelocityField} {Ω H : NSTime → ℝ} {t : NSTime}
    (hν : 0 ≤ ν)
    (hBal : vorticityEnstrophyBalanceAt ν u t)
    (hLog : BKMLogSobolevGradientControlOn u T C Ω H)
    (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hStretchInt : Integrable (fun x => vorticityStretchingPower u t x))
    (hEnstrophyInt : Integrable (fun x => vorticityEnstrophyDensity u t x)) :
    vorticityEnstrophyGradientControlledAt ν u t
      (bkmLogSobolevGradientEnvelope C Ω H t) :=
  vorticityEnstrophyGradientControlledAt_of_balance_logSobolev_control
    hν hBal hLog ht0 htT hStretchInt hEnstrophyInt

theorem bkm_logSobolev_pointwise_to_enstrophy_growth_regression
    {ν T C : ℝ} {u : NSVelocityField} {Ω H : NSTime → ℝ} {t : NSTime}
    (hν : 0 ≤ ν)
    (hBal : vorticityEnstrophyBalanceAt ν u t)
    (hC : 0 ≤ C)
    (hΩ : ∀ s, 0 ≤ s → s ≤ T → 0 ≤ Ω s)
    (hH : ∀ s, 0 ≤ s → s ≤ T → 0 ≤ H s)
    (hIneq : BKMLogSobolevPointwiseInequalityOn u T C Ω H)
    (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hStretchInt : Integrable (fun x => vorticityStretchingPower u t x))
    (hEnstrophyInt : Integrable (fun x => vorticityEnstrophyDensity u t x)) :
    vorticityEnstrophyGradientControlledAt ν u t
      (bkmLogSobolevGradientEnvelope C Ω H t) :=
  vorticityEnstrophyGradientControlledAt_of_balance_logSobolev_pointwiseInequality
    hν hBal hC hΩ hH hIneq ht0 htT hStretchInt hEnstrophyInt

theorem bkm_logSobolev_affine_pointwise_to_enstrophy_growth_regression
    {ν T C0 C1 : ℝ} {u : NSVelocityField} {Ω H : NSTime → ℝ} {t : NSTime}
    (hν : 0 ≤ ν)
    (hBal : vorticityEnstrophyBalanceAt ν u t)
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1)
    (hΩ : ∀ s, 0 ≤ s → s ≤ T → 0 ≤ Ω s)
    (hH : ∀ s, 0 ≤ s → s ≤ T → 0 ≤ H s)
    (hAffine : BKMLogSobolevAffinePointwiseInequalityOn u T C0 C1 Ω H)
    (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hStretchInt : Integrable (fun x => vorticityStretchingPower u t x))
    (hEnstrophyInt : Integrable (fun x => vorticityEnstrophyDensity u t x)) :
    vorticityEnstrophyGradientControlledAt ν u t
      (C0 + C1 * bkmLogSobolevLogFactor Ω H t) :=
  vorticityEnstrophyGradientControlledAt_of_balance_logSobolev_affinePointwiseInequality
    hν hBal hC0 hC1 hΩ hH hAffine ht0 htT hStretchInt hEnstrophyInt

theorem bkm_logSobolev_material_remainder_bound_regression
    {ν T C : ℝ} {u : NSVelocityField} {Ω H : NSTime → ℝ}
    (hEq : concreteVorticityEquationOn ν u T)
    (hLog : BKMLogSobolevGradientControlOn u T C Ω H)
    (hΩ : vorticityEnvelopeOn u T Ω)
    {t : NSTime} {x : NSSpace} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ‖vorticityMaterialDiffusionRemainder ν u t x‖ ≤
      bkmLogSobolevGradientEnvelope C Ω H t * Ω t :=
  norm_vorticityMaterialDiffusionRemainder_le_of_logSobolev_control
    hEq hLog hΩ ht0 htT

theorem bkm_logSobolev_material_power_bound_regression
    {ν T C : ℝ} {u : NSVelocityField} {Ω H : NSTime → ℝ}
    (hEq : concreteVorticityEquationOn ν u T)
    (hLog : BKMLogSobolevGradientControlOn u T C Ω H)
    (hΩ : vorticityEnvelopeOn u T Ω)
    {t : NSTime} {x : NSSpace} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    |vorticityMaterialDiffusionPower ν u t x| ≤
      bkmLogSobolevGradientEnvelope C Ω H t * (Ω t * Ω t) :=
  abs_vorticityMaterialDiffusionPower_le_of_logSobolev_control
    hEq hLog hΩ ht0 htT

theorem bkm_logSobolev_growth_estimate_closed_regression :
    BKMLogSobolevGrowthEstimateClosed :=
  BKMLogSobolevGrowthEstimateClosed_proved

theorem bkm_logSobolev_affine_reduction_closed_regression :
    BKMLogSobolevAffineReductionClosed :=
  BKMLogSobolevAffineReductionClosed_proved

theorem bkm_vorticity_enstrophy_logSobolev_growth_closed_regression :
    BKMVorticityEnstrophyLogSobolevGrowthClosed :=
  BKMVorticityEnstrophyLogSobolevGrowthClosed_proved

theorem bkm_vorticity_enstrophy_affine_log_growth_closed_regression :
    BKMVorticityEnstrophyAffineLogGrowthClosed :=
  BKMVorticityEnstrophyAffineLogGrowthClosed_proved

end Regression

end NavierStokes
end FluidDynamics
end Mettapedia
