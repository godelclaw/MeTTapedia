import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMLogSobolevControl

/-!
# Regression checks for the BKM log-Sobolev gradient-control interface
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

namespace Regression

theorem bkm_logSobolev_envelope_nonneg_regression
    {C : ℝ} {Ω H : NSTime → ℝ} {t : NSTime}
    (hC : 0 ≤ C) (hΩ : 0 ≤ Ω t) (hH : 0 ≤ H t) :
    0 ≤ bkmLogSobolevGradientEnvelope C Ω H t :=
  bkmLogSobolevGradientEnvelope_nonneg_of_nonneg hC hΩ hH

theorem bkm_logSobolev_pointwise_to_control_regression
    {u : NSVelocityField} {T C : ℝ} {Ω H : NSTime → ℝ}
    (hC : 0 ≤ C)
    (hΩ : ∀ t, 0 ≤ t → t ≤ T → 0 ≤ Ω t)
    (hH : ∀ t, 0 ≤ t → t ≤ T → 0 ≤ H t)
    (hIneq : BKMLogSobolevPointwiseInequalityOn u T C Ω H) :
    BKMLogSobolevGradientControlOn u T C Ω H :=
  BKMLogSobolevGradientControlOn.of_pointwiseInequality hC hΩ hH hIneq

theorem bkm_logSobolev_control_to_gradient_envelope_regression
    {u : NSVelocityField} {T C : ℝ} {Ω H : NSTime → ℝ}
    (hLog : BKMLogSobolevGradientControlOn u T C Ω H) :
    spatialGradientOperatorEnvelopeOn u T
      (bkmLogSobolevGradientEnvelope C Ω H) :=
  BKMLogSobolevGradientControlOn.to_spatialGradientOperatorEnvelopeOn hLog

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

end Regression

end NavierStokes
end FluidDynamics
end Mettapedia
