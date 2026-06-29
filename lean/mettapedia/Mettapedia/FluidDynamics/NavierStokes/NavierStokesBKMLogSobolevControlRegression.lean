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
