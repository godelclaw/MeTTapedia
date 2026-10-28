import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMVorticityStretching

/-!
# Regression checks for BKM vorticity-stretching estimates
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open scoped ContDiff RealInnerProductSpace

namespace Regression

theorem bkm_stretching_term_pointwise_bound_regression
    (u : NSVelocityField) (t : NSTime) (x : NSSpace) :
    ‖vorticityStretchingTerm u t x‖ ≤
      ‖spatialFDeriv u t x‖ * ‖spatialVorticity u t x‖ :=
  norm_vorticityStretchingTerm_le u t x

theorem bkm_stretching_power_pointwise_bound_regression
    (u : NSVelocityField) (t : NSTime) (x : NSSpace) :
    |vorticityStretchingPower u t x| ≤
      ‖spatialFDeriv u t x‖ *
        (‖spatialVorticity u t x‖ * ‖spatialVorticity u t x‖) :=
  abs_vorticityStretchingPower_le u t x

theorem bkm_stretching_term_envelope_bound_regression
    {u : NSVelocityField} {T : ℝ} {Γ Ω : NSTime → ℝ}
    (hΓ : spatialGradientOperatorEnvelopeOn u T Γ)
    (hΩ : vorticityEnvelopeOn u T Ω)
    {t : NSTime} {x : NSSpace} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ‖vorticityStretchingTerm u t x‖ ≤ Γ t * Ω t :=
  norm_vorticityStretchingTerm_le_of_envelopes hΓ hΩ ht0 htT

theorem bkm_stretching_power_uniform_bound_regression
    {u : NSVelocityField} {T G B : ℝ}
    (hG : uniformSpatialGradientOperatorBoundUpTo u T G)
    (hω : uniformVorticityBoundUpTo u T B) :
    0 ≤ G * (B * B) ∧
      ∀ t x, 0 ≤ t → t ≤ T →
        |vorticityStretchingPower u t x| ≤ G * (B * B) :=
  uniform_vorticityStretchingPower_boundUpTo hG hω

end Regression

end NavierStokes
end FluidDynamics
end Mettapedia
