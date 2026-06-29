import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMVorticityGrowth

/-!
# BKM log-Sobolev gradient-control interface

This module does not prove the analytic log-Sobolev/Biot-Savart estimate.
It records the exact interface needed by the BKM route: once such a gradient
control is supplied, the already-checked stretching and standard-vorticity
growth estimates apply with the corresponding logarithmic envelope.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section BKMContinuation

/-- Candidate logarithmic gradient envelope for the BKM route.  The `H`
argument is an external high-norm envelope; this definition only records the
shape used downstream, not a proof that `H` is any particular Sobolev norm. -/
def bkmLogSobolevGradientEnvelope
    (C : ℝ) (Ω H : NSTime → ℝ) (t : NSTime) : ℝ :=
  C * (1 + Ω t * Real.log (Real.exp 1 + H t))

/-- A supplied log-Sobolev/Biot-Savart gradient-control hypothesis on a slab. -/
def BKMLogSobolevGradientControlOn
    (u : NSVelocityField) (T C : ℝ) (Ω H : NSTime → ℝ) : Prop :=
  (∀ t, 0 ≤ t → t ≤ T → 0 ≤ bkmLogSobolevGradientEnvelope C Ω H t) ∧
    ∀ t x, 0 ≤ t → t ≤ T →
      ‖spatialFDeriv u t x‖ ≤ bkmLogSobolevGradientEnvelope C Ω H t

/-- A supplied log-Sobolev gradient control is exactly the gradient envelope
needed by the checked stretching estimates. -/
theorem BKMLogSobolevGradientControlOn.to_spatialGradientOperatorEnvelopeOn
    {u : NSVelocityField} {T C : ℝ} {Ω H : NSTime → ℝ}
    (hLog : BKMLogSobolevGradientControlOn u T C Ω H) :
    spatialGradientOperatorEnvelopeOn u T
      (bkmLogSobolevGradientEnvelope C Ω H) :=
  hLog

/-- Log-Sobolev gradient control and a vorticity envelope control the
material-minus-diffusion remainder under the standard vorticity equation. -/
theorem norm_vorticityMaterialDiffusionRemainder_le_of_logSobolev_control
    {ν T C : ℝ} {u : NSVelocityField} {Ω H : NSTime → ℝ}
    (hEq : concreteVorticityEquationOn ν u T)
    (hLog : BKMLogSobolevGradientControlOn u T C Ω H)
    (hΩ : vorticityEnvelopeOn u T Ω)
    {t : NSTime} {x : NSSpace} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ‖vorticityMaterialDiffusionRemainder ν u t x‖ ≤
      bkmLogSobolevGradientEnvelope C Ω H t * Ω t := by
  exact
    norm_vorticityMaterialDiffusionRemainder_le_of_envelopes hEq
      (BKMLogSobolevGradientControlOn.to_spatialGradientOperatorEnvelopeOn hLog)
      hΩ ht0 htT

/-- Log-Sobolev gradient control and a vorticity envelope control the
pointwise enstrophy-production contribution of the standard vorticity
equation. -/
theorem abs_vorticityMaterialDiffusionPower_le_of_logSobolev_control
    {ν T C : ℝ} {u : NSVelocityField} {Ω H : NSTime → ℝ}
    (hEq : concreteVorticityEquationOn ν u T)
    (hLog : BKMLogSobolevGradientControlOn u T C Ω H)
    (hΩ : vorticityEnvelopeOn u T Ω)
    {t : NSTime} {x : NSSpace} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    |vorticityMaterialDiffusionPower ν u t x| ≤
      bkmLogSobolevGradientEnvelope C Ω H t * (Ω t * Ω t) := by
  exact
    abs_vorticityMaterialDiffusionPower_le_of_envelopes hEq
      (BKMLogSobolevGradientControlOn.to_spatialGradientOperatorEnvelopeOn hLog)
      hΩ ht0 htT

/-- The downstream BKM growth estimates are closed once the analytic
log-Sobolev/Biot-Savart gradient control is supplied as an explicit
hypothesis. -/
def BKMLogSobolevGrowthEstimateClosed : Prop :=
  ∀ (ν : ℝ) (u : NSVelocityField) (T C : ℝ) (Ω H : NSTime → ℝ),
    concreteVorticityEquationOn ν u T →
      BKMLogSobolevGradientControlOn u T C Ω H →
        vorticityEnvelopeOn u T Ω →
          spatialGradientOperatorEnvelopeOn u T
              (bkmLogSobolevGradientEnvelope C Ω H) ∧
            (∀ t x, 0 ≤ t → t ≤ T →
              ‖vorticityMaterialDiffusionRemainder ν u t x‖ ≤
                bkmLogSobolevGradientEnvelope C Ω H t * Ω t) ∧
            (∀ t x, 0 ≤ t → t ≤ T →
              |vorticityMaterialDiffusionPower ν u t x| ≤
                bkmLogSobolevGradientEnvelope C Ω H t * (Ω t * Ω t))

/-- Checked proof of the log-Sobolev-control-to-growth package. -/
theorem BKMLogSobolevGrowthEstimateClosed_proved :
    BKMLogSobolevGrowthEstimateClosed := by
  intro ν u T C Ω H hEq hLog hΩ
  exact
    ⟨BKMLogSobolevGradientControlOn.to_spatialGradientOperatorEnvelopeOn hLog,
      fun t x ht0 htT =>
        norm_vorticityMaterialDiffusionRemainder_le_of_logSobolev_control
          hEq hLog hΩ ht0 htT,
      fun t x ht0 htT =>
        abs_vorticityMaterialDiffusionPower_le_of_logSobolev_control
          hEq hLog hΩ ht0 htT⟩

end BKMContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
