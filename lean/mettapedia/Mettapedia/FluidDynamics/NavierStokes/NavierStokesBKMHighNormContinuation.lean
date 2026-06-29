import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMAnalyticReduction

/-!
# BKM high-norm continuation assembly

The checked BKM route now has pointwise stretching estimates, the residual-curl
surface, the residual-curl expansion algebra, and the supplied-log-Sobolev
growth interface.  This module splits the remaining analytic continuation
lemma into the three concrete ingredients still needed by the classical BKM
argument.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section BKMContinuation

/-- Analytic log-Sobolev/Biot-Savart ingredient: once the standard vorticity
equation and BKM envelope data are available on a slab, produce a logarithmic
gradient-control envelope for the witness velocity. -/
def BKMLogSobolevGradientControlFromEnvelope : Prop :=
  ∀ (ν : ℝ) (u₀ : NSInitialVelocity) (T : ℝ)
      (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
      (Ω : NSTime → ℝ) (B : ℝ),
    0 ≤ T →
      0 < ν →
        smoothInitialVelocityData u₀ →
          (∀ x, initialSpatialDivergence u₀ x = 0) →
            finiteInitialKineticEnergy u₀ →
              concreteVorticityEquationOn ν W.velocity T →
                vorticityEnvelopeOn W.velocity T Ω →
                  integrableVorticityEnvelopeOn Ω T B →
                    ∃ C : ℝ, ∃ H : NSTime → ℝ,
                      BKMLogSobolevGradientControlOn W.velocity T C Ω H

/-- Analytic high-norm continuation ingredient: the standard vorticity equation,
an integrable vorticity envelope, and the corresponding logarithmic gradient
control extend the finite-time witness to the existing explicit global-output
surface. -/
def BKMHighNormContinuationFromLogControl : Prop :=
  ∀ (ν : ℝ) (u₀ : NSInitialVelocity) (T : ℝ)
      (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
      (Ω : NSTime → ℝ) (B C : ℝ) (H : NSTime → ℝ),
    0 ≤ T →
      0 < ν →
        smoothInitialVelocityData u₀ →
          (∀ x, initialSpatialDivergence u₀ x = 0) →
            finiteInitialKineticEnergy u₀ →
              vorticityEnvelopeOn W.velocity T Ω →
                integrableVorticityEnvelopeOn Ω T B →
                  concreteVorticityEquationOn ν W.velocity T →
                    BKMLogSobolevGradientControlOn W.velocity T C Ω H →
                      ExplicitConcreteNavierStokesGlobalOutput ν u₀

/-- Componentized form of the remaining BKM analytic route.  The first
component is the residual-curl expansion identity, the second supplies the
logarithmic gradient envelope from BKM data, and the third closes the high-norm
continuation step. -/
def BKMAnalyticComponentsClosed : Prop :=
  BKMResidualCurlExpansionDefectVanishes ∧
    BKMLogSobolevGradientControlFromEnvelope ∧
      BKMHighNormContinuationFromLogControl

/-- The three analytic components imply the previous single continuation
lemma. -/
theorem BKMAnalyticContinuationLemma_of_components
    (hDefect : BKMResidualCurlExpansionDefectVanishes)
    (hLog : BKMLogSobolevGradientControlFromEnvelope)
    (hHigh : BKMHighNormContinuationFromLogControl) :
    BKMAnalyticContinuationLemma := by
  intro ν u₀ T hT hν hsmooth hdiv hfinite W hCurl hEnv
  rcases hEnv with ⟨Ω, B, hΩ, hInt⟩
  have hEq : concreteVorticityEquationOn ν W.velocity T :=
    hDefect.implies_concreteVorticityEquationOn W.smooth_velocity
      (fun t x ht0 htT => W.incompressible_on t x ht0 htT)
      hCurl
  rcases hLog ν u₀ T W Ω B hT hν hsmooth hdiv hfinite hEq hΩ hInt with
    ⟨C, H, hLogControl⟩
  exact hHigh ν u₀ T W Ω B C H hT hν hsmooth hdiv hfinite
    hΩ hInt hEq hLogControl

/-- Bundled component form implies the previous single continuation lemma. -/
theorem BKMAnalyticComponentsClosed.implies_BKMAnalyticContinuationLemma
    (h : BKMAnalyticComponentsClosed) :
    BKMAnalyticContinuationLemma := by
  exact BKMAnalyticContinuationLemma_of_components h.1 h.2.1 h.2.2

/-- The repaired nonnegative-horizon BKM target follows from the componentized
analytic route. -/
theorem BKMAnalyticComponentsClosed.implies_finiteEnergyBKMContinuationTargetOnNonnegHorizons
    (h : BKMAnalyticComponentsClosed) :
    ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons :=
  BKMAnalyticContinuationLemma_implies_finiteEnergyBKMContinuationTargetOnNonnegHorizons
    h.implies_BKMAnalyticContinuationLemma

/-- Route-facing packet: the local BKM estimates are checked, and the remaining
target follows from the componentized analytic ingredients. -/
theorem BKMContinuation_reduced_to_analytic_components :
    BKMVorticityStretchingEstimateClosed ∧
      BKMResidualCurlExpansionAlgebraClosed ∧
        BKMStandardVorticityGrowthEstimateClosed ∧
          BKMVorticityPointwiseEnstrophyDerivativeClosed ∧
            BKMVorticityRawBalanceFromStandardEquationClosed ∧
              BKMVorticityTransportCancellationAlgebraClosed ∧
                BKMVorticityDiffusionIntegrationByPartsSchwartzClosed ∧
                  BKMVorticityFiniteTimeWitnessSchwartzSliceAprioriClosed ∧
                    BKMVorticityEnstrophyBalanceAssemblyClosed ∧
                      BKMVorticityEnstrophyAprioriEstimateClosed ∧
                        BKMVorticityEnstrophyGradientGrowthClosed ∧
                          BKMVorticityEnstrophyLogSobolevGrowthClosed ∧
                            BKMLogSobolevGrowthEstimateClosed ∧
                              (BKMAnalyticComponentsClosed →
                                ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons) := by
  exact
    ⟨BKMVorticityStretchingEstimateClosed_proved,
      BKMResidualCurlExpansionAlgebraClosed_proved,
      BKMStandardVorticityGrowthEstimateClosed_proved,
      BKMVorticityPointwiseEnstrophyDerivativeClosed_proved,
      BKMVorticityRawBalanceFromStandardEquationClosed_proved,
      BKMVorticityTransportCancellationAlgebraClosed_proved,
      BKMVorticityDiffusionIntegrationByPartsSchwartzClosed_proved,
      BKMVorticityFiniteTimeWitnessSchwartzSliceAprioriClosed_proved,
      BKMVorticityEnstrophyBalanceAssemblyClosed_proved,
      BKMVorticityEnstrophyAprioriEstimateClosed_proved,
      BKMVorticityEnstrophyGradientGrowthClosed_proved,
      BKMVorticityEnstrophyLogSobolevGrowthClosed_proved,
      BKMLogSobolevGrowthEstimateClosed_proved,
      BKMAnalyticComponentsClosed.implies_finiteEnergyBKMContinuationTargetOnNonnegHorizons⟩

end BKMContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
