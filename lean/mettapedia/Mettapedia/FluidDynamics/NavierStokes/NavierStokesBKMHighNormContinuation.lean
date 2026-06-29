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

/-- Sharper analytic log-Sobolev/Biot-Savart ingredient in the conventional
affine form: from BKM vorticity-envelope data, produce constants and a
nonnegative high-norm envelope satisfying
`||grad u|| <= C0 + C1 * Omega log(exp(1) + H)`.

The checked algebra in `NavierStokesBKMLogSobolevControl` normalizes this into
the one-constant gradient envelope used downstream. -/
def BKMLogSobolevAffinePointwiseFromEnvelope : Prop :=
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
                    ∃ C0 : ℝ, ∃ C1 : ℝ, ∃ H : NSTime → ℝ,
                      0 ≤ C0 ∧
                        0 ≤ C1 ∧
                          (∀ t, 0 ≤ t → t ≤ T → 0 ≤ H t) ∧
                            BKMLogSobolevAffinePointwiseInequalityOn
                              W.velocity T C0 C1 Ω H

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

/-- The sharper affine pointwise log-Sobolev component implies the older
one-constant gradient-control component. -/
theorem BKMLogSobolevGradientControlFromEnvelope_of_affinePointwiseFromEnvelope
    (hAffine : BKMLogSobolevAffinePointwiseFromEnvelope) :
    BKMLogSobolevGradientControlFromEnvelope := by
  intro ν u₀ T W Ω B hT hν hsmooth hdiv hfinite hEq hΩ hInt
  rcases hAffine ν u₀ T W Ω B hT hν hsmooth hdiv hfinite hEq hΩ hInt with
    ⟨C0, C1, H, hC0, hC1, hH, hAffinePointwise⟩
  refine ⟨max C0 C1, H, ?_⟩
  exact
    BKMLogSobolevGradientControlOn.of_affinePointwiseInequality_max
      hC0 hC1 hΩ.1 hH hAffinePointwise

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

/-- Componentized BKM route with the log-Sobolev ingredient stated in the
conventional affine pointwise form. -/
def BKMAffineLogSobolevAnalyticComponentsClosed : Prop :=
  BKMResidualCurlExpansionDefectVanishes ∧
    BKMLogSobolevAffinePointwiseFromEnvelope ∧
      BKMHighNormContinuationFromLogControl

/-- The affine-log component bundle implies the older component bundle. -/
theorem BKMAffineLogSobolevAnalyticComponentsClosed.implies_BKMAnalyticComponentsClosed
    (h : BKMAffineLogSobolevAnalyticComponentsClosed) :
    BKMAnalyticComponentsClosed := by
  exact
    ⟨h.1,
      BKMLogSobolevGradientControlFromEnvelope_of_affinePointwiseFromEnvelope h.2.1,
      h.2.2⟩

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

/-- The affine-log component bundle implies the repaired nonnegative-horizon
BKM target through the checked affine normalization. -/
theorem BKMAffineLogSobolevAnalyticComponentsClosed.implies_finiteEnergyBKMContinuationTargetOnNonnegHorizons
    (h : BKMAffineLogSobolevAnalyticComponentsClosed) :
    ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons :=
  BKMAnalyticComponentsClosed.implies_finiteEnergyBKMContinuationTargetOnNonnegHorizons
    (BKMAffineLogSobolevAnalyticComponentsClosed.implies_BKMAnalyticComponentsClosed h)

/-- Route-facing packet: the local BKM estimates are checked, and the remaining
target follows from the componentized analytic ingredients. -/
theorem BKMContinuation_reduced_to_analytic_components :
    BKMVorticityStretchingEstimateClosed ∧
      BKMResidualCurlExpansionAlgebraClosed ∧
        BKMStandardVorticityGrowthEstimateClosed ∧
          BKMVorticityPointwiseEnstrophyDerivativeClosed ∧
            BKMVorticityRawBalanceFromStandardEquationClosed ∧
              BKMVorticityTransportCancellationAlgebraClosed ∧
                BKMVorticityTransportCancellationSchwartzClosed ∧
                  BKMVorticityDiffusionIntegrationByPartsSchwartzClosed ∧
                    BKMVorticityFiniteTimeWitnessSchwartzSliceAprioriClosed ∧
                      BKMVorticityFiniteTimeWitnessVelocityVorticitySchwartzAprioriClosed ∧
                        BKMVorticityFiniteTimeWitnessVelocitySchwartzAprioriClosed ∧
                          BKMVorticityEnstrophyBalanceAssemblyClosed ∧
                            BKMVorticityEnstrophyAprioriEstimateClosed ∧
                                BKMVorticityEnstrophyGradientGrowthClosed ∧
                                BKMVorticityEnstrophyLogSobolevGrowthClosed ∧
                                  BKMVorticityEnstrophyAffineLogGrowthClosed ∧
                                    BKMVorticityFiniteTimeWitnessAffineLogGrowthClosed ∧
                                      BKMVorticityFiniteTimeWitnessVelocitySchwartzAffineLogGrowthClosed ∧
                                        BKMVorticityStretchingAffineLogIntegralBoundClosed ∧
                                          BKMLogSobolevAffineReductionClosed ∧
                                            BKMLogSobolevGrowthEstimateClosed ∧
                                              (BKMAnalyticComponentsClosed →
                                                ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons) ∧
                                                (BKMAffineLogSobolevAnalyticComponentsClosed →
                                                  ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons) := by
  exact
    ⟨BKMVorticityStretchingEstimateClosed_proved,
      BKMResidualCurlExpansionAlgebraClosed_proved,
      BKMStandardVorticityGrowthEstimateClosed_proved,
      BKMVorticityPointwiseEnstrophyDerivativeClosed_proved,
      BKMVorticityRawBalanceFromStandardEquationClosed_proved,
      BKMVorticityTransportCancellationAlgebraClosed_proved,
      BKMVorticityTransportCancellationSchwartzClosed_proved,
      BKMVorticityDiffusionIntegrationByPartsSchwartzClosed_proved,
      BKMVorticityFiniteTimeWitnessSchwartzSliceAprioriClosed_proved,
      BKMVorticityFiniteTimeWitnessVelocityVorticitySchwartzAprioriClosed_proved,
      BKMVorticityFiniteTimeWitnessVelocitySchwartzAprioriClosed_proved,
      BKMVorticityEnstrophyBalanceAssemblyClosed_proved,
      BKMVorticityEnstrophyAprioriEstimateClosed_proved,
      BKMVorticityEnstrophyGradientGrowthClosed_proved,
      BKMVorticityEnstrophyLogSobolevGrowthClosed_proved,
      BKMVorticityEnstrophyAffineLogGrowthClosed_proved,
      BKMVorticityFiniteTimeWitnessAffineLogGrowthClosed_proved,
      BKMVorticityFiniteTimeWitnessVelocitySchwartzAffineLogGrowthClosed_proved,
      BKMVorticityStretchingAffineLogIntegralBoundClosed_proved,
      BKMLogSobolevAffineReductionClosed_proved,
      BKMLogSobolevGrowthEstimateClosed_proved,
      BKMAnalyticComponentsClosed.implies_finiteEnergyBKMContinuationTargetOnNonnegHorizons,
      BKMAffineLogSobolevAnalyticComponentsClosed.implies_finiteEnergyBKMContinuationTargetOnNonnegHorizons⟩

end BKMContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
