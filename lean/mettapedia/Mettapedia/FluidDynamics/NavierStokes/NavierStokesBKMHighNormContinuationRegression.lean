import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMHighNormContinuation

/-!
# Regression checks for the BKM high-norm continuation assembly
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section BKMContinuation

theorem BKMLogSobolevGradientControlFromEnvelope_of_affinePointwiseFromEnvelope_regression
    (hAffine : BKMLogSobolevAffinePointwiseFromEnvelope) :
    BKMLogSobolevGradientControlFromEnvelope := by
  exact BKMLogSobolevGradientControlFromEnvelope_of_affinePointwiseFromEnvelope hAffine

theorem BKMLogSobolevAffinePointwiseFromEnvelope_of_schwartzHighNormEnvelope_and_biotSavart_regression
    (hHighNorm : BKMFiniteTimeWitnessSchwartzHighNormEnvelopeFromBKMData)
    (hBiotSavart : BKMSchwartzSliceBiotSavartAffineLogPointwiseEstimate) :
    BKMLogSobolevAffinePointwiseFromEnvelope := by
  exact
    BKMLogSobolevAffinePointwiseFromEnvelope_of_schwartzHighNormEnvelope_and_biotSavart
      hHighNorm hBiotSavart

theorem BKMAnalyticContinuationLemma_of_components_regression
    (hDefect : BKMResidualCurlExpansionDefectVanishes)
    (hLog : BKMLogSobolevGradientControlFromEnvelope)
    (hHigh : BKMHighNormContinuationFromLogControl) :
    BKMAnalyticContinuationLemma := by
  exact BKMAnalyticContinuationLemma_of_components hDefect hLog hHigh

theorem BKMAffineLogSobolevAnalyticComponentsClosed_implies_BKMAnalyticComponentsClosed_regression
    (h : BKMAffineLogSobolevAnalyticComponentsClosed) :
    BKMAnalyticComponentsClosed := by
  exact h.implies_BKMAnalyticComponentsClosed

theorem BKMAnalyticComponentsClosed_implies_BKMAnalyticContinuationLemma_regression
    (h : BKMAnalyticComponentsClosed) :
    BKMAnalyticContinuationLemma := by
  exact h.implies_BKMAnalyticContinuationLemma

theorem BKMAnalyticComponentsClosed_implies_finiteEnergyBKMContinuationTargetOnNonnegHorizons_regression
    (h : BKMAnalyticComponentsClosed) :
    ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons := by
  exact h.implies_finiteEnergyBKMContinuationTargetOnNonnegHorizons

theorem BKMAffineLogSobolevAnalyticComponentsClosed_implies_finiteEnergyBKMContinuationTargetOnNonnegHorizons_regression
    (h : BKMAffineLogSobolevAnalyticComponentsClosed) :
    ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons := by
  exact h.implies_finiteEnergyBKMContinuationTargetOnNonnegHorizons

theorem BKMArbitraryWitnessAffineLogBiotSavartGronwallContinuationLemma_of_components_regression
    (hAffine : BKMLogSobolevAffinePointwiseFromEnvelope)
    (hHigh : BKMHighNormContinuationFromLogControl) :
    BKMArbitraryWitnessAffineLogBiotSavartGronwallContinuationLemma := by
  exact
    BKMArbitraryWitnessAffineLogBiotSavartGronwallContinuationLemma_of_components
      hAffine hHigh

theorem BKMArbitraryWitnessAffineLogBiotSavartGronwallContinuationLemma_implies_finiteEnergyBKMContinuationTargetOnNonnegHorizons_regression
    (hDefect : BKMResidualCurlExpansionDefectVanishes)
    (h : BKMArbitraryWitnessAffineLogBiotSavartGronwallContinuationLemma) :
    ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons := by
  exact h.implies_finiteEnergyBKMContinuationTargetOnNonnegHorizons hDefect

theorem normalizedVorticityEnstrophyAt_le_gronwallBound_of_gradientControlled_constant_regression
    {ν G T : ℝ} {u : NSVelocityField}
    (hcont :
      ContinuousOn (fun t => normalizedVorticityEnstrophyAt u t)
        (Set.Icc 0 T))
    (hGrowth :
      ∀ t, t ∈ Set.Ico 0 T →
        vorticityEnstrophyGradientControlledAt ν u t G) :
    ∀ t, t ∈ Set.Icc 0 T →
      normalizedVorticityEnstrophyAt u t ≤
        gronwallBound (normalizedVorticityEnstrophyAt u 0) (2 * G) 0 (t - 0) := by
  exact
    normalizedVorticityEnstrophyAt_le_gronwallBound_of_gradientControlled_constant
      hcont hGrowth

theorem normalizedVorticityEnstrophyAt_le_gronwallBound_of_gradientControlled_majorized_regression
    {ν K T : ℝ} {u : NSVelocityField} {G : NSTime → ℝ}
    (hcont :
      ContinuousOn (fun t => normalizedVorticityEnstrophyAt u t)
        (Set.Icc 0 T))
    (hGrowth :
      ∀ t, t ∈ Set.Ico 0 T →
        vorticityEnstrophyGradientControlledAt ν u t (G t))
    (hGle : ∀ t, t ∈ Set.Ico 0 T → G t ≤ K) :
    ∀ t, t ∈ Set.Icc 0 T →
      normalizedVorticityEnstrophyAt u t ≤
        gronwallBound (normalizedVorticityEnstrophyAt u 0) (2 * K) 0 (t - 0) := by
  exact
    normalizedVorticityEnstrophyAt_le_gronwallBound_of_gradientControlled_majorized
      hcont hGrowth hGle

theorem normalizedVorticityEnstrophyAt_mul_exp_neg_antiderivative_le_initial_regression
    {ν T : ℝ} {u : NSVelocityField} {G A : NSTime → ℝ}
    (hcont :
      ContinuousOn (fun t => normalizedVorticityEnstrophyAt u t)
        (Set.Icc 0 T))
    (hAcont : ContinuousOn A (Set.Icc 0 T))
    (hAderiv :
      ∀ t, t ∈ Set.Ico 0 T →
        HasDerivWithinAt A (2 * G t) (Set.Ici t) t)
    (hGrowth :
      ∀ t, t ∈ Set.Ico 0 T →
        vorticityEnstrophyGradientControlledAt ν u t (G t)) :
    ∀ t, t ∈ Set.Icc 0 T →
      normalizedVorticityEnstrophyAt u t * Real.exp (-(A t)) ≤
        normalizedVorticityEnstrophyAt u 0 * Real.exp (-(A 0)) := by
  exact
    normalizedVorticityEnstrophyAt_mul_exp_neg_antiderivative_le_initial
      hcont hAcont hAderiv hGrowth

theorem normalizedVorticityEnstrophyAt_le_initial_mul_exp_antiderivative_regression
    {ν T : ℝ} {u : NSVelocityField} {G A : NSTime → ℝ}
    (hcont :
      ContinuousOn (fun t => normalizedVorticityEnstrophyAt u t)
        (Set.Icc 0 T))
    (hAcont : ContinuousOn A (Set.Icc 0 T))
    (hAderiv :
      ∀ t, t ∈ Set.Ico 0 T →
        HasDerivWithinAt A (2 * G t) (Set.Ici t) t)
    (hGrowth :
      ∀ t, t ∈ Set.Ico 0 T →
        vorticityEnstrophyGradientControlledAt ν u t (G t)) :
    ∀ t, t ∈ Set.Icc 0 T →
      normalizedVorticityEnstrophyAt u t ≤
        normalizedVorticityEnstrophyAt u 0 * Real.exp (A t - A 0) := by
  exact
    normalizedVorticityEnstrophyAt_le_initial_mul_exp_antiderivative
      hcont hAcont hAderiv hGrowth

theorem BKMContinuation_reduced_to_analytic_components_regression :
    BKMVorticityStretchingEstimateClosed ∧
      BKMResidualCurlExpansionAlgebraClosed ∧
        BKMStandardVorticityGrowthEstimateClosed ∧
          BKMVorticityPointwiseEnstrophyDerivativeClosed ∧
            BKMVorticityRawBalanceIntegrabilitySchwartzClosed ∧
              BKMVorticityScalarSchwartzTimePairingDerivativeClosed ∧
                BKMVorticityTwoProfileSchwartzTimePairingDerivativeClosed ∧
                  BKMVorticityRawBalanceFromStandardEquationClosed ∧
                    BKMVorticityTransportCancellationAlgebraClosed ∧
                      BKMVorticityTransportCancellationSchwartzClosed ∧
                        BKMVorticityDiffusionIntegrationByPartsSchwartzClosed ∧
                          BKMVorticityFiniteTimeWitnessVelocitySchwartzEnstrophyIntegrableClosed ∧
                            BKMVorticityFiniteTimeWitnessVelocitySchwartzRawBalanceIntegrabilityClosed ∧
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
  exact BKMContinuation_reduced_to_analytic_components

end BKMContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
