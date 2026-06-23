import Mettapedia.Computability.PNP.CruxKpolySubrepairClassCoreAliases
import Mettapedia.Computability.PNP.CruxKpolySubrepairClassActualLocalAliases
import Mettapedia.Computability.PNP.CruxKpolySubrepairClassBitFallbackAliases
import Mettapedia.Computability.PNP.CruxKpolySubrepairClassRecoveryAliases
import Mettapedia.Computability.PNP.CruxKpolySubrepairClassFiniteImageAliases
import Mettapedia.Computability.PNP.CruxKpolySubrepairClassObservedSupportAliases

/-!
# PNP `Kpoly` actual-local recovery subrepair coverage

Recovery-threshold, payload, pairwise-agreement, and region-mass boundaries
covered by the current stack.
-/

namespace Mettapedia.Computability.PNP

/-- Actual-local recovery `Kpoly` subrepairs covered by the current stack. -/
def currentPNPKpolyRecoveryCoveredSubrepairs : List PNPKpolySubrepairClass :=
  [.surjectiveActualLocalJointRecoveryBoundary,
    .surjectiveActualLocalRecoveryVisibleWidthBoundary,
    .surjectiveActualLocalRecoveryLightestPointBoundary,
    .surjectiveActualLocalRecoveryUniformCardinalityThresholdBoundary,
    .actualLocalInjectiveRecoveryUniformCardinalityThresholdBoundary,
    .surjectiveActualLocalRecoveryPayloadPredictorCardObstruction,
    .surjectiveActualLocalNoExtractorRecoveryPayloadPredictorCardObstruction,
    .actualLocalRecoveryPayloadInjectiveProbeCardObstruction,
    .actualLocalNoExtractorRecoveryPayloadInjectiveProbeCardObstruction,
    .fullRuleActualLocalRecoveryBitVecCardinalityThresholdBoundary,
    .actualLocalInjectiveRecoveryBitVecCardinalityThresholdBoundary,
    .fullRuleActualLocalNoExtractorRecoveryBitVecCardinalityThresholdObstruction,
    .actualLocalNoInjectiveExtractorRecoveryBitVecCardinalityThresholdObstruction,
    .fullRuleActualLocalRecoveryThresholdWidthBoundary,
    .fullRuleActualLocalNoExtractorRecoveryThresholdWidthObstruction,
    .boundedSamplePluginMajorityActualLocalRecoveryThresholdWidthBoundary,
    .boundedSamplePluginMajorityActualLocalNoExtractorRecoveryThresholdWidthObstruction,
    .fullRuleActualLocalRecoveryThresholdVisibleBudgetBoundary,
    .fullRuleActualLocalNoExtractorRecoveryThresholdVisibleBudgetObstruction,
    .boundedSamplePluginMajorityActualLocalRecoveryThresholdVisibleBudgetBoundary,
    .boundedSamplePluginMajorityActualLocalNoExtractorRecoveryThresholdVisibleBudgetObstruction,
    .actualLocalRecoveryPairwiseAgreementBoundary,
    .actualLocalNoExtractorRecoveryPairwiseAgreementObstruction,
    .surjectiveActualLocalRecoveryProperRegionMassBoundary,
    .surjectiveActualLocalNoExtractorProperRegionMassBoundary,
    .actualLocalRecoveryHeavyRegionTraceCardBoundary,
    .actualLocalNoExtractorRecoveryHeavyRegionTraceCardObstruction,
    .surjectiveActualLocalNoExtractorLightestPointBoundary,
    .surjectiveActualLocalNoExtractorVisibleWidthBoundary]

end Mettapedia.Computability.PNP
