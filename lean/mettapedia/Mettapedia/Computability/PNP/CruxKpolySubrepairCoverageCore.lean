import Mettapedia.Computability.PNP.CruxKpolySubrepairClassCoreAliases
import Mettapedia.Computability.PNP.CruxKpolySubrepairClassActualLocalAliases
import Mettapedia.Computability.PNP.CruxKpolySubrepairClassBitFallbackAliases
import Mettapedia.Computability.PNP.CruxKpolySubrepairClassRecoveryAliases
import Mettapedia.Computability.PNP.CruxKpolySubrepairClassFiniteImageAliases
import Mettapedia.Computability.PNP.CruxKpolySubrepairClassObservedSupportAliases

/-!
# PNP `Kpoly` core/exact-visible subrepair coverage

The core block records exact-visible, raw `(a,b)`, shared `(a,b)`, and first
actual-local boundary subrepairs already covered by the current stack.
-/

namespace Mettapedia.Computability.PNP

/-- Core exact-visible and raw/shared `(a,b)` `Kpoly` subrepairs covered by the current stack. -/
def currentPNPKpolyCoreCoveredSubrepairs : List PNPKpolySubrepairClass :=
  [.clockWrapperEquivalence,
    .rawABDecisionListFullRuleObstruction,
    .rawABDecisionListExactPullbackObstruction,
    .sharedABAffineFeatureFullRuleObstruction,
    .sharedABSparseThresholdFullRuleObstruction,
    .sharedABDecisionListFullRuleObstruction,
    .sharedExactABAffineFeaturePullbackObstruction,
    .sharedExactABSparseThresholdPullbackObstruction,
    .sharedExactABDecisionListPullbackObstruction,
    .sharedABFeatureInjectiveProbeImageObstruction,
    .sharedExactABFeatureInjectiveProbePullbackObstruction,
    .abVisibleInvariantPointTargetObstruction,
    .abVisibleInvariantSupportDisagreementObstruction,
    .abVisibleInvariantExactSurfaceSurjectivityObstruction,
    .exactVisibleImageBudgetEquivalence,
    .clockedFiniteLearningPayloadEquivalence,
    .exactZABERMClockedPayloadClosure,
    .bitVecZABERMClockedPayloadClosure,
    .equalityToBitVecZABERMClockedPayloadClosure,
    .exactZABBadCodeLargeRegionDisagreementBoundary,
    .actualLocalZABDecisionListVisibleCardGapLowerBound,
    .actualLocalZABDecisionListBitVecTruthTableGapObstruction,
    .surjectiveActualLocalSparseThresholdERMVisibleBudgetBoundary,
    .surjectiveActualLocalSparseThresholdERMVisibleWidthBoundary,
    .surjectiveActualLocalNoExtractorSparseThresholdERMVisibleWidthBoundary]

end Mettapedia.Computability.PNP
