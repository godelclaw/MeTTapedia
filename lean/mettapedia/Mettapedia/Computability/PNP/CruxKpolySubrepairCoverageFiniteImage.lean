import Mettapedia.Computability.PNP.CruxKpolySubrepairClassCoreAliases
import Mettapedia.Computability.PNP.CruxKpolySubrepairClassActualLocalAliases
import Mettapedia.Computability.PNP.CruxKpolySubrepairClassBitFallbackAliases
import Mettapedia.Computability.PNP.CruxKpolySubrepairClassRecoveryAliases
import Mettapedia.Computability.PNP.CruxKpolySubrepairClassFiniteImageAliases
import Mettapedia.Computability.PNP.CruxKpolySubrepairClassObservedSupportAliases

/-!
# PNP `Kpoly` finite-image bridge subrepair coverage

Finite predictor-image, representative-index, quotient-code, factor-transport,
pullback, product-bound, and fielded-switching bridge subrepairs covered by the
current stack.
-/

namespace Mettapedia.Computability.PNP

/-- Finite-image and bridge-schema `Kpoly` subrepairs covered by the current stack. -/
def currentPNPKpolyFiniteImageCoveredSubrepairs : List PNPKpolySubrepairClass :=
  [.exactVisibleCompressionTargetPredictorCoverEquivalence,
    .clockedExactVisibleRealizationPredictorCoverEquivalence,
    .clockedFiniteLearningPayloadPredictorCoverEquivalence,
    .clockedFiniteLearningPayloadExactVisibleCompressionEquivalence,
    .finitePredictorQuotientEquivalence,
    .exactVisibleCompressionTargetPredictorQuotientEquivalence,
    .clockedExactVisibleRealizationPredictorQuotientEquivalence,
    .exactVisibleCompressionTargetRepresentativeIndexCoverEquivalence,
    .clockedExactVisibleRealizationRepresentativeIndexCoverEquivalence,
    .notClockedExactVisibleRealizationRepresentativeIndexCoverEquivalence,
    .notClockedExactVisibleRealizationPredictorQuotientEquivalence,
    .exactVisibleImageSurjectivityObstruction,
    .exactVisibleRepresentativeCoverSurjectivityObstruction,
    .exactVisiblePredictorQuotientSurjectivityObstruction,
    .exactVisibleClockedRealizationSurjectivityObstruction,
    .injectiveFiniteProbeImageLowerBound,
    .injectiveFiniteRepresentativeIndexCoverLowerBound,
    .injectiveFinitePredictorQuotientLowerBound,
    .injectiveFiniteProbeExactVisibleCompressionObstruction,
    .injectiveFiniteProbeClockedRealizationObstruction,
    .exactVisibleClockedFiniteLearningPayloadSurjectivityObstruction,
    .injectiveFiniteProbeClockedFiniteLearningPayloadObstruction,
    .clockedFiniteLearningPayloadImageObstruction,
    .exactVisibleClockedFiniteLearningPayloadSurjectivityLowerBound,
    .injectiveFiniteProbeClockedFiniteLearningPayloadLowerBound,
    .sectionBackedClockedFiniteLearningPayloadSurjectiveLowerBound,
    .sectionBackedClockedFiniteLearningPayloadSurjectiveObstruction,
    .sectionBackedInjectiveFiniteProbeClockedFiniteLearningPayloadLowerBound,
    .sectionBackedInjectiveFiniteProbeClockedFiniteLearningPayloadObstruction,
    .sectionBackedInjectiveFiniteProbePullbackLowerBound,
    .sectionBackedInjectiveFiniteProbePullbackObstruction,
    .sectionBackedInjectiveFiniteRepresentativeIndexCoverLowerBound,
    .sectionBackedInjectiveFiniteRepresentativeIndexCoverObstruction,
    .sectionBackedInjectiveFinitePredictorQuotientLowerBound,
    .sectionBackedInjectiveFinitePredictorQuotientObstruction,
    .finiteRepresentativeIndexCoverEquivalence,
    .finiteImageCoverBudgetWeakening,
    .finitePredictorCoverBudgetWeakeningBoundary,
    .finiteRepresentativeIndexCoverBudgetWeakeningBoundary,
    .finitePredictorQuotientBudgetWeakeningBoundary,
    .finiteImageCoverFactorTransport,
    .finitePredictorCoverFactorTransportBoundary,
    .finiteRepresentativeIndexCoverFactorTransportBoundary,
    .finitePredictorQuotientFactorTransportBoundary,
    .sectionBackedFinitePredictorCoverSurjectiveObstruction,
    .sectionBackedFiniteRepresentativeIndexCoverSurjectiveObstruction,
    .sectionBackedFinitePredictorQuotientSurjectiveObstruction,
    .sectionBackedFinitePredictorCoverSurjectiveLowerBound,
    .sectionBackedFiniteRepresentativeIndexCoverSurjectiveLowerBound,
    .sectionBackedFinitePredictorQuotientSurjectiveLowerBound,
    .surjectiveFinitePredictorCoverLowerBound,
    .surjectiveFiniteRepresentativeIndexCoverLowerBound,
    .surjectiveFinitePredictorQuotientLowerBound,
    .finiteImageReducedABPullbackObstruction,
    .finiteImageReducedABInjectiveProbePullbackObstruction,
    .finiteQuotientReducedABPullbackObstruction,
    .productBoundBridgeFiniteImageBoundary,
    .fieldedSwitchingBridgeFiniteImageBoundary,
    .productBoundOnlyFullVisibleObstruction,
    .fieldedSwitchingOnlyFullVisibleObstruction,
    .productBoundOnlySurjectiveVisibleObstruction,
    .fieldedSwitchingOnlySurjectiveVisibleObstruction,
    .productBoundClockedPayloadBridgeFiniteImageBoundary,
    .fieldedSwitchingClockedPayloadBridgeFiniteImageBoundary,
    .productBoundOnlyClockedPayloadFullVisibleObstruction,
    .fieldedSwitchingOnlyClockedPayloadFullVisibleObstruction,
    .productBoundOnlyClockedPayloadSurjectiveVisibleObstruction,
    .fieldedSwitchingOnlyClockedPayloadSurjectiveVisibleObstruction,
    .actualSwitchedHistoryBitVecFullWidthIntervalObstruction,
    .actualSwitchedHistoryBitVecFullWidthIntervalClockedPayloadObstruction]

end Mettapedia.Computability.PNP
