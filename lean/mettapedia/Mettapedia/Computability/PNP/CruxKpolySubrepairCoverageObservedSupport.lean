import Mettapedia.Computability.PNP.CruxKpolySubrepairClassCoreAliases
import Mettapedia.Computability.PNP.CruxKpolySubrepairClassActualLocalAliases
import Mettapedia.Computability.PNP.CruxKpolySubrepairClassBitFallbackAliases
import Mettapedia.Computability.PNP.CruxKpolySubrepairClassRecoveryAliases
import Mettapedia.Computability.PNP.CruxKpolySubrepairClassFiniteImageAliases
import Mettapedia.Computability.PNP.CruxKpolySubrepairClassObservedSupportAliases

/-!
# PNP `Kpoly` observed-support subrepair coverage

Observed-output support, decoder, query, adaptive-query, and one-block
subrepairs covered by the current stack.
-/

namespace Mettapedia.Computability.PNP

/-- Observed-support and one-block `Kpoly` subrepairs covered by the current stack. -/
def currentPNPKpolyObservedSupportCoveredSubrepairs : List PNPKpolySubrepairClass :=
  [.supportFullRuleObservedSmallNotExactVisibleCoverBoundary,
    .supportFullRuleNotClockedPayloadBelowSurfaceCard,
    .supportFullRuleUniformSectionFinitePredictorCoverBoundary,
    .supportFullRuleUniformSectionClockedPayloadBoundary,
    .supportFullRuleUniformSectionSurfaceCardBoundary,
    .supportFullRuleNoUniformSectionBelowSurfaceCard,
    .supportFullRuleOutputFamilyFactorBoundary,
    .supportFullRuleObservedRuleInjectiveSurjectiveBoundary,
    .supportFullRuleExactDecoderSurjectiveBoundary,
    .supportFullRuleObservedRuleMapNoninjectiveBelowSurfaceCard,
    .supportFullRuleDistinctRulesSameOutputBelowSurfaceCard,
    .supportFullRulePropertyDecoderFiberConstancyBoundary,
    .supportFullRulePropertyDecoderIffFiberConstancyBoundary,
    .supportFullRuleNoPropertyDecoderSameOutputBoundary,
    .supportFullRuleEvalDecoderRangeBoundary,
    .supportFullRuleAllEvalDecodersSurjectiveBoundary,
    .supportFullRuleQueryDecoderRangeBoundary,
    .supportFullRuleNoQueryDecoderMissedQueryBoundary,
    .supportFullRuleAdaptiveQueryDecoderReachableBoundary,
    .supportFullRuleAdaptiveQueryDecoderIffFiberConstancyBoundary,
    .supportFullRuleNoAdaptiveQueryDecoderSameOutputEvalBoundary,
    .supportFullRuleNoRootAdaptiveQueryDecoderMissedPointBoundary,
    .supportFullRuleNoExactDecoderBelowSurfaceCard,
    .supportFullRuleUnobservableEvalBelowSurfaceCard,
    .oneBlockFullRuleObservedSmallNotExactVisibleCoverBoundary,
    .oneBlockFullRuleNotClockedPayloadBelowSurfaceCard,
    .oneBlockFullRuleNoExactDecoderOneLtSurfaceCardBoundary,
    .oneBlockFullRuleUnobservableEvalOneLtSurfaceCardBoundary]

end Mettapedia.Computability.PNP
