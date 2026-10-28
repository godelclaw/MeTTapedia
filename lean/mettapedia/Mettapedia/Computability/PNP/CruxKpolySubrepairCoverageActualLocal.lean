import Mettapedia.Computability.PNP.CruxKpolySubrepairClassCoreAliases
import Mettapedia.Computability.PNP.CruxKpolySubrepairClassActualLocalAliases
import Mettapedia.Computability.PNP.CruxKpolySubrepairClassBitFallbackAliases
import Mettapedia.Computability.PNP.CruxKpolySubrepairClassRecoveryAliases
import Mettapedia.Computability.PNP.CruxKpolySubrepairClassFiniteImageAliases
import Mettapedia.Computability.PNP.CruxKpolySubrepairClassObservedSupportAliases

/-!
# PNP `Kpoly` actual-local/support subrepair coverage

Actual-local support, plug-in, bounded-sample, and structured fallback
subrepairs covered by the current stack, before the bit-coded fallback layer.
-/

namespace Mettapedia.Computability.PNP

/-- Actual-local support and non-bit-coded fallback `Kpoly` subrepairs covered by the current stack. -/
def currentPNPKpolyActualLocalCoveredSubrepairs : List PNPKpolySubrepairClass :=
  [.bareExactVisibleInterfacePayloadInsufficiency,
    .actualObservedSupportPayloadInsufficiency,
    .actualObservedSupportUniformSectionBoundary,
    .actualObservedSupportQuotientLossBoundary,
    .actualObservedSupportDecoderRecoveryBoundary,
    .actualObservedSupportObservablePropertyBoundary,
    .actualObservedSupportPropertyFactorBoundary,
    .actualObservedSupportPointQueryBoundary,
    .actualObservedSupportQueryFamilyBoundary,
    .actualObservedSupportAdaptiveQueryBoundary,
    .actualLocalPluginLookupFullRuleObstruction,
    .actualLocalPluginMajorityFullRuleObstruction,
    .actualLocalPluginSampleMajorityFullRuleObstruction,
    .actualLocalPluginSampleMajoritySparseThresholdERMVisibleBudgetBoundary,
    .actualLocalBoundedSampleMajorityThresholdBoundary,
    .actualLocalBoundedSampleMajorityFalseSupportBoundary,
    .actualLocalBoundedSampleMajorityDefaultTieBoundary,
    .actualLocalBoundedSampleMajorityFallbackSideChannelBoundary,
    .actualLocalBoundedSampleMajorityFallbackFinitePredictorCoverObstruction,
    .actualLocalBoundedSampleMajorityFallbackFiniteIndexRepresentativeCoverObstruction,
    .actualLocalBoundedSampleMajorityFallbackFinitePredictorQuotientObstruction,
    .actualLocalBoundedSampleMajorityFallbackExactVisibleCompressionObstruction,
    .actualLocalBoundedSampleMajorityFallbackClockedRealizationObstruction,
    .actualLocalBoundedSampleMajorityFallbackClockedPayloadObstruction,
    .actualLocalBoundedSampleMajorityFallbackFamilySparseBoundary,
    .actualLocalBoundedSampleMajorityFallbackFamilyEmptySampleRealizationBoundary,
    .actualLocalBoundedSampleMajorityFallbackFamilyLargeDisagreementSupportObstruction,
    .actualLocalBoundedSampleMajorityFallbackFamilyRadiusCoverBoundary,
    .actualLocalBoundedSampleMajorityFallbackFamilyFinitePredictorCoverBoundary,
    .actualLocalBoundedSampleMajorityFallbackFamilyRadiusCoverSurjectivityBoundary,
    .actualLocalBoundedSampleMajorityFallbackFamilyPointwiseRadiusCoverSurjectivityBoundary,
    .actualLocalBoundedSampleMajorityFallbackFamilyFallbackSurjectiveBoundary,
    .actualLocalBoundedSampleMajorityFallbackFamilySmallSubsetsProductBoundary,
    .actualLocalBoundedSampleMajorityFallbackFamilySmallSubsetsProductSurjectivityObstruction,
    .actualLocalBoundedSampleMajorityFallbackFamilyFullRadiusBoundary,
    .actualLocalBoundedSampleMajorityFallbackFamilyZeroSampleFallbackEquivalence,
    .actualLocalBoundedSampleMajorityFallbackFamilyZeroSampleFinitePredictorCoverBoundary,
    .actualLocalBoundedSampleMajorityFallbackFamilyZeroSampleFiniteIndexRepresentativeCoverBoundary,
    .actualLocalBoundedSampleMajorityFallbackFamilyZeroSampleFinitePredictorQuotientBoundary,
    .actualLocalBoundedSampleMajorityFallbackFamilyZeroSampleExactVisibleCompressionBoundary,
    .actualLocalBoundedSampleMajorityFallbackFamilyZeroSampleClockedRealizationBoundary,
    .actualLocalBoundedSampleMajorityFallbackFamilyZeroSampleClockedPayloadBoundary]

end Mettapedia.Computability.PNP
