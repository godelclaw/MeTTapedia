import Mettapedia.Computability.PNP.CruxKpolySubrepairClassBase
/-!
# Legacy flat names for PNP `Kpoly` actual-local support subrepair classes

This module keeps the historical `PNPKpolySubrepairClass.foo` names while
the semantic class family lives in `PNPKpolyActualLocalSubrepairClass`.
-/

namespace Mettapedia.Computability.PNP

namespace PNPKpolySubrepairClass

  /-- The bare exact-visible family interface alone cannot imply clocked
  finite-learning payloads for all families below the full visible surface. -/
abbrev bareExactVisibleInterfacePayloadInsufficiency : PNPKpolySubrepairClass :=
  .actualLocal .bareExactVisibleInterfacePayloadInsufficiency
  /-- A small observed actual-local block-output image does not imply a small
  exact-visible local-rule image. -/
abbrev actualObservedSupportPayloadInsufficiency : PNPKpolySubrepairClass :=
  .actualLocal .actualObservedSupportPayloadInsufficiency
  /-- Observed actual-local output compression transfers to full exact-visible
  compression only with a uniform visible section; the finite-support full-rule
  construction cannot supply one below the full exact-visible surface size. -/
abbrev actualObservedSupportUniformSectionBoundary : PNPKpolySubrepairClass :=
  .actualLocal .actualObservedSupportUniformSectionBoundary
  /-- A reachable-support quotient only records restriction along `visibleOf`;
  below surface cardinality it identifies distinct exact-visible rules. -/
abbrev actualObservedSupportQuotientLossBoundary : PNPKpolySubrepairClass :=
  .actualLocal .actualObservedSupportQuotientLossBoundary
  /-- No decoder from observed block-output traces can reconstruct all full
  exact-visible rules unless the reachable support hits the whole surface. -/
abbrev actualObservedSupportDecoderRecoveryBoundary : PNPKpolySubrepairClass :=
  .actualLocal .actualObservedSupportDecoderRecoveryBoundary
  /-- Any downstream property decoded from observed block traces must be
  constant on observed-output fibers; off-support exact-visible bits are not
  observable below full support. -/
abbrev actualObservedSupportObservablePropertyBoundary : PNPKpolySubrepairClass :=
  .actualLocal .actualObservedSupportObservablePropertyBoundary
  /-- A downstream property factors through observed block traces exactly when
  it is constant on observed-output fibers. -/
abbrev actualObservedSupportPropertyFactorBoundary : PNPKpolySubrepairClass :=
  .actualLocal .actualObservedSupportPropertyFactorBoundary
  /-- Exact-visible point queries are observable from block traces exactly at
  points in the reachable support; all point queries force full support
  surjectivity. -/
abbrev actualObservedSupportPointQueryBoundary : PNPKpolySubrepairClass :=
  .actualLocal .actualObservedSupportPointQueryBoundary
  /-- A whole family of exact-visible point queries is decodable from observed
  traces exactly when every queried point lies in reachable support. -/
abbrev actualObservedSupportQueryFamilyBoundary : PNPKpolySubrepairClass :=
  .actualLocal .actualObservedSupportQueryFamilyBoundary
  /-- Adaptive point-query trees over exact-visible points still factor
  through observed traces exactly by quotient constancy, and missed root
  queries with distinct branches are impossible to decode. -/
abbrev actualObservedSupportAdaptiveQueryBoundary : PNPKpolySubrepairClass :=
  .actualLocal .actualObservedSupportAdaptiveQueryBoundary
  /-- An unrestricted plug-in lookup endpoint over the exact visible alphabet
  is still the full Boolean rule family, not a small-image `Kpoly` bridge. -/
abbrev actualLocalPluginLookupFullRuleObstruction : PNPKpolySubrepairClass :=
  .actualLocal .actualLocalPluginLookupFullRuleObstruction
  /-- Unrestricted per-input plug-in majority counts still realize every
  Boolean rule on the exact visible alphabet. -/
abbrev actualLocalPluginMajorityFullRuleObstruction : PNPKpolySubrepairClass :=
  .actualLocal .actualLocalPluginMajorityFullRuleObstruction
  /-- Sample-level plug-in majority still realizes every Boolean rule via the
  graph sample unless the samples are further restricted. -/
abbrev actualLocalPluginSampleMajorityFullRuleObstruction : PNPKpolySubrepairClass :=
  .actualLocal .actualLocalPluginSampleMajorityFullRuleObstruction
  /-- Unrestricted sample-level plug-in majority still cannot be identified
  with one shared sparse-threshold ERM family, nor carry its stronger recovery
  packet, below the point-block visible-budget threshold. -/
abbrev actualLocalPluginSampleMajoritySparseThresholdERMVisibleBudgetBoundary : PNPKpolySubrepairClass :=
  .actualLocal .actualLocalPluginSampleMajoritySparseThresholdERMVisibleBudgetBoundary
  /-- Bounded sample-level plug-in majority is full-rule expressive exactly
  when the sample bound reaches the exact visible alphabet size. -/
abbrev actualLocalBoundedSampleMajorityThresholdBoundary : PNPKpolySubrepairClass :=
  .actualLocal .actualLocalBoundedSampleMajorityThresholdBoundary
  /-- Bounded sample-level plug-in majority can be false only on sampled exact
  visible inputs, so target rules with too-large false support are not
  realizable. -/
abbrev actualLocalBoundedSampleMajorityFalseSupportBoundary : PNPKpolySubrepairClass :=
  .actualLocal .actualLocalBoundedSampleMajorityFalseSupportBoundary
  /-- Changing the bounded sample-level plug-in majority tie-break does not
  change the cardinal threshold: only sampled inputs can differ from the
  chosen default. -/
abbrev actualLocalBoundedSampleMajorityDefaultTieBoundary : PNPKpolySubrepairClass :=
  .actualLocal .actualLocalBoundedSampleMajorityDefaultTieBoundary
  /-- An input-dependent tie fallback for bounded sample-level plug-in majority
  is already a full exact-visible lookup table, even with the empty sample. -/
abbrev actualLocalBoundedSampleMajorityFallbackSideChannelBoundary : PNPKpolySubrepairClass :=
  .actualLocal .actualLocalBoundedSampleMajorityFallbackSideChannelBoundary
  /-- That same full-rule fallback side channel still has no small finite
  predictor-image cover below the full exact-visible Boolean rule cube. -/
abbrev actualLocalBoundedSampleMajorityFallbackFinitePredictorCoverObstruction : PNPKpolySubrepairClass :=
  .actualLocal .actualLocalBoundedSampleMajorityFallbackFinitePredictorCoverObstruction
  /-- That same full-rule fallback side channel still has no finite selected-
  index representative cover below the full exact-visible Boolean rule cube. -/
abbrev actualLocalBoundedSampleMajorityFallbackFiniteIndexRepresentativeCoverObstruction : PNPKpolySubrepairClass :=
  .actualLocal .actualLocalBoundedSampleMajorityFallbackFiniteIndexRepresentativeCoverObstruction
  /-- The same full-rule fallback side channel also has no finite quotient-code
  presentation below the full exact-visible Boolean rule cube. -/
abbrev actualLocalBoundedSampleMajorityFallbackFinitePredictorQuotientObstruction : PNPKpolySubrepairClass :=
  .actualLocal .actualLocalBoundedSampleMajorityFallbackFinitePredictorQuotientObstruction
  /-- The same fallback side channel therefore admits no exact-visible
  compression target below the full exact-visible Boolean rule cube. -/
abbrev actualLocalBoundedSampleMajorityFallbackExactVisibleCompressionObstruction : PNPKpolySubrepairClass :=
  .actualLocal .actualLocalBoundedSampleMajorityFallbackExactVisibleCompressionObstruction
  /-- The same fallback side channel also admits no clocked exact-visible
  realization below the full exact-visible Boolean rule cube. -/
abbrev actualLocalBoundedSampleMajorityFallbackClockedRealizationObstruction : PNPKpolySubrepairClass :=
  .actualLocal .actualLocalBoundedSampleMajorityFallbackClockedRealizationObstruction
  /-- The same fallback side channel cannot provide the full clocked finite-
  learning payload below the full exact-visible Boolean rule cube either. -/
abbrev actualLocalBoundedSampleMajorityFallbackClockedPayloadObstruction : PNPKpolySubrepairClass :=
  .actualLocal .actualLocalBoundedSampleMajorityFallbackClockedPayloadObstruction
  /-- If the input-dependent fallback is restricted to a structured fallback
  family, bounded samples only produce sparse point changes from the selected
  fallback rule. -/
abbrev actualLocalBoundedSampleMajorityFallbackFamilySparseBoundary : PNPKpolySubrepairClass :=
  .actualLocal .actualLocalBoundedSampleMajorityFallbackFamilySparseBoundary
  /-- For any structured fallback code, the empty sampled override set realizes
  that fallback rule exactly. -/
abbrev actualLocalBoundedSampleMajorityFallbackFamilyEmptySampleRealizationBoundary : PNPKpolySubrepairClass :=
  .actualLocal .actualLocalBoundedSampleMajorityFallbackFamilyEmptySampleRealizationBoundary
  /-- If every structured fallback code disagrees with a target rule on more
  than `sampleBound` surface points, bounded samples cannot realize that rule
  at all. -/
abbrev actualLocalBoundedSampleMajorityFallbackFamilyLargeDisagreementSupportObstruction : PNPKpolySubrepairClass :=
  .actualLocal .actualLocalBoundedSampleMajorityFallbackFamilyLargeDisagreementSupportObstruction
  /-- For a structured fallback family, a target rule is realizable exactly
  when it lies in the radius-`sampleBound` Hamming cover of the fallback
  codes. -/
abbrev actualLocalBoundedSampleMajorityFallbackFamilyRadiusCoverBoundary : PNPKpolySubrepairClass :=
  .actualLocal .actualLocalBoundedSampleMajorityFallbackFamilyRadiusCoverBoundary
  /-- The same structured fallback-family endpoint has predictor image covered
  by at most `|FallbackIndex| * |smallSubsets surface sampleBound|` rules. -/
abbrev actualLocalBoundedSampleMajorityFallbackFamilyFinitePredictorCoverBoundary : PNPKpolySubrepairClass :=
  .actualLocal .actualLocalBoundedSampleMajorityFallbackFamilyFinitePredictorCoverBoundary
  /-- Full-rule expressivity of the structured fallback-family endpoint is
  equivalent to the radius-`sampleBound` Hamming cover already filling the
  whole exact-visible Boolean rule cube. -/
abbrev actualLocalBoundedSampleMajorityFallbackFamilyRadiusCoverSurjectivityBoundary : PNPKpolySubrepairClass :=
  .actualLocal .actualLocalBoundedSampleMajorityFallbackFamilyRadiusCoverSurjectivityBoundary
  /-- Full-rule expressivity of the structured fallback-family endpoint is
  equivalently the pointwise condition that every exact-visible rule lie
  within disagreement radius `sampleBound` of some fallback code. -/
abbrev actualLocalBoundedSampleMajorityFallbackFamilyPointwiseRadiusCoverSurjectivityBoundary : PNPKpolySubrepairClass :=
  .actualLocal .actualLocalBoundedSampleMajorityFallbackFamilyPointwiseRadiusCoverSurjectivityBoundary
  /-- If a structured fallback family is already full-rule expressive, bounded
  samples preserve that full exact-visible expressivity. -/
abbrev actualLocalBoundedSampleMajorityFallbackFamilyFallbackSurjectiveBoundary : PNPKpolySubrepairClass :=
  .actualLocal .actualLocalBoundedSampleMajorityFallbackFamilyFallbackSurjectiveBoundary
  /-- Full-rule expressivity already forces the abstract fallback-family
  support product `|FallbackIndex| * |smallSubsets surface sampleBound|`. -/
abbrev actualLocalBoundedSampleMajorityFallbackFamilySmallSubsetsProductBoundary : PNPKpolySubrepairClass :=
  .actualLocal .actualLocalBoundedSampleMajorityFallbackFamilySmallSubsetsProductBoundary
  /-- The same abstract fallback-family support product blocks surjectivity
  whenever it stays strictly below the full exact-visible Boolean rule cube. -/
abbrev actualLocalBoundedSampleMajorityFallbackFamilySmallSubsetsProductSurjectivityObstruction : PNPKpolySubrepairClass :=
  .actualLocal .actualLocalBoundedSampleMajorityFallbackFamilySmallSubsetsProductSurjectivityObstruction
  /-- Once the sample bound reaches the exact-visible alphabet size, any
  nonempty structured fallback family is already full-rule expressive. -/
abbrev actualLocalBoundedSampleMajorityFallbackFamilyFullRadiusBoundary : PNPKpolySubrepairClass :=
  .actualLocal .actualLocalBoundedSampleMajorityFallbackFamilyFullRadiusBoundary
  /-- At zero sparse-support radius, the wrapper contributes no hidden
  expressivity: surjectivity of the endpoint is equivalent to surjectivity of
  the fallback family itself. -/
abbrev actualLocalBoundedSampleMajorityFallbackFamilyZeroSampleFallbackEquivalence : PNPKpolySubrepairClass :=
  .actualLocal .actualLocalBoundedSampleMajorityFallbackFamilyZeroSampleFallbackEquivalence
  /-- At zero sparse-support radius, the structured fallback wrapper has
  exactly the same finite predictor-image covers as the raw fallback family
  itself. -/
abbrev actualLocalBoundedSampleMajorityFallbackFamilyZeroSampleFinitePredictorCoverBoundary : PNPKpolySubrepairClass :=
  .actualLocal .actualLocalBoundedSampleMajorityFallbackFamilyZeroSampleFinitePredictorCoverBoundary
  /-- At zero sparse-support radius, the structured fallback wrapper has
  exactly the same finite selected-index representative covers as the raw
  fallback family itself. -/
abbrev actualLocalBoundedSampleMajorityFallbackFamilyZeroSampleFiniteIndexRepresentativeCoverBoundary : PNPKpolySubrepairClass :=
  .actualLocal .actualLocalBoundedSampleMajorityFallbackFamilyZeroSampleFiniteIndexRepresentativeCoverBoundary
  /-- At zero sparse-support radius, the structured fallback wrapper has
  exactly the same finite quotient-code presentations as the raw fallback
  family itself. -/
abbrev actualLocalBoundedSampleMajorityFallbackFamilyZeroSampleFinitePredictorQuotientBoundary : PNPKpolySubrepairClass :=
  .actualLocal .actualLocalBoundedSampleMajorityFallbackFamilyZeroSampleFinitePredictorQuotientBoundary
  /-- Radius-zero exact visible compression claims for the structured fallback
  wrapper are exactly the corresponding compression claims for the raw
  fallback family. -/
abbrev actualLocalBoundedSampleMajorityFallbackFamilyZeroSampleExactVisibleCompressionBoundary : PNPKpolySubrepairClass :=
  .actualLocal .actualLocalBoundedSampleMajorityFallbackFamilyZeroSampleExactVisibleCompressionBoundary
  /-- Radius-zero clocked exact-visible realization claims for the structured
  fallback wrapper are exactly the corresponding claims for the raw fallback
  family. -/
abbrev actualLocalBoundedSampleMajorityFallbackFamilyZeroSampleClockedRealizationBoundary : PNPKpolySubrepairClass :=
  .actualLocal .actualLocalBoundedSampleMajorityFallbackFamilyZeroSampleClockedRealizationBoundary
  /-- Radius-zero clocked finite-learning payload claims for the structured
  fallback wrapper are exactly the corresponding payload claims for the raw
  fallback family. -/
abbrev actualLocalBoundedSampleMajorityFallbackFamilyZeroSampleClockedPayloadBoundary : PNPKpolySubrepairClass :=
  .actualLocal .actualLocalBoundedSampleMajorityFallbackFamilyZeroSampleClockedPayloadBoundary

end PNPKpolySubrepairClass

end Mettapedia.Computability.PNP
