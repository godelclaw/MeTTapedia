import Mettapedia.Computability.PNP.CruxLedger
/-!
# PNP `Kpoly` actual-local support subrepair classes

Actual-local support, observed-support, plug-in, bounded-sample, and structured fallback subrepair classes before the bit-coded fallback layer.
-/

namespace Mettapedia.Computability.PNP

/-- Actual-local support, observed-support, plug-in, bounded-sample, and structured fallback subrepair classes before the bit-coded fallback layer. -/
inductive PNPKpolyActualLocalSubrepairClass where
  /-- The bare exact-visible family interface alone cannot imply clocked
  finite-learning payloads for all families below the full visible surface. -/
  | bareExactVisibleInterfacePayloadInsufficiency
  /-- A small observed actual-local block-output image does not imply a small
  exact-visible local-rule image. -/
  | actualObservedSupportPayloadInsufficiency
  /-- Observed actual-local output compression transfers to full exact-visible
  compression only with a uniform visible section; the finite-support full-rule
  construction cannot supply one below the full exact-visible surface size. -/
  | actualObservedSupportUniformSectionBoundary
  /-- A reachable-support quotient only records restriction along `visibleOf`;
  below surface cardinality it identifies distinct exact-visible rules. -/
  | actualObservedSupportQuotientLossBoundary
  /-- No decoder from observed block-output traces can reconstruct all full
  exact-visible rules unless the reachable support hits the whole surface. -/
  | actualObservedSupportDecoderRecoveryBoundary
  /-- Any downstream property decoded from observed block traces must be
  constant on observed-output fibers; off-support exact-visible bits are not
  observable below full support. -/
  | actualObservedSupportObservablePropertyBoundary
  /-- A downstream property factors through observed block traces exactly when
  it is constant on observed-output fibers. -/
  | actualObservedSupportPropertyFactorBoundary
  /-- Exact-visible point queries are observable from block traces exactly at
  points in the reachable support; all point queries force full support
  surjectivity. -/
  | actualObservedSupportPointQueryBoundary
  /-- A whole family of exact-visible point queries is decodable from observed
  traces exactly when every queried point lies in reachable support. -/
  | actualObservedSupportQueryFamilyBoundary
  /-- Adaptive point-query trees over exact-visible points still factor
  through observed traces exactly by quotient constancy, and missed root
  queries with distinct branches are impossible to decode. -/
  | actualObservedSupportAdaptiveQueryBoundary
  /-- An unrestricted plug-in lookup endpoint over the exact visible alphabet
  is still the full Boolean rule family, not a small-image `Kpoly` bridge. -/
  | actualLocalPluginLookupFullRuleObstruction
  /-- Unrestricted per-input plug-in majority counts still realize every
  Boolean rule on the exact visible alphabet. -/
  | actualLocalPluginMajorityFullRuleObstruction
  /-- Sample-level plug-in majority still realizes every Boolean rule via the
  graph sample unless the samples are further restricted. -/
  | actualLocalPluginSampleMajorityFullRuleObstruction
  /-- Unrestricted sample-level plug-in majority still cannot be identified
  with one shared sparse-threshold ERM family, nor carry its stronger recovery
  packet, below the point-block visible-budget threshold. -/
  | actualLocalPluginSampleMajoritySparseThresholdERMVisibleBudgetBoundary
  /-- Bounded sample-level plug-in majority is full-rule expressive exactly
  when the sample bound reaches the exact visible alphabet size. -/
  | actualLocalBoundedSampleMajorityThresholdBoundary
  /-- Bounded sample-level plug-in majority can be false only on sampled exact
  visible inputs, so target rules with too-large false support are not
  realizable. -/
  | actualLocalBoundedSampleMajorityFalseSupportBoundary
  /-- Changing the bounded sample-level plug-in majority tie-break does not
  change the cardinal threshold: only sampled inputs can differ from the
  chosen default. -/
  | actualLocalBoundedSampleMajorityDefaultTieBoundary
  /-- An input-dependent tie fallback for bounded sample-level plug-in majority
  is already a full exact-visible lookup table, even with the empty sample. -/
  | actualLocalBoundedSampleMajorityFallbackSideChannelBoundary
  /-- That same full-rule fallback side channel still has no small finite
  predictor-image cover below the full exact-visible Boolean rule cube. -/
  | actualLocalBoundedSampleMajorityFallbackFinitePredictorCoverObstruction
  /-- That same full-rule fallback side channel still has no finite selected-
  index representative cover below the full exact-visible Boolean rule cube. -/
  | actualLocalBoundedSampleMajorityFallbackFiniteIndexRepresentativeCoverObstruction
  /-- The same full-rule fallback side channel also has no finite quotient-code
  presentation below the full exact-visible Boolean rule cube. -/
  | actualLocalBoundedSampleMajorityFallbackFinitePredictorQuotientObstruction
  /-- The same fallback side channel therefore admits no exact-visible
  compression target below the full exact-visible Boolean rule cube. -/
  | actualLocalBoundedSampleMajorityFallbackExactVisibleCompressionObstruction
  /-- The same fallback side channel also admits no clocked exact-visible
  realization below the full exact-visible Boolean rule cube. -/
  | actualLocalBoundedSampleMajorityFallbackClockedRealizationObstruction
  /-- The same fallback side channel cannot provide the full clocked finite-
  learning payload below the full exact-visible Boolean rule cube either. -/
  | actualLocalBoundedSampleMajorityFallbackClockedPayloadObstruction
  /-- If the input-dependent fallback is restricted to a structured fallback
  family, bounded samples only produce sparse point changes from the selected
  fallback rule. -/
  | actualLocalBoundedSampleMajorityFallbackFamilySparseBoundary
  /-- For any structured fallback code, the empty sampled override set realizes
  that fallback rule exactly. -/
  | actualLocalBoundedSampleMajorityFallbackFamilyEmptySampleRealizationBoundary
  /-- If every structured fallback code disagrees with a target rule on more
  than `sampleBound` surface points, bounded samples cannot realize that rule
  at all. -/
  | actualLocalBoundedSampleMajorityFallbackFamilyLargeDisagreementSupportObstruction
  /-- For a structured fallback family, a target rule is realizable exactly
  when it lies in the radius-`sampleBound` Hamming cover of the fallback
  codes. -/
  | actualLocalBoundedSampleMajorityFallbackFamilyRadiusCoverBoundary
  /-- The same structured fallback-family endpoint has predictor image covered
  by at most `|FallbackIndex| * |smallSubsets surface sampleBound|` rules. -/
  | actualLocalBoundedSampleMajorityFallbackFamilyFinitePredictorCoverBoundary
  /-- Full-rule expressivity of the structured fallback-family endpoint is
  equivalent to the radius-`sampleBound` Hamming cover already filling the
  whole exact-visible Boolean rule cube. -/
  | actualLocalBoundedSampleMajorityFallbackFamilyRadiusCoverSurjectivityBoundary
  /-- Full-rule expressivity of the structured fallback-family endpoint is
  equivalently the pointwise condition that every exact-visible rule lie
  within disagreement radius `sampleBound` of some fallback code. -/
  | actualLocalBoundedSampleMajorityFallbackFamilyPointwiseRadiusCoverSurjectivityBoundary
  /-- If a structured fallback family is already full-rule expressive, bounded
  samples preserve that full exact-visible expressivity. -/
  | actualLocalBoundedSampleMajorityFallbackFamilyFallbackSurjectiveBoundary
  /-- Full-rule expressivity already forces the abstract fallback-family
  support product `|FallbackIndex| * |smallSubsets surface sampleBound|`. -/
  | actualLocalBoundedSampleMajorityFallbackFamilySmallSubsetsProductBoundary
  /-- The same abstract fallback-family support product blocks surjectivity
  whenever it stays strictly below the full exact-visible Boolean rule cube. -/
  | actualLocalBoundedSampleMajorityFallbackFamilySmallSubsetsProductSurjectivityObstruction
  /-- Once the sample bound reaches the exact-visible alphabet size, any
  nonempty structured fallback family is already full-rule expressive. -/
  | actualLocalBoundedSampleMajorityFallbackFamilyFullRadiusBoundary
  /-- At zero sparse-support radius, the wrapper contributes no hidden
  expressivity: surjectivity of the endpoint is equivalent to surjectivity of
  the fallback family itself. -/
  | actualLocalBoundedSampleMajorityFallbackFamilyZeroSampleFallbackEquivalence
  /-- At zero sparse-support radius, the structured fallback wrapper has
  exactly the same finite predictor-image covers as the raw fallback family
  itself. -/
  | actualLocalBoundedSampleMajorityFallbackFamilyZeroSampleFinitePredictorCoverBoundary
  /-- At zero sparse-support radius, the structured fallback wrapper has
  exactly the same finite selected-index representative covers as the raw
  fallback family itself. -/
  | actualLocalBoundedSampleMajorityFallbackFamilyZeroSampleFiniteIndexRepresentativeCoverBoundary
  /-- At zero sparse-support radius, the structured fallback wrapper has
  exactly the same finite quotient-code presentations as the raw fallback
  family itself. -/
  | actualLocalBoundedSampleMajorityFallbackFamilyZeroSampleFinitePredictorQuotientBoundary
  /-- Radius-zero exact visible compression claims for the structured fallback
  wrapper are exactly the corresponding compression claims for the raw
  fallback family. -/
  | actualLocalBoundedSampleMajorityFallbackFamilyZeroSampleExactVisibleCompressionBoundary
  /-- Radius-zero clocked exact-visible realization claims for the structured
  fallback wrapper are exactly the corresponding claims for the raw fallback
  family. -/
  | actualLocalBoundedSampleMajorityFallbackFamilyZeroSampleClockedRealizationBoundary
  /-- Radius-zero clocked finite-learning payload claims for the structured
  fallback wrapper are exactly the corresponding payload claims for the raw
  fallback family. -/
  | actualLocalBoundedSampleMajorityFallbackFamilyZeroSampleClockedPayloadBoundary
  deriving DecidableEq, Repr

end Mettapedia.Computability.PNP
