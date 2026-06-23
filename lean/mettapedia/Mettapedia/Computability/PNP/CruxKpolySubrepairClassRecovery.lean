import Mettapedia.Computability.PNP.CruxLedger
/-!
# PNP `Kpoly` actual-local recovery subrepair classes

Actual-local recovery-threshold, payload, pairwise-agreement, and region-mass subrepair classes.
-/

namespace Mettapedia.Computability.PNP

/-- Actual-local recovery-threshold, payload, pairwise-agreement, and region-mass subrepair classes. -/
inductive PNPKpolyRecoverySubrepairClass where
  | surjectiveActualLocalJointRecoveryBoundary
  /-- On any surjective actual-local endpoint, the manuscript-facing sparse-
  threshold recovery packet already forces the unconditional half-width
  ceiling. -/
  | surjectiveActualLocalRecoveryVisibleWidthBoundary
  /-- On any surjective actual-local endpoint, the manuscript-facing sparse-
  threshold recovery packet already forces the intrinsic lightest-point
  threshold. -/
  | surjectiveActualLocalRecoveryLightestPointBoundary
  /-- On any finite nonempty surjective actual-local endpoint, the recovery
  packet already forces `q` above the uniform-complement threshold
  `1 - |surface|⁻¹`. -/
  | surjectiveActualLocalRecoveryUniformCardinalityThresholdBoundary
  /-- Even without surjectivity, any actual-local endpoint with an injective
  extractor of positive combined width already forces the same
  uniform-complement recovery threshold `q ≥ 1 - |surface|⁻¹`. -/
  | actualLocalInjectiveRecoveryUniformCardinalityThresholdBoundary
  /-- On any surjective actual-local endpoint, the manuscript-facing sparse-
  threshold recovery packet already implies the bundled finite-learning
  payload, so it is impossible below the full predictor-image cardinality. -/
  | surjectiveActualLocalRecoveryPayloadPredictorCardObstruction
  /-- The same surjective predictor-card obstruction already removes the
  extractor choice itself: below the payload budget, no extractor can support
  the manuscript-facing sparse-threshold recovery packet. -/
  | surjectiveActualLocalNoExtractorRecoveryPayloadPredictorCardObstruction
  /-- More generally, once an actual-local endpoint already realizes an
  injectively indexed finite probe family larger than the current payload
  budget, the manuscript-facing sparse-threshold recovery packet is impossible
  even without full surjectivity. -/
  | actualLocalRecoveryPayloadInjectiveProbeCardObstruction
  /-- The same injective finite-probe payload obstruction also removes the
  extractor choice itself. -/
  | actualLocalNoExtractorRecoveryPayloadInjectiveProbeCardObstruction
  /-- On the full-rule `BitVec n` endpoint, the recovery packet already forces
  the explicit threshold `q ≥ 1 - 2^-(n + 2*k)`. -/
  | fullRuleActualLocalRecoveryBitVecCardinalityThresholdBoundary
  /-- The same `BitVec n` threshold already applies to any actual-local
  endpoint once the extractor is injective and has positive combined width. -/
  | actualLocalInjectiveRecoveryBitVecCardinalityThresholdBoundary
  /-- Therefore below that explicit `BitVec n` threshold, no extractor at all
  can support the full-rule manuscript-facing recovery packet. -/
  | fullRuleActualLocalNoExtractorRecoveryBitVecCardinalityThresholdObstruction
  /-- Therefore below that explicit `BitVec n` threshold, no injective
  extractor of positive combined width can support the manuscript-facing
  recovery packet on that actual-local endpoint. -/
  | actualLocalNoInjectiveExtractorRecoveryBitVecCardinalityThresholdObstruction
  /-- On the full-rule `BitVec n` endpoint, if the manuscript-facing recovery
  threshold already lies below `1 - 2^-p`, then the visible width already
  satisfies `n + 2*k < p`. -/
  | fullRuleActualLocalRecoveryThresholdWidthBoundary
  /-- Therefore if `p ≤ n + 2*k`, no extractor at all can support the
  full-rule manuscript-facing recovery packet below `1 - 2^-p`. -/
  | fullRuleActualLocalNoExtractorRecoveryThresholdWidthObstruction
  /-- The same direct visible-width obstruction also applies to bounded-sample
  plug-in-majority endpoints once the sample bound is large enough for
  surjectivity. -/
  | boundedSamplePluginMajorityActualLocalRecoveryThresholdWidthBoundary
  /-- Therefore if `p ≤ n + 2*k`, no extractor at all can support that
  bounded-sample plug-in-majority recovery packet below `1 - 2^-p`. -/
  | boundedSamplePluginMajorityActualLocalNoExtractorRecoveryThresholdWidthObstruction
  /-- On the full-rule `BitVec n` endpoint, if the manuscript-facing recovery
  threshold already lies below `1 - 2^-(2*r + 4*k + slack + 1)`, then the
  visible-width ceiling sharpens to `n ≤ 2*r + 2*k + slack`. -/
  | fullRuleActualLocalRecoveryThresholdVisibleBudgetBoundary
  /-- Therefore below that sharpened point-block boundary, no extractor at all
  can support the full-rule manuscript-facing recovery packet at such a small
  threshold. -/
  | fullRuleActualLocalNoExtractorRecoveryThresholdVisibleBudgetObstruction
  /-- The same sharpened point-block visible-budget ceiling also applies to
  bounded-sample plug-in-majority endpoints once the sample bound is large
  enough for surjectivity. -/
  | boundedSamplePluginMajorityActualLocalRecoveryThresholdVisibleBudgetBoundary
  /-- Therefore below that sharpened boundary, no extractor at all can support
  the bounded-sample plug-in-majority recovery packet when the threshold is
  already that small. -/
  | boundedSamplePluginMajorityActualLocalNoExtractorRecoveryThresholdVisibleBudgetObstruction
  /-- On any actual-local endpoint, every two distinct realized predictors in
  a manuscript-facing sparse-threshold recovery packet already have mutual
  agreement mass at most `q`. -/
  | actualLocalRecoveryPairwiseAgreementBoundary
  /-- Therefore if one distinct realized predictor pair already has agreement
  mass above `q`, no extractor at all can support the manuscript-facing
  sparse-threshold recovery packet on that endpoint. -/
  | actualLocalNoExtractorRecoveryPairwiseAgreementObstruction
  /-- On any surjective actual-local endpoint, every proper finite visible
  region already has total mass at most `q` under any manuscript-facing
  sparse-threshold recovery packet. This strengthens the earlier lightest-point
  boundary from singletons to arbitrary proper regions. -/
  | surjectiveActualLocalRecoveryProperRegionMassBoundary
  /-- Therefore if one proper finite visible region already has mass above
  `q`, no extractor at all can support the manuscript-facing sparse-threshold
  recovery packet on that surjective actual-local endpoint. -/
  | surjectiveActualLocalNoExtractorProperRegionMassBoundary
  /-- More generally, once an injectively indexed actual-local endpoint already
  has one finite visible region of mass above `q`, the manuscript-facing
  sparse-threshold recovery packet forces the whole predictor family to fit
  inside the Boolean trace space on that region. -/
  | actualLocalRecoveryHeavyRegionTraceCardBoundary
  /-- The same heavy-region trace-space obstruction also removes the extractor
  choice itself on that injectively indexed actual-local endpoint. -/
  | actualLocalNoExtractorRecoveryHeavyRegionTraceCardObstruction
  /-- Below the intrinsic lightest-point threshold, no extractor at all can
  support the manuscript-facing sparse-threshold recovery packet on a
  surjective actual-local endpoint. -/
  | surjectiveActualLocalNoExtractorLightestPointBoundary
  /-- If the visible width itself already exceeds the unconditional
  surjective actual-local half-width ceiling, then no extractor at all can
  support the manuscript-facing sparse-threshold recovery packet. -/
  | surjectiveActualLocalNoExtractorVisibleWidthBoundary
  deriving DecidableEq, Repr

end Mettapedia.Computability.PNP
