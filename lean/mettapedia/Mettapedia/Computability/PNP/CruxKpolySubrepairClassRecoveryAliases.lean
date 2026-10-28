import Mettapedia.Computability.PNP.CruxKpolySubrepairClassBase
/-!
# Legacy flat names for PNP `Kpoly` actual-local recovery subrepair classes

This module keeps the historical `PNPKpolySubrepairClass.foo` names while
the semantic class family lives in `PNPKpolyRecoverySubrepairClass`.
-/

namespace Mettapedia.Computability.PNP

namespace PNPKpolySubrepairClass

abbrev surjectiveActualLocalJointRecoveryBoundary : PNPKpolySubrepairClass :=
  .recovery .surjectiveActualLocalJointRecoveryBoundary
  /-- On any surjective actual-local endpoint, the manuscript-facing sparse-
  threshold recovery packet already forces the unconditional half-width
  ceiling. -/
abbrev surjectiveActualLocalRecoveryVisibleWidthBoundary : PNPKpolySubrepairClass :=
  .recovery .surjectiveActualLocalRecoveryVisibleWidthBoundary
  /-- On any surjective actual-local endpoint, the manuscript-facing sparse-
  threshold recovery packet already forces the intrinsic lightest-point
  threshold. -/
abbrev surjectiveActualLocalRecoveryLightestPointBoundary : PNPKpolySubrepairClass :=
  .recovery .surjectiveActualLocalRecoveryLightestPointBoundary
  /-- On any finite nonempty surjective actual-local endpoint, the recovery
  packet already forces `q` above the uniform-complement threshold
  `1 - |surface|⁻¹`. -/
abbrev surjectiveActualLocalRecoveryUniformCardinalityThresholdBoundary : PNPKpolySubrepairClass :=
  .recovery .surjectiveActualLocalRecoveryUniformCardinalityThresholdBoundary
  /-- Even without surjectivity, any actual-local endpoint with an injective
  extractor of positive combined width already forces the same
  uniform-complement recovery threshold `q ≥ 1 - |surface|⁻¹`. -/
abbrev actualLocalInjectiveRecoveryUniformCardinalityThresholdBoundary : PNPKpolySubrepairClass :=
  .recovery .actualLocalInjectiveRecoveryUniformCardinalityThresholdBoundary
  /-- On any surjective actual-local endpoint, the manuscript-facing sparse-
  threshold recovery packet already implies the bundled finite-learning
  payload, so it is impossible below the full predictor-image cardinality. -/
abbrev surjectiveActualLocalRecoveryPayloadPredictorCardObstruction : PNPKpolySubrepairClass :=
  .recovery .surjectiveActualLocalRecoveryPayloadPredictorCardObstruction
  /-- The same surjective predictor-card obstruction already removes the
  extractor choice itself: below the payload budget, no extractor can support
  the manuscript-facing sparse-threshold recovery packet. -/
abbrev surjectiveActualLocalNoExtractorRecoveryPayloadPredictorCardObstruction : PNPKpolySubrepairClass :=
  .recovery .surjectiveActualLocalNoExtractorRecoveryPayloadPredictorCardObstruction
  /-- More generally, once an actual-local endpoint already realizes an
  injectively indexed finite probe family larger than the current payload
  budget, the manuscript-facing sparse-threshold recovery packet is impossible
  even without full surjectivity. -/
abbrev actualLocalRecoveryPayloadInjectiveProbeCardObstruction : PNPKpolySubrepairClass :=
  .recovery .actualLocalRecoveryPayloadInjectiveProbeCardObstruction
  /-- The same injective finite-probe payload obstruction also removes the
  extractor choice itself. -/
abbrev actualLocalNoExtractorRecoveryPayloadInjectiveProbeCardObstruction : PNPKpolySubrepairClass :=
  .recovery .actualLocalNoExtractorRecoveryPayloadInjectiveProbeCardObstruction
  /-- On the full-rule `BitVec n` endpoint, the recovery packet already forces
  the explicit threshold `q ≥ 1 - 2^-(n + 2*k)`. -/
abbrev fullRuleActualLocalRecoveryBitVecCardinalityThresholdBoundary : PNPKpolySubrepairClass :=
  .recovery .fullRuleActualLocalRecoveryBitVecCardinalityThresholdBoundary
  /-- The same `BitVec n` threshold already applies to any actual-local
  endpoint once the extractor is injective and has positive combined width. -/
abbrev actualLocalInjectiveRecoveryBitVecCardinalityThresholdBoundary : PNPKpolySubrepairClass :=
  .recovery .actualLocalInjectiveRecoveryBitVecCardinalityThresholdBoundary
  /-- Therefore below that explicit `BitVec n` threshold, no extractor at all
  can support the full-rule manuscript-facing recovery packet. -/
abbrev fullRuleActualLocalNoExtractorRecoveryBitVecCardinalityThresholdObstruction : PNPKpolySubrepairClass :=
  .recovery .fullRuleActualLocalNoExtractorRecoveryBitVecCardinalityThresholdObstruction
  /-- Therefore below that explicit `BitVec n` threshold, no injective
  extractor of positive combined width can support the manuscript-facing
  recovery packet on that actual-local endpoint. -/
abbrev actualLocalNoInjectiveExtractorRecoveryBitVecCardinalityThresholdObstruction : PNPKpolySubrepairClass :=
  .recovery .actualLocalNoInjectiveExtractorRecoveryBitVecCardinalityThresholdObstruction
  /-- On the full-rule `BitVec n` endpoint, if the manuscript-facing recovery
  threshold already lies below `1 - 2^-p`, then the visible width already
  satisfies `n + 2*k < p`. -/
abbrev fullRuleActualLocalRecoveryThresholdWidthBoundary : PNPKpolySubrepairClass :=
  .recovery .fullRuleActualLocalRecoveryThresholdWidthBoundary
  /-- Therefore if `p ≤ n + 2*k`, no extractor at all can support the
  full-rule manuscript-facing recovery packet below `1 - 2^-p`. -/
abbrev fullRuleActualLocalNoExtractorRecoveryThresholdWidthObstruction : PNPKpolySubrepairClass :=
  .recovery .fullRuleActualLocalNoExtractorRecoveryThresholdWidthObstruction
  /-- The same direct visible-width obstruction also applies to bounded-sample
  plug-in-majority endpoints once the sample bound is large enough for
  surjectivity. -/
abbrev boundedSamplePluginMajorityActualLocalRecoveryThresholdWidthBoundary : PNPKpolySubrepairClass :=
  .recovery .boundedSamplePluginMajorityActualLocalRecoveryThresholdWidthBoundary
  /-- Therefore if `p ≤ n + 2*k`, no extractor at all can support that
  bounded-sample plug-in-majority recovery packet below `1 - 2^-p`. -/
abbrev boundedSamplePluginMajorityActualLocalNoExtractorRecoveryThresholdWidthObstruction : PNPKpolySubrepairClass :=
  .recovery .boundedSamplePluginMajorityActualLocalNoExtractorRecoveryThresholdWidthObstruction
  /-- On the full-rule `BitVec n` endpoint, if the manuscript-facing recovery
  threshold already lies below `1 - 2^-(2*r + 4*k + slack + 1)`, then the
  visible-width ceiling sharpens to `n ≤ 2*r + 2*k + slack`. -/
abbrev fullRuleActualLocalRecoveryThresholdVisibleBudgetBoundary : PNPKpolySubrepairClass :=
  .recovery .fullRuleActualLocalRecoveryThresholdVisibleBudgetBoundary
  /-- Therefore below that sharpened point-block boundary, no extractor at all
  can support the full-rule manuscript-facing recovery packet at such a small
  threshold. -/
abbrev fullRuleActualLocalNoExtractorRecoveryThresholdVisibleBudgetObstruction : PNPKpolySubrepairClass :=
  .recovery .fullRuleActualLocalNoExtractorRecoveryThresholdVisibleBudgetObstruction
  /-- The same sharpened point-block visible-budget ceiling also applies to
  bounded-sample plug-in-majority endpoints once the sample bound is large
  enough for surjectivity. -/
abbrev boundedSamplePluginMajorityActualLocalRecoveryThresholdVisibleBudgetBoundary : PNPKpolySubrepairClass :=
  .recovery .boundedSamplePluginMajorityActualLocalRecoveryThresholdVisibleBudgetBoundary
  /-- Therefore below that sharpened boundary, no extractor at all can support
  the bounded-sample plug-in-majority recovery packet when the threshold is
  already that small. -/
abbrev boundedSamplePluginMajorityActualLocalNoExtractorRecoveryThresholdVisibleBudgetObstruction : PNPKpolySubrepairClass :=
  .recovery .boundedSamplePluginMajorityActualLocalNoExtractorRecoveryThresholdVisibleBudgetObstruction
  /-- On any actual-local endpoint, every two distinct realized predictors in
  a manuscript-facing sparse-threshold recovery packet already have mutual
  agreement mass at most `q`. -/
abbrev actualLocalRecoveryPairwiseAgreementBoundary : PNPKpolySubrepairClass :=
  .recovery .actualLocalRecoveryPairwiseAgreementBoundary
  /-- Therefore if one distinct realized predictor pair already has agreement
  mass above `q`, no extractor at all can support the manuscript-facing
  sparse-threshold recovery packet on that endpoint. -/
abbrev actualLocalNoExtractorRecoveryPairwiseAgreementObstruction : PNPKpolySubrepairClass :=
  .recovery .actualLocalNoExtractorRecoveryPairwiseAgreementObstruction
  /-- On any surjective actual-local endpoint, every proper finite visible
  region already has total mass at most `q` under any manuscript-facing
  sparse-threshold recovery packet. This strengthens the earlier lightest-point
  boundary from singletons to arbitrary proper regions. -/
abbrev surjectiveActualLocalRecoveryProperRegionMassBoundary : PNPKpolySubrepairClass :=
  .recovery .surjectiveActualLocalRecoveryProperRegionMassBoundary
  /-- Therefore if one proper finite visible region already has mass above
  `q`, no extractor at all can support the manuscript-facing sparse-threshold
  recovery packet on that surjective actual-local endpoint. -/
abbrev surjectiveActualLocalNoExtractorProperRegionMassBoundary : PNPKpolySubrepairClass :=
  .recovery .surjectiveActualLocalNoExtractorProperRegionMassBoundary
  /-- More generally, once an injectively indexed actual-local endpoint already
  has one finite visible region of mass above `q`, the manuscript-facing
  sparse-threshold recovery packet forces the whole predictor family to fit
  inside the Boolean trace space on that region. -/
abbrev actualLocalRecoveryHeavyRegionTraceCardBoundary : PNPKpolySubrepairClass :=
  .recovery .actualLocalRecoveryHeavyRegionTraceCardBoundary
  /-- The same heavy-region trace-space obstruction also removes the extractor
  choice itself on that injectively indexed actual-local endpoint. -/
abbrev actualLocalNoExtractorRecoveryHeavyRegionTraceCardObstruction : PNPKpolySubrepairClass :=
  .recovery .actualLocalNoExtractorRecoveryHeavyRegionTraceCardObstruction
  /-- Below the intrinsic lightest-point threshold, no extractor at all can
  support the manuscript-facing sparse-threshold recovery packet on a
  surjective actual-local endpoint. -/
abbrev surjectiveActualLocalNoExtractorLightestPointBoundary : PNPKpolySubrepairClass :=
  .recovery .surjectiveActualLocalNoExtractorLightestPointBoundary
  /-- If the visible width itself already exceeds the unconditional
  surjective actual-local half-width ceiling, then no extractor at all can
  support the manuscript-facing sparse-threshold recovery packet. -/
abbrev surjectiveActualLocalNoExtractorVisibleWidthBoundary : PNPKpolySubrepairClass :=
  .recovery .surjectiveActualLocalNoExtractorVisibleWidthBoundary

end PNPKpolySubrepairClass

end Mettapedia.Computability.PNP
