import Mettapedia.Computability.PNP.CruxKpolySubrepairClassBase
/-!
# Legacy flat names for PNP `Kpoly` core/exact-visible subrepair classes

This module keeps the historical `PNPKpolySubrepairClass.foo` names while
the semantic class family lives in `PNPKpolyCoreSubrepairClass`.
-/

namespace Mettapedia.Computability.PNP

namespace PNPKpolySubrepairClass

  /-- A clocked exact-visible realization family is exactly the existing
  exact-visible bit-budget target. -/
abbrev clockWrapperEquivalence : PNPKpolySubrepairClass :=
  .core .clockWrapperEquivalence
  /-- The fixed-order raw `(a,b)` decision-list class cannot realize the full
  raw Boolean rule family at positive width. -/
abbrev rawABDecisionListFullRuleObstruction : PNPKpolySubrepairClass :=
  .core .rawABDecisionListFullRuleObstruction
  /-- The same raw `(a,b)` full-rule obstruction lifts through the exact
  visible pullback. -/
abbrev rawABDecisionListExactPullbackObstruction : PNPKpolySubrepairClass :=
  .core .rawABDecisionListExactPullbackObstruction
  /-- Shared affine-feature families cannot realize all raw `(a,b)` Boolean
  rules below the reduced truth-table threshold. -/
abbrev sharedABAffineFeatureFullRuleObstruction : PNPKpolySubrepairClass :=
  .core .sharedABAffineFeatureFullRuleObstruction
  /-- Shared sparse-threshold families cannot realize all raw `(a,b)` Boolean
  rules below the reduced truth-table threshold. -/
abbrev sharedABSparseThresholdFullRuleObstruction : PNPKpolySubrepairClass :=
  .core .sharedABSparseThresholdFullRuleObstruction
  /-- Shared decision-list families cannot realize all raw `(a,b)` Boolean
  rules below the reduced truth-table threshold. -/
abbrev sharedABDecisionListFullRuleObstruction : PNPKpolySubrepairClass :=
  .core .sharedABDecisionListFullRuleObstruction
  /-- The shared affine-feature full-rule obstruction lifts through the exact
  visible pullback. -/
abbrev sharedExactABAffineFeaturePullbackObstruction : PNPKpolySubrepairClass :=
  .core .sharedExactABAffineFeaturePullbackObstruction
  /-- The shared sparse-threshold full-rule obstruction lifts through the exact
  visible pullback. -/
abbrev sharedExactABSparseThresholdPullbackObstruction : PNPKpolySubrepairClass :=
  .core .sharedExactABSparseThresholdPullbackObstruction
  /-- The shared decision-list full-rule obstruction lifts through the exact
  visible pullback. -/
abbrev sharedExactABDecisionListPullbackObstruction : PNPKpolySubrepairClass :=
  .core .sharedExactABDecisionListPullbackObstruction
  /-- Shared raw `(a,b)` feature families cannot realize injective finite probe
  images larger than their finite combiner image, without needing full reduced
  rule surjectivity. -/
abbrev sharedABFeatureInjectiveProbeImageObstruction : PNPKpolySubrepairClass :=
  .core .sharedABFeatureInjectiveProbeImageObstruction
  /-- The shared raw `(a,b)` finite-probe obstruction lifts through exact
  visible pullback along `abVisibleData`. -/
abbrev sharedExactABFeatureInjectiveProbePullbackObstruction : PNPKpolySubrepairClass :=
  .core .sharedExactABFeatureInjectiveProbePullbackObstruction
  /-- Any exact family invariant under raw `(a,b)` cannot select a target rule
  that separates two exact inputs in the same `(a,b)` fiber. -/
abbrev abVisibleInvariantPointTargetObstruction : PNPKpolySubrepairClass :=
  .core .abVisibleInvariantPointTargetObstruction
  /-- Any raw `(a,b)`-invariant exact predictor must disagree on positive mass
  with a target that separates two positive-mass inputs in one same-`(a,b)`
  fiber. -/
abbrev abVisibleInvariantSupportDisagreementObstruction : PNPKpolySubrepairClass :=
  .core .abVisibleInvariantSupportDisagreementObstruction
  /-- Any exact family invariant under raw `(a,b)` is not surjective onto all
  exact visible Boolean rules when the hidden `Z` datum is nontrivial. -/
abbrev abVisibleInvariantExactSurfaceSurjectivityObstruction : PNPKpolySubrepairClass :=
  .core .abVisibleInvariantExactSurfaceSurjectivityObstruction
  /-- Exact visible / clocked `Kpoly` budgets are exactly finite predictor-image
  covers of size at most `2^s`. -/
abbrev exactVisibleImageBudgetEquivalence : PNPKpolySubrepairClass :=
  .core .exactVisibleImageBudgetEquivalence
  /-- The accumulated clocked finite-learning payload is exactly the same
  finite predictor-image cover obligation. -/
abbrev clockedFiniteLearningPayloadEquivalence : PNPKpolySubrepairClass :=
  .core .clockedFiniteLearningPayloadEquivalence
  /-- The concrete exact `(zfeat(z), a, b)` decision-list ERM family closes the
  clocked finite-learning payload at its explicit code budget. -/
abbrev exactZABERMClockedPayloadClosure : PNPKpolySubrepairClass :=
  .core .exactZABERMClockedPayloadClosure
  /-- The bit-vector exact ZAB ERM specialization closes the clocked
  finite-learning payload at the same explicit budget. -/
abbrev bitVecZABERMClockedPayloadClosure : PNPKpolySubrepairClass :=
  .core .bitVecZABERMClockedPayloadClosure
  /-- Equality with the concrete bit-vector ERM family is a sufficient
  manuscript-facing missing assumption for the clocked payload. -/
abbrev equalityToBitVecZABERMClockedPayloadClosure : PNPKpolySubrepairClass :=
  .core .equalityToBitVecZABERMClockedPayloadClosure
  /-- A strict exact-ZAB bad-code agreement threshold forces every region above
  that threshold to contain a positive-mass bad-code disagreement. -/
abbrev exactZABBadCodeLargeRegionDisagreementBoundary : PNPKpolySubrepairClass :=
  .core .exactZABBadCodeLargeRegionDisagreementBoundary
  /-- If an actual switched-local family is both surjective and realized by
  shared exact `(zfeat z, a, b)` decision-list data, the extractor width must
  absorb the full exact-visible surface gap `|surface| - (2k + 1)`. -/
abbrev actualLocalZABDecisionListVisibleCardGapLowerBound : PNPKpolySubrepairClass :=
  .core .actualLocalZABDecisionListVisibleCardGapLowerBound
  /-- On `Z = BitVec n`, the full-rule actual switched-local family cannot
  carry exact ZAB decision-list data once the extractor width stays below the
  truth-table gap `2^(n + 2k) - (2k + 1)`. -/
abbrev actualLocalZABDecisionListBitVecTruthTableGapObstruction : PNPKpolySubrepairClass :=
  .core .actualLocalZABDecisionListBitVecTruthTableGapObstruction
  /-- On any surjective actual switched-local endpoint, the weaker shared
  sparse-threshold ERM packet must still fit inside the point-block visible
  budget `2 * allAffinePointBlockFeatureCount (r + 2*k)`. -/
abbrev surjectiveActualLocalSparseThresholdERMVisibleBudgetBoundary : PNPKpolySubrepairClass :=
  .core .surjectiveActualLocalSparseThresholdERMVisibleBudgetBoundary
  /-- On `Z = BitVec n`, any surjective actual switched-local endpoint
  carrying the weaker shared sparse-threshold ERM packet must satisfy the same
  unconditional half-width ceiling `n ≤ 2*r + 2*k + 1`. -/
abbrev surjectiveActualLocalSparseThresholdERMVisibleWidthBoundary : PNPKpolySubrepairClass :=
  .core .surjectiveActualLocalSparseThresholdERMVisibleWidthBoundary
  /-- If `2*r + 2*k + 1 < n`, then no extractor at all can support the weaker
  shared sparse-threshold ERM packet on a surjective actual switched-local
  endpoint. -/
abbrev surjectiveActualLocalNoExtractorSparseThresholdERMVisibleWidthBoundary : PNPKpolySubrepairClass :=
  .core .surjectiveActualLocalNoExtractorSparseThresholdERMVisibleWidthBoundary

end PNPKpolySubrepairClass

end Mettapedia.Computability.PNP
