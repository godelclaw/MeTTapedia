import Mettapedia.Computability.PNP.CruxLedger
/-!
# PNP `Kpoly` core/exact-visible subrepair classes

Core exact-visible, raw `(a,b)`, shared `(a,b)`, and first actual-local sparse-threshold subrepair classes.
-/

namespace Mettapedia.Computability.PNP

/-- Core exact-visible, raw `(a,b)`, shared `(a,b)`, and first actual-local sparse-threshold subrepair classes. -/
inductive PNPKpolyCoreSubrepairClass where
  /-- A clocked exact-visible realization family is exactly the existing
  exact-visible bit-budget target. -/
  | clockWrapperEquivalence
  /-- The fixed-order raw `(a,b)` decision-list class cannot realize the full
  raw Boolean rule family at positive width. -/
  | rawABDecisionListFullRuleObstruction
  /-- The same raw `(a,b)` full-rule obstruction lifts through the exact
  visible pullback. -/
  | rawABDecisionListExactPullbackObstruction
  /-- Shared affine-feature families cannot realize all raw `(a,b)` Boolean
  rules below the reduced truth-table threshold. -/
  | sharedABAffineFeatureFullRuleObstruction
  /-- Shared sparse-threshold families cannot realize all raw `(a,b)` Boolean
  rules below the reduced truth-table threshold. -/
  | sharedABSparseThresholdFullRuleObstruction
  /-- Shared decision-list families cannot realize all raw `(a,b)` Boolean
  rules below the reduced truth-table threshold. -/
  | sharedABDecisionListFullRuleObstruction
  /-- The shared affine-feature full-rule obstruction lifts through the exact
  visible pullback. -/
  | sharedExactABAffineFeaturePullbackObstruction
  /-- The shared sparse-threshold full-rule obstruction lifts through the exact
  visible pullback. -/
  | sharedExactABSparseThresholdPullbackObstruction
  /-- The shared decision-list full-rule obstruction lifts through the exact
  visible pullback. -/
  | sharedExactABDecisionListPullbackObstruction
  /-- Shared raw `(a,b)` feature families cannot realize injective finite probe
  images larger than their finite combiner image, without needing full reduced
  rule surjectivity. -/
  | sharedABFeatureInjectiveProbeImageObstruction
  /-- The shared raw `(a,b)` finite-probe obstruction lifts through exact
  visible pullback along `abVisibleData`. -/
  | sharedExactABFeatureInjectiveProbePullbackObstruction
  /-- Any exact family invariant under raw `(a,b)` cannot select a target rule
  that separates two exact inputs in the same `(a,b)` fiber. -/
  | abVisibleInvariantPointTargetObstruction
  /-- Any raw `(a,b)`-invariant exact predictor must disagree on positive mass
  with a target that separates two positive-mass inputs in one same-`(a,b)`
  fiber. -/
  | abVisibleInvariantSupportDisagreementObstruction
  /-- Any exact family invariant under raw `(a,b)` is not surjective onto all
  exact visible Boolean rules when the hidden `Z` datum is nontrivial. -/
  | abVisibleInvariantExactSurfaceSurjectivityObstruction
  /-- Exact visible / clocked `Kpoly` budgets are exactly finite predictor-image
  covers of size at most `2^s`. -/
  | exactVisibleImageBudgetEquivalence
  /-- The accumulated clocked finite-learning payload is exactly the same
  finite predictor-image cover obligation. -/
  | clockedFiniteLearningPayloadEquivalence
  /-- The concrete exact `(zfeat(z), a, b)` decision-list ERM family closes the
  clocked finite-learning payload at its explicit code budget. -/
  | exactZABERMClockedPayloadClosure
  /-- The bit-vector exact ZAB ERM specialization closes the clocked
  finite-learning payload at the same explicit budget. -/
  | bitVecZABERMClockedPayloadClosure
  /-- Equality with the concrete bit-vector ERM family is a sufficient
  manuscript-facing missing assumption for the clocked payload. -/
  | equalityToBitVecZABERMClockedPayloadClosure
  /-- A strict exact-ZAB bad-code agreement threshold forces every region above
  that threshold to contain a positive-mass bad-code disagreement. -/
  | exactZABBadCodeLargeRegionDisagreementBoundary
  /-- If an actual switched-local family is both surjective and realized by
  shared exact `(zfeat z, a, b)` decision-list data, the extractor width must
  absorb the full exact-visible surface gap `|surface| - (2k + 1)`. -/
  | actualLocalZABDecisionListVisibleCardGapLowerBound
  /-- On `Z = BitVec n`, the full-rule actual switched-local family cannot
  carry exact ZAB decision-list data once the extractor width stays below the
  truth-table gap `2^(n + 2k) - (2k + 1)`. -/
  | actualLocalZABDecisionListBitVecTruthTableGapObstruction
  /-- On any surjective actual switched-local endpoint, the weaker shared
  sparse-threshold ERM packet must still fit inside the point-block visible
  budget `2 * allAffinePointBlockFeatureCount (r + 2*k)`. -/
  | surjectiveActualLocalSparseThresholdERMVisibleBudgetBoundary
  /-- On `Z = BitVec n`, any surjective actual switched-local endpoint
  carrying the weaker shared sparse-threshold ERM packet must satisfy the same
  unconditional half-width ceiling `n ≤ 2*r + 2*k + 1`. -/
  | surjectiveActualLocalSparseThresholdERMVisibleWidthBoundary
  /-- If `2*r + 2*k + 1 < n`, then no extractor at all can support the weaker
  shared sparse-threshold ERM packet on a surjective actual switched-local
  endpoint. -/
  | surjectiveActualLocalNoExtractorSparseThresholdERMVisibleWidthBoundary
  deriving DecidableEq, Repr

end Mettapedia.Computability.PNP
