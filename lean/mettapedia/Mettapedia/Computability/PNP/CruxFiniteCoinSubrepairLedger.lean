import Mettapedia.Computability.PNP.CruxLedger

/-!
# PNP finite-coin subrepair ledger

Static subrepair taxonomy and covered-subrepair list for this branch of
the PNP crux ledger.  The theorem-backed coverage proofs live in the
corresponding semantic coverage modules.
-/

namespace Mettapedia.Computability.PNP

/-- Precise finite-coin subrepair classes covered by the current grassroots
finite-coin stack.  These sit inside the same-source finite-count approximation
surface; they are not broad residual or `Kpoly` closure claims. -/
inductive PNPFiniteCoinSubrepairClass where
  /-- Same-source finite-coin marginal recoding of a Boolean source bit. -/
  | sameSourceFiniteCoinMarginalRecoding
  /-- Balanced fibers are erasure for every decidable output predicate. -/
  | predicateErasure
  /-- Balanced fibers force every Boolean output decoder to be exactly
  half-accurate in aggregate. -/
  | decoderHalfAccuracy
  /-- Each output fiber's finite-count defect is `|Coin|` times its imbalance. -/
  | exactScaledFiberImbalance
  /-- Tolerance below `|Coin|` collapses approximate independence to exact
  balanced fibers. -/
  | subCardinalityToleranceQuantization
  /-- Tolerance below a lower-bounded source/coin imbalance block collapses
  approximate independence to exact balanced fibers. -/
  | sourceLowerBoundToleranceQuantization
  /-- If the coin is retained, tolerance below a source/coin block collapses
  approximate independence to pointwise source-blindness at every coin. -/
  | retainedCoinTolerancePointwiseCollapse
  /-- If side information is retained, tolerance below a source/coin block
  collapses approximate independence to true/false balance inside every
  retained side/output fiber. -/
  | retainedSideToleranceSideFiberBalance
  /-- Source-side nondegeneracy plus a nonempty coin space blocks uniform
  true/false distinguishing fibers at zero tolerance. -/
  | sourceNonconstantUniformFiberZeroBlock
  /-- On nondegenerate source surfaces, zero-tolerance finite-coin output
  independence is equivalent to balanced output fibers. -/
  | sourceNonconstantZeroIffBalanced
  /-- Exact balanced-fiber erasure is preserved by deterministic output
  postprocessing. -/
  | deterministicOutputPostprocessing
  /-- Injective deterministic output postprocessing cannot create balanced
  finite-coin erasure that was not already present. -/
  | injectivePostprocessingErasureEquivalence
  /-- A postprocessor that recovers the original observed finite-coin output on
  the support cannot create finite-coin erasure. -/
  | observedLeftInversePostprocessingErasureEquivalence
  /-- A postprocessor injective on the observed finite-coin support cannot
  create finite-coin erasure. -/
  | observedInjectivePostprocessingErasureEquivalence
  /-- If postprocessing balances an unbalanced finite-coin recoding, it must
  collide two distinct observed original outputs. -/
  | postprocessingObservedOutputCollisionObligation
  /-- If postprocessing balances an unbalanced finite-coin recoding, one
  postprocessed fiber must merge opposite source-bias original outputs. -/
  | postprocessingObservedOppositeBiasCollisionObligation
  /-- Balanced deterministic postprocessing requires exact signed-bias
  cancellation in every postprocessed fiber. -/
  | postprocessingSignedBiasCancellationCertificate
  /-- Postprocessed retained-side tolerance below a source/coin block collapses
  to observed-fiber true/false balance. -/
  | postprocessedSideToleranceObservedFiberBalance
  /-- Any residual observed-fiber imbalance after retained-side postprocessing
  forces a proportional source/coin tolerance lower bound. -/
  | postprocessedSideObservedFiberImbalanceLowerBound
  /-- Below a source/coin block, every downstream predicate on a postprocessed
  retained-side output has equal true/false coin counts. -/
  | postprocessedSidePredicateErasure
  /-- Below a source/coin block, every downstream Boolean decoder on a
  postprocessed retained-side output is exactly half-accurate. -/
  | postprocessedSideDecoderHalfAccuracy
  /-- Below a source/coin block, uniform downstream source recovery after
  retained-side postprocessing is impossible. -/
  | postprocessedSideSourceRecoveryBlock
  /-- Below a source/coin block, postprocessed retained-side independence
  forces a true/false observed support collision. -/
  | postprocessedSideCollisionObligation
  /-- Below a source/coin block, every postprocessed observed coin value must
  have witnesses on both source sides. -/
  | postprocessedSidePointwiseCollisionObligation
  /-- Two-sided pointwise support collisions do not suffice for the
  postprocessed-side preserving coin matching. -/
  | postprocessedSidePointwiseCollisionInsufficient
  /-- One-sided witness maps do not suffice for postprocessed-side preserving
  coin matching unless they are injective, hence bijective. -/
  | postprocessedSideOneSidedCoinMapInsufficient
  /-- Injective one-sided witness maps are exactly the preserving
  postprocessed-side coin-matching obligation. -/
  | postprocessedSideInjectiveWitnessMapEquivalence
  /-- Below a source/coin block, postprocessed observations must provide a
  bijective true/false coin matching preserving every observed value. -/
  | postprocessedSideCoinMatchingObligation
  /-- A single postprocessed observed-fiber multiplicity mismatch blocks the
  coin-matching repair and below-threshold approximate independence. -/
  | postprocessedSideCoinMatchingCardinalityBlock
  /-- A downstream predicate count mismatch blocks the postprocessed-side
  coin-matching repair, covering predicate-only and decoder-only probes. -/
  | postprocessedSideCoinMatchingPredicateBlock
  /-- Neutrality for all downstream predicates is equivalent to the full
  postprocessed-side preserving coin matching. -/
  | postprocessedSidePredicateMatchingEquivalence
  /-- Below a source/coin block, postprocessed approximate independence is
  equivalent to the full preserving coin matching. -/
  | postprocessedSideApproxIndependenceCoinMatchingEquivalence
  /-- Approximate output independence under deterministic postprocessing has
  explicit finite-preimage blowup `τ ↦ m * τ`. -/
  | finitePreimagePostprocessingBlowup
  deriving DecidableEq, Repr

/-- The exact finite-coin subrepair list currently covered by the stack. -/
def currentPNPFiniteCoinCoveredSubrepairs : List PNPFiniteCoinSubrepairClass :=
  [.sameSourceFiniteCoinMarginalRecoding,
    .predicateErasure,
    .decoderHalfAccuracy,
    .exactScaledFiberImbalance,
    .subCardinalityToleranceQuantization,
    .sourceLowerBoundToleranceQuantization,
    .retainedCoinTolerancePointwiseCollapse,
    .retainedSideToleranceSideFiberBalance,
    .sourceNonconstantUniformFiberZeroBlock,
    .sourceNonconstantZeroIffBalanced,
    .deterministicOutputPostprocessing,
    .injectivePostprocessingErasureEquivalence,
    .observedLeftInversePostprocessingErasureEquivalence,
    .observedInjectivePostprocessingErasureEquivalence,
    .postprocessingObservedOutputCollisionObligation,
    .postprocessingObservedOppositeBiasCollisionObligation,
    .postprocessingSignedBiasCancellationCertificate,
    .postprocessedSideToleranceObservedFiberBalance,
    .postprocessedSideObservedFiberImbalanceLowerBound,
    .postprocessedSidePredicateErasure,
    .postprocessedSideDecoderHalfAccuracy,
    .postprocessedSideSourceRecoveryBlock,
    .postprocessedSideCollisionObligation,
    .postprocessedSidePointwiseCollisionObligation,
    .postprocessedSidePointwiseCollisionInsufficient,
    .postprocessedSideOneSidedCoinMapInsufficient,
    .postprocessedSideInjectiveWitnessMapEquivalence,
    .postprocessedSideCoinMatchingObligation,
    .postprocessedSideCoinMatchingCardinalityBlock,
    .postprocessedSideCoinMatchingPredicateBlock,
    .postprocessedSidePredicateMatchingEquivalence,
    .postprocessedSideApproxIndependenceCoinMatchingEquivalence,
    .finitePreimagePostprocessingBlowup]

/-- Broad repair classes not closed by the finite-coin stack.  This repeats the
current gap list intentionally: the finite-coin stack is useful coverage inside
the same-source finite-count branch, not a stop-grade proof. -/
def finiteCoinStackUncoveredBroadRepairClasses : List PNPRepairClass :=
  [.residualSideInformation,
    .randomizedResidual,
    .approximateDecorrelation,
    .kpolyCompressionBridge]

/-- The finite-coin subrepair coverage list is exact. -/
theorem currentPNPFiniteCoinCoveredSubrepairs_exact
    (repair : PNPFiniteCoinSubrepairClass) :
    repair ∈ currentPNPFiniteCoinCoveredSubrepairs := by
  cases repair <;> simp [currentPNPFiniteCoinCoveredSubrepairs]

end Mettapedia.Computability.PNP
