import Mettapedia.Computability.PNP.CruxLedger
/-!
# PNP `Kpoly` observed-support bridge subrepair classes

Observed-output support, decoder, query, adaptive-query, and one-block subrepair classes.
-/

namespace Mettapedia.Computability.PNP

/-- Observed-output support, decoder, query, adaptive-query, and one-block subrepair classes. -/
inductive PNPKpolyObservedSupportSubrepairClass where
  | supportFullRuleObservedSmallNotExactVisibleCoverBoundary
  /-- The same observed-support regime still refutes every clocked
  finite-learning payload below exact-visible surface cardinality. -/
  | supportFullRuleNotClockedPayloadBelowSurfaceCard
  /-- If a uniform visible section exists, the observed block truth-table
  cover really does transfer to a finite predictor-image cover of the full
  exact-visible family. -/
  | supportFullRuleUniformSectionFinitePredictorCoverBoundary
  /-- Under the same uniform visible section, the observed-output bit budget
  lifts to a clocked finite-learning payload for the full exact-visible
  family at block cardinality. -/
  | supportFullRuleUniformSectionClockedPayloadBoundary
  /-- Any uniform visible section for the support-full-rule interface already
  forces the observed block support to be at least as large as the full
  exact-visible surface. -/
  | supportFullRuleUniformSectionSurfaceCardBoundary
  /-- Therefore no uniform visible section exists once the observed block
  support is smaller than the full exact-visible surface. -/
  | supportFullRuleNoUniformSectionBelowSurfaceCard
  /-- The observed block-output family is only the pullback of the full
  exact-visible family along the reachable-support map. -/
  | supportFullRuleOutputFamilyFactorBoundary
  /-- Therefore an injective observed-output quotient on full exact-visible
  rules already forces the reachable-support map to be surjective. -/
  | supportFullRuleObservedRuleInjectiveSurjectiveBoundary
  /-- In particular any exact decoder from observed block-output traces to
  full exact-visible rules already forces reachable-support surjectivity. -/
  | supportFullRuleExactDecoderSurjectiveBoundary
  /-- If observed block-output support is smaller than the exact-visible
  surface, the observed-output quotient map cannot be injective on full
  exact-visible rules. -/
  | supportFullRuleObservedRuleMapNoninjectiveBelowSurfaceCard
  /-- Under the same observed-support deficit, two distinct full exact-visible
  rules collapse to the same observed block-output trace. -/
  | supportFullRuleDistinctRulesSameOutputBelowSurfaceCard
  /-- Any property decoded from observed block-output traces must be constant
  on observed-output fibers of the full exact-visible family. -/
  | supportFullRulePropertyDecoderFiberConstancyBoundary
  /-- A downstream property is decodable from observed block-output traces
  exactly when it is constant on observed-output fibers. -/
  | supportFullRulePropertyDecoderIffFiberConstancyBoundary
  /-- Therefore any property separating two full rules with the same observed
  trace cannot be decoded from observed block-output traces. -/
  | supportFullRuleNoPropertyDecoderSameOutputBoundary
  /-- A single exact-visible point query is decodable from observed
  block-output traces exactly when that point lies in reachable support. -/
  | supportFullRuleEvalDecoderRangeBoundary
  /-- Decoding every exact-visible point query from observed block-output
  traces is equivalent to full reachable-support surjectivity. -/
  | supportFullRuleAllEvalDecodersSurjectiveBoundary
  /-- A whole family of exact-visible point queries is decodable from observed
  block-output traces exactly when every queried point lies in reachable
  support. -/
  | supportFullRuleQueryDecoderRangeBoundary
  /-- Any query family containing one unreachable exact-visible point is
  undecodable from observed block-output traces. -/
  | supportFullRuleNoQueryDecoderMissedQueryBoundary
  /-- An adaptive exact-visible query tree is decodable from observed
  block-output traces whenever all of its queried points lie in reachable
  support. -/
  | supportFullRuleAdaptiveQueryDecoderReachableBoundary
  /-- Such an adaptive exact-visible query tree is decodable exactly when its
  output is constant on observed-output fibers. -/
  | supportFullRuleAdaptiveQueryDecoderIffFiberConstancyBoundary
  /-- Any observed-output collision that separates an adaptive query tree
  refutes every observed-trace decoder for that tree. -/
  | supportFullRuleNoAdaptiveQueryDecoderSameOutputEvalBoundary
  /-- Missing a queried surface point already refutes every nontrivial root
  adaptive-query decoder over observed block-output traces. -/
  | supportFullRuleNoRootAdaptiveQueryDecoderMissedPointBoundary
  /-- If observed block-output support is smaller than the exact-visible
  surface, no post-processing decoder can recover every full exact-visible
  rule from the observed quotient. -/
  | supportFullRuleNoExactDecoderBelowSurfaceCard
  /-- Under the same observed-support deficit, at least one exact-visible
  point query remains undecodable from observed block-output traces. -/
  | supportFullRuleUnobservableEvalBelowSurfaceCard
  /-- The one-block actual-local interface already exhibits the small-support
  finite-cover / exact-visible-cover gap. -/
  | oneBlockFullRuleObservedSmallNotExactVisibleCoverBoundary
  /-- The same one-block actual-local interface already refutes every clocked
  finite-learning payload below exact-visible surface cardinality. -/
  | oneBlockFullRuleNotClockedPayloadBelowSurfaceCard
  /-- Once the exact-visible surface has more than one point, no decoder from
  the one-block observed quotient recovers every full exact-visible rule. -/
  | oneBlockFullRuleNoExactDecoderOneLtSurfaceCardBoundary
  /-- Under the same one-block cardinality hypothesis, at least one
  exact-visible point query remains unobservable from the observed quotient. -/
  | oneBlockFullRuleUnobservableEvalOneLtSurfaceCardBoundary
  deriving DecidableEq, Repr

end Mettapedia.Computability.PNP
