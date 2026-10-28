import Mettapedia.Computability.PNP.CruxKpolySubrepairClassBase
/-!
# Legacy flat names for PNP `Kpoly` observed-support bridge subrepair classes

This module keeps the historical `PNPKpolySubrepairClass.foo` names while
the semantic class family lives in `PNPKpolyObservedSupportSubrepairClass`.
-/

namespace Mettapedia.Computability.PNP

namespace PNPKpolySubrepairClass

abbrev supportFullRuleObservedSmallNotExactVisibleCoverBoundary : PNPKpolySubrepairClass :=
  .observedSupport .supportFullRuleObservedSmallNotExactVisibleCoverBoundary
  /-- The same observed-support regime still refutes every clocked
  finite-learning payload below exact-visible surface cardinality. -/
abbrev supportFullRuleNotClockedPayloadBelowSurfaceCard : PNPKpolySubrepairClass :=
  .observedSupport .supportFullRuleNotClockedPayloadBelowSurfaceCard
  /-- If a uniform visible section exists, the observed block truth-table
  cover really does transfer to a finite predictor-image cover of the full
  exact-visible family. -/
abbrev supportFullRuleUniformSectionFinitePredictorCoverBoundary : PNPKpolySubrepairClass :=
  .observedSupport .supportFullRuleUniformSectionFinitePredictorCoverBoundary
  /-- Under the same uniform visible section, the observed-output bit budget
  lifts to a clocked finite-learning payload for the full exact-visible
  family at block cardinality. -/
abbrev supportFullRuleUniformSectionClockedPayloadBoundary : PNPKpolySubrepairClass :=
  .observedSupport .supportFullRuleUniformSectionClockedPayloadBoundary
  /-- Any uniform visible section for the support-full-rule interface already
  forces the observed block support to be at least as large as the full
  exact-visible surface. -/
abbrev supportFullRuleUniformSectionSurfaceCardBoundary : PNPKpolySubrepairClass :=
  .observedSupport .supportFullRuleUniformSectionSurfaceCardBoundary
  /-- Therefore no uniform visible section exists once the observed block
  support is smaller than the full exact-visible surface. -/
abbrev supportFullRuleNoUniformSectionBelowSurfaceCard : PNPKpolySubrepairClass :=
  .observedSupport .supportFullRuleNoUniformSectionBelowSurfaceCard
  /-- The observed block-output family is only the pullback of the full
  exact-visible family along the reachable-support map. -/
abbrev supportFullRuleOutputFamilyFactorBoundary : PNPKpolySubrepairClass :=
  .observedSupport .supportFullRuleOutputFamilyFactorBoundary
  /-- Therefore an injective observed-output quotient on full exact-visible
  rules already forces the reachable-support map to be surjective. -/
abbrev supportFullRuleObservedRuleInjectiveSurjectiveBoundary : PNPKpolySubrepairClass :=
  .observedSupport .supportFullRuleObservedRuleInjectiveSurjectiveBoundary
  /-- In particular any exact decoder from observed block-output traces to
  full exact-visible rules already forces reachable-support surjectivity. -/
abbrev supportFullRuleExactDecoderSurjectiveBoundary : PNPKpolySubrepairClass :=
  .observedSupport .supportFullRuleExactDecoderSurjectiveBoundary
  /-- If observed block-output support is smaller than the exact-visible
  surface, the observed-output quotient map cannot be injective on full
  exact-visible rules. -/
abbrev supportFullRuleObservedRuleMapNoninjectiveBelowSurfaceCard : PNPKpolySubrepairClass :=
  .observedSupport .supportFullRuleObservedRuleMapNoninjectiveBelowSurfaceCard
  /-- Under the same observed-support deficit, two distinct full exact-visible
  rules collapse to the same observed block-output trace. -/
abbrev supportFullRuleDistinctRulesSameOutputBelowSurfaceCard : PNPKpolySubrepairClass :=
  .observedSupport .supportFullRuleDistinctRulesSameOutputBelowSurfaceCard
  /-- Any property decoded from observed block-output traces must be constant
  on observed-output fibers of the full exact-visible family. -/
abbrev supportFullRulePropertyDecoderFiberConstancyBoundary : PNPKpolySubrepairClass :=
  .observedSupport .supportFullRulePropertyDecoderFiberConstancyBoundary
  /-- A downstream property is decodable from observed block-output traces
  exactly when it is constant on observed-output fibers. -/
abbrev supportFullRulePropertyDecoderIffFiberConstancyBoundary : PNPKpolySubrepairClass :=
  .observedSupport .supportFullRulePropertyDecoderIffFiberConstancyBoundary
  /-- Therefore any property separating two full rules with the same observed
  trace cannot be decoded from observed block-output traces. -/
abbrev supportFullRuleNoPropertyDecoderSameOutputBoundary : PNPKpolySubrepairClass :=
  .observedSupport .supportFullRuleNoPropertyDecoderSameOutputBoundary
  /-- A single exact-visible point query is decodable from observed
  block-output traces exactly when that point lies in reachable support. -/
abbrev supportFullRuleEvalDecoderRangeBoundary : PNPKpolySubrepairClass :=
  .observedSupport .supportFullRuleEvalDecoderRangeBoundary
  /-- Decoding every exact-visible point query from observed block-output
  traces is equivalent to full reachable-support surjectivity. -/
abbrev supportFullRuleAllEvalDecodersSurjectiveBoundary : PNPKpolySubrepairClass :=
  .observedSupport .supportFullRuleAllEvalDecodersSurjectiveBoundary
  /-- A whole family of exact-visible point queries is decodable from observed
  block-output traces exactly when every queried point lies in reachable
  support. -/
abbrev supportFullRuleQueryDecoderRangeBoundary : PNPKpolySubrepairClass :=
  .observedSupport .supportFullRuleQueryDecoderRangeBoundary
  /-- Any query family containing one unreachable exact-visible point is
  undecodable from observed block-output traces. -/
abbrev supportFullRuleNoQueryDecoderMissedQueryBoundary : PNPKpolySubrepairClass :=
  .observedSupport .supportFullRuleNoQueryDecoderMissedQueryBoundary
  /-- An adaptive exact-visible query tree is decodable from observed
  block-output traces whenever all of its queried points lie in reachable
  support. -/
abbrev supportFullRuleAdaptiveQueryDecoderReachableBoundary : PNPKpolySubrepairClass :=
  .observedSupport .supportFullRuleAdaptiveQueryDecoderReachableBoundary
  /-- Such an adaptive exact-visible query tree is decodable exactly when its
  output is constant on observed-output fibers. -/
abbrev supportFullRuleAdaptiveQueryDecoderIffFiberConstancyBoundary : PNPKpolySubrepairClass :=
  .observedSupport .supportFullRuleAdaptiveQueryDecoderIffFiberConstancyBoundary
  /-- Any observed-output collision that separates an adaptive query tree
  refutes every observed-trace decoder for that tree. -/
abbrev supportFullRuleNoAdaptiveQueryDecoderSameOutputEvalBoundary : PNPKpolySubrepairClass :=
  .observedSupport .supportFullRuleNoAdaptiveQueryDecoderSameOutputEvalBoundary
  /-- Missing a queried surface point already refutes every nontrivial root
  adaptive-query decoder over observed block-output traces. -/
abbrev supportFullRuleNoRootAdaptiveQueryDecoderMissedPointBoundary : PNPKpolySubrepairClass :=
  .observedSupport .supportFullRuleNoRootAdaptiveQueryDecoderMissedPointBoundary
  /-- If observed block-output support is smaller than the exact-visible
  surface, no post-processing decoder can recover every full exact-visible
  rule from the observed quotient. -/
abbrev supportFullRuleNoExactDecoderBelowSurfaceCard : PNPKpolySubrepairClass :=
  .observedSupport .supportFullRuleNoExactDecoderBelowSurfaceCard
  /-- Under the same observed-support deficit, at least one exact-visible
  point query remains undecodable from observed block-output traces. -/
abbrev supportFullRuleUnobservableEvalBelowSurfaceCard : PNPKpolySubrepairClass :=
  .observedSupport .supportFullRuleUnobservableEvalBelowSurfaceCard
  /-- The one-block actual-local interface already exhibits the small-support
  finite-cover / exact-visible-cover gap. -/
abbrev oneBlockFullRuleObservedSmallNotExactVisibleCoverBoundary : PNPKpolySubrepairClass :=
  .observedSupport .oneBlockFullRuleObservedSmallNotExactVisibleCoverBoundary
  /-- The same one-block actual-local interface already refutes every clocked
  finite-learning payload below exact-visible surface cardinality. -/
abbrev oneBlockFullRuleNotClockedPayloadBelowSurfaceCard : PNPKpolySubrepairClass :=
  .observedSupport .oneBlockFullRuleNotClockedPayloadBelowSurfaceCard
  /-- Once the exact-visible surface has more than one point, no decoder from
  the one-block observed quotient recovers every full exact-visible rule. -/
abbrev oneBlockFullRuleNoExactDecoderOneLtSurfaceCardBoundary : PNPKpolySubrepairClass :=
  .observedSupport .oneBlockFullRuleNoExactDecoderOneLtSurfaceCardBoundary
  /-- Under the same one-block cardinality hypothesis, at least one
  exact-visible point query remains unobservable from the observed quotient. -/
abbrev oneBlockFullRuleUnobservableEvalOneLtSurfaceCardBoundary : PNPKpolySubrepairClass :=
  .observedSupport .oneBlockFullRuleUnobservableEvalOneLtSurfaceCardBoundary

end PNPKpolySubrepairClass

end Mettapedia.Computability.PNP
