import Mettapedia.Computability.PNP.CruxKpolySubrepairClassBase
/-!
# Legacy flat names for PNP `Kpoly` finite-image bridge subrepair classes

This module keeps the historical `PNPKpolySubrepairClass.foo` names while
the semantic class family lives in `PNPKpolyFiniteImageSubrepairClass`.
-/

namespace Mettapedia.Computability.PNP

namespace PNPKpolySubrepairClass

abbrev exactVisibleCompressionTargetPredictorCoverEquivalence : PNPKpolySubrepairClass :=
  .finiteImage .exactVisibleCompressionTargetPredictorCoverEquivalence
  /-- Clocked exact-visible realization targets are equivalently finite
  predictor-image covers at the same bit budget. -/
abbrev clockedExactVisibleRealizationPredictorCoverEquivalence : PNPKpolySubrepairClass :=
  .finiteImage .clockedExactVisibleRealizationPredictorCoverEquivalence
  /-- The bundled clocked finite-learning payload is equivalently a finite
  predictor-image cover at the same bit budget. -/
abbrev clockedFiniteLearningPayloadPredictorCoverEquivalence : PNPKpolySubrepairClass :=
  .finiteImage .clockedFiniteLearningPayloadPredictorCoverEquivalence
  /-- The bundled clocked finite-learning payload is equivalently the exact
  visible compression target at the same bit budget. -/
abbrev clockedFiniteLearningPayloadExactVisibleCompressionEquivalence : PNPKpolySubrepairClass :=
  .finiteImage .clockedFiniteLearningPayloadExactVisibleCompressionEquivalence
  /-- Finite predictor-image covers are equivalently finite quotient-code
  presentations with an index encoder and predictor decoder. -/
abbrev finitePredictorQuotientEquivalence : PNPKpolySubrepairClass :=
  .finiteImage .finitePredictorQuotientEquivalence
  /-- Exact visible compression targets are equivalently finite quotient-code
  presentations at the same bit budget. -/
abbrev exactVisibleCompressionTargetPredictorQuotientEquivalence : PNPKpolySubrepairClass :=
  .finiteImage .exactVisibleCompressionTargetPredictorQuotientEquivalence
  /-- Clocked exact-visible realization targets are equivalently finite
  quotient-code presentations at the same bit budget. -/
abbrev clockedExactVisibleRealizationPredictorQuotientEquivalence : PNPKpolySubrepairClass :=
  .finiteImage .clockedExactVisibleRealizationPredictorQuotientEquivalence
  /-- Exact visible compression targets are equivalently finite
  representative-index covers at the same bit budget. -/
abbrev exactVisibleCompressionTargetRepresentativeIndexCoverEquivalence : PNPKpolySubrepairClass :=
  .finiteImage .exactVisibleCompressionTargetRepresentativeIndexCoverEquivalence
  /-- Clocked exact-visible realization targets are equivalently finite
  representative-index covers at the same bit budget. -/
abbrev clockedExactVisibleRealizationRepresentativeIndexCoverEquivalence : PNPKpolySubrepairClass :=
  .finiteImage .clockedExactVisibleRealizationRepresentativeIndexCoverEquivalence
  /-- Failure of clocked exact-visible realization is equivalently failure of
  a finite representative-index cover at the same bit budget. -/
abbrev notClockedExactVisibleRealizationRepresentativeIndexCoverEquivalence : PNPKpolySubrepairClass :=
  .finiteImage .notClockedExactVisibleRealizationRepresentativeIndexCoverEquivalence
  /-- Failure of clocked exact-visible realization is equivalently failure of
  a finite quotient-code presentation at the same bit budget. -/
abbrev notClockedExactVisibleRealizationPredictorQuotientEquivalence : PNPKpolySubrepairClass :=
  .finiteImage .notClockedExactVisibleRealizationPredictorQuotientEquivalence
  /-- A fully expressive exact visible family cannot have a finite
  predictor-image cover below the full Boolean classifier-space cardinality. -/
abbrev exactVisibleImageSurjectivityObstruction : PNPKpolySubrepairClass :=
  .finiteImage .exactVisibleImageSurjectivityObstruction
  /-- The same fully expressive exact visible family cannot have a finite
  representative-index cover below the full Boolean classifier-space
  cardinality. -/
abbrev exactVisibleRepresentativeCoverSurjectivityObstruction : PNPKpolySubrepairClass :=
  .finiteImage .exactVisibleRepresentativeCoverSurjectivityObstruction
  /-- Nor can it have a finite quotient-code presentation below that full
  Boolean classifier-space cardinality. -/
abbrev exactVisiblePredictorQuotientSurjectivityObstruction : PNPKpolySubrepairClass :=
  .finiteImage .exactVisiblePredictorQuotientSurjectivityObstruction
  /-- The same surjective exact-visible regime already blocks the clocked
  exact-visible realization target below the full predictor-image
  cardinality. -/
abbrev exactVisibleClockedRealizationSurjectivityObstruction : PNPKpolySubrepairClass :=
  .finiteImage .exactVisibleClockedRealizationSurjectivityObstruction
  /-- Any injectively indexed finite probe family already realized by the
  switched predictors gives the same finite-image lower bound, without needing
  full surjectivity onto every Boolean classifier. -/
abbrev injectiveFiniteProbeImageLowerBound : PNPKpolySubrepairClass :=
  .finiteImage .injectiveFiniteProbeImageLowerBound
  /-- The same injective finite-probe realization bound also applies to finite
  representative-index covers. -/
abbrev injectiveFiniteRepresentativeIndexCoverLowerBound : PNPKpolySubrepairClass :=
  .finiteImage .injectiveFiniteRepresentativeIndexCoverLowerBound
  /-- And it equally applies to finite quotient-code presentations. -/
abbrev injectiveFinitePredictorQuotientLowerBound : PNPKpolySubrepairClass :=
  .finiteImage .injectiveFinitePredictorQuotientLowerBound
  /-- The same injective finite-probe lower bound already blocks exact-visible
  compression below the realized probe cardinality. -/
abbrev injectiveFiniteProbeExactVisibleCompressionObstruction : PNPKpolySubrepairClass :=
  .finiteImage .injectiveFiniteProbeExactVisibleCompressionObstruction
  /-- And it equally blocks clocked exact-visible realization below that same
  realized probe cardinality. -/
abbrev injectiveFiniteProbeClockedRealizationObstruction : PNPKpolySubrepairClass :=
  .finiteImage .injectiveFiniteProbeClockedRealizationObstruction
  /-- A fully expressive exact visible family already refutes the bundled
  clocked finite-learning payload below the full Boolean image size. -/
abbrev exactVisibleClockedFiniteLearningPayloadSurjectivityObstruction : PNPKpolySubrepairClass :=
  .finiteImage .exactVisibleClockedFiniteLearningPayloadSurjectivityObstruction
  /-- Any injectively realized finite probe family already refutes the bundled
  clocked finite-learning payload below the realized probe cardinality. -/
abbrev injectiveFiniteProbeClockedFiniteLearningPayloadObstruction : PNPKpolySubrepairClass :=
  .finiteImage .injectiveFiniteProbeClockedFiniteLearningPayloadObstruction
  /-- The same surjectivity and finite-probe lower bounds jointly refute the
  bundled clocked finite-learning payload below the corresponding image size. -/
abbrev clockedFiniteLearningPayloadImageObstruction : PNPKpolySubrepairClass :=
  .finiteImage .clockedFiniteLearningPayloadImageObstruction
  /-- A fully expressive exact-visible family forces every bundled clocked
  finite-learning payload to budget at least the full Boolean image size. -/
abbrev exactVisibleClockedFiniteLearningPayloadSurjectivityLowerBound : PNPKpolySubrepairClass :=
  .finiteImage .exactVisibleClockedFiniteLearningPayloadSurjectivityLowerBound
  /-- Any injectively realized finite probe family forces the bundled clocked
  finite-learning payload to budget at least the realized probe cardinality. -/
abbrev injectiveFiniteProbeClockedFiniteLearningPayloadLowerBound : PNPKpolySubrepairClass :=
  .finiteImage .injectiveFiniteProbeClockedFiniteLearningPayloadLowerBound
  /-- A section-backed factorization through a fully expressive finite summary
  forces the same full-Boolean lower bound on the bundled clocked
  finite-learning payload. -/
abbrev sectionBackedClockedFiniteLearningPayloadSurjectiveLowerBound : PNPKpolySubrepairClass :=
  .finiteImage .sectionBackedClockedFiniteLearningPayloadSurjectiveLowerBound
  /-- Therefore such a section-backed fully expressive finite summary already
  refutes the bundled clocked finite-learning payload below its Boolean image
  size. -/
abbrev sectionBackedClockedFiniteLearningPayloadSurjectiveObstruction : PNPKpolySubrepairClass :=
  .finiteImage .sectionBackedClockedFiniteLearningPayloadSurjectiveObstruction
  /-- Section-backed factor maps preserve injective finite-probe lower bounds
  for the bundled clocked finite-learning payload. -/
abbrev sectionBackedInjectiveFiniteProbeClockedFiniteLearningPayloadLowerBound : PNPKpolySubrepairClass :=
  .finiteImage .sectionBackedInjectiveFiniteProbeClockedFiniteLearningPayloadLowerBound
  /-- Hence section-backed pullbacks also refute the bundled clocked
  finite-learning payload below the realized probe cardinality. -/
abbrev sectionBackedInjectiveFiniteProbeClockedFiniteLearningPayloadObstruction : PNPKpolySubrepairClass :=
  .finiteImage .sectionBackedInjectiveFiniteProbeClockedFiniteLearningPayloadObstruction
  /-- Section-backed factor maps preserve finite-probe lower bounds from a
  reduced view, without needing the reduced family to be fully surjective. -/
abbrev sectionBackedInjectiveFiniteProbePullbackLowerBound : PNPKpolySubrepairClass :=
  .finiteImage .sectionBackedInjectiveFiniteProbePullbackLowerBound
  /-- The same section-backed pullback already refutes finite predictor-image
  covers below the realized probe cardinality. -/
abbrev sectionBackedInjectiveFiniteProbePullbackObstruction : PNPKpolySubrepairClass :=
  .finiteImage .sectionBackedInjectiveFiniteProbePullbackObstruction
  /-- Section-backed factor maps preserve the same finite-probe lower bound
  for representative-index covers. -/
abbrev sectionBackedInjectiveFiniteRepresentativeIndexCoverLowerBound : PNPKpolySubrepairClass :=
  .finiteImage .sectionBackedInjectiveFiniteRepresentativeIndexCoverLowerBound
  /-- And therefore refute representative-index covers below the realized
  probe cardinality as well. -/
abbrev sectionBackedInjectiveFiniteRepresentativeIndexCoverObstruction : PNPKpolySubrepairClass :=
  .finiteImage .sectionBackedInjectiveFiniteRepresentativeIndexCoverObstruction
  /-- The same section-backed lower bound also transfers to finite
  quotient-code presentations. -/
abbrev sectionBackedInjectiveFinitePredictorQuotientLowerBound : PNPKpolySubrepairClass :=
  .finiteImage .sectionBackedInjectiveFinitePredictorQuotientLowerBound
  /-- Hence section-backed pullbacks also refute quotient-code presentations
  below the realized probe cardinality. -/
abbrev sectionBackedInjectiveFinitePredictorQuotientObstruction : PNPKpolySubrepairClass :=
  .finiteImage .sectionBackedInjectiveFinitePredictorQuotientObstruction
  /-- Finite predictor-image covers are equivalently finite representative
  index covers using actual selected predictors. -/
abbrev finiteRepresentativeIndexCoverEquivalence : PNPKpolySubrepairClass :=
  .finiteImage .finiteRepresentativeIndexCoverEquivalence
  /-- Finite predictor-image covers, representative-index covers, and
  quotient-code presentations are monotone in the allowed finite-image budget. -/
abbrev finiteImageCoverBudgetWeakening : PNPKpolySubrepairClass :=
  .finiteImage .finiteImageCoverBudgetWeakening
  /-- Finite predictor-image covers are monotone in the allowed finite-image
  budget. -/
abbrev finitePredictorCoverBudgetWeakeningBoundary : PNPKpolySubrepairClass :=
  .finiteImage .finitePredictorCoverBudgetWeakeningBoundary
  /-- Finite representative-index covers are monotone in the allowed
  finite-image budget. -/
abbrev finiteRepresentativeIndexCoverBudgetWeakeningBoundary : PNPKpolySubrepairClass :=
  .finiteImage .finiteRepresentativeIndexCoverBudgetWeakeningBoundary
  /-- Finite quotient-code presentations are monotone in the allowed
  finite-image budget. -/
abbrev finitePredictorQuotientBudgetWeakeningBoundary : PNPKpolySubrepairClass :=
  .finiteImage .finitePredictorQuotientBudgetWeakeningBoundary
  /-- Finite predictor-image covers, representative-index covers, and
  quotient-code presentations transport across explicit factor maps, and push
  back along factorizations with a section. -/
abbrev finiteImageCoverFactorTransport : PNPKpolySubrepairClass :=
  .finiteImage .finiteImageCoverFactorTransport
  /-- Finite predictor-image covers transport across explicit factor maps and
  push back along factorizations with a section. -/
abbrev finitePredictorCoverFactorTransportBoundary : PNPKpolySubrepairClass :=
  .finiteImage .finitePredictorCoverFactorTransportBoundary
  /-- Finite representative-index covers transport across explicit factor maps
  and push back along factorizations with a section. -/
abbrev finiteRepresentativeIndexCoverFactorTransportBoundary : PNPKpolySubrepairClass :=
  .finiteImage .finiteRepresentativeIndexCoverFactorTransportBoundary
  /-- Finite quotient-code presentations transport across explicit factor maps
  and push back along factorizations with a section. -/
abbrev finitePredictorQuotientFactorTransportBoundary : PNPKpolySubrepairClass :=
  .finiteImage .finitePredictorQuotientFactorTransportBoundary
  /-- If a family factors through a finite summary with a section and the
  summary is fully expressive, finite predictor-image covers below the summary
  Boolean classifier-space cardinality are impossible. -/
abbrev sectionBackedFinitePredictorCoverSurjectiveObstruction : PNPKpolySubrepairClass :=
  .finiteImage .sectionBackedFinitePredictorCoverSurjectiveObstruction
  /-- The same section-backed fully expressive finite-summary obstruction
  holds for representative-index covers. -/
abbrev sectionBackedFiniteRepresentativeIndexCoverSurjectiveObstruction : PNPKpolySubrepairClass :=
  .finiteImage .sectionBackedFiniteRepresentativeIndexCoverSurjectiveObstruction
  /-- The same section-backed fully expressive finite-summary obstruction
  holds for quotient-code presentations. -/
abbrev sectionBackedFinitePredictorQuotientSurjectiveObstruction : PNPKpolySubrepairClass :=
  .finiteImage .sectionBackedFinitePredictorQuotientSurjectiveObstruction
  /-- A section-backed factorization through a fully expressive finite summary
  forces the same full-Boolean lower bound on predictor-image covers. -/
abbrev sectionBackedFinitePredictorCoverSurjectiveLowerBound : PNPKpolySubrepairClass :=
  .finiteImage .sectionBackedFinitePredictorCoverSurjectiveLowerBound
  /-- The same section-backed fully expressive finite-summary lower bound
  holds for representative-index covers. -/
abbrev sectionBackedFiniteRepresentativeIndexCoverSurjectiveLowerBound : PNPKpolySubrepairClass :=
  .finiteImage .sectionBackedFiniteRepresentativeIndexCoverSurjectiveLowerBound
  /-- The same section-backed fully expressive finite-summary lower bound
  holds for quotient-code presentations. -/
abbrev sectionBackedFinitePredictorQuotientSurjectiveLowerBound : PNPKpolySubrepairClass :=
  .finiteImage .sectionBackedFinitePredictorQuotientSurjectiveLowerBound
  /-- A fully expressive finite family forces every finite predictor-image
  cover to have at least the full Boolean classifier-space cardinality. -/
abbrev surjectiveFinitePredictorCoverLowerBound : PNPKpolySubrepairClass :=
  .finiteImage .surjectiveFinitePredictorCoverLowerBound
  /-- The same generic full-Boolean lower bound holds for representative-index
  covers. -/
abbrev surjectiveFiniteRepresentativeIndexCoverLowerBound : PNPKpolySubrepairClass :=
  .finiteImage .surjectiveFiniteRepresentativeIndexCoverLowerBound
  /-- The same generic full-Boolean lower bound holds for quotient-code
  presentations. -/
abbrev surjectiveFinitePredictorQuotientLowerBound : PNPKpolySubrepairClass :=
  .finiteImage .surjectiveFinitePredictorQuotientLowerBound
  /-- If an exact family factors through `(a,b)` and the reduced family is
  still fully expressive, finite-image covers below the reduced Boolean
  classifier-space cardinality are impossible. -/
abbrev finiteImageReducedABPullbackObstruction : PNPKpolySubrepairClass :=
  .finiteImage .finiteImageReducedABPullbackObstruction
  /-- If an exact family factors through `(a,b)`, every injectively indexed
  finite probe family already realized on the reduced `(a,b)` view gives the
  same finite-image lower bound after pullback. -/
abbrev finiteImageReducedABInjectiveProbePullbackObstruction : PNPKpolySubrepairClass :=
  .finiteImage .finiteImageReducedABInjectiveProbePullbackObstruction
  /-- The same reduced `(a,b)` pullback obstruction holds for finite
  quotient-code presentations. -/
abbrev finiteQuotientReducedABPullbackObstruction : PNPKpolySubrepairClass :=
  .finiteImage .finiteQuotientReducedABPullbackObstruction
  /-- Product-bound-only bridge schemas are exactly demands for finite
  predictor-image covers for every exact-visible family. -/
abbrev productBoundBridgeFiniteImageBoundary : PNPKpolySubrepairClass :=
  .finiteImage .productBoundBridgeFiniteImageBoundary
  /-- Fixed-field switching-only bridge schemas are exactly demands for finite
  predictor-image covers for every exact-visible family. -/
abbrev fieldedSwitchingBridgeFiniteImageBoundary : PNPKpolySubrepairClass :=
  .finiteImage .fieldedSwitchingBridgeFiniteImageBoundary
  /-- Product-bound-only bridge schemas are refuted below the exact-visible
  surface threshold by the full exact-visible Boolean family. -/
abbrev productBoundOnlyFullVisibleObstruction : PNPKpolySubrepairClass :=
  .finiteImage .productBoundOnlyFullVisibleObstruction
  /-- Fixed-field switching-only bridge schemas are refuted below the
  exact-visible surface threshold by the full exact-visible Boolean family. -/
abbrev fieldedSwitchingOnlyFullVisibleObstruction : PNPKpolySubrepairClass :=
  .finiteImage .fieldedSwitchingOnlyFullVisibleObstruction
  /-- Product-bound-only bridge schemas are refuted below the exact-visible
  surface threshold by any already-surjective exact-visible family. -/
abbrev productBoundOnlySurjectiveVisibleObstruction : PNPKpolySubrepairClass :=
  .finiteImage .productBoundOnlySurjectiveVisibleObstruction
  /-- Fixed-field switching-only bridge schemas are refuted below the
  exact-visible surface threshold by any already-surjective exact-visible
  family. -/
abbrev fieldedSwitchingOnlySurjectiveVisibleObstruction : PNPKpolySubrepairClass :=
  .finiteImage .fieldedSwitchingOnlySurjectiveVisibleObstruction
  /-- Product-bound-only bridge schemas to the full clocked finite-learning
  payload are still exactly demands for finite predictor-image covers. -/
abbrev productBoundClockedPayloadBridgeFiniteImageBoundary : PNPKpolySubrepairClass :=
  .finiteImage .productBoundClockedPayloadBridgeFiniteImageBoundary
  /-- Fixed-field switching-only bridge schemas to the full clocked
  finite-learning payload are still exactly demands for finite predictor-image
  covers. -/
abbrev fieldedSwitchingClockedPayloadBridgeFiniteImageBoundary : PNPKpolySubrepairClass :=
  .finiteImage .fieldedSwitchingClockedPayloadBridgeFiniteImageBoundary
  /-- Product-bound-only clocked-payload bridge schemas are refuted below the
  exact-visible surface threshold by the full exact-visible Boolean family. -/
abbrev productBoundOnlyClockedPayloadFullVisibleObstruction : PNPKpolySubrepairClass :=
  .finiteImage .productBoundOnlyClockedPayloadFullVisibleObstruction
  /-- Fixed-field switching-only clocked-payload bridge schemas are refuted
  below the exact-visible surface threshold by the full exact-visible Boolean
  family. -/
abbrev fieldedSwitchingOnlyClockedPayloadFullVisibleObstruction : PNPKpolySubrepairClass :=
  .finiteImage .fieldedSwitchingOnlyClockedPayloadFullVisibleObstruction
  /-- Product-bound-only clocked-payload bridge schemas are refuted below the
  Boolean predictor-space threshold by any already-surjective exact-visible
  family. -/
abbrev productBoundOnlyClockedPayloadSurjectiveVisibleObstruction : PNPKpolySubrepairClass :=
  .finiteImage .productBoundOnlyClockedPayloadSurjectiveVisibleObstruction
  /-- Fixed-field switching-only clocked-payload bridge schemas are refuted
  below the Boolean predictor-space threshold by any already-surjective
  exact-visible family. -/
abbrev fieldedSwitchingOnlyClockedPayloadSurjectiveVisibleObstruction : PNPKpolySubrepairClass :=
  .finiteImage .fieldedSwitchingOnlyClockedPayloadSurjectiveVisibleObstruction
  /-- On bit-valued latent data, once the visible width is at least `2`, every
  actual switched-history exact-visible wrapper with budget
  `s ≤ n + 2*k + 1` is already impossible under true fielded switching and
  surjectivity of the actual switched family. -/
abbrev actualSwitchedHistoryBitVecFullWidthIntervalObstruction : PNPKpolySubrepairClass :=
  .finiteImage .actualSwitchedHistoryBitVecFullWidthIntervalObstruction
  /-- The same full-width interval obstruction holds for the actual
  switched-history clocked finite-learning wrapper. -/
abbrev actualSwitchedHistoryBitVecFullWidthIntervalClockedPayloadObstruction : PNPKpolySubrepairClass :=
  .finiteImage .actualSwitchedHistoryBitVecFullWidthIntervalClockedPayloadObstruction

end PNPKpolySubrepairClass

end Mettapedia.Computability.PNP
