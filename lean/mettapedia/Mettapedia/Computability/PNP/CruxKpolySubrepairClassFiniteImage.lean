import Mettapedia.Computability.PNP.CruxLedger
/-!
# PNP `Kpoly` finite-image bridge subrepair classes

Finite predictor-image, representative-index, quotient-code, factor-transport, pullback, product-bound, and fielded-switching bridge subrepair classes.
-/

namespace Mettapedia.Computability.PNP

/-- Finite predictor-image, representative-index, quotient-code, factor-transport, pullback, product-bound, and fielded-switching bridge subrepair classes. -/
inductive PNPKpolyFiniteImageSubrepairClass where
  | exactVisibleCompressionTargetPredictorCoverEquivalence
  /-- Clocked exact-visible realization targets are equivalently finite
  predictor-image covers at the same bit budget. -/
  | clockedExactVisibleRealizationPredictorCoverEquivalence
  /-- The bundled clocked finite-learning payload is equivalently a finite
  predictor-image cover at the same bit budget. -/
  | clockedFiniteLearningPayloadPredictorCoverEquivalence
  /-- The bundled clocked finite-learning payload is equivalently the exact
  visible compression target at the same bit budget. -/
  | clockedFiniteLearningPayloadExactVisibleCompressionEquivalence
  /-- Finite predictor-image covers are equivalently finite quotient-code
  presentations with an index encoder and predictor decoder. -/
  | finitePredictorQuotientEquivalence
  /-- Exact visible compression targets are equivalently finite quotient-code
  presentations at the same bit budget. -/
  | exactVisibleCompressionTargetPredictorQuotientEquivalence
  /-- Clocked exact-visible realization targets are equivalently finite
  quotient-code presentations at the same bit budget. -/
  | clockedExactVisibleRealizationPredictorQuotientEquivalence
  /-- Exact visible compression targets are equivalently finite
  representative-index covers at the same bit budget. -/
  | exactVisibleCompressionTargetRepresentativeIndexCoverEquivalence
  /-- Clocked exact-visible realization targets are equivalently finite
  representative-index covers at the same bit budget. -/
  | clockedExactVisibleRealizationRepresentativeIndexCoverEquivalence
  /-- Failure of clocked exact-visible realization is equivalently failure of
  a finite representative-index cover at the same bit budget. -/
  | notClockedExactVisibleRealizationRepresentativeIndexCoverEquivalence
  /-- Failure of clocked exact-visible realization is equivalently failure of
  a finite quotient-code presentation at the same bit budget. -/
  | notClockedExactVisibleRealizationPredictorQuotientEquivalence
  /-- A fully expressive exact visible family cannot have a finite
  predictor-image cover below the full Boolean classifier-space cardinality. -/
  | exactVisibleImageSurjectivityObstruction
  /-- The same fully expressive exact visible family cannot have a finite
  representative-index cover below the full Boolean classifier-space
  cardinality. -/
  | exactVisibleRepresentativeCoverSurjectivityObstruction
  /-- Nor can it have a finite quotient-code presentation below that full
  Boolean classifier-space cardinality. -/
  | exactVisiblePredictorQuotientSurjectivityObstruction
  /-- The same surjective exact-visible regime already blocks the clocked
  exact-visible realization target below the full predictor-image
  cardinality. -/
  | exactVisibleClockedRealizationSurjectivityObstruction
  /-- Any injectively indexed finite probe family already realized by the
  switched predictors gives the same finite-image lower bound, without needing
  full surjectivity onto every Boolean classifier. -/
  | injectiveFiniteProbeImageLowerBound
  /-- The same injective finite-probe realization bound also applies to finite
  representative-index covers. -/
  | injectiveFiniteRepresentativeIndexCoverLowerBound
  /-- And it equally applies to finite quotient-code presentations. -/
  | injectiveFinitePredictorQuotientLowerBound
  /-- The same injective finite-probe lower bound already blocks exact-visible
  compression below the realized probe cardinality. -/
  | injectiveFiniteProbeExactVisibleCompressionObstruction
  /-- And it equally blocks clocked exact-visible realization below that same
  realized probe cardinality. -/
  | injectiveFiniteProbeClockedRealizationObstruction
  /-- A fully expressive exact visible family already refutes the bundled
  clocked finite-learning payload below the full Boolean image size. -/
  | exactVisibleClockedFiniteLearningPayloadSurjectivityObstruction
  /-- Any injectively realized finite probe family already refutes the bundled
  clocked finite-learning payload below the realized probe cardinality. -/
  | injectiveFiniteProbeClockedFiniteLearningPayloadObstruction
  /-- The same surjectivity and finite-probe lower bounds jointly refute the
  bundled clocked finite-learning payload below the corresponding image size. -/
  | clockedFiniteLearningPayloadImageObstruction
  /-- A fully expressive exact-visible family forces every bundled clocked
  finite-learning payload to budget at least the full Boolean image size. -/
  | exactVisibleClockedFiniteLearningPayloadSurjectivityLowerBound
  /-- Any injectively realized finite probe family forces the bundled clocked
  finite-learning payload to budget at least the realized probe cardinality. -/
  | injectiveFiniteProbeClockedFiniteLearningPayloadLowerBound
  /-- A section-backed factorization through a fully expressive finite summary
  forces the same full-Boolean lower bound on the bundled clocked
  finite-learning payload. -/
  | sectionBackedClockedFiniteLearningPayloadSurjectiveLowerBound
  /-- Therefore such a section-backed fully expressive finite summary already
  refutes the bundled clocked finite-learning payload below its Boolean image
  size. -/
  | sectionBackedClockedFiniteLearningPayloadSurjectiveObstruction
  /-- Section-backed factor maps preserve injective finite-probe lower bounds
  for the bundled clocked finite-learning payload. -/
  | sectionBackedInjectiveFiniteProbeClockedFiniteLearningPayloadLowerBound
  /-- Hence section-backed pullbacks also refute the bundled clocked
  finite-learning payload below the realized probe cardinality. -/
  | sectionBackedInjectiveFiniteProbeClockedFiniteLearningPayloadObstruction
  /-- Section-backed factor maps preserve finite-probe lower bounds from a
  reduced view, without needing the reduced family to be fully surjective. -/
  | sectionBackedInjectiveFiniteProbePullbackLowerBound
  /-- The same section-backed pullback already refutes finite predictor-image
  covers below the realized probe cardinality. -/
  | sectionBackedInjectiveFiniteProbePullbackObstruction
  /-- Section-backed factor maps preserve the same finite-probe lower bound
  for representative-index covers. -/
  | sectionBackedInjectiveFiniteRepresentativeIndexCoverLowerBound
  /-- And therefore refute representative-index covers below the realized
  probe cardinality as well. -/
  | sectionBackedInjectiveFiniteRepresentativeIndexCoverObstruction
  /-- The same section-backed lower bound also transfers to finite
  quotient-code presentations. -/
  | sectionBackedInjectiveFinitePredictorQuotientLowerBound
  /-- Hence section-backed pullbacks also refute quotient-code presentations
  below the realized probe cardinality. -/
  | sectionBackedInjectiveFinitePredictorQuotientObstruction
  /-- Finite predictor-image covers are equivalently finite representative
  index covers using actual selected predictors. -/
  | finiteRepresentativeIndexCoverEquivalence
  /-- Finite predictor-image covers, representative-index covers, and
  quotient-code presentations are monotone in the allowed finite-image budget. -/
  | finiteImageCoverBudgetWeakening
  /-- Finite predictor-image covers are monotone in the allowed finite-image
  budget. -/
  | finitePredictorCoverBudgetWeakeningBoundary
  /-- Finite representative-index covers are monotone in the allowed
  finite-image budget. -/
  | finiteRepresentativeIndexCoverBudgetWeakeningBoundary
  /-- Finite quotient-code presentations are monotone in the allowed
  finite-image budget. -/
  | finitePredictorQuotientBudgetWeakeningBoundary
  /-- Finite predictor-image covers, representative-index covers, and
  quotient-code presentations transport across explicit factor maps, and push
  back along factorizations with a section. -/
  | finiteImageCoverFactorTransport
  /-- Finite predictor-image covers transport across explicit factor maps and
  push back along factorizations with a section. -/
  | finitePredictorCoverFactorTransportBoundary
  /-- Finite representative-index covers transport across explicit factor maps
  and push back along factorizations with a section. -/
  | finiteRepresentativeIndexCoverFactorTransportBoundary
  /-- Finite quotient-code presentations transport across explicit factor maps
  and push back along factorizations with a section. -/
  | finitePredictorQuotientFactorTransportBoundary
  /-- If a family factors through a finite summary with a section and the
  summary is fully expressive, finite predictor-image covers below the summary
  Boolean classifier-space cardinality are impossible. -/
  | sectionBackedFinitePredictorCoverSurjectiveObstruction
  /-- The same section-backed fully expressive finite-summary obstruction
  holds for representative-index covers. -/
  | sectionBackedFiniteRepresentativeIndexCoverSurjectiveObstruction
  /-- The same section-backed fully expressive finite-summary obstruction
  holds for quotient-code presentations. -/
  | sectionBackedFinitePredictorQuotientSurjectiveObstruction
  /-- A section-backed factorization through a fully expressive finite summary
  forces the same full-Boolean lower bound on predictor-image covers. -/
  | sectionBackedFinitePredictorCoverSurjectiveLowerBound
  /-- The same section-backed fully expressive finite-summary lower bound
  holds for representative-index covers. -/
  | sectionBackedFiniteRepresentativeIndexCoverSurjectiveLowerBound
  /-- The same section-backed fully expressive finite-summary lower bound
  holds for quotient-code presentations. -/
  | sectionBackedFinitePredictorQuotientSurjectiveLowerBound
  /-- A fully expressive finite family forces every finite predictor-image
  cover to have at least the full Boolean classifier-space cardinality. -/
  | surjectiveFinitePredictorCoverLowerBound
  /-- The same generic full-Boolean lower bound holds for representative-index
  covers. -/
  | surjectiveFiniteRepresentativeIndexCoverLowerBound
  /-- The same generic full-Boolean lower bound holds for quotient-code
  presentations. -/
  | surjectiveFinitePredictorQuotientLowerBound
  /-- If an exact family factors through `(a,b)` and the reduced family is
  still fully expressive, finite-image covers below the reduced Boolean
  classifier-space cardinality are impossible. -/
  | finiteImageReducedABPullbackObstruction
  /-- If an exact family factors through `(a,b)`, every injectively indexed
  finite probe family already realized on the reduced `(a,b)` view gives the
  same finite-image lower bound after pullback. -/
  | finiteImageReducedABInjectiveProbePullbackObstruction
  /-- The same reduced `(a,b)` pullback obstruction holds for finite
  quotient-code presentations. -/
  | finiteQuotientReducedABPullbackObstruction
  /-- Product-bound-only bridge schemas are exactly demands for finite
  predictor-image covers for every exact-visible family. -/
  | productBoundBridgeFiniteImageBoundary
  /-- Fixed-field switching-only bridge schemas are exactly demands for finite
  predictor-image covers for every exact-visible family. -/
  | fieldedSwitchingBridgeFiniteImageBoundary
  /-- Product-bound-only bridge schemas are refuted below the exact-visible
  surface threshold by the full exact-visible Boolean family. -/
  | productBoundOnlyFullVisibleObstruction
  /-- Fixed-field switching-only bridge schemas are refuted below the
  exact-visible surface threshold by the full exact-visible Boolean family. -/
  | fieldedSwitchingOnlyFullVisibleObstruction
  /-- Product-bound-only bridge schemas are refuted below the exact-visible
  surface threshold by any already-surjective exact-visible family. -/
  | productBoundOnlySurjectiveVisibleObstruction
  /-- Fixed-field switching-only bridge schemas are refuted below the
  exact-visible surface threshold by any already-surjective exact-visible
  family. -/
  | fieldedSwitchingOnlySurjectiveVisibleObstruction
  /-- Product-bound-only bridge schemas to the full clocked finite-learning
  payload are still exactly demands for finite predictor-image covers. -/
  | productBoundClockedPayloadBridgeFiniteImageBoundary
  /-- Fixed-field switching-only bridge schemas to the full clocked
  finite-learning payload are still exactly demands for finite predictor-image
  covers. -/
  | fieldedSwitchingClockedPayloadBridgeFiniteImageBoundary
  /-- Product-bound-only clocked-payload bridge schemas are refuted below the
  exact-visible surface threshold by the full exact-visible Boolean family. -/
  | productBoundOnlyClockedPayloadFullVisibleObstruction
  /-- Fixed-field switching-only clocked-payload bridge schemas are refuted
  below the exact-visible surface threshold by the full exact-visible Boolean
  family. -/
  | fieldedSwitchingOnlyClockedPayloadFullVisibleObstruction
  /-- Product-bound-only clocked-payload bridge schemas are refuted below the
  Boolean predictor-space threshold by any already-surjective exact-visible
  family. -/
  | productBoundOnlyClockedPayloadSurjectiveVisibleObstruction
  /-- Fixed-field switching-only clocked-payload bridge schemas are refuted
  below the Boolean predictor-space threshold by any already-surjective
  exact-visible family. -/
  | fieldedSwitchingOnlyClockedPayloadSurjectiveVisibleObstruction
  /-- On bit-valued latent data, once the visible width is at least `2`, every
  actual switched-history exact-visible wrapper with budget
  `s ≤ n + 2*k + 1` is already impossible under true fielded switching and
  surjectivity of the actual switched family. -/
  | actualSwitchedHistoryBitVecFullWidthIntervalObstruction
  /-- The same full-width interval obstruction holds for the actual
  switched-history clocked finite-learning wrapper. -/
  | actualSwitchedHistoryBitVecFullWidthIntervalClockedPayloadObstruction
  deriving DecidableEq, Repr

end Mettapedia.Computability.PNP
