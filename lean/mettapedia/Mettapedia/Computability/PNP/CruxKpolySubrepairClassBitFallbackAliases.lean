import Mettapedia.Computability.PNP.CruxKpolySubrepairClassBase
/-!
# Legacy flat names for PNP `Kpoly` bit-coded fallback subrepair classes

This module keeps the historical `PNPKpolySubrepairClass.foo` names while
the semantic class family lives in `PNPKpolyBitFallbackSubrepairClass`.
-/

namespace Mettapedia.Computability.PNP

namespace PNPKpolySubrepairClass

abbrev actualLocalBoundedSampleMajorityBitFallbackSparseThresholdERMVisibleBudgetBoundary : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackSparseThresholdERMVisibleBudgetBoundary
  /-- For a bit-coded structured fallback family, a target rule is realizable
  exactly when it lies in the radius-`sampleBound` Hamming cover of the lifted
  fallback codes. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackRadiusCoverBoundary : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackRadiusCoverBoundary
  /-- The same bit-coded structured fallback-family endpoint has predictor
  image covered by at most `2 ^ fallbackBits * |smallSubsets surface
  sampleBound|` rules. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackFinitePredictorCoverBoundary : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackFinitePredictorCoverBoundary
  /-- Full-rule expressivity of the bit-coded structured fallback-family
  endpoint is equivalent to the lifted radius-`sampleBound` Hamming cover
  already filling the whole exact-visible Boolean rule cube. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackRadiusCoverSurjectivityBoundary : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackRadiusCoverSurjectivityBoundary
  /-- Full-rule expressivity of the bit-coded structured fallback-family
  endpoint is equivalently the pointwise condition that every exact-visible
  rule lie within disagreement radius `sampleBound` of some fallback code. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackPointwiseRadiusCoverSurjectivityBoundary : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackPointwiseRadiusCoverSurjectivityBoundary
  /-- At full sample radius, any bit-coded structured fallback family is
  already full-rule expressive, independently of the fallback-bit budget. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackFullRadiusBoundary : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackFullRadiusBoundary
  /-- With zero fallback bits, a bounded-sample sparse-override endpoint is
  not full-rule expressive below the exact-visible alphabet size. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackZeroFallbackBitsDeficitObstruction : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackZeroFallbackBitsDeficitObstruction
  /-- With zero fallback bits, full-rule expressivity is exactly equivalent to
  allowing sampled overrides on the whole exact-visible alphabet. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackZeroFallbackBitsExactRadiusBoundary : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackZeroFallbackBitsExactRadiusBoundary
  /-- If a bit-coded structured fallback decoder is already full-rule
  expressive, then the bounded-sample wrapper still inherits the later
  lightest-point recovery threshold. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackRecoveryLightestPointBoundary : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackRecoveryLightestPointBoundary
  /-- For the canonical exact-visible truth-table fallback decoder, bounded
  sample-level plug-in majority is already full-rule expressive for every
  sample bound, so the wrapper contributes no `Kpoly` compression on that
  route by itself. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackExactDecoderFullRuleBoundary : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackExactDecoderFullRuleBoundary
  /-- For the same canonical exact-visible truth-table decoder, the weaker
  manuscript-facing shared sparse-threshold ERM packet already fails below the
  unconditional point-block visible-budget threshold. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackExactDecoderSparseThresholdERMVisibleBudgetBoundary : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackExactDecoderSparseThresholdERMVisibleBudgetBoundary
  /-- For the same canonical exact-visible truth-table decoder, the same
  point-block visible-budget gap already rules out every extractor for the
  shared sparse-threshold ERM packet. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackExactDecoderNoExtractorSparseThresholdERMVisibleBudgetBoundary : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackExactDecoderNoExtractorSparseThresholdERMVisibleBudgetBoundary
  /-- For the same canonical exact-visible truth-table decoder, any
  manuscript-facing sparse-threshold recovery packet must satisfy the
  unconditional visible-width ceiling. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackExactDecoderVisibleWidthBoundary : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackExactDecoderVisibleWidthBoundary
  /-- For the same canonical exact-visible truth-table decoder, any
  manuscript-facing sparse-threshold recovery packet must satisfy the
  intrinsic lightest-point threshold. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackExactDecoderLightestPointBoundary : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackExactDecoderLightestPointBoundary
  /-- For the same canonical exact-visible truth-table decoder, any
  manuscript-facing sparse-threshold recovery packet must satisfy both the
  visible-width ceiling and the lightest-point threshold; violating either
  rules the route out. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackExactDecoderJointRecoveryBoundary : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackExactDecoderJointRecoveryBoundary
  /-- For the same canonical exact-visible truth-table decoder, a visible-width
  gap alone already rules out every extractor. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackExactDecoderNoExtractorVisibleWidthBoundary : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackExactDecoderNoExtractorVisibleWidthBoundary
  /-- For the same canonical exact-visible truth-table decoder, falling below
  the intrinsic lightest-point threshold already rules out every extractor. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackExactDecoderNoExtractorLightestPointBoundary : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackExactDecoderNoExtractorLightestPointBoundary
  /-- For the same canonical exact-visible truth-table decoder, a visible-width
  gap or lightest-point deficit already rules out every extractor. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackExactDecoderNoExtractorJointRecoveryBoundary : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackExactDecoderNoExtractorJointRecoveryBoundary
  /-- For the same canonical exact-visible truth-table decoder, the wrapper
  already admits no clocked finite-learning payload below the exact-visible
  surface threshold. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackExactDecoderClockedPayloadObstruction : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackExactDecoderClockedPayloadObstruction
  /-- For a structured bit-coded fallback family, even a coarse polynomial
  envelope on sampled sparse overrides still forces the total fallback-plus-
  overhead bit budget to reach the exact-visible alphabet size under full-rule
  expressivity. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackPolynomialEnvelopeBudgetBoundary : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackPolynomialEnvelopeBudgetBoundary
  /-- If that same coarse polynomial sparse-override envelope fits into
  `overheadBits` bits but the total fallback-plus-overhead budget is still
  below the exact-visible alphabet size, the endpoint is not full-rule
  expressive. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackPolynomialEnvelopeSurjectivityObstruction : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackPolynomialEnvelopeSurjectivityObstruction
  /-- If a route separately budgets the sparse-override radius and visible
  alphabet base in bits, full-rule expressivity still forces the resulting
  additive fallback-plus-factor budget to reach the exact-visible alphabet
  size. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackFactorBudgetBoundary : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackFactorBudgetBoundary
  /-- The same separately-budgeted radius/base certificate still blocks the
  endpoint whenever its total fallback-plus-factor bit count stays below the
  exact-visible alphabet size. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackFactorSurjectivityObstruction : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackFactorSurjectivityObstruction
  /-- If a route states only raw-value bit bounds for the sample radius and
  visible alphabet size, the sparse-support envelope still pays one successor
  bit for each factor. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackSuccessorFactorBudgetBoundary : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackSuccessorFactorBudgetBoundary
  /-- The same raw-value radius/base certificate still blocks surjectivity once
  those two successor bits are paid and the total fallback-plus-factor budget
  remains below the exact-visible alphabet size. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackSuccessorFactorSurjectivityObstruction : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackSuccessorFactorSurjectivityObstruction
  /-- If a route budgets both the raw sample-radius value and the raw visible
  alphabet size value, the sparse-support envelope pays a successor bit for
  each of them. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackDoubleSuccessorFactorBudgetBoundary : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackDoubleSuccessorFactorBudgetBoundary
  /-- The same doubly raw-valued certificate still blocks surjectivity once
  both successor bits are paid and the total fallback-plus-factor budget stays
  below the exact-visible alphabet size. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackDoubleSuccessorFactorSurjectivityObstruction : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackDoubleSuccessorFactorSurjectivityObstruction
  /-- In the one-sample special case, the exact successor-count envelope
  already forces the fallback-plus-visible-bit budget to reach the exact-
  visible alphabet size. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackOneSampleBudgetBoundary : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackOneSampleBudgetBoundary
  /-- The same exact one-sample successor-count certificate blocks
  surjectivity whenever the fallback-plus-visible-bit budget stays strictly
  below the exact-visible alphabet size. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackOneSampleSurjectivityObstruction : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackOneSampleSurjectivityObstruction
  /-- If the one-sample route only budgets the raw visible alphabet size,
  the support envelope still pays one successor bit on that factor. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackOneSampleSuccessorBudgetBoundary : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackOneSampleSuccessorBudgetBoundary
  /-- The same raw one-sample visible-size certificate blocks surjectivity
  once that successor bit is paid and the total budget remains strictly below
  the exact-visible alphabet size. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackOneSampleSuccessorSurjectivityObstruction : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackOneSampleSuccessorSurjectivityObstruction
  /-- At zero sparse-support radius, full-rule expressivity already forces the
  fallback code itself to have at least the exact-visible alphabet size. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackZeroSampleBudgetBoundary : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackZeroSampleBudgetBoundary
  /-- The same zero-sample route is not surjective whenever the fallback code
  has strictly fewer bits than the exact-visible alphabet size. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackZeroSampleSurjectivityObstruction : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackZeroSampleSurjectivityObstruction
  /-- The zero-sample boundary is sharp: with the canonical exact-visible
  decoder, the bit-coded fallback endpoint is already fully expressive. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackZeroSampleExactDecoderBoundary : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackZeroSampleExactDecoderBoundary
  /-- At zero sparse-support radius, the canonical exact-visible truth-table
  decoder leaves no finite predictor-image cover below the full Boolean rule
  cube. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackZeroSampleExactDecoderFinitePredictorCoverObstruction : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackZeroSampleExactDecoderFinitePredictorCoverObstruction
  /-- At zero sparse-support radius, the same canonical exact-visible
  truth-table decoder leaves no finite selected-index representative cover
  below the full Boolean rule cube. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackZeroSampleExactDecoderFiniteIndexRepresentativeCoverObstruction : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackZeroSampleExactDecoderFiniteIndexRepresentativeCoverObstruction
  /-- At zero sparse-support radius, the same canonical exact-visible
  truth-table decoder leaves no finite quotient-code presentation below the
  full Boolean rule cube. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackZeroSampleExactDecoderFinitePredictorQuotientObstruction : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackZeroSampleExactDecoderFinitePredictorQuotientObstruction
  /-- At zero sparse-support radius, the same canonical exact-visible
  truth-table decoder admits no exact-visible compression target below the
  truth-table bit budget. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackZeroSampleExactDecoderExactVisibleCompressionObstruction : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackZeroSampleExactDecoderExactVisibleCompressionObstruction
  /-- At zero sparse-support radius, the same canonical exact-visible
  truth-table decoder admits no clocked exact-visible realization below the
  truth-table bit budget. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackZeroSampleExactDecoderClockedRealizationObstruction : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackZeroSampleExactDecoderClockedRealizationObstruction
  /-- At zero sparse-support radius, the same canonical exact-visible
  truth-table decoder admits no clocked finite-learning payload below the
  truth-table bit budget. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackZeroSampleExactDecoderClockedPayloadObstruction : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackZeroSampleExactDecoderClockedPayloadObstruction
  /-- At zero sparse-support radius, the wrapper contributes no hidden
  expressivity: surjectivity of the endpoint is equivalent to surjectivity of
  the fallback decoder itself. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackZeroSampleFallbackEquivalence : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackZeroSampleFallbackEquivalence
  /-- At zero sparse-support radius, the wrapper has exactly the same finite
  predictor-image covers as the raw fallback decoder family itself. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackZeroSampleFinitePredictorCoverBoundary : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackZeroSampleFinitePredictorCoverBoundary
  /-- At zero sparse-support radius, the wrapper has exactly the same finite
  selected-index representative covers as the raw fallback decoder family
  itself. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackZeroSampleFiniteIndexRepresentativeCoverBoundary : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackZeroSampleFiniteIndexRepresentativeCoverBoundary
  /-- At zero sparse-support radius, the wrapper has exactly the same finite
  quotient-code presentations as the raw fallback decoder family itself. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackZeroSampleFinitePredictorQuotientBoundary : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackZeroSampleFinitePredictorQuotientBoundary
  /-- Radius-zero exact visible compression claims for the wrapper are exactly
  the corresponding compression claims for the raw fallback decoder family. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackZeroSampleExactVisibleCompressionBoundary : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackZeroSampleExactVisibleCompressionBoundary
  /-- Radius-zero clocked exact-visible realization claims for the wrapper are
  exactly the corresponding claims for the raw fallback decoder family. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackZeroSampleClockedRealizationBoundary : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackZeroSampleClockedRealizationBoundary
  /-- Radius-zero clocked finite-learning payload claims for the wrapper are
  exactly the corresponding payload claims for the raw fallback decoder
  family. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackZeroSampleClockedPayloadBoundary : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackZeroSampleClockedPayloadBoundary
  /-- With one sampled sparse override, full-rule expressivity already forces
  the exact product budget `2 ^ fallbackBits * (surfaceCard + 1)`. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackOneSampleProductBoundary : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackOneSampleProductBoundary
  /-- The same exact one-sample product budget blocks surjectivity whenever it
  stays strictly below the full exact-visible Boolean rule cube. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackOneSampleProductSurjectivityObstruction : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackOneSampleProductSurjectivityObstruction
  /-- With two sampled sparse overrides, full-rule expressivity already forces
  the exact quadratic product budget `2 ^ fallbackBits * (1 + surfaceCard +
  choose surfaceCard 2)`. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackTwoSampleQuadraticProductBoundary : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackTwoSampleQuadraticProductBoundary
  /-- The same exact two-sample quadratic product budget blocks surjectivity
  whenever it stays strictly below the full exact-visible Boolean rule cube. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackTwoSampleQuadraticProductSurjectivityObstruction : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackTwoSampleQuadraticProductSurjectivityObstruction
  /-- If the exact two-sample quadratic support envelope fits into
  `overheadBits` bits, full-rule expressivity still forces the total fallback-
  plus-overhead bit budget to reach the exact-visible alphabet size. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackTwoSampleQuadraticEnvelopeBudgetBoundary : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackTwoSampleQuadraticEnvelopeBudgetBoundary
  /-- The same exact two-sample quadratic support envelope blocks surjectivity
  whenever the resulting fallback-plus-overhead bit budget stays strictly
  below the exact-visible alphabet size. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackTwoSampleQuadraticEnvelopeSurjectivityObstruction : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackTwoSampleQuadraticEnvelopeSurjectivityObstruction
  /-- Full-rule expressivity already forces the abstract sparse-support
  product budget `2 ^ fallbackBits * |smallSubsets surface sampleBound|`. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackSmallSubsetsProductBoundary : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackSmallSubsetsProductBoundary
  /-- The same abstract sparse-support product budget blocks surjectivity
  whenever it stays strictly below the full exact-visible Boolean rule cube. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackSmallSubsetsProductSurjectivityObstruction : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackSmallSubsetsProductSurjectivityObstruction
  /-- For the full exact bounded-sample support count, full-rule expressivity
  already forces the exact product budget
  `2 ^ fallbackBits * ∑_{i ≤ sampleBound} choose surfaceCard i`. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackSumChooseProductBoundary : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackSumChooseProductBoundary
  /-- The same exact bounded-sample product budget blocks surjectivity
  whenever it stays strictly below the full exact-visible Boolean rule cube. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackSumChooseProductSurjectivityObstruction : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackSumChooseProductSurjectivityObstruction
  /-- If the exact bounded-sample support envelope itself fits into
  `overheadBits` bits, full-rule expressivity still forces the total fallback-
  plus-overhead bit budget to reach the exact-visible alphabet size. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackSumChooseEnvelopeBudgetBoundary : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackSumChooseEnvelopeBudgetBoundary
  /-- The same exact bounded-sample support envelope blocks surjectivity
  whenever the resulting fallback-plus-overhead bit budget stays strictly
  below the exact-visible alphabet size. -/
abbrev actualLocalBoundedSampleMajorityBitFallbackSumChooseEnvelopeSurjectivityObstruction : PNPKpolySubrepairClass :=
  .bitFallback .actualLocalBoundedSampleMajorityBitFallbackSumChooseEnvelopeSurjectivityObstruction

end PNPKpolySubrepairClass

end Mettapedia.Computability.PNP
