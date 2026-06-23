import Mettapedia.Computability.PNP.ClockedKpolyGapAssessment
import Mettapedia.Computability.PNP.CruxKpolyBitFallbackZeroSampleObstructions

/-!
# PNP `Kpoly` bit-fallback zero-sample equivalence anchors

This module isolates the zero-sample equivalences between the bounded-sample
wrapper and the raw fallback decoder family for covers, compression,
realization, and clocked finite-learning payloads.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- Route-coverage anchor: with no sampled overrides, a bit-coded structured
fallback endpoint is full-rule expressive exactly when its fallback decoder is
full-rule expressive. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_zeroSample_surjective_iff_fallback_surjective
    {Z : Type v} {k fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k) :
    Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 0 fallbackBits fallback).predictorFamily.predict ↔
      Function.Surjective fallback :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_zeroSample_surjective_iff_fallback_surjective
    (Z := Z) (k := k) (fallbackBits := fallbackBits) fallback

/-- Route-coverage anchor: at zero sample radius, the wrapper has exactly the
same finite predictor-image covers as the raw fallback decoder family. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_zeroSample_finitePredictorCover_iff_fallbackDecoderFamily
    {Z : Type v} {k fallbackBits N : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k) :
    (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 0 fallbackBits fallback).predictorFamily.FinitePredictorCover N ↔
      (BitFallbackZeroSampleImage.fallbackDecoderFamily fallback).FinitePredictorCover N := by
  simpa [BitFallbackZeroSampleImage.zeroSampleWrapperFamily] using
    (BitFallbackZeroSampleImage.finitePredictorCover_iff_fallbackDecoderFamily
      (Z := Z) (k := k) (fallbackBits := fallbackBits) (N := N) fallback)

/-- Route-coverage anchor: at zero sample radius, finite selected-index
representative covers of the wrapper are exactly those of the raw fallback
decoder family. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_zeroSample_finiteIndexRepresentativeCover_iff_fallbackDecoderFamily
    {Z : Type v} {k fallbackBits N : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k) :
    (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 0 fallbackBits fallback).predictorFamily.FiniteIndexRepresentativeCover N ↔
      (BitFallbackZeroSampleImage.fallbackDecoderFamily fallback).FiniteIndexRepresentativeCover N := by
  simpa [BitFallbackZeroSampleImage.zeroSampleWrapperFamily] using
    (BitFallbackZeroSampleImage.finiteIndexRepresentativeCover_iff_fallbackDecoderFamily
      (Z := Z) (k := k) (fallbackBits := fallbackBits) (N := N) fallback)

/-- Route-coverage anchor: at zero sample radius, finite quotient-code
presentations of the wrapper are exactly those of the raw fallback decoder
family. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_zeroSample_finitePredictorQuotient_iff_fallbackDecoderFamily
    {Z : Type v} {k fallbackBits N : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k) :
    (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 0 fallbackBits fallback).predictorFamily.FinitePredictorQuotient N ↔
      (BitFallbackZeroSampleImage.fallbackDecoderFamily fallback).FinitePredictorQuotient N := by
  simpa [BitFallbackZeroSampleImage.zeroSampleWrapperFamily] using
    (BitFallbackZeroSampleImage.finitePredictorQuotient_iff_fallbackDecoderFamily
      (Z := Z) (k := k) (fallbackBits := fallbackBits) (N := N) fallback)

/-- Route-coverage anchor: at zero sample radius, exact visible compression of
the wrapper is exactly exact visible compression of the raw fallback decoder
family. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_zeroSample_exactVisibleCompressionTarget_iff_fallbackDecoderFamily
    {Z : Type v} {k fallbackBits s : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k) :
    ExactVisibleCompressionTarget
        (Z := Z) (k := k)
        (Index := BitFallbackZeroSampleImage.ZeroSampleIndex Z k fallbackBits)
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 0 fallbackBits fallback).predictorFamily s ↔
      ExactVisibleCompressionTarget
        (Z := Z) (k := k)
        (Index := BitCode fallbackBits)
        (BitFallbackZeroSampleImage.fallbackDecoderFamily fallback) s := by
  simpa [BitFallbackZeroSampleImage.zeroSampleWrapperFamily] using
    (BitFallbackZeroSampleImage.exactVisibleCompressionTarget_iff_fallbackDecoderFamily
      (Z := Z) (k := k) (fallbackBits := fallbackBits) (s := s) fallback)

/-- Route-coverage anchor: at zero sample radius, clocked exact-visible
realization of the wrapper is exactly clocked realization of the raw fallback
decoder family. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_zeroSample_exists_clockedExactVisibleRealization_iff_fallbackDecoderFamily
    {Z : Type v} {k fallbackBits s clock : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k) :
    (∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 0 fallbackBits fallback).predictorFamily.RealizedByClockedBitFamily F) ↔
      ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        (BitFallbackZeroSampleImage.fallbackDecoderFamily fallback).RealizedByClockedBitFamily F := by
  simpa [BitFallbackZeroSampleImage.zeroSampleWrapperFamily] using
    (BitFallbackZeroSampleImage.exists_clockedExactVisibleRealization_iff_fallbackDecoderFamily
      (Z := Z) (k := k) (fallbackBits := fallbackBits) (s := s) (clock := clock) fallback)

/-- Route-coverage anchor: at zero sample radius, the wrapper has exactly the
same clocked finite-learning payload claims as the raw fallback decoder family. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_zeroSample_clockedPayload_iff_fallbackDecoderFamily
    {Z : Type v} [Fintype Z] {k fallbackBits s clock : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k) :
    ClockedKpolyFiniteLearningPayload
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 0 fallbackBits fallback).predictorFamily s clock ↔
      ClockedKpolyFiniteLearningPayload
        (BitFallbackZeroSampleImage.fallbackDecoderFamily fallback) s clock := by
  constructor
  · intro hpayload
    have hcomp :
        ExactVisibleCompressionTarget
          (Z := Z) (k := k)
          (Index := BitFallbackZeroSampleImage.ZeroSampleIndex Z k fallbackBits)
          (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
            Z k 0 fallbackBits fallback).predictorFamily s :=
      (clockedKpolyFiniteLearningPayload_iff_exactVisibleCompressionTarget
        (G := (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 0 fallbackBits fallback).predictorFamily) (s := s) (clock := clock)).1 hpayload
    have hcomp' :
        ExactVisibleCompressionTarget
          (Z := Z) (k := k) (Index := BitCode fallbackBits)
          (BitFallbackZeroSampleImage.fallbackDecoderFamily fallback) s :=
      (kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_zeroSample_exactVisibleCompressionTarget_iff_fallbackDecoderFamily
        (Z := Z) (k := k) (fallbackBits := fallbackBits) (s := s) fallback).1 hcomp
    exact
      (clockedKpolyFiniteLearningPayload_iff_exactVisibleCompressionTarget
        (G := BitFallbackZeroSampleImage.fallbackDecoderFamily fallback)
        (s := s) (clock := clock)).2 hcomp'
  · intro hpayload
    have hcomp :
        ExactVisibleCompressionTarget
          (Z := Z) (k := k) (Index := BitCode fallbackBits)
          (BitFallbackZeroSampleImage.fallbackDecoderFamily fallback) s :=
      (clockedKpolyFiniteLearningPayload_iff_exactVisibleCompressionTarget
        (G := BitFallbackZeroSampleImage.fallbackDecoderFamily fallback)
        (s := s) (clock := clock)).1 hpayload
    have hcomp' :
        ExactVisibleCompressionTarget
          (Z := Z) (k := k)
          (Index := BitFallbackZeroSampleImage.ZeroSampleIndex Z k fallbackBits)
          (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
            Z k 0 fallbackBits fallback).predictorFamily s :=
      (kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_zeroSample_exactVisibleCompressionTarget_iff_fallbackDecoderFamily
        (Z := Z) (k := k) (fallbackBits := fallbackBits) (s := s) fallback).2 hcomp
    exact
      (clockedKpolyFiniteLearningPayload_iff_exactVisibleCompressionTarget
        (G := (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 0 fallbackBits fallback).predictorFamily) (s := s) (clock := clock)).2 hcomp'
end Mettapedia.Computability.PNP
