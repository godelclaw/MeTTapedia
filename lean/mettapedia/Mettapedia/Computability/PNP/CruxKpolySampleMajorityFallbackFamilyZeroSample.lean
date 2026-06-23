import Mettapedia.Computability.PNP.ActualSwitchedLocalFallbackZeroSampleImage
import Mettapedia.Computability.PNP.ClockedKpolyGapAssessment

/-!
# PNP `Kpoly` sample-majority anchors: fallback-family zero sample layer

Structured fallback-family anchors that identify the zero-sample wrapper with the raw fallback family.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- Route-coverage anchor: if the fallback is chosen from a structured
fallback family, bounded samples can only make `sampleBound` point changes
relative to the selected fallback rule. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_disagreementSupport_card_le_sampleBound
    {FallbackIndex : Type v} {Z : Type v} [Fintype Z] {k sampleBound : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (index :
      BoundedSampleFallbackFamilyIndex
        FallbackIndex (ExactVisiblePostSwitchSurface Z k) sampleBound) :
    (PluginSampleMajority.disagreementSupport (fallback index.1)
      (fun u : ExactVisiblePostSwitchSurface Z k =>
        (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k sampleBound fallback).predictorFamily.predict index u)).card ≤
        sampleBound :=
  boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_disagreementSupport_card_le_sampleBound
    (Z := Z) (k := k) (sampleBound := sampleBound) fallback index

/-- Route-coverage anchor: selecting a structured fallback code and using the
empty sample realizes that fallback rule exactly. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_emptySample_predict
    {FallbackIndex : Type v} {Z : Type v} {k sampleBound : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k) (code : FallbackIndex) :
    (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
        FallbackIndex Z k sampleBound fallback).predictorFamily.predict
        (code, ⟨[], by simp⟩) =
      fallback code :=
  boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_emptySample_predict
    (Z := Z) (k := k) (sampleBound := sampleBound) fallback code

/-- Route-coverage anchor: bounded samples do not reduce a structured fallback
family that is already full-rule expressive.  A proposed repair must therefore
prove smallness of the fallback family itself, not merely boundedness of the
sampled overrides. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_surjective_of_fallback_surjective
    {FallbackIndex : Type v} {Z : Type v} {k sampleBound : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (hsurj : Function.Surjective fallback) :
    Function.Surjective
      (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
        FallbackIndex Z k sampleBound fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_surjective_of_fallback_surjective
    (Z := Z) (k := k) (sampleBound := sampleBound) fallback hsurj

/-- Route-coverage anchor: with no sampled overrides, a structured fallback
endpoint is full-rule expressive exactly when the fallback family itself is
full-rule expressive.  Thus the zero-sample boundary leaves no hidden
expressivity in the bounded-sample wrapper. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_zeroSample_surjective_iff_fallback_surjective
    {FallbackIndex : Type v} {Z : Type v} {k : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    Function.Surjective
        (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k 0 fallback).predictorFamily.predict ↔
      Function.Surjective fallback :=
  boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_zeroSample_surjective_iff_fallback_surjective
    (Z := Z) (k := k) fallback

/-- Route-coverage anchor: at zero sample radius, the structured fallback
wrapper has exactly the same finite predictor-image covers as the raw fallback
family itself. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_zeroSample_finitePredictorCover_iff_fallbackFamily
    {FallbackIndex : Type v} {Z : Type v} {k N : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
        FallbackIndex Z k 0 fallback).predictorFamily.FinitePredictorCover N ↔
      (FallbackZeroSampleImage.fallbackFamily fallback).FinitePredictorCover N := by
  simpa [FallbackZeroSampleImage.zeroSampleWrapperFamily] using
    (FallbackZeroSampleImage.finitePredictorCover_iff_fallbackFamily
      (FallbackIndex := FallbackIndex) (Z := Z) (k := k) (N := N) fallback)

/-- Route-coverage anchor: at zero sample radius, the structured fallback
wrapper has exactly the same finite selected-index representative covers as
the raw fallback family itself. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_zeroSample_finiteIndexRepresentativeCover_iff_fallbackFamily
    {FallbackIndex : Type v} {Z : Type v} {k N : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
        FallbackIndex Z k 0 fallback).predictorFamily.FiniteIndexRepresentativeCover N ↔
      (FallbackZeroSampleImage.fallbackFamily fallback).FiniteIndexRepresentativeCover N := by
  simpa [FallbackZeroSampleImage.zeroSampleWrapperFamily] using
    (FallbackZeroSampleImage.finiteIndexRepresentativeCover_iff_fallbackFamily
      (FallbackIndex := FallbackIndex) (Z := Z) (k := k) (N := N) fallback)

/-- Route-coverage anchor: at zero sample radius, the structured fallback
wrapper has exactly the same finite quotient-code presentations as the raw
fallback family itself. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_zeroSample_finitePredictorQuotient_iff_fallbackFamily
    {FallbackIndex : Type v} {Z : Type v} {k N : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
        FallbackIndex Z k 0 fallback).predictorFamily.FinitePredictorQuotient N ↔
      (FallbackZeroSampleImage.fallbackFamily fallback).FinitePredictorQuotient N := by
  simpa [FallbackZeroSampleImage.zeroSampleWrapperFamily] using
    (FallbackZeroSampleImage.finitePredictorQuotient_iff_fallbackFamily
      (FallbackIndex := FallbackIndex) (Z := Z) (k := k) (N := N) fallback)

/-- Route-coverage anchor: at zero sample radius, exact visible compression of
the wrapper is exactly exact visible compression of the raw fallback family. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_zeroSample_exactVisibleCompressionTarget_iff_fallbackFamily
    {FallbackIndex : Type v} {Z : Type v} {k s : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    ExactVisibleCompressionTarget
        (Z := Z) (k := k)
        (Index := FallbackZeroSampleImage.ZeroSampleIndex FallbackIndex Z k)
        (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k 0 fallback).predictorFamily s ↔
      ExactVisibleCompressionTarget
        (Z := Z) (k := k)
        (Index := FallbackIndex)
        (FallbackZeroSampleImage.fallbackFamily fallback) s := by
  simpa [FallbackZeroSampleImage.zeroSampleWrapperFamily] using
    (FallbackZeroSampleImage.exactVisibleCompressionTarget_iff_fallbackFamily
      (FallbackIndex := FallbackIndex) (Z := Z) (k := k) (s := s) fallback)

/-- Route-coverage anchor: at zero sample radius, clocked exact-visible
realization of the wrapper is exactly clocked realization of the raw fallback
family. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_zeroSample_exists_clockedExactVisibleRealization_iff_fallbackFamily
    {FallbackIndex : Type v} {Z : Type v} {k s clock : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    (∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k 0 fallback).predictorFamily.RealizedByClockedBitFamily F) ↔
      ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        (FallbackZeroSampleImage.fallbackFamily fallback).RealizedByClockedBitFamily F := by
  simpa [FallbackZeroSampleImage.zeroSampleWrapperFamily] using
    (FallbackZeroSampleImage.exists_clockedExactVisibleRealization_iff_fallbackFamily
      (FallbackIndex := FallbackIndex) (Z := Z) (k := k) (s := s) (clock := clock) fallback)

/-- Route-coverage anchor: at zero sample radius, the structured fallback
wrapper has exactly the same clocked finite-learning payload claims as the raw
fallback family. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_zeroSample_clockedPayload_iff_fallbackFamily
    {FallbackIndex : Type v} {Z : Type v} [Fintype Z] {k s clock : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    ClockedKpolyFiniteLearningPayload
        (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k 0 fallback).predictorFamily s clock ↔
      ClockedKpolyFiniteLearningPayload
        (FallbackZeroSampleImage.fallbackFamily fallback) s clock := by
  constructor
  · intro hpayload
    have hcomp :
        ExactVisibleCompressionTarget
          (Z := Z) (k := k)
          (Index := FallbackZeroSampleImage.ZeroSampleIndex FallbackIndex Z k)
          (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
            FallbackIndex Z k 0 fallback).predictorFamily s :=
      (clockedKpolyFiniteLearningPayload_iff_exactVisibleCompressionTarget
        (G := (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k 0 fallback).predictorFamily)
        (s := s) (clock := clock)).1 hpayload
    have hcomp' :
        ExactVisibleCompressionTarget
          (Z := Z) (k := k) (Index := FallbackIndex)
          (FallbackZeroSampleImage.fallbackFamily fallback) s :=
      (kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_zeroSample_exactVisibleCompressionTarget_iff_fallbackFamily
        (FallbackIndex := FallbackIndex) (Z := Z) (k := k) (s := s) fallback).1 hcomp
    exact
      (clockedKpolyFiniteLearningPayload_iff_exactVisibleCompressionTarget
        (G := FallbackZeroSampleImage.fallbackFamily fallback)
        (s := s) (clock := clock)).2 hcomp'
  · intro hpayload
    have hcomp :
        ExactVisibleCompressionTarget
          (Z := Z) (k := k) (Index := FallbackIndex)
          (FallbackZeroSampleImage.fallbackFamily fallback) s :=
      (clockedKpolyFiniteLearningPayload_iff_exactVisibleCompressionTarget
        (G := FallbackZeroSampleImage.fallbackFamily fallback)
        (s := s) (clock := clock)).1 hpayload
    have hcomp' :
        ExactVisibleCompressionTarget
          (Z := Z) (k := k)
          (Index := FallbackZeroSampleImage.ZeroSampleIndex FallbackIndex Z k)
          (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
            FallbackIndex Z k 0 fallback).predictorFamily s :=
      (kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_zeroSample_exactVisibleCompressionTarget_iff_fallbackFamily
        (FallbackIndex := FallbackIndex) (Z := Z) (k := k) (s := s) fallback).2 hcomp
    exact
      (clockedKpolyFiniteLearningPayload_iff_exactVisibleCompressionTarget
        (G := (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k 0 fallback).predictorFamily)
        (s := s) (clock := clock)).2 hcomp'


end Mettapedia.Computability.PNP
