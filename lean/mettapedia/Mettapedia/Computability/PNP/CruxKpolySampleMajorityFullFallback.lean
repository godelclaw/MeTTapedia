import Mettapedia.Computability.PNP.CruxKpolySampleMajorityBasic

/-!
# PNP `Kpoly` sample-majority anchors: input-dependent fallback

Full-rule fallback side-channel anchors and the resulting finite-cover, quotient, compression, and payload obstructions.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- Route-coverage anchor: if the tie fallback is allowed to depend on the
exact-visible input, the empty sample already realizes any fallback rule. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithFallback_emptySample_predict
    {Z : Type v} {k sampleBound : ℕ}
    (fallback : ExactVisibleRule Z k) :
    (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
        Z k sampleBound).predictorFamily.predict
        (fallback, ⟨[], by simp⟩) =
      fallback :=
  boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface_emptySample_predict
    (Z := Z) (k := k) (sampleBound := sampleBound) fallback

/-- Route-coverage anchor: the input-dependent fallback endpoint is
full-rule expressive for every sample bound, including zero. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithFallback_surjective
    (Z : Type v) (k sampleBound : ℕ) :
    Function.Surjective
      (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
        Z k sampleBound).predictorFamily.predict :=
  boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface_surjective
    Z k sampleBound

/-- Route-coverage anchor: since the fallback component is already a full rule,
the endpoint has no small finite predictor cover below the exact-visible
truth-table budget. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithFallback_not_finitePredictorCover_of_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k s sampleBound : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
        Z k sampleBound).predictorFamily.FinitePredictorCover (2 ^ s) :=
  boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface_not_finitePredictorCover_of_lt_surfaceCard
    (Z := Z) (k := k) (s := s) (sampleBound := sampleBound) hs

/-- Route-coverage anchor: the same full-rule fallback side channel has no
finite selected-index representative cover below the exact-visible truth-table
budget. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithFallback_not_finiteIndexRepresentativeCover_of_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k s sampleBound : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
        Z k sampleBound).predictorFamily.FiniteIndexRepresentativeCover (2 ^ s) := by
  have hpow : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) :=
    Nat.pow_lt_pow_right Nat.one_lt_two hs
  exact
    not_exactVisible_finiteIndexRepresentativeCover_of_surjective_predict
      (G := (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
        Z k sampleBound).predictorFamily)
      (N := 2 ^ s) hpow
      (kpolyCoverage_anchor_boundedSampleMajorityWithFallback_surjective Z k sampleBound)

/-- Route-coverage anchor: the same full-rule fallback side channel has no
finite quotient-code presentation below the exact-visible truth-table budget. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithFallback_not_finitePredictorQuotient_of_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k s sampleBound : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
        Z k sampleBound).predictorFamily.FinitePredictorQuotient (2 ^ s) := by
  have hpow : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) :=
    Nat.pow_lt_pow_right Nat.one_lt_two hs
  exact
    not_exactVisible_finitePredictorQuotient_of_surjective_predict
      (G := (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
        Z k sampleBound).predictorFamily)
      (N := 2 ^ s) hpow
      (kpolyCoverage_anchor_boundedSampleMajorityWithFallback_surjective Z k sampleBound)

/-- Route-coverage anchor: the same full-rule fallback side channel has no
exact-visible compression target below the exact-visible truth-table budget. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithFallback_not_exactVisibleCompressionTarget_of_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k s sampleBound : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ExactVisibleCompressionTarget
        (Z := Z) (k := k)
        (Index := BoundedSampleFallbackIndex
          (ExactVisiblePostSwitchSurface Z k) sampleBound)
        (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
          Z k sampleBound).predictorFamily s := by
  intro hcomp
  have hcover :
      (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
          Z k sampleBound).predictorFamily.FinitePredictorCover (2 ^ s) :=
    (exactVisibleCompressionTarget_iff_finitePredictorCover
      (Z := Z) (k := k) (s := s)
      (Index := BoundedSampleFallbackIndex
        (ExactVisiblePostSwitchSurface Z k) sampleBound)
      (G := (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
        Z k sampleBound).predictorFamily)).1 hcomp
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithFallback_not_finitePredictorCover_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) (sampleBound := sampleBound) hs hcover

/-- Route-coverage anchor: the same fallback side channel admits no clocked
exact-visible realization below the exact-visible truth-table budget. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithFallback_not_clockedRealization_of_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k s sampleBound clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
          Z k sampleBound).predictorFamily.RealizedByClockedBitFamily F := by
  have hpow : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) :=
    Nat.pow_lt_pow_right Nat.one_lt_two hs
  exact
    not_exists_clockedExactVisibleRealization_of_surjective_predict_of_lt_predictorCard
      (G := (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
        Z k sampleBound).predictorFamily)
      (clock := clock) hpow
      (kpolyCoverage_anchor_boundedSampleMajorityWithFallback_surjective Z k sampleBound)

/-- Route-coverage anchor: the same fallback side channel cannot provide the
clocked finite-learning payload below the exact-visible truth-table budget. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithFallback_not_clockedPayload_of_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k s sampleBound clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
          Z k sampleBound).predictorFamily s clock :=
  boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface_not_clockedKpolyFiniteLearningPayload_of_lt_surfaceCard
    (Z := Z) (k := k) (s := s) (sampleBound := sampleBound) (clock := clock) hs


end Mettapedia.Computability.PNP
