import Mettapedia.Computability.PNP.CruxKpolyBitFallbackExactVisibleDecoder
import Mettapedia.Computability.PNP.ActualSwitchedLocalBitFallbackWrapperSparseThresholdERMObstruction
import Mettapedia.Computability.PNP.ActualSwitchedLocalBitFallbackWrapperSparseThresholdERMRecoveryHeavyRegionCharacterization

/-!
# PNP `Kpoly` bit-fallback endpoint threshold anchors

This module contains the direct threshold barriers for bit-coded fallback
endpoints in the `Kpoly` bridge: fallback-surjective endpoints, canonical
exact-visible fallback decoding, and the paired visible-width/lightest-point
threshold for bounded-sample bit-fallback families.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal BigOperators

universe u v w z

/-- Route-coverage anchor: if a bit-coded fallback decoder is already
full-rule expressive, then the wrapped bounded-sample endpoint cannot carry
shared exact sparse-threshold ERM data below the point-block visible-budget
threshold. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_nonempty_sharedExactZABSparseThresholdERMData_of_fallback_surjective_of_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k r sampleBound fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hsurj : Function.Surjective fallback)
    (zfeat : Z → BitVec r)
    (hs :
      2 * allAffinePointBlockFeatureCount (r + (k + k)) <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMData
          (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
            Z k sampleBound fallbackBits fallback)
          zfeat) :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMData_of_fallback_surjective_of_lt_surfaceCard
    (Z := Z) (k := k) (sampleBound := sampleBound)
    (fallbackBits := fallbackBits) fallback hsurj zfeat hs

/-- Route-coverage anchor: on the canonical exact-visible truth-table fallback
decoder, the weaker manuscript-facing shared sparse-threshold ERM packet
already fails below the unconditional point-block visible-budget threshold. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_nonempty_sharedExactZABSparseThresholdERMData_of_exactVisibleRuleDecode_of_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k r sampleBound : ℕ}
    (zfeat : Z → BitVec r)
    (hs :
      2 * allAffinePointBlockFeatureCount (r + (k + k)) <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMData
          (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
            Z k sampleBound
            (Fintype.card (ExactVisiblePostSwitchSurface Z k))
            (exactVisibleRuleDecode (Z := Z) (k := k)))
          zfeat) := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_nonempty_sharedExactZABSparseThresholdERMData_of_fallback_surjective_of_lt_surfaceCard
      (k := k) (r := r) (sampleBound := sampleBound)
      (fallbackBits := Fintype.card (ExactVisiblePostSwitchSurface Z k))
      (exactVisibleRuleDecode (Z := Z) (k := k))
      (kpolyCoverage_anchor_exactVisibleRuleDecode_surjective
        (Z := Z) (k := k))
      zfeat
      hs

/-- Route-coverage anchor: equivalently, on the canonical exact-visible
truth-table fallback decoder, the same point-block visible-budget gap already
rules out every extractor for the weaker manuscript-facing sparse-threshold
ERM packet. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_exists_sharedExactZABSparseThresholdERMData_of_exactVisibleRuleDecode_of_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k sampleBound r : ℕ}
    (hs :
      2 * allAffinePointBlockFeatureCount (r + (k + k)) <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ∃ zfeat : Z → BitVec r,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMData
            (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
              Z k sampleBound
              (Fintype.card (ExactVisiblePostSwitchSurface Z k))
              (exactVisibleRuleDecode (Z := Z) (k := k)))
            zfeat) := by
  intro h
  rcases h with ⟨zfeat, hnonempty⟩
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_nonempty_sharedExactZABSparseThresholdERMData_of_exactVisibleRuleDecode_of_lt_surfaceCard
      (k := k) (r := r) (sampleBound := sampleBound) zfeat hs hnonempty

/-- Route-coverage anchor: on `BitVec n`, a bit-coded full-rule fallback side
channel does not rescue the stronger sparse-threshold recovery packet below
the same unconditional half-width ceiling. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_fallback_surjective_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
    {n k r sampleBound fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule (BitVec n) k)
    (hsurj : Function.Surjective fallback)
    (μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k))
    (zfeat : BitVec n → BitVec r)
    (q : ℝ≥0∞)
    (hgap : 2 * r + 2 * k + 1 < n) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ
          (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
            (BitVec n) k sampleBound fallbackBits fallback)
          zfeat
          q) :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_fallback_surjective_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
    (n := n) (k := k) (r := r) (sampleBound := sampleBound)
    (fallbackBits := fallbackBits) fallback hsurj μ zfeat q hgap

/-- Route-coverage anchor: if a bit-coded fallback decoder is already
full-rule expressive, then any sparse-threshold recovery packet on the wrapped
bounded-sample endpoint still forces the later lightest-point threshold. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_one_sub_apply_lightestPoint_le_of_nonempty_recovery_of_fallback_surjective
    {Z : Type v} [Fintype Z] {k r sampleBound fallbackBits : ℕ}
    [Nonempty (ExactVisiblePostSwitchSurface Z k)]
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)} {q : ℝ≥0∞}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hsurj : Function.Surjective fallback)
    (zfeat : Z → BitVec r)
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ
          (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
            Z k sampleBound fallbackBits fallback)
          zfeat
          q)) :
    1 - μ (PMF.lightestPoint μ) ≤ q :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_one_sub_apply_lightestPoint_le_of_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_fallback_surjective
    (Z := Z) (k := k) (sampleBound := sampleBound)
    (fallbackBits := fallbackBits) fallback hsurj zfeat h

/-- Route-coverage anchor: on the same bounded-sample bit-fallback endpoint,
surjective fallback expressivity lets two independent obstruction axes fire at
once.  Any hypothetical recovery witness must satisfy both the visible-width
budget and the lightest-point threshold. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_visibleWidth_and_lightestPoint_threshold_of_nonempty_recovery_of_fallback_surjective
    {n k r sampleBound fallbackBits : ℕ}
    [Nonempty (ExactVisiblePostSwitchSurface (BitVec n) k)]
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)} {q : ℝ≥0∞}
    (fallback : BitCode fallbackBits → ExactVisibleRule (BitVec n) k)
    (hsurj : Function.Surjective fallback)
    (zfeat : BitVec n → BitVec r)
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ
          (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
            (BitVec n) k sampleBound fallbackBits fallback)
          zfeat
          q)) :
    n ≤ 2 * r + 2 * k + 1 ∧
      1 - μ (PMF.lightestPoint μ) ≤ q := by
  refine ⟨?_, ?_⟩
  · exact
      boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_visibleWidth_le_two_mul_extractorWidth_add_two_mul_k_succ_of_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_fallback_surjective
        (sampleBound := sampleBound)
        (fallbackBits := fallbackBits)
        fallback hsurj μ zfeat q h
  · exact
      kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_one_sub_apply_lightestPoint_le_of_nonempty_recovery_of_fallback_surjective
        (k := k) (r := r) (sampleBound := sampleBound)
        (fallbackBits := fallbackBits)
        fallback hsurj zfeat h
end Mettapedia.Computability.PNP
