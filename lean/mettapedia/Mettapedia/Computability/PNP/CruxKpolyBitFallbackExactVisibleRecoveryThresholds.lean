import Mettapedia.Computability.PNP.CruxKpolyBitFallbackThresholdSurjective

/-!
# PNP `Kpoly` exact-visible recovery thresholds

Necessary visible-width and lightest-point threshold facts for the canonical
exact-visible truth-table fallback decoder.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal BigOperators

universe u v w z

/-- Route-coverage anchor: for the canonical exact-visible truth-table fallback
decoder, any hypothetical recovery witness on the wrapped bounded-sample
endpoint must satisfy the unconditional visible-width ceiling. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_visibleWidth_le_two_mul_extractorWidth_add_two_mul_k_succ_of_nonempty_recovery_of_exactVisibleRuleDecode
    {n k r sampleBound : ℕ}
    [Nonempty (ExactVisiblePostSwitchSurface (BitVec n) k)]
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)} {q : ℝ≥0∞}
    (zfeat : BitVec n → BitVec r)
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ
          (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
            (BitVec n) k sampleBound
            (Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k))
            (exactVisibleRuleDecode (Z := BitVec n) (k := k)))
          zfeat
          q)) :
    n ≤ 2 * r + 2 * k + 1 := by
  exact
    kpolyCoverage_anchor_surjectiveActualLocal_visibleWidth_le_two_mul_extractorWidth_add_two_mul_k_succ_of_nonempty_recovery
      (k := k) (r := r)
      (T := boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        (BitVec n) k sampleBound
        (Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k))
        (exactVisibleRuleDecode (Z := BitVec n) (k := k)))
      (kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_surjective_exactVisibleRuleDecode
        (Z := BitVec n) (k := k) (sampleBound := sampleBound))
      zfeat
      h

/-- Route-coverage anchor: for the canonical exact-visible truth-table fallback
decoder, any hypothetical recovery witness on the wrapped bounded-sample
endpoint must satisfy the intrinsic lightest-point threshold. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_one_sub_apply_lightestPoint_le_of_nonempty_recovery_of_exactVisibleRuleDecode
    {Z : Type v} [Fintype Z] {k r sampleBound : ℕ}
    [Nonempty (ExactVisiblePostSwitchSurface Z k)]
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)} {q : ℝ≥0∞}
    (zfeat : Z → BitVec r)
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ
          (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
            Z k sampleBound
            (Fintype.card (ExactVisiblePostSwitchSurface Z k))
            (exactVisibleRuleDecode (Z := Z) (k := k)))
          zfeat
          q)) :
    1 - μ (PMF.lightestPoint μ) ≤ q := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_one_sub_apply_lightestPoint_le_of_nonempty_recovery_of_fallback_surjective
      (k := k) (r := r) (sampleBound := sampleBound)
      (fallbackBits := Fintype.card (ExactVisiblePostSwitchSurface Z k))
      (exactVisibleRuleDecode (Z := Z) (k := k))
      (kpolyCoverage_anchor_exactVisibleRuleDecode_surjective
        (Z := Z) (k := k))
      zfeat
      h

/-- Route-coverage anchor: for the canonical exact-visible truth-table fallback
decoder, any hypothetical recovery witness on the wrapped bounded-sample
endpoint must satisfy both the visible-width ceiling and the lightest-point
threshold together. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_visibleWidth_and_lightestPoint_threshold_of_nonempty_recovery_of_exactVisibleRuleDecode
    {n k r sampleBound : ℕ}
    [Nonempty (ExactVisiblePostSwitchSurface (BitVec n) k)]
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)} {q : ℝ≥0∞}
    (zfeat : BitVec n → BitVec r)
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ
          (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
            (BitVec n) k sampleBound
            (Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k))
            (exactVisibleRuleDecode (Z := BitVec n) (k := k)))
          zfeat
          q)) :
    n ≤ 2 * r + 2 * k + 1 ∧
      1 - μ (PMF.lightestPoint μ) ≤ q := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_visibleWidth_and_lightestPoint_threshold_of_nonempty_recovery_of_fallback_surjective
      (k := k) (r := r) (sampleBound := sampleBound)
      (fallbackBits := Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k))
      (μ := μ) (q := q)
      (exactVisibleRuleDecode (Z := BitVec n) (k := k))
      (kpolyCoverage_anchor_exactVisibleRuleDecode_surjective
        (Z := BitVec n) (k := k))
      zfeat h

end Mettapedia.Computability.PNP
