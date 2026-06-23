import Mettapedia.Computability.PNP.CruxKpolyBitFallbackExactVisibleRecoveryThresholds

/-!
# PNP `Kpoly` exact-visible recovery obstructions

No-recovery and no-extractor consequences for the canonical exact-visible
truth-table fallback decoder.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal BigOperators

universe u v w z

/-- Route-coverage anchor: in particular, the canonical truth-table fallback
decoder cannot rescue the wrapped bounded-sample endpoint below the same
lightest-point recovery threshold. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_nonempty_recovery_of_exactVisibleRuleDecode_of_lt_one_sub_apply_lightestPoint
    {Z : Type v} [Fintype Z] {k r sampleBound : ℕ}
    [Nonempty (ExactVisiblePostSwitchSurface Z k)]
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)} {q : ℝ≥0∞}
    (zfeat : Z → BitVec r)
    (hq_lt : q < 1 - μ (PMF.lightestPoint μ)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ
          (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
            Z k sampleBound
            (Fintype.card (ExactVisiblePostSwitchSurface Z k))
            (exactVisibleRuleDecode (Z := Z) (k := k)))
          zfeat
          q) :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_exactVisibleRuleDecode_of_lt_one_sub_apply_lightestPoint
    (Z := Z) (k := k) (sampleBound := sampleBound) zfeat hq_lt

/-- Route-coverage anchor: equivalently, below the intrinsic lightest-point
threshold, the canonical truth-table fallback decoder admits no extractor at
all for the manuscript-facing sparse-threshold recovery packet. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_exists_recovery_of_exactVisibleRuleDecode_of_lt_one_sub_apply_lightestPoint
    {Z : Type v} [Fintype Z] {k sampleBound r : ℕ}
    [Nonempty (ExactVisiblePostSwitchSurface Z k)]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (q : ℝ≥0∞)
    (hq_lt : q < 1 - μ (PMF.lightestPoint μ)) :
    ¬ ∃ zfeat : Z → BitVec r,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
            μ
            (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
              Z k sampleBound
              (Fintype.card (ExactVisiblePostSwitchSurface Z k))
              (exactVisibleRuleDecode (Z := Z) (k := k)))
            zfeat
            q) := by
  exact
    kpolyCoverage_anchor_surjectiveActualLocal_not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_apply_lightestPoint
      (r := r)
      (μ := μ)
      (T := boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound
        (Fintype.card (ExactVisiblePostSwitchSurface Z k))
        (exactVisibleRuleDecode (Z := Z) (k := k)))
      (q := q)
      (kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_surjective_exactVisibleRuleDecode
        (Z := Z) (k := k) (sampleBound := sampleBound))
      hq_lt

/-- Route-coverage anchor: on the canonical exact-visible truth-table fallback
decoder, violating either the visible-width ceiling or the lightest-point
threshold already rules out the manuscript-facing recovery packet. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_nonempty_recovery_of_exactVisibleRuleDecode_of_visibleWidth_gap_or_lt_one_sub_apply_lightestPoint
    {n k r sampleBound : ℕ}
    [Nonempty (ExactVisiblePostSwitchSurface (BitVec n) k)]
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)} {q : ℝ≥0∞}
    (zfeat : BitVec n → BitVec r)
    (hbad : 2 * r + 2 * k + 1 < n ∨ q < 1 - μ (PMF.lightestPoint μ)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ
          (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
            (BitVec n) k sampleBound
            (Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k))
            (exactVisibleRuleDecode (Z := BitVec n) (k := k)))
          zfeat
          q) := by
  rcases hbad with hgap | hq_lt
  · exact
      kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_fallback_surjective_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
        (sampleBound := sampleBound)
        (fallbackBits := Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k))
        (exactVisibleRuleDecode (Z := BitVec n) (k := k))
        (kpolyCoverage_anchor_exactVisibleRuleDecode_surjective
          (Z := BitVec n) (k := k))
        μ zfeat q hgap
  · exact
      kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_nonempty_recovery_of_exactVisibleRuleDecode_of_lt_one_sub_apply_lightestPoint
        (k := k) (r := r) (sampleBound := sampleBound)
        (μ := μ) (q := q) zfeat hq_lt

/-- Route-coverage anchor: on the canonical exact-visible truth-table fallback
decoder, an unconditional visible-width gap already rules out the manuscript-
facing sparse-threshold recovery packet. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_nonempty_recovery_of_exactVisibleRuleDecode_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
    {n k r sampleBound : ℕ}
    [Nonempty (ExactVisiblePostSwitchSurface (BitVec n) k)]
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)} {q : ℝ≥0∞}
    (zfeat : BitVec n → BitVec r)
    (hgap : 2 * r + 2 * k + 1 < n) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ
          (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
            (BitVec n) k sampleBound
            (Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k))
            (exactVisibleRuleDecode (Z := BitVec n) (k := k)))
          zfeat
          q) := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_fallback_surjective_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
      (sampleBound := sampleBound)
      (fallbackBits := Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k))
      (exactVisibleRuleDecode (Z := BitVec n) (k := k))
      (kpolyCoverage_anchor_exactVisibleRuleDecode_surjective
        (Z := BitVec n) (k := k))
      μ zfeat q hgap

/-- Route-coverage anchor: equivalently, on the canonical exact-visible
truth-table fallback decoder, an unconditional visible-width gap already rules
out every extractor for the manuscript-facing sparse-threshold recovery
packet. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_exists_recovery_of_exactVisibleRuleDecode_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
    {n k sampleBound r : ℕ}
    [Nonempty (ExactVisiblePostSwitchSurface (BitVec n) k)]
    (μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k))
    (q : ℝ≥0∞)
    (hgap : 2 * r + 2 * k + 1 < n) :
    ¬ ∃ zfeat : BitVec n → BitVec r,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
            μ
            (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
              (BitVec n) k sampleBound
              (Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k))
              (exactVisibleRuleDecode (Z := BitVec n) (k := k)))
            zfeat
            q) := by
  exact
    kpolyCoverage_anchor_surjectiveActualLocal_not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
      (n := n) (k := k) (r := r)
      (μ := μ)
      (T := boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        (BitVec n) k sampleBound
        (Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k))
        (exactVisibleRuleDecode (Z := BitVec n) (k := k)))
      (q := q)
      (kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_surjective_exactVisibleRuleDecode
        (Z := BitVec n) (k := k) (sampleBound := sampleBound))
      hgap

/-- Route-coverage anchor: equivalently, on the canonical exact-visible
truth-table fallback decoder, a visible-width gap or lightest-point deficit
already rules out every extractor for the manuscript-facing recovery packet. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_exists_recovery_of_exactVisibleRuleDecode_of_visibleWidth_gap_or_lt_one_sub_apply_lightestPoint
    {n k sampleBound r : ℕ}
    [Nonempty (ExactVisiblePostSwitchSurface (BitVec n) k)]
    (μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k))
    (q : ℝ≥0∞)
    (hbad : 2 * r + 2 * k + 1 < n ∨ q < 1 - μ (PMF.lightestPoint μ)) :
    ¬ ∃ zfeat : BitVec n → BitVec r,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
            μ
            (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
              (BitVec n) k sampleBound
              (Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k))
              (exactVisibleRuleDecode (Z := BitVec n) (k := k)))
            zfeat
            q) := by
  exact
    kpolyCoverage_anchor_surjectiveActualLocal_not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_visibleWidth_gap_or_lt_one_sub_apply_lightestPoint
      (n := n) (k := k) (r := r)
      (μ := μ)
      (T := boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        (BitVec n) k sampleBound
        (Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k))
        (exactVisibleRuleDecode (Z := BitVec n) (k := k)))
      (q := q)
      (kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_surjective_exactVisibleRuleDecode
        (Z := BitVec n) (k := k) (sampleBound := sampleBound))
      hbad

end Mettapedia.Computability.PNP
