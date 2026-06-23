import Mettapedia.Computability.PNP.CruxKpolyBitFallbackExactVisibleRecoveryObstructions

/-!
# Regression checks for PNP Kpoly bounded-sample anchors: exact-decoder ERM obstruction checks

This module is part of the decomposed bounded-sample Kpoly regression ledger.
It keeps the historical `CruxSynthesisRegression` theorem namespace while
separating checks by mathematical role.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
open scoped ENNReal

universe u v w z

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_sparse_threshold_erm_obstruction_exact_decoder_regression
    {Z : Type v} [Fintype Z] {k sampleBound r : ℕ}
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
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_nonempty_sharedExactZABSparseThresholdERMData_of_exactVisibleRuleDecode_of_lt_surfaceCard
      (k := k) (r := r) (sampleBound := sampleBound) zfeat hs

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_no_extractor_sparse_threshold_erm_visible_budget_exact_decoder_regression
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
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_exists_sharedExactZABSparseThresholdERMData_of_exactVisibleRuleDecode_of_lt_surfaceCard
      (k := k) (sampleBound := sampleBound) (r := r) hs

theorem kpoly_anchor_surjective_actual_local_lightest_point_exact_decoder_fallback_regression
    {Z : Type v} [Fintype Z] {k sampleBound r : ℕ}
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
    kpolyCoverage_anchor_surjectiveActualLocal_one_sub_apply_lightestPoint_le_of_nonempty_recovery
      (T := boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound
        (Fintype.card (ExactVisiblePostSwitchSurface Z k))
        (exactVisibleRuleDecode (Z := Z) (k := k)))
      (kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_surjective_exactVisibleRuleDecode
        (Z := Z) (k := k) (sampleBound := sampleBound))
      zfeat
      h

theorem kpoly_anchor_surjective_actual_local_no_extractor_lightest_point_exact_decoder_fallback_regression
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

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_no_extractor_lightest_point_exact_decoder_regression
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
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_exists_recovery_of_exactVisibleRuleDecode_of_lt_one_sub_apply_lightestPoint
      (k := k) (sampleBound := sampleBound) (r := r) μ q hq_lt

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_visible_width_threshold_exact_decoder_regression
    {n k sampleBound r : ℕ}
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
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_visibleWidth_le_two_mul_extractorWidth_add_two_mul_k_succ_of_nonempty_recovery_of_exactVisibleRuleDecode
      (k := k) (r := r) (sampleBound := sampleBound)
      (μ := μ) (q := q) zfeat h

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_lightest_point_threshold_exact_decoder_regression
    {Z : Type v} [Fintype Z] {k sampleBound r : ℕ}
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
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_one_sub_apply_lightestPoint_le_of_nonempty_recovery_of_exactVisibleRuleDecode
      (k := k) (r := r) (sampleBound := sampleBound)
      (μ := μ) (q := q) zfeat h

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_visible_width_obstruction_exact_decoder_regression
    {n k sampleBound r : ℕ}
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
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_nonempty_recovery_of_exactVisibleRuleDecode_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
      (k := k) (r := r) (sampleBound := sampleBound)
      (μ := μ) (q := q) zfeat hgap

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_no_extractor_visible_width_exact_decoder_regression
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
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_exists_recovery_of_exactVisibleRuleDecode_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
      (k := k) (sampleBound := sampleBound) (r := r) μ q hgap

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_joint_recovery_threshold_exact_decoder_regression
    {n k sampleBound r : ℕ}
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
    (n ≤ 2 * r + 2 * k + 1) ∧
      (1 - μ (PMF.lightestPoint μ) ≤ q) := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_visibleWidth_and_lightestPoint_threshold_of_nonempty_recovery_of_exactVisibleRuleDecode
      (k := k) (r := r) (sampleBound := sampleBound)
      (μ := μ) (q := q) zfeat h

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_joint_obstruction_exact_decoder_regression
    {n k sampleBound r : ℕ}
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
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_nonempty_recovery_of_exactVisibleRuleDecode_of_visibleWidth_gap_or_lt_one_sub_apply_lightestPoint
      (k := k) (r := r) (sampleBound := sampleBound)
      (μ := μ) (q := q) zfeat hbad

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_no_extractor_joint_obstruction_exact_decoder_regression
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
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_exists_recovery_of_exactVisibleRuleDecode_of_visibleWidth_gap_or_lt_one_sub_apply_lightestPoint
      (k := k) (sampleBound := sampleBound) (r := r) μ q hbad

end Mettapedia.Computability.PNP.CruxSynthesisRegression
