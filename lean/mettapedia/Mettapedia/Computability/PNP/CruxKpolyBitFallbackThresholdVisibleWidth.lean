import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryThresholdVisibleBudgetObstruction
import Mettapedia.Computability.PNP.CruxKpolyBitFallbackThresholdActualLocal

/-!
# PNP `Kpoly` visible-width threshold anchors

This module packages the direct visible-width consequences of the actual-local
threshold barriers for full-rule and bounded-sample plug-in-majority endpoints,
including sharpened slack bounds.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal BigOperators

universe u v w z

/-- Route-coverage anchor: on the full-rule `BitVec n` endpoint, a recovery
threshold below `1 - 2^-p` already forces the direct visible-width bound
`n + 2*k < p`. -/
theorem kpolyCoverage_anchor_fullRuleActualLocal_visibleWidth_lt_of_nonempty_recovery_of_lt_one_sub_pow_inv
    {n k r p : ℕ}
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)} {q : ℝ≥0∞}
    (zfeat : BitVec n → BitVec r)
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ
          (fullRuleActualSwitchedLocalInterface (BitVec n) k)
          zfeat
          q))
    (hq_lt : q < 1 - (2 ^ p : ℝ≥0∞)⁻¹) :
    n + 2 * k < p := by
  rcases h with ⟨h⟩
  exact
    ActualSwitchedLocalInterface.visibleWidth_lt_of_nonempty_fullRuleActualSwitchedLocalInterface_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_pow_inv
      (μ := μ)
      (k := k)
      (zfeat := zfeat)
      (p := p)
      h
      hq_lt

/-- Route-coverage anchor: therefore if `p ≤ n + 2*k`, no extractor at all
can support the full-rule manuscript-facing recovery packet below
`1 - 2^-p`. -/
theorem kpolyCoverage_anchor_fullRuleActualLocal_not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_pow_inv_of_le_visibleWidth
    {n k r p : ℕ}
    (μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k))
    (q : ℝ≥0∞)
    (hwidth : p ≤ n + 2 * k)
    (hq_lt : q < 1 - (2 ^ p : ℝ≥0∞)⁻¹) :
    ¬ ∃ zfeat : BitVec n → BitVec r,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
            μ
            (fullRuleActualSwitchedLocalInterface (BitVec n) k)
            zfeat
            q) := by
  rintro ⟨zfeat, hdata⟩
  exact
    ActualSwitchedLocalInterface.fullRuleActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_pow_inv_of_le_visibleWidth
      (μ := μ)
      (k := k)
      (r := r)
      (p := p)
      (zfeat := zfeat)
      hwidth
      hq_lt
      hdata

/-- Route-coverage anchor: the same direct visible-width obstruction applies
to bounded-sample plug-in-majority endpoints once the sample bound is large
enough for surjectivity. -/
theorem kpolyCoverage_anchor_boundedSamplePluginMajorityActualLocal_visibleWidth_lt_of_nonempty_recovery_of_lt_one_sub_pow_inv
    {n k r sampleBound p : ℕ}
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)} {q : ℝ≥0∞}
    (zfeat : BitVec n → BitVec r)
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ
          (boundedSamplePluginMajorityActualSwitchedLocalInterface
            (BitVec n) k sampleBound)
          zfeat
          q))
    (hsample : Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) ≤ sampleBound)
    (hq_lt : q < 1 - (2 ^ p : ℝ≥0∞)⁻¹) :
    n + 2 * k < p := by
  rcases h with ⟨h⟩
  exact
    ActualSwitchedLocalInterface.boundedSamplePluginMajorityActualSwitchedLocalInterface_visibleWidth_lt_of_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_pow_inv
      (μ := μ)
      (k := k)
      (sampleBound := sampleBound)
      (zfeat := zfeat)
      (p := p)
      hsample
      h
      hq_lt

/-- Route-coverage anchor: therefore if `p ≤ n + 2*k`, no extractor at all
can support the bounded-sample plug-in-majority recovery packet below
`1 - 2^-p` once the sample bound is large enough for surjectivity. -/
theorem kpolyCoverage_anchor_boundedSamplePluginMajorityActualLocal_not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_pow_inv_of_le_visibleWidth
    {n k r sampleBound p : ℕ}
    (μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k))
    (q : ℝ≥0∞)
    (hsample : Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) ≤ sampleBound)
    (hwidth : p ≤ n + 2 * k)
    (hq_lt : q < 1 - (2 ^ p : ℝ≥0∞)⁻¹) :
    ¬ ∃ zfeat : BitVec n → BitVec r,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
            μ
            (boundedSamplePluginMajorityActualSwitchedLocalInterface
              (BitVec n) k sampleBound)
            zfeat
            q) := by
  rintro ⟨zfeat, hdata⟩
  exact
    ActualSwitchedLocalInterface.boundedSamplePluginMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_pow_inv_of_le_visibleWidth
      (μ := μ)
      (k := k)
      (r := r)
      (sampleBound := sampleBound)
      (p := p)
      (zfeat := zfeat)
      hsample
      hwidth
      hq_lt
      hdata

/-- Route-coverage anchor: on the full-rule `BitVec n` endpoint, a recovery
threshold below `1 - 2^-(2*r + 4*k + slack + 1)` sharpens the visible-width
ceiling from the unconditional half-width bound to `n ≤ 2*r + 2*k + slack`. -/
theorem kpolyCoverage_anchor_fullRuleActualLocal_visibleWidth_le_two_mul_extractorWidth_add_two_mul_k_add_slack_of_nonempty_recovery_of_lt_one_sub_pow_inv
    {n k r slack : ℕ}
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)} {q : ℝ≥0∞}
    (zfeat : BitVec n → BitVec r)
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ
          (fullRuleActualSwitchedLocalInterface (BitVec n) k)
          zfeat
          q))
    (hq_lt : q < 1 - (2 ^ (2 * r + 4 * k + slack + 1) : ℝ≥0∞)⁻¹) :
    n ≤ 2 * r + 2 * k + slack := by
  rcases h with ⟨h⟩
  exact
    ActualSwitchedLocalInterface.visibleWidth_le_two_mul_extractorWidth_add_two_mul_k_add_slack_of_nonempty_fullRuleActualSwitchedLocalInterface_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_pow_inv
      (μ := μ)
      (k := k)
      (r := r)
      (zfeat := zfeat)
      (slack := slack)
      h
      hq_lt

/-- Route-coverage anchor: below that sharpened point-block threshold, no
extractor at all can support the full-rule manuscript-facing recovery packet. -/
theorem kpolyCoverage_anchor_fullRuleActualLocal_not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_pow_inv_of_two_mul_extractorWidth_add_two_mul_k_add_slack_lt_visibleWidth
    {n k r slack : ℕ}
    (μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k))
    (q : ℝ≥0∞)
    (hgap : 2 * r + 2 * k + slack < n)
    (hq_lt : q < 1 - (2 ^ (2 * r + 4 * k + slack + 1) : ℝ≥0∞)⁻¹) :
    ¬ ∃ zfeat : BitVec n → BitVec r,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
            μ
            (fullRuleActualSwitchedLocalInterface (BitVec n) k)
            zfeat
            q) := by
  rintro ⟨zfeat, hdata⟩
  exact
    ActualSwitchedLocalInterface.fullRuleActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_pow_inv_of_two_mul_extractorWidth_add_two_mul_k_add_slack_lt_visibleWidth
      (μ := μ)
      (k := k)
      (r := r)
      (slack := slack)
      (zfeat := zfeat)
      hgap
      hq_lt
      hdata

/-- Route-coverage anchor: the same sharpened point-block visible-budget
ceiling applies to bounded-sample plug-in-majority endpoints once the sample
bound is large enough for surjectivity. -/
theorem kpolyCoverage_anchor_boundedSamplePluginMajorityActualLocal_visibleWidth_le_two_mul_extractorWidth_add_two_mul_k_add_slack_of_nonempty_recovery_of_lt_one_sub_pow_inv
    {n k r sampleBound slack : ℕ}
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)} {q : ℝ≥0∞}
    (zfeat : BitVec n → BitVec r)
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ
          (boundedSamplePluginMajorityActualSwitchedLocalInterface
            (BitVec n) k sampleBound)
          zfeat
          q))
    (hsample : Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) ≤ sampleBound)
    (hq_lt : q < 1 - (2 ^ (2 * r + 4 * k + slack + 1) : ℝ≥0∞)⁻¹) :
    n ≤ 2 * r + 2 * k + slack := by
  rcases h with ⟨h⟩
  exact
    ActualSwitchedLocalInterface.boundedSamplePluginMajorityActualSwitchedLocalInterface_visibleWidth_le_two_mul_extractorWidth_add_two_mul_k_add_slack_of_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_pow_inv
      (μ := μ)
      (k := k)
      (r := r)
      (sampleBound := sampleBound)
      (zfeat := zfeat)
      (slack := slack)
      hsample
      h
      hq_lt

/-- Route-coverage anchor: below that sharpened threshold, no extractor at all
can support the bounded-sample plug-in-majority recovery packet once the
sample bound is large enough for surjectivity. -/
theorem kpolyCoverage_anchor_boundedSamplePluginMajorityActualLocal_not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_pow_inv_of_two_mul_extractorWidth_add_two_mul_k_add_slack_lt_visibleWidth
    {n k r sampleBound slack : ℕ}
    (μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k))
    (q : ℝ≥0∞)
    (hsample : Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) ≤ sampleBound)
    (hgap : 2 * r + 2 * k + slack < n)
    (hq_lt : q < 1 - (2 ^ (2 * r + 4 * k + slack + 1) : ℝ≥0∞)⁻¹) :
    ¬ ∃ zfeat : BitVec n → BitVec r,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
            μ
            (boundedSamplePluginMajorityActualSwitchedLocalInterface
              (BitVec n) k sampleBound)
            zfeat
            q) := by
  rintro ⟨zfeat, hdata⟩
  exact
    ActualSwitchedLocalInterface.boundedSamplePluginMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_pow_inv_of_two_mul_extractorWidth_add_two_mul_k_add_slack_lt_visibleWidth
      (μ := μ)
      (k := k)
      (r := r)
      (sampleBound := sampleBound)
      (slack := slack)
      (zfeat := zfeat)
      hsample
      hgap
      hq_lt
      hdata
end Mettapedia.Computability.PNP
