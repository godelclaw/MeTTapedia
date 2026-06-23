import Mettapedia.Computability.PNP.CruxKpolyBitFallbackThresholdRegions
import Mettapedia.Computability.PNP.CruxKpolyActualLocalSparseThreshold

/-!
# PNP `Kpoly` surjective endpoint combined threshold anchors

This module contains the final surjective actual-local wrappers that combine
the visible-width, shared-ERM, and lightest-point threshold obstructions.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal BigOperators

universe u v w z

/-- Route-coverage anchor: on any finite surjective actual-local endpoint, the
same recovery witness must satisfy both the unconditional half-width ceiling
and the intrinsic lightest-point threshold together. -/
theorem kpolyCoverage_anchor_surjectiveActualLocal_visibleWidth_and_lightestPoint_threshold_of_nonempty_recovery
    {n k r : ℕ} {Index : Type u} {Block : Type w}
    [Nonempty (ExactVisiblePostSwitchSurface (BitVec n) k)]
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)} {q : ℝ≥0∞}
    (T : ActualSwitchedLocalInterface (BitVec n) k Index Block)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (zfeat : BitVec n → BitVec r)
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ T zfeat q)) :
    n ≤ 2 * r + 2 * k + 1 ∧
      1 - μ (PMF.lightestPoint μ) ≤ q := by
  refine ⟨?_, ?_⟩
  · exact
      kpolyCoverage_anchor_surjectiveActualLocal_visibleWidth_le_two_mul_extractorWidth_add_two_mul_k_succ_of_nonempty_recovery
        (k := k) (r := r) T hsurj zfeat h
  · exact
      kpolyCoverage_anchor_surjectiveActualLocal_one_sub_apply_lightestPoint_le_of_nonempty_recovery
        (k := k) (r := r) T hsurj zfeat h

/-- Route-coverage anchor: on any finite surjective actual-local endpoint,
violating either the unconditional half-width ceiling or the intrinsic
lightest-point threshold already rules out the manuscript-facing sparse-
threshold recovery packet. -/
theorem kpolyCoverage_anchor_surjectiveActualLocal_not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_visibleWidth_gap_or_lt_one_sub_apply_lightestPoint
    {n k r : ℕ} {Index : Type u} {Block : Type w}
    [Nonempty (ExactVisiblePostSwitchSurface (BitVec n) k)]
    (μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k))
    (T : ActualSwitchedLocalInterface (BitVec n) k Index Block)
    (q : ℝ≥0∞)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (hbad : 2 * r + 2 * k + 1 < n ∨ q < 1 - μ (PMF.lightestPoint μ)) :
    ¬ ∃ zfeat : BitVec n → BitVec r,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
            μ T zfeat q) := by
  rcases hbad with hgap | hq_lt
  · exact
      kpolyCoverage_anchor_surjectiveActualLocal_not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
        (n := n) (k := k) (r := r) (μ := μ) (T := T) (q := q) hsurj hgap
  · rintro ⟨zfeat, hdata⟩
    exact
      ActualSwitchedLocalInterface.not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_lt_one_sub_apply_lightestPoint
        (μ := μ) (T := T) (zfeat := zfeat) hsurj hq_lt hdata

/-- Route-coverage anchor: if the visible width already exceeds
`2*r + 2*k + 1`, then no extractor at all can support even the weaker shared
sparse-threshold ERM packet on a surjective actual-local `BitVec n`
endpoint. -/
theorem kpolyCoverage_anchor_surjectiveActualLocal_not_exists_sharedExactZABSparseThresholdERMData_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
    {n k r : ℕ} {Index : Type u} {Block : Type w}
    (T : ActualSwitchedLocalInterface (BitVec n) k Index Block)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (hgap : 2 * r + 2 * k + 1 < n) :
    ¬ ∃ zfeat : BitVec n → BitVec r,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMData
            T zfeat) :=
  ActualSwitchedLocalInterface.not_exists_sharedExactZABSparseThresholdERMData_of_surjective_predict_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
    (T := T) hsurj hgap

/-- Route-coverage anchor: below the intrinsic lightest-point threshold, no
extractor at all can support the manuscript-facing sparse-threshold recovery
packet on a surjective actual-local endpoint. -/
theorem kpolyCoverage_anchor_surjectiveActualLocal_not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_apply_lightestPoint
    {Z : Type v} [Fintype Z] {k r : ℕ} {Index : Type u} {Block : Type w}
    [Nonempty (ExactVisiblePostSwitchSurface Z k)]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (q : ℝ≥0∞)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (hq_lt : q < 1 - μ (PMF.lightestPoint μ)) :
    ¬ ∃ zfeat : Z → BitVec r,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
            μ T zfeat q) := by
  rintro ⟨zfeat, hdata⟩
  exact
    ActualSwitchedLocalInterface.not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_lt_one_sub_apply_lightestPoint
      (μ := μ) (T := T) (zfeat := zfeat) hsurj hq_lt hdata
end Mettapedia.Computability.PNP
