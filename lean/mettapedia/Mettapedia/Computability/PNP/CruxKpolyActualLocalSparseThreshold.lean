import Mettapedia.Computability.PNP.ActualSwitchedLocalPluginSampleMajoritySparseThresholdERMObstruction


/-!
# PNP `Kpoly` actual-local sparse-threshold anchors

Visible-budget and half-width barriers for shared exact sparse-threshold ERM data on actual-local endpoints.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal BigOperators

universe u v w z

/-- Route-coverage anchor: on any finite surjective actual-local endpoint, the
weaker shared sparse-threshold ERM packet still forces the exact visible
surface to fit inside the point-block visible budget
`2 * allAffinePointBlockFeatureCount (r + 2*k)`. -/
theorem kpolyCoverage_anchor_surjectiveActualLocal_surfaceCard_le_pointBlockVisibleBudget_of_nonempty_sharedExactZABSparseThresholdERMData
    {Z : Type v} [Fintype Z] {k r : ℕ} {Index : Type u} {Block : Type w}
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (zfeat : Z → BitVec r)
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMData
          T zfeat)) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      2 * allAffinePointBlockFeatureCount (r + (k + k)) := by
  rcases h with ⟨h⟩
  exact h.surfaceCard_le_of_surjective_predict hsurj

/-- Route-coverage anchor: equivalently, below that point-block visible-budget
threshold, no fixed extractor can support the weaker shared sparse-threshold
ERM packet on a surjective actual-local endpoint. -/
theorem kpolyCoverage_anchor_surjectiveActualLocal_not_nonempty_sharedExactZABSparseThresholdERMData_of_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k r : ℕ} {Index : Type u} {Block : Type w}
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (zfeat : Z → BitVec r)
    (hs :
      2 * allAffinePointBlockFeatureCount (r + (k + k)) <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMData
          T zfeat) :=
  ActualSwitchedLocalInterface.not_nonempty_sharedExactZABSparseThresholdERMData_of_surjective_predict_of_lt_surfaceCard
    (T := T) zfeat hsurj hs

/-- Route-coverage anchor: any surjective actual-local endpoint on
`BitVec n` already loses the manuscript-facing sparse-threshold recovery packet
below the unconditional half-width ceiling, regardless of extractor choice.
The concrete plug-in-majority and fallback repairs are only instances of this
surjective actual-local boundary. -/
theorem kpolyCoverage_anchor_surjectiveActualLocal_not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
    {n k r : ℕ} {Index : Type u} {Block : Type w}
    (μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k))
    (T : ActualSwitchedLocalInterface (BitVec n) k Index Block)
    (q : ℝ≥0∞)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (hgap : 2 * r + 2 * k + 1 < n) :
    ¬ ∃ zfeat : BitVec n → BitVec r,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
            μ T zfeat q) :=
  ActualSwitchedLocalInterface.not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
    (T := T) (μ := μ) (q := q) hsurj hgap

/-- Route-coverage anchor: on `BitVec n`, the same sample-level majority
endpoint cannot carry the stronger sparse-threshold recovery packet once the
visible width exceeds the unconditional half-width ceiling. -/
theorem kpolyCoverage_anchor_pluginSampleMajority_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
    {n k r : ℕ}
    (μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k))
    (zfeat : BitVec n → BitVec r)
    (q : ℝ≥0∞)
    (hgap : 2 * r + 2 * k + 1 < n) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ
          (pluginSampleMajorityActualSwitchedLocalInterface (BitVec n) k)
          zfeat
          q) :=
  pluginSampleMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
    (n := n) (k := k) (r := r) μ zfeat q hgap

end Mettapedia.Computability.PNP
