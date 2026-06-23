import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryPayloadObstruction


/-!
# PNP `Kpoly` actual-local recovery-payload anchors

Sparse-threshold recovery payload cardinality barriers for surjective and injectively realized actual-local endpoints.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal BigOperators

universe u v w z

/-- Route-coverage anchor: on any finite surjective actual-local endpoint, the
manuscript-facing sparse-threshold recovery packet already implies the bundled
finite-learning payload, so it is impossible below the full predictor-image
cardinality. -/
theorem kpolyCoverage_anchor_surjectiveActualLocal_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_lt_predictorCard
    {Z : Type v} [Fintype Z] {k r : ℕ} {Index : Type u} {Block : Type w}
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (zfeat : Z → BitVec r)
    (q : ℝ≥0∞)
    (hs :
      2 ^ (2 * allAffinePointBlockFeatureCount (r + (k + k))) <
        2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hsurj : Function.Surjective T.predictorFamily.predict) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ T zfeat q) :=
  ActualSwitchedLocalInterface.not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_lt_predictorCard
    (μ := μ) (T := T) (zfeat := zfeat) (q := q) hs hsurj

/-- Route-coverage anchor: the same predictor-card obstruction already removes
the extractor choice itself on surjective actual-local endpoints. -/
theorem kpolyCoverage_anchor_surjectiveActualLocal_not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_lt_predictorCard
    {Z : Type v} [Fintype Z] {k r : ℕ} {Index : Type u} {Block : Type w}
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (q : ℝ≥0∞)
    (hs :
      2 ^ (2 * allAffinePointBlockFeatureCount (r + (k + k))) <
        2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hsurj : Function.Surjective T.predictorFamily.predict) :
    ¬ ∃ zfeat : Z → BitVec r,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
            μ T zfeat q) :=
  ActualSwitchedLocalInterface.not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_lt_predictorCard
    (μ := μ) (T := T) (q := q) hs hsurj

/-- Route-coverage anchor: more generally, any injectively realized finite
probe family larger than the current payload budget already blocks the
manuscript-facing sparse-threshold recovery packet, without needing full
surjectivity. -/
theorem kpolyCoverage_anchor_actualLocal_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_injective_realization_of_lt_card
    {Probe : Type*} [Fintype Probe]
    {Z : Type v} [Fintype Z] {k r : ℕ} {Index : Type u} {Block : Type w}
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (zfeat : Z → BitVec r)
    (q : ℝ≥0∞)
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, T.predictorFamily.predict i = target p)
    (hs :
      2 ^ (2 * allAffinePointBlockFeatureCount (r + (k + k))) <
        Fintype.card Probe) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ T zfeat q) :=
  ActualSwitchedLocalInterface.not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_injective_realization_of_lt_card
    (μ := μ) (T := T) (zfeat := zfeat) (q := q) target hinj hreal hs

/-- Route-coverage anchor: the same injective finite-probe payload obstruction
also removes the extractor choice itself. -/
theorem kpolyCoverage_anchor_actualLocal_not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_injective_realization_of_lt_card
    {Probe : Type*} [Fintype Probe]
    {Z : Type v} [Fintype Z] {k r : ℕ} {Index : Type u} {Block : Type w}
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (q : ℝ≥0∞)
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, T.predictorFamily.predict i = target p)
    (hs :
      2 ^ (2 * allAffinePointBlockFeatureCount (r + (k + k))) <
        Fintype.card Probe) :
    ¬ ∃ zfeat : Z → BitVec r,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
            μ T zfeat q) :=
  ActualSwitchedLocalInterface.not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_injective_realization_of_lt_card
    (μ := μ) (T := T) (q := q) target hinj hreal hs

end Mettapedia.Computability.PNP
