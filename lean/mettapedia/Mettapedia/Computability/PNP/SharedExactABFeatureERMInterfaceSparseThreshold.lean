import Mettapedia.Computability.PNP.SharedExactABFeatureERMInterfaceData

/-!
# Shared exact `(a,b)` sparse-threshold ERM interface

This module derives manuscript-facing target, compression, surface-card, and
recovery consequences from sparse-threshold ERM recovery data.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {r k : ℕ} {Index : Type*}
variable [Inhabited Z] [Fintype Z]

def SharedExactABSparseThresholdERMRecoveryData.targetData
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactABSparseThresholdERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q) :
    SharedABSparseThresholdTargetData
      (Z := Z) (r := r) (k := k) (Index := Index) G := by
  rcases h with ⟨features, samples, rfl, agreement_le⟩
  exact sharedExactABSparseThresholdAffineERMTargetData
    (Z := Z) (r := r) (k := k) (Index := Index) features samples

theorem SharedExactABSparseThresholdERMRecoveryData.compressionTarget
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactABSparseThresholdERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index) G (2 * r) := by
  rcases h with ⟨features, samples, rfl, agreement_le⟩
  exact sharedExactABSparseThresholdAffineERMCompressionTarget
    (Z := Z) (r := r) (k := k) (Index := Index) features samples

theorem SharedExactABSparseThresholdERMRecoveryData.surfaceCard_le_of_surjective_predict
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactABSparseThresholdERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q)
    (hsurj : Function.Surjective G.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ 2 * r := by
  exact (h.targetData).surfaceCard_le_of_surjective_predict hsurj

theorem SharedExactABSparseThresholdERMRecoveryData.not_surjective_predict_of_lt_surfaceCard
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactABSparseThresholdERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q)
    (hs : 2 * r < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective G.predict := by
  exact (h.targetData).not_surjective_predict_of_lt_surfaceCard hs

theorem SharedExactABSparseThresholdERMRecoveryData.recoveryLowerBound
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactABSparseThresholdERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (2 * r) : ℝ≥0∞) * q ^ m ≤
      (sharedExactABSparseThresholdAffineBitFamily Z h.features).bitExactRecoverySampleMass
        μ (G.predict i) m := by
  rcases h with ⟨features, samples, rfl, agreement_le⟩
  exact sharedExactABSparseThresholdAffineERMRecoveryLowerBound
    (Z := Z) (r := r) (k := k) (Index := Index)
    μ features samples q agreement_le i m

end

end Mettapedia.Computability.PNP
