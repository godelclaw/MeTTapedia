import Mettapedia.Computability.PNP.SharedABRecoveryInterfaceAffine

/-!
# Shared raw exact `(a,b)` sparse-threshold recovery interface

This module packages the sparse-threshold recovery data and derives the
compression and exact-recovery consequences.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {r k : ℕ} {Index : Type*}

section

variable [Inhabited Z] [Fintype Z]

def SharedABSparseThresholdRecoveryData.targetData
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedABSparseThresholdRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q) :
    SharedABSparseThresholdTargetData
      (Z := Z) (r := r) (k := k) (Index := Index) G where
  features := h.features
  invariant := h.invariant
  realized := h.realized

theorem SharedABSparseThresholdRecoveryData.compressionTarget
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedABSparseThresholdRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index) G (2 * r) := by
  exact (h.targetData).compressionTarget

theorem SharedABSparseThresholdRecoveryData.surfaceCard_le_of_surjective_predict
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedABSparseThresholdRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q)
    (hsurj : Function.Surjective G.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ 2 * r := by
  exact (h.targetData).surfaceCard_le_of_surjective_predict hsurj

theorem SharedABSparseThresholdRecoveryData.not_surjective_predict_of_lt_surfaceCard
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedABSparseThresholdRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q)
    (hs : 2 * r < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective G.predict := by
  exact (h.targetData).not_surjective_predict_of_lt_surfaceCard hs

theorem SharedABSparseThresholdRecoveryData.recoveryLowerBound
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedABSparseThresholdRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (2 * r) : ℝ≥0∞) * q ^ m ≤
      (sharedExactABSparseThresholdAffineBitFamily Z h.features).bitExactRecoverySampleMass
        μ (G.predict i) m := by
  have hexact :
      RealizedBySharedExactABSparseThresholdAffineFamily
        (Z := Z) (r := r) (k := k) h.features G :=
    realizedBySharedExactABSparseThresholdAffineFamily_of_factorsThrough_ab
      (Z := Z) (r := r) (k := k)
      (factorsThrough_abVisibleData_of_invariant (Z := Z) (k := k) h.invariant)
      h.realized
  rcases hexact i with ⟨code, hcode⟩
  exact sharedExactABSparseThresholdAffineRecoveryLowerBound
    (Z := Z) (r := r) (k := k) h.features
    (μ := μ) (target := G.predict i) (m := m)
    ⟨code, hcode⟩ (h.agreement_le i)

end

end

end Mettapedia.Computability.PNP
