import Mettapedia.Computability.PNP.SharedABTargetInterfaceCore

/-!
# Shared raw `(a,b)` decision-list recovery interface

This module keeps the decision-list-specific exact-recovery lower bound
separate from the generic shared-AB target-data interfaces.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {r k : ℕ} {Index : Type*}

structure SharedABDecisionListRecoveryData
    [Inhabited Z]
    [Fintype Z]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (features : Fin r → AffineColumnCode (k + k))
    (G : ExactVisibleSwitchedFamily Z k Index)
    (q : ℝ≥0∞)
    where
  invariant : ABVisibleInvariant (Z := Z) (k := k) G
  realized :
    RealizedBySharedABAffineDecisionListFamily (r := r) (k := k) features
      (liftToABVisibleFamily (Z := Z) (k := k) G)
  agreement_le :
    ∀ i,
      ∀ c :
        (sharedExactABAffineDecisionListBitFamily Z features).toEncodedFamily.BadCodes
          (G.predict i),
        agreementMass μ (G.predict i)
          ((sharedExactABAffineDecisionListBitFamily Z features).decode c.1) ≤ q

section

variable [Inhabited Z] [Fintype Z]

def SharedABDecisionListRecoveryData.targetData
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {features : Fin r → AffineColumnCode (k + k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedABDecisionListRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index)
        μ features G q) :
    SharedABDecisionListTargetData
      (Z := Z) (r := r) (k := k) (Index := Index) G where
  features := features
  invariant := h.invariant
  realized := h.realized

theorem SharedABDecisionListRecoveryData.compressionTarget
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {features : Fin r → AffineColumnCode (k + k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedABDecisionListRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index)
        μ features G q) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (r + 1) := by
  exact (h.targetData).compressionTarget

theorem SharedABDecisionListRecoveryData.surfaceCard_le_of_surjective_predict
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {features : Fin r → AffineColumnCode (k + k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedABDecisionListRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index)
        μ features G q)
    (hsurj : Function.Surjective G.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ r + 1 := by
  exact (h.targetData).surfaceCard_le_of_surjective_predict hsurj

theorem SharedABDecisionListRecoveryData.not_surjective_predict_of_lt_surfaceCard
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {features : Fin r → AffineColumnCode (k + k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedABDecisionListRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index)
        μ features G q)
    (hs : r + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective G.predict := by
  exact (h.targetData).not_surjective_predict_of_lt_surfaceCard hs

theorem SharedABDecisionListRecoveryData.recoveryLowerBound
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {features : Fin r → AffineColumnCode (k + k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedABDecisionListRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index)
        μ features G q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (r + 1) : ℝ≥0∞) * q ^ m ≤
      (sharedExactABAffineDecisionListBitFamily Z features).bitExactRecoverySampleMass
        μ (G.predict i) m := by
  have hexact :
      RealizedBySharedExactABAffineDecisionListFamily (Z := Z) (r := r) (k := k) features G :=
    realizedBySharedExactABAffineDecisionListFamily_of_factorsThrough_ab
      (Z := Z) (r := r) (k := k)
      (factorsThrough_abVisibleData_of_invariant (Z := Z) (k := k) h.invariant)
      h.realized
  rcases hexact i with ⟨code, hcode⟩
  exact sharedExactABAffineDecisionListRecoveryLowerBound
    (Z := Z) (r := r) (k := k) features
    (μ := μ) (target := G.predict i) (m := m)
    ⟨code, hcode⟩ (h.agreement_le i)

end

end

end Mettapedia.Computability.PNP
