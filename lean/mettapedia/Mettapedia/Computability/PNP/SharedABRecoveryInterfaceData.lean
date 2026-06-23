import Mettapedia.Computability.PNP.SharedABDecisionListRecoveryInterface

/-!
# Shared raw exact `(a,b)` recovery data

This module contains the affine-feature and sparse-threshold recovery data
structures shared by the recovery consequence modules.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {r k : ℕ} {Index : Type*}

structure SharedABAffineFeatureRecoveryData
    [Inhabited Z] [Fintype Z]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (G : ExactVisibleSwitchedFamily Z k Index)
    (q : ℝ≥0∞) where
  features : Fin r → AffineColumnCode (k + k)
  invariant : ABVisibleInvariant (Z := Z) (k := k) G
  realized :
    RealizedBySharedABAffineFeatureFamily (r := r) (k := k) features
      (liftToABVisibleFamily (Z := Z) (k := k) G)
  agreement_le :
    ∀ i,
      ∀ c :
        (sharedExactABAffineFeatureBitFamily Z features).toEncodedFamily.BadCodes
          (G.predict i),
        agreementMass μ (G.predict i)
          ((sharedExactABAffineFeatureBitFamily Z features).decode c.1) ≤ q

structure SharedABSparseThresholdRecoveryData
    [Inhabited Z] [Fintype Z]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (G : ExactVisibleSwitchedFamily Z k Index)
    (q : ℝ≥0∞) where
  features : Fin r → AffineColumnCode (k + k)
  invariant : ABVisibleInvariant (Z := Z) (k := k) G
  realized :
    RealizedBySharedABSparseThresholdAffineFamily (r := r) (k := k) features
      (liftToABVisibleFamily (Z := Z) (k := k) G)
  agreement_le :
    ∀ i,
      ∀ c :
        (sharedExactABSparseThresholdAffineBitFamily Z features).toEncodedFamily.BadCodes
          (G.predict i),
        agreementMass μ (G.predict i)
          ((sharedExactABSparseThresholdAffineBitFamily Z features).decode c.1) ≤ q

end

end Mettapedia.Computability.PNP
