import Mettapedia.Computability.PNP.SharedExactABFeatureERMRouteRecovery

/-!
# Shared exact `(a,b)` ERM interface data

This module contains the manuscript-facing recovery-data structures for ERM
over shared raw exact `(a,b)` affine-feature and sparse-threshold classes.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {r k : ℕ} {Index : Type*}

structure SharedExactABAffineFeatureERMRecoveryData
    [Inhabited Z] [Fintype Z]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (G : ExactVisibleSwitchedFamily Z k Index)
    (q : ℝ≥0∞) where
  features : Fin r → AffineColumnCode (k + k)
  samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool
  exact_family :
    G = sharedExactABAffineFeatureERMFamily (Z := Z) (r := r) (k := k) features samples
  agreement_le :
    ∀ i,
      ∀ c :
        (sharedExactABAffineFeatureBitFamily Z features).toEncodedFamily.BadCodes
          (G.predict i),
        agreementMass μ (G.predict i)
          ((sharedExactABAffineFeatureBitFamily Z features).decode c.1) ≤ q

structure SharedExactABSparseThresholdERMRecoveryData
    [Inhabited Z] [Fintype Z]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (G : ExactVisibleSwitchedFamily Z k Index)
    (q : ℝ≥0∞) where
  features : Fin r → AffineColumnCode (k + k)
  samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool
  exact_family :
    G =
      sharedExactABSparseThresholdAffineERMFamily
        (Z := Z) (r := r) (k := k) features samples
  agreement_le :
    ∀ i,
      ∀ c :
        (sharedExactABSparseThresholdAffineBitFamily Z features).toEncodedFamily.BadCodes
          (G.predict i),
        agreementMass μ (G.predict i)
          ((sharedExactABSparseThresholdAffineBitFamily Z features).decode c.1) ≤ q

end

end Mettapedia.Computability.PNP
