import Mettapedia.Computability.PNP.SharedExactZABFeatureERMRouteFamilies
import Mettapedia.Computability.PNP.SharedExactZABFeatureERMRouteTargets
import Mettapedia.Computability.PNP.SharedExactZABFeatureERMRouteRecovery

/-!
# P vs NP grassroots: shared exact ZAB feature ERM interface data

This module collects the final manuscript-facing ERM recovery-data records for
the shared exact `(zfeat(z), a, b)` affine-feature and sparse-threshold classes.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {p r k : ℕ} {Index : Type*}

structure SharedExactZABAffineFeatureERMRecoveryData
    [Fintype Z]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (zfeat : Z → BitVec r)
    (G : ExactVisibleSwitchedFamily Z k Index)
    (q : ℝ≥0∞) where
  features : Fin p → AffineColumnCode (r + (k + k))
  samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool
  exact_family :
    G =
      sharedExactZABAffineFeatureERMFamily
        (Z := Z) (p := p) (r := r) (k := k) zfeat features samples
  agreement_le :
    ∀ i,
      ∀ c :
        (sharedExactZABAffineFeatureBitFamily Z zfeat features).toEncodedFamily.BadCodes
          (G.predict i),
        agreementMass μ (G.predict i)
          ((sharedExactZABAffineFeatureBitFamily Z zfeat features).decode c.1) ≤ q

structure SharedExactZABSparseThresholdERMRecoveryData
    [Fintype Z]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (zfeat : Z → BitVec r)
    (G : ExactVisibleSwitchedFamily Z k Index)
    (q : ℝ≥0∞) where
  features : Fin p → AffineColumnCode (r + (k + k))
  samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool
  exact_family :
    G =
      sharedExactZABSparseThresholdAffineERMFamily
        (Z := Z) (p := p) (r := r) (k := k) zfeat features samples
  agreement_le :
    ∀ i,
      ∀ c :
        (sharedExactZABSparseThresholdAffineBitFamily Z zfeat features).toEncodedFamily.BadCodes
          (G.predict i),
        agreementMass μ (G.predict i)
          ((sharedExactZABSparseThresholdAffineBitFamily Z zfeat features).decode c.1) ≤ q

end

end Mettapedia.Computability.PNP
