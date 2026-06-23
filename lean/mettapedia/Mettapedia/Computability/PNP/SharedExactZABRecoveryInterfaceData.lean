import Mettapedia.Computability.PNP.SharedExactZABTargetInterfaceData
import Mettapedia.Computability.PNP.SharedExactZABTargetInterfaceAffineFeature
import Mettapedia.Computability.PNP.SharedExactZABTargetInterfaceSparseThreshold
import Mettapedia.Computability.PNP.SharedExactZABTargetInterfaceDecisionList
import Mettapedia.Computability.PNP.SharedExactZABTargetInterfaceDecisionListRecovery

/-!
# P vs NP grassroots: shared exact ZAB recovery data

This module collects the affine-feature and sparse-threshold recovery-data
records for the shared-basis exact `(zfeat(z), a, b)` route.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {p r k : ℕ} {Index : Type*}

structure SharedExactZABAffineFeatureRecoveryData
    [Fintype Z]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (zfeat : Z → BitVec r)
    (G : ExactVisibleSwitchedFamily Z k Index)
    (q : ℝ≥0∞) where
  features : Fin p → AffineColumnCode (r + (k + k))
  realized :
    RealizedBySharedExactZABAffineFeatureFamily
      (Z := Z) (p := p) (r := r) (k := k) zfeat features G
  agreement_le :
    ∀ i,
      ∀ c :
        (sharedExactZABAffineFeatureBitFamily Z zfeat features).toEncodedFamily.BadCodes
          (G.predict i),
        agreementMass μ (G.predict i)
          ((sharedExactZABAffineFeatureBitFamily Z zfeat features).decode c.1) ≤ q

structure SharedExactZABSparseThresholdRecoveryData
    [Fintype Z]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (zfeat : Z → BitVec r)
    (G : ExactVisibleSwitchedFamily Z k Index)
    (q : ℝ≥0∞) where
  features : Fin p → AffineColumnCode (r + (k + k))
  realized :
    RealizedBySharedExactZABSparseThresholdAffineFamily
      (Z := Z) (p := p) (r := r) (k := k) zfeat features G
  agreement_le :
    ∀ i,
      ∀ c :
        (sharedExactZABSparseThresholdAffineBitFamily Z zfeat features).toEncodedFamily.BadCodes
          (G.predict i),
        agreementMass μ (G.predict i)
          ((sharedExactZABSparseThresholdAffineBitFamily Z zfeat features).decode c.1) ≤ q

end

end Mettapedia.Computability.PNP
