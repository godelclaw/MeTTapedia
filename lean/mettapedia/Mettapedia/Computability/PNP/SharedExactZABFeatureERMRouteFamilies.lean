import Mettapedia.Computability.PNP.BitFamilyERM
import Mettapedia.Computability.PNP.SharedExactZABRecoveryInterfaceData
import Mettapedia.Computability.PNP.SharedExactZABRecoveryInterfaceAffineFeature
import Mettapedia.Computability.PNP.SharedExactZABRecoveryInterfaceSparseThreshold

/-!
# P vs NP grassroots: shared exact ZAB feature ERM families

This module defines the empirical-risk-minimizing switched families for the
shared-basis exact `(zfeat(z), a, b)` affine-feature and sparse-threshold
classes.
-/

namespace Mettapedia.Computability.PNP
section

variable {Z : Type*} {p r k : ℕ} {Index : Type*}

/-- ERM inside the shared exact `(zfeat(z), a, b)` affine-feature class. -/
noncomputable def sharedExactZABAffineFeatureERMFamily
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ExactVisibleSwitchedFamily Z k Index :=
  (sharedExactZABAffineFeatureBitFamily Z zfeat features).indexedEmpiricalRiskFamily samples

/-- ERM inside the shared exact `(zfeat(z), a, b)` sparse-threshold class. -/
noncomputable def sharedExactZABSparseThresholdAffineERMFamily
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ExactVisibleSwitchedFamily Z k Index :=
  (sharedExactZABSparseThresholdAffineBitFamily Z zfeat features).indexedEmpiricalRiskFamily samples

end

end Mettapedia.Computability.PNP
