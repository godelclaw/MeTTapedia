import Mettapedia.Computability.PNP.SharedExactZABFeatureFamilies

/-!
# P vs NP grassroots: shared exact ZAB target data

This module collects the route target-data structures for the shared-basis
`(zfeat(z), a, b)` route.  The affine-feature, sparse-threshold, and
decision-list consequence modules build on these data records.
-/

namespace Mettapedia.Computability.PNP

section

variable {Z : Type*} {p r k : ℕ} {Index : Type*}

structure SharedExactZABAffineFeatureTargetData
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (G : ExactVisibleSwitchedFamily Z k Index) where
  realized :
    RealizedBySharedExactZABAffineFeatureFamily
      (Z := Z) (p := p) (r := r) (k := k) zfeat features G

structure SharedExactZABSparseThresholdTargetData
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (G : ExactVisibleSwitchedFamily Z k Index) where
  realized :
    RealizedBySharedExactZABSparseThresholdAffineFamily
      (Z := Z) (p := p) (r := r) (k := k) zfeat features G

structure SharedExactZABDecisionListTargetData
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (G : ExactVisibleSwitchedFamily Z k Index) where
  realized :
    RealizedBySharedExactZABAffineDecisionListFamily
      (Z := Z) (p := p) (r := r) (k := k) zfeat features G

end

end Mettapedia.Computability.PNP
