import Mettapedia.Computability.PNP.BitVecZABCompressionObstruction
import Mettapedia.Computability.PNP.SharedExactZABFeatureERMRouteFamilies
import Mettapedia.Computability.PNP.SharedExactZABFeatureERMRouteTargets
import Mettapedia.Computability.PNP.SharedExactZABFeatureERMRouteRecovery

/-!
# P vs NP crux: injective exact-ZAB shared affine-feature branch

This module records the shared feature-count lower bound for the shared exact
affine-feature ERM route on `BitVec n`.
-/

namespace Mettapedia.Computability.PNP
section Route

variable {n p r k : ℕ} {Index : Type*}

theorem sharedExactZABAffineFeatureERMFamily_featureCountLowerBound_of_surjective_predict
    (zfeat : BitVec n → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hsurj :
      Function.Surjective
        (sharedExactZABAffineFeatureERMFamily
          (Z := BitVec n) (p := p) (r := r) (k := k) zfeat features samples).predict) :
    n + 2 * k ≤ p := by
  have hpow :
      2 ^ (n + 2 * k) ≤ 2 ^ p := by
    simpa [card_exactVisiblePostSwitchSurface_bitVec] using
      (sharedExactZABAffineFeatureERMFamily_surfaceCard_le_of_surjective_predict
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index)
        zfeat features samples hsurj)
  exact (Nat.pow_le_pow_iff_right Nat.one_lt_two).1 hpow

theorem sharedExactZABAffineFeatureERMFamily_not_surjective_of_featureCount_lt_visibleWidth
    (zfeat : BitVec n → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hfeat : p < n + 2 * k) :
    ¬ Function.Surjective
        (sharedExactZABAffineFeatureERMFamily
          (Z := BitVec n) (p := p) (r := r) (k := k) zfeat features samples).predict := by
  intro hsurj
  exact Nat.not_le_of_lt hfeat <|
    sharedExactZABAffineFeatureERMFamily_featureCountLowerBound_of_surjective_predict
      (n := n) (p := p) (r := r) (k := k) (Index := Index) zfeat features samples hsurj

end Route

end Mettapedia.Computability.PNP
