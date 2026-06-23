import Mettapedia.Computability.PNP.BitVecZABCompressionObstruction
import Mettapedia.Computability.PNP.SharedExactZABERMRoute

/-!
# P vs NP crux: injective exact-ZAB shared decision-list branch

This module records the shared decision-list combiner-width lower bound for the
shared exact affine-decision-list ERM route on `BitVec n`.
-/

namespace Mettapedia.Computability.PNP
section Route

variable {n p r k : ℕ} {Index : Type*}

theorem sharedExactZABAffineDecisionListERMFamily_combinerWidthLowerBound_of_surjective_predict
    (zfeat : BitVec n → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hsurj :
      Function.Surjective
        (sharedExactZABAffineDecisionListERMFamily
          (Z := BitVec n) (p := p) (r := r) (k := k)
          zfeat features samples).predict) :
    2 ^ (n + 2 * k) - 1 ≤ p := by
  let s := 2 ^ (n + 2 * k)
  have hs : s ≤ p + 1 := by
    simpa [s, card_exactVisiblePostSwitchSurface_bitVec] using
      (sharedExactZABAffineDecisionListERMFamily_surfaceCard_le_of_surjective_predict
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index)
        zfeat features samples hsurj)
  rw [Nat.sub_le_iff_le_add]
  simpa [s, Nat.add_comm] using hs

theorem sharedExactZABAffineDecisionListERMFamily_not_surjective_of_combinerWidth_lt_truthTableGap
    (zfeat : BitVec n → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hgap : p < 2 ^ (n + 2 * k) - 1) :
    ¬ Function.Surjective
        (sharedExactZABAffineDecisionListERMFamily
          (Z := BitVec n) (p := p) (r := r) (k := k)
          zfeat features samples).predict := by
  intro hsurj
  exact Nat.not_le_of_lt hgap <|
    sharedExactZABAffineDecisionListERMFamily_combinerWidthLowerBound_of_surjective_predict
      (n := n) (p := p) (r := r) (k := k) (Index := Index)
      zfeat features samples hsurj

end Route

end Mettapedia.Computability.PNP
