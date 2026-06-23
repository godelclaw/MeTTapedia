import Mettapedia.Computability.PNP.BitVecZABCompressionObstruction
import Mettapedia.Computability.PNP.ExactZABERMRoute

/-!
# P vs NP crux: injective exact-ZAB raw decision-list branch

This module records the extractor-width lower bound for the raw exact
decision-list ERM route on `BitVec n`.
-/

namespace Mettapedia.Computability.PNP
section Route

variable {n r k : ℕ} {Index : Type*}

theorem exactZABDecisionListERMFamily_extractorWidthLowerBound_of_surjective_predict
    (zfeat : BitVec n → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hsurj :
      Function.Surjective
        (exactZABDecisionListERMFamily
          (Z := BitVec n) (r := r) (k := k) zfeat samples).predict) :
    2 ^ (n + 2 * k) - (2 * k + 1) ≤ r := by
  let s := 2 ^ (n + 2 * k)
  have hs : s ≤ r + 2 * k + 1 := by
    simpa [s, card_exactVisiblePostSwitchSurface_bitVec] using
      (exactZABDecisionListERMFamily_surfaceCard_le_of_surjective_predict
        (Z := BitVec n) (r := r) (k := k) (Index := Index) zfeat samples hsurj)
  rw [Nat.sub_le_iff_le_add]
  simpa [s, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hs

theorem exactZABDecisionListERMFamily_not_surjective_of_extractorWidth_lt_truthTableGap
    (zfeat : BitVec n → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hgap : r < 2 ^ (n + 2 * k) - (2 * k + 1)) :
    ¬ Function.Surjective
        (exactZABDecisionListERMFamily
          (Z := BitVec n) (r := r) (k := k) zfeat samples).predict := by
  intro hsurj
  exact Nat.not_le_of_lt hgap <|
    exactZABDecisionListERMFamily_extractorWidthLowerBound_of_surjective_predict
      (n := n) (r := r) (k := k) (Index := Index) zfeat samples hsurj

end Route

end Mettapedia.Computability.PNP
