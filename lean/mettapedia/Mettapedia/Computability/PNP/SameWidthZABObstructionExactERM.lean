import Mettapedia.Computability.PNP.ExactZABInjectiveBranchObstructionExactDecisionList
import Mettapedia.Computability.PNP.ExactZABInjectiveBranchObstructionSharedAffineFeature
import Mettapedia.Computability.PNP.ExactZABInjectiveBranchObstructionSharedDecisionList
import Mettapedia.Computability.PNP.SameWidthZABObstructionArithmetic

/-!
# Same-width exact ZAB obstruction: exact ERM consequence

This module applies the same-width arithmetic budget bound to the exact
decision-list ERM route.
-/

namespace Mettapedia.Computability.PNP
section ExactERM

variable {n k : ℕ} {Index : Type*}

theorem exactZABDecisionListERMFamily_not_surjective_of_sameWidth
    (zfeat : BitVec n → BitVec n)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hvisible : 2 ≤ n + 2 * k) :
    ¬ Function.Surjective
        (exactZABDecisionListERMFamily
          (Z := BitVec n) (r := n) (k := k) zfeat samples).predict := by
  exact
    exactZABDecisionListERMFamily_not_surjective_of_extractorWidth_lt_truthTableGap
      (n := n) (r := n) (k := k) (Index := Index) zfeat samples
      (sameWidthExtractor_lt_truthTableGap_of_two_le_visibleWidth
        (n := n) (k := k) hvisible)

end ExactERM

end Mettapedia.Computability.PNP
