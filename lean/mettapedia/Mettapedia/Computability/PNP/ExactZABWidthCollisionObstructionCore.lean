import Mettapedia.Computability.PNP.ExactZABVisibleCollisionObstructionCore
import Mettapedia.Computability.PNP.ExactZABVisibleCollisionObstructionTargets
import Mettapedia.Computability.PNP.ExactZABVisibleCollisionObstructionRecovery
import Mettapedia.Computability.PNP.ExactZABVisibleCollisionObstructionERM

/-!
# Exact ZAB width-collision obstruction: core extractor fact

This module contains the route-independent cardinality fact: a width-compressing
`BitVec n → BitVec r` extractor is noninjective.
-/

namespace Mettapedia.Computability.PNP
section Core

theorem not_injective_bitVecExtractor_of_width_lt
    {n r : ℕ}
    (zfeat : BitVec n → BitVec r)
    (hwidth : r < n) :
    ¬ Function.Injective zfeat := by
  apply not_injective_of_card_gt_bitVec (Z := BitVec n) (r := r) zfeat
  simpa [BitVec] using (Nat.pow_lt_pow_right Nat.one_lt_two hwidth)

end Core

end Mettapedia.Computability.PNP
