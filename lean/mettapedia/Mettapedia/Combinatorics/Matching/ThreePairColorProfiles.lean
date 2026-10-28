import Mettapedia.Combinatorics.Matching.Sum

/-! Color multiplicities for a transversal of three bichromatic pairs. -/

namespace MatchingColorProfile

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- Three disjoint bichromatic pairs have multiplicities `(0,3,3)`, `(1,2,3)`
or `(2,2,2)`, up to a permutation of the three colors. In particular the middle
profile alone is not exhaustive. -/
theorem threePair_profile :
    ∀ c : Fin 6 → Fin 3,
      c 0 ≠ c 1 → c 2 ≠ c 3 → c 4 ≠ c 5 →
      ([ (MatchingSum.colourFiber c 0).card,
          (MatchingSum.colourFiber c 1).card,
          (MatchingSum.colourFiber c 2).card ].Perm [0, 3, 3] ∨
       [ (MatchingSum.colourFiber c 0).card,
          (MatchingSum.colourFiber c 1).card,
          (MatchingSum.colourFiber c 2).card ].Perm [1, 2, 3] ∨
       [ (MatchingSum.colourFiber c 0).card,
          (MatchingSum.colourFiber c 1).card,
          (MatchingSum.colourFiber c 2).card ].Perm [2, 2, 2]) := by
  decide

end MatchingColorProfile
