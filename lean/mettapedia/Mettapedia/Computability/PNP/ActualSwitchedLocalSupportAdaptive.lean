import Mettapedia.Computability.PNP.ActualSwitchedLocalFamily

/-!
# Adaptive Boolean query trees

Finite adaptive Boolean query trees and their simulation from reachable observed
block-output traces.
-/

namespace Mettapedia.Computability.PNP

universe v u w

/-- A finite adaptive Boolean query tree over an oracle
`Surface → Bool`.  A node queries one surface point and selects the next
subtree according to the Boolean answer. -/
inductive AdaptiveBoolQueryTree (Surface : Type u) (α : Type w) : Type (max u w) where
  | leaf : α → AdaptiveBoolQueryTree Surface α
  | query :
      Surface →
      AdaptiveBoolQueryTree Surface α →
      AdaptiveBoolQueryTree Surface α →
      AdaptiveBoolQueryTree Surface α

namespace AdaptiveBoolQueryTree

variable {Surface : Type*} {α : Type*} {Block : Type*}

/-- Evaluate an adaptive query tree against a Boolean oracle.  The second
subtree is followed on a `true` answer. -/
def eval (oracle : Surface → Bool) :
    AdaptiveBoolQueryTree Surface α → α
  | leaf value => value
  | query u ifFalse ifTrue =>
      if oracle u then eval oracle ifTrue else eval oracle ifFalse

/-- Every query node in the tree asks a point reached by the support map. -/
def AllQueriesReachable (visibleOf : Block → Surface) :
    AdaptiveBoolQueryTree Surface α → Prop
  | leaf _ => True
  | query u ifFalse ifTrue =>
      (∃ phi, visibleOf phi = u) ∧
        AllQueriesReachable visibleOf ifFalse ∧
        AllQueriesReachable visibleOf ifTrue

/-- If every adaptive query is reachable, the whole adaptive transcript can be
simulated from the observed block-output trace. -/
theorem exists_traceDecoder_of_allQueriesReachable
    (visibleOf : Block → Surface)
    (tree : AdaptiveBoolQueryTree Surface α)
    (hreach : AllQueriesReachable visibleOf tree) :
    ∃ decode : (Block → Bool) → α,
      ∀ oracle : Surface → Bool,
        decode (fun phi => oracle (visibleOf phi)) = eval oracle tree := by
  induction tree with
  | leaf value =>
      exact ⟨fun _ => value, by intro oracle; rfl⟩
  | query u ifFalse ifTrue ihFalse ihTrue =>
      rcases hreach with ⟨⟨phi, hphi⟩, hFalse, hTrue⟩
      rcases ihFalse hFalse with ⟨decodeFalse, hdecodeFalse⟩
      rcases ihTrue hTrue with ⟨decodeTrue, hdecodeTrue⟩
      refine
        ⟨fun trace => if trace phi then decodeTrue trace else decodeFalse trace, ?_⟩
      intro oracle
      by_cases hu : oracle u
      · simp [eval, hphi, hu, hdecodeTrue]
      · simp [eval, hphi, hu, hdecodeFalse]

end AdaptiveBoolQueryTree

end Mettapedia.Computability.PNP
