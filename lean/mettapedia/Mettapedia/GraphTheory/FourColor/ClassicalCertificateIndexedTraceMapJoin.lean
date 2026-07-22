import Mettapedia.GraphTheory.FourColor.ClassicalCertificateIndexedTraceMap

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateIndexedTraceMap

open ClassicalCertificateTraceTree

namespace Tree

def isNode : Tree → Bool
  | .node _ _ _ => true
  | _ => false

/-- A ternary trace-map node is checked by composing its three independently
checked symbol branches. -/
theorem checkAt_of_isNode_and_children
    (accepts : Nat → List TraceSymbol → Bool) (length : Nat)
    (tree : Tree) (stem : List TraceSymbol)
    (hnode : tree.isNode = true)
    (hred : checkAt accepts length (tree.child .red)
      (stem ++ [.red]) = true)
    (hblue : checkAt accepts length (tree.child .blue)
      (stem ++ [.blue]) = true)
    (hpurple : checkAt accepts length (tree.child .purple)
      (stem ++ [.purple]) = true) :
    checkAt accepts (length + 1) tree stem = true := by
  cases tree with
  | empty => simp [isNode] at hnode
  | leaf value => simp [isNode] at hnode
  | node red blue purple =>
      simp only [child] at hred hblue hpurple
      simp [checkAt, hred, hblue, hpurple]

end Tree

end ClassicalCertificateIndexedTraceMap

end Mettapedia.GraphTheory.FourColor
