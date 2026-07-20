import Mettapedia.GraphTheory.FourColor.ClassicalCertificateResponseDag

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateResponseTree

open ClassicalCertificateKempeClosure

/-- A direct four-way decision tree for chromogram lookup.  Unlike an indexed
DAG, a lookup follows only the twelve constructors on its selected path. -/
inductive Tree where
  | empty
  | leaf (valueIndex : Nat)
  | node (push skip popSame popOpposite : Tree)

def lookup : Tree → Chromogram → Option Nat
  | .leaf valueIndex, [] => some valueIndex
  | .node push _ _ _, .push :: gram => lookup push gram
  | .node _ skip _ _, .skip :: gram => lookup skip gram
  | .node _ _ popSame _, .popSame :: gram => lookup popSame gram
  | .node _ _ _ popOpposite, .popOpposite :: gram =>
      lookup popOpposite gram
  | _, _ => none

end ClassicalCertificateResponseTree

end Mettapedia.GraphTheory.FourColor
