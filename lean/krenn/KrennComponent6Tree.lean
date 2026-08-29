import KrennComponent6.Root
import KrennComponent6.SelectedSubtreeROOT

/-! A provenance-bound adapter from the complete selected-row tree to
the common component-tree interface used by the semantic connector. -/

namespace Krenn.Component6.Tree

abbrev rootEquations := Krenn.Component6.Root.rootEquations
abbrev RootCommonZero {R : Type*} [CommRing R]
    (values : Fin 59 → R) : Prop :=
  Krenn.Component6.Root.RootCommonZero values

theorem component6HasNoCommonZero {R : Type*} [Field R] [CharZero R]
    (values : Fin 59 → R) (rootZero : RootCommonZero values) : False := by
  exact Krenn.Component6.SelectedSubtreeROOT.subtreeROOTImpossible values rootZero

end Krenn.Component6.Tree

#print axioms Krenn.Component6.Tree.component6HasNoCommonZero
