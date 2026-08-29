import KrennComponent19.Root
import KrennComponent19.SelectedSubtreeROOT

/-! A provenance-bound adapter from the complete selected-row tree to
the common component-tree interface used by the semantic connector. -/

namespace Krenn.Component19.Tree

abbrev rootEquations := Krenn.Component19.Root.rootEquations
abbrev RootCommonZero {R : Type*} [CommRing R]
    (values : Fin 62 → R) : Prop :=
  Krenn.Component19.Root.RootCommonZero values

theorem component19HasNoCommonZero {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R) (rootZero : RootCommonZero values) : False := by
  exact Krenn.Component19.SelectedSubtreeROOT.subtreeROOTImpossible values rootZero

end Krenn.Component19.Tree

#print axioms Krenn.Component19.Tree.component19HasNoCommonZero
