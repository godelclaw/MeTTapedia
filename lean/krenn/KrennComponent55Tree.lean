import KrennComponent55.Root
import KrennComponent55.SelectedSubtreeROOT

/-! A provenance-bound adapter from the complete selected-row tree to
the common component-tree interface used by the semantic connector. -/

namespace Krenn.Component55.Tree

abbrev rootEquations := Krenn.Component55.Root.rootEquations
abbrev RootCommonZero {R : Type*} [CommRing R]
    (values : Fin 58 → R) : Prop :=
  Krenn.Component55.Root.RootCommonZero values

theorem component55HasNoCommonZero {R : Type*} [Field R] [CharZero R]
    (values : Fin 58 → R) (rootZero : RootCommonZero values) : False := by
  exact Krenn.Component55.SelectedSubtreeROOT.subtreeROOTImpossible values rootZero

end Krenn.Component55.Tree

#print axioms Krenn.Component55.Tree.component55HasNoCommonZero
