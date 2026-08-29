import KrennComponent25.Root
import KrennComponent25.SelectedSubtreeROOT

/-! A provenance-bound adapter from the complete selected-row tree to
the common component-tree interface used by the semantic connector. -/

namespace Krenn.Component25.Tree

abbrev rootEquations := Krenn.Component25.Root.rootEquations
abbrev RootCommonZero {R : Type*} [CommRing R]
    (values : Fin 61 → R) : Prop :=
  Krenn.Component25.Root.RootCommonZero values

theorem component25HasNoCommonZero {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R) (rootZero : RootCommonZero values) : False := by
  exact Krenn.Component25.SelectedSubtreeROOT.subtreeROOTImpossible values rootZero

end Krenn.Component25.Tree

#print axioms Krenn.Component25.Tree.component25HasNoCommonZero
