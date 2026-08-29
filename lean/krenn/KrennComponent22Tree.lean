import KrennComponent22.Root
import KrennComponent22.SelectedSubtreeROOT

/-! A provenance-bound adapter from the complete selected-row tree to
the common component-tree interface used by the semantic connector. -/

namespace Krenn.Component22.Tree

abbrev rootEquations := Krenn.Component22.Root.rootEquations
abbrev RootCommonZero {R : Type*} [CommRing R]
    (values : Fin 60 → R) : Prop :=
  Krenn.Component22.Root.RootCommonZero values

theorem component22HasNoCommonZero {R : Type*} [Field R] [CharZero R]
    (values : Fin 60 → R) (rootZero : RootCommonZero values) : False := by
  exact Krenn.Component22.SelectedSubtreeROOT.subtreeROOTImpossible values rootZero

end Krenn.Component22.Tree

#print axioms Krenn.Component22.Tree.component22HasNoCommonZero
