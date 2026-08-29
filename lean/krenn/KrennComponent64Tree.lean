import KrennComponent64.Root
import KrennComponent64.SelectedSubtreeROOT

/-! A provenance-bound adapter from the complete selected-row tree to
the common component-tree interface used by the semantic connector. -/

namespace Krenn.Component64.Tree

abbrev rootEquations := Krenn.Component64.Root.rootEquations
abbrev RootCommonZero {R : Type*} [CommRing R]
    (values : Fin 60 → R) : Prop :=
  Krenn.Component64.Root.RootCommonZero values

theorem component64HasNoCommonZero {R : Type*} [Field R] [CharZero R]
    (values : Fin 60 → R) (rootZero : RootCommonZero values) : False := by
  exact Krenn.Component64.SelectedSubtreeROOT.subtreeROOTImpossible values rootZero

end Krenn.Component64.Tree

#print axioms Krenn.Component64.Tree.component64HasNoCommonZero
