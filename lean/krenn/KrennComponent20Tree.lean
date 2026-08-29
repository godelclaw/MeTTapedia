import KrennComponent20.Root
import KrennComponent20.SelectedSubtreeROOT

/-! A provenance-bound adapter from the complete selected-row tree to
the common component-tree interface used by the semantic connector. -/

namespace Krenn.Component20.Tree

abbrev rootEquations := Krenn.Component20.Root.rootEquations
abbrev RootCommonZero {R : Type*} [CommRing R]
    (values : Fin 60 → R) : Prop :=
  Krenn.Component20.Root.RootCommonZero values

theorem component20HasNoCommonZero {R : Type*} [Field R] [CharZero R]
    (values : Fin 60 → R) (rootZero : RootCommonZero values) : False := by
  exact Krenn.Component20.SelectedSubtreeROOT.subtreeROOTImpossible values rootZero

end Krenn.Component20.Tree

#print axioms Krenn.Component20.Tree.component20HasNoCommonZero
