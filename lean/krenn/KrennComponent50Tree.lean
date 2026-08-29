import KrennComponent50.Root
import KrennComponent50.SelectedSubtreeROOT

/-! A provenance-bound adapter from the complete selected-row tree to
the common component-tree interface used by the semantic connector. -/

namespace Krenn.Component50.Tree

abbrev rootEquations := Krenn.Component50.Root.rootEquations
abbrev RootCommonZero {R : Type*} [CommRing R]
    (values : Fin 60 → R) : Prop :=
  Krenn.Component50.Root.RootCommonZero values

theorem component50HasNoCommonZero {R : Type*} [Field R] [CharZero R]
    (values : Fin 60 → R) (rootZero : RootCommonZero values) : False := by
  exact Krenn.Component50.SelectedSubtreeROOT.subtreeROOTImpossible values rootZero

end Krenn.Component50.Tree

#print axioms Krenn.Component50.Tree.component50HasNoCommonZero
