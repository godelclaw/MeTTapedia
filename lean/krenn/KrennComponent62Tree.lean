import KrennComponent62.Root
import KrennComponent62.SelectedSubtreeROOT

/-! A provenance-bound adapter from the complete selected-row tree to
the common component-tree interface used by the semantic connector. -/

namespace Krenn.Component62.Tree

abbrev rootEquations := Krenn.Component62.Root.rootEquations
abbrev RootCommonZero {R : Type*} [CommRing R]
    (values : Fin 60 → R) : Prop :=
  Krenn.Component62.Root.RootCommonZero values

theorem component62HasNoCommonZero {R : Type*} [Field R] [CharZero R]
    (values : Fin 60 → R) (rootZero : RootCommonZero values) : False := by
  exact Krenn.Component62.SelectedSubtreeROOT.subtreeROOTImpossible values rootZero

end Krenn.Component62.Tree

#print axioms Krenn.Component62.Tree.component62HasNoCommonZero
