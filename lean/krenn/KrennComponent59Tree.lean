import KrennComponent59.Root
import KrennComponent59.SelectedSubtreeROOT

/-! A provenance-bound adapter from the complete selected-row tree to
the common component-tree interface used by the semantic connector. -/

namespace Krenn.Component59.Tree

abbrev rootEquations := Krenn.Component59.Root.rootEquations
abbrev RootCommonZero {R : Type*} [CommRing R]
    (values : Fin 58 → R) : Prop :=
  Krenn.Component59.Root.RootCommonZero values

theorem component59HasNoCommonZero {R : Type*} [Field R] [CharZero R]
    (values : Fin 58 → R) (rootZero : RootCommonZero values) : False := by
  exact Krenn.Component59.SelectedSubtreeROOT.subtreeROOTImpossible values rootZero

end Krenn.Component59.Tree

#print axioms Krenn.Component59.Tree.component59HasNoCommonZero
