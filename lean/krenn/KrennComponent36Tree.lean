import KrennComponent36.Root
import KrennComponent36.SelectedSubtreeROOT

/-! A provenance-bound adapter from the complete selected-row tree to
the common component-tree interface used by the semantic connector. -/

namespace Krenn.Component36.Tree

abbrev rootEquations := Krenn.Component36.Root.rootEquations
abbrev RootCommonZero {R : Type*} [CommRing R]
    (values : Fin 62 → R) : Prop :=
  Krenn.Component36.Root.RootCommonZero values

theorem component36HasNoCommonZero {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R) (rootZero : RootCommonZero values) : False := by
  exact Krenn.Component36.SelectedSubtreeROOT.subtreeROOTImpossible values rootZero

end Krenn.Component36.Tree

#print axioms Krenn.Component36.Tree.component36HasNoCommonZero
