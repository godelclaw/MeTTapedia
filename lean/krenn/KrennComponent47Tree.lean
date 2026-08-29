import KrennComponent47.Root
import KrennComponent47.SelectedSubtreeROOT

/-! A provenance-bound adapter from the complete selected-row tree to
the common component-tree interface used by the semantic connector. -/

namespace Krenn.Component47.Tree

abbrev rootEquations := Krenn.Component47.Root.rootEquations
abbrev RootCommonZero {R : Type*} [CommRing R]
    (values : Fin 58 → R) : Prop :=
  Krenn.Component47.Root.RootCommonZero values

theorem component47HasNoCommonZero {R : Type*} [Field R] [CharZero R]
    (values : Fin 58 → R) (rootZero : RootCommonZero values) : False := by
  exact Krenn.Component47.SelectedSubtreeROOT.subtreeROOTImpossible values rootZero

end Krenn.Component47.Tree

#print axioms Krenn.Component47.Tree.component47HasNoCommonZero
