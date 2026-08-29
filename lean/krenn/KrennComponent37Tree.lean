import KrennComponent37.Root
import KrennComponent37.SelectedSubtreeROOT

/-! A provenance-bound adapter from the complete selected-row tree to
the common component-tree interface used by the semantic connector. -/

namespace Krenn.Component37.Tree

abbrev rootEquations := Krenn.Component37.Root.rootEquations
abbrev RootCommonZero {R : Type*} [CommRing R]
    (values : Fin 62 → R) : Prop :=
  Krenn.Component37.Root.RootCommonZero values

theorem component37HasNoCommonZero {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R) (rootZero : RootCommonZero values) : False := by
  exact Krenn.Component37.SelectedSubtreeROOT.subtreeROOTImpossible values rootZero

end Krenn.Component37.Tree

#print axioms Krenn.Component37.Tree.component37HasNoCommonZero
