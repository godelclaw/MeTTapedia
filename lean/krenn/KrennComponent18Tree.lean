import KrennComponent18.Root
import KrennComponent18.SelectedSubtreeROOT

/-! A provenance-bound adapter from the complete selected-row tree to
the common component-tree interface used by the semantic connector. -/

namespace Krenn.Component18.Tree

abbrev rootEquations := Krenn.Component18.Root.rootEquations
abbrev RootCommonZero {R : Type*} [CommRing R]
    (values : Fin 61 → R) : Prop :=
  Krenn.Component18.Root.RootCommonZero values

theorem component18HasNoCommonZero {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R) (rootZero : RootCommonZero values) : False := by
  exact Krenn.Component18.SelectedSubtreeROOT.subtreeROOTImpossible values rootZero

end Krenn.Component18.Tree

#print axioms Krenn.Component18.Tree.component18HasNoCommonZero
