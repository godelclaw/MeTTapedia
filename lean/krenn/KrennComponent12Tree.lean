import KrennComponent12.Root
import KrennComponent12.SelectedSubtreeROOT

/-! A provenance-bound adapter from the complete selected-row tree to
the common component-tree interface used by the semantic connector. -/

namespace Krenn.Component12.Tree

abbrev rootEquations := Krenn.Component12.Root.rootEquations
abbrev RootCommonZero {R : Type*} [CommRing R]
    (values : Fin 59 → R) : Prop :=
  Krenn.Component12.Root.RootCommonZero values

theorem component12HasNoCommonZero {R : Type*} [Field R] [CharZero R]
    (values : Fin 59 → R) (rootZero : RootCommonZero values) : False := by
  exact Krenn.Component12.SelectedSubtreeROOT.subtreeROOTImpossible values rootZero

end Krenn.Component12.Tree

#print axioms Krenn.Component12.Tree.component12HasNoCommonZero
