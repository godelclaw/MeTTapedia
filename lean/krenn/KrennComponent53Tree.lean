import KrennComponent53.Root
import KrennComponent53.SelectedSubtreeROOT

/-! A provenance-bound adapter from the complete selected-row tree to
the common component-tree interface used by the semantic connector. -/

namespace Krenn.Component53.Tree

abbrev rootEquations := Krenn.Component53.Root.rootEquations
abbrev RootCommonZero {R : Type*} [CommRing R]
    (values : Fin 61 → R) : Prop :=
  Krenn.Component53.Root.RootCommonZero values

theorem component53HasNoCommonZero {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R) (rootZero : RootCommonZero values) : False := by
  exact Krenn.Component53.SelectedSubtreeROOT.subtreeROOTImpossible values rootZero

end Krenn.Component53.Tree

#print axioms Krenn.Component53.Tree.component53HasNoCommonZero
