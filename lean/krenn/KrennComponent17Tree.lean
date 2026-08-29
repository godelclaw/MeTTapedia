import KrennComponent17.Root
import KrennComponent17.SelectedSubtreeROOT

/-! A provenance-bound adapter from the complete selected-row tree to
the common component-tree interface used by the semantic connector. -/

namespace Krenn.Component17.Tree

abbrev rootEquations := Krenn.Component17.Root.rootEquations
abbrev RootCommonZero {R : Type*} [CommRing R]
    (values : Fin 59 → R) : Prop :=
  Krenn.Component17.Root.RootCommonZero values

theorem component17HasNoCommonZero {R : Type*} [Field R] [CharZero R]
    (values : Fin 59 → R) (rootZero : RootCommonZero values) : False := by
  exact Krenn.Component17.SelectedSubtreeROOT.subtreeROOTImpossible values rootZero

end Krenn.Component17.Tree

#print axioms Krenn.Component17.Tree.component17HasNoCommonZero
