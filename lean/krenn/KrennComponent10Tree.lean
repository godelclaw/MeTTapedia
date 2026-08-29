import KrennComponent10.Root
import KrennComponent10.SelectedSubtreeROOT

/-! A provenance-bound adapter from the complete selected-row tree to
the common component-tree interface used by the semantic connector. -/

namespace Krenn.Component10.Tree

abbrev rootEquations := Krenn.Component10.Root.rootEquations
abbrev RootCommonZero {R : Type*} [CommRing R]
    (values : Fin 60 → R) : Prop :=
  Krenn.Component10.Root.RootCommonZero values

theorem component10HasNoCommonZero {R : Type*} [Field R] [CharZero R]
    (values : Fin 60 → R) (rootZero : RootCommonZero values) : False := by
  exact Krenn.Component10.SelectedSubtreeROOT.subtreeROOTImpossible values rootZero

end Krenn.Component10.Tree

#print axioms Krenn.Component10.Tree.component10HasNoCommonZero
