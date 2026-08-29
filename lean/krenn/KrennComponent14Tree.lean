import KrennComponent14.Root
import KrennComponent14.SelectedSubtreeROOT

/-! A provenance-bound adapter from the complete selected-row tree to
the common component-tree interface used by the semantic connector. -/

namespace Krenn.Component14.Tree

abbrev rootEquations := Krenn.Component14.Root.rootEquations
abbrev RootCommonZero {R : Type*} [CommRing R]
    (values : Fin 59 → R) : Prop :=
  Krenn.Component14.Root.RootCommonZero values

theorem component14HasNoCommonZero {R : Type*} [Field R] [CharZero R]
    (values : Fin 59 → R) (rootZero : RootCommonZero values) : False := by
  exact Krenn.Component14.SelectedSubtreeROOT.subtreeROOTImpossible values rootZero

end Krenn.Component14.Tree

#print axioms Krenn.Component14.Tree.component14HasNoCommonZero
