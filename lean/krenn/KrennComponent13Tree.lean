import KrennComponent13.Root
import KrennComponent13.SelectedSubtreeROOT

/-! A provenance-bound adapter from the complete selected-row tree to
the common component-tree interface used by the semantic connector. -/

namespace Krenn.Component13.Tree

abbrev rootEquations := Krenn.Component13.Root.rootEquations
abbrev RootCommonZero {R : Type*} [CommRing R]
    (values : Fin 58 → R) : Prop :=
  Krenn.Component13.Root.RootCommonZero values

theorem component13HasNoCommonZero {R : Type*} [Field R] [CharZero R]
    (values : Fin 58 → R) (rootZero : RootCommonZero values) : False := by
  exact Krenn.Component13.SelectedSubtreeROOT.subtreeROOTImpossible values rootZero

end Krenn.Component13.Tree

#print axioms Krenn.Component13.Tree.component13HasNoCommonZero
