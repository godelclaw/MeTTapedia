import KrennComponent39.Root
import KrennComponent39.SelectedSubtreeROOT

/-! A provenance-bound adapter from the complete selected-row tree to
the common component-tree interface used by the semantic connector. -/

namespace Krenn.Component39.Tree

abbrev rootEquations := Krenn.Component39.Root.rootEquations
abbrev RootCommonZero {R : Type*} [CommRing R]
    (values : Fin 61 → R) : Prop :=
  Krenn.Component39.Root.RootCommonZero values

theorem component39HasNoCommonZero {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R) (rootZero : RootCommonZero values) : False := by
  exact Krenn.Component39.SelectedSubtreeROOT.subtreeROOTImpossible values rootZero

end Krenn.Component39.Tree

#print axioms Krenn.Component39.Tree.component39HasNoCommonZero
