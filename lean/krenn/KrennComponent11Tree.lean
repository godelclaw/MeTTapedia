import KrennComponent11.Root
import KrennComponent11.SelectedSubtreeROOT

/-! A provenance-bound adapter from the complete selected-row tree to
the common component-tree interface used by the semantic connector. -/

namespace Krenn.Component11.Tree

abbrev rootEquations := Krenn.Component11.Root.rootEquations
abbrev RootCommonZero {R : Type*} [CommRing R]
    (values : Fin 61 → R) : Prop :=
  Krenn.Component11.Root.RootCommonZero values

theorem component11HasNoCommonZero {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R) (rootZero : RootCommonZero values) : False := by
  exact Krenn.Component11.SelectedSubtreeROOT.subtreeROOTImpossible values rootZero

end Krenn.Component11.Tree

#print axioms Krenn.Component11.Tree.component11HasNoCommonZero
