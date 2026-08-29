import KrennComponent1.Root
import KrennComponent1.SelectedSubtreeROOT

/-! A provenance-bound adapter from the complete selected-row tree to
the common component-tree interface used by the semantic connector. -/

namespace Krenn.Component1.Tree

abbrev rootEquations := Krenn.Component1.Root.rootEquations
abbrev RootCommonZero {R : Type*} [CommRing R]
    (values : Fin 57 → R) : Prop :=
  Krenn.Component1.Root.RootCommonZero values

theorem component1HasNoCommonZero {R : Type*} [Field R] [CharZero R]
    (values : Fin 57 → R) (rootZero : RootCommonZero values) : False := by
  exact Krenn.Component1.SelectedSubtreeROOT.subtreeROOTImpossible values rootZero

end Krenn.Component1.Tree

#print axioms Krenn.Component1.Tree.component1HasNoCommonZero
