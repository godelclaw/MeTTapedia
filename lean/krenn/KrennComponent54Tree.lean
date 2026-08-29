import KrennComponent54.Root
import KrennComponent54.SelectedSubtreeROOT

/-! A provenance-bound adapter from the complete selected-row tree to
the common component-tree interface used by the semantic connector. -/

namespace Krenn.Component54.Tree

abbrev rootEquations := Krenn.Component54.Root.rootEquations
abbrev RootCommonZero {R : Type*} [CommRing R]
    (values : Fin 61 → R) : Prop :=
  Krenn.Component54.Root.RootCommonZero values

theorem component54HasNoCommonZero {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R) (rootZero : RootCommonZero values) : False := by
  exact Krenn.Component54.SelectedSubtreeROOT.subtreeROOTImpossible values rootZero

end Krenn.Component54.Tree

#print axioms Krenn.Component54.Tree.component54HasNoCommonZero
