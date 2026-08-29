import KrennComponent56.Root
import KrennComponent56.SelectedSubtreeROOT

/-! A provenance-bound adapter from the complete selected-row tree to
the common component-tree interface used by the semantic connector. -/

namespace Krenn.Component56.Tree

abbrev rootEquations := Krenn.Component56.Root.rootEquations
abbrev RootCommonZero {R : Type*} [CommRing R]
    (values : Fin 57 → R) : Prop :=
  Krenn.Component56.Root.RootCommonZero values

theorem component56HasNoCommonZero {R : Type*} [Field R] [CharZero R]
    (values : Fin 57 → R) (rootZero : RootCommonZero values) : False := by
  exact Krenn.Component56.SelectedSubtreeROOT.subtreeROOTImpossible values rootZero

end Krenn.Component56.Tree

#print axioms Krenn.Component56.Tree.component56HasNoCommonZero
