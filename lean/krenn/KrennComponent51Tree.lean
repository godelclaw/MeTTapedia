import KrennComponent51.Root
import KrennComponent51.SelectedSubtreeROOT

/-! A provenance-bound adapter from the complete selected-row tree to
the common component-tree interface used by the semantic connector. -/

namespace Krenn.Component51.Tree

abbrev rootEquations := Krenn.Component51.Root.rootEquations
abbrev RootCommonZero {R : Type*} [CommRing R]
    (values : Fin 59 → R) : Prop :=
  Krenn.Component51.Root.RootCommonZero values

theorem component51HasNoCommonZero {R : Type*} [Field R] [CharZero R]
    (values : Fin 59 → R) (rootZero : RootCommonZero values) : False := by
  exact Krenn.Component51.SelectedSubtreeROOT.subtreeROOTImpossible values rootZero

end Krenn.Component51.Tree

#print axioms Krenn.Component51.Tree.component51HasNoCommonZero
