import KrennComponent16.Root
import KrennComponent16.SelectedSubtreeROOT

/-! A provenance-bound adapter from the complete selected-row tree to
the common component-tree interface used by the semantic connector. -/

namespace Krenn.Component16.Tree

abbrev rootEquations := Krenn.Component16.Root.rootEquations
abbrev RootCommonZero {R : Type*} [CommRing R]
    (values : Fin 62 → R) : Prop :=
  Krenn.Component16.Root.RootCommonZero values

theorem component16HasNoCommonZero {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R) (rootZero : RootCommonZero values) : False := by
  exact Krenn.Component16.SelectedSubtreeROOT.subtreeROOTImpossible values rootZero

end Krenn.Component16.Tree

#print axioms Krenn.Component16.Tree.component16HasNoCommonZero
