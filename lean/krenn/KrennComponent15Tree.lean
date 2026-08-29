import KrennComponent15.Root
import KrennComponent15.SelectedSubtreeROOT

/-! A provenance-bound adapter from the complete selected-row tree to
the common component-tree interface used by the semantic connector. -/

namespace Krenn.Component15.Tree

abbrev rootEquations := Krenn.Component15.Root.rootEquations
abbrev RootCommonZero {R : Type*} [CommRing R]
    (values : Fin 57 → R) : Prop :=
  Krenn.Component15.Root.RootCommonZero values

theorem component15HasNoCommonZero {R : Type*} [Field R] [CharZero R]
    (values : Fin 57 → R) (rootZero : RootCommonZero values) : False := by
  exact Krenn.Component15.SelectedSubtreeROOT.subtreeROOTImpossible values rootZero

end Krenn.Component15.Tree

#print axioms Krenn.Component15.Tree.component15HasNoCommonZero
