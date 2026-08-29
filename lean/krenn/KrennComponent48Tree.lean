import KrennComponent48.Root
import KrennComponent48.SelectedSubtreeROOT

/-! A provenance-bound adapter from the complete selected-row tree to
the common component-tree interface used by the semantic connector. -/

namespace Krenn.Component48.Tree

abbrev rootEquations := Krenn.Component48.Root.rootEquations
abbrev RootCommonZero {R : Type*} [CommRing R]
    (values : Fin 60 → R) : Prop :=
  Krenn.Component48.Root.RootCommonZero values

theorem component48HasNoCommonZero {R : Type*} [Field R] [CharZero R]
    (values : Fin 60 → R) (rootZero : RootCommonZero values) : False := by
  exact Krenn.Component48.SelectedSubtreeROOT.subtreeROOTImpossible values rootZero

end Krenn.Component48.Tree

#print axioms Krenn.Component48.Tree.component48HasNoCommonZero
