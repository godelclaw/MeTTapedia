import KrennComponent60.Root
import KrennComponent60.SelectedSubtreeROOT

/-! A provenance-bound adapter from the complete selected-row tree to
the common component-tree interface used by the semantic connector. -/

namespace Krenn.Component60.Tree

abbrev rootEquations := Krenn.Component60.Root.rootEquations
abbrev RootCommonZero {R : Type*} [CommRing R]
    (values : Fin 61 → R) : Prop :=
  Krenn.Component60.Root.RootCommonZero values

theorem component60HasNoCommonZero {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R) (rootZero : RootCommonZero values) : False := by
  exact Krenn.Component60.SelectedSubtreeROOT.subtreeROOTImpossible values rootZero

end Krenn.Component60.Tree

#print axioms Krenn.Component60.Tree.component60HasNoCommonZero
