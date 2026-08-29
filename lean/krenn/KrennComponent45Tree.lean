import KrennComponent45.Root
import KrennComponent45.SelectedSubtreeROOT

/-! A provenance-bound adapter from the complete selected-row tree to
the common component-tree interface used by the semantic connector. -/

namespace Krenn.Component45.Tree

abbrev rootEquations := Krenn.Component45.Root.rootEquations
abbrev RootCommonZero {R : Type*} [CommRing R]
    (values : Fin 57 → R) : Prop :=
  Krenn.Component45.Root.RootCommonZero values

theorem component45HasNoCommonZero {R : Type*} [Field R] [CharZero R]
    (values : Fin 57 → R) (rootZero : RootCommonZero values) : False := by
  exact Krenn.Component45.SelectedSubtreeROOT.subtreeROOTImpossible values rootZero

end Krenn.Component45.Tree

#print axioms Krenn.Component45.Tree.component45HasNoCommonZero
