import KrennComponent24.Root
import KrennComponent24.SelectedSubtreeROOT

/-! A provenance-bound adapter from the complete selected-row tree to
the common component-tree interface used by the semantic connector. -/

namespace Krenn.Component24.Tree

abbrev rootEquations := Krenn.Component24.Root.rootEquations
abbrev RootCommonZero {R : Type*} [CommRing R]
    (values : Fin 62 → R) : Prop :=
  Krenn.Component24.Root.RootCommonZero values

theorem component24HasNoCommonZero {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R) (rootZero : RootCommonZero values) : False := by
  exact Krenn.Component24.SelectedSubtreeROOT.subtreeROOTImpossible values rootZero

end Krenn.Component24.Tree

#print axioms Krenn.Component24.Tree.component24HasNoCommonZero
