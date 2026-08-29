import KrennComponent52.Root
import KrennComponent52.SelectedSubtreeROOT

/-! A provenance-bound adapter from the complete selected-row tree to
the common component-tree interface used by the semantic connector. -/

namespace Krenn.Component52.Tree

abbrev rootEquations := Krenn.Component52.Root.rootEquations
abbrev RootCommonZero {R : Type*} [CommRing R]
    (values : Fin 60 → R) : Prop :=
  Krenn.Component52.Root.RootCommonZero values

theorem component52HasNoCommonZero {R : Type*} [Field R] [CharZero R]
    (values : Fin 60 → R) (rootZero : RootCommonZero values) : False := by
  exact Krenn.Component52.SelectedSubtreeROOT.subtreeROOTImpossible values rootZero

end Krenn.Component52.Tree

#print axioms Krenn.Component52.Tree.component52HasNoCommonZero
