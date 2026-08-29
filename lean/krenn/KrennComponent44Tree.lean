import KrennComponent44.Root
import KrennComponent44.SelectedSubtreeROOT

/-! A provenance-bound adapter from the complete selected-row tree to
the common component-tree interface used by the semantic connector. -/

namespace Krenn.Component44.Tree

abbrev rootEquations := Krenn.Component44.Root.rootEquations
abbrev RootCommonZero {R : Type*} [CommRing R]
    (values : Fin 60 → R) : Prop :=
  Krenn.Component44.Root.RootCommonZero values

theorem component44HasNoCommonZero {R : Type*} [Field R] [CharZero R]
    (values : Fin 60 → R) (rootZero : RootCommonZero values) : False := by
  exact Krenn.Component44.SelectedSubtreeROOT.subtreeROOTImpossible values rootZero

end Krenn.Component44.Tree

#print axioms Krenn.Component44.Tree.component44HasNoCommonZero
