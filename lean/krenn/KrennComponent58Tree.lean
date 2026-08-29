import KrennComponent58.Root
import KrennComponent58.SelectedSubtreeROOT

/-! A provenance-bound adapter from the complete selected-row tree to
the common component-tree interface used by the semantic connector. -/

namespace Krenn.Component58.Tree

abbrev rootEquations := Krenn.Component58.Root.rootEquations
abbrev RootCommonZero {R : Type*} [CommRing R]
    (values : Fin 59 → R) : Prop :=
  Krenn.Component58.Root.RootCommonZero values

theorem component58HasNoCommonZero {R : Type*} [Field R] [CharZero R]
    (values : Fin 59 → R) (rootZero : RootCommonZero values) : False := by
  exact Krenn.Component58.SelectedSubtreeROOT.subtreeROOTImpossible values rootZero

end Krenn.Component58.Tree

#print axioms Krenn.Component58.Tree.component58HasNoCommonZero
