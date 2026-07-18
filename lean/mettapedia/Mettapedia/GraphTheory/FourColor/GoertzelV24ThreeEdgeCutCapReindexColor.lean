import Mettapedia.GraphTheory.FourColor.GoertzelV24ThreeEdgeCutCapBridge

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationSpliceConstructor

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

namespace RotationSystem.ThreeEdgeCutSideData

variable {RS : RotationSystem V E} (data : ThreeEdgeCutSideData RS)

/-- Associate each dart of the original cap with the edge of a reindexed
cap carrying the same retained incidence. A cap dart is matched by its
original exposed boundary dart, not by its numeric position. -/
def capReindexEdgeOfDart (index : Equiv.Perm (Fin 3))
    (dart : data.CapDart) :
    (data.reindex index).capRewiredDartSystem.Edge :=
  match data.capDartEquiv dart with
  | Sum.inl retained =>
      (data.reindex index).capEdgeOfRetainedDart retained
  | Sum.inr step =>
      (data.reindex index).capEdgeOfRetainedDart
        (data.crossingBoundaryDartEquiv step).1

/-- Pull an edge coloring of a reindexed cap back to a dart coloring of the
original cap. -/
def capReindexDartColor (index : Equiv.Perm (Fin 3))
    (coloring :
      (data.reindex index).capRotationSystem.EdgeColoring Color)
    (dart : data.CapDart) : Color :=
  coloring (data.capReindexEdgeOfDart index dart)

@[simp]
theorem capReindexDartColor_capDartOfRetained
    (index : Equiv.Perm (Fin 3))
    (coloring :
      (data.reindex index).capRotationSystem.EdgeColoring Color)
    (dart : RetainedDart RS data.keep) :
    data.capReindexDartColor index coloring
        (data.capDartOfRetained dart) =
      coloring
        ((data.reindex index).capEdgeOfRetainedDart dart) := by
  simp [capReindexDartColor, capReindexEdgeOfDart]

@[simp]
theorem capReindexDartColor_capDart
    (index : Equiv.Perm (Fin 3))
    (coloring :
      (data.reindex index).capRotationSystem.EdgeColoring Color)
    (step : Fin 3) :
    data.capReindexDartColor index coloring (data.capDart step) =
      coloring ((data.reindex index).capEdgeOfRetainedDart
        (data.crossingBoundaryDartEquiv step).1) := by
  rfl

/-- The pulled-back dart color is invariant under the original cap edge
flip. -/
theorem capReindexDartColor_alpha
    (index : Equiv.Perm (Fin 3))
    (coloring :
      (data.reindex index).capRotationSystem.EdgeColoring Color)
    (dart : data.CapDart) :
    data.capReindexDartColor index coloring
        (data.capRewiredDartSystem.alpha dart) =
      data.capReindexDartColor index coloring dart := by
  rcases dart with internal | boundaryOrCap
  · change coloring
      ((data.reindex index).capEdgeOfRetainedDart
        (internalAlpha RS data.keep internal).1) =
        coloring ((data.reindex index).capEdgeOfRetainedDart internal.1)
    exact congrArg coloring
      ((data.reindex index).capEdgeOfRetainedDart_alpha_of_internal
        internal.1.1 internal.1.2 internal.2)
  · rcases boundaryOrCap with boundary | step
    · change coloring
        ((data.reindex index).capEdgeOfRetainedDart
          (data.crossingBoundaryDartEquiv
            (data.crossingBoundaryDartEquiv.symm boundary)).1) =
          coloring
            ((data.reindex index).capEdgeOfRetainedDart boundary.1)
      rw [Equiv.apply_symm_apply]
    · change coloring
        ((data.reindex index).capEdgeOfRetainedDart
          (data.crossingBoundaryDartEquiv step).1) =
          coloring
            ((data.reindex index).capEdgeOfRetainedDart
              (data.crossingBoundaryDartEquiv step).1)
      rfl

/-- Local properness of a reindexed cap coloring is preserved by pulling it
back through retained incidences. -/
theorem capReindexDartColor_proper
    (index : Equiv.Perm (Fin 3))
    (coloring :
      (data.reindex index).capRotationSystem.EdgeColoring Color)
    {left right : data.CapDart}
    (hvertex : data.capRewiredDartSystem.vertOf left =
      data.capRewiredDartSystem.vertOf right)
    (hne : left ≠ right) :
    data.capReindexDartColor index coloring left ≠
      data.capReindexDartColor index coloring right := by
  let leftTarget := data.capDartEquiv left
  let rightTarget := data.capDartEquiv right
  have htargetVertex :
      data.capTargetVert leftTarget = data.capTargetVert rightTarget := by
    rw [← data.capSeamData_vertOf_eq_capTargetVert,
      ← data.capSeamData_vertOf_eq_capTargetVert]
    exact hvertex
  have htargetNe : leftTarget ≠ rightTarget := by
    intro htargets
    exact hne (data.capDartEquiv.injective htargets)
  unfold capReindexDartColor capReindexEdgeOfDart
  rw [show data.capDartEquiv left = leftTarget by rfl,
    show data.capDartEquiv right = rightTarget by rfl]
  rcases leftTarget with leftRetained | leftStep <;>
    rcases rightTarget with rightRetained | rightStep
  · apply coloring.valid
    apply (data.reindex index).capEdgeAdj_of_retainedDarts
    · exact congrArg Subtype.val (Sum.inl.inj htargetVertex)
    · intro hdarts
      apply htargetNe
      apply congrArg Sum.inl
      exact Subtype.ext hdarts
  · change (Sum.inl _ : data.CapVertex) = Sum.inr () at htargetVertex
    exact False.elim (by cases htargetVertex)
  · change (Sum.inr () : data.CapVertex) = Sum.inl _ at htargetVertex
    exact False.elim (by cases htargetVertex)
  · apply coloring.valid
    change (data.reindex index).capRotationSystem.edgeAdjacencyGraph.Adj
      ((data.reindex index).capEdgeOfRetainedDart
        (data.crossingBoundaryDartEquiv leftStep).1)
      ((data.reindex index).capEdgeOfRetainedDart
        (data.crossingBoundaryDartEquiv rightStep).1)
    rw [(data.reindex index).capEdgeOfRetainedDart_eq_capEdge_of_boundary,
      (data.reindex index).capEdgeOfRetainedDart_eq_capEdge_of_boundary]
    apply (data.reindex index).capEdgeAdj_of_ne
    apply (data.reindex index).crossingBoundaryDartEquiv.symm.injective.ne
    intro hboundaries
    apply htargetNe
    apply congrArg Sum.inr
    exact data.crossingBoundaryDartEquiv.injective hboundaries

/-- Descend the pulled-back dart colors to an edge coloring of the original
cap. -/
def capColoringOfReindex (index : Equiv.Perm (Fin 3))
    (coloring :
      (data.reindex index).capRotationSystem.EdgeColoring Color) :
    data.capRotationSystem.EdgeColoring Color :=
  data.capRewiredDartSystem.descendedColoring
    (data.capReindexDartColor index coloring)
    (data.capReindexDartColor_alpha index coloring)
    (data.capReindexDartColor_proper index coloring)

/-- Tait colorings pull back across arbitrary reindexings of the three cap
spokes. -/
theorem capColoringOfReindex_isTait
    (index : Equiv.Perm (Fin 3))
    (coloring :
      (data.reindex index).capRotationSystem.EdgeColoring Color)
    (hTait :
      (data.reindex index).capRotationSystem.IsTaitEdgeColoring coloring) :
    data.capRotationSystem.IsTaitEdgeColoring
      (data.capColoringOfReindex index coloring) := by
  apply data.capRewiredDartSystem.descendedColoring_isTait
    (data.capReindexDartColor index coloring)
    (data.capReindexDartColor_alpha index coloring)
    (data.capReindexDartColor_proper index coloring)
  intro dart
  exact hTait (data.capReindexEdgeOfDart index dart)

/-- Colorability of any reindexed cap implies colorability of the original
ordered cap. -/
theorem cap_taitColorable_of_reindex
    (index : Equiv.Perm (Fin 3))
    (hcolorable : ∃ coloring,
      (data.reindex index).capRotationSystem.IsTaitEdgeColoring coloring) :
    ∃ coloring,
      data.capRotationSystem.IsTaitEdgeColoring coloring := by
  rcases hcolorable with ⟨coloring, hTait⟩
  exact ⟨data.capColoringOfReindex index coloring,
    data.capColoringOfReindex_isTait index coloring hTait⟩

/-- In particular, a Tait coloring of the independently planar-ordered cap
can be returned to the common cut order used for gluing. -/
theorem cap_taitColorable_of_planarOrdered
    (htwoSided : OrbitFacesTwoSided RS)
    (hcolorable : ∃ coloring,
      (data.planarOrdered htwoSided).capRotationSystem.IsTaitEdgeColoring
        coloring) :
    ∃ coloring,
      data.capRotationSystem.IsTaitEdgeColoring coloring := by
  exact data.cap_taitColorable_of_reindex
    (data.planarReindex htwoSided) hcolorable

end RotationSystem.ThreeEdgeCutSideData

end

end Mettapedia.GraphTheory.FourColor
