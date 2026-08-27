import Mettapedia.GraphTheory.FourColor.GoertzelV24DualPathTransversal
import Mettapedia.GraphTheory.FourColor.GoertzelV24InteriorDualPointwiseLookup

/-!
# Facial-dual transversals from pointwise incidence receipts

The opened annular carrier does not satisfy the historical global hypothesis
`PairwiseUniqueSharedInteriorEdges`: the two hole faces may share many edges.
A dual walk never consumes that statement globally.  At step `i` it asks only
that the two consecutive faces at positions `i` and `i + 1` share at most one
interior edge.

This file gives the dual-walk transversal construction that exact dependency.
It mirrors the established global API, proves the same injectivity and support
theorems directly, and proves extensional agreement with the old lookup when
the stronger premise is available.  Thus migrating a Cell witness changes its
receipt, not its selected primal edges.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24DualPathPointwiseTransversal

open GoertzelV24DualPathTransversal
open GoertzelV24FaceDualConnectedness
open GoertzelV24InteriorDualPointwiseLookup
open SimpleGraph

variable {F E : Type*} [Fintype F] [DecidableEq F]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- The exact uniqueness receipt consumed by one facial-dual walk. -/
def DualWalkStepUnique
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    {start finish : AmbientFace allFaces}
    (walk : (interiorDualGraph faceBoundary allFaces).Walk start finish) : Prop :=
  ∀ step : Fin walk.length,
    (sharedInteriorEdges faceBoundary allFaces
      (walk.getVert step.val).1
      (walk.getVert (step.val + 1)).1).card ≤ 1

/-- Global pairwise uniqueness implies the pointwise receipt on every walk. -/
theorem dualWalkStepUnique_of_pairwiseUnique
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    {start finish : AmbientFace allFaces}
    (walk : (interiorDualGraph faceBoundary allFaces).Walk start finish) :
    DualWalkStepUnique faceBoundary allFaces walk := by
  intro step
  exact card_le_one_of_pairwiseUnique faceBoundary allFaces hunique
    (walk.adj_getVert_succ step.isLt)

/-- The primal edge crossed at one dual-walk step, selected from that step's
local incidence receipt. -/
noncomputable def pointwiseDualWalkCrossingEdge
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    {start finish : AmbientFace allFaces}
    (walk : (interiorDualGraph faceBoundary allFaces).Walk start finish)
    (hlocal : DualWalkStepUnique faceBoundary allFaces walk)
    (step : Fin walk.length) : E :=
  sharedInteriorEdgeOfAdj faceBoundary allFaces (hlocal step)
    (walk.adj_getVert_succ step.isLt)

/-- The selected edge is in the shared interior-edge set of its two faces. -/
theorem pointwiseDualWalkCrossingEdge_mem_shared
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    {start finish : AmbientFace allFaces}
    (walk : (interiorDualGraph faceBoundary allFaces).Walk start finish)
    (hlocal : DualWalkStepUnique faceBoundary allFaces walk)
    (step : Fin walk.length) :
    pointwiseDualWalkCrossingEdge faceBoundary allFaces walk hlocal step ∈
      sharedInteriorEdges faceBoundary allFaces
        (walk.getVert step.val).1
        (walk.getVert (step.val + 1)).1 :=
  sharedInteriorEdgeOfAdj_mem faceBoundary allFaces (hlocal step)
    (walk.adj_getVert_succ step.isLt)

/-- A pointwise dual-walk crossing is an ambient interior edge. -/
theorem pointwiseDualWalkCrossingEdge_mem_interiorEdgeSupport
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    {start finish : AmbientFace allFaces}
    (walk : (interiorDualGraph faceBoundary allFaces).Walk start finish)
    (hlocal : DualWalkStepUnique faceBoundary allFaces walk)
    (step : Fin walk.length) :
    pointwiseDualWalkCrossingEdge faceBoundary allFaces walk hlocal step ∈
      interiorEdgeSupport faceBoundary allFaces :=
  (mem_sharedInteriorEdges_iff faceBoundary allFaces).1
    (pointwiseDualWalkCrossingEdge_mem_shared faceBoundary allFaces walk hlocal step) |>.1

/-- The crossed edge lies on the face before its dual step. -/
theorem pointwiseDualWalkCrossingEdge_mem_leftFace
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    {start finish : AmbientFace allFaces}
    (walk : (interiorDualGraph faceBoundary allFaces).Walk start finish)
    (hlocal : DualWalkStepUnique faceBoundary allFaces walk)
    (step : Fin walk.length) :
    pointwiseDualWalkCrossingEdge faceBoundary allFaces walk hlocal step ∈
      faceBoundary (walk.getVert step.val).1 :=
  (mem_sharedInteriorEdges_iff faceBoundary allFaces).1
    (pointwiseDualWalkCrossingEdge_mem_shared faceBoundary allFaces walk hlocal step) |>.2.1

/-- The crossed edge lies on the face after its dual step. -/
theorem pointwiseDualWalkCrossingEdge_mem_rightFace
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    {start finish : AmbientFace allFaces}
    (walk : (interiorDualGraph faceBoundary allFaces).Walk start finish)
    (hlocal : DualWalkStepUnique faceBoundary allFaces walk)
    (step : Fin walk.length) :
    pointwiseDualWalkCrossingEdge faceBoundary allFaces walk hlocal step ∈
      faceBoundary (walk.getVert (step.val + 1)).1 :=
  (mem_sharedInteriorEdges_iff faceBoundary allFaces).1
    (pointwiseDualWalkCrossingEdge_mem_shared faceBoundary allFaces walk hlocal step) |>.2.2

/-- The selected edge is independent of the proof used for the pointwise
receipt. -/
theorem pointwiseDualWalkCrossingEdge_congr
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    {start finish : AmbientFace allFaces}
    (walk : (interiorDualGraph faceBoundary allFaces).Walk start finish)
    (hlocal hlocal' : DualWalkStepUnique faceBoundary allFaces walk)
    (step : Fin walk.length) :
    pointwiseDualWalkCrossingEdge faceBoundary allFaces walk hlocal step =
      pointwiseDualWalkCrossingEdge faceBoundary allFaces walk hlocal' step :=
  sharedInteriorEdgeOfAdj_congr faceBoundary allFaces
    (hlocal step) (hlocal' step)
    (walk.adj_getVert_succ step.isLt) (walk.adj_getVert_succ step.isLt)

/-- Migration is exact: under the old global premise the new and old crossing
edges are equal at every position. -/
theorem pointwiseDualWalkCrossingEdge_eq_dualWalkCrossingEdge
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    {start finish : AmbientFace allFaces}
    (walk : (interiorDualGraph faceBoundary allFaces).Walk start finish)
    (step : Fin walk.length) :
    pointwiseDualWalkCrossingEdge faceBoundary allFaces walk
        (dualWalkStepUnique_of_pairwiseUnique faceBoundary allFaces hunique walk) step =
      dualWalkCrossingEdge faceBoundary allFaces hunique walk step :=
  sharedInteriorEdgeOfAdj_eq_sharedInteriorEdgeOfAdjOfPairwiseUnique
    faceBoundary allFaces hunique (walk.adj_getVert_succ step.isLt)

/-- A simple facial-dual path crosses distinct primal edges using only the
pointwise step receipt. -/
theorem pointwiseDualWalkCrossingEdge_injective_of_isPath
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (hall : ∀ edge, totalIncidenceCount faceBoundary allFaces edge ≤ 2)
    {start finish : AmbientFace allFaces}
    (walk : (interiorDualGraph faceBoundary allFaces).Walk start finish)
    (hlocal : DualWalkStepUnique faceBoundary allFaces walk)
    (hpath : walk.IsPath) :
    Function.Injective
      (pointwiseDualWalkCrossingEdge faceBoundary allFaces walk hlocal) := by
  intro first second hedges
  let firstLeft := walk.getVert first.val
  let firstRight := walk.getVert (first.val + 1)
  let secondLeft := walk.getVert second.val
  let secondRight := walk.getVert (second.val + 1)
  have hfirstAdj := walk.adj_getVert_succ first.isLt
  have hfirstFaces : firstLeft.1 ≠ firstRight.1 := by
    intro hfaces
    exact hfirstAdj.ne (Subtype.ext hfaces)
  have hfirstLeft :
      pointwiseDualWalkCrossingEdge faceBoundary allFaces walk hlocal first ∈
        faceBoundary firstLeft.1 :=
    pointwiseDualWalkCrossingEdge_mem_leftFace
      faceBoundary allFaces walk hlocal first
  have hfirstRight :
      pointwiseDualWalkCrossingEdge faceBoundary allFaces walk hlocal first ∈
        faceBoundary firstRight.1 :=
    pointwiseDualWalkCrossingEdge_mem_rightFace
      faceBoundary allFaces walk hlocal first
  have hsecondLeft :
      pointwiseDualWalkCrossingEdge faceBoundary allFaces walk hlocal first ∈
        faceBoundary secondLeft.1 := by
    rw [hedges]
    exact pointwiseDualWalkCrossingEdge_mem_leftFace
      faceBoundary allFaces walk hlocal second
  have hsecondRight :
      pointwiseDualWalkCrossingEdge faceBoundary allFaces walk hlocal first ∈
        faceBoundary secondRight.1 := by
    rw [hedges]
    exact pointwiseDualWalkCrossingEdge_mem_rightFace
      faceBoundary allFaces walk hlocal second
  have hsecondLeftCases :=
    eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
      faceBoundary allFaces hall firstLeft.2 firstRight.2 secondLeft.2
      hfirstFaces hfirstLeft hfirstRight hsecondLeft
  rcases hsecondLeftCases with hsecondFirst | hsecondNext
  · apply Fin.ext
    exact hpath.getVert_injOn
      (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega)
      (Subtype.ext hsecondFirst.symm)
  · have hsecondVal : second.val = first.val + 1 :=
      hpath.getVert_injOn
        (by simp only [Set.mem_setOf_eq]; omega)
        (by simp only [Set.mem_setOf_eq]; omega)
        (Subtype.ext hsecondNext)
    have hsecondRightCases :=
      eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
        faceBoundary allFaces hall firstLeft.2 firstRight.2 secondRight.2
        hfirstFaces hfirstLeft hfirstRight hsecondRight
    rcases hsecondRightCases with hrightFirst | hrightNext
    · have hvalue : second.val + 1 = first.val :=
        hpath.getVert_injOn
          (by simp only [Set.mem_setOf_eq]; omega)
          (by simp only [Set.mem_setOf_eq]; omega)
          (Subtype.ext hrightFirst)
      omega
    · have hvalue : second.val + 1 = first.val + 1 :=
        hpath.getVert_injOn
          (by simp only [Set.mem_setOf_eq]; omega)
          (by simp only [Set.mem_setOf_eq]; omega)
          (Subtype.ext hrightNext)
      omega

/-- The finite set of primal edges crossed by a pointwise facial-dual walk. -/
def pointwiseDualWalkCrossingEdges
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    {start finish : AmbientFace allFaces}
    (walk : (interiorDualGraph faceBoundary allFaces).Walk start finish)
    (hlocal : DualWalkStepUnique faceBoundary allFaces walk) : Finset E :=
  Finset.univ.image
    (pointwiseDualWalkCrossingEdge faceBoundary allFaces walk hlocal)

@[simp]
theorem mem_pointwiseDualWalkCrossingEdges_iff
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    {start finish : AmbientFace allFaces}
    (walk : (interiorDualGraph faceBoundary allFaces).Walk start finish)
    (hlocal : DualWalkStepUnique faceBoundary allFaces walk)
    (edge : E) :
    edge ∈ pointwiseDualWalkCrossingEdges faceBoundary allFaces walk hlocal ↔
      ∃ step : Fin walk.length,
        pointwiseDualWalkCrossingEdge faceBoundary allFaces walk hlocal step = edge := by
  simp [pointwiseDualWalkCrossingEdges]

/-- A pointwise simple dual path crosses exactly one distinct primal edge per
step. -/
theorem card_pointwiseDualWalkCrossingEdges_eq_length_of_isPath
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (hall : ∀ edge, totalIncidenceCount faceBoundary allFaces edge ≤ 2)
    {start finish : AmbientFace allFaces}
    (walk : (interiorDualGraph faceBoundary allFaces).Walk start finish)
    (hlocal : DualWalkStepUnique faceBoundary allFaces walk)
    (hpath : walk.IsPath) :
    (pointwiseDualWalkCrossingEdges faceBoundary allFaces walk hlocal).card =
      walk.length := by
  rw [pointwiseDualWalkCrossingEdges,
    Finset.card_image_of_injective _
      (pointwiseDualWalkCrossingEdge_injective_of_isPath
        faceBoundary allFaces hall walk hlocal hpath),
    Finset.card_univ, Fintype.card_fin]

/-- Under a global receipt, the finite supports computed by the old and new
APIs are equal. -/
theorem pointwiseDualWalkCrossingEdges_eq_dualWalkCrossingEdges
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    {start finish : AmbientFace allFaces}
    (walk : (interiorDualGraph faceBoundary allFaces).Walk start finish) :
    pointwiseDualWalkCrossingEdges faceBoundary allFaces walk
        (dualWalkStepUnique_of_pairwiseUnique faceBoundary allFaces hunique walk) =
      dualWalkCrossingEdges faceBoundary allFaces hunique walk := by
  unfold pointwiseDualWalkCrossingEdges dualWalkCrossingEdges
  apply Finset.image_congr
  intro step _
  exact pointwiseDualWalkCrossingEdge_eq_dualWalkCrossingEdge
    faceBoundary allFaces hunique walk step

end

end GoertzelV24DualPathPointwiseTransversal

end Mettapedia.GraphTheory.FourColor
