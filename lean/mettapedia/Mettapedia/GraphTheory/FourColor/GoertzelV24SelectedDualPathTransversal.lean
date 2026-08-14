import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscut

/-!
# Selected crossings of a simple facial-dual transversal

A simple transversal in the source is a simple facial-dual path together with
the actual primal edge crossed at each dual step.  It need not require that
every adjacent pair of ambient faces have a globally unique shared edge: a
source construction supplies the particular edge that its transversal crosses.

This file records that weaker, source-faithful datum.  The local
at-most-two-face-incidence law is enough to show that its crossings are
injective along a simple dual path.  It deliberately does not construct a
crosscut or a separated pair of crosscuts.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24SelectedDualPathTransversal

open GoertzelV24AnnularCrosscut
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open SimpleGraph

variable {F E : Type*} [Fintype F] [DecidableEq F]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- A simple facial-dual transversal with its literally selected primal
crossing at every dual step.  The selected edge is certified locally to lie
on both consecutive faces and in the interior support. -/
structure SelectedDualPathTransversal
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (start finish : AmbientFace allFaces) where
  crosscut : SimpleDualCrosscut faceBoundary allFaces start finish
  crossingEdge : Fin crosscut.walk.length → E
  crossing_mem_shared : ∀ step,
    crossingEdge step ∈ sharedInteriorEdges faceBoundary allFaces
      (crosscut.walk.getVert step.val).1
      (crosscut.walk.getVert (step.val + 1)).1

namespace SelectedDualPathTransversal

/-- The finite support of the actual primal edges crossed by a selected
transversal. -/
def crossingEdges
    {faceBoundary : F → Finset E} {allFaces : Finset F}
    {start finish : AmbientFace allFaces}
    (transversal : SelectedDualPathTransversal faceBoundary allFaces start finish) :
    Finset E :=
  Finset.univ.image transversal.crossingEdge

@[simp]
theorem mem_crossingEdges_iff
    {faceBoundary : F → Finset E} {allFaces : Finset F}
    {start finish : AmbientFace allFaces}
    (transversal : SelectedDualPathTransversal faceBoundary allFaces start finish)
    (edge : E) :
    edge ∈ transversal.crossingEdges ↔
      ∃ step : Fin transversal.crosscut.walk.length,
        transversal.crossingEdge step = edge := by
  simp [crossingEdges]

/-- Every selected crossing is an ambient interior edge. -/
theorem crossingEdge_mem_interiorEdgeSupport
    {faceBoundary : F → Finset E} {allFaces : Finset F}
    {start finish : AmbientFace allFaces}
    (transversal : SelectedDualPathTransversal faceBoundary allFaces start finish)
    (step : Fin transversal.crosscut.walk.length) :
    transversal.crossingEdge step ∈ interiorEdgeSupport faceBoundary allFaces := by
  exact (mem_sharedInteriorEdges_iff faceBoundary allFaces).1
    (transversal.crossing_mem_shared step) |>.1

/-- A selected crossing lies on the face before its dual step. -/
theorem crossingEdge_mem_leftFace
    {faceBoundary : F → Finset E} {allFaces : Finset F}
    {start finish : AmbientFace allFaces}
    (transversal : SelectedDualPathTransversal faceBoundary allFaces start finish)
    (step : Fin transversal.crosscut.walk.length) :
    transversal.crossingEdge step ∈
      faceBoundary (transversal.crosscut.walk.getVert step.val).1 := by
  exact (mem_sharedInteriorEdges_iff faceBoundary allFaces).1
    (transversal.crossing_mem_shared step) |>.2.1

/-- A selected crossing lies on the face after its dual step. -/
theorem crossingEdge_mem_rightFace
    {faceBoundary : F → Finset E} {allFaces : Finset F}
    {start finish : AmbientFace allFaces}
    (transversal : SelectedDualPathTransversal faceBoundary allFaces start finish)
    (step : Fin transversal.crosscut.walk.length) :
    transversal.crossingEdge step ∈
      faceBoundary (transversal.crosscut.walk.getVert (step.val + 1)).1 := by
  exact (mem_sharedInteriorEdges_iff faceBoundary allFaces).1
    (transversal.crossing_mem_shared step) |>.2.2

/-- A simple facial-dual path cannot select the same primal edge at two
different steps.  Only its vertex-injectivity and the local at-most-two
face-incidence law are used; no global unique-shared-edge hypothesis enters. -/
theorem crossingEdge_injective
    {faceBoundary : F → Finset E} {allFaces : Finset F}
    (hall : ∀ edge, totalIncidenceCount faceBoundary allFaces edge ≤ 2)
    {start finish : AmbientFace allFaces}
    (transversal : SelectedDualPathTransversal faceBoundary allFaces start finish) :
    Function.Injective transversal.crossingEdge := by
  intro first second hedges
  let firstLeft := transversal.crosscut.walk.getVert first.val
  let firstRight := transversal.crosscut.walk.getVert (first.val + 1)
  let secondLeft := transversal.crosscut.walk.getVert second.val
  let secondRight := transversal.crosscut.walk.getVert (second.val + 1)
  have hfirstAdj := transversal.crosscut.walk.adj_getVert_succ first.isLt
  have hfirstFaces : firstLeft.1 ≠ firstRight.1 := by
    intro hfaces
    exact hfirstAdj.ne (Subtype.ext hfaces)
  have hfirstLeft : transversal.crossingEdge first ∈ faceBoundary firstLeft.1 :=
    transversal.crossingEdge_mem_leftFace first
  have hfirstRight : transversal.crossingEdge first ∈ faceBoundary firstRight.1 :=
    transversal.crossingEdge_mem_rightFace first
  have hsecondLeft : transversal.crossingEdge first ∈ faceBoundary secondLeft.1 := by
    rw [hedges]
    exact transversal.crossingEdge_mem_leftFace second
  have hsecondRight : transversal.crossingEdge first ∈ faceBoundary secondRight.1 := by
    rw [hedges]
    exact transversal.crossingEdge_mem_rightFace second
  have hsecondLeftCases :=
    eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
      faceBoundary allFaces hall firstLeft.2 firstRight.2 secondLeft.2
      hfirstFaces hfirstLeft hfirstRight hsecondLeft
  rcases hsecondLeftCases with hsecondFirst | hsecondNext
  · apply Fin.ext
    exact transversal.crosscut.isPath.getVert_injOn
      (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega)
      (Subtype.ext hsecondFirst.symm)
  · have hsecondVal : second.val = first.val + 1 :=
      transversal.crosscut.isPath.getVert_injOn
        (by simp only [Set.mem_setOf_eq]; omega)
        (by simp only [Set.mem_setOf_eq]; omega)
        (Subtype.ext hsecondNext)
    have hsecondRightCases :=
      eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
        faceBoundary allFaces hall firstLeft.2 firstRight.2 secondRight.2
        hfirstFaces hfirstLeft hfirstRight hsecondRight
    rcases hsecondRightCases with hrightFirst | hrightNext
    · have hvalue : second.val + 1 = first.val :=
        transversal.crosscut.isPath.getVert_injOn
          (by simp only [Set.mem_setOf_eq]; omega)
          (by simp only [Set.mem_setOf_eq]; omega)
          (Subtype.ext hrightFirst)
      omega
    · have hvalue : second.val + 1 = first.val + 1 :=
        transversal.crosscut.isPath.getVert_injOn
          (by simp only [Set.mem_setOf_eq]; omega)
          (by simp only [Set.mem_setOf_eq]; omega)
          (Subtype.ext hrightNext)
      omega

/-- The selected crossing support has exactly one edge per dual step. -/
theorem card_crossingEdges_eq_length
    {faceBoundary : F → Finset E} {allFaces : Finset F}
    (hall : ∀ edge, totalIncidenceCount faceBoundary allFaces edge ≤ 2)
    {start finish : AmbientFace allFaces}
    (transversal : SelectedDualPathTransversal faceBoundary allFaces start finish) :
    transversal.crossingEdges.card = transversal.crosscut.walk.length := by
  rw [crossingEdges,
    Finset.card_image_of_injective _ (transversal.crossingEdge_injective hall),
    Finset.card_univ, Fintype.card_fin]

/-- The older unique-shared-edge presentation supplies a selected crossing at
each step.  This is an adapter, not a requirement of the selected API. -/
def ofPairwiseUnique
    {faceBoundary : F → Finset E} {allFaces : Finset F}
    {start finish : AmbientFace allFaces}
    (crosscut : SimpleDualCrosscut faceBoundary allFaces start finish)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces) :
    SelectedDualPathTransversal faceBoundary allFaces start finish where
  crosscut := crosscut
  crossingEdge := crosscut.crossingEdge hunique
  crossing_mem_shared step :=
    sharedInteriorEdgeOfAdjOfPairwiseUnique_mem_sharedInteriorEdges
      faceBoundary allFaces hunique
      (crosscut.walk.adj_getVert_succ step.isLt)

end SelectedDualPathTransversal

end

end GoertzelV24SelectedDualPathTransversal

end Mettapedia.GraphTheory.FourColor
