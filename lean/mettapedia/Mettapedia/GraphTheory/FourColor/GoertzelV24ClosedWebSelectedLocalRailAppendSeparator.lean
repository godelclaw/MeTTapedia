import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailAppendObstruction
import Mettapedia.GraphTheory.FourColor.GoertzelV24SelectedDualCycleSeparator

/-!
# The selected adjacent-append triangle is a three-edge separator

The fail-closed adjacent rail append exposes a literal facial-dual triangle
when its exact common-neighbour classification fails.  This module applies
the selected-crossing separator theorem to that triangle.  Its three dual
steps select three distinct primal edges, and deleting those edges disconnects
the graph underlying the framed annular cellulation.

This is the graph-level separator promised by the right branch of the append
alternative.  It does not yet classify either component of the deletion,
prove that a component avoids the two stub boundaries, promote the separator
to a cyclic three-edge cut, or reroute the rails.  Those distinctions are the
remaining source-local geometry.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebBoundaryData.AnnularBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FramedAnnularExcess
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24SelectedDualCycleSeparator

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance.SelectedLocalLayerFormation

variable
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}

namespace SeparatedSelectedSourceLocalRailSuccessor.AdjacentDualTriangle

variable
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {leftPlacement : SelectedInternalHexRungPlacement corridor rungs leftInterior}
    {rightPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior leftInterior hnext)}
    {successor : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement}

/-- The first step of the literal three-step obstruction walk, from the left
corridor centre to its successor centre. -/
abbrev firstStep (triangle : AdjacentDualTriangle successor) :
    Fin triangle.walk.length :=
  ⟨0, by rw [triangle.walk_length]; decide⟩

/-- The final step of the obstruction walk, from its third common face back
to the left corridor centre. -/
abbrev lastStep (triangle : AdjacentDualTriangle successor) :
    Fin triangle.walk.length :=
  ⟨2, by rw [triangle.walk_length]; decide⟩

/-- The obstruction triangle equipped with one actual shared primal edge at
each of its three dual steps.  Its first crossing is definitionally the
selected outgoing rung between the two consecutive corridor centres; only the
other two crossings are choice-selected. -/
noncomputable def selectedCycle
    (triangle : AdjacentDualTriangle successor) :
    SelectedDualCycle web.annular.RS
      ((corridor.toCleanOrbitHexCorridorSkeleton
        |>.toOrbitHexCorridorSkeleton).faceAt leftInterior.center) :=
  SelectedDualCycle.ofWalkWithCrossingAt web.annular.RS triangle.walk
    triangle.walk_isCycle triangle.firstStep
    (rungs.edge leftInterior.outgoing) (by
      simpa [AdjacentDualTriangle.walk, nextCorridorInterior] using
        rungs.mem_shared leftInterior.outgoing)

@[simp] theorem selectedCycle_walk
    (triangle : AdjacentDualTriangle successor) :
    triangle.selectedCycle.walk = triangle.walk := rfl

@[simp] theorem walk_getVert_lastStep
    (triangle : AdjacentDualTriangle successor) :
    triangle.walk.getVert triangle.lastStep.val = triangle.third := rfl

@[simp] theorem walk_getVert_two
    (triangle : AdjacentDualTriangle successor) :
    triangle.walk.getVert 2 = triangle.third := rfl

@[simp] theorem walk_getVert_lastStep_succ
    (triangle : AdjacentDualTriangle successor) :
    triangle.walk.getVert (triangle.lastStep.val + 1) =
      ((corridor.toCleanOrbitHexCorridorSkeleton
        |>.toOrbitHexCorridorSkeleton).faceAt leftInterior.center) := rfl

/-- The distinguished first selected crossing retains the literal source rung
rather than an arbitrary shared-edge choice. -/
@[simp] theorem selectedCycle_crossingEdge_zero
    (triangle : AdjacentDualTriangle successor) :
    triangle.selectedCycle.crossingEdge triangle.firstStep =
      rungs.edge leftInterior.outgoing := by
  simp [selectedCycle]

/-- The obstruction triangle crosses exactly three distinct primal edges. -/
theorem crossingEdges_card_eq_three
    (triangle : AdjacentDualTriangle successor) :
    triangle.selectedCycle.crossingEdges.card = 3 := by
  rw [triangle.selectedCycle.card_crossingEdges_eq_length
    (orbitFace_incidence_le_two web.annular.RS)]
  exact triangle.walk_length

/-- The three selected separator edges avoid the designated inner-hole
boundary.  This follows from the boundary-clean corridor invariant for all
three dual faces, not from a global face-uniqueness assumption. -/
theorem crossingEdges_disjoint_innerHoleBoundary
    (triangle : AdjacentDualTriangle successor) :
    Disjoint triangle.selectedCycle.crossingEdges
      (orbitFaceBoundary web.annular.RS
        web.annular.cellulation.innerHole) := by
  exact triangle.selectedCycle.crossingEdges_disjoint_faceBoundary_of_support
    web.annular.cellulation.interiorFaces triangle.walk_support_internal
    web.annular.cellulation.innerHole
    (by
      simp [FramedAnnularCellulation.interiorFaces,
        FramedAnnularCellulation.holeFaces])

/-- The same selected separator avoids the designated outer-hole boundary. -/
theorem crossingEdges_disjoint_outerHoleBoundary
    (triangle : AdjacentDualTriangle successor) :
    Disjoint triangle.selectedCycle.crossingEdges
      (orbitFaceBoundary web.annular.RS
        web.annular.cellulation.outerHole) := by
  exact triangle.selectedCycle.crossingEdges_disjoint_faceBoundary_of_support
    web.annular.cellulation.interiorFaces triangle.walk_support_internal
    web.annular.cellulation.outerHole
    (by
      simp [FramedAnnularCellulation.interiorFaces,
        FramedAnnularCellulation.holeFaces])

/-- Deleting the three selected primal crossings of the obstruction triangle
disconnects the graph underlying the literal framed annulus. -/
theorem not_connected_deleteEdges_primalCut
    (triangle : AdjacentDualTriangle successor) :
    ¬ (G.deleteEdges triangle.selectedCycle.primalCut).Connected := by
  exact triangle.selectedCycle.not_connected_deleteEdges_primalCut
    web.annular.cellulation.rotation
    web.annular.cellulation.fullOrbitFaceInteriorDual_connected
    web.annular.cellulation.connected
    web.annular.cellulation.euler

end SeparatedSelectedSourceLocalRailSuccessor.AdjacentDualTriangle

end Instance.SelectedLocalLayerFormation

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
