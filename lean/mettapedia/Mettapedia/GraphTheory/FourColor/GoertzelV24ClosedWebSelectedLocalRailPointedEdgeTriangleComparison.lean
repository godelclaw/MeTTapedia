import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementBoundedSuffixSharedCollisionFirstWindowPointedEdgeReceipt
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementSquareEndpointTriangles

/-!
# L1: compare pointed rail-edge receipts with square endpoint triangles

The complete adjacent terminal classifier gives every surviving rail edge a
literal selected primal crossing.  A square-bond endpoint triangle also
carries one selected primal crossing at every dual step.  This module compares
the two presentations through that named primal edge.

No global uniqueness of a shared edge between two faces is assumed.  Instead,
the rotation system's incidence-at-most-two theorem shows that one primal edge
shared by the receipted face pair and selected by the endpoint triangle forces
the same unoriented dual edge.  Consequently, if the incoming and outgoing
receipted crossings at a pointed collision both meet one endpoint centre, the
triangle supplies the literal predecessor-to-successor bypass.

This does not yet prove that the two source crossings meet the same endpoint
centre.  Discharging that finite placement comparison, iterating the rolling
transition, and attaching the two end caps remain open; Fable flag L1 is not
closed here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24DualPathPointedOccurrence
open GoertzelV24DualPathTransversal
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FiniteDeletionCyclicCut
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24SelectedDualCycleSeparator

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

private abbrev SelectedFace
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) :=
  AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))

private abbrev SelectedDualGraph
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) :=
  interiorDualGraph (orbitFaceBoundary web.annular.RS)
    (Finset.univ : Finset (OrbitFace web.annular.RS))

/-- A uniform form of the three adjacent terminal receipt alternatives: the
dual edge is displayed by its two distinct incident faces, and one concrete
primal edge is shared by those faces. -/
structure SelectedAdjacentTerminalEdgeCrossingReceipt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring}
    (edge : Sym2 (SelectedFace web)) where
  first : SelectedFace web
  second : SelectedFace web
  edge_eq : edge = s(first, second)
  faces_ne : first ≠ second
  crossing : G.edgeSet
  crossing_mem_shared : crossing ∈ sharedInteriorEdges
    (orbitFaceBoundary web.annular.RS)
    (Finset.univ : Finset (OrbitFace web.annular.RS)) first.1 second.1

section ReceiptNormalization

variable
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {leftPlacement : SelectedInternalHexRungPlacement corridor rungs leftInterior}
    {rightPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior leftInterior hnext)}

/-- Proof-relevant source provenance for a normalized adjacent-terminal
crossing.  The three constructors deliberately remain distinct: a surviving
dual edge can come from the old selected placement, the successor placement,
or an explicit old-centre connector.  In every case the packet retains the
named primal corner met by the selected crossing.

This is the finite coordinate datum needed by the square-bond comparison.  It
does not assert that the corner is either endpoint of a later square bond. -/
inductive SelectedAdjacentTerminalEdgeCrossingOrigin
    (edge : Sym2 (SelectedFace web)) : Type
  | oldForward
      (left right :
        {position // position ∈ selectedPlacementSidePositions leftPlacement})
      (successor : right.1.val ≡ left.1.val + 1 [MOD 6])
      (step : SelectedPlacementSideForwardEdgeReceipt
        leftPlacement left right edge)
  | successorForward
      (left right :
        {position // position ∈ selectedPlacementSidePositions rightPlacement})
      (successor : right.1.val ≡ left.1.val + 1 [MOD 6])
      (step : SelectedPlacementSideForwardEdgeReceipt
        rightPlacement left right edge)
  | oldCenter
      (position :
        {position // position ∈ selectedPlacementSidePositions leftPlacement})
      (step : SelectedPlacementCenterSideEdgeReceipt
        leftPlacement position edge)

/-- Normalize a proof-relevant source origin to the common facial-dual
crossing packet consumed by the endpoint-triangle comparison. -/
def SelectedAdjacentTerminalEdgeCrossingOrigin.toCrossingReceipt
    {edge : Sym2 (SelectedFace web)}
    (origin : SelectedAdjacentTerminalEdgeCrossingOrigin
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement) edge) :
    SelectedAdjacentTerminalEdgeCrossingReceipt edge := by
  cases origin with
  | oldForward left right _ step =>
      exact {
        first := selectedPlacementSideFace leftPlacement left
        second := selectedPlacementSideFace leftPlacement right
        edge_eq := step.edge_eq
        faces_ne := step.faces_ne
        crossing := selectedPlacementSideForwardThirdEdge leftPlacement left
        crossing_mem_shared := step.thirdEdge_mem_shared
      }
  | successorForward left right _ step =>
      exact {
        first := selectedPlacementSideFace rightPlacement left
        second := selectedPlacementSideFace rightPlacement right
        edge_eq := step.edge_eq
        faces_ne := step.faces_ne
        crossing := selectedPlacementSideForwardThirdEdge rightPlacement left
        crossing_mem_shared := step.thirdEdge_mem_shared
      }
  | oldCenter position step =>
      let centerFace :=
        corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          leftInterior.center
      have hadj : (SelectedDualGraph web).Adj centerFace
          (selectedPlacementSideFace leftPlacement position) :=
        selectedPlacementSideFace_adjacent_center
          (corridor := corridor) leftPlacement position
      exact {
        first := centerFace
        second := selectedPlacementSideFace leftPlacement position
        edge_eq := step.edge_eq
        faces_ne := hadj.ne
        crossing := web.annular.RS.edgeOf
          (faceCycleDart web.annular.RS leftPlacement.root position.1)
        crossing_mem_shared := step.sideEdge_mem_shared
      }

/-- The exact named primal corner retained by a source crossing origin. -/
def SelectedAdjacentTerminalEdgeCrossingOrigin.corner
    {edge : Sym2 (SelectedFace web)}
    (origin : SelectedAdjacentTerminalEdgeCrossingOrigin
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement) edge) : V :=
  match origin with
  | .oldForward left _ _ _ =>
      selectedPlacementSideForwardCorner leftPlacement left
  | .successorForward left _ _ _ =>
      selectedPlacementSideForwardCorner rightPlacement left
  | .oldCenter position _ =>
      selectedPlacementSideForwardCorner leftPlacement position

/-- The source corner is genuinely an endpoint of the normalized primal
crossing.  This is the strongest uniform endpoint fact supported by all three
receipt constructors; identifying it with a square-bond endpoint is the
remaining finite placement comparison. -/
theorem SelectedAdjacentTerminalEdgeCrossingOrigin.corner_mem_crossing
    {edge : Sym2 (SelectedFace web)}
    (origin : SelectedAdjacentTerminalEdgeCrossingOrigin
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement) edge) :
    origin.corner ∈ origin.toCrossingReceipt.crossing.1 := by
  cases origin with
  | oldForward left right successor step =>
      let dart := selectedPlacementSideForwardDart leftPlacement left
      have hvertex : web.annular.RS.vertOf
            (web.annular.RS.rho (web.annular.RS.phi dart)) =
          web.annular.RS.vertOf (web.annular.RS.alpha dart) :=
        (web.annular.RS.vert_rho (web.annular.RS.phi dart)).trans
          (web.annular.RS.vert_phi_eq_vert_alpha dart)
      have hmem : web.annular.RS.vertOf
            (web.annular.RS.rho (web.annular.RS.phi dart)) ∈
          (web.annular.RS.edgeOf
            (web.annular.RS.rho (web.annular.RS.phi dart))).1 := by
        change (web.annular.RS.rho (web.annular.RS.phi dart)).fst ∈
          s((web.annular.RS.rho (web.annular.RS.phi dart)).fst,
            (web.annular.RS.rho (web.annular.RS.phi dart)).snd)
        simp
      change web.annular.RS.vertOf (web.annular.RS.alpha dart) ∈
        (web.annular.RS.edgeOf
          (web.annular.RS.rho (web.annular.RS.phi dart))).1
      rw [← hvertex]
      exact hmem
  | successorForward left right successor step =>
      let dart := selectedPlacementSideForwardDart rightPlacement left
      have hvertex : web.annular.RS.vertOf
            (web.annular.RS.rho (web.annular.RS.phi dart)) =
          web.annular.RS.vertOf (web.annular.RS.alpha dart) :=
        (web.annular.RS.vert_rho (web.annular.RS.phi dart)).trans
          (web.annular.RS.vert_phi_eq_vert_alpha dart)
      have hmem : web.annular.RS.vertOf
            (web.annular.RS.rho (web.annular.RS.phi dart)) ∈
          (web.annular.RS.edgeOf
            (web.annular.RS.rho (web.annular.RS.phi dart))).1 := by
        change (web.annular.RS.rho (web.annular.RS.phi dart)).fst ∈
          s((web.annular.RS.rho (web.annular.RS.phi dart)).fst,
            (web.annular.RS.rho (web.annular.RS.phi dart)).snd)
        simp
      change web.annular.RS.vertOf (web.annular.RS.alpha dart) ∈
        (web.annular.RS.edgeOf
          (web.annular.RS.rho (web.annular.RS.phi dart))).1
      rw [← hvertex]
      exact hmem
  | oldCenter position step =>
      let dart := selectedPlacementSideForwardDart leftPlacement position
      have hmem : web.annular.RS.vertOf (web.annular.RS.alpha dart) ∈
          (web.annular.RS.edgeOf (web.annular.RS.alpha dart)).1 := by
        change (web.annular.RS.alpha dart).fst ∈
          s((web.annular.RS.alpha dart).fst,
            (web.annular.RS.alpha dart).snd)
        simp
      change web.annular.RS.vertOf (web.annular.RS.alpha dart) ∈
        (web.annular.RS.edgeOf dart).1
      simpa only [web.annular.RS.edge_alpha] using hmem

/-- Every adjacent terminal receipt retains one of the three exact source
origins above.  Unlike `toCrossingReceipt`, this theorem does not erase which
placement and which local corner produced the crossing. -/
theorem SelectedAdjacentTerminalEdgeReceipt.toCrossingOrigin
    {edge : Sym2 (SelectedFace web)}
    (receipt : SelectedAdjacentTerminalEdgeReceipt
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
      edge) :
    Nonempty (SelectedAdjacentTerminalEdgeCrossingOrigin
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement) edge) := by
  rcases receipt with oldForward | successorOrCenter
  · rcases oldForward with ⟨left, right, hsuccessor, step⟩
    exact ⟨.oldForward left right hsuccessor step⟩
  · rcases successorOrCenter with successorForward | center
    · rcases successorForward with ⟨left, right, hsuccessor, step⟩
      exact ⟨.successorForward left right hsuccessor step⟩
    · rcases center with ⟨position, step⟩
      exact ⟨.oldCenter position step⟩

/-- Each old-step, successor-step, or old-centre receipt exposes one common
primal-crossing representation. -/
theorem SelectedAdjacentTerminalEdgeReceipt.toCrossingReceipt
    {edge : Sym2 (SelectedFace web)}
    (receipt : SelectedAdjacentTerminalEdgeReceipt
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
      edge) :
    Nonempty (SelectedAdjacentTerminalEdgeCrossingReceipt edge) := by
  rcases receipt.toCrossingOrigin with ⟨origin⟩
  exact ⟨origin.toCrossingReceipt⟩

end ReceiptNormalization

section TriangleComparison

variable
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring}

/-- A receipted primal crossing remains shared after identifying its
unoriented facial-dual edge with a particular walk step.  This is only
incidence transport; it does not choose the step or assert uniqueness of a
primal edge shared by the two faces. -/
theorem SelectedAdjacentTerminalEdgeCrossingReceipt.crossing_mem_shared_at
    {edge : Sym2 (SelectedFace web)}
    (receipt : SelectedAdjacentTerminalEdgeCrossingReceipt edge)
    {start finish : SelectedFace web}
    (walk : (SelectedDualGraph web).Walk start finish)
    (step : Fin walk.length)
    (hedge : edge = coreDualWalkGraphEdge
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)) walk step) :
    receipt.crossing ∈ sharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      (walk.getVert step.val).1 (walk.getVert (step.val + 1)).1 := by
  apply MiddleReplacementShortDualCycle.mem_sharedInteriorEdges_of_sym2_eq
    web.annular.RS
  · simpa [coreDualWalkGraphEdge] using hedge.symm.trans receipt.edge_eq
  · exact receipt.crossing_mem_shared

/-- A primal edge selected by both an arbitrary receipted dual edge and an
endpoint triangle determines the same unoriented dual edge.  Incidence at
most two, rather than global shared-edge uniqueness, is the load-bearing
fact. -/
theorem SelectedAdjacentTerminalEdgeCrossingReceipt.edge_eq_coreDualWalkGraphEdge
    {edge : Sym2 (SelectedFace web)}
    (receipt : SelectedAdjacentTerminalEdgeCrossingReceipt edge)
    {face : SelectedFace web}
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    {bond : MiddleReplacementShortDualCycle.SquareBondRealization cycle component}
    (triangle : bond.EndpointSelectedTriangle)
    (step : Fin triangle.selectedCycle.walk.length)
    (hcrossing : triangle.selectedCycle.crossingEdge step = receipt.crossing) :
    edge = coreDualWalkGraphEdge
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      triangle.selectedCycle.walk step := by
  let stepLeft := triangle.selectedCycle.walk.getVert step.val
  let stepRight := triangle.selectedCycle.walk.getVert (step.val + 1)
  have hstepAdj := triangle.selectedCycle.walk.adj_getVert_succ step.isLt
  have hstepFacesNe : stepLeft.1 ≠ stepRight.1 := by
    intro hfaces
    exact hstepAdj.ne (Subtype.ext hfaces)
  have hreceipt := (mem_sharedInteriorEdges_iff
    (orbitFaceBoundary web.annular.RS)
    (Finset.univ : Finset (OrbitFace web.annular.RS))).1
      receipt.crossing_mem_shared
  have hstepLeft : receipt.crossing ∈
      orbitFaceBoundary web.annular.RS stepLeft.1 := by
    rw [← hcrossing]
    exact triangle.selectedCycle.crossingEdge_mem_leftFace step
  have hstepRight : receipt.crossing ∈
      orbitFaceBoundary web.annular.RS stepRight.1 := by
    rw [← hcrossing]
    exact triangle.selectedCycle.crossingEdge_mem_rightFace step
  have hreceiptFacesNe : receipt.first.1 ≠ receipt.second.1 := by
    intro hfaces
    exact receipt.faces_ne (Subtype.ext hfaces)
  have hleft :=
    eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      (orbitFace_incidence_le_two web.annular.RS)
      receipt.first.2 receipt.second.2 stepLeft.2 hreceiptFacesNe
      hreceipt.2.1 hreceipt.2.2 hstepLeft
  have hright :=
    eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      (orbitFace_incidence_le_two web.annular.RS)
      receipt.first.2 receipt.second.2 stepRight.2 hreceiptFacesNe
      hreceipt.2.1 hreceipt.2.2 hstepRight
  rw [receipt.edge_eq]
  change s(receipt.first, receipt.second) = s(stepLeft, stepRight)
  rcases hleft with hleft | hleft <;>
    rcases hright with hright | hright
  · exact False.elim (hstepFacesNe (hleft.trans hright.symm))
  · apply Sym2.eq_iff.mpr
    exact Or.inl ⟨Subtype.ext hleft.symm, Subtype.ext hright.symm⟩
  · apply Sym2.eq_iff.mpr
    exact Or.inr ⟨Subtype.ext hright.symm, Subtype.ext hleft.symm⟩
  · exact False.elim (hstepFacesNe (hleft.trans hright.symm))

/-- If the receipt's selected primal crossing occurs on the endpoint
triangle, then the receipted dual edge is literally one of its three walk
edges. -/
theorem SelectedAdjacentTerminalEdgeCrossingReceipt.edge_mem_endpointTriangle
    {edge : Sym2 (SelectedFace web)}
    (receipt : SelectedAdjacentTerminalEdgeCrossingReceipt edge)
    {face : SelectedFace web}
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    {bond : MiddleReplacementShortDualCycle.SquareBondRealization cycle component}
    (triangle : bond.EndpointSelectedTriangle)
    (hcrossing : receipt.crossing ∈ triangle.selectedCycle.crossingEdges) :
    edge ∈ triangle.selectedCycle.walk.edges := by
  rcases (triangle.selectedCycle.mem_crossingEdges_iff receipt.crossing).1
      hcrossing with ⟨step, hstep⟩
  have hedge := receipt.edge_eq_coreDualWalkGraphEdge triangle step hstep
  let edgeStep : Fin triangle.selectedCycle.walk.edges.length :=
    Fin.cast triangle.selectedCycle.walk.length_edges.symm step
  have hget := edges_get_coreDualWalkGraphEdge
    (orbitFaceBoundary web.annular.RS)
    (Finset.univ : Finset (OrbitFace web.annular.RS))
    triangle.selectedCycle.walk step
  rw [hedge, ← hget]
  exact List.get_mem triangle.selectedCycle.walk.edges edgeStep

/-- Incidence with the endpoint centre is the convenient local criterion for
membership in that endpoint triangle's selected crossing set. -/
theorem SelectedAdjacentTerminalEdgeCrossingReceipt.edge_mem_endpointTriangle_of_meets_center
    {edge : Sym2 (SelectedFace web)}
    (receipt : SelectedAdjacentTerminalEdgeCrossingReceipt edge)
    {face : SelectedFace web}
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    {bond : MiddleReplacementShortDualCycle.SquareBondRealization cycle component}
    (triangle : bond.EndpointSelectedTriangle)
    (hcenter : triangle.center ∈ receipt.crossing.1) :
    edge ∈ triangle.selectedCycle.walk.edges := by
  apply receipt.edge_mem_endpointTriangle triangle
  rw [triangle.crossingEdges_eq_incidentEdgeFinset]
  simpa [incidentEdgeFinset] using hcenter

/-- A receipted crossing on the selected square boundary belongs to at least
one of the two endpoint triangles.  This is the exact allocation statement
supported by the two-vertex bond: it deliberately does not assert that two
different rail crossings choose the same endpoint. -/
theorem SelectedAdjacentTerminalEdgeCrossingReceipt.edge_mem_first_or_second_endpointTriangle
    {edge : Sym2 (SelectedFace web)}
    (receipt : SelectedAdjacentTerminalEdgeCrossingReceipt edge)
    {face : SelectedFace web}
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    {bond : MiddleReplacementShortDualCycle.SquareBondRealization cycle component}
    (firstTriangle secondTriangle : bond.EndpointSelectedTriangle)
    (hfirstCenter : firstTriangle.center = bond.first)
    (hsecondCenter : secondTriangle.center = bond.second)
    (hcrossing : receipt.crossing ∈ cycle.selectedCycle.crossingEdges) :
    edge ∈ firstTriangle.selectedCycle.walk.edges ∨
      edge ∈ secondTriangle.selectedCycle.walk.edges := by
  rcases bond.covers_crossingEdges receipt.crossing hcrossing with
    hfirst | hsecond
  · exact .inl (receipt.edge_mem_endpointTriangle_of_meets_center
      firstTriangle (by simpa [hfirstCenter] using hfirst))
  · exact .inr (receipt.edge_mem_endpointTriangle_of_meets_center
      secondTriangle (by simpa [hsecondCenter] using hsecond))

/-- Once both pointed incident crossings meet the same square endpoint, the
endpoint triangle gives the one-edge predecessor-to-successor bypass required
by the rolling rail repair. -/
theorem InteriorOccurrence.endpointTriangle_bypass_of_crossingReceipts
    {start finish current : SelectedFace web}
    {walk : (SelectedDualGraph web).Walk start finish}
    (occurrence : InteriorOccurrence (current := current) walk)
    (hpath : walk.IsPath)
    (incomingReceipt :
      SelectedAdjacentTerminalEdgeCrossingReceipt occurrence.incomingEdge)
    (outgoingReceipt :
      SelectedAdjacentTerminalEdgeCrossingReceipt occurrence.outgoingEdge)
    {face : SelectedFace web}
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    {bond : MiddleReplacementShortDualCycle.SquareBondRealization cycle component}
    (triangle : bond.EndpointSelectedTriangle)
    (hincomingCenter : triangle.center ∈ incomingReceipt.crossing.1)
    (houtgoingCenter : triangle.center ∈ outgoingReceipt.crossing.1) :
    (SelectedDualGraph web).Adj occurrence.predecessor occurrence.successor := by
  have hincoming := incomingReceipt
    |>.edge_mem_endpointTriangle_of_meets_center triangle hincomingCenter
  have houtgoing := outgoingReceipt
    |>.edge_mem_endpointTriangle_of_meets_center triangle houtgoingCenter
  have hpredecessor : occurrence.predecessor ∈
      triangle.selectedCycle.walk.support :=
    triangle.selectedCycle.walk.mem_support_of_mem_edges hincoming
      (by simp [InteriorOccurrence.incomingEdge])
  have hsuccessor : occurrence.successor ∈
      triangle.selectedCycle.walk.support :=
    triangle.selectedCycle.walk.mem_support_of_mem_edges houtgoing
      (by simp [InteriorOccurrence.outgoingEdge])
  exact triangle.adj_of_mem_support_of_ne hpredecessor hsuccessor
    (occurrence.predecessor_ne_successor hpath)

/-- **L1 square-endpoint allocation.**  If both literal pointed rail
crossings occur on the selected four-edge square boundary, then either one
endpoint triangle already supplies the predecessor-to-successor bypass, or
the two rail edges are allocated to opposite endpoint triangles.  The second
alternative is retained explicitly; no same-endpoint claim is assumed. -/
theorem InteriorOccurrence.endpointTriangle_bypass_or_opposite_of_crossingReceipts
    {start finish current : SelectedFace web}
    {walk : (SelectedDualGraph web).Walk start finish}
    (occurrence : InteriorOccurrence (current := current) walk)
    (hpath : walk.IsPath)
    (incomingReceipt :
      SelectedAdjacentTerminalEdgeCrossingReceipt occurrence.incomingEdge)
    (outgoingReceipt :
      SelectedAdjacentTerminalEdgeCrossingReceipt occurrence.outgoingEdge)
    {face : SelectedFace web}
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    {bond : MiddleReplacementShortDualCycle.SquareBondRealization cycle component}
    (firstTriangle secondTriangle : bond.EndpointSelectedTriangle)
    (hfirstCenter : firstTriangle.center = bond.first)
    (hsecondCenter : secondTriangle.center = bond.second)
    (hincomingCrossing :
      incomingReceipt.crossing ∈ cycle.selectedCycle.crossingEdges)
    (houtgoingCrossing :
      outgoingReceipt.crossing ∈ cycle.selectedCycle.crossingEdges) :
    (SelectedDualGraph web).Adj occurrence.predecessor occurrence.successor ∨
      ((occurrence.incomingEdge ∈ firstTriangle.selectedCycle.walk.edges ∧
          occurrence.outgoingEdge ∈ secondTriangle.selectedCycle.walk.edges) ∨
        (occurrence.incomingEdge ∈ secondTriangle.selectedCycle.walk.edges ∧
          occurrence.outgoingEdge ∈ firstTriangle.selectedCycle.walk.edges)) := by
  have hincoming := incomingReceipt
    |>.edge_mem_first_or_second_endpointTriangle firstTriangle secondTriangle
      hfirstCenter hsecondCenter hincomingCrossing
  have houtgoing := outgoingReceipt
    |>.edge_mem_first_or_second_endpointTriangle firstTriangle secondTriangle
      hfirstCenter hsecondCenter houtgoingCrossing
  rcases hincoming with hincomingFirst | hincomingSecond <;>
    rcases houtgoing with houtgoingFirst | houtgoingSecond
  · left
    have hpredecessor : occurrence.predecessor ∈
        firstTriangle.selectedCycle.walk.support :=
      firstTriangle.selectedCycle.walk.mem_support_of_mem_edges hincomingFirst
        (by simp [InteriorOccurrence.incomingEdge])
    have hsuccessor : occurrence.successor ∈
        firstTriangle.selectedCycle.walk.support :=
      firstTriangle.selectedCycle.walk.mem_support_of_mem_edges houtgoingFirst
        (by simp [InteriorOccurrence.outgoingEdge])
    exact firstTriangle.adj_of_mem_support_of_ne hpredecessor hsuccessor
      (occurrence.predecessor_ne_successor hpath)
  · exact .inr (.inl ⟨hincomingFirst, houtgoingSecond⟩)
  · exact .inr (.inr ⟨hincomingSecond, houtgoingFirst⟩)
  · left
    have hpredecessor : occurrence.predecessor ∈
        secondTriangle.selectedCycle.walk.support :=
      secondTriangle.selectedCycle.walk.mem_support_of_mem_edges hincomingSecond
        (by simp [InteriorOccurrence.incomingEdge])
    have hsuccessor : occurrence.successor ∈
        secondTriangle.selectedCycle.walk.support :=
      secondTriangle.selectedCycle.walk.mem_support_of_mem_edges houtgoingSecond
        (by simp [InteriorOccurrence.outgoingEdge])
    exact secondTriangle.adj_of_mem_support_of_ne hpredecessor hsuccessor
      (occurrence.predecessor_ne_successor hpath)

end TriangleComparison

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
