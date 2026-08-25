import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailPointedEdgeFaceAllocation

/-!
# L1: consume the opposite endpoint-triangle allocation

The pointed square comparison can allocate the incoming and outgoing rail
edges to different endpoint triangles of the two-vertex bond.  This is not a
dead branch.  The two triangles share the facial-dual edge crossing the
internal bond, so one of that edge's two faces is different from the removed
collision face.  It gives a literal bypass of length at most two from the
predecessor to the successor.

This module constructs that bypass directly.  It does not yet prove that the
two pointed source crossings lie in the endpoint-triangle packet, splice the
bypass into the retained rail, prove separation from the companion rail,
iterate the rolling transition, attach end caps, or close Fable flag L1.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24DualPathPointedOccurrence
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FiniteDeletionCyclicCut
open GoertzelV24SelectedDualCycleSeparator

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
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

/-- A concrete replacement for one strict pointed occurrence.  Its support
avoids the removed face, and it uses at most two facial-dual edges. -/
structure InteriorOccurrence.TwoHopBypass
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring}
    {start finish current : SelectedFace web}
    {rail : (SelectedDualGraph web).Walk start finish}
    (occurrence : InteriorOccurrence (current := current) rail) where
  walk : (SelectedDualGraph web).Walk occurrence.predecessor occurrence.successor
  length_le_two : walk.length ≤ 2
  current_not_mem_support : current ∉ walk.support

section OppositeEndpoint

variable
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring}

/-- The internal bond edge places the same two literal faces in both endpoint
triangles.  This uses the selected crossing itself, rather than a global
uniqueness assertion for arbitrary shared face edges. -/
theorem MiddleReplacementShortDualCycle.SquareBondRealization.commonFaces_of_endpointTriangles
    {face : SelectedFace web}
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    {bond : MiddleReplacementShortDualCycle.SquareBondRealization cycle component}
    (firstTriangle secondTriangle : bond.EndpointSelectedTriangle)
    (hinter : firstTriangle.selectedCycle.crossingEdges ∩
        secondTriangle.selectedCycle.crossingEdges = {bond.internalEdge}) :
    ∃ first second : SelectedFace web,
      first ≠ second ∧
        first ∈ firstTriangle.selectedCycle.walk.support ∧
        second ∈ firstTriangle.selectedCycle.walk.support ∧
        first ∈ secondTriangle.selectedCycle.walk.support ∧
        second ∈ secondTriangle.selectedCycle.walk.support := by
  have hinternalInter : bond.internalEdge ∈
      firstTriangle.selectedCycle.crossingEdges ∩
        secondTriangle.selectedCycle.crossingEdges := by
    rw [hinter]
    simp
  have hinternalFirst := (Finset.mem_inter.mp hinternalInter).1
  have hinternalSecond := (Finset.mem_inter.mp hinternalInter).2
  rcases (firstTriangle.selectedCycle.mem_crossingEdges_iff
      bond.internalEdge).1 hinternalFirst with ⟨step, hstep⟩
  let first := firstTriangle.selectedCycle.walk.getVert step.val
  let second := firstTriangle.selectedCycle.walk.getVert (step.val + 1)
  have hadj : (SelectedDualGraph web).Adj first second :=
    firstTriangle.selectedCycle.walk.adj_getVert_succ step.isLt
  have hshared := firstTriangle.selectedCycle.crossing_mem_shared step
  have hsharedInternal : bond.internalEdge ∈ sharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)) first.1 second.1 := by
    simpa [first, second, hstep] using hshared
  let receipt : SelectedAdjacentTerminalEdgeCrossingReceipt
      (web := web) s(first, second) := {
    first := first
    second := second
    edge_eq := rfl
    faces_ne := hadj.ne
    crossing := bond.internalEdge
    crossing_mem_shared := hsharedInternal
  }
  have hedgeSecond : s(first, second) ∈
      secondTriangle.selectedCycle.walk.edges :=
    receipt.edge_mem_endpointTriangle secondTriangle hinternalSecond
  have hfirstFirst : first ∈ firstTriangle.selectedCycle.walk.support := by
    exact firstTriangle.selectedCycle.walk.getVert_mem_support step.val
  have hsecondFirst : second ∈ firstTriangle.selectedCycle.walk.support := by
    exact firstTriangle.selectedCycle.walk.getVert_mem_support (step.val + 1)
  have hfirstSecond : first ∈ secondTriangle.selectedCycle.walk.support :=
    secondTriangle.selectedCycle.walk.mem_support_of_mem_edges hedgeSecond
      (by simp)
  have hsecondSecond : second ∈ secondTriangle.selectedCycle.walk.support :=
    secondTriangle.selectedCycle.walk.mem_support_of_mem_edges hedgeSecond
      (by simp)
  exact ⟨first, second, hadj.ne, hfirstFirst, hsecondFirst,
    hfirstSecond, hsecondSecond⟩

/-- **L1 opposite-endpoint consumer.**  When the two pointed rail edges are
allocated to opposite endpoint triangles, their common internal-bond edge
supplies an explicit collision-free replacement walk of length at most two.
The symmetric allocation is handled without choosing an orientation. -/
theorem InteriorOccurrence.exists_twoHopBypass_of_opposite_endpointTriangles
    {start finish current : SelectedFace web}
    {rail : (SelectedDualGraph web).Walk start finish}
    (occurrence : InteriorOccurrence (current := current) rail)
    (hpath : rail.IsPath)
    {face : SelectedFace web}
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    {bond : MiddleReplacementShortDualCycle.SquareBondRealization cycle component}
    (firstTriangle secondTriangle : bond.EndpointSelectedTriangle)
    (hinter : firstTriangle.selectedCycle.crossingEdges ∩
        secondTriangle.selectedCycle.crossingEdges = {bond.internalEdge})
    (hopposite :
      (occurrence.incomingEdge ∈ firstTriangle.selectedCycle.walk.edges ∧
          occurrence.outgoingEdge ∈ secondTriangle.selectedCycle.walk.edges) ∨
        (occurrence.incomingEdge ∈ secondTriangle.selectedCycle.walk.edges ∧
          occurrence.outgoingEdge ∈ firstTriangle.selectedCycle.walk.edges)) :
    Nonempty (InteriorOccurrence.TwoHopBypass occurrence) := by
  rcases bond.commonFaces_of_endpointTriangles firstTriangle secondTriangle
      hinter with
    ⟨first, second, hfirstSecond, hfirstFirst, hsecondFirst,
      hfirstSecondSupport, hsecondSecondSupport⟩
  let bridgeFace : SelectedFace web := if first = current then second else first
  have hbridgeNe : bridgeFace ≠ current := by
    dsimp [bridgeFace]
    split_ifs with hfirst
    · intro hsecond
      exact hfirstSecond (hfirst.trans hsecond.symm)
    · exact hfirst
  have hbridgeFirst : bridgeFace ∈
      firstTriangle.selectedCycle.walk.support := by
    dsimp [bridgeFace]
    split_ifs <;> assumption
  have hbridgeSecond : bridgeFace ∈
      secondTriangle.selectedCycle.walk.support := by
    dsimp [bridgeFace]
    split_ifs <;> assumption
  have build : ∀
      (incomingTriangle outgoingTriangle : bond.EndpointSelectedTriangle),
      bridgeFace ∈ incomingTriangle.selectedCycle.walk.support →
      bridgeFace ∈ outgoingTriangle.selectedCycle.walk.support →
      occurrence.incomingEdge ∈ incomingTriangle.selectedCycle.walk.edges →
      occurrence.outgoingEdge ∈ outgoingTriangle.selectedCycle.walk.edges →
      Nonempty (InteriorOccurrence.TwoHopBypass occurrence) := by
    intro incomingTriangle outgoingTriangle hbridgeIncoming hbridgeOutgoing
      hincoming houtgoing
    have hpredecessor : occurrence.predecessor ∈
        incomingTriangle.selectedCycle.walk.support :=
      incomingTriangle.selectedCycle.walk.mem_support_of_mem_edges hincoming
        (by simp [InteriorOccurrence.incomingEdge])
    have hsuccessor : occurrence.successor ∈
        outgoingTriangle.selectedCycle.walk.support :=
      outgoingTriangle.selectedCycle.walk.mem_support_of_mem_edges houtgoing
        (by simp [InteriorOccurrence.outgoingEdge])
    by_cases hpredecessorBridge : occurrence.predecessor = bridgeFace
    · have hbridgeSuccessor : (SelectedDualGraph web).Adj
          bridgeFace occurrence.successor :=
        outgoingTriangle.adj_of_mem_support_of_ne hbridgeOutgoing hsuccessor
          (by
            intro h
            apply occurrence.predecessor_ne_successor hpath
            exact hpredecessorBridge.trans h)
      have hpredecessorSuccessor : (SelectedDualGraph web).Adj
          occurrence.predecessor occurrence.successor := by
        simpa [hpredecessorBridge] using hbridgeSuccessor
      exact ⟨{
        walk := .cons hpredecessorSuccessor .nil
        length_le_two := by simp
        current_not_mem_support := by
          simp [occurrence.predecessor_ne_current.symm,
            occurrence.current_ne_successor]
      }⟩
    · by_cases hsuccessorBridge : occurrence.successor = bridgeFace
      · have hpredecessorBridgeAdj : (SelectedDualGraph web).Adj
            occurrence.predecessor bridgeFace :=
          incomingTriangle.adj_of_mem_support_of_ne hpredecessor hbridgeIncoming
            hpredecessorBridge
        have hpredecessorSuccessor : (SelectedDualGraph web).Adj
            occurrence.predecessor occurrence.successor := by
          simpa [hsuccessorBridge] using hpredecessorBridgeAdj
        exact ⟨{
          walk := .cons hpredecessorSuccessor .nil
          length_le_two := by simp
          current_not_mem_support := by
            simp [occurrence.predecessor_ne_current.symm,
              occurrence.current_ne_successor]
        }⟩
      · have hpredecessorBridgeAdj : (SelectedDualGraph web).Adj
            occurrence.predecessor bridgeFace :=
          incomingTriangle.adj_of_mem_support_of_ne hpredecessor hbridgeIncoming
            hpredecessorBridge
        have hbridgeSuccessor : (SelectedDualGraph web).Adj
            bridgeFace occurrence.successor :=
          outgoingTriangle.adj_of_mem_support_of_ne hbridgeOutgoing hsuccessor
            (Ne.symm hsuccessorBridge)
        exact ⟨{
          walk := .cons hpredecessorBridgeAdj (.cons hbridgeSuccessor .nil)
          length_le_two := by simp
          current_not_mem_support := by
            simp [occurrence.predecessor_ne_current.symm,
              occurrence.current_ne_successor, hbridgeNe.symm]
        }⟩
  rcases hopposite with hopposite | hopposite
  · exact build firstTriangle secondTriangle hbridgeFirst hbridgeSecond
      hopposite.1 hopposite.2
  · exact build secondTriangle firstTriangle hbridgeSecond hbridgeFirst
      hopposite.1 hopposite.2

end OppositeEndpoint

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
