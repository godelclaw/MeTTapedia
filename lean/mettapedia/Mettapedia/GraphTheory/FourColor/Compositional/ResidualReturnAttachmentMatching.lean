import Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnSeparatorExitSide

/-!
# Matching role of residual-return attachments

An ambient residual return runs in the graph left after deleting the reference
pairing before and after an alternating exchange.  At a strict internal vertex
of such a return, its two path edges are therefore not reference-pairing edges.
Cubicity identifies the remaining attachment edge with the reference pairing.

This identification removes one apparent branch in the separator-exit
analysis.  The alternating carrier is closed under the reference pairing, so
an internal attachment cannot return to that carrier.  Hence every external
attachment really leaves the displayed separator and carries the exact
face-side information already stored by `AttachmentExitSideReceipt`.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace ResidualReturnAttachmentMatching

open CubicPathAttachment
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrderedMeshResidualSiteMatching
open GoertzelV24ResidualReturnArc
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24ResidualReturnPairing
open GoertzelV24ResidualReturnSectorNoncrossing
open MatchingParity
open ResidualReturnPathAttachment
open ResidualReturnSeparatorExitSide
open SimpleGraph

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

private theorem orderedChordAmbientPath_edges_eq_orderedReturnPath
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (chord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site)) :
    (orderedChordAmbientPath hG sigma hSigma site chord).edges =
      (orderedReturnPath hG sigma hSigma site chord.left).edges := by
  simp only [orderedChordAmbientPath, SimpleGraph.Walk.edges_copy,
    orderedAmbientReturnPath, SimpleGraph.Walk.edges_mapLe_eq_edges]

/-- At an internal position of a residual return, the preceding path edge is
an edge of the common residual graph. -/
private theorem commonResidualGraph_adj_previousVertex
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (chord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (position : AmbientReturnInternalPosition hG sigma hSigma site chord) :
    (commonResidualGraph G sigma site).Adj position.vertex
      position.previousVertex := by
  let ambientPath := orderedChordAmbientPath hG sigma hSigma site chord
  let sourcePath := orderedReturnPath hG sigma hSigma site chord.left
  have hindex : position.index - 1 + 1 = position.index := by
    have := position.index_ne_zero
    omega
  have hsubgraph : ambientPath.toSubgraph.Adj position.vertex
      position.previousVertex := by
    have hadj := ambientPath.toSubgraph_adj_getVert
      (i := position.index - 1)
      (lt_of_le_of_lt (Nat.sub_le _ _) position.index_lt_length)
    simpa only [ambientPath, InternalPosition.vertex,
      InternalPosition.previousVertex, hindex] using hadj.symm
  have hambientEdge : s(position.vertex, position.previousVertex) ∈
      ambientPath.edges := by
    rw [← ambientPath.mem_edges_toSubgraph, SimpleGraph.Subgraph.mem_edgeSet]
    exact hsubgraph
  have hsourceEdge : s(position.vertex, position.previousVertex) ∈
      sourcePath.edges := by
    rw [← orderedChordAmbientPath_edges_eq_orderedReturnPath
      hG sigma hSigma site chord]
    exact hambientEdge
  exact (commonResidualGraph G sigma site).mem_edgeSet.mp
    (sourcePath.edges_subset_edgeSet hsourceEdge)

/-- At an internal position of a residual return, the following path edge is
an edge of the common residual graph. -/
private theorem commonResidualGraph_adj_nextVertex
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (chord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (position : AmbientReturnInternalPosition hG sigma hSigma site chord) :
    (commonResidualGraph G sigma site).Adj position.vertex
      position.nextVertex := by
  let ambientPath := orderedChordAmbientPath hG sigma hSigma site chord
  let sourcePath := orderedReturnPath hG sigma hSigma site chord.left
  have hsubgraph : ambientPath.toSubgraph.Adj position.vertex
      position.nextVertex := by
    have hadj := ambientPath.toSubgraph_adj_getVert
      (i := position.index) position.index_lt_length
    simpa only [ambientPath, InternalPosition.vertex,
      InternalPosition.nextVertex] using hadj
  have hambientEdge : s(position.vertex, position.nextVertex) ∈
      ambientPath.edges := by
    rw [← ambientPath.mem_edges_toSubgraph, SimpleGraph.Subgraph.mem_edgeSet]
    exact hsubgraph
  have hsourceEdge : s(position.vertex, position.nextVertex) ∈
      sourcePath.edges := by
    rw [← orderedChordAmbientPath_edges_eq_orderedReturnPath
      hG sigma hSigma site chord]
    exact hambientEdge
  exact (commonResidualGraph G sigma site).mem_edgeSet.mp
    (sourcePath.edges_subset_edgeSet hsourceEdge)

/-- The unique third edge at an internal common-residual return vertex is the
reference-pairing edge. -/
theorem ambientReturnAttachmentNeighbor_eq_partner
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (chord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (position : AmbientReturnInternalPosition hG sigma hSigma site chord) :
    ambientReturnAttachmentNeighbor hG sigma hSigma site chord position =
      sigma.partner position.vertex := by
  symm
  let hpath := orderedChordAmbientPath_isPath hG sigma hSigma site chord
  apply eq_attachmentNeighbor_of_mem hpath
    (regularOfDegreeThree_of_cubicIncidentTriples hG) position
  refine ⟨hSigma position.vertex, ?_⟩
  change sigma.partner
      ((orderedChordAmbientPath hG sigma hSigma site chord).getVert
        position.index) ∉
    (orderedChordAmbientPath hG sigma hSigma site chord).toSubgraph.neighborSet
      ((orderedChordAmbientPath hG sigma hSigma site chord).getVert
        position.index)
  rw [hpath.neighborSet_toSubgraph_internal position.index_ne_zero
    position.index_lt_length]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  push Not
  constructor
  · exact ((commonResidualGraph_adj sigma site).1
      (commonResidualGraph_adj_previousVertex
        hG sigma hSigma site chord position)).2.1
  · exact ((commonResidualGraph_adj sigma site).1
      (commonResidualGraph_adj_nextVertex
        hG sigma hSigma site chord position)).2.1

/-- A strict internal residual-return attachment cannot return to the
alternating carrier. -/
theorem ambientReturnAttachmentNeighbor_not_mem_carrier
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (chord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (position : AmbientReturnInternalPosition hG sigma hSigma site chord) :
    ambientReturnAttachmentNeighbor hG sigma hSigma site chord position ∉
      site.carrier := by
  intro hattachmentCarrier
  have hpartner := ambientReturnAttachmentNeighbor_eq_partner
    hG sigma hSigma site chord position
  have hpositionCarrier := site.sigma_closed
    (ambientReturnAttachmentNeighbor hG sigma hSigma site chord position)
    hattachmentCarrier
  rw [hpartner, sigma.partner_partner] at hpositionCarrier
  have hpath : position.vertex ∈
      (orderedChordAmbientPath hG sigma hSigma site chord).support := by
    exact SimpleGraph.Walk.getVert_mem_support _ position.index
  rcases
      eq_left_or_eq_right_of_mem_orderedChordAmbientPath_support_of_mem_carrier
        hG sigma hSigma site chord hpath hpositionCarrier with
    hleft | hright
  · have hleft' :
        (orderedChordAmbientPath hG sigma hSigma site chord).getVert
            position.index =
          (orderedChordAmbientPath hG sigma hSigma site chord).getVert 0 := by
      simpa only [InternalPosition.vertex,
        SimpleGraph.Walk.getVert_zero] using hleft
    have hindex :=
      (orderedChordAmbientPath_isPath hG sigma hSigma site chord).getVert_injOn
        (Nat.le_of_lt position.index_lt_length) (Nat.zero_le _) hleft'
    exact position.index_ne_zero hindex
  · have hright' :
        (orderedChordAmbientPath hG sigma hSigma site chord).getVert
            position.index =
          (orderedChordAmbientPath hG sigma hSigma site chord).getVert
            (orderedChordAmbientPath hG sigma hSigma site chord).length := by
      simpa only [InternalPosition.vertex,
        SimpleGraph.Walk.getVert_length] using hright
    have hindex :=
      (orderedChordAmbientPath_isPath hG sigma hSigma site chord).getVert_injOn
        (by
          simp only [Set.mem_setOf_eq]
          exact Nat.le_of_lt position.index_lt_length)
        (by
          simp only [Set.mem_setOf_eq]
          exact le_rfl) hright'
    exact (Nat.ne_of_lt position.index_lt_length) hindex

/-- Consequently an external attachment always leaves the complete displayed
separator; the former carrier-return alternative is impossible. -/
theorem ambientReturnExternalAttachment_leavesSeparator
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (chord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (position : AmbientReturnInternalPosition hG sigma hSigma site chord)
    (hexternal : IsExternalAttachment
      (orderedChordAmbientPath_isPath hG sigma hSigma site chord)
      (regularOfDegreeThree_of_cubicIncidentTriples hG) position) :
    ambientReturnAttachmentNeighbor hG sigma hSigma site chord position ∉
      (orderedReturnSeparator hG sigma hSigma site chord).support := by
  rcases ambientReturnExternalAttachment_reachesCarrier_or_leavesSeparator
      hG sigma hSigma site chord position hexternal with hcarrier | hexit
  · exact False.elim
      (ambientReturnAttachmentNeighbor_not_mem_carrier
        hG sigma hSigma site chord position hcarrier)
  · exact hexit

/-- The outcome of every separator-exit receipt is therefore its exact
face-side branch. -/
theorem AttachmentExitSideReceipt.faceSide
    {rotation : SimpleGraphDartRotation.Data G}
    {hG : HasCubicIncidentEdgeTriples G}
    {sigma : Pairing V} {hSigma : sigma.SupportedBy G}
    {first second : V}
    {site : ProperAlternatingSiteWitness G sigma first second}
    {chord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site)}
    (receipt : AttachmentExitSideReceipt rotation hG sigma hSigma site chord) :
    (ambientReturnAttachmentTurn rotation hG sigma hSigma site chord
            receipt.position = .backwardToAttachment ∧
        ∀ selected : F2,
          receipt.cut.filledCycleSide rotation
              (orderedReturnSeparator hG sigma hSigma site chord) selected
              (ambientReturnAttachmentNeighbor
                hG sigma hSigma site chord receipt.position) ↔
            receipt.cut.label (dartOrbitFace rotation.toRotationSystem
              (CubicPathRotation.forwardDart receipt.position)) = selected) ∨
      (ambientReturnAttachmentTurn rotation hG sigma hSigma site chord
            receipt.position = .forwardToAttachment ∧
        ∀ selected : F2,
          receipt.cut.filledCycleSide rotation
              (orderedReturnSeparator hG sigma hSigma site chord) selected
              (ambientReturnAttachmentNeighbor
                hG sigma hSigma site chord receipt.position) ↔
            receipt.cut.label (dartOrbitFace rotation.toRotationSystem
              (CubicPathRotation.backwardDart receipt.position)) = selected) := by
  rcases receipt.outcome with hcarrier | hfaceSide
  · exact False.elim
      (ambientReturnAttachmentNeighbor_not_mem_carrier
        hG sigma hSigma site chord receipt.position hcarrier)
  · exact hfaceSide

end

end ResidualReturnAttachmentMatching

end Mettapedia.GraphTheory.FourColor.Compositional
