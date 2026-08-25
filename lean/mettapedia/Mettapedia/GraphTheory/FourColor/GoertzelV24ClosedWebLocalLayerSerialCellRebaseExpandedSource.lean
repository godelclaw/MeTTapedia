import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellPastOverlap
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellRebaseExpandedCoreState
import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceDeletionComponentFactorForget

/-!
# The literal successor carrier as a partial expanded-interface map

The deletion-safe rebase state uses the predecessor's literal carrier plus
four semantic roles.  The successor carrier is again bounded by twenty-one,
but a padded successor coordinate may be inactive and a literal successor
edge may be supplied either by a role or by a predecessor coordinate.

This file constructs the exact partial map into the unpadded expanded
interface.  Role names take precedence, matching the colour recurrence.  Lean
proves that every returned source denotes the literal target edge, and that a
target edge with no source is isolated in each successor tracked graph.  The
latter uses the already-proved source Cell overlap theorem; it is not an
assumption about inactive padding.

Together with `GoertzelV24InterfaceDeletionComponentFactorForget`, these are
the graph-level hypotheses needed to reindex the deletion-stable core through
forgotten expanded coordinates.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellRebaseExpandedSource

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseTrackedColorParametric
open GoertzelV24ClosedWebLocalLayerSerialCellPastOverlap
open GoertzelV24ClosedWebLocalLayerSerialCellRebaseCarrierTransport
open GoertzelV24ClosedWebLocalLayerSerialCellRebaseExpandedInterface
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedTransitionCarrier
open GoertzelV24CorridorProfile
open GoertzelV24DeletionSensitivePortResidualFactorContraction
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24InterfaceDeletionComponentFactorForget
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance cellRebaseExpandedSourceOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- Map one literal successor-carrier coordinate into the actual-cardinality
expanded predecessor interface. -/
noncomputable def sourceLocalLayerSerialCellRebaseExpandedSourceAt
    (graphData : Data G)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    let current := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData
      caps coloring web corridor hunique offset
    let target := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData
      caps coloring web corridor hunique
        (sourceLocalLayerNextOffset offset hnext)
    Fin target.card →
      Option (SourceLocalLayerSerialCellRebaseExpandedInterface current) := by
  classical
  dsimp only
  intro targetSlot
  let current := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData
    caps coloring web corridor hunique offset
  let target := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
    coloring web corridor hunique (sourceLocalLayerNextOffset offset hnext)
  let targetEdge : {edge // edge ∈ target} :=
    (carrierCoordinate target).symm targetSlot
  let roleAt := sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset
    hnext
  if hrole : ∃ role, roleAt role = targetEdge.1 then
    exact some (.inr (Classical.choose hrole))
  else if hcurrent : targetEdge.1 ∈ current then
    exact some (.inl (carrierCoordinate current ⟨targetEdge.1, hcurrent⟩))
  else
    exact none

/-- Any returned expanded coordinate denotes exactly the literal successor
edge from which it was selected. -/
theorem sourceLocalLayerSerialCellRebaseExpandedSourceAt_edge_eq
    (graphData : Data G)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (targetSlot : Fin
      (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique (sourceLocalLayerNextOffset offset hnext)).card)
    (source : SourceLocalLayerSerialCellRebaseExpandedInterface
      (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique offset))
    (hsource : sourceLocalLayerSerialCellRebaseExpandedSourceAt graphData caps
      coloring web corridor hunique offset hnext targetSlot = some source) :
    expandedInterfaceEdgeAt
        (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
          coloring web corridor hunique offset)
        (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext)
        source =
      (((carrierCoordinate
        (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
          coloring web corridor hunique
            (sourceLocalLayerNextOffset offset hnext))).symm targetSlot).1) := by
  classical
  unfold sourceLocalLayerSerialCellRebaseExpandedSourceAt at hsource
  dsimp only at hsource
  simp only [id_eq] at hsource
  split at hsource <;> rename_i hrole
  · simp only [Option.some.injEq] at hsource
    subst source
    simpa [expandedInterfaceEdgeAt] using (Classical.choose_spec hrole)
  · split at hsource <;> rename_i hcurrent
    · simp only [Option.some.injEq] at hsource
      subst source
      change
        (((carrierCoordinate
          (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
            coloring web corridor hunique offset)).symm
          ((carrierCoordinate
            (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
              coloring web corridor hunique offset))
            ⟨_, hcurrent⟩)).1) = _
      rw [Equiv.symm_apply_apply]
    · cases hsource

/-- Failure of the partial source map means exactly that the literal target
edge is neither a named rebase role nor a predecessor-carrier edge. -/
theorem sourceLocalLayerSerialCellRebaseExpandedSourceAt_eq_none_iff
    (graphData : Data G)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (targetSlot : Fin
      (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique (sourceLocalLayerNextOffset offset hnext)).card) :
    sourceLocalLayerSerialCellRebaseExpandedSourceAt graphData caps coloring web
        corridor hunique offset hnext targetSlot = none ↔
      (¬ ∃ role : SourceLocalLayerBoundaryRebaseRole,
        sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext
            role =
          (((carrierCoordinate
            (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
              coloring web corridor hunique
                (sourceLocalLayerNextOffset offset hnext))).symm targetSlot).1)) ∧
      (((carrierCoordinate
          (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
            coloring web corridor hunique
              (sourceLocalLayerNextOffset offset hnext))).symm targetSlot).1) ∉
        sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
          web corridor hunique offset := by
  classical
  unfold sourceLocalLayerSerialCellRebaseExpandedSourceAt
  dsimp only
  simp only [id_eq]
  split <;> rename_i hrole
  · constructor
    · intro hfalse
      cases hfalse
    · rintro ⟨hnotRole, _⟩
      exact (hnotRole hrole).elim
  · split <;> rename_i hcurrent
    · constructor
      · intro hfalse
        cases hfalse
      · rintro ⟨_, hnotCurrent⟩
        exact (hnotCurrent hcurrent).elim
    · exact ⟨fun _ => ⟨hrole, hcurrent⟩, fun _ => rfl⟩

/-- An unmapped literal successor coordinate is isolated in every successor
tracked graph.  This is the load-bearing source discharge for partial finite
reindexing: the conclusion follows from clean-corridor past overlap, not from
padding convention or a new hypothesis. -/
theorem sourceLocalLayerSerialCellRebaseExpandedSourceAt_none_not_mem_support
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (pair : TrackedColorPair)
    (targetSlot : Fin
      (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique (sourceLocalLayerNextOffset offset hnext)).card)
    (hnone : sourceLocalLayerSerialCellRebaseExpandedSourceAt graphData caps
      coloring web corridor hunique offset hnext targetSlot = none) :
    (((carrierCoordinate
        (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
          coloring web corridor hunique
            (sourceLocalLayerNextOffset offset hnext))).symm targetSlot).1) ∉
      (successorTrackedGraphForColorAt corridor hunique offset hnext color pair
        ).support := by
  let targetCarrier :=
    sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring web
      corridor hunique (sourceLocalLayerNextOffset offset hnext)
  let targetEdge : {edge // edge ∈ targetCarrier} :=
    (carrierCoordinate targetCarrier).symm targetSlot
  have hnoneCases :=
    (sourceLocalLayerSerialCellRebaseExpandedSourceAt_eq_none_iff graphData caps
      coloring web corridor hunique offset hnext targetSlot).1 hnone
  intro hsupport
  rcases (SimpleGraph.mem_support _).1 hsupport with ⟨other, hadj⟩
  have hregion : targetEdge.1 ∈
      sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext) := by
    exact hadj.2.1
  have hpast := sourceLocalLayerSerialCellRebase_pastCellOverlap graphData
    minimal caps coloring web corridor hunique offset hnext
  have hlookahead :=
    sourceLocalLayerSerialCellRebaseCarrier_oldPrefixLookahead_of_pastCellOverlap
      graphData caps coloring web corridor hunique offset hnext hpast
  have hcovered :=
    sourceLocalLayerSerialCellRebaseCarrier_covered_of_oldPrefixLookahead
      graphData caps coloring web corridor hunique offset hnext hlookahead
      targetEdge hregion
  rcases hcovered with hswitch | hcurrent
  · apply hnoneCases.1
    rcases (mem_sourceLocalLayerBoundaryRebaseSwitchAt_iff corridor hunique
      offset hnext targetEdge.1).1 hswitch with ⟨role, hrole⟩
    exact ⟨role, hrole⟩
  · exact hnoneCases.2 hcurrent

/-- The generic forgetting mask now specializes without hypotheses: on the
literal source corridor, masking the mapped expanded coordinates leaves
exactly the successor tracked graph exterior to its literal target carrier.
Forgotten expanded coordinates remain available to connect exterior
components, while unmapped target coordinates are proved isolated above. -/
theorem sourceLocalLayerSerialCellRebase_partialMask_eq_successorExterior
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (pair : TrackedColorPair) :
    let current := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData
      caps coloring web corridor hunique offset
    let target := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData
      caps coloring web corridor hunique
        (sourceLocalLayerNextOffset offset hnext)
    let roleAt := sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset
      hnext
    let expandedVertex := expandedInterfaceEdgeAt current roleAt
    let targetVertex := fun slot : Fin target.card =>
      ((carrierCoordinate target).symm slot).1
    let sourceAt := sourceLocalLayerSerialCellRebaseExpandedSourceAt graphData
      caps coloring web corridor hunique offset hnext
    let graph := successorTrackedGraphForColorAt corridor hunique offset hnext
      color pair
    restrictedByMask graph expandedVertex
        (partialRetainedCoordinateMask sourceAt) =
      exteriorGraph graph targetVertex := by
  dsimp only
  apply restrictedBy_partialRetainedCoordinateMask_eq_exteriorGraph
  · intro targetSlot source hsource
    exact sourceLocalLayerSerialCellRebaseExpandedSourceAt_edge_eq graphData caps
      coloring web corridor hunique offset hnext targetSlot source hsource
  · intro targetSlot hnone
    exact
      sourceLocalLayerSerialCellRebaseExpandedSourceAt_none_not_mem_support
        graphData minimal caps coloring web corridor hunique offset hnext color
        pair targetSlot hnone

/-- The actual-cardinality target carrier has no padded aliases. -/
theorem sourceLocalLayerSerialCellRebase_targetVertex_injective
    (graphData : Data G)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    Function.Injective (fun slot : Fin
      (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique (sourceLocalLayerNextOffset offset hnext)).card =>
      (((carrierCoordinate
        (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
          coloring web corridor hunique
            (sourceLocalLayerNextOffset offset hnext))).symm slot).1)) := by
  intro left right heq
  apply (carrierCoordinate
    (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
      web corridor hunique
        (sourceLocalLayerNextOffset offset hnext))).symm.injective
  exact Subtype.ext heq

/-- The elementary equality row of the partial reindexing is exact on the
literal successor carrier. -/
theorem sourceLocalLayerSerialCellRebase_partialReindexedVertexEq_iff
    (graphData : Data G)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (left right : Fin
      (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique (sourceLocalLayerNextOffset offset hnext)).card) :
    partialReindexedVertexEq left right = true ↔
      (((carrierCoordinate
        (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
          coloring web corridor hunique
            (sourceLocalLayerNextOffset offset hnext))).symm left).1) =
      (((carrierCoordinate
        (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
          coloring web corridor hunique
            (sourceLocalLayerNextOffset offset hnext))).symm right).1) := by
  exact partialReindexedVertexEq_eq_true_iff _
    (sourceLocalLayerSerialCellRebase_targetVertex_injective graphData caps
      coloring web corridor hunique offset hnext) left right

/-- The direct-adjacency row pulled through the partial expanded source map is
also exact for every successor tracked graph. -/
theorem sourceLocalLayerSerialCellRebase_partialReindexedDirectAdj_iff
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (pair : TrackedColorPair)
    (left right : Fin
      (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique (sourceLocalLayerNextOffset offset hnext)).card) :
    let current := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData
      caps coloring web corridor hunique offset
    let target := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData
      caps coloring web corridor hunique
        (sourceLocalLayerNextOffset offset hnext)
    let roleAt := sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset
      hnext
    let expandedVertex := expandedInterfaceEdgeAt current roleAt
    let targetVertex := fun slot : Fin target.card =>
      ((carrierCoordinate target).symm slot).1
    let sourceAt := sourceLocalLayerSerialCellRebaseExpandedSourceAt graphData
      caps coloring web corridor hunique offset hnext
    let graph := successorTrackedGraphForColorAt corridor hunique offset hnext
      color pair
    partialReindexedDirectAdj
        (exactInterfaceExteriorCode graph expandedVertex) sourceAt left right =
          true ↔
      graph.Adj (targetVertex left) (targetVertex right) := by
  dsimp only
  apply partialReindexedDirectAdj_exact_iff
  · intro targetSlot source hsource
    exact sourceLocalLayerSerialCellRebaseExpandedSourceAt_edge_eq graphData caps
      coloring web corridor hunique offset hnext targetSlot source hsource
  · intro targetSlot hnone
    exact
      sourceLocalLayerSerialCellRebaseExpandedSourceAt_none_not_mem_support
        graphData minimal caps coloring web corridor hunique offset hnext color
        pair targetSlot hnone

end

end GoertzelV24ClosedWebLocalLayerSerialCellRebaseExpandedSource

end Mettapedia.GraphTheory.FourColor
