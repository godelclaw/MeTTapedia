import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellUniformInterface
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellRebaseExpandedInterface
import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceDeletionComponentFactorMaskUpdate
import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceDeletionComponentFactorTotal

/-!
# Exact tracked recurrence on the uniform Cell--rebase interface

The cumulative tracked graph immediately before a boundary rebase contains
arbitrarily much prefix history, but the preceding module proves that one
literal Cell update and its following rebase interact with a carrier of at
most forty-nine primal edges.  This file performs the complete tracked update
on that fixed carrier.

The finite recurrence has three literal operations:

1. extract the mask-independent exterior-component code of the cumulative
   pre-rebase graph on the uniform carrier;
2. delete every coordinate naming one of the four switch edges; and
3. Boolean-OR the exact adjacency table of the local successor residue.

Lean proves rowwise that the resulting code is the exact exterior-component
code of the successor tracked graph.  Its total finite closure therefore
recovers successor reachability between every pair of uniform coordinates.
The result is independent of the corridor length; it does not yet assemble
the facial rows or enumerate a reachable closure.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellUniformTrackedRecurrence

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseDeletionSensitiveTrackedCore
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseTrackedColorParametric
open GoertzelV24ClosedWebLocalLayerSerialCellRebaseExpandedInterface
open GoertzelV24CorridorProfile
open GoertzelV24DeletionSensitivePortResidualFactorContraction
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24InterfaceDeletionComponentFactorMaskUpdate
open GoertzelV24InterfaceDeletionComponentFactorTotal
open GoertzelV24InterfaceDeletionComponentFactorUpdate
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance cellUniformTrackedRecurrenceEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance cellUniformTrackedRecurrenceOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- The canonical ambient edge represented by one coordinate of the uniform
tracked interaction carrier. -/
noncomputable def sourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt
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
    Fin (sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData
      caps coloring web corridor hunique offset hnext).card →
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet :=
  fun slot =>
    ((carrierCoordinate
      (sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData
        caps coloring web corridor hunique offset hnext)).symm slot).1

/-- Uniform coordinates name distinct ambient edges. -/
theorem sourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt_injective
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
    Function.Injective
      (sourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt graphData caps
        coloring web corridor hunique offset hnext) := by
  intro left right heq
  apply (carrierCoordinate
    (sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
      coloring web corridor hunique offset hnext)).symm.injective
  apply Subtype.ext
  exact heq

/-- The four switch edges lie in the uniform carrier, because it contains the
whole edge-adjacency-closed rebase collar. -/
theorem sourceLocalLayerBoundaryRebaseSwitch_subset_uniformTrackedCarrier
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
    sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique offset hnext ⊆
      sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
        coloring web corridor hunique offset hnext := by
  intro edge hedge
  apply Finset.mem_union_right
  apply (web.annular.RS.mem_edgeAdjacencyClosedCarrier_iff _ edge).2
  exact Or.inl hedge

/-- The Boolean deletion mask on the uniform coordinates selects exactly the
literal four-edge switch. -/
noncomputable def sourceLocalLayerSerialCellRebaseUniformSwitchMaskAt
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
    Fin (sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData
      caps coloring web corridor hunique offset hnext).card → Bool :=
  fun slot => decide
    (sourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt graphData caps
      coloring web corridor hunique offset hnext slot ∈
        sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique offset hnext)

/-- The coordinate mask and the source's semantic-role presentation remove
the same ambient vertices. -/
theorem removedBy_uniformSwitchMask_iff
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
    (edge : caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet) :
    RemovedByInterfaceMask
        (sourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt graphData caps
          coloring web corridor hunique offset hnext)
        (sourceLocalLayerSerialCellRebaseUniformSwitchMaskAt graphData caps
          coloring web corridor hunique offset hnext) edge ↔
      edge ∈ sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique offset
        hnext := by
  let carrier :=
    sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
      coloring web corridor hunique offset hnext
  let edgeAt :=
    sourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt graphData caps coloring
      web corridor hunique offset hnext
  let removed :=
    sourceLocalLayerSerialCellRebaseUniformSwitchMaskAt graphData caps coloring
      web corridor hunique offset hnext
  constructor
  · rintro ⟨slot, hremoved, rfl⟩
    simpa [removed, sourceLocalLayerSerialCellRebaseUniformSwitchMaskAt] using
      hremoved
  · intro hedge
    have hcarrier : edge ∈ carrier :=
      sourceLocalLayerBoundaryRebaseSwitch_subset_uniformTrackedCarrier
        graphData caps coloring web corridor hunique offset hnext hedge
    let slot : Fin carrier.card := carrierCoordinate carrier ⟨edge, hcarrier⟩
    refine ⟨slot, ?_, ?_⟩
    · simp [sourceLocalLayerSerialCellRebaseUniformSwitchMaskAt,
        sourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt, slot,
        carrier, hedge]
    · simp [sourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt, slot,
        carrier]

/-- Deleting the uniform switch coordinates from the cumulative pre-rebase
graph gives exactly the unchanged core consumed by the successor recurrence. -/
theorem restrictedPreRebaseTrackedGraph_uniformSwitchMask_eq_core
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
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (pair : TrackedColorPair) :
    let graph := regionalTrackedEdgeGraph web.annular.RS
      (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
      color (trackedColorPairColors pair).1 (trackedColorPairColors pair).2
    restrictedByMask graph
        (sourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt graphData caps
          coloring web corridor hunique offset hnext)
        (sourceLocalLayerSerialCellRebaseUniformSwitchMaskAt graphData caps
          coloring web corridor hunique offset hnext) =
      coreTrackedGraphForColorAt corridor hunique offset hnext color pair := by
  dsimp only
  let graph := regionalTrackedEdgeGraph web.annular.RS
    (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
    color (trackedColorPairColors pair).1 (trackedColorPairColors pair).2
  let roleAt := sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset
    hnext
  have hpresentations :
      restrictedByMask graph
          (sourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt graphData caps
            coloring web corridor hunique offset hnext)
          (sourceLocalLayerSerialCellRebaseUniformSwitchMaskAt graphData caps
            coloring web corridor hunique offset hnext) =
        restrictedByMask graph roleAt allBoundaryRebaseRolesRemoved := by
    apply restrictedByMask_eq_of_removedByInterfaceMask_iff_on_support
    intro edge _hedge
    rw [removedBy_uniformSwitchMask_iff graphData caps coloring web corridor
      hunique offset hnext edge]
    rw [mem_sourceLocalLayerBoundaryRebaseSwitchAt_iff]
    constructor
    · rintro ⟨role, heq⟩
      exact ⟨role, rfl, heq.symm⟩
    · rintro ⟨role, _hremoved, heq⟩
      exact ⟨role, heq.symm⟩
  rw [hpresentations]
  exact restrictedPreRebaseTrackedGraph_eq_coreTrackedGraphForColorAt corridor
    hunique offset hnext color pair

/-- The executable row update on the literal uniform carrier: mask the switch
rows of the exact pre-rebase interface code, then add the local successor
adjacency row. -/
noncomputable def sourceLocalLayerSerialCellRebaseUniformTrackedSuccessorRawCodeAt
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
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (pair : TrackedColorPair) :
    BoundedInterfaceExteriorCode
      (Fin (sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
        graphData caps coloring web corridor hunique offset hnext).card) :=
  let edgeAt :=
    sourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt graphData caps coloring
      web corridor hunique offset hnext
  let removed :=
    sourceLocalLayerSerialCellRebaseUniformSwitchMaskAt graphData caps coloring
      web corridor hunique offset hnext
  let preRebase := regionalTrackedEdgeGraph web.annular.RS
    (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
    color (trackedColorPairColors pair).1 (trackedColorPairColors pair).2
  let localGraph := localTrackedGraphForColorAt corridor hunique offset hnext
    color pair
  addInterfaceAdjacency
    (maskInterfaceExteriorCode
      (exactInterfaceExteriorCode preRebase edgeAt) removed)
    (fun left right => by
      classical
      exact decide (localGraph.Adj (edgeAt left) (edgeAt right)))

/-- Closed source-independent packaging of the same raw row update.  The
dependent coordinate count is stored below the uniform bound of forty-nine. -/
noncomputable def
    sourceLocalLayerSerialCellRebaseUniformTrackedBoundedSuccessorCodeAt
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
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color) :
    BoundedInterfaceExteriorFamilyCode 49 TrackedColorPair := by
  let carrier :=
    sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
      coloring web corridor hunique offset hnext
  have hcard : carrier.card ≤ 49 :=
    sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt_card_le_fortyNine
      graphData minimal caps coloring web corridor hunique offset hnext
  exact {
    vertexCount := ⟨carrier.card, Nat.lt_succ_of_le hcard⟩
    code := sourceLocalLayerSerialCellRebaseUniformTrackedSuccessorRawCodeAt
      graphData caps coloring web corridor hunique offset hnext color }

/-- The finite row update is exactly the mask-independent exterior code of the
literal successor tracked graph. -/
theorem sourceLocalLayerSerialCellRebaseUniformTrackedSuccessorCodeAt_exact
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
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (pair : TrackedColorPair) :
    let edgeAt :=
      sourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt graphData caps
        coloring web corridor hunique offset hnext
    sourceLocalLayerSerialCellRebaseUniformTrackedSuccessorRawCodeAt graphData
      caps coloring web corridor hunique offset hnext color pair =
      exactInterfaceExteriorCode
        (successorTrackedGraphForColorAt corridor hunique offset hnext color
          pair) edgeAt := by
  dsimp only
  let carrier :=
    sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
      coloring web corridor hunique offset hnext
  let edgeAt :=
    sourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt graphData caps coloring
      web corridor hunique offset hnext
  let removed :=
    sourceLocalLayerSerialCellRebaseUniformSwitchMaskAt graphData caps coloring
      web corridor hunique offset hnext
  let preRebase := regionalTrackedEdgeGraph web.annular.RS
    (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
    color (trackedColorPairColors pair).1 (trackedColorPairColors pair).2
  let localGraph := localTrackedGraphForColorAt corridor hunique offset hnext color
    pair
  have hinjective : Function.Injective edgeAt :=
    sourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt_injective graphData caps
      coloring web corridor hunique offset hnext
  have hlocalSupport : localGraph.support ⊆ Set.range edgeAt := by
    intro edge hedge
    have hcarrier : edge ∈ carrier :=
        (sourceLocalLayerSerialCell_trackedRebase_support_subset_uniformInterface
        graphData caps coloring web corridor hunique offset hnext color pair).2
        hedge
    refine ⟨carrierCoordinate carrier ⟨edge, hcarrier⟩, ?_⟩
    simp [edgeAt, sourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt,
      carrier]
  change
    addInterfaceAdjacency
        (maskInterfaceExteriorCode
          (exactInterfaceExteriorCode preRebase edgeAt) removed)
        (fun left right => by
          classical
          exact decide (localGraph.Adj (edgeAt left) (edgeAt right))) =
      exactInterfaceExteriorCode
        (successorTrackedGraphForColorAt corridor hunique offset hnext color
          pair) edgeAt
  rw [maskInterfaceExteriorCode_exact_code_eq preRebase edgeAt hinjective
    removed]
  rw [restrictedPreRebaseTrackedGraph_uniformSwitchMask_eq_core graphData caps
    coloring web corridor hunique offset hnext color pair]
  have hadded :
      addInterfaceAdjacency
          (exactInterfaceExteriorCode
            (coreTrackedGraphForColorAt corridor hunique offset hnext color pair)
            edgeAt)
          (fun left right => by
            classical
            exact decide (localGraph.Adj (edgeAt left) (edgeAt right))) =
        exactInterfaceExteriorCode
          (coreTrackedGraphForColorAt corridor hunique offset hnext color pair ⊔
            localGraph) edgeAt := by
    apply addInterfaceAdjacency_exact_code_eq
      (coreTrackedGraphForColorAt corridor hunique offset hnext color pair)
      localGraph edgeAt hlocalSupport
    intro left right
    simp
  rw [hadded]
  exact congrArg (fun graph => exactInterfaceExteriorCode graph edgeAt)
    (core_sup_localTrackedForColor_eq_successor corridor hunique offset hnext
      color pair)

/-- The closed finite code computes literal successor reachability between
all named uniform coordinates. -/
theorem sourceLocalLayerSerialCellRebaseUniformTrackedSuccessorCodeAt_reachable_iff
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
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (pair : TrackedColorPair)
    (left right : Fin
      (sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
        coloring web corridor hunique offset hnext).card) :
    let edgeAt :=
      sourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt graphData caps
        coloring web corridor hunique offset hnext
    InterfaceExteriorTotalFactoredReachability
        (sourceLocalLayerSerialCellRebaseUniformTrackedSuccessorRawCodeAt
          graphData caps coloring web corridor hunique offset hnext color pair)
        edgeAt (fun _ => false) left right ↔
      (successorTrackedGraphForColorAt corridor hunique offset hnext color pair
        ).Reachable (edgeAt left) (edgeAt right) := by
  dsimp only
  rw [sourceLocalLayerSerialCellRebaseUniformTrackedSuccessorCodeAt_exact
    graphData caps coloring web corridor hunique offset hnext color pair]
  rw [exactInterfaceExteriorCode_totalFactoredReachability_iff]
  have hrestricted :
      restrictedByMask
          (successorTrackedGraphForColorAt corridor hunique offset hnext color
            pair)
          (sourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt graphData caps
            coloring web corridor hunique offset hnext)
          (fun _ => false) =
        successorTrackedGraphForColorAt corridor hunique offset hnext color
          pair := by
    rw [restrictedByMask]
    have hkeep :
        survivesMask
            (sourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt graphData caps
              coloring web corridor hunique offset hnext)
            (fun _ => false) =
          (fun _ => True) := by
      funext edge
      apply propext
      simp [survivesMask]
    rw [hkeep]
    exact supportRestriction_true _
  rw [hrestricted]

end

end GoertzelV24ClosedWebLocalLayerSerialCellUniformTrackedRecurrence

end Mettapedia.GraphTheory.FourColor
