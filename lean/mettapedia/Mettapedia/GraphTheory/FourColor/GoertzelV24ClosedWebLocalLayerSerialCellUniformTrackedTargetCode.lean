import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellUniformSuccessorColorParametric
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellPastOverlap
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialTrackedPrefixAttachmentColorParametric
import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceDeletionComponentFactorForgetExterior
import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceExteriorSupportedPortProjection

/-!
# Contract the uniform tracked successor to the rolling target carrier

The exact Cell--rebase successor graph is encoded on a bounded carrier of at
most forty-nine edges.  The next cumulative state again uses the rolling
twenty-one-slot transition carrier.  This file constructs the partial map from
that target carrier into the uniform carrier and contracts every forgotten
uniform coordinate into the exterior row.

An unmapped target coordinate is proved isolated in the successor graph using
the already established past-overlap theorem.  Consequently the contracted
three-row code is exactly the canonical exterior code on the literal target
carrier.  This is the graph-level projection needed before the next supported
attachment state can be decoded.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellUniformTrackedTargetCode

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
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedTransitionCarrier
open GoertzelV24ClosedWebLocalLayerSerialCellUniformTrackedRecurrence
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedPrefixAttachmentState
open GoertzelV24ClosedWebLocalLayerSerialTrackedPrefixAttachmentColorParametric
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24FramedTrail
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24InterfaceDeletionComponentFactorForget
open GoertzelV24InterfaceDeletionComponentFactorForgetExterior
open GoertzelV24InterfaceExteriorSupportedPortProjection
open GoertzelV24SimpleGraphPortResidualFactorContraction
open GoertzelV24SimpleGraphSupportedPortResidualFactorContraction
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance uniformTrackedTargetCodeEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance uniformTrackedTargetCodeOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- Partial coordinate map from the actual-cardinality target carrier to the
uniform forty-nine-edge carrier. -/
noncomputable def sourceLocalLayerSerialCellRebaseUniformTrackedTargetSourceAt
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
    let target := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData
      caps coloring web corridor hunique
        (sourceLocalLayerNextOffset offset hnext)
    let uniform :=
      sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
        coloring web corridor hunique offset hnext
    Fin target.card → Option (Fin uniform.card) := by
  classical
  dsimp only
  let target := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
    coloring web corridor hunique (sourceLocalLayerNextOffset offset hnext)
  let uniform := sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
    graphData caps coloring web corridor hunique offset hnext
  intro targetSlot
  let edge := ((carrierCoordinate target).symm targetSlot).1
  if hedge : edge ∈ uniform then
    exact some (carrierCoordinate uniform ⟨edge, hedge⟩)
  else
    exact none

/-- Every mapped target coordinate denotes the same ambient edge. -/
theorem sourceLocalLayerSerialCellRebaseUniformTrackedTargetSourceAt_edge_eq
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
    (uniformSlot : Fin
      (sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
        coloring web corridor hunique offset hnext).card)
    (hsource :
      sourceLocalLayerSerialCellRebaseUniformTrackedTargetSourceAt graphData caps
        coloring web corridor hunique offset hnext targetSlot =
          some uniformSlot) :
    sourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt graphData caps coloring
        web corridor hunique offset hnext uniformSlot =
      (((carrierCoordinate
        (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
          web corridor hunique (sourceLocalLayerNextOffset offset hnext))
        ).symm targetSlot).1) := by
  classical
  simp only [sourceLocalLayerSerialCellRebaseUniformTrackedTargetSourceAt,
    id_eq] at hsource
  split at hsource <;> rename_i hedge
  · simp only [Option.some.injEq] at hsource
    subst uniformSlot
    simp [sourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt]
  · cases hsource

/-- An unmapped target coordinate is isolated in every literal successor
tracked graph.  This is where bounded historical overlap is consumed. -/
theorem
    sourceLocalLayerSerialCellRebaseUniformTrackedTargetSourceAt_none_not_mem_support
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
    (hnone :
      sourceLocalLayerSerialCellRebaseUniformTrackedTargetSourceAt graphData caps
        coloring web corridor hunique offset hnext targetSlot = none) :
    (((carrierCoordinate
      (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique (sourceLocalLayerNextOffset offset hnext))
      ).symm targetSlot).1) ∉
      (successorTrackedGraphForColorAt corridor hunique offset hnext color pair
        ).support := by
  classical
  let target := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
    coloring web corridor hunique (sourceLocalLayerNextOffset offset hnext)
  let targetEdge : {edge // edge ∈ target} :=
    (carrierCoordinate target).symm targetSlot
  let uniform := sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
    graphData caps coloring web corridor hunique offset hnext
  have hnotUniform : targetEdge.1 ∉ uniform := by
    simp only [sourceLocalLayerSerialCellRebaseUniformTrackedTargetSourceAt,
      id_eq] at hnone
    split at hnone <;> rename_i hedge
    · cases hnone
    · exact hedge
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
  apply hnotUniform
  rcases hcovered with hswitch | hcurrent
  · exact sourceLocalLayerBoundaryRebaseSwitch_subset_uniformTrackedCarrier
      graphData caps coloring web corridor hunique offset hnext hswitch
  · exact Finset.mem_union_left _ hcurrent

/-- Exact successor exterior code after contracting the uniform carrier to the
literal next rolling carrier. -/
noncomputable def sourceLocalLayerSerialCellRebaseUniformTrackedTargetRawCodeAt
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
    BoundedInterfaceExteriorCode (Fin
      (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique (sourceLocalLayerNextOffset offset hnext)).card) :=
  partialContractedInterfaceExteriorCode
    (sourceLocalLayerSerialCellRebaseUniformTrackedSuccessorRawCodeAt graphData
      caps coloring web corridor hunique offset hnext color pair)
    (sourceLocalLayerSerialCellRebaseUniformTrackedTargetSourceAt graphData caps
      coloring web corridor hunique offset hnext)

/-- The contracted code is literally the canonical exterior code on the
actual-cardinality target carrier. -/
theorem sourceLocalLayerSerialCellRebaseUniformTrackedTargetRawCodeAt_exact
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
    let target := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData
      caps coloring web corridor hunique
        (sourceLocalLayerNextOffset offset hnext)
    let targetVertex := fun slot : Fin target.card =>
      ((carrierCoordinate target).symm slot).1
    sourceLocalLayerSerialCellRebaseUniformTrackedTargetRawCodeAt graphData caps
        coloring web corridor hunique offset hnext color pair =
      exactInterfaceExteriorCode
        (successorTrackedGraphForColorAt corridor hunique offset hnext color pair)
        targetVertex := by
  dsimp only
  let graph := successorTrackedGraphForColorAt corridor hunique offset hnext
    color pair
  let largerVertex := sourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt
    graphData caps coloring web corridor hunique offset hnext
  let target := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
    coloring web corridor hunique (sourceLocalLayerNextOffset offset hnext)
  let targetVertex := fun slot : Fin target.card =>
    ((carrierCoordinate target).symm slot).1
  let retain := sourceLocalLayerSerialCellRebaseUniformTrackedTargetSourceAt
    graphData caps coloring web corridor hunique offset hnext
  have hcode := sourceLocalLayerSerialCellRebaseUniformTrackedSuccessorCodeAt_exact
    graphData caps coloring web corridor hunique offset hnext color pair
  change partialContractedInterfaceExteriorCode
      (sourceLocalLayerSerialCellRebaseUniformTrackedSuccessorRawCodeAt graphData
        caps coloring web corridor hunique offset hnext color pair) retain =
      exactInterfaceExteriorCode graph targetVertex
  rw [hcode]
  have hinjective : Function.Injective targetVertex := by
    intro left right heq
    apply (carrierCoordinate target).symm.injective
    exact Subtype.ext heq
  have hsome : ∀ retained slot, retain retained = some slot →
      largerVertex slot = targetVertex retained := by
    intro retained slot hretain
    exact sourceLocalLayerSerialCellRebaseUniformTrackedTargetSourceAt_edge_eq
      graphData caps coloring web corridor hunique offset hnext retained slot
        hretain
  have hnone : ∀ retained, retain retained = none →
      targetVertex retained ∉ graph.support := by
    intro retained hretain
    exact
      sourceLocalLayerSerialCellRebaseUniformTrackedTargetSourceAt_none_not_mem_support
        graphData minimal caps coloring web corridor hunique offset hnext color
          pair retained hretain
  apply boundedInterfaceExteriorCode_ext_iff
  · intro left right
    change partialReindexedVertexEq left right = true ↔
      (exactInterfaceExteriorCode graph targetVertex).vertexEq left right = true
    rw [partialReindexedVertexEq_eq_true_iff targetVertex hinjective]
    simp [exactInterfaceExteriorCode]
  · intro left right
    change partialReindexedDirectAdj
        (exactInterfaceExteriorCode graph largerVertex) retain left right = true ↔
      (exactInterfaceExteriorCode graph targetVertex).directAdj left right = true
    rw [partialReindexedDirectAdj_exact_iff graph largerVertex targetVertex
      retain hsome hnone left right]
    simp [exactInterfaceExteriorCode]
  · intro left right
    change partialReindexedExteriorConnected
        (exactInterfaceExteriorCode graph largerVertex) retain left right = true ↔
      (exactInterfaceExteriorCode graph targetVertex).exteriorConnected left
        right = true
    rw [partialReindexedExteriorConnected_exact_eq_true_iff graph largerVertex
      targetVertex retain hsome hnone left right]
    simp [exactInterfaceExteriorCode]

/-- Literal successor port as an element of the next rolling carrier. -/
noncomputable def sourceLocalLayerSerialCellRebaseTrackedTargetPortEdgeAt
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
    (port : CorridorPort 2 1) :
    {edge // edge ∈ sourceLocalLayerSerialTrackedTransitionCarrierAt graphData
      caps coloring web corridor hunique
        (sourceLocalLayerNextOffset offset hnext)} := by
  let next := sourceLocalLayerNextOffset offset hnext
  rcases port with crossing | terminal
  · refine ⟨sourceLocalLayerLeftCrossingAt corridor hunique next crossing, ?_⟩
    exact Finset.mem_union_left _ <| Finset.mem_union_left _ <|
      sourceLocalLayerCellRegionAt_leftCrossing corridor hunique next crossing
  · refine ⟨sourceLocalLayerSharedRungAt corridor hunique next, ?_⟩
    exact Finset.mem_union_right _ (Finset.mem_singleton_self _)

/-- The target-carrier port coordinate denotes the terminal-input port edge
on the nose. -/
@[simp] theorem sourceLocalLayerSerialCellRebaseTrackedTargetPortEdgeAt_val
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
    (port : CorridorPort 2 1) :
    (sourceLocalLayerSerialCellRebaseTrackedTargetPortEdgeAt graphData caps
      coloring web corridor hunique offset hnext port).1 =
      (sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext)).portEdge port := by
  rcases port with crossing | terminal
  · rfl
  · exact Fin.eq_zero terminal ▸ rfl

/-- Stable twenty-one-slot decoder into coordinates of the literal next
rolling carrier. -/
noncomputable def sourceLocalLayerSerialCellRebaseTrackedTargetSlotAt
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
    Fin 21 → Option (Fin
      (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique
          (sourceLocalLayerNextOffset offset hnext)).card) :=
  let target := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
    coloring web corridor hunique (sourceLocalLayerNextOffset offset hnext)
  fun slot => (sourceLocalLayerSerialTrackedTransitionEdgeAtSlot? graphData caps
    coloring web corridor hunique (sourceLocalLayerNextOffset offset hnext) slot
      ).map (carrierCoordinate target)

/-- The graph-free target projection, now packaged in the same stable state
type used by the next cumulative prefix. -/
noncomputable def sourceLocalLayerSerialCellRebaseUniformTrackedTargetStateAt
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
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color) :
    SourceLocalLayerSerialTrackedPrefixAttachmentState :=
  let target := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
    coloring web corridor hunique (sourceLocalLayerNextOffset offset hnext)
  let portCoordinate := fun port : CorridorPort 2 1 => carrierCoordinate target
    (sourceLocalLayerSerialCellRebaseTrackedTargetPortEdgeAt graphData caps
      coloring web corridor hunique offset hnext port)
  fun pair => projectSupportedPortResidualCode
    (sourceLocalLayerSerialCellRebaseUniformTrackedTargetRawCodeAt graphData caps
      coloring web corridor hunique offset hnext color pair)
    (sourceLocalLayerSerialCellRebaseTrackedTargetSlotAt graphData caps coloring
      web corridor hunique offset hnext)
    portCoordinate

/-- The executable projection is exactly the canonical next cumulative
twenty-one-slot attachment state. -/
theorem sourceLocalLayerSerialCellRebaseUniformTrackedTargetStateAt_exact
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
    sourceLocalLayerSerialCellRebaseUniformTrackedTargetStateAt graphData caps
        coloring web corridor hunique offset hnext color =
      sourceLocalLayerSerialTrackedPrefixAttachmentStateForColorAt graphData caps
        coloring web corridor hunique (sourceLocalLayerNextOffset offset hnext)
          color := by
  funext pair
  let target := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
    coloring web corridor hunique (sourceLocalLayerNextOffset offset hnext)
  let targetVertex := fun slot : Fin target.card =>
    ((carrierCoordinate target).symm slot).1
  let targetPort := fun port : CorridorPort 2 1 => carrierCoordinate target
    (sourceLocalLayerSerialCellRebaseTrackedTargetPortEdgeAt graphData caps
      coloring web corridor hunique offset hnext port)
  let decode := sourceLocalLayerSerialCellRebaseTrackedTargetSlotAt graphData caps
    coloring web corridor hunique offset hnext
  have hinjective : Function.Injective targetVertex := by
    intro left right heq
    apply (carrierCoordinate target).symm.injective
    exact Subtype.ext heq
  change projectSupportedPortResidualCode
      (sourceLocalLayerSerialCellRebaseUniformTrackedTargetRawCodeAt graphData caps
        coloring web corridor hunique offset hnext color pair)
      decode targetPort = _
  rw [sourceLocalLayerSerialCellRebaseUniformTrackedTargetRawCodeAt_exact
    graphData minimal caps coloring web corridor hunique offset hnext color pair]
  rw [projectSupportedPortResidualCode_exact_eq_pad _ targetVertex hinjective
    decode targetPort]
  let edgeDecode := sourceLocalLayerSerialTrackedTransitionEdgeAtSlot? graphData
    caps coloring web corridor hunique (sourceLocalLayerNextOffset offset hnext)
  let portEdge := sourceLocalLayerSerialCellRebaseTrackedTargetPortEdgeAt
    graphData caps coloring web corridor hunique offset hnext
  simpa [decode, targetVertex, targetPort, edgeDecode, portEdge,
      sourceLocalLayerSerialCellRebaseTrackedTargetSlotAt,
      sourceLocalLayerSerialTrackedPrefixAttachmentStateForColorAt,
      successorTrackedGraphForColorAt] using
    (pad_exactSupportedPortResidualCode_equiv
      (successorTrackedGraphForColorAt corridor hunique offset hnext color pair)
      (fun edge : {edge // edge ∈ target} => edge.1)
      (carrierCoordinate target) edgeDecode portEdge)

end

end GoertzelV24ClosedWebLocalLayerSerialCellUniformTrackedTargetCode

end Mettapedia.GraphTheory.FourColor
