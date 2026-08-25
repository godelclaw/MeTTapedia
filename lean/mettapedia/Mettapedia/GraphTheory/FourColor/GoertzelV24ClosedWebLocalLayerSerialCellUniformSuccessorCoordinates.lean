import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellUniformTrackedRecurrence
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceRecurrence
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseFiniteProfileReceipt
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteOutputPort
import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceDeletionComponentFactorGraphFree

/-!
# Named successor coordinates in the uniform Cell--rebase carriers

The fixed tracked and facial recurrences are expressed on anonymous `Fin`
coordinates.  The five-field corridor profile, however, observes named
successor ports and boundary-face fragments.  This file supplies the exact
coordinate adapters between those two presentations.

Each successor port edge belongs to the forty-nine-edge tracked carrier.  Each
canonical fragment dart and both literal dart occurrences over every successor
port belong to the forty-eight-dart facial carrier.  The coordinate maps are
proved to decode back to the literal ambient edge or dart.

These adapters carry no arbitrary output bits and assert no reachable-state
count.  They are the indexing bridge consumed by the combined finite letter.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellUniformSuccessorCoordinates

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseTrackedColorParametric
open GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceRecurrence
open GoertzelV24ClosedWebLocalLayerSerialCellUniformTrackedRecurrence
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteOutputPort
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24InterfaceDeletionComponentFactorGraphFree
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance cellUniformSuccessorCoordinatesEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance cellUniformSuccessorCoordinatesOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- Coordinate of one named successor port in the uniform tracked carrier. -/
noncomputable def sourceLocalLayerSerialCellRebaseUniformTrackedPortCoordinateAt
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
    Fin (sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData
      caps coloring web corridor hunique offset hnext).card := by
  let carrier :=
    sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
      coloring web corridor hunique offset hnext
  let role := sourceLocalLayerBoundaryRebaseSuccessorPortRole port
  let edge := sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext
    role
  have hedgeSwitch : edge ∈
      sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique offset hnext :=
    (mem_sourceLocalLayerBoundaryRebaseSwitchAt_iff corridor hunique offset
      hnext edge).2 ⟨role, rfl⟩
  have hedgeCarrier : edge ∈ carrier :=
    sourceLocalLayerBoundaryRebaseSwitch_subset_uniformTrackedCarrier graphData
      caps coloring web corridor hunique offset hnext hedgeSwitch
  exact carrierCoordinate carrier ⟨edge, hedgeCarrier⟩

/-- The tracked coordinate denotes exactly the successor cut's named port
edge. -/
@[simp]
theorem sourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt_portCoordinate
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
    sourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt graphData caps coloring
        web corridor hunique offset hnext
        (sourceLocalLayerSerialCellRebaseUniformTrackedPortCoordinateAt
          graphData caps coloring web corridor hunique offset hnext port) =
      (sourceLocalLayerBoundaryRebaseSuccessorCutDataAt corridor hunique offset
        hnext).portEdge port := by
  rw [← sourceLocalLayerBoundaryRebaseEdgeAt_successorPortRole corridor hunique
    offset hnext port]
  simp [sourceLocalLayerSerialCellRebaseUniformTrackedPortCoordinateAt,
    sourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt]

/-- Coordinate of the canonical literal dart naming one successor boundary
fragment in the uniform facial carrier. -/
noncomputable def sourceLocalLayerSerialCellRebaseUniformFaceFragmentCoordinateAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (fragment : SourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAt corridor
      hunique offset hnext) :
    Fin (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor
      hunique offset hnext).card := by
  let carrier := sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
    corridor hunique offset hnext
  let dart := sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentDartAt corridor
    hunique offset hnext fragment
  have hdart : dart ∈ carrier := Finset.mem_union_right _
    (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentDartAt_mem_collar
      corridor hunique offset hnext fragment)
  exact carrierCoordinate carrier ⟨dart, hdart⟩

/-- The facial fragment coordinate denotes its canonical literal dart. -/
@[simp]
theorem sourceLocalLayerSerialCellRebaseUniformFaceDartAt_fragmentCoordinate
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (fragment : SourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAt corridor
      hunique offset hnext) :
    sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor hunique offset
        hnext
        (sourceLocalLayerSerialCellRebaseUniformFaceFragmentCoordinateAt
          corridor hunique offset hnext fragment) =
      sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentDartAt corridor hunique
        offset hnext fragment := by
  simp [sourceLocalLayerSerialCellRebaseUniformFaceFragmentCoordinateAt,
    sourceLocalLayerSerialCellRebaseUniformFaceDartAt]

/-- The two literal dart occurrences over one successor port edge. -/
noncomputable def sourceLocalLayerSerialCellRebaseUniformFacePortDartEquivAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (port : CorridorPort 2 1) :
    Fin 2 ≃ {dart : web.annular.RS.D //
      dart ∈ web.annular.RS.dartsOn
        ((sourceLocalLayerBoundaryRebaseSuccessorCutDataAt corridor hunique
          offset hnext).portEdge port)} :=
  let darts := {dart : web.annular.RS.D //
    dart ∈ web.annular.RS.dartsOn
      ((sourceLocalLayerBoundaryRebaseSuccessorCutDataAt corridor hunique offset
        hnext).portEdge port)}
  let hcard : Fintype.card darts = 2 := by
    rw [Fintype.card_coe]
    exact web.annular.RS.dartsOn_card_two
      ((sourceLocalLayerBoundaryRebaseSuccessorCutDataAt corridor hunique offset
        hnext).portEdge port)
  ((Fintype.equivFin darts).trans (finCongr hcard)).symm

/-- One selected occurrence over a successor port edge. -/
noncomputable def sourceLocalLayerSerialCellRebaseUniformFacePortDartAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (port : CorridorPort 2 1) (side : Fin 2) : web.annular.RS.D :=
  (sourceLocalLayerSerialCellRebaseUniformFacePortDartEquivAt corridor hunique
    offset hnext port side).1

/-- Every successor port occurrence belongs to the uniform facial carrier. -/
theorem sourceLocalLayerSerialCellRebaseUniformFacePortDartAt_mem_carrier
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (port : CorridorPort 2 1) (side : Fin 2) :
    sourceLocalLayerSerialCellRebaseUniformFacePortDartAt corridor hunique
        offset hnext port side ∈
      sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor hunique
        offset hnext := by
  apply sourceLocalLayerBoundaryRebaseChangedFaceDarts_subset_uniformFaceCarrier
    corridor hunique offset hnext
  rw [mem_sourceLocalLayerBoundaryRebaseChangedFaceDartsAt_iff]
  have hedge :
      web.annular.RS.edgeOf
          (sourceLocalLayerSerialCellRebaseUniformFacePortDartAt corridor
            hunique offset hnext port side) =
        (sourceLocalLayerBoundaryRebaseSuccessorCutDataAt corridor hunique offset
          hnext).portEdge port := by
    exact (web.annular.RS.mem_dartsOn).1
      (sourceLocalLayerSerialCellRebaseUniformFacePortDartEquivAt corridor
        hunique offset hnext port side).2
  rw [hedge, ← sourceLocalLayerBoundaryRebaseEdgeAt_successorPortRole corridor
    hunique offset hnext port]
  exact (mem_sourceLocalLayerBoundaryRebaseSwitchAt_iff corridor hunique offset
    hnext _).2
      ⟨sourceLocalLayerBoundaryRebaseSuccessorPortRole port, rfl⟩

/-- Coordinate of one selected successor port occurrence in the uniform facial
carrier. -/
noncomputable def sourceLocalLayerSerialCellRebaseUniformFacePortCoordinateAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (port : CorridorPort 2 1) (side : Fin 2) :
    Fin (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor
      hunique offset hnext).card :=
  carrierCoordinate
    (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor hunique
      offset hnext)
    ⟨sourceLocalLayerSerialCellRebaseUniformFacePortDartAt corridor hunique
      offset hnext port side,
      sourceLocalLayerSerialCellRebaseUniformFacePortDartAt_mem_carrier corridor
        hunique offset hnext port side⟩

/-- The facial port coordinate denotes exactly the selected literal dart
occurrence. -/
@[simp]
theorem sourceLocalLayerSerialCellRebaseUniformFaceDartAt_portCoordinate
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (port : CorridorPort 2 1) (side : Fin 2) :
    sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor hunique offset
        hnext
        (sourceLocalLayerSerialCellRebaseUniformFacePortCoordinateAt corridor
          hunique offset hnext port side) =
      sourceLocalLayerSerialCellRebaseUniformFacePortDartAt corridor hunique
        offset hnext port side := by
  simp [sourceLocalLayerSerialCellRebaseUniformFacePortCoordinateAt,
    sourceLocalLayerSerialCellRebaseUniformFaceDartAt]

/-- The graph-free tracked closure on the named successor ports is exactly
reachability in the literal successor two-colour graph. -/
theorem sourceLocalLayerSerialCellRebaseUniformTrackedClosure_port_iff
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
    (pair : TrackedColorPair) (left right : CorridorPort 2 1) :
    InterfaceExteriorClosure
        (sourceLocalLayerSerialCellRebaseUniformTrackedSuccessorRawCodeAt
          graphData caps coloring web corridor hunique offset hnext color pair)
        (sourceLocalLayerSerialCellRebaseUniformTrackedPortCoordinateAt graphData
          caps coloring web corridor hunique offset hnext left)
        (sourceLocalLayerSerialCellRebaseUniformTrackedPortCoordinateAt graphData
          caps coloring web corridor hunique offset hnext right) ↔
      (successorTrackedGraphForColorAt corridor hunique offset hnext color pair
        ).Reachable
        ((sourceLocalLayerBoundaryRebaseSuccessorCutDataAt corridor hunique
          offset hnext).portEdge left)
        ((sourceLocalLayerBoundaryRebaseSuccessorCutDataAt corridor hunique
          offset hnext).portEdge right) := by
  rw [sourceLocalLayerSerialCellRebaseUniformTrackedSuccessorCodeAt_exact
    graphData caps coloring web corridor hunique offset hnext color pair]
  rw [exactInterfaceExteriorCode_closure_iff_of_injective]
  · simp
  · exact sourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt_injective
      graphData caps coloring web corridor hunique offset hnext

/-- The graph-free facial closure from one port occurrence to one canonical
fragment occurrence is exactly literal successor-face reachability. -/
theorem sourceLocalLayerSerialCellRebaseUniformFaceClosure_port_fragment_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (port : CorridorPort 2 1) (side : Fin 2)
    (fragment : SourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAt corridor
      hunique offset hnext) :
    InterfaceExteriorClosure
        (sourceLocalLayerSerialCellRebaseUniformFaceSuccessorRawCodeAt corridor
          hunique offset hnext)
        (sourceLocalLayerSerialCellRebaseUniformFacePortCoordinateAt corridor
          hunique offset hnext port side)
        (sourceLocalLayerSerialCellRebaseUniformFaceFragmentCoordinateAt corridor
          hunique offset hnext fragment) ↔
      (sourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt corridor hunique offset
        hnext).Reachable
        (sourceLocalLayerSerialCellRebaseUniformFacePortDartAt corridor hunique
          offset hnext port side)
        (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentDartAt corridor
          hunique offset hnext fragment) := by
  rw [sourceLocalLayerSerialCellRebaseUniformFaceSuccessorCodeAt_exact corridor
    hunique offset hnext]
  rw [exactInterfaceExteriorCode_closure_iff_of_injective]
  · simp
  · exact sourceLocalLayerSerialCellRebaseUniformFaceDartAt_injective corridor
      hunique offset hnext

/-- The finite facial closure recognizes exact incidence of a successor
boundary fragment with a named successor port. -/
theorem sourceLocalLayerSerialCellRebaseUniformFaceFragmentContainsPort_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (fragment : SourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAt corridor
      hunique offset hnext) (port : CorridorPort 2 1) :
    (∃ side : Fin 2,
      InterfaceExteriorClosure
        (sourceLocalLayerSerialCellRebaseUniformFaceSuccessorRawCodeAt corridor
          hunique offset hnext)
        (sourceLocalLayerSerialCellRebaseUniformFacePortCoordinateAt corridor
          hunique offset hnext port side)
        (sourceLocalLayerSerialCellRebaseUniformFaceFragmentCoordinateAt corridor
          hunique offset hnext fragment)) ↔
      (sourceLocalLayerBoundaryRebaseFiniteFaceReceiptAt corridor hunique offset
        hnext).fragmentContainsPort
          (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentSlotAt corridor
            hunique offset hnext fragment) port = true := by
  rw [sourceLocalLayerBoundaryRebaseFiniteFaceReceiptAt_fragmentContainsPort_iff]
  let cutData := sourceLocalLayerBoundaryRebaseSuccessorCutDataAt corridor
    hunique offset hnext
  have hportRegion : cutData.portEdge port ∈ cutData.regionEdges := by
    exact sourceLocalLayerSerialTerminalInputCutDataAt_portsInRegion corridor
      hunique (sourceLocalLayerNextOffset offset hnext) port
  rw [edge_mem_boundaryRegionalFragmentEdges_iff_exists_dart_reachable
    web.annular.RS _ _ fragment (cutData.portEdge port) hportRegion]
  constructor
  · rintro ⟨side, hclosure⟩
    refine ⟨sourceLocalLayerSerialCellRebaseUniformFacePortDartEquivAt corridor
      hunique offset hnext port side, ?_⟩
    exact
      (sourceLocalLayerSerialCellRebaseUniformFaceClosure_port_fragment_iff
        corridor hunique offset hnext port side fragment).1 hclosure
  · rintro ⟨dart, hreachable⟩
    let side :=
      (sourceLocalLayerSerialCellRebaseUniformFacePortDartEquivAt corridor
        hunique offset hnext port).symm dart
    refine ⟨side, ?_⟩
    apply
      (sourceLocalLayerSerialCellRebaseUniformFaceClosure_port_fragment_iff
        corridor hunique offset hnext port side fragment).2
    simpa [side, sourceLocalLayerSerialCellRebaseUniformFacePortDartAt,
      sourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt,
      sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentDartAt] using
      hreachable

end

end GoertzelV24ClosedWebLocalLayerSerialCellUniformSuccessorCoordinates

end Mettapedia.GraphTheory.FourColor
