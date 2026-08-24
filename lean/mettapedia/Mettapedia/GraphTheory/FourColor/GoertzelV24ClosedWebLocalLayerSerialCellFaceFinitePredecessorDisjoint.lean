import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteNewEdgeAdequacy
import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutLayerSeparation

/-!
# Local simplicity for predecessor contributions of one source Cell

An outgoing source-Cell face fragment meets one of the two crossings of the
second literal layer.  Hence its ambient face occurs in that layer walk and,
by boundary cleanliness of the corridor, is an annular-interior face.  This
local fact is the replacement for a false global two-sidedness assumption on
the opened carrier.

The eventual predecessor cap decoder uses this theorem to show that distinct
old components contributing to one output fragment have disjoint primal-edge
supports.  No cap sum is identified in this file.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellFaceFinitePredecessorDisjoint

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteClosure
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteOutputCap
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteOutputFragment
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFinitePredecessorRepresentatives
open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24FaceOrbitIncidence
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationAllFaceCutProfile
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationFaceRegionalDartGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebLocalLayerSerialCellFaceFinitePredecessorDisjointEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Every actual outgoing fragment of a literal source Cell lies on an
annular-interior face.  The proof follows its canonical cut edge into the
second local layer; no global two-sidedness property is used. -/
theorem sourceLocalLayerSerialFaceOutputFragment_face_mem_interiorFaces
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (fragment : SourceLocalLayerSerialFaceOutputFragmentAt corridor hunique
      offset) :
    fragment.1.1 ∈ web.annular.cellulation.interiorFaces := by
  let layers := sourceLocalLayerPairAt corridor hunique offset
  let cut := indexedCrossingEdgeSet
    (sourceLocalLayerRightCrossingAt corridor hunique offset)
  let region := sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique
    offset
  let edge := boundaryRegionalFragmentCutEdge web.annular.RS cut region fragment
  have hedgeCut : edge ∈ cut :=
    boundaryRegionalFragmentCutEdge_mem_cut web.annular.RS cut region fragment
  rcases (mem_indexedCrossingEdgeSet_iff
    (sourceLocalLayerRightCrossingAt corridor hunique offset) edge).1 hedgeCut with
    ⟨step, hstep⟩
  let secondStep : Fin layers.secondLayer.walk.length :=
    ⟨step.val, by
      simpa [LocalLayerPair.secondLayer, LocalLayerPair.secondWalk] using
        step.isLt⟩
  have hedgeCrossing : edge ∈ layers.secondLayer.crossingEdges hunique := by
    apply (layers.secondLayer.mem_crossingEdges_iff hunique edge).2
    refine ⟨secondStep, ?_⟩
    simpa [sourceLocalLayerRightCrossingAt, layers, secondStep] using hstep
  have hedgeFragment : edge ∈
      boundaryRegionalFragmentEdges web.annular.RS cut region fragment :=
    boundaryRegionalFragmentCutEdge_mem_fragment web.annular.RS cut region
      fragment
  have hedgeFace : edge ∈ orbitFaceBoundary web.annular.RS fragment.1.1 :=
    (Finset.mem_inter.mp
      (boundaryRegionalFragmentEdges_subset_boundary_inter_region
        web.annular.RS cut region fragment hedgeFragment)).1
  have hsecondSupport :
      (⟨fragment.1.1, Finset.mem_univ fragment.1.1⟩ :
        AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))) ∈
        layers.secondWalk.support := by
    exact layers.secondLayer.face_mem_walk_support_of_mem_crossingEdge_of_mem_boundary
      hunique hedgeCrossing hedgeFace
  apply layers.localLayerLoop_support_internal
    ⟨fragment.1.1, Finset.mem_univ fragment.1.1⟩
  simp [LocalLayerPair.localLayerLoop, LocalLayerPair.firstWalk,
    LocalLayerPair.secondWalk] at hsecondSupport ⊢
  aesop

/-- Two disconnected regional components on the same annular-interior face
have disjoint primal-edge supports.  Boundary simplicity is used only for the
one face in question; the opened carrier need not be globally two-sided. -/
theorem sourceLocalLayerBoundaryRebaseFaceComponentEdges_disjoint_of_same_interior_face
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) (region : Finset G.edgeSet)
    {left right : web.annular.RS.D}
    (hsameFace : dartOrbitFace web.annular.RS left =
      dartOrbitFace web.annular.RS right)
    (hface : dartOrbitFace web.annular.RS left ∈
      web.annular.cellulation.interiorFaces)
    (hnotReachable : ¬ (faceRegionalDartGraph web.annular.RS region).Reachable
      left right) :
    Disjoint
      (sourceLocalLayerBoundaryRebaseFaceComponentEdges web.annular.RS region
        left)
      (sourceLocalLayerBoundaryRebaseFaceComponentEdges web.annular.RS region
        right) := by
  classical
  rw [Finset.disjoint_left]
  intro edge hleftEdge hrightEdge
  rcases (mem_sourceLocalLayerBoundaryRebaseFaceComponentEdges_iff
      web.annular.RS region left edge).1 hleftEdge with
    ⟨_leftRegion, leftDart, hleftReachable⟩
  rcases (mem_sourceLocalLayerBoundaryRebaseFaceComponentEdges_iff
      web.annular.RS region right edge).1 hrightEdge with
    ⟨_rightRegion, rightDart, hrightReachable⟩
  have hleftDartFace :=
    faceRegionalDartGraph_reachable_dartOrbitFace_eq web.annular.RS region
      hleftReachable
  have hrightDartFace :=
    faceRegionalDartGraph_reachable_dartOrbitFace_eq web.annular.RS region
      hrightReachable
  have hinjective : Set.InjOn web.annular.RS.edgeOf
      (orbitFaceDarts web.annular.RS
        (dartOrbitFace web.annular.RS left)) := by
    apply Finset.card_image_iff.mp
    exact Instance.InteriorFace.boundary_card_eq_darts_card web left hface
  have hleftDartMem : leftDart.1 ∈ orbitFaceDarts web.annular.RS
      (dartOrbitFace web.annular.RS left) :=
    (mem_orbitFaceDarts_iff web.annular.RS
      (dartOrbitFace web.annular.RS left) leftDart.1).2 hleftDartFace.symm
  have hrightDartMem : rightDart.1 ∈ orbitFaceDarts web.annular.RS
      (dartOrbitFace web.annular.RS left) :=
    (mem_orbitFaceDarts_iff web.annular.RS
      (dartOrbitFace web.annular.RS left) rightDart.1).2
        ((hsameFace.trans hrightDartFace).symm)
  have hleftEdgeOf : web.annular.RS.edgeOf leftDart.1 = edge :=
    (web.annular.RS.mem_dartsOn).1 leftDart.2
  have hrightEdgeOf : web.annular.RS.edgeOf rightDart.1 = edge :=
    (web.annular.RS.mem_dartsOn).1 rightDart.2
  have hdarts : leftDart.1 = rightDart.1 :=
    hinjective hleftDartMem hrightDartMem
      (hleftEdgeOf.trans hrightEdgeOf.symm)
  apply hnotReachable
  exact hleftReachable.trans (hdarts ▸ hrightReachable.symm)

/-- The cap stored at any live finite predecessor coordinate is exactly the
cap at five of that coordinate's literal predecessor-component edge support. -/
theorem sourceLocalLayerSerialFaceFinitePredecessor_componentCap_eq
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6) :
    let carrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor
      hunique offset
    let coordinate := carrierCoordinate carrier
    let code := sourceLocalLayerSerialFaceTransitionCodeAt corridor hunique
      offset hcell
    let state := sourceLocalLayerSerialFacePrefixAttachmentStateAt corridor
      hunique offset hcell
    ∀ coordinateIndex : Fin code.vertexCount.val,
      state.componentCap
          (sourceLocalLayerSerialFaceFiniteStableSlot code coordinateIndex) =
        ⟨min (sourceLocalLayerBoundaryRebaseFaceComponentEdges web.annular.RS
            (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
            (coordinate.symm coordinateIndex).1).card 5,
          Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩ := by
  dsimp only
  intro coordinateIndex
  let carrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
    offset
  let coordinate := carrierCoordinate carrier
  let code := sourceLocalLayerSerialFaceTransitionCodeAt corridor hunique offset
    hcell
  let state := sourceLocalLayerSerialFacePrefixAttachmentStateAt corridor
    hunique offset hcell
  have hslotDart (dart : {dart // dart ∈ carrier}) :
      sourceLocalLayerSerialFaceFiniteStableSlot code (coordinate dart) =
        sourceLocalLayerSerialFaceTransitionSlotAt corridor hunique offset hcell
          dart := by
    rfl
  have hslot :
      sourceLocalLayerSerialFaceFiniteStableSlot code coordinateIndex =
        sourceLocalLayerSerialFaceTransitionSlotAt corridor hunique offset hcell
          (coordinate.symm coordinateIndex) := by
    rw [← hslotDart (coordinate.symm coordinateIndex)]
    simp
  rw [hslot]
  exact sourceLocalLayerSerialFacePrefixAttachmentStateAt_componentCap corridor
    hunique offset hcell (coordinate.symm coordinateIndex)

/-- Value form of the exact predecessor-cap theorem, ready for the finite
representative sum. -/
theorem sourceLocalLayerSerialFaceFinitePredecessor_componentCap_val
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6) :
    let carrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor
      hunique offset
    let coordinate := carrierCoordinate carrier
    let code := sourceLocalLayerSerialFaceTransitionCodeAt corridor hunique
      offset hcell
    let state := sourceLocalLayerSerialFacePrefixAttachmentStateAt corridor
      hunique offset hcell
    ∀ coordinateIndex : Fin code.vertexCount.val,
      (state.componentCap
          (sourceLocalLayerSerialFaceFiniteStableSlot code coordinateIndex)).val =
        min (sourceLocalLayerBoundaryRebaseFaceComponentEdges web.annular.RS
          (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
          (coordinate.symm coordinateIndex).1).card 5 := by
  dsimp only
  intro coordinateIndex
  exact congrArg Fin.val
    (sourceLocalLayerSerialFaceFinitePredecessor_componentCap_eq corridor
      hunique offset hcell coordinateIndex)

/-- Distinct canonical predecessor components that contribute to one actual
outgoing fragment have disjoint old primal-edge supports.  This is the exact
non-overlap fact needed before their capped sizes may be added. -/
theorem sourceLocalLayerSerialFaceFiniteContributingPredecessor_componentEdges_disjoint
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (fragment : SourceLocalLayerSerialFaceOutputFragmentAt corridor hunique
      offset) :
    let carrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor
      hunique offset
    let coordinate := carrierCoordinate carrier
    let code := sourceLocalLayerSerialFaceTransitionCodeAt corridor hunique
      offset hcell
    let state := sourceLocalLayerSerialFacePrefixAttachmentStateAt corridor
      hunique offset hcell
    let semantic := sourceLocalLayerSerialFaceFinitePredecessorSemanticAt
      corridor hunique offset hcell
    let output := coordinate
      (sourceLocalLayerSerialFaceOutputFragmentTransitionDartAt corridor hunique
        offset fragment)
    ∀ {left right : Fin code.vertexCount.val},
      left ∈ sourceLocalLayerSerialFaceFiniteContributingPredecessors state
          code semantic output →
      right ∈ sourceLocalLayerSerialFaceFiniteContributingPredecessors state
          code semantic output →
      left ≠ right →
        Disjoint
          (sourceLocalLayerBoundaryRebaseFaceComponentEdges web.annular.RS
            (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
            (coordinate.symm left).1)
          (sourceLocalLayerBoundaryRebaseFaceComponentEdges web.annular.RS
            (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
            (coordinate.symm right).1) := by
  dsimp only
  intro left right hleft hright hne
  let carrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
    offset
  let coordinate := carrierCoordinate carrier
  let code := sourceLocalLayerSerialFaceTransitionCodeAt corridor hunique offset
    hcell
  let state := sourceLocalLayerSerialFacePrefixAttachmentStateAt corridor
    hunique offset hcell
  let semantic := sourceLocalLayerSerialFaceFinitePredecessorSemanticAt corridor
    hunique offset hcell
  let outputDart :=
    sourceLocalLayerSerialFaceOutputFragmentTransitionDartAt corridor hunique
      offset fragment
  let output := coordinate outputDart
  let oldRegion := sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
    offset
  let outputRegion := sourceLocalLayerSerialPreRebaseOutputRegionAt corridor
    hunique offset
  have hleftData :
      left ∈ sourceLocalLayerSerialFaceFinitePredecessorRepresentatives state
          code semantic ∧
        Relation.ReflTransGen
          (SourceLocalLayerSerialFaceFiniteComponentStep state code) output left := by
    simpa [sourceLocalLayerSerialFaceFiniteContributingPredecessors, state, code,
      semantic, output, coordinate, carrier] using hleft
  have hrightData :
      right ∈ sourceLocalLayerSerialFaceFinitePredecessorRepresentatives state
          code semantic ∧
        Relation.ReflTransGen
          (SourceLocalLayerSerialFaceFiniteComponentStep state code) output right := by
    simpa [sourceLocalLayerSerialFaceFiniteContributingPredecessors, state, code,
      semantic, output, coordinate, carrier] using hright
  have hleftFixed :=
    (mem_sourceLocalLayerSerialFaceFinitePredecessorRepresentatives_iff state
      code semantic left).1 hleftData.1 |>.2
  have hrightFixed :=
    (mem_sourceLocalLayerSerialFaceFinitePredecessorRepresentatives_iff state
      code semantic right).1 hrightData.1 |>.2
  have hnotConnected :
      ¬ SourceLocalLayerSerialFaceFinitePredecessorConnected state code left
        right := by
    intro hconnected
    have hrepresentatives :=
      (sourceLocalLayerSerialFaceFinitePredecessorRepresentative_eq_iff state
        code semantic left right).2 hconnected
    apply hne
    exact hleftFixed.symm.trans (hrepresentatives.symm.trans hrightFixed)
  have hslotDart (dart : {dart // dart ∈ carrier}) :
      sourceLocalLayerSerialFaceFiniteStableSlot code (coordinate dart) =
        sourceLocalLayerSerialFaceTransitionSlotAt corridor hunique offset hcell
          dart := by
    rfl
  have hslot (coordinateIndex : Fin code.vertexCount.val) :
      sourceLocalLayerSerialFaceFiniteStableSlot code coordinateIndex =
        sourceLocalLayerSerialFaceTransitionSlotAt corridor hunique offset hcell
          (coordinate.symm coordinateIndex) := by
    rw [← hslotDart (coordinate.symm coordinateIndex)]
    simp
  have hconnectedIff :
      SourceLocalLayerSerialFaceFinitePredecessorConnected state code left right ↔
        (faceRegionalDartGraph web.annular.RS oldRegion).Reachable
          (coordinate.symm left).1 (coordinate.symm right).1 := by
    unfold SourceLocalLayerSerialFaceFinitePredecessorConnected
    rw [hslot left, hslot right]
    exact
      sourceLocalLayerSerialFacePrefixAttachmentStateAt_factoredReachability_iff
        corridor hunique offset hcell (coordinate.symm left)
          (coordinate.symm right)
  have hnotOldReachable :
      ¬ (faceRegionalDartGraph web.annular.RS oldRegion).Reachable
        (coordinate.symm left).1 (coordinate.symm right).1 :=
    fun hreachable => hnotConnected (hconnectedIff.2 hreachable)
  have hleftOutputReachable :
      (faceRegionalDartGraph web.annular.RS outputRegion).Reachable
        outputDart.1 (coordinate.symm left).1 := by
    apply (sourceLocalLayerSerialPreRebaseFaceDartReachable_iff_finiteClosure
      corridor hunique offset hcell outputDart (coordinate.symm left)).2
    simpa [output, outputDart, state, code, coordinate, carrier] using
      hleftData.2
  have hrightOutputReachable :
      (faceRegionalDartGraph web.annular.RS outputRegion).Reachable
        outputDart.1 (coordinate.symm right).1 := by
    apply (sourceLocalLayerSerialPreRebaseFaceDartReachable_iff_finiteClosure
      corridor hunique offset hcell outputDart (coordinate.symm right)).2
    simpa [output, outputDart, state, code, coordinate, carrier] using
      hrightData.2
  have hleftFace := faceRegionalDartGraph_reachable_dartOrbitFace_eq
    web.annular.RS outputRegion hleftOutputReachable
  have hrightFace := faceRegionalDartGraph_reachable_dartOrbitFace_eq
    web.annular.RS outputRegion hrightOutputReachable
  have houtputFace : dartOrbitFace web.annular.RS outputDart.1 = fragment.1.1 := by
    simp only [outputDart,
      sourceLocalLayerSerialFaceOutputFragmentTransitionDartAt,
      boundaryRegionalFragmentDartOccurrence]
    rw [dartOrbitFace_faceCycleDart, dartOrbitFace_orbitFaceRoot]
  have houtputInterior : dartOrbitFace web.annular.RS outputDart.1 ∈
      web.annular.cellulation.interiorFaces := by
    rw [houtputFace]
    exact sourceLocalLayerSerialFaceOutputFragment_face_mem_interiorFaces
      corridor hunique offset fragment
  apply sourceLocalLayerBoundaryRebaseFaceComponentEdges_disjoint_of_same_interior_face
    web oldRegion
  · exact hleftFace.symm.trans hrightFace
  · exact hleftFace ▸ houtputInterior
  · exact hnotOldReachable

/-- Literal old-prefix edge support contributed to one outgoing fragment,
formed as the union of its canonical predecessor components. -/
noncomputable def sourceLocalLayerSerialFaceOldComponentEdgesAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (fragment : SourceLocalLayerSerialFaceOutputFragmentAt corridor hunique
      offset) : Finset G.edgeSet := by
  classical
  let carrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
    offset
  let coordinate := carrierCoordinate carrier
  let code := sourceLocalLayerSerialFaceTransitionCodeAt corridor hunique offset
    hcell
  let state := sourceLocalLayerSerialFacePrefixAttachmentStateAt corridor
    hunique offset hcell
  let semantic := sourceLocalLayerSerialFaceFinitePredecessorSemanticAt corridor
    hunique offset hcell
  let output := coordinate
    (sourceLocalLayerSerialFaceOutputFragmentTransitionDartAt corridor hunique
      offset fragment)
  let oldRegion := sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
    offset
  exact (sourceLocalLayerSerialFaceFiniteContributingPredecessors state code
    semantic output).biUnion fun representative =>
      sourceLocalLayerBoundaryRebaseFaceComponentEdges web.annular.RS oldRegion
        (coordinate.symm representative).1

/-- The old-component union is cardinality-additive because its canonical
predecessor components are pairwise edge-disjoint. -/
theorem sourceLocalLayerSerialFaceOldComponentEdgesAt_card
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (fragment : SourceLocalLayerSerialFaceOutputFragmentAt corridor hunique
      offset) :
    let carrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor
      hunique offset
    let coordinate := carrierCoordinate carrier
    let code := sourceLocalLayerSerialFaceTransitionCodeAt corridor hunique
      offset hcell
    let state := sourceLocalLayerSerialFacePrefixAttachmentStateAt corridor
      hunique offset hcell
    let semantic := sourceLocalLayerSerialFaceFinitePredecessorSemanticAt
      corridor hunique offset hcell
    let output := coordinate
      (sourceLocalLayerSerialFaceOutputFragmentTransitionDartAt corridor hunique
        offset fragment)
    (sourceLocalLayerSerialFaceOldComponentEdgesAt corridor hunique offset hcell
      fragment).card =
      ∑ representative ∈
        sourceLocalLayerSerialFaceFiniteContributingPredecessors state code
          semantic output,
        (sourceLocalLayerBoundaryRebaseFaceComponentEdges web.annular.RS
          (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
          (coordinate.symm representative).1).card := by
  dsimp only
  let carrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
    offset
  let coordinate := carrierCoordinate carrier
  let code := sourceLocalLayerSerialFaceTransitionCodeAt corridor hunique offset
    hcell
  let state := sourceLocalLayerSerialFacePrefixAttachmentStateAt corridor
    hunique offset hcell
  let semantic := sourceLocalLayerSerialFaceFinitePredecessorSemanticAt corridor
    hunique offset hcell
  let output := coordinate
    (sourceLocalLayerSerialFaceOutputFragmentTransitionDartAt corridor hunique
      offset fragment)
  unfold sourceLocalLayerSerialFaceOldComponentEdgesAt
  apply Finset.card_biUnion
  intro left hleft right hright hne
  exact sourceLocalLayerSerialFaceFiniteContributingPredecessor_componentEdges_disjoint
    corridor hunique offset hcell fragment hleft hright hne

/-- The graph-free predecessor cap sum is exactly the cap at five of the
literal disjoint old-component union. -/
theorem sourceLocalLayerSerialFaceFinitePredecessorCapSum_eq_oldComponentEdges
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (fragment : SourceLocalLayerSerialFaceOutputFragmentAt corridor hunique
      offset) :
    let carrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor
      hunique offset
    let coordinate := carrierCoordinate carrier
    let code := sourceLocalLayerSerialFaceTransitionCodeAt corridor hunique
      offset hcell
    let state := sourceLocalLayerSerialFacePrefixAttachmentStateAt corridor
      hunique offset hcell
    let semantic := sourceLocalLayerSerialFaceFinitePredecessorSemanticAt
      corridor hunique offset hcell
    let output := coordinate
      (sourceLocalLayerSerialFaceOutputFragmentTransitionDartAt corridor hunique
        offset fragment)
    sourceLocalLayerSerialFaceFinitePredecessorCapSum state code semantic output =
      min (sourceLocalLayerSerialFaceOldComponentEdgesAt corridor hunique offset
        hcell fragment).card 5 := by
  dsimp only
  let carrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
    offset
  let coordinate := carrierCoordinate carrier
  let code := sourceLocalLayerSerialFaceTransitionCodeAt corridor hunique offset
    hcell
  let state := sourceLocalLayerSerialFacePrefixAttachmentStateAt corridor
    hunique offset hcell
  let semantic := sourceLocalLayerSerialFaceFinitePredecessorSemanticAt corridor
    hunique offset hcell
  let output := coordinate
    (sourceLocalLayerSerialFaceOutputFragmentTransitionDartAt corridor hunique
      offset fragment)
  let contributors :=
    sourceLocalLayerSerialFaceFiniteContributingPredecessors state code semantic
      output
  unfold sourceLocalLayerSerialFaceFinitePredecessorCapSum
  rw [sourceLocalLayerSerialFaceOldComponentEdgesAt_card corridor hunique offset
    hcell fragment]
  apply GoertzelV24CorridorSpliceObservables.min_sum_eq_of_pointwise_min_eq
  intro representative hrepresentative
  have hcap :=
    sourceLocalLayerSerialFaceFinitePredecessor_componentCap_val corridor
      hunique offset hcell representative
  have hcapLe :
      ((sourceLocalLayerSerialFacePrefixAttachmentStateAt corridor hunique
        offset hcell).componentCap
        (sourceLocalLayerSerialFaceFiniteStableSlot
          (sourceLocalLayerSerialFaceTransitionCodeAt corridor hunique offset
            hcell) representative)).val ≤ 5 :=
    Nat.le_of_lt_succ ((sourceLocalLayerSerialFacePrefixAttachmentStateAt
      corridor hunique offset hcell).componentCap
        (sourceLocalLayerSerialFaceFiniteStableSlot
          (sourceLocalLayerSerialFaceTransitionCodeAt corridor hunique offset
            hcell) representative)).isLt
  rw [Nat.min_eq_left hcapLe]
  exact hcap

end

end GoertzelV24ClosedWebLocalLayerSerialCellFaceFinitePredecessorDisjoint

end Mettapedia.GraphTheory.FourColor
