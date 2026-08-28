import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedFaceFiniteNewEdgeAdequacy
import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutLayerSeparation

/-!
# Local simplicity for predecessor contributions of one source Cell

An outgoing source-Cell face fragment meets one of the two crossings of the
second literal layer.  Hence its ambient face occurs in that layer walk and,
by boundary cleanliness of the corridor, is an annular-interior face.  This
local fact is the replacement for a false global two-sidedness assumption on
the opened carrier.

The predecessor cap decoder then shows that distinct old components
contributing to one output fragment have disjoint primal-edge supports and
identifies their finite capped sum with the literal old-edge union.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebPointwiseSelectedFaceFinitePredecessorDisjoint

open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Formation
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteClosure
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteOutputCap
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteOutputFragment
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFinitePredecessorRepresentatives
open GoertzelV24ClosedWebPointwiseSelectedFaceFiniteClosure
open GoertzelV24ClosedWebPointwiseSelectedFaceFiniteOutputFragment
open GoertzelV24ClosedWebPointwiseSelectedFaceFiniteRepresentatives
open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24FaceOrbitIncidence
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationAllFaceCutProfile
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationFaceRegionalDartGraph
open GoertzelV24SelectedDualPathTransversal
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance pointwiseSelectedFaceFinitePredecessorDisjointEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Every actual outgoing fragment of a literal source Cell lies on an
annular-interior face.  The proof follows its canonical cut edge into the
second local layer; no global two-sidedness property is used. -/
theorem pointwiseSelectedSourceLocalLayerSerialFaceOutputFragment_face_mem_interiorFaces
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (fragment : PointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentAt formation corridor hinterior
      offset) :
    fragment.1.1 ∈ formation.annular.cellulation.interiorFaces := by
  let layers := pointwiseSelectedSourceLocalLayerPairAt formation corridor
    hinterior offset
  let pair := layers.pointwiseSelectedLocalLayerPair hinterior
  let cut := indexedCrossingEdgeSet
    (pointwiseSelectedSourceLocalLayerRightCrossingAt formation corridor
      hinterior offset)
  let region :=
    pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt formation
      corridor hinterior offset
  let edge := boundaryRegionalFragmentCutEdge formation.annular.RS cut region
    fragment
  have hedgeCut : edge ∈ cut :=
    boundaryRegionalFragmentCutEdge_mem_cut formation.annular.RS cut region
      fragment
  rcases (mem_indexedCrossingEdgeSet_iff
    (pointwiseSelectedSourceLocalLayerRightCrossingAt formation corridor
      hinterior offset) edge).1 hedgeCut with
    ⟨step, hstep⟩
  let secondStep : Fin pair.right.crosscut.walk.length :=
    ⟨step.val, by
      simpa [pair, Formation.LocalLayerPair.pointwiseSelectedLocalLayerPair,
        Formation.LocalLayerPair.pointwiseSelectedSecondLayer,
        Formation.LocalLayerPair.secondLayer,
        Formation.LocalLayerPair.secondWalk] using step.isLt⟩
  have hedgeCrossing : pair.right.crossingEdge secondStep = edge := by
    simpa [pointwiseSelectedSourceLocalLayerRightCrossingAt, layers, pair,
      secondStep, Formation.LocalLayerPair.pointwiseSelectedLocalLayerPair,
      Formation.LocalLayerPair.pointwiseSelectedSecondLayer,
      Formation.LocalLayerPair.secondLayer,
      Formation.LocalLayerPair.secondWalk] using hstep
  have hedgeFragment : edge ∈
      boundaryRegionalFragmentEdges formation.annular.RS cut region fragment :=
    boundaryRegionalFragmentCutEdge_mem_fragment formation.annular.RS cut region
      fragment
  have hedgeFace : edge ∈ orbitFaceBoundary formation.annular.RS fragment.1.1 :=
    (Finset.mem_inter.mp
      (boundaryRegionalFragmentEdges_subset_boundary_inter_region
        formation.annular.RS cut region fragment hedgeFragment)).1
  let leftFace := pair.right.crosscut.walk.getVert secondStep.val
  let rightFace := pair.right.crosscut.walk.getVert (secondStep.val + 1)
  have hleftFace : edge ∈ orbitFaceBoundary formation.annular.RS leftFace.1 := by
    rw [← hedgeCrossing]
    exact pair.right.crossingEdge_mem_leftFace secondStep
  have hrightFace : edge ∈ orbitFaceBoundary formation.annular.RS rightFace.1 := by
    rw [← hedgeCrossing]
    exact pair.right.crossingEdge_mem_rightFace secondStep
  have hfacesNe : leftFace.1 ≠ rightFace.1 := by
    intro hfaces
    exact (pair.right.crosscut.walk.adj_getVert_succ secondStep.isLt).ne
      (Subtype.ext hfaces)
  have hcases :=
    eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
      (orbitFaceBoundary formation.annular.RS)
      (Finset.univ : Finset (OrbitFace formation.annular.RS))
      (orbitFace_incidence_le_two formation.annular.RS) leftFace.2 rightFace.2
      (Finset.mem_univ fragment.1.1) hfacesNe hleftFace hrightFace hedgeFace
  have hwalk : pair.right.crosscut.walk = layers.secondWalk := by
    rfl
  have hleftInterior : leftFace.1 ∈
      formation.annular.cellulation.interiorFaces := by
    have hindex : secondStep.val < layers.secondWalk.length + 1 := by
      have hlt : secondStep.val < layers.secondWalk.length := by
        simpa [hwalk] using secondStep.isLt
      omega
    have hinteriorLeft := layers.secondWalk_getVert_internal
      ⟨secondStep.val, hindex⟩
    simpa [leftFace, pair,
      Formation.LocalLayerPair.pointwiseSelectedLocalLayerPair,
      Formation.LocalLayerPair.pointwiseSelectedSecondLayer,
      Formation.LocalLayerPair.secondLayer] using hinteriorLeft
  have hrightInterior : rightFace.1 ∈
      formation.annular.cellulation.interiorFaces := by
    have hindex : secondStep.val + 1 < layers.secondWalk.length + 1 := by
      have hlt : secondStep.val < layers.secondWalk.length := by
        simpa [hwalk] using secondStep.isLt
      omega
    have hinteriorRight := layers.secondWalk_getVert_internal
      ⟨secondStep.val + 1, hindex⟩
    simpa [rightFace, pair,
      Formation.LocalLayerPair.pointwiseSelectedLocalLayerPair,
      Formation.LocalLayerPair.pointwiseSelectedSecondLayer,
      Formation.LocalLayerPair.secondLayer] using hinteriorRight
  rcases hcases with hleft | hright
  · rw [hleft]
    exact hleftInterior
  · rw [hright]
    exact hrightInterior

/-- Two disconnected regional components on the same annular-interior face
have disjoint primal-edge supports.  Boundary simplicity is used only for the
one face in question; the opened carrier need not be globally two-sided. -/
theorem pointwiseSelectedSourceLocalLayerBoundaryRebaseFaceComponentEdges_disjoint_of_same_interior_face
    {data : AnnularBoundaryData G 5}
    (formation : Formation data) (region : Finset G.edgeSet)
    {left right : formation.annular.RS.D}
    (hsameFace : dartOrbitFace formation.annular.RS left =
      dartOrbitFace formation.annular.RS right)
    (hface : dartOrbitFace formation.annular.RS left ∈
      formation.annular.cellulation.interiorFaces)
    (hnotReachable : ¬ (faceRegionalDartGraph formation.annular.RS region).Reachable
      left right) :
    Disjoint
      (sourceLocalLayerBoundaryRebaseFaceComponentEdges formation.annular.RS region
        left)
      (sourceLocalLayerBoundaryRebaseFaceComponentEdges formation.annular.RS region
        right) := by
  classical
  rw [Finset.disjoint_left]
  intro edge hleftEdge hrightEdge
  rcases (mem_sourceLocalLayerBoundaryRebaseFaceComponentEdges_iff
      formation.annular.RS region left edge).1 hleftEdge with
    ⟨_leftRegion, leftDart, hleftReachable⟩
  rcases (mem_sourceLocalLayerBoundaryRebaseFaceComponentEdges_iff
      formation.annular.RS region right edge).1 hrightEdge with
    ⟨_rightRegion, rightDart, hrightReachable⟩
  have hleftDartFace :=
    faceRegionalDartGraph_reachable_dartOrbitFace_eq formation.annular.RS region
      hleftReachable
  have hrightDartFace :=
    faceRegionalDartGraph_reachable_dartOrbitFace_eq formation.annular.RS region
      hrightReachable
  have hinjective : Set.InjOn formation.annular.RS.edgeOf
      (orbitFaceDarts formation.annular.RS
        (dartOrbitFace formation.annular.RS left)) := by
    apply Finset.card_image_iff.mp
    exact Formation.InteriorFace.boundary_card_eq_darts_card formation left hface
  have hleftDartMem : leftDart.1 ∈ orbitFaceDarts formation.annular.RS
      (dartOrbitFace formation.annular.RS left) :=
    (mem_orbitFaceDarts_iff formation.annular.RS
      (dartOrbitFace formation.annular.RS left) leftDart.1).2 hleftDartFace.symm
  have hrightDartMem : rightDart.1 ∈ orbitFaceDarts formation.annular.RS
      (dartOrbitFace formation.annular.RS left) :=
    (mem_orbitFaceDarts_iff formation.annular.RS
      (dartOrbitFace formation.annular.RS left) rightDart.1).2
        ((hsameFace.trans hrightDartFace).symm)
  have hleftEdgeOf : formation.annular.RS.edgeOf leftDart.1 = edge :=
    (formation.annular.RS.mem_dartsOn).1 leftDart.2
  have hrightEdgeOf : formation.annular.RS.edgeOf rightDart.1 = edge :=
    (formation.annular.RS.mem_dartsOn).1 rightDart.2
  have hdarts : leftDart.1 = rightDart.1 :=
    hinjective hleftDartMem hrightDartMem
      (hleftEdgeOf.trans hrightEdgeOf.symm)
  apply hnotReachable
  exact hleftReachable.trans (hdarts ▸ hrightReachable.symm)

/-- The cap stored at any live finite predecessor coordinate is exactly the
cap at five of that coordinate's literal predecessor-component edge support. -/
theorem pointwiseSelectedSourceLocalLayerSerialFaceFinitePredecessor_componentCap_eq
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor hinterior offset).card ≤ 6) :
    let carrier := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation corridor
      hinterior offset
    let coordinate := carrierCoordinate carrier
    let code := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCodeAt formation corridor hinterior
      offset hcell
    let state := pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt formation corridor
      hinterior offset hcell
    ∀ coordinateIndex : Fin code.vertexCount.val,
      state.componentCap
          (sourceLocalLayerSerialFaceFiniteStableSlot code coordinateIndex) =
        ⟨min (sourceLocalLayerBoundaryRebaseFaceComponentEdges formation.annular.RS
            (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation corridor hinterior offset)
            (coordinate.symm coordinateIndex).1).card 5,
          Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩ := by
  dsimp only
  intro coordinateIndex
  let carrier := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation corridor hinterior
    offset
  let coordinate := carrierCoordinate carrier
  let code := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCodeAt formation corridor hinterior offset
    hcell
  let state := pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt formation corridor
    hinterior offset hcell
  have hslotDart (dart : {dart // dart ∈ carrier}) :
      sourceLocalLayerSerialFaceFiniteStableSlot code (coordinate dart) =
        pointwiseSelectedSourceLocalLayerSerialFaceTransitionSlotAt formation corridor hinterior offset hcell
          dart := by
    rfl
  have hslot :
      sourceLocalLayerSerialFaceFiniteStableSlot code coordinateIndex =
        pointwiseSelectedSourceLocalLayerSerialFaceTransitionSlotAt formation corridor hinterior offset hcell
          (coordinate.symm coordinateIndex) := by
    rw [← hslotDart (coordinate.symm coordinateIndex)]
    simp
  rw [hslot]
  exact
    pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt_componentCap
      formation corridor hinterior offset hcell
        (coordinate.symm coordinateIndex)

/-- Value form of the exact predecessor-cap theorem, ready for the finite
representative sum. -/
theorem pointwiseSelectedSourceLocalLayerSerialFaceFinitePredecessor_componentCap_val
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor hinterior offset).card ≤ 6) :
    let carrier := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation corridor
      hinterior offset
    let coordinate := carrierCoordinate carrier
    let code := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCodeAt formation corridor hinterior
      offset hcell
    let state := pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt formation corridor
      hinterior offset hcell
    ∀ coordinateIndex : Fin code.vertexCount.val,
      (state.componentCap
          (sourceLocalLayerSerialFaceFiniteStableSlot code coordinateIndex)).val =
        min (sourceLocalLayerBoundaryRebaseFaceComponentEdges formation.annular.RS
          (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation corridor hinterior offset)
          (coordinate.symm coordinateIndex).1).card 5 := by
  dsimp only
  intro coordinateIndex
  exact congrArg Fin.val
    (pointwiseSelectedSourceLocalLayerSerialFaceFinitePredecessor_componentCap_eq formation corridor
      hinterior offset hcell coordinateIndex)

/-- Distinct canonical predecessor components that contribute to one actual
outgoing fragment have disjoint old primal-edge supports.  This is the exact
non-overlap fact needed before their capped sizes may be added. -/
theorem pointwiseSelectedSourceLocalLayerSerialFaceFiniteContributingPredecessor_componentEdges_disjoint
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor hinterior offset).card ≤ 6)
    (fragment : PointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentAt formation corridor hinterior
      offset) :
    let carrier := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation corridor
      hinterior offset
    let coordinate := carrierCoordinate carrier
    let code := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCodeAt formation corridor hinterior
      offset hcell
    let state := pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt formation corridor
      hinterior offset hcell
    let semantic := pointwiseSelectedSourceLocalLayerSerialFaceFinitePredecessorSemanticAt
      formation corridor hinterior offset hcell
    let output := coordinate
      (pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentTransitionDartAt formation corridor hinterior
        offset fragment)
    ∀ {left right : Fin code.vertexCount.val},
      left ∈ sourceLocalLayerSerialFaceFiniteContributingPredecessors state
          code semantic output →
      right ∈ sourceLocalLayerSerialFaceFiniteContributingPredecessors state
          code semantic output →
      left ≠ right →
        Disjoint
          (sourceLocalLayerBoundaryRebaseFaceComponentEdges formation.annular.RS
            (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation corridor hinterior offset)
            (coordinate.symm left).1)
          (sourceLocalLayerBoundaryRebaseFaceComponentEdges formation.annular.RS
            (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation corridor hinterior offset)
            (coordinate.symm right).1) := by
  dsimp only
  intro left right hleft hright hne
  let carrier := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation corridor hinterior
    offset
  let coordinate := carrierCoordinate carrier
  let code := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCodeAt formation corridor hinterior offset
    hcell
  let state := pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt formation corridor
    hinterior offset hcell
  let semantic := pointwiseSelectedSourceLocalLayerSerialFaceFinitePredecessorSemanticAt formation corridor
    hinterior offset hcell
  let outputDart :=
    pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentTransitionDartAt formation corridor hinterior
      offset fragment
  let output := coordinate outputDart
  let oldRegion := pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation corridor hinterior
    offset
  let outputRegion := pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt formation corridor
    hinterior offset
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
        pointwiseSelectedSourceLocalLayerSerialFaceTransitionSlotAt formation corridor hinterior offset hcell
          dart := by
    rfl
  have hslot (coordinateIndex : Fin code.vertexCount.val) :
      sourceLocalLayerSerialFaceFiniteStableSlot code coordinateIndex =
        pointwiseSelectedSourceLocalLayerSerialFaceTransitionSlotAt formation corridor hinterior offset hcell
          (coordinate.symm coordinateIndex) := by
    rw [← hslotDart (coordinate.symm coordinateIndex)]
    simp
  have hconnectedIff :
      SourceLocalLayerSerialFaceFinitePredecessorConnected state code left right ↔
        (faceRegionalDartGraph formation.annular.RS oldRegion).Reachable
          (coordinate.symm left).1 (coordinate.symm right).1 := by
    unfold SourceLocalLayerSerialFaceFinitePredecessorConnected
    rw [hslot left, hslot right]
    exact
      pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt_factoredReachability_iff
        formation corridor hinterior offset hcell (coordinate.symm left)
          (coordinate.symm right)
  have hnotOldReachable :
      ¬ (faceRegionalDartGraph formation.annular.RS oldRegion).Reachable
        (coordinate.symm left).1 (coordinate.symm right).1 :=
    fun hreachable => hnotConnected (hconnectedIff.2 hreachable)
  have hcomponentStep :
      SourceLocalLayerSerialFaceFiniteComponentStep state code =
        PointwiseSelectedSourceLocalLayerSerialFaceFiniteComponentStep state
          code := by
    rfl
  have hleftOutputReachable :
      (faceRegionalDartGraph formation.annular.RS outputRegion).Reachable
        outputDart.1 (coordinate.symm left).1 := by
    apply (pointwiseSelectedSourceLocalLayerSerialPreRebaseFaceDartReachable_iff_finiteClosure
      formation corridor hinterior offset hcell outputDart (coordinate.symm left)).2
    have hleftFinite := hleftData.2
    rw [hcomponentStep] at hleftFinite
    simpa [output, outputDart, state, code, coordinate, carrier] using
      hleftFinite
  have hrightOutputReachable :
      (faceRegionalDartGraph formation.annular.RS outputRegion).Reachable
        outputDart.1 (coordinate.symm right).1 := by
    apply (pointwiseSelectedSourceLocalLayerSerialPreRebaseFaceDartReachable_iff_finiteClosure
      formation corridor hinterior offset hcell outputDart (coordinate.symm right)).2
    have hrightFinite := hrightData.2
    rw [hcomponentStep] at hrightFinite
    simpa [output, outputDart, state, code, coordinate, carrier] using
      hrightFinite
  have hleftFace := faceRegionalDartGraph_reachable_dartOrbitFace_eq
    formation.annular.RS outputRegion hleftOutputReachable
  have hrightFace := faceRegionalDartGraph_reachable_dartOrbitFace_eq
    formation.annular.RS outputRegion hrightOutputReachable
  have houtputFace : dartOrbitFace formation.annular.RS outputDart.1 = fragment.1.1 := by
    simp only [outputDart,
      pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentTransitionDartAt,
      boundaryRegionalFragmentDartOccurrence]
    rw [dartOrbitFace_faceCycleDart, dartOrbitFace_orbitFaceRoot]
  have houtputInterior : dartOrbitFace formation.annular.RS outputDart.1 ∈
      formation.annular.cellulation.interiorFaces := by
    rw [houtputFace]
    exact pointwiseSelectedSourceLocalLayerSerialFaceOutputFragment_face_mem_interiorFaces
      formation corridor hinterior offset fragment
  apply pointwiseSelectedSourceLocalLayerBoundaryRebaseFaceComponentEdges_disjoint_of_same_interior_face
    formation oldRegion
  · exact hleftFace.symm.trans hrightFace
  · exact hleftFace ▸ houtputInterior
  · exact hnotOldReachable

/-- Literal old-prefix edge support contributed to one outgoing fragment,
formed as the union of its canonical predecessor components. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialFaceOldComponentEdgesAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor hinterior offset).card ≤ 6)
    (fragment : PointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentAt formation corridor hinterior
      offset) : Finset G.edgeSet := by
  classical
  let carrier := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation corridor hinterior
    offset
  let coordinate := carrierCoordinate carrier
  let code := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCodeAt formation corridor hinterior offset
    hcell
  let state := pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt formation corridor
    hinterior offset hcell
  let semantic := pointwiseSelectedSourceLocalLayerSerialFaceFinitePredecessorSemanticAt formation corridor
    hinterior offset hcell
  let output := coordinate
    (pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentTransitionDartAt formation corridor hinterior
      offset fragment)
  let oldRegion := pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation corridor hinterior
    offset
  exact (sourceLocalLayerSerialFaceFiniteContributingPredecessors state code
    semantic output).biUnion fun representative =>
      sourceLocalLayerBoundaryRebaseFaceComponentEdges formation.annular.RS oldRegion
        (coordinate.symm representative).1

/-- The old-component union is cardinality-additive because its canonical
predecessor components are pairwise edge-disjoint. -/
theorem pointwiseSelectedSourceLocalLayerSerialFaceOldComponentEdgesAt_card
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor hinterior offset).card ≤ 6)
    (fragment : PointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentAt formation corridor hinterior
      offset) :
    let carrier := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation corridor
      hinterior offset
    let coordinate := carrierCoordinate carrier
    let code := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCodeAt formation corridor hinterior
      offset hcell
    let state := pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt formation corridor
      hinterior offset hcell
    let semantic := pointwiseSelectedSourceLocalLayerSerialFaceFinitePredecessorSemanticAt
      formation corridor hinterior offset hcell
    let output := coordinate
      (pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentTransitionDartAt formation corridor hinterior
        offset fragment)
    (pointwiseSelectedSourceLocalLayerSerialFaceOldComponentEdgesAt formation corridor hinterior offset hcell
      fragment).card =
      ∑ representative ∈
        sourceLocalLayerSerialFaceFiniteContributingPredecessors state code
          semantic output,
        (sourceLocalLayerBoundaryRebaseFaceComponentEdges formation.annular.RS
          (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation corridor hinterior offset)
          (coordinate.symm representative).1).card := by
  dsimp only
  let carrier := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation corridor hinterior
    offset
  let coordinate := carrierCoordinate carrier
  let code := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCodeAt formation corridor hinterior offset
    hcell
  let state := pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt formation corridor
    hinterior offset hcell
  let semantic := pointwiseSelectedSourceLocalLayerSerialFaceFinitePredecessorSemanticAt formation corridor
    hinterior offset hcell
  let output := coordinate
    (pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentTransitionDartAt formation corridor hinterior
      offset fragment)
  unfold pointwiseSelectedSourceLocalLayerSerialFaceOldComponentEdgesAt
  apply Finset.card_biUnion
  intro left hleft right hright hne
  exact pointwiseSelectedSourceLocalLayerSerialFaceFiniteContributingPredecessor_componentEdges_disjoint
    formation corridor hinterior offset hcell fragment hleft hright hne

/-- The graph-free predecessor cap sum is exactly the cap at five of the
literal disjoint old-component union. -/
theorem pointwiseSelectedSourceLocalLayerSerialFaceFinitePredecessorCapSum_eq_oldComponentEdges
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor hinterior offset).card ≤ 6)
    (fragment : PointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentAt formation corridor hinterior
      offset) :
    let carrier := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation corridor
      hinterior offset
    let coordinate := carrierCoordinate carrier
    let code := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCodeAt formation corridor hinterior
      offset hcell
    let state := pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt formation corridor
      hinterior offset hcell
    let semantic := pointwiseSelectedSourceLocalLayerSerialFaceFinitePredecessorSemanticAt
      formation corridor hinterior offset hcell
    let output := coordinate
      (pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentTransitionDartAt formation corridor hinterior
        offset fragment)
    sourceLocalLayerSerialFaceFinitePredecessorCapSum state code semantic output =
      min (pointwiseSelectedSourceLocalLayerSerialFaceOldComponentEdgesAt formation corridor hinterior offset
        hcell fragment).card 5 := by
  dsimp only
  let carrier := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation corridor hinterior
    offset
  let coordinate := carrierCoordinate carrier
  let code := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCodeAt formation corridor hinterior offset
    hcell
  let state := pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt formation corridor
    hinterior offset hcell
  let semantic := pointwiseSelectedSourceLocalLayerSerialFaceFinitePredecessorSemanticAt formation corridor
    hinterior offset hcell
  let output := coordinate
    (pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentTransitionDartAt formation corridor hinterior
      offset fragment)
  let contributors :=
    sourceLocalLayerSerialFaceFiniteContributingPredecessors state code semantic
      output
  unfold sourceLocalLayerSerialFaceFinitePredecessorCapSum
  rw [pointwiseSelectedSourceLocalLayerSerialFaceOldComponentEdgesAt_card formation corridor hinterior offset
    hcell fragment]
  apply GoertzelV24CorridorSpliceObservables.min_sum_eq_of_pointwise_min_eq
  intro representative hrepresentative
  have hcap :=
    pointwiseSelectedSourceLocalLayerSerialFaceFinitePredecessor_componentCap_val formation corridor
      hinterior offset hcell representative
  have hcapLe :
      ((pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt formation corridor hinterior
        offset hcell).componentCap
        (sourceLocalLayerSerialFaceFiniteStableSlot
          (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCodeAt formation corridor hinterior offset
            hcell) representative)).val ≤ 5 :=
    Nat.le_of_lt_succ ((pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt
      formation corridor hinterior offset hcell).componentCap
        (sourceLocalLayerSerialFaceFiniteStableSlot
          (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCodeAt formation corridor hinterior offset
            hcell) representative)).isLt
  rw [Nat.min_eq_left hcapLe]
  exact hcap

end

end GoertzelV24ClosedWebPointwiseSelectedFaceFinitePredecessorDisjoint

end Mettapedia.GraphTheory.FourColor
