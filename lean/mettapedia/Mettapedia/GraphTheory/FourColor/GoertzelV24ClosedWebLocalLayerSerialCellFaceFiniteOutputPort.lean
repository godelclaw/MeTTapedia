import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteOutputFragment
import Mettapedia.GraphTheory.FourColor.GoertzelV24WidthTwoPortIncidenceCompression
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFullProfileRelation

/-!
# Finite outgoing port incidence for one source Cell

The outgoing regional fragments and the two literal dart occurrences of each
displayed port edge all lie in the common twenty-four-slot facial carrier.
This file proves that actual fragment/port incidence is exactly the existence
of one of those two port coordinates in the graph-free Cell closure.

The proof is occurrence-sensitive and remains valid on a one-sided opened
carrier.  It does not identify ambient orbit faces, compute distinct-edge
component caps, or claim a complete one-Cell support letter.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteOutputPort

open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationAllFaceCutProfile
open GoertzelV24RotationFaceFragments
open GoertzelV24RotationFaceRegionalDartGraph
open GoertzelV24TerminalProfileFaceUpdate
open GoertzelV24WidthTwoPortIncidenceCompression
open SimpleGraphDartRotation

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

theorem edge_mem_boundaryRegionalFragmentEdges_iff_exists_dart_reachable
    (RS : RotationSystem V E) (cut region : Finset E)
    (fragment : BoundaryRegionalFragment RS cut region) (edge : E)
    (hedgeRegion : edge ∈ region) :
    edge ∈ boundaryRegionalFragmentEdges RS cut region fragment ↔
      ∃ dart : {dart : RS.D // dart ∈ RS.dartsOn edge},
        (faceRegionalDartGraph RS region).Reachable dart.1
          (boundaryRegionalFragmentDartOccurrence RS cut region fragment).1 := by
  constructor
  · intro hedge
    let root := orbitFaceRoot RS fragment.1.1
    let witness : { fragment : BoundaryRegionalFragment RS cut region //
        edge ∈ boundaryRegionalFragmentEdges RS cut region fragment } :=
      ⟨fragment, hedge⟩
    let position := boundaryRegionalFragmentEdgePosition RS cut region edge witness
    let canonical := boundaryRegionalFragmentCutPosition RS cut region fragment
    rcases (mem_faceRegionalFragmentPositions_iff RS root region fragment.2.1
      position).1 (by
        simpa [root, position, witness] using
          boundaryRegionalFragmentEdgePosition_mem RS cut region edge witness) with
      ⟨leftRegional, hleftSupp, hleftPosition⟩
    rcases (mem_faceRegionalFragmentPositions_iff RS root region fragment.2.1
      canonical).1 (by
        simpa [root, canonical] using
          boundaryRegionalFragmentCutPosition_mem RS cut region fragment) with
      ⟨rightRegional, hrightSupp, hrightPosition⟩
    have hregional := faceRegionalFragment_reachable RS root region fragment.2.1
      hleftSupp hrightSupp
    have hambient :=
      (faceRegionalPositionGraph_reachable_iff_ambient RS root region
        leftRegional rightRegional).1 hregional
    have hinduced :=
      (faceRegionalAmbientPositionGraph_reachable_iff_dartOrbit RS root region
        position canonical).1 (by
          simpa [hleftPosition, hrightPosition] using hambient)
    have hdart :=
      (faceRegionalDartGraph_reachable_iff_induce_faceOrbit RS root region
        (faceCycleDartOrbitEquiv RS root position)
        (faceCycleDartOrbitEquiv RS root canonical)).2 hinduced
    refine ⟨boundaryRegionalFragmentEdgeDart RS cut region edge witness, ?_⟩
    simpa [root, position, canonical, witness,
      boundaryRegionalFragmentEdgeDart,
      boundaryRegionalFragmentDartOccurrence] using hdart
  · rintro ⟨dart, hreachable⟩
    let root := orbitFaceRoot RS fragment.1.1
    have hface := faceRegionalDartGraph_reachable_dartOrbitFace_eq RS region
      hreachable
    have hcanonicalFace :
        dartOrbitFace RS
            (boundaryRegionalFragmentDartOccurrence RS cut region fragment).1 =
          fragment.1.1 := by
      simpa [boundaryRegionalFragmentDartOccurrence, root] using
        (dartOrbitFace_faceCycleDart RS root
          (boundaryRegionalFragmentCutPosition RS cut region fragment)).trans
            (dartOrbitFace_orbitFaceRoot RS fragment.1.1)
    have hdartOrbit : dart.1 ∈ RS.faceOrbit root := by
      rw [← orbitFaceDarts_dartOrbitFace_eq_faceOrbit RS root,
        mem_orbitFaceDarts_iff]
      exact hface.trans hcanonicalFace |>.trans
        (dartOrbitFace_orbitFaceRoot RS fragment.1.1).symm
    let dartInOrbit : ↑(RS.faceOrbit root) := ⟨dart.1, hdartOrbit⟩
    let position := (faceCycleDartOrbitEquiv RS root).symm dartInOrbit
    let canonical := boundaryRegionalFragmentCutPosition RS cut region fragment
    have hinduced :=
      (faceRegionalDartGraph_reachable_iff_induce_faceOrbit RS root region
        dartInOrbit (faceCycleDartOrbitEquiv RS root canonical)).1 (by
          simpa [dartInOrbit, canonical, root,
            boundaryRegionalFragmentDartOccurrence] using hreachable)
    have hambient :=
      (faceRegionalAmbientPositionGraph_reachable_iff_dartOrbit RS root region
        position canonical).2 (by
          simpa [position] using hinduced)
    have hpositionEdge : faceCycleEdge RS root position = edge := by
      have hdartValue : faceCycleDart RS root position = dart.1 := by
        exact congrArg Subtype.val
          ((faceCycleDartOrbitEquiv RS root).apply_symm_apply dartInOrbit)
      change RS.edgeOf (faceCycleDart RS root position) = edge
      rw [hdartValue]
      exact (RS.mem_dartsOn).1 dart.2
    let leftRegional : FaceRegionalPosition RS root region :=
      ⟨position, (mem_faceRegionalPositions_iff RS root region position).2
        (hpositionEdge ▸ hedgeRegion)⟩
    rcases (mem_faceRegionalFragmentPositions_iff RS root region fragment.2.1
      canonical).1 (by
        simpa [root, canonical] using
          boundaryRegionalFragmentCutPosition_mem RS cut region fragment) with
      ⟨rightRegional, hrightSupp, hrightPosition⟩
    have hregional : (faceRegionalPositionGraph RS root region).Reachable
        leftRegional rightRegional :=
      (faceRegionalPositionGraph_reachable_iff_ambient RS root region
        leftRegional rightRegional).2 (by
          simpa [leftRegional, hrightPosition] using hambient)
    have hleftSupp : leftRegional ∈ fragment.2.1.supp := by
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
      exact (SimpleGraph.ConnectedComponent.sound hregional).trans
        ((SimpleGraph.ConnectedComponent.mem_supp_iff fragment.2.1
          rightRegional).1 hrightSupp)
    rw [boundaryRegionalFragmentEdges,
      mem_faceRegionalFragmentEdges_iff]
    exact ⟨position,
      (mem_faceRegionalFragmentPositions_iff RS root region fragment.2.1
        position).2 ⟨leftRegional, hleftSupp, rfl⟩,
      hpositionEdge⟩

end


open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteClosure
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteOutputFragment
open GoertzelV24FaceOrbitIncidence
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationAllFaceCutProfile
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationFaceRegionalDartCarrier
open GoertzelV24RotationFaceRegionalDartGraph
open GoertzelV24WidthTwoPortIncidenceCompression
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

local instance closedWebLocalLayerSerialCellFaceFiniteOutputPortEdgeSetDecidableEq :
    DecidableEq G.edgeSet := Subtype.instDecidableEq

/-- The two literal dart occurrences over one outgoing port edge. -/
noncomputable def sourceLocalLayerSerialFaceOutputPortDartEquivAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) (port : Fin 2) :
    Fin 2 ≃ {dart : web.annular.RS.D //
      dart ∈ web.annular.RS.dartsOn
        (sourceLocalLayerRightCrossingAt corridor hunique offset port)} :=
  let darts := {dart : web.annular.RS.D //
    dart ∈ web.annular.RS.dartsOn
      (sourceLocalLayerRightCrossingAt corridor hunique offset port)}
  let hcard : Fintype.card darts = 2 := by
    rw [Fintype.card_coe]
    exact web.annular.RS.dartsOn_card_two
      (sourceLocalLayerRightCrossingAt corridor hunique offset port)
  ((Fintype.equivFin darts).trans (finCongr hcard)).symm

/-- One indexed outgoing port occurrence in the common transition carrier. -/
noncomputable def sourceLocalLayerSerialFaceOutputPortTransitionDartAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) (port side : Fin 2) :
    {dart // dart ∈
      sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset} :=
  let occurrence := sourceLocalLayerSerialFaceOutputPortDartEquivAt corridor
    hunique offset port side
  have hedge : web.annular.RS.edgeOf occurrence.1 ∈
      indexedCrossingEdgeSet
        (sourceLocalLayerRightCrossingAt corridor hunique offset) := by
    apply (mem_indexedCrossingEdgeSet_iff _ _).2
    refine ⟨port, ?_⟩
    exact ((web.annular.RS.mem_dartsOn).1 occurrence.2).symm
  ⟨occurrence.1, Finset.mem_union_right _
    (mem_closedDartCarrier_of_edge_mem web.annular.RS _ occurrence.1 hedge)⟩

/-- The finite port-incidence predicate decoded from the two literal port
occurrences and the graph-free Cell closure. -/
def SourceLocalLayerSerialFaceOutputFragmentContainsPortFinite
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcellBound :
      (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (fragment : SourceLocalLayerSerialFaceOutputFragmentAt corridor hunique
      offset) (port : Fin 2) : Prop :=
  ∃ side : Fin 2,
    Relation.ReflTransGen
      (SourceLocalLayerSerialFaceFiniteComponentStep
        (sourceLocalLayerSerialFacePrefixAttachmentStateAt corridor hunique
          offset hcellBound)
        (sourceLocalLayerSerialFaceTransitionCodeAt corridor hunique offset
          hcellBound))
      (carrierCoordinate
        (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset)
        (sourceLocalLayerSerialFaceOutputPortTransitionDartAt corridor hunique
          offset port side))
      (carrierCoordinate
        (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset)
        (sourceLocalLayerSerialFaceOutputFragmentTransitionDartAt corridor
          hunique offset fragment))

theorem sourceLocalLayerSerialFaceOutputFragmentContainsPortFinite_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcellBound :
      (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (fragment : SourceLocalLayerSerialFaceOutputFragmentAt corridor hunique
      offset) (port : Fin 2) :
    SourceLocalLayerSerialFaceOutputFragmentContainsPortFinite corridor hunique
        offset hcellBound fragment port ↔
      sourceLocalLayerRightCrossingAt corridor hunique offset port ∈
        boundaryRegionalFragmentEdges web.annular.RS
          (indexedCrossingEdgeSet
            (sourceLocalLayerRightCrossingAt corridor hunique offset))
          (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique
            offset) fragment := by
  let edge := sourceLocalLayerRightCrossingAt corridor hunique offset port
  let cut := indexedCrossingEdgeSet
    (sourceLocalLayerRightCrossingAt corridor hunique offset)
  let region := sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique
    offset
  have hedgeRegion : edge ∈ region := by
    change sourceLocalLayerRightCrossingAt corridor hunique offset port ∈
      sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset
    rw [← sourceLocalLayerSerialTerminalInputRegionAt_union_cell corridor
      hunique offset]
    exact Finset.mem_union_right _
      (sourceLocalLayerCellRegionAt_rightCrossing corridor hunique offset port)
  rw [edge_mem_boundaryRegionalFragmentEdges_iff_exists_dart_reachable
    web.annular.RS cut region fragment edge hedgeRegion]
  constructor
  · rintro ⟨side, hfinite⟩
    let dart := sourceLocalLayerSerialFaceOutputPortDartEquivAt corridor hunique
      offset port side
    refine ⟨dart, ?_⟩
    exact (sourceLocalLayerSerialPreRebaseFaceDartReachable_iff_finiteClosure
      corridor hunique offset hcellBound
      (sourceLocalLayerSerialFaceOutputPortTransitionDartAt corridor hunique
        offset port side)
      (sourceLocalLayerSerialFaceOutputFragmentTransitionDartAt corridor
        hunique offset fragment)).2 (by
          simpa [SourceLocalLayerSerialFaceOutputFragmentContainsPortFinite]
            using hfinite)
  · rintro ⟨dart, hreachable⟩
    let side := sourceLocalLayerSerialFaceOutputPortDartEquivAt corridor hunique
      offset port |>.symm dart
    refine ⟨side, ?_⟩
    have hfinite :=
      (sourceLocalLayerSerialPreRebaseFaceDartReachable_iff_finiteClosure
        corridor hunique offset hcellBound
        (sourceLocalLayerSerialFaceOutputPortTransitionDartAt corridor hunique
          offset port side)
        (sourceLocalLayerSerialFaceOutputFragmentTransitionDartAt corridor
          hunique offset fragment)).1 ?_
    · exact hfinite
    · simpa [side, sourceLocalLayerSerialFaceOutputPortTransitionDartAt] using
        hreachable

/-- The finite port-incidence predicate is exactly the corresponding Boolean
coordinate of the actual graph-derived outgoing profile. -/
theorem sourceLocalLayerSerialFaceOutputFragmentContainsPortFinite_iff_profile
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcellBound :
      (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (color : G.edgeSet → Color)
    (hcolor : ∀ port : Fin 2,
      color (sourceLocalLayerRightCrossingAt corridor hunique offset port) ≠ 0)
    (fragment : Fin (Fintype.card
      (SourceLocalLayerSerialFaceOutputFragmentAt corridor hunique offset)))
    (port : Fin 2) :
    SourceLocalLayerSerialFaceOutputFragmentContainsPortFinite corridor hunique
        offset hcellBound
        (boundaryRegionalFragmentAt web.annular.RS
          (indexedCrossingEdgeSet
            (sourceLocalLayerRightCrossingAt corridor hunique offset))
          (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique
            offset) fragment) port ↔
      ((sourceLocalLayerSerialPreRebaseOutputCutDataAt corridor hunique offset
          ).regionalProfile color hcolor).fragmentContainsPort fragment
            (.inl port) = true := by
  rw [sourceLocalLayerSerialFaceOutputFragmentContainsPortFinite_iff]
  rw [GraphCorridorCutData.regionalProfile_fragmentContainsPort_eq_true_iff]
  rw [(sourceLocalLayerSerialPreRebaseOutputCutDataAt corridor hunique offset)
    |>.regionalFragmentEdges_eq_of_fragmentsOnFaceInRegion
      (sourceLocalLayerSerialPreRebaseOutputCutDataAt_fragmentsOnFaceInRegion
        corridor hunique offset)]
  rfl

end GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteOutputPort

end Mettapedia.GraphTheory.FourColor
