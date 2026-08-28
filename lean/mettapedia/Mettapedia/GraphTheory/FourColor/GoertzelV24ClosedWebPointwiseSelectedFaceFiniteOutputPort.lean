import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteOutputPort
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedFaceFiniteOutputFragment

/-!
# Finite outgoing port incidence for a pointwise-selected Cell

The two literal dart occurrences over each selected outgoing edge lie in the
common twenty-four-slot facial carrier.  An outgoing fragment contains a port
exactly when one of those two coordinates reaches the fragment coordinate in
the finite closure.

The generic occurrence-sensitive edge-membership lemma is reused from the
existing regional-fragment development.  Every source-specific theorem here
uses only the pointwise-selected geometry and its interior-face uniqueness
receipt.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebPointwiseSelectedFaceFiniteOutputPort

open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Formation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteOutputPort
open GoertzelV24ClosedWebPointwiseSelectedFaceFiniteClosure
open GoertzelV24ClosedWebPointwiseSelectedFaceFiniteOutputFragment
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

noncomputable section

local instance pointwiseSelectedFaceFiniteOutputPortEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The two literal dart occurrences over one selected outgoing port edge. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialFaceOutputPortDartEquivAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) (port : Fin 2) :
    Fin 2 ≃ {dart : formation.annular.RS.D //
      dart ∈ formation.annular.RS.dartsOn
        (pointwiseSelectedSourceLocalLayerRightCrossingAt formation corridor
          hinterior offset port)} :=
  let darts := {dart : formation.annular.RS.D //
    dart ∈ formation.annular.RS.dartsOn
      (pointwiseSelectedSourceLocalLayerRightCrossingAt formation corridor
        hinterior offset port)}
  let hcard : Fintype.card darts = 2 := by
    rw [Fintype.card_coe]
    exact formation.annular.RS.dartsOn_card_two
      (pointwiseSelectedSourceLocalLayerRightCrossingAt formation corridor
        hinterior offset port)
  ((Fintype.equivFin darts).trans (finCongr hcard)).symm

/-- One indexed selected outgoing-port occurrence in the common transition
carrier. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialFaceOutputPortTransitionDartAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) (port side : Fin 2) :
    {dart // dart ∈
      pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation
        corridor hinterior offset} :=
  let occurrence :=
    pointwiseSelectedSourceLocalLayerSerialFaceOutputPortDartEquivAt formation
      corridor hinterior offset port side
  have hedge : formation.annular.RS.edgeOf occurrence.1 ∈
      indexedCrossingEdgeSet
        (pointwiseSelectedSourceLocalLayerRightCrossingAt formation corridor
          hinterior offset) := by
    apply (mem_indexedCrossingEdgeSet_iff _ _).2
    refine ⟨port, ?_⟩
    exact ((formation.annular.RS.mem_dartsOn).1 occurrence.2).symm
  ⟨occurrence.1, Finset.mem_union_right _
    (mem_closedDartCarrier_of_edge_mem formation.annular.RS _ occurrence.1
      hedge)⟩

/-- Finite selected port incidence decoded from the two literal port
occurrences and graph-free Cell closure. -/
def PointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentContainsPortFinite
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
      hinterior offset).card ≤ 6)
    (fragment : PointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentAt
      formation corridor hinterior offset) (port : Fin 2) : Prop :=
  ∃ side : Fin 2,
    Relation.ReflTransGen
      (PointwiseSelectedSourceLocalLayerSerialFaceFiniteComponentStep
        (pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt
          formation corridor hinterior offset hcell)
        (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCodeAt formation
          corridor hinterior offset hcell))
      (carrierCoordinate
        (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt
          formation corridor hinterior offset)
        (pointwiseSelectedSourceLocalLayerSerialFaceOutputPortTransitionDartAt
          formation corridor hinterior offset port side))
      (carrierCoordinate
        (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt
          formation corridor hinterior offset)
        (pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentTransitionDartAt
          formation corridor hinterior offset fragment))

/-- The finite predicate is exact literal selected fragment/port incidence. -/
theorem pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentContainsPortFinite_iff
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
      hinterior offset).card ≤ 6)
    (fragment : PointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentAt
      formation corridor hinterior offset) (port : Fin 2) :
    PointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentContainsPortFinite
        formation corridor hinterior offset hcell fragment port ↔
      pointwiseSelectedSourceLocalLayerRightCrossingAt formation corridor
          hinterior offset port ∈
        boundaryRegionalFragmentEdges formation.annular.RS
          (indexedCrossingEdgeSet
            (pointwiseSelectedSourceLocalLayerRightCrossingAt formation corridor
              hinterior offset))
          (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt
            formation corridor hinterior offset) fragment := by
  let edge := pointwiseSelectedSourceLocalLayerRightCrossingAt formation corridor
    hinterior offset port
  let cut := indexedCrossingEdgeSet
    (pointwiseSelectedSourceLocalLayerRightCrossingAt formation corridor
      hinterior offset)
  let region :=
    pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt formation
      corridor hinterior offset
  have hedgeRegion : edge ∈ region := by
    change pointwiseSelectedSourceLocalLayerRightCrossingAt formation corridor
        hinterior offset port ∈
      pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt formation
        corridor hinterior offset
    rw [← pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt_union_cell
      formation corridor hinterior offset]
    exact Finset.mem_union_right _
      (pointwiseSelectedSourceLocalLayerCellRegionAt_rightCrossing formation
        corridor hinterior offset port)
  rw [edge_mem_boundaryRegionalFragmentEdges_iff_exists_dart_reachable
    formation.annular.RS cut region fragment edge hedgeRegion]
  constructor
  · rintro ⟨side, hfinite⟩
    let dart :=
      pointwiseSelectedSourceLocalLayerSerialFaceOutputPortDartEquivAt formation
        corridor hinterior offset port side
    refine ⟨dart, ?_⟩
    exact
      (pointwiseSelectedSourceLocalLayerSerialPreRebaseFaceDartReachable_iff_finiteClosure
        formation corridor hinterior offset hcell
        (pointwiseSelectedSourceLocalLayerSerialFaceOutputPortTransitionDartAt
          formation corridor hinterior offset port side)
        (pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentTransitionDartAt
          formation corridor hinterior offset fragment)).2 (by
            simpa only
              [PointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentContainsPortFinite]
              using hfinite)
  · rintro ⟨dart, hreachable⟩
    let side :=
      (pointwiseSelectedSourceLocalLayerSerialFaceOutputPortDartEquivAt formation
        corridor hinterior offset port).symm dart
    refine ⟨side, ?_⟩
    have hfinite :=
      (pointwiseSelectedSourceLocalLayerSerialPreRebaseFaceDartReachable_iff_finiteClosure
        formation corridor hinterior offset hcell
        (pointwiseSelectedSourceLocalLayerSerialFaceOutputPortTransitionDartAt
          formation corridor hinterior offset port side)
        (pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentTransitionDartAt
          formation corridor hinterior offset fragment)).1 ?_
    · exact hfinite
    · simpa [side,
        pointwiseSelectedSourceLocalLayerSerialFaceOutputPortTransitionDartAt]
        using hreachable

/-- The finite selected predicate is exactly the corresponding Boolean of the
actual graph-derived pre-rebase profile. -/
theorem pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentContainsPortFinite_iff_profile
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
      hinterior offset).card ≤ 6)
    (color : G.edgeSet → Color)
    (hcolor : ∀ port : Fin 2,
      color (pointwiseSelectedSourceLocalLayerRightCrossingAt formation corridor
        hinterior offset port) ≠ 0)
    (fragment : Fin (Fintype.card
      (PointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentAt formation
        corridor hinterior offset)))
    (port : Fin 2) :
    PointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentContainsPortFinite
        formation corridor hinterior offset hcell
        (boundaryRegionalFragmentAt formation.annular.RS
          (indexedCrossingEdgeSet
            (pointwiseSelectedSourceLocalLayerRightCrossingAt formation corridor
              hinterior offset))
          (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt
            formation corridor hinterior offset) fragment) port ↔
      ((pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputCutDataAt formation
          corridor hinterior offset).regionalProfile color hcolor
        ).fragmentContainsPort fragment (.inl port) = true := by
  rw [pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentContainsPortFinite_iff]
  rw [GraphCorridorCutData.regionalProfile_fragmentContainsPort_eq_true_iff]
  rw [(pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputCutDataAt formation
    corridor hinterior offset
    ).regionalFragmentEdges_eq_of_fragmentsOnFaceInRegion
      (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputCutDataAt_fragmentsOnFaceInRegion
        formation corridor hinterior offset)]
  rfl

end

end GoertzelV24ClosedWebPointwiseSelectedFaceFiniteOutputPort

end Mettapedia.GraphTheory.FourColor
