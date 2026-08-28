import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteNewEdgeRepresentatives
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedFaceFiniteEdgeState

/-!
# Semantic certificates for selected finite face representatives

The predecessor-component and new-edge representative constructions are
entirely graph-free.  This file supplies their semantic laws for the
pointwise-selected source Cell.  The fixed state, stable-slot embedding, and
finite component step are shared definitionally with the generic selector;
only the reflection to the selected literal geometry is new.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebPointwiseSelectedFaceFiniteRepresentatives

open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Formation
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteClosure
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteEdgeState
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteNewEdgeRepresentatives
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteOutputCap
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFinitePredecessorRepresentatives
open GoertzelV24ClosedWebPointwiseSelectedFaceFiniteClosure
open GoertzelV24ClosedWebPointwiseSelectedFaceFiniteEdgeState
open GoertzelV24FaceOrbitIncidence
open GoertzelV24RotationFaceRegionalDartGraph
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance pointwiseSelectedFaceFiniteRepresentativesEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Every pointwise-selected source Cell supplies the component-equivalence,
presence, and cap-coherence laws required by the generic predecessor
representative selector. -/
theorem pointwiseSelectedSourceLocalLayerSerialFaceFinitePredecessorSemanticAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
      hinterior offset).card ≤ 6) :
    SourceLocalLayerSerialFaceFinitePredecessorSemantic
      (pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt
        formation corridor hinterior offset hcell)
      (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCodeAt formation
        corridor hinterior offset hcell) := by
  let carrier :=
    pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation
      corridor hinterior offset
  let coordinate := carrierCoordinate carrier
  let code := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCodeAt
    formation corridor hinterior offset hcell
  let state :=
    pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt formation
      corridor hinterior offset hcell
  let region :=
    pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
      corridor hinterior offset
  let graph := faceRegionalDartGraph formation.annular.RS region
  have hslotDart (dart : {dart // dart ∈ carrier}) :
      sourceLocalLayerSerialFaceFiniteStableSlot code (coordinate dart) =
        pointwiseSelectedSourceLocalLayerSerialFaceTransitionSlotAt formation
          corridor hinterior offset hcell dart := by
    rfl
  have hslot (coordinateIndex : Fin code.vertexCount.val) :
      sourceLocalLayerSerialFaceFiniteStableSlot code coordinateIndex =
        pointwiseSelectedSourceLocalLayerSerialFaceTransitionSlotAt formation
          corridor hinterior offset hcell (coordinate.symm coordinateIndex) := by
    rw [← hslotDart (coordinate.symm coordinateIndex)]
    simp
  have hconnected (left right : Fin code.vertexCount.val) :
      SourceLocalLayerSerialFaceFinitePredecessorConnected state code left
          right ↔
        graph.Reachable (coordinate.symm left).1
          (coordinate.symm right).1 := by
    unfold SourceLocalLayerSerialFaceFinitePredecessorConnected
    rw [hslot left, hslot right]
    exact
      pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt_factoredReachability_iff
        formation corridor hinterior offset hcell (coordinate.symm left)
          (coordinate.symm right)
  have hpresent (coordinateIndex : Fin code.vertexCount.val) :
      state.interfacePresent
          (sourceLocalLayerSerialFaceFiniteStableSlot code coordinateIndex) =
            true ↔
        formation.annular.RS.edgeOf (coordinate.symm coordinateIndex).1 ∈
          region := by
    rw [hslot coordinateIndex]
    rw [pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt_interfacePresent]
    simp [region]
  have hcap (coordinateIndex : Fin code.vertexCount.val) :
      state.componentCap
          (sourceLocalLayerSerialFaceFiniteStableSlot code coordinateIndex) =
        ⟨min (sourceLocalLayerBoundaryRebaseFaceComponentEdges
            formation.annular.RS region
            (coordinate.symm coordinateIndex).1).card 5,
          Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩ := by
    rw [hslot coordinateIndex]
    exact
      pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt_componentCap
        formation corridor hinterior offset hcell
          (coordinate.symm coordinateIndex)
  refine {
    connected_refl := ?_
    connected_symm := ?_
    connected_trans := ?_
    present_constant := ?_
    cap_constant := ?_ }
  · intro coordinateIndex
    exact (hconnected coordinateIndex coordinateIndex).2
      SimpleGraph.Reachable.rfl
  · intro left right hsame
    exact (hconnected right left).2 ((hconnected left right).1 hsame).symm
  · intro left middle right hleft hright
    exact (hconnected left right).2
      (((hconnected left middle).1 hleft).trans
        ((hconnected middle right).1 hright))
  · intro left right hsame
    apply Bool.eq_iff_iff.mpr
    rw [hpresent left, hpresent right]
    have hreachable := (hconnected left right).1 hsame
    by_cases heq : (coordinate.symm left).1 = (coordinate.symm right).1
    · rw [heq]
    · constructor
      · intro _
        have hsupport := SimpleGraph.mem_support_of_reachable (Ne.symm heq)
          hreachable.symm
        rw [SimpleGraph.mem_support] at hsupport
        rcases hsupport with ⟨neighbor, hadjacent⟩
        exact hadjacent.2.2.1
      · intro _
        have hsupport := SimpleGraph.mem_support_of_reachable heq hreachable
        rw [SimpleGraph.mem_support] at hsupport
        rcases hsupport with ⟨neighbor, hadjacent⟩
        exact hadjacent.2.2.1
  · intro left right hsame
    rw [hcap left, hcap right]
    apply Fin.ext
    exact congrArg (fun cardinality => min cardinality 5)
      (congrArg Finset.card
        (sourceLocalLayerBoundaryRebaseFaceComponentEdges_eq_of_reachable
          formation.annular.RS region ((hconnected left right).1 hsame)))

/-- The exact selected primal-edge equality table supplies the equivalence
laws required by the generic new-edge representative selector. -/
theorem pointwiseSelectedSourceLocalLayerSerialFaceFiniteNewEdgeSemanticAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
      hinterior offset).card ≤ 6)
    (output : Fin
      (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCodeAt formation
        corridor hinterior offset hcell).vertexCount.val) :
    SourceLocalLayerSerialFaceFiniteNewEdgeSemantic
      (pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt
        formation corridor hinterior offset hcell)
      (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCodeAt formation
        corridor hinterior offset hcell)
      (pointwiseSelectedSourceLocalLayerSerialFaceFiniteEdgeStateAt formation
        corridor hinterior offset hcell)
      output := by
  let carrier :=
    pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation
      corridor hinterior offset
  let coordinate := carrierCoordinate carrier
  let code := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCodeAt
    formation corridor hinterior offset hcell
  let edgeState :=
    pointwiseSelectedSourceLocalLayerSerialFaceFiniteEdgeStateAt formation
      corridor hinterior offset hcell
  have hslotDart (dart : {dart // dart ∈ carrier}) :
      sourceLocalLayerSerialFaceFiniteStableSlot code (coordinate dart) =
        pointwiseSelectedSourceLocalLayerSerialFaceTransitionSlotAt formation
          corridor hinterior offset hcell dart := by
    rfl
  have hslot (coordinateIndex : Fin code.vertexCount.val) :
      sourceLocalLayerSerialFaceFiniteStableSlot code coordinateIndex =
        pointwiseSelectedSourceLocalLayerSerialFaceTransitionSlotAt formation
          corridor hinterior offset hcell (coordinate.symm coordinateIndex) := by
    rw [← hslotDart (coordinate.symm coordinateIndex)]
    simp
  have hsame (left right : Fin code.vertexCount.val) :
      edgeState.samePrimalEdge
          (sourceLocalLayerSerialFaceFiniteStableSlot code left)
          (sourceLocalLayerSerialFaceFiniteStableSlot code right) = true ↔
        formation.annular.RS.edgeOf (coordinate.symm left).1 =
          formation.annular.RS.edgeOf (coordinate.symm right).1 := by
    rw [hslot left, hslot right]
    exact
      pointwiseSelectedSourceLocalLayerSerialFaceFiniteEdgeStateAt_samePrimalEdge_iff
        formation corridor hinterior offset hcell (coordinate.symm left)
          (coordinate.symm right)
  refine {
    same_refl := ?_
    same_symm := ?_
    same_trans := ?_ }
  · intro coordinateIndex _hcontributes
    exact (hsame coordinateIndex coordinateIndex).2 rfl
  · intro left right _hleft _hright hsameEdge
    exact (hsame right left).2 ((hsame left right).1 hsameEdge).symm
  · intro left middle right _hleft _hmiddle _hright hleft hright
    exact (hsame left right).2
      (((hsame left middle).1 hleft).trans
        ((hsame middle right).1 hright))

end

end GoertzelV24ClosedWebPointwiseSelectedFaceFiniteRepresentatives

end Mettapedia.GraphTheory.FourColor
