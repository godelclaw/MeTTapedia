import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedRungPlacement
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebCorridorLayer

/-!
# Selected local Cell-3 layer formation

The older local-layer constructor obtains its two rail faces from a closed-map
`PairwiseUniqueSharedInteriorEdges` hypothesis.  That hypothesis must not be
imported into the open Cell-3 tangle.  Here a literal selected rung placement
instead gives an exhaustive local alternative: either its two outgoing flank
faces make the genuine local layer pair, or a finite face collision is retained
with the exact double shared-interior-edge witness it entails.

This is a source-local construction, not a claim that these local layers have
already assembled into the source's long separated crosscuts.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebBoundaryData.AnnularBoundaryData
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabSideAdjacency
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24OrientedHexSlab
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance

namespace SelectedLocalLayerFormation

/-- Transport a standard six-cycle coordinate back to the actual boundary of
a selected Cell-3 hexagon. -/
def selectedPlacementPositionOfSix
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : SelectedInternalHexRungPlacement corridor rungs interior)
    (position : Fin 6) : Fin (web.annular.RS.faceOrbit placement.root).card :=
  Fin.cast placement.orbit_card.symm position

@[simp]
theorem selectedPlacementPositionOfSix_val
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : SelectedInternalHexRungPlacement corridor rungs interior)
    (position : Fin 6) :
    (selectedPlacementPositionOfSix placement position).val = position.val :=
  rfl

@[simp]
theorem selectedPlacementPositionOfSix_incomingPosition6
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : SelectedInternalHexRungPlacement corridor rungs interior) :
    selectedPlacementPositionOfSix placement placement.incomingPosition6 =
      placement.incomingPosition := by
  apply Fin.ext
  rfl

@[simp]
theorem selectedPlacementPositionOfSix_outgoingPosition6
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : SelectedInternalHexRungPlacement corridor rungs interior) :
    selectedPlacementPositionOfSix placement placement.outgoingPosition6 =
      placement.outgoingPosition := by
  apply Fin.ext
  rfl

/-- A non-rung standard six-cycle position is a genuine selected side slot. -/
def selectedPlacementSidePositionOfSix
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : SelectedInternalHexRungPlacement corridor rungs interior)
    (position : {position // position ∈ hexSidePositions
      placement.incomingPosition6 placement.outgoingPosition6}) :
    {position // position ∈ selectedPlacementSidePositions placement} :=
  ⟨selectedPlacementPositionOfSix placement position.1, by
    apply (mem_selectedPlacementSidePositions_iff placement _).2
    have hposition := position.2
    simp only [hexSidePositions, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton, not_or] at hposition
    exact ⟨fun heq => hposition.1 (by
        apply Fin.ext
        simpa [selectedPlacementPositionOfSix,
          SelectedInternalHexRungPlacement.incomingPosition6] using
          congrArg Fin.val heq),
      fun heq => hposition.2 (by
        apply Fin.ext
        simpa [selectedPlacementPositionOfSix,
          SelectedInternalHexRungPlacement.outgoingPosition6] using
          congrArg Fin.val heq)⟩⟩

/-- The two selected slots immediately flanking the outgoing rung exist and
are distinct.  This is just the finite six-cycle calculation, transported to
the literal selected Cell-3 face. -/
theorem exists_two_selectedPlacementSidePositions_flanking_outgoing
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : SelectedInternalHexRungPlacement corridor rungs interior) :
    ∃ before after : {position // position ∈ selectedPlacementSidePositions placement},
      before ≠ after ∧
      placement.outgoingPosition.val ≡ before.1.val + 1 [MOD 6] ∧
      after.1.val ≡ placement.outgoingPosition.val + 1 [MOD 6] := by
  have hnonadjacent :=
    SelectedInternalHexRungPlacement.rungType_ne_adjacent_of_cell3
      corridor rungs interior placement
  rcases exists_two_hexSidePositions_flanking_outgoing
      placement.incomingPosition6 placement.outgoingPosition6
      placement.positions6_ne hnonadjacent with
    ⟨before6, after6, hbeforeAfter, hbeforeMod, hafterMod⟩
  let before := selectedPlacementSidePositionOfSix placement before6
  let after := selectedPlacementSidePositionOfSix placement after6
  refine ⟨before, after, ?_, ?_, ?_⟩
  · intro heq
    apply hbeforeAfter
    apply Subtype.ext
    apply Fin.ext
    simpa [before, after, selectedPlacementSidePositionOfSix,
      selectedPlacementPositionOfSix] using
      congrArg (fun position => position.1.val) heq
  · simpa [before, selectedPlacementSidePositionOfSix,
      selectedPlacementPositionOfSix,
      SelectedInternalHexRungPlacement.outgoingPosition6] using hbeforeMod
  · simpa [after, selectedPlacementSidePositionOfSix,
      selectedPlacementPositionOfSix,
      SelectedInternalHexRungPlacement.outgoingPosition6] using hafterMod

/-- The finite exceptional alternatives left by the source-local Cell-3
construction.  A collision is retained as data rather than ruled out by the
closed-map global uniqueness theorem. -/
inductive SelectedLocalLayerCollision
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (hnext : interior.center.val + 2 < blockLength)
    (placement : SelectedInternalHexRungPlacement corridor rungs interior) : Prop where
  | hitsSuccessor
      (position : {position // position ∈ selectedPlacementSidePositions placement})
      (hface : selectedPlacementSideFace placement position =
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
          (nextCorridorInterior interior hnext).center) :
      SelectedLocalLayerCollision hnext placement
  | repeatsSide
      (left right : {position // position ∈ selectedPlacementSidePositions placement})
      (hpositions : left.1 ≠ right.1)
      (hfaces : selectedPlacementSideFace placement left =
        selectedPlacementSideFace placement right) :
      SelectedLocalLayerCollision hnext placement

/-- Every retained selected collision exhibits two distinct shared interior
edges.  This is the exact finite geometry handed to the remaining L1 case
classification; it is not a global no-double-intersection assumption. -/
theorem SelectedLocalLayerCollision.exists_two_distinct_sharedInteriorEdges
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    {hnext : interior.center.val + 2 < blockLength}
    {placement : SelectedInternalHexRungPlacement corridor rungs interior}
    (collision : SelectedLocalLayerCollision hnext placement) :
    ∃ neighbor : AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS)),
      ∃ first second,
        first ∈ sharedInteriorEdges (orbitFaceBoundary web.annular.RS)
          (Finset.univ : Finset (OrbitFace web.annular.RS))
          ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
            interior.center).1 neighbor.1 ∧
        second ∈ sharedInteriorEdges (orbitFaceBoundary web.annular.RS)
          (Finset.univ : Finset (OrbitFace web.annular.RS))
          ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
            interior.center).1 neighbor.1 ∧
        first ≠ second := by
  cases collision with
  | hitsSuccessor position hface =>
      refine ⟨(corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
        (nextCorridorInterior interior hnext).center, ?_⟩
      exact selectedSideFace_eq_nextCenter_implies_two_distinct_sharedInteriorEdges
        (corridor := corridor) hnext placement position hface
  | repeatsSide left right hpositions hfaces =>
      refine ⟨selectedPlacementSideFace placement left, ?_⟩
      exact selectedPlacementSideFace_eq_implies_two_distinct_sharedInteriorEdges
        (corridor := corridor) placement left right hpositions hfaces

/-- **L1 local layer alternative.** The two literal flank faces around a
selected outgoing rung either form the genuine local Cell-3 layer pair, or
fall into an explicit finite collision case.  No caller supplies a global
face-intersection uniqueness premise.

The theorem is intentionally local: its successful branch supplies one
simple layer boundary; its collision branch is for the finite Cell-3 analysis;
neither branch alone assembles a long annular crosscut. -/
theorem exists_selectedLocalLayerPair_or_collision
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (hnext : interior.center.val + 2 < blockLength)
    (placement : SelectedInternalHexRungPlacement corridor rungs interior) :
    Nonempty (LocalLayerPair web corridor interior hnext) ∨
      SelectedLocalLayerCollision hnext placement := by
  let skeleton := corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
  rcases exists_two_selectedPlacementSidePositions_flanking_outgoing
      (corridor := corridor) placement with
    ⟨before, after, hbeforeAfter, hbeforeMod, hafterMod⟩
  by_cases hbeforeNext : selectedPlacementSideFace placement before =
      skeleton.faceAt (nextCorridorInterior interior hnext).center
  · exact Or.inr (.hitsSuccessor before hbeforeNext)
  by_cases hafterNext : selectedPlacementSideFace placement after =
      skeleton.faceAt (nextCorridorInterior interior hnext).center
  · exact Or.inr (.hitsSuccessor after hafterNext)
  by_cases hfaces : selectedPlacementSideFace placement before =
      selectedPlacementSideFace placement after
  · exact Or.inr (.repeatsSide before after (by
      intro hpositions
      apply hbeforeAfter
      apply Subtype.ext
      exact hpositions) hfaces)
  left
  exact ⟨{
    firstFace := selectedPlacementSideFace placement before
    secondFace := selectedPlacementSideFace placement after
    first_ne_second := hfaces
    center_ne_nextCenter := by
      intro hcenters
      have hindices := skeleton.faceAt_injective hcenters
      have hvalues := congrArg Fin.val hindices
      change interior.center.val = interior.center.val + 1 at hvalues
      omega
    first_adjacent_center :=
      (selectedPlacementSideFace_adjacent_center (corridor := corridor)
        placement before).symm
    center_adjacent_second :=
      selectedPlacementSideFace_adjacent_center (corridor := corridor)
        placement after
    first_adjacent_nextCenter :=
      (selectedPlacementSideFace_eq_or_adjacent_next_of_beforeOutgoing
        (corridor := corridor) hnext placement before hbeforeMod).resolve_left
          hbeforeNext
    nextCenter_adjacent_second :=
      ((selectedPlacementSideFace_eq_or_adjacent_next_of_afterOutgoing
        (corridor := corridor) hnext placement after hafterMod).resolve_left
          hafterNext).symm
    first_internal := selectedPlacementSideFace_internal (corridor := corridor)
      placement before
    second_internal := selectedPlacementSideFace_internal (corridor := corridor)
      placement after
  }⟩

end SelectedLocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
