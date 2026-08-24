import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseTrackedInputAttachmentState
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellTrackedSeamFamilyCode
import Mettapedia.GraphTheory.FourColor.GoertzelV24SquareGraphComposition
import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphSupResidual

/-!
# Exact tracked recurrence through an actual source boundary rebase

The predecessor receipt already records exact tracked connectivity in the
unchanged core.  This file isolates the genuinely new successor adjacencies
as a canonical residual.  That residual is supported in the closed
edge-adjacency neighborhood of the at-most-four-edge boundary switch, hence on
at most twenty-eight primal edges.

Consequently successor tracked reachability is an exact finite closure of
whole-core component moves and local-residual moves.  No identification of
old and new crossing names is assumed: coincident names merely shrink the
literal switch carrier.

This is still a semantic recurrence on actual graph edges.  The next layer
transports its finite carrier to coordinates and combines it with the facial
collar recurrence in the complete five-field rebase letter.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24SimpleGraphSupResidual
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebLocalLayerSerialBoundaryRebaseTrackedCoreRecurrenceEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- The successor regional tracked graph for one color pair. -/
noncomputable def sourceLocalLayerBoundaryRebaseSuccessorTrackedGraphAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (pair : TrackedColorPair) : SimpleGraph G.edgeSet :=
  regionalTrackedEdgeGraph web.annular.RS
    (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
      (sourceLocalLayerNextOffset offset hnext))
    coloring (trackedColorPairColors pair).1
      (trackedColorPairColors pair).2

/-- The tracked graph on the common old/new core. -/
noncomputable def sourceLocalLayerBoundaryRebaseCoreTrackedGraphAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (pair : TrackedColorPair) : SimpleGraph G.edgeSet :=
  regionalTrackedEdgeGraph web.annular.RS
    (sourceLocalLayerBoundaryRebaseFaceCoreRegionAt corridor hunique offset
      hnext)
    coloring (trackedColorPairColors pair).1
      (trackedColorPairColors pair).2

/-- The canonical tracked successor residue not already present in the core. -/
noncomputable def sourceLocalLayerBoundaryRebaseLocalTrackedGraphAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (pair : TrackedColorPair) : SimpleGraph G.edgeSet :=
  supResidual
    (sourceLocalLayerBoundaryRebaseSuccessorTrackedGraphAt corridor hunique
      offset hnext pair)
    (sourceLocalLayerBoundaryRebaseCoreTrackedGraphAt corridor hunique offset
      hnext pair)
    ⊥

theorem sourceLocalLayerBoundaryRebaseCoreTrackedGraphAt_le_successor
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (pair : TrackedColorPair) :
    sourceLocalLayerBoundaryRebaseCoreTrackedGraphAt corridor hunique offset
        hnext pair ≤
      sourceLocalLayerBoundaryRebaseSuccessorTrackedGraphAt corridor hunique
        offset hnext pair := by
  apply regionalTrackedEdgeGraph_mono
  intro edge hedge
  rw [sourceLocalLayerBoundaryRebaseFaceCoreRegionAt_eq_next_sdiff corridor
    hunique offset hnext] at hedge
  exact (Finset.mem_sdiff.mp hedge).1

/-- The successor graph is exactly its unchanged core plus its canonical local
residue. -/
theorem sourceLocalLayerBoundaryRebaseCore_sup_localTracked_eq_successor
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (pair : TrackedColorPair) :
    sourceLocalLayerBoundaryRebaseCoreTrackedGraphAt corridor hunique offset
          hnext pair ⊔
        sourceLocalLayerBoundaryRebaseLocalTrackedGraphAt corridor hunique
          offset hnext pair =
      sourceLocalLayerBoundaryRebaseSuccessorTrackedGraphAt corridor hunique
        offset hnext pair := by
  have h := sup_sup_supResidual_eq
    (sourceLocalLayerBoundaryRebaseSuccessorTrackedGraphAt corridor hunique
      offset hnext pair)
    (sourceLocalLayerBoundaryRebaseCoreTrackedGraphAt corridor hunique offset
      hnext pair)
    (⊥ : SimpleGraph G.edgeSet)
    (sourceLocalLayerBoundaryRebaseCoreTrackedGraphAt_le_successor corridor
      hunique offset hnext pair)
    bot_le
  simpa [sourceLocalLayerBoundaryRebaseLocalTrackedGraphAt] using h

/-- The switch together with every ambient edge adjacent to it. -/
noncomputable def sourceLocalLayerBoundaryRebaseTrackedCollarAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) : Finset G.edgeSet :=
  web.annular.RS.edgeAdjacencyClosedCarrier
    (sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique offset hnext)

/-- Four switch edges in a subcubic carrier have a closed edge neighborhood
of size at most twenty-eight. -/
theorem sourceLocalLayerBoundaryRebaseTrackedCollarAt_card_le_twentyEight
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    (sourceLocalLayerBoundaryRebaseTrackedCollarAt corridor hunique offset
      hnext).card ≤ 28 := by
  calc
    (sourceLocalLayerBoundaryRebaseTrackedCollarAt corridor hunique offset
      hnext).card ≤
        7 * (sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique offset
          hnext).card := by
      exact web.annular.RS
        |>.edgeAdjacencyClosedCarrier_card_le_seven_mul_of_incidentEdges_card_le_three
          (annularRS_incidentEdges_card_le_three web) _
    _ ≤ 7 * 4 := Nat.mul_le_mul_left 7
      (card_sourceLocalLayerBoundaryRebaseSwitchAt_le_four corridor hunique
        offset hnext)
    _ = 28 := by norm_num

/-- Every edge touched by the genuinely local tracked successor factor lies
in the finite tracked collar. -/
theorem sourceLocalLayerBoundaryRebaseLocalTrackedGraphAt_support_subset_collar
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (pair : TrackedColorPair) :
    (sourceLocalLayerBoundaryRebaseLocalTrackedGraphAt corridor hunique offset
      hnext pair).support ⊆
      sourceLocalLayerBoundaryRebaseTrackedCollarAt corridor hunique offset
        hnext := by
  intro edge hedge
  rcases (SimpleGraph.mem_support _).1 hedge with ⟨other, hadj⟩
  have hresidual := (supResidual_adj
    (sourceLocalLayerBoundaryRebaseSuccessorTrackedGraphAt corridor hunique
      offset hnext pair)
    (sourceLocalLayerBoundaryRebaseCoreTrackedGraphAt corridor hunique offset
      hnext pair)
    ⊥ edge other).1 hadj
  have hwhole := hresidual.1
  have hnotCore := hresidual.2.1
  have hchanged : edge ∈
        sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique offset hnext ∨
      other ∈
        sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique offset hnext := by
    by_contra hnot
    have hedgeNot : edge ∉
        sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique offset hnext :=
      fun h => hnot (Or.inl h)
    have hotherNot : other ∉
        sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique offset hnext :=
      fun h => hnot (Or.inr h)
    apply hnotCore
    refine ⟨hwhole.1, ?_, ?_⟩
    · rw [sourceLocalLayerBoundaryRebaseFaceCoreRegionAt_eq_next_sdiff
        corridor hunique offset hnext]
      exact Finset.mem_sdiff.mpr ⟨hwhole.2.1, hedgeNot⟩
    · rw [sourceLocalLayerBoundaryRebaseFaceCoreRegionAt_eq_next_sdiff
        corridor hunique offset hnext]
      exact Finset.mem_sdiff.mpr ⟨hwhole.2.2, hotherNot⟩
  apply (web.annular.RS.mem_edgeAdjacencyClosedCarrier_iff _ edge).2
  rcases hchanged with hedgeChanged | hotherChanged
  · exact Or.inl hedgeChanged
  · exact Or.inr ⟨other, hotherChanged, hwhole.1.1⟩

/-- Exact successor tracked reachability on the finite collar: alternate
whole-core component moves with moves in the local residual. -/
theorem sourceLocalLayerBoundaryRebaseSuccessorTracked_reachable_iff_collarComponentClosure
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (pair : TrackedColorPair) (left right : G.edgeSet)
    (hleft : left ∈ sourceLocalLayerBoundaryRebaseTrackedCollarAt corridor
      hunique offset hnext)
    (hright : right ∈ sourceLocalLayerBoundaryRebaseTrackedCollarAt corridor
      hunique offset hnext) :
    (sourceLocalLayerBoundaryRebaseSuccessorTrackedGraphAt corridor hunique
      offset hnext pair).Reachable left right ↔
      Relation.ReflTransGen
        (fun first second : Subtype (fun edge =>
            edge ∈ sourceLocalLayerBoundaryRebaseTrackedCollarAt corridor
              hunique offset hnext) =>
          (sourceLocalLayerBoundaryRebaseCoreTrackedGraphAt corridor hunique
            offset hnext pair).Reachable first.1 second.1 ∨
          (sourceLocalLayerBoundaryRebaseLocalTrackedGraphAt corridor hunique
            offset hnext pair).Reachable first.1 second.1)
        ⟨left, hleft⟩ ⟨right, hright⟩ := by
  rw [← sourceLocalLayerBoundaryRebaseCore_sup_localTracked_eq_successor
    corridor hunique offset hnext pair]
  apply reachable_sup_iff_subtype_componentClosure
  intro x middle y _hx hmiddleY _hcore hlocal
  apply sourceLocalLayerBoundaryRebaseLocalTrackedGraphAt_support_subset_collar
    corridor hunique offset hnext pair
  exact SimpleGraph.mem_support_of_reachable hmiddleY hlocal

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
