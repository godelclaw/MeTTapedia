import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellRebaseExpandedFaceBoundary

/-!
# Promoted blocks in the fixed facial Cell--rebase receipt

Deleting every newly named facial occurrence need not be safe one occurrence
at a time: several promoted darts can form one short path.  The fixed receipt
already contains exactly the data needed at the right granularity.  Its
equality row glues duplicate occurrences, and its direct-adjacency row joins
consecutive promoted darts.

This file turns those rows into a finite graph on promoted occurrences and
defines the exact block condition used by the deletion theorem: every
promoted occurrence can reach one having an old rolling neighbour.  For a
literal source receipt, reachability in this finite graph maps to reachability
through genuinely promoted darts of the ambient pre-rebase facial graph.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24RotationFaceRegionalDartGraph
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance cellRebaseExpandedFaceBlocksEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- Occurrence coordinates which the finite receipt marks as genuinely new
and present immediately before the facial rebase. -/
abbrev SourceLocalLayerSerialCellRebaseExpandedFacePromotedSlot
    (state : SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState) :=
  {occurrence : SourceLocalLayerSerialCellRebaseExpandedFaceInterface //
    state.promoted occurrence = true}

/-- The finite promoted-block graph.  Two distinct occurrence coordinates are
joined when the receipt says that they name the same ambient dart or directly
adjacent ambient darts.  `SimpleGraph.fromRel` discards loops and symmetrizes
the relation, so this remains a graph even on an arbitrary finite receipt. -/
def SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState.promotedBlockGraph
    (state : SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState) :
    SimpleGraph
      (SourceLocalLayerSerialCellRebaseExpandedFacePromotedSlot state) :=
  SimpleGraph.fromRel fun left right =>
    state.vertexEq left.1 right.1 = true ∨
      state.directAdj left.1 right.1 = true

/-- Exact finite non-splitting condition at block granularity: every promoted
occurrence lies in a promoted block which contains an occurrence adjacent to
the old rolling carrier. -/
def SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState.PromotedBlocksMeetOld
    (state : SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState) :
    Prop :=
  ∀ start : SourceLocalLayerSerialCellRebaseExpandedFacePromotedSlot state,
    ∃ endpoint : SourceLocalLayerSerialCellRebaseExpandedFacePromotedSlot state,
      state.promotedBlockGraph.Reachable start endpoint ∧
        (state.oldNeighbor? endpoint.1).isSome

/-- Boolean reflection of the promoted-block condition. -/
noncomputable def
    SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState.promotedBlocksMeetOld
    (state : SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState) : Bool := by
  classical
  exact decide state.PromotedBlocksMeetOld

@[simp]
theorem
    SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState.promotedBlocksMeetOld_eq_true_iff
    (state : SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState) :
    state.promotedBlocksMeetOld = true ↔ state.PromotedBlocksMeetOld := by
  classical
  simp [SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState.promotedBlocksMeetOld]

/-- Every promoted source occurrence has a decoded ambient dart. -/
noncomputable def sourceLocalLayerSerialCellRebaseExpandedFacePromotedDartAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (slot : SourceLocalLayerSerialCellRebaseExpandedFacePromotedSlot
      (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
        hunique offset hnext hcell)) :
    web.annular.RS.D := by
  classical
  have hpresent :
      (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
        hunique offset hnext hcell).preRebasePresent slot.1 = true :=
    (Bool.and_eq_true_iff.mp slot.2).1
  have hoccupied :=
    sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_occupied_of_present
      corridor hunique offset hnext hcell slot.1 hpresent
  exact Classical.choose
    ((sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_occupied_iff
      corridor hunique offset hnext hcell slot.1).1 hoccupied)

/-- The promoted-dart decoder returns the dart chosen above. -/
theorem sourceLocalLayerSerialCellRebaseExpandedFacePromotedDartAt_spec
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (slot : SourceLocalLayerSerialCellRebaseExpandedFacePromotedSlot
      (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
        hunique offset hnext hcell)) :
    sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot? corridor hunique
        offset hnext hcell slot.1 =
      some (sourceLocalLayerSerialCellRebaseExpandedFacePromotedDartAt corridor
        hunique offset hnext hcell slot) := by
  classical
  unfold sourceLocalLayerSerialCellRebaseExpandedFacePromotedDartAt
  exact Classical.choose_spec
    ((sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_occupied_iff
      corridor hunique offset hnext hcell slot.1).1
      (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_occupied_of_present
        corridor hunique offset hnext hcell slot.1
          (Bool.and_eq_true_iff.mp slot.2).1))

/-- The decoded dart of a promoted source coordinate is regionally present
and absent from the predecessor rolling carrier. -/
theorem sourceLocalLayerSerialCellRebaseExpandedFacePromotedDartAt_semantic
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (slot : SourceLocalLayerSerialCellRebaseExpandedFacePromotedSlot
      (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
        hunique offset hnext hcell)) :
    let dart := sourceLocalLayerSerialCellRebaseExpandedFacePromotedDartAt
      corridor hunique offset hnext hcell slot
    web.annular.RS.edgeOf dart ∈
        sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset ∧
      dart ∉ sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
        offset := by
  dsimp only
  exact
    (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_promoted_iff_of_decode
      corridor hunique offset hnext hcell slot.1
        (sourceLocalLayerSerialCellRebaseExpandedFacePromotedDartAt corridor
          hunique offset hnext hcell slot)
        (sourceLocalLayerSerialCellRebaseExpandedFacePromotedDartAt_spec corridor
          hunique offset hnext hcell slot)).1 slot.2

/-- The ambient pre-rebase facial graph restricted to the genuinely promoted
darts represented by the uniform Cell--rebase interface. -/
def sourceLocalLayerSerialCellRebasePromotedFaceGraphAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    SimpleGraph {dart : web.annular.RS.D //
      web.annular.RS.edgeOf dart ∈
          sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset ∧
        dart ∉ sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
          offset ∧
        dart ∈ sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
          corridor hunique offset hnext} :=
  (faceRegionalDartGraph web.annular.RS
    (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
    ).induce _

/-- Interpret a promoted fixed occurrence as a vertex of the ambient promoted
facial graph. -/
noncomputable def sourceLocalLayerSerialCellRebaseExpandedFacePromotedVertexAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (slot : SourceLocalLayerSerialCellRebaseExpandedFacePromotedSlot
      (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
        hunique offset hnext hcell)) :
    {dart : web.annular.RS.D //
      web.annular.RS.edgeOf dart ∈
          sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset ∧
        dart ∉ sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
          offset ∧
        dart ∈ sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
          corridor hunique offset hnext} :=
  ⟨sourceLocalLayerSerialCellRebaseExpandedFacePromotedDartAt corridor hunique
      offset hnext hcell slot,
    (sourceLocalLayerSerialCellRebaseExpandedFacePromotedDartAt_semantic corridor
      hunique offset hnext hcell slot).1,
    (sourceLocalLayerSerialCellRebaseExpandedFacePromotedDartAt_semantic corridor
      hunique offset hnext hcell slot).2,
    sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot?_mem_uniform corridor
      hunique offset hnext hcell slot.1
        (sourceLocalLayerSerialCellRebaseExpandedFacePromotedDartAt corridor
          hunique offset hnext hcell slot)
        (sourceLocalLayerSerialCellRebaseExpandedFacePromotedDartAt_spec corridor
          hunique offset hnext hcell slot)⟩

/-- Reachability in the finite promoted-block graph is sound for ambient
reachability through promoted darts.  Alias edges map to reflexivity; literal
direct-adjacency edges map to one ambient facial edge. -/
theorem sourceLocalLayerSerialCellRebaseExpandedFace_promotedBlock_reachable
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (left right : SourceLocalLayerSerialCellRebaseExpandedFacePromotedSlot
      (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
        hunique offset hnext hcell))
    (hreachable :
      (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
        hunique offset hnext hcell).promotedBlockGraph.Reachable left right) :
    (sourceLocalLayerSerialCellRebasePromotedFaceGraphAt corridor hunique offset
      hnext).Reachable
        (sourceLocalLayerSerialCellRebaseExpandedFacePromotedVertexAt corridor
          hunique offset hnext hcell left)
        (sourceLocalLayerSerialCellRebaseExpandedFacePromotedVertexAt corridor
          hunique offset hnext hcell right) := by
  let state :=
    sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
      hunique offset hnext hcell
  let promotedGraph := state.promotedBlockGraph
  let ambientGraph :=
    sourceLocalLayerSerialCellRebasePromotedFaceGraphAt corridor hunique offset
      hnext
  let vertexAt :=
    sourceLocalLayerSerialCellRebaseExpandedFacePromotedVertexAt corridor
      hunique offset hnext hcell
  have hstep : ∀ first second :
      SourceLocalLayerSerialCellRebaseExpandedFacePromotedSlot state,
      promotedGraph.Adj first second →
        ambientGraph.Reachable (vertexAt first) (vertexAt second) := by
    intro first second hadj
    rcases (SimpleGraph.fromRel_adj _ first second).1 hadj with
      ⟨_ne, hforward | hbackward⟩
    · rcases hforward with heq | hadjacent
      · have hdartEq :
            (vertexAt first).1 = (vertexAt second).1 :=
          (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_vertexEq_iff_of_decode
            corridor hunique offset hnext hcell first.1 second.1
              (vertexAt first).1 (vertexAt second).1
              (sourceLocalLayerSerialCellRebaseExpandedFacePromotedDartAt_spec
                corridor hunique offset hnext hcell first)
              (sourceLocalLayerSerialCellRebaseExpandedFacePromotedDartAt_spec
                corridor hunique offset hnext hcell second)).1 heq
        have hvertexEq : vertexAt first = vertexAt second :=
          Subtype.ext hdartEq
        rw [hvertexEq]
      · apply SimpleGraph.Adj.reachable
        change (faceRegionalDartGraph web.annular.RS
          (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique
            offset)).Adj (vertexAt first).1 (vertexAt second).1
        exact
          (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_directAdj_iff_of_decode
            corridor hunique offset hnext hcell first.1 second.1
              (vertexAt first).1 (vertexAt second).1
              (sourceLocalLayerSerialCellRebaseExpandedFacePromotedDartAt_spec
                corridor hunique offset hnext hcell first)
              (sourceLocalLayerSerialCellRebaseExpandedFacePromotedDartAt_spec
                corridor hunique offset hnext hcell second)).1 hadjacent
    · rcases hbackward with heq | hadjacent
      · have hdartEq :
            (vertexAt second).1 = (vertexAt first).1 :=
          (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_vertexEq_iff_of_decode
            corridor hunique offset hnext hcell second.1 first.1
              (vertexAt second).1 (vertexAt first).1
              (sourceLocalLayerSerialCellRebaseExpandedFacePromotedDartAt_spec
                corridor hunique offset hnext hcell second)
              (sourceLocalLayerSerialCellRebaseExpandedFacePromotedDartAt_spec
                corridor hunique offset hnext hcell first)).1 heq
        have hvertexEq : vertexAt first = vertexAt second :=
          Subtype.ext hdartEq.symm
        rw [hvertexEq]
      · apply SimpleGraph.Adj.reachable
        change (faceRegionalDartGraph web.annular.RS
          (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique
            offset)).Adj (vertexAt first).1 (vertexAt second).1
        exact
          ((sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_directAdj_iff_of_decode
            corridor hunique offset hnext hcell second.1 first.1
              (vertexAt second).1 (vertexAt first).1
              (sourceLocalLayerSerialCellRebaseExpandedFacePromotedDartAt_spec
                corridor hunique offset hnext hcell second)
              (sourceLocalLayerSerialCellRebaseExpandedFacePromotedDartAt_spec
                corridor hunique offset hnext hcell first)).1 hadjacent).symm
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreachable
  induction hreachable with
  | refl => exact SimpleGraph.Reachable.rfl
  | tail hprefix hadj ih => exact ih.trans (hstep _ _ hadj)

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
