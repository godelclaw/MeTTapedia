import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellRebaseExpandedFaceSource

/-!
# Executable validity laws for the expanded facial occurrence receipt

The fixed forty-eight-slot Cell--rebase receipt contains inactive padding as
well as actual dart occurrences.  The literal pre-rebase presence row is the
load-bearing discriminator: direct facial adjacency can use only two present
occurrences, while an absent occurrence is isolated from every other slot.

These laws are stated entirely on the finite receipt.  They let the later
interface-enlargement decoder discard far-side collar padding before applying
the degree-two exterior-component update; no geometric assertion is made
about an inactive occurrence.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24RotationFaceRegionalDartGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance cellRebaseExpandedFaceValidityEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- Literal pre-rebase presence implies that the fixed occurrence slot is
occupied. -/
theorem sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_occupied_of_present
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (slot : SourceLocalLayerSerialCellRebaseExpandedFaceInterface)
    (hpresent :
      (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
        hunique offset hnext hcell).preRebasePresent slot = true) :
    (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
      hunique offset hnext hcell).occupied slot = true := by
  classical
  unfold sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt at hpresent ⊢
  dsimp only at hpresent ⊢
  cases hdecode : sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot?
      corridor hunique offset hnext hcell slot <;> simp_all

/-- A direct pre-rebase facial adjacency has two present endpoints.  This is
the exact finite form of the regional graph's support condition. -/
theorem sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_present_of_directAdj
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (left right : SourceLocalLayerSerialCellRebaseExpandedFaceInterface)
    (hadj :
      (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
        hunique offset hnext hcell).directAdj left right = true) :
    (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
        hunique offset hnext hcell).preRebasePresent left = true ∧
      (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
        hunique offset hnext hcell).preRebasePresent right = true := by
  classical
  unfold sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt at hadj ⊢
  dsimp only at hadj ⊢
  cases hleft : sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot?
      corridor hunique offset hnext hcell left with
  | none => simp [hleft] at hadj
  | some leftDart =>
    cases hright : sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot?
        corridor hunique offset hnext hcell right with
    | none => simp [hleft, hright] at hadj
    | some rightDart =>
      simp only [hleft, hright] at hadj ⊢
      have hregional :
          (faceRegionalDartGraph web.annular.RS
            (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique
              offset)).Adj leftDart rightDart := by
        simpa using hadj
      exact ⟨decide_eq_true hregional.2.2.1,
        decide_eq_true hregional.2.2.2⟩

/-- Literal presence is constant on the ambient-dart aliases recorded by the
fixed occurrence receipt.  The inactive case is included: two inactive
coordinates can be equal only when they are the same fixed coordinate. -/
theorem sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_present_congr
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (left right : SourceLocalLayerSerialCellRebaseExpandedFaceInterface)
    (heq :
      (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
        hunique offset hnext hcell).vertexEq left right = true) :
    (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
        hunique offset hnext hcell).preRebasePresent left =
      (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
        hunique offset hnext hcell).preRebasePresent right := by
  classical
  unfold sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt at heq ⊢
  dsimp only at heq ⊢
  cases hleft : sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot?
      corridor hunique offset hnext hcell left <;>
    cases hright : sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot?
      corridor hunique offset hnext hcell right <;>
    simp_all

/-- Direct-adjacency rows are constant on aliases in their left coordinate. -/
theorem sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_directAdj_congr_left
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (left left' right : SourceLocalLayerSerialCellRebaseExpandedFaceInterface)
    (heq :
      (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
        hunique offset hnext hcell).vertexEq left left' = true) :
    (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
        hunique offset hnext hcell).directAdj left right =
      (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
        hunique offset hnext hcell).directAdj left' right := by
  classical
  unfold sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt at heq ⊢
  dsimp only at heq ⊢
  cases hleft : sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot?
      corridor hunique offset hnext hcell left <;>
    cases hleft' : sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot?
      corridor hunique offset hnext hcell left' <;>
    simp_all

/-- Direct-adjacency rows are constant on aliases in their right coordinate. -/
theorem sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_directAdj_congr_right
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (left right right' : SourceLocalLayerSerialCellRebaseExpandedFaceInterface)
    (heq :
      (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
        hunique offset hnext hcell).vertexEq right right' = true) :
    (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
        hunique offset hnext hcell).directAdj left right =
      (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
        hunique offset hnext hcell).directAdj left right' := by
  classical
  unfold sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt at heq ⊢
  dsimp only at heq ⊢
  cases hright : sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot?
      corridor hunique offset hnext hcell right <;>
    cases hright' : sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot?
      corridor hunique offset hnext hcell right' <;>
    simp_all

/-- An absent fixed occurrence has no outgoing direct-adjacency row. -/
theorem sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_directAdj_eq_false_of_not_present_left
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (left right : SourceLocalLayerSerialCellRebaseExpandedFaceInterface)
    (hleft :
      (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
        hunique offset hnext hcell).preRebasePresent left = false) :
    (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
      hunique offset hnext hcell).directAdj left right = false := by
  apply Bool.eq_false_iff.mpr
  intro hadj
  have hpresent :=
    sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_present_of_directAdj
      corridor hunique offset hnext hcell left right hadj
  simp [hleft] at hpresent

/-- An absent fixed occurrence has no incoming direct-adjacency row either. -/
theorem sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_directAdj_eq_false_of_not_present_right
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (left right : SourceLocalLayerSerialCellRebaseExpandedFaceInterface)
    (hright :
      (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
        hunique offset hnext hcell).preRebasePresent right = false) :
    (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
      hunique offset hnext hcell).directAdj left right = false := by
  apply Bool.eq_false_iff.mpr
  intro hadj
  have hpresent :=
    sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_present_of_directAdj
      corridor hunique offset hnext hcell left right hadj
  simp [hright] at hpresent

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
