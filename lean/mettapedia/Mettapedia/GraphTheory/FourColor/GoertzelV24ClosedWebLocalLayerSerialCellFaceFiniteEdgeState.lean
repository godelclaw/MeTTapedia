import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteOutputCap

/-!
# Finite primal-edge identity for one source Cell

The facial closure runs on literal dart occurrences, while capped face
progress counts distinct primal edges.  Two of the twenty-four dart slots may
therefore represent the same edge and must not be counted twice.

This file records exactly the two missing finite observables: equality of the
underlying primal edges and membership in the newly adjoined Cell region.  In
combination with the predecessor-presence bit already stored in the facial
attachment state, Lean proves exact membership in the pre-rebase output
region.  No component cardinality or complete support letter is computed here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteEdgeState

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
open SimpleGraphDartRotation

/-- The finite edge observables needed to turn a dart-component closure into
a distinct primal-edge count. -/
structure SourceLocalLayerSerialFaceFiniteEdgeState where
  samePrimalEdge : Fin 24 → Fin 24 → Bool
  cellPresent : Fin 24 → Bool

private def sourceLocalLayerSerialFaceFiniteEdgeStateEquiv :
    SourceLocalLayerSerialFaceFiniteEdgeState ≃
      (Fin 24 → Fin 24 → Bool) × (Fin 24 → Bool) where
  toFun state := ⟨state.samePrimalEdge, state.cellPresent⟩
  invFun state :=
    { samePrimalEdge := state.1
      cellPresent := state.2 }
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance : DecidableEq SourceLocalLayerSerialFaceFiniteEdgeState :=
  Classical.decEq _

noncomputable instance : Fintype SourceLocalLayerSerialFaceFiniteEdgeState := by
  exact Fintype.ofEquiv _ sourceLocalLayerSerialFaceFiniteEdgeStateEquiv.symm

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebLocalLayerSerialCellFaceFiniteEdgeStateEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Extract edge identity and literal Cell membership from the represented
dart slots, padding unused coordinates with `false`. -/
noncomputable def sourceLocalLayerSerialFaceFiniteEdgeStateAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6) :
    SourceLocalLayerSerialFaceFiniteEdgeState := by
  classical
  let decode := sourceLocalLayerSerialFaceTransitionDartAtSlot? corridor
    hunique offset hcell
  exact {
    samePrimalEdge := fun left right =>
      match decode left, decode right with
      | some leftDart, some rightDart =>
          decide (web.annular.RS.edgeOf leftDart.1 =
            web.annular.RS.edgeOf rightDart.1)
      | _, _ => false
    cellPresent := fun slot =>
      match decode slot with
      | some dart => decide (web.annular.RS.edgeOf dart.1 ∈
          sourceLocalLayerCellRegionAt corridor hunique offset)
      | none => false }

/-- On represented slots the finite equality table is exactly equality of the
underlying primal edges. -/
@[simp]
theorem sourceLocalLayerSerialFaceFiniteEdgeStateAt_samePrimalEdge_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (left right : {dart // dart ∈
      sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset}) :
    (sourceLocalLayerSerialFaceFiniteEdgeStateAt corridor hunique offset hcell
      ).samePrimalEdge
        (sourceLocalLayerSerialFaceTransitionSlotAt corridor hunique offset
          hcell left)
        (sourceLocalLayerSerialFaceTransitionSlotAt corridor hunique offset
          hcell right) = true ↔
      web.annular.RS.edgeOf left.1 = web.annular.RS.edgeOf right.1 := by
  classical
  simp [sourceLocalLayerSerialFaceFiniteEdgeStateAt]

/-- On a represented slot the new-region bit is exactly literal Cell
membership. -/
@[simp]
theorem sourceLocalLayerSerialFaceFiniteEdgeStateAt_cellPresent_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (dart : {dart // dart ∈
      sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset}) :
    (sourceLocalLayerSerialFaceFiniteEdgeStateAt corridor hunique offset hcell
      ).cellPresent
        (sourceLocalLayerSerialFaceTransitionSlotAt corridor hunique offset
          hcell dart) = true ↔
      web.annular.RS.edgeOf dart.1 ∈
        sourceLocalLayerCellRegionAt corridor hunique offset := by
  classical
  simp [sourceLocalLayerSerialFaceFiniteEdgeStateAt]

/-- The predecessor and Cell presence bits jointly decide exact membership in
the pre-rebase output region. -/
theorem sourceLocalLayerSerialFaceFiniteOutputPresent_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (dart : {dart // dart ∈
      sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset}) :
    (sourceLocalLayerSerialFacePrefixAttachmentStateAt corridor hunique offset
          hcell).interfacePresent
        (sourceLocalLayerSerialFaceTransitionSlotAt corridor hunique offset
          hcell dart) = true ∨
      (sourceLocalLayerSerialFaceFiniteEdgeStateAt corridor hunique offset hcell
          ).cellPresent
        (sourceLocalLayerSerialFaceTransitionSlotAt corridor hunique offset
          hcell dart) = true ↔
      web.annular.RS.edgeOf dart.1 ∈
        sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset := by
  rw [sourceLocalLayerSerialFacePrefixAttachmentStateAt_interfacePresent,
    sourceLocalLayerSerialFaceFiniteEdgeStateAt_cellPresent_iff,
    ← sourceLocalLayerSerialTerminalInputRegionAt_union_cell corridor hunique
      offset]
  simp

end


end GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteEdgeState

end Mettapedia.GraphTheory.FourColor
