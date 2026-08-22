import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseFaceCollarFragment

/-!
# A finite facial receipt for an actual source rebase

The bounded collar code computes the successor regional component relation,
but the source profile has three distinct facial observations: ambient-face
continuation, port incidence, and capped regional progress.  This file keeps
those observations separate and packages them with the collar code in one
finite receipt with four padded successor-fragment slots.

The receipt is relational evidence extracted from one literal source rebase.
It does not claim that predecessor data determine a unique successor, and it
does not replace the source's heterogeneous support relation by a function.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationBoundaryFaceCutProfile
open SimpleGraphDartRotation

/-- One finite successor-face receipt.  The dependent coordinate field keeps
each occupied row on the exact carrier used by `collarCode`. -/
structure SourceLocalLayerBoundaryRebaseFiniteFaceReceipt where
  collarCode : BoundedCarrierGraphFamilyCode 24 0 Bool
  fragmentOccupied : Fin 4 → Bool
  fragmentCoordinate : Fin 4 → Option (Fin collarCode.vertexCount.val)
  faceContinues : Fin 4 → Fin 4 → Bool
  fragmentContainsPort : Fin 4 → CorridorPort 2 1 → Bool
  faceLengthCap : Fin 4 → Fin 6

noncomputable instance :
    DecidableEq SourceLocalLayerBoundaryRebaseFiniteFaceReceipt :=
  Classical.decEq _

private def sourceLocalLayerBoundaryRebaseFiniteFaceReceiptEquiv :
    SourceLocalLayerBoundaryRebaseFiniteFaceReceipt ≃
      Σ code : BoundedCarrierGraphFamilyCode 24 0 Bool,
        (Fin 4 → Bool) ×
          (Fin 4 → Option (Fin code.vertexCount.val)) ×
            (Fin 4 → Fin 4 → Bool) ×
              (Fin 4 → CorridorPort 2 1 → Bool) × (Fin 4 → Fin 6) where
  toFun receipt :=
    ⟨receipt.collarCode, receipt.fragmentOccupied,
      receipt.fragmentCoordinate, receipt.faceContinues,
      receipt.fragmentContainsPort, receipt.faceLengthCap⟩
  invFun data :=
    { collarCode := data.1
      fragmentOccupied := data.2.1
      fragmentCoordinate := data.2.2.1
      faceContinues := data.2.2.2.1
      fragmentContainsPort := data.2.2.2.2.1
      faceLengthCap := data.2.2.2.2.2 }
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance :
    Fintype SourceLocalLayerBoundaryRebaseFiniteFaceReceipt :=
  Fintype.ofEquiv _ sourceLocalLayerBoundaryRebaseFiniteFaceReceiptEquiv.symm

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebLocalLayerSerialBoundaryRebaseFiniteFaceReceiptEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- The next terminal-aware graph cut whose facial rows the receipt decodes. -/
noncomputable def sourceLocalLayerBoundaryRebaseSuccessorCutDataAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :=
  sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
    (sourceLocalLayerNextOffset offset hnext)

/-- Extract the complete finite facial receipt of one actual rebase. -/
noncomputable def sourceLocalLayerBoundaryRebaseFiniteFaceReceiptAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    SourceLocalLayerBoundaryRebaseFiniteFaceReceipt := by
  classical
  let decode := sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAtSlot?
    corridor hunique offset hnext
  let code := sourceLocalLayerBoundaryRebaseFaceCollarCodeAt corridor hunique
    offset hnext
  let cut := indexedCrossingEdgeSet
    (sourceLocalLayerLeftCrossingAt corridor hunique
      (sourceLocalLayerNextOffset offset hnext))
  let region := sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
    (sourceLocalLayerNextOffset offset hnext)
  let cutData := sourceLocalLayerBoundaryRebaseSuccessorCutDataAt corridor
    hunique offset hnext
  exact {
    collarCode := code
    fragmentOccupied := fun slot => (decode slot).isSome
    fragmentCoordinate := fun slot =>
      match decode slot with
      | some fragment =>
          some (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentCoordinateAt
            corridor hunique offset hnext fragment)
      | none => none
    faceContinues := fun leftSlot rightSlot =>
      match decode leftSlot, decode rightSlot with
      | some left, some right => decide (left.1.1 = right.1.1)
      | _, _ => false
    fragmentContainsPort := fun slot port =>
      match decode slot with
      | some fragment => decide
          (cutData.portEdge port ∈
            boundaryRegionalFragmentEdges web.annular.RS cut region fragment)
      | none => false
    faceLengthCap := fun slot =>
      match decode slot with
      | some fragment =>
          ⟨min (boundaryRegionalFragmentEdges web.annular.RS cut region
              fragment).card 5,
            Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
      | none => ⟨0, by omega⟩ }

@[simp]
theorem sourceLocalLayerBoundaryRebaseFiniteFaceReceiptAt_fragmentOccupied
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (fragment : SourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAt
      corridor hunique offset hnext) :
    (sourceLocalLayerBoundaryRebaseFiniteFaceReceiptAt corridor hunique offset
      hnext).fragmentOccupied
        (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentSlotAt corridor
          hunique offset hnext fragment) = true := by
  simp [sourceLocalLayerBoundaryRebaseFiniteFaceReceiptAt]

@[simp]
theorem sourceLocalLayerBoundaryRebaseFiniteFaceReceiptAt_fragmentCoordinate
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (fragment : SourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAt
      corridor hunique offset hnext) :
    (sourceLocalLayerBoundaryRebaseFiniteFaceReceiptAt corridor hunique offset
      hnext).fragmentCoordinate
        (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentSlotAt corridor
          hunique offset hnext fragment) =
      some (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentCoordinateAt
        corridor hunique offset hnext fragment) := by
  simp [sourceLocalLayerBoundaryRebaseFiniteFaceReceiptAt]

@[simp]
theorem sourceLocalLayerBoundaryRebaseFiniteFaceReceiptAt_faceContinues_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (left right : SourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAt
      corridor hunique offset hnext) :
    (sourceLocalLayerBoundaryRebaseFiniteFaceReceiptAt corridor hunique offset
      hnext).faceContinues
        (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentSlotAt corridor
          hunique offset hnext left)
        (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentSlotAt corridor
          hunique offset hnext right) = true ↔
      left.1.1 = right.1.1 := by
  simp [sourceLocalLayerBoundaryRebaseFiniteFaceReceiptAt]

@[simp]
theorem sourceLocalLayerBoundaryRebaseFiniteFaceReceiptAt_fragmentContainsPort_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (fragment : SourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAt
      corridor hunique offset hnext)
    (port : CorridorPort 2 1) :
    (sourceLocalLayerBoundaryRebaseFiniteFaceReceiptAt corridor hunique offset
      hnext).fragmentContainsPort
        (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentSlotAt corridor
          hunique offset hnext fragment) port = true ↔
      (sourceLocalLayerBoundaryRebaseSuccessorCutDataAt corridor hunique offset
        hnext).portEdge port ∈
        boundaryRegionalFragmentEdges web.annular.RS
          (indexedCrossingEdgeSet
            (sourceLocalLayerLeftCrossingAt corridor hunique
              (sourceLocalLayerNextOffset offset hnext)))
          (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
            (sourceLocalLayerNextOffset offset hnext)) fragment := by
  simp [sourceLocalLayerBoundaryRebaseFiniteFaceReceiptAt]

@[simp]
theorem sourceLocalLayerBoundaryRebaseFiniteFaceReceiptAt_faceLengthCap_val
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (fragment : SourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAt
      corridor hunique offset hnext) :
    ((sourceLocalLayerBoundaryRebaseFiniteFaceReceiptAt corridor hunique offset
      hnext).faceLengthCap
        (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentSlotAt corridor
          hunique offset hnext fragment)).val =
      min (boundaryRegionalFragmentEdges web.annular.RS
        (indexedCrossingEdgeSet
          (sourceLocalLayerLeftCrossingAt corridor hunique
            (sourceLocalLayerNextOffset offset hnext)))
        (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
          (sourceLocalLayerNextOffset offset hnext)) fragment).card 5 := by
  simp [sourceLocalLayerBoundaryRebaseFiniteFaceReceiptAt]

/-- The receipt's embedded collar closure recognizes actual successor
fragments exactly. -/
theorem sourceLocalLayerBoundaryRebaseFiniteFaceReceiptAt_fragmentClosure_iff_eq
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (left right : SourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAt
      corridor hunique offset hnext) :
    Relation.ReflTransGen
        (fun first second : Fin
            (sourceLocalLayerBoundaryRebaseFiniteFaceReceiptAt corridor hunique
              offset hnext).collarCode.vertexCount.val =>
          ((sourceLocalLayerBoundaryRebaseFiniteFaceReceiptAt corridor hunique
            offset hnext).collarCode.graph false).Reachable first second ∨
          ((sourceLocalLayerBoundaryRebaseFiniteFaceReceiptAt corridor hunique
            offset hnext).collarCode.graph true).Reachable first second)
        (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentCoordinateAt
          corridor hunique offset hnext left)
        (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentCoordinateAt
          corridor hunique offset hnext right) ↔
      left = right := by
  simpa [sourceLocalLayerBoundaryRebaseFiniteFaceReceiptAt] using
    (sourceLocalLayerBoundaryRebaseFaceCollarCode_fragmentClosure_iff_eq
      corridor hunique offset hnext left right)

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
