import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseFiniteFaceReceipt

/-!
# The finite rebase face receipt decodes the actual successor profile

The finite facial receipt is useful to the compositional word only if its rows
are the rows of the literal successor profile.  This file makes that junction
explicit.  It uses the same canonical fragment enumeration as the graph-derived
profile and proves exact agreement for ambient-face continuation, port
incidence, and capped regional progress.

This remains the facial part of a relational support letter.  It does not
assert a deterministic update from the predecessor profile, join tracked
connectivity, or claim a reachable-state bound.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24GraphDerivedTerminalProfile
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationBoundaryFaceCutProfile
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebLocalLayerSerialBoundaryRebaseFiniteFaceReceiptProfileEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- The canonical actual successor fragment named by one profile row. -/
noncomputable def sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAtIndex
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (index : Fin (Fintype.card
      (SourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAt corridor hunique
        offset hnext))) :
    SourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAt corridor hunique
      offset hnext :=
  boundaryRegionalFragmentAt web.annular.RS
    (indexedCrossingEdgeSet
      (sourceLocalLayerLeftCrossingAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext)))
    (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
      (sourceLocalLayerNextOffset offset hnext)) index

@[simp]
theorem sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentSlotAt_index
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (index : Fin (Fintype.card
      (SourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAt corridor hunique
        offset hnext))) :
    sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentSlotAt corridor hunique
        offset hnext
        (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAtIndex corridor
          hunique offset hnext index) =
      Fin.castLE
        (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAt_card_le_four
          corridor hunique offset hnext) index := by
  apply Fin.ext
  simp [sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentSlotAt,
    sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAtIndex,
    boundaryRegionalFragmentAt]

/-- The canonical successor cut row has exactly the edge support of the
corresponding occurrence-sensitive fragment. -/
theorem sourceLocalLayerBoundaryRebaseSuccessorCutDataAt_regionalFragmentEdges
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (fragment : Fin (Fintype.card
      (SourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAt corridor hunique
        offset hnext))) :
    (sourceLocalLayerBoundaryRebaseSuccessorCutDataAt corridor hunique offset
      hnext).regionalFragmentEdges fragment =
      boundaryRegionalFragmentEdges web.annular.RS
        (indexedCrossingEdgeSet
          (sourceLocalLayerLeftCrossingAt corridor hunique
            (sourceLocalLayerNextOffset offset hnext)))
        (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
          (sourceLocalLayerNextOffset offset hnext))
        (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAtIndex corridor
          hunique offset hnext fragment) := by
  rw [GraphCorridorCutData.regionalFragmentEdges_eq_of_fragmentsOnFaceInRegion
    (sourceLocalLayerBoundaryRebaseSuccessorCutDataAt corridor hunique offset
      hnext)
    (sourceLocalLayerSerialTerminalInputCutDataAt_fragmentsOnFaceInRegion
      corridor hunique (sourceLocalLayerNextOffset offset hnext))]
  rfl

/-- The receipt and the literal successor profile have the same ambient-face
continuation rows. -/
theorem sourceLocalLayerBoundaryRebaseFiniteFaceReceiptAt_faceContinues_profile
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (left right : Fin (Fintype.card
      (SourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAt corridor hunique
        offset hnext))) :
    (sourceLocalLayerBoundaryRebaseFiniteFaceReceiptAt corridor hunique offset
      hnext).faceContinues
        (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentSlotAt corridor
          hunique offset hnext
          (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAtIndex corridor
            hunique offset hnext left))
        (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentSlotAt corridor
          hunique offset hnext
          (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAtIndex corridor
            hunique offset hnext right)) =
      (sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext)).profile.faceContinues
          left right := by
  apply Bool.eq_iff_iff.mpr
  simpa [sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAtIndex,
    sourceLocalLayerSerialTerminalInputBoundedProfileAt,
    sourceLocalLayerSerialTerminalInputCutDataAt,
    sourceLocalLayerSerialTerminalInputBaseCutDataAt,
    regionalBoundaryGraphCutData, withTerminalEdges] using
    (sourceLocalLayerBoundaryRebaseFiniteFaceReceiptAt_faceContinues_iff
      corridor hunique offset hnext
      (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAtIndex corridor
        hunique offset hnext left)
      (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAtIndex corridor
        hunique offset hnext right))

/-- The receipt and the literal successor profile have the same port-incidence
rows. -/
theorem sourceLocalLayerBoundaryRebaseFiniteFaceReceiptAt_fragmentContainsPort_profile
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (fragment : Fin (Fintype.card
      (SourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAt corridor hunique
        offset hnext)))
    (port : CorridorPort 2 1) :
    (sourceLocalLayerBoundaryRebaseFiniteFaceReceiptAt corridor hunique offset
      hnext).fragmentContainsPort
        (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentSlotAt corridor
          hunique offset hnext
          (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAtIndex corridor
            hunique offset hnext fragment)) port =
      (sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext)).profile.fragmentContainsPort
          fragment port := by
  apply Bool.eq_iff_iff.mpr
  rw [sourceLocalLayerBoundaryRebaseFiniteFaceReceiptAt_fragmentContainsPort_iff]
  change _ ↔
    ((sourceLocalLayerBoundaryRebaseSuccessorCutDataAt corridor hunique offset
      hnext).regionalProfile coloring (fun _ => web.tait _)
      ).fragmentContainsPort fragment port = true
  rw [GraphCorridorCutData.regionalProfile_fragmentContainsPort_eq_true_iff]
  rw [sourceLocalLayerBoundaryRebaseSuccessorCutDataAt_regionalFragmentEdges]

/-- The receipt and the literal successor profile have the same capped
regional-progress rows. -/
theorem sourceLocalLayerBoundaryRebaseFiniteFaceReceiptAt_faceLengthCap_profile
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (fragment : Fin (Fintype.card
      (SourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAt corridor hunique
        offset hnext))) :
    (sourceLocalLayerBoundaryRebaseFiniteFaceReceiptAt corridor hunique offset
      hnext).faceLengthCap
        (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentSlotAt corridor
          hunique offset hnext
          (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAtIndex corridor
            hunique offset hnext fragment)) =
      (sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext)).profile.faceLengthCap
          fragment := by
  apply Fin.ext
  rw [sourceLocalLayerBoundaryRebaseFiniteFaceReceiptAt_faceLengthCap_val]
  change _ =
    (((sourceLocalLayerBoundaryRebaseSuccessorCutDataAt corridor hunique offset
      hnext).regionalProfile coloring (fun _ => web.tait _)
      ).faceLengthCap fragment).val
  rw [GraphCorridorCutData.regionalProfile_faceLengthCap_val]
  rw [sourceLocalLayerBoundaryRebaseSuccessorCutDataAt_regionalFragmentEdges]

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
