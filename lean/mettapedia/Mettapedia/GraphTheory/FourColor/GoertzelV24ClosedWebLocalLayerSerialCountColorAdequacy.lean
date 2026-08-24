import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerLiteralCountWitness
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerLiteralSerialTangle
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialFiniteBoolStepLetter

/-!
# Boundary-colour adequacy of the literal Cell receipt

The source letter is the complete positive support of the literal Cell's
five-coordinate `Count` matrix.  The executable Cell--rebase receipt was
initially extracted from one ambient colouring, so it must not be mistaken
for that complete relation.

This module proves the first exact comparison between the two presentations.
For the actual source witness, the positive `Count` entry and the executable
receipt display the same two ordered boundary-colour words.  The statement is
intentionally colour-coordinate adequacy only.  Tracked connectivity, facial
identity and incidence, capped face progress, and the converse construction
from an arbitrary positive `Count` entry remain separate obligations.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCountColorAdequacy

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebComputedDepthProfile
open GoertzelV24ClosedWebLocalLayerSerialFiniteBoolStepLetter
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24HexCorridorSkeleton
open GoertzelV24OpenRegionTaitInheritance
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24OpenRegionRotation.retainedVertexDecidableEq
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq

local instance openedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- The positive literal-`Count` witness and the executable receipt agree on
the ordered input boundary colours of one actual source step. -/
theorem sourceLocalLayerSerialFiniteBoolStepLetterAt_count_inputColorWord
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    sourceLocalLayerCellBoundedProfileColorWord
        (sourceLocalLayerCellProfileCode corridor hunique
          (sourceLocalLayerInteriorAt offset)
          (sourceLocalLayerInteriorAt_hasNext offset)
          (sourceLocalLayerCellInheritedLeftProfile corridor hunique
            (sourceLocalLayerInteriorAt offset)
            (sourceLocalLayerInteriorAt_hasNext offset))) =
      fun step =>
        (((sourceLocalLayerSerialFiniteBoolStepLetterAt graphData minimal caps
          coloring web corridor hunique offset hnext).input).profile.edgeColor
            step).toColor := by
  funext step
  change
    ((sourceLocalLayerCellInheritedLeftProfile corridor hunique
        (sourceLocalLayerInteriorAt offset)
        (sourceLocalLayerInteriorAt_hasNext offset)).edgeColor step).toColor =
      ((sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor hunique
        offset).profile.edgeColor step).toColor
  let relation := sourceLocalLayerSerialCellFullProfileRelation_of_ambientColoring
    corridor hunique offset
  let pair := (sourceLocalLayerPairAt corridor hunique offset
    ).separatedLocalLayerPair hunique
  let boundary := sourceLocalLayerBoundaryAt corridor hunique offset
  let leftCut := pair.sourceCrosscutComplementLeftCutData
    web.annular.cellulation.rotation boundary
  calc
    ((sourceLocalLayerCellInheritedLeftProfile corridor hunique
        (sourceLocalLayerInteriorAt offset)
        (sourceLocalLayerInteriorAt_hasNext offset)).edgeColor step).toColor =
        (rotationColoringOfGraph web.annular coloring)
          (leftCut.crossingEdge step) := by
      rw [sourceLocalLayerCellInheritedLeftProfile_eq_ambientProfile]
      exact leftCut.regionalProfile_edgeColor_toColor
            (rotationColoringOfGraph web.annular coloring)
            (fun crossing =>
              rotationColoringOfGraph_isTait web.annular coloring web.tait
                (leftCut.crossingEdge crossing)) step
    _ = coloring (sourceLocalLayerLeftCrossingAt corridor hunique offset step) := by
      rfl
    _ = ((sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor hunique
          offset).profile.edgeColor step).toColor :=
      (relation.inputEdgeColor step).symm

/-- The positive literal-`Count` witness and the executable receipt agree on
the ordered pre-rebase output boundary colours of one actual source step. -/
theorem sourceLocalLayerSerialFiniteBoolStepLetterAt_count_outputColorWord
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    sourceLocalLayerCellBoundedProfileColorWord
        (sourceLocalLayerCellProfileCode corridor hunique
          (sourceLocalLayerInteriorAt offset)
          (sourceLocalLayerInteriorAt_hasNext offset)
          (sourceLocalLayerCellInheritedRightProfile corridor hunique
            (sourceLocalLayerInteriorAt offset)
            (sourceLocalLayerInteriorAt_hasNext offset))) =
      fun step =>
        (((sourceLocalLayerSerialFiniteBoolStepLetterAt graphData minimal caps
          coloring web corridor hunique offset hnext).cell.output).profile.edgeColor
            step).toColor := by
  funext step
  change
    ((sourceLocalLayerCellInheritedRightProfile corridor hunique
        (sourceLocalLayerInteriorAt offset)
        (sourceLocalLayerInteriorAt_hasNext offset)).edgeColor step).toColor =
      ((sourceLocalLayerSerialPreRebaseOutputBoundedProfileAt corridor hunique
        offset).profile.edgeColor step).toColor
  let relation := sourceLocalLayerSerialCellFullProfileRelation_of_ambientColoring
    corridor hunique offset
  let pair := (sourceLocalLayerPairAt corridor hunique offset
    ).separatedLocalLayerPair hunique
  let boundary := sourceLocalLayerBoundaryAt corridor hunique offset
  let rightCut := pair.sourceCrosscutComplementRightCutData
    web.annular.cellulation.rotation boundary
  calc
    ((sourceLocalLayerCellInheritedRightProfile corridor hunique
        (sourceLocalLayerInteriorAt offset)
        (sourceLocalLayerInteriorAt_hasNext offset)).edgeColor step).toColor =
        (rotationColoringOfGraph web.annular coloring)
          (rightCut.crossingEdge step) := by
      rw [sourceLocalLayerCellInheritedRightProfile_eq_ambientProfile]
      exact rightCut.regionalProfile_edgeColor_toColor
            (rotationColoringOfGraph web.annular coloring)
            (fun crossing =>
              rotationColoringOfGraph_isTait web.annular coloring web.tait
                (rightCut.crossingEdge crossing)) step
    _ = coloring (sourceLocalLayerRightCrossingAt corridor hunique offset step) := by
      rfl
    _ = ((sourceLocalLayerSerialPreRebaseOutputBoundedProfileAt corridor hunique
          offset).profile.edgeColor step).toColor :=
      (relation.outputEdgeColor step).symm

/-- One actual source step simultaneously supplies a positive entry of the
literal five-coordinate `Count`, a supported executable receipt, and exact
agreement of their two boundary-colour projections.  This packages the first
coordinate of the still-open full-profile adequacy theorem. -/
theorem exists_count_supported_finiteBoolStep_with_colorAgreement
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    let leftInterior := sourceLocalLayerInteriorAt offset
    let hinteriorNext := sourceLocalLayerInteriorAt_hasNext offset
    let left := sourceLocalLayerCellInheritedLeftProfile corridor hunique
      leftInterior hinteriorNext
    let right := sourceLocalLayerCellInheritedRightProfile corridor hunique
      leftInterior hinteriorNext
    let letter := sourceLocalLayerSerialFiniteBoolStepLetterAt graphData minimal
      caps coloring web corridor hunique offset hnext
    sourceLocalLayerCellBoundedProfileTransfer corridor hunique
        leftInterior hinteriorNext
        (sourceLocalLayerCellProfileCode corridor hunique leftInterior
          hinteriorNext left)
        (sourceLocalLayerCellProfileCode corridor hunique leftInterior
          hinteriorNext right) ∧
      SourceLocalLayerSerialFiniteBoolStepSupportsBool letter = true ∧
      (sourceLocalLayerCellBoundedProfileColorWord
          (sourceLocalLayerCellProfileCode corridor hunique leftInterior
            hinteriorNext left) =
        fun step => (letter.input.profile.edgeColor step).toColor) ∧
      (sourceLocalLayerCellBoundedProfileColorWord
          (sourceLocalLayerCellProfileCode corridor hunique leftInterior
            hinteriorNext right) =
        fun step => (letter.cell.output.profile.edgeColor step).toColor) := by
  dsimp only
  exact ⟨
    sourceLocalLayerCellBoundedProfileTransfer_of_ambientColoring corridor
      hunique (sourceLocalLayerInteriorAt offset)
        (sourceLocalLayerInteriorAt_hasNext offset),
    sourceLocalLayerSerialFiniteBoolStepLetterAt_supports graphData minimal caps
      coloring web corridor hunique offset hnext,
    sourceLocalLayerSerialFiniteBoolStepLetterAt_count_inputColorWord graphData
      minimal caps coloring web corridor hunique offset hnext,
    sourceLocalLayerSerialFiniteBoolStepLetterAt_count_outputColorWord graphData
      minimal caps coloring web corridor hunique offset hnext⟩

end

end GoertzelV24ClosedWebLocalLayerSerialCountColorAdequacy

end Mettapedia.GraphTheory.FourColor
