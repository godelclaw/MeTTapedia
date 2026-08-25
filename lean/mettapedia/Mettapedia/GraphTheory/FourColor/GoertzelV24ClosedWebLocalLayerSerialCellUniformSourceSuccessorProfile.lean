import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellUniformSuccessorLetter
import Mettapedia.GraphTheory.FourColor.GoertzelV24SourceCorridorProfile

/-!
# Projecting the literal successor letter to the source two-pair profile

The finite successor letter internally retains all three two-color component
families.  The manuscript-facing output forgets `beta ∪ gamma` and keeps only
`alpha ∪ beta` and `alpha ∪ gamma`.

This adapter is stated in the standard color-name gauge
`(alpha, beta, gamma) = (a, b, c)`.  Applying it to an arbitrary good word
still requires the separate simultaneous color-normalization theorem; no
choice of a majority color is hidden in this definition.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellUniformSuccessorLetter

open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24SourceCorridorProfile
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraphDartRotation

/-- The source-visible output of one finite literal Cell successor letter in
the standard `alpha/beta/gamma` color-name gauge. -/
noncomputable def
    SourceLocalLayerSerialCellUniformSuccessorLetter.standardGaugeSourceProfile
    (letter : SourceLocalLayerSerialCellUniformSuccessorLetter) :
    BoundedSourceCorridorCutProfile 2 1 4 :=
  toBoundedSourceProfile letter.outputProfile

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance cellUniformSourceSuccessorProfileEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance cellUniformSourceSuccessorProfileOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- The projected letter still decodes exactly to the projected literal next
profile.  Only the deliberately extra `beta ∪ gamma` coordinate is forgotten. -/
theorem sourceLocalLayerSerialCellUniformSuccessorLetterAt_standardGaugeSourceProfile_eq
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
    (sourceLocalLayerSerialCellUniformSuccessorLetterAt graphData minimal caps
      coloring web corridor hunique offset hnext).standardGaugeSourceProfile =
      toBoundedSourceProfile
        (sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor hunique
          (sourceLocalLayerNextOffset offset hnext)) := by
  apply congrArg toBoundedSourceProfile
  exact sourceLocalLayerSerialCellUniformSuccessorLetterAt_outputProfile_eq
    graphData minimal caps coloring web corridor hunique offset hnext

end

end GoertzelV24ClosedWebLocalLayerSerialCellUniformSuccessorLetter

end Mettapedia.GraphTheory.FourColor
