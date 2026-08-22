import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialTerminalProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24TerminalAwareProfileCompression

/-!
# Lossless compression of the opened-source terminal profile

The cumulative literal-Cell recurrence retains one shared rung as a terminal
beside its two moving crossings.  This module applies the generic
terminal-aware semantic compression to that actual graph-derived profile.
Every source state satisfies the required symmetry and diagonal laws, and
equality of compressed source states reconstructs equality of all five raw
profile fields.

At the current occurrence-sensitive four-fragment bound, the exact carrier
drops from the arbitrary-matrix fallback to `12556911218688` codes.  This is
still only a lossless semantic carrier bound: it is not a measured reachable
closure, a numerical base threshold, or `BaseVerified`.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24TerminalAwareProfileCompression
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/- Keep the edge-subtype equality decision definitionally aligned with the
source-profile module whose definitions are consumed below. -/
local instance sourceEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- Every literal terminal-aware predecessor profile lies in the lossless
semantic subcarrier. -/
theorem sourceLocalLayerSerialTerminalInputBoundedProfileAt_isTerminalGraphSemantic
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :
    BoundedIsTerminalGraphSemantic
      (sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor hunique
        offset) := by
  exact regionalProfile_isTerminalGraphSemantic
    (sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique offset)
    (sourceLocalLayerSerialTerminalInputCutDataAt_portsInRegion corridor
      hunique offset)
    coloring (fun _ => web.tait _)

/-- The canonical lossless code of one actual terminal-aware source state. -/
noncomputable def sourceLocalLayerSerialTerminalInputCompressedProfileAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :
    BoundedTerminalAwareCompressedProfile 2 1 4 :=
  compressBounded
    (sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor hunique
      offset)
    (sourceLocalLayerSerialTerminalInputBoundedProfileAt_isTerminalGraphSemantic
      corridor hunique offset)

/-- No complete splice observable is lost by the source compression. -/
theorem sourceLocalLayerSerialTerminalInputBoundedProfileAt_eq_of_compressed_eq
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (left right : Fin (blockLength - 3))
    (heq : sourceLocalLayerSerialTerminalInputCompressedProfileAt corridor
        hunique left =
      sourceLocalLayerSerialTerminalInputCompressedProfileAt corridor hunique
        right) :
    sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor hunique left =
      sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor hunique
        right := by
  exact compressBounded_injective
    (sourceLocalLayerSerialTerminalInputBoundedProfileAt_isTerminalGraphSemantic
      corridor hunique left)
    (sourceLocalLayerSerialTerminalInputBoundedProfileAt_isTerminalGraphSemantic
      corridor hunique right)
    heq

/-- The actual opened-source profile word has a gap-at-least-four repeat at
the compressed semantic threshold, with equality restored in the original
five-field carrier. -/
theorem exists_equal_sourceLocalLayerSerialTerminalInputProfiles_separated
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (hlarge :
      4 * boundedTerminalAwareCompressedProfileCount 2 1 4 + 1 ≤
        blockLength - 3) :
    ∃ first second : Fin
        (4 * boundedTerminalAwareCompressedProfileCount 2 1 4 + 1),
      first.val + 3 < second.val ∧
        sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor hunique
            (Fin.castLE hlarge first) =
          sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor hunique
            (Fin.castLE hlarge second) := by
  let profiles : Fin
        (4 * boundedTerminalAwareCompressedProfileCount 2 1 4 + 1) →
      GoertzelV24BoundaryProfileFiniteState.BoundedCorridorCutProfile 2 1 4 :=
    fun offset =>
      sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor hunique
        (Fin.castLE hlarge offset)
  have hsemantic : ∀ offset,
      BoundedIsTerminalGraphSemantic (profiles offset) := by
    intro offset
    exact
      sourceLocalLayerSerialTerminalInputBoundedProfileAt_isTerminalGraphSemantic
        corridor hunique (Fin.castLE hlarge offset)
  exact exists_separated_profile_eq_of_terminalSemantic profiles hsemantic

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
