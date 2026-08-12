import Mettapedia.GraphTheory.FourColor.GoertzelV24CorridorTransferWordReachablePumping
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSourceTransferWord

/-!
# Reachable-set pumping for the realized source Cell word

The heterogeneous word of literal source Cells has one finite bounded-profile
relation at every indexed Cell position.  The generic reachable-set theorem
therefore supplies a strictly shorter rejected relation word once the number
of cuts exceeds the number of subsets of the profile carrier.

This is the algebraic L2 conclusion only.  It does not assert that the
shortened list is realized by a source corridor or by the annular splice.
That identification remains a separate geometric use-site obligation, as does
the joint update from local Cell profiles to cumulative cut-local profiles.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24CorridorTransferWord
open GoertzelV24CorridorTransferWordReachablePumping
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSourceReachablePumpingEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- If the realized source Cell word has more cut positions than reachable
profile sets, rejection survives deletion of a nonempty algebraic subword.
The conclusion deliberately returns a relation word, not a geometric
corridor. -/
theorem exists_strictlyShorter_rejected_sourceCorridorCellTransferWord
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (initial : Finset
      SourceConsecutiveSlabInterface.LocalLayerPairCellBoundedProfile)
    (isAccepting :
      SourceConsecutiveSlabInterface.LocalLayerPairCellBoundedProfile → Prop)
    (hlarge : Fintype.card (Finset
      SourceConsecutiveSlabInterface.LocalLayerPairCellBoundedProfile) <
        blockLength - 3 + 1)
    (hfull : ¬ TransferWordAccepts
      (sourceCorridorCellTransferWord realization hcubic hrotation htwoSided
        hunique) initial isAccepting) :
    ∃ shorter : List
        (SourceConsecutiveSlabInterface.LocalLayerPairCellBoundedProfile →
          SourceConsecutiveSlabInterface.LocalLayerPairCellBoundedProfile →
            Prop),
      shorter.length < blockLength - 3 ∧
        ¬ TransferWordAccepts shorter initial isAccepting := by
  let steps := sourceCorridorCellTransferWord realization hcubic hrotation
    htwoSided hunique
  have hstepsLength : steps.length = blockLength - 3 := by
    exact sourceCorridorCellTransferWord_length realization hcubic hrotation
      htwoSided hunique
  have hlargeSteps : Fintype.card (Finset
      SourceConsecutiveSlabInterface.LocalLayerPairCellBoundedProfile) <
      steps.length + 1 := by
    simpa only [hstepsLength] using hlarge
  have hfullSteps : ¬ TransferWordAccepts steps initial isAccepting := by
    exact hfull
  rcases exists_strictlyShorter_rejected_transferWord
      steps initial isAccepting hlargeSteps hfullSteps with
    ⟨shorter, hshorter, hrejected⟩
  exact ⟨shorter, hstepsLength ▸ hshorter, hrejected⟩

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
