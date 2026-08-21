import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialPrefixProfileCompression
import Mettapedia.GraphTheory.FourColor.GoertzelV24WidthTwoFragmentReindexSplice

/-!
# Fragment-reindexed repetition in the literal serial-prefix word

The route-correct cumulative word is the heterogeneous word of literal source
Cells.  Its input profile has at most four occurrence-sensitive face
fragments.  Equality after quotienting only the arbitrary enumeration of
those fragments therefore gives a separated repeat after `422977` positions,
and the conclusion returns the explicit fragment permutation consumed by the
splice interface.

This is a sound finite-carrier bound for the actual serial word.  It is not an
exact reachable-closure computation, a factorization through the three
oriented geometric slab types, a graph-size threshold `V0`, or a verified
finite base.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24CorridorProfile
open GoertzelV24SpliceUnification
open GoertzelV24WidthTwoFragmentReindexCompression
open GoertzelV24WidthTwoFragmentReindexSplice
open GoertzelV24WidthTwoPortIncidenceCompression
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialFragmentReindexRepeatEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- A source-facing `L7` repeat for the literal heterogeneous serial word.
The complete five-field profiles agree after the returned presentation-only
fragment permutation. -/
theorem exists_reindexed_sourceCorridorSerialInputProfiles
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
    (hlarge : 4 * boundedWidthTwoFragmentReindexProfileCount 4 + 1 ≤
      blockLength - 3)
    (color : G.edgeSet → Color)
    (hcolor : ∀ (offset : Fin (blockLength - 3)) (step : Fin 2),
      color ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
        hunique offset).localLayerPrefixCrossing step) ≠ 0) :
    ∃ first second :
        Fin (4 * boundedWidthTwoFragmentReindexProfileCount 4 + 1),
      ∃ fragmentCount : Fin 5,
      ∃ left right : CorridorCutProfile 2 0 fragmentCount.val,
        first.val + 3 < second.val ∧
        sourceCorridorSerialInputBoundedProfileAt realization hcubic hrotation
            htwoSided hunique (Fin.castLE hlarge first) color
              (hcolor (Fin.castLE hlarge first)) =
          ⟨fragmentCount, left⟩ ∧
        sourceCorridorSerialInputBoundedProfileAt realization hcubic hrotation
            htwoSided hunique (Fin.castLE hlarge second) color
              (hcolor (Fin.castLE hlarge second)) =
          ⟨fragmentCount, right⟩ ∧
        ∃ permutation : Equiv.Perm (Fin fragmentCount.val),
          reindexCorridorCutProfile left (fragmentIndexing permutation) =
            right := by
  let profiles :
      Fin (4 * boundedWidthTwoFragmentReindexProfileCount 4 + 1) →
        BoundedCorridorCutProfile 2 0 4 :=
    fun offset =>
      sourceCorridorSerialInputBoundedProfileAt realization hcubic hrotation
        htwoSided hunique (Fin.castLE hlarge offset) color
          (hcolor (Fin.castLE hlarge offset))
  have hsemantic : ∀ offset,
      BoundedIsPortIncidenceSemantic (profiles offset) := by
    intro offset
    exact sourceCorridorSerialInputBoundedProfileAt_isPortIncidenceSemantic
      realization hcubic hrotation htwoSided hunique
      (Fin.castLE hlarge offset) color (hcolor (Fin.castLE hlarge offset))
  have hrepeat :=
    exists_separated_reindexed_profile_of_portIncidenceSemantic
      profiles hsemantic
  simpa only [profiles] using hrepeat

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
