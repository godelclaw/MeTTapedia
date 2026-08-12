import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorAlignedTwoTileSerialIndex
import Mettapedia.GraphTheory.FourColor.GoertzelV24CorridorProfileRestriction

/-!
# Transverse restrictions of the source-aligned two-tile profile

The real aligned rail cycle has six crossing coordinates.  Its first and
second transverse blocks are the consecutive two-edge interfaces of the
source serial word.  This file restricts the complete five-field profile of
that cycle along those two literal embeddings.

Both restrictions retain the aligned boundary's regional fragment carrier.
They are therefore restrictions of one six-port profile, not identifications
with the cumulative prefix profiles computed on different edge regions.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24CorridorProfileRestriction
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorAlignedTwoTileProfileRestrictionEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- Restrict the aligned boundary data to its first transverse source cut.
The edge region and all face-fragment coordinates remain unchanged. -/
noncomputable def sourceTwoTileAlignedFirstRestrictedProfileDataAt
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
    (offset : Fin (blockLength - 4)) :=
  GraphCorridorCutData.restrictCrossings
    (sourceTwoTileAlignedOrderedProfileDataAt realization hcubic hrotation
      htwoSided hunique offset)
    (sourceTwoTileAlignedFirstProfileIndexAt realization hcubic hrotation
      htwoSided hunique offset)

/-- Restrict the aligned boundary data to its second transverse source cut.
The reversal and variable rail length are already absorbed by its embedding. -/
noncomputable def sourceTwoTileAlignedSecondRestrictedProfileDataAt
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
    (offset : Fin (blockLength - 4)) :=
  GraphCorridorCutData.restrictCrossings
    (sourceTwoTileAlignedOrderedProfileDataAt realization hcubic hrotation
      htwoSided hunique offset)
    (sourceTwoTileAlignedSecondProfileIndexAt realization hcubic hrotation
      htwoSided hunique offset)

/-- The first restricted raw cut uses the literal incoming source crossings. -/
@[simp]
theorem sourceTwoTileAlignedFirstRestrictedProfileDataAt_crossingEdge
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
    (offset : Fin (blockLength - 4)) (step : Fin 2) :
    (sourceTwoTileAlignedFirstRestrictedProfileDataAt realization hcubic
        hrotation htwoSided hunique offset).crossingEdge step =
      (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        (sourceSlabRailStartOffset offset)).localLayerPrefixCrossing step := by
  exact sourceTwoTileAlignedOrderedProfileDataAt_crossingEdge_first_serial
    realization hcubic hrotation htwoSided hunique offset step

/-- The second restricted raw cut uses the literal following source
crossings. -/
@[simp]
theorem sourceTwoTileAlignedSecondRestrictedProfileDataAt_crossingEdge
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
    (offset : Fin (blockLength - 4)) (step : Fin 2) :
    (sourceTwoTileAlignedSecondRestrictedProfileDataAt realization hcubic
        hrotation htwoSided hunique offset).crossingEdge step =
      (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        (sourceSlabRailFinishOffset offset)).localLayerPrefixCrossing step := by
  exact sourceTwoTileAlignedOrderedProfileDataAt_crossingEdge_second_serial
    realization hcubic hrotation htwoSided hunique offset step

/-- Computing the full profile and then exposing the first source interface
is exactly the same as first restricting the raw graph cut.  All five profile
fields, not only the boundary colors, are covered by this equality. -/
theorem sourceTwoTileAlignedOrderedProfile_restrict_first
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
    (offset : Fin (blockLength - 4))
    (color : G.edgeSet → Color)
    (hcolor : ∀ crossing,
      color ((sourceTwoTileAlignedOrderedProfileDataAt realization hcubic
        hrotation htwoSided hunique offset).crossingEdge crossing) ≠ 0) :
    CorridorCutProfile.restrictCrossings
        ((sourceTwoTileAlignedOrderedProfileDataAt realization hcubic hrotation
          htwoSided hunique offset).regionalProfile color hcolor)
        (sourceTwoTileAlignedFirstProfileIndexAt realization hcubic hrotation
          htwoSided hunique offset) =
      (sourceTwoTileAlignedFirstRestrictedProfileDataAt realization hcubic
        hrotation htwoSided hunique offset).regionalProfile color
          (fun step => hcolor
            (sourceTwoTileAlignedFirstProfileIndexAt realization hcubic
              hrotation htwoSided hunique offset step)) := by
  exact GraphCorridorCutData.restrictCrossings_regionalProfile
    (sourceTwoTileAlignedOrderedProfileDataAt realization hcubic hrotation
      htwoSided hunique offset)
    (sourceTwoTileAlignedFirstProfileIndexAt realization hcubic hrotation
      htwoSided hunique offset) color hcolor

/-- The analogous equality for the following source interface, including the
reversal used by the aligned closed cycle. -/
theorem sourceTwoTileAlignedOrderedProfile_restrict_second
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
    (offset : Fin (blockLength - 4))
    (color : G.edgeSet → Color)
    (hcolor : ∀ crossing,
      color ((sourceTwoTileAlignedOrderedProfileDataAt realization hcubic
        hrotation htwoSided hunique offset).crossingEdge crossing) ≠ 0) :
    CorridorCutProfile.restrictCrossings
        ((sourceTwoTileAlignedOrderedProfileDataAt realization hcubic hrotation
          htwoSided hunique offset).regionalProfile color hcolor)
        (sourceTwoTileAlignedSecondProfileIndexAt realization hcubic hrotation
          htwoSided hunique offset) =
      (sourceTwoTileAlignedSecondRestrictedProfileDataAt realization hcubic
        hrotation htwoSided hunique offset).regionalProfile color
          (fun step => hcolor
            (sourceTwoTileAlignedSecondProfileIndexAt realization hcubic
              hrotation htwoSided hunique offset step)) := by
  exact GraphCorridorCutData.restrictCrossings_regionalProfile
    (sourceTwoTileAlignedOrderedProfileDataAt realization hcubic hrotation
      htwoSided hunique offset)
    (sourceTwoTileAlignedSecondProfileIndexAt realization hcubic hrotation
      htwoSided hunique offset) color hcolor

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
