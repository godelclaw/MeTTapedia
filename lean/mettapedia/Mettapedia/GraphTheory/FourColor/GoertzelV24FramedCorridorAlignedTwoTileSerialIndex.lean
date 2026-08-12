import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorAlignedTwoTileProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSourceRailPair

/-!
# Serial indices of the source-aligned two-tile boundary

The aligned two-tile boundary is built from two consecutive source
interfaces, while the cumulative transfer word indexes those interfaces by
`Fin (blockLength - 3)`.  This file identifies the two presentations at their
literal source positions.  The result is coordinate bookkeeping only: it
does not identify either cumulative region with the retained side of the
six-edge boundary and does not turn that retained side into a Cell generator.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationVertexCutProfile
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorAlignedTwoTileSerialIndexEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The first interior used by the two-tile construction is definitionally
the source-transfer interior at the rail step's starting index. -/
theorem sourceTwoTileLeftInterior_eq_sourceSlabRailStart
    {blockLength : Nat} (offset : Fin (blockLength - 4)) :
    sourceTwoTileLeftInterior offset =
      sourceSlabLeftInterior (sourceSlabRailStartOffset offset) := by
  rfl

/-- The first interface of the aligned two-tile boundary is exactly the
first indexed interface of the serial source word. -/
theorem sourceTwoTileFirstInterfaceAt_toInterface_eq_sourceSlabInterfaceAt
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
    (offset : Fin (blockLength - 4)) :
    (sourceTwoTileFirstInterfaceAt realization hcubic hrotation htwoSided
        hunique offset).toInterface =
      sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        (sourceSlabRailStartOffset offset) := by
  rfl

/-- Before reindexing by the adjacent source-word position, the second
two-tile interface is exactly the already named next rail interface. -/
theorem sourceTwoTileSecondInterfaceAt_eq_sourceSlabRailNextCornerInterfaceAt
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
    (offset : Fin (blockLength - 4)) :
    sourceTwoTileSecondInterfaceAt realization hcubic hrotation htwoSided
        hunique offset =
      sourceSlabRailNextCornerInterfaceAt realization hcubic hrotation
        htwoSided hunique offset := by
  rfl

/-- The second interface of the aligned boundary is the next indexed
interface of the serial source word. -/
theorem sourceTwoTileSecondInterfaceAt_toInterface_eq_sourceSlabInterfaceAt
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
    (offset : Fin (blockLength - 4)) :
    (sourceTwoTileSecondInterfaceAt realization hcubic hrotation htwoSided
        hunique offset).toInterface =
      sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        (sourceSlabRailFinishOffset offset) := by
  have hinterior := sourceSlabLeftInterior_railFinish_eq_next offset
  cases hinterior
  rfl

/-- The first transverse block of the aligned cycle is the incoming cut at
the starting position of the serial source word. -/
theorem sourceTwoTileAlignedOrderedCrossing_first_serial
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
    (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
        htwoSided hunique offset).orderedCrossing
          (sourceTwoTileAlignedFirstCrossingIndex step) =
      (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        (sourceSlabRailStartOffset offset)).localLayerPrefixCrossing step := by
  rw [sourceTwoTileAlignedOrderedCrossing_first]
  rw [sourceTwoTileFirstInterfaceAt_toInterface_eq_sourceSlabInterfaceAt]
  rfl

/-- The reversed second transverse block of the aligned cycle is the incoming
cut at the following position of the serial source word. -/
theorem sourceTwoTileAlignedOrderedCrossing_second_serial
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
    (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
        htwoSided hunique offset).orderedCrossing
          (sourceTwoTileAlignedSecondCrossingIndexAt realization hcubic
            hrotation htwoSided hunique offset step) =
      (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        (sourceSlabRailFinishOffset offset)).localLayerPrefixCrossing step := by
  rw [sourceTwoTileAlignedOrderedCrossing_second]
  rw [sourceTwoTileSecondInterfaceAt_toInterface_eq_sourceSlabInterfaceAt]
  rfl

/-- The first transverse coordinate, retyped from the source's literal
six-step order to the dependent crossing carrier of the aligned profile. -/
noncomputable def sourceTwoTileAlignedFirstProfileIndexAt
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
    Fin (Fintype.card (VertexSetCrossingEdge
      embedded.cellulation.rotation.toRotationSystem
      (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
        htwoSided hunique offset).componentSide)) :=
  Fin.cast
    (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
      htwoSided hunique offset).crossingCard_eq_six.symm
    (sourceTwoTileAlignedFirstCrossingIndex step)

/-- The second transverse coordinate in the same dependent profile carrier. -/
noncomputable def sourceTwoTileAlignedSecondProfileIndexAt
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
    Fin (Fintype.card (VertexSetCrossingEdge
      embedded.cellulation.rotation.toRotationSystem
      (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
        htwoSided hunique offset).componentSide)) :=
  Fin.cast
    (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
      htwoSided hunique offset).crossingCard_eq_six.symm
    (sourceTwoTileAlignedSecondCrossingIndexAt realization hcubic hrotation
      htwoSided hunique offset step)

/-- The raw aligned profile names the serial word's first incoming cut at
the first transverse coordinates. -/
theorem sourceTwoTileAlignedOrderedProfileDataAt_crossingEdge_first_serial
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
    (sourceTwoTileAlignedOrderedProfileDataAt realization hcubic hrotation
        htwoSided hunique offset).crossingEdge
          (sourceTwoTileAlignedFirstProfileIndexAt realization hcubic
            hrotation htwoSided hunique offset step) =
      (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        (sourceSlabRailStartOffset offset)).localLayerPrefixCrossing step := by
  unfold sourceTwoTileAlignedOrderedProfileDataAt
  rw [(sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
    htwoSided hunique offset).orderedProfileData_crossingEdge]
  change
    (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
        htwoSided hunique offset).orderedCrossing
          (sourceTwoTileAlignedFirstCrossingIndex step) = _
  exact sourceTwoTileAlignedOrderedCrossing_first_serial realization hcubic
    hrotation htwoSided hunique offset step

/-- The raw aligned profile likewise names the following serial input cut at
the second transverse coordinates. -/
theorem sourceTwoTileAlignedOrderedProfileDataAt_crossingEdge_second_serial
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
    (sourceTwoTileAlignedOrderedProfileDataAt realization hcubic hrotation
        htwoSided hunique offset).crossingEdge
          (sourceTwoTileAlignedSecondProfileIndexAt realization hcubic
            hrotation htwoSided hunique offset step) =
      (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        (sourceSlabRailFinishOffset offset)).localLayerPrefixCrossing step := by
  unfold sourceTwoTileAlignedOrderedProfileDataAt
  rw [(sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
    htwoSided hunique offset).orderedProfileData_crossingEdge]
  change
    (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
        htwoSided hunique offset).orderedCrossing
          (sourceTwoTileAlignedSecondCrossingIndexAt realization hcubic
            hrotation htwoSided hunique offset step) = _
  exact sourceTwoTileAlignedOrderedCrossing_second_serial realization hcubic
    hrotation htwoSided hunique offset step

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
