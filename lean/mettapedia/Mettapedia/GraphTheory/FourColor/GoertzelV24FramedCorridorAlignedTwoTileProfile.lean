import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorAlignedTwoTileComponent
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorPrefixBoundaryProfile

/-!
# Ordered profile of the source-aligned two-tile boundary

The source rail pair and the two transverse layers already form one literal
six-step simple facial-dual cycle.  This file packages that particular cycle
in the existing two-tile boundary interface, so its oriented component,
source order, and complete five-field profile are available without choosing
a second cycle.

No equality with the independently selected two-tile boundary is asserted.
The only identification below is definitional: the packaged walk and crossing
support are the source-aligned walk and support themselves.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24CleanHexCorridor
open GoertzelV24ClosedWebProfileFiniteness
open GoertzelV24DualPathTransversal
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorAlignedTwoTileProfileEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The actual source-aligned rail cycle, viewed through the generic ordered
two-tile boundary interface. -/
noncomputable def sourceTwoTileAlignedLayerBoundaryAt
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
    SourceCornerAlignedTwoTileLayerBoundary
      (sourceTwoTileFirstInterfaceAt realization hcubic hrotation htwoSided
        hunique offset)
      (sourceTwoTileSecondInterfaceAt realization hcubic hrotation htwoSided
        hunique offset) where
  walk := sourceTwoTileAlignedBoundaryWalkAt realization hcubic hrotation
    htwoSided hunique offset
  isCycle := sourceTwoTileAlignedBoundaryWalkAt_isCycle realization hcubic
    hrotation htwoSided hunique offset
  length_eq_six := sourceTwoTileAlignedBoundaryWalkAt_length_eq_six realization
    hcubic hrotation htwoSided hunique offset

/-- The packaged boundary has definitionally the literal source-aligned walk. -/
@[simp]
theorem sourceTwoTileAlignedLayerBoundaryAt_walk
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
    (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
      htwoSided hunique offset).walk =
      sourceTwoTileAlignedBoundaryWalkAt realization hcubic hrotation
        htwoSided hunique offset :=
  rfl

/-- Its finite crossing support is exactly the previously proved aligned
`2 + 2 + 2` support. -/
@[simp]
theorem sourceTwoTileAlignedLayerBoundaryAt_cutEdges
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
    (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
      htwoSided hunique offset).cutEdges =
      sourceTwoTileAlignedBoundaryCrossingEdgesAt realization hcubic hrotation
        htwoSided hunique offset :=
  rfl

/-- The first transverse layer occupies the first two coordinates of the
literal aligned boundary. -/
def sourceTwoTileAlignedFirstCrossingIndex (step : Fin 2) : Fin 6 :=
  ⟨step.val, by omega⟩

/-- The second transverse layer occurs after the first layer and the second
exterior rail.  Its orientation is reversed in the closed boundary walk. -/
noncomputable def sourceTwoTileAlignedSecondCrossingIndexAt
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
    (offset : Fin (blockLength - 4)) (step : Fin 2) : Fin 6 := by
  let first := sourceTwoTileFirstInterfaceAt realization hcubic hrotation
    htwoSided hunique offset
  let second := sourceTwoTileSecondInterfaceAt realization hcubic hrotation
    htwoSided hunique offset
  let pair := sourceTwoTileRailPairAt realization hcubic hrotation htwoSided
    hunique offset
  let secondStep : Fin second.toInterface.localLayer.walk.length :=
    Fin.cast second.toInterface.localLayer_walk_length_eq_two.symm step
  exact ⟨first.toInterface.localLayer.walk.length + pair.secondRail.length +
      (second.toInterface.localLayer.walk.length - (secondStep.val + 1)), by
    change 2 + pair.secondRail.length + (2 - (step.val + 1)) < 6
    have hrail := pair.secondRail_length_le_two
    omega⟩

/-- Reading the first two profile coordinates recovers the first literal
source transversal, with no finite-carrier permutation. -/
theorem sourceTwoTileAlignedOrderedCrossing_first
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
      (sourceTwoTileFirstInterfaceAt realization hcubic hrotation htwoSided
        hunique offset).toInterface.localLayerPrefixCrossing step := by
  let first := sourceTwoTileFirstInterfaceAt realization hcubic hrotation
    htwoSided hunique offset
  let second := sourceTwoTileSecondInterfaceAt realization hcubic hrotation
    htwoSided hunique offset
  let pair := sourceTwoTileRailPairAt realization hcubic hrotation htwoSided
    hunique offset
  let firstStep : Fin first.toInterface.localLayer.walk.length :=
    Fin.cast first.toInterface.localLayer_walk_length_eq_two.symm step
  let firstRailStep : Fin
      (first.toInterface.localLayer.walk.append pair.secondRail).length :=
    ⟨firstStep.val, by
      rw [SimpleGraph.Walk.length_append]
      omega⟩
  let throughSecondStep : Fin
      ((first.toInterface.localLayer.walk.append pair.secondRail).append
        second.toInterface.localLayer.walk.reverse).length :=
    ⟨firstRailStep.val, by
      have hfirstRailStep := firstRailStep.isLt
      simp only [SimpleGraph.Walk.length_append] at hfirstRailStep ⊢
      omega⟩
  let boundaryStep : Fin
      (((first.toInterface.localLayer.walk.append pair.secondRail).append
        second.toInterface.localLayer.walk.reverse).append
          pair.firstRail.reverse).length :=
    ⟨throughSecondStep.val, by
      have hthroughSecondStep := throughSecondStep.isLt
      simp only [SimpleGraph.Walk.length_append] at hthroughSecondStep ⊢
      omega⟩
  change dualWalkCrossingEdge
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
      (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
        htwoSided hunique offset).walk
      (Fin.cast
        (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
          htwoSided hunique offset).length_eq_six.symm
        (sourceTwoTileAlignedFirstCrossingIndex step)) = _
  have hboundaryStep :
      Fin.cast
          (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
            htwoSided hunique offset).length_eq_six.symm
          (sourceTwoTileAlignedFirstCrossingIndex step) = boundaryStep := by
    apply Fin.ext
    rfl
  rw [hboundaryStep]
  change dualWalkCrossingEdge
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
      (((first.toInterface.localLayer.walk.append pair.secondRail).append
        second.toInterface.localLayer.walk.reverse).append
          pair.firstRail.reverse) boundaryStep =
    dualWalkCrossingEdge
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
      first.toInterface.localLayer.walk firstStep
  calc
    _ = dualWalkCrossingEdge
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
        ((first.toInterface.localLayer.walk.append pair.secondRail).append
          second.toInterface.localLayer.walk.reverse) throughSecondStep := by
          simpa [boundaryStep] using
            dualWalkCrossingEdge_append_left
              (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
              (Finset.univ : Finset
                (OrbitFace embedded.cellulation.rotation.toRotationSystem))
              hunique
              ((first.toInterface.localLayer.walk.append pair.secondRail).append
                second.toInterface.localLayer.walk.reverse)
              pair.firstRail.reverse throughSecondStep
    _ = dualWalkCrossingEdge
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
        (first.toInterface.localLayer.walk.append pair.secondRail)
          firstRailStep := by
          simpa [throughSecondStep] using
            dualWalkCrossingEdge_append_left
              (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
              (Finset.univ : Finset
                (OrbitFace embedded.cellulation.rotation.toRotationSystem))
              hunique (first.toInterface.localLayer.walk.append pair.secondRail)
              second.toInterface.localLayer.walk.reverse firstRailStep
    _ = dualWalkCrossingEdge
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
        first.toInterface.localLayer.walk firstStep := by
          simpa [firstRailStep] using
            dualWalkCrossingEdge_append_left
              (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
              (Finset.univ : Finset
                (OrbitFace embedded.cellulation.rotation.toRotationSystem))
              hunique first.toInterface.localLayer.walk pair.secondRail firstStep

/-- Reading the second transverse block recovers the next literal source
transversal.  The `Fin 6` coordinate records both the variable rail length and
the reversal used to close the aligned cycle. -/
theorem sourceTwoTileAlignedOrderedCrossing_second
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
      (sourceTwoTileSecondInterfaceAt realization hcubic hrotation htwoSided
        hunique offset).toInterface.localLayerPrefixCrossing step := by
  let first := sourceTwoTileFirstInterfaceAt realization hcubic hrotation
    htwoSided hunique offset
  let second := sourceTwoTileSecondInterfaceAt realization hcubic hrotation
    htwoSided hunique offset
  let pair := sourceTwoTileRailPairAt realization hcubic hrotation htwoSided
    hunique offset
  let secondStep : Fin second.toInterface.localLayer.walk.length :=
    Fin.cast second.toInterface.localLayer_walk_length_eq_two.symm step
  let reverseStep : Fin second.toInterface.localLayer.walk.reverse.length :=
    ⟨second.toInterface.localLayer.walk.length - (secondStep.val + 1), by
      rw [SimpleGraph.Walk.length_reverse]
      omega⟩
  let throughSecondStep : Fin
      ((first.toInterface.localLayer.walk.append pair.secondRail).append
        second.toInterface.localLayer.walk.reverse).length :=
    ⟨(first.toInterface.localLayer.walk.append pair.secondRail).length +
        reverseStep.val, by
      simp only [SimpleGraph.Walk.length_append]
      exact Nat.add_lt_add_left reverseStep.isLt _⟩
  let boundaryStep : Fin
      (((first.toInterface.localLayer.walk.append pair.secondRail).append
        second.toInterface.localLayer.walk.reverse).append
          pair.firstRail.reverse).length :=
    ⟨throughSecondStep.val, by
      have hthroughSecondStep := throughSecondStep.isLt
      simp only [SimpleGraph.Walk.length_append] at hthroughSecondStep ⊢
      omega⟩
  change dualWalkCrossingEdge
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
      (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
        htwoSided hunique offset).walk
      (Fin.cast
        (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
          htwoSided hunique offset).length_eq_six.symm
        (sourceTwoTileAlignedSecondCrossingIndexAt realization hcubic hrotation
          htwoSided hunique offset step)) = _
  have hboundaryStep :
      Fin.cast
          (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
            htwoSided hunique offset).length_eq_six.symm
          (sourceTwoTileAlignedSecondCrossingIndexAt realization hcubic
            hrotation htwoSided hunique offset step) = boundaryStep := by
    apply Fin.ext
    change first.toInterface.localLayer.walk.length + pair.secondRail.length +
        (second.toInterface.localLayer.walk.length - (secondStep.val + 1)) =
      (first.toInterface.localLayer.walk.append pair.secondRail).length +
        reverseStep.val
    simp only [SimpleGraph.Walk.length_append]
    rfl
  rw [hboundaryStep]
  change dualWalkCrossingEdge
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
      (((first.toInterface.localLayer.walk.append pair.secondRail).append
        second.toInterface.localLayer.walk.reverse).append
          pair.firstRail.reverse) boundaryStep =
    dualWalkCrossingEdge
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
      second.toInterface.localLayer.walk secondStep
  calc
    _ = dualWalkCrossingEdge
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
        ((first.toInterface.localLayer.walk.append pair.secondRail).append
          second.toInterface.localLayer.walk.reverse) throughSecondStep := by
          simpa [boundaryStep] using
            dualWalkCrossingEdge_append_left
              (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
              (Finset.univ : Finset
                (OrbitFace embedded.cellulation.rotation.toRotationSystem))
              hunique
              ((first.toInterface.localLayer.walk.append pair.secondRail).append
                second.toInterface.localLayer.walk.reverse)
              pair.firstRail.reverse throughSecondStep
    _ = dualWalkCrossingEdge
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
        second.toInterface.localLayer.walk.reverse reverseStep := by
          simpa [throughSecondStep] using
            dualWalkCrossingEdge_append_right
              (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
              (Finset.univ : Finset
                (OrbitFace embedded.cellulation.rotation.toRotationSystem))
              hunique (first.toInterface.localLayer.walk.append pair.secondRail)
              second.toInterface.localLayer.walk.reverse reverseStep
    _ = dualWalkCrossingEdge
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
        second.toInterface.localLayer.walk secondStep := by
          simpa [reverseStep] using
            dualWalkCrossingEdge_reverse
              (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
              (Finset.univ : Finset
                (OrbitFace embedded.cellulation.rotation.toRotationSystem))
              hunique second.toInterface.localLayer.walk secondStep


/-- The complete graph-derived profile data of the actual rail cycle, with
ports ordered by that cycle rather than by an arbitrary finite equivalence. -/
noncomputable def sourceTwoTileAlignedOrderedProfileDataAt
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
  (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation htwoSided
    hunique offset).orderedProfileData

/-- The corresponding finite L7 state retains cut colors, tracked
connectivity, face continuation, fragment incidence, and capped face length
on the literal aligned boundary. -/
noncomputable def sourceTwoTileAlignedLayerDepthProfile
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
    (coloring : embedded.cellulation.rotation.toRotationSystem.EdgeColoring Color)
    (hcoloring : embedded.cellulation.rotation.toRotationSystem.IsTaitEdgeColoring
      coloring) :
    ClosedWebDepthProfile 6 :=
  (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation htwoSided
    hunique offset).orderedDepthProfile coloring hcoloring

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
