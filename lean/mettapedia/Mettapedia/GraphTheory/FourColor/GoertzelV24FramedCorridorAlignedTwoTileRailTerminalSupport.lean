import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorAlignedTwoTileTerminalProfile

/-!
# Rail terminals of an aligned source slab

The source-aligned two-tile slab has a real six-edge boundary.  Its four
transverse ports are the two source interfaces, and its two terminal ports
must be the two literal rail crossings.  This module records that latter
identification without treating a rail as part of an adjacent moving cut.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24DualPathTransversal
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorAlignedTwoTileRailTerminalSupportEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- Each terminal of the source-aligned `4 + 2` profile is one of the two
actual primal crossings of the exterior rails. -/
theorem sourceTwoTileAlignedTerminalProfileDataAt_terminalEdge_mem_railCrossingEdges
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
    (offset : Fin (blockLength - 4)) (terminal : Fin 2) :
    (sourceTwoTileAlignedTerminalProfileDataAt realization hcubic hrotation
      htwoSided hunique offset).terminalEdge terminal ∈
      sourceTwoTileRailCrossingEdgesAt realization hcubic hrotation htwoSided
        hunique offset := by
  rw [sourceTwoTileAlignedTerminalProfileDataAt_terminalEdge]
  let first := sourceTwoTileFirstInterfaceAt realization hcubic hrotation
    htwoSided hunique offset
  let second := sourceTwoTileSecondInterfaceAt realization hcubic hrotation
    htwoSided hunique offset
  let pair := sourceTwoTileRailPairAt realization hcubic hrotation htwoSided
    hunique offset
  have hrails : pair.secondRail.length + pair.firstRail.length = 2 := by
    have hsum := pair.firstRail_length_add_secondRail_length_eq_two
    omega
  let railStep : Fin (pair.secondRail.length + pair.firstRail.length) :=
    Fin.cast hrails.symm terminal
  change dualWalkCrossingEdge
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
      (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
        htwoSided hunique offset).walk
      (Fin.cast
        (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
          htwoSided hunique offset).length_eq_six.symm
        (sourceTwoTileAlignedRailCrossingIndexAt realization hcubic hrotation
          htwoSided hunique offset terminal)) ∈
      dualWalkCrossingEdges
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
        pair.firstRail ∪
      dualWalkCrossingEdges
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
        pair.secondRail
  rcases hrailStep : (finSumFinEquiv.symm railStep :
      Fin pair.secondRail.length ⊕ Fin pair.firstRail.length) with
    secondStep | firstStep
  · let firstRailStep : Fin (first.toInterface.localLayer.walk.append
        pair.secondRail).length :=
      ⟨first.toInterface.localLayer.walk.length + secondStep.val, by
        simp only [SimpleGraph.Walk.length_append]
        exact Nat.add_lt_add_left secondStep.isLt _⟩
    let throughSecondStep : Fin
        ((first.toInterface.localLayer.walk.append pair.secondRail).append
          second.toInterface.localLayer.walk.reverse).length :=
      ⟨firstRailStep.val, by
        have hsecond : second.toInterface.localLayer.walk.reverse.length = 2 := by
          rw [SimpleGraph.Walk.length_reverse,
            second.toInterface.localLayer_walk_length_eq_two]
        simp only [SimpleGraph.Walk.length_append, hsecond]
        have hstep : firstRailStep.val <
            first.toInterface.localLayer.walk.length + pair.secondRail.length := by
          simpa only [SimpleGraph.Walk.length_append] using firstRailStep.isLt
        exact lt_of_lt_of_le hstep (Nat.le_add_right _ _)⟩
    let boundaryStep : Fin
        (((first.toInterface.localLayer.walk.append pair.secondRail).append
          second.toInterface.localLayer.walk.reverse).append
            pair.firstRail.reverse).length :=
      ⟨throughSecondStep.val, by
        have hbound : throughSecondStep.val <
            ((first.toInterface.localLayer.walk.append pair.secondRail).append
              second.toInterface.localLayer.walk.reverse).length +
              pair.firstRail.reverse.length :=
          lt_of_lt_of_le throughSecondStep.isLt (Nat.le_add_right _ _)
        simpa only [SimpleGraph.Walk.length_append] using hbound⟩
    have hboundaryStep :
        Fin.cast
            (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
              htwoSided hunique offset).length_eq_six.symm
            (sourceTwoTileAlignedRailCrossingIndexAt realization hcubic
              hrotation htwoSided hunique offset terminal) = boundaryStep := by
      apply Fin.ext
      simp [sourceTwoTileAlignedRailCrossingIndexAt, pair, railStep,
        hrailStep, boundaryStep, throughSecondStep, firstRailStep, first,
        SourceConsecutiveSlabInterface.localLayer_walk_length_eq_two]
    rw [hboundaryStep]
    apply Finset.mem_union_right
    apply (mem_dualWalkCrossingEdges_iff
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
      pair.secondRail _).2
    refine ⟨secondStep, ?_⟩
    change dualWalkCrossingEdge
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
        pair.secondRail secondStep =
      dualWalkCrossingEdge
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
        (((first.toInterface.localLayer.walk.append pair.secondRail).append
          second.toInterface.localLayer.walk.reverse).append
            pair.firstRail.reverse) boundaryStep
    symm
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
                (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
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
                (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
              (first.toInterface.localLayer.walk.append pair.secondRail)
              second.toInterface.localLayer.walk.reverse firstRailStep
      _ = dualWalkCrossingEdge
          (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
          (Finset.univ : Finset
            (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
          pair.secondRail secondStep := by
          simpa [firstRailStep] using
            dualWalkCrossingEdge_append_right
              (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
              (Finset.univ : Finset
                (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
              first.toInterface.localLayer.walk pair.secondRail secondStep
  · let reverseStep : Fin pair.firstRail.reverse.length :=
      ⟨firstStep.val, by
        rw [SimpleGraph.Walk.length_reverse]
        exact firstStep.isLt⟩
    let originalStep : Fin pair.firstRail.length :=
      ⟨pair.firstRail.length - (reverseStep.val + 1), by
        have hfirstLt : firstStep.val < pair.firstRail.length := firstStep.isLt
        omega⟩
    let throughSecondLength :=
      ((first.toInterface.localLayer.walk.append pair.secondRail).append
        second.toInterface.localLayer.walk.reverse).length
    let boundaryStep : Fin
        (((first.toInterface.localLayer.walk.append pair.secondRail).append
          second.toInterface.localLayer.walk.reverse).append
            pair.firstRail.reverse).length :=
      ⟨throughSecondLength + reverseStep.val, by
        have hstep : reverseStep.val < pair.firstRail.reverse.length :=
          reverseStep.isLt
        simpa [throughSecondLength, SimpleGraph.Walk.length_append] using
          Nat.add_lt_add_left hstep throughSecondLength⟩
    have hboundaryStep :
        Fin.cast
            (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
              htwoSided hunique offset).length_eq_six.symm
            (sourceTwoTileAlignedRailCrossingIndexAt realization hcubic
              hrotation htwoSided hunique offset terminal) = boundaryStep := by
      apply Fin.ext
      simp [sourceTwoTileAlignedRailCrossingIndexAt, pair, railStep,
        hrailStep, boundaryStep, throughSecondLength, reverseStep, first,
        SourceConsecutiveSlabInterface.localLayer_walk_length_eq_two]
    rw [hboundaryStep]
    apply Finset.mem_union_left
    apply (mem_dualWalkCrossingEdges_iff
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
      pair.firstRail _).2
    refine ⟨originalStep, ?_⟩
    change dualWalkCrossingEdge
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
        pair.firstRail originalStep =
      dualWalkCrossingEdge
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
        (((first.toInterface.localLayer.walk.append pair.secondRail).append
          second.toInterface.localLayer.walk.reverse).append
            pair.firstRail.reverse) boundaryStep
    symm
    calc
      _ = dualWalkCrossingEdge
          (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
          (Finset.univ : Finset
            (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
          pair.firstRail.reverse reverseStep := by
          simpa [boundaryStep, throughSecondLength] using
            dualWalkCrossingEdge_append_right
              (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
              (Finset.univ : Finset
                (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
              ((first.toInterface.localLayer.walk.append pair.secondRail).append
                second.toInterface.localLayer.walk.reverse)
              pair.firstRail.reverse reverseStep
      _ = dualWalkCrossingEdge
          (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
          (Finset.univ : Finset
            (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
          pair.firstRail originalStep := by
          simpa [originalStep, reverseStep] using
            (dualWalkCrossingEdge_unreverse
              (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
              (Finset.univ : Finset
                (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
              pair.firstRail reverseStep).symm

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
