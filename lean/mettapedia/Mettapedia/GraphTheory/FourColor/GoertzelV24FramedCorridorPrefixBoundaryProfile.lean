import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorLocalLayerPair
import Mettapedia.GraphTheory.FourColor.GoertzelV24HexCorridorPrefixProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24RegionalBoundaryProfileFiniteState

/-!
# Finite profiles on source corridor cross-sections

A source Cell has two two-edge cross-sections: the local layer through its
current central face and the next layer through the following central face.
Both crossing lists lie in their literal cumulative corridor prefixes.  This
file places the full graph-derived profile on those two actual interfaces.

The four-edge closed loop surrounding the Cell is not used as a profile
carrier here.  It is the boundary of the generating morphism, whereas the
transfer state lives on either two-edge cross-section.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24DualPathTransversal
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorPrefixProfile
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance corridorPrefixBoundaryProfileGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

namespace SourceConsecutiveSlabInterface

variable {source : SourceTrail G}
  {embedded : source.AnnularEmbedding} {blockLength : Nat}
  {realization : BoundaryCleanCorridorRealization embedded blockLength}
  {htwoSided : OrbitFacesTwoSided
    embedded.cellulation.rotation.toRotationSystem}
  {hunique : PairwiseUniqueSharedInteriorEdges
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
    (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
  {leftInterior : CorridorInterior blockLength}
  {hnext : leftInterior.center.val + 2 < blockLength}

/-- The two source-ordered crossings of the Cell's left interface. -/
noncomputable def localLayerPrefixCrossing
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) (step : Fin 2) : G.edgeSet :=
  interface.localLayer.crossingEdge hunique
    (Fin.cast interface.localLayer_walk_length_eq_two.symm step)

/-- The two source-ordered crossings of the Cell's right interface. -/
noncomputable def nextLocalLayerPrefixCrossing
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) (step : Fin 2) : G.edgeSet :=
  interface.nextLocalLayer.crossingEdge hunique
    (Fin.cast interface.nextLocalLayer_walk_length_eq_two.symm step)

/-- Both crossings of the left interface lie on the current central face and
hence in the cumulative prefix ending at that face. -/
theorem localLayerPrefixCrossing_mem_prefixEdgeRegion
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) (step : Fin 2) :
    interface.localLayerPrefixCrossing step ∈
      corridorPrefixEdgeRegion
        realization.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        (leftInterior.center.val + 1) := by
  let cutStep : Fin interface.localLayer.walk.length :=
    Fin.cast interface.localLayer_walk_length_eq_two.symm step
  have hcases : cutStep.val = 0 ∨ cutStep.val = 1 := by
    change step.val = 0 ∨ step.val = 1
    omega
  have hcenter : interface.localLayerPrefixCrossing step ∈ orbitFaceBoundary
      embedded.cellulation.rotation.toRotationSystem
      interface.centerLayerFace.1 := by
    change dualWalkCrossingEdge
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
      interface.localLayer.walk cutStep ∈ _
    rcases hcases with hzero | hone
    · have hstep : cutStep = ⟨0, by
          rw [interface.localLayer_walk_length_eq_two]
          omega⟩ := by
        apply Fin.ext
        exact hzero
      rw [hstep]
      simpa [localLayer, localLayerWalk] using
        (dualWalkCrossingEdge_mem_rightFace
          (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
          (Finset.univ : Finset
            (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
          interface.localLayer.walk
          ⟨0, by rw [interface.localLayer_walk_length_eq_two]; omega⟩)
    · have hstep : cutStep = ⟨1, by
          rw [interface.localLayer_walk_length_eq_two]
          omega⟩ := by
        apply Fin.ext
        exact hone
      rw [hstep]
      simpa [localLayer, localLayerWalk] using
        (dualWalkCrossingEdge_mem_leftFace
          (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
          (Finset.univ : Finset
            (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
          interface.localLayer.walk
          ⟨1, by rw [interface.localLayer_walk_length_eq_two]; omega⟩)
  apply corridorFaceBoundary_subset_prefixEdgeRegion
    realization.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
    (leftInterior.center.val + 1) leftInterior.center (by omega)
  simpa [centerLayerFace] using hcenter

/-- Both crossings of the right interface lie on the next central face and
hence in the cumulative prefix ending at that face. -/
theorem nextLocalLayerPrefixCrossing_mem_prefixEdgeRegion
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) (step : Fin 2) :
    interface.nextLocalLayerPrefixCrossing step ∈
      corridorPrefixEdgeRegion
        realization.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        (leftInterior.center.val + 2) := by
  let cutStep : Fin interface.nextLocalLayer.walk.length :=
    Fin.cast interface.nextLocalLayer_walk_length_eq_two.symm step
  have hcases : cutStep.val = 0 ∨ cutStep.val = 1 := by
    change step.val = 0 ∨ step.val = 1
    omega
  have hcenter : interface.nextLocalLayerPrefixCrossing step ∈ orbitFaceBoundary
      embedded.cellulation.rotation.toRotationSystem
      interface.nextCenterLayerFace.1 := by
    change dualWalkCrossingEdge
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
      interface.nextLocalLayer.walk cutStep ∈ _
    rcases hcases with hzero | hone
    · have hstep : cutStep = ⟨0, by
          rw [interface.nextLocalLayer_walk_length_eq_two]
          omega⟩ := by
        apply Fin.ext
        exact hzero
      rw [hstep]
      simpa [nextLocalLayer, nextLocalLayerWalk] using
        (dualWalkCrossingEdge_mem_rightFace
          (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
          (Finset.univ : Finset
            (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
          interface.nextLocalLayer.walk
          ⟨0, by rw [interface.nextLocalLayer_walk_length_eq_two]; omega⟩)
    · have hstep : cutStep = ⟨1, by
          rw [interface.nextLocalLayer_walk_length_eq_two]
          omega⟩ := by
        apply Fin.ext
        exact hone
      rw [hstep]
      simpa [nextLocalLayer, nextLocalLayerWalk] using
        (dualWalkCrossingEdge_mem_leftFace
          (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
          (Finset.univ : Finset
            (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
          interface.nextLocalLayer.walk
          ⟨1, by rw [interface.nextLocalLayer_walk_length_eq_two]; omega⟩)
  apply corridorFaceBoundary_subset_prefixEdgeRegion
    realization.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
    (leftInterior.center.val + 2)
    (nextCorridorInterior leftInterior hnext).center (by
      change leftInterior.center.val + 1 < leftInterior.center.val + 2
      omega)
  simpa [nextCenterLayerFace] using hcenter

theorem localLayerPrefixCrossing_injective
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    Function.Injective interface.localLayerPrefixCrossing := by
  intro first second heq
  apply Fin.cast_injective interface.localLayer_walk_length_eq_two.symm
  apply interface.localLayer.crossingEdge_injective
    (orbitFace_incidence_le_two
      embedded.cellulation.rotation.toRotationSystem) hunique
  simpa [localLayerPrefixCrossing] using heq

theorem nextLocalLayerPrefixCrossing_injective
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    Function.Injective interface.nextLocalLayerPrefixCrossing := by
  intro first second heq
  apply Fin.cast_injective interface.nextLocalLayer_walk_length_eq_two.symm
  apply interface.nextLocalLayer.crossingEdge_injective
    (orbitFace_incidence_le_two
      embedded.cellulation.rotation.toRotationSystem) hunique
  simpa [nextLocalLayerPrefixCrossing] using heq

/-- Passing from the left cross-section of a source Cell to its right
cross-section adds exactly the boundary of the next central hexagonal face.
This is the literal regional decomposition to which the one-Cell transfer
law must be applied. -/
theorem localLayerRightPrefixEdgeRegion_eq_left_union_nextCenterBoundary
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    corridorPrefixEdgeRegion
        realization.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        (leftInterior.center.val + 2) =
      corridorPrefixEdgeRegion
          realization.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
          (leftInterior.center.val + 1) ∪
        orbitFaceBoundary
          embedded.cellulation.rotation.toRotationSystem
          interface.nextCenterLayerFace.1 := by
  have hcut : leftInterior.center.val + 1 < blockLength := by omega
  simpa [nextCenterLayerFace, nextCorridorInterior, CorridorInterior.outgoing,
    CorridorStep.right] using
    (corridorPrefixEdgeRegion_succ
      realization.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      (leftInterior.center.val + 1) hcut)

/-- Full cut data for the cumulative prefix immediately before the Cell. -/
noncomputable def localLayerLeftPrefixGraphCutData
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :=
  regionalBoundaryGraphCutData
    embedded.cellulation.rotation.toRotationSystem
    (corridorPrefixEdgeRegion
      realization.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      (leftInterior.center.val + 1))
    interface.localLayerPrefixCrossing

/-- Full cut data for the cumulative prefix immediately after the Cell. -/
noncomputable def localLayerRightPrefixGraphCutData
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :=
  regionalBoundaryGraphCutData
    embedded.cellulation.rotation.toRotationSystem
    (corridorPrefixEdgeRegion
      realization.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      (leftInterior.center.val + 2))
    interface.nextLocalLayerPrefixCrossing

theorem localLayerLeftPrefixGraphCutData_portsInRegion
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    interface.localLayerLeftPrefixGraphCutData.PortsInRegion := by
  exact regionalBoundaryGraphCutData_portsInRegion
    embedded.cellulation.rotation.toRotationSystem
    (corridorPrefixEdgeRegion
      realization.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      (leftInterior.center.val + 1))
    interface.localLayerPrefixCrossing
    interface.localLayerPrefixCrossing_mem_prefixEdgeRegion

theorem localLayerRightPrefixGraphCutData_portsInRegion
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    interface.localLayerRightPrefixGraphCutData.PortsInRegion := by
  exact regionalBoundaryGraphCutData_portsInRegion
    embedded.cellulation.rotation.toRotationSystem
    (corridorPrefixEdgeRegion
      realization.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      (leftInterior.center.val + 2))
    interface.nextLocalLayerPrefixCrossing
    interface.nextLocalLayerPrefixCrossing_mem_prefixEdgeRegion

/-- The complete finite source-prefix profile before one Cell. -/
noncomputable def localLayerLeftPrefixBoundedProfile
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (color : G.edgeSet → Color)
    (hcolor : ∀ step, color (interface.localLayerPrefixCrossing step) ≠ 0) :
    BoundedCorridorCutProfile 2 0 4 :=
  regionalBoundaryBoundedProfile
    embedded.cellulation.rotation.toRotationSystem
    (corridorPrefixEdgeRegion
      realization.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      (leftInterior.center.val + 1))
    interface.localLayerPrefixCrossing color hcolor

/-- The complete finite source-prefix profile after one Cell. -/
noncomputable def localLayerRightPrefixBoundedProfile
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (color : G.edgeSet → Color)
    (hcolor : ∀ step, color (interface.nextLocalLayerPrefixCrossing step) ≠ 0) :
    BoundedCorridorCutProfile 2 0 4 :=
  regionalBoundaryBoundedProfile
    embedded.cellulation.rotation.toRotationSystem
    (corridorPrefixEdgeRegion
      realization.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      (leftInterior.center.val + 2))
    interface.nextLocalLayerPrefixCrossing color hcolor

end SourceConsecutiveSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
