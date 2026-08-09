import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscut
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorOpenSlab

/-!
# Source-realized local layer boundaries in a clean corridor

The compositional source treats a corridor as a composite of open slabs.  A
slab boundary must therefore be constructed from the actual face rotations,
not supplied as an abstract cut.  The two side positions computed for a source
corridor face give a literal simple facial-dual path through that face.  Two
consecutive slabs use the same two external endpoint faces, so these paths are
the local layer boundaries of the source corridor.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24AnnularCrosscut
open GoertzelV24CleanHexCorridor
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexCorridorSlab
open GoertzelV24HexFaceRungType
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24OrientedHexSlab
open GoertzelV24OrbitFaceTwoSided
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace SourceTrail

namespace AnnularEmbedding

namespace SourceConsecutiveSlabInterface

/-- The first external face of the actual two-port layer at a source slab. -/
noncomputable def firstLayerFace
    {source : SourceTrail G}
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
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    AmbientFace (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem)) :=
  placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton htwoSided
    hunique (realization.slabPlacementAt htwoSided hunique leftInterior)
    interface.leftBeforePos

/-- The second external face of the actual two-port layer at a source slab. -/
noncomputable def secondLayerFace
    {source : SourceTrail G}
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
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    AmbientFace (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem)) :=
  placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton htwoSided
    hunique (realization.slabPlacementAt htwoSided hunique leftInterior)
    interface.leftAfterPos

/-- The central source face through which the local layer passes. -/
def centerLayerFace
    {source : SourceTrail G}
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
    (_interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    AmbientFace (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem)) :=
  realization.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
    leftInterior.center

/-- Each external layer endpoint is genuinely outside the source corridor
axis, so the dual path cannot fold back through its central face. -/
theorem firstLayerFace_ne_centerLayerFace
    {source : SourceTrail G}
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
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    interface.firstLayerFace ≠ interface.centerLayerFace := by
  exact placementSideNeighbor_ne_faceAt
    realization.toCleanOrbitHexCorridorSkeleton htwoSided hunique
    (realization.slabPlacementAt htwoSided hunique leftInterior)
    interface.leftBeforePos leftInterior.center

/-- The second endpoint is also distinct from the central source face. -/
theorem secondLayerFace_ne_centerLayerFace
    {source : SourceTrail G}
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
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    interface.secondLayerFace ≠ interface.centerLayerFace := by
  exact placementSideNeighbor_ne_faceAt
    realization.toCleanOrbitHexCorridorSkeleton htwoSided hunique
    (realization.slabPlacementAt htwoSided hunique leftInterior)
    interface.leftAfterPos leftInterior.center

/-- The two external layer endpoints are different faces, not merely two
names for one side of the central hexagon. -/
theorem firstLayerFace_ne_secondLayerFace
    {source : SourceTrail G}
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
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    interface.firstLayerFace ≠ interface.secondLayerFace := by
  intro hfaces
  apply interface.left_distinct
  exact placementSideNeighbor_injective
    realization.toCleanOrbitHexCorridorSkeleton htwoSided hunique
    (realization.slabPlacementAt htwoSided hunique leftInterior) hfaces

/-- The first external endpoint is dual-adjacent to the central source face. -/
theorem firstLayerFace_adjacent_centerLayerFace
    {source : SourceTrail G}
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
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    (interiorDualGraph
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Adj
      interface.firstLayerFace interface.centerLayerFace := by
  simpa [firstLayerFace, centerLayerFace, placementSideNeighbor] using
    (internalSideNeighbor_adjacent realization.toCleanOrbitHexCorridorSkeleton
      htwoSided hunique leftInterior
      (placementSideEdge htwoSided
        (realization.slabPlacementAt htwoSided hunique leftInterior)
        interface.leftBeforePos)).symm

/-- The central source face is dual-adjacent to the second external endpoint. -/
theorem centerLayerFace_adjacent_secondLayerFace
    {source : SourceTrail G}
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
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    (interiorDualGraph
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Adj
      interface.centerLayerFace interface.secondLayerFace := by
  simpa [secondLayerFace, centerLayerFace, placementSideNeighbor] using
    internalSideNeighbor_adjacent realization.toCleanOrbitHexCorridorSkeleton
      htwoSided hunique leftInterior
      (placementSideEdge htwoSided
        (realization.slabPlacementAt htwoSided hunique leftInterior)
        interface.leftAfterPos)

/-- The concrete two-step facial-dual walk crossing one source slab. -/
noncomputable def localLayerWalk
    {source : SourceTrail G}
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
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    (interiorDualGraph
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Walk
      interface.firstLayerFace interface.secondLayerFace :=
  SimpleGraph.Walk.cons interface.firstLayerFace_adjacent_centerLayerFace
    (SimpleGraph.Walk.cons interface.centerLayerFace_adjacent_secondLayerFace
      SimpleGraph.Walk.nil)

/-- The source-slab walk is simple: its two external faces and its central
face are pairwise distinct by the actual cubic face-incidence calculation. -/
theorem localLayerWalk_isPath
    {source : SourceTrail G}
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
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    interface.localLayerWalk.IsPath := by
  unfold localLayerWalk
  apply SimpleGraph.Walk.IsPath.cons
  · apply SimpleGraph.Walk.IsPath.cons
    · exact SimpleGraph.Walk.IsPath.nil
    · simpa using interface.secondLayerFace_ne_centerLayerFace.symm
  · simp [interface.firstLayerFace_ne_centerLayerFace,
      interface.firstLayerFace_ne_secondLayerFace]

/-- A source corridor slab therefore produces a literal simple layer boundary
in the facial dual.  This is a constructed `SimpleDualCrosscut`, not an
assumption about a chord wall. -/
noncomputable def localLayer
    {source : SourceTrail G}
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
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    SimpleDualCrosscut
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))
      interface.firstLayerFace interface.secondLayerFace where
  walk := interface.localLayerWalk
  isPath := interface.localLayerWalk_isPath

/-- The constructed source layer crosses exactly two primal edges. -/
theorem localLayer_walk_length_eq_two
    {source : SourceTrail G}
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
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    interface.localLayer.walk.length = 2 := by
  simp [localLayer, localLayerWalk]

/-- The first endpoint face is shared with the next source slab exactly as
the local rotation calculation says. -/
theorem firstLayerFace_eq_next_firstLayerFace
    {source : SourceTrail G}
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
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    interface.firstLayerFace =
      placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton htwoSided
        hunique
        (realization.slabPlacementAt htwoSided hunique
          (nextCorridorInterior leftInterior hnext)) interface.rightBeforePos :=
  interface.before_match

/-- The second endpoint face is shared with the next source slab as well. -/
theorem secondLayerFace_eq_next_secondLayerFace
    {source : SourceTrail G}
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
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    interface.secondLayerFace =
      placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton htwoSided
        hunique
        (realization.slabPlacementAt htwoSided hunique
          (nextCorridorInterior leftInterior hnext)) interface.rightAfterPos :=
  interface.after_match

end SourceConsecutiveSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
