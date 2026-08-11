import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorLayerFormation

/-!
# Dual slab cycles from adjacent source corridor layers

Two local layer boundaries on consecutive source corridor hexagons have the
same two external endpoint faces.  Their union is therefore a literal simple
four-step cycle in the facial dual.  This is the finite ladder cell from which
the eventual open corridor patch and its primal separator are assembled.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

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

/-- The central source face of the next slab in the local corridor pair. -/
def nextCenterLayerFace
    (_interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    AmbientFace (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem)) :=
  realization.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
    (nextCorridorInterior leftInterior hnext).center

/-- The next slab centre is one of the literal hexagonal faces of the source
corridor. -/
theorem nextCenterLayerFace_boundary_card_eq_six
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
      interface.nextCenterLayerFace.1).card = 6 := by
  simpa [nextCenterLayerFace] using
    realization.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      |>.hexagonal (nextCorridorInterior leftInterior hnext).center

/-- The two central faces in a source slab are different positions of the
actual simple clean corridor path. -/
theorem centerLayerFace_ne_nextCenterLayerFace
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    interface.centerLayerFace ≠ interface.nextCenterLayerFace := by
  intro hfaces
  have hindices := realization.toCleanOrbitHexCorridorSkeleton
    |>.toOrbitHexCorridorSkeleton.faceAt_injective hfaces
  have hvalues := congrArg Fin.val hindices
  change leftInterior.center.val = leftInterior.center.val + 1 at hvalues
  omega

/-- The first external layer face is also adjacent to the next source
hexagon.  This is the first half of the locally constructed slab square. -/
theorem firstLayerFace_adjacent_nextCenterLayerFace
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    (interiorDualGraph
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Adj
      interface.firstLayerFace interface.nextCenterLayerFace := by
  rw [interface.firstLayerFace_eq_next_firstLayerFace]
  simpa [nextCenterLayerFace, placementSideNeighbor] using
    (internalSideNeighbor_adjacent realization.toCleanOrbitHexCorridorSkeleton
      htwoSided hunique (nextCorridorInterior leftInterior hnext)
      (placementSideEdge htwoSided
        (realization.slabPlacementAt htwoSided hunique
          (nextCorridorInterior leftInterior hnext)) interface.rightBeforePos)).symm

/-- The next central face is also adjacent to the second external layer face. -/
theorem nextCenterLayerFace_adjacent_secondLayerFace
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    (interiorDualGraph
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Adj
      interface.nextCenterLayerFace interface.secondLayerFace := by
  rw [interface.secondLayerFace_eq_next_secondLayerFace]
  simpa [nextCenterLayerFace, placementSideNeighbor] using
    internalSideNeighbor_adjacent realization.toCleanOrbitHexCorridorSkeleton
      htwoSided hunique (nextCorridorInterior leftInterior hnext)
      (placementSideEdge htwoSided
        (realization.slabPlacementAt htwoSided hunique
          (nextCorridorInterior leftInterior hnext)) interface.rightAfterPos)

/-- Neither external layer face can coincide with the next corridor face. -/
theorem firstLayerFace_ne_nextCenterLayerFace
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    interface.firstLayerFace ≠ interface.nextCenterLayerFace := by
  exact placementSideNeighbor_ne_faceAt
    realization.toCleanOrbitHexCorridorSkeleton htwoSided hunique
    (realization.slabPlacementAt htwoSided hunique leftInterior)
    interface.leftBeforePos (nextCorridorInterior leftInterior hnext).center

/-- Neither external layer face can coincide with the next corridor face. -/
theorem secondLayerFace_ne_nextCenterLayerFace
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    interface.secondLayerFace ≠ interface.nextCenterLayerFace := by
  exact placementSideNeighbor_ne_faceAt
    realization.toCleanOrbitHexCorridorSkeleton htwoSided hunique
    (realization.slabPlacementAt htwoSided hunique leftInterior)
    interface.leftAfterPos (nextCorridorInterior leftInterior hnext).center

/-- The facial-dual boundary of the literal source slab, ordered around its
four distinct faces. -/
noncomputable def dualSlabCycleWalk
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    (interiorDualGraph
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Walk
      interface.centerLayerFace interface.centerLayerFace :=
  SimpleGraph.Walk.cons interface.firstLayerFace_adjacent_centerLayerFace.symm
    (SimpleGraph.Walk.cons interface.firstLayerFace_adjacent_nextCenterLayerFace
      (SimpleGraph.Walk.cons interface.nextCenterLayerFace_adjacent_secondLayerFace
        (SimpleGraph.Walk.cons interface.centerLayerFace_adjacent_secondLayerFace.symm
          SimpleGraph.Walk.nil)))

/-- The local source slab boundary is a simple four-cycle in the facial dual.
This is not a topological assertion from a picture: Lean checks all six
pairwise face inequalities from the corridor's actual rotations. -/
theorem dualSlabCycleWalk_isCycle
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    interface.dualSlabCycleWalk.IsCycle := by
  simp [dualSlabCycleWalk, SimpleGraph.Walk.cons_isCycle_iff,
    SimpleGraph.Walk.cons_isPath_iff,
    interface.firstLayerFace_ne_centerLayerFace,
    interface.secondLayerFace_ne_centerLayerFace,
    interface.firstLayerFace_ne_secondLayerFace,
    interface.centerLayerFace_ne_nextCenterLayerFace,
    interface.centerLayerFace_ne_nextCenterLayerFace.symm,
    interface.firstLayerFace_ne_nextCenterLayerFace,
    interface.secondLayerFace_ne_nextCenterLayerFace.symm]

/-- One local slab has exactly four dual boundary steps, matching the finite
four-edge interface computed from its two adjacent source layers. -/
theorem dualSlabCycleWalk_length_eq_four
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    interface.dualSlabCycleWalk.length = 4 := by
  simp [dualSlabCycleWalk]

end SourceConsecutiveSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
