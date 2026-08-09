import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorRealization
import Mettapedia.GraphTheory.FourColor.GoertzelV24HexCorridorInterfaceMatching

/-!
# Open slab generators of a source-realized corridor

The source's `Open` category is generated locally by corridor slabs.  This
file connects that statement to the framed L1 formation: an internal face of
the actual selected corridor gives a literal four-edge open interface, and
two consecutive source slabs have two computed matching side faces.  No
transversal carrier is supplied by a caller.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24CleanHexCorridor
open GoertzelV24BulkCorridor
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexCorridorSlab
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabSideAdjacency
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24OrientedHexSlab
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace SourceTrail

namespace AnnularEmbedding

/-- The actual local placement of the two corridor rungs in a source-selected
hexagonal face.  It is chosen from the rotation system's real facial cycle,
not represented by an abstract six-slot pattern. -/
noncomputable def BoundaryCleanCorridorRealization.slabPlacementAt
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (interior : CorridorInterior blockLength) :
    InternalHexRungPlacement
      realization.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique interior :=
  Classical.choice (exists_internalHexRungPlacement
    realization.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
    htwoSided hunique interior)

/-- A local rung placement is anchored at exactly the face selected from the
original framed L1 path. -/
theorem BoundaryCleanCorridorRealization.slabPlacementAt_root_face
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (interior : CorridorInterior blockLength) :
    dartOrbitFace embedded.cellulation.rotation.toRotationSystem
      (realization.slabPlacementAt htwoSided hunique interior).root =
      (embedded.internalFaceToFull
        (realization.path.getVert
          (corridorBlockIndex
            (defectBudget := embedded.boundaryCleanContaminationBudget)
            realization.block interior.center).val)).1 := by
  calc
    dartOrbitFace embedded.cellulation.rotation.toRotationSystem
        (realization.slabPlacementAt htwoSided hunique interior).root =
        (realization.toCleanOrbitHexCorridorSkeleton
          |>.toOrbitHexCorridorSkeleton.faceAt interior.center).1 :=
      (realization.slabPlacementAt htwoSided hunique interior).root_face
    _ = (embedded.internalFaceToFull
        (realization.path.getVert
          (corridorBlockIndex
            (defectBudget := embedded.boundaryCleanContaminationBudget)
            realization.block interior.center).val)).1 :=
      congrArg Subtype.val
        (realization.toCleanOrbitHexCorridorSkeleton_faceAt interior.center)

/-- The four actual non-rung edges of one source corridor slab.  This is the
finite boundary interface of the corresponding open generator. -/
def BoundaryCleanCorridorRealization.slabBoundary
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (interior : CorridorInterior blockLength) :
    Finset G.edgeSet :=
  internalSideEdges
    realization.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
    hunique interior

/-- Every source slab exposes exactly four primal interface edges. -/
theorem BoundaryCleanCorridorRealization.card_slabBoundary_eq_four
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (interior : CorridorInterior blockLength) :
    (realization.slabBoundary hunique interior).card = 4 := by
  exact card_internalSideEdges_eq_four
    realization.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
    htwoSided hunique interior

/-- A boundary edge of a source slab lies on the actual source face at that
corridor position. -/
theorem BoundaryCleanCorridorRealization.slabBoundary_mem_sourceFace
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (interior : CorridorInterior blockLength) (edge : G.edgeSet)
    (hedge : edge ∈ realization.slabBoundary hunique interior) :
    edge ∈ orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
      (embedded.internalFaceToFull
        (realization.path.getVert
          (corridorBlockIndex
            (defectBudget := embedded.boundaryCleanContaminationBudget)
            realization.block interior.center).val)).1 := by
  have hside := (mem_internalSideEdges_iff
    realization.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
    hunique interior edge).1 hedge
  rw [realization.toCleanOrbitHexCorridorSkeleton_faceAt interior.center] at hside
  exact hside.1

/-- The external full-dual face across one literal source-slab boundary edge.
The subtype guarantees that it is one of the four real interface edges. -/
noncomputable def BoundaryCleanCorridorRealization.slabNeighbor
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (interior : CorridorInterior blockLength)
    (side : {edge // edge ∈ realization.slabBoundary hunique interior}) :
    AmbientFace (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem)) :=
  internalSideNeighbor realization.toCleanOrbitHexCorridorSkeleton htwoSided
    hunique interior side

/-- The slab neighbour is connected to the source corridor face by its
specified actual boundary edge. -/
theorem BoundaryCleanCorridorRealization.slabNeighbor_adjacent
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (interior : CorridorInterior blockLength)
    (side : {edge // edge ∈ realization.slabBoundary hunique interior}) :
    (interiorDualGraph
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Adj
      (realization.toCleanOrbitHexCorridorSkeleton
        |>.toOrbitHexCorridorSkeleton.faceAt interior.center)
      (realization.slabNeighbor htwoSided hunique interior side) := by
  exact internalSideNeighbor_adjacent realization.toCleanOrbitHexCorridorSkeleton
    htwoSided hunique interior side

/-- The radius-one cleanliness delivered by framed L1 propagates to every
face across a source-slab interface edge. -/
theorem BoundaryCleanCorridorRealization.slabNeighbor_hexagonal
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (interior : CorridorInterior blockLength)
    (side : {edge // edge ∈ realization.slabBoundary hunique interior}) :
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
      (realization.slabNeighbor htwoSided hunique interior side).1).card = 6 := by
  exact internalSideNeighbor_hexagonal realization.toCleanOrbitHexCorridorSkeleton
    htwoSided hunique interior side

/-- The adjacent-rung local case is impossible on the source-realized
corridor: this is the finite cubic rotation-system classification that keeps
the slab alphabet to the three non-adjacent oriented types. -/
theorem BoundaryCleanCorridorRealization.slabPlacementAt_rungType_ne_adjacent
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
    (interior : CorridorInterior blockLength) :
    (realization.slabPlacementAt htwoSided hunique interior).rungType ≠
      HexRungType.adjacent := by
  exact InternalHexRungPlacement.rungType_ne_adjacent
    (realization.slabPlacementAt htwoSided hunique interior)
      hcubic hrotation htwoSided

/-- Consecutive source slabs have two distinct, computed side-face matches.
This supplies the local composition data from which the global corridor
interfaces are assembled; it is derived from facial rotations, not added as
an extra boundary hypothesis. -/
theorem BoundaryCleanCorridorRealization.consecutiveSlabInterfacesMatch
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
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) :
    ConsecutiveSlabInterfacesMatch realization.toCleanOrbitHexCorridorSkeleton
      htwoSided hunique leftInterior hnext
      (realization.slabPlacementAt htwoSided hunique leftInterior)
      (realization.slabPlacementAt htwoSided hunique
        (nextCorridorInterior leftInterior hnext)) := by
  exact GoertzelV24HexCorridorInterfaceMatching.consecutiveSlabInterfacesMatch
    realization.toCleanOrbitHexCorridorSkeleton hcubic hrotation htwoSided
      hunique leftInterior hnext
      (realization.slabPlacementAt htwoSided hunique leftInterior)
      (realization.slabPlacementAt htwoSided hunique
        (nextCorridorInterior leftInterior hnext))

/-- The two-port transverse position between consecutive source slabs.  All
four slots are literal positions on actual six-dart facial cycles; the two
matching equations say that the corresponding side faces are the same on
both slabs. -/
structure SourceConsecutiveSlabInterface
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) where
  leftBeforePos :
    {position // position ∈ placementSidePositions
      (realization.slabPlacementAt htwoSided hunique leftInterior)}
  leftAfterPos :
    {position // position ∈ placementSidePositions
      (realization.slabPlacementAt htwoSided hunique leftInterior)}
  rightBeforePos :
    {position // position ∈ placementSidePositions
      (realization.slabPlacementAt htwoSided hunique
        (nextCorridorInterior leftInterior hnext))}
  rightAfterPos :
    {position // position ∈ placementSidePositions
      (realization.slabPlacementAt htwoSided hunique
        (nextCorridorInterior leftInterior hnext))}
  left_distinct : leftBeforePos ≠ leftAfterPos
  right_distinct : rightBeforePos ≠ rightAfterPos
  before_match :
    placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton
      htwoSided hunique
      (realization.slabPlacementAt htwoSided hunique leftInterior) leftBeforePos =
      placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton
        htwoSided hunique
        (realization.slabPlacementAt htwoSided hunique
          (nextCorridorInterior leftInterior hnext)) rightBeforePos
  after_match :
    placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton
      htwoSided hunique
      (realization.slabPlacementAt htwoSided hunique leftInterior) leftAfterPos =
      placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton
        htwoSided hunique
        (realization.slabPlacementAt htwoSided hunique
          (nextCorridorInterior leftInterior hnext)) rightAfterPos

/-- The cubic rotation-system calculation constructs each consecutive
two-port transverse position.  Thus the source corridor does not require a
separate user-provided layer boundary at every step. -/
theorem BoundaryCleanCorridorRealization.exists_sourceConsecutiveSlabInterface
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
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) :
    Nonempty (SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) := by
  rcases realization.consecutiveSlabInterfacesMatch hcubic hrotation htwoSided
      hunique leftInterior hnext with
    ⟨leftBefore, leftAfter, rightBefore, rightAfter,
      hleft, hright, hbefore, hafter⟩
  exact ⟨{
    leftBeforePos := leftBefore
    leftAfterPos := leftAfter
    rightBeforePos := rightBefore
    rightAfterPos := rightAfter
    left_distinct := hleft
    right_distinct := hright
    before_match := hbefore
    after_match := hafter
  }⟩

/-- The canonical local transverse position chosen from the theorem above.
The choice only resolves finite local orientation; all its incidence and
matching facts remain checked projections of the source realization. -/
noncomputable def BoundaryCleanCorridorRealization.sourceConsecutiveSlabInterface
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
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) :
    SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext :=
  Classical.choice
    (realization.exists_sourceConsecutiveSlabInterface hcubic hrotation
      htwoSided hunique leftInterior hnext)

namespace SourceConsecutiveSlabInterface

/-- The first left port's concrete edge in the source slab boundary. -/
def leftBeforeEdge
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
      leftInterior hnext) :=
  placementSideEdge htwoSided
    (realization.slabPlacementAt htwoSided hunique leftInterior)
    interface.leftBeforePos

/-- The second left port's concrete edge in the source slab boundary. -/
def leftAfterEdge
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
      leftInterior hnext) :=
  placementSideEdge htwoSided
    (realization.slabPlacementAt htwoSided hunique leftInterior)
    interface.leftAfterPos

/-- The two left ports really are different source edges. -/
theorem leftBeforeEdge_ne_leftAfterEdge
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
    interface.leftBeforeEdge ≠ interface.leftAfterEdge := by
  intro hedges
  apply interface.left_distinct
  exact placementSideEdge_injective htwoSided
    (realization.slabPlacementAt htwoSided hunique leftInterior) hedges

/-- The first pair of ports sees one and the same actual external face from
both consecutive source slabs. -/
theorem before_match_face
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
    placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton
      htwoSided hunique
      (realization.slabPlacementAt htwoSided hunique leftInterior)
      interface.leftBeforePos =
      placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton
        htwoSided hunique
        (realization.slabPlacementAt htwoSided hunique
          (nextCorridorInterior leftInterior hnext)) interface.rightBeforePos :=
  interface.before_match

/-- The second pair of ports sees one and the same actual external face from
both consecutive source slabs. -/
theorem after_match_face
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
    placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton
      htwoSided hunique
      (realization.slabPlacementAt htwoSided hunique leftInterior)
      interface.leftAfterPos =
      placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton
        htwoSided hunique
        (realization.slabPlacementAt htwoSided hunique
          (nextCorridorInterior leftInterior hnext)) interface.rightAfterPos :=
  interface.after_match

end SourceConsecutiveSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
