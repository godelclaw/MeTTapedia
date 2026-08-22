import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebase
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialPrefixVertexSide

/-!
# Old-side boundary localization for the literal serial rebase

The boundary-rebase seam joins the accumulated literal prefix to the two
newly displayed successor crossings.  Its endpoint on the accumulated-prefix
side is not definitionally one of the two displayed old ports.  It is,
however, forced onto the prefix's genuine vertex-side frontier: the opposite
seam endpoint belongs to the new rebase region and is absent from the old
prefix.

This module proves that localization for both tracked connectivity and
occurrence-sensitive facial progress.  Together with the existing historical
Cell-interface classification, it reduces rebase portal completeness to the
remaining internal-interface absorption theorem.  It does not identify the
true frontier with the current two-edge moving cut.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationVertexCutProfile
open GoertzelV24TerminalProfileRegionalCoverage
open GoertzelV24TerminalProfileSeamResidual
open GoertzelV24TerminalProfileVertexSideSeam
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseOldBoundaryEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- In a tracked rebase seam adjacency, the endpoint belonging to the old
literal prefix lies on that prefix's true vertex-side frontier. -/
theorem sourceCorridorSerialBoundaryRebaseTrackedSeamAt_adj_oldEndpoint_mem_truePrefixCrossing
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
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet → Color) (first second : Color) {x y : G.edgeSet}
    (hadj : (sourceCorridorSerialBoundaryRebaseTrackedSeamAt realization
      hcubic hrotation htwoSided hunique offset hnext color first second).Adj
        x y) :
    (x ∈ (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
          htwoSided hunique offset).regionEdges ∧
        x ∈ sourceCorridorSerialPrefixTrueCrossingEdges realization hcubic
          hrotation htwoSided hunique (offset.val + 1)) ∨
      (y ∈ (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
          htwoSided hunique offset).regionEdges ∧
        y ∈ sourceCorridorSerialPrefixTrueCrossingEdges realization hcubic
          hrotation htwoSided hunique (offset.val + 1)) := by
  let RS := embedded.cellulation.rotation.toRotationSystem
  let oldRegion :=
    (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
      htwoSided hunique offset).regionEdges
  let side := sourceCorridorSerialPrefixVertexSide realization hcubic
    hrotation htwoSided hunique (offset.val + 1)
  have holdRegion : oldRegion = vertexSetRegionEdges RS side := by
    change sourceCorridorSerialPrefixRegion realization hcubic hrotation
        htwoSided hunique (offset.val + 1) =
      vertexSetRegionEdges RS side
    exact sourceCorridorSerialPrefixRegion_eq_vertexSetRegionEdges realization
      hcubic hrotation htwoSided hunique (offset.val + 1)
  have hraw := (regionalTrackedSeamGraph_adj_iff RS oldRegion
    (sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic hrotation
      htwoSided hunique offset hnext) color first second x y).1 hadj
  rcases hraw.2 with hforward | hbackward
  · have hcrossing : x ∈ vertexSetCrossingEdges RS side :=
      mem_vertexSetCrossingEdges_of_adjacent_not_mem_region RS side
        hraw.1.1.symm (by simpa [← holdRegion] using hforward.2.2.2)
        (by simpa [← holdRegion] using hforward.1)
    exact Or.inl ⟨hforward.1, by
      simpa [sourceCorridorSerialPrefixTrueCrossingEdges, side, RS] using
        hcrossing⟩
  · have hcrossing : y ∈ vertexSetCrossingEdges RS side :=
      mem_vertexSetCrossingEdges_of_adjacent_not_mem_region RS side
        hraw.1.1 (by simpa [← holdRegion] using hbackward.2.1)
        (by simpa [← holdRegion] using hbackward.2.2.1)
    exact Or.inr ⟨hbackward.2.2.1, by
      simpa [sourceCorridorSerialPrefixTrueCrossingEdges, side, RS] using
        hcrossing⟩

/-- The occurrence-sensitive facial seam has the same old-side frontier
localization after projecting a face position to its ambient edge. -/
theorem sourceCorridorSerialBoundaryRebaseFaceSeamAt_adj_oldEndpoint_mem_truePrefixCrossing
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
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (root : embedded.cellulation.rotation.toRotationSystem.D)
    {x y : Fin
      (embedded.cellulation.rotation.toRotationSystem.faceOrbit root).card}
    (hadj : (sourceCorridorSerialBoundaryRebaseFaceSeamAt realization hcubic
      hrotation htwoSided hunique offset hnext root).Adj x y) :
    (faceCycleEdge embedded.cellulation.rotation.toRotationSystem root x ∈
          (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
            htwoSided hunique offset).regionEdges ∧
        faceCycleEdge embedded.cellulation.rotation.toRotationSystem root x ∈
          sourceCorridorSerialPrefixTrueCrossingEdges realization hcubic
            hrotation htwoSided hunique (offset.val + 1)) ∨
      (faceCycleEdge embedded.cellulation.rotation.toRotationSystem root y ∈
          (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
            htwoSided hunique offset).regionEdges ∧
        faceCycleEdge embedded.cellulation.rotation.toRotationSystem root y ∈
          sourceCorridorSerialPrefixTrueCrossingEdges realization hcubic
            hrotation htwoSided hunique (offset.val + 1)) := by
  let RS := embedded.cellulation.rotation.toRotationSystem
  let oldRegion :=
    (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
      htwoSided hunique offset).regionEdges
  let side := sourceCorridorSerialPrefixVertexSide realization hcubic
    hrotation htwoSided hunique (offset.val + 1)
  have holdRegion : oldRegion = vertexSetRegionEdges RS side := by
    change sourceCorridorSerialPrefixRegion realization hcubic hrotation
        htwoSided hunique (offset.val + 1) =
      vertexSetRegionEdges RS side
    exact sourceCorridorSerialPrefixRegion_eq_vertexSetRegionEdges realization
      hcubic hrotation htwoSided hunique (offset.val + 1)
  have hraw := (faceRegionalSeamGraph_adj_iff RS root oldRegion
    (sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic hrotation
      htwoSided hunique offset hnext) x y).1 hadj
  have hedgeAdj := edgeAdjacencyGraph_adj_of_faceCyclePositionGraph_adj
    RS hcubic hrotation root hraw.1
  rcases hraw.2 with hforward | hbackward
  · have hcrossing : faceCycleEdge RS root x ∈
        vertexSetCrossingEdges RS side :=
      mem_vertexSetCrossingEdges_of_adjacent_not_mem_region RS side
        hedgeAdj.symm (by simpa [← holdRegion] using hforward.2.2.2)
        (by simpa [← holdRegion] using hforward.1)
    exact Or.inl ⟨hforward.1, by
      simpa [sourceCorridorSerialPrefixTrueCrossingEdges, side, RS] using
        hcrossing⟩
  · have hcrossing : faceCycleEdge RS root y ∈
        vertexSetCrossingEdges RS side :=
      mem_vertexSetCrossingEdges_of_adjacent_not_mem_region RS side
        hedgeAdj (by simpa [← holdRegion] using hbackward.2.1)
        (by simpa [← holdRegion] using hbackward.2.2.1)
    exact Or.inr ⟨hbackward.2.2.1, by
      simpa [sourceCorridorSerialPrefixTrueCrossingEdges, side, RS] using
        hcrossing⟩

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
