import Mettapedia.GraphTheory.FourColor.GoertzelV24BoundaryDartUnionAbsorption
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorAlignedTwoTileSuccessorBoundaryDart

/-!
# Absorption at a consecutive aligned-slab interface

The source coordinates identify the two transverse edges shared by
consecutive aligned two-tile windows.  The boundary-dart classification says
that each such edge is either exposed with opposite orientations, or the two
enclosed vertex carriers overlap at the displayed endpoint.  In the first
case this file proves the graph-theoretic consequence needed by a serial
prefix: the shared edge is internal after the two enclosed sides are joined.

This is a local portal-cancellation theorem.  It does not rule out the
overlap branch, identify the two lateral rail ports at different offsets, or
assert that unions of arbitrarily many windows have bounded frontier.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationVertexCutProfile
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorAlignedTwoTileSuccessorAbsorptionEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- An alpha-oriented transverse portal of two consecutive aligned windows
is absorbed by the union of their enclosed vertex sides. -/
theorem sourceTwoTileAlignedEnclosed_sharedEdge_not_mem_unionCrossing_of_alpha
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
    (offset : Fin (blockLength - 5)) (step : Fin 2)
    (halpha :
      embedded.cellulation.rotation.toRotationSystem.alpha
          (sourceTwoTileAlignedEnclosedOutputBoundaryDartAt realization hcubic
            hrotation htwoSided hunique offset step).1.1 =
        (sourceTwoTileAlignedEnclosedSuccessorInputBoundaryDartAt realization
          hcubic hrotation htwoSided hunique offset step).1.1) :
    embedded.cellulation.rotation.toRotationSystem.edgeOf
        (sourceTwoTileAlignedEnclosedOutputBoundaryDartAt realization hcubic
          hrotation htwoSided hunique offset step).1.1 ∉
      vertexSetCrossingEdges
        embedded.cellulation.rotation.toRotationSystem
        ((sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
            htwoSided hunique
            (sourceTwoTileSuccessorStartOffset offset)).componentSideᶜ ∪
          (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
            htwoSided hunique
          (sourceTwoTileSuccessorNextOffset offset)).componentSideᶜ) := by
  let RS := embedded.cellulation.rotation.toRotationSystem
  let left := sourceTwoTileAlignedEnclosedOutputBoundaryDartAt realization
    hcubic hrotation htwoSided hunique offset step
  let right := sourceTwoTileAlignedEnclosedSuccessorInputBoundaryDartAt
    realization hcubic hrotation htwoSided hunique offset step
  apply not_mem_vertexSetCrossingEdges_of_endpoints_subset
  rw [RS.endpoints_eq_pair_of_mem (RS.mem_dartsOn.2 rfl)]
  intro vertex hvertex
  simp only [Finset.mem_insert, Finset.mem_singleton] at hvertex
  rcases hvertex with hleft | hright
  · rw [hleft]
    apply Finset.mem_union_left
    simpa [RS, left, deletedRegionKeep] using left.1.2
  · rw [hright, halpha]
    apply Finset.mem_union_right
    simpa [RS, right, deletedRegionKeep] using right.1.2

/-- Exact local alternative at every shared transverse portal: either the
portal is absorbed by the joined enclosed side, or the source windows have a
concrete common enclosed vertex.  The theorem deliberately leaves the second
branch visible. -/
theorem sourceTwoTileAlignedEnclosed_sharedEdge_absorbed_or_vertexOverlap
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
    (offset : Fin (blockLength - 5)) (step : Fin 2) :
    embedded.cellulation.rotation.toRotationSystem.edgeOf
        (sourceTwoTileAlignedEnclosedOutputBoundaryDartAt realization hcubic
          hrotation htwoSided hunique offset step).1.1 ∉
      vertexSetCrossingEdges
        embedded.cellulation.rotation.toRotationSystem
        ((sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
            htwoSided hunique
            (sourceTwoTileSuccessorStartOffset offset)).componentSideᶜ ∪
          (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
            htwoSided hunique
            (sourceTwoTileSuccessorNextOffset offset)).componentSideᶜ) ∨
    ∃ vertex,
      deletedRegionKeep
        (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
          htwoSided hunique
          (sourceTwoTileSuccessorStartOffset offset)).componentSide vertex ∧
      deletedRegionKeep
        (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
          htwoSided hunique
          (sourceTwoTileSuccessorNextOffset offset)).componentSide vertex := by
  rcases sourceTwoTileAlignedEnclosed_alphaSeam_or_vertexOverlap realization
      hcubic hrotation htwoSided hunique offset step with halpha | hoverlap
  · exact Or.inl
      (sourceTwoTileAlignedEnclosed_sharedEdge_not_mem_unionCrossing_of_alpha
        realization hcubic hrotation htwoSided hunique offset step halpha)
  · exact Or.inr hoverlap

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
