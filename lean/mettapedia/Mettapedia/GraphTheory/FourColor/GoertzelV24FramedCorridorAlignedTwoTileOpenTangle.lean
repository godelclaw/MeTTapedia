import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorAlignedTwoTileOpenBoundary
import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenTangleBoundaryReindex

/-!
# Literal open tangle of an aligned two-tile source slab

The certified six-edge aligned boundary cuts out an actual planar open
tangle.  This file reindexes its literal boundary half-edges by the four
transverse and two rail coordinates already certified for the source slab.

It constructs only the underlying literal open-tangle carrier.  In
particular, it does not yet add the source's frozen/free/defect markings,
claim serial gluing of consecutive slabs, or identify rail coordinates across
different offsets.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24CorridorProfile
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OpenTangleComposition
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationVertexCutProfile
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorAlignedTwoTileOpenTangleEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- A root dart on the non-outer side of the aligned six-edge source slab. -/
noncomputable def sourceTwoTileAlignedEnclosedRootDart
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
    RetainedDart embedded.cellulation.rotation.toRotationSystem
      (deletedRegionKeep
        (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
          htwoSided hunique offset).componentSide) := by
  let boundary := sourceTwoTileAlignedLayerBoundaryAt realization hcubic
    hrotation htwoSided hunique offset
  let dart := Classical.choose (exists_dart_vertOf_eq_of_isCubic
    embedded.cellulation.rotation.toRotationSystem hcubic boundary.removed)
  have hdart : embedded.cellulation.rotation.toRotationSystem.vertOf dart =
      boundary.removed :=
    Classical.choose_spec (exists_dart_vertOf_eq_of_isCubic
      embedded.cellulation.rotation.toRotationSystem hcubic boundary.removed)
  refine ⟨dart, ?_⟩
  simp only [deletedRegionKeep]
  intro hside
  apply boundary.removed_not_mem_component
  have hside' : embedded.cellulation.rotation.toRotationSystem.vertOf dart ∈
      boundary.componentSide := by
    exact hside
  have hremovedSide : boundary.removed ∈ boundary.componentSide := by
    rw [← hdart]
    exact hside'
  exact (SourceCornerAlignedTwoTileLayerBoundary.mem_componentSide_iff
    boundary boundary.removed).mp hremovedSide

/-- The actual cut-open tangle enclosed by the aligned six-edge source slab,
with its literal boundary reindexed by the displayed physical `4 + 2` ports.
-/
noncomputable def sourceTwoTileAlignedEnclosedOpenTangle
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
    OpenTangleData
      { vertex : V // deletedRegionKeep
        (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
          htwoSided hunique offset).componentSide vertex }
      (InternalDart embedded.cellulation.rotation.toRotationSystem
        (deletedRegionKeep
          (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
            htwoSided hunique offset).componentSide))
      (CorridorPort 4 2) := by
  let boundary := sourceTwoTileAlignedLayerBoundaryAt realization hcubic
    hrotation htwoSided hunique offset
  exact (OpenTangleData.ofVertexSide
    embedded.cellulation.rotation.toRotationSystem
    (deletedRegionKeep boundary.componentSide)
    (sourceTwoTileAlignedEnclosedRootDart realization hcubic hrotation
      htwoSided hunique offset)).reindexBoundary
        (sourceTwoTileAlignedTerminalPortBoundaryDartEquiv realization hcubic
          hrotation htwoSided hunique offset)

/-- The displayed boundary vertex of the literal open tangle is the old
vertex carrying the corresponding physical boundary half-edge. -/
@[simp]
theorem sourceTwoTileAlignedEnclosedOpenTangle_boundaryVert_val
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
    (offset : Fin (blockLength - 4)) (port : CorridorPort 4 2) :
    ((sourceTwoTileAlignedEnclosedOpenTangle realization hcubic hrotation
      htwoSided hunique offset).boundaryVert port).1 =
      embedded.cellulation.rotation.toRotationSystem.vertOf
        ((sourceTwoTileAlignedTerminalPortBoundaryDartEquiv realization hcubic
          hrotation htwoSided hunique offset port).1.1) :=
  rfl

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
