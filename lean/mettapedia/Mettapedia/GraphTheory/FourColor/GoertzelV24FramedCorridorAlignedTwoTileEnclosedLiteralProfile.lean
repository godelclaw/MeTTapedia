import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorAlignedTwoTileEnclosedProfileRestriction
import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutOpenRegionalProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenRegionTaitInheritance

/-!
# Literal coloring semantics for the enclosed aligned slab

The source `Count` semantics observes a profile on the open morphism being
colored. The aligned slab's literal morphism is complementary to the selected
outer retained side. This file reads its graph-derived `4 + 2` profile from
arbitrary Tait colorings of that literal open region.

It deliberately constructs neither a serial product nor a cumulative-prefix
transition. Those require a separate geometric realization of how successive
local morphisms compose.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24AnnularCrosscutOpenRegionalProfile
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24HexFaceRungType
open GoertzelV24OpenRegionRotation
open GoertzelV24OpenRegionTaitInheritance
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationVertexCutProfile
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorAlignedTwoTileEnclosedLiteralProfileEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The enclosed root viewed as a dart of the literal open rotation system. -/
noncomputable def sourceTwoTileAlignedEnclosedOpenRoot
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
    Dart embedded.cellulation.rotation.toRotationSystem
      (deletedRegionKeep
        (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
          htwoSided hunique offset).componentSide) :=
  Sum.inl (sourceTwoTileAlignedEnclosedRootDart realization hcubic hrotation
    htwoSided hunique offset)

/-- The literal open rotation system enclosed by the aligned slab. -/
noncomputable def sourceTwoTileAlignedEnclosedOpenRegion
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
  rotationSystem embedded.cellulation.rotation.toRotationSystem
    (deletedRegionKeep
      (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
        htwoSided hunique offset).componentSide)
    (sourceTwoTileAlignedEnclosedOpenRoot realization hcubic hrotation
      htwoSided hunique offset)

/-- The enclosed profile's regional carrier is genuinely contained in the
literal enclosed vertex side. -/
theorem sourceTwoTileAlignedEnclosedTerminalProfileDataAt_regionEdges_subset
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
    (sourceTwoTileAlignedEnclosedTerminalProfileDataAt realization hcubic
      hrotation htwoSided hunique offset).regionEdges ⊆
      vertexSetRegionEdges embedded.cellulation.rotation.toRotationSystem
        (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
          htwoSided hunique offset).componentSideᶜ := by
  intro edge hedge
  simpa [sourceTwoTileAlignedEnclosedTerminalProfileDataAt,
    GoertzelV24CorridorProfilePortPartition.GraphCorridorCutData.partitionCrossings,
    sourceTwoTileAlignedEnclosedOrderedProfileDataAt,
    vertexSetBoundaryGraphCutDataWithIndexing] using hedge

/-- Read an enclosed regional edge from an arbitrary literal open coloring. -/
noncomputable def sourceTwoTileAlignedEnclosedLiteralColorOnVertexSide
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
    (coloring : (sourceTwoTileAlignedEnclosedOpenRegion realization hcubic
      hrotation htwoSided hunique offset).EdgeColoring Color) :
    G.edgeSet → Color :=
  fun edge =>
    if hedge : edge ∈ vertexSetRegionEdges
        embedded.cellulation.rotation.toRotationSystem
        (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
          htwoSided hunique offset).componentSideᶜ then
      dartColor embedded.cellulation.rotation.toRotationSystem
        (deletedRegionKeep
          (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
            htwoSided hunique offset).componentSide)
        (sourceTwoTileAlignedEnclosedOpenRoot realization hcubic hrotation
          htwoSided hunique offset) coloring
        (Sum.inl ⟨vertexSideDart embedded.cellulation.rotation.toRotationSystem
          (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
            htwoSided hunique offset).componentSideᶜ edge hedge, by
          simpa [deletedRegionKeep] using vertexSideDart_mem_inside
            embedded.cellulation.rotation.toRotationSystem
            (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
              htwoSided hunique offset).componentSideᶜ edge hedge⟩)
    else 0

/-- Every enclosed regional edge is nonzero under a literal open Tait
coloring. -/
theorem sourceTwoTileAlignedEnclosedLiteralColorOnVertexSide_ne_zero
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
    (coloring : (sourceTwoTileAlignedEnclosedOpenRegion realization hcubic
      hrotation htwoSided hunique offset).EdgeColoring Color)
    (hcoloring : (sourceTwoTileAlignedEnclosedOpenRegion realization hcubic
      hrotation htwoSided hunique offset).IsTaitEdgeColoring coloring)
    {edge : G.edgeSet}
    (hedge : edge ∈ vertexSetRegionEdges
      embedded.cellulation.rotation.toRotationSystem
      (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
        htwoSided hunique offset).componentSideᶜ) :
    sourceTwoTileAlignedEnclosedLiteralColorOnVertexSide realization hcubic
      hrotation htwoSided hunique offset coloring edge ≠ 0 := by
  rw [sourceTwoTileAlignedEnclosedLiteralColorOnVertexSide]
  simp only [dif_pos hedge]
  exact dartColor_ne_zero embedded.cellulation.rotation.toRotationSystem
    (deletedRegionKeep
      (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
        htwoSided hunique offset).componentSide)
    (sourceTwoTileAlignedEnclosedOpenRoot realization hcubic hrotation
      htwoSided hunique offset) coloring hcoloring _

/-- The complete local `4 + 2` profile of a literal enclosed-slab Tait
coloring. Every coordinate is calculated from the same open morphism. -/
noncomputable def sourceTwoTileAlignedEnclosedLiteralOpenProfile
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
    (coloring : (sourceTwoTileAlignedEnclosedOpenRegion realization hcubic
      hrotation htwoSided hunique offset).EdgeColoring Color)
    (hcoloring : (sourceTwoTileAlignedEnclosedOpenRegion realization hcubic
      hrotation htwoSided hunique offset).IsTaitEdgeColoring coloring) :=
  let hregion := sourceTwoTileAlignedEnclosedTerminalProfileDataAt_regionEdges_subset
    realization hcubic hrotation htwoSided hunique offset
  let hports := sourceTwoTileAlignedEnclosedTerminalProfileDataAt_portsInRegion
    realization hcubic hrotation htwoSided hunique offset
  (sourceTwoTileAlignedEnclosedTerminalProfileDataAt realization hcubic
    hrotation htwoSided hunique offset).regionalProfile
    (sourceTwoTileAlignedEnclosedLiteralColorOnVertexSide realization hcubic
      hrotation htwoSided hunique offset coloring)
    (fun crossing =>
      sourceTwoTileAlignedEnclosedLiteralColorOnVertexSide_ne_zero
        realization hcubic hrotation htwoSided hunique offset coloring hcoloring
        (hregion (hports (.inl crossing))))

/-- The color coordinate of the literal enclosed-slab profile reads the
color of its corresponding literal boundary edge. -/
@[simp]
theorem sourceTwoTileAlignedEnclosedLiteralOpenProfile_edgeColor_toColor
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
    (coloring : (sourceTwoTileAlignedEnclosedOpenRegion realization hcubic
      hrotation htwoSided hunique offset).EdgeColoring Color)
    (hcoloring : (sourceTwoTileAlignedEnclosedOpenRegion realization hcubic
      hrotation htwoSided hunique offset).IsTaitEdgeColoring coloring)
    (crossing : Fin 4) :
    ((sourceTwoTileAlignedEnclosedLiteralOpenProfile realization hcubic
      hrotation htwoSided hunique offset coloring hcoloring).edgeColor
        crossing).toColor =
      sourceTwoTileAlignedEnclosedLiteralColorOnVertexSide realization hcubic
        hrotation htwoSided hunique offset coloring
        ((sourceTwoTileAlignedEnclosedTerminalProfileDataAt realization hcubic
          hrotation htwoSided hunique offset).crossingEdge crossing) := by
  unfold sourceTwoTileAlignedEnclosedLiteralOpenProfile
  exact GraphCorridorCutData.regionalProfile_edgeColor_toColor _ _ _ crossing

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
