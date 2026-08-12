import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialPrefixSeamSupport
import Mettapedia.GraphTheory.FourColor.GoertzelV24VertexSetRegionUnion

/-!
# The literal source prefix is a vertex-side carrier

Each literal source Cell is the regional edge carrier induced by the
complementary side of its source crosscut.  Since regional edge carriers
commute with finite unions, the cumulative literal prefix is itself the
carrier induced by the union of those Cell sides.

This identifies the real vertex side underlying the prefix.  It deliberately
does not identify the true crossing-edge frontier of that side with the two
caller-supplied moving-cut edges; that is the next geometric question.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24AnnularCrosscut
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationVertexCutProfile
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialPrefixVertexSideEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The vertex side whose regional carrier is one literal source Cell. -/
noncomputable def sourceSlabLiteralCellVertexSideAt
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
    (offset : Fin (blockLength - 3)) : Finset V :=
  ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
      offset).separatedLocalLayerPair.componentSide
    ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
      offset).localLayerPairSourceCrosscutBoundaryData hcubic).component)ᶜ

/-- One literal Cell is exactly the edge carrier induced by its named vertex
side. -/
theorem sourceSlabLiteralCellRegionAt_eq_vertexSetRegionEdges_cellSide
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
    (offset : Fin (blockLength - 3)) :
    sourceSlabLiteralCellRegionAt realization hcubic hrotation htwoSided
        hunique offset =
      vertexSetRegionEdges embedded.cellulation.rotation.toRotationSystem
        (sourceSlabLiteralCellVertexSideAt realization hcubic hrotation
          htwoSided hunique offset) := by
  simpa [sourceSlabLiteralCellVertexSideAt] using
    sourceSlabLiteralCellRegionAt_eq_vertexSetRegionEdges_compl realization
      hcubic hrotation htwoSided hunique offset

/-- The retained vertex data of the first `cut` literal Cells. -/
noncomputable def sourceCorridorSerialPrefixVertexSide
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
    (cut : Nat) : Finset V :=
  (Finset.univ.filter fun offset : Fin (blockLength - 3) => offset.val < cut)
    |>.biUnion
      (sourceSlabLiteralCellVertexSideAt realization hcubic hrotation
        htwoSided hunique)

/-- The cumulative literal prefix is not an arbitrary edge region: it is
exactly the regional edge carrier induced by the union of its Cell sides. -/
theorem sourceCorridorSerialPrefixRegion_eq_vertexSetRegionEdges
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
    (cut : Nat) :
    sourceCorridorSerialPrefixRegion realization hcubic hrotation htwoSided
        hunique cut =
      vertexSetRegionEdges embedded.cellulation.rotation.toRotationSystem
        (sourceCorridorSerialPrefixVertexSide realization hcubic hrotation
          htwoSided hunique cut) := by
  unfold sourceCorridorSerialPrefixRegion
  unfold sourceCorridorSerialPrefixVertexSide
  rw [← vertexSetRegionEdges_biUnion]
  ext edge
  simp only [Finset.mem_biUnion]
  constructor
  · rintro ⟨offset, hoffset, hedge⟩
    refine ⟨offset, hoffset, ?_⟩
    rw [← sourceSlabLiteralCellRegionAt_eq_vertexSetRegionEdges_cellSide]
    exact hedge
  · rintro ⟨offset, hoffset, hedge⟩
    refine ⟨offset, hoffset, ?_⟩
    rw [sourceSlabLiteralCellRegionAt_eq_vertexSetRegionEdges_cellSide]
    exact hedge

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
