import Mettapedia.GraphTheory.FourColor.GoertzelV24DeletedRegionBoundaryOrder
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorAlignedTwoTilePortExact
import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenTangleComposition

/-!
# Literal open boundary of an aligned two-tile source slab

The six physical ports of an aligned source slab are not merely a finite
profile coordinate.  On the component enclosed by its certified layer
boundary, they are exactly the six literal boundary half-edges of the
cut-open rotation system.  This file exposes that equivalence.

The result is deliberately an interface-realization theorem only.  It does
not identify this local framed boundary with a serial composite, does not
declare the two rail ports persistent at a neighbouring slab, and does not
replace the moving two-port profile by a six-port state.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24CorridorProfile
open GoertzelV24DeletedRegionBoundaryOrder
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

local instance framedCorridorAlignedTwoTileOpenBoundaryEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The actual crossing edge named by one displayed `4 + 2` aligned-slab
port, regarded as a crossing of the enclosed (non-outer) component. -/
noncomputable def sourceTwoTileAlignedTerminalPortCrossing
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
    VertexSetCrossingEdge embedded.cellulation.rotation.toRotationSystem
      (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
        htwoSided hunique offset).componentSide := by
  let boundary := sourceTwoTileAlignedLayerBoundaryAt realization hcubic
    hrotation htwoSided hunique offset
  refine ⟨(sourceTwoTileAlignedTerminalProfileDataAt realization hcubic
    hrotation htwoSided hunique offset).portEdge port, ?_⟩
  rw [sourceTwoTileAlignedTerminalProfileDataAt_portEdge_eq_orderedCrossing]
  exact boundary.orderedCrossing_mem
    (sourceTwoTileAlignedTerminalPortBoundaryIndexAt realization hcubic
      hrotation htwoSided hunique offset port)

/-- The crossing coordinate forgets no information: its underlying edge is
the profile port edge by construction. -/
@[simp]
theorem sourceTwoTileAlignedTerminalPortCrossing_val
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
    (sourceTwoTileAlignedTerminalPortCrossing realization hcubic hrotation
      htwoSided hunique offset port).1 =
      (sourceTwoTileAlignedTerminalProfileDataAt realization hcubic
        hrotation htwoSided hunique offset).portEdge port :=
  by
    rfl

/-- Distinct displayed ports determine distinct crossing-edge coordinates. -/
theorem sourceTwoTileAlignedTerminalPortCrossing_injective
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
    Function.Injective
      (sourceTwoTileAlignedTerminalPortCrossing realization hcubic hrotation
        htwoSided hunique offset) := by
  intro first second heq
  apply sourceTwoTileAlignedTerminalProfileDataAt_portsInjective realization
    hcubic hrotation htwoSided hunique offset
  simpa only [sourceTwoTileAlignedTerminalPortCrossing_val] using
    congrArg Subtype.val heq

/-- The physical `4 + 2` ports exhaust the crossing-edge carrier of the
enclosed aligned slab. -/
theorem sourceTwoTileAlignedTerminalPortCrossing_surjective
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
    Function.Surjective
      (sourceTwoTileAlignedTerminalPortCrossing realization hcubic hrotation
        htwoSided hunique offset) := by
  intro crossing
  let boundary := sourceTwoTileAlignedLayerBoundaryAt realization hcubic
    hrotation htwoSided hunique offset
  have hboundary : crossing.1 ∈
      sourceTwoTileAlignedBoundaryCrossingEdgesAt realization hcubic
        hrotation htwoSided hunique offset := by
    rw [← sourceTwoTileAlignedLayerBoundaryAt_cutEdges,
      ← boundary.vertexSetCrossingEdges_componentSide_eq_cutEdges]
    exact crossing.2
  rw [← sourceTwoTileAlignedTerminalProfileDataAt_portEdges_eq_boundary
    realization hcubic hrotation htwoSided hunique offset] at hboundary
  rcases Finset.mem_image.mp hboundary with ⟨port, _hport, hedge⟩
  refine ⟨port, ?_⟩
  apply Subtype.ext
  simpa only [sourceTwoTileAlignedTerminalPortCrossing_val] using hedge

/-- The six displayed physical ports are exactly the actual crossing-edge
carrier of the enclosed source slab. -/
noncomputable def sourceTwoTileAlignedTerminalPortCrossingEquiv
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
    CorridorPort 4 2 ≃
      VertexSetCrossingEdge embedded.cellulation.rotation.toRotationSystem
        (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
          htwoSided hunique offset).componentSide :=
  Equiv.ofBijective
    (sourceTwoTileAlignedTerminalPortCrossing realization hcubic hrotation
      htwoSided hunique offset)
    ⟨sourceTwoTileAlignedTerminalPortCrossing_injective realization hcubic
        hrotation htwoSided hunique offset,
      sourceTwoTileAlignedTerminalPortCrossing_surjective realization hcubic
        hrotation htwoSided hunique offset⟩

/-- The six displayed physical ports are exactly the fresh boundary
half-edges of the component enclosed by the aligned source layer. -/
noncomputable def sourceTwoTileAlignedTerminalPortBoundaryDartEquiv
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
    CorridorPort 4 2 ≃
      BoundaryDart embedded.cellulation.rotation.toRotationSystem
        (deletedRegionKeep
          (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
            htwoSided hunique offset).componentSide) :=
  (sourceTwoTileAlignedTerminalPortCrossingEquiv realization hcubic
    hrotation htwoSided hunique offset).trans
    (boundaryDartEquivVertexSetCrossingEdge
      embedded.cellulation.rotation.toRotationSystem
      (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
        htwoSided hunique offset).componentSide).symm

/-- Reading the boundary dart supplied by a displayed port recovers exactly
that physical source edge. -/
theorem sourceTwoTileAlignedTerminalPortBoundaryDartEquiv_edgeOf
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
    embedded.cellulation.rotation.toRotationSystem.edgeOf
        ((sourceTwoTileAlignedTerminalPortBoundaryDartEquiv realization hcubic
          hrotation htwoSided hunique offset port).1.1) =
      (sourceTwoTileAlignedTerminalProfileDataAt realization hcubic
        hrotation htwoSided hunique offset).portEdge port := by
  let crossingEquiv := sourceTwoTileAlignedTerminalPortCrossingEquiv
    realization hcubic hrotation htwoSided hunique offset
  let boundaryEquiv := boundaryDartEquivVertexSetCrossingEdge
    embedded.cellulation.rotation.toRotationSystem
    (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
      htwoSided hunique offset).componentSide
  change (boundaryEquiv (boundaryEquiv.symm (crossingEquiv port))).1 = _
  rw [boundaryEquiv.apply_symm_apply]
  exact sourceTwoTileAlignedTerminalPortCrossing_val realization hcubic
    hrotation htwoSided hunique offset port

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
