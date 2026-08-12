import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorAlignedTwoTileOpenTangle
import Mettapedia.GraphTheory.FourColor.GoertzelV24CorridorProfilePortPartition

/-!
# Enclosed-side profile of an aligned two-tile source slab

The certified aligned slab has one physical six-edge boundary.  Its existing
terminal presentation computes regional connectivity and face fragments on the
outer retained component.  The literal open tangle, however, is the enclosed
complementary component.  This file therefore reuses only the exact physical
port order and recomputes graph-derived profile data on that enclosed side.

It does not identify the two regional fragment carriers, assert serial gluing,
or turn the local `4 + 2` slab boundary into a persistent corridor state.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24CorridorProfile
open GoertzelV24CorridorProfilePortPartition
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationVertexCutProfile
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorAlignedTwoTileEnclosedProfileEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- One certified physical `4 + 2` port, viewed as a crossing of the enclosed
component.  Only the physical edge is reused from the retained-side boundary
presentation; its regional profile is reconstructed below. -/
noncomputable def sourceTwoTileAlignedEnclosedPortCrossing
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
        htwoSided hunique offset).componentSideᶜ := by
  let boundary := sourceTwoTileAlignedLayerBoundaryAt realization hcubic
    hrotation htwoSided hunique offset
  refine ⟨(sourceTwoTileAlignedTerminalPortCrossing realization hcubic
    hrotation htwoSided hunique offset port).1, ?_⟩
  rw [mem_vertexSetCrossingEdges_iff]
  apply (edgeCrossesVertexSet_compl
    embedded.cellulation.rotation.toRotationSystem boundary.componentSide _).2
  rw [← mem_vertexSetCrossingEdges_iff]
  exact (sourceTwoTileAlignedTerminalPortCrossing realization hcubic
    hrotation htwoSided hunique offset port).2

/-- The enclosed crossing coordinate has exactly the same underlying physical
edge as the already certified slab port. -/
@[simp]
theorem sourceTwoTileAlignedEnclosedPortCrossing_val
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
    (sourceTwoTileAlignedEnclosedPortCrossing realization hcubic hrotation
      htwoSided hunique offset port).1 =
      (sourceTwoTileAlignedTerminalPortCrossing realization hcubic hrotation
        htwoSided hunique offset port).1 :=
  rfl

/-- The certified physical ports still enumerate the whole crossing carrier
when the same layer is read from its enclosed side. -/
theorem sourceTwoTileAlignedEnclosedPortCrossing_injective
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
      (sourceTwoTileAlignedEnclosedPortCrossing realization hcubic hrotation
        htwoSided hunique offset) := by
  intro first second heq
  apply sourceTwoTileAlignedTerminalPortCrossing_injective realization hcubic
    hrotation htwoSided hunique offset
  apply Subtype.ext
  simpa only [sourceTwoTileAlignedEnclosedPortCrossing_val] using
    congrArg Subtype.val heq

theorem sourceTwoTileAlignedEnclosedPortCrossing_surjective
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
      (sourceTwoTileAlignedEnclosedPortCrossing realization hcubic hrotation
        htwoSided hunique offset) := by
  intro crossing
  let boundary := sourceTwoTileAlignedLayerBoundaryAt realization hcubic
    hrotation htwoSided hunique offset
  have hretained : crossing.1 ∈
      vertexSetCrossingEdges embedded.cellulation.rotation.toRotationSystem
        boundary.componentSide := by
    rw [mem_vertexSetCrossingEdges_iff]
    apply (edgeCrossesVertexSet_compl
      embedded.cellulation.rotation.toRotationSystem boundary.componentSide _).1
    rw [← mem_vertexSetCrossingEdges_iff]
    exact crossing.2
  obtain ⟨port, hport⟩ :=
    sourceTwoTileAlignedTerminalPortCrossing_surjective realization hcubic
      hrotation htwoSided hunique offset ⟨crossing.1, hretained⟩
  refine ⟨port, ?_⟩
  apply Subtype.ext
  simpa only [sourceTwoTileAlignedEnclosedPortCrossing_val] using
    congrArg Subtype.val hport

/-- The source's physical `4 + 2` order gives an exact crossing indexing for
the enclosed-side graph profile. -/
noncomputable def sourceTwoTileAlignedEnclosedCrossingIndexing
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
    VertexSetCrossingIndexing embedded.cellulation.rotation.toRotationSystem
      (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
        htwoSided hunique offset).componentSideᶜ := by
  let hportEquiv := Equiv.ofBijective
    (sourceTwoTileAlignedEnclosedPortCrossing realization hcubic hrotation
      htwoSided hunique offset)
    ⟨sourceTwoTileAlignedEnclosedPortCrossing_injective realization hcubic
        hrotation htwoSided hunique offset,
      sourceTwoTileAlignedEnclosedPortCrossing_surjective realization hcubic
        hrotation htwoSided hunique offset⟩
  let hcard : Fintype.card (VertexSetCrossingEdge
      embedded.cellulation.rotation.toRotationSystem
      (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
        htwoSided hunique offset).componentSideᶜ) = 4 + 2 := by
    simpa only [Fintype.card_sum, Fintype.card_fin] using
      (Fintype.card_congr hportEquiv).symm
  exact (finCongr hcard).trans ((finSumFinEquiv).symm.trans hportEquiv)

/-- Full graph-derived profile data for the literal enclosed side of one
aligned slab.  Its boundary order is shared with the physical open tangle,
but its connectivity and face fragments are computed afresh on that tangle's
vertex side. -/
noncomputable def sourceTwoTileAlignedEnclosedOrderedProfileDataAt
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
  vertexSetBoundaryGraphCutDataWithIndexing
    embedded.cellulation.rotation.toRotationSystem
    (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
      htwoSided hunique offset).componentSideᶜ
    (sourceTwoTileAlignedEnclosedCrossingIndexing realization hcubic hrotation
      htwoSided hunique offset)

/-- The dependent raw-profile coordinate of one displayed physical port on
the enclosed side. -/
noncomputable def sourceTwoTileAlignedEnclosedPortProfileIndexAt
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
    Fin (Fintype.card (VertexSetCrossingEdge
      embedded.cellulation.rotation.toRotationSystem
      (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
        htwoSided hunique offset).componentSideᶜ)) :=
  (sourceTwoTileAlignedEnclosedCrossingIndexing realization hcubic hrotation
    htwoSided hunique offset).symm
      (sourceTwoTileAlignedEnclosedPortCrossing realization hcubic hrotation
        htwoSided hunique offset port)

/-- Reading the freshly computed enclosed profile at its source coordinate
recovers the same physical edge as the literal open-tangle boundary port. -/
@[simp]
theorem sourceTwoTileAlignedEnclosedOrderedProfileDataAt_crossingEdge
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
    (sourceTwoTileAlignedEnclosedOrderedProfileDataAt realization hcubic
      hrotation htwoSided hunique offset).crossingEdge
        (sourceTwoTileAlignedEnclosedPortProfileIndexAt realization hcubic
          hrotation htwoSided hunique offset port) =
      (sourceTwoTileAlignedTerminalProfileDataAt realization hcubic hrotation
        htwoSided hunique offset).portEdge port := by
  simp only [sourceTwoTileAlignedEnclosedOrderedProfileDataAt,
    sourceTwoTileAlignedEnclosedPortProfileIndexAt,
    vertexSetBoundaryGraphCutDataWithIndexing,
    vertexSetCrossingEdgeAtWithIndexing,
    sourceTwoTileAlignedEnclosedCrossingIndexing]
  rw [Equiv.apply_symm_apply]
  rfl

/-- The enclosed-side graph profile, partitioned into the same four transverse
and two rail coordinates as the literal slab boundary.  Its five profile
fields are all computed from the enclosed region. -/
noncomputable def sourceTwoTileAlignedEnclosedTerminalProfileDataAt
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
  GoertzelV24CorridorProfilePortPartition.GraphCorridorCutData.partitionCrossings
    (sourceTwoTileAlignedEnclosedOrderedProfileDataAt realization hcubic
      hrotation htwoSided hunique offset)
    (fun crossing =>
      sourceTwoTileAlignedEnclosedPortProfileIndexAt realization hcubic
        hrotation htwoSided hunique offset (.inl crossing))
    (fun terminal =>
      sourceTwoTileAlignedEnclosedPortProfileIndexAt realization hcubic
        hrotation htwoSided hunique offset (.inr terminal))

/-- The enclosed `4 + 2` profile and the literal open tangle name exactly the
same physical boundary edge at every port. -/
@[simp]
theorem sourceTwoTileAlignedEnclosedTerminalProfileDataAt_portEdge
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
    (sourceTwoTileAlignedEnclosedTerminalProfileDataAt realization hcubic
      hrotation htwoSided hunique offset).portEdge port =
      (sourceTwoTileAlignedTerminalProfileDataAt realization hcubic hrotation
        htwoSided hunique offset).portEdge port := by
  rcases port with crossing | terminal
  · change
      (sourceTwoTileAlignedEnclosedOrderedProfileDataAt realization hcubic
        hrotation htwoSided hunique offset).crossingEdge
          (sourceTwoTileAlignedEnclosedPortProfileIndexAt realization hcubic
            hrotation htwoSided hunique offset (.inl crossing)) = _
    exact sourceTwoTileAlignedEnclosedOrderedProfileDataAt_crossingEdge
      realization hcubic hrotation htwoSided hunique offset (.inl crossing)
  · change
      (sourceTwoTileAlignedEnclosedOrderedProfileDataAt realization hcubic
        hrotation htwoSided hunique offset).crossingEdge
          (sourceTwoTileAlignedEnclosedPortProfileIndexAt realization hcubic
            hrotation htwoSided hunique offset (.inr terminal)) = _
    exact sourceTwoTileAlignedEnclosedOrderedProfileDataAt_crossingEdge
      realization hcubic hrotation htwoSided hunique offset (.inr terminal)

/-- Every displayed enclosed-side port lies in the exact regional carrier on
which its connectivity and face fragments are computed. -/
theorem sourceTwoTileAlignedEnclosedTerminalProfileDataAt_portsInRegion
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
      hrotation htwoSided hunique offset).PortsInRegion := by
  apply GoertzelV24CorridorProfilePortPartition.GraphCorridorCutData.partitionCrossings_portsInRegion
  exact vertexSetBoundaryGraphCutDataWithIndexing_portsInRegion
    embedded.cellulation.rotation.toRotationSystem
    (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
      htwoSided hunique offset).componentSideᶜ
    (sourceTwoTileAlignedEnclosedCrossingIndexing realization hcubic hrotation
      htwoSided hunique offset)

/-- The physical `4 + 2` ports remain distinct after their enclosed-side
profile is recomputed. -/
theorem sourceTwoTileAlignedEnclosedTerminalProfileDataAt_portsInjective
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
      hrotation htwoSided hunique offset).PortsInjective := by
  intro first second heq
  apply sourceTwoTileAlignedTerminalProfileDataAt_portsInjective realization
    hcubic hrotation htwoSided hunique offset
  simpa only [← sourceTwoTileAlignedEnclosedTerminalProfileDataAt_portEdge
    realization hcubic hrotation htwoSided hunique offset first,
    ← sourceTwoTileAlignedEnclosedTerminalProfileDataAt_portEdge
      realization hcubic hrotation htwoSided hunique offset second] using heq

/-- The recomputed enclosed-side profile is indexed by the literal boundary
half-edges of the corresponding open tangle. -/
@[simp]
theorem sourceTwoTileAlignedEnclosedTerminalProfileDataAt_portEdge_eq_boundaryDart
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
    (sourceTwoTileAlignedEnclosedTerminalProfileDataAt realization hcubic
      hrotation htwoSided hunique offset).portEdge port =
      embedded.cellulation.rotation.toRotationSystem.edgeOf
        ((sourceTwoTileAlignedTerminalPortBoundaryDartEquiv realization hcubic
          hrotation htwoSided hunique offset port).1.1) := by
  rw [sourceTwoTileAlignedEnclosedTerminalProfileDataAt_portEdge]
  exact (sourceTwoTileAlignedTerminalPortBoundaryDartEquiv_edgeOf realization
    hcubic hrotation htwoSided hunique offset port).symm

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
