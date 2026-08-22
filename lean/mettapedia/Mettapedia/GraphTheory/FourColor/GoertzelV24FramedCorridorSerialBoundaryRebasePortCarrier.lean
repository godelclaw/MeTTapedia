import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseCode

/-!
# Both sides of the literal serial boundary rebase on one finite carrier

The boundary-rebase seam is supported in the closed edge neighbourhood of the
two newly displayed crossings, a carrier of size at most fourteen.  A decoder
also has to know where the preceding profile's two displayed crossings enter
that local geometry.  They need not belong to the fourteen-edge seam carrier.

This file therefore adjoins those two old crossings explicitly.  The resulting
carrier has size at most sixteen and retains all four named ports: two from the
old prefix profile and two from the successor input profile.  The existing
tracked graph factors remain supported on this enlarged carrier.

This is finite coordinate bookkeeping for the source's heterogeneous rebase
letter.  It does not yet decode the successor five-field profile or assert
that every abstract finite code is geometrically realizable.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebasePortCarrierEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The two displayed ports of the old prefix profile at a rebase. -/
noncomputable def sourceCorridorSerialBoundaryRebaseOldEdgeSetAt
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
    (offset : Fin (blockLength - 3)) : Finset G.edgeSet :=
  indexedCrossingEdgeSet
    ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
      offset).nextLocalLayerPrefixCrossing)

/-- The old displayed pair has cardinality at most two. -/
theorem sourceCorridorSerialBoundaryRebaseOldEdgeSetAt_card_le_two
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
    (sourceCorridorSerialBoundaryRebaseOldEdgeSetAt realization hcubic
      hrotation htwoSided hunique offset).card ≤ 2 := by
  exact card_indexedCrossingEdgeSet_le _

/-- One common carrier containing the old two ports and every graph factor of
the boundary-rebase letter. -/
noncomputable def sourceCorridorSerialBoundaryRebasePortCarrierAt
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
    (hnext : offset.val + 1 < blockLength - 3) : Finset G.edgeSet :=
  sourceCorridorSerialBoundaryRebaseCarrierAt realization hcubic hrotation
      htwoSided hunique offset hnext ∪
    sourceCorridorSerialBoundaryRebaseOldEdgeSetAt realization hcubic
      hrotation htwoSided hunique offset

/-- Retaining the old ports costs at most two additional carrier positions. -/
theorem sourceCorridorSerialBoundaryRebasePortCarrierAt_card_le_sixteen
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
    (hnext : offset.val + 1 < blockLength - 3) :
    (sourceCorridorSerialBoundaryRebasePortCarrierAt realization hcubic
      hrotation htwoSided hunique offset hnext).card ≤ 16 := by
  rw [sourceCorridorSerialBoundaryRebasePortCarrierAt]
  calc
    _ ≤
        (sourceCorridorSerialBoundaryRebaseCarrierAt realization hcubic
          hrotation htwoSided hunique offset hnext).card +
        (sourceCorridorSerialBoundaryRebaseOldEdgeSetAt realization hcubic
          hrotation htwoSided hunique offset).card := Finset.card_union_le _ _
    _ ≤ 14 + 2 := Nat.add_le_add
      (sourceCorridorSerialBoundaryRebaseCarrierAt_card_le_fourteen realization
        hcubic hrotation htwoSided hunique offset hnext)
      (sourceCorridorSerialBoundaryRebaseOldEdgeSetAt_card_le_two realization
        hcubic hrotation htwoSided hunique offset)
    _ = 16 := by norm_num

/-- One named port on either side of the rebase, transported into the common
sixteen-edge carrier.  `Sum.inl` denotes an old output port and `Sum.inr` a
new successor-input port. -/
noncomputable def sourceCorridorSerialBoundaryRebasePortAt
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
    (port : Fin 2 ⊕ Fin 2) :
    {edge // edge ∈
      sourceCorridorSerialBoundaryRebasePortCarrierAt realization hcubic
        hrotation htwoSided hunique offset hnext} := by
  rcases port with old | new
  · refine ⟨
      (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        offset).nextLocalLayerPrefixCrossing old, ?_⟩
    apply Finset.mem_union_right
    exact (mem_indexedCrossingEdgeSet_iff _ _).2 ⟨old, rfl⟩
  · refine ⟨sourceCorridorSerialBoundaryRebaseCrossingAt realization
      hcubic hrotation htwoSided hunique offset hnext new, ?_⟩
    apply Finset.mem_union_left
    exact (sourceCorridorSerialBoundaryRebasePointAt realization hcubic
      hrotation htwoSided hunique offset hnext new).2

/-- The existing tracked local/remainder graphs remain fully supported after
the old ports are adjoined. -/
theorem sourceCorridorSerialBoundaryRebaseTrackedGraphAt_support_subset_portCarrier
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
    (color : G.edgeSet → Color)
    (factor : SourceCorridorSerialBoundaryRebaseTrackedFactor) :
    (sourceCorridorSerialBoundaryRebaseTrackedGraphAt realization hcubic
      hrotation htwoSided hunique offset hnext color factor).support ⊆
      sourceCorridorSerialBoundaryRebasePortCarrierAt realization hcubic
        hrotation htwoSided hunique offset hnext := by
  intro edge hedge
  apply Finset.mem_union_left
  exact sourceCorridorSerialBoundaryRebaseTrackedGraphAt_support_subset_carrier
    realization hcubic hrotation htwoSided hunique offset hnext color factor hedge

/-- The complete tracked rebase code with both the old and new profile ports
retained in one fixed coordinate system. -/
noncomputable def sourceCorridorSerialBoundaryRebasePortTrackedCodeAt
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
    (color : G.edgeSet → Color) :
    BoundedCarrierGraphFamilyCode 16 4
      SourceCorridorSerialBoundaryRebaseTrackedFactor :=
  boundedCarrierGraphFamilyCode
    (sourceCorridorSerialBoundaryRebasePortCarrierAt realization hcubic
      hrotation htwoSided hunique offset hnext)
    16 4
    (sourceCorridorSerialBoundaryRebasePortCarrierAt_card_le_sixteen
      realization hcubic hrotation htwoSided hunique offset hnext)
    (fun index => sourceCorridorSerialBoundaryRebasePortAt realization hcubic
      hrotation htwoSided hunique offset hnext (finSumFinEquiv.symm index))
    (sourceCorridorSerialBoundaryRebaseTrackedGraphAt realization hcubic
      hrotation htwoSided hunique offset hnext color)

/-- The first two distinguished finite coordinates are exactly the old
profile ports. -/
theorem sourceCorridorSerialBoundaryRebasePortTrackedCodeAt_oldPoint
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
    (color : G.edgeSet → Color) (step : Fin 2) :
    (sourceCorridorSerialBoundaryRebasePortTrackedCodeAt realization hcubic
      hrotation htwoSided hunique offset hnext color).point
        (finSumFinEquiv (Sum.inl step : Fin 2 ⊕ Fin 2)) =
      carrierCoordinate
        (sourceCorridorSerialBoundaryRebasePortCarrierAt realization hcubic
          hrotation htwoSided hunique offset hnext)
        (sourceCorridorSerialBoundaryRebasePortAt realization hcubic hrotation
          htwoSided hunique offset hnext (.inl step)) := by
  change carrierCoordinate _
      (sourceCorridorSerialBoundaryRebasePortAt realization hcubic hrotation
        htwoSided hunique offset hnext
        (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl step)))) = _
  rw [Equiv.symm_apply_apply]

/-- The last two distinguished finite coordinates are exactly the new
successor-input ports. -/
theorem sourceCorridorSerialBoundaryRebasePortTrackedCodeAt_newPoint
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
    (color : G.edgeSet → Color) (step : Fin 2) :
    (sourceCorridorSerialBoundaryRebasePortTrackedCodeAt realization hcubic
      hrotation htwoSided hunique offset hnext color).point
        (finSumFinEquiv (Sum.inr step : Fin 2 ⊕ Fin 2)) =
      carrierCoordinate
        (sourceCorridorSerialBoundaryRebasePortCarrierAt realization hcubic
          hrotation htwoSided hunique offset hnext)
        (sourceCorridorSerialBoundaryRebasePortAt realization hcubic hrotation
          htwoSided hunique offset hnext (.inr step)) := by
  change carrierCoordinate _
      (sourceCorridorSerialBoundaryRebasePortAt realization hcubic hrotation
        htwoSided hunique offset hnext
        (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr step)))) = _
  rw [Equiv.symm_apply_apply]

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
