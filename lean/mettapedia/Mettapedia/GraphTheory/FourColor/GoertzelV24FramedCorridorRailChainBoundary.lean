import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorRailChain

/-!
# Closing a finite source rail chain into a layer boundary

`SourceCornerAlignedRailChain` retains the two actual exterior facial-dual
rails across a finite source segment.  Closing them with the two transverse
layers needs more than path composition: each rail must avoid both endpoint
centres, and the two rails must not meet.  This file packages exactly those
geometric requirements and proves that they produce a simple boundary cycle.

The requirements remain explicit.  In particular, this construction does not
claim that local rail-pair data alone proves a global separator.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24CleanHexCorridor
open GoertzelV24DualPathTransversal
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace SourceTrail

namespace AnnularEmbedding

/-- Every face visited by a source transverse layer is an internal annular
face.  The centre is one of the selected internal corridor faces, and each
endpoint is a full-dual neighbour covered by boundary cleanliness. -/
theorem SourceConsecutiveSlabInterface.localLayerWalk_support_internal
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
      leftInterior hnext)
    (face : AmbientFace (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (hface : face ∈ interface.localLayerWalk.support) :
    face.1 ∈ embedded.cellulation.interiorFaces := by
  have hpositive : 0 < blockLength := by omega
  simp only [SourceConsecutiveSlabInterface.localLayerWalk,
    SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
    List.mem_cons] at hface
  rcases hface with rfl | rfl | hface
  · apply realization.coreWalk_neighbor_internal hpositive leftInterior.center
    rw [realization.coreWalk_getVert hpositive leftInterior.center,
      ← realization.toCleanOrbitHexCorridorSkeleton_faceAt]
    exact interface.firstLayerFace_adjacent_centerLayerFace.symm
  · rw [SourceConsecutiveSlabInterface.centerLayerFace,
      realization.toCleanOrbitHexCorridorSkeleton_faceAt,
      ← realization.coreWalk_getVert hpositive leftInterior.center]
    exact (realization.coreWalk.getVert leftInterior.center.val).2
  · rcases hface with rfl | hfalse
    · apply realization.coreWalk_neighbor_internal hpositive leftInterior.center
      rw [realization.coreWalk_getVert hpositive leftInterior.center,
        ← realization.toCleanOrbitHexCorridorSkeleton_faceAt]
      exact interface.centerLayerFace_adjacent_secondLayerFace
    · simp at hfalse

/-- The exact finite noncollision data needed to close a rail chain with its
two endpoint transverse layers.  This is a geometric condition on the
literal source realization, not a consequence of finite profile equality. -/
structure SourceCornerAlignedRailChain.BoundarySeparation
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
    {hnextNext : (nextCorridorInterior leftInterior hnext).center.val + 2 < blockLength}
    {hnextThird :
      (nextCorridorInterior
        (nextCorridorInterior leftInterior hnext) hnextNext).center.val + 2 < blockLength}
    {first : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext}
    {last : SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior
        (nextCorridorInterior leftInterior hnext) hnextNext) hnextThird}
    (chain : SourceCornerAlignedRailChain first last) : Prop where
  firstRail_support_internal :
    ∀ face ∈ chain.firstRail.support,
      face.1 ∈ embedded.cellulation.interiorFaces
  secondRail_support_internal :
    ∀ face ∈ chain.secondRail.support,
      face.1 ∈ embedded.cellulation.interiorFaces
  firstRail_support_disjoint_secondRail :
    chain.firstRail.support.Disjoint chain.secondRail.support
  firstRail_avoids_firstCenter :
    first.toInterface.centerLayerFace ∉ chain.firstRail.support
  firstRail_avoids_lastCenter :
    last.toInterface.centerLayerFace ∉ chain.firstRail.support
  secondRail_avoids_firstCenter :
    first.toInterface.centerLayerFace ∉ chain.secondRail.support
  secondRail_avoids_lastCenter :
    last.toInterface.centerLayerFace ∉ chain.secondRail.support

/-- The endpoint centres of a three-interface rail chain are distinct because
their source-corridor indices differ by two. -/
theorem sourceCornerAlignedRailChain_endpointCenters_ne
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
    {hnextNext : (nextCorridorInterior leftInterior hnext).center.val + 2 < blockLength}
    {hnextThird :
      (nextCorridorInterior
        (nextCorridorInterior leftInterior hnext) hnextNext).center.val + 2 < blockLength}
    {first : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext}
    {last : SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior
        (nextCorridorInterior leftInterior hnext) hnextNext) hnextThird} :
    first.toInterface.centerLayerFace ≠ last.toInterface.centerLayerFace := by
  have hcenterIndex : leftInterior.center ≠
      (nextCorridorInterior
        (nextCorridorInterior leftInterior hnext) hnextNext).center := by
    intro h
    have hvalues := congrArg Fin.val h
    change leftInterior.center.val = leftInterior.center.val + 1 + 1 at hvalues
    omega
  intro hcenters
  apply realization.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt_ne
    hcenterIndex
  simpa [SourceConsecutiveSlabInterface.centerLayerFace] using hcenters

/-- Close the endpoint transverse layers by the two concrete rails retained
by a source chain. -/
noncomputable def SourceCornerAlignedRailChain.alignedBoundaryWalk
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
    {hnextNext : (nextCorridorInterior leftInterior hnext).center.val + 2 < blockLength}
    {hnextThird :
      (nextCorridorInterior
        (nextCorridorInterior leftInterior hnext) hnextNext).center.val + 2 < blockLength}
    {first : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext}
    {last : SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior
        (nextCorridorInterior leftInterior hnext) hnextNext) hnextThird}
    (chain : SourceCornerAlignedRailChain first last) :
    (interiorDualGraph
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Walk
      first.toInterface.firstLayerFace first.toInterface.firstLayerFace :=
  (((first.toInterface.localLayer.walk.append chain.secondRail).append
    last.toInterface.localLayer.walk.reverse).append chain.firstRail.reverse)

/-- The completed rail-chain boundary stays wholly in the annular interior.
This is the exact topological safety fact later used to keep the cut disjoint
from both source-container cycles. -/
theorem SourceCornerAlignedRailChain.alignedBoundaryWalk_support_internal
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
    {hnextNext : (nextCorridorInterior leftInterior hnext).center.val + 2 < blockLength}
    {hnextThird :
      (nextCorridorInterior
        (nextCorridorInterior leftInterior hnext) hnextNext).center.val + 2 < blockLength}
    {first : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext}
    {last : SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior
        (nextCorridorInterior leftInterior hnext) hnextNext) hnextThird}
    (chain : SourceCornerAlignedRailChain first last)
    (hseparation : chain.BoundarySeparation)
    (face : AmbientFace (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (hface : face ∈ chain.alignedBoundaryWalk.support) :
    face.1 ∈ embedded.cellulation.interiorFaces := by
  rw [SourceCornerAlignedRailChain.alignedBoundaryWalk,
    SimpleGraph.Walk.support_append] at hface
  rcases List.mem_append.mp hface with hfirstSecondLast | hfirstRail
  · rw [SimpleGraph.Walk.support_append] at hfirstSecondLast
    rcases List.mem_append.mp hfirstSecondLast with hfirstSecond | hlast
    · rw [SimpleGraph.Walk.support_append] at hfirstSecond
      rcases List.mem_append.mp hfirstSecond with hfirst | hsecond
      · exact first.toInterface.localLayerWalk_support_internal face hfirst
      · exact hseparation.secondRail_support_internal face
          (List.mem_of_mem_tail hsecond)
    · apply last.toInterface.localLayerWalk_support_internal face
      have hlast' := List.mem_of_mem_tail hlast
      simpa [SourceConsecutiveSlabInterface.localLayer,
        SimpleGraph.Walk.support_reverse] using hlast'
  · apply hseparation.firstRail_support_internal face
    have hfirstRail' := List.mem_of_mem_tail hfirstRail
    simpa [SimpleGraph.Walk.support_reverse] using hfirstRail'

/-- Explicit endpoint and rail separation turns a finite source rail chain
into a simple facial-dual cycle. -/
theorem SourceCornerAlignedRailChain.alignedBoundaryWalk_isCycle
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
    {hnextNext : (nextCorridorInterior leftInterior hnext).center.val + 2 < blockLength}
    {hnextThird :
      (nextCorridorInterior
        (nextCorridorInterior leftInterior hnext) hnextNext).center.val + 2 < blockLength}
    {first : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext}
    {last : SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior
        (nextCorridorInterior leftInterior hnext) hnextNext) hnextThird}
    (chain : SourceCornerAlignedRailChain first last)
    (hseparation : chain.BoundarySeparation) :
    chain.alignedBoundaryWalk.IsCycle := by
  let firstHalf := first.toInterface.localLayer.walk.append chain.secondRail
  let secondHalf := last.toInterface.localLayer.walk.reverse.append
    chain.firstRail.reverse
  have hrailDisjoint := List.disjoint_left.mp
    hseparation.firstRail_support_disjoint_secondRail
  have hfirstHalf : firstHalf.IsPath := by
    rw [← SimpleGraph.Walk.isPath_reverse_iff]
    let reverse0 := chain.secondRail.reverse.concat
      first.toInterface.centerLayerFace_adjacent_secondLayerFace.symm
    have hreverse0 : reverse0.IsPath := by
      apply chain.secondRail_isPath.reverse.concat
      simpa [SimpleGraph.Walk.support_reverse] using
        hseparation.secondRail_avoids_firstCenter
    have hfirstNotSecond :
        first.toInterface.firstLayerFace ∉ chain.secondRail.support := by
      intro hmem
      exact hrailDisjoint chain.firstRail.start_mem_support hmem
    have hreverse : (reverse0.concat
        first.toInterface.firstLayerFace_adjacent_centerLayerFace.symm).IsPath := by
      apply hreverse0.concat
      simp only [reverse0, SimpleGraph.Walk.support_concat,
        List.mem_append, List.mem_singleton]
      intro hmem
      rcases hmem with hmem | hmem
      · exact hfirstNotSecond (by
          simpa [SimpleGraph.Walk.support_reverse] using hmem)
      · exact first.toInterface.firstLayerFace_ne_centerLayerFace hmem
    simpa [firstHalf, reverse0, SourceConsecutiveSlabInterface.localLayer,
      SourceConsecutiveSlabInterface.localLayerWalk,
      SimpleGraph.Walk.reverse_append, SimpleGraph.Walk.concat,
      SimpleGraph.Walk.append_assoc] using hreverse
  have hsecondHalf : secondHalf.IsPath := by
    rw [← SimpleGraph.Walk.isPath_reverse_iff]
    let reverse0 := chain.firstRail.concat
      last.toInterface.firstLayerFace_adjacent_centerLayerFace
    have hreverse0 : reverse0.IsPath := by
      apply chain.firstRail_isPath.concat
      exact hseparation.firstRail_avoids_lastCenter
    have hsecondNotFirst :
        last.toInterface.secondLayerFace ∉ chain.firstRail.support := by
      intro hmem
      exact hrailDisjoint hmem chain.secondRail.end_mem_support
    have hreverse : (reverse0.concat
        last.toInterface.centerLayerFace_adjacent_secondLayerFace).IsPath := by
      apply hreverse0.concat
      simp only [reverse0, SimpleGraph.Walk.support_concat,
        List.mem_append, List.mem_singleton]
      intro hmem
      rcases hmem with hmem | hmem
      · exact hsecondNotFirst hmem
      · exact last.toInterface.secondLayerFace_ne_centerLayerFace hmem
    simpa [secondHalf, reverse0, SourceConsecutiveSlabInterface.localLayer,
      SourceConsecutiveSlabInterface.localLayerWalk,
      SimpleGraph.Walk.reverse_append, SimpleGraph.Walk.concat,
      SimpleGraph.Walk.append_assoc] using hreverse
  have htails : firstHalf.support.tail.Disjoint secondHalf.support.tail := by
    rw [List.disjoint_left]
    intro face hfirstFace hsecondFace
    simp only [firstHalf, secondHalf, SimpleGraph.Walk.support_append,
      SourceConsecutiveSlabInterface.localLayer,
      SourceConsecutiveSlabInterface.localLayerWalk,
      SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      SimpleGraph.Walk.support_reverse, List.reverse_cons, List.reverse_nil]
      at hfirstFace hsecondFace
    simp only [List.cons_append, List.nil_append, List.tail_cons,
      List.mem_cons] at hfirstFace hsecondFace
    have hfirstRail_of_rightEndpoint
        (hface : face = last.toInterface.firstLayerFace) :
        face ∈ chain.firstRail.support := by
      rw [hface]
      exact chain.firstRail.end_mem_support
    have hsecondRail_of_leftEndpoint
        (hface : face = first.toInterface.secondLayerFace) :
        face ∈ chain.secondRail.support := by
      rw [hface]
      exact chain.secondRail.start_mem_support
    have hfirstRail_of_reverseTail
        (hface : face ∈ chain.firstRail.support.reverse.tail) :
        face ∈ chain.firstRail.support := by
      have hmem := List.mem_of_mem_tail hface
      simpa using hmem
    have hsecondRail_of_tail
        (hface : face ∈ chain.secondRail.support.tail) :
        face ∈ chain.secondRail.support :=
      List.mem_of_mem_tail hface
    rcases hfirstFace with hfirstCenter | hfirstOuter | hsecondRail
    · rcases hsecondFace with hlastCenter | hlastOuter | hfirstRail
      · exact sourceCornerAlignedRailChain_endpointCenters_ne
          (hfirstCenter.symm.trans hlastCenter)
      · apply hseparation.firstRail_avoids_firstCenter
        simpa [hfirstCenter] using hfirstRail_of_rightEndpoint hlastOuter
      · apply hseparation.firstRail_avoids_firstCenter
        simpa [hfirstCenter] using hfirstRail_of_reverseTail hfirstRail
    · have hsecondRailMem := hsecondRail_of_leftEndpoint hfirstOuter
      rcases hsecondFace with hlastCenter | hlastOuter | hfirstRail
      · apply hseparation.secondRail_avoids_lastCenter
        simpa [hlastCenter] using hsecondRailMem
      · exact hrailDisjoint
          (hfirstRail_of_rightEndpoint hlastOuter) hsecondRailMem
      · exact hrailDisjoint
          (hfirstRail_of_reverseTail hfirstRail) hsecondRailMem
    · have hsecondRailMem := hsecondRail_of_tail hsecondRail
      rcases hsecondFace with hlastCenter | hlastOuter | hfirstRail
      · apply hseparation.secondRail_avoids_lastCenter
        simpa [hlastCenter] using hsecondRailMem
      · exact hrailDisjoint
          (hfirstRail_of_rightEndpoint hlastOuter) hsecondRailMem
      · exact hrailDisjoint
          (hfirstRail_of_reverseTail hfirstRail) hsecondRailMem
  have hcycle := SimpleGraph.Walk.IsPath.isCycle_append hfirstHalf hsecondHalf htails
    (Or.inl (by
      simp [firstHalf, SourceConsecutiveSlabInterface.localLayer,
        SourceConsecutiveSlabInterface.localLayerWalk]))
  simpa [SourceCornerAlignedRailChain.alignedBoundaryWalk, firstHalf, secondHalf,
    SimpleGraph.Walk.append_assoc] using hcycle

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
