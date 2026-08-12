import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorIntercellRailSupport

/-!
# Source-aligned two-tile boundary support

The two transverse source layers account for four crossings of a two-tile
boundary.  The paired exterior rails account for the other two.  This module
assembles those four actual facial-dual walks before passing to a finite
boundary carrier, so the lateral crossings cannot disappear behind an
abstract identification of the two transverse interfaces.
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

local instance framedCorridorAlignedTwoTileBoundaryEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- Close the two transverse layer walks with the corresponding exterior
rails.  The order follows the boundary starting at the first interface's
first exterior face. -/
noncomputable def SourceCornerAlignedRailPair.alignedBoundaryWalk
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
    {hnextNext :
      (nextCorridorInterior leftInterior hnext).center.val + 2 < blockLength}
    {first : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext}
    {second : SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior leftInterior hnext) hnextNext}
    (pair : SourceCornerAlignedRailPair first second) :
    (interiorDualGraph
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Walk
      first.toInterface.firstLayerFace first.toInterface.firstLayerFace :=
  (((first.toInterface.localLayer.walk.append pair.secondRail).append
    second.toInterface.localLayer.walk.reverse).append pair.firstRail.reverse)

/-- Two disjoint source rails close the transverse layers to a simple cycle.
The rail-pair record carries the local center-avoidance facts established by
the three source rung cases. -/
theorem SourceCornerAlignedRailPair.alignedBoundaryWalk_isCycle
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
    {hnextNext :
      (nextCorridorInterior leftInterior hnext).center.val + 2 < blockLength}
    {first : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext}
    {second : SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior leftInterior hnext) hnextNext}
    (pair : SourceCornerAlignedRailPair first second) :
    pair.alignedBoundaryWalk.IsCycle := by
  let firstHalf := first.toInterface.localLayer.walk.append pair.secondRail
  let secondHalf := second.toInterface.localLayer.walk.reverse.append
    pair.firstRail.reverse
  have hrailDisjoint := List.disjoint_left.mp
    pair.firstRail_support_disjoint_secondRail
  have hfirstHalf : firstHalf.IsPath := by
    rw [← SimpleGraph.Walk.isPath_reverse_iff]
    let reverse0 := pair.secondRail.reverse.concat
      first.toInterface.centerLayerFace_adjacent_secondLayerFace.symm
    have hreverse0 : reverse0.IsPath := by
      apply pair.secondRail_isPath.reverse.concat
      simpa [SimpleGraph.Walk.support_reverse] using
        pair.secondRail_avoids_firstCenter
    have hfirstNotSecond :
        first.toInterface.firstLayerFace ∉ pair.secondRail.support := by
      intro hmem
      exact hrailDisjoint pair.firstRail.start_mem_support hmem
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
    let reverse0 := pair.firstRail.concat
      second.toInterface.firstLayerFace_adjacent_centerLayerFace
    have hreverse0 : reverse0.IsPath := by
      apply pair.firstRail_isPath.concat
      exact pair.firstRail_avoids_secondCenter
    have hsecondNotFirst :
        second.toInterface.secondLayerFace ∉ pair.firstRail.support := by
      intro hmem
      exact hrailDisjoint hmem pair.secondRail.end_mem_support
    have hreverse : (reverse0.concat
        second.toInterface.centerLayerFace_adjacent_secondLayerFace).IsPath := by
      apply hreverse0.concat
      simp only [reverse0, SimpleGraph.Walk.support_concat,
        List.mem_append, List.mem_singleton]
      intro hmem
      rcases hmem with hmem | hmem
      · exact hsecondNotFirst hmem
      · exact second.toInterface.secondLayerFace_ne_centerLayerFace hmem
    simpa [secondHalf, reverse0, SourceConsecutiveSlabInterface.localLayer,
      SourceConsecutiveSlabInterface.localLayerWalk,
      SimpleGraph.Walk.reverse_append, SimpleGraph.Walk.concat,
      SimpleGraph.Walk.append_assoc] using hreverse
  have hcenterIndex : leftInterior.center ≠
      (nextCorridorInterior leftInterior hnext).center := by
    intro h
    have hvalues := congrArg Fin.val h
    change leftInterior.center.val = leftInterior.center.val + 1 at hvalues
    omega
  have hcenters : first.toInterface.centerLayerFace ≠
      second.toInterface.centerLayerFace := by
    simpa [SourceConsecutiveSlabInterface.centerLayerFace] using
      realization.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt_ne
        hcenterIndex
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
        (hface : face = second.toInterface.firstLayerFace) :
        face ∈ pair.firstRail.support := by
      rw [hface]
      exact pair.firstRail.end_mem_support
    have hsecondRail_of_leftEndpoint
        (hface : face = first.toInterface.secondLayerFace) :
        face ∈ pair.secondRail.support := by
      rw [hface]
      exact pair.secondRail.start_mem_support
    have hfirstRail_of_reverseTail
        (hface : face ∈ pair.firstRail.support.reverse.tail) :
        face ∈ pair.firstRail.support := by
      have hmem := List.mem_of_mem_tail hface
      simpa using hmem
    have hsecondRail_of_tail
        (hface : face ∈ pair.secondRail.support.tail) :
        face ∈ pair.secondRail.support :=
      List.mem_of_mem_tail hface
    rcases hfirstFace with hfirstCenter | hfirstOuter | hsecondRail
    · rcases hsecondFace with hsecondCenter | hsecondOuter | hfirstRail
      · exact hcenters (hfirstCenter.symm.trans hsecondCenter)
      · apply pair.firstRail_avoids_firstCenter
        simpa [hfirstCenter] using hfirstRail_of_rightEndpoint hsecondOuter
      · apply pair.firstRail_avoids_firstCenter
        simpa [hfirstCenter] using hfirstRail_of_reverseTail hfirstRail
    · have hsecondRailMem := hsecondRail_of_leftEndpoint hfirstOuter
      rcases hsecondFace with hsecondCenter | hsecondOuter | hfirstRail
      · apply pair.secondRail_avoids_secondCenter
        simpa [hsecondCenter] using hsecondRailMem
      · exact hrailDisjoint
          (hfirstRail_of_rightEndpoint hsecondOuter) hsecondRailMem
      · exact hrailDisjoint
          (hfirstRail_of_reverseTail hfirstRail) hsecondRailMem
    · have hsecondRailMem := hsecondRail_of_tail hsecondRail
      rcases hsecondFace with hsecondCenter | hsecondOuter | hfirstRail
      · apply pair.secondRail_avoids_secondCenter
        simpa [hsecondCenter] using hsecondRailMem
      · exact hrailDisjoint
          (hfirstRail_of_rightEndpoint hsecondOuter) hsecondRailMem
      · exact hrailDisjoint
          (hfirstRail_of_reverseTail hfirstRail) hsecondRailMem
  have hcycle := SimpleGraph.Walk.IsPath.isCycle_append hfirstHalf hsecondHalf htails
    (Or.inl (by
      simp [firstHalf, SourceConsecutiveSlabInterface.localLayer,
        SourceConsecutiveSlabInterface.localLayerWalk]))
  simpa [SourceCornerAlignedRailPair.alignedBoundaryWalk, firstHalf, secondHalf,
    SimpleGraph.Walk.append_assoc] using hcycle

/-- The literal closed facial-dual walk obtained from the first transverse
layer, the second exterior rail, the reversed second transverse layer, and
the reversed first exterior rail.  Its construction retains all four source
pieces; the theorem below derives simplicity from their checked local
separation data. -/
noncomputable def sourceTwoTileAlignedBoundaryWalkAt
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
    (interiorDualGraph
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Walk
      (sourceTwoTileFirstInterfaceAt realization hcubic hrotation htwoSided
        hunique offset).toInterface.firstLayerFace
      (sourceTwoTileFirstInterfaceAt realization hcubic hrotation htwoSided
        hunique offset).toInterface.firstLayerFace := by
  let first := sourceTwoTileFirstInterfaceAt realization hcubic hrotation
    htwoSided hunique offset
  let second := sourceTwoTileSecondInterfaceAt realization hcubic hrotation
    htwoSided hunique offset
  let pair := sourceTwoTileRailPairAt realization hcubic hrotation htwoSided
    hunique offset
  exact (((first.toInterface.localLayer.walk.append pair.secondRail).append
    second.toInterface.localLayer.walk.reverse).append pair.firstRail.reverse)

/-- The source-indexed aligned boundary is a genuine simple facial-dual
cycle. -/
theorem sourceTwoTileAlignedBoundaryWalkAt_isCycle
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
    (sourceTwoTileAlignedBoundaryWalkAt realization hcubic hrotation htwoSided
      hunique offset).IsCycle := by
  simpa [sourceTwoTileAlignedBoundaryWalkAt,
    SourceCornerAlignedRailPair.alignedBoundaryWalk] using
    (sourceTwoTileRailPairAt realization hcubic hrotation htwoSided hunique
      offset).alignedBoundaryWalk_isCycle

/-- The aligned walk has the source's exact `2 + 2 + 2` length: two steps
through each transverse layer and two exterior-rail steps in total. -/
theorem sourceTwoTileAlignedBoundaryWalkAt_length_eq_six
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
    (sourceTwoTileAlignedBoundaryWalkAt realization hcubic hrotation htwoSided
      hunique offset).length = 6 := by
  dsimp [sourceTwoTileAlignedBoundaryWalkAt]
  simp only [SimpleGraph.Walk.length_append,
    SimpleGraph.Walk.length_reverse]
  rw [(sourceTwoTileFirstInterfaceAt realization hcubic hrotation htwoSided
      hunique offset).toInterface.localLayer_walk_length_eq_two,
    (sourceTwoTileSecondInterfaceAt realization hcubic hrotation htwoSided
      hunique offset).toInterface.localLayer_walk_length_eq_two]
  have hrails := (sourceTwoTileRailPairAt realization hcubic hrotation
    htwoSided hunique offset).firstRail_length_add_secondRail_length_eq_two
  omega

/-- The two crossings supplied by the first transverse source layer. -/
noncomputable def sourceTwoTileFirstLayerCrossingEdgesAt
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
    (offset : Fin (blockLength - 4)) : Finset G.edgeSet :=
  dualWalkCrossingEdges
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
    (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
    (sourceTwoTileFirstInterfaceAt realization hcubic hrotation htwoSided
      hunique offset).toInterface.localLayer.walk

/-- The two crossings supplied by the second transverse source layer. -/
noncomputable def sourceTwoTileSecondLayerCrossingEdgesAt
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
    (offset : Fin (blockLength - 4)) : Finset G.edgeSet :=
  dualWalkCrossingEdges
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
    (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
    (sourceTwoTileSecondInterfaceAt realization hcubic hrotation htwoSided
      hunique offset).toInterface.localLayer.walk

/-- The primal crossing support of the source-aligned closed walk. -/
noncomputable def sourceTwoTileAlignedBoundaryCrossingEdgesAt
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
    (offset : Fin (blockLength - 4)) : Finset G.edgeSet :=
  dualWalkCrossingEdges
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
    (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
    (sourceTwoTileAlignedBoundaryWalkAt realization hcubic hrotation htwoSided
      hunique offset)

/-- The aligned boundary support is exactly the two transverse supports plus
the retained intercell-rail support.  In particular, the two lateral source
crossings are not erased by identifying the transverse interfaces. -/
theorem sourceTwoTileAlignedBoundaryCrossingEdgesAt_eq_layers_union_rails
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
    sourceTwoTileAlignedBoundaryCrossingEdgesAt realization hcubic hrotation
        htwoSided hunique offset =
      sourceTwoTileFirstLayerCrossingEdgesAt realization hcubic hrotation
          htwoSided hunique offset ∪
        sourceTwoTileSecondLayerCrossingEdgesAt realization hcubic hrotation
            htwoSided hunique offset ∪
          sourceTwoTileRailCrossingEdgesAt realization hcubic hrotation
            htwoSided hunique offset := by
  simp only [sourceTwoTileAlignedBoundaryCrossingEdgesAt,
    sourceTwoTileAlignedBoundaryWalkAt,
    sourceTwoTileFirstLayerCrossingEdgesAt,
    sourceTwoTileSecondLayerCrossingEdgesAt,
    sourceTwoTileRailCrossingEdgesAt,
    dualWalkCrossingEdges_append, dualWalkCrossingEdges_reverse]
  ext edge
  simp only [Finset.mem_union]
  tauto

/-- Even before simplicity is used, the provenance theorem gives the sharp
six-edge upper bound: two crossings from each transverse layer and exactly
two from the exterior rails. -/
theorem sourceTwoTileAlignedBoundaryCrossingEdgesAt_card_le_six
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
    (sourceTwoTileAlignedBoundaryCrossingEdgesAt realization hcubic hrotation
      htwoSided hunique offset).card ≤ 6 := by
  let first := sourceTwoTileFirstInterfaceAt realization hcubic hrotation
    htwoSided hunique offset
  let second := sourceTwoTileSecondInterfaceAt realization hcubic hrotation
    htwoSided hunique offset
  let firstEdges := sourceTwoTileFirstLayerCrossingEdgesAt realization hcubic
    hrotation htwoSided hunique offset
  let secondEdges := sourceTwoTileSecondLayerCrossingEdgesAt realization hcubic
    hrotation htwoSided hunique offset
  let railEdges := sourceTwoTileRailCrossingEdgesAt realization hcubic hrotation
    htwoSided hunique offset
  have hfirstCard : firstEdges.card = 2 := by
    dsimp [firstEdges, sourceTwoTileFirstLayerCrossingEdgesAt]
    rw [card_dualWalkCrossingEdges_eq_length_of_isPath
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))
      (orbitFace_incidence_le_two
        embedded.cellulation.rotation.toRotationSystem)
      hunique first.toInterface.localLayer.walk
      first.toInterface.localLayer.isPath,
      first.toInterface.localLayer_walk_length_eq_two]
  have hsecondCard : secondEdges.card = 2 := by
    dsimp [secondEdges, sourceTwoTileSecondLayerCrossingEdgesAt]
    rw [card_dualWalkCrossingEdges_eq_length_of_isPath
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))
      (orbitFace_incidence_le_two
        embedded.cellulation.rotation.toRotationSystem)
      hunique second.toInterface.localLayer.walk
      second.toInterface.localLayer.isPath,
      second.toInterface.localLayer_walk_length_eq_two]
  have hrailCard : railEdges.card = 2 := by
    exact sourceTwoTileRailCrossingEdgesAt_card_eq_two realization hcubic
      hrotation htwoSided hunique offset
  rw [sourceTwoTileAlignedBoundaryCrossingEdgesAt_eq_layers_union_rails]
  calc
    ((firstEdges ∪ secondEdges) ∪ railEdges).card ≤
        (firstEdges ∪ secondEdges).card + railEdges.card :=
      Finset.card_union_le _ _
    _ ≤ (firstEdges.card + secondEdges.card) + railEdges.card := by
      gcongr
      exact Finset.card_union_le _ _
    _ = 6 := by rw [hfirstCard, hsecondCard, hrailCard]

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
