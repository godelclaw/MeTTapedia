import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerPointwiseCrossings
import Mettapedia.GraphTheory.FourColor.GoertzelV24SelectedDualPathTransversalPair

/-!
# Pointwise selected crossings for a colouring-free literal Cell layer

The corrected source carrier constructs a `Formation.LocalLayerPair` from
annular-interior geometry.  This file packages its two literal two-step walks
as selected facial-dual transversals.  The selected primal edge at each step
is the pointwise edge supplied by the restricted interior-face uniqueness
receipt, so the result agrees with the historical lookup wherever the latter
is defined without importing its false global hypothesis.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24AnnularCrosscut
open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24DualPathPointwiseTransversal
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24OrientedHexSlab
open GoertzelV24SelectedDualPathTransversal

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance pointwiseSelectedLocalLayerEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Formation.LocalLayerPair

/-- The first literal two-step layer is a simple facial-dual path. -/
theorem firstWalk_isPath
    {data : AnnularBoundaryData G 5}
    {formation : Formation data} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : LocalLayerPair formation corridor leftInterior hnext) :
    layers.firstWalk.IsPath := by
  unfold firstWalk
  apply SimpleGraph.Walk.IsPath.cons
  · apply SimpleGraph.Walk.IsPath.cons
    · exact SimpleGraph.Walk.IsPath.nil
    · simpa using layers.center_adjacent_second.ne
  · simp [layers.first_adjacent_center.ne, layers.first_ne_second]

/-- The successor literal layer is a simple facial-dual path. -/
theorem secondWalk_isPath
    {data : AnnularBoundaryData G 5}
    {formation : Formation data} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : LocalLayerPair formation corridor leftInterior hnext) :
    layers.secondWalk.IsPath := by
  unfold secondWalk
  apply SimpleGraph.Walk.IsPath.cons
  · apply SimpleGraph.Walk.IsPath.cons
    · exact SimpleGraph.Walk.IsPath.nil
    · simpa using layers.nextCenter_adjacent_second.ne
  · simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons, not_or]
    exact ⟨by
      simpa [nextCorridorInterior] using layers.first_adjacent_nextCenter.ne,
      ⟨layers.first_ne_second, by simp⟩⟩

/-- The first literal walk as the generic simple-crosscut carrier. -/
noncomputable def firstLayer
    {data : AnnularBoundaryData G 5}
    {formation : Formation data} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : LocalLayerPair formation corridor leftInterior hnext) :
    SimpleDualCrosscut (orbitFaceBoundary formation.annular.RS)
      (Finset.univ : Finset (OrbitFace formation.annular.RS))
      layers.firstFace layers.secondFace where
  walk := layers.firstWalk
  isPath := layers.firstWalk_isPath

/-- The successor literal walk as the generic simple-crosscut carrier. -/
noncomputable def secondLayer
    {data : AnnularBoundaryData G 5}
    {formation : Formation data} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : LocalLayerPair formation corridor leftInterior hnext) :
    SimpleDualCrosscut (orbitFaceBoundary formation.annular.RS)
      (Finset.univ : Finset (OrbitFace formation.annular.RS))
      layers.firstFace layers.secondFace where
  walk := layers.secondWalk
  isPath := layers.secondWalk_isPath

/-- The two local rails meet only in their two named endpoint faces. -/
theorem localLayers_tail_disjoint
    {data : AnnularBoundaryData G 5}
    {formation : Formation data} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : LocalLayerPair formation corridor leftInterior hnext) :
    layers.firstWalk.support.tail.Disjoint
      layers.secondWalk.reverse.support.tail := by
  have hnext_ne_center :
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (nextCorridorInterior leftInterior hnext).center ≠
        corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          leftInterior.center :=
    layers.center_ne_nextCenter.symm
  have hnext_ne_second :
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (nextCorridorInterior leftInterior hnext).center ≠ layers.secondFace :=
    layers.nextCenter_adjacent_second.ne
  have hfirst_ne_center : layers.firstFace ≠
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        leftInterior.center := layers.first_adjacent_center.ne
  have hnext_ne_center' :
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          leftInterior.outgoing.right ≠
        corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          leftInterior.center := by
    simpa [nextCorridorInterior] using hnext_ne_center
  have hnext_ne_second' :
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          leftInterior.outgoing.right ≠ layers.secondFace := by
    simpa [nextCorridorInterior] using hnext_ne_second
  simp [firstWalk, secondWalk, hnext_ne_center', hnext_ne_second',
    hfirst_ne_center, layers.first_ne_second]

/-- The first rail with the exact pointwise-selected primal crossing at every
step. -/
noncomputable def pointwiseSelectedFirstLayer
    {data : AnnularBoundaryData G 5}
    {formation : Formation data} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (layers : LocalLayerPair formation corridor leftInterior hnext) :
    SelectedDualPathTransversal (orbitFaceBoundary formation.annular.RS)
      (Finset.univ : Finset (OrbitFace formation.annular.RS))
      layers.firstFace layers.secondFace where
  crosscut := layers.firstLayer
  crossingEdge := layers.firstCrossingEdge hinterior
  crossing_mem_shared := by
    intro step
    exact pointwiseDualWalkCrossingEdge_mem_shared
      (orbitFaceBoundary formation.annular.RS)
      (Finset.univ : Finset (OrbitFace formation.annular.RS))
      layers.firstWalk (layers.firstWalkStepUnique hinterior) step

/-- The successor rail with the exact pointwise-selected primal crossing at
every step. -/
noncomputable def pointwiseSelectedSecondLayer
    {data : AnnularBoundaryData G 5}
    {formation : Formation data} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (layers : LocalLayerPair formation corridor leftInterior hnext) :
    SelectedDualPathTransversal (orbitFaceBoundary formation.annular.RS)
      (Finset.univ : Finset (OrbitFace formation.annular.RS))
      layers.firstFace layers.secondFace where
  crosscut := layers.secondLayer
  crossingEdge := layers.secondCrossingEdge hinterior
  crossing_mem_shared := by
    intro step
    exact pointwiseDualWalkCrossingEdge_mem_shared
      (orbitFaceBoundary formation.annular.RS)
      (Finset.univ : Finset (OrbitFace formation.annular.RS))
      layers.secondWalk (layers.secondWalkStepUnique hinterior) step

/-- The two exact pointwise crossing supports are disjoint.  A reused edge
would be incident with three distinct annular faces, contradicting the local
two-face incidence law. -/
theorem pointwiseSelectedLayers_crossing_disjoint
    {data : AnnularBoundaryData G 5}
    {formation : Formation data} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (layers : LocalLayerPair formation corridor leftInterior hnext) :
    Disjoint (layers.pointwiseSelectedFirstLayer hinterior).crossingEdges
      (layers.pointwiseSelectedSecondLayer hinterior).crossingEdges := by
  classical
  let first := layers.pointwiseSelectedFirstLayer hinterior
  let second := layers.pointwiseSelectedSecondLayer hinterior
  let center :=
    corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
      leftInterior.center
  let nextCenter :=
    corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
      leftInterior.outgoing.right
  have hall := orbitFace_incidence_le_two formation.annular.RS
  refine Finset.disjoint_left.2 ?_
  intro edge hfirst hsecond
  rcases (SelectedDualPathTransversal.mem_crossingEdges_iff first edge).1 hfirst with
    ⟨firstStep, hfirstEdge⟩
  rcases (SelectedDualPathTransversal.mem_crossingEdges_iff second edge).1 hsecond with
    ⟨secondStep, hsecondEdge⟩
  have hfirstLt : firstStep.val < 2 := by
    have := firstStep.isLt
    simp only [first, pointwiseSelectedFirstLayer, firstLayer, firstWalk,
      SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at this
    omega
  have hsecondLt : secondStep.val < 2 := by
    have := secondStep.isLt
    simp only [second, pointwiseSelectedSecondLayer, secondLayer, secondWalk,
      SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at this
    omega
  have hnextMem : edge ∈ orbitFaceBoundary formation.annular.RS nextCenter.1 := by
    have hzeroOrOne : secondStep.val = 0 ∨ secondStep.val = 1 := by omega
    rcases hzeroOrOne with hzero | hone
    · have hmem := second.crossingEdge_mem_rightFace secondStep
      rw [hsecondEdge] at hmem
      change edge ∈ orbitFaceBoundary formation.annular.RS
        (layers.secondWalk.getVert (secondStep.val + 1)).1 at hmem
      simpa [secondWalk, nextCenter, hzero] using hmem
    · have hmem := second.crossingEdge_mem_leftFace secondStep
      rw [hsecondEdge] at hmem
      change edge ∈ orbitFaceBoundary formation.annular.RS
        (layers.secondWalk.getVert secondStep.val).1 at hmem
      simpa [secondWalk, nextCenter, hone] using hmem
  have hzeroOrOne : firstStep.val = 0 ∨ firstStep.val = 1 := by omega
  rcases hzeroOrOne with hzero | hone
  · have hleft := first.crossingEdge_mem_leftFace firstStep
    have hright := first.crossingEdge_mem_rightFace firstStep
    rw [hfirstEdge] at hleft hright
    change edge ∈ orbitFaceBoundary formation.annular.RS
      (layers.firstWalk.getVert firstStep.val).1 at hleft
    change edge ∈ orbitFaceBoundary formation.annular.RS
      (layers.firstWalk.getVert (firstStep.val + 1)).1 at hright
    have hleft' : edge ∈ orbitFaceBoundary formation.annular.RS
        layers.firstFace.1 := by
      simpa [first, pointwiseSelectedFirstLayer, firstLayer, firstWalk, hzero]
        using hleft
    have hright' : edge ∈ orbitFaceBoundary formation.annular.RS center.1 := by
      simpa [first, pointwiseSelectedFirstLayer, firstLayer, firstWalk,
        center, hzero] using hright
    have hcases :=
      eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
        (orbitFaceBoundary formation.annular.RS)
        (Finset.univ : Finset (OrbitFace formation.annular.RS)) hall
        layers.firstFace.2 center.2 nextCenter.2
        (by
          intro hfaces
          exact layers.first_adjacent_center.ne (Subtype.ext hfaces))
        hleft' hright' hnextMem
    rcases hcases with hcase | hcase
    · exact layers.first_adjacent_nextCenter.ne (by
        apply Subtype.ext
        simpa [nextCenter, nextCorridorInterior] using hcase.symm)
    · exact layers.center_ne_nextCenter (by
        apply Subtype.ext
        simpa [center, nextCenter, nextCorridorInterior] using hcase.symm)
  · have hleft := first.crossingEdge_mem_leftFace firstStep
    have hright := first.crossingEdge_mem_rightFace firstStep
    rw [hfirstEdge] at hleft hright
    change edge ∈ orbitFaceBoundary formation.annular.RS
      (layers.firstWalk.getVert firstStep.val).1 at hleft
    change edge ∈ orbitFaceBoundary formation.annular.RS
      (layers.firstWalk.getVert (firstStep.val + 1)).1 at hright
    have hleft' : edge ∈ orbitFaceBoundary formation.annular.RS center.1 := by
      simpa [first, pointwiseSelectedFirstLayer, firstLayer, firstWalk,
        center, hone] using hleft
    have hright' : edge ∈ orbitFaceBoundary formation.annular.RS
        layers.secondFace.1 := by
      simpa [first, pointwiseSelectedFirstLayer, firstLayer, firstWalk, hone]
        using hright
    have hcases :=
      eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
        (orbitFaceBoundary formation.annular.RS)
        (Finset.univ : Finset (OrbitFace formation.annular.RS)) hall
        center.2 layers.secondFace.2 nextCenter.2
        (by
          intro hfaces
          exact layers.center_adjacent_second.ne (Subtype.ext hfaces))
        hleft' hright' hnextMem
    rcases hcases with hcase | hcase
    · exact layers.center_ne_nextCenter (by
        apply Subtype.ext
        simpa [center, nextCenter, nextCorridorInterior] using hcase.symm)
    · exact layers.nextCenter_adjacent_second.ne (by
        apply Subtype.ext
        simpa [nextCenter, nextCorridorInterior] using hcase)

/-- The corrected literal Cell layer inhabits the selected paired-transversal
carrier without a colouring or global face-intersection uniqueness. -/
noncomputable def pointwiseSelectedLocalLayerPair
    {data : AnnularBoundaryData G 5}
    {formation : Formation data} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (layers : LocalLayerPair formation corridor leftInterior hnext) :
    SeparatedAlignedSelectedDualTransversals
      (orbitFaceBoundary formation.annular.RS)
      (Finset.univ : Finset (OrbitFace formation.annular.RS))
      layers.firstFace layers.secondFace where
  left := layers.pointwiseSelectedFirstLayer hinterior
  right := layers.pointwiseSelectedSecondLayer hinterior
  length_eq := by
    norm_num [pointwiseSelectedFirstLayer, pointwiseSelectedSecondLayer,
      firstLayer, secondLayer, firstWalk, secondWalk]
  crossing_disjoint := layers.pointwiseSelectedLayers_crossing_disjoint hinterior
  transverse_disjoint := layers.localLayers_tail_disjoint
  nondegenerate := Or.inl (by
    norm_num [pointwiseSelectedFirstLayer, firstLayer, firstWalk])

end Formation.LocalLayerPair

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
