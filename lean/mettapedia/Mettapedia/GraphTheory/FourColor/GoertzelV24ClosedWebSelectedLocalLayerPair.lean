import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalLayerFormation
import Mettapedia.GraphTheory.FourColor.GoertzelV24SelectedDualPathTransversalPair

/-!
# Selected crossing data for a literal local Cell-3 layer pair

A successful source-local `LocalLayerPair` already consists of two simple
length-two facial-dual paths with the same endpoints and distinct corridor
centres.  This file equips both paths with actual selected primal crossings
and proves that their crossing supports are disjoint using only the local
at-most-two facial-incidence law.

No global `PairwiseUniqueSharedInteriorEdges` premise is introduced.  The
result remains one local Cell-3 layer tile, not the source's long, end-capped
transversal construction.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24AnnularCrosscut
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexFaceRungType
open GoertzelV24SelectedDualPathTransversal

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq
  GoertzelV24SeamFaceArcPartition.hitPointFintype

local instance selectedLocalLayerPairEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance.LocalLayerPair

/-- The first local layer with one actual primal edge selected at each dual
step. -/
noncomputable def selectedFirstLayer
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : Instance.LocalLayerPair web corridor leftInterior hnext) :
    SelectedDualPathTransversal (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      layers.firstFace layers.secondFace :=
  SelectedDualPathTransversal.ofCrosscut layers.firstLayer

/-- The successor local layer with one actual primal edge selected at each
dual step. -/
noncomputable def selectedSecondLayer
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : Instance.LocalLayerPair web corridor leftInterior hnext) :
    SelectedDualPathTransversal (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      layers.firstFace layers.secondFace :=
  SelectedDualPathTransversal.ofCrosscut layers.secondLayer

/-- The two locally selected transverse interfaces cannot reuse a primal
edge.  Any reused edge would be incident with three distinct faces: the next
corridor centre and the two faces on one step of the first interface. -/
theorem selectedLayers_crossing_disjoint
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : Instance.LocalLayerPair web corridor leftInterior hnext) :
    Disjoint layers.selectedFirstLayer.crossingEdges
      layers.selectedSecondLayer.crossingEdges := by
  classical
  let first := layers.selectedFirstLayer
  let second := layers.selectedSecondLayer
  let center :=
    corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
      leftInterior.center
  let nextCenter :=
    corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
      leftInterior.outgoing.right
  have hall := orbitFace_incidence_le_two web.annular.RS
  refine Finset.disjoint_left.2 ?_
  intro edge hfirst hsecond
  rcases (SelectedDualPathTransversal.mem_crossingEdges_iff first edge).1 hfirst with
    ⟨firstStep, hfirstEdge⟩
  rcases (SelectedDualPathTransversal.mem_crossingEdges_iff second edge).1 hsecond with
    ⟨secondStep, hsecondEdge⟩
  have hfirstLt : firstStep.val < 2 := by
    have := firstStep.isLt
    simp only [first, selectedFirstLayer, SelectedDualPathTransversal.ofCrosscut,
      Instance.LocalLayerPair.firstLayer,
      Instance.LocalLayerPair.firstWalk, SimpleGraph.Walk.length_cons,
      SimpleGraph.Walk.length_nil] at this
    omega
  have hsecondLt : secondStep.val < 2 := by
    have := secondStep.isLt
    simp only [second, selectedSecondLayer, SelectedDualPathTransversal.ofCrosscut,
      Instance.LocalLayerPair.secondLayer,
      Instance.LocalLayerPair.secondWalk, SimpleGraph.Walk.length_cons,
      SimpleGraph.Walk.length_nil] at this
    omega
  have hnextMem : edge ∈ orbitFaceBoundary web.annular.RS nextCenter.1 := by
    have hzeroOrOne : secondStep.val = 0 ∨ secondStep.val = 1 := by omega
    rcases hzeroOrOne with hzero | hone
    · have hmem := second.crossingEdge_mem_rightFace secondStep
      rw [hsecondEdge] at hmem
      change edge ∈ orbitFaceBoundary web.annular.RS
        (layers.secondWalk.getVert (secondStep.val + 1)).1 at hmem
      simpa [Instance.LocalLayerPair.secondWalk, nextCenter, hzero] using hmem
    · have hmem := second.crossingEdge_mem_leftFace secondStep
      rw [hsecondEdge] at hmem
      change edge ∈ orbitFaceBoundary web.annular.RS
        (layers.secondWalk.getVert secondStep.val).1 at hmem
      simpa [Instance.LocalLayerPair.secondWalk, nextCenter, hone] using hmem
  have hzeroOrOne : firstStep.val = 0 ∨ firstStep.val = 1 := by omega
  rcases hzeroOrOne with hzero | hone
  · have hleft := first.crossingEdge_mem_leftFace firstStep
    have hright := first.crossingEdge_mem_rightFace firstStep
    rw [hfirstEdge] at hleft hright
    change edge ∈ orbitFaceBoundary web.annular.RS
      (layers.firstWalk.getVert firstStep.val).1 at hleft
    change edge ∈ orbitFaceBoundary web.annular.RS
      (layers.firstWalk.getVert (firstStep.val + 1)).1 at hright
    have hleft' : edge ∈ orbitFaceBoundary web.annular.RS layers.firstFace.1 := by
      simpa [first, selectedFirstLayer,
        Instance.LocalLayerPair.firstLayer,
        Instance.LocalLayerPair.firstWalk, hzero] using hleft
    have hright' : edge ∈ orbitFaceBoundary web.annular.RS center.1 := by
      simpa [first, selectedFirstLayer,
        Instance.LocalLayerPair.firstLayer,
        Instance.LocalLayerPair.firstWalk, center, hzero] using hright
    have hcases :=
      eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
        (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS)) hall
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
    change edge ∈ orbitFaceBoundary web.annular.RS
      (layers.firstWalk.getVert firstStep.val).1 at hleft
    change edge ∈ orbitFaceBoundary web.annular.RS
      (layers.firstWalk.getVert (firstStep.val + 1)).1 at hright
    have hleft' : edge ∈ orbitFaceBoundary web.annular.RS center.1 := by
      simpa [first, selectedFirstLayer,
        Instance.LocalLayerPair.firstLayer,
        Instance.LocalLayerPair.firstWalk, center, hone] using hleft
    have hright' : edge ∈ orbitFaceBoundary web.annular.RS layers.secondFace.1 := by
      simpa [first, selectedFirstLayer,
        Instance.LocalLayerPair.firstLayer,
        Instance.LocalLayerPair.firstWalk, hone] using hright
    have hcases :=
      eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
        (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS)) hall
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

/-- A successful literal local layer pair inhabits the selected paired
transversal carrier without any global unique-shared-edge hypothesis. -/
noncomputable def selectedLocalLayerPair
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : Instance.LocalLayerPair web corridor leftInterior hnext) :
    SeparatedAlignedSelectedDualTransversals
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      layers.firstFace layers.secondFace where
  left := layers.selectedFirstLayer
  right := layers.selectedSecondLayer
  length_eq := by
    norm_num [selectedFirstLayer, selectedSecondLayer,
      SelectedDualPathTransversal.ofCrosscut,
      Instance.LocalLayerPair.firstLayer,
      Instance.LocalLayerPair.secondLayer,
      Instance.LocalLayerPair.firstWalk,
      Instance.LocalLayerPair.secondWalk]
  crossing_disjoint := layers.selectedLayers_crossing_disjoint
  transverse_disjoint := layers.localLayers_tail_disjoint
  nondegenerate := Or.inl (by
    norm_num [selectedFirstLayer, SelectedDualPathTransversal.ofCrosscut,
      Instance.LocalLayerPair.firstLayer,
      Instance.LocalLayerPair.firstWalk])

/-- **L1 selected local alternative.**  A literal selected rung placement
either supplies a paired selected Cell-3 transversal tile, or retains the
exact finite collision produced by the source-local formation theorem.

This is the source-facing local dichotomy in the repaired representation.  It
does not eliminate the collision or assemble/end-cap a long transversal. -/
theorem exists_selectedLocalLayerPair_or_collision
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (hnext : interior.center.val + 2 < blockLength)
    (placement : SelectedInternalHexRungPlacement corridor rungs interior) :
    (∃ firstFace secondFace,
      Nonempty (SeparatedAlignedSelectedDualTransversals
        (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))
        firstFace secondFace)) ∨
      Instance.SelectedLocalLayerFormation.SelectedLocalLayerCollision
        hnext placement := by
  rcases Instance.SelectedLocalLayerFormation.exists_selectedLocalLayerPair_or_collision
      hnext placement with
    success | collision
  · rcases success with ⟨layers⟩
    exact Or.inl ⟨layers.firstFace, layers.secondFace,
      ⟨layers.selectedLocalLayerPair⟩⟩
  · exact Or.inr collision

end Instance.LocalLayerPair

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
