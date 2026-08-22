import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFactorization
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerFiniteTrackedLetter
import Mettapedia.GraphTheory.FourColor.GoertzelV24TerminalProfileVertexSideSeam

/-!
# Portal completeness for one actual opened-source Cell

The exact cumulative-prefix update is the union of a terminal-aware old
prefix and one literal complementary Cell.  Its residual seam can interact
with the Cell only along the Cell's four-edge vertex cut.  The two incoming
crossings already belong to the old prefix, so a genuinely residual seam
adjacency must touch one of the two outgoing crossings.

This proves that every non-isolated tracked seam component, and every
non-isolated occurrence-sensitive facial seam component, reaches a named
outgoing portal.  The statement concerns the seam actually consumed by the
one-Cell factorization; it does not claim that every historical boundary of
the accumulated prefix has only two edges.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24AnnularCrosscut
open GoertzelV24AnnularCrosscut.SeparatedAlignedSimpleDualCrosscuts
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24RotationFaceFragments
open GoertzelV24RotationVertexCutProfile
open GoertzelV24TerminalProfileSeamResidual
open GoertzelV24TerminalProfileVertexSideSeam
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebLocalLayerSerialCellPortalCompletenessEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- Consecutive face occurrences with distinct underlying edges are adjacent
in the edge-adjacency graph.  Unlike the usual cubic version, this local
form also applies to an opened carrier: the only non-cubic face steps are
degree-one bounces, and those repeat the same underlying edge. -/
private theorem edgeAdjacencyGraph_adj_of_faceCyclePositionGraph_adj_of_ne
    {E : Type*} [Fintype E] [DecidableEq E]
    (RS : RotationSystem V E) (root : RS.D)
    {left right : Fin (RS.faceOrbit root).card}
    (hadj : (faceCyclePositionGraph RS root).Adj left right)
    (hne : faceCycleEdge RS root left ≠ faceCycleEdge RS root right) :
    RS.edgeAdjacencyGraph.Adj
      (faceCycleEdge RS root left) (faceCycleEdge RS root right) := by
  rcases hadj.2 with hforward | hbackward
  · apply RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges hne
    · apply (RS.mem_incidentEdges_iff).2
      exact ⟨RS.alpha (faceCycleDart RS root left),
        RS.edge_alpha (faceCycleDart RS root left),
        (RS.vert_phi_eq_vert_alpha (faceCycleDart RS root left)).symm⟩
    · apply (RS.mem_incidentEdges_iff).2
      exact ⟨faceCycleDart RS root right, rfl, by simp [hforward]⟩
  · apply SimpleGraph.Adj.symm
    apply RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges hne.symm
    · apply (RS.mem_incidentEdges_iff).2
      exact ⟨RS.alpha (faceCycleDart RS root right),
        RS.edge_alpha (faceCycleDart RS root right),
        (RS.vert_phi_eq_vert_alpha (faceCycleDart RS root right)).symm⟩
    · apply (RS.mem_incidentEdges_iff).2
      exact ⟨faceCycleDart RS root left, rfl, by simp [hbackward]⟩

/-- Every edge crossing the literal Cell's vertex cut is one of its two
incoming or two outgoing source crossings. -/
theorem sourceLocalLayerCellCrossingAt_eq_left_or_right
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) {edge : G.edgeSet}
    (hedge : edge ∈ vertexSetCrossingEdges web.annular.RS
      (sourceLocalLayerCellVertexSide corridor hunique
        (sourceLocalLayerInteriorAt offset)
        (sourceLocalLayerInteriorAt_hasNext offset))) :
    (∃ step : Fin 2,
      edge = sourceLocalLayerLeftCrossingAt corridor hunique offset step) ∨
      ∃ step : Fin 2,
        edge = sourceLocalLayerRightCrossingAt corridor hunique offset step := by
  let layers := sourceLocalLayerPairAt corridor hunique offset
  let pair := layers.separatedLocalLayerPair hunique
  let boundary := sourceLocalLayerBoundaryAt corridor hunique offset
  have hside := sourceLocalLayerCellVertexSide_eq_retained_compl
    corridor hunique (sourceLocalLayerInteriorAt offset)
      (sourceLocalLayerInteriorAt_hasNext offset)
  have hedge' : edge ∈ vertexSetCrossingEdges web.annular.RS
      (pair.componentSide boundary.component)ᶜ := by
    rw [hside] at hedge
    simpa [sourceLocalLayerRetainedVertexSide,
      sourceLocalLayerPairAt, sourceLocalLayerBoundaryAt, layers, pair,
      boundary] using hedge
  let crossing : VertexSetCrossingEdge web.annular.RS
      (pair.componentSide boundary.component)ᶜ := ⟨edge, hedge'⟩
  let sourceIndex :=
    (pair.sourceCrosscutComplementPort
      web.annular.cellulation.rotation boundary).symm crossing
  have hsource :
      pair.sourceCrosscutComplementPort web.annular.cellulation.rotation
          boundary sourceIndex = crossing :=
    (pair.sourceCrosscutComplementPort web.annular.cellulation.rotation
      boundary).apply_symm_apply crossing
  rcases sourceIndex with leftStep | rightStep
  · apply Or.inl
    have hlength : layers.firstLayer.walk.length = 2 := by
      simp [layers, sourceLocalLayerPairAt, LocalLayerPair.firstLayer,
        LocalLayerPair.firstWalk]
    let step : Fin 2 :=
      Fin.cast hlength leftStep
    refine ⟨step, ?_⟩
    have hedgeEq := congrArg Subtype.val hsource
    rw [pair.sourceCrosscutComplementPort_left
      web.annular.cellulation.rotation boundary] at hedgeEq
    simpa [sourceLocalLayerLeftCrossingAt, sourceLocalLayerPairAt, layers,
      pair, boundary, step, LocalLayerPair.separatedLocalLayerPair] using
        hedgeEq.symm
  · apply Or.inr
    have hlength : layers.secondLayer.walk.length = 2 := by
      simp [layers, sourceLocalLayerPairAt, LocalLayerPair.secondLayer,
        LocalLayerPair.secondWalk]
    let step : Fin 2 :=
      Fin.cast hlength rightStep
    refine ⟨step, ?_⟩
    have hedgeEq := congrArg Subtype.val hsource
    rw [pair.sourceCrosscutComplementPort_right
      web.annular.cellulation.rotation boundary] at hedgeEq
    simpa [sourceLocalLayerRightCrossingAt, sourceLocalLayerPairAt, layers,
      pair, boundary, step, LocalLayerPair.separatedLocalLayerPair] using
        hedgeEq.symm

/-- Every tracked residual adjacency between the actual cumulative prefix and
one literal Cell touches one of the two outgoing source crossings. -/
theorem sourceLocalLayerSerialTerminalTrackedSeamAt_adj_touches_rightCrossing
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (color : G.edgeSet → Color) (first second : Color) {x y : G.edgeSet}
    (hadj : (sourceLocalLayerSerialTerminalTrackedSeamAt corridor hunique
      offset color first second).Adj x y) :
    ∃ step : Fin 2,
      x = sourceLocalLayerRightCrossingAt corridor hunique offset step ∨
        y = sourceLocalLayerRightCrossingAt corridor hunique offset step := by
  let inside := sourceLocalLayerCellVertexSide corridor hunique
    (sourceLocalLayerInteriorAt offset)
    (sourceLocalLayerInteriorAt_hasNext offset)
  have hcell : sourceLocalLayerCellRegionAt corridor hunique offset =
      vertexSetRegionEdges web.annular.RS inside := by
    have hside := sourceLocalLayerCellVertexSide_eq_retained_compl
      corridor hunique (sourceLocalLayerInteriorAt offset)
        (sourceLocalLayerInteriorAt_hasNext offset)
    exact congrArg (vertexSetRegionEdges web.annular.RS) hside.symm
  have hlocalized := regionalTrackedSeamGraph_adj_localizes_to_vertexCut
    web.annular.RS
    (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
    inside color first second (by
      simpa [sourceLocalLayerSerialTerminalTrackedSeamAt, hcell] using hadj)
  rcases hlocalized with
    ⟨_hxOld, _hxNotCell, _hyCell, hyNotOld, hyCut⟩ |
      ⟨_hxCell, hxNotOld, hxCut, _hyOld, _hyNotCell⟩
  · rcases sourceLocalLayerCellCrossingAt_eq_left_or_right corridor hunique
      offset hyCut with ⟨step, hyLeft⟩ | ⟨step, hyRight⟩
    · have hyMem : y ∈ sourceLocalLayerSerialTerminalInputRegionAt
          corridor hunique offset := by
        rw [hyLeft]
        exact Finset.mem_union_left _
          (sourceLocalLayerSerialInputRegionAt_leftCrossing corridor hunique
            offset step)
      exact (hyNotOld hyMem).elim
    · exact ⟨step, Or.inr hyRight⟩
  · rcases sourceLocalLayerCellCrossingAt_eq_left_or_right corridor hunique
      offset hxCut with ⟨step, hxLeft⟩ | ⟨step, hxRight⟩
    · have hxMem : x ∈ sourceLocalLayerSerialTerminalInputRegionAt
          corridor hunique offset := by
        rw [hxLeft]
        exact Finset.mem_union_left _
          (sourceLocalLayerSerialInputRegionAt_leftCrossing corridor hunique
            offset step)
      exact (hxNotOld hxMem).elim
    · exact ⟨step, Or.inl hxRight⟩

/-- Every non-isolated tracked residual component reaches a named outgoing
source crossing. -/
theorem sourceLocalLayerSerialTerminalTrackedSeamAt_support_reaches_rightCrossing
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (color : G.edgeSet → Color) (first second : Color) (edge : G.edgeSet)
    (hedge : edge ∈ (sourceLocalLayerSerialTerminalTrackedSeamAt corridor
      hunique offset color first second).support) :
    ∃ step : Fin 2,
      (sourceLocalLayerSerialTerminalTrackedSeamAt corridor hunique offset color
        first second).Reachable edge
          (sourceLocalLayerRightCrossingAt corridor hunique offset step) := by
  let seam := sourceLocalLayerSerialTerminalTrackedSeamAt corridor hunique
    offset color first second
  rcases (SimpleGraph.mem_support seam).1 hedge with ⟨neighbor, hadj⟩
  rcases sourceLocalLayerSerialTerminalTrackedSeamAt_adj_touches_rightCrossing
      corridor hunique offset color first second hadj with
    ⟨step, hedgeRight | hneighborRight⟩
  · refine ⟨step, ?_⟩
    simp [hedgeRight]
  · refine ⟨step, ?_⟩
    simpa [seam, hneighborRight] using hadj.reachable

/-- Every occurrence-sensitive facial residual adjacency uses the same
outgoing portal geometry as tracked connectivity. -/
theorem sourceLocalLayerSerialTerminalFaceSeamAt_adj_touches_rightCrossing
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) (root : web.annular.RS.D)
    {x y : Fin (web.annular.RS.faceOrbit root).card}
    (hadj : (sourceLocalLayerSerialTerminalFaceSeamAt corridor hunique offset
      root).Adj x y) :
    ∃ step : Fin 2,
      faceCycleEdge web.annular.RS root x =
          sourceLocalLayerRightCrossingAt corridor hunique offset step ∨
        faceCycleEdge web.annular.RS root y =
          sourceLocalLayerRightCrossingAt corridor hunique offset step := by
  let inside := sourceLocalLayerCellVertexSide corridor hunique
    (sourceLocalLayerInteriorAt offset)
    (sourceLocalLayerInteriorAt_hasNext offset)
  have hcell : sourceLocalLayerCellRegionAt corridor hunique offset =
      vertexSetRegionEdges web.annular.RS inside := by
    have hside := sourceLocalLayerCellVertexSide_eq_retained_compl
      corridor hunique (sourceLocalLayerInteriorAt offset)
        (sourceLocalLayerInteriorAt_hasNext offset)
    exact congrArg (vertexSetRegionEdges web.annular.RS) hside.symm
  have hseam : (faceRegionalSeamGraph web.annular.RS root
      (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
      (vertexSetRegionEdges web.annular.RS inside)).Adj x y := by
    simpa [sourceLocalLayerSerialTerminalFaceSeamAt, hcell] using hadj
  rcases (faceRegionalSeamGraph_adj_iff web.annular.RS root
      (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
      (vertexSetRegionEdges web.annular.RS inside) x y).1 hseam with
    ⟨hface, hforward | hbackward⟩
  · have hne : faceCycleEdge web.annular.RS root x ≠
        faceCycleEdge web.annular.RS root y := by
      intro heq
      apply hforward.2.1
      rw [heq]
      exact hforward.2.2.1
    have hedgeAdj :=
      edgeAdjacencyGraph_adj_of_faceCyclePositionGraph_adj_of_ne
        web.annular.RS root hface hne
    have hyCut := mem_vertexSetCrossingEdges_of_adjacent_not_mem_region
      web.annular.RS inside hedgeAdj hforward.2.1 hforward.2.2.1
    have hyNotOld := hforward.2.2.2
    rcases sourceLocalLayerCellCrossingAt_eq_left_or_right corridor hunique
      offset hyCut with ⟨step, hyLeft⟩ | ⟨step, hyRight⟩
    · have hyMem : faceCycleEdge web.annular.RS root y ∈
          sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset := by
        rw [hyLeft]
        exact Finset.mem_union_left _
          (sourceLocalLayerSerialInputRegionAt_leftCrossing corridor hunique
            offset step)
      exact (hyNotOld hyMem).elim
    · exact ⟨step, Or.inr hyRight⟩
  · have hne : faceCycleEdge web.annular.RS root x ≠
        faceCycleEdge web.annular.RS root y := by
      intro heq
      apply hbackward.2.1
      rw [heq]
      exact hbackward.2.2.1
    have hedgeAdj :=
      edgeAdjacencyGraph_adj_of_faceCyclePositionGraph_adj_of_ne
        web.annular.RS root hface hne
    have hxCut := mem_vertexSetCrossingEdges_of_adjacent_not_mem_region
      web.annular.RS inside hedgeAdj.symm hbackward.2.2.2 hbackward.1
    have hxNotOld := hbackward.2.1
    rcases sourceLocalLayerCellCrossingAt_eq_left_or_right corridor hunique
      offset hxCut with ⟨step, hxLeft⟩ | ⟨step, hxRight⟩
    · have hxMem : faceCycleEdge web.annular.RS root x ∈
          sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset := by
        rw [hxLeft]
        exact Finset.mem_union_left _
          (sourceLocalLayerSerialInputRegionAt_leftCrossing corridor hunique
            offset step)
      exact (hxNotOld hxMem).elim
    · exact ⟨step, Or.inl hxRight⟩

/-- Every non-isolated occurrence of the facial residual seam reaches an
occurrence of a named outgoing source crossing. -/
theorem sourceLocalLayerSerialTerminalFaceSeamAt_support_reaches_rightCrossing
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) (root : web.annular.RS.D)
    (position : Fin (web.annular.RS.faceOrbit root).card)
    (hposition : position ∈
      (sourceLocalLayerSerialTerminalFaceSeamAt corridor hunique offset
        root).support) :
    ∃ (step : Fin 2)
        (outputPosition : Fin (web.annular.RS.faceOrbit root).card),
      faceCycleEdge web.annular.RS root outputPosition =
          sourceLocalLayerRightCrossingAt corridor hunique offset step ∧
      (sourceLocalLayerSerialTerminalFaceSeamAt corridor hunique offset root
        ).Reachable position outputPosition := by
  let seam := sourceLocalLayerSerialTerminalFaceSeamAt corridor hunique offset
    root
  rcases (SimpleGraph.mem_support seam).1 hposition with ⟨neighbor, hadj⟩
  rcases sourceLocalLayerSerialTerminalFaceSeamAt_adj_touches_rightCrossing
      corridor hunique offset root hadj with
    ⟨step, hpositionRight | hneighborRight⟩
  · exact ⟨step, position, hpositionRight, SimpleGraph.Reachable.rfl⟩
  · exact ⟨step, neighbor, hneighborRight, hadj.reachable⟩

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
