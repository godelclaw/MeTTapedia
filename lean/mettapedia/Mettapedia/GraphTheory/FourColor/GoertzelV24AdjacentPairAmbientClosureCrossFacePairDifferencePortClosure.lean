import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferencePortPath
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCrossChannelAmbientClosurePair

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace GoertzelV24AdjacentPairBoundary.AdjacentPairData

/-- Index the two ports incident with the first deleted vertex. -/
def firstSidePort (index : Fin 2) : Fin 4 :=
  ⟨index.val, by omega⟩

/-- Index the two ports incident with the second deleted vertex. -/
def secondSidePort (index : Fin 2) : Fin 4 :=
  ⟨index.val + 2, by omega⟩

@[simp] theorem firstSidePort_zero : firstSidePort 0 = 0 := by
  apply Fin.ext
  rfl

@[simp] theorem firstSidePort_one : firstSidePort 1 = 1 := by
  apply Fin.ext
  rfl

@[simp] theorem secondSidePort_zero : secondSidePort 0 = 2 := by
  apply Fin.ext
  rfl

@[simp] theorem secondSidePort_one : secondSidePort 1 = 3 := by
  apply Fin.ext
  rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem firstSidePort_ne_secondSidePort (first second : Fin 2) :
    firstSidePort first ≠ secondSidePort second := by
  fin_cases first <;> fin_cases second <;> decide

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem secondSidePort_ne_firstSidePort (second first : Fin 2) :
    secondSidePort second ≠ firstSidePort first :=
  (firstSidePort_ne_secondSidePort first second).symm

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem first_adj_firstSidePort
    (data : AdjacentPairData G) (index : Fin 2) :
    G.Adj data.firstVertex (data.portVertex (firstSidePort index)) := by
  fin_cases index
  · simpa using data.first_adj_port_zero
  · simpa using data.first_adj_port_one

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem second_adj_secondSidePort
    (data : AdjacentPairData G) (index : Fin 2) :
    G.Adj data.secondVertex (data.portVertex (secondSidePort index)) := by
  fin_cases index
  · simpa using data.second_adj_port_two
  · simpa using data.second_adj_port_three

/-- The three-edge return through the restored pair for any of the four
cross-side port channels. -/
def crossSidePortCentralReturn
    (data : AdjacentPairData G) (first second : Fin 2) :
    G.Walk (data.portVertex (secondSidePort second))
      (data.portVertex (firstSidePort first)) :=
  SimpleGraph.Walk.cons (data.second_adj_secondSidePort second).symm
    (SimpleGraph.Walk.cons data.centralAdjacent.symm
      (SimpleGraph.Walk.cons (data.first_adj_firstSidePort first)
        SimpleGraph.Walk.nil))

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem crossSidePortCentralReturn_length
    (data : AdjacentPairData G) (first second : Fin 2) :
    (data.crossSidePortCentralReturn first second).length = 3 := by
  simp [crossSidePortCentralReturn]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem crossSidePortCentralReturn_edges
    (data : AdjacentPairData G) (first second : Fin 2) :
    (data.crossSidePortCentralReturn first second).edges =
      [boundaryEdgeValue data (secondSidePort second),
        centralEdgeValue data,
        boundaryEdgeValue data (firstSidePort first)] := by
  fin_cases first <;> fin_cases second <;>
    simp [crossSidePortCentralReturn, boundaryEdgeValue,
      GoertzelV24AdjacentPairInsertion.AdjacentPairData.centralEdgeValue,
      Sym2.eq_swap]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem crossSidePortCentralReturn_isPath
    (data : AdjacentPairData G) (first second : Fin 2) :
    (data.crossSidePortCentralReturn first second).IsPath := by
  rw [crossSidePortCentralReturn, SimpleGraph.Walk.cons_isPath_iff]
  constructor
  · rw [SimpleGraph.Walk.cons_isPath_iff]
    constructor
    · rw [SimpleGraph.Walk.cons_isPath_iff]
      exact ⟨SimpleGraph.Walk.IsPath.nil, by
        simpa using (data.portNeFirst (firstSidePort first)).symm⟩
    · simp only [SimpleGraph.Walk.support_cons,
        SimpleGraph.Walk.support_nil, List.mem_cons,
        List.not_mem_nil, or_false, not_or]
      exact ⟨data.centralAdjacent.ne.symm,
        (data.portNeSecond (firstSidePort first)).symm⟩
  · simp only [SimpleGraph.Walk.support_cons,
      SimpleGraph.Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false, not_or]
    exact ⟨data.portNeSecond (secondSidePort second),
      data.portNeFirst (secondSidePort second),
      data.portVertex_ne (secondSidePort_ne_firstSidePort second first)⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A retained walk is edge-disjoint from every restored cross-side
three-edge return. -/
theorem retainedWalkToAmbient_edges_disjoint_crossSidePortCentralReturn
    (data : AdjacentPairData G)
    {left right : retainedVertexSet data.firstVertex data.secondVertex}
    (walk : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk left right)
    (first second : Fin 2) :
    (data.retainedWalkToAmbient walk).edges.Disjoint
      (data.crossSidePortCentralReturn first second).edges := by
  rw [List.disjoint_left]
  intro edge hretained hreturn
  rw [data.crossSidePortCentralReturn_edges] at hreturn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hreturn
  rcases hreturn with hsecond | hcentral | hfirst
  · subst edge
    exact data.boundaryEdgeValue_not_mem_retainedWalkToAmbient_edges
      walk (secondSidePort second) hretained
  · subst edge
    exact data.centralEdgeValue_not_mem_retainedWalkToAmbient_edges
      walk hretained
  · subst edge
    exact data.boundaryEdgeValue_not_mem_retainedWalkToAmbient_edges
      walk (firstSidePort first) hretained

/-- Close a retained path in any of the four cross-side port channels
through the restored adjacent pair. -/
def crossSidePortClosure
    (data : AdjacentPairData G) (first second : Fin 2)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk
        (data.retainedPort (firstSidePort first))
        (data.retainedPort (secondSidePort second))) :
    G.Walk (data.portVertex (firstSidePort first))
      (data.portVertex (firstSidePort first)) :=
  (data.retainedWalkToAmbient path).append
    (data.crossSidePortCentralReturn first second)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem crossSidePortClosure_isTrail
    (data : AdjacentPairData G) (first second : Fin 2)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk
        (data.retainedPort (firstSidePort first))
        (data.retainedPort (secondSidePort second)))
    (hpath : path.IsTrail) :
    (data.crossSidePortClosure first second path).IsTrail := by
  change ((data.retainedWalkToAmbient path).append
    (data.crossSidePortCentralReturn first second)).IsTrail
  exact (SimpleGraph.Walk.isTrail_append
    (data.retainedWalkToAmbient path)
      (data.crossSidePortCentralReturn first second)).2
    ⟨data.retainedWalkToAmbient_isTrail hpath,
      data.crossSidePortCentralReturn_isPath first second |>.isTrail,
      data.retainedWalkToAmbient_edges_disjoint_crossSidePortCentralReturn
        path first second⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A simple retained path in any cross-side channel closes to a simple
ambient cycle through the restored pair. -/
theorem crossSidePortClosure_isCycle
    (data : AdjacentPairData G) (first second : Fin 2)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk
        (data.retainedPort (firstSidePort first))
        (data.retainedPort (secondSidePort second)))
    (hpath : path.IsPath) :
    (data.crossSidePortClosure first second path).IsCycle := by
  have hambientPath : (data.retainedWalkToAmbient path).IsPath :=
    data.retainedWalkToAmbient_isPath hpath
  have hreturnPath :
      (data.crossSidePortCentralReturn first second).IsPath :=
    data.crossSidePortCentralReturn_isPath first second
  have hstartNotAmbientTail : data.portVertex (firstSidePort first) ∉
      (data.retainedWalkToAmbient path).support.tail := by
    have hnodup := hambientPath.support_nodup
    rw [← (data.retainedWalkToAmbient path).cons_tail_support] at hnodup
    exact (List.nodup_cons.mp hnodup).1
  have hdisjoint :
      (data.retainedWalkToAmbient path).support.tail.Disjoint
        (data.crossSidePortCentralReturn first second).support.tail := by
    rw [List.disjoint_left]
    intro vertex hambient hreturn
    have hambientSupport : vertex ∈
        (data.retainedWalkToAmbient path).support :=
      List.mem_of_mem_tail hambient
    have hambientMap := hambientSupport
    rw [GoertzelV24AdjacentPairBoundary.AdjacentPairData.retainedWalkToAmbient,
      SimpleGraph.Walk.support_map] at hambientMap
    rcases List.mem_map.mp hambientMap with
      ⟨retained, _hretainedSupport, hvertex⟩
    change retained.1 = vertex at hvertex
    subst vertex
    simp only [crossSidePortCentralReturn,
      SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at hreturn
    rcases hreturn with hsecondVertex | hfirstVertex | hfirstPort
    · exact retained.2.2 hsecondVertex
    · exact retained.2.1 hfirstVertex
    · exact hstartNotAmbientTail (hfirstPort ▸ hambient)
  apply hambientPath.isCycle_append hreturnPath hdisjoint
  exact Or.inr (by
    change 1 < 3
    omega)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem crossSidePortCentralReturn_zero_zero
    (data : AdjacentPairData G) :
    data.crossSidePortCentralReturn 0 0 =
      data.oppositePortCentralReturn := by
  rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem crossSidePortCentralReturn_one_one
    (data : AdjacentPairData G) :
    data.crossSidePortCentralReturn 1 1 =
      data.alternateOppositePortCentralReturn := by
  rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem crossSidePortClosure_zero_zero
    (data : AdjacentPairData G)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2)) :
    data.crossSidePortClosure 0 0 path =
      data.oppositePortClosure path := by
  rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem crossSidePortClosure_one_one
    (data : AdjacentPairData G)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 1) (data.retainedPort 3)) :
    data.crossSidePortClosure 1 1 path =
      data.alternateOppositePortClosure path := by
  rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The edge list of an indexed channel closure is the retained path followed
by its restored three-edge return. -/
theorem crossSidePortClosure_edges
    (data : AdjacentPairData G) (first second : Fin 2)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk
        (data.retainedPort (firstSidePort first))
        (data.retainedPort (secondSidePort second))) :
    (data.crossSidePortClosure first second path).edges =
      (data.retainedWalkToAmbient path).edges ++
        (data.crossSidePortCentralReturn first second).edges := by
  change ((data.retainedWalkToAmbient path).append
    (data.crossSidePortCentralReturn first second)).edges = _
  exact SimpleGraph.Walk.edges_append _ _

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Every indexed channel closure contains the restored central edge. -/
theorem centralEdgeValue_mem_crossSidePortClosure_edges
    (data : AdjacentPairData G) (first second : Fin 2)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk
        (data.retainedPort (firstSidePort first))
        (data.retainedPort (secondSidePort second))) :
    centralEdgeValue data ∈
      (data.crossSidePortClosure first second path).edges := by
  rw [data.crossSidePortClosure_edges]
  apply List.mem_append_right
  rw [data.crossSidePortCentralReturn_edges]
  simp

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The indexed channel closure contains its selected first-side boundary
edge. -/
theorem firstBoundaryEdgeValue_mem_crossSidePortClosure_edges
    (data : AdjacentPairData G) (first second : Fin 2)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk
        (data.retainedPort (firstSidePort first))
        (data.retainedPort (secondSidePort second))) :
    boundaryEdgeValue data (firstSidePort first) ∈
      (data.crossSidePortClosure first second path).edges := by
  rw [data.crossSidePortClosure_edges]
  apply List.mem_append_right
  rw [data.crossSidePortCentralReturn_edges]
  simp

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The indexed channel closure contains its selected second-side boundary
edge. -/
theorem secondBoundaryEdgeValue_mem_crossSidePortClosure_edges
    (data : AdjacentPairData G) (first second : Fin 2)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk
        (data.retainedPort (firstSidePort first))
        (data.retainedPort (secondSidePort second))) :
    boundaryEdgeValue data (secondSidePort second) ∈
      (data.crossSidePortClosure first second path).edges := by
  rw [data.crossSidePortClosure_edges]
  apply List.mem_append_right
  rw [data.crossSidePortCentralReturn_edges]
  simp

end GoertzelV24AdjacentPairBoundary.AdjacentPairData

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData
open GoertzelV24FaceBoundaryLinearAlgebra
open GoertzelV24MinimalFaceIntersections
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraphDartRotation

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- One fixed binary coordinate of the cross-face difference selects an
indexed cross-side channel and supports its entire retained segment. -/
theorem CrossCentralExactFaceCutPair.exists_indexedCrossSide_coordinateSupportPortClosure
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross) :
    ∃ (firstIndex secondIndex : Fin 2)
        (path : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk
            (data.retainedPort (firstSidePort firstIndex))
            (data.retainedPort (secondSidePort secondIndex))),
      path.IsPath ∧
        (cross : Sym2 (retainedVertexSet data.firstVertex
          data.secondVertex)) ∉ path.edges ∧
        (((pair.crossFaceDifferenceProfile
              (boundaryEdge data (secondSidePort secondIndex))).1 ≠ 0 ∧
            (pair.crossFaceDifferenceProfile
              (boundaryEdge data (firstSidePort firstIndex))).1 ≠ 0 ∧
            ∀ edge : (DeletedAdjacentPairGraph G data.firstVertex
                data.secondVertex).edgeSet,
              (edge : Sym2 (retainedVertexSet data.firstVertex
                data.secondVertex)) ∈ path.edges →
                (pair.crossFaceDifferenceProfile
                  (retainedEdgeToAmbientEdge data edge)).1 ≠ 0) ∨
          ((pair.crossFaceDifferenceProfile
              (boundaryEdge data (secondSidePort secondIndex))).2 ≠ 0 ∧
            (pair.crossFaceDifferenceProfile
              (boundaryEdge data (firstSidePort firstIndex))).2 ≠ 0 ∧
            ∀ edge : (DeletedAdjacentPairGraph G data.firstVertex
                data.secondVertex).edgeSet,
              (edge : Sym2 (retainedVertexSet data.firstVertex
                data.secondVertex)) ∈ path.edges →
                (pair.crossFaceDifferenceProfile
                  (retainedEdgeToAmbientEdge data edge)).2 ≠ 0)) ∧
        (data.crossSidePortClosure firstIndex secondIndex path).IsCycle := by
  rcases pair.exists_crossSide_coordinateSupportPortPath minimal with
    ⟨secondPort, firstPort, path, hsecondSide, hfirstSide,
      hpath, hcross, hcoordinate⟩
  obtain ⟨secondIndex, hsecondIndex⟩ :
      ∃ secondIndex : Fin 2,
        secondPort = secondSidePort secondIndex := by
    rcases hsecondSide with rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
  obtain ⟨firstIndex, hfirstIndex⟩ :
      ∃ firstIndex : Fin 2,
        firstPort = firstSidePort firstIndex := by
    rcases hfirstSide with rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
  subst secondPort
  subst firstPort
  refine ⟨firstIndex, secondIndex, path.reverse, hpath.reverse, ?_, ?_,
    data.crossSidePortClosure_isCycle firstIndex secondIndex path.reverse
      hpath.reverse⟩
  · intro hcrossReverse
    apply hcross
    simpa only [SimpleGraph.Walk.edges_reverse, List.mem_reverse] using
      hcrossReverse
  · rcases hcoordinate with hfirstCoordinate | hsecondCoordinate
    · refine Or.inl ⟨hfirstCoordinate.1, hfirstCoordinate.2.1, ?_⟩
      intro edge hedge
      apply hfirstCoordinate.2.2 edge
      simpa only [SimpleGraph.Walk.edges_reverse, List.mem_reverse] using hedge
    · refine Or.inr ⟨hsecondCoordinate.1, hsecondCoordinate.2.1, ?_⟩
      intro edge hedge
      apply hsecondCoordinate.2.2 edge
      simpa only [SimpleGraph.Walk.edges_reverse, List.mem_reverse] using hedge

/-- The cross-face difference support path has one of the four indexed
cross-side endpoint channels.  It is oriented from the first side to the
second side while preserving support and avoidance of the retained cross. -/
theorem CrossCentralExactFaceCutPair.exists_indexedCrossSide_differenceSupportPortPath
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross) :
    ∃ (firstIndex secondIndex : Fin 2)
        (path : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk
            (data.retainedPort (firstSidePort firstIndex))
            (data.retainedPort (secondSidePort secondIndex))),
      path.IsPath ∧
        (cross : Sym2 (retainedVertexSet data.firstVertex
          data.secondVertex)) ∉ path.edges ∧
        pair.crossFaceDifferenceProfile
            (boundaryEdge data (secondSidePort secondIndex)) ≠ 0 ∧
        pair.crossFaceDifferenceProfile
            (boundaryEdge data (firstSidePort firstIndex)) ≠ 0 ∧
        ∀ edge : (DeletedAdjacentPairGraph G data.firstVertex
            data.secondVertex).edgeSet,
          (edge : Sym2 (retainedVertexSet data.firstVertex
            data.secondVertex)) ∈ path.edges →
            pair.crossFaceDifferenceProfile
              (retainedEdgeToAmbientEdge data edge) ≠ 0 := by
  rcases pair.exists_crossSide_differenceSupportPortPath minimal with
    ⟨secondPort, firstPort, path, hrest⟩
  rcases hrest with ⟨hsecondSide, hrest⟩
  rcases hrest with ⟨hfirstSide, hrest⟩
  rcases hrest with ⟨hpath, hrest⟩
  rcases hrest with ⟨hcross, hrest⟩
  rcases hrest with ⟨hsecondBoundary, hrest⟩
  rcases hrest with ⟨hfirstBoundary, hsupport⟩
  obtain ⟨secondIndex, hsecondIndex⟩ :
      ∃ secondIndex : Fin 2,
        secondPort = secondSidePort secondIndex := by
    rcases hsecondSide with rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
  obtain ⟨firstIndex, hfirstIndex⟩ :
      ∃ firstIndex : Fin 2,
        firstPort = firstSidePort firstIndex := by
    rcases hfirstSide with rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
  subst secondPort
  subst firstPort
  refine ⟨firstIndex, secondIndex, path.reverse, hpath.reverse, ?_,
    hsecondBoundary, hfirstBoundary, ?_⟩
  · intro hcrossReverse
    apply hcross
    simpa only [SimpleGraph.Walk.edges_reverse, List.mem_reverse] using
      hcrossReverse
  · intro edge hedge
    apply hsupport edge
    simpa only [SimpleGraph.Walk.edges_reverse, List.mem_reverse] using hedge

/-- Consequently, a paired exact face cut selects one of four simple ambient
cycles through the restored adjacent pair.  Its retained segment avoids the
cross and is pointwise supported by the cross-face difference profile. -/
theorem CrossCentralExactFaceCutPair.exists_indexedCrossSide_differenceSupportPortClosure
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross) :
    ∃ (firstIndex secondIndex : Fin 2)
        (path : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk
            (data.retainedPort (firstSidePort firstIndex))
            (data.retainedPort (secondSidePort secondIndex))),
      path.IsPath ∧
        (cross : Sym2 (retainedVertexSet data.firstVertex
          data.secondVertex)) ∉ path.edges ∧
        pair.crossFaceDifferenceProfile
            (boundaryEdge data (secondSidePort secondIndex)) ≠ 0 ∧
        pair.crossFaceDifferenceProfile
            (boundaryEdge data (firstSidePort firstIndex)) ≠ 0 ∧
        (∀ edge : (DeletedAdjacentPairGraph G data.firstVertex
            data.secondVertex).edgeSet,
          (edge : Sym2 (retainedVertexSet data.firstVertex
            data.secondVertex)) ∈ path.edges →
            pair.crossFaceDifferenceProfile
              (retainedEdgeToAmbientEdge data edge) ≠ 0) ∧
        (data.crossSidePortClosure firstIndex secondIndex path).IsCycle := by
  rcases pair.exists_indexedCrossSide_differenceSupportPortPath minimal with
    ⟨firstIndex, secondIndex, path, hpath, hcross,
      hsecondBoundary, hfirstBoundary, hsupport⟩
  exact ⟨firstIndex, secondIndex, path, hpath, hcross,
    hsecondBoundary, hfirstBoundary, hsupport,
    data.crossSidePortClosure_isCycle firstIndex secondIndex path hpath⟩

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
