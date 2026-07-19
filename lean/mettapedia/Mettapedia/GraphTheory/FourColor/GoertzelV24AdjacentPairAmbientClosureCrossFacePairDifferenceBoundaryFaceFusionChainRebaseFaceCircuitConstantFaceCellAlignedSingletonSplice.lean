import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitConstantFaceCellSignedSingleton

namespace SimpleGraph.Walk

universe u

variable {Vertex : Type u} {Graph : SimpleGraph Vertex}

/-- If two walks traverse selected copies of one edge in the same direction,
join their strict incoming prefixes after reversing the second prefix.  The
common edge itself is omitted. -/
def prefixPairAtAlignedDart
    {firstLeft firstRight secondLeft secondRight : Vertex}
    (firstWalk : Graph.Walk firstLeft firstRight)
    (secondWalk : Graph.Walk secondLeft secondRight)
    (firstPosition : Fin firstWalk.edges.length)
    (secondPosition : Fin secondWalk.edges.length)
    (hsame : secondWalk.dartAtEdgePosition secondPosition =
      firstWalk.dartAtEdgePosition firstPosition) :
    Graph.Walk firstLeft secondLeft :=
  let hjoin : secondWalk.getVert secondPosition.val =
      firstWalk.getVert firstPosition.val := by
    simpa using congrArg (fun dart => dart.fst) hsame
  (firstWalk.take firstPosition.val).append
    ((secondWalk.take secondPosition.val).reverse.copy hjoin rfl)

/-- The complementary aligned splice reverses the first strict outgoing
suffix and joins it to the second strict outgoing suffix. -/
def suffixPairAtAlignedDart
    {firstLeft firstRight secondLeft secondRight : Vertex}
    (firstWalk : Graph.Walk firstLeft firstRight)
    (secondWalk : Graph.Walk secondLeft secondRight)
    (firstPosition : Fin firstWalk.edges.length)
    (secondPosition : Fin secondWalk.edges.length)
    (hsame : secondWalk.dartAtEdgePosition secondPosition =
      firstWalk.dartAtEdgePosition firstPosition) :
    Graph.Walk firstRight secondRight :=
  let hjoin : secondWalk.getVert (secondPosition.val + 1) =
      firstWalk.getVert (firstPosition.val + 1) := by
    simpa using congrArg (fun dart => dart.snd) hsame
  (firstWalk.drop (firstPosition.val + 1)).reverse.append
    ((secondWalk.drop (secondPosition.val + 1)).copy hjoin rfl)

/-- The incoming aligned splice contains exactly the two strict prefixes,
with the second one traversed backwards. -/
@[simp] theorem prefixPairAtAlignedDart_edges
    {firstLeft firstRight secondLeft secondRight : Vertex}
    (firstWalk : Graph.Walk firstLeft firstRight)
    (secondWalk : Graph.Walk secondLeft secondRight)
    (firstPosition : Fin firstWalk.edges.length)
    (secondPosition : Fin secondWalk.edges.length)
    (hsame : secondWalk.dartAtEdgePosition secondPosition =
      firstWalk.dartAtEdgePosition firstPosition) :
    (firstWalk.prefixPairAtAlignedDart secondWalk firstPosition
        secondPosition hsame).edges =
      firstWalk.edges.take firstPosition.val ++
        (secondWalk.edges.take secondPosition.val).reverse := by
  simp [prefixPairAtAlignedDart, SimpleGraph.Walk.edges_append,
    SimpleGraph.Walk.edges_take]

/-- The outgoing aligned splice contains exactly the reversed first strict
suffix followed by the second strict suffix. -/
@[simp] theorem suffixPairAtAlignedDart_edges
    {firstLeft firstRight secondLeft secondRight : Vertex}
    (firstWalk : Graph.Walk firstLeft firstRight)
    (secondWalk : Graph.Walk secondLeft secondRight)
    (firstPosition : Fin firstWalk.edges.length)
    (secondPosition : Fin secondWalk.edges.length)
    (hsame : secondWalk.dartAtEdgePosition secondPosition =
      firstWalk.dartAtEdgePosition firstPosition) :
    (firstWalk.suffixPairAtAlignedDart secondWalk firstPosition
        secondPosition hsame).edges =
      (firstWalk.edges.drop (firstPosition.val + 1)).reverse ++
        secondWalk.edges.drop (secondPosition.val + 1) := by
  simp [suffixPairAtAlignedDart, SimpleGraph.Walk.edges_append,
    SimpleGraph.Walk.edges_drop]

/-- Duplicate-free source edge lists ensure that the aligned incoming splice
does not contain the selected common edge. -/
theorem selectedEdge_not_mem_prefixPairAtAlignedDart_edges
    {firstLeft firstRight secondLeft secondRight : Vertex}
    (firstWalk : Graph.Walk firstLeft firstRight)
    (secondWalk : Graph.Walk secondLeft secondRight)
    (firstPosition : Fin firstWalk.edges.length)
    (secondPosition : Fin secondWalk.edges.length)
    (hsame : secondWalk.dartAtEdgePosition secondPosition =
      firstWalk.dartAtEdgePosition firstPosition)
    (hfirstNodup : firstWalk.edges.Nodup)
    (hsecondNodup : secondWalk.edges.Nodup) :
    firstWalk.edges.get firstPosition ∉
      (firstWalk.prefixPairAtAlignedDart secondWalk firstPosition
        secondPosition hsame).edges := by
  have hedge : secondWalk.edges.get secondPosition =
      firstWalk.edges.get firstPosition := by
    have hdartEdge := congrArg SimpleGraph.Dart.edge hsame
    simpa using hdartEdge
  rw [prefixPairAtAlignedDart_edges]
  intro hmem
  rcases List.mem_append.mp hmem with hfirst | hsecond
  · exact hfirstNodup.get_not_mem_take firstPosition hfirst
  · apply hsecondNodup.get_not_mem_take secondPosition
    rw [hedge]
    simpa using hsecond

/-- The selected common edge is also absent from the aligned outgoing
splice. -/
theorem selectedEdge_not_mem_suffixPairAtAlignedDart_edges
    {firstLeft firstRight secondLeft secondRight : Vertex}
    (firstWalk : Graph.Walk firstLeft firstRight)
    (secondWalk : Graph.Walk secondLeft secondRight)
    (firstPosition : Fin firstWalk.edges.length)
    (secondPosition : Fin secondWalk.edges.length)
    (hsame : secondWalk.dartAtEdgePosition secondPosition =
      firstWalk.dartAtEdgePosition firstPosition)
    (hfirstNodup : firstWalk.edges.Nodup)
    (hsecondNodup : secondWalk.edges.Nodup) :
    firstWalk.edges.get firstPosition ∉
      (firstWalk.suffixPairAtAlignedDart secondWalk firstPosition
        secondPosition hsame).edges := by
  have hedge : secondWalk.edges.get secondPosition =
      firstWalk.edges.get firstPosition := by
    have hdartEdge := congrArg SimpleGraph.Dart.edge hsame
    simpa using hdartEdge
  rw [suffixPairAtAlignedDart_edges]
  intro hmem
  rcases List.mem_append.mp hmem with hfirst | hsecond
  · exact hfirstNodup.get_not_mem_drop_succ firstPosition
      (by simpa using hfirst)
  · apply hsecondNodup.get_not_mem_drop_succ secondPosition
    rw [hedge]
    exact hsecond

/-- Exact length of the incoming aligned splice. -/
@[simp] theorem prefixPairAtAlignedDart_length
    {firstLeft firstRight secondLeft secondRight : Vertex}
    (firstWalk : Graph.Walk firstLeft firstRight)
    (secondWalk : Graph.Walk secondLeft secondRight)
    (firstPosition : Fin firstWalk.edges.length)
    (secondPosition : Fin secondWalk.edges.length)
    (hsame : secondWalk.dartAtEdgePosition secondPosition =
      firstWalk.dartAtEdgePosition firstPosition) :
    (firstWalk.prefixPairAtAlignedDart secondWalk firstPosition
        secondPosition hsame).length =
      firstPosition.val + secondPosition.val := by
  have hfirst : firstPosition.val < firstWalk.length := by
    simpa using firstPosition.isLt
  have hsecond : secondPosition.val < secondWalk.length := by
    simpa using secondPosition.isLt
  simp [prefixPairAtAlignedDart, Nat.min_eq_left hfirst.le,
    Nat.min_eq_left hsecond.le]

/-- Exact length of the outgoing aligned splice. -/
@[simp] theorem suffixPairAtAlignedDart_length
    {firstLeft firstRight secondLeft secondRight : Vertex}
    (firstWalk : Graph.Walk firstLeft firstRight)
    (secondWalk : Graph.Walk secondLeft secondRight)
    (firstPosition : Fin firstWalk.edges.length)
    (secondPosition : Fin secondWalk.edges.length)
    (hsame : secondWalk.dartAtEdgePosition secondPosition =
      firstWalk.dartAtEdgePosition firstPosition) :
    (firstWalk.suffixPairAtAlignedDart secondWalk firstPosition
        secondPosition hsame).length =
      (firstWalk.length - (firstPosition.val + 1)) +
        (secondWalk.length - (secondPosition.val + 1)) := by
  simp [suffixPairAtAlignedDart]

/-- Together the two aligned splices remove precisely the two selected edge
occurrences from the source walks. -/
theorem alignedDartSplices_length_add_add_two
    {firstLeft firstRight secondLeft secondRight : Vertex}
    (firstWalk : Graph.Walk firstLeft firstRight)
    (secondWalk : Graph.Walk secondLeft secondRight)
    (firstPosition : Fin firstWalk.edges.length)
    (secondPosition : Fin secondWalk.edges.length)
    (hsame : secondWalk.dartAtEdgePosition secondPosition =
      firstWalk.dartAtEdgePosition firstPosition) :
    (firstWalk.prefixPairAtAlignedDart secondWalk firstPosition
          secondPosition hsame).length +
        (firstWalk.suffixPairAtAlignedDart secondWalk firstPosition
          secondPosition hsame).length + 2 =
      firstWalk.length + secondWalk.length := by
  rw [prefixPairAtAlignedDart_length, suffixPairAtAlignedDart_length]
  have hfirst : firstPosition.val < firstWalk.length := by
    simpa using firstPosition.isLt
  have hsecond : secondPosition.val < secondWalk.length := by
    simpa using secondPosition.isLt
  omega

end SimpleGraph.Walk

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace GoertzelV24AdjacentPairBoundary.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData
open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

/-- The two-edge return from port `1` to port `0` through the first restored
vertex. -/
def firstSidePortReturn (data : AdjacentPairData G) :
    G.Walk (data.portVertex 1) (data.portVertex 0) :=
  SimpleGraph.Walk.cons data.first_adj_port_one.symm
    (SimpleGraph.Walk.cons data.first_adj_port_zero SimpleGraph.Walk.nil)

/-- The symmetric two-edge return from port `3` to port `2` through the
second restored vertex. -/
def secondSidePortReturn (data : AdjacentPairData G) :
    G.Walk (data.portVertex 3) (data.portVertex 2) :=
  SimpleGraph.Walk.cons data.second_adj_port_three.symm
    (SimpleGraph.Walk.cons data.second_adj_port_two SimpleGraph.Walk.nil)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem firstSidePortReturn_length (data : AdjacentPairData G) :
    data.firstSidePortReturn.length = 2 := by
  simp [firstSidePortReturn]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem secondSidePortReturn_length (data : AdjacentPairData G) :
    data.secondSidePortReturn.length = 2 := by
  simp [secondSidePortReturn]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem firstSidePortReturn_isPath (data : AdjacentPairData G) :
    data.firstSidePortReturn.IsPath := by
  rw [firstSidePortReturn, SimpleGraph.Walk.cons_isPath_iff]
  constructor
  · rw [SimpleGraph.Walk.cons_isPath_iff]
    exact ⟨SimpleGraph.Walk.IsPath.nil,
      by simpa using (data.portNeFirst 0).symm⟩
  · simp only [SimpleGraph.Walk.support_cons,
      SimpleGraph.Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false, not_or]
    exact ⟨data.portNeFirst 1,
      data.portVertex_ne (by decide : (1 : Fin 4) ≠ 0)⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem secondSidePortReturn_isPath (data : AdjacentPairData G) :
    data.secondSidePortReturn.IsPath := by
  rw [secondSidePortReturn, SimpleGraph.Walk.cons_isPath_iff]
  constructor
  · rw [SimpleGraph.Walk.cons_isPath_iff]
    exact ⟨SimpleGraph.Walk.IsPath.nil,
      by simpa using (data.portNeSecond 2).symm⟩
  · simp only [SimpleGraph.Walk.support_cons,
      SimpleGraph.Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false, not_or]
    exact ⟨data.portNeSecond 3,
      data.portVertex_ne (by decide : (3 : Fin 4) ≠ 2)⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem firstSidePortReturn_edges (data : AdjacentPairData G) :
    data.firstSidePortReturn.edges =
      [boundaryEdgeValue data 1, boundaryEdgeValue data 0] := by
  simp [firstSidePortReturn, boundaryEdgeValue, Sym2.eq_swap]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem secondSidePortReturn_edges (data : AdjacentPairData G) :
    data.secondSidePortReturn.edges =
      [boundaryEdgeValue data 3, boundaryEdgeValue data 2] := by
  simp [secondSidePortReturn, boundaryEdgeValue, Sym2.eq_swap]

/-- Close a retained `0–1` path through the first restored vertex. -/
def firstSidePortClosure (data : AdjacentPairData G)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 1)) :
    G.Walk (data.portVertex 0) (data.portVertex 0) :=
  (data.retainedWalkToAmbient path).append data.firstSidePortReturn

/-- Close a retained `2–3` path through the second restored vertex. -/
def secondSidePortClosure (data : AdjacentPairData G)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 2) (data.retainedPort 3)) :
    G.Walk (data.portVertex 2) (data.portVertex 2) :=
  (data.retainedWalkToAmbient path).append data.secondSidePortReturn

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A retained walk is edge-disjoint from the first-side return. -/
theorem retainedWalkToAmbient_edges_disjoint_firstSidePortReturn
    (data : AdjacentPairData G)
    {left right : retainedVertexSet data.firstVertex data.secondVertex}
    (walk : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk left right) :
    (data.retainedWalkToAmbient walk).edges.Disjoint
      data.firstSidePortReturn.edges := by
  rw [List.disjoint_left]
  intro edge hretained hreturn
  rw [data.firstSidePortReturn_edges] at hreturn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hreturn
  rcases hreturn with hone | hzero
  · subst edge
    exact data.boundaryEdgeValue_not_mem_retainedWalkToAmbient_edges
      walk 1 hretained
  · subst edge
    exact data.boundaryEdgeValue_not_mem_retainedWalkToAmbient_edges
      walk 0 hretained

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A retained walk is edge-disjoint from the second-side return. -/
theorem retainedWalkToAmbient_edges_disjoint_secondSidePortReturn
    (data : AdjacentPairData G)
    {left right : retainedVertexSet data.firstVertex data.secondVertex}
    (walk : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk left right) :
    (data.retainedWalkToAmbient walk).edges.Disjoint
      data.secondSidePortReturn.edges := by
  rw [List.disjoint_left]
  intro edge hretained hreturn
  rw [data.secondSidePortReturn_edges] at hreturn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hreturn
  rcases hreturn with hthree | htwo
  · subst edge
    exact data.boundaryEdgeValue_not_mem_retainedWalkToAmbient_edges
      walk 3 hretained
  · subst edge
    exact data.boundaryEdgeValue_not_mem_retainedWalkToAmbient_edges
      walk 2 hretained

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A simple retained `0–1` path closes to a simple ambient cycle. -/
theorem firstSidePortClosure_isCycle (data : AdjacentPairData G)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 1))
    (hpath : path.IsPath) :
    (data.firstSidePortClosure path).IsCycle := by
  have hambientPath : (data.retainedWalkToAmbient path).IsPath :=
    data.retainedWalkToAmbient_isPath hpath
  have hstartNotAmbientTail : data.portVertex 0 ∉
      (data.retainedWalkToAmbient path).support.tail := by
    have hnodup := hambientPath.support_nodup
    rw [← (data.retainedWalkToAmbient path).cons_tail_support] at hnodup
    exact (List.nodup_cons.mp hnodup).1
  have hdisjoint :
      (data.retainedWalkToAmbient path).support.tail.Disjoint
        data.firstSidePortReturn.support.tail := by
    rw [List.disjoint_left]
    intro vertex hambient hreturn
    have hambientSupport : vertex ∈
        (data.retainedWalkToAmbient path).support :=
      List.mem_of_mem_tail hambient
    have hambientMap := hambientSupport
    rw [retainedWalkToAmbient, SimpleGraph.Walk.support_map] at hambientMap
    rcases List.mem_map.mp hambientMap with
      ⟨retained, _hretainedSupport, hvertex⟩
    change retained.1 = vertex at hvertex
    subst vertex
    simp only [firstSidePortReturn, SimpleGraph.Walk.support_cons,
      SimpleGraph.Walk.support_nil, List.tail_cons, List.mem_cons,
      List.not_mem_nil, or_false] at hreturn
    rcases hreturn with hfirstVertex | hfirstPort
    · exact retained.2.1 hfirstVertex
    · exact hstartNotAmbientTail (hfirstPort ▸ hambient)
  apply hambientPath.isCycle_append data.firstSidePortReturn_isPath hdisjoint
  exact Or.inr (by change 1 < 2; omega)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A simple retained `2–3` path closes to a simple ambient cycle. -/
theorem secondSidePortClosure_isCycle (data : AdjacentPairData G)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 2) (data.retainedPort 3))
    (hpath : path.IsPath) :
    (data.secondSidePortClosure path).IsCycle := by
  have hambientPath : (data.retainedWalkToAmbient path).IsPath :=
    data.retainedWalkToAmbient_isPath hpath
  have hstartNotAmbientTail : data.portVertex 2 ∉
      (data.retainedWalkToAmbient path).support.tail := by
    have hnodup := hambientPath.support_nodup
    rw [← (data.retainedWalkToAmbient path).cons_tail_support] at hnodup
    exact (List.nodup_cons.mp hnodup).1
  have hdisjoint :
      (data.retainedWalkToAmbient path).support.tail.Disjoint
        data.secondSidePortReturn.support.tail := by
    rw [List.disjoint_left]
    intro vertex hambient hreturn
    have hambientSupport : vertex ∈
        (data.retainedWalkToAmbient path).support :=
      List.mem_of_mem_tail hambient
    have hambientMap := hambientSupport
    rw [retainedWalkToAmbient, SimpleGraph.Walk.support_map] at hambientMap
    rcases List.mem_map.mp hambientMap with
      ⟨retained, _hretainedSupport, hvertex⟩
    change retained.1 = vertex at hvertex
    subst vertex
    simp only [secondSidePortReturn, SimpleGraph.Walk.support_cons,
      SimpleGraph.Walk.support_nil, List.tail_cons, List.mem_cons,
      List.not_mem_nil, or_false] at hreturn
    rcases hreturn with hsecondVertex | hsecondPort
    · exact retained.2.2 hsecondVertex
    · exact hstartNotAmbientTail (hsecondPort ▸ hambient)
  apply hambientPath.isCycle_append data.secondSidePortReturn_isPath hdisjoint
  exact Or.inr (by change 1 < 2; omega)

end GoertzelV24AdjacentPairBoundary.AdjacentPairData

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData
open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- The aligned common edge splices the two incoming arms into the same-side
`0–1` channel. -/
def RetainedIntersectionExactFaceCutPair.zeroToOneSpliceAtAlignedSharedEdge
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (position : Fin pair.prefixSharedEdgeOrder.length)
    (hsame : pair.suffixSharedEdgeDart position =
      pair.prefixSharedEdgeDart position) :
    (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex).Walk
      (data.retainedPort 0) (data.retainedPort 1) :=
  pair.prefixTrail.prefixPairAtAlignedDart pair.suffixTrail
    (pair.prefixSharedEdgePositionEmbedding position)
    (pair.suffixSharedEdgePositionEmbedding
      (pair.sharedEdgeOrderEquiv position)) hsame

/-- The two outgoing arms give the complementary same-side `2–3` channel. -/
def RetainedIntersectionExactFaceCutPair.twoToThreeSpliceAtAlignedSharedEdge
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (position : Fin pair.prefixSharedEdgeOrder.length)
    (hsame : pair.suffixSharedEdgeDart position =
      pair.prefixSharedEdgeDart position) :
    (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex).Walk
      (data.retainedPort 2) (data.retainedPort 3) :=
  pair.prefixTrail.suffixPairAtAlignedDart pair.suffixTrail
    (pair.prefixSharedEdgePositionEmbedding position)
    (pair.suffixSharedEdgePositionEmbedding
      (pair.sharedEdgeOrderEquiv position)) hsame

/-- Bypass repeated vertices in the aligned `0–1` splice. -/
def RetainedIntersectionExactFaceCutPair.zeroToOnePathAtAlignedSharedEdge
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (position : Fin pair.prefixSharedEdgeOrder.length)
    (hsame : pair.suffixSharedEdgeDart position =
      pair.prefixSharedEdgeDart position) :
    (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex).Walk
      (data.retainedPort 0) (data.retainedPort 1) :=
  (pair.zeroToOneSpliceAtAlignedSharedEdge position hsame).bypass

/-- Bypass repeated vertices in the aligned `2–3` splice. -/
def RetainedIntersectionExactFaceCutPair.twoToThreePathAtAlignedSharedEdge
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (position : Fin pair.prefixSharedEdgeOrder.length)
    (hsame : pair.suffixSharedEdgeDart position =
      pair.prefixSharedEdgeDart position) :
    (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex).Walk
      (data.retainedPort 2) (data.retainedPort 3) :=
  (pair.twoToThreeSpliceAtAlignedSharedEdge position hsame).bypass

theorem RetainedIntersectionExactFaceCutPair.zeroToOnePathAtAlignedSharedEdge_isPath
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (position : Fin pair.prefixSharedEdgeOrder.length)
    (hsame : pair.suffixSharedEdgeDart position =
      pair.prefixSharedEdgeDart position) :
    (pair.zeroToOnePathAtAlignedSharedEdge position hsame).IsPath :=
  (pair.zeroToOneSpliceAtAlignedSharedEdge position hsame).bypass_isPath

theorem RetainedIntersectionExactFaceCutPair.twoToThreePathAtAlignedSharedEdge_isPath
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (position : Fin pair.prefixSharedEdgeOrder.length)
    (hsame : pair.suffixSharedEdgeDart position =
      pair.prefixSharedEdgeDart position) :
    (pair.twoToThreePathAtAlignedSharedEdge position hsame).IsPath :=
  (pair.twoToThreeSpliceAtAlignedSharedEdge position hsame).bypass_isPath

/-- The selected shared edge is absent from the raw aligned `0–1` splice. -/
theorem RetainedIntersectionExactFaceCutPair.sharedEdgeAt_not_mem_zeroToOneSplice_edges
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (position : Fin pair.prefixSharedEdgeOrder.length)
    (hsame : pair.suffixSharedEdgeDart position =
      pair.prefixSharedEdgeDart position) :
    (pair.sharedEdgeAt position).1 ∉
      (pair.zeroToOneSpliceAtAlignedSharedEdge position hsame).edges := by
  have hselected : (pair.sharedEdgeAt position).1 =
      pair.prefixTrail.edges.get
        (pair.prefixSharedEdgePositionEmbedding position) :=
    pair.prefixSharedEdgePositionEmbedding_preserves_edge position
  rw [hselected]
  exact pair.prefixTrail.selectedEdge_not_mem_prefixPairAtAlignedDart_edges
    pair.suffixTrail (pair.prefixSharedEdgePositionEmbedding position)
      (pair.suffixSharedEdgePositionEmbedding
        (pair.sharedEdgeOrderEquiv position)) hsame
      pair.prefixRetained_isTrail.edges_nodup
      pair.suffixRetained_isTrail.edges_nodup

/-- The selected shared edge is absent from the raw aligned `2–3` splice. -/
theorem RetainedIntersectionExactFaceCutPair.sharedEdgeAt_not_mem_twoToThreeSplice_edges
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (position : Fin pair.prefixSharedEdgeOrder.length)
    (hsame : pair.suffixSharedEdgeDart position =
      pair.prefixSharedEdgeDart position) :
    (pair.sharedEdgeAt position).1 ∉
      (pair.twoToThreeSpliceAtAlignedSharedEdge position hsame).edges := by
  have hselected : (pair.sharedEdgeAt position).1 =
      pair.prefixTrail.edges.get
        (pair.prefixSharedEdgePositionEmbedding position) :=
    pair.prefixSharedEdgePositionEmbedding_preserves_edge position
  rw [hselected]
  exact pair.prefixTrail.selectedEdge_not_mem_suffixPairAtAlignedDart_edges
    pair.suffixTrail (pair.prefixSharedEdgePositionEmbedding position)
      (pair.suffixSharedEdgePositionEmbedding
        (pair.sharedEdgeOrderEquiv position)) hsame
      pair.prefixRetained_isTrail.edges_nodup
      pair.suffixRetained_isTrail.edges_nodup

/-- Bypassing either aligned splice cannot reintroduce its deleted shared
edge. -/
theorem RetainedIntersectionExactFaceCutPair.sharedEdgeAt_not_mem_zeroToOnePath_edges
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (position : Fin pair.prefixSharedEdgeOrder.length)
    (hsame : pair.suffixSharedEdgeDart position =
      pair.prefixSharedEdgeDart position) :
    (pair.sharedEdgeAt position).1 ∉
      (pair.zeroToOnePathAtAlignedSharedEdge position hsame).edges := by
  intro hmem
  apply pair.sharedEdgeAt_not_mem_zeroToOneSplice_edges position hsame
  exact SimpleGraph.Walk.edges_bypass_subset_edges
    (pair.zeroToOneSpliceAtAlignedSharedEdge position hsame) hmem

theorem RetainedIntersectionExactFaceCutPair.sharedEdgeAt_not_mem_twoToThreePath_edges
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (position : Fin pair.prefixSharedEdgeOrder.length)
    (hsame : pair.suffixSharedEdgeDart position =
      pair.prefixSharedEdgeDart position) :
    (pair.sharedEdgeAt position).1 ∉
      (pair.twoToThreePathAtAlignedSharedEdge position hsame).edges := by
  intro hmem
  apply pair.sharedEdgeAt_not_mem_twoToThreeSplice_edges position hsame
  exact SimpleGraph.Walk.edges_bypass_subset_edges
    (pair.twoToThreeSpliceAtAlignedSharedEdge position hsame) hmem

/-- The aligned raw splices delete exactly two edge occurrences. -/
theorem RetainedIntersectionExactFaceCutPair.alignedSharedEdgeSplices_length_add_add_two
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (position : Fin pair.prefixSharedEdgeOrder.length)
    (hsame : pair.suffixSharedEdgeDart position =
      pair.prefixSharedEdgeDart position) :
    (pair.zeroToOneSpliceAtAlignedSharedEdge position hsame).length +
        (pair.twoToThreeSpliceAtAlignedSharedEdge position hsame).length + 2 =
      pair.prefixTrail.length + pair.suffixTrail.length :=
  pair.prefixTrail.alignedDartSplices_length_add_add_two pair.suffixTrail
    (pair.prefixSharedEdgePositionEmbedding position)
    (pair.suffixSharedEdgePositionEmbedding
      (pair.sharedEdgeOrderEquiv position)) hsame

/-- Bypass cannot increase either aligned splice, so their total path length
is strictly smaller than the two source trails. -/
theorem RetainedIntersectionExactFaceCutPair.alignedSharedEdgePaths_length_add_lt
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (position : Fin pair.prefixSharedEdgeOrder.length)
    (hsame : pair.suffixSharedEdgeDart position =
      pair.prefixSharedEdgeDart position) :
    (pair.zeroToOnePathAtAlignedSharedEdge position hsame).length +
        (pair.twoToThreePathAtAlignedSharedEdge position hsame).length <
      pair.prefixTrail.length + pair.suffixTrail.length := by
  have hzero :=
    (pair.zeroToOneSpliceAtAlignedSharedEdge position hsame).length_bypass_le_length
  have htwo :=
    (pair.twoToThreeSpliceAtAlignedSharedEdge position hsame).length_bypass_le_length
  have hsum := pair.alignedSharedEdgeSplices_length_add_add_two position hsame
  change
    (pair.zeroToOneSpliceAtAlignedSharedEdge position hsame).bypass.length +
        (pair.twoToThreeSpliceAtAlignedSharedEdge position hsame).bypass.length <
      pair.prefixTrail.length + pair.suffixTrail.length
  omega

/-- The geometric output of an aligned localized shared edge: two same-side
paths avoiding that edge and having strictly smaller total length. -/
structure LocalizedStrictlyShorterSameSidePaths
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (face : OrbitFace graphData.toRotationSystem) where
  selectedEdge : (DeletedAdjacentPairGraph G data.firstVertex
    data.secondVertex).edgeSet
  selectedEdge_ne_oldCross : selectedEdge ≠ oldCross
  selectedAmbientEdge_mem_face :
    retainedEdgeToAmbientEdge data selectedEdge ∈
      orbitFaceBoundary graphData.toRotationSystem face
  zeroToOnePath :
    (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex).Walk
      (data.retainedPort 0) (data.retainedPort 1)
  twoToThreePath :
    (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex).Walk
      (data.retainedPort 2) (data.retainedPort 3)
  zeroToOne_isPath : zeroToOnePath.IsPath
  twoToThree_isPath : twoToThreePath.IsPath
  zeroToOne_closure_isCycle :
    (data.firstSidePortClosure zeroToOnePath).IsCycle
  twoToThree_closure_isCycle :
    (data.secondSidePortClosure twoToThreePath).IsCycle
  selectedEdge_not_mem_zeroToOnePath :
    selectedEdge.1 ∉ zeroToOnePath.edges
  selectedEdge_not_mem_twoToThreePath :
    selectedEdge.1 ∉ twoToThreePath.edges
  total_length_lt :
    zeroToOnePath.length + twoToThreePath.length <
      pair.prefixTrail.length + pair.suffixTrail.length

/-- Package one aligned localized profile position as strict same-side
descent. -/
def RetainedIntersectionExactFaceCutPair.toLocalizedStrictlyShorterSameSidePaths
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (face : OrbitFace graphData.toRotationSystem)
    (position : Fin pair.prefixSharedEdgeOrder.length)
    (hsame : pair.suffixSharedEdgeDart position =
      pair.prefixSharedEdgeDart position)
    (hne : pair.sharedEdgeAt position ≠ oldCross)
    (hface : retainedEdgeToAmbientEdge data (pair.sharedEdgeAt position) ∈
      orbitFaceBoundary graphData.toRotationSystem face) :
    LocalizedStrictlyShorterSameSidePaths pair oldCross face where
  selectedEdge := pair.sharedEdgeAt position
  selectedEdge_ne_oldCross := hne
  selectedAmbientEdge_mem_face := hface
  zeroToOnePath := pair.zeroToOnePathAtAlignedSharedEdge position hsame
  twoToThreePath := pair.twoToThreePathAtAlignedSharedEdge position hsame
  zeroToOne_isPath :=
    pair.zeroToOnePathAtAlignedSharedEdge_isPath position hsame
  twoToThree_isPath :=
    pair.twoToThreePathAtAlignedSharedEdge_isPath position hsame
  zeroToOne_closure_isCycle := data.firstSidePortClosure_isCycle
    (pair.zeroToOnePathAtAlignedSharedEdge position hsame)
    (pair.zeroToOnePathAtAlignedSharedEdge_isPath position hsame)
  twoToThree_closure_isCycle := data.secondSidePortClosure_isCycle
    (pair.twoToThreePathAtAlignedSharedEdge position hsame)
    (pair.twoToThreePathAtAlignedSharedEdge_isPath position hsame)
  selectedEdge_not_mem_zeroToOnePath :=
    pair.sharedEdgeAt_not_mem_zeroToOnePath_edges position hsame
  selectedEdge_not_mem_twoToThreePath :=
    pair.sharedEdgeAt_not_mem_twoToThreePath_edges position hsame
  total_length_lt :=
    pair.alignedSharedEdgePaths_length_add_lt position hsame

/-- Every exact rebase target has strict total-length descent.  Equal
singleton orientations give the two same-side channels; opposite
orientations give the two mixed-port channels. -/
theorem CrossCentralExactFaceRebaseStep.target_strictlyShorterSameSidePaths_or_strictlyShorterMixedPortCycles
    {graphData : Data G} {data : AdjacentPairData G}
    {source : CrossCentralExactFaceCutChannelState graphData data}
    {firstRoot secondRoot : V}
    {firstFusion : G.Walk firstRoot firstRoot}
    {secondFusion : G.Walk secondRoot secondRoot}
    {successors : LocalizedFusionSuccessorResolution source.pair source.face
      firstFusion secondFusion}
    (step : CrossCentralExactFaceRebaseStep graphData data source successors) :
    let pair := step.targetRetainedIntersectionProfile
    Nonempty (LocalizedStrictlyShorterSameSidePaths pair source.cross
        source.face) ∨
      Nonempty (LocalizedStrictlyShorterMixedPortCycles pair source.cross
        source.face) := by
  let pair := step.targetRetainedIntersectionProfile
  rcases step.target_signedMonodromy_eq_refl_or_strictlyShorterMixedPortCycles
      with hidentity | hmixed
  · let position := step.targetPair.singletonSharedPosition
    have hsame : pair.suffixSharedEdgeDart position =
        pair.prefixSharedEdgeDart position :=
      pair.suffixSharedEdgeDart_eq_prefixSharedEdgeDart_of_sharedEdgeSignedMonodromy_eq_refl
        hidentity position
    have hmem : pair.sharedEdgeAt position ∈ pair.sharedEdges :=
      pair.sharedEdgeAt_mem_sharedEdges position
    have hlocalized :=
      step.targetRetainedIntersectionProfile_localized
        (pair.sharedEdgeAt position) hmem
    exact Or.inl ⟨pair.toLocalizedStrictlyShorterSameSidePaths
      source.cross source.face position hsame hlocalized.1 hlocalized.2⟩
  · exact Or.inr hmixed

/-- Restore the minimal-counterexample provenance on the strict singleton
descent normal form. -/
theorem CrossCentralExactFaceCertifiedRebaseStep.target_strictlyShorterSameSidePaths_or_strictlyShorterMixedPortCycles
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {source : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    (step : CrossCentralExactFaceCertifiedRebaseStep graphData minimal
      baseData source) :
    let pair := step.target.retainedIntersectionProfile
    Nonempty (LocalizedStrictlyShorterSameSidePaths pair source.1
        step.selectedFace) ∨
      Nonempty (LocalizedStrictlyShorterMixedPortCycles pair source.1
        step.selectedFace) := by
  exact
    step.rebase.target_strictlyShorterSameSidePaths_or_strictlyShorterMixedPortCycles

namespace CrossCentralExactFaceCertifiedRebaseInvolutionCell

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

/-- Forward motion in an involution cell strictly shortens into either the
same-side or mixed-port endpoint pattern. -/
theorem target_strictlyShorterSameSidePaths_or_strictlyShorterMixedPortCycles
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData) :
    let pair := cell.target.retainedIntersectionProfile
    Nonempty (LocalizedStrictlyShorterSameSidePaths pair cell.source.1
        cell.face) ∨
      Nonempty (LocalizedStrictlyShorterMixedPortCycles pair cell.source.1
        cell.face) := by
  rcases cell.forward with ⟨step, htarget, hface⟩
  rw [← htarget, ← hface]
  exact
    step.target_strictlyShorterSameSidePaths_or_strictlyShorterMixedPortCycles

/-- Reverse motion supplies the symmetric strict shortening at the source. -/
theorem source_strictlyShorterSameSidePaths_or_strictlyShorterMixedPortCycles
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData) :
    let pair := cell.source.retainedIntersectionProfile
    Nonempty (LocalizedStrictlyShorterSameSidePaths pair cell.target.1
        cell.face) ∨
      Nonempty (LocalizedStrictlyShorterMixedPortCycles pair cell.target.1
        cell.face) := by
  rcases cell.backward with ⟨step, htarget, hface⟩
  rw [← htarget, ← hface]
  exact
    step.target_strictlyShorterSameSidePaths_or_strictlyShorterMixedPortCycles

/-- Both endpoints of an involution cell therefore carry explicit strict
path-length descent, with only the endpoint pairing left to distinguish. -/
theorem endpoint_strictDescent_normalForm
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData) :
    (let pair := cell.source.retainedIntersectionProfile;
      Nonempty (LocalizedStrictlyShorterSameSidePaths pair cell.target.1
          cell.face) ∨
        Nonempty (LocalizedStrictlyShorterMixedPortCycles pair cell.target.1
          cell.face)) ∧
      (let pair := cell.target.retainedIntersectionProfile;
        Nonempty (LocalizedStrictlyShorterSameSidePaths pair cell.source.1
            cell.face) ∨
          Nonempty (LocalizedStrictlyShorterMixedPortCycles pair cell.source.1
            cell.face)) :=
  ⟨cell.source_strictlyShorterSameSidePaths_or_strictlyShorterMixedPortCycles,
    cell.target_strictlyShorterSameSidePaths_or_strictlyShorterMixedPortCycles⟩

end CrossCentralExactFaceCertifiedRebaseInvolutionCell

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
