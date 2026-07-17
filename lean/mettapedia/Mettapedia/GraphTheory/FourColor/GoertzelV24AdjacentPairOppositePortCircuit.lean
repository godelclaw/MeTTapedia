import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCrossChannelOutcome

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24AdjacentPairBoundary
open GoertzelV24FourDefectBoundary

namespace GoertzelV24AdjacentPairBoundary.AdjacentPairData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- The three-edge return from port `2` to port `0` through the deleted
adjacent pair. -/
def oppositePortCentralReturn (data : AdjacentPairData G) :
    G.Walk (data.portVertex 2) (data.portVertex 0) :=
  SimpleGraph.Walk.cons data.second_adj_port_two.symm
    (SimpleGraph.Walk.cons data.centralAdjacent.symm
      (SimpleGraph.Walk.cons data.first_adj_port_zero
        SimpleGraph.Walk.nil))

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem oppositePortCentralReturn_length
    (data : AdjacentPairData G) :
    data.oppositePortCentralReturn.length = 3 := by
  simp [oppositePortCentralReturn]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem oppositePortCentralReturn_isPath
    (data : AdjacentPairData G) :
    data.oppositePortCentralReturn.IsPath := by
  rw [oppositePortCentralReturn,
    SimpleGraph.Walk.cons_isPath_iff]
  constructor
  · rw [SimpleGraph.Walk.cons_isPath_iff]
    constructor
    · rw [SimpleGraph.Walk.cons_isPath_iff]
      exact ⟨SimpleGraph.Walk.IsPath.nil, by
        simpa using (data.portNeFirst 0).symm⟩
    · simp only [SimpleGraph.Walk.support_cons,
        SimpleGraph.Walk.support_nil, List.mem_cons,
        List.not_mem_nil, or_false, not_or]
      exact ⟨data.centralAdjacent.ne.symm,
        (data.portNeSecond 0).symm⟩
  · simp only [SimpleGraph.Walk.support_cons,
      SimpleGraph.Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false, not_or]
    exact ⟨data.portNeSecond 2, data.portNeFirst 2,
      data.portVertex_ne (by decide : (2 : Fin 4) ≠ 0)⟩

/-- The transparent inclusion of the retained induced graph into the
ambient graph. -/
abbrev retainedGraphHom (data : AdjacentPairData G) :
    DeletedAdjacentPairGraph G data.firstVertex data.secondVertex →g G where
  toFun := Subtype.val
  map_rel' := fun {_ _} hedge ↦ hedge

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem retainedGraphHom_apply (data : AdjacentPairData G)
    (vertex : retainedVertexSet data.firstVertex data.secondVertex) :
    data.retainedGraphHom vertex = vertex.1 := rfl

/-- Map a walk in the induced adjacent-pair deletion back to the ambient
graph. -/
def retainedWalkToAmbient (data : AdjacentPairData G)
    {left right : retainedVertexSet data.firstVertex data.secondVertex}
    (walk : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk left right) :
    G.Walk left.1 right.1 :=
  walk.map data.retainedGraphHom

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem retainedWalkToAmbient_isPath
    (data : AdjacentPairData G)
    {left right : retainedVertexSet data.firstVertex data.secondVertex}
    {walk : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk left right}
    (hwalk : walk.IsPath) :
    (data.retainedWalkToAmbient walk).IsPath := by
  exact SimpleGraph.Walk.map_isPath_of_injective
    Subtype.val_injective hwalk

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Mapping into the ambient graph also preserves the weaker no-repeated-edge
condition. -/
theorem retainedWalkToAmbient_isTrail
    (data : AdjacentPairData G)
    {left right : retainedVertexSet data.firstVertex data.secondVertex}
    {walk : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk left right}
    (hwalk : walk.IsTrail) :
    (data.retainedWalkToAmbient walk).IsTrail := by
  exact SimpleGraph.Walk.map_isTrail_of_injective
    Subtype.val_injective hwalk

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- No restored boundary edge can occur in a walk mapped from the retained
induced graph. -/
theorem boundaryEdgeValue_not_mem_retainedWalkToAmbient_edges
    (data : AdjacentPairData G)
    {left right : retainedVertexSet data.firstVertex data.secondVertex}
    (walk : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk left right)
    (port : Fin 4) :
    GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryEdgeValue
        data port ∉ (data.retainedWalkToAmbient walk).edges := by
  intro hmem
  rw [retainedWalkToAmbient, SimpleGraph.Walk.edges_map] at hmem
  rcases List.mem_map.mp hmem with ⟨edge, _hedge, hedgeValue⟩
  have hdeletedMem :
      GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryDeletedVertex
          data port ∈ edge.map data.retainedGraphHom := by
    rw [hedgeValue]
    rw [GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryEdgeValue_eq]
    simp
  rcases Sym2.mem_map.mp hdeletedMem with
    ⟨retained, _hretainedMem, hvalue⟩
  fin_cases port
  · change retained.1 = data.firstVertex at hvalue
    exact retained.2.1 hvalue
  · change retained.1 = data.firstVertex at hvalue
    exact retained.2.1 hvalue
  · change retained.1 = data.secondVertex at hvalue
    exact retained.2.2 hvalue
  · change retained.1 = data.secondVertex at hvalue
    exact retained.2.2 hvalue

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The central restored edge cannot occur in a walk mapped from the retained
induced graph. -/
theorem centralEdgeValue_not_mem_retainedWalkToAmbient_edges
    (data : AdjacentPairData G)
    {left right : retainedVertexSet data.firstVertex data.secondVertex}
    (walk : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk left right) :
    GoertzelV24AdjacentPairInsertion.AdjacentPairData.centralEdgeValue data ∉
      (data.retainedWalkToAmbient walk).edges := by
  intro hmem
  rw [retainedWalkToAmbient, SimpleGraph.Walk.edges_map] at hmem
  rcases List.mem_map.mp hmem with ⟨edge, _hedge, hedgeValue⟩
  have hdeletedMem : data.firstVertex ∈ edge.map data.retainedGraphHom := by
    rw [hedgeValue]
    change data.firstVertex ∈ s(data.firstVertex, data.secondVertex)
    simp
  rcases Sym2.mem_map.mp hdeletedMem with
    ⟨retained, _hretainedMem, hvalue⟩
  change retained.1 = data.firstVertex at hvalue
  exact retained.2.1 hvalue

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The central return uses boundary ports `2` and `0`, with the central edge
between them. -/
theorem oppositePortCentralReturn_edges
    (data : AdjacentPairData G) :
    data.oppositePortCentralReturn.edges =
      [GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryEdgeValue
          data 2,
        GoertzelV24AdjacentPairInsertion.AdjacentPairData.centralEdgeValue data,
        GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryEdgeValue
          data 0] := by
  simp [oppositePortCentralReturn,
    GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryEdgeValue,
    GoertzelV24AdjacentPairInsertion.AdjacentPairData.centralEdgeValue,
    Sym2.eq_swap]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Every retained walk is edge-disjoint from the restored three-edge
central return. -/
theorem retainedWalkToAmbient_edges_disjoint_oppositePortCentralReturn
    (data : AdjacentPairData G)
    {left right : retainedVertexSet data.firstVertex data.secondVertex}
    (walk : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk left right) :
    (data.retainedWalkToAmbient walk).edges.Disjoint
      data.oppositePortCentralReturn.edges := by
  rw [List.disjoint_left]
  intro edge hretained hreturn
  rw [data.oppositePortCentralReturn_edges] at hreturn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hreturn
  rcases hreturn with htwo | hcentral | hzero
  · subst edge
    exact data.boundaryEdgeValue_not_mem_retainedWalkToAmbient_edges
      walk 2 hretained
  · subst edge
    exact data.centralEdgeValue_not_mem_retainedWalkToAmbient_edges
      walk hretained
  · subst edge
    exact data.boundaryEdgeValue_not_mem_retainedWalkToAmbient_edges
      walk 0 hretained

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Among the four restored boundary edges, the central return uses exactly
the opposite pair `0,2`. -/
theorem boundaryEdgeValue_mem_oppositePortCentralReturn_edges_iff
    (data : AdjacentPairData G) (port : Fin 4) :
    GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryEdgeValue
        data port ∈ data.oppositePortCentralReturn.edges ↔
      port = 0 ∨ port = 2 := by
  rw [data.oppositePortCentralReturn_edges]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · intro hmem
    rcases hmem with htwo | hcentral | hzero
    · exact Or.inr
        (GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryEdgeValue_injective
          data htwo)
    · exact False.elim
        (GoertzelV24AdjacentPairInsertion.AdjacentPairData.centralEdgeValue_ne_boundaryEdgeValue
          data port hcentral.symm)
    · exact Or.inl
        (GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryEdgeValue_injective
          data hzero)
  · intro hport
    rcases hport with rfl | rfl
    · exact Or.inr (Or.inr rfl)
    · exact Or.inl rfl

/-- Close a retained path from port `0` to port `2` through the central
adjacent pair. -/
def oppositePortClosure (data : AdjacentPairData G)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2)) :
    G.Walk (data.portVertex 0) (data.portVertex 0) :=
  (data.retainedWalkToAmbient path).append data.oppositePortCentralReturn

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A retained trail between opposite ports closes through the deleted pair
to an ambient closed trail. Unlike simplicity, the trail condition is stable
under the sparse cross-splice constructions used below. -/
theorem oppositePortClosure_isTrail
    (data : AdjacentPairData G)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2))
    (hpath : path.IsTrail) :
    (data.oppositePortClosure path).IsTrail := by
  change ((data.retainedWalkToAmbient path).append
    data.oppositePortCentralReturn).IsTrail
  exact (SimpleGraph.Walk.isTrail_append
    (data.retainedWalkToAmbient path) data.oppositePortCentralReturn).2
      ⟨data.retainedWalkToAmbient_isTrail hpath,
        data.oppositePortCentralReturn_isPath.isTrail,
        data.retainedWalkToAmbient_edges_disjoint_oppositePortCentralReturn
          path⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The opposite-port closure contains exactly boundary edges `0` and `2`;
its retained arc contains none of the restored boundary edges. -/
theorem boundaryEdgeValue_mem_oppositePortClosure_edges_iff
    (data : AdjacentPairData G)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2))
    (port : Fin 4) :
    GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryEdgeValue
        data port ∈ (data.oppositePortClosure path).edges ↔
      port = 0 ∨ port = 2 := by
  change GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryEdgeValue
      data port ∈
      ((data.retainedWalkToAmbient path).append
        data.oppositePortCentralReturn).edges ↔ port = 0 ∨ port = 2
  rw [SimpleGraph.Walk.edges_append, List.mem_append]
  constructor
  · intro hmem
    rcases hmem with hretained | hreturn
    · exact False.elim
        (data.boundaryEdgeValue_not_mem_retainedWalkToAmbient_edges
          path port hretained)
    · exact (data.boundaryEdgeValue_mem_oppositePortCentralReturn_edges_iff
        port).1 hreturn
  · intro hport
    exact Or.inr
      ((data.boundaryEdgeValue_mem_oppositePortCentralReturn_edges_iff
        port).2 hport)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A simple retained path between opposite ports closes through the
deleted pair to a simple ambient cycle. -/
theorem oppositePortClosure_isCycle
    (data : AdjacentPairData G)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2))
    (hpath : path.IsPath) :
    (data.oppositePortClosure path).IsCycle := by
  have hambientPath : (data.retainedWalkToAmbient path).IsPath :=
    data.retainedWalkToAmbient_isPath hpath
  have hreturnPath : data.oppositePortCentralReturn.IsPath :=
    data.oppositePortCentralReturn_isPath
  have hstartNotAmbientTail : data.portVertex 0 ∉
      (data.retainedWalkToAmbient path).support.tail := by
    have hnodup := hambientPath.support_nodup
    rw [← (data.retainedWalkToAmbient path).cons_tail_support] at hnodup
    exact (List.nodup_cons.mp hnodup).1
  have hdisjoint :
      (data.retainedWalkToAmbient path).support.tail.Disjoint
        data.oppositePortCentralReturn.support.tail := by
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
    simp only [oppositePortCentralReturn,
      SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at hreturn
    rcases hreturn with hsecond | hfirst | hzero
    · exact retained.2.2 hsecond
    · exact retained.2.1 hfirst
    · exact hstartNotAmbientTail (hzero ▸ hambient)
  apply hambientPath.isCycle_append hreturnPath hdisjoint
  exact Or.inr (by
    change 1 < 3
    omega)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Loop erasure preserves the retained edge support while producing the
simple path used by the ambient closure. -/
theorem exists_oppositePortClosure_isCycle_with_edges_subset
    (data : AdjacentPairData G)
    (walk : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2)) :
    ∃ path : (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2),
      path.IsPath ∧ (data.oppositePortClosure path).IsCycle ∧
        path.edges ⊆ walk.edges := by
  let path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2) :=
    walk.toPath
  refine ⟨path, ?_, ?_, ?_⟩
  · exact SimpleGraph.Path.isPath walk.toPath
  · exact data.oppositePortClosure_isCycle path
      (SimpleGraph.Path.isPath walk.toPath)
  · dsimp only [path]
    exact walk.edges_toPath_subset_edges

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Every retained walk between ports `0` and `2` contains a simple path,
and hence determines an ambient cycle through the deleted adjacent pair. -/
theorem exists_oppositePortClosure_isCycle
    (data : AdjacentPairData G)
    (walk : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2)) :
    ∃ path : (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2),
      path.IsPath ∧ (data.oppositePortClosure path).IsCycle := by
  rcases data.exists_oppositePortClosure_isCycle_with_edges_subset walk with
    ⟨path, hpath, hcycle, _hsubset⟩
  exact ⟨path, hpath, hcycle⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The ambient closure contains both restored central vertices. -/
theorem firstVertex_mem_oppositePortClosure_support
    (data : AdjacentPairData G)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2)) :
    data.firstVertex ∈ (data.oppositePortClosure path).support := by
  apply (SimpleGraph.Walk.mem_support_append_iff
    (data.retainedWalkToAmbient path) data.oppositePortCentralReturn).2
  apply Or.inr
  change data.firstVertex ∈ [data.portVertex 2, data.secondVertex,
    data.firstVertex, data.portVertex 0]
  simp

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem secondVertex_mem_oppositePortClosure_support
    (data : AdjacentPairData G)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2)) :
    data.secondVertex ∈ (data.oppositePortClosure path).support := by
  apply (SimpleGraph.Walk.mem_support_append_iff
    (data.retainedWalkToAmbient path) data.oppositePortCentralReturn).2
  apply Or.inr
  change data.secondVertex ∈ [data.portVertex 2, data.secondVertex,
    data.firstVertex, data.portVertex 0]
  simp

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The closure uses the restored central edge. -/
theorem centralEdgeValue_mem_oppositePortClosure_edges
    (data : AdjacentPairData G)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2)) :
    GoertzelV24AdjacentPairInsertion.AdjacentPairData.centralEdgeValue data ∈
      (data.oppositePortClosure path).edges := by
  have hreturn :
      GoertzelV24AdjacentPairInsertion.AdjacentPairData.centralEdgeValue data ∈
        data.oppositePortCentralReturn.edges := by
    change s(data.firstVertex, data.secondVertex) ∈
      [s(data.portVertex 2, data.secondVertex),
        s(data.secondVertex, data.firstVertex),
        s(data.firstVertex, data.portVertex 0)]
    simp [Sym2.eq_swap]
  change GoertzelV24AdjacentPairInsertion.AdjacentPairData.centralEdgeValue data ∈
    ((data.retainedWalkToAmbient path).append
      data.oppositePortCentralReturn).edges
  rw [SimpleGraph.Walk.edges_append]
  exact List.mem_append_right _ hreturn

end


end GoertzelV24AdjacentPairBoundary.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
