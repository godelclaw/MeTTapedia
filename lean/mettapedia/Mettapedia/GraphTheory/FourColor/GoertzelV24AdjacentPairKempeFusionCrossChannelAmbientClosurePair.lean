import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCrossChannelSuffixSplice

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open SimpleGraph

namespace GoertzelV24AdjacentPairBoundary.AdjacentPairData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- The three-edge return from port `3` to port `1` through the deleted
adjacent pair. -/
def alternateOppositePortCentralReturn (data : AdjacentPairData G) :
    G.Walk (data.portVertex 3) (data.portVertex 1) :=
  SimpleGraph.Walk.cons data.second_adj_port_three.symm
    (SimpleGraph.Walk.cons data.centralAdjacent.symm
      (SimpleGraph.Walk.cons data.first_adj_port_one
        SimpleGraph.Walk.nil))

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem alternateOppositePortCentralReturn_length
    (data : AdjacentPairData G) :
    data.alternateOppositePortCentralReturn.length = 3 := by
  simp [alternateOppositePortCentralReturn]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem alternateOppositePortCentralReturn_isPath
    (data : AdjacentPairData G) :
    data.alternateOppositePortCentralReturn.IsPath := by
  rw [alternateOppositePortCentralReturn,
    SimpleGraph.Walk.cons_isPath_iff]
  constructor
  · rw [SimpleGraph.Walk.cons_isPath_iff]
    constructor
    · rw [SimpleGraph.Walk.cons_isPath_iff]
      exact ⟨SimpleGraph.Walk.IsPath.nil, by
        simpa using (data.portNeFirst 1).symm⟩
    · simp only [SimpleGraph.Walk.support_cons,
        SimpleGraph.Walk.support_nil, List.mem_cons,
        List.not_mem_nil, or_false, not_or]
      exact ⟨data.centralAdjacent.ne.symm,
        (data.portNeSecond 1).symm⟩
  · simp only [SimpleGraph.Walk.support_cons,
      SimpleGraph.Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false, not_or]
    exact ⟨data.portNeSecond 3, data.portNeFirst 3,
      data.portVertex_ne (by decide : (3 : Fin 4) ≠ 1)⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem alternateOppositePortCentralReturn_edges
    (data : AdjacentPairData G) :
    data.alternateOppositePortCentralReturn.edges =
      [boundaryEdgeValue data 3, centralEdgeValue data,
        boundaryEdgeValue data 1] := by
  simp [alternateOppositePortCentralReturn,
    GoertzelV24AdjacentPairInsertion.AdjacentPairData.centralEdgeValue,
    Sym2.eq_swap]

/-- Endpoint-aligned form of the alternate return for appending to a walk
whose endpoints are retained-vertex subtypes. -/
def alternateOppositePortCentralReturnRetained
    (data : AdjacentPairData G) :
    G.Walk (data.retainedPort 3).1 (data.retainedPort 1).1 :=
  data.alternateOppositePortCentralReturn.copy rfl rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem alternateOppositePortCentralReturnRetained_edges
    (data : AdjacentPairData G) :
    data.alternateOppositePortCentralReturnRetained.edges =
      data.alternateOppositePortCentralReturn.edges := by
  simp [alternateOppositePortCentralReturnRetained]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem alternateOppositePortCentralReturnRetained_isPath
    (data : AdjacentPairData G) :
    data.alternateOppositePortCentralReturnRetained.IsPath := by
  simpa only [alternateOppositePortCentralReturnRetained,
    SimpleGraph.Walk.isPath_copy] using
      data.alternateOppositePortCentralReturn_isPath

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Every retained walk is edge-disjoint from the alternate restored
three-edge return. -/
theorem retainedWalkToAmbient_edges_disjoint_alternateOppositePortCentralReturn
    (data : AdjacentPairData G)
    {left right : retainedVertexSet data.firstVertex data.secondVertex}
    (walk : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk left right) :
    (data.retainedWalkToAmbient walk).edges.Disjoint
      data.alternateOppositePortCentralReturn.edges := by
  rw [List.disjoint_left]
  intro edge hretained hreturn
  rw [data.alternateOppositePortCentralReturn_edges] at hreturn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hreturn
  rcases hreturn with hthree | hcentral | hone
  · subst edge
    exact data.boundaryEdgeValue_not_mem_retainedWalkToAmbient_edges
      walk 3 hretained
  · subst edge
    exact data.centralEdgeValue_not_mem_retainedWalkToAmbient_edges
      walk hretained
  · subst edge
    exact data.boundaryEdgeValue_not_mem_retainedWalkToAmbient_edges
      walk 1 hretained

/-- Close a retained trail from port `1` to port `3` through the deleted
adjacent pair. -/
def alternateOppositePortClosure (data : AdjacentPairData G)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 1) (data.retainedPort 3)) :
    G.Walk (data.retainedPort 1).1 (data.retainedPort 1).1 :=
  (data.retainedWalkToAmbient path).append
    data.alternateOppositePortCentralReturnRetained

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem alternateOppositePortClosure_isTrail
    (data : AdjacentPairData G)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 1) (data.retainedPort 3))
    (hpath : path.IsTrail) :
    (data.alternateOppositePortClosure path).IsTrail := by
  change ((data.retainedWalkToAmbient path).append
    data.alternateOppositePortCentralReturnRetained).IsTrail
  exact (SimpleGraph.Walk.isTrail_append
    (data.retainedWalkToAmbient path)
      data.alternateOppositePortCentralReturnRetained).2
    ⟨data.retainedWalkToAmbient_isTrail hpath,
      data.alternateOppositePortCentralReturnRetained_isPath.isTrail,
      by
        rw [data.alternateOppositePortCentralReturnRetained_edges]
        exact
          data.retainedWalkToAmbient_edges_disjoint_alternateOppositePortCentralReturn
            path⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The alternate closure contains its restored central edge. -/
theorem centralEdgeValue_mem_alternateOppositePortClosure_edges
    (data : AdjacentPairData G)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 1) (data.retainedPort 3)) :
    centralEdgeValue data ∈
      (data.alternateOppositePortClosure path).edges := by
  have hreturn : centralEdgeValue data ∈
      data.alternateOppositePortCentralReturnRetained.edges := by
    rw [data.alternateOppositePortCentralReturnRetained_edges]
    rw [data.alternateOppositePortCentralReturn_edges]
    simp
  rw [alternateOppositePortClosure, SimpleGraph.Walk.edges_append]
  exact List.mem_append_right _ hreturn

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The two restored three-edge returns share exactly the central edge. -/
theorem mem_oppositePortCentralReturns_iff_eq_centralEdgeValue
    (data : AdjacentPairData G) (edge : Sym2 V) :
    edge ∈ data.oppositePortCentralReturn.edges ∧
        edge ∈ data.alternateOppositePortCentralReturnRetained.edges ↔
      edge = centralEdgeValue data := by
  rw [data.oppositePortCentralReturn_edges,
    data.alternateOppositePortCentralReturnRetained_edges,
    data.alternateOppositePortCentralReturn_edges]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨htwo | hcentral | hzero, hthree | hcentral' | hone⟩
    · exact False.elim
        (GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryEdgeValue_ne
          data (by decide : (2 : Fin 4) ≠ 3)
          (htwo.symm.trans hthree))
    · exact False.elim
        (GoertzelV24AdjacentPairInsertion.AdjacentPairData.centralEdgeValue_ne_boundaryEdgeValue
          data 2
          (hcentral'.symm.trans htwo))
    · exact False.elim
        (GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryEdgeValue_ne
          data (by decide : (2 : Fin 4) ≠ 1)
          (htwo.symm.trans hone))
    · exact hcentral
    · exact hcentral
    · exact hcentral
    · exact False.elim
        (GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryEdgeValue_ne
          data (by decide : (0 : Fin 4) ≠ 3)
          (hzero.symm.trans hthree))
    · exact False.elim
        (GoertzelV24AdjacentPairInsertion.AdjacentPairData.centralEdgeValue_ne_boundaryEdgeValue
          data 0
          (hcentral'.symm.trans hzero))
    · exact False.elim
        (GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryEdgeValue_ne
          data (by decide : (0 : Fin 4) ≠ 1)
          (hzero.symm.trans hone))
  · intro hedge
    subst edge
    exact ⟨Or.inr (Or.inl rfl), Or.inr (Or.inl rfl)⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Exact intersection of two retained edge lists is preserved by inclusion
into the ambient graph. -/
theorem mem_both_retainedWalkToAmbient_edges_iff_of_exact
    (data : AdjacentPairData G)
    (prefixPath : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2))
    (suffixPath : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 1) (data.retainedPort 3))
    (shared : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (hexact : ∀ edge : Sym2 (retainedVertexSet data.firstVertex
        data.secondVertex),
      edge ∈ prefixPath.edges ∧ edge ∈ suffixPath.edges ↔
        edge = shared.1)
    (edge : Sym2 V) :
    edge ∈ (data.retainedWalkToAmbient prefixPath).edges ∧
        edge ∈ (data.retainedWalkToAmbient suffixPath).edges ↔
      edge = (retainedEdgeToAmbientEdge data shared).1 := by
  constructor
  · rintro ⟨hprefix, hsuffix⟩
    rw [GoertzelV24AdjacentPairBoundary.AdjacentPairData.retainedWalkToAmbient,
      SimpleGraph.Walk.edges_map] at hprefix hsuffix
    rcases List.mem_map.mp hprefix with
      ⟨prefixSource, hprefixSource, hprefixValue⟩
    rcases List.mem_map.mp hsuffix with
      ⟨suffixSource, hsuffixSource, hsuffixValue⟩
    have hsources : prefixSource = suffixSource :=
      Sym2.map.injective Subtype.val_injective
        (hprefixValue.trans hsuffixValue.symm)
    subst suffixSource
    have hshared := (hexact prefixSource).1
      ⟨hprefixSource, hsuffixSource⟩
    rw [GoertzelV24AdjacentPairInsertion.AdjacentPairData.retainedEdgeToAmbientEdge_val]
    exact hprefixValue.symm.trans
      (congrArg (Sym2.map Subtype.val) hshared)
  · intro hedge
    subst edge
    have hshared := (hexact shared.1).2 rfl
    exact ⟨
      (GoertzelV24AdjacentPairInsertion.AdjacentPairData.retainedEdgeToAmbientEdge_mem_retainedWalkToAmbient_edges_iff
        data prefixPath shared).2 hshared.1,
      (GoertzelV24AdjacentPairInsertion.AdjacentPairData.retainedEdgeToAmbientEdge_mem_retainedWalkToAmbient_edges_iff
        data suffixPath shared).2 hshared.2⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Closing two exact complementary retained trails through the deleted
adjacent pair adds exactly one common edge: the restored central edge. -/
theorem mem_both_oppositePortClosures_iff_of_exact_retained_intersection
    (data : AdjacentPairData G)
    (prefixPath : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2))
    (suffixPath : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 1) (data.retainedPort 3))
    (shared : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (hexact : ∀ retainedEdge : Sym2 (retainedVertexSet data.firstVertex
        data.secondVertex),
      retainedEdge ∈ prefixPath.edges ∧ retainedEdge ∈ suffixPath.edges ↔
        retainedEdge = shared.1)
    (edge : Sym2 V) :
    edge ∈ (data.oppositePortClosure prefixPath).edges ∧
        edge ∈ (data.alternateOppositePortClosure suffixPath).edges ↔
      edge = (retainedEdgeToAmbientEdge data shared).1 ∨
        edge = centralEdgeValue data := by
  constructor
  · rintro ⟨hprefixClosure, hsuffixClosure⟩
    change edge ∈ ((data.retainedWalkToAmbient prefixPath).append
      data.oppositePortCentralReturn).edges at hprefixClosure
    change edge ∈ ((data.retainedWalkToAmbient suffixPath).append
      data.alternateOppositePortCentralReturnRetained).edges at hsuffixClosure
    rw [SimpleGraph.Walk.edges_append, List.mem_append] at hprefixClosure hsuffixClosure
    rcases hprefixClosure with hprefix | hreturn
    · rcases hsuffixClosure with hsuffix | haltReturn
      · exact Or.inl
          ((data.mem_both_retainedWalkToAmbient_edges_iff_of_exact
            prefixPath suffixPath shared hexact edge).1 ⟨hprefix, hsuffix⟩)
      · rw [data.alternateOppositePortCentralReturnRetained_edges] at haltReturn
        have hdisjoint :=
          data.retainedWalkToAmbient_edges_disjoint_alternateOppositePortCentralReturn
            prefixPath
        rw [List.disjoint_left] at hdisjoint
        exact False.elim (hdisjoint hprefix haltReturn)
    · rcases hsuffixClosure with hsuffix | haltReturn
      · have hdisjoint :=
          data.retainedWalkToAmbient_edges_disjoint_oppositePortCentralReturn
            suffixPath
        rw [List.disjoint_left] at hdisjoint
        exact False.elim (hdisjoint hsuffix hreturn)
      · exact Or.inr
          ((data.mem_oppositePortCentralReturns_iff_eq_centralEdgeValue
            edge).1 ⟨hreturn, haltReturn⟩)
  · rintro (hshared | hcentral)
    · subst edge
      have hmapped :=
        (data.mem_both_retainedWalkToAmbient_edges_iff_of_exact
          prefixPath suffixPath shared hexact
            (retainedEdgeToAmbientEdge data shared).1).2 rfl
      constructor
      · change (retainedEdgeToAmbientEdge data shared).1 ∈
          ((data.retainedWalkToAmbient prefixPath).append
            data.oppositePortCentralReturn).edges
        rw [SimpleGraph.Walk.edges_append, List.mem_append]
        exact Or.inl hmapped.1
      · change (retainedEdgeToAmbientEdge data shared).1 ∈
          ((data.retainedWalkToAmbient suffixPath).append
            data.alternateOppositePortCentralReturnRetained).edges
        rw [SimpleGraph.Walk.edges_append, List.mem_append]
        exact Or.inl hmapped.2
    · subst edge
      exact ⟨data.centralEdgeValue_mem_oppositePortClosure_edges prefixPath,
        data.centralEdgeValue_mem_alternateOppositePortClosure_edges
          suffixPath⟩

end

end GoertzelV24AdjacentPairBoundary.AdjacentPairData

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- A rejected unique `bc` cross state yields two ambient closed trails whose
exact common edge set consists of the selected retained cross edge and the
restored central edge. -/
theorem EvenKempeFusionLens.exists_bcExactAmbientClosurePair_of_rejected
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hdata : data.degreeTwoBoundaryData.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support)
    (hcount : (lens01.bcCrossSites lens23).length ≤ 1)
    (site : lens01.bRoute.CrossSite lens23.cRoute)
    (hfalse : EvenKempeFusionLens.bcCrossExitFaceTransferBit
      lens01 graphData lens23 hab hac hbc site = false) :
    ∃ (prefixTrail : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk
            (data.retainedPort 0) (data.retainedPort 2))
        (suffixTrail : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk
            (data.retainedPort 1) (data.retainedPort 3)),
      (data.oppositePortClosure prefixTrail).IsTrail ∧
        (data.alternateOppositePortClosure suffixTrail).IsTrail ∧
        (retainedEdgeToAmbientEdge data site.1).1 ≠ centralEdgeValue data ∧
        (∀ edge : Sym2 V,
          edge ∈ (data.oppositePortClosure prefixTrail).edges ∧
              edge ∈ (data.alternateOppositePortClosure suffixTrail).edges ↔
            edge = (retainedEdgeToAmbientEdge data site.1).1 ∨
              edge = centralEdgeValue data) := by
  rcases EvenKempeFusionLens.exists_bcExactCrossTrailPair_of_rejected
      graphData data lens01 lens23 hdata hab hac hbc hbDisjoint hcDisjoint
        hcount site hfalse with
    ⟨prefixTrail, suffixTrail, hprefixTrail, hsuffixTrail,
      _hprefixPositive, _hsuffixPositive, _hprefixEdges, _hsuffixEdges,
      hexact⟩
  refine ⟨prefixTrail, suffixTrail,
    data.oppositePortClosure_isTrail prefixTrail hprefixTrail,
    data.alternateOppositePortClosure_isTrail suffixTrail hsuffixTrail, ?_, ?_⟩
  · intro hedge
    exact retainedEdgeToAmbientEdge_ne_centralEdge data site.1
      (Subtype.ext hedge)
  · intro edge
    exact
      data.mem_both_oppositePortClosures_iff_of_exact_retained_intersection
        prefixTrail suffixTrail site.1 hexact edge

/-- The symmetric rejected unique `cb` cross state yields the same exact
two-edge intersection profile for its two ambient closed trails. -/
theorem EvenKempeFusionLens.exists_cbExactAmbientClosurePair_of_rejected
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hdata : data.degreeTwoBoundaryData.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support)
    (hcount : (lens01.cbCrossSites lens23).length ≤ 1)
    (site : lens01.cRoute.CrossSite lens23.bRoute)
    (hfalse : EvenKempeFusionLens.cbCrossExitFaceTransferBit
      lens01 graphData lens23 hab hac hbc site = false) :
    ∃ (prefixTrail : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk
            (data.retainedPort 0) (data.retainedPort 2))
        (suffixTrail : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk
            (data.retainedPort 1) (data.retainedPort 3)),
      (data.oppositePortClosure prefixTrail).IsTrail ∧
        (data.alternateOppositePortClosure suffixTrail).IsTrail ∧
        (retainedEdgeToAmbientEdge data site.1).1 ≠ centralEdgeValue data ∧
        (∀ edge : Sym2 V,
          edge ∈ (data.oppositePortClosure prefixTrail).edges ∧
              edge ∈ (data.alternateOppositePortClosure suffixTrail).edges ↔
            edge = (retainedEdgeToAmbientEdge data site.1).1 ∨
              edge = centralEdgeValue data) := by
  rcases EvenKempeFusionLens.exists_cbExactCrossTrailPair_of_rejected
      graphData data lens01 lens23 hdata hab hac hbc hbDisjoint hcDisjoint
        hcount site hfalse with
    ⟨prefixTrail, suffixTrail, hprefixTrail, hsuffixTrail,
      _hprefixPositive, _hsuffixPositive, _hprefixEdges, _hsuffixEdges,
      hexact⟩
  refine ⟨prefixTrail, suffixTrail,
    data.oppositePortClosure_isTrail prefixTrail hprefixTrail,
    data.alternateOppositePortClosure_isTrail suffixTrail hsuffixTrail, ?_, ?_⟩
  · intro hedge
    exact retainedEdgeToAmbientEdge_ne_centralEdge data site.1
      (Subtype.ext hedge)
  · intro edge
    exact
      data.mem_both_oppositePortClosures_iff_of_exact_retained_intersection
        prefixTrail suffixTrail site.1 hexact edge

end

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
