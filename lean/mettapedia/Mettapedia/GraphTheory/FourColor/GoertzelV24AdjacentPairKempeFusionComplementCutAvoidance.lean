import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCrossChannelPrimalTrail
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionTerminalTurns
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairOppositePortCircuit

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24FourDefectBoundary
open SimpleGraph

namespace GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance complementCutAvoidanceGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- An edge of the second-color `c` class cannot occur on the `(a,b)`
route when all three colors are distinct. -/
theorem EvenKempeFusionLens.not_mem_bAmbientPath_support_of_color_eq_c
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (hbc : b ≠ c) {edge : G.edgeSet}
    (hcolor : C edge = c) :
    edge ∉ lens.bRoute.ambientPath.support := by
  intro hmem
  rcases (lens.bRoute.mem_ambientPath_support_iff edge).1 hmem |>.1 with
    ha | hb
  · exact hac (ha.symm.trans hcolor)
  · exact hbc (hb.symm.trans hcolor)

/-- Symmetrically, a `b`-colored edge cannot occur on the `(a,c)` route. -/
theorem EvenKempeFusionLens.not_mem_cAmbientPath_support_of_color_eq_b
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hbc : b ≠ c) {edge : G.edgeSet}
    (hcolor : C edge = b) :
    edge ∉ lens.cRoute.ambientPath.support := by
  intro hmem
  rcases (lens.cRoute.mem_ambientPath_support_iff edge).1 hmem |>.1 with
    ha | hc
  · exact hab (ha.symm.trans hcolor)
  · exact hbc (hcolor.symm.trans hc)

/-- Both `c` arms adjacent to a fusion edge are outside the `b` route. -/
theorem EvenKempeFusionLens.cPreviousVertex_not_mem_bAmbientPath_support
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (hbc : b ≠ c) (site : lens.FusionSite) :
    (lens.cPreviousVertex site).1 ∉
      lens.bRoute.ambientPath.support :=
  lens.not_mem_bAmbientPath_support_of_color_eq_c hac hbc
    (lens.cPreviousColor hac site)

theorem EvenKempeFusionLens.cNextVertex_not_mem_bAmbientPath_support
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (hbc : b ≠ c) (site : lens.FusionSite) :
    (lens.cNextVertex site).1 ∉ lens.bRoute.ambientPath.support :=
  lens.not_mem_bAmbientPath_support_of_color_eq_c hac hbc
    (lens.cNextColor hac site)

/-- Both `b` arms adjacent to a fusion edge are outside the `c` route. -/
theorem EvenKempeFusionLens.bPreviousVertex_not_mem_cAmbientPath_support
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hbc : b ≠ c) (site : lens.FusionSite) :
    (lens.bPreviousVertex site).1 ∉
      lens.cRoute.ambientPath.support :=
  lens.not_mem_cAmbientPath_support_of_color_eq_b hab hbc
    (lens.bPreviousColor hab site)

theorem EvenKempeFusionLens.bNextVertex_not_mem_cAmbientPath_support
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hbc : b ≠ c) (site : lens.FusionSite) :
    (lens.bNextVertex site).1 ∉ lens.cRoute.ambientPath.support :=
  lens.not_mem_cAmbientPath_support_of_color_eq_b hab hbc
    (lens.bNextColor hab site)

/-- Every named arm really occurs on its defining route. -/
theorem EvenKempeFusionLens.bPreviousVertex_mem_bAmbientPath_support
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (site : lens.FusionSite) :
    (lens.bPreviousVertex site).1 ∈ lens.bRoute.ambientPath.support := by
  apply (lens.bRoute.mem_ambientPath_support_iff _).2
  exact ⟨(lens.bPreviousVertex site).2,
    lens.bRoute.path.getVert_mem_support _⟩

theorem EvenKempeFusionLens.bNextVertex_mem_bAmbientPath_support
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (site : lens.FusionSite) :
    (lens.bNextVertex site).1 ∈ lens.bRoute.ambientPath.support := by
  apply (lens.bRoute.mem_ambientPath_support_iff _).2
  exact ⟨(lens.bNextVertex site).2,
    lens.bRoute.path.getVert_mem_support _⟩

theorem EvenKempeFusionLens.cPreviousVertex_mem_cAmbientPath_support
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (site : lens.FusionSite) :
    (lens.cPreviousVertex site).1 ∈ lens.cRoute.ambientPath.support := by
  apply (lens.cRoute.mem_ambientPath_support_iff _).2
  exact ⟨(lens.cPreviousVertex site).2,
    lens.cRoute.path.getVert_mem_support _⟩

theorem EvenKempeFusionLens.cNextVertex_mem_cAmbientPath_support
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (site : lens.FusionSite) :
    (lens.cNextVertex site).1 ∈ lens.cRoute.ambientPath.support := by
  apply (lens.cRoute.mem_ambientPath_support_iff _).2
  exact ⟨(lens.cNextVertex site).2,
    lens.cRoute.path.getVert_mem_support _⟩

/-- A trail supported in the `b(0,1)`--`c(2,3)` cross channel cannot use
an edge of the complementary `c(0,1)` route unless that edge also lies on
the first `b` route. -/
theorem EvenKempeFusionLens.c01_not_mem_bcTrail_edges_of_not_mem_b01
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support)
    (trail : G.Walk (data.defectVertex 0) (data.defectVertex 2))
    (hsupport : trail.edges ⊆
      (lens01.bRoute.ambientPath.support ++
        lens23.cRoute.ambientPath.support).map Subtype.val)
    {edge : G.edgeSet}
    (hc01 : edge ∈ lens01.cRoute.ambientPath.support)
    (hb01 : edge ∉ lens01.bRoute.ambientPath.support) :
    edge.1 ∉ trail.edges := by
  intro hedge
  rcases List.mem_map.mp (hsupport hedge) with
    ⟨source, hsource, hvalue⟩
  have hsourceEq : source = edge := Subtype.ext hvalue
  subst source
  rcases List.mem_append.mp hsource with hb | hc
  · exact hb01 hb
  · exact (List.disjoint_left.mp hcDisjoint) hc01 hc

/-- The other complementary route in a `bc` channel is excluded by the
same-family separation on the `b` routes. -/
theorem EvenKempeFusionLens.b23_not_mem_bcTrail_edges_of_not_mem_c23
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (trail : G.Walk (data.defectVertex 0) (data.defectVertex 2))
    (hsupport : trail.edges ⊆
      (lens01.bRoute.ambientPath.support ++
        lens23.cRoute.ambientPath.support).map Subtype.val)
    {edge : G.edgeSet}
    (hb23 : edge ∈ lens23.bRoute.ambientPath.support)
    (hc23 : edge ∉ lens23.cRoute.ambientPath.support) :
    edge.1 ∉ trail.edges := by
  intro hedge
  rcases List.mem_map.mp (hsupport hedge) with
    ⟨source, hsource, hvalue⟩
  have hsourceEq : source = edge := Subtype.ext hvalue
  subst source
  rcases List.mem_append.mp hsource with hb | hc
  · exact (List.disjoint_left.mp hbDisjoint) hb hb23
  · exact hc23 hc

/-- For the complementary `c(0,1)`--`b(2,3)` channel, a first-lens `b`
edge is absent unless it also lies on the first-lens `c` route. -/
theorem EvenKempeFusionLens.b01_not_mem_cbTrail_edges_of_not_mem_c01
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (trail : G.Walk (data.defectVertex 0) (data.defectVertex 2))
    (hsupport : trail.edges ⊆
      (lens01.cRoute.ambientPath.support ++
        lens23.bRoute.ambientPath.support).map Subtype.val)
    {edge : G.edgeSet}
    (hb01 : edge ∈ lens01.bRoute.ambientPath.support)
    (hc01 : edge ∉ lens01.cRoute.ambientPath.support) :
    edge.1 ∉ trail.edges := by
  intro hedge
  rcases List.mem_map.mp (hsupport hedge) with
    ⟨source, hsource, hvalue⟩
  have hsourceEq : source = edge := Subtype.ext hvalue
  subst source
  rcases List.mem_append.mp hsource with hc | hb
  · exact hc01 hc
  · exact (List.disjoint_left.mp hbDisjoint) hb01 hb

/-- The second-lens `c` route is the remaining complement of a `cb`
channel. -/
theorem EvenKempeFusionLens.c23_not_mem_cbTrail_edges_of_not_mem_b23
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support)
    (trail : G.Walk (data.defectVertex 0) (data.defectVertex 2))
    (hsupport : trail.edges ⊆
      (lens01.cRoute.ambientPath.support ++
        lens23.bRoute.ambientPath.support).map Subtype.val)
    {edge : G.edgeSet}
    (hc23 : edge ∈ lens23.cRoute.ambientPath.support)
    (hb23 : edge ∉ lens23.bRoute.ambientPath.support) :
    edge.1 ∉ trail.edges := by
  intro hedge
  rcases List.mem_map.mp (hsupport hedge) with
    ⟨source, hsource, hvalue⟩
  have hsourceEq : source = edge := Subtype.ext hvalue
  subst source
  rcases List.mem_append.mp hsource with hc | hb
  · exact (List.disjoint_left.mp hcDisjoint) hc hc23
  · exact hb23 hb

end

end GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance complementClosureGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A retained edge cannot be the central edge restored through the
deleted adjacent pair. -/
theorem retainedEdgeToAmbientEdge_ne_centralEdge
    (data : AdjacentPairData G)
    (edge : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet) :
    retainedEdgeToAmbientEdge data edge ≠ centralEdge data := by
  intro heq
  have hfirst : data.firstVertex ∈
      ((retainedEdgeToAmbientEdge data edge).1 : Sym2 V) := by
    rw [heq]
    change data.firstVertex ∈
      (GoertzelV24AdjacentPairInsertion.AdjacentPairData.centralEdgeValue
        data : Sym2 V)
    simp [GoertzelV24AdjacentPairInsertion.AdjacentPairData.centralEdgeValue]
  rw [retainedEdgeToAmbientEdge_val] at hfirst
  rcases Sym2.mem_map.mp hfirst with ⟨retained, _hmem, hvalue⟩
  exact retained.2.1 hvalue

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Inclusion into the ambient graph preserves and reflects membership of
retained edges in a walk's edge list. -/
theorem retainedEdgeToAmbientEdge_mem_retainedWalkToAmbient_edges_iff
    (data : AdjacentPairData G)
    {left right : retainedVertexSet data.firstVertex data.secondVertex}
    (walk : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk left right)
    (edge : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet) :
    (retainedEdgeToAmbientEdge data edge).1 ∈
        (data.retainedWalkToAmbient walk).edges ↔
      edge.1 ∈ walk.edges := by
  rw [GoertzelV24AdjacentPairBoundary.AdjacentPairData.retainedWalkToAmbient,
    SimpleGraph.Walk.edges_map]
  change edge.1.map Subtype.val ∈
      walk.edges.map (Sym2.map Subtype.val) ↔ edge.1 ∈ walk.edges
  rw [← List.mem_map_of_injective
    (Sym2.map.injective Subtype.val_injective)]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The three-edge central return is disjoint from every retained edge. -/
theorem retainedEdgeToAmbientEdge_not_mem_oppositePortCentralReturn_edges
    (data : AdjacentPairData G)
    (edge : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet) :
    (retainedEdgeToAmbientEdge data edge).1 ∉
      data.oppositePortCentralReturn.edges := by
  rw [data.oppositePortCentralReturn_edges]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro (htwo | hcentral | hzero)
  · exact retainedEdgeToAmbientEdge_ne_boundaryEdge data edge 2
      (Subtype.ext htwo)
  · exact retainedEdgeToAmbientEdge_ne_centralEdge data edge
      (Subtype.ext hcentral)
  · exact retainedEdgeToAmbientEdge_ne_boundaryEdge data edge 0
      (Subtype.ext hzero)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- For retained edges, membership in an opposite-port closure is exactly
membership in its retained path. The restored three-edge return contributes
no retained edge. -/
theorem retainedEdgeToAmbientEdge_mem_oppositePortClosure_edges_iff
    (data : AdjacentPairData G)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2))
    (edge : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet) :
    (retainedEdgeToAmbientEdge data edge).1 ∈
        (data.oppositePortClosure path).edges ↔
      edge.1 ∈ path.edges := by
  change (retainedEdgeToAmbientEdge data edge).1 ∈
      ((data.retainedWalkToAmbient path).append
        data.oppositePortCentralReturn).edges ↔ edge.1 ∈ path.edges
  rw [SimpleGraph.Walk.edges_append, List.mem_append]
  constructor
  · rintro (hpath | hreturn)
    · exact (retainedEdgeToAmbientEdge_mem_retainedWalkToAmbient_edges_iff
        data
        path edge).1 hpath
    · exact False.elim
        (retainedEdgeToAmbientEdge_not_mem_oppositePortCentralReturn_edges
          data edge hreturn)
  · intro hpath
    exact Or.inl
      ((retainedEdgeToAmbientEdge_mem_retainedWalkToAmbient_edges_iff data
        path edge).2 hpath)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- If a retained path is supported in a specified line-edge list, then no
other retained edge can enter its ambient opposite-port closure through the
restored central return. -/
theorem retainedEdgeToAmbientEdge_mem_support_of_mem_oppositePortClosure_edges
    (data : AdjacentPairData G)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2))
    (support : List (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (hsupport : path.edges ⊆ support.map Subtype.val)
    (edge : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (hmem : (retainedEdgeToAmbientEdge data edge).1 ∈
      (data.oppositePortClosure path).edges) :
    edge ∈ support := by
  have hpath :=
    (retainedEdgeToAmbientEdge_mem_oppositePortClosure_edges_iff
      data path edge).1 hmem
  rcases List.mem_map.mp (hsupport hpath) with
    ⟨source, hsource, hvalue⟩
  have hsourceEq : source = edge := Subtype.ext hvalue
  simpa only [hsourceEq] using hsource

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Contrapositive support form of the exact retained-edge profile. -/
theorem retainedEdgeToAmbientEdge_not_mem_oppositePortClosure_edges_of_not_mem_support
    (data : AdjacentPairData G)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2))
    (support : List (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (hsupport : path.edges ⊆ support.map Subtype.val)
    (edge : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (hnot : edge ∉ support) :
    (retainedEdgeToAmbientEdge data edge).1 ∉
      (data.oppositePortClosure path).edges := by
  intro hmem
  exact hnot
    (retainedEdgeToAmbientEdge_mem_support_of_mem_oppositePortClosure_edges
      data path support hsupport edge hmem)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Away from one explicitly exceptional retained edge, an opposite-port
closure has exactly the prescribed support.  The forward implication is the
support bound on the retained path; the reverse implication is the certified
coverage supplied by the coherent splice. -/
theorem retainedEdgeToAmbientEdge_mem_oppositePortClosure_edges_iff_mem_support_of_ne
    (data : AdjacentPairData G)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2))
    (support : List (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (exception : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (hsupport : path.edges ⊆ support.map Subtype.val)
    (hcoverage : ∀ edge ∈ support,
      edge = exception ∨
        (retainedEdgeToAmbientEdge data edge).1 ∈
          (data.oppositePortClosure path).edges)
    (edge : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (hne : edge ≠ exception) :
    (retainedEdgeToAmbientEdge data edge).1 ∈
        (data.oppositePortClosure path).edges ↔
      edge ∈ support := by
  constructor
  · exact retainedEdgeToAmbientEdge_mem_support_of_mem_oppositePortClosure_edges
      data path support hsupport edge
  · intro hedge
    rcases hcoverage edge hedge with heq | hmem
    · exact False.elim (hne heq)
    · exact hmem

omit [Fintype V] [DecidableEq V] in
/-- In a singleton `bc` cross channel, both strict route tails after the
selected cross site lie outside every opposite-port closure whose retained
path is supported in the corresponding prefix splice. -/
theorem EvenKempeFusionLens.bcCrossSpliceSuffixes_not_mem_oppositePortClosure_edges
    (data : AdjacentPairData G)
    [retainedFintype : Fintype
      (retainedVertexSet data.firstVertex data.secondVertex)]
    [retainedDecidableEq : DecidableEq
      (retainedVertexSet data.firstVertex data.secondVertex)]
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hcount : (lens01.bcCrossSites lens23).length ≤ 1)
    (site : lens01.bRoute.CrossSite lens23.cRoute)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2))
    (hsupport : path.edges ⊆
      (lens01.bRoute.crossSplice lens23.cRoute site).support.map
        Subtype.val) :
    (∀ edge ∈
        (lens01.bRoute.firstSuffixFromCrossSite
          lens23.cRoute site).support.tail,
      (retainedEdgeToAmbientEdge data edge).1 ∉
        (data.oppositePortClosure path).edges) ∧
      (∀ edge ∈
          (lens01.bRoute.secondSuffixFromCrossSite
            lens23.cRoute site).support.tail,
        (retainedEdgeToAmbientEdge data edge).1 ∉
          (data.oppositePortClosure path).edges) := by
  have hunique : ∀ edge,
      edge ∈ lens01.bRoute.ambientPath.support →
      edge ∈ lens23.cRoute.ambientPath.support → edge = site.1 :=
    lens01.bcCrossSite_eq_of_length_le_one lens23 hcount site
  have hfirstDisjoint :=
    lens01.bRoute.firstSuffix_tail_disjoint_crossSplice_support
      lens23.cRoute site hunique
  have hsecondDisjoint :=
    lens01.bRoute.secondSuffix_tail_disjoint_crossSplice_support
      lens23.cRoute site hunique
  constructor
  · intro edge hedge
    apply retainedEdgeToAmbientEdge_not_mem_oppositePortClosure_edges_of_not_mem_support
      data path (lens01.bRoute.crossSplice lens23.cRoute site).support
        hsupport edge
    intro hsplice
    exact (List.disjoint_left.mp hfirstDisjoint) hedge hsplice
  · intro edge hedge
    apply retainedEdgeToAmbientEdge_not_mem_oppositePortClosure_edges_of_not_mem_support
      data path (lens01.bRoute.crossSplice lens23.cRoute site).support
        hsupport edge
    intro hsplice
    exact (List.disjoint_left.mp hsecondDisjoint) hedge hsplice

omit [Fintype V] [DecidableEq V] in
/-- The complementary singleton `cb` channel has the same exact strict-tail
avoidance profile. -/
theorem EvenKempeFusionLens.cbCrossSpliceSuffixes_not_mem_oppositePortClosure_edges
    (data : AdjacentPairData G)
    [retainedFintype : Fintype
      (retainedVertexSet data.firstVertex data.secondVertex)]
    [retainedDecidableEq : DecidableEq
      (retainedVertexSet data.firstVertex data.secondVertex)]
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hcount : (lens01.cbCrossSites lens23).length ≤ 1)
    (site : lens01.cRoute.CrossSite lens23.bRoute)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2))
    (hsupport : path.edges ⊆
      (lens01.cRoute.crossSplice lens23.bRoute site).support.map
        Subtype.val) :
    (∀ edge ∈
        (lens01.cRoute.firstSuffixFromCrossSite
          lens23.bRoute site).support.tail,
      (retainedEdgeToAmbientEdge data edge).1 ∉
        (data.oppositePortClosure path).edges) ∧
      (∀ edge ∈
          (lens01.cRoute.secondSuffixFromCrossSite
            lens23.bRoute site).support.tail,
        (retainedEdgeToAmbientEdge data edge).1 ∉
          (data.oppositePortClosure path).edges) := by
  have hunique : ∀ edge,
      edge ∈ lens01.cRoute.ambientPath.support →
      edge ∈ lens23.bRoute.ambientPath.support → edge = site.1 :=
    lens01.cbCrossSite_eq_of_length_le_one lens23 hcount site
  have hfirstDisjoint :=
    lens01.cRoute.firstSuffix_tail_disjoint_crossSplice_support
      lens23.bRoute site hunique
  have hsecondDisjoint :=
    lens01.cRoute.secondSuffix_tail_disjoint_crossSplice_support
      lens23.bRoute site hunique
  constructor
  · intro edge hedge
    apply retainedEdgeToAmbientEdge_not_mem_oppositePortClosure_edges_of_not_mem_support
      data path (lens01.cRoute.crossSplice lens23.bRoute site).support
        hsupport edge
    intro hsplice
    exact (List.disjoint_left.mp hfirstDisjoint) hedge hsplice
  · intro edge hedge
    apply retainedEdgeToAmbientEdge_not_mem_oppositePortClosure_edges_of_not_mem_support
      data path (lens01.cRoute.crossSplice lens23.bRoute site).support
        hsupport edge
    intro hsplice
    exact (List.disjoint_left.mp hsecondDisjoint) hedge hsplice

omit [Fintype V] [DecidableEq V] in
/-- A first cross channel supplies an exact closure profile: its selected
splice is contained in the opposite-port closure, with the cross site as
the only possible omission caused by coherent triangle contraction. -/
theorem EvenKempeFusionLens.exists_bcOppositePortClosure_with_crossSpliceCoverage
    (data : AdjacentPairData G)
    [retainedFintype : Fintype
      (retainedVertexSet data.firstVertex data.secondVertex)]
    [retainedDecidableEq : DecidableEq
      (retainedVertexSet data.firstVertex data.secondVertex)]
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
    (hnonempty : lens01.bcCrossSites lens23 ≠ []) :
    ∃ (site : lens01.bRoute.CrossSite lens23.cRoute)
        (path : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk
            (data.retainedPort 0) (data.retainedPort 2)),
      path.IsTrail ∧ 0 < path.length ∧
        path.edges ⊆
          (lens01.bRoute.crossSplice lens23.cRoute site).support.map
            Subtype.val ∧
        path.edges ⊆
          (lens01.bRoute.ambientPath.support ++
            lens23.cRoute.ambientPath.support).map Subtype.val ∧
        (∀ edge ∈
          (lens01.bRoute.crossSplice lens23.cRoute site).support,
          edge = site.1 ∨
            (retainedEdgeToAmbientEdge data edge).1 ∈
              (data.oppositePortClosure path).edges) := by
  rcases lens01.exists_bcPrimalTrail_with_crossSpliceCoverage lens23
      hdata hab hac hbc hbDisjoint hcDisjoint hnonempty with
    ⟨site, path, htrail, hpositive, hspliceSupport, hsupport, hcoverage⟩
  refine ⟨site, path, htrail, hpositive, hspliceSupport, hsupport, ?_⟩
  intro edge hedge
  rcases hcoverage edge hedge with hedgeSite | hedgePath
  · exact Or.inl hedgeSite
  · exact Or.inr
      ((retainedEdgeToAmbientEdge_mem_oppositePortClosure_edges_iff
        data path edge).2 hedgePath)

omit [Fintype V] [DecidableEq V] in
/-- The complementary cross channel has the same exact one-site closure
profile. -/
theorem EvenKempeFusionLens.exists_cbOppositePortClosure_with_crossSpliceCoverage
    (data : AdjacentPairData G)
    [retainedFintype : Fintype
      (retainedVertexSet data.firstVertex data.secondVertex)]
    [retainedDecidableEq : DecidableEq
      (retainedVertexSet data.firstVertex data.secondVertex)]
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
    (hnonempty : lens01.cbCrossSites lens23 ≠ []) :
    ∃ (site : lens01.cRoute.CrossSite lens23.bRoute)
        (path : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk
            (data.retainedPort 0) (data.retainedPort 2)),
      path.IsTrail ∧ 0 < path.length ∧
        path.edges ⊆
          (lens01.cRoute.crossSplice lens23.bRoute site).support.map
            Subtype.val ∧
        path.edges ⊆
          (lens01.cRoute.ambientPath.support ++
            lens23.bRoute.ambientPath.support).map Subtype.val ∧
        (∀ edge ∈
          (lens01.cRoute.crossSplice lens23.bRoute site).support,
          edge = site.1 ∨
            (retainedEdgeToAmbientEdge data edge).1 ∈
              (data.oppositePortClosure path).edges) := by
  rcases lens01.exists_cbPrimalTrail_with_crossSpliceCoverage lens23
      hdata hab hac hbc hbDisjoint hcDisjoint hnonempty with
    ⟨site, path, htrail, hpositive, hspliceSupport, hsupport, hcoverage⟩
  refine ⟨site, path, htrail, hpositive, hspliceSupport, hsupport, ?_⟩
  intro edge hedge
  rcases hcoverage edge hedge with hedgeSite | hedgePath
  · exact Or.inl hedgeSite
  · exact Or.inr
      ((retainedEdgeToAmbientEdge_mem_oppositePortClosure_edges_iff
        data path edge).2 hedgePath)

omit [Fintype V] [DecidableEq V] in
/-- In the sparse nonempty `bc` branch, one obtains a complete one-site
support profile: away from the cross site the exact closure cut is precisely
the prefix splice, and both strict tails to the unused ports avoid the cut. -/
theorem EvenKempeFusionLens.exists_bcOppositePortClosure_with_exactCrossSpliceProfile
    (data : AdjacentPairData G)
    [retainedFintype : Fintype
      (retainedVertexSet data.firstVertex data.secondVertex)]
    [retainedDecidableEq : DecidableEq
      (retainedVertexSet data.firstVertex data.secondVertex)]
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
    (hnonempty : lens01.bcCrossSites lens23 ≠ []) :
    ∃ (site : lens01.bRoute.CrossSite lens23.cRoute)
        (path : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk
            (data.retainedPort 0) (data.retainedPort 2)),
      path.IsTrail ∧ 0 < path.length ∧
        path.edges ⊆
          (lens01.bRoute.crossSplice lens23.cRoute site).support.map
            Subtype.val ∧
        path.edges ⊆
          (lens01.bRoute.ambientPath.support ++
            lens23.cRoute.ambientPath.support).map Subtype.val ∧
        (∀ edge,
          edge ≠ site.1 →
            ((retainedEdgeToAmbientEdge data edge).1 ∈
                (data.oppositePortClosure path).edges ↔
              edge ∈
                (lens01.bRoute.crossSplice
                  lens23.cRoute site).support)) ∧
        (∀ edge ∈
            (lens01.bRoute.firstSuffixFromCrossSite
              lens23.cRoute site).support.tail,
          (retainedEdgeToAmbientEdge data edge).1 ∉
            (data.oppositePortClosure path).edges) ∧
        (∀ edge ∈
            (lens01.bRoute.secondSuffixFromCrossSite
              lens23.cRoute site).support.tail,
          (retainedEdgeToAmbientEdge data edge).1 ∉
            (data.oppositePortClosure path).edges) := by
  rcases EvenKempeFusionLens.exists_bcOppositePortClosure_with_crossSpliceCoverage
      data lens01 lens23 hdata hab hac hbc hbDisjoint hcDisjoint hnonempty with
    ⟨site, path, htrail, hpositive, hspliceSupport, hrouteSupport,
      hcoverage⟩
  have htails :=
    EvenKempeFusionLens.bcCrossSpliceSuffixes_not_mem_oppositePortClosure_edges
      data lens01 lens23 hcount site path hspliceSupport
  refine ⟨site, path, htrail, hpositive, hspliceSupport, hrouteSupport,
    ?_, htails.1, htails.2⟩
  intro edge hne
  exact retainedEdgeToAmbientEdge_mem_oppositePortClosure_edges_iff_mem_support_of_ne
    data path (lens01.bRoute.crossSplice lens23.cRoute site).support
      site.1 hspliceSupport hcoverage edge hne

omit [Fintype V] [DecidableEq V] in
/-- The sparse nonempty `cb` branch supplies the symmetric exact splice and
strict-tail profile. -/
theorem EvenKempeFusionLens.exists_cbOppositePortClosure_with_exactCrossSpliceProfile
    (data : AdjacentPairData G)
    [retainedFintype : Fintype
      (retainedVertexSet data.firstVertex data.secondVertex)]
    [retainedDecidableEq : DecidableEq
      (retainedVertexSet data.firstVertex data.secondVertex)]
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
    (hnonempty : lens01.cbCrossSites lens23 ≠ []) :
    ∃ (site : lens01.cRoute.CrossSite lens23.bRoute)
        (path : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk
            (data.retainedPort 0) (data.retainedPort 2)),
      path.IsTrail ∧ 0 < path.length ∧
        path.edges ⊆
          (lens01.cRoute.crossSplice lens23.bRoute site).support.map
            Subtype.val ∧
        path.edges ⊆
          (lens01.cRoute.ambientPath.support ++
            lens23.bRoute.ambientPath.support).map Subtype.val ∧
        (∀ edge,
          edge ≠ site.1 →
            ((retainedEdgeToAmbientEdge data edge).1 ∈
                (data.oppositePortClosure path).edges ↔
              edge ∈
                (lens01.cRoute.crossSplice
                  lens23.bRoute site).support)) ∧
        (∀ edge ∈
            (lens01.cRoute.firstSuffixFromCrossSite
              lens23.bRoute site).support.tail,
          (retainedEdgeToAmbientEdge data edge).1 ∉
            (data.oppositePortClosure path).edges) ∧
        (∀ edge ∈
            (lens01.cRoute.secondSuffixFromCrossSite
              lens23.bRoute site).support.tail,
          (retainedEdgeToAmbientEdge data edge).1 ∉
            (data.oppositePortClosure path).edges) := by
  rcases EvenKempeFusionLens.exists_cbOppositePortClosure_with_crossSpliceCoverage
      data lens01 lens23 hdata hab hac hbc hbDisjoint hcDisjoint hnonempty with
    ⟨site, path, htrail, hpositive, hspliceSupport, hrouteSupport,
      hcoverage⟩
  have htails :=
    EvenKempeFusionLens.cbCrossSpliceSuffixes_not_mem_oppositePortClosure_edges
      data lens01 lens23 hcount site path hspliceSupport
  refine ⟨site, path, htrail, hpositive, hspliceSupport, hrouteSupport,
    ?_, htails.1, htails.2⟩
  intro edge hne
  exact retainedEdgeToAmbientEdge_mem_oppositePortClosure_edges_iff_mem_support_of_ne
    data path (lens01.cRoute.crossSplice lens23.bRoute site).support
      site.1 hspliceSupport hcoverage edge hne

omit [Fintype V] [DecidableEq V] in
/-- A `c(0,1)` edge outside `b(0,1)` is outside every opposite-port
closure whose retained path is supported in the `bc` cross channel. -/
theorem EvenKempeFusionLens.c01_not_mem_bcOppositePortClosure_edges_of_not_mem_b01
    (data : AdjacentPairData G)
    [retainedFintype : Fintype
      (retainedVertexSet data.firstVertex data.secondVertex)]
    [retainedDecidableEq : DecidableEq
      (retainedVertexSet data.firstVertex data.secondVertex)]
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2))
    (hsupport : path.edges ⊆
      (lens01.bRoute.ambientPath.support ++
        lens23.cRoute.ambientPath.support).map Subtype.val)
    {edge : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (hc01 : edge ∈ lens01.cRoute.ambientPath.support)
    (hb01 : edge ∉ lens01.bRoute.ambientPath.support) :
    (retainedEdgeToAmbientEdge data edge).1 ∉
      (data.oppositePortClosure path).edges := by
  rw [retainedEdgeToAmbientEdge_mem_oppositePortClosure_edges_iff]
  exact lens01.c01_not_mem_bcTrail_edges_of_not_mem_b01
    lens23 hcDisjoint path hsupport hc01 hb01

omit [Fintype V] [DecidableEq V] in
/-- The `b(2,3)` complement of a `bc` channel is cut-free under the
analogous local nonintersection condition. -/
theorem EvenKempeFusionLens.b23_not_mem_bcOppositePortClosure_edges_of_not_mem_c23
    (data : AdjacentPairData G)
    [retainedFintype : Fintype
      (retainedVertexSet data.firstVertex data.secondVertex)]
    [retainedDecidableEq : DecidableEq
      (retainedVertexSet data.firstVertex data.secondVertex)]
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2))
    (hsupport : path.edges ⊆
      (lens01.bRoute.ambientPath.support ++
        lens23.cRoute.ambientPath.support).map Subtype.val)
    {edge : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (hb23 : edge ∈ lens23.bRoute.ambientPath.support)
    (hc23 : edge ∉ lens23.cRoute.ambientPath.support) :
    (retainedEdgeToAmbientEdge data edge).1 ∉
      (data.oppositePortClosure path).edges := by
  rw [retainedEdgeToAmbientEdge_mem_oppositePortClosure_edges_iff]
  exact lens01.b23_not_mem_bcTrail_edges_of_not_mem_c23
    lens23 hbDisjoint path hsupport hb23 hc23

omit [Fintype V] [DecidableEq V] in
/-- The first-lens `b` complement is cut-free for a path supported in the
`cb` cross channel. -/
theorem EvenKempeFusionLens.b01_not_mem_cbOppositePortClosure_edges_of_not_mem_c01
    (data : AdjacentPairData G)
    [retainedFintype : Fintype
      (retainedVertexSet data.firstVertex data.secondVertex)]
    [retainedDecidableEq : DecidableEq
      (retainedVertexSet data.firstVertex data.secondVertex)]
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2))
    (hsupport : path.edges ⊆
      (lens01.cRoute.ambientPath.support ++
        lens23.bRoute.ambientPath.support).map Subtype.val)
    {edge : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (hb01 : edge ∈ lens01.bRoute.ambientPath.support)
    (hc01 : edge ∉ lens01.cRoute.ambientPath.support) :
    (retainedEdgeToAmbientEdge data edge).1 ∉
      (data.oppositePortClosure path).edges := by
  rw [retainedEdgeToAmbientEdge_mem_oppositePortClosure_edges_iff]
  exact lens01.b01_not_mem_cbTrail_edges_of_not_mem_c01
    lens23 hbDisjoint path hsupport hb01 hc01

omit [Fintype V] [DecidableEq V] in
/-- The second-lens `c` complement is cut-free for a `cb`-supported path. -/
theorem EvenKempeFusionLens.c23_not_mem_cbOppositePortClosure_edges_of_not_mem_b23
    (data : AdjacentPairData G)
    [retainedFintype : Fintype
      (retainedVertexSet data.firstVertex data.secondVertex)]
    [retainedDecidableEq : DecidableEq
      (retainedVertexSet data.firstVertex data.secondVertex)]
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2))
    (hsupport : path.edges ⊆
      (lens01.cRoute.ambientPath.support ++
        lens23.bRoute.ambientPath.support).map Subtype.val)
    {edge : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (hc23 : edge ∈ lens23.cRoute.ambientPath.support)
    (hb23 : edge ∉ lens23.bRoute.ambientPath.support) :
    (retainedEdgeToAmbientEdge data edge).1 ∉
      (data.oppositePortClosure path).edges := by
  rw [retainedEdgeToAmbientEdge_mem_oppositePortClosure_edges_iff]
  exact lens01.c23_not_mem_cbTrail_edges_of_not_mem_b23
    lens23 hcDisjoint path hsupport hc23 hb23

omit [Fintype V] [DecidableEq V] in
/-- Every `c` arm at a first-lens fusion site avoids a `bc`-supported
opposite-port closure. -/
theorem EvenKempeFusionLens.c01FusionArms_not_mem_bcOppositePortClosure_edges
    (data : AdjacentPairData G)
    [retainedFintype : Fintype
      (retainedVertexSet data.firstVertex data.secondVertex)]
    [retainedDecidableEq : DecidableEq
      (retainedVertexSet data.firstVertex data.secondVertex)]
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hac : a ≠ c) (hbc : b ≠ c)
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2))
    (hsupport : path.edges ⊆
      (lens01.bRoute.ambientPath.support ++
        lens23.cRoute.ambientPath.support).map Subtype.val)
    (site : lens01.FusionSite) :
    (retainedEdgeToAmbientEdge data (lens01.cPreviousVertex site).1).1 ∉
        (data.oppositePortClosure path).edges ∧
      (retainedEdgeToAmbientEdge data (lens01.cNextVertex site).1).1 ∉
        (data.oppositePortClosure path).edges := by
  constructor
  · exact EvenKempeFusionLens.c01_not_mem_bcOppositePortClosure_edges_of_not_mem_b01
      data lens01 lens23 hcDisjoint path hsupport
        (lens01.cPreviousVertex_mem_cAmbientPath_support site)
        (lens01.cPreviousVertex_not_mem_bAmbientPath_support hac hbc site)
  · exact EvenKempeFusionLens.c01_not_mem_bcOppositePortClosure_edges_of_not_mem_b01
      data lens01 lens23 hcDisjoint path hsupport
        (lens01.cNextVertex_mem_cAmbientPath_support site)
        (lens01.cNextVertex_not_mem_bAmbientPath_support hac hbc site)

omit [Fintype V] [DecidableEq V] in
/-- Every `b` arm at a second-lens fusion site avoids a `bc`-supported
opposite-port closure. -/
theorem EvenKempeFusionLens.b23FusionArms_not_mem_bcOppositePortClosure_edges
    (data : AdjacentPairData G)
    [retainedFintype : Fintype
      (retainedVertexSet data.firstVertex data.secondVertex)]
    [retainedDecidableEq : DecidableEq
      (retainedVertexSet data.firstVertex data.secondVertex)]
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hab : a ≠ b) (hbc : b ≠ c)
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2))
    (hsupport : path.edges ⊆
      (lens01.bRoute.ambientPath.support ++
        lens23.cRoute.ambientPath.support).map Subtype.val)
    (site : lens23.FusionSite) :
    (retainedEdgeToAmbientEdge data (lens23.bPreviousVertex site).1).1 ∉
        (data.oppositePortClosure path).edges ∧
      (retainedEdgeToAmbientEdge data (lens23.bNextVertex site).1).1 ∉
        (data.oppositePortClosure path).edges := by
  constructor
  · exact EvenKempeFusionLens.b23_not_mem_bcOppositePortClosure_edges_of_not_mem_c23
      data lens01 lens23 hbDisjoint path hsupport
        (lens23.bPreviousVertex_mem_bAmbientPath_support site)
        (lens23.bPreviousVertex_not_mem_cAmbientPath_support hab hbc site)
  · exact EvenKempeFusionLens.b23_not_mem_bcOppositePortClosure_edges_of_not_mem_c23
      data lens01 lens23 hbDisjoint path hsupport
        (lens23.bNextVertex_mem_bAmbientPath_support site)
        (lens23.bNextVertex_not_mem_cAmbientPath_support hab hbc site)

omit [Fintype V] [DecidableEq V] in
/-- In the complementary channel orientation, every first-lens `b` arm
avoids the `cb`-supported closure. -/
theorem EvenKempeFusionLens.b01FusionArms_not_mem_cbOppositePortClosure_edges
    (data : AdjacentPairData G)
    [retainedFintype : Fintype
      (retainedVertexSet data.firstVertex data.secondVertex)]
    [retainedDecidableEq : DecidableEq
      (retainedVertexSet data.firstVertex data.secondVertex)]
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hab : a ≠ b) (hbc : b ≠ c)
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2))
    (hsupport : path.edges ⊆
      (lens01.cRoute.ambientPath.support ++
        lens23.bRoute.ambientPath.support).map Subtype.val)
    (site : lens01.FusionSite) :
    (retainedEdgeToAmbientEdge data (lens01.bPreviousVertex site).1).1 ∉
        (data.oppositePortClosure path).edges ∧
      (retainedEdgeToAmbientEdge data (lens01.bNextVertex site).1).1 ∉
        (data.oppositePortClosure path).edges := by
  constructor
  · exact EvenKempeFusionLens.b01_not_mem_cbOppositePortClosure_edges_of_not_mem_c01
      data lens01 lens23 hbDisjoint path hsupport
        (lens01.bPreviousVertex_mem_bAmbientPath_support site)
        (lens01.bPreviousVertex_not_mem_cAmbientPath_support hab hbc site)
  · exact EvenKempeFusionLens.b01_not_mem_cbOppositePortClosure_edges_of_not_mem_c01
      data lens01 lens23 hbDisjoint path hsupport
        (lens01.bNextVertex_mem_bAmbientPath_support site)
        (lens01.bNextVertex_not_mem_cAmbientPath_support hab hbc site)

omit [Fintype V] [DecidableEq V] in
/-- Every second-lens `c` arm avoids a `cb`-supported closure. -/
theorem EvenKempeFusionLens.c23FusionArms_not_mem_cbOppositePortClosure_edges
    (data : AdjacentPairData G)
    [retainedFintype : Fintype
      (retainedVertexSet data.firstVertex data.secondVertex)]
    [retainedDecidableEq : DecidableEq
      (retainedVertexSet data.firstVertex data.secondVertex)]
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hac : a ≠ c) (hbc : b ≠ c)
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2))
    (hsupport : path.edges ⊆
      (lens01.cRoute.ambientPath.support ++
        lens23.bRoute.ambientPath.support).map Subtype.val)
    (site : lens23.FusionSite) :
    (retainedEdgeToAmbientEdge data (lens23.cPreviousVertex site).1).1 ∉
        (data.oppositePortClosure path).edges ∧
      (retainedEdgeToAmbientEdge data (lens23.cNextVertex site).1).1 ∉
        (data.oppositePortClosure path).edges := by
  constructor
  · exact EvenKempeFusionLens.c23_not_mem_cbOppositePortClosure_edges_of_not_mem_b23
      data lens01 lens23 hcDisjoint path hsupport
        (lens23.cPreviousVertex_mem_cAmbientPath_support site)
        (lens23.cPreviousVertex_not_mem_bAmbientPath_support hac hbc site)
  · exact EvenKempeFusionLens.c23_not_mem_cbOppositePortClosure_edges_of_not_mem_b23
      data lens01 lens23 hcDisjoint path hsupport
        (lens23.cNextVertex_mem_cAmbientPath_support site)
        (lens23.cNextVertex_not_mem_bAmbientPath_support hac hbc site)

end

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
