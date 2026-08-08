import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebRadialComponents

/-!
# Inner-touching components of a totally closed v24 web

After Cubic Closure identifies the web with the whole annular tangle, the
source says that every bichromatic strand is inner-touching.  This module
states that component-level property and derives its first nontrivial graph
consequence: every such component has a second, distinct boundary endpoint.

The proof uses only the actual degree structure.  Boundary support vertices
have degree one, nonboundary support vertices have degree two, and the
handshaking lemma inside one connected component pairs the odd endpoint.
The remaining census step must rule out that the second endpoint is another
inner endpoint when `n_out = 5`.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebInnerTouching

open SimpleGraph
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebSelectedEdgeStructure
open GoertzelV24ClosedWebRadialComponents
open GoertzelV24DegreeTwoSpanningPath

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

noncomputable local instance colorPairGraphNeighborSetFintype
    (C : G.EdgeColoring Color) (first second : Color) (vertex : V) :
    Fintype ((colorPairGraph C first second).neighborSet vertex) := by
  classical
  exact Subtype.fintype _

noncomputable local instance colorPairSupportGraphNeighborSetFintype
    (C : G.EdgeColoring Color) (first second : Color)
    (vertex : ColorPairSupportVertex C first second) :
    Fintype ((colorPairSupportGraph C first second).neighborSet vertex) := by
  classical
  exact Subtype.fintype _

/-- A selected support vertex is one of the ordered inner stubs. -/
def IsInnerStub
    (data : AnnularBoundaryData G outerCount)
    {C : G.EdgeColoring Color} {first second : Color}
    (vertex : ColorPairSupportVertex C first second) : Prop :=
  ∃ inner : Fin 5, vertex.1 = data.innerStub inner

/-- A selected support vertex is one of the ordered outer stubs. -/
def IsOuterStub
    (data : AnnularBoundaryData G outerCount)
    {C : G.EdgeColoring Color} {first second : Color}
    (vertex : ColorPairSupportVertex C first second) : Prop :=
  ∃ outer : Fin outerCount, vertex.1 = data.outerStub outer

/-- Either kind of interface stub. -/
def IsBoundaryStub
    (data : AnnularBoundaryData G outerCount)
    {C : G.EdgeColoring Color} {first second : Color}
    (vertex : ColorPairSupportVertex C first second) : Prop :=
  IsInnerStub data vertex ∨ IsOuterStub data vertex

/-- Component-level content of "every strand is inner-touching." -/
def EveryComponentInnerTouching
    (data : AnnularBoundaryData G outerCount)
    (C : G.EdgeColoring Color) (first second : Color) : Prop :=
  ∀ component : (colorPairSupportGraph C first second).ConnectedComponent,
    ∃ inner : Fin 5,
      ComponentContainsInnerStub data C first second component inner

/-- All three Tait pairs are inner-touching after Cubic Closure. -/
def EveryColorPairComponentInnerTouching
    (data : AnnularBoundaryData G outerCount)
    (C : G.EdgeColoring Color) : Prop :=
  ∀ first second : Color,
    ValidColorPair first second →
      EveryComponentInnerTouching data C first second

/-- An inner boundary vertex that lies in the selected support graph has
support-graph degree one. -/
theorem degree_eq_one_of_isInnerStub
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (first second : Color)
    (vertex : ColorPairSupportVertex C first second)
    (hinner : IsInnerStub data vertex) :
    (colorPairSupportGraph C first second).degree vertex = 1 := by
  rcases hinner with ⟨inner, hvertex⟩
  have hpositive :
      0 < (colorPairGraph C first second).degree (data.innerStub inner) := by
    apply ((colorPairGraph C first second).degree_pos_iff_mem_support
      (data.innerStub inner)).mpr
    simpa [hvertex] using vertex.property
  have hselected : C (data.innerBoundaryEdge inner) = first ∨
      C (data.innerBoundaryEdge inner) = second := by
    by_contra hnotSelected
    rw [AnnularBoundaryData.colorPairGraph_degree_innerStub
      data hdata C first second inner] at hpositive
    simp [hnotSelected] at hpositive
  rw [colorPairSupportGraph_degree_eq C first second vertex]
  rw [hvertex,
    AnnularBoundaryData.colorPairGraph_degree_innerStub
      data hdata C first second inner]
  simp [hselected]

/-- The analogous exact degree at an outer boundary support vertex. -/
theorem degree_eq_one_of_isOuterStub
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (first second : Color)
    (vertex : ColorPairSupportVertex C first second)
    (houter : IsOuterStub data vertex) :
    (colorPairSupportGraph C first second).degree vertex = 1 := by
  rcases houter with ⟨outer, hvertex⟩
  have hpositive :
      0 < (colorPairGraph C first second).degree (data.outerStub outer) := by
    apply ((colorPairGraph C first second).degree_pos_iff_mem_support
      (data.outerStub outer)).mpr
    simpa [hvertex] using vertex.property
  have hselected : C (data.outerBoundaryEdge outer) = first ∨
      C (data.outerBoundaryEdge outer) = second := by
    by_contra hnotSelected
    rw [AnnularBoundaryData.colorPairGraph_degree_outerStub
      data hdata C first second outer] at hpositive
    simp [hnotSelected] at hpositive
  rw [colorPairSupportGraph_degree_eq C first second vertex]
  rw [hvertex,
    AnnularBoundaryData.colorPairGraph_degree_outerStub
      data hdata C first second outer]
  simp [hselected]

/-- Either kind of boundary support vertex has selected-pair degree one. -/
theorem degree_eq_one_of_isBoundaryStub
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (first second : Color)
    (vertex : ColorPairSupportVertex C first second)
    (hboundary : IsBoundaryStub data vertex) :
    (colorPairSupportGraph C first second).degree vertex = 1 := by
  rcases hboundary with hinner | houter
  · exact degree_eq_one_of_isInnerStub
      data hdata C first second vertex hinner
  · exact degree_eq_one_of_isOuterStub
      data hdata C first second vertex houter

/-- Every nonboundary support vertex is a cubic Tait vertex and hence has
selected-pair degree two. -/
theorem degree_eq_two_of_not_boundaryStub
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    {first second : Color} (hpair : ValidColorPair first second)
    (vertex : ColorPairSupportVertex C first second)
    (hnotBoundary : ¬ IsBoundaryStub data vertex) :
    (colorPairSupportGraph C first second).degree vertex = 2 := by
  have hnotInner : ∀ inner : Fin 5,
      vertex.1 ≠ data.innerStub inner := by
    intro inner heq
    exact hnotBoundary (Or.inl ⟨inner, heq⟩)
  have hnotOuter : ∀ outer : Fin outerCount,
      vertex.1 ≠ data.outerStub outer := by
    intro outer heq
    exact hnotBoundary (Or.inr ⟨outer, heq⟩)
  rw [colorPairSupportGraph_degree_eq C first second vertex]
  exact colorPairGraph_degree_eq_two_of_cubic_tait C hC vertex.1
    (hdata.cubic_elsewhere vertex.1 hnotInner hnotOuter) hpair

/-- Every support-graph vertex has degree exactly one or exactly two. -/
theorem degree_eq_one_or_two
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    {first second : Color} (hpair : ValidColorPair first second)
    (vertex : ColorPairSupportVertex C first second) :
    (colorPairSupportGraph C first second).degree vertex = 1 ∨
      (colorPairSupportGraph C first second).degree vertex = 2 := by
  by_cases hinner : IsInnerStub data vertex
  · exact Or.inl (degree_eq_one_of_isInnerStub
      data hdata C first second vertex hinner)
  by_cases houter : IsOuterStub data vertex
  · exact Or.inl (degree_eq_one_of_isOuterStub
      data hdata C first second vertex houter)
  · exact Or.inr (degree_eq_two_of_not_boundaryStub
      data hdata C hC hpair vertex (by simp [IsBoundaryStub, hinner, houter]))

/-- A selected-pair component contains at most two boundary stubs.  More
precisely, once two distinct boundary vertices in the component are named,
every other boundary vertex in that component equals one of them.

This is the graph-theoretic justification for treating connected components
as the manuscript's bichromatic strands: all support degrees are at most two,
so the path between two degree-one boundary vertices covers the component. -/
theorem boundaryStub_eq_start_or_finish_of_mem_component
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    {first second : Color} (hpair : ValidColorPair first second)
    (component :
      (colorPairSupportGraph C first second).ConnectedComponent)
    (start finish candidate : ColorPairSupportVertex C first second)
    (hstartComponent : start ∈ component.supp)
    (hfinishComponent : finish ∈ component.supp)
    (hcandidateComponent : candidate ∈ component.supp)
    (hstartFinish : start ≠ finish)
    (hstartBoundary : IsBoundaryStub data start)
    (hfinishBoundary : IsBoundaryStub data finish)
    (hcandidateBoundary : IsBoundaryStub data candidate) :
    candidate = start ∨ candidate = finish := by
  classical
  have hstartDegree :
      (colorPairSupportGraph C first second).degree start = 1 :=
    degree_eq_one_of_isBoundaryStub
      data hdata C first second start hstartBoundary
  have hfinishDegree :
      (colorPairSupportGraph C first second).degree finish = 1 :=
    degree_eq_one_of_isBoundaryStub
      data hdata C first second finish hfinishBoundary
  have hdegreeElse :
      ∀ vertex : ColorPairSupportVertex C first second,
        vertex ∈ component.supp →
        vertex ≠ start → vertex ≠ finish →
        (colorPairSupportGraph C first second).degree vertex ≤ 2 := by
    intro vertex _hvertexComponent _hvertexStart _hvertexFinish
    rcases degree_eq_one_or_two data hdata C hC hpair vertex with
      hone | htwo
    · omega
    · omega
  rcases
      exists_path_covering_component_of_endpoints_degree_one_of_degree_le_two_else
        (H := colorPairSupportGraph C first second) component
        hstartComponent hfinishComponent hstartFinish
        hstartDegree hfinishDegree hdegreeElse with
    ⟨path, hpath, hpathVertices⟩
  by_contra hcandidateEndpoints
  have hcandidateNeStart : candidate ≠ start := by
    intro heq
    exact hcandidateEndpoints (Or.inl heq)
  have hcandidateNeFinish : candidate ≠ finish := by
    intro heq
    exact hcandidateEndpoints (Or.inr heq)
  have hcandidatePathVertices : candidate ∈ path.toSubgraph.verts := by
    rw [hpathVertices]
    exact hcandidateComponent
  have hcandidatePathSupport : candidate ∈ path.support :=
    path.mem_verts_toSubgraph.mp hcandidatePathVertices
  rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp
      hcandidatePathSupport with
    ⟨index, hindexCandidate, hindexBound⟩
  have hindexNeZero : index ≠ 0 := by
    intro hindexZero
    apply hcandidateNeStart
    calc
      candidate = path.getVert index := hindexCandidate.symm
      _ = start := (hpath.getVert_eq_start_iff hindexBound).2 hindexZero
  have hindexNeLength : index ≠ path.length := by
    intro hindexLength
    apply hcandidateNeFinish
    calc
      candidate = path.getVert index := hindexCandidate.symm
      _ = finish := (hpath.getVert_eq_end_iff hindexBound).2 hindexLength
  have hindexLtLength : index < path.length := by
    omega
  have hpathNeighborCount :
      (path.toSubgraph.neighborSet candidate).ncard = 2 := by
    simpa [hindexCandidate] using
      hpath.ncard_neighborSet_toSubgraph_internal_eq_two
        hindexNeZero hindexLtLength
  have hneighborSubset :
      path.toSubgraph.neighborSet candidate ⊆
        (colorPairSupportGraph C first second).neighborSet candidate := by
    intro neighbor hneighbor
    exact path.toSubgraph.adj_sub hneighbor
  have hdegreeAtLeastTwo :
      2 ≤ (colorPairSupportGraph C first second).degree candidate := by
    have hsubsetCard := Set.ncard_le_ncard hneighborSubset
    have hambientNeighborCount :
        ((colorPairSupportGraph C first second).neighborSet candidate).ncard =
          (colorPairSupportGraph C first second).degree candidate := by
      simpa only [Set.fintypeCard_eq_ncard] using
        (SimpleGraph.card_neighborSet_eq_degree
          (G := colorPairSupportGraph C first second) (v := candidate))
    omega
  have hcandidateDegree :
      (colorPairSupportGraph C first second).degree candidate = 1 :=
    degree_eq_one_of_isBoundaryStub
      data hdata C first second candidate hcandidateBoundary
  omega

/-- In an inner-touching component, parity forces a second distinct boundary
stub.  This is the graph half of the inner-inner/radial census split. -/
theorem exists_distinct_second_boundaryStub_of_component_innerTouching
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    {first second : Color} (hpair : ValidColorPair first second)
    (hinnerTouching : EveryComponentInnerTouching data C first second)
    (component : (colorPairSupportGraph C first second).ConnectedComponent) :
    ∃ start finish : ColorPairSupportVertex C first second,
      start ≠ finish ∧
      start ∈ component.supp ∧ finish ∈ component.supp ∧
      IsInnerStub data start ∧ IsBoundaryStub data finish := by
  classical
  rcases hinnerTouching component with
    ⟨inner, start, hstartComponent, hstartEq⟩
  have hstartInner : IsInnerStub data start := ⟨inner, hstartEq⟩
  have hstartDegree :
      (colorPairSupportGraph C first second).degree start = 1 :=
    degree_eq_one_of_isInnerStub
      data hdata C first second start hstartInner
  let componentGraph : SimpleGraph component.supp :=
    (colorPairSupportGraph C first second).induce component.supp
  have hdegreeInduce :
      ∀ vertex : component.supp,
        componentGraph.degree vertex =
          (colorPairSupportGraph C first second).degree vertex := by
    intro vertex
    have hneighborSubset :
        (colorPairSupportGraph C first second).neighborSet vertex ⊆
          component.supp := by
      intro neighbor hadjacent
      exact component.mem_supp_of_adj_mem_supp
        vertex.property hadjacent
    simpa [componentGraph] using
      (SimpleGraph.degree_induce_of_neighborSet_subset
        (G := colorPairSupportGraph C first second)
        (s := component.supp) (v := vertex) hneighborSubset)
  let startInComponent : component.supp := ⟨start, hstartComponent⟩
  have hstartOdd : Odd (componentGraph.degree startInComponent) := by
    rw [hdegreeInduce, hstartDegree]
    simp
  obtain ⟨finishInComponent, hfinishNe, hfinishOdd⟩ :=
    componentGraph.exists_ne_odd_degree_of_exists_odd_degree
      startInComponent hstartOdd
  let finish : ColorPairSupportVertex C first second := finishInComponent.1
  have hfinishComponent : finish ∈ component.supp :=
    finishInComponent.property
  have hfinishDegreeCases :=
    degree_eq_one_or_two data hdata C hC hpair finish
  have hfinishDegree :
      (colorPairSupportGraph C first second).degree finish = 1 := by
    rcases hfinishDegreeCases with hone | htwo
    · exact hone
    · have hdegreeTwo : componentGraph.degree finishInComponent = 2 := by
        rw [hdegreeInduce]
        simpa [finish] using htwo
      have hnotOdd : ¬ Odd (componentGraph.degree finishInComponent) := by
        rw [hdegreeTwo]
        norm_num
      exact False.elim (hnotOdd hfinishOdd)
  have hfinishBoundary : IsBoundaryStub data finish := by
    by_contra hnotBoundary
    have htwo := degree_eq_two_of_not_boundaryStub
      data hdata C hC hpair finish hnotBoundary
    rw [hfinishDegree] at htwo
    omega
  have hstartFinish : start ≠ finish := by
    intro heq
    apply hfinishNe
    apply Subtype.ext
    exact heq.symm
  exact ⟨start, finish, hstartFinish, hstartComponent,
    hfinishComponent, hstartInner, hfinishBoundary⟩

/-- Census-level exclusion of the inner--inner strand type. -/
def NoComponentHasTwoDistinctInnerStubs
    (data : AnnularBoundaryData G outerCount)
    (C : G.EdgeColoring Color) (first second : Color) : Prop :=
  ∀ component : (colorPairSupportGraph C first second).ConnectedComponent,
    ∀ firstInner secondInner : Fin 5,
      ComponentContainsInnerStub
          data C first second component firstInner →
      ComponentContainsInnerStub
          data C first second component secondInner →
      firstInner = secondInner

/-- The inner--inner exclusion simultaneously for every valid Tait pair. -/
def NoColorPairComponentHasTwoDistinctInnerStubs
    (data : AnnularBoundaryData G outerCount)
    (C : G.EdgeColoring Color) : Prop :=
  ∀ first second : Color,
    ValidColorPair first second →
      NoComponentHasTwoDistinctInnerStubs data C first second

/-- Inner-touching plus exclusion of the inner--inner type forces every
component to reach the outer boundary. -/
theorem exists_inner_and_outer_of_innerTouching_of_noTwoInner
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    {first second : Color} (hpair : ValidColorPair first second)
    (hinnerTouching : EveryComponentInnerTouching data C first second)
    (hnoTwoInner : NoComponentHasTwoDistinctInnerStubs
      data C first second)
    (component : (colorPairSupportGraph C first second).ConnectedComponent) :
    (∃ inner : Fin 5,
      ComponentContainsInnerStub data C first second component inner) ∧
    ∃ outer : Fin outerCount,
      ComponentContainsOuterStub data C first second component outer := by
  rcases exists_distinct_second_boundaryStub_of_component_innerTouching
      data hdata C hC hpair hinnerTouching component with
    ⟨start, finish, hstartFinish, hstartComponent, hfinishComponent,
      ⟨startInner, hstartEq⟩, hfinishBoundary⟩
  refine ⟨⟨startInner, start, hstartComponent, hstartEq⟩, ?_⟩
  rcases hfinishBoundary with hfinishInner | hfinishOuter
  · rcases hfinishInner with ⟨finishInner, hfinishEq⟩
    have hinnerEq : startInner = finishInner :=
      hnoTwoInner component startInner finishInner
        ⟨start, hstartComponent, hstartEq⟩
        ⟨finish, hfinishComponent, hfinishEq⟩
    exfalso
    apply hstartFinish
    apply Subtype.ext
    calc
      start.1 = data.innerStub startInner := hstartEq
      _ = data.innerStub finishInner := congrArg data.innerStub hinnerEq
      _ = finish.1 := hfinishEq.symm
  · rcases hfinishOuter with ⟨outer, hfinishEq⟩
    exact ⟨outer, finish, hfinishComponent, hfinishEq⟩

/-- Inner-touching component semantics plus the census-level absence of an
inner--inner strand gives the manuscript's exact radial component semantics:
one and only one endpoint on each boundary. -/
theorem everyComponentRadial_of_innerTouching_of_noTwoInner
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    {first second : Color} (hpair : ValidColorPair first second)
    (hinnerTouching : EveryComponentInnerTouching data C first second)
    (hnoTwoInner : NoComponentHasTwoDistinctInnerStubs
      data C first second) :
    EveryComponentRadial data C first second := by
  classical
  intro component
  rcases exists_inner_and_outer_of_innerTouching_of_noTwoInner
      data hdata C hC hpair hinnerTouching hnoTwoInner component with
    ⟨⟨inner, hinnerContains⟩, ⟨outer, houterContains⟩⟩
  refine ⟨⟨inner, hinnerContains, ?_⟩,
    ⟨outer, houterContains, ?_⟩⟩
  · intro candidate hcandidateContains
    exact hnoTwoInner component candidate inner
      hcandidateContains hinnerContains
  · intro candidate hcandidateContains
    rcases hinnerContains with
      ⟨innerVertex, hinnerComponent, hinnerEq⟩
    rcases houterContains with
      ⟨outerVertex, houterComponent, houterEq⟩
    rcases hcandidateContains with
      ⟨candidateVertex, hcandidateComponent, hcandidateEq⟩
    have hinnerOuter : innerVertex ≠ outerVertex := by
      intro heq
      apply hdata.inner_outer_stub_disjoint inner outer
      calc
        data.innerStub inner = innerVertex.1 := hinnerEq.symm
        _ = outerVertex.1 := congrArg Subtype.val heq
        _ = data.outerStub outer := houterEq
    have hcandidateEndpoints :=
      boundaryStub_eq_start_or_finish_of_mem_component
        data hdata C hC hpair component innerVertex outerVertex
        candidateVertex hinnerComponent houterComponent
        hcandidateComponent hinnerOuter
        (Or.inl ⟨inner, hinnerEq⟩)
        (Or.inr ⟨outer, houterEq⟩)
        (Or.inr ⟨candidate, hcandidateEq⟩)
    rcases hcandidateEndpoints with hcandidateInner | hcandidateOuter
    · exfalso
      apply hdata.inner_outer_stub_disjoint inner candidate
      calc
        data.innerStub inner = innerVertex.1 := hinnerEq.symm
        _ = candidateVertex.1 := congrArg Subtype.val hcandidateInner.symm
        _ = data.outerStub candidate := hcandidateEq
    · apply data.outerStub.injective
      calc
        data.outerStub candidate = candidateVertex.1 := hcandidateEq.symm
        _ = outerVertex.1 := congrArg Subtype.val hcandidateOuter
        _ = data.outerStub outer := houterEq

/-- All-pairs form of the preceding component-level implication. -/
theorem everyColorPairComponentRadial_of_innerTouching_of_noTwoInner
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (hinnerTouching : EveryColorPairComponentInnerTouching data C)
    (hnoTwoInner : NoColorPairComponentHasTwoDistinctInnerStubs data C) :
    EveryColorPairComponentRadial data C := by
  intro first second hpair
  exact everyComponentRadial_of_innerTouching_of_noTwoInner
    data hdata C hC hpair
      (hinnerTouching first second hpair)
      (hnoTwoInner first second hpair)

end GoertzelV24ClosedWebInnerTouching

end Mettapedia.GraphTheory.FourColor
