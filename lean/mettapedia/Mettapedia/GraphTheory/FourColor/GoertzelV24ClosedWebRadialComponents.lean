import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebGoodWordCounts
import Mettapedia.GraphTheory.FourColor.GoertzelV24DegreeTwoSpanningPath

/-!
# Radial components of the v24 closed-web color-pair graphs

This module gives the manuscript's word "radial" an actual connected-
component meaning.  Isolated vertices are removed by inducing each selected
color-pair graph on its support.  A radial component then contains exactly
one inner stub and exactly one outer stub.

`EveryColorPairComponentRadial` is a semantic target, not an assumption
hidden in the annular data.  A later theorem must derive it from total web
closure and the strand census.  Conditional on that target, the already
proved good-word endpoint count forces the singleton color-pair graph to
have exactly two components.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebRadialComponents

open SimpleGraph
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebSelectedEdgeStructure
open GoertzelV24ClosedWebGoodWordCounts
open GoertzelV24DegreeTwoSpanningPath

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

noncomputable local instance colorPairGraphNeighborSetFintype
    (C : G.EdgeColoring Color) (first second : Color) (vertex : V) :
    Fintype ((colorPairGraph C first second).neighborSet vertex) := by
  classical
  exact Subtype.fintype _

/-- Vertices incident to at least one edge of a selected color pair. -/
abbrev ColorPairSupportVertex
    (C : G.EdgeColoring Color) (first second : Color) :=
  (colorPairGraph C first second).support

/-- The selected color-pair graph with isolated ambient vertices removed. -/
def colorPairSupportGraph
    (C : G.EdgeColoring Color) (first second : Color) :
    SimpleGraph (ColorPairSupportVertex C first second) :=
  (colorPairGraph C first second).induce
    (colorPairGraph C first second).support

noncomputable local instance colorPairSupportGraphNeighborSetFintype
    (C : G.EdgeColoring Color) (first second : Color)
    (vertex : ColorPairSupportVertex C first second) :
    Fintype ((colorPairSupportGraph C first second).neighborSet vertex) := by
  classical
  exact Subtype.fintype _

/-- A component of the support graph contains a specified inner stub. -/
def ComponentContainsInnerStub
    (data : AnnularBoundaryData G outerCount)
    (C : G.EdgeColoring Color) (first second : Color)
    (component : (colorPairSupportGraph C first second).ConnectedComponent)
    (inner : Fin 5) : Prop :=
  ∃ vertex : ColorPairSupportVertex C first second,
    vertex ∈ component.supp ∧ vertex.1 = data.innerStub inner

/-- A component of the support graph contains a specified outer stub. -/
def ComponentContainsOuterStub
    (data : AnnularBoundaryData G outerCount)
    (C : G.EdgeColoring Color) (first second : Color)
    (component : (colorPairSupportGraph C first second).ConnectedComponent)
    (outer : Fin outerCount) : Prop :=
  ∃ vertex : ColorPairSupportVertex C first second,
    vertex ∈ component.supp ∧ vertex.1 = data.outerStub outer

/-- Component-level radiality: every nonisolated component has exactly one
endpoint on each boundary. -/
def EveryComponentRadial
    (data : AnnularBoundaryData G outerCount)
    (C : G.EdgeColoring Color) (first second : Color) : Prop :=
  ∀ component : (colorPairSupportGraph C first second).ConnectedComponent,
    (∃! inner : Fin 5,
      ComponentContainsInnerStub data C first second component inner) ∧
    (∃! outer : Fin outerCount,
      ComponentContainsOuterStub data C first second component outer)

/-- The all-radial target across the three Tait color pairs. -/
def EveryColorPairComponentRadial
    (data : AnnularBoundaryData G outerCount)
    (C : G.EdgeColoring Color) : Prop :=
  ∀ first second : Color,
    ValidColorPair first second →
      EveryComponentRadial data C first second

/-- An active inner boundary position is a genuine vertex of the selected
pair's support graph. -/
theorem innerStub_mem_colorPairGraph_support_of_mem_activeSupport
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (first second : Color) (inner : Fin 5)
    (hinner : inner ∈ cap5ActiveSupport first second
      (data.innerBoundaryWord C)) :
    data.innerStub inner ∈ (colorPairGraph C first second).support := by
  have hselected : C (data.innerBoundaryEdge inner) = first ∨
      C (data.innerBoundaryEdge inner) = second := by
    simpa [cap5ActiveSupport, AnnularBoundaryData.innerBoundaryWord,
      cap5BoundaryWordOfEdges] using hinner
  apply ((colorPairGraph C first second).degree_pos_iff_mem_support
    (data.innerStub inner)).mp
  rw [AnnularBoundaryData.colorPairGraph_degree_innerStub
    data hdata C first second inner]
  simp [hselected]

/-- Conversely, if an inner stub occurs in a support component then its
boundary index is active for that color pair. -/
theorem mem_activeSupport_of_componentContainsInnerStub
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (first second : Color)
    (component : (colorPairSupportGraph C first second).ConnectedComponent)
    (inner : Fin 5)
    (hinner : ComponentContainsInnerStub
      data C first second component inner) :
    inner ∈ cap5ActiveSupport first second (data.innerBoundaryWord C) := by
  rcases hinner with ⟨vertex, _hvertexComponent, hvertex⟩
  have hstubSupport :
      data.innerStub inner ∈ (colorPairGraph C first second).support := by
    simpa [hvertex] using vertex.property
  have hdegreePositive :
      0 < (colorPairGraph C first second).degree (data.innerStub inner) :=
    ((colorPairGraph C first second).degree_pos_iff_mem_support
      (data.innerStub inner)).mpr hstubSupport
  have hselected : C (data.innerBoundaryEdge inner) = first ∨
      C (data.innerBoundaryEdge inner) = second := by
    by_contra hnotSelected
    rw [AnnularBoundaryData.colorPairGraph_degree_innerStub
      data hdata C first second inner] at hdegreePositive
    simp [hnotSelected] at hdegreePositive
  simpa [cap5ActiveSupport, AnnularBoundaryData.innerBoundaryWord,
    cap5BoundaryWordOfEdges] using hselected

/-- If the inner pair support has cardinality two and every component is
radial, then the selected support graph has exactly two connected
components.  This is the component-counting half of the source's "two radial
paths" statement; path shape is proved separately from degrees. -/
theorem exists_exactly_two_components_of_activeSupport_card_two_of_radial
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (first second : Color)
    (hactive :
      (cap5ActiveSupport first second (data.innerBoundaryWord C)).card = 2)
    (hradial : EveryComponentRadial data C first second) :
    ∃ firstComponent secondComponent :
        (colorPairSupportGraph C first second).ConnectedComponent,
      firstComponent ≠ secondComponent ∧
      ∀ component,
        component = firstComponent ∨ component = secondComponent := by
  classical
  rcases Finset.card_eq_two.mp hactive with
    ⟨firstInner, secondInner, hinnersNe, hactiveSet⟩
  have hfirstActive : firstInner ∈
      cap5ActiveSupport first second (data.innerBoundaryWord C) := by
    rw [hactiveSet]
    simp
  have hsecondActive : secondInner ∈
      cap5ActiveSupport first second (data.innerBoundaryWord C) := by
    rw [hactiveSet]
    simp
  let firstVertex : ColorPairSupportVertex C first second :=
    ⟨data.innerStub firstInner,
      innerStub_mem_colorPairGraph_support_of_mem_activeSupport
        data hdata C first second firstInner hfirstActive⟩
  let secondVertex : ColorPairSupportVertex C first second :=
    ⟨data.innerStub secondInner,
      innerStub_mem_colorPairGraph_support_of_mem_activeSupport
        data hdata C first second secondInner hsecondActive⟩
  let firstComponent :=
    (colorPairSupportGraph C first second).connectedComponentMk firstVertex
  let secondComponent :=
    (colorPairSupportGraph C first second).connectedComponentMk secondVertex
  have hfirstContains : ComponentContainsInnerStub
      data C first second firstComponent firstInner := by
    exact ⟨firstVertex,
      ConnectedComponent.connectedComponentMk_mem, rfl⟩
  have hsecondContains : ComponentContainsInnerStub
      data C first second secondComponent secondInner := by
    exact ⟨secondVertex,
      ConnectedComponent.connectedComponentMk_mem, rfl⟩
  have hcomponentsNe : firstComponent ≠ secondComponent := by
    intro heq
    have hsecondInFirst : ComponentContainsInnerStub
        data C first second firstComponent secondInner := by
      rw [heq]
      exact hsecondContains
    rcases (hradial firstComponent).1 with
      ⟨uniqueInner, _huniqueInner, hunique⟩
    have hfirstEq : firstInner = uniqueInner :=
      hunique firstInner hfirstContains
    have hsecondEq : secondInner = uniqueInner :=
      hunique secondInner hsecondInFirst
    exact hinnersNe (hfirstEq.trans hsecondEq.symm)
  refine ⟨firstComponent, secondComponent, hcomponentsNe, ?_⟩
  intro component
  rcases (hradial component).1 with
    ⟨componentInner, hcomponentInner, _hcomponentInnerUnique⟩
  have hcomponentActive : componentInner ∈
      cap5ActiveSupport first second (data.innerBoundaryWord C) :=
    mem_activeSupport_of_componentContainsInnerStub
      data hdata C first second component componentInner hcomponentInner
  rw [hactiveSet] at hcomponentActive
  simp only [Finset.mem_insert, Finset.mem_singleton] at hcomponentActive
  rcases hcomponentActive with hinnerFirst | hinnerSecond
  · left
    rcases hcomponentInner with ⟨vertex, hvertexComponent, hvertexInner⟩
    have hvertexEq : vertex = firstVertex := by
      apply Subtype.ext
      exact hvertexInner.trans (congrArg data.innerStub hinnerFirst)
    have hcomponentEq :
        (colorPairSupportGraph C first second).connectedComponentMk vertex =
          component :=
      (ConnectedComponent.mem_supp_iff component vertex).mp hvertexComponent
    calc
      component =
          (colorPairSupportGraph C first second).connectedComponentMk vertex :=
        hcomponentEq.symm
      _ = firstComponent := by rw [hvertexEq]
  · right
    rcases hcomponentInner with ⟨vertex, hvertexComponent, hvertexInner⟩
    have hvertexEq : vertex = secondVertex := by
      apply Subtype.ext
      exact hvertexInner.trans (congrArg data.innerStub hinnerSecond)
    have hcomponentEq :
        (colorPairSupportGraph C first second).connectedComponentMk vertex =
          component :=
      (ConnectedComponent.mem_supp_iff component vertex).mp hvertexComponent
    calc
      component =
          (colorPairSupportGraph C first second).connectedComponentMk vertex :=
        hcomponentEq.symm
      _ = secondComponent := by rw [hvertexEq]

/-- Good inner-word data plus all-radial component semantics supplies the
source's singleton pair and proves that its support graph has exactly two
components. -/
theorem exists_singletonPair_with_exactly_two_components_of_goodWord_of_allRadial
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color)
    (hgood : CAP5BoundaryWordHasColoredBlock311
      (data.innerBoundaryWord C))
    (hallRadial : EveryColorPairComponentRadial data C) :
    ∃ majority singletonFirst singletonSecond : Color,
      IsTaitColorTriple majority singletonFirst singletonSecond ∧
      ∃ firstComponent secondComponent :
          (colorPairSupportGraph C singletonFirst singletonSecond).ConnectedComponent,
        firstComponent ≠ secondComponent ∧
        ∀ component,
          component = firstComponent ∨ component = secondComponent := by
  rcases exists_exact_pairEndpointCounts_of_coloredBlock311 hgood with
    ⟨majority, singletonFirst, singletonSecond, htriple,
      hsingletonCount, _hfirstCount, _hsecondCount⟩
  have hpair : ValidColorPair singletonFirst singletonSecond :=
    ⟨htriple.2.1, htriple.2.2.1, htriple.2.2.2.2.2⟩
  rcases exists_exactly_two_components_of_activeSupport_card_two_of_radial
      data hdata C singletonFirst singletonSecond hsingletonCount
      (hallRadial singletonFirst singletonSecond hpair) with
    ⟨firstComponent, secondComponent, hne, hall⟩
  exact ⟨majority, singletonFirst, singletonSecond, htriple,
    firstComponent, secondComponent, hne, hall⟩

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- Degree in the isolated-vertex-free support graph is the same as degree
in the selected color-pair graph. -/
theorem colorPairSupportGraph_degree_eq
    (C : G.EdgeColoring Color) (first second : Color)
    (vertex : ColorPairSupportVertex C first second) :
    (colorPairSupportGraph C first second).degree vertex =
      (colorPairGraph C first second).degree vertex := by
  classical
  have hneighborSubset :
      (colorPairGraph C first second).neighborSet vertex ⊆
        (colorPairGraph C first second).support := by
    intro neighbor hadjacent
    exact hadjacent.mem_support_right
  exact SimpleGraph.degree_induce_of_neighborSet_subset
    (G := colorPairGraph C first second)
    (s := (colorPairGraph C first second).support)
    (v := vertex) hneighborSubset

/-- A path realization of one radial support component. -/
structure ComponentRadialPath
    (data : AnnularBoundaryData G outerCount)
    (C : G.EdgeColoring Color) (first second : Color)
    (component : (colorPairSupportGraph C first second).ConnectedComponent) where
  inner : Fin 5
  outer : Fin outerCount
  start : ColorPairSupportVertex C first second
  finish : ColorPairSupportVertex C first second
  start_mem : start ∈ component.supp
  finish_mem : finish ∈ component.supp
  start_eq_innerStub : start.1 = data.innerStub inner
  finish_eq_outerStub : finish.1 = data.outerStub outer
  path : (colorPairSupportGraph C first second).Walk start finish
  path_isPath : path.IsPath
  path_vertices : path.toSubgraph.verts = component.supp

/-- Every component declared radial is, from the actual degree facts, an
actual simple path from its unique inner stub to its unique outer stub that
covers the component. -/
theorem nonempty_componentRadialPath
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    {first second : Color} (hpair : ValidColorPair first second)
    (hradial : EveryComponentRadial data C first second)
    (component : (colorPairSupportGraph C first second).ConnectedComponent) :
    Nonempty (ComponentRadialPath data C first second component) := by
  classical
  rcases hradial component with
    ⟨⟨inner, hinner, hinnerUnique⟩,
      ⟨outer, houter, houterUnique⟩⟩
  rcases hinner with ⟨start, hstartComponent, hstartEq⟩
  rcases houter with ⟨finish, hfinishComponent, hfinishEq⟩
  have hstartActive : inner ∈
      cap5ActiveSupport first second (data.innerBoundaryWord C) :=
    mem_activeSupport_of_componentContainsInnerStub
      data hdata C first second component inner
        ⟨start, hstartComponent, hstartEq⟩
  have hstartSelected : C (data.innerBoundaryEdge inner) = first ∨
      C (data.innerBoundaryEdge inner) = second := by
    simpa [cap5ActiveSupport, AnnularBoundaryData.innerBoundaryWord,
      cap5BoundaryWordOfEdges] using hstartActive
  have hstartDegree :
      (colorPairSupportGraph C first second).degree start = 1 := by
    rw [colorPairSupportGraph_degree_eq C first second start]
    rw [hstartEq,
      AnnularBoundaryData.colorPairGraph_degree_innerStub
        data hdata C first second inner]
    simp [hstartSelected]
  have hfinishSelected : C (data.outerBoundaryEdge outer) = first ∨
      C (data.outerBoundaryEdge outer) = second := by
    have hfinishPositive :
        0 < (colorPairGraph C first second).degree
          (data.outerStub outer) := by
      apply ((colorPairGraph C first second).degree_pos_iff_mem_support
        (data.outerStub outer)).mpr
      simpa [hfinishEq] using finish.property
    by_contra hnotSelected
    rw [AnnularBoundaryData.colorPairGraph_degree_outerStub
      data hdata C first second outer] at hfinishPositive
    simp [hnotSelected] at hfinishPositive
  have hfinishDegree :
      (colorPairSupportGraph C first second).degree finish = 1 := by
    rw [colorPairSupportGraph_degree_eq C first second finish]
    rw [hfinishEq,
      AnnularBoundaryData.colorPairGraph_degree_outerStub
        data hdata C first second outer]
    simp [hfinishSelected]
  have hstartFinish : start ≠ finish := by
    intro heq
    apply hdata.inner_outer_stub_disjoint inner outer
    calc
      data.innerStub inner = start.1 := hstartEq.symm
      _ = finish.1 := congrArg Subtype.val heq
      _ = data.outerStub outer := hfinishEq
  have hdegreeElse :
      ∀ vertex : ColorPairSupportVertex C first second,
        vertex ∈ component.supp →
        vertex ≠ start → vertex ≠ finish →
        (colorPairSupportGraph C first second).degree vertex = 2 := by
    intro vertex hvertexComponent hvertexStart hvertexFinish
    have hnotInner : ∀ candidate : Fin 5,
        vertex.1 ≠ data.innerStub candidate := by
      intro candidate heq
      have hcandidateContains : ComponentContainsInnerStub
          data C first second component candidate :=
        ⟨vertex, hvertexComponent, heq⟩
      have hcandidateEq : candidate = inner :=
        hinnerUnique candidate hcandidateContains
      apply hvertexStart
      apply Subtype.ext
      calc
        vertex.1 = data.innerStub candidate := heq
        _ = data.innerStub inner := congrArg data.innerStub hcandidateEq
        _ = start.1 := hstartEq.symm
    have hnotOuter : ∀ candidate : Fin outerCount,
        vertex.1 ≠ data.outerStub candidate := by
      intro candidate heq
      have hcandidateContains : ComponentContainsOuterStub
          data C first second component candidate :=
        ⟨vertex, hvertexComponent, heq⟩
      have hcandidateEq : candidate = outer :=
        houterUnique candidate hcandidateContains
      apply hvertexFinish
      apply Subtype.ext
      calc
        vertex.1 = data.outerStub candidate := heq
        _ = data.outerStub outer := congrArg data.outerStub hcandidateEq
        _ = finish.1 := hfinishEq.symm
    rw [colorPairSupportGraph_degree_eq C first second vertex]
    exact colorPairGraph_degree_eq_two_of_cubic_tait C hC vertex.1
      (hdata.cubic_elsewhere vertex.1 hnotInner hnotOuter) hpair
  rcases
      exists_path_covering_component_of_endpoints_degree_one_of_degree_two_else
        (H := colorPairSupportGraph C first second) component
        hstartComponent hfinishComponent hstartFinish
        hstartDegree hfinishDegree hdegreeElse with
    ⟨path, hpath, hpathVertices⟩
  exact ⟨{
    inner := inner
    outer := outer
    start := start
    finish := finish
    start_mem := hstartComponent
    finish_mem := hfinishComponent
    start_eq_innerStub := hstartEq
    finish_eq_outerStub := hfinishEq
    path := path
    path_isPath := hpath
    path_vertices := hpathVertices
  }⟩

/-- With two active inner endpoints and radial component semantics, the
selected graph is exactly two radial paths, and those paths jointly cover
every vertex of the selected support graph. -/
theorem exists_two_radialPaths_covering_support_of_activeSupport_card_two
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    {first second : Color} (hpair : ValidColorPair first second)
    (hactive :
      (cap5ActiveSupport first second (data.innerBoundaryWord C)).card = 2)
    (hradial : EveryComponentRadial data C first second) :
    ∃ firstComponent secondComponent :
        (colorPairSupportGraph C first second).ConnectedComponent,
      firstComponent ≠ secondComponent ∧
      ∃ firstPath : ComponentRadialPath
          data C first second firstComponent,
        ∃ secondPath : ComponentRadialPath
            data C first second secondComponent,
          firstPath.path.toSubgraph.verts ∪
              secondPath.path.toSubgraph.verts = Set.univ := by
  classical
  rcases exists_exactly_two_components_of_activeSupport_card_two_of_radial
      data hdata C first second hactive hradial with
    ⟨firstComponent, secondComponent, hcomponentsNe, hallComponents⟩
  rcases nonempty_componentRadialPath
      data hdata C hC hpair hradial firstComponent with ⟨firstPath⟩
  rcases nonempty_componentRadialPath
      data hdata C hC hpair hradial secondComponent with ⟨secondPath⟩
  refine ⟨firstComponent, secondComponent, hcomponentsNe,
    firstPath, secondPath, Set.eq_univ_of_forall ?_⟩
  intro vertex
  let component :=
    (colorPairSupportGraph C first second).connectedComponentMk vertex
  rcases hallComponents component with hfirst | hsecond
  · apply Set.mem_union_left
    rw [firstPath.path_vertices]
    rw [← hfirst]
    exact ConnectedComponent.connectedComponentMk_mem
  · apply Set.mem_union_right
    rw [secondPath.path_vertices]
    rw [← hsecond]
    exact ConnectedComponent.connectedComponentMk_mem

/-- Every cubic Cell-3 interior vertex belongs to every valid selected color
pair's support graph. -/
theorem interior_mem_colorPairGraph_support
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    {first second : Color} (hpair : ValidColorPair first second)
    {vertex : V} (hvertex : vertex ∈ data.interiorVertices) :
    vertex ∈ (colorPairGraph C first second).support := by
  apply ((colorPairGraph C first second).degree_pos_iff_mem_support vertex).mp
  rw [AnnularBoundaryData.colorPairGraph_degree_interior_eq_two
    data hdata C hC hpair hvertex]
  omega

/-- Source-facing form: a good inner word and all-radial semantics produce
the singleton pair's two radial paths covering its support. -/
theorem exists_singletonPair_two_radialPaths_of_goodWord_of_allRadial
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (hgood : CAP5BoundaryWordHasColoredBlock311
      (data.innerBoundaryWord C))
    (hallRadial : EveryColorPairComponentRadial data C) :
    ∃ majority singletonFirst singletonSecond : Color,
      IsTaitColorTriple majority singletonFirst singletonSecond ∧
      ∃ firstComponent secondComponent :
          (colorPairSupportGraph C singletonFirst singletonSecond).ConnectedComponent,
        firstComponent ≠ secondComponent ∧
        ∃ firstPath : ComponentRadialPath
            data C singletonFirst singletonSecond firstComponent,
          ∃ secondPath : ComponentRadialPath
              data C singletonFirst singletonSecond secondComponent,
            firstPath.path.toSubgraph.verts ∪
                secondPath.path.toSubgraph.verts = Set.univ := by
  rcases exists_exact_pairEndpointCounts_of_coloredBlock311 hgood with
    ⟨majority, singletonFirst, singletonSecond, htriple,
      hsingletonCount, _hfirstCount, _hsecondCount⟩
  have hpair : ValidColorPair singletonFirst singletonSecond :=
    ⟨htriple.2.1, htriple.2.2.1, htriple.2.2.2.2.2⟩
  rcases exists_two_radialPaths_covering_support_of_activeSupport_card_two
      data hdata C hC hpair hsingletonCount
      (hallRadial singletonFirst singletonSecond hpair) with
    ⟨firstComponent, secondComponent, hne, firstPath, secondPath, hcover⟩
  exact ⟨majority, singletonFirst, singletonSecond, htriple,
    firstComponent, secondComponent, hne, firstPath, secondPath, hcover⟩

end GoertzelV24ClosedWebRadialComponents

end Mettapedia.GraphTheory.FourColor
