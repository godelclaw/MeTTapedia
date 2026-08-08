import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# A finite connected degree-two graph with two endpoints is a path

This small graph-theoretic module is the component classifier needed by the
v24 closed-web exactness argument.  It is intentionally independent of the
closed-web definitions: a connected finite simple graph with two distinct
degree-one vertices and degree two everywhere else has a simple path between
those endpoints whose vertex set is the whole graph.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24DegreeTwoSpanningPath

open SimpleGraph

variable {Vertex : Type*} {H : SimpleGraph Vertex}
  [Fintype Vertex] [DecidableEq Vertex] [DecidableRel H.Adj]

/-- A connected finite graph with two degree-one endpoints and maximum
degree two is one spanning path. -/
theorem exists_spanningPath_of_connected_of_endpoints_degree_one_of_degree_le_two_else
    (hconnected : H.Connected) {start finish : Vertex}
    (hstartFinish : start ≠ finish)
    (hstartDegree : H.degree start = 1)
    (hfinishDegree : H.degree finish = 1)
    (hdegreeElse :
      ∀ vertex : Vertex,
        vertex ≠ start → vertex ≠ finish → H.degree vertex ≤ 2) :
    ∃ path : H.Walk start finish,
      path.IsPath ∧ path.toSubgraph.verts = Set.univ := by
  classical
  obtain ⟨path, hpath⟩ := hconnected.exists_isPath start finish
  have hpathNotNil : ¬ path.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    by_contra hlength
    exact hstartFinish (path.eq_of_length_eq_zero (by omega))
  refine ⟨path, hpath, Set.eq_univ_of_forall ?_⟩
  intro vertex
  by_contra hvertexVerts
  have hvertexSupport : vertex ∉ path.support := by
    intro hvertex
    exact hvertexVerts (path.mem_verts_toSubgraph.mpr hvertex)
  obtain ⟨route, hroute⟩ := hconnected.exists_isPath vertex start
  let pathSupport : Finset Vertex := path.support.toFinset
  have hintersection :
      {candidate ∈ pathSupport | candidate ∈ route.support}.Nonempty := by
    refine ⟨start, by
      simp [pathSupport, path.start_mem_support, route.end_mem_support]⟩
  obtain ⟨firstHit, hfirstHitPath, hfirstHitRoute, hfirstHit⟩ :=
    route.exists_mem_support_forall_mem_support_imp_eq
      pathSupport hintersection
  have hfirstHitSupport : firstHit ∈ path.support := by
    simpa [pathSupport] using hfirstHitPath
  let routeToHit : H.Walk vertex firstHit :=
    route.takeUntil firstHit hfirstHitRoute
  have hrouteToHitNotNil : ¬ routeToHit.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    by_contra hlength
    have hvertexFirstHit : vertex ≠ firstHit := by
      intro heq
      exact hvertexSupport (heq ▸ hfirstHitSupport)
    exact hvertexFirstHit (routeToHit.eq_of_length_eq_zero (by omega))
  let predecessor : Vertex := routeToHit.penultimate
  have hpredecessorAdj : H.Adj predecessor firstHit :=
    routeToHit.adj_penultimate hrouteToHitNotNil
  have hpredecessorRoute : predecessor ∈ routeToHit.support := by
    exact SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr
      ⟨routeToHit.length - 1, rfl, Nat.sub_le _ _⟩
  have hpredecessorNotPath : predecessor ∉ path.support := by
    intro hpredecessorPath
    have hpredecessorEq : predecessor = firstHit :=
      hfirstHit predecessor (by simpa [pathSupport] using hpredecessorPath)
        hpredecessorRoute
    exact H.irrefl (hpredecessorEq ▸ hpredecessorAdj)
  rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hfirstHitSupport with
    ⟨index, hfirstHitIndex, hindexBound⟩
  by_cases hindexStart : index = 0
  · have hfirstHitStart : firstHit = start := by
      calc
        firstHit = path.getVert index := hfirstHitIndex.symm
        _ = start := (hpath.getVert_eq_start_iff hindexBound).2 hindexStart
    have hnextAdj : H.Adj start path.snd := path.adj_snd hpathNotNil
    have hnextSupport : path.snd ∈ path.support := by
      exact SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr
        ⟨1, by simp [SimpleGraph.Walk.snd], by
          have hpositive : 0 < path.length :=
            SimpleGraph.Walk.not_nil_iff_lt_length.mp hpathNotNil
          omega⟩
    have hpredecessorAdjStart : H.Adj start predecessor := by
      simpa [hfirstHitStart] using hpredecessorAdj.symm
    have hnextNePredecessor : path.snd ≠ predecessor := by
      intro heq
      exact hpredecessorNotPath (heq.symm ▸ hnextSupport)
    let neighbors : Finset Vertex := {path.snd, predecessor}
    have hneighborsSubset : neighbors ⊆ H.neighborFinset start := by
      intro candidate hcandidate
      simp [neighbors] at hcandidate
      rcases hcandidate with rfl | rfl
      · simpa using hnextAdj
      · simpa using hpredecessorAdjStart
    have hneighborsCard : neighbors.card = 2 := by
      simp [neighbors, hnextNePredecessor]
    have hstartDegreeAtLeastTwo : 2 ≤ H.degree start := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      calc
        2 = neighbors.card := by simp [hneighborsCard]
        _ ≤ (H.neighborFinset start).card :=
          Finset.card_le_card hneighborsSubset
    omega
  · by_cases hindexFinish : index = path.length
    · have hfirstHitFinish : firstHit = finish := by
        calc
          firstHit = path.getVert index := hfirstHitIndex.symm
          _ = finish := (hpath.getVert_eq_end_iff hindexBound).2 hindexFinish
      have hpreviousAdj : H.Adj finish path.penultimate :=
        (path.adj_penultimate hpathNotNil).symm
      have hpreviousSupport : path.penultimate ∈ path.support := by
        exact SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr
          ⟨path.length - 1, rfl, Nat.sub_le _ _⟩
      have hpredecessorAdjFinish : H.Adj finish predecessor := by
        simpa [hfirstHitFinish] using hpredecessorAdj.symm
      have hpreviousNePredecessor : path.penultimate ≠ predecessor := by
        intro heq
        exact hpredecessorNotPath (heq.symm ▸ hpreviousSupport)
      let neighbors : Finset Vertex := {path.penultimate, predecessor}
      have hneighborsSubset : neighbors ⊆ H.neighborFinset finish := by
        intro candidate hcandidate
        simp [neighbors] at hcandidate
        rcases hcandidate with rfl | rfl
        · simpa using hpreviousAdj
        · simpa using hpredecessorAdjFinish
      have hneighborsCard : neighbors.card = 2 := by
        simp [neighbors, hpreviousNePredecessor]
      have hfinishDegreeAtLeastTwo : 2 ≤ H.degree finish := by
        rw [← SimpleGraph.card_neighborFinset_eq_degree]
        calc
          2 = neighbors.card := by simp [hneighborsCard]
          _ ≤ (H.neighborFinset finish).card :=
            Finset.card_le_card hneighborsSubset
      omega
    · have hindexLt : index < path.length := by omega
      have hfirstHitNeStart : firstHit ≠ start := by
        intro heq
        have : index = 0 :=
          (hpath.getVert_eq_start_iff hindexBound).1
            (by simp [hfirstHitIndex, heq])
        exact hindexStart this
      have hfirstHitNeFinish : firstHit ≠ finish := by
        intro heq
        have : index = path.length :=
          (hpath.getVert_eq_end_iff hindexBound).1
            (by simp [hfirstHitIndex, heq])
        exact hindexFinish this
      let previous : Vertex := path.getVert (index - 1)
      let next : Vertex := path.getVert (index + 1)
      have hpreviousAdj : H.Adj firstHit previous := by
        have hpreviousIndex : index - 1 < path.length := by omega
        have hadj :
            H.Adj (path.getVert (index - 1))
              (path.getVert ((index - 1) + 1)) :=
          path.adj_getVert_succ hpreviousIndex
        have hsub : index - 1 + 1 = index :=
          Nat.sub_add_cancel (Nat.pos_of_ne_zero hindexStart)
        simpa [previous, hfirstHitIndex, hsub] using hadj.symm
      have hnextAdj : H.Adj firstHit next := by
        have hadj : H.Adj (path.getVert index) (path.getVert (index + 1)) :=
          path.adj_getVert_succ hindexLt
        simpa [next, hfirstHitIndex] using hadj
      have hpreviousSupport : previous ∈ path.support := by
        exact SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr
          ⟨index - 1, by simp [previous], by omega⟩
      have hnextSupport : next ∈ path.support := by
        exact SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr
          ⟨index + 1, by simp [next], by omega⟩
      have hpredecessorNePrevious : predecessor ≠ previous := by
        intro heq
        exact hpredecessorNotPath (heq ▸ hpreviousSupport)
      have hpredecessorNeNext : predecessor ≠ next := by
        intro heq
        exact hpredecessorNotPath (heq ▸ hnextSupport)
      have hpreviousNeNext : previous ≠ next := by
        intro heq
        have hindices : index - 1 = index + 1 :=
          hpath.getVert_injOn
            (by rw [Set.mem_setOf_eq]; omega)
            (by rw [Set.mem_setOf_eq]; omega)
            (by simpa [previous, next] using heq)
        omega
      let neighbors : Finset Vertex := {predecessor, previous, next}
      have hneighborsSubset : neighbors ⊆ H.neighborFinset firstHit := by
        intro candidate hcandidate
        simp [neighbors] at hcandidate
        rcases hcandidate with rfl | rfl | rfl
        · simpa using hpredecessorAdj.symm
        · simpa using hpreviousAdj
        · simpa using hnextAdj
      have hneighborsCard : neighbors.card = 3 := by
        simp [neighbors, hpredecessorNePrevious, hpredecessorNeNext,
          hpreviousNeNext]
      have hfirstHitDegreeAtLeastThree : 3 ≤ H.degree firstHit := by
        rw [← SimpleGraph.card_neighborFinset_eq_degree]
        calc
          3 = neighbors.card := by simp [hneighborsCard]
          _ ≤ (H.neighborFinset firstHit).card :=
            Finset.card_le_card hneighborsSubset
      have hfirstHitDegreeAtMostTwo : H.degree firstHit ≤ 2 :=
        hdegreeElse firstHit hfirstHitNeStart hfirstHitNeFinish
      omega

/-- Exact-degree specialization of the maximum-degree spanning-path
classifier. -/
theorem exists_spanningPath_of_connected_of_endpoints_degree_one_of_degree_two_else
    (hconnected : H.Connected) {start finish : Vertex}
    (hstartFinish : start ≠ finish)
    (hstartDegree : H.degree start = 1)
    (hfinishDegree : H.degree finish = 1)
    (hdegreeElse :
      ∀ vertex : Vertex,
        vertex ≠ start → vertex ≠ finish → H.degree vertex = 2) :
    ∃ path : H.Walk start finish,
      path.IsPath ∧ path.toSubgraph.verts = Set.univ := by
  apply exists_spanningPath_of_connected_of_endpoints_degree_one_of_degree_le_two_else
    hconnected hstartFinish hstartDegree hfinishDegree
  intro vertex hvertexStart hvertexFinish
  exact (hdegreeElse vertex hvertexStart hvertexFinish).le

/-- Component-local maximum-degree form: two degree-one vertices in a
maximum-degree-two component are joined by a path covering that component. -/
theorem exists_path_covering_component_of_endpoints_degree_one_of_degree_le_two_else
    (component : H.ConnectedComponent) {start finish : Vertex}
    (hstartComponent : start ∈ component.supp)
    (hfinishComponent : finish ∈ component.supp)
    (hstartFinish : start ≠ finish)
    (hstartDegree : H.degree start = 1)
    (hfinishDegree : H.degree finish = 1)
    (hdegreeElse :
      ∀ vertex : Vertex,
        vertex ∈ component.supp →
        vertex ≠ start → vertex ≠ finish → H.degree vertex ≤ 2) :
    ∃ path : H.Walk start finish,
      path.IsPath ∧ path.toSubgraph.verts = component.supp := by
  classical
  let componentGraph : SimpleGraph component.supp :=
    H.induce component.supp
  have hcomponentGraphConnected : componentGraph.Connected := by
    simpa [componentGraph, SimpleGraph.ConnectedComponent.toSimpleGraph] using
      component.connected_toSimpleGraph
  have hdegreeInduce :
      ∀ vertex : component.supp,
        componentGraph.degree vertex = H.degree vertex := by
    intro vertex
    have hneighborSubset : H.neighborSet vertex ⊆ component.supp := by
      intro neighbor hadjacent
      exact component.mem_supp_of_adj_mem_supp vertex.property hadjacent
    simpa [componentGraph] using
      (SimpleGraph.degree_induce_of_neighborSet_subset
        (G := H) (s := component.supp) (v := vertex) hneighborSubset)
  let startInComponent : component.supp := ⟨start, hstartComponent⟩
  let finishInComponent : component.supp := ⟨finish, hfinishComponent⟩
  have hstartDegreeComponent :
      componentGraph.degree startInComponent = 1 := by
    rw [hdegreeInduce]
    exact hstartDegree
  have hfinishDegreeComponent :
      componentGraph.degree finishInComponent = 1 := by
    rw [hdegreeInduce]
    exact hfinishDegree
  have hstartFinishComponent : startInComponent ≠ finishInComponent := by
    intro heq
    exact hstartFinish (Subtype.ext_iff.mp heq)
  have hdegreeElseComponent :
      ∀ vertex : component.supp,
        vertex ≠ startInComponent →
        vertex ≠ finishInComponent →
        componentGraph.degree vertex ≤ 2 := by
    intro vertex hvertexStart hvertexFinish
    rw [hdegreeInduce]
    exact hdegreeElse vertex vertex.property
      (fun heq => hvertexStart (Subtype.ext heq))
      (fun heq => hvertexFinish (Subtype.ext heq))
  rcases exists_spanningPath_of_connected_of_endpoints_degree_one_of_degree_le_two_else
      (H := componentGraph) hcomponentGraphConnected hstartFinishComponent
      hstartDegreeComponent hfinishDegreeComponent hdegreeElseComponent with
    ⟨path, hpath, hpathVertices⟩
  let inclusion : componentGraph →g H :=
    { toFun := fun vertex => vertex.1
      map_rel' := by
        intro first second hadjacent
        exact hadjacent }
  refine ⟨path.map inclusion, ?_, ?_⟩
  · exact SimpleGraph.Walk.map_isPath_of_injective
      Subtype.val_injective hpath
  · ext vertex
    constructor
    · intro hvertex
      rw [SimpleGraph.Walk.mem_verts_toSubgraph,
        SimpleGraph.Walk.support_map] at hvertex
      rcases List.mem_map.mp hvertex with ⟨source, _hsource, rfl⟩
      exact source.property
    · intro hvertex
      rw [SimpleGraph.Walk.mem_verts_toSubgraph,
        SimpleGraph.Walk.support_map]
      refine List.mem_map.mpr ?_
      refine ⟨⟨vertex, hvertex⟩, ?_, rfl⟩
      rw [← SimpleGraph.Walk.mem_verts_toSubgraph, hpathVertices]
      simp

/-- Exact-degree specialization of the component-local classifier. -/
theorem exists_path_covering_component_of_endpoints_degree_one_of_degree_two_else
    (component : H.ConnectedComponent) {start finish : Vertex}
    (hstartComponent : start ∈ component.supp)
    (hfinishComponent : finish ∈ component.supp)
    (hstartFinish : start ≠ finish)
    (hstartDegree : H.degree start = 1)
    (hfinishDegree : H.degree finish = 1)
    (hdegreeElse :
      ∀ vertex : Vertex,
        vertex ∈ component.supp →
        vertex ≠ start → vertex ≠ finish → H.degree vertex = 2) :
    ∃ path : H.Walk start finish,
      path.IsPath ∧ path.toSubgraph.verts = component.supp := by
  apply exists_path_covering_component_of_endpoints_degree_one_of_degree_le_two_else
    component hstartComponent hfinishComponent hstartFinish
      hstartDegree hfinishDegree
  intro vertex hvertexComponent hvertexStart hvertexFinish
  exact (hdegreeElse vertex hvertexComponent
    hvertexStart hvertexFinish).le

end GoertzelV24DegreeTwoSpanningPath

end Mettapedia.GraphTheory.FourColor
