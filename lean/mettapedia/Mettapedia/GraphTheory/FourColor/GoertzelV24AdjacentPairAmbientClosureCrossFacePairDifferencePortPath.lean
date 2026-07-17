import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceCycle
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionPrimalCircuit

namespace SimpleGraph.Walk

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- A simple cycle containing an edge can be rooted and oriented so that
the prescribed edge is its first edge, without changing edge membership. -/
theorem IsCycle.exists_oriented_at_edge
    [DecidableEq V]
    {root first second : V} {cycle : G.Walk root root}
    (hcycle : cycle.IsCycle) (hedge : s(first, second) ∈ cycle.edges) :
    ∃ oriented : G.Walk first first,
      oriented.IsCycle ∧ oriented.snd = second ∧
        ∀ edge : Sym2 V, edge ∈ oriented.edges ↔ edge ∈ cycle.edges := by
  have hfirst : first ∈ cycle.support :=
    cycle.fst_mem_support_of_mem_edges hedge
  let rotated := cycle.rotate first hfirst
  have hrotatedCycle : rotated.IsCycle := hcycle.rotate hfirst
  have hedgeRotated : s(first, second) ∈ rotated.edges :=
    (cycle.rotate_edges first hfirst).mem_iff.mpr hedge
  have hadj : rotated.toSubgraph.Adj first second :=
    Subgraph.mem_edgeSet.mp
      (rotated.mem_edges_toSubgraph.mpr hedgeRotated)
  have hneighbor : second ∈ rotated.toSubgraph.neighborSet first := hadj
  rw [hrotatedCycle.neighborSet_toSubgraph_endpoint] at hneighbor
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hneighbor
  rcases hneighbor with hsnd | hpenultimate
  · refine ⟨rotated, hrotatedCycle, hsnd.symm, ?_⟩
    intro edge
    exact (cycle.rotate_edges first hfirst).mem_iff
  · refine ⟨rotated.reverse, hrotatedCycle.reverse, ?_, ?_⟩
    · simpa only [SimpleGraph.Walk.snd_reverse] using hpenultimate.symm
    · intro edge
      rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse]
      exact (cycle.rotate_edges first hfirst).mem_iff

end SimpleGraph.Walk

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary
open GoertzelV24FaceBoundaryLinearAlgebra
open GoertzelV24MinimalFaceIntersections
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraphDartRotation

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

omit [Fintype V] [DecidableRel G.Adj] in
/-- Removing the restored central edge from a simple ambient cycle leaves
a simple retained path from a port on the second deleted vertex to a port
on the first.  Its ambient edge list remains inside the original cycle. -/
theorem exists_crossSide_retainedPortPath_of_central_cycle
    (data : AdjacentPairData G)
    {root : V} {cycle : G.Walk root root}
    (hcycle : cycle.IsCycle)
    (hcentral : (centralEdge data : Sym2 V) ∈ cycle.edges) :
    ∃ (secondPort firstPort : Fin 4)
        (path : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk
            (data.retainedPort secondPort) (data.retainedPort firstPort)),
      (secondPort = 2 ∨ secondPort = 3) ∧
        (firstPort = 0 ∨ firstPort = 1) ∧
        path.IsPath ∧
        (data.retainedWalkToAmbient path).edges ⊆ cycle.edges := by
  have hcentralValue :
      s(data.firstVertex, data.secondVertex) ∈ cycle.edges := by
    simpa [centralEdge, centralEdgeValue] using hcentral
  rcases hcycle.exists_oriented_at_edge hcentralValue with
    ⟨oriented, horientedCycle, horientedSnd, horientedEdges⟩
  let returnPath : G.Walk data.secondVertex data.firstVertex :=
    oriented.tail.copy horientedSnd rfl
  have hreturnPath : returnPath.IsPath := by
    simpa [returnPath] using horientedCycle.isPath_tail
  have hreturnLength : returnPath.length + 1 = oriented.length := by
    simpa [returnPath] using
      oriented.length_tail_add_one horientedCycle.not_nil
  have hreturnLengthTwo : 2 ≤ returnPath.length := by
    have := horientedCycle.three_le_length
    omega
  have hreturnNotNil : ¬returnPath.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    omega
  have hreturnTailLength : returnPath.tail.length + 1 = returnPath.length :=
    returnPath.length_tail_add_one hreturnNotNil
  have hreturnTailNotNil : ¬returnPath.tail.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    omega
  have hstartNotFirst : returnPath.snd ≠ data.firstVertex := by
    intro hstart
    have hindex := (hreturnPath.getVert_eq_end_iff
      (i := 1) (by omega)).mp hstart
    omega
  have hstartCases :
      returnPath.snd = data.firstVertex ∨
        returnPath.snd = data.portVertex 2 ∨
        returnPath.snd = data.portVertex 3 := by
    have hneighbor : returnPath.snd ∈
        G.neighborSet data.secondVertex :=
      returnPath.adj_snd hreturnNotNil
    rw [data.secondNeighbors] at hneighbor
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hneighbor
  obtain ⟨secondPort, hsecondSide, hsecondEndpoint⟩ :
      ∃ secondPort : Fin 4,
        (secondPort = 2 ∨ secondPort = 3) ∧
          returnPath.snd = data.portVertex secondPort := by
    rcases hstartCases with hfirst | htwo | hthree
    · exact False.elim (hstartNotFirst hfirst)
    · exact ⟨2, Or.inl rfl, htwo⟩
    · exact ⟨3, Or.inr rfl, hthree⟩
  have hpenultimateEq :
      returnPath.penultimate = returnPath.tail.penultimate := by
    calc
      returnPath.penultimate =
          (SimpleGraph.Walk.cons (returnPath.adj_snd hreturnNotNil)
            returnPath.tail).penultimate :=
        congrArg SimpleGraph.Walk.penultimate
          (returnPath.cons_tail_eq hreturnNotNil).symm
      _ = returnPath.tail.penultimate :=
        SimpleGraph.Walk.penultimate_cons_of_not_nil _ _
          hreturnTailNotNil
  have hendNotSecond :
      returnPath.tail.penultimate ≠ data.secondVertex := by
    intro hend
    have hpenultimate :
        returnPath.penultimate = data.secondVertex := by
      rw [hpenultimateEq]
      exact hend
    have hindex := (hreturnPath.getVert_eq_start_iff
      (i := returnPath.length - 1) (Nat.sub_le _ _)).mp hpenultimate
    omega
  have hendCases :
      returnPath.tail.penultimate = data.secondVertex ∨
        returnPath.tail.penultimate = data.portVertex 0 ∨
        returnPath.tail.penultimate = data.portVertex 1 := by
    have hneighbor : returnPath.tail.penultimate ∈
        G.neighborSet data.firstVertex :=
      (returnPath.tail.adj_penultimate hreturnTailNotNil).symm
    rw [data.firstNeighbors] at hneighbor
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hneighbor
  obtain ⟨firstPort, hfirstSide, hfirstEndpoint⟩ :
      ∃ firstPort : Fin 4,
        (firstPort = 0 ∨ firstPort = 1) ∧
          returnPath.tail.penultimate = data.portVertex firstPort := by
    rcases hendCases with hsecond | hzero | hone
    · exact False.elim (hendNotSecond hsecond)
    · exact ⟨0, Or.inl rfl, hzero⟩
    · exact ⟨1, Or.inr rfl, hone⟩
  let middle : G.Walk returnPath.snd returnPath.tail.penultimate :=
    returnPath.tail.dropLast
  have hmiddlePath : middle.IsPath := by
    change returnPath.tail.dropLast.IsPath
    exact hreturnPath.tail.take (returnPath.tail.length - 1)
  have hmiddleSupportEq :
      middle.support = returnPath.support.tail.dropLast := by
    change returnPath.tail.dropLast.support = _
    rw [SimpleGraph.Walk.support_dropLast hreturnTailNotNil,
      returnPath.support_tail_of_not_nil hreturnNotNil]
  have hmiddleSupport : ∀ vertex ∈ middle.support,
      vertex ∈ retainedVertexSet data.firstVertex data.secondVertex := by
    intro vertex hvertex
    rw [hmiddleSupportEq] at hvertex
    constructor
    · intro hfirst
      subst vertex
      exact hreturnPath.end_not_mem_support_tail_dropLast hvertex
    · intro hsecond
      subst vertex
      exact hreturnPath.start_not_mem_support_tail
        (List.mem_of_mem_dropLast hvertex)
  let induced := middle.induce
    (retainedVertexSet data.firstVertex data.secondVertex) hmiddleSupport
  have hinducedPath : induced.IsPath := by
    have hmapped :
        (induced.map (SimpleGraph.Embedding.induce
          (retainedVertexSet data.firstVertex data.secondVertex)).toHom).IsPath := by
      change ((middle.induce
        (retainedVertexSet data.firstVertex data.secondVertex)
          hmiddleSupport).map (SimpleGraph.Embedding.induce
            (retainedVertexSet data.firstVertex data.secondVertex)).toHom).IsPath
      rw [SimpleGraph.Walk.map_induce]
      exact hmiddlePath
    exact SimpleGraph.Walk.IsPath.of_map hmapped
  have hinducedStart :
      (⟨returnPath.snd,
          hmiddleSupport returnPath.snd middle.start_mem_support⟩ :
        retainedVertexSet data.firstVertex data.secondVertex) =
        data.retainedPort secondPort := by
    apply Subtype.ext
    exact hsecondEndpoint
  have hinducedEnd :
      (⟨returnPath.tail.penultimate,
          hmiddleSupport returnPath.tail.penultimate middle.end_mem_support⟩ :
        retainedVertexSet data.firstVertex data.secondVertex) =
        data.retainedPort firstPort := by
    apply Subtype.ext
    exact hfirstEndpoint
  let path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk
        (data.retainedPort secondPort) (data.retainedPort firstPort) :=
    induced.copy hinducedStart hinducedEnd
  have hpath : path.IsPath := by
    simpa [path] using hinducedPath
  have hretainedHom : data.retainedGraphHom =
      (SimpleGraph.Embedding.induce
        (retainedVertexSet data.firstVertex data.secondVertex)).toHom := rfl
  have hambientPathEdges :
      (data.retainedWalkToAmbient path).edges = middle.edges := by
    calc
      (data.retainedWalkToAmbient path).edges =
          (induced.map data.retainedGraphHom).edges := by
        simp [path,
          GoertzelV24AdjacentPairBoundary.AdjacentPairData.retainedWalkToAmbient]
      _ = middle.edges := by
        rw [hretainedHom]
        exact congrArg SimpleGraph.Walk.edges
          (SimpleGraph.Walk.map_induce middle hmiddleSupport)
  have hmiddleEdges : middle.edges ⊆ returnPath.edges := by
    intro edge hedge
    change edge ∈ (returnPath.tail.take
      (returnPath.tail.length - 1)).edges at hedge
    rw [SimpleGraph.Walk.edges_take] at hedge
    have htail : edge ∈ returnPath.tail.edges :=
      List.mem_of_mem_take hedge
    rw [← returnPath.cons_tail_eq hreturnNotNil]
    simp only [SimpleGraph.Walk.edges_cons, List.mem_cons]
    exact Or.inr htail
  have hreturnEdges : returnPath.edges ⊆ oriented.edges := by
    intro edge hedge
    change edge ∈ (oriented.tail.copy horientedSnd rfl).edges at hedge
    rw [SimpleGraph.Walk.edges_copy] at hedge
    rw [← oriented.cons_tail_eq horientedCycle.not_nil]
    simp only [SimpleGraph.Walk.edges_cons, List.mem_cons]
    exact Or.inr hedge
  refine ⟨secondPort, firstPort, path, hsecondSide, hfirstSide,
    hpath, ?_⟩
  intro edge hedge
  rw [hambientPathEdges] at hedge
  exact (horientedEdges edge).mp (hreturnEdges (hmiddleEdges hedge))

/-- A nonzero central edge of a binary Kirchhoff flow on a finite cubic
graph supplies a simple cross-side retained path entirely supported by that
flow coordinate. -/
theorem exists_crossSide_scalarSupportPortPath
    (data : AdjacentPairData G)
    (flow : G.edgeSet → F2)
    (hflow : ∀ vertex : V,
      scalarVertexKirchhoffSum G flow vertex = 0)
    (hcubic : ∀ vertex : V,
      (incidentEdgeFinset G vertex).card = 3)
    (hcentral : flow (centralEdge data) ≠ 0) :
    ∃ (secondPort firstPort : Fin 4)
        (path : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk
            (data.retainedPort secondPort) (data.retainedPort firstPort)),
      (secondPort = 2 ∨ secondPort = 3) ∧
        (firstPort = 0 ∨ firstPort = 1) ∧
        path.IsPath ∧
        ∀ edge : G.edgeSet,
          (edge : Sym2 V) ∈ (data.retainedWalkToAmbient path).edges →
            flow edge ≠ 0 := by
  rcases exists_isCycle_through_of_scalar_ne_zero flow hflow hcubic
      (centralEdge data) hcentral with
    ⟨root, cycle, hcycle, hcentralCycle, hcycleSupport⟩
  rcases exists_crossSide_retainedPortPath_of_central_cycle data
      hcycle hcentralCycle with
    ⟨secondPort, firstPort, path, hsecondSide, hfirstSide,
      hpath, hpathSubset⟩
  refine ⟨secondPort, firstPort, path, hsecondSide, hfirstSide,
    hpath, ?_⟩
  intro edge hedge
  exact hcycleSupport edge (hpathSubset hedge)

/-- The cross-face difference flow contains a simple retained path joining
the two sides of the deleted pair, avoiding the retained cross, on which one
fixed binary coordinate is everywhere nonzero. -/
theorem CrossCentralExactFaceCutPair.exists_crossSide_coordinateSupportPortPath
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross) :
    ∃ (secondPort firstPort : Fin 4)
        (path : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk
            (data.retainedPort secondPort) (data.retainedPort firstPort)),
      (secondPort = 2 ∨ secondPort = 3) ∧
        (firstPort = 0 ∨ firstPort = 1) ∧
        path.IsPath ∧
        (cross : Sym2 (retainedVertexSet data.firstVertex
          data.secondVertex)) ∉ path.edges ∧
        ((∀ edge : (DeletedAdjacentPairGraph G data.firstVertex
              data.secondVertex).edgeSet,
            (edge : Sym2 (retainedVertexSet data.firstVertex
              data.secondVertex)) ∈ path.edges →
              (pair.crossFaceDifferenceProfile
                (retainedEdgeToAmbientEdge data edge)).1 ≠ 0) ∨
          (∀ edge : (DeletedAdjacentPairGraph G data.firstVertex
              data.secondVertex).edgeSet,
            (edge : Sym2 (retainedVertexSet data.firstVertex
              data.secondVertex)) ∈ path.edges →
              (pair.crossFaceDifferenceProfile
                (retainedEdgeToAmbientEdge data edge)).2 ≠ 0)) := by
  let difference : G.edgeSet → Color := pair.crossFaceDifferenceProfile
  have hdifference : IsGraphFlow G difference :=
    pair.crossFaceDifferenceProfile_isGraphFlow minimal
  have hfirstFlow : ∀ vertex : V,
      scalarVertexKirchhoffSum G (fun edge => (difference edge).1) vertex = 0 := by
    intro vertex
    rw [scalarVertexKirchhoffSum_fst]
    exact congrArg Prod.fst (hdifference vertex)
  have hsecondFlow : ∀ vertex : V,
      scalarVertexKirchhoffSum G (fun edge => (difference edge).2) vertex = 0 := by
    intro vertex
    rw [scalarVertexKirchhoffSum_snd]
    exact congrArg Prod.snd (hdifference vertex)
  have hcubic : ∀ vertex : V,
      (incidentEdgeFinset G vertex).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData minimal.spherical.cubic
  have hcentral : difference (centralEdge data) ≠ 0 := by
    simpa [difference] using
      pair.crossFaceDifferenceProfile_centralEdge_ne_zero minimal
  have hcross :
      difference (retainedEdgeToAmbientEdge data cross) = 0 := by
    simpa [difference] using
      pair.crossFaceDifferenceProfile_retainedCross minimal
  by_cases hfirst : (difference (centralEdge data)).1 = 0
  · have hsecond : (difference (centralEdge data)).2 ≠ 0 := by
      intro hzero
      exact hcentral (Prod.ext hfirst hzero)
    rcases exists_crossSide_scalarSupportPortPath data
        (fun edge => (difference edge).2) hsecondFlow hcubic hsecond with
      ⟨secondPort, firstPort, path, hsecondSide, hfirstSide,
        hpath, hsupport⟩
    have hcoordinate :
        ∀ edge : (DeletedAdjacentPairGraph G data.firstVertex
            data.secondVertex).edgeSet,
          (edge : Sym2 (retainedVertexSet data.firstVertex
            data.secondVertex)) ∈ path.edges →
            (pair.crossFaceDifferenceProfile
              (retainedEdgeToAmbientEdge data edge)).2 ≠ 0 := by
      intro edge hedge
      change (difference (retainedEdgeToAmbientEdge data edge)).2 ≠ 0
      apply hsupport (retainedEdgeToAmbientEdge data edge)
      exact (retainedEdgeToAmbientEdge_mem_retainedWalkToAmbient_edges_iff
        data path edge).2 hedge
    have hcrossAvoided :
        (cross : Sym2 (retainedVertexSet data.firstVertex
          data.secondVertex)) ∉ path.edges := by
      intro hmem
      exact hcoordinate cross hmem (congrArg Prod.snd hcross)
    exact ⟨secondPort, firstPort, path, hsecondSide, hfirstSide,
      hpath, hcrossAvoided, Or.inr hcoordinate⟩
  · rcases exists_crossSide_scalarSupportPortPath data
        (fun edge => (difference edge).1) hfirstFlow hcubic hfirst with
      ⟨secondPort, firstPort, path, hsecondSide, hfirstSide,
        hpath, hsupport⟩
    have hcoordinate :
        ∀ edge : (DeletedAdjacentPairGraph G data.firstVertex
            data.secondVertex).edgeSet,
          (edge : Sym2 (retainedVertexSet data.firstVertex
            data.secondVertex)) ∈ path.edges →
            (pair.crossFaceDifferenceProfile
              (retainedEdgeToAmbientEdge data edge)).1 ≠ 0 := by
      intro edge hedge
      change (difference (retainedEdgeToAmbientEdge data edge)).1 ≠ 0
      apply hsupport (retainedEdgeToAmbientEdge data edge)
      exact (retainedEdgeToAmbientEdge_mem_retainedWalkToAmbient_edges_iff
        data path edge).2 hedge
    have hcrossAvoided :
        (cross : Sym2 (retainedVertexSet data.firstVertex
          data.secondVertex)) ∉ path.edges := by
      intro hmem
      exact hcoordinate cross hmem (congrArg Prod.fst hcross)
    exact ⟨secondPort, firstPort, path, hsecondSide, hfirstSide,
      hpath, hcrossAvoided, Or.inl hcoordinate⟩

/-- Forgetting which scalar coordinate supports the path gives a simple
cross-side retained path of strict cross-face profile disagreements. -/
theorem CrossCentralExactFaceCutPair.exists_crossSide_differenceSupportPortPath
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross) :
    ∃ (secondPort firstPort : Fin 4)
        (path : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk
            (data.retainedPort secondPort) (data.retainedPort firstPort)),
      (secondPort = 2 ∨ secondPort = 3) ∧
        (firstPort = 0 ∨ firstPort = 1) ∧
        path.IsPath ∧
        (cross : Sym2 (retainedVertexSet data.firstVertex
          data.secondVertex)) ∉ path.edges ∧
        ∀ edge : (DeletedAdjacentPairGraph G data.firstVertex
            data.secondVertex).edgeSet,
          (edge : Sym2 (retainedVertexSet data.firstVertex
            data.secondVertex)) ∈ path.edges →
            pair.crossFaceDifferenceProfile
              (retainedEdgeToAmbientEdge data edge) ≠ 0 := by
  rcases pair.exists_crossSide_coordinateSupportPortPath minimal with
    ⟨secondPort, firstPort, path, hsecondSide, hfirstSide,
      hpath, hcross, hfirstCoordinate | hsecondCoordinate⟩
  · refine ⟨secondPort, firstPort, path, hsecondSide, hfirstSide,
      hpath, hcross, ?_⟩
    intro edge hedge hzero
    exact hfirstCoordinate edge hedge (congrArg Prod.fst hzero)
  · refine ⟨secondPort, firstPort, path, hsecondSide, hfirstSide,
      hpath, hcross, ?_⟩
    intro edge hedge hzero
    exact hsecondCoordinate edge hedge (congrArg Prod.snd hzero)

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
