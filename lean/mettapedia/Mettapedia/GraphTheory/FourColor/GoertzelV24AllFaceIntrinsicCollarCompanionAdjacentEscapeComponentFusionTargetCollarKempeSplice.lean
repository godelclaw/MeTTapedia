import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionAdjacentEscapeComponentFusionTargetCollarKempeRoutes

set_option autoImplicit false

namespace SimpleGraph.Walk

universe u

variable {Vertex : Type u} [DecidableEq Vertex]
  {Graph : SimpleGraph Vertex}
  {left right : Vertex}

/-- Replace the first passage through an internal vertex by an arbitrary
walk between the predecessor and successor of that passage. -/
def replaceInternalVertex
    (walk : Graph.Walk left right) (vertex : Vertex)
    (hvertex : vertex ∈ walk.support)
    (replacement : Graph.Walk
      (walk.takeUntil vertex hvertex).penultimate
      (walk.dropUntil vertex hvertex).snd) :
    Graph.Walk left right :=
  (walk.takeUntil vertex hvertex).dropLast.append
    (replacement.append (walk.dropUntil vertex hvertex).tail)

/-- Internal-vertex replacement has the literal prefix, replacement, and
suffix edge word. -/
theorem replaceInternalVertex_edges
    (walk : Graph.Walk left right) (vertex : Vertex)
    (hvertex : vertex ∈ walk.support)
    (replacement : Graph.Walk
      (walk.takeUntil vertex hvertex).penultimate
      (walk.dropUntil vertex hvertex).snd) :
    (walk.replaceInternalVertex vertex hvertex replacement).edges =
      (walk.takeUntil vertex hvertex).dropLast.edges ++
        replacement.edges ++
          (walk.dropUntil vertex hvertex).tail.edges := by
  simp [replaceInternalVertex, SimpleGraph.Walk.edges_append,
    List.append_assoc]

/-- Every edge after internal-vertex replacement came from the old walk or
from the inserted walk. -/
theorem mem_edges_replaceInternalVertex
    (walk : Graph.Walk left right) (vertex : Vertex)
    (hvertex : vertex ∈ walk.support)
    (replacement : Graph.Walk
      (walk.takeUntil vertex hvertex).penultimate
      (walk.dropUntil vertex hvertex).snd)
    {edge : Sym2 Vertex}
    (hedge : edge ∈
      (walk.replaceInternalVertex vertex hvertex replacement).edges) :
    edge ∈ walk.edges ∨ edge ∈ replacement.edges := by
  simp only [replaceInternalVertex, SimpleGraph.Walk.edges_append,
    List.mem_append] at hedge
  rcases hedge with hprefix | hreplacement | hsuffix
  · apply Or.inl
    apply walk.edges_takeUntil_subset_edges hvertex
    rw [SimpleGraph.Walk.dropLast, SimpleGraph.Walk.edges_take] at hprefix
    exact List.mem_of_mem_take hprefix
  · exact Or.inr hreplacement
  · apply Or.inl
    apply walk.edges_dropUntil_subset_edges hvertex
    rw [SimpleGraph.Walk.tail, SimpleGraph.Walk.edges_drop] at hsuffix
    exact List.mem_of_mem_drop hsuffix

/-- Every vertex after internal-vertex replacement came from the old walk
or from the inserted walk. -/
theorem mem_support_replaceInternalVertex
    (walk : Graph.Walk left right) (vertex : Vertex)
    (hvertex : vertex ∈ walk.support)
    (replacement : Graph.Walk
      (walk.takeUntil vertex hvertex).penultimate
      (walk.dropUntil vertex hvertex).snd)
    {point : Vertex}
    (hpoint : point ∈
      (walk.replaceInternalVertex vertex hvertex replacement).support) :
    point ∈ walk.support ∨ point ∈ replacement.support := by
  simp only [replaceInternalVertex,
    SimpleGraph.Walk.mem_support_append_iff] at hpoint
  rcases hpoint with hbefore | hreplacement | hafter
  · exact Or.inl <|
      ((walk.isSubwalk_takeUntil hvertex).dropLast.support_subset hbefore)
  · exact Or.inr hreplacement
  · exact Or.inl <|
      ((walk.isSubwalk_dropUntil hvertex).tail.support_subset hafter)

/-- Replacing an internal vertex of a simple path by a walk that avoids
that vertex removes it from the resulting support. -/
theorem replaceInternalVertex_not_mem_support
    (walk : Graph.Walk left right) (vertex : Vertex)
    (hpath : walk.IsPath)
    (hvertex : vertex ∈ walk.support)
    (hleft : left ≠ vertex) (hright : right ≠ vertex)
    (replacement : Graph.Walk
      (walk.takeUntil vertex hvertex).penultimate
      (walk.dropUntil vertex hvertex).snd)
    (hreplacement : ¬ vertex ∈ replacement.support) :
    ¬ vertex ∈
      (walk.replaceInternalVertex vertex hvertex replacement).support := by
  let before : Graph.Walk left vertex :=
    walk.takeUntil vertex hvertex
  let after : Graph.Walk vertex right :=
    walk.dropUntil vertex hvertex
  have beforeNotNil : ¬ before.Nil := by
    exact SimpleGraph.Walk.not_nil_of_ne hleft
  have afterNotNil : ¬ after.Nil := by
    exact SimpleGraph.Walk.not_nil_of_ne hright.symm
  have beforePath : before.IsPath := hpath.takeUntil hvertex
  have afterPath : after.IsPath := hpath.dropUntil hvertex
  have vertexNotBefore : ¬ vertex ∈ before.dropLast.support := by
    have hnodup := beforePath.support_nodup
    rw [← before.support_dropLast_concat beforeNotNil] at hnodup
    have hconcat :
        (before.dropLast.support.concat vertex).Nodup := by
      simpa only [List.concat_eq_append] using hnodup
    exact ((List.nodup_concat before.dropLast.support vertex).mp hconcat).1
  have vertexNotAfter : ¬ vertex ∈ after.tail.support := by
    have hnodup := afterPath.support_nodup
    rw [← after.cons_support_tail afterNotNil] at hnodup
    exact (List.nodup_cons.mp hnodup).1
  simp only [replaceInternalVertex,
    SimpleGraph.Walk.mem_support_append_iff, not_or]
  exact ⟨vertexNotBefore, hreplacement, vertexNotAfter⟩

/-- Path bypass after replacement retains the vertex avoidance just proved. -/
theorem bypass_replaceInternalVertex_not_mem_support
    (walk : Graph.Walk left right) (vertex : Vertex)
    (hpath : walk.IsPath)
    (hvertex : vertex ∈ walk.support)
    (hleft : left ≠ vertex) (hright : right ≠ vertex)
    (replacement : Graph.Walk
      (walk.takeUntil vertex hvertex).penultimate
      (walk.dropUntil vertex hvertex).snd)
    (hreplacement : ¬ vertex ∈ replacement.support) :
    ¬ vertex ∈
      (walk.replaceInternalVertex vertex hvertex replacement).bypass.support := by
  intro hmem
  exact walk.replaceInternalVertex_not_mem_support vertex hpath hvertex
    hleft hright replacement hreplacement
      ((walk.replaceInternalVertex vertex hvertex replacement
        ).support_bypass_subset_support hmem)

/-- At an internal vertex with three displayed neighbors, a simple path
that avoids the edge to the excluded neighbor must enter and leave through
the other two neighbors, in one of the two orientations. -/
theorem internalPassage_orientation_of_neighborSet_eq_triple
    (walk : Graph.Walk left right) (vertex excluded firstExit secondExit : Vertex)
    (hpath : walk.IsPath)
    (hvertex : vertex ∈ walk.support)
    (hleft : left ≠ vertex) (hright : right ≠ vertex)
    (hneighbors : Graph.neighborSet vertex =
      ({excluded, firstExit, secondExit} : Set Vertex))
    (hforbidden : s(vertex, excluded) ∉ walk.edges) :
    (((walk.takeUntil vertex hvertex).penultimate = firstExit ∧
        (walk.dropUntil vertex hvertex).snd = secondExit) ∨
      ((walk.takeUntil vertex hvertex).penultimate = secondExit ∧
        (walk.dropUntil vertex hvertex).snd = firstExit)) := by
  let before : Graph.Walk left vertex := walk.takeUntil vertex hvertex
  let after : Graph.Walk vertex right := walk.dropUntil vertex hvertex
  have beforeNotNil : ¬ before.Nil :=
    SimpleGraph.Walk.not_nil_of_ne hleft
  have afterNotNil : ¬ after.Nil :=
    SimpleGraph.Walk.not_nil_of_ne hright.symm
  have beforeEdge : s(before.penultimate, vertex) ∈ before.edges :=
    before.mk_penultimate_end_mem_edges beforeNotNil
  have afterEdge : s(vertex, after.snd) ∈ after.edges :=
    after.mk_start_snd_mem_edges afterNotNil
  have predecessorOptions :
      before.penultimate = firstExit ∨ before.penultimate = secondExit := by
    have hadj : Graph.Adj vertex before.penultimate :=
      (before.adj_penultimate beforeNotNil).symm
    have hmem : before.penultimate ∈ Graph.neighborSet vertex := hadj
    rw [hneighbors] at hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with hexcluded | hfirst | hsecond
    · exfalso
      apply hforbidden
      apply walk.edges_takeUntil_subset_edges hvertex
      simpa only [hexcluded, Sym2.eq_swap] using beforeEdge
    · exact Or.inl hfirst
    · exact Or.inr hsecond
  have successorOptions :
      after.snd = firstExit ∨ after.snd = secondExit := by
    have hadj : Graph.Adj vertex after.snd := after.adj_snd afterNotNil
    have hmem : after.snd ∈ Graph.neighborSet vertex := hadj
    rw [hneighbors] at hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with hexcluded | hfirst | hsecond
    · exfalso
      apply hforbidden
      apply walk.edges_dropUntil_subset_edges hvertex
      simpa only [hexcluded] using afterEdge
    · exact Or.inl hfirst
    · exact Or.inr hsecond
  have predecessor_ne_successor : before.penultimate ≠ after.snd := by
    intro heq
    have hdisjoint := hpath.isTrail.disjoint_edges_takeUntil_dropUntil hvertex
    apply hdisjoint beforeEdge
    simpa only [heq, Sym2.eq_swap] using afterEdge
  rcases predecessorOptions with hfirst | hsecond
  · rcases successorOptions with hfirst' | hsecond'
    · exact (predecessor_ne_successor (hfirst.trans hfirst'.symm)).elim
    · exact Or.inl ⟨hfirst, hsecond'⟩
  · rcases successorOptions with hfirst' | hsecond'
    · exact Or.inr ⟨hsecond, hfirst'⟩
    · exact (predecessor_ne_successor (hsecond.trans hsecond'.symm)).elim

end SimpleGraph.Walk

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24CorridorPumping
open GoertzelV24FourDefectBoundary
open GoertzelV24RecoveredAdjacentPairData
open GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- Every vertex of a deletion walk remains outside both deleted vertices
after mapping the walk back into the ambient graph. -/
theorem support_retainedWalkToAmbient_mem_retainedVertexSet
    (data : AdjacentPairData G)
    {left right : retainedVertexSet data.firstVertex data.secondVertex}
    (walk : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk left right)
    {vertex : V}
    (hvertex : vertex ∈ (data.retainedWalkToAmbient walk).support) :
    vertex ∈ retainedVertexSet data.firstVertex data.secondVertex := by
  rw [GoertzelV24AdjacentPairBoundary.AdjacentPairData.retainedWalkToAmbient,
    SimpleGraph.Walk.support_map] at hvertex
  rcases List.mem_map.mp hvertex with ⟨retained, _hretained, hvalue⟩
  change retained.1 = vertex at hvalue
  rw [← hvalue]
  exact retained.2

/-- A simple ambient path whose endpoints survive the adjacent-pair
deletion and which avoids the central edge can be rerouted past the first
deleted vertex using any retained bypass from port `0` to port `1`.
Path bypass absorbs all accidental overlap with the old path. -/
theorem exists_path_avoiding_firstVertex_of_central_not_mem_of_portBypass
    (data : AdjacentPairData G)
    {left right : V}
    (walk : G.Walk left right) (hpath : walk.IsPath)
    (hleft : left ∈ retainedVertexSet data.firstVertex data.secondVertex)
    (hright : right ∈ retainedVertexSet data.firstVertex data.secondVertex)
    (hcentral : (centralEdge data).1 ∉ walk.edges)
    (portBypass : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 1)) :
    ∃ rerouted : G.Walk left right,
      rerouted.IsPath ∧
      data.firstVertex ∉ rerouted.support ∧
      (data.secondVertex ∉ walk.support →
        data.secondVertex ∉ rerouted.support) ∧
      (centralEdge data).1 ∉ rerouted.edges ∧
      ∀ edge ∈ rerouted.edges,
        edge ∈ walk.edges ∨
          edge ∈ (data.retainedWalkToAmbient portBypass).edges := by
  by_cases hfirst : data.firstVertex ∈ walk.support
  · have orientation :=
      walk.internalPassage_orientation_of_neighborSet_eq_triple
        data.firstVertex data.secondVertex (data.portVertex 0)
          (data.portVertex 1) hpath hfirst hleft.1 hright.1
          data.firstNeighbors hcentral
    let ambientBypass := data.retainedWalkToAmbient portBypass
    have ambientBypassFirst : data.firstVertex ∉ ambientBypass.support := by
      intro hmem
      exact (support_retainedWalkToAmbient_mem_retainedVertexSet data
        portBypass hmem).1 rfl
    have ambientBypassSecond : data.secondVertex ∉ ambientBypass.support := by
      intro hmem
      exact (support_retainedWalkToAmbient_mem_retainedVertexSet data
        portBypass hmem).2 rfl
    have ambientBypassCentral :
        (centralEdge data).1 ∉ ambientBypass.edges := by
      exact data.centralEdgeValue_not_mem_retainedWalkToAmbient_edges
        portBypass
    rcases orientation with ⟨hbefore, hafter⟩ | ⟨hbefore, hafter⟩
    · let replacement : G.Walk
          (walk.takeUntil data.firstVertex hfirst).penultimate
          (walk.dropUntil data.firstVertex hfirst).snd :=
        ambientBypass.copy hbefore.symm hafter.symm
      let replaced := walk.replaceInternalVertex data.firstVertex hfirst
        replacement
      let rerouted := replaced.bypass
      refine ⟨rerouted, replaced.bypass_isPath, ?_, ?_, ?_, ?_⟩
      · apply walk.bypass_replaceInternalVertex_not_mem_support
          data.firstVertex hpath hfirst hleft.1 hright.1 replacement
        simpa only [replacement, SimpleGraph.Walk.support_copy] using
          ambientBypassFirst
      · intro hsecond hmem
        have hraw := replaced.support_bypass_subset_support hmem
        rcases walk.mem_support_replaceInternalVertex data.firstVertex
            hfirst replacement hraw with hold | hnew
        · exact hsecond hold
        · exact ambientBypassSecond (by
            simpa only [replacement, SimpleGraph.Walk.support_copy] using hnew)
      · intro hedge
        have hraw := replaced.edges_bypass_subset_edges hedge
        rcases walk.mem_edges_replaceInternalVertex data.firstVertex hfirst
            replacement hraw with hold | hnew
        · exact hcentral hold
        · exact ambientBypassCentral (by
            simpa only [replacement, SimpleGraph.Walk.edges_copy] using hnew)
      · intro edge hedge
        have hraw := replaced.edges_bypass_subset_edges hedge
        rcases walk.mem_edges_replaceInternalVertex data.firstVertex hfirst
            replacement hraw with hold | hnew
        · exact Or.inl hold
        · exact Or.inr (by
            simpa only [replacement, SimpleGraph.Walk.edges_copy] using hnew)
    · let replacement : G.Walk
          (walk.takeUntil data.firstVertex hfirst).penultimate
          (walk.dropUntil data.firstVertex hfirst).snd :=
        ambientBypass.reverse.copy hbefore.symm hafter.symm
      let replaced := walk.replaceInternalVertex data.firstVertex hfirst
        replacement
      let rerouted := replaced.bypass
      refine ⟨rerouted, replaced.bypass_isPath, ?_, ?_, ?_, ?_⟩
      · apply walk.bypass_replaceInternalVertex_not_mem_support
          data.firstVertex hpath hfirst hleft.1 hright.1 replacement
        intro hmem
        apply ambientBypassFirst
        dsimp only [replacement] at hmem
        rw [SimpleGraph.Walk.support_copy,
          SimpleGraph.Walk.support_reverse] at hmem
        exact List.mem_reverse.mp hmem
      · intro hsecond hmem
        have hraw := replaced.support_bypass_subset_support hmem
        rcases walk.mem_support_replaceInternalVertex data.firstVertex
            hfirst replacement hraw with hold | hnew
        · exact hsecond hold
        · apply ambientBypassSecond
          dsimp only [replacement] at hnew
          rw [SimpleGraph.Walk.support_copy,
            SimpleGraph.Walk.support_reverse] at hnew
          exact List.mem_reverse.mp hnew
      · intro hedge
        have hraw := replaced.edges_bypass_subset_edges hedge
        rcases walk.mem_edges_replaceInternalVertex data.firstVertex hfirst
            replacement hraw with hold | hnew
        · exact hcentral hold
        · exact ambientBypassCentral (by
            simpa only [replacement, SimpleGraph.Walk.edges_copy,
              SimpleGraph.Walk.edges_reverse, List.mem_reverse] using hnew)
      · intro edge hedge
        have hraw := replaced.edges_bypass_subset_edges hedge
        rcases walk.mem_edges_replaceInternalVertex data.firstVertex hfirst
            replacement hraw with hold | hnew
        · exact Or.inl hold
        · exact Or.inr (by
            simpa only [replacement, SimpleGraph.Walk.edges_copy,
              SimpleGraph.Walk.edges_reverse, List.mem_reverse] using hnew)
  · exact ⟨walk, hpath, hfirst, fun hsecond => hsecond, hcentral,
      fun _ hedge => Or.inl hedge⟩

/-- The symmetric surgery reroutes a simple ambient path past the second
deleted vertex using a retained bypass from port `2` to port `3`. -/
theorem exists_path_avoiding_secondVertex_of_central_not_mem_of_portBypass
    (data : AdjacentPairData G)
    {left right : V}
    (walk : G.Walk left right) (hpath : walk.IsPath)
    (hleft : left ∈ retainedVertexSet data.firstVertex data.secondVertex)
    (hright : right ∈ retainedVertexSet data.firstVertex data.secondVertex)
    (hcentral : (centralEdge data).1 ∉ walk.edges)
    (portBypass : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 2) (data.retainedPort 3)) :
    ∃ rerouted : G.Walk left right,
      rerouted.IsPath ∧
      data.secondVertex ∉ rerouted.support ∧
      (data.firstVertex ∉ walk.support →
        data.firstVertex ∉ rerouted.support) ∧
      (centralEdge data).1 ∉ rerouted.edges ∧
      ∀ edge ∈ rerouted.edges,
        edge ∈ walk.edges ∨
          edge ∈ (data.retainedWalkToAmbient portBypass).edges := by
  by_cases hsecond : data.secondVertex ∈ walk.support
  · have hcentralSymm :
        s(data.secondVertex, data.firstVertex) ∉ walk.edges := by
      simpa only [centralEdge_val, centralEdgeValue, Sym2.eq_swap] using
        hcentral
    have orientation :=
      walk.internalPassage_orientation_of_neighborSet_eq_triple
        data.secondVertex data.firstVertex (data.portVertex 2)
          (data.portVertex 3) hpath hsecond hleft.2 hright.2
          data.secondNeighbors hcentralSymm
    let ambientBypass := data.retainedWalkToAmbient portBypass
    have ambientBypassFirst : data.firstVertex ∉ ambientBypass.support := by
      intro hmem
      exact (support_retainedWalkToAmbient_mem_retainedVertexSet data
        portBypass hmem).1 rfl
    have ambientBypassSecond : data.secondVertex ∉ ambientBypass.support := by
      intro hmem
      exact (support_retainedWalkToAmbient_mem_retainedVertexSet data
        portBypass hmem).2 rfl
    have ambientBypassCentral :
        (centralEdge data).1 ∉ ambientBypass.edges := by
      exact data.centralEdgeValue_not_mem_retainedWalkToAmbient_edges
        portBypass
    rcases orientation with ⟨hbefore, hafter⟩ | ⟨hbefore, hafter⟩
    · let replacement : G.Walk
          (walk.takeUntil data.secondVertex hsecond).penultimate
          (walk.dropUntil data.secondVertex hsecond).snd :=
        ambientBypass.copy hbefore.symm hafter.symm
      let replaced := walk.replaceInternalVertex data.secondVertex hsecond
        replacement
      let rerouted := replaced.bypass
      refine ⟨rerouted, replaced.bypass_isPath, ?_, ?_, ?_, ?_⟩
      · apply walk.bypass_replaceInternalVertex_not_mem_support
          data.secondVertex hpath hsecond hleft.2 hright.2 replacement
        simpa only [replacement, SimpleGraph.Walk.support_copy] using
          ambientBypassSecond
      · intro hfirst hmem
        have hraw := replaced.support_bypass_subset_support hmem
        rcases walk.mem_support_replaceInternalVertex data.secondVertex
            hsecond replacement hraw with hold | hnew
        · exact hfirst hold
        · exact ambientBypassFirst (by
            simpa only [replacement, SimpleGraph.Walk.support_copy] using hnew)
      · intro hedge
        have hraw := replaced.edges_bypass_subset_edges hedge
        rcases walk.mem_edges_replaceInternalVertex data.secondVertex hsecond
            replacement hraw with hold | hnew
        · exact hcentral hold
        · exact ambientBypassCentral (by
            simpa only [replacement, SimpleGraph.Walk.edges_copy] using hnew)
      · intro edge hedge
        have hraw := replaced.edges_bypass_subset_edges hedge
        rcases walk.mem_edges_replaceInternalVertex data.secondVertex hsecond
            replacement hraw with hold | hnew
        · exact Or.inl hold
        · exact Or.inr (by
            simpa only [replacement, SimpleGraph.Walk.edges_copy] using hnew)
    · let replacement : G.Walk
          (walk.takeUntil data.secondVertex hsecond).penultimate
          (walk.dropUntil data.secondVertex hsecond).snd :=
        ambientBypass.reverse.copy hbefore.symm hafter.symm
      let replaced := walk.replaceInternalVertex data.secondVertex hsecond
        replacement
      let rerouted := replaced.bypass
      refine ⟨rerouted, replaced.bypass_isPath, ?_, ?_, ?_, ?_⟩
      · apply walk.bypass_replaceInternalVertex_not_mem_support
          data.secondVertex hpath hsecond hleft.2 hright.2 replacement
        intro hmem
        apply ambientBypassSecond
        dsimp only [replacement] at hmem
        rw [SimpleGraph.Walk.support_copy,
          SimpleGraph.Walk.support_reverse] at hmem
        exact List.mem_reverse.mp hmem
      · intro hfirst hmem
        have hraw := replaced.support_bypass_subset_support hmem
        rcases walk.mem_support_replaceInternalVertex data.secondVertex
            hsecond replacement hraw with hold | hnew
        · exact hfirst hold
        · apply ambientBypassFirst
          dsimp only [replacement] at hnew
          rw [SimpleGraph.Walk.support_copy,
            SimpleGraph.Walk.support_reverse] at hnew
          exact List.mem_reverse.mp hnew
      · intro hedge
        have hraw := replaced.edges_bypass_subset_edges hedge
        rcases walk.mem_edges_replaceInternalVertex data.secondVertex hsecond
            replacement hraw with hold | hnew
        · exact hcentral hold
        · exact ambientBypassCentral (by
            simpa only [replacement, SimpleGraph.Walk.edges_copy,
              SimpleGraph.Walk.edges_reverse, List.mem_reverse] using hnew)
      · intro edge hedge
        have hraw := replaced.edges_bypass_subset_edges hedge
        rcases walk.mem_edges_replaceInternalVertex data.secondVertex hsecond
            replacement hraw with hold | hnew
        · exact Or.inl hold
        · exact Or.inr (by
            simpa only [replacement, SimpleGraph.Walk.edges_copy,
              SimpleGraph.Walk.edges_reverse, List.mem_reverse] using hnew)
  · exact ⟨walk, hpath, hsecond, fun hfirst => hfirst, hcentral,
      fun _ hedge => Or.inl hedge⟩

/-- Two retained same-side bypasses remove both vertices of an adjacent
pair from any simple ambient path that avoids the central edge. The result
is an honest simple path in the induced adjacent-pair deletion with the
same endpoints. -/
theorem exists_deletedAdjacentPairPath_of_central_not_mem_of_portBypasses
    (data : AdjacentPairData G)
    {left right : V}
    (walk : G.Walk left right) (hpath : walk.IsPath)
    (hleft : left ∈ retainedVertexSet data.firstVertex data.secondVertex)
    (hright : right ∈ retainedVertexSet data.firstVertex data.secondVertex)
    (hcentral : (centralEdge data).1 ∉ walk.edges)
    (firstBypass : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 1))
    (secondBypass : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 2) (data.retainedPort 3)) :
    ∃ targetPath : (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).Walk ⟨left, hleft⟩ ⟨right, hright⟩,
      targetPath.IsPath ∧
      ∀ edge ∈ (data.retainedWalkToAmbient targetPath).edges,
        edge ∈ walk.edges ∨
          edge ∈ (data.retainedWalkToAmbient firstBypass).edges ∨
            edge ∈ (data.retainedWalkToAmbient secondBypass).edges := by
  rcases exists_path_avoiding_firstVertex_of_central_not_mem_of_portBypass
      data walk hpath hleft hright hcentral firstBypass with
    ⟨firstReroute, firstPath, firstAvoids, _firstPreservesSecond,
      firstCentral, firstEdgeOrigin⟩
  rcases exists_path_avoiding_secondVertex_of_central_not_mem_of_portBypass
      data firstReroute firstPath hleft hright firstCentral secondBypass with
    ⟨secondReroute, secondPath, secondAvoids, preservesFirst,
      _secondCentral, secondEdgeOrigin⟩
  have secondAvoidsFirst : data.firstVertex ∉ secondReroute.support :=
    preservesFirst firstAvoids
  have supportRetained : ∀ vertex ∈ secondReroute.support,
      vertex ∈ retainedVertexSet data.firstVertex data.secondVertex := by
    intro vertex hvertex
    exact ⟨fun heq => secondAvoidsFirst (heq ▸ hvertex),
      fun heq => secondAvoids (heq ▸ hvertex)⟩
  let targetPath := secondReroute.induce
    (retainedVertexSet data.firstVertex data.secondVertex) supportRetained
  let embedding := SimpleGraph.Embedding.induce
    (G := G) (retainedVertexSet data.firstVertex data.secondVertex)
  have mappedEq : targetPath.map embedding.toHom = secondReroute :=
    SimpleGraph.Walk.map_induce secondReroute supportRetained
  have ambientEq : data.retainedWalkToAmbient targetPath = secondReroute := by
    change targetPath.map embedding.toHom = secondReroute
    exact mappedEq
  have mapped : (targetPath.map embedding.toHom).IsPath := by
    rw [mappedEq]
    exact secondPath
  refine ⟨targetPath, ?_, ?_⟩
  · exact (SimpleGraph.Walk.map_isPath_iff_of_injective
      (p := targetPath) (f := embedding.toHom) embedding.injective).1 mapped
  · intro edge hedge
    rw [ambientEq] at hedge
    rcases secondEdgeOrigin edge hedge with hfirst | hsecond
    · rcases firstEdgeOrigin edge hfirst with hold | hfirstBypass
      · exact Or.inl hold
      · exact Or.inr (Or.inl hfirstBypass)
    · exact Or.inr (Or.inr hsecond)

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

namespace CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

namespace IntrinsicShortTargetEscapeCollar

variable {cycle :
    CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle rebaseCircuit}
  {targetEdge : G.edgeSet}
  {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
    graphData minimal baseData}
  {collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge}
  {start : sourceNormal.KempeOrbitAdjacentEscape}

namespace CompanionCrossPairFusionTargetCollarTraversal

variable (traversal :
  CompanionCrossPairFusionTargetCollarTraversal collar start)

/-- Every noncentral target-collar traversal can be replaced, without any
edge-disjointness premise, by an honest simple path in the target
adjacent-pair deletion between the original fusion endpoints. -/
theorem exists_targetKempeReroutedPath_of_noncentral
    (hclass : traversal.traversalClass = .firstBoundaryPair ∨
      traversal.traversalClass = .secondBoundaryPair ∨
      traversal.traversalClass = .bothBoundaryPairs) :
    ∃ targetPath : (DeletedAdjacentPairGraph G
        collar.targetData.firstVertex collar.targetData.secondVertex).Walk
        ⟨traversal.contact.fusion.startVertex.1,
          traversal.contact.fusion.startVertex_mem_targetRetainedVertexSet⟩
        ⟨traversal.contact.fusion.endVertex.1,
          traversal.contact.fusion.endVertex_mem_targetRetainedVertexSet⟩,
      targetPath.IsPath := by
  let fusion := traversal.contact.fusion
  have centralNotAmbient : (centralEdge collar.targetData).1 ∉
      fusion.ambientTrail.edges := by
    rcases hclass with hfirst | hsecond | hboth
    · have husage := traversal.exactUsage
      rw [hfirst] at husage
      exact husage.1
    · have husage := traversal.exactUsage
      rw [hsecond] at husage
      exact husage.1
    · have husage := traversal.exactUsage
      rw [hboth] at husage
      exact husage.1
  let ambientPath := fusion.ambientTrail.bypass
  have ambientPathIsPath : ambientPath.IsPath :=
    fusion.ambientTrail.bypass_isPath
  have centralNotAmbientPath : (centralEdge collar.targetData).1 ∉
      ambientPath.edges := by
    intro hmem
    exact centralNotAmbient
      (fusion.ambientTrail.edges_bypass_subset_edges hmem)
  rcases collar.exists_targetOwnSameSideKempePrimalTrails_disjoint with
    ⟨_routes, firstBypass, secondBypass, _firstIsTrail, _secondIsTrail,
      _firstEdges, _secondEdges, _disjoint⟩
  rcases exists_deletedAdjacentPairPath_of_central_not_mem_of_portBypasses
      collar.targetData ambientPath ambientPathIsPath
      fusion.startVertex_mem_targetRetainedVertexSet
      fusion.endVertex_mem_targetRetainedVertexSet centralNotAmbientPath
      firstBypass secondBypass with ⟨targetPath, targetPathIsPath, _origin⟩
  exact ⟨targetPath, targetPathIsPath⟩

/-- The rerouted target path has exact edge provenance.  Every edge either
comes from the original fusion trail, or belongs to one of the two genuine
target-own Kempe routes and is therefore selected by the target color pair. -/
theorem exists_targetKempeReroutedPath_with_edgeOrigin_of_noncentral
    (hclass : traversal.traversalClass = .firstBoundaryPair ∨
      traversal.traversalClass = .secondBoundaryPair ∨
      traversal.traversalClass = .bothBoundaryPairs) :
    ∃ targetPath : (DeletedAdjacentPairGraph G
        collar.targetData.firstVertex collar.targetData.secondVertex).Walk
        ⟨traversal.contact.fusion.startVertex.1,
          traversal.contact.fusion.startVertex_mem_targetRetainedVertexSet⟩
        ⟨traversal.contact.fusion.endVertex.1,
          traversal.contact.fusion.endVertex_mem_targetRetainedVertexSet⟩,
      targetPath.IsPath ∧
      ∀ edge : (DeletedAdjacentPairGraph G
          collar.targetData.firstVertex collar.targetData.secondVertex).edgeSet,
        edge.1 ∈ targetPath.edges →
          (retainedEdgeToAmbientEdge collar.targetData edge).1 ∈
              traversal.contact.fusion.ambientTrail.edges ∨
            edge ∈ collar.targetEscape.coloring.bicoloredSet
              collar.targetOwnFirstColor collar.targetOwnSecondColor := by
  let fusion := traversal.contact.fusion
  have centralNotAmbient : (centralEdge collar.targetData).1 ∉
      fusion.ambientTrail.edges := by
    rcases hclass with hfirst | hsecond | hboth
    · have husage := traversal.exactUsage
      rw [hfirst] at husage
      exact husage.1
    · have husage := traversal.exactUsage
      rw [hsecond] at husage
      exact husage.1
    · have husage := traversal.exactUsage
      rw [hboth] at husage
      exact husage.1
  let ambientPath := fusion.ambientTrail.bypass
  have ambientPathIsPath : ambientPath.IsPath :=
    fusion.ambientTrail.bypass_isPath
  have centralNotAmbientPath : (centralEdge collar.targetData).1 ∉
      ambientPath.edges := by
    intro hmem
    exact centralNotAmbient
      (fusion.ambientTrail.edges_bypass_subset_edges hmem)
  rcases collar.exists_targetOwnSameSideKempePrimalTrails_disjoint with
    ⟨routes, firstBypass, secondBypass, _firstIsTrail, _secondIsTrail,
      firstEdges, secondEdges, _disjoint⟩
  rcases exists_deletedAdjacentPairPath_of_central_not_mem_of_portBypasses
      collar.targetData ambientPath ambientPathIsPath
      fusion.startVertex_mem_targetRetainedVertexSet
      fusion.endVertex_mem_targetRetainedVertexSet centralNotAmbientPath
      firstBypass secondBypass with
    ⟨targetPath, targetPathIsPath, edgeOrigin⟩
  refine ⟨targetPath, targetPathIsPath, ?_⟩
  intro edge hedge
  have ambientEdgeMem :
      (retainedEdgeToAmbientEdge collar.targetData edge).1 ∈
        (collar.targetData.retainedWalkToAmbient targetPath).edges :=
    (retainedEdgeToAmbientEdge_mem_retainedWalkToAmbient_edges_iff
      collar.targetData targetPath edge).2 hedge
  rcases edgeOrigin _ ambientEdgeMem with hold | hfirst | hsecond
  · exact Or.inl
      (fusion.ambientTrail.edges_bypass_subset_edges hold)
  · apply Or.inr
    have hfirst' : edge.1 ∈ firstBypass.edges :=
      (retainedEdgeToAmbientEdge_mem_retainedWalkToAmbient_edges_iff
        collar.targetData firstBypass edge).1 hfirst
    rw [firstEdges] at hfirst'
    rcases List.mem_map.mp hfirst' with ⟨routeEdge, routeEdgeMem, routeEdgeEq⟩
    have routeEdge_eq : routeEdge = edge := Subtype.ext routeEdgeEq
    subst routeEdge
    exact (routes.firstRoute.mem_ambientPath_support_iff edge).1
      routeEdgeMem |>.1
  · apply Or.inr
    have hsecond' : edge.1 ∈ secondBypass.edges :=
      (retainedEdgeToAmbientEdge_mem_retainedWalkToAmbient_edges_iff
        collar.targetData secondBypass edge).1 hsecond
    rw [secondEdges] at hsecond'
    rcases List.mem_map.mp hsecond' with
      ⟨routeEdge, routeEdgeMem, routeEdgeEq⟩
    have routeEdge_eq : routeEdge = edge := Subtype.ext routeEdgeEq
    subst routeEdge
    rcases (routes.secondRoute.mem_ambientPath_support_iff edge).1
        routeEdgeMem |>.1 with hsecondColor | hfirstColor
    · exact Or.inr hsecondColor
    · exact Or.inl hfirstColor

/-- The seven exact traversal classes now have a geometric local outcome:
the three noncentral classes reroute to a target-deletion path, while each
central class exposes the precise cross-arm Kempe obstruction. -/
theorem exists_targetKempeReroutedPath_or_crossObstruction :
    (∃ targetPath : (DeletedAdjacentPairGraph G
        collar.targetData.firstVertex collar.targetData.secondVertex).Walk
        ⟨traversal.contact.fusion.startVertex.1,
          traversal.contact.fusion.startVertex_mem_targetRetainedVertexSet⟩
        ⟨traversal.contact.fusion.endVertex.1,
          traversal.contact.fusion.endVertex_mem_targetRetainedVertexSet⟩,
      targetPath.IsPath) ∨
    ∃ firstUsesOne secondUsesThree,
      traversal.traversalClass = .cross firstUsesOne secondUsesThree ∧
      ¬ collar.targetData.degreeTwoBoundaryData.KempePortsConnected
        collar.targetEscape.coloring collar.targetOwnFirstColor
          collar.targetOwnSecondColor
          (TargetCollarTraversalClass.firstCrossPort firstUsesOne)
          (TargetCollarTraversalClass.secondCrossPort secondUsesThree) := by
  cases hclass : traversal.traversalClass with
  | firstBoundaryPair =>
      exact Or.inl <| traversal.exists_targetKempeReroutedPath_of_noncentral
        (Or.inl hclass)
  | secondBoundaryPair =>
      exact Or.inl <| traversal.exists_targetKempeReroutedPath_of_noncentral
        (Or.inr (Or.inl hclass))
  | bothBoundaryPairs =>
      exact Or.inl <| traversal.exists_targetKempeReroutedPath_of_noncentral
        (Or.inr (Or.inr hclass))
  | cross firstUsesOne secondUsesThree =>
      exact Or.inr ⟨firstUsesOne, secondUsesThree, rfl,
        collar.not_targetOwnKempePortsConnected_cross
          firstUsesOne secondUsesThree⟩

end CompanionCrossPairFusionTargetCollarTraversal
end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end
end Mettapedia.GraphTheory.FourColor
