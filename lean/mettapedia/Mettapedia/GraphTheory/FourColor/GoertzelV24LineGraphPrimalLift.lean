import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionOrientation
import Mathlib.Data.List.ChainOfFn

namespace SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

namespace Walk

/-- The primal junction used by one step of a line-graph walk. -/
noncomputable def lineGraphJunctionAt {first last : G.edgeSet}
    (walk : G.lineGraph.Walk first last) (position : Fin walk.length) : V :=
  lineGraphCommonVertex (walk.adj_getVert_succ position.isLt)

theorem lineGraphJunctionAt_mem_left {first last : G.edgeSet}
    (walk : G.lineGraph.Walk first last) (position : Fin walk.length) :
    walk.lineGraphJunctionAt position ∈
      ((walk.getVert position.val).1 : Sym2 V) :=
  lineGraphCommonVertex_mem_left
    (walk.adj_getVert_succ position.isLt)

theorem lineGraphJunctionAt_mem_right {first last : G.edgeSet}
    (walk : G.lineGraph.Walk first last) (position : Fin walk.length) :
    walk.lineGraphJunctionAt position ∈
      ((walk.getVert (position.val + 1)).1 : Sym2 V) :=
  lineGraphCommonVertex_mem_right
    (walk.adj_getVert_succ position.isLt)

/-- A closed line-graph walk is primal-coherent when consecutive selected
junctions use opposite endpoints of every intermediate primal edge, including
the closing pair. -/
structure IsPrimalCoherentClosed {edge : G.edgeSet}
    (walk : G.lineGraph.Walk edge edge) : Prop where
  internal : ∀ (position : Nat)
      (hposition : position + 1 < walk.length),
    walk.lineGraphJunctionAt
        ⟨position, by omega⟩ ≠
      walk.lineGraphJunctionAt ⟨position + 1, hposition⟩
  closing : ∀ (hpositive : 0 < walk.length),
    walk.lineGraphJunctionAt
        ⟨walk.length - 1, Nat.sub_lt hpositive Nat.zero_lt_one⟩ ≠
      walk.lineGraphJunctionAt ⟨0, hpositive⟩

theorem adj_lineGraphJunctionAt_succ {edge : G.edgeSet}
    (walk : G.lineGraph.Walk edge edge)
    (position : Nat) (hposition : position + 1 < walk.length)
    (hcoherent :
      walk.lineGraphJunctionAt
          ⟨position, by omega⟩ ≠
        walk.lineGraphJunctionAt ⟨position + 1, hposition⟩) :
    G.Adj
      (walk.lineGraphJunctionAt
        ⟨position, by omega⟩)
      (walk.lineGraphJunctionAt ⟨position + 1, hposition⟩) := by
  let current : Fin walk.length :=
    ⟨position, by omega⟩
  let next : Fin walk.length := ⟨position + 1, hposition⟩
  let commonEdge : G.edgeSet := walk.getVert (position + 1)
  have hcurrent : walk.lineGraphJunctionAt current ∈
      (commonEdge.1 : Sym2 V) := by
    exact walk.lineGraphJunctionAt_mem_right current
  have hnext : walk.lineGraphJunctionAt next ∈
      (commonEdge.1 : Sym2 V) := by
    exact walk.lineGraphJunctionAt_mem_left next
  have hedge : commonEdge.1 = s(walk.lineGraphJunctionAt current,
      walk.lineGraphJunctionAt next) :=
    (Sym2.mem_and_mem_iff hcoherent).1 ⟨hcurrent, hnext⟩
  have hadj := commonEdge.property
  rw [hedge] at hadj
  exact hadj

theorem pair_lineGraphJunctionAt_succ_eq_getVert {edge : G.edgeSet}
    (walk : G.lineGraph.Walk edge edge)
    (position : Nat) (hposition : position + 1 < walk.length)
    (hcoherent :
      walk.lineGraphJunctionAt ⟨position, by omega⟩ ≠
        walk.lineGraphJunctionAt ⟨position + 1, hposition⟩) :
    s(walk.lineGraphJunctionAt ⟨position, by omega⟩,
        walk.lineGraphJunctionAt ⟨position + 1, hposition⟩) =
      (walk.getVert (position + 1)).1 := by
  apply (Sym2.mem_and_mem_iff hcoherent).1 ⟨?_, ?_⟩ |>.symm
  · exact walk.lineGraphJunctionAt_mem_right ⟨position, by omega⟩
  · exact walk.lineGraphJunctionAt_mem_left
      ⟨position + 1, hposition⟩

theorem adj_lineGraphJunctionAt_last_first {edge : G.edgeSet}
    (walk : G.lineGraph.Walk edge edge)
    (hpositive : 0 < walk.length)
    (hcoherent :
      walk.lineGraphJunctionAt
          ⟨walk.length - 1, Nat.sub_lt hpositive Nat.zero_lt_one⟩ ≠
        walk.lineGraphJunctionAt ⟨0, hpositive⟩) :
    G.Adj
      (walk.lineGraphJunctionAt
        ⟨walk.length - 1, Nat.sub_lt hpositive Nat.zero_lt_one⟩)
      (walk.lineGraphJunctionAt ⟨0, hpositive⟩) := by
  let finalPosition : Fin walk.length :=
    ⟨walk.length - 1, Nat.sub_lt hpositive Nat.zero_lt_one⟩
  let firstPosition : Fin walk.length := ⟨0, hpositive⟩
  have hfinal : walk.lineGraphJunctionAt finalPosition ∈
      (edge.1 : Sym2 V) := by
    have hmem := walk.lineGraphJunctionAt_mem_right finalPosition
    simpa only [finalPosition, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2
      (Nat.ne_of_gt hpositive)), walk.getVert_length] using hmem
  have hfirst : walk.lineGraphJunctionAt firstPosition ∈
      (edge.1 : Sym2 V) := by
    have hmem := walk.lineGraphJunctionAt_mem_left firstPosition
    simpa only [firstPosition, walk.getVert_zero] using hmem
  have hedge : edge.1 = s(walk.lineGraphJunctionAt finalPosition,
      walk.lineGraphJunctionAt firstPosition) :=
    (Sym2.mem_and_mem_iff hcoherent).1 ⟨hfinal, hfirst⟩
  have hadj := edge.property
  rw [hedge] at hadj
  exact hadj

theorem pair_lineGraphJunctionAt_last_first_eq_edge {edge : G.edgeSet}
    (walk : G.lineGraph.Walk edge edge)
    (hpositive : 0 < walk.length)
    (hcoherent :
      walk.lineGraphJunctionAt
          ⟨walk.length - 1, Nat.sub_lt hpositive Nat.zero_lt_one⟩ ≠
        walk.lineGraphJunctionAt ⟨0, hpositive⟩) :
    s(walk.lineGraphJunctionAt
          ⟨walk.length - 1, Nat.sub_lt hpositive Nat.zero_lt_one⟩,
        walk.lineGraphJunctionAt ⟨0, hpositive⟩) = edge.1 := by
  apply (Sym2.mem_and_mem_iff hcoherent).1 ⟨?_, ?_⟩ |>.symm
  · have hmem := walk.lineGraphJunctionAt_mem_right
      ⟨walk.length - 1, Nat.sub_lt hpositive Nat.zero_lt_one⟩
    simpa only [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2
      (Nat.ne_of_gt hpositive)), walk.getVert_length] using hmem
  · have hmem := walk.lineGraphJunctionAt_mem_left ⟨0, hpositive⟩
    simpa only [walk.getVert_zero] using hmem

/-- The cyclic list of primal junctions selected by a positive-length closed
line-graph walk. -/
noncomputable def primalJunctionSupport {edge : G.edgeSet}
    (walk : G.lineGraph.Walk edge edge) (hpositive : 0 < walk.length) :
    List V :=
  List.ofFn walk.lineGraphJunctionAt ++
    [walk.lineGraphJunctionAt ⟨0, hpositive⟩]

@[simp] theorem primalJunctionSupport_length {edge : G.edgeSet}
    (walk : G.lineGraph.Walk edge edge) (hpositive : 0 < walk.length) :
    (walk.primalJunctionSupport hpositive).length = walk.length + 1 := by
  simp [primalJunctionSupport]

theorem primalJunctionSupport_ne_nil {edge : G.edgeSet}
    (walk : G.lineGraph.Walk edge edge) (hpositive : 0 < walk.length) :
    walk.primalJunctionSupport hpositive ≠ [] := by
  simp [primalJunctionSupport]

theorem primalJunctionSupport_head {edge : G.edgeSet}
    (walk : G.lineGraph.Walk edge edge) (hpositive : 0 < walk.length) :
    (walk.primalJunctionSupport hpositive).head
        (walk.primalJunctionSupport_ne_nil hpositive) =
      walk.lineGraphJunctionAt ⟨0, hpositive⟩ := by
  unfold primalJunctionSupport
  have hne : List.ofFn walk.lineGraphJunctionAt ≠ [] := by
    apply List.ne_nil_of_length_pos
    simpa using hpositive
  rw [List.head_append_of_ne_nil hne]
  rw [List.head_eq_getElem_zero hne]
  simp

theorem primalJunctionSupport_getLast {edge : G.edgeSet}
    (walk : G.lineGraph.Walk edge edge) (hpositive : 0 < walk.length) :
    (walk.primalJunctionSupport hpositive).getLast
        (walk.primalJunctionSupport_ne_nil hpositive) =
      walk.lineGraphJunctionAt ⟨0, hpositive⟩ := by
  exact List.getLast_append_singleton _

@[simp] theorem primalJunctionSupport_getElem {edge : G.edgeSet}
    (walk : G.lineGraph.Walk edge edge) (hpositive : 0 < walk.length)
    (position : Fin walk.length) :
    (walk.primalJunctionSupport hpositive)[position.val]'(by
        rw [walk.primalJunctionSupport_length hpositive]
        omega) = walk.lineGraphJunctionAt position := by
  simp [primalJunctionSupport]

@[simp] theorem primalJunctionSupport_getElem_length {edge : G.edgeSet}
    (walk : G.lineGraph.Walk edge edge) (hpositive : 0 < walk.length) :
    (walk.primalJunctionSupport hpositive)[walk.length]'(by
        rw [walk.primalJunctionSupport_length hpositive]
        omega) = walk.lineGraphJunctionAt ⟨0, hpositive⟩ := by
  simp [primalJunctionSupport]

theorem primalJunctionSupport_isChain {edge : G.edgeSet}
    (walk : G.lineGraph.Walk edge edge) (hpositive : 0 < walk.length)
    (hcoherent : walk.IsPrimalCoherentClosed) :
    (walk.primalJunctionSupport hpositive).IsChain G.Adj := by
  rw [primalJunctionSupport]
  apply List.IsChain.append
  · rw [List.isChain_ofFn]
    intro position hposition
    exact walk.adj_lineGraphJunctionAt_succ position hposition
      (hcoherent.internal position hposition)
  · simp
  · intro lastJunction hlast firstJunction hfirst
    rcases List.mem_getLast?_eq_getLast hlast with ⟨hne, rfl⟩
    simp at hfirst
    subst firstJunction
    rw [List.getLast_ofFn hne]
    exact walk.adj_lineGraphJunctionAt_last_first hpositive
      (hcoherent.closing hpositive)

/-- A primal-coherent closed line-graph walk canonically lifts to a closed
walk in the primal graph. -/
noncomputable def primalLift {edge : G.edgeSet}
    (walk : G.lineGraph.Walk edge edge) (hpositive : 0 < walk.length)
    (hcoherent : walk.IsPrimalCoherentClosed) :
    G.Walk (walk.lineGraphJunctionAt ⟨0, hpositive⟩)
      (walk.lineGraphJunctionAt ⟨0, hpositive⟩) :=
  (Walk.ofSupport (walk.primalJunctionSupport hpositive)
      (walk.primalJunctionSupport_ne_nil hpositive)
      (walk.primalJunctionSupport_isChain hpositive hcoherent)).copy
    (walk.primalJunctionSupport_head hpositive)
    (walk.primalJunctionSupport_getLast hpositive)

@[simp] theorem primalLift_support {edge : G.edgeSet}
    (walk : G.lineGraph.Walk edge edge) (hpositive : 0 < walk.length)
    (hcoherent : walk.IsPrimalCoherentClosed) :
    (walk.primalLift hpositive hcoherent).support =
      walk.primalJunctionSupport hpositive := by
  simp [primalLift]

@[simp] theorem primalLift_length {edge : G.edgeSet}
    (walk : G.lineGraph.Walk edge edge) (hpositive : 0 < walk.length)
    (hcoherent : walk.IsPrimalCoherentClosed) :
    (walk.primalLift hpositive hcoherent).length = walk.length := by
  simp [primalLift, primalJunctionSupport]

theorem primalLift_edges_getElem {edge : G.edgeSet}
    (walk : G.lineGraph.Walk edge edge) (hpositive : 0 < walk.length)
    (hcoherent : walk.IsPrimalCoherentClosed)
    (position : Fin walk.length) :
    (walk.primalLift hpositive hcoherent).edges[position.val]'(by
        rw [Walk.length_edges, walk.primalLift_length hpositive hcoherent]
        exact position.isLt) =
      (walk.getVert (position.val + 1)).1 := by
  simp only [Walk.edges_eq_zipWith_support, List.getElem_zipWith,
    List.getElem_tail, primalLift_support]
  by_cases hinternal : position.val + 1 < walk.length
  · rw [walk.primalJunctionSupport_getElem hpositive position,
      walk.primalJunctionSupport_getElem hpositive
        ⟨position.val + 1, hinternal⟩]
    exact walk.pair_lineGraphJunctionAt_succ_eq_getVert
      position.val hinternal (hcoherent.internal position.val hinternal)
  · have hlast : position.val + 1 = walk.length := by omega
    have hposition : position =
        ⟨walk.length - 1, Nat.sub_lt hpositive Nat.zero_lt_one⟩ := by
      apply Fin.ext
      dsimp
      omega
    rw [walk.primalJunctionSupport_getElem hpositive position,
      hposition]
    have hlastIndex : walk.length - 1 + 1 = walk.length := by omega
    simp only [hlastIndex, walk.primalJunctionSupport_getElem_length]
    simpa only [walk.getVert_length] using
      walk.pair_lineGraphJunctionAt_last_first_eq_edge hpositive
        (hcoherent.closing hpositive)

theorem primalLift_edges_eq_ofFn_getVert_succ {edge : G.edgeSet}
    (walk : G.lineGraph.Walk edge edge) (hpositive : 0 < walk.length)
    (hcoherent : walk.IsPrimalCoherentClosed) :
    (walk.primalLift hpositive hcoherent).edges =
      List.ofFn (fun position : Fin walk.length ↦
        (walk.getVert (position.val + 1)).1) := by
  apply List.ext_getElem
  · simp
  · intro position hleft hright
    have hposition : position < walk.length := by
      simpa using hright
    simpa using walk.primalLift_edges_getElem hpositive hcoherent
      ⟨position, hposition⟩

theorem ofFn_getVert_succ_eq_map_tail_support
    {first last : G.edgeSet} (walk : G.lineGraph.Walk first last) :
    List.ofFn (fun position : Fin walk.length ↦
        (walk.getVert (position.val + 1)).1) =
      walk.support.tail.map Subtype.val := by
  apply List.ext_getElem
  · simp
  · intro position hleft hright
    have hposition : position < walk.length := by
      simpa using hleft
    simp only [List.getElem_ofFn, List.getElem_map, List.getElem_tail]
    exact congrArg Subtype.val
      (walk.getVert_eq_support_getElem (Nat.succ_le_of_lt hposition))

/-- The lifted primal walk traverses exactly the line-graph vertices after
the initial one, in the same cyclic order. -/
theorem primalLift_edges_eq_map_tail_support {edge : G.edgeSet}
    (walk : G.lineGraph.Walk edge edge) (hpositive : 0 < walk.length)
    (hcoherent : walk.IsPrimalCoherentClosed) :
    (walk.primalLift hpositive hcoherent).edges =
      walk.support.tail.map Subtype.val := by
  rw [walk.primalLift_edges_eq_ofFn_getVert_succ hpositive hcoherent,
    walk.ofFn_getVert_succ_eq_map_tail_support]

theorem primalLift_isTrail_of_isCycle {edge : G.edgeSet}
    (walk : G.lineGraph.Walk edge edge) (hpositive : 0 < walk.length)
    (hcoherent : walk.IsPrimalCoherentClosed) (hcycle : walk.IsCycle) :
    (walk.primalLift hpositive hcoherent).IsTrail := by
  constructor
  rw [walk.primalLift_edges_eq_map_tail_support hpositive hcoherent]
  exact hcycle.support_nodup.map Subtype.val_injective

/-- A primal-coherent line-graph cycle lifts to a nonempty closed primal
trail, with the same length and the same underlying edge run. -/
theorem primalLift_isCircuit_of_isCycle {edge : G.edgeSet}
    (walk : G.lineGraph.Walk edge edge) (hpositive : 0 < walk.length)
    (hcoherent : walk.IsPrimalCoherentClosed) (hcycle : walk.IsCycle) :
    (walk.primalLift hpositive hcoherent).IsCircuit := by
  constructor
  · exact walk.primalLift_isTrail_of_isCycle hpositive hcoherent hcycle
  · intro heq
    have hnil : (walk.primalLift hpositive hcoherent).Nil :=
      Walk.eq_nil_iff_nil.1 heq
    have hnotNil : ¬(walk.primalLift hpositive hcoherent).Nil := by
      rw [Walk.not_nil_iff_lt_length,
        walk.primalLift_length hpositive hcoherent]
      exact hpositive
    exact hnotNil hnil

end Walk

end SimpleGraph
