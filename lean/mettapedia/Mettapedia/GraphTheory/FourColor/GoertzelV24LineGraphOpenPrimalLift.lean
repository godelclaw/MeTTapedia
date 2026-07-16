import Mettapedia.GraphTheory.FourColor.GoertzelV24LineGraphOpenCoherentShortcut
import Mathlib.Data.List.ChainOfFn

namespace SimpleGraph.Walk

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- Consecutive junctions of an open primal-coherent line-graph walk are
adjacent in the primal graph. -/
theorem adj_lineGraphJunctionAt_succ_open
    {first last : G.edgeSet}
    (walk : G.lineGraph.Walk first last)
    (position : Nat) (hposition : position + 1 < walk.length)
    (hcoherent : walk.IsPrimalCoherent) :
    G.Adj
      (walk.lineGraphJunctionAt ⟨position, by omega⟩)
      (walk.lineGraphJunctionAt ⟨position + 1, hposition⟩) := by
  let current : Fin walk.length := ⟨position, by omega⟩
  let next : Fin walk.length := ⟨position + 1, hposition⟩
  let commonEdge : G.edgeSet := walk.getVert (position + 1)
  have hcurrent : walk.lineGraphJunctionAt current ∈
      (commonEdge.1 : Sym2 V) :=
    walk.lineGraphJunctionAt_mem_right current
  have hnext : walk.lineGraphJunctionAt next ∈
      (commonEdge.1 : Sym2 V) :=
    walk.lineGraphJunctionAt_mem_left next
  have hne := hcoherent position hposition
  have hedge : commonEdge.1 =
      s(walk.lineGraphJunctionAt current,
        walk.lineGraphJunctionAt next) :=
    (Sym2.mem_and_mem_iff hne).1 ⟨hcurrent, hnext⟩
  have hadj := commonEdge.property
  rw [hedge] at hadj
  exact hadj

/-- The primal edge between two consecutive open-walk junctions is the
intermediate line-graph vertex. -/
theorem pair_lineGraphJunctionAt_succ_eq_getVert_open
    {first last : G.edgeSet}
    (walk : G.lineGraph.Walk first last)
    (position : Nat) (hposition : position + 1 < walk.length)
    (hcoherent : walk.IsPrimalCoherent) :
    s(walk.lineGraphJunctionAt ⟨position, by omega⟩,
        walk.lineGraphJunctionAt ⟨position + 1, hposition⟩) =
      (walk.getVert (position + 1)).1 := by
  apply (Sym2.mem_and_mem_iff
    (hcoherent position hposition)).1 ⟨?_, ?_⟩ |>.symm
  · exact walk.lineGraphJunctionAt_mem_right ⟨position, by omega⟩
  · exact walk.lineGraphJunctionAt_mem_left
      ⟨position + 1, hposition⟩

theorem pair_start_lineGraphJunctionAt_eq_first
    {first last : G.edgeSet}
    (walk : G.lineGraph.Walk first last)
    (hpositive : 0 < walk.length)
    (startVertex : V) (hstartMem : startVertex ∈ (first.1 : Sym2 V))
    (hstartNe : startVertex ≠
      walk.lineGraphJunctionAt ⟨0, hpositive⟩) :
    s(startVertex, walk.lineGraphJunctionAt ⟨0, hpositive⟩) =
      first.1 := by
  apply (Sym2.mem_and_mem_iff hstartNe).1 ⟨hstartMem, ?_⟩ |>.symm
  simpa only [walk.getVert_zero] using
    walk.lineGraphJunctionAt_mem_left ⟨0, hpositive⟩

theorem pair_lineGraphJunctionAt_end_eq_last
    {first last : G.edgeSet}
    (walk : G.lineGraph.Walk first last)
    (hpositive : 0 < walk.length)
    (endVertex : V) (hendMem : endVertex ∈ (last.1 : Sym2 V))
    (hendNe : walk.lineGraphJunctionAt
        ⟨walk.length - 1,
          Nat.sub_lt hpositive Nat.zero_lt_one⟩ ≠ endVertex) :
    s(walk.lineGraphJunctionAt
        ⟨walk.length - 1,
          Nat.sub_lt hpositive Nat.zero_lt_one⟩, endVertex) =
      last.1 := by
  apply (Sym2.mem_and_mem_iff hendNe).1 ⟨?_, hendMem⟩ |>.symm
  have hmem := walk.lineGraphJunctionAt_mem_right
    ⟨walk.length - 1,
      Nat.sub_lt hpositive Nat.zero_lt_one⟩
  have hlast : walk.length - 1 + 1 = walk.length := by omega
  simpa only [hlast, walk.getVert_length] using hmem

/-- Add prescribed endpoints to the ordered junction list of an open
line-graph walk. -/
noncomputable def cappedPrimalJunctionSupport
    {first last : G.edgeSet}
    (walk : G.lineGraph.Walk first last)
    (startVertex endVertex : V) : List V :=
  startVertex :: List.ofFn walk.lineGraphJunctionAt ++ [endVertex]

@[simp] theorem cappedPrimalJunctionSupport_length
    {first last : G.edgeSet}
    (walk : G.lineGraph.Walk first last)
    (startVertex endVertex : V) :
    (walk.cappedPrimalJunctionSupport startVertex endVertex).length =
      walk.length + 2 := by
  simp [cappedPrimalJunctionSupport]

theorem cappedPrimalJunctionSupport_ne_nil
    {first last : G.edgeSet}
    (walk : G.lineGraph.Walk first last)
    (startVertex endVertex : V) :
    walk.cappedPrimalJunctionSupport startVertex endVertex ≠ [] := by
  simp [cappedPrimalJunctionSupport]

theorem cappedPrimalJunctionSupport_head
    {first last : G.edgeSet}
    (walk : G.lineGraph.Walk first last)
    (startVertex endVertex : V) :
    (walk.cappedPrimalJunctionSupport startVertex endVertex).head
        (walk.cappedPrimalJunctionSupport_ne_nil startVertex endVertex) =
      startVertex := by
  simp [cappedPrimalJunctionSupport]

theorem cappedPrimalJunctionSupport_getLast
    {first last : G.edgeSet}
    (walk : G.lineGraph.Walk first last)
    (startVertex endVertex : V) :
    (walk.cappedPrimalJunctionSupport startVertex endVertex).getLast
        (walk.cappedPrimalJunctionSupport_ne_nil startVertex endVertex) =
      endVertex := by
  simp [cappedPrimalJunctionSupport]

@[simp] theorem cappedPrimalJunctionSupport_getElem_zero
    {first last : G.edgeSet}
    (walk : G.lineGraph.Walk first last)
    (startVertex endVertex : V) :
    (walk.cappedPrimalJunctionSupport startVertex endVertex)[0]'(by
      rw [walk.cappedPrimalJunctionSupport_length startVertex endVertex]
      omega) = startVertex := by
  simp [cappedPrimalJunctionSupport]

@[simp] theorem cappedPrimalJunctionSupport_getElem_succ
    {first last : G.edgeSet}
    (walk : G.lineGraph.Walk first last)
    (startVertex endVertex : V) (position : Fin walk.length) :
    (walk.cappedPrimalJunctionSupport startVertex endVertex)[position.val + 1]'(by
          rw [walk.cappedPrimalJunctionSupport_length startVertex endVertex]
          omega) =
      walk.lineGraphJunctionAt position := by
  simp [cappedPrimalJunctionSupport]

@[simp] theorem cappedPrimalJunctionSupport_getElem_length_add_one
    {first last : G.edgeSet}
    (walk : G.lineGraph.Walk first last)
    (startVertex endVertex : V) :
    (walk.cappedPrimalJunctionSupport startVertex endVertex)[walk.length + 1]'(by
          rw [walk.cappedPrimalJunctionSupport_length startVertex endVertex]
          omega) = endVertex := by
  simp [cappedPrimalJunctionSupport]

/-- The capped junction list is a primal adjacency chain when the cap
vertices are the opposite endpoints of the terminal line vertices. -/
theorem cappedPrimalJunctionSupport_isChain
    {first last : G.edgeSet}
    (walk : G.lineGraph.Walk first last)
    (hpositive : 0 < walk.length)
    (hcoherent : walk.IsPrimalCoherent)
    (startVertex endVertex : V)
    (hstartMem : startVertex ∈ (first.1 : Sym2 V))
    (hendMem : endVertex ∈ (last.1 : Sym2 V))
    (hstartNe : startVertex ≠
      walk.lineGraphJunctionAt ⟨0, hpositive⟩)
    (hendNe : walk.lineGraphJunctionAt
        ⟨walk.length - 1,
          Nat.sub_lt hpositive Nat.zero_lt_one⟩ ≠ endVertex) :
    (walk.cappedPrimalJunctionSupport startVertex endVertex).IsChain
      G.Adj := by
  rw [cappedPrimalJunctionSupport]
  let junctions : List V := List.ofFn walk.lineGraphJunctionAt
  have hjunctionsNonempty : junctions ≠ [] := by
    apply List.ne_nil_of_length_pos
    simpa only [junctions, List.length_ofFn] using hpositive
  have hjunctionsChain : junctions.IsChain G.Adj := by
    dsimp only [junctions]
    rw [List.isChain_ofFn]
    intro position hposition
    exact walk.adj_lineGraphJunctionAt_succ_open position hposition
      hcoherent
  have hjunctionsEndChain : (junctions ++ [endVertex]).IsChain G.Adj := by
    apply hjunctionsChain.append (List.isChain_singleton endVertex)
    intro lastJunction hlast candidate hcand
    simp at hcand
    subst candidate
    rcases List.mem_getLast?_eq_getLast hlast with ⟨hne, rfl⟩
    dsimp only [junctions]
    rw [List.getLast_ofFn hne]
    have hadj := last.property
    rw [← walk.pair_lineGraphJunctionAt_end_eq_last
      hpositive endVertex hendMem hendNe] at hadj
    exact hadj
  have hjunctionsEndNonempty : junctions ++ [endVertex] ≠ [] :=
    List.append_ne_nil_of_right_ne_nil junctions (List.cons_ne_nil _ _)
  apply hjunctionsEndChain.cons_of_ne_nil hjunctionsEndNonempty
  · have hhead : (junctions ++ [endVertex]).head
        (List.append_ne_nil_of_left_ne_nil hjunctionsNonempty [endVertex]) =
        walk.lineGraphJunctionAt ⟨0, hpositive⟩ := by
      rw [List.head_append_of_ne_nil hjunctionsNonempty]
      rw [List.head_eq_getElem_zero hjunctionsNonempty]
      dsimp only [junctions]
      simp
    rw [hhead]
    have hadj := first.property
    rw [← walk.pair_start_lineGraphJunctionAt_eq_first
      hpositive startVertex hstartMem hstartNe] at hadj
    exact hadj

/-- Canonical open primal lift, capped by the two prescribed endpoints. -/
noncomputable def cappedPrimalLift
    {first last : G.edgeSet}
    (walk : G.lineGraph.Walk first last)
    (hpositive : 0 < walk.length)
    (hcoherent : walk.IsPrimalCoherent)
    (startVertex endVertex : V)
    (hstartMem : startVertex ∈ (first.1 : Sym2 V))
    (hendMem : endVertex ∈ (last.1 : Sym2 V))
    (hstartNe : startVertex ≠
      walk.lineGraphJunctionAt ⟨0, hpositive⟩)
    (hendNe : walk.lineGraphJunctionAt
        ⟨walk.length - 1,
          Nat.sub_lt hpositive Nat.zero_lt_one⟩ ≠ endVertex) :
    G.Walk startVertex endVertex :=
  (Walk.ofSupport
      (walk.cappedPrimalJunctionSupport startVertex endVertex)
      (walk.cappedPrimalJunctionSupport_ne_nil startVertex endVertex)
      (walk.cappedPrimalJunctionSupport_isChain hpositive hcoherent
        startVertex endVertex hstartMem hendMem hstartNe hendNe)).copy
    (walk.cappedPrimalJunctionSupport_head startVertex endVertex)
    (walk.cappedPrimalJunctionSupport_getLast startVertex endVertex)

@[simp] theorem cappedPrimalLift_support
    {first last : G.edgeSet}
    (walk : G.lineGraph.Walk first last)
    (hpositive : 0 < walk.length)
    (hcoherent : walk.IsPrimalCoherent)
    (startVertex endVertex : V)
    (hstartMem : startVertex ∈ (first.1 : Sym2 V))
    (hendMem : endVertex ∈ (last.1 : Sym2 V))
    (hstartNe : startVertex ≠
      walk.lineGraphJunctionAt ⟨0, hpositive⟩)
    (hendNe : walk.lineGraphJunctionAt
        ⟨walk.length - 1,
          Nat.sub_lt hpositive Nat.zero_lt_one⟩ ≠ endVertex) :
    (walk.cappedPrimalLift hpositive hcoherent startVertex endVertex
      hstartMem hendMem hstartNe hendNe).support =
      walk.cappedPrimalJunctionSupport startVertex endVertex := by
  simp [cappedPrimalLift]

@[simp] theorem cappedPrimalLift_length
    {first last : G.edgeSet}
    (walk : G.lineGraph.Walk first last)
    (hpositive : 0 < walk.length)
    (hcoherent : walk.IsPrimalCoherent)
    (startVertex endVertex : V)
    (hstartMem : startVertex ∈ (first.1 : Sym2 V))
    (hendMem : endVertex ∈ (last.1 : Sym2 V))
    (hstartNe : startVertex ≠
      walk.lineGraphJunctionAt ⟨0, hpositive⟩)
    (hendNe : walk.lineGraphJunctionAt
        ⟨walk.length - 1,
          Nat.sub_lt hpositive Nat.zero_lt_one⟩ ≠ endVertex) :
    (walk.cappedPrimalLift hpositive hcoherent startVertex endVertex
      hstartMem hendMem hstartNe hendNe).length = walk.length + 1 := by
  rw [cappedPrimalLift, SimpleGraph.Walk.length_copy,
    SimpleGraph.Walk.length_ofSupport,
    walk.cappedPrimalJunctionSupport_length startVertex endVertex]
  omega

/-- The edge at every position of the capped primal lift is the
corresponding line-graph vertex. -/
theorem cappedPrimalLift_edges_getElem
    {first last : G.edgeSet}
    (walk : G.lineGraph.Walk first last)
    (hpositive : 0 < walk.length)
    (hcoherent : walk.IsPrimalCoherent)
    (startVertex endVertex : V)
    (hstartMem : startVertex ∈ (first.1 : Sym2 V))
    (hendMem : endVertex ∈ (last.1 : Sym2 V))
    (hstartNe : startVertex ≠
      walk.lineGraphJunctionAt ⟨0, hpositive⟩)
    (hendNe : walk.lineGraphJunctionAt
        ⟨walk.length - 1,
          Nat.sub_lt hpositive Nat.zero_lt_one⟩ ≠ endVertex)
    (position : Fin (walk.length + 1)) :
    (walk.cappedPrimalLift hpositive hcoherent startVertex endVertex
      hstartMem hendMem hstartNe hendNe).edges[position.val]'(by
        rw [SimpleGraph.Walk.length_edges,
          walk.cappedPrimalLift_length hpositive hcoherent
            startVertex endVertex hstartMem hendMem hstartNe hendNe]
        exact position.isLt) =
      (walk.getVert position.val).1 := by
  simp only [SimpleGraph.Walk.edges_eq_zipWith_support,
    List.getElem_zipWith, List.getElem_tail,
    walk.cappedPrimalLift_support hpositive hcoherent startVertex endVertex
      hstartMem hendMem hstartNe hendNe]
  by_cases hzero : position.val = 0
  · have hposition : position = ⟨0, by omega⟩ := by
      apply Fin.ext
      exact hzero
    rw [hposition]
    rw [walk.cappedPrimalJunctionSupport_getElem_zero,
      walk.cappedPrimalJunctionSupport_getElem_succ
        startVertex endVertex ⟨0, hpositive⟩]
    simpa only [walk.getVert_zero] using
      walk.pair_start_lineGraphJunctionAt_eq_first
        hpositive startVertex hstartMem hstartNe
  · obtain ⟨previous, hpositionValue⟩ :=
      Nat.exists_eq_add_one_of_ne_zero hzero
    by_cases hinternal : previous + 1 < walk.length
    · have hposition : position =
          ⟨previous + 1, by omega⟩ := by
        apply Fin.ext
        exact hpositionValue
      rw [hposition]
      rw [walk.cappedPrimalJunctionSupport_getElem_succ
          startVertex endVertex ⟨previous, by omega⟩,
        walk.cappedPrimalJunctionSupport_getElem_succ
          startVertex endVertex ⟨previous + 1, hinternal⟩]
      exact walk.pair_lineGraphJunctionAt_succ_eq_getVert_open
        previous hinternal hcoherent
    · have hlast : previous + 1 = walk.length := by
        have hbound := position.isLt
        rw [hpositionValue] at hbound
        omega
      have hposition : position =
          ⟨walk.length, by omega⟩ := by
        apply Fin.ext
        exact hpositionValue.trans hlast
      rw [hposition]
      have hlastIndex : walk.length - 1 + 1 = walk.length := by omega
      have hfirstSupport :
          (walk.cappedPrimalJunctionSupport startVertex endVertex)[walk.length]'(by
                rw [walk.cappedPrimalJunctionSupport_length
                  startVertex endVertex]
                omega) =
            walk.lineGraphJunctionAt
              ⟨walk.length - 1, by omega⟩ := by
        simpa only [hlastIndex] using
          walk.cappedPrimalJunctionSupport_getElem_succ
            startVertex endVertex ⟨walk.length - 1, by omega⟩
      rw [hfirstSupport,
        walk.cappedPrimalJunctionSupport_getElem_length_add_one]
      simpa only [walk.getVert_length] using
        walk.pair_lineGraphJunctionAt_end_eq_last
          hpositive endVertex hendMem hendNe

/-- The capped lift traverses exactly the primal edges represented by the
line-graph path, in the same order. -/
theorem cappedPrimalLift_edges_eq_map_support
    {first last : G.edgeSet}
    (walk : G.lineGraph.Walk first last)
    (hpositive : 0 < walk.length)
    (hcoherent : walk.IsPrimalCoherent)
    (startVertex endVertex : V)
    (hstartMem : startVertex ∈ (first.1 : Sym2 V))
    (hendMem : endVertex ∈ (last.1 : Sym2 V))
    (hstartNe : startVertex ≠
      walk.lineGraphJunctionAt ⟨0, hpositive⟩)
    (hendNe : walk.lineGraphJunctionAt
        ⟨walk.length - 1,
          Nat.sub_lt hpositive Nat.zero_lt_one⟩ ≠ endVertex) :
    (walk.cappedPrimalLift hpositive hcoherent startVertex endVertex
      hstartMem hendMem hstartNe hendNe).edges =
      walk.support.map Subtype.val := by
  apply List.ext_getElem
  · rw [SimpleGraph.Walk.length_edges,
      walk.cappedPrimalLift_length hpositive hcoherent
        startVertex endVertex hstartMem hendMem hstartNe hendNe,
      List.length_map, walk.length_support]
  · intro position hleft hright
    have hposition : position < walk.length + 1 := by
      simpa only [List.length_map, walk.length_support] using hright
    have hlift := walk.cappedPrimalLift_edges_getElem
      hpositive hcoherent startVertex endVertex hstartMem hendMem
      hstartNe hendNe ⟨position, hposition⟩
    have hsupport := congrArg Subtype.val
      (walk.getVert_eq_support_getElem (n := position) (by omega))
    simpa only [List.getElem_map] using hlift.trans hsupport

/-- A simple primal-coherent open line-graph path lifts, with valid endpoint
caps, to a primal trail using exactly its represented edges. -/
theorem cappedPrimalLift_isTrail_of_isPath
    {first last : G.edgeSet}
    (walk : G.lineGraph.Walk first last)
    (hpositive : 0 < walk.length)
    (hcoherent : walk.IsPrimalCoherent)
    (hpath : walk.IsPath)
    (startVertex endVertex : V)
    (hstartMem : startVertex ∈ (first.1 : Sym2 V))
    (hendMem : endVertex ∈ (last.1 : Sym2 V))
    (hstartNe : startVertex ≠
      walk.lineGraphJunctionAt ⟨0, hpositive⟩)
    (hendNe : walk.lineGraphJunctionAt
        ⟨walk.length - 1,
          Nat.sub_lt hpositive Nat.zero_lt_one⟩ ≠ endVertex) :
    (walk.cappedPrimalLift hpositive hcoherent startVertex endVertex
      hstartMem hendMem hstartNe hendNe).IsTrail := by
  constructor
  rw [walk.cappedPrimalLift_edges_eq_map_support
    hpositive hcoherent startVertex endVertex hstartMem hendMem
    hstartNe hendNe]
  exact hpath.support_nodup.map Subtype.val_injective

end SimpleGraph.Walk
