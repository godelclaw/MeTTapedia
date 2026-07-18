import Mathlib.Combinatorics.SimpleGraph.Matching

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V}

omit [Fintype V] [DecidableEq V] in
/-- A walk starting in a vertex set stays there when that set is closed
under every ambient adjacency encountered by the walk. -/
theorem walk_support_subset_of_start_mem_of_adj_closed
    {H : SimpleGraph V} {u w : V} (walk : H.Walk u w)
    {vertices : Set V} (hstart : u ∈ vertices)
    (hclosed : ∀ {left right : V}, left ∈ vertices →
      H.Adj left right → right ∈ vertices) :
    ∀ vertex ∈ walk.support, vertex ∈ vertices := by
  induction walk with
  | nil => simpa using hstart
  | @cons left middle right hadj tail ih =>
      intro vertex hvertex
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hvertex
      rcases hvertex with rfl | hvertex
      · exact hstart
      · exact ih (hclosed hstart hadj) vertex hvertex

/-- A simple cycle has no proper nonempty simple subcycle: edge containment
between two simple cycles is equality of their edge supports. -/
theorem isCycle_mem_edges_iff_of_subset
    {firstRoot secondRoot : V}
    {first : G.Walk firstRoot firstRoot}
    {second : G.Walk secondRoot secondRoot}
    (hfirst : first.IsCycle) (hsecond : second.IsCycle)
    (hsubset : second.edges ⊆ first.edges) (edge : Sym2 V) :
    edge ∈ first.edges ↔ edge ∈ second.edges := by
  let H : SimpleGraph V := first.toSubgraph.spanningCoe
  letI : H.LocallyFinite := fun _ => Fintype.ofFinite _
  have hsecondH : ∀ edge, edge ∈ second.edges → edge ∈ H.edgeSet := by
    intro edge hedge
    change edge ∈ first.toSubgraph.edgeSet
    exact first.mem_edges_toSubgraph.2 (hsubset hedge)
  let transferredSecond := second.transfer H hsecondH
  have htransferredSecond : transferredSecond.IsCycle :=
    hsecond.transfer hsecondH
  have hHcycles : H.IsCycles :=
    hfirst.isCycles_spanningCoe_toSubgraph
  have hsecondRootFirst : secondRoot ∈ first.support :=
    first.fst_mem_support_of_mem_edges
      (hsubset (second.mk_start_snd_mem_edges hsecond.not_nil))
  let rotatedFirst := first.rotate secondRoot hsecondRootFirst
  have hrotatedFirstH : ∀ edge, edge ∈ rotatedFirst.edges →
      edge ∈ H.edgeSet := by
    intro edge hedge
    change edge ∈ first.toSubgraph.edgeSet
    exact first.mem_edges_toSubgraph.2
      ((first.rotate_edges secondRoot hsecondRootFirst).mem_iff.1 hedge)
  let transferredFirst := rotatedFirst.transfer H hrotatedFirstH
  have hclosed : ∀ {left right : V},
      left ∈ transferredSecond.toSubgraph.verts → H.Adj left right →
        right ∈ transferredSecond.toSubgraph.verts := by
    intro left right hleft hadj
    have hsubgraphAdj : transferredSecond.toSubgraph.Adj left right :=
      (htransferredSecond.adj_toSubgraph_iff_of_isCycles hHcycles
        hleft right).2 hadj
    exact transferredSecond.toSubgraph.edge_vert hsubgraphAdj.symm
  have htransferredFirstSupport : ∀ vertex ∈ transferredFirst.support,
      vertex ∈ transferredSecond.toSubgraph.verts :=
    walk_support_subset_of_start_mem_of_adj_closed transferredFirst
      transferredSecond.start_mem_verts_toSubgraph hclosed
  have hfirstSupport : ∀ vertex ∈ first.support,
      vertex ∈ transferredSecond.toSubgraph.verts := by
    intro vertex hvertex
    apply htransferredFirstSupport vertex
    rw [SimpleGraph.Walk.support_transfer]
    exact (first.mem_support_rotate_iff secondRoot hsecondRootFirst).2 hvertex
  constructor
  · intro hedge
    induction edge using Sym2.ind with
    | _ left right =>
        have hfirstAdj : first.toSubgraph.Adj left right :=
          first.adj_toSubgraph_iff_mem_edges.2 hedge
        have hleft : left ∈ transferredSecond.toSubgraph.verts :=
          hfirstSupport left (first.mem_support_of_adj_toSubgraph hfirstAdj)
        have hHadj : H.Adj left right := by
          exact hfirstAdj
        have hsecondAdj : transferredSecond.toSubgraph.Adj left right :=
          (htransferredSecond.adj_toSubgraph_iff_of_isCycles hHcycles
            hleft right).2 hHadj
        have htransferredEdge : s(left, right) ∈ transferredSecond.edges :=
          transferredSecond.adj_toSubgraph_iff_mem_edges.1 hsecondAdj
        simpa [transferredSecond] using htransferredEdge
  · intro hedge
    exact hsubset hedge

end Mettapedia.GraphTheory.FourColor
