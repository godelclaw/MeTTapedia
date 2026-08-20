import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# L1: point an internal occurrence of a path vertex

Support membership forgets where a vertex occurs.  For the source-local rail
assembly this distinction is load-bearing: a retained collision in the tail
of a simple rail is either its terminal endpoint, or it has literal predecessor
and successor vertices on that rail.

This file packages the second alternative without making any geometric claim
about those neighbours.  In particular it does not identify an endpoint
triangle, construct a bypass, prove separation from a companion path, or close
Fable flag L1.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24DualPathPointedOccurrence

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- A proof-relevant internal occurrence of `current` on `walk`.  The strict
index bounds deliberately exclude both endpoints. -/
structure InteriorOccurrence
    {start finish current : V} (walk : G.Walk start finish) where
  index : Nat
  index_pos : 0 < index
  index_lt : index < walk.length
  getVert_eq : walk.getVert index = current

namespace InteriorOccurrence

variable {start finish current : V} {walk : G.Walk start finish}

/-- The vertex immediately before the pointed occurrence. -/
def predecessor (occurrence : InteriorOccurrence (current := current) walk) : V :=
  walk.getVert (occurrence.index - 1)

/-- The vertex immediately after the pointed occurrence. -/
def successor (occurrence : InteriorOccurrence (current := current) walk) : V :=
  walk.getVert (occurrence.index + 1)

/-- The graph edge by which the path enters the pointed occurrence. -/
def incomingEdge (occurrence : InteriorOccurrence (current := current) walk) :
    Sym2 V :=
  s(occurrence.predecessor, current)

/-- The graph edge by which the path leaves the pointed occurrence. -/
def outgoingEdge (occurrence : InteriorOccurrence (current := current) walk) :
    Sym2 V :=
  s(current, occurrence.successor)

theorem predecessor_adj_current
    (occurrence : InteriorOccurrence (current := current) walk) :
    G.Adj occurrence.predecessor current := by
  have hpreviousLt : occurrence.index - 1 < walk.length :=
    Nat.lt_of_le_of_lt (Nat.sub_le occurrence.index 1) occurrence.index_lt
  have hadj := walk.adj_getVert_succ
    (i := occurrence.index - 1) hpreviousLt
  have hstep : occurrence.index - 1 + 1 = occurrence.index :=
    Nat.sub_add_cancel occurrence.index_pos
  rw [hstep, occurrence.getVert_eq] at hadj
  exact hadj

theorem current_adj_successor
    (occurrence : InteriorOccurrence (current := current) walk) :
    G.Adj current occurrence.successor := by
  simpa [successor, occurrence.getVert_eq] using
    walk.adj_getVert_succ (i := occurrence.index) occurrence.index_lt

theorem predecessor_ne_current
    (occurrence : InteriorOccurrence (current := current) walk) :
    occurrence.predecessor ≠ current :=
  occurrence.predecessor_adj_current.ne

theorem current_ne_successor
    (occurrence : InteriorOccurrence (current := current) walk) :
    current ≠ occurrence.successor :=
  occurrence.current_adj_successor.ne

/-- The incoming edge is a literal edge of the original walk, not merely an
ambient adjacency reconstructed from its support. -/
theorem incomingEdge_mem_edges
    (occurrence : InteriorOccurrence (current := current) walk) :
    occurrence.incomingEdge ∈ walk.edges := by
  have hindex : occurrence.index - 1 < walk.darts.length := by
    rw [walk.length_darts]
    exact Nat.lt_of_le_of_lt (Nat.sub_le occurrence.index 1)
      occurrence.index_lt
  have hstep : occurrence.index - 1 + 1 = occurrence.index :=
    Nat.sub_add_cancel occurrence.index_pos
  rw [SimpleGraph.Walk.edges]
  apply List.mem_map.mpr
  refine ⟨walk.darts[occurrence.index - 1], List.getElem_mem hindex, ?_⟩
  rw [walk.darts_getElem_eq_getVert (occurrence.index - 1) hindex]
  simp [incomingEdge, predecessor, hstep, occurrence.getVert_eq]

/-- The outgoing edge is likewise retained as an edge occurrence of the
original walk. -/
theorem outgoingEdge_mem_edges
    (occurrence : InteriorOccurrence (current := current) walk) :
    occurrence.outgoingEdge ∈ walk.edges := by
  have hindex : occurrence.index < walk.darts.length := by
    simpa using occurrence.index_lt
  rw [SimpleGraph.Walk.edges]
  apply List.mem_map.mpr
  refine ⟨walk.darts[occurrence.index], List.getElem_mem hindex, ?_⟩
  rw [walk.darts_getElem_eq_getVert occurrence.index hindex]
  simp [outgoingEdge, successor, occurrence.getVert_eq]

/-- Simplicity prevents the two neighbours of an internal occurrence from
coinciding. -/
theorem predecessor_ne_successor
    (occurrence : InteriorOccurrence (current := current) walk)
    (hpath : walk.IsPath) :
    occurrence.predecessor ≠ occurrence.successor := by
  intro heq
  have hindex := hpath.getVert_injOn
    (show occurrence.index - 1 ∈ {i | i ≤ walk.length} by
      exact Nat.le_trans (Nat.sub_le occurrence.index 1)
        (Nat.le_of_lt occurrence.index_lt))
    (show occurrence.index + 1 ∈ {i | i ≤ walk.length} by
      exact Nat.add_one_le_iff.mpr occurrence.index_lt)
    (by simpa [predecessor, successor] using heq)
  omega

end InteriorOccurrence

/-- A tail vertex of a simple path is either the terminal endpoint or has a
literal internal occurrence.  Tail membership rules out the initial endpoint;
the theorem keeps the terminal case explicit. -/
theorem eq_finish_or_nonempty_interiorOccurrence_of_mem_support_tail
    {start finish current : V} (walk : G.Walk start finish)
    (hpath : walk.IsPath) (hcurrent : current ∈ walk.support.tail) :
    current = finish ∨
      Nonempty (InteriorOccurrence (current := current) walk) := by
  have hstartNotTail : start ∉ walk.support.tail := by
    have hnodup := hpath.support_nodup
    rw [← walk.cons_tail_support] at hnodup
    exact (List.nodup_cons.mp hnodup).1
  have hstartNe : start ≠ current := by
    intro heq
    exact hstartNotTail (heq ▸ hcurrent)
  obtain ⟨index, hget, hindexLe⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp
      (List.mem_of_mem_tail hcurrent)
  have hindexPos : 0 < index := by
    by_contra hnot
    have hzero : index = 0 := by omega
    subst index
    exact hstartNe (by simpa using hget)
  by_cases hterminal : index = walk.length
  · left
    subst index
    simpa using hget.symm
  · right
    exact ⟨{
      index := index
      index_pos := hindexPos
      index_lt := by omega
      getVert_eq := hget
    }⟩

end GoertzelV24DualPathPointedOccurrence

end Mettapedia.GraphTheory.FourColor
