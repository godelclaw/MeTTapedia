import Mettapedia.OSLF.MeTTaIL.Complete.Settled

/-!
# The transition graph of an exploration

An explorer visits each state once, so a receipt whose target already has a node adds no node.
The transition is not lost: it stays in the publication of the node that found it. `edges`
reads every node's published receipts as transitions `(state, receipt, target)`: the states
are the explored set, and the edges keep every event and its origin, including those that
reach a state found along another path.

- `edge_valid`: every edge is a valid receipt of its source state;
- `edge_target`: in a settled explorer every edge ends at an explored state;
- `edges_complete`: in a settled explorer of a stable search, every receipt that the search
  of an explored state ever publishes is an edge;
- `edges_cover_steps`: for the search modulo equations, every GSLT step out of an explored
  state appears as an edge, up to equality.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Complete.Graph

open Mettapedia.Machines.ResumableSearchRunner (Search Status)
open Mettapedia.OSLF.MeTTaIL.Complete.Explore (Node Explorer explore step begin)
open Mettapedia.OSLF.MeTTaIL.Complete.Settled (Stable nodeSettled settled roundsUntilSettled)

variable {σ Run Receipt : Type} [DecidableEq σ] (S : Search σ Run Receipt)

/-- The transitions a node has found. -/
def nodeEdges (node : Node σ Run Receipt) : List (σ × Receipt × σ) :=
  (S.publication node.run).map fun receipt => (node.state, receipt, S.target receipt)

/-- **The transitions an explorer has found.** -/
def edges (explorer : Explorer σ Run Receipt) : List (σ × Receipt × σ) :=
  explorer.nodes.flatMap (nodeEdges S)

omit [DecidableEq σ] in
theorem mem_edges {explorer : Explorer σ Run Receipt} {edge : σ × Receipt × σ} :
    edge ∈ edges S explorer ↔
      ∃ node ∈ explorer.nodes, ∃ receipt ∈ S.publication node.run, edge = (node.state, receipt, S.target receipt) := by
  simp only [edges, nodeEdges, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨node, member, receipt, published, rfl⟩
    exact ⟨node, member, receipt, published, rfl⟩
  · rintro ⟨node, member, receipt, published, rfl⟩
    exact ⟨node, member, receipt, published, rfl⟩

variable {S}

/-- Stopping once settled is some number of rounds, at most the work allowed. -/
theorem roundsUntilSettled_explore (source : σ) : ∀ (work rounds : Nat),
    ∃ more ≤ work, roundsUntilSettled S work (explore S source rounds) = explore S source (rounds + more)
  | 0, rounds => ⟨0, Nat.le_refl _, rfl⟩
  | work + 1, rounds => by
    simp only [roundsUntilSettled]
    split
    · exact ⟨0, Nat.zero_le _, rfl⟩
    · obtain ⟨more, bounded, same⟩ := roundsUntilSettled_explore source work (rounds + 1)
      refine ⟨more + 1, by omega, ?_⟩
      rw [show step S (explore S source rounds) = explore S source (rounds + 1) from rfl, same]
      congr 1
      omega

/-- **Every edge is a valid receipt of its source state.** -/
theorem edge_valid (lawful : S.Lawful) (source : σ) (work : Nat) :
    ∀ edge ∈ edges S (explore S source work), S.Valid edge.1 edge.2.1 ∧ edge.2.2 = S.target edge.2.1 := by
  intro edge member
  obtain ⟨node, present, receipt, published, rfl⟩ := (mem_edges S).mp member
  have good := Explore.explore_good lawful source work
  refine ⟨?_, rfl⟩
  apply lawful.sound node.state ((explore S source work).round - node.born)
  rw [← good.run node present]
  exact published

/-- **In a settled explorer every edge ends at an explored state.** -/
theorem edge_target (lawful : S.Lawful) (source : σ) (work : Nat)
    (done : settled S (explore S source work) = true) :
    ∀ edge ∈ edges S (explore S source work), ∃ node ∈ (explore S source work).nodes, node.state = edge.2.2 := by
  intro edge member
  obtain ⟨node, present, receipt, published, rfl⟩ := (mem_edges S).mp member
  have nodeDone : nodeSettled S node = true := List.all_eq_true.mp done node present
  simp only [nodeSettled, Bool.and_eq_true, beq_iff_eq] at nodeDone
  have taken : receipt ∈ (S.publication node.run).take node.consumed := by
    rw [nodeDone.2, List.take_length]
    exact published
  exact (Explore.explore_good lawful source work).children node present receipt taken

/-- **In a settled explorer of a stable search, every receipt that the search of an explored
state ever publishes is an edge.** -/
theorem edges_complete (lawful : S.Lawful) (stable : Stable S) (source : σ) (work : Nat)
    (done : settled S (explore S source work) = true) :
    ∀ node ∈ (explore S source work).nodes, ∀ (rounds : Nat) (receipt : Receipt),
      receipt ∈ S.publication (S.run node.state rounds) →
        (node.state, receipt, S.target receipt) ∈ edges S (explore S source work) := by
  intro node present rounds receipt published
  have nodeDone : nodeSettled S node = true := List.all_eq_true.mp done node present
  simp only [nodeSettled, Bool.and_eq_true, beq_iff_eq] at nodeDone
  have runNow := (Explore.explore_good lawful source work).run node present
  set spent := (explore S source work).round - node.born
  have inRun : receipt ∈ S.publication node.run := by
    rw [runNow]
    by_cases early : rounds ≤ spent
    · obtain ⟨extra, total⟩ := Nat.exists_eq_add_of_le early
      rw [total]
      exact (lawful.publication_prefix node.state rounds extra).subset published
    · obtain ⟨extra, total⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt (Nat.lt_of_not_le early))
      have complete : S.status (S.run node.state spent) = .complete := by rw [← runNow]; exact nodeDone.1
      have same := (stable (S.run node.state spent) extra complete).1
      rw [lawful.resume_run, ← total] at same
      rw [same] at published
      exact published
  exact (mem_edges S).mpr ⟨node, present, receipt, inRun, rfl⟩

/-! ## Steps modulo equations -/

section Classes

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralExecutionAdmission

variable (plan : Plan) (bound : List TypeExpr) (expected : TypeExpr)

/-- **Every GSLT step out of an explored state appears as an edge**, up to equality, once the
exploration modulo equations is settled. -/
theorem edges_cover_steps (checked : Predecessors.equationsChecked plan = true) (source : Pattern) (work : Nat)
    (done : settled (Classes.search plan bound expected) (explore (Classes.search plan bound expected) source work) = true)
    {node : Node Pattern (Classes.State plan) GeneralOccurrenceSemantics.Receipt}
    (present : node ∈ (explore (Classes.search plan bound expected) source work).nodes) {target : Pattern}
    (stepped : (GeneralOccurrenceSemantics.gslt plan bound expected).Step node.state target) :
    ∃ receipt, (node.state, receipt, receipt.target) ∈
        edges (Classes.search plan bound expected) (explore (Classes.search plan bound expected) source work) ∧
      Relation.EqvGen (GeneralOccurrenceSemantics.Equation plan bound expected) receipt.target target := by
  obtain ⟨rounds, receipt, published, related⟩ := Classes.complete_in_limit plan bound expected node.state checked stepped
  exact ⟨receipt, edges_complete (Classes.search_lawful plan bound expected) (Settled.classes_stable plan bound expected)
    source work done node present rounds receipt published, related⟩

end Classes

end Mettapedia.OSLF.MeTTaIL.Complete.Graph
